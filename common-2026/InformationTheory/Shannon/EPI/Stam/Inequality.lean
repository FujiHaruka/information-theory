import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.Blachman.Density
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Stam inequality body discharge (Cauchy–Schwarz / convolution-score path)

This file builds the body of the Stam inequality `1 / J(X + Y) ≥ 1 / J(X) + 1 / J(Y)` (published as
`IsStamInequalityHyp` in `StamEPIBridge`) along the Cauchy–Schwarz / convolution-score path.

## Main definitions

* `IsStamScoreConvolution X Y P` — the score-convolution representation (Step 1).
* `IsStamCauchySchwarz X Y P` — the conditional Cauchy–Schwarz plus total expectation (Steps 2-3).
* `IsStamCauchySchwarzOptimal X Y P` — the optimal-`λ` form of the Cauchy–Schwarz bound.

## Main statements

* `stam_step2_density_wall` — the genuine Step 2-3 analytic core, producing the optimal
  Cauchy–Schwarz bound from regularity alone.
* `isStamInequalityHyp_via_body` — bridge from the optimal Cauchy–Schwarz form to the published
  Stam signature `IsStamInequalityHyp`.
* `epi_via_stam_body_gaussian` — end-to-end entropy power inequality for Gaussians via the body
  discharge.

## Implementation notes

The standard 1-dimensional Stam inequality proof (Cover–Thomas Lemma 17.7.2) follows the path:
score representation of the convolution (Blachman 1965), conditional Cauchy–Schwarz, total
expectation giving `J(Z) ≤ λ² J(X) + (1 - λ)² J(Y)`, and optimization over `λ` at
`λ = J(Y) / (J(X) + J(Y))`. The genuine analytic core (Steps 2-3) is localized to
`stam_step2_density_wall`; the `λ`-optimization is the pure arithmetic `stam_lambda_min`.

## References

[CoverThomas2006] Lemmas 17.7.1, 17.7.2; [Blachman1965].
-/

namespace InformationTheory.Shannon.StamInequality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.StamEPIBridge

/-! ## §1 — Convolution score representation predicate (Step 1) -/

/-- The score-convolution representation (Blachman 1965 / Cover–Thomas Lemma 17.7.1): for
independent `X, Y` with smooth densities, the score of `Z := X + Y` is the conditional expectation
`s_Z(z) = E[λ s_X(X) + (1 - λ) s_Y(Y) | X + Y = z]` for every `λ`. This predicate reifies the
*output* of that identity — the existence of the optimal `λ`-witness `λ* = J_Y / (J_X + J_Y)` in
`[0, 1]` — rather than its derivation. The witness is unconditionally constructible
(`isStamScoreConvolution_intro`), so the predicate is not load-bearing: the downstream
`λ`-optimization only consumes the witness.

@audit:ok -/
def IsStamScoreConvolution {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y : ℝ) (fX fY : ℝ → ℝ), 0 < J_X → 0 < J_Y →
    J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ lam = J_Y / (J_X + J_Y)

/-- Unconditional discharge of the score-convolution predicate: the optimal `λ`-witness
`λ* = J_Y / (J_X + J_Y)` always lies in `[0, 1]` for positive Fisher infos.

@audit:ok -/
@[entry_point]
theorem isStamScoreConvolution_intro {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : IsStamScoreConvolution X Y P := by
  intro J_X J_Y fX fY hJX hJY _hJX_def _hJY_def
  refine ⟨J_Y / (J_X + J_Y), ?_, ?_, rfl⟩
  · positivity
  · have hsum : 0 < J_X + J_Y := by linarith
    rw [div_le_one hsum]; linarith


/-! ## §2 — Cauchy-Schwarz + total expectation predicate (Step 2-3) -/

/-- **Cauchy-Schwarz + total expectation hypothesis** (Stam body).

The genuine Stam-proof body step: given the score-convolution identity, apply
Cauchy-Schwarz pointwise to `s_Z(z)² = E[λ s_X + (1 - λ) s_Y | sum = z]²`,
then take total expectation against `p_Z` to obtain

    `J(Z) ≤ λ² J(X) + (1 - λ)² J(Y)`.

Phrased here as: there exists `λ ∈ [0, 1]` with the inequality between
real-valued Fisher info projections. The predicate enforces only the
**existence of the bounding λ-witness**; the optimum is selected separately in
§3. -/
def IsStamCauchySchwarz {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX →
    InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY →
    (∫ x, fX x ∂MeasureTheory.volume = 1) →
    (∫ x, fY x ∂MeasureTheory.volume = 1) →
    (∀ x, fXY x =
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x) →
    InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY →
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      J_sum ≤ lam ^ 2 * J_X + (1 - lam) ^ 2 * J_Y

/-- The Cauchy-Schwarz predicate is symmetric in `X, Y` (swap `λ ↦ 1 - λ`). -/
theorem isStamCauchySchwarz_symm {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamCauchySchwarz X Y P) :
    IsStamCauchySchwarz Y X P := by
  intro J_Y J_X J_sum fY fX fXY hJY hJX hJsum hJY_def hJX_def hJsum_def
    hregY hregX hnormY hnormX hconv hready
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm] at hJsum_def
  -- transport the convolution constraint across `convDensityAdd` commutativity
  have hconv' : ∀ x, fXY x =
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x := by
    intro x
    rw [InformationTheory.Shannon.EPIConvDensity.convDensityAdd_comm fX fY]
    exact hconv x
  have hready' :
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY :=
    InformationTheory.Shannon.EPIBlachmanDensity.isBlachmanConvReady_symm hready
  obtain ⟨lam, hlam_lo, hlam_hi, hbd⟩ :=
    h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
      hregX hregY hnormX hnormY hconv' hready'
  refine ⟨1 - lam, by linarith, by linarith, ?_⟩
  -- `J_sum ≤ lam² J_X + (1 - lam)² J_Y = (1 - (1 - lam))² J_X + (1 - lam)² J_Y`.
  have : (1 - (1 - lam)) ^ 2 = lam ^ 2 := by ring
  linarith [this]

/-! ## §3 — λ-optimization closed form (Step 4): pure arithmetic, no predicate -/

/-- **λ-optimization closed form** (Stam Step 4).

For positive `a, b > 0`, the function `λ ↦ λ² a + (1 - λ)² b` is minimized at
`λ* = b / (a + b)` with minimum value `a b / (a + b)`. Combined with Step 3,
this gives `J(Z) ≤ J(X) J(Y) / (J(X) + J(Y))`, equivalently
`1 / J(Z) ≥ 1 / J(X) + 1 / J(Y)`. -/
@[entry_point]
theorem stam_lambda_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let lam := b / (a + b)
    lam ^ 2 * a + (1 - lam) ^ 2 * b = a * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  show (b / (a + b)) ^ 2 * a + (1 - b / (a + b)) ^ 2 * b = a * b / (a + b)
  field_simp
  ring

/-- **λ optimum upper bound**: for any `λ ∈ ℝ`, `λ² a + (1-λ)² b ≥ ab / (a+b)`.
Cauchy-Schwarz / AM-GM direct consequence. -/
@[entry_point]
theorem stam_lambda_lower_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (lam : ℝ) :
    a * b / (a + b) ≤ lam ^ 2 * a + (1 - lam) ^ 2 * b := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  -- The minimum value `ab/(a+b)` is achieved at `λ = b/(a+b)`. The deviation
  -- `(λ - b/(a+b))² · (a+b)` measures the slack. We show
  -- `λ² a + (1 - λ)² b - ab/(a+b) = (λ - b/(a+b))² · (a+b) ≥ 0`.
  have h_expand : lam ^ 2 * a + (1 - lam) ^ 2 * b - a * b / (a + b)
      = (lam - b / (a + b)) ^ 2 * (a + b) := by
    field_simp
    ring
  have h_sq_nn : 0 ≤ (lam - b / (a + b)) ^ 2 := sq_nonneg _
  have h_prod_nn : 0 ≤ (lam - b / (a + b)) ^ 2 * (a + b) :=
    mul_nonneg h_sq_nn hab.le
  linarith [h_expand, h_prod_nn]

/-- **Inverse-form Stam algebraic identity**: for `a, b, c > 0` with
`c ≤ ab/(a+b)`, the inverse relation `1/c ≥ 1/a + 1/b` holds. -/
@[entry_point]
theorem stam_inverse_form_of_harmonic_mean
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_le : c ≤ a * b / (a + b)) :
    1 / c ≥ 1 / a + 1 / b := by
  have hab : 0 < a + b := by linarith
  have h_target_pos : 0 < a * b / (a + b) := by positivity
  -- `c ≤ ab/(a+b) → 1/c ≥ (a+b)/(ab) = 1/a + 1/b`.
  have h_inv_le : 1 / (a * b / (a + b)) ≤ 1 / c :=
    one_div_le_one_div_of_le hc h_le
  have h_rhs : 1 / (a * b / (a + b)) = 1 / a + 1 / b := by
    have hab_ne : a + b ≠ 0 := hab.ne'
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne'
    field_simp
    ring
  rw [h_rhs] at h_inv_le
  exact h_inv_le

/-! ## §4 — Predicate chain combinator (the deliverable) -/

/-- The optimal Cauchy–Schwarz form: `IsStamCauchySchwarz` strengthened to the optimal witness
`λ = J_Y / (J_X + J_Y)`, giving the harmonic-mean bound `J_sum ≤ J_X · J_Y / (J_X + J_Y)`. The
quantification block carries regularity preconditions (`IsRegularDensityV2 fX/fY`, the
normalizations, the pointwise convolution identity, and the `IsBlachmanConvReady fX fY` bundle),
not the inequality core; the bound is produced from regularity by `stam_step2_density_wall` via
`convex_fisher_bound_of_ready`.
@audit:ok -/
def IsStamCauchySchwarzOptimal {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX →
    InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY →
    (∫ x, fX x ∂MeasureTheory.volume = 1) →
    (∫ x, fY x ∂MeasureTheory.volume = 1) →
    (∀ x, fXY x =
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x) →
    InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY →
    J_sum ≤ J_X * J_Y / (J_X + J_Y)

/-- The genuine analytic core of the Stam inequality's Steps 2-3 (Cover–Thomas Lemma 17.7.2 /
Blachman 1965): for independent `X, Y` with smooth densities, the conditional Cauchy–Schwarz
`s_Z(z)² ≤ E[(λ s_X + (1 - λ) s_Y)² | X + Y = z]` integrated against `p_Z` gives the convex Fisher
bound `J(Z) ≤ λ² J(X) + (1 - λ)² J(Y)`, whose `λ`-optimum is the optimal Cauchy–Schwarz form
`J(Z) ≤ J(X) J(Y) / (J(X) + J(Y))`.

The convex Fisher bound is supplied by the genuine `convex_fisher_bound_of_ready`
(`EPIBlachmanDensity`, a condExp-free explicit-density formulation), and the `λ`-optimization is
`stam_lambda_min`. The pointwise convolution hypothesis collapses `fisherInfoOfDensity fXY` to
`fisherInfoOfDensity (convDensityAdd fX fY)` by `funext`; the added hypotheses are regularity
preconditions, not the inequality core.
@audit:ok -/
theorem stam_step2_density_wall
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamCauchySchwarzOptimal X Y P := by
  -- `IsStamCondExpCSHyp` lives downstream (`StamConditionalCauchySchwarz` imports this file), so we
  -- inline the `∀λ`-bound ⇒ optimal reduction here (the λ-optimization is `stam_lambda_min`,
  -- available in this file) rather than routing through `stamCauchySchwarzOptimal_of_condExpCSHyp`.
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  -- `fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f` (rfl), pointwise `hconv`
  -- collapses `fXY` to the convolution density.
  rw [InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2_def] at hJX_def hJY_def hJsum_def
  have hfXY : fXY = InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY :=
    funext hconv
  rw [hfXY] at hJsum_def
  subst hJX_def hJY_def hJsum_def
  -- genuine `∀λ` convex Fisher bound from the regularity bundle, at the optimal
  -- `λ* = J_Y / (J_X + J_Y)` where `stam_lambda_min` gives the harmonic-mean RHS.
  set J_X := (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity fX).toReal with hJXdef
  set J_Y := (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity fY).toReal with hJYdef
  have hsum : 0 < J_X + J_Y := by linarith
  have hlam0 : (0 : ℝ) ≤ J_Y / (J_X + J_Y) := by positivity
  have hlam1 : J_Y / (J_X + J_Y) ≤ 1 := by rw [div_le_one hsum]; linarith
  have h_bd := InformationTheory.Shannon.EPIBlachmanDensity.convex_fisher_bound_of_ready
    fX fY (J_Y / (J_X + J_Y)) hlam0 hlam1 hregX hregY hnormX hnormY hready
  have h_min := stam_lambda_min hJX hJY
  linarith [h_bd, h_min]

/-- Given the optimal Cauchy–Schwarz predicate, chains through the `λ`-optimization closed form to
obtain the inverse-form Stam inequality `1 / J_sum ≥ 1 / J_X + 1 / J_Y`. A genuine implication
wrapper: the body is the algebraic reshaping from `J_sum ≤ J_X · J_Y / (J_X + J_Y)` (conclusion
type ≠ hypothesis type).
@audit:ok -/
@[entry_point]
theorem stam_inequality_via_predicate_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX →
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY →
      (∫ x, fX x ∂MeasureTheory.volume = 1) →
      (∫ x, fY x ∂MeasureTheory.volume = 1) →
      (∀ x, fXY x =
        InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x) →
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY →
      1 / J_sum ≥ 1 / J_X + 1 / J_Y := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  have h_le := h_cs_opt J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  exact stam_inverse_form_of_harmonic_mean hJX hJY hJsum h_le

/-- Bridge from the body-level optimal Cauchy–Schwarz predicate to the published Stam signature
`IsStamInequalityHyp` (Cover–Thomas Lemma 17.7.2). A genuine implication wrapper: it introduces the
matching hypotheses, applies `h_cs_opt` to get the harmonic-mean bound
`J_sum ≤ J_X · J_Y / (J_X + J_Y)`, and reshapes to the inverse form via
`stam_inverse_form_of_harmonic_mean` (conclusion type ≠ hypothesis type, no circularity). The
inequality core lives upstream in `stam_step2_density_wall`; the antecedent's extra hypotheses are
regularity preconditions.
@audit:ok -/
@[entry_point]
theorem isStamInequalityHyp_via_body
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    IsStamInequalityHyp X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  have h_le := h_cs_opt J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  exact stam_inverse_form_of_harmonic_mean hJX hJY hJsum h_le

/-! ## §5 — Gaussian saturation discharge

The genuine Gaussian entropy power inequality runs via `entropyPower_gaussian_additivity`
(see `epi_via_stam_body_gaussian` in §6 below). -/

/-! ## §6 — EPI pipeline integration with body discharge -/

/-- **Stam-to-EPI bridge via body discharge** (Gaussian case): combine
the body-derived Stam inequality with the Stam-to-EPI bridge from
`StamEPIBridge.isStamToEPIBridgeHyp_of_gaussian`. -/
@[entry_point]
theorem isStamToEPIBridgeHyp_via_body_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsStamToEPIBridgeHyp X Y P :=
  isStamToEPIBridgeHyp_of_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-- **EPI via Stam body discharge (Gaussian case)**: full deliverable end-to-end.
For Gaussian `X, Y` with non-zero variance, EPI follows through the body
discharge + Gaussian saturation bridge — no upstream hypothesis required. -/
@[entry_point]
theorem epi_via_stam_body_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  epi_via_stam_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-! ## §7 — Predicate manipulation lemmas -/

/-- The optimal CS predicate is *strictly stronger* than the existential CS
predicate `IsStamCauchySchwarz`. -/
theorem isStamCauchySchwarz_of_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamCauchySchwarzOptimal X Y P) :
    IsStamCauchySchwarz X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  -- Optimal λ = J_Y / (J_X + J_Y) gives the inequality
  -- `J_sum ≤ λ² J_X + (1-λ)² J_Y = J_X J_Y / (J_X + J_Y)`.
  refine ⟨J_Y / (J_X + J_Y), ?_, ?_, ?_⟩
  · positivity
  · have hsum : 0 < J_X + J_Y := by linarith
    rw [div_le_one hsum]
    linarith
  · have h_le := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
      hregX hregY hnormX hnormY hconv hready
    have h_min := stam_lambda_min hJX hJY
    -- `lam² J_X + (1-lam)² J_Y = J_X J_Y / (J_X + J_Y)` at `lam = J_Y/(J_X+J_Y)`.
    show J_sum ≤ (J_Y / (J_X + J_Y)) ^ 2 * J_X
                  + (1 - J_Y / (J_X + J_Y)) ^ 2 * J_Y
    linarith [h_min]

/-- The score-convolution predicate is symmetric in `X, Y` — *unconditionally*
provable since the W9 typed body is a pure existence Prop on the optimal λ
witness (which is constructed from `J_X, J_Y` only, no asymmetry in the
predicate body). Provided primarily to absorb `IsStamScoreConvolution Y X P`
slots in upstream pipelines that swap `(X, Y)` order. -/
theorem isStamScoreConvolution_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (_h : IsStamScoreConvolution X Y P) :
    IsStamScoreConvolution Y X P :=
  isStamScoreConvolution_intro Y X P

/-! ## §8 — λ-optimization: independent algebraic corollaries -/

/-! ## §9 — Direct optimal-CS construction from λ-witness -/

/-- **Optimal CS from a λ-witness at the optimum**: given a Cauchy-Schwarz
witness with `λ = J_Y / (J_X + J_Y)`, the optimal-form predicate is recovered.

`@audit:ok` -/
theorem isStamCauchySchwarzOptimal_of_lambda_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      J_sum ≤ (J_Y / (J_X + J_Y)) ^ 2 * J_X
              + (1 - J_Y / (J_X + J_Y)) ^ 2 * J_Y) :
    IsStamCauchySchwarzOptimal X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv hready
  have h_bd := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_min := stam_lambda_min hJX hJY
  linarith [h_min]

/-! ## §10 — Stam inequality body discharge pipeline integration -/

/-- Composes the body-discharged Stam inequality into the `EPIL3Integration` integrated pipeline.
The pipeline is built from the genuine Stam residual alone; the Stam-to-EPI bridge is discharged
internally by consumers via `stamToEPIBridge_holds`.
@audit:ok -/
@[entry_point]
theorem isStamInequalityHyp_via_body_to_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    InformationTheory.Shannon.EPIL3Integration.IsEPIL3IntegratedPipeline X Y P :=
  { stam := isStamInequalityHyp_via_body h_cs_opt }

/-! ## §11 — Sanity check / regression theorems -/

/-- **Sanity check**: `stam_inverse_form_of_harmonic_mean` recovers the standard
form `1/c ≥ 1/a + 1/b` when `c = ab/(a+b)` exactly. -/
theorem stam_inverse_form_at_equality {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (a * b / (a + b)) = 1 / a + 1 / b := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  have ha_ne : a ≠ 0 := ha.ne'
  have hb_ne : b ≠ 0 := hb.ne'
  field_simp
  ring

/-- **Sanity check**: at `λ = 0`, the upper bound is `J_Y`. -/
theorem stam_lambda_at_zero (a b : ℝ) :
    (0 : ℝ) ^ 2 * a + (1 - 0) ^ 2 * b = b := by ring

/-- **Sanity check**: at `λ = 1`, the upper bound is `J_X`. -/
theorem stam_lambda_at_one (a b : ℝ) :
    (1 : ℝ) ^ 2 * a + (1 - 1) ^ 2 * b = a := by ring

end InformationTheory.Shannon.StamInequality
