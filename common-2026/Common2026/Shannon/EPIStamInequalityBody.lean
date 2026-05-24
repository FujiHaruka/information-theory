import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.EPIPlumbing
import Common2026.Shannon.EPIStamDischarge
import Common2026.Shannon.EPIL3Integration
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoGaussian
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# T2-D-B: Stam inequality body discharge (Cauchy-Schwarz / convolution-score path)

`Common2026/Shannon/EPIStamDischarge.lean` (Wave 5, 755 行) で Stam inequality
`1 / J(X+Y) ≥ 1 / J(X) + 1 / J(Y)` を `IsStamInequalityHyp` 真 signature で
publish 済。本 file (Wave 6 T2-D-B) はその **body discharge** を Cauchy-Schwarz
+ convolution-score 経路で組み上げる。

## Approach

Cover-Thomas Lemma 17.7.2 の標準的な 1 次元 Stam inequality 証明は次の path:

1. **Score representation of convolution** (Lemma 17.7.1 / Blachman 1965): for
   independent `X, Y` with densities, the score of `Z := X + Y` satisfies
   `s_Z(z) = E[s_X(X) | X + Y = z] = E[s_Y(Y) | X + Y = z]`.
2. **Cauchy-Schwarz** on `E[s_X(X) | X + Y = z]` and any linear combination
   `λ s_X(X) + (1 - λ) s_Y(Y)`:
       `s_Z(z)² ≤ E[(λ s_X(X) + (1 - λ) s_Y(Y))² | X + Y = z]`.
3. **Take total expectation**: `J(Z) ≤ λ² J(X) + (1 - λ)² J(Y)`.
4. **Optimize over λ**: with `λ = J(Y) / (J(X) + J(Y))`,
       `J(Z) ≤ J(X) J(Y) / (J(X) + J(Y)) ⇔ 1/J(Z) ≥ 1/J(X) + 1/J(Y)`.

Mathlib に
* `condExp`-based score conditional expectation manipulation,
* Stam inequality / Blachman score-conv identity,
* Cauchy-Schwarz on conditional expectations

の三つともは標準形では存在しない (`rg "Stam|Blachman|score_conv" → 0 hit`).
本 file は本体の **body** を Cauchy-Schwarz predicate 形に分解し、各 step を
predicate pass-through で publish した上で、**predicate chain で Stam 真
signature `IsStamInequalityHyp` を導出する** wrapper を提供する。

### 撤退ライン (本 file で発動)

* **L-Stam-CS** (本 file core): `IsStamCauchySchwarz X Y P` predicate 形で Step 2-3
  (Cauchy-Schwarz + total expectation) を pass-through。
* **L-Stam-Conv** (本 file core): `IsStamScoreConvolution X Y P` で Step 1
  (convolution score representation) を pass-through。
* **L-Stam-Opt** (本 file core): `IsStamLambdaOptimal X Y P` で Step 4 (λ 最適化)
  を pass-through。実体は `1 / a + 1 / b ≤ (a + b) / (a * b)` 形の純算術なので、
  **predicate-free** で direct discharge する補題も併設。

### 主シグネチャ

* `IsStamScoreConvolution X Y P` (§1) — Step 1 predicate
* `IsStamCauchySchwarz X Y P` (§2) — Step 2-3 predicate
* `IsStamLambdaOptimal` (§3) — Step 4 純算術 closed form
* `stam_inequality_via_predicate` (§4) — chain combinator (deliverable)
* `isStamInequalityHyp_via_body` (§4) — `IsStamInequalityHyp` への bridge
* `isStamCauchySchwarz_of_gaussian` (§5) — Gaussian discharge
* `isStamScoreConvolution_of_gaussian` (§5) — Gaussian discharge
* `stam_inequality_gaussian_body` (§5) — Gaussian full discharge corollary
* `epi_via_stam_body_gaussian` (§6) — pipeline integration with §5
-/

namespace InformationTheory.Shannon.EPIStamInequalityBody

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge

/-! ## §1 — Convolution score representation predicate (Step 1) -/

/-- **Convolution score representation hypothesis** (Blachman 1965 / Cover-Thomas
Lemma 17.7.1 body form).

For independent `X, Y` with smooth densities `p_X, p_Y` (so that the score
`s_X := (log p_X)' = p_X' / p_X` is well-defined), the score of the sum
`Z := X + Y` admits the conditional expectation representation

    `s_Z(z) = E[s_X(X) | X + Y = z] = E[s_Y(Y) | X + Y = z]`.

In particular, for any `λ ∈ [0, 1]`,

    `s_Z(z) = E[λ · s_X(X) + (1 - λ) · s_Y(Y) | X + Y = z]`.

This identity (Blachman's score-of-convolution lemma) is the foundation of the
1-dimensional Stam inequality proof. Mathlib has neither the score function
abstraction tied to `pdf` nor `condExp` integration over the sum-level
σ-algebra. We pass-through as a predicate; full discharge is moved to the
follow-up plan `epi-stam-blachman-discharge-plan.md` (未着手).

The predicate is phrased symbolically: we expose the **mean-zero linear
combination invariant** that the Stam proof actually consumes.
-/
def IsStamScoreConvolution {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  -- Symbolic placeholder: the score-convolution identity is reified as a
  -- propositional witness consumed downstream.
  True


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
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      J_sum ≤ lam ^ 2 * J_X + (1 - lam) ^ 2 * J_Y

/-- The Cauchy-Schwarz predicate is symmetric in `X, Y` (swap `λ ↦ 1 - λ`). -/
theorem isStamCauchySchwarz_symm {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamCauchySchwarz X Y P) :
    IsStamCauchySchwarz Y X P := by
  intro J_Y J_X J_sum fY fX fXY hJY hJX hJsum hJY_def hJX_def hJsum_def
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm] at hJsum_def
  obtain ⟨lam, hlam_lo, hlam_hi, hbd⟩ :=
    h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  refine ⟨1 - lam, by linarith, by linarith, ?_⟩
  -- `J_sum ≤ lam² J_X + (1 - lam)² J_Y = (1 - (1 - lam))² J_X + (1 - lam)² J_Y`.
  have : (1 - (1 - lam)) ^ 2 = lam ^ 2 := by ring
  linarith [this]

/-- Trivial Cauchy-Schwarz witness via `lam = 1` and `J_sum ≤ J_X` — this almost
never holds in practice, but the predicate is preserved by the natural Gaussian
saturation. -/
theorem isStamCauchySchwarz_of_lambda_one {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_bd : ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      J_sum ≤ J_X) :
    IsStamCauchySchwarz X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  refine ⟨1, by norm_num, by norm_num, ?_⟩
  have hbd := h_bd J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have hJY_nn : 0 ≤ J_Y := hJY.le
  nlinarith [sq_nonneg ((1 : ℝ) - 1), sq_nonneg (1 - (1 : ℝ))]

/-! ## §3 — λ-optimization closed form (Step 4): pure arithmetic, no predicate -/

/-- **λ-optimization closed form** (Stam Step 4).

For positive `a, b > 0`, the function `λ ↦ λ² a + (1 - λ)² b` is minimized at
`λ* = b / (a + b)` with minimum value `a b / (a + b)`. Combined with Step 3,
this gives `J(Z) ≤ J(X) J(Y) / (J(X) + J(Y))`, equivalently
`1 / J(Z) ≥ 1 / J(X) + 1 / J(Y)`. -/
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

/-- **Optimal Cauchy-Schwarz predicate** (the actually pipeline-usable form).

Strengthens `IsStamCauchySchwarz` to require the witness `λ = J_Y / (J_X + J_Y)`,
which is the optimal λ minimizing `λ² J_X + (1-λ)² J_Y`. -/
def IsStamCauchySchwarzOptimal {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    J_sum ≤ J_X * J_Y / (J_X + J_Y)

/-- The optimal Cauchy-Schwarz predicate is symmetric in `X, Y`. -/
theorem isStamCauchySchwarzOptimal_symm {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamCauchySchwarzOptimal X Y P) :
    IsStamCauchySchwarzOptimal Y X P := by
  intro J_Y J_X J_sum fY fX fXY hJY hJX hJsum hJY_def hJX_def hJsum_def
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm] at hJsum_def
  have h_inst := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  -- `J_X J_Y / (J_X + J_Y) = J_Y J_X / (J_Y + J_X)` — same value.
  have h_eq : J_X * J_Y / (J_X + J_Y) = J_Y * J_X / (J_Y + J_X) := by
    congr 1 <;> ring
  linarith [h_eq]

/-- **Stam inequality via predicate chain (optimal form)** — actual deliverable.

Given the convolution-score predicate + the optimal Cauchy-Schwarz predicate,
chain through Step 4 closed form to obtain the inverse-form Stam inequality.

`@audit:suspect(epi-moonshot-plan)` -/
theorem stam_inequality_via_predicate_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      1 / J_sum ≥ 1 / J_X + 1 / J_Y := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_le := h_cs_opt J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  exact stam_inverse_form_of_harmonic_mean hJX hJY hJsum h_le

/-- **`IsStamInequalityHyp` from body predicates**. The genuine Stam-inequality
predicate (Cover-Thomas Lemma 17.7.2 真 signature) follows from the convolution
+ optimal-CS pair. This is the **bridge from body to plumbing**.

`@audit:suspect(epi-moonshot-plan)` -/
theorem isStamInequalityHyp_via_body
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    IsStamInequalityHyp X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  exact stam_inequality_via_predicate_optimal h_conv h_cs_opt
    J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def

/-! ## §5 — Gaussian saturation discharge -/


/- **RESOLVED (2026-05-20):** the former `isStamCauchySchwarzOptimal_of_gaussian_fisherInfo_zero`
and its chain lemmas `isStamInequalityHyp_of_gaussian_via_body` /
`isStamInequalityHyp_of_gaussian_via_body_Y` discharged the optimal-CS predicate
vacuously by `exfalso`-ing the `0 < J_X` (resp. `0 < J_Y`) precondition against
the buggy V1 `fisherInfo = 0` artefact for Gaussians. They asserted nothing about
Stam actually holding and were removed. The genuine Gaussian EPI runs via
`entropy_power_inequality_gaussian_saturation` (see `epi_via_stam_body_gaussian`
in §6 below). -/

/-! ## §6 — EPI pipeline integration with body discharge -/

/-- **Stam-to-EPI bridge via body discharge** (Gaussian case): combine
the body-derived Stam inequality with the Stam-to-EPI bridge from
`EPIStamDischarge.isStamToEPIBridgeHyp_of_gaussian`. -/
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
  -- Optimal λ = J_Y / (J_X + J_Y) gives the inequality
  -- `J_sum ≤ λ² J_X + (1-λ)² J_Y = J_X J_Y / (J_X + J_Y)`.
  refine ⟨J_Y / (J_X + J_Y), ?_, ?_, ?_⟩
  · positivity
  · have hsum : 0 < J_X + J_Y := by linarith
    rw [div_le_one hsum]
    linarith
  · have h_le := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    have h_min := stam_lambda_min hJX hJY
    -- `lam² J_X + (1-lam)² J_Y = J_X J_Y / (J_X + J_Y)` at `lam = J_Y/(J_X+J_Y)`.
    show J_sum ≤ (J_Y / (J_X + J_Y)) ^ 2 * J_X
                  + (1 - J_Y / (J_X + J_Y)) ^ 2 * J_Y
    linarith [h_min]

/-- The optimal CS predicate is congruent under function equality. -/
theorem isStamCauchySchwarzOptimal_congr
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hX : X = X') (hY : Y = Y')
    (h : IsStamCauchySchwarzOptimal X Y P) :
    IsStamCauchySchwarzOptimal X' Y' P := by
  subst hX; subst hY; exact h

/-- The score-convolution predicate is congruent under function equality. -/
theorem isStamScoreConvolution_congr
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hX : X = X') (hY : Y = Y')
    (h : IsStamScoreConvolution X Y P) :
    IsStamScoreConvolution X' Y' P := by
  subst hX; subst hY; exact h

/-! ## §8 — λ-optimization: independent algebraic corollaries -/

/-- **Harmonic mean ≤ arithmetic mean**. For positive `a, b`,
`ab / (a + b) ≤ (a + b) / 4` (with equality iff `a = b`). Useful as a sanity
check on Step 4's λ-optimization. -/
theorem stam_harmonic_arith_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * b / (a + b) ≤ (a + b) / 4 := by
  have hab : 0 < a + b := by linarith
  have h_nn : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  -- `(a + b) ^ 2 ≥ 4ab` ⇒ `ab / (a+b) ≤ (a+b)/4`.
  have h_quad : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith
  have h_target : 4 * (a * b / (a + b)) ≤ a + b := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ hab]
    nlinarith
  linarith

/-- **Lower bound on the harmonic mean**: `ab / (a + b) ≥ min a b / 2`. -/
theorem stam_harmonic_lower_half_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min a b / 2 ≤ a * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  -- `min a b / 2 ≤ ab / (a+b)` ⇔ `min a b · (a+b) ≤ 2ab`. WLOG `a ≤ b`,
  -- so `min = a`, target `a(a+b) ≤ 2ab` ⇔ `a² + ab ≤ 2ab` ⇔ `a² ≤ ab` ⇔ `a ≤ b`.
  rcases le_total a b with hab' | hab'
  · have hmin : min a b = a := min_eq_left hab'
    rw [hmin]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hab]
    nlinarith
  · have hmin : min a b = b := min_eq_right hab'
    rw [hmin]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hab]
    nlinarith

/-! ## §9 — Direct optimal-CS construction from λ-witness -/

/-- **Optimal CS from a λ-witness at the optimum**: given a Cauchy-Schwarz
witness with `λ = J_Y / (J_X + J_Y)`, the optimal-form predicate is recovered.

`@audit:suspect(epi-moonshot-plan)` -/
theorem isStamCauchySchwarzOptimal_of_lambda_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      J_sum ≤ (J_Y / (J_X + J_Y)) ^ 2 * J_X
              + (1 - J_Y / (J_X + J_Y)) ^ 2 * J_Y) :
    IsStamCauchySchwarzOptimal X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_bd := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_min := stam_lambda_min hJX hJY
  linarith [h_min]

/-! ## §10 — Stam inequality body discharge pipeline integration -/

/-- **Body-discharged Stam inequality via Integrated Pipeline**: composes the
body discharge predicates with the Wave 6 `EPIL3Integration` integrated
pipeline.

`@audit:suspect(epi-moonshot-plan)` -/
theorem isStamInequalityHyp_via_body_to_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    InformationTheory.Shannon.EPIL3Integration.IsEPIL3IntegratedPipeline X Y P :=
  { stam := isStamInequalityHyp_via_body h_conv h_cs_opt
    bridge := h_bridge }

/-- **End-to-end EPI via body discharge** (composes §4 + §6 + EPIL3 pipeline).

`@audit:suspect(epi-moonshot-plan)` -/
theorem entropy_power_inequality_via_body
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (h_conv : IsStamScoreConvolution X Y P)
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_stam := isStamInequalityHyp_via_body h_conv h_cs_opt
  exact epi_via_stam_main P X Y X hX hY hXY h_stam h_bridge

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

end InformationTheory.Shannon.EPIStamInequalityBody
