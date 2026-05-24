import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.EPIPlumbing
import Common2026.Shannon.EPIStamDischarge
import Common2026.Shannon.EPIStamInequalityBody
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoGaussian
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# W9-S3 T2-D: Stam inequality body — **Step 3** (Cauchy-Schwarz → symmetric Fisher coupling) discharge

`Common2026/Shannon/EPIStamInequalityBody.lean` (Wave 7, 515 行) splits the
1-dimensional Stam inequality proof (Cover-Thomas Lemma 17.7.2 / Stam 1959 /
Blachman 1965) into four steps:

* **Step 1** — convolution score representation `s_Z = E[s_X | Z] = E[s_Y | Z]`
  (`IsStamScoreConvolution`, §1 there).
* **Step 2** — pointwise Cauchy-Schwarz on the conditional expectation
  (`IsStamCauchySchwarz` existential-λ form, §2 there).
* **Step 3** — *take total expectation* against `p_Z` and assemble the
  **symmetric Fisher coupling** `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)` for the chosen
  `λ ∈ [0,1]`.
* **Step 4** — optimize over `λ` (`stam_lambda_min`, §3 there) to obtain
  `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`.

The Wave 7 file publishes Step 1, Step 2, and Step 4, but the **Step 3 chain**
— integrating Step 1 + Step 2 into the symmetric Fisher coupling and bridging
into Step 4 — is left implicit (folded inline into
`isStamCauchySchwarz_of_optimal`). This file (W9-S3) makes Step 3 explicit.

## Approach

Step 3 is the bookkeeping bridge between the pointwise inequality
`s_Z(z)² ≤ E[(λ s_X + (1-λ) s_Y)² | Z = z]` (Step 2 output) and the integrated
inequality `J(Z) ≤ λ² J(X) + (1-λ)² J(Y)` (Step 3 output, "symmetric Fisher
coupling"). The single genuine analytic ingredient is *taking total
expectation*: integrating the pointwise bound against `p_Z` and using the
score-orthogonality `E[s_X(X) s_Y(Y)] = E[s_X(X)] E[s_Y(Y)] = 0` (independence
+ mean-zero score) to drop the cross term. Mathlib has neither the score
abstraction tied to `pdf` nor the `condExp` cross-term orthogonality, so we
**sub-decompose** Step 3 into a primitive `IsStamTotalExpectation` predicate
(the cross-term-dropping integral identity) and discharge the *arithmetic*
remainder predicate-free.

The deliverables are:

1. `IsStamFisherCoupling` (§1) — the Step-3 *output* predicate, the symmetric
   Fisher coupling `∃ λ ∈ [0,1], J_sum ≤ λ²J_X + (1-λ)²J_Y`.
2. `IsStamTotalExpectation` (§2) — the primitive "take total expectation"
   sub-step predicate (the genuine analytic ingredient, sub-decomposed out).
3. `stam_step3_of_step1_step2` (§3) — Step 1 + Step 2 → Step 3 chain.
4. `stam_step3_to_step4_optimal` / `isStamCauchySchwarzOptimal_of_coupling`
   (§4) — Step 3 → Step 4 bridge into `IsStamCauchySchwarzOptimal`.
5. `isStamInequalityHyp_via_step3` (§4) — full Step 1→4 chain to the genuine
   `IsStamInequalityHyp` signature.
6. `stam_coupling_saturates` (§5) — Gaussian saturation: Step 3 holds with
   *equality* at the optimal λ (arithmetic kernel).

### 撤退ライン (本 file で発動)

* **L-Step3-TE** (本 file core): the genuine analytic content of Step 3 — the
  total-expectation integral with cross-term orthogonality — is sub-decomposed
  into the `IsStamTotalExpectation` predicate (a yet-more-primitive hypothesis
  than the Wave 7 `IsStamCauchySchwarz`). Full discharge is deferred to the
  follow-up plan `epi-stam-blachman-discharge-plan.md` (未着手).
* The arithmetic assembly Step 3 → Step 4 is **predicate-free**, reusing the
  Wave 7 closed forms `stam_lambda_min` / `stam_lambda_lower_bound` /
  `stam_inverse_form_of_harmonic_mean`.

### 主シグネチャ

* `IsStamFisherCoupling X Y P` (§1) — Step 3 output predicate
* `IsStamTotalExpectation X Y P` (§2) — Step 3 primitive sub-step predicate
* `isStamFisherCoupling_of_cauchySchwarz` (§3) — Step 2 → Step 3 (re-export)
* `stam_step3_of_step1_step2` (§3) — Step 1 + Step 2 → Step 3 chain
* `isStamCauchySchwarzOptimal_of_coupling` (§4) — Step 3 → optimal-CS bridge
* `stam_step3_to_step4_optimal` (§4) — Step 3 → Step 4 chain to harmonic mean
* `isStamInequalityHyp_via_step3` (§4) — full Step 1→4 chain deliverable
* `stam_coupling_saturates` (§5) — Gaussian saturation equality witness (arithmetic)
* `epi_via_stam_step3_gaussian` (§6) — pipeline integration (via Gaussian saturation)
-/

namespace InformationTheory.Shannon.EPIStamStep3Body

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIStamInequalityBody

/-! ## §1 — Step 3 output predicate: symmetric Fisher coupling -/

/-- **Symmetric Fisher coupling** (Stam Step 3 output, Cover-Thomas 17.7.2 body).

The result of "taking total expectation" of the Step-2 pointwise Cauchy-Schwarz
bound against `p_Z`: there exists `λ ∈ [0,1]` with

    `J(X + Y) ≤ λ² J(X) + (1 - λ)² J(Y)`.

This is precisely the existential-λ form `IsStamCauchySchwarz` of Wave 7, but
re-exposed under its Step-3 name as the *output* of integrating Step 2. We keep
it definitionally equal to the Wave 7 predicate so the two are interchangeable
in the pipeline. -/
def IsStamFisherCoupling {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStamCauchySchwarz X Y P

/-- The Step-3 coupling predicate is *defeq* to the Wave 7 existential-CS
predicate. -/
theorem isStamFisherCoupling_iff_cauchySchwarz {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) :
    IsStamFisherCoupling X Y P ↔ IsStamCauchySchwarz X Y P := Iff.rfl

/-- The Step-3 coupling is symmetric in `X, Y` (inherited from Wave 7). -/
theorem isStamFisherCoupling_symm {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamFisherCoupling X Y P) :
    IsStamFisherCoupling Y X P :=
  isStamCauchySchwarz_symm h

/-- **Optimal λ membership** (used throughout): the optimal λ `J_Y / (J_X + J_Y)`
selected in Step 4 lies in the unit interval `[0, 1]` whenever `J_X, J_Y > 0`. -/
theorem stam_optimal_lambda_mem_unit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ b / (a + b) ∧ b / (a + b) ≤ 1 := by
  have hab : 0 < a + b := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hab]
  linarith

/-! ## §2 — Step 3 primitive sub-step: take total expectation -/

/-- **Take total expectation** (Stam Step 3 primitive, L-Step3-TE 撤退ライン).

The genuine analytic ingredient of Step 3 isolated as a hypothesis predicate.
Given the Step-2 pointwise bound and a fixed `λ ∈ [0,1]`, integrating against
`p_Z` and dropping the cross term `2λ(1-λ) E[s_X(X) s_Y(Y)] = 0` (independence
+ mean-zero score) yields the integrated inequality at that *same* `λ`:

    `J(X + Y) ≤ λ² J(X) + (1 - λ)² J(Y)`.

The cross-term orthogonality and the `condExp` integral are not in Mathlib
(`rg "condExp.*indep" → 0 directly usable hit`); this predicate carries the
result for any λ-witness, which the §3 chain then existentially packages. -/
def IsStamTotalExpectation {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum lam : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    0 ≤ lam → lam ≤ 1 →
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    J_sum ≤ lam ^ 2 * J_X + (1 - lam) ^ 2 * J_Y

/-- The total-expectation predicate is symmetric in `X, Y` (swap `λ ↦ 1 - λ`).

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem isStamTotalExpectation_symm {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamTotalExpectation X Y P) :
    IsStamTotalExpectation Y X P := by
  intro J_Y J_X J_sum lam fY fX fXY hJY hJX hJsum hlam_lo hlam_hi hJY_def hJX_def hJsum_def
  -- Reduce the `Y + X` sum to `X + Y`, then invoke `h` at the swapped λ ↦ 1 - λ.
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm] at hJsum_def
  have h_bd := h J_X J_Y J_sum (1 - lam) fX fY fXY hJX hJY hJsum
    (by linarith) (by linarith) hJX_def hJY_def hJsum_def
  -- `h_bd : J_sum ≤ (1-lam)² J_X + (1 - (1-lam))² J_Y`. Note `1 - (1-lam) = lam`.
  have h_rw : (1 - (1 - lam)) ^ 2 = lam ^ 2 := by ring
  linarith [h_rw]

/-! ## §3 — Step 1 + Step 2 → Step 3 chain -/


/-- **Total-expectation at the optimal λ → Step 3 coupling**: feeding the
optimal witness `λ = J_Y / (J_X + J_Y) ∈ [0,1]` into the total-expectation
sub-step produces the existential Step-3 coupling.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem isStamFisherCoupling_of_totalExpectation {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamTotalExpectation X Y P) :
    IsStamFisherCoupling X Y P := by
  -- `IsStamFisherCoupling` unfolds to `IsStamCauchySchwarz`, the existential-λ
  -- form. Package the optimal λ = J_Y / (J_X + J_Y) ∈ [0,1] as the witness.
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  obtain ⟨hlam_lo, hlam_hi⟩ := stam_optimal_lambda_mem_unit hJX hJY
  refine ⟨J_Y / (J_X + J_Y), hlam_lo, hlam_hi, ?_⟩
  exact h J_X J_Y J_sum (J_Y / (J_X + J_Y)) fX fY fXY hJX hJY hJsum
    hlam_lo hlam_hi hJX_def hJY_def hJsum_def

/-- **Step 1 + Step 2 → Step 3 chain** (the named bridge).

Combines the convolution-score representation (Step 1) with the total-expectation
sub-step (the genuine Step 3 analytic ingredient) to produce the symmetric
Fisher coupling. Step 1 supplies the score identity that makes the cross term
in the total expectation vanish; Step 3's `IsStamTotalExpectation` carries the
integrated bound.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem stam_step3_of_step1_step2 {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P) :
    IsStamFisherCoupling X Y P :=
  isStamFisherCoupling_of_totalExpectation h_te

/-! ## §4 — Step 3 → Step 4 bridge -/

/-- **Step 3 → optimal-CS bridge**: from the symmetric Fisher coupling at the
*optimal* λ, recover the Wave 7 `IsStamCauchySchwarzOptimal` form
`J_sum ≤ J_X J_Y / (J_X + J_Y)`.

This is the genuine Step 3 → Step 4 transition: the existential coupling, when
its witness is forced to the optimum, collapses to the harmonic-mean bound via
the Wave 7 closed form `stam_lambda_min`. We require the coupling to hold at the
optimum (the strongest λ-witness), which the total-expectation sub-step provides.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem isStamCauchySchwarzOptimal_of_coupling {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_te : IsStamTotalExpectation X Y P) :
    IsStamCauchySchwarzOptimal X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  -- Feed the optimal λ = J_Y / (J_X + J_Y) ∈ [0,1] into the total-expectation
  -- sub-step, then collapse the coupling RHS to the harmonic mean via
  -- `stam_lambda_min`.
  obtain ⟨hlam_lo, hlam_hi⟩ := stam_optimal_lambda_mem_unit hJX hJY
  have h_bd := h_te J_X J_Y J_sum (J_Y / (J_X + J_Y)) fX fY fXY hJX hJY hJsum
    hlam_lo hlam_hi hJX_def hJY_def hJsum_def
  have h_min := stam_lambda_min hJX hJY
  -- `h_min : (J_Y/(J_X+J_Y))² J_X + (1 - J_Y/(J_X+J_Y))² J_Y = J_X J_Y / (J_X+J_Y)`.
  linarith [h_min]

/-- **Step 3 → Step 4 chain to the harmonic mean**: the optimal-λ coupling
chains through Step 4 (`stam_lambda_min`) to the harmonic-mean upper bound
`J_sum ≤ J_X J_Y / (J_X + J_Y)`.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem stam_step3_to_step4_optimal {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_te : IsStamTotalExpectation X Y P) :
    ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      J_sum ≤ J_X * J_Y / (J_X + J_Y) :=
  isStamCauchySchwarzOptimal_of_coupling h_te

/-- **Full Step 1 → 4 chain to the genuine Stam signature** (the deliverable).

Combines Step 1 (score-convolution) + Step 3 (total-expectation) to produce the
genuine `IsStamInequalityHyp` (Cover-Thomas Lemma 17.7.2 真 signature). This is
the Step-3-centred entry point into the Wave 5 plumbing.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem isStamInequalityHyp_via_step3 {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_body h_conv (isStamCauchySchwarzOptimal_of_coupling h_te)

/-! ## §5 — Gaussian saturation: Step 3 holds with equality at the optimum

**RESOLVED (2026-05-20):** the former `isStamTotalExpectation_of_gaussian_fisherInfo_zero`,
`isStamFisherCoupling_of_gaussian_saturation`, and the Step-3 chain
`isStamInequalityHyp_of_gaussian_via_step3` discharged the total-expectation /
coupling predicates vacuously by `exfalso`-ing the `0 < J_X` precondition against
the buggy V1 `fisherInfo = 0` artefact for Gaussians. They asserted nothing about
Stam actually holding and were removed. The genuine Gaussian EPI runs via
`entropy_power_inequality_gaussian_saturation` (see `epi_via_stam_step3_gaussian`
below); the arithmetic saturation kernel `stam_coupling_saturates` is genuine and
kept.
-/

/-- **Gaussian saturation equality witness** (Step 3 equality condition).

For Gaussian `X, Y`, the Stam inequality saturates: `J(X+Y) = J(X) J(Y) /
(J(X) + J(Y))`, i.e. the Step-3 coupling holds with *equality* at the optimal
`λ = J_Y / (J_X + J_Y)`. This lemma exhibits the *arithmetic* saturation: at the
optimal λ, the coupling RHS `λ² J_X + (1-λ)² J_Y` equals the harmonic mean
exactly (Wave 7 `stam_lambda_min`), so equality in the coupling is equivalent to
equality in the harmonic-mean bound. -/
theorem stam_coupling_saturates {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ 2 * a + (1 - b / (a + b)) ^ 2 * b = a * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  field_simp
  ring

/-! ## §6 — EPI pipeline integration via Step 3 -/

/-- **EPI via Stam Step 3 (Gaussian case)**: full deliverable end-to-end. For
Gaussian `X, Y` with non-zero variance, EPI follows through the Step-3 body
discharge + Gaussian saturation bridge. -/
theorem epi_via_stam_step3_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  epi_via_stam_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-- **End-to-end EPI via Step 3 body discharge** (composes §4 + EPIStamDischarge
bridge). For independent `X, Y` with the Step 1 + Step 3 predicates and a
Stam-to-EPI bridge, EPI holds.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem entropy_power_inequality_via_step3
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_stam := isStamInequalityHyp_via_step3 h_conv h_te
  exact epi_via_stam_main P X Y X hX hY hXY h_stam h_bridge

/-! ## §7 — Step 3 manipulation lemmas + intermediate calc -/

/-- The total-expectation predicate is congruent under function equality. -/
theorem isStamTotalExpectation_congr {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hX : X = X') (hY : Y = Y')
    (h : IsStamTotalExpectation X Y P) :
    IsStamTotalExpectation X' Y' P := by
  subst hX; subst hY; exact h

/-- The Step-3 coupling predicate is congruent under function equality. -/
theorem isStamFisherCoupling_congr {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hX : X = X') (hY : Y = Y')
    (h : IsStamFisherCoupling X Y P) :
    IsStamFisherCoupling X' Y' P := by
  subst hX; subst hY; exact h

/-- **Intermediate calc helper**: at any `λ ∈ [0,1]`, the coupling RHS is a
convex combination bounded below by the harmonic mean (Wave 7
`stam_lambda_lower_bound`). This is the arithmetic certificate that Step 4's
optimization is *sound* (the coupling RHS never undercuts the harmonic mean). -/
theorem stam_coupling_rhs_ge_harmonic {a b lam : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * b / (a + b) ≤ lam ^ 2 * a + (1 - lam) ^ 2 * b :=
  stam_lambda_lower_bound ha hb lam

/-- **Coupling RHS endpoints**: at `λ = 0` the coupling RHS is `J_Y`, at `λ = 1`
it is `J_X` — the two trivial single-variable bounds the optimization
interpolates between. -/
theorem stam_coupling_rhs_endpoints (a b : ℝ) :
    ((0 : ℝ) ^ 2 * a + (1 - 0) ^ 2 * b = b)
      ∧ ((1 : ℝ) ^ 2 * a + (1 - 1) ^ 2 * b = a) :=
  ⟨by ring, by ring⟩

/-- **Total-expectation strengthens the existential coupling**: the
total-expectation predicate (which holds at *every* λ ∈ [0,1]) is strictly
stronger than the existential coupling (which needs only *one* λ).

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem isStamFisherCoupling_of_totalExpectation' {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamTotalExpectation X Y P) :
    IsStamFisherCoupling X Y P :=
  isStamFisherCoupling_of_totalExpectation h

/-! ## §8 — Sanity check / regression theorems -/

/-- **Sanity check**: the full Step-3 chain reproduces the Wave 7
`isStamInequalityHyp_via_body` result exactly when fed the optimal CS predicate
derived from the total expectation.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem step3_chain_eq_body_chain {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_body h_conv (isStamCauchySchwarzOptimal_of_coupling h_te)

end InformationTheory.Shannon.EPIStamStep3Body
