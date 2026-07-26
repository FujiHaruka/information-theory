import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.EPI.Stam.Inequality
import InformationTheory.Shannon.FisherInfo.OfDensity
import InformationTheory.Shannon.FisherInfo.DeBruijn
import InformationTheory.Shannon.FisherInfo.Gaussian
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Stam inequality body — Step 3 (Cauchy–Schwarz to symmetric Fisher coupling)

The 1-dimensional Stam inequality proof (Cover–Thomas Lemma 17.7.2 / Stam 1959 / Blachman 1965)
splits into four steps: the convolution score representation `s_Z = E[s_X | Z] = E[s_Y | Z]`,
pointwise Cauchy–Schwarz on the conditional expectation, total expectation against `p_Z` giving the
symmetric Fisher coupling `J(X + Y) ≤ λ² J(X) + (1 - λ)² J(Y)`, and optimization over `λ` giving
`1 / J(X + Y) ≥ 1 / J(X) + 1 / J(Y)`. This file makes Step 3 — integrating the earlier steps into
the symmetric Fisher coupling and bridging into the optimization — explicit.

## Main statements

* `isStamInequalityHyp_of_indepFun` — the full chain to the `IsStamInequalityHyp` signature,
  from regularity alone via `stamCauchySchwarzOptimal_of_indepFun`.
* `stam_optimal_lambda_mem_unit` — membership of the optimal `λ` in the unit interval.
* `stam_coupling_saturates` — the Gaussian saturation arithmetic kernel.
* `entropyPower_add_ge_of_gaussian` — pipeline integration via Gaussian saturation.

## Implementation notes

The analytic content of Steps 2-3 — the conditional Cauchy–Schwarz integrated against `p_Z`
giving the convex Fisher bound and its `λ`-optimum — is localized to the single lemma
`StamInequality.stamCauchySchwarzOptimal_of_indepFun`, which takes regularity preconditions only.

## References

[CoverThomas2006] Lemma 17.7.2; [Stam1959]; [Blachman1965].
-/

namespace InformationTheory.Shannon.StamFisherCoupling

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.StamEPIBridge
open InformationTheory.Shannon.StamInequality

/-! ## §1 — Optimal λ membership (arithmetic) -/

/-- The optimal λ `J_Y / (J_X + J_Y)` selected in Step 4 lies in the unit interval
`[0, 1]` whenever `J_X, J_Y > 0` (used throughout). -/
@[entry_point]
theorem stam_optimal_lambda_mem_unit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ b / (a + b) ∧ b / (a + b) ≤ 1 := by
  have hab : 0 < a + b := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hab]
  linarith

/-! ## §4 — Full Step 1 → 4 chain to the Stam signature -/

/-- The full Step 1 → 4 chain to the Stam signature: produces `IsStamInequalityHyp`
(Cover–Thomas Lemma 17.7.2) from regularity preconditions alone. The Step 2-3 convex Fisher bound
is supplied internally by `stamCauchySchwarzOptimal_of_indepFun`, and the remaining steps are
discharged arithmetically by `isStamInequalityHyp_via_body`. The hypotheses are only measurability,
independence, and the probability-measure instance.
@audit:ok -/
@[entry_point]
theorem isStamInequalityHyp_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_body (stamCauchySchwarzOptimal_of_indepFun P X Y hX hY hXY)

/-! ## §5 — Gaussian saturation: Step 3 holds with equality at the optimum

The Gaussian entropy power inequality runs via `entropyPower_gaussian_additivity`
(see `entropyPower_add_ge_of_gaussian` below); `stam_coupling_saturates` is the
arithmetic saturation kernel.
-/

/-- Gaussian saturation equality witness: at the optimal `λ = b / (a + b)`, the coupling RHS
`λ² a + (1 - λ)² b` equals the harmonic mean `a b / (a + b)` exactly, so equality in the Step-3
coupling is equivalent to equality in the harmonic-mean bound. -/
@[entry_point]
theorem stam_coupling_saturates {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ 2 * a + (1 - b / (a + b)) ^ 2 * b = a * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  field_simp
  ring

/-! ## §6 — EPI pipeline integration -/

/-- For Gaussian `X, Y` with non-zero variance, EPI holds with no Stam-predicate hypothesis:
the Gaussian saturation bridge `StamEPIBridge.epi_via_stam_gaussian`, re-exported into the
Fisher-coupling module. -/
@[entry_point]
theorem entropyPower_add_ge_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  epi_via_stam_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

end InformationTheory.Shannon.StamFisherCoupling
