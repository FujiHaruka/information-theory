import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import InformationTheory.Shannon.DifferentialEntropy

/-!
# Fisher information density helpers

Density-based regularity predicates and score-function lemmas underpinning the Fisher
information development. The score function reuses Mathlib's `logDeriv f := deriv f / f`
(`Mathlib/Analysis/Calculus/LogDeriv.lean`), which is definitionally the score of a
density `f`.

## Main definitions

* `IsRegularDensity` — the regularity predicate (Cover–Thomas 17.7) bundling the
  differentiability, positivity, tail-vanishing, and integrability conditions on a smooth
  representative of the PDF.

## Main statements

* `integral_logDeriv_pdf_eq_zero` — the score function `logDeriv density · density` has
  zero integral over `ℝ`.

## Implementation notes

The Fisher information itself is defined in `FisherInfo.lean` (`fisherInfoOfDensity`) and
`FisherInfoDeBruijn.lean` (`fisherInfoOfMeasureV2`); this file holds only the
density-based helpers that do not reference those definitions.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-- The regularity predicate of Cover–Thomas 17.7, bundling the differentiability,
positivity, tail-vanishing, and integrability conditions needed for
`integral_logDeriv_pdf_eq_zero`. It is exposed as a predicate to be discharged downstream
rather than verified for a general random variable `X`.

Since `MeasureTheory.pdf X P volume` is defined only up to a.e. equivalence, pointwise
smoothness and positivity conditions cannot be stated on the PDF itself. The structure
therefore carries a chosen smooth representative `density : ℝ → ℝ` together with the
a.e.-equality `pdf_ae_eq`, and states the pointwise regularity conditions on `density`. -/
structure IsRegularDensity {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) [HasPDF X P volume] where
  /-- A smooth representative of the PDF (`(pdf X P volume x).toReal` is a.e.-equal
  to this representative, see `pdf_ae_eq`). -/
  density : ℝ → ℝ
  /-- `(pdf X P volume).toReal` equals the smooth representative `density` a.e. -/
  pdf_ae_eq : (fun x ↦ (pdf X P volume x).toReal) =ᵐ[volume] density
  /-- The representative is differentiable on all of `ℝ`. -/
  diff : Differentiable ℝ density
  /-- The representative is strictly positive everywhere (so `logDeriv` is well-defined). -/
  pos : ∀ x, 0 < density x
  /-- The representative tends to `0` at `-∞`. -/
  tail_bot : Filter.Tendsto density Filter.atBot (nhds 0)
  /-- The representative tends to `0` at `+∞`. -/
  tail_top : Filter.Tendsto density Filter.atTop (nhds 0)
  /-- The derivative of the representative is Lebesgue-integrable on all of `ℝ`. -/
  integrable_deriv : Integrable (deriv density) volume
  /-- The derivative integrates to `0` over `ℝ` (the boundary difference of `density`,
  which vanishes by the tail conditions). A regularity consequence equivalent to FTC plus
  tail-vanishing on the half-lines, discharged downstream via
  `MeasureTheory.integral_deriv_eq_sub` or its improper variants. -/
  integral_deriv_eq_zero : ∫ x, deriv density x ∂volume = 0

/-- The score function has zero expectation (Cover–Thomas 17.7). For the smooth
representative `density` of `IsRegularDensity`, the integral of
`logDeriv density · density = deriv density` over `ℝ` is `0`. Stated on the
representative `h_reg.density`; combine with `h_reg.pdf_ae_eq` to recast in terms of
`(pdf X P volume).toReal` via an a.e.-integral congruence.

@audit:ok -/
@[entry_point]
theorem integral_logDeriv_pdf_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P volume]
    (h_reg : IsRegularDensity X P) :
    ∫ x, logDeriv h_reg.density x * h_reg.density x ∂volume = 0 := by
  -- Pointwise: `logDeriv g x * g x = (deriv g x / g x) * g x = deriv g x` since `g x > 0`.
  set g : ℝ → ℝ := h_reg.density with hg
  have h_eq : ∀ x, logDeriv g x * g x = deriv g x := by
    intro x
    have hgx : g x ≠ 0 := (h_reg.pos x).ne'
    rw [logDeriv_apply, div_mul_cancel₀ _ hgx]
  -- Apply pointwise rewriting to the integral.
  have h_int : ∫ x, logDeriv g x * g x ∂volume = ∫ x, deriv g x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall h_eq)
  calc ∫ x, logDeriv g x * g x ∂volume
      = ∫ x, deriv g x ∂volume := h_int
    _ = 0 := h_reg.integral_deriv_eq_zero

end InformationTheory.Shannon