import InformationTheory.Shannon.EPI.Conv.Density
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Convolution

/-!
# Normalization of the convolution density (EPI A-5 precondition (2))

`∫ z, convDensityAdd pX g_t z ∂volume = 1` when `pX` is a normalized probability
density and `g_t = gaussianPDFReal 0 ⟨t, _⟩` is a Gaussian heat kernel (`t > 0`).

## Route

`convDensityAdd pX g z = ∫ x, pX x * g (z - x) = (pX ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) z`
(definitional match: `(mul ℝ ℝ) a b = a * b`). We then apply
`MeasureTheory.integral_convolution`, which gives
`∫ z, (pX ⋆[L,ν] g) z = L (∫ pX) (∫ g) = (∫ pX) * (∫ g) = 1 * 1 = 1`.

- `∫ pX = 1` from `hpX_norm`.
- `∫ g = 1` from `ProbabilityTheory.integral_gaussianPDFReal_eq_one`.
- Gaussian integrability `Integrable g` from `ProbabilityTheory.integrable_gaussianPDFReal`.
-/

open MeasureTheory Real

namespace InformationTheory.Shannon.EPIConvDensity

open scoped NNReal

/-- The convolution density of a normalized density `pX` against a Gaussian heat
kernel `g_t` (`t > 0`) integrates to `1`. EPI A-5 precondition (2).

Independent honesty audit (2026-06-01, fresh auditor): verdict **ok**. The hard step
`∫ conv = (∫pX)·(∫g)` is done in-body by Mathlib `integral_convolution`, not assumed;
`∫ pX = 1` is the input probability-density normalization (regularity precondition).
Sufficiency holds. sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
@audit:ok -/
theorem integral_convDensityAdd_gaussian_eq_one (pX : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_int : Integrable pX volume)
    (hpX_norm : ∫ x, pX x ∂volume = 1) :
    ∫ z, InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (ProbabilityTheory.gaussianPDFReal 0 ⟨t, ht.le⟩) z ∂volume = 1 := by
  classical
  set g : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  have hg_int : Integrable g volume := ProbabilityTheory.integrable_gaussianPDFReal 0 ⟨t, ht.le⟩
  have hg_norm : ∫ x, g x ∂volume = 1 := by
    have hv : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
      intro h
      exact ht.ne' (congrArg NNReal.toReal h)
    exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hv
  -- `convDensityAdd pX g = pX ⋆[mul ℝ ℝ, volume] g` (definitional, via `mul_apply'`).
  have hconv : (fun z => convDensityAdd pX g z)
      = fun z => (convolution pX g (ContinuousLinearMap.mul ℝ ℝ) volume) z := by
    funext z
    unfold convDensityAdd convolution
    simp only [ContinuousLinearMap.mul_apply']
  rw [hconv]
  rw [MeasureTheory.integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hpX_int hg_int]
  rw [hpX_norm, hg_norm]
  simp

end InformationTheory.Shannon.EPIConvDensity
