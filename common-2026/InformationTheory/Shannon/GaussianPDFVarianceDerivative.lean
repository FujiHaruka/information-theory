import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.FisherInfo.DeBruijnHeatFlow
import InformationTheory.Shannon.FisherInfo.HeatFlow

/-!
# Gaussian PDF variance (time) derivative — de Bruijn FTC core

The time-derivative half of the de Bruijn identity machinery: the heat equation
`∂_t p = (1/2) Δ_x p` for the Gaussian heat kernel.

The variance-derivative of `gaussianPDFReal` is not in Mathlib. This file
builds it from scratch via the `Real.exp` / `Real.sqrt` chain rule and assembles
the full heat equation for the Gaussian kernel.

## Main definitions

* `gaussianPDFRealVar` — real-variance Gaussian density
  `(√(2πv))⁻¹ · exp(−(x−m)²/(2v))`.

## Main statements

* `gaussianPDFRealVar_eq_gaussianPDFReal` — for `v > 0`, agrees with `gaussianPDFReal m ⟨v, _⟩`.
* `hasDerivAt_gaussianPDFRealVar_variance` — variance-derivative:
  `∂_v gaussianPDFRealVar m v x = ((x−m)²/(2v²) − 1/(2v)) · gaussianPDFRealVar m v x`.
* `hasDerivAt_heatKernel_time` — time-derivative of the heat kernel:
  `∂_t g_t x = (1/2)(x²/t² − 1/t)·g_t x`.
* `isHeatTimeDerivHyp_gaussian` — `IsHeatTimeDerivHyp` for the Gaussian heat kernel
  with `Δp = spatialLaplacianHeatKernel`.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Real-variance Gaussian density -/

/-- **Real-variance Gaussian density** `(√(2πv))⁻¹ · exp(−(x−m)²/(2v))`.

This is `gaussianPDFReal m v x` with the variance `v` taken as a *real* number
(rather than `ℝ≥0`), so that we can differentiate in `v`. For `v > 0` it agrees
with `gaussianPDFReal m ⟨v, _⟩` (see `gaussianPDFRealVar_eq_gaussianPDFReal`). -/
noncomputable def gaussianPDFRealVar (m v x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * v))

/-- For `v > 0`, `gaussianPDFRealVar` agrees with `gaussianPDFReal m ⟨v, _⟩`. -/
@[entry_point]
theorem gaussianPDFRealVar_eq_gaussianPDFReal (m : ℝ) {v : ℝ} (hv : 0 < v) (x : ℝ) :
    gaussianPDFRealVar m v x = gaussianPDFReal m ⟨v, hv.le⟩ x := by
  rw [gaussianPDFReal]
  rfl

/-! ## Variance-derivative lemma (the Mathlib gap closure) -/

/-- **Variance-derivative of the `(√(2πv))⁻¹` normalising factor.**

`∂_v (√(2πv))⁻¹ = -(1/(2v)) · (√(2πv))⁻¹`. The `√` cancels: the log-derivative
of `(√(2πv))⁻¹` is rational. -/
@[entry_point]
theorem hasDerivAt_gaussianNorm_variance {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v ↦ (Real.sqrt (2 * Real.pi * v))⁻¹)
      (-(1 / (2 * v)) * (Real.sqrt (2 * Real.pi * v))⁻¹) v := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2piv_pos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  have h2piv_ne : (2 * Real.pi * v : ℝ) ≠ 0 := ne_of_gt h2piv_pos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr h2piv_pos
  have hsqrt_ne : Real.sqrt (2 * Real.pi * v) ≠ 0 := ne_of_gt hsqrt_pos
  -- inner: `2πv`, derivative `2π`
  have h_inner : HasDerivAt (fun v : ℝ ↦ 2 * Real.pi * v) (2 * Real.pi) v := by
    have := (hasDerivAt_id v).const_mul (2 * Real.pi)
    simpa using this
  -- sqrt: derivative `(2π) / (2 · √(2πv))`
  have h_sqrt : HasDerivAt (fun v : ℝ ↦ Real.sqrt (2 * Real.pi * v))
      ((2 * Real.pi) / (2 * Real.sqrt (2 * Real.pi * v))) v := h_inner.sqrt h2piv_ne
  -- inverse: derivative `-((2π)/(2·√(2πv))) / (√(2πv))²`
  have h_inv := h_sqrt.inv hsqrt_ne
  -- reshape the derivative value
  convert h_inv using 1
  -- goal: `-(1/(2v)) · (√(2πv))⁻¹ = -((2π)/(2·√(2πv))) / (√(2πv))²`
  rw [Real.sq_sqrt h2piv_pos.le]
  field_simp

/-- **Variance-derivative of the exponential factor.**

`∂_v exp(−(x−m)²/(2v)) = ((x−m)²/(2v²)) · exp(−(x−m)²/(2v))`. -/
@[entry_point]
theorem hasDerivAt_gaussianExp_variance (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v ↦ Real.exp (-(x - m) ^ 2 / (2 * v)))
      (((x - m) ^ 2 / (2 * v ^ 2)) * Real.exp (-(x - m) ^ 2 / (2 * v))) v := by
  have h2v_ne : (2 * v : ℝ) ≠ 0 := by positivity
  -- inner argument `-(x-m)²/(2v)`, derivative `(x-m)²/(2v²)`
  have h_num : HasDerivAt (fun _ : ℝ ↦ -(x - m) ^ 2) 0 v := hasDerivAt_const v _
  have h_den : HasDerivAt (fun v : ℝ ↦ 2 * v) 2 v := by
    have := (hasDerivAt_id v).const_mul (2 : ℝ)
    simpa using this
  have h_div : HasDerivAt (fun v : ℝ ↦ -(x - m) ^ 2 / (2 * v))
      ((0 * (2 * v) - -(x - m) ^ 2 * 2) / (2 * v) ^ 2) v := h_num.div h_den h2v_ne
  have h_div' : HasDerivAt (fun v : ℝ ↦ -(x - m) ^ 2 / (2 * v))
      ((x - m) ^ 2 / (2 * v ^ 2)) v := by
    convert h_div using 1
    field_simp
    ring
  -- chain through `exp`
  have h_exp := h_div'.exp
  convert h_exp using 1
  ring

/-- **The variance-derivative lemma (Mathlib-gap closure).**

`∂_v gaussianPDFRealVar m v x
   = ((x−m)²/(2v²) − 1/(2v)) · gaussianPDFRealVar m v x`,

for `v > 0`. Proven from scratch via the `Real.exp` / `Real.sqrt` chain rule. -/
@[entry_point]
theorem hasDerivAt_gaussianPDFRealVar_variance (m x : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v ↦ gaussianPDFRealVar m v x)
      (((x - m) ^ 2 / (2 * v ^ 2) - 1 / (2 * v)) * gaussianPDFRealVar m v x) v := by
  have hA := hasDerivAt_gaussianNorm_variance hv
  have hB := hasDerivAt_gaussianExp_variance m x hv
  -- product rule on `A(v) · B(v)`
  have hAB := hA.mul hB
  -- `gaussianPDFRealVar m v x = A v * B v` definitionally; rewrite the goal's
  -- derivative value to match the product-rule output.
  have hprod : HasDerivAt (fun v ↦ gaussianPDFRealVar m v x)
      (-(1 / (2 * v)) * (Real.sqrt (2 * Real.pi * v))⁻¹
          * Real.exp (-(x - m) ^ 2 / (2 * v))
        + (Real.sqrt (2 * Real.pi * v))⁻¹
          * ((x - m) ^ 2 / (2 * v ^ 2) * Real.exp (-(x - m) ^ 2 / (2 * v)))) v := hAB
  convert hprod using 1
  unfold gaussianPDFRealVar
  ring

/-! ## Heat-kernel time derivative (m = 0) -/

/-- **Time-derivative of the Gaussian heat kernel.**

`∂_t g_t x = (1/2)(x²/t² − 1/t)·g_t x = (1/2) Δ_x g_t x`, i.e. `g_t` solves the
heat equation `∂_t p = (1/2) Δ_x p`. This is the `m = 0` specialization of
`hasDerivAt_gaussianPDFRealVar_variance`, re-expressed against `heatKernel` and
`spatialLaplacianHeatKernel`. -/
@[entry_point]
theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s ↦ InformationTheory.Shannon.FisherInfo.heatKernel s x)
      ((1 / 2) * InformationTheory.Shannon.FisherInfo.spatialLaplacianHeatKernel t x) t := by
  -- variance-derivative of `gaussianPDFRealVar 0 · x` at `t` (m = 0)
  have hvar := hasDerivAt_gaussianPDFRealVar_variance 0 x ht
  -- the derivative value equals `(1/2) · spatialLaplacianHeatKernel t x`
  have hval : ((x - 0) ^ 2 / (2 * t ^ 2) - 1 / (2 * t)) * gaussianPDFRealVar 0 t x
      = (1 / 2) * InformationTheory.Shannon.FisherInfo.spatialLaplacianHeatKernel t x := by
    rw [InformationTheory.Shannon.FisherInfo.spatialLaplacianHeatKernel,
      InformationTheory.Shannon.FisherInfo.heatKernel_def_gaussianPDFReal ht,
      ← gaussianPDFRealVar_eq_gaussianPDFReal 0 ht]
    ring
  rw [hval] at hvar
  -- transfer from `gaussianPDFRealVar 0 · x` to `heatKernel · x` (agree near `t`)
  refine hvar.congr_of_eventuallyEq ?_
  have h_nhds : Set.Ioi (0 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
  filter_upwards [h_nhds] with s hs
  rw [InformationTheory.Shannon.FisherInfo.heatKernel_def_gaussianPDFReal hs,
    ← gaussianPDFRealVar_eq_gaussianPDFReal 0 hs]

/-! ## Proof of `IsHeatTimeDerivHyp` -/

/-- **Gaussian heat kernel satisfies the time-derivative sub-predicate.**

`IsHeatTimeDerivHyp` for the Gaussian heat kernel with
`Δp t x := spatialLaplacianHeatKernel t x`. -/
@[entry_point]
theorem isHeatTimeDerivHyp_gaussian :
    InformationTheory.Shannon.FisherInfo.IsHeatTimeDerivHyp
      (fun t x ↦ InformationTheory.Shannon.FisherInfo.heatKernel t x)
      (fun t x ↦ InformationTheory.Shannon.FisherInfo.spatialLaplacianHeatKernel t x) := by
  intro t ht x
  exact hasDerivAt_heatKernel_time ht x

end InformationTheory.Shannon
