import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Heat-flow path (2-source) for EPI-Stam Csiszár scaling

`heatFlowPath2 X Z s := √(1-s) · X + √s · Z`, the 2-source generalization of
the 1-source `gaussianConvolution X Z t = X + √t · Z` in `FisherInfoV2DeBruijn.lean`.
Used in `EPIStamToBridge.IsStamToEPIScalingHyp` (Phase 0 refactor) to carry
genuine Csiszár scaling monotonicity along `s ∈ [0, 1]`.

## Endpoints

* `heatFlowPath2 X Z 0 = X` (a.e., `√1 · X + √0 · Z = X`)
* `heatFlowPath2 X Z 1 = Z` (a.e., `√0 · X + √1 · Z = Z`)

## Mathlib-shape-driven design

The conclusion-form target is `MonotoneOn _ (Set.Icc 0 1)`, chosen so that
`monotoneOn_of_deriv_nonneg`'s `interior = Ioo 0 1` premise aligns with
`HasDerivAt.sqrt`'s `f x ≠ 0` premise on both `√(1-s)` and `√s`.
-/

namespace Common2026.Shannon

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal MeasureTheory

/-- 2-source heat-flow path `√(1-s) · X + √s · Z`. -/
noncomputable def heatFlowPath2 {α : Type*} (X Z : α → ℝ) (s : ℝ) : α → ℝ :=
  fun ω => Real.sqrt (1 - s) * X ω + Real.sqrt s * Z ω

@[simp] theorem heatFlowPath2_apply {α : Type*} (X Z : α → ℝ) (s : ℝ) (ω : α) :
    heatFlowPath2 X Z s ω = Real.sqrt (1 - s) * X ω + Real.sqrt s * Z ω := rfl

/-- Measurability of `heatFlowPath2`. -/
theorem measurable_heatFlowPath2 {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (s : ℝ) :
    Measurable (heatFlowPath2 X Z s) := by
  unfold heatFlowPath2
  exact (measurable_const.mul hX).add (measurable_const.mul hZ)

/-- Endpoint at `s = 0`: `heatFlowPath2 X Z 0 = X`. -/
theorem heatFlowPath2_zero {α : Type*} (X Z : α → ℝ) :
    heatFlowPath2 X Z 0 = X := by
  funext ω
  simp [heatFlowPath2, Real.sqrt_one, Real.sqrt_zero]

/-- Endpoint at `s = 1`: `heatFlowPath2 X Z 1 = Z`. -/
theorem heatFlowPath2_one {α : Type*} (X Z : α → ℝ) :
    heatFlowPath2 X Z 1 = Z := by
  funext ω
  simp [heatFlowPath2, Real.sqrt_one, Real.sqrt_zero]

/-- Law of `heatFlowPath2 X Z s` when `Z ∼ 𝒩(0, 1)` and `X ⊥ Z`:
    `P.map (heatFlowPath2 X Z s)` is the convolution of
    `P.map (√(1-s) · X)` with `𝒩(0, s)`. -/
theorem heatFlowPath2_law {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ}
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1) {s : ℝ} (hs0 : 0 ≤ s) (_hs1 : s ≤ 1) :
    P.map (heatFlowPath2 X Z s)
      = (P.map (fun ω => Real.sqrt (1 - s) * X ω)) ∗ gaussianReal 0 ⟨s, hs0⟩ := by
  -- Step 1: law of `√s · Z` is `𝒩(0, s)`.
  have h_sqrt_nn : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have h_sqrt_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0
  have h_sqrtZ_map : Measure.map (fun ω => Real.sqrt s * Z ω) P
      = gaussianReal 0 ⟨s, hs0⟩ := by
    have h_compose : Measure.map (fun ω => Real.sqrt s * Z ω) P
        = (P.map Z).map (fun y => Real.sqrt s * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt s * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hZ
      simpa [Function.comp] using this.symm
    rw [h_compose, hZ_law, gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]
      apply NNReal.eq
      exact h_sqrt_sq
  -- Step 2: independence `(√(1-s) · X) ⊥ (√s · Z)`.
  have h_indep : IndepFun (fun ω => Real.sqrt (1 - s) * X ω)
      (fun ω => Real.sqrt s * Z ω) P :=
    hXZ.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  -- Step 3: rewrite `heatFlowPath2 X Z s` as the pointwise sum.
  have h_funext : heatFlowPath2 X Z s
      = (fun ω => Real.sqrt (1 - s) * X ω) + (fun ω => Real.sqrt s * Z ω) := by
    funext ω; rfl
  rw [h_funext]
  -- Step 4: apply `IndepFun.map_add_eq_map_conv_map`.
  have h_meas_X : Measurable (fun ω => Real.sqrt (1 - s) * X ω) :=
    measurable_const.mul hX
  have h_meas_Z : Measurable (fun ω => Real.sqrt s * Z ω) :=
    measurable_const.mul hZ
  rw [h_indep.map_add_eq_map_conv_map h_meas_X h_meas_Z, h_sqrtZ_map]

/-- When `X` is also `𝒩(m, v)`, the full law of `heatFlowPath2 X Z s` is
    `𝒩((√(1-s)) · m, (1-s) · v + s)`. Gaussian saturation endpoint case. -/
theorem heatFlowPath2_law_of_gaussian {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ}
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    P.map (heatFlowPath2 X Z s)
      = gaussianReal (Real.sqrt (1 - s) * m)
          (⟨1 - s, by linarith⟩ * v + ⟨s, hs0⟩) := by
  -- Preliminary positivity facts.
  have h_1ms_nn : (0 : ℝ) ≤ 1 - s := by linarith
  have h_sqrt_1ms_nn : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have h_sqrt_1ms_sq : (Real.sqrt (1 - s)) ^ 2 = 1 - s := Real.sq_sqrt h_1ms_nn
  have h_sqrt_s_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0
  -- Step 1: law of `√(1-s) · X` is `𝒩(√(1-s) · m, (1-s) · v)`.
  have h_sqrtX_map : Measure.map (fun ω => Real.sqrt (1 - s) * X ω) P
      = gaussianReal (Real.sqrt (1 - s) * m) (⟨1 - s, h_1ms_nn⟩ * v) := by
    have h_compose : Measure.map (fun ω => Real.sqrt (1 - s) * X ω) P
        = (P.map X).map (fun y => Real.sqrt (1 - s) * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt (1 - s) * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hX
      simpa [Function.comp] using this.symm
    rw [h_compose, hX_law, gaussianReal_map_const_mul]
    -- Goal: gaussianReal (√(1-s) * m) (.mk ((√(1-s))^2) _ * v)
    --     = gaussianReal (√(1-s) * m) (⟨1-s, h_1ms_nn⟩ * v)
    congr 2
    apply NNReal.eq
    push_cast
    exact h_sqrt_1ms_sq
  -- Step 2: law of `√s · Z` is `𝒩(0, s)`.
  have h_sqrtZ_map : Measure.map (fun ω => Real.sqrt s * Z ω) P
      = gaussianReal 0 ⟨s, hs0⟩ := by
    have h_compose : Measure.map (fun ω => Real.sqrt s * Z ω) P
        = (P.map Z).map (fun y => Real.sqrt s * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt s * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hZ
      simpa [Function.comp] using this.symm
    rw [h_compose, hZ_law, gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]
      apply NNReal.eq
      exact h_sqrt_s_sq
  -- Step 3: independence `(√(1-s) · X) ⊥ (√s · Z)`.
  have h_indep : IndepFun (fun ω => Real.sqrt (1 - s) * X ω)
      (fun ω => Real.sqrt s * Z ω) P :=
    hXZ.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  -- Step 4: sum of independent Gaussians.
  have h_sum := gaussianReal_add_gaussianReal_of_indepFun (P := P)
    (X := fun ω => Real.sqrt (1 - s) * X ω)
    (Y := fun ω => Real.sqrt s * Z ω)
    (m₁ := Real.sqrt (1 - s) * m) (m₂ := 0)
    (v₁ := ⟨1 - s, h_1ms_nn⟩ * v) (v₂ := ⟨s, hs0⟩)
    h_indep h_sqrtX_map h_sqrtZ_map
  -- Step 5: `heatFlowPath2 X Z s` is the pointwise sum.
  have h_funext : heatFlowPath2 X Z s
      = (fun ω => Real.sqrt (1 - s) * X ω) + (fun ω => Real.sqrt s * Z ω) := by
    funext ω; rfl
  rw [h_funext, h_sum]
  congr 1
  ring

end Common2026.Shannon
