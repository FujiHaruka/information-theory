import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.FisherInfo.Basic
import InformationTheory.Shannon.FisherInfo.Gaussian
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-!
# Fisher information of a density

The Fisher information `fisherInfoOfDensity f := ∫⁻ (logDeriv f x)² · f x dx` takes the
density `f : ℝ → ℝ` as an explicit argument rather than extracting it from a measure via
`Measure.rnDeriv`. The Radon–Nikodym derivative is defined via `Classical.choose` of the
Lebesgue decomposition and returns a generically non-differentiable representative, so a
measure-keyed definition collapses `logDeriv` to `0` a.e.; supplying the density directly
avoids that.

## Main definitions

* `fisherInfoOfDensity` — the Fisher information of a density (`ℝ≥0∞`-valued).
* `fisherInfoOfDensityReal` — its real-valued projection.
* `IsRegularDensityV2` — the regularity predicate with the density `f` as its primary
  field.

## Main statements

* `integral_logDeriv_density_eq_zero` — the score function has zero expectation.
* `fisherInfoOfDensity_gaussianPDFReal` — the Gaussian closed form
  `fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1 / v)`.
-/

namespace InformationTheory.Shannon.FisherInfo

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-- The Fisher information of a density `f : ℝ → ℝ`, defined as
`∫⁻ (logDeriv f x)² · f x dx` with `logDeriv f := deriv f / f` Mathlib's score function.
Valued in `ℝ≥0∞` to capture `+∞` for irregular families; use `fisherInfoOfDensityReal` or
`.toReal` to project to `ℝ` when finite. -/
noncomputable def fisherInfoOfDensity (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv f x) ^ 2) * ENNReal.ofReal (f x) ∂volume

/-- Fisher information of a density is non-negative (trivially, as `ℝ≥0∞`). -/
@[entry_point]
theorem fisherInfoOfDensity_nonneg (f : ℝ → ℝ) : 0 ≤ fisherInfoOfDensity f := bot_le

/-- The Fisher information of the constant-zero density is `0`. -/
@[entry_point]
theorem fisherInfoOfDensity_zero : fisherInfoOfDensity (fun _ : ℝ ↦ (0 : ℝ)) = 0 := by
  unfold fisherInfoOfDensity
  simp

/-- Real-valued projection of `fisherInfoOfDensity`. -/
noncomputable def fisherInfoOfDensityReal (f : ℝ → ℝ) : ℝ := (fisherInfoOfDensity f).toReal

@[entry_point]
theorem fisherInfoOfDensityReal_nonneg (f : ℝ → ℝ) : 0 ≤ fisherInfoOfDensityReal f :=
  ENNReal.toReal_nonneg

/-- The regularity predicate on a density `f`, bundling the differentiability, positivity,
tail-vanishing, and integrability conditions needed for
`integral_logDeriv_density_eq_zero`. No measure is mentioned: the link to a random variable
`X` is established separately via an a.e.-equality between `f` and `(pdf X P volume).toReal`. -/
structure IsRegularDensityV2 (f : ℝ → ℝ) : Prop where
  /-- `f` is differentiable on all of `ℝ`. -/
  diff : Differentiable ℝ f
  /-- `f` is strictly positive everywhere (so `logDeriv f` is well-defined). -/
  pos : ∀ x, 0 < f x
  /-- `f` tends to `0` at `-∞`. -/
  tail_bot : Filter.Tendsto f Filter.atBot (nhds 0)
  /-- `f` tends to `0` at `+∞`. -/
  tail_top : Filter.Tendsto f Filter.atTop (nhds 0)
  /-- `deriv f` is Lebesgue-integrable on all of `ℝ`. -/
  integrable_deriv : Integrable (deriv f) volume
  /-- `deriv f` integrates to `0` over `ℝ`, a regularity consequence of FTC plus
  tail-vanishing on the half-lines. -/
  integral_deriv_eq_zero : ∫ x, deriv f x ∂volume = 0

/-- The score function has zero expectation: for a regular density `f`, the integral of
`logDeriv f · f = deriv f` over `ℝ` is `0`.

@audit:ok -/
@[entry_point]
theorem integral_logDeriv_density_eq_zero {f : ℝ → ℝ} (h_reg : IsRegularDensityV2 f) :
    ∫ x, logDeriv f x * f x ∂volume = 0 := by
  -- Pointwise: `logDeriv f x * f x = (deriv f x / f x) * f x = deriv f x` since `f x > 0`.
  have h_eq : ∀ x, logDeriv f x * f x = deriv f x := by
    intro x
    have hfx : f x ≠ 0 := (h_reg.pos x).ne'
    rw [logDeriv_apply, div_mul_cancel₀ _ hfx]
  have h_int : ∫ x, logDeriv f x * f x ∂volume = ∫ x, deriv f x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall h_eq)
  calc ∫ x, logDeriv f x * f x ∂volume
      = ∫ x, deriv f x ∂volume := h_int
    _ = 0 := h_reg.integral_deriv_eq_zero

/-! ## Gaussian closed form -/

/-- `((x - m) / v)² · gaussianPDFReal m v x` is Lebesgue-integrable for `v ≠ 0`. -/
lemma integrable_logDeriv_sq_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x ↦ ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x) volume := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2v_pos : (0 : ℝ) < 2 * (v : ℝ) := by positivity
  have hb : (0 : ℝ) < (2 * v)⁻¹ := inv_pos.mpr h2v_pos
  have hv_ne : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  -- `integrable_rpow_mul_exp_neg_mul_sq` at `s = 2`. Convert rpow `^(2:ℝ)`
  -- to nat-pow `^2` using `Real.rpow_two`.
  have h_pow_two : Integrable
      (fun y : ℝ ↦ y ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)) volume := by
    have h_rpow : Integrable
        (fun y : ℝ ↦ y ^ (2 : ℝ) * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)) volume :=
      integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
    refine h_rpow.congr (Filter.Eventually.of_forall fun y ↦ ?_)
    show y ^ (2 : ℝ) * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)
        = y ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)
    rw [Real.rpow_two]
  -- Shift: `y ↦ y - m`.
  have h_shift : Integrable
      (fun x : ℝ ↦ (x - m) ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m) ^ 2)) volume :=
    h_pow_two.comp_sub_right m
  -- Multiply by `(1 / v²) · (√(2πv))⁻¹` to obtain the target shape.
  have h_scaled : Integrable
      (fun x : ℝ ↦ ((1 / (v : ℝ) ^ 2) * (Real.sqrt (2 * Real.pi * v))⁻¹)
          * ((x - m) ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m) ^ 2))) volume :=
    h_shift.const_mul _
  -- Match the target shape `((x - m) / v)² · gaussianPDFReal m v x`.
  refine h_scaled.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  -- Expand the Gaussian PDF and reconcile the exponent form.
  have hexp_eq :
      Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ)))
        = Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m) ^ 2) := by
    congr 1; field_simp
  simp only [gaussianPDFReal, hexp_eq]
  field_simp

/-- `∫ ((x - m)/v)² · gaussianPDFReal m v x dx = 1 / v`. -/
private lemma integral_logDeriv_sq_mul_gaussianPDFReal_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x ∂volume = 1 / (v : ℝ) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hv_ne : (v : ℝ) ≠ 0 := hv_pos.ne'
  have hv_sq_ne : (v : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hv_ne
  -- Step 1: pull out `(1/v²)`.
  have h_eq : (fun x : ℝ ↦ ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x)
      = fun x : ℝ ↦ (1 / (v : ℝ) ^ 2) * ((x - m) ^ 2 * gaussianPDFReal m v x) := by
    funext x; field_simp
  rw [h_eq, integral_const_mul]
  -- Step 2: `∫ (x - m)² · gaussianPDFReal m v x = v` via variance.
  have h_var : ∫ x, (x - m) ^ 2 * gaussianPDFReal m v x ∂volume = (v : ℝ) := by
    -- Via `integral_gaussianReal_eq_integral_smul`:
    --   ∫ f x ∂(gaussianReal m v) = ∫ gaussianPDFReal m v x • f x ∂volume.
    -- With `f x := (x - m) ^ 2`, the LHS equals the variance of the Gaussian, namely `v`.
    have h_smul := integral_gaussianReal_eq_integral_smul
      (μ := m) (v := v) (f := fun x ↦ (x - m) ^ 2) hv
    -- LHS = ∫ (x - m)² ∂(gaussianReal m v) = Var[fun x => x; gaussianReal m v] = v.
    have h_var_eq : ∫ x, (x - m) ^ 2 ∂(gaussianReal m v) = (v : ℝ) := by
      have h_int_id : ∫ x, x ∂(gaussianReal m v) = m := integral_id_gaussianReal
      have h_id_mb : AEMeasurable (fun x : ℝ ↦ x) (gaussianReal m v) := aemeasurable_id'
      have h_var := variance_fun_id_gaussianReal (μ := m) (v := v)
      rw [variance_eq_integral h_id_mb] at h_var
      -- h_var : ∫ ω, (ω - ∫ x, x ∂(gaussianReal m v)) ^ 2 ∂(gaussianReal m v) = v
      rw [h_int_id] at h_var
      exact h_var
    rw [h_var_eq] at h_smul
    -- h_smul : v = ∫ x, gaussianPDFReal m v x • (fun x => (x - m) ^ 2) x ∂volume.
    -- Beta-reduce + smul_eq_mul + commute the factors.
    have h_smul' : (v : ℝ) = ∫ x, (x - m) ^ 2 * gaussianPDFReal m v x ∂volume := by
      rw [h_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp [smul_eq_mul, mul_comm]
    exact h_smul'.symm
  rw [h_var]
  -- Conclude: (1/v²) * v = 1/v.
  field_simp

/-- The Gaussian Fisher information in closed form:
`fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1 / v)`, obtained by
supplying the Gaussian PDF directly and evaluating the integral via the variance identity. -/
@[entry_point]
theorem fisherInfoOfDensity_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1 / (v : ℝ)) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  -- Step 1: Convert the `lintegral` to a Bochner integral. The integrand is
  -- `((x - m)/v)² · gaussianPDFReal m v x ≥ 0` and integrable.
  unfold fisherInfoOfDensity
  -- Rewrite the integrand pointwise: combine the two `ENNReal.ofReal`s into one.
  have h_pointwise : ∀ x,
      ENNReal.ofReal ((logDeriv (gaussianPDFReal m v) x) ^ 2)
          * ENNReal.ofReal (gaussianPDFReal m v x)
        = ENNReal.ofReal (((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x) := by
    intro x
    have h_sq_nn : 0 ≤ (logDeriv (gaussianPDFReal m v) x) ^ 2 := sq_nonneg _
    have h_pdf_nn : 0 ≤ gaussianPDFReal m v x := (gaussianPDFReal_pos m v x hv).le
    rw [← ENNReal.ofReal_mul h_sq_nn]
    congr 1
    rw [InformationTheory.Shannon.logDeriv_gaussianPDFReal hv]
    ring
  rw [lintegral_congr h_pointwise]
  -- Step 2: convert `∫⁻ ofReal g = ofReal (∫ g)` using non-negativity + integrability.
  have h_nn : 0 ≤ᵐ[volume] fun x : ℝ ↦
      ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have h_pdf_nn : 0 ≤ gaussianPDFReal m v x := (gaussianPDFReal_pos m v x hv).le
    have h_sq_nn : 0 ≤ ((x - m) / (v : ℝ)) ^ 2 := sq_nonneg _
    exact mul_nonneg h_sq_nn h_pdf_nn
  have h_int := integrable_logDeriv_sq_mul_gaussianPDFReal m hv
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  -- Step 3: compute the Bochner integral to `1/v`.
  rw [integral_logDeriv_sq_mul_gaussianPDFReal_eq m hv]

/-- Real-valued projection of the Gaussian Fisher info closed form. -/
theorem fisherInfoOfDensityReal_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfDensityReal (gaussianPDFReal m v) = 1 / (v : ℝ) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  unfold fisherInfoOfDensityReal
  rw [fisherInfoOfDensity_gaussianPDFReal m hv]
  rw [ENNReal.toReal_ofReal (by positivity)]

end InformationTheory.Shannon.FisherInfo