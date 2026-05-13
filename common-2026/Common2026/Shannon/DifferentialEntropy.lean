import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Differential entropy + Gaussian max-entropy (E-9)

Common2026 E-9 ムーンショット ([`docs/shannon/differential-entropy-plan.md`])。

Cover-Thomas 8.1 (微分エントロピー定義), 8.6.1 (translation / scaling), 9.6
(Gaussian max-entropy)。`differentialEntropy μ := ∫ x, Real.negMulLog
((μ.rnDeriv volume x).toReal) ∂volume`。

## 主シグネチャ

* `differentialEntropy` — Phase A 定義 (rnDeriv vs. Lebesgue, Bochner Real-valued)
* `differentialEntropy_eq_integral_withDensity` — `μ = volume.withDensity f` の場合の書換
* `differentialEntropy_eq_integral_density` — `f log f` 直書き形 (Phase D に使う)
* `integrable_density_log_density_of_gaussian` — gaussianReal 上の可積分性
* `differentialEntropy_map_add_const` / `..._mul_const` / `..._affine` — Phase B
* `differentialEntropy_gaussianReal` — Phase C 主定理 `(1/2) log (2πe v)`
* `differentialEntropy_le_gaussian_of_variance_le` — Phase D 主定理
* `klDiv_gaussianReal_gaussianReal_eq` — Phase E 1 KL closed-form
-/

namespace Common2026.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase A — `differentialEntropy` 定義 + 基本可積分性 -/

/-- **Differential entropy**. For a measure `μ` on `ℝ`, define
`differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume`,
i.e. `-∫ f log f dx` where `f := dμ/dvolume` is the Radon-Nikodym derivative w.r.t.
the Lebesgue measure. `Real.negMulLog 0 = 0` covers the support boundary automatically.
The value is meaningful primarily when `μ ≪ volume`; under singular `μ`, the rnDeriv
captures only the absolutely continuous part. -/
noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
  ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume

/-- For `μ = volume.withDensity f` with measurable `f`, the differential entropy is the
integral of `negMulLog (f x).toReal` over the Lebesgue measure. -/
theorem differentialEntropy_eq_integral_withDensity
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    differentialEntropy (volume.withDensity f)
      = ∫ x, Real.negMulLog (f x).toReal ∂volume := by
  unfold differentialEntropy
  refine integral_congr_ae ?_
  have h := Measure.rnDeriv_withDensity (volume : Measure ℝ) hf
  filter_upwards [h] with x hx
  rw [hx]

/-- For `μ ≪ volume` with a measurable Real-valued density `f` such that
`μ = volume.withDensity (fun x => ENNReal.ofReal (f x))` (and `0 ≤ f`),
`differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume`. -/
theorem differentialEntropy_eq_integral_density
    {f : ℝ → ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x)
    (μ : Measure ℝ)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume := by
  subst hμ
  rw [differentialEntropy_eq_integral_withDensity hf.ennreal_ofReal]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [Real.negMulLog_def]
  rw [ENNReal.toReal_ofReal (hf_nn x)]
  ring

/-- The integrand `gaussianPDFReal m v x * Real.log (gaussianPDFReal m v x)` is integrable
on Lebesgue volume. This is the key integrability lemma needed for Phase C and D.

Strategy: `log f = -(1/2) log(2πv) - (x-m)²/(2v)`, so
`f * log f = c₀ * f - (x-m)² * f / (2v)`. First term is `const * integrable f`. Second term
reduces, via substitution `y = x - m`, to `(√(2πv))⁻¹ * y² * exp(-y²/(2v))`, integrable by
`integrable_rpow_mul_exp_neg_mul_sq` with `s = 2`. -/
theorem integrable_density_log_density_of_gaussian
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => gaussianPDFReal m v x * Real.log (gaussianPDFReal m v x)) volume := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2πv_pos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  -- Split via `log f = c₀ - (x-m)²/(2v)`, where `c₀ := -(1/2) log(2πv)`.
  set c₀ : ℝ := -(1/2) * Real.log (2 * Real.pi * v) with hc₀
  have h_log_eq : ∀ x, Real.log (gaussianPDFReal m v x)
      = c₀ - (x - m)^2 / (2 * v) := by
    intro x
    unfold gaussianPDFReal
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne']
    rw [Real.log_inv, Real.log_sqrt h2πv_pos.le, Real.log_exp]
    simp only [hc₀]
    ring
  have h_eq : (fun x => gaussianPDFReal m v x * Real.log (gaussianPDFReal m v x))
      = fun x => c₀ * gaussianPDFReal m v x
          - gaussianPDFReal m v x * ((x - m)^2 / (2 * v)) := by
    funext x
    rw [h_log_eq x]
    ring
  rw [h_eq]
  refine Integrable.sub ?_ ?_
  · exact (integrable_gaussianPDFReal m v).const_mul c₀
  · -- `gaussianPDFReal m v x * (x-m)² / (2v)` is integrable.
    -- Express as `(2v)⁻¹ * ( (√(2πv))⁻¹ * ( (x-m)² * exp(-(x-m)²/(2v)) ) )`.
    have hb : (0 : ℝ) < (2 * v)⁻¹ := inv_pos.mpr (by positivity)
    -- Base integrability from `integrable_rpow_mul_exp_neg_mul_sq` at `s = 2`.
    have h_rpow : Integrable
        (fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-(2 * v)⁻¹ * y^2)) volume :=
      integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
    have h_base : Integrable
        (fun y : ℝ => y^2 * Real.exp (-(2 * v)⁻¹ * y^2)) volume := by
      refine h_rpow.congr (Filter.Eventually.of_forall fun y => ?_)
      simp
    have h_inner : Integrable
        (fun x : ℝ => (x - m)^2 * Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m)^2)) volume := by
      -- `h_base` and `h_inner` use coerced `↑(2 * v)⁻¹`; normalize via `congr 2`/`push_cast`.
      have hb_eq : (fun y : ℝ => y^2 * Real.exp (-((2 * v : ℝ≥0))⁻¹ * y^2))
          = fun y => y^2 * Real.exp (-(2 * (v : ℝ))⁻¹ * y^2) := by
        funext y
        push_cast
        ring_nf
      have h_base' :
          Integrable (fun y : ℝ => y^2 * Real.exp (-(2 * (v : ℝ))⁻¹ * y^2)) volume := by
        rw [← hb_eq]; exact h_base
      exact h_base'.comp_sub_right m
    -- Now express the target as a constant multiple of `h_inner`.
    refine (h_inner.const_mul ((2 * (v : ℝ))⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹)).congr
        (Filter.Eventually.of_forall fun x => ?_)
    -- Verify pointwise equality.
    simp only [gaussianPDFReal]
    have h2v_pos : (0 : ℝ) < 2 * v := by positivity
    have h2v_ne : (2 * (v : ℝ)) ≠ 0 := ne_of_gt h2v_pos
    have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi * v) :=
      Real.sqrt_pos.mpr (by positivity)
    have hsqrt_ne : Real.sqrt (2 * Real.pi * v) ≠ 0 := hsqrt_pos.ne'
    -- Inside `exp`: `-(x-m)^2 / (2v) = -(2v)⁻¹ * (x-m)^2`.
    have hexp_eq :
        Real.exp (-(x - m)^2 / (2 * (v : ℝ))) = Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m)^2) := by
      congr 1; field_simp
    rw [hexp_eq]
    field_simp

/-- (Phase A-3) For a Dirac measure `Measure.dirac m`, the differential entropy is `0`:
the rnDeriv vs. Lebesgue is `=ᵐ 0` (mutual singularity), and `Real.negMulLog 0 = 0`. -/
theorem differentialEntropy_dirac (m : ℝ) :
    differentialEntropy (Measure.dirac m) = 0 := by
  unfold differentialEntropy
  have h_sing : Measure.dirac m ⟂ₘ (volume : Measure ℝ) := mutuallySingular_dirac m volume
  have h_rnDeriv : (Measure.dirac m).rnDeriv volume =ᵐ[volume] 0 :=
    h_sing.rnDeriv_ae_eq_zero
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
  · simp
  · filter_upwards [h_rnDeriv] with x hx
    rw [hx]
    simp [Real.negMulLog]

/-! ## Phase B — Translation invariance / scaling -/

/-- **Translation invariance** (Phase B-1): `h(X + y) = h(X)`. -/
theorem differentialEntropy_map_add_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) (y : ℝ) :
    differentialEntropy (μ.map (· + y)) = differentialEntropy μ := by
  sorry

/-- **Scaling** (Phase B-2): `h(cX) = h(X) + log |c|`. -/
theorem differentialEntropy_map_mul_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) {c : ℝ} (hc : c ≠ 0) :
    differentialEntropy (μ.map (· * c)) = differentialEntropy μ + Real.log |c| := by
  sorry

/-- **Affine** corollary (Phase B-3): `h(aX + b) = h(X) + log |a|`. -/
theorem differentialEntropy_map_affine
    {μ : Measure ℝ} (hμ : μ ≪ volume) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    differentialEntropy (μ.map (fun x => a * x + b))
      = differentialEntropy μ + Real.log |a| := by
  sorry

/-! ## Phase C — `differentialEntropy (gaussianReal m v) = (1/2) log (2πe v)` -/

/-- (Phase C-1) Rewriting `differentialEntropy (gaussianReal m v)` in terms of
`gaussianPDFReal`. -/
theorem differentialEntropy_gaussianReal_form
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    differentialEntropy (gaussianReal m v)
      = ∫ x, gaussianPDFReal m v x * (- Real.log (gaussianPDFReal m v x)) ∂volume := by
  sorry

/-- (Phase C-2) `log (gaussianPDFReal m v x) = -(1/2) log (2πv) - (x - m)²/(2v)`. -/
theorem log_gaussianPDFReal_eq
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = -(1/2) * Real.log (2 * Real.pi * v) - (x - m)^2 / (2 * v) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2πv_pos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr h2πv_pos
  unfold gaussianPDFReal
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne']
  rw [Real.log_inv, Real.log_sqrt h2πv_pos.le, Real.log_exp]
  ring

/-- (Phase C-3, **主定理**) `h(𝒩(m, v)) = (1/2) log (2πe v)`. -/
theorem differentialEntropy_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    differentialEntropy (gaussianReal m v)
      = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  sorry

/-- (Phase C-4) `h(𝒩(0,1)) = (1/2) log (2πe)`. -/
theorem differentialEntropy_gaussianReal_std :
    differentialEntropy (gaussianReal 0 1)
      = (1/2) * Real.log (2 * Real.pi * Real.exp 1) := by
  sorry

/-! ## Phase D — Gaussian Max-entropy 定理 -/

/-- (Phase D-1, **max-entropy 主定理**) 平均 `m`, 分散 ≤ `v` の `μ ≪ volume` で
`differentialEntropy μ ≤ (1/2) log (2πe v)`. -/
theorem differentialEntropy_le_gaussian_of_variance_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m)
    (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) :
    differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  sorry

/-- (Phase D-2, 等号条件) max-entropy 等号は `μ = gaussianReal m v` のみ。 -/
theorem differentialEntropy_eq_gaussian_iff
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ = (v : ℝ)) :
    differentialEntropy μ = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
      ↔ μ = gaussianReal m v := by
  sorry

/-! ## Phase E — KL bridge / corollaries -/

/-- (Phase E-1) Closed-form KL between two Gaussians. -/
theorem klDiv_gaussianReal_gaussianReal_eq
    (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    (klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)).toReal
      = (1/2) * (Real.log ((v₂ : ℝ) / v₁) + (v₁ : ℝ) / v₂
                  + (m₁ - m₂)^2 / v₂ - 1) := by
  sorry

/-- (Phase E-2) `h(𝒩(0,1)) = (1/2) log (2π) + 1/2`. -/
theorem differentialEntropy_gaussianReal_std_val :
    differentialEntropy (gaussianReal 0 1)
      = (1/2) * Real.log (2 * Real.pi) + (1/2) := by
  sorry

end Common2026.Shannon
