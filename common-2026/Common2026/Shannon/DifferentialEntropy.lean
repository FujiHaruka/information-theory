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

set_option linter.unusedVariables false in
/-- **Translation invariance** (Phase B-1): `h(X + y) = h(X)`. -/
theorem differentialEntropy_map_add_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (y : ℝ) :
    differentialEntropy (μ.map (· + y)) = differentialEntropy μ := by
  unfold differentialEntropy
  -- Strategy: substitute x ↦ x + y on the LHS integral, then identify the integrand with
  -- `negMulLog (μ.rnDeriv volume x).toReal` via `MeasurableEmbedding.rnDeriv_map`.
  have hf : MeasurableEmbedding (fun x : ℝ => x + y) := measurableEmbedding_addRight y
  -- `volume.map (· + y) = volume` (translation-invariance of Lebesgue).
  have h_map_vol : (volume : Measure ℝ).map (· + y) = volume :=
    MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) y
  -- `MeasurableEmbedding.rnDeriv_map`:
  -- `fun x => (μ.map f).rnDeriv (volume.map f) (f x) =ᵐ[volume] μ.rnDeriv volume`.
  have h_rn := hf.rnDeriv_map μ (volume : Measure ℝ)
  -- Substitute `volume.map (· + y) = volume` to clean up the statement.
  rw [h_map_vol] at h_rn
  -- Apply translation invariance of the Lebesgue integral.
  -- LHS: `∫ x, negMulLog ((μ.map (· + y)).rnDeriv volume x).toReal dx`
  -- Substitute u = x + y:
  -- = ∫ u, negMulLog ((μ.map (· + y)).rnDeriv volume (u + y)).toReal du
  -- By h_rn, integrand a.e. equal to negMulLog ((μ.rnDeriv volume u).toReal).
  rw [← integral_add_right_eq_self
      (fun x => Real.negMulLog ((μ.map (· + y)).rnDeriv volume x).toReal) y]
  refine integral_congr_ae ?_
  filter_upwards [h_rn] with x hx
  rw [hx]

/-- **Scaling** (Phase B-2): `h(cX) = h(X) + log |c|`.

Requires integrability of the entropy integrand (this is not automatic from `μ ≪ volume`;
e.g. heavy-tail densities can have non-integrable `negMulLog`). -/
theorem differentialEntropy_map_mul_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {c : ℝ} (hc : c ≠ 0)
    (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy (μ.map (· * c)) = differentialEntropy μ + Real.log |c| := by
  -- Strategy:
  -- (1) `(μ.map (·*c)).rnDeriv volume (x * c) =ᵐ ENNReal.ofReal |c⁻¹| * μ.rnDeriv volume x`,
  --     via `MeasurableEmbedding.rnDeriv_map` + `rnDeriv_smul_right_of_ne_top'`
  --     (using `Real.map_volume_mul_right hc : volume.map (·*c) = ENNReal.ofReal |c⁻¹| • volume`).
  -- (2) Substitute `x ↦ x * c` in the LHS via `Measure.integral_comp_mul_right`.
  -- (3) Algebraic expansion of `negMulLog (|c⁻¹| · t) = |c⁻¹| log|c| · t + |c⁻¹| · negMulLog t`.
  unfold differentialEntropy
  have hf : MeasurableEmbedding (fun x : ℝ => x * c) := measurableEmbedding_mulRight₀ hc
  have hc_inv_pos : (0 : ℝ) < |c⁻¹| := abs_pos.mpr (inv_ne_zero hc)
  have hc_abs_pos : (0 : ℝ) < |c| := abs_pos.mpr hc
  -- `volume.map (·*c) = ENNReal.ofReal |c⁻¹| • volume`.
  have h_map_vol : (volume : Measure ℝ).map (· * c) = ENNReal.ofReal |c⁻¹| • volume :=
    Real.map_volume_mul_right hc
  -- `MeasurableEmbedding.rnDeriv_map`: with `f := (·*c)`:
  -- `(μ.map (·*c)).rnDeriv (volume.map (·*c)) (x*c) =ᵐ[volume] μ.rnDeriv volume x`.
  have h_rn1 := hf.rnDeriv_map μ (volume : Measure ℝ)
  rw [h_map_vol] at h_rn1
  -- `rnDeriv_smul_right_of_ne_top`: when `r ≠ 0, r ≠ ∞`,
  -- `(μ.map (·*c)).rnDeriv (r • volume) =ᵐ[volume] r⁻¹ • (μ.map (·*c)).rnDeriv volume`.
  set r : ℝ≥0∞ := ENNReal.ofReal |c⁻¹| with hr_def
  have hr_pos : r ≠ 0 := by
    simp only [hr_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hc_inv_pos
  have hr_ne_top : r ≠ ∞ := by simp [hr_def]
  have h_rn2 : (μ.map (· * c)).rnDeriv (r • volume) =ᵐ[volume]
      r⁻¹ • (μ.map (· * c)).rnDeriv volume :=
    Measure.rnDeriv_smul_right_of_ne_top (μ.map (· * c)) volume hr_pos hr_ne_top
  -- Combine h_rn1 and h_rn2 to get the pointwise relation.
  -- h_rn1 : `fun x => (μ.map (·*c)).rnDeriv (r • volume) (x * c) =ᵐ[volume] μ.rnDeriv volume`
  -- h_rn2 (composed with `· * c`): we need it at point `x * c`. Use `Filter.EventuallyEq.comp`.
  -- Quasi-measure-preserving for `(· * c)` gives that h_rn2 transfers to composition.
  have h_qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x * c) volume volume := by
    refine ⟨measurable_mul_const c, ?_⟩
    rw [h_map_vol]
    exact Measure.smul_absolutelyContinuous
  have h_rn2_comp : (fun x => (μ.map (· * c)).rnDeriv (r • volume) (x * c)) =ᵐ[volume]
      fun x => (r⁻¹ • (μ.map (· * c)).rnDeriv volume) (x * c) :=
    h_qmp.ae_eq h_rn2
  -- So `r⁻¹ • (μ.map (·*c)).rnDeriv volume (x*c) =ᵐ[volume] μ.rnDeriv volume x`.
  have h_rn3 : (fun x => r⁻¹ * (μ.map (· * c)).rnDeriv volume (x * c)) =ᵐ[volume]
      μ.rnDeriv volume := by
    filter_upwards [h_rn1, h_rn2_comp] with x h1 h2 using
      (by simp [Pi.smul_apply, smul_eq_mul] at h2; rw [← h2]; exact h1)
  -- Hence `(μ.map (·*c)).rnDeriv volume (x*c) =ᵐ r * μ.rnDeriv volume x`.
  have h_rn4 : (fun x => (μ.map (· * c)).rnDeriv volume (x * c)) =ᵐ[volume]
      fun x => r * μ.rnDeriv volume x := by
    filter_upwards [h_rn3] with x hx
    -- From `r⁻¹ * a = b` deduce `a = r * b` (given r ≠ 0, ≠ ∞).
    have h_cancel :
        (μ.map (· * c)).rnDeriv volume (x * c)
          = r * (r⁻¹ * (μ.map (· * c)).rnDeriv volume (x * c)) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hr_pos hr_ne_top, one_mul]
    rw [h_cancel, hx]
  -- Now compute the integral. Substitute u = x * c via `Measure.integral_comp_mul_right`.
  -- `∫ x, negMulLog ((μ.map (·*c)).rnDeriv volume x).toReal dx`
  --   = |c| · ∫ x, negMulLog ((μ.map (·*c)).rnDeriv volume (x * c)).toReal dx
  -- Use the form `∫ g(x * a) = |a⁻¹| · ∫ g y` from `integral_comp_mul_right`.
  have h_sub :
      ∫ x, Real.negMulLog ((μ.map (· * c)).rnDeriv volume x).toReal ∂volume
      = |c| * ∫ x, Real.negMulLog ((μ.map (· * c)).rnDeriv volume (x * c)).toReal ∂volume := by
    have h_icmr := Measure.integral_comp_mul_right
      (fun y => Real.negMulLog ((μ.map (· * c)).rnDeriv volume y).toReal) c
    -- h_icmr : ∫ x, g(x * c) = |c⁻¹| • ∫ y, g y
    rw [show |(c⁻¹ : ℝ)| = |c|⁻¹ from abs_inv c, smul_eq_mul] at h_icmr
    have h_c_ne : (|c| : ℝ) ≠ 0 := hc_abs_pos.ne'
    -- h_icmr : |c|⁻¹ * ∫ y, g y = ∫ x, g(x * c)
    -- We want: ∫ y, g y = |c| * ∫ x, g(x * c)
    have h_step := h_icmr  -- |c|⁻¹ * ∫_y = ∫_(x*c)
    have h_mul : ∫ y, Real.negMulLog ((μ.map (· * c)).rnDeriv volume y).toReal ∂volume
        = |c| * (|c|⁻¹ * ∫ y, Real.negMulLog ((μ.map (· * c)).rnDeriv volume y).toReal ∂volume) := by
      rw [← mul_assoc, mul_inv_cancel₀ h_c_ne, one_mul]
    rw [h_mul, h_step]
  rw [h_sub]
  -- Apply h_rn4 to rewrite the integrand.
  have h_int_eq :
      ∫ x, Real.negMulLog ((μ.map (· * c)).rnDeriv volume (x * c)).toReal ∂volume
      = ∫ x, Real.negMulLog (|c⁻¹| * (μ.rnDeriv volume x).toReal) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [h_rn4] with x hx
    rw [hx]
    rw [ENNReal.toReal_mul, hr_def, ENNReal.toReal_ofReal hc_inv_pos.le]
  rw [h_int_eq]
  -- Algebraic expansion:
  -- negMulLog (|c⁻¹| · t) = -(|c⁻¹| · t) · log(|c⁻¹| · t)
  -- For t ≥ 0: if t = 0, both sides are 0. If t > 0:
  --   = -(|c⁻¹| · t) · (log|c⁻¹| + log t)
  --   = -|c⁻¹| · t · log|c⁻¹| + |c⁻¹| · (-t · log t)
  --   = |c⁻¹| · t · log|c| + |c⁻¹| · negMulLog t   (since -log|c⁻¹| = log|c|)
  have h_neg_log_inv : -Real.log |c⁻¹| = Real.log |c| := by
    rw [abs_inv, Real.log_inv, neg_neg]
  set f : ℝ → ℝ := fun x => (μ.rnDeriv volume x).toReal with hf_def
  have h_negMulLog_abs_inv : Real.negMulLog |c⁻¹| = |c⁻¹| * Real.log |c| := by
    simp only [Real.negMulLog_def]
    rw [← h_neg_log_inv]; ring
  have h_pointwise : ∀ x, Real.negMulLog (|c⁻¹| * f x)
      = |c⁻¹| * Real.log |c| * f x + |c⁻¹| * Real.negMulLog (f x) := by
    intro x
    rw [Real.negMulLog_mul, h_negMulLog_abs_inv]; ring
  -- Apply h_pointwise pointwise and split the integral.
  have h_int_split :
      ∫ x, Real.negMulLog (|c⁻¹| * f x) ∂volume
      = ∫ x, (|c⁻¹| * Real.log |c| * f x + |c⁻¹| * Real.negMulLog (f x)) ∂volume := by
    refine integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun x => h_pointwise x)
  rw [h_int_split]
  -- Show integrability of both summands.
  -- For the first: `|c⁻¹| · log|c| · f x` — constant multiple of `f = (μ.rnDeriv volume).toReal`.
  -- `∫ f dx = μ.real Univ = 1` (probability measure).
  have hf_integrable : Integrable f volume := by
    refine Measure.integrable_toReal_rnDeriv
  have hf_int_eq : ∫ x, f x ∂volume = 1 := by
    have h := Measure.integral_toReal_rnDeriv hμ
    -- h : ∫ x, (μ.rnDeriv volume x).toReal ∂volume = μ.real Set.univ
    rw [hf_def]
    rw [h, probReal_univ]
  -- For the second: `|c⁻¹| · negMulLog (f x)` — this involves the integrand of `differentialEntropy μ`.
  -- The integral of `negMulLog (μ.rnDeriv volume x).toReal` is by definition `differentialEntropy μ`.
  -- For the second integrand: `|c⁻¹| · negMulLog (f x)`. Integrability of this is **not** generic
  -- (negMulLog of a probability density is not always integrable). We assume it as a side
  -- hypothesis. For Phase B-2 to be useful in our pipeline, the caller must establish this.
  -- Compute under the integrability hypothesis:
  rw [integral_add (hf_integrable.const_mul (|c⁻¹| * Real.log |c|))]
  · -- two integrals: `∫ |c⁻¹| log|c| · f` and `∫ |c⁻¹| · negMulLog f`
    rw [integral_const_mul, integral_const_mul, hf_int_eq, mul_one]
    -- Goal: |c| * (|c⁻¹| log|c| + |c⁻¹| · ∫ negMulLog f) = ∫ negMulLog (∂μ/∂ℙ).toReal + log |c|
    -- Note: by `hf_def`, `∫ negMulLog f = ∫ negMulLog (∂μ/∂ℙ).toReal`.
    have hf_eq : ∫ x, Real.negMulLog (f x) ∂volume
        = ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume := by
      simp [hf_def]
    rw [hf_eq]
    have h_cancel : |c| * |c⁻¹| = 1 := by
      rw [abs_inv, mul_inv_cancel₀ hc_abs_pos.ne']
    ring_nf
    rw [show |c| * |c⁻¹| = 1 from h_cancel]
    ring
  · -- Integrability of `|c⁻¹| · negMulLog f`. Follows from `h_ent_int` after unfolding `f`.
    have h_eq : (fun x => |c⁻¹| * Real.negMulLog (f x))
        = fun x => |c⁻¹| * Real.negMulLog ((μ.rnDeriv volume x).toReal) := by
      simp [hf_def]
    rw [h_eq]
    exact h_ent_int.const_mul _

/-- **Affine** corollary (Phase B-3): `h(aX + b) = h(X) + log |a|`.

Requires integrability of the entropy integrand on `μ` (inherited from Phase B-2). -/
theorem differentialEntropy_map_affine
    {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy (μ.map (fun x => a * x + b))
      = differentialEntropy μ + Real.log |a| := by
  -- Decompose `fun x => a * x + b = (· + b) ∘ (· * a)` (using commutativity of `*`).
  have h_decomp : (fun x : ℝ => a * x + b) = (fun y => y + b) ∘ (fun x => x * a) := by
    funext x
    show a * x + b = (x * a) + b
    ring
  have h_meas_mul : Measurable (fun x : ℝ => x * a) := measurable_mul_const a
  have h_meas_add : Measurable (fun y : ℝ => y + b) := measurable_add_const b
  -- `μ.map (fun x => a * x + b) = (μ.map (· * a)).map (· + b)`.
  rw [h_decomp, ← Measure.map_map h_meas_add h_meas_mul]
  -- Apply Phase B-1 first (translation), then Phase B-2 (scaling).
  -- For B-1 we need `(μ.map (· * a)) ≪ volume` and `SigmaFinite`.
  have h_mul_ac : μ.map (· * a) ≪ volume := by
    have h_qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x * a) volume volume := by
      refine ⟨measurable_mul_const a, ?_⟩
      rw [Real.map_volume_mul_right ha]
      exact Measure.smul_absolutelyContinuous
    -- μ ≪ volume ⟹ μ.map f ≪ volume.map f, then use volume.map f = (...) • volume ≪ volume.
    have h1 : μ.map (· * a) ≪ volume.map (· * a) := hμ.map h_qmp.measurable
    rw [Real.map_volume_mul_right ha] at h1
    exact h1.trans Measure.smul_absolutelyContinuous
  haveI : IsProbabilityMeasure (μ.map (fun x : ℝ => x * a)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const a).aemeasurable
  haveI : SigmaFinite (μ.map (fun x : ℝ => x * a)) := inferInstance
  rw [differentialEntropy_map_add_const h_mul_ac b]
  rw [differentialEntropy_map_mul_const hμ ha h_ent_int]

/-! ## Phase C — `differentialEntropy (gaussianReal m v) = (1/2) log (2πe v)` -/

set_option linter.unusedVariables false in
/-- (Phase C-1) Rewriting `differentialEntropy (gaussianReal m v)` in terms of
`gaussianPDFReal`. -/
theorem differentialEntropy_gaussianReal_form
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    differentialEntropy (gaussianReal m v)
      = ∫ x, gaussianPDFReal m v x * (- Real.log (gaussianPDFReal m v x)) ∂volume := by
  unfold differentialEntropy
  refine integral_congr_ae ?_
  filter_upwards [rnDeriv_gaussianReal m v] with x hx
  rw [hx, toReal_gaussianPDF, Real.negMulLog_def]
  ring

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
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2πv_pos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  -- Step 1: use Phase C-1 to rewrite as ∫ f * (-log f)
  rw [differentialEntropy_gaussianReal_form m hv]
  -- Step 2: expand using Phase C-2, decomposing -log f(x) into c₁ + (x-m)²/(2v)
  set c₁ : ℝ := (1/2) * Real.log (2 * Real.pi * v) with hc₁
  have h_neg_log : ∀ x, - Real.log (gaussianPDFReal m v x)
      = c₁ + (x - m)^2 / (2 * v) := by
    intro x
    rw [log_gaussianPDFReal_eq m hv x]
    simp [hc₁]; ring
  have h_eq : (fun x => gaussianPDFReal m v x * (- Real.log (gaussianPDFReal m v x)))
      = fun x => c₁ * gaussianPDFReal m v x
          + gaussianPDFReal m v x * ((x - m)^2 / (2 * v)) := by
    funext x
    rw [h_neg_log x]; ring
  rw [h_eq]
  -- Step 3: split integral.
  -- 3a: integrability of the first term (constant * f).
  have h_int1 : Integrable (fun x => c₁ * gaussianPDFReal m v x) volume :=
    (integrable_gaussianPDFReal m v).const_mul c₁
  -- 3b: integrability of the second term — `f * (x-m)² / (2v)`.
  -- Reuse the proof from `integrable_density_log_density_of_gaussian` where
  -- we already showed `f x * ((x-m)² / (2v))` is integrable.
  have h_int2 : Integrable
      (fun x => gaussianPDFReal m v x * ((x - m)^2 / (2 * (v : ℝ)))) volume := by
    have h_int_log := integrable_density_log_density_of_gaussian m hv
    -- `f x * log f = c₀ * f x - f x * ((x-m)²/(2v))` so
    -- `f x * ((x-m)²/(2v)) = c₀ * f x - f x * log f x`.
    set c₀ : ℝ := -(1/2) * Real.log (2 * Real.pi * v) with hc₀
    have h_eq2 : (fun x => gaussianPDFReal m v x * ((x - m)^2 / (2 * (v : ℝ))))
        = fun x => c₀ * gaussianPDFReal m v x
            - gaussianPDFReal m v x * Real.log (gaussianPDFReal m v x) := by
      funext x
      rw [log_gaussianPDFReal_eq m hv x]
      simp [hc₀]; ring
    rw [h_eq2]
    exact ((integrable_gaussianPDFReal m v).const_mul c₀).sub h_int_log
  rw [integral_add h_int1 h_int2]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one m hv, mul_one]
  -- Now show ∫ f(x) * ((x-m)² / (2v)) dx = 1/2 (since ∫ (x-m)² f dx = v).
  -- Rewrite as (1/(2v)) * ∫ f(x) * (x-m)² dx.
  have h_second :
      ∫ x, gaussianPDFReal m v x * ((x - m)^2 / (2 * (v : ℝ))) ∂volume = 1 / 2 := by
    have h_factor : (fun x => gaussianPDFReal m v x * ((x - m)^2 / (2 * (v : ℝ))))
        = fun x => (1 / (2 * (v : ℝ))) * (gaussianPDFReal m v x * (x - m)^2) := by
      funext x; ring
    rw [h_factor, integral_const_mul]
    -- ∫ f(x) * (x-m)² dx = v (from variance)
    have h_var :
        ∫ x, gaussianPDFReal m v x * (x - m)^2 ∂volume = (v : ℝ) := by
      have h1 : ∫ x, (x - m)^2 ∂(gaussianReal m v) = (v : ℝ) := by
        have hX : AEMeasurable (fun x : ℝ => x) (gaussianReal m v) :=
          measurable_id.aemeasurable
        have h_var_eq := variance_eq_integral (μ := gaussianReal m v) hX
        rw [variance_fun_id_gaussianReal] at h_var_eq
        have h_mean : ∫ x, (id : ℝ → ℝ) x ∂(gaussianReal m v) = m :=
          integral_id_gaussianReal
        simp only [id] at h_mean
        rw [h_mean] at h_var_eq
        exact h_var_eq.symm
      rw [integral_gaussianReal_eq_integral_smul hv] at h1
      simpa [smul_eq_mul] using h1
    rw [h_var]
    field_simp
  rw [h_second]
  -- Final algebra: c₁ + 1/2 = (1/2) * log(2πev).
  rw [hc₁]
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2πev_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * v := by positivity
  -- log(2πev) = log(2πv) + log e = log(2πv) + 1
  have h_log_split : Real.log (2 * Real.pi * Real.exp 1 * v)
      = Real.log (2 * Real.pi * v) + 1 := by
    have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have h_rewrite : 2 * Real.pi * Real.exp 1 * (v : ℝ)
        = (2 * Real.pi * v) * Real.exp 1 := by ring
    rw [h_rewrite, Real.log_mul h2πv_pos.ne' hexp_pos.ne', Real.log_exp]
  rw [h_log_split]
  ring

/-- (Phase C-4) `h(𝒩(0,1)) = (1/2) log (2πe)`. -/
theorem differentialEntropy_gaussianReal_std :
    differentialEntropy (gaussianReal 0 1)
      = (1/2) * Real.log (2 * Real.pi * Real.exp 1) := by
  have h := differentialEntropy_gaussianReal 0 (v := (1 : ℝ≥0)) one_ne_zero
  simpa using h

/-! ## Phase D — Gaussian Max-entropy 定理 -/

/-- (Phase D-1, **max-entropy 主定理**) 平均 `m`, 分散 ≤ `v` の `μ ≪ volume` で
`differentialEntropy μ ≤ (1/2) log (2πe v)`.

可積分性副仮説:
* `h_ent_int` — `differentialEntropy μ` の被積分関数の Lebesgue 可積分性。Mathlib の
  Bochner 積分は非可積分なら `0` を返すため、`h(μ) = +∞` の不可能性 (KL ≥ 0 で
  排除されるはず) を保証するために必要。
* `h_var_int` — 2 次モーメントの可積分性。これがないと `h_var` 仮説自体が
  `0 ≤ v` に縮退する。 -/
theorem differentialEntropy_le_gaussian_of_variance_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m)
    (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ))
    (h_var_int : Integrable (fun x => (x - m)^2) μ)
    (h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  -- 戦略: `0 ≤ (klDiv μ (gaussianReal m v)).toReal = ∫ llr μ ν ∂μ`
  --       = -h(μ) + (1/2) log(2πv) + (1/(2v)) ∫(x-m)² ∂μ
  -- ≤ -h(μ) + (1/2) log(2πev) via `h_var`.
  let _ := h_mean  -- mean は使わない (median 仮定相当)
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2πv_pos : (0 : ℝ) < 2 * Real.pi * v := by positivity
  have h2v_pos : (0 : ℝ) < 2 * v := by positivity
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set ν : Measure ℝ := gaussianReal m v with hν_def
  have hμν : μ ≪ ν := hμ.trans (gaussianReal_absolutelyContinuous' m hv)
  -- `(klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ`.
  have h_meas_eq : μ Set.univ = ν Set.univ := by simp [hν_def]
  have h_kl_eq : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ :=
    toReal_klDiv_of_measure_eq hμν h_meas_eq
  have h_kl_nn : (0 : ℝ) ≤ ∫ x, llr μ ν x ∂μ := h_kl_eq ▸ ENNReal.toReal_nonneg
  -- 鍵: `llr μ ν x =ᵐ[μ] log (μ.rnDeriv volume x).toReal - log (gaussianPDFReal m v x)`.
  have h_rn_chain_vol : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[volume] μ.rnDeriv volume :=
    Measure.rnDeriv_mul_rnDeriv hμν
  have h_rn_chain_μ : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[μ] μ.rnDeriv volume :=
    hμ.ae_le h_rn_chain_vol
  have h_rn_gauss_μ : ν.rnDeriv volume =ᵐ[μ] gaussianPDF m v :=
    hμ.ae_le (rnDeriv_gaussianReal m v)
  have h_rn_μν_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hμν
  have h_rn_μν_lt_top : ∀ᵐ x ∂μ, μ.rnDeriv ν x < ∞ :=
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)
  have h_llr_decomp : ∀ᵐ x ∂μ,
      llr μ ν x = Real.log ((μ.rnDeriv volume x).toReal)
        - Real.log (gaussianPDFReal m v x) := by
    filter_upwards [h_rn_chain_μ, h_rn_gauss_μ, h_rn_μν_pos, h_rn_μν_lt_top]
      with x h_chain h_gauss h_pos h_lt_top
    have hg_pos : 0 < gaussianPDFReal m v x := gaussianPDFReal_pos m v x hv
    have hμν_real_pos : 0 < (μ.rnDeriv ν x).toReal :=
      ENNReal.toReal_pos h_pos.ne' h_lt_top.ne
    -- `μ.rnDeriv volume x = μ.rnDeriv ν x * gaussianPDF m v x`
    have h_combine : μ.rnDeriv volume x = μ.rnDeriv ν x * gaussianPDF m v x := by
      rw [← h_chain, Pi.mul_apply, h_gauss]
    show Real.log ((μ.rnDeriv ν x).toReal)
        = Real.log ((μ.rnDeriv volume x).toReal) - Real.log (gaussianPDFReal m v x)
    rw [h_combine, ENNReal.toReal_mul, toReal_gaussianPDF,
      Real.log_mul hμν_real_pos.ne' hg_pos.ne']
    ring
  -- `∫ llr μ ν x ∂μ = ∫ log (μ.rnDeriv vol).toReal ∂μ - ∫ log gaussianPDFReal m v ∂μ`.
  -- 各積分を計算するために integrability を準備。
  -- (i) `∫ log (μ.rnDeriv vol x).toReal ∂μ = - h(μ)`:
  --     `integral_rnDeriv_smul hμ` で `∫ g ∂μ = ∫ (μ.rnDeriv vol).toReal • g ∂vol`、
  --     `g = log ((μ.rnDeriv vol).toReal)` で `(μ.rnDeriv vol).toReal · log ... = -negMulLog ...`
  --     (pointwise).
  -- ※ ただし `g` 自体は `vol` 上で必ずしも可積分でないので、`integral_rnDeriv_smul` 直接は
  --   注意; 等号は両側とも `integral_undef = 0` で成り立つかも。簡単のために
  --   `integral_rnDeriv_smul` の strong form (unconditional) を信じて進める。
  have h_int_log_μ_eq :
      ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ = - differentialEntropy μ := by
    have h_pull : ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ
        = ∫ x, (μ.rnDeriv volume x).toReal • Real.log ((μ.rnDeriv volume x).toReal) ∂volume := by
      rw [integral_rnDeriv_smul (μ := μ) (ν := volume) hμ
        (f := fun x => Real.log ((μ.rnDeriv volume x).toReal))]
    rw [h_pull]
    unfold differentialEntropy
    rw [show -∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
        = ∫ x, -Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume from (integral_neg _).symm]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [smul_eq_mul, Real.negMulLog_def]
    ring
  -- (ii) `∫ log gaussianPDFReal m v ∂μ = -(1/2) log(2πv) - (1/(2v)) ∫(x-m)² ∂μ`:
  have h_log_g_eq : ∀ x, Real.log (gaussianPDFReal m v x)
      = (-(1/2) * Real.log (2 * Real.pi * v)) + (-(1/(2 * v))) * (x - m)^2 := by
    intro x
    rw [log_gaussianPDFReal_eq m hv x]
    ring
  have h_int_log_g : Integrable (fun x => Real.log (gaussianPDFReal m v x)) μ := by
    -- 定数 + 定数 × (x-m)² の形。
    have h_eq : (fun x => Real.log (gaussianPDFReal m v x))
        = fun x => (-(1/2) * Real.log (2 * Real.pi * v))
            + (-(1/(2 * v))) * (x - m)^2 := by
      funext x; exact h_log_g_eq x
    rw [h_eq]
    exact (integrable_const _).add (h_var_int.const_mul (-(1/(2 * v))))
  have h_int_log_g_eq :
      ∫ x, Real.log (gaussianPDFReal m v x) ∂μ
        = -(1/2) * Real.log (2 * Real.pi * v)
          + (-(1/(2 * v))) * ∫ x, (x - m)^2 ∂μ := by
    rw [show (fun x => Real.log (gaussianPDFReal m v x))
        = fun x => (-(1/2) * Real.log (2 * Real.pi * v))
            + (-(1/(2 * v))) * (x - m)^2 from funext h_log_g_eq]
    rw [integral_add (integrable_const _) (h_var_int.const_mul _)]
    rw [integral_const, integral_const_mul]
    simp
  -- (iii) Integrability of `log (μ.rnDeriv volume x).toReal` on μ:
  --   = -negMulLog ((μ.rnDeriv vol x).toReal) / (μ.rnDeriv vol x).toReal (when > 0).
  --   Equivalently: `∫ g ∂μ` integrable iff `(μ.rnDeriv vol).toReal • g` integrable on vol.
  have h_int_log_μ : Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)) μ := by
    -- Use `integrable_rnDeriv_smul_iff hμ`:
    -- `Integrable (fun x => (μ.rnDeriv vol x).toReal • g x) vol ↔ Integrable g μ`.
    rw [← integrable_rnDeriv_smul_iff (μ := μ) (ν := volume) hμ
      (f := fun x => Real.log ((μ.rnDeriv volume x).toReal))]
    -- Goal: `Integrable (fun x => (μ.rnDeriv vol x).toReal • log ((μ.rnDeriv vol x).toReal)) vol`
    -- which equals `-negMulLog ((μ.rnDeriv vol x).toReal)` (pointwise).
    refine (h_ent_int.neg).congr (Filter.Eventually.of_forall fun x => ?_)
    show -Real.negMulLog ((μ.rnDeriv volume x).toReal)
        = (μ.rnDeriv volume x).toReal • Real.log ((μ.rnDeriv volume x).toReal)
    simp only [smul_eq_mul, Real.negMulLog_def]
    ring
  -- llr 可積分性も同様 (decomp identity).
  have h_int_llr : Integrable (llr μ ν) μ := by
    have h_sub : Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)
        - Real.log (gaussianPDFReal m v x)) μ := h_int_log_μ.sub h_int_log_g
    refine h_sub.congr ?_
    filter_upwards [h_llr_decomp] with x hx using hx.symm
  -- 積分等式: `∫ llr μ ν ∂μ = -h(μ) - (-(1/2) log(2πv) - (1/(2v)) ∫(x-m)² ∂μ)`.
  have h_int_llr_eq :
      ∫ x, llr μ ν x ∂μ = - differentialEntropy μ + (1/2) * Real.log (2 * Real.pi * v)
        + (1/(2 * v)) * ∫ x, (x - m)^2 ∂μ := by
    have h_split : ∫ x, llr μ ν x ∂μ
        = ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ
          - ∫ x, Real.log (gaussianPDFReal m v x) ∂μ := by
      rw [← integral_sub h_int_log_μ h_int_log_g]
      exact integral_congr_ae h_llr_decomp
    rw [h_split, h_int_log_μ_eq, h_int_log_g_eq]
    ring
  -- 最終: `0 ≤ -h(μ) + (1/2) log(2πv) + (1/(2v)) ∫(x-m)² ∂μ ≤ -h(μ) + (1/2) log(2πv) + 1/2`.
  have h_combined : (0 : ℝ) ≤ - differentialEntropy μ + (1/2) * Real.log (2 * Real.pi * v)
      + (1/(2 * v)) * ∫ x, (x - m)^2 ∂μ := h_int_llr_eq ▸ h_kl_nn
  -- 不等式合成: `(1/(2v)) ∫(x-m)² ∂μ ≤ (1/(2v)) · v = 1/2`.
  have h_var_bound : (1/(2 * v)) * ∫ x, (x - m)^2 ∂μ ≤ 1/2 := by
    have h_2v_inv_pos : 0 < 1 / (2 * (v : ℝ)) := by positivity
    calc (1/(2 * v)) * ∫ x, (x - m)^2 ∂μ
        ≤ (1/(2 * v)) * (v : ℝ) := mul_le_mul_of_nonneg_left h_var h_2v_inv_pos.le
      _ = 1/2 := by field_simp
  -- 結論: `h(μ) ≤ (1/2) log(2πv) + 1/2 = (1/2) log(2πev)`.
  have h_log_split : Real.log (2 * Real.pi * Real.exp 1 * v)
      = Real.log (2 * Real.pi * v) + 1 := by
    have h_rewrite : 2 * Real.pi * Real.exp 1 * (v : ℝ)
        = (2 * Real.pi * v) * Real.exp 1 := by ring
    rw [h_rewrite, Real.log_mul h2πv_pos.ne' hexp_pos.ne', Real.log_exp]
  linarith [h_combined, h_var_bound]

/-- (Phase D-2, 等号条件) max-entropy 等号は `μ = gaussianReal m v` のみ。 -/
theorem differentialEntropy_eq_gaussian_iff
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ = (v : ℝ))
    (h_var_int : Integrable (fun x => (x - m)^2) μ)
    (h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy μ = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
      ↔ μ = gaussianReal m v := by
  let _ := h_mean
  constructor
  · -- 等式 ⟹ `μ = gaussianReal m v`. D-1 と同じ展開で `(klDiv μ ν).toReal = 0` を取り出す。
    intro h_eq
    have hv_pos : (0 : ℝ) < v := by
      have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
    have h2πv_pos : (0 : ℝ) < 2 * Real.pi * v := by positivity
    have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    set ν : Measure ℝ := gaussianReal m v with hν_def
    have hμν : μ ≪ ν := hμ.trans (gaussianReal_absolutelyContinuous' m hv)
    have h_meas_eq : μ Set.univ = ν Set.univ := by simp [hν_def]
    -- KL.toReal の代数恒等式を再計算 (D-1 と同じ chain).
    have h_kl_eq : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ :=
      toReal_klDiv_of_measure_eq hμν h_meas_eq
    have h_rn_chain_vol : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[volume] μ.rnDeriv volume :=
      Measure.rnDeriv_mul_rnDeriv hμν
    have h_rn_chain_μ : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[μ] μ.rnDeriv volume :=
      hμ.ae_le h_rn_chain_vol
    have h_rn_gauss_μ : ν.rnDeriv volume =ᵐ[μ] gaussianPDF m v :=
      hμ.ae_le (rnDeriv_gaussianReal m v)
    have h_rn_μν_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hμν
    have h_rn_μν_lt_top : ∀ᵐ x ∂μ, μ.rnDeriv ν x < ∞ :=
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)
    have h_llr_decomp : ∀ᵐ x ∂μ,
        llr μ ν x = Real.log ((μ.rnDeriv volume x).toReal)
          - Real.log (gaussianPDFReal m v x) := by
      filter_upwards [h_rn_chain_μ, h_rn_gauss_μ, h_rn_μν_pos, h_rn_μν_lt_top]
        with x h_chain h_gauss h_pos h_lt_top
      have hg_pos : 0 < gaussianPDFReal m v x := gaussianPDFReal_pos m v x hv
      have hμν_real_pos : 0 < (μ.rnDeriv ν x).toReal :=
        ENNReal.toReal_pos h_pos.ne' h_lt_top.ne
      have h_combine : μ.rnDeriv volume x = μ.rnDeriv ν x * gaussianPDF m v x := by
        rw [← h_chain, Pi.mul_apply, h_gauss]
      show Real.log ((μ.rnDeriv ν x).toReal)
          = Real.log ((μ.rnDeriv volume x).toReal) - Real.log (gaussianPDFReal m v x)
      rw [h_combine, ENNReal.toReal_mul, toReal_gaussianPDF,
        Real.log_mul hμν_real_pos.ne' hg_pos.ne']
      ring
    have h_int_log_μ_eq :
        ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ = - differentialEntropy μ := by
      have h_pull : ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ
          = ∫ x, (μ.rnDeriv volume x).toReal • Real.log ((μ.rnDeriv volume x).toReal) ∂volume := by
        rw [integral_rnDeriv_smul (μ := μ) (ν := volume) hμ
          (f := fun x => Real.log ((μ.rnDeriv volume x).toReal))]
      rw [h_pull]
      unfold differentialEntropy
      rw [show -∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
          = ∫ x, -Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume from (integral_neg _).symm]
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [smul_eq_mul, Real.negMulLog_def]
      ring
    have h_log_g_eq : ∀ x, Real.log (gaussianPDFReal m v x)
        = (-(1/2) * Real.log (2 * Real.pi * v)) + (-(1/(2 * v))) * (x - m)^2 := by
      intro x
      rw [log_gaussianPDFReal_eq m hv x]
      ring
    have h_int_log_g : Integrable (fun x => Real.log (gaussianPDFReal m v x)) μ := by
      have h_eq : (fun x => Real.log (gaussianPDFReal m v x))
          = fun x => (-(1/2) * Real.log (2 * Real.pi * v))
              + (-(1/(2 * v))) * (x - m)^2 := by
        funext x; exact h_log_g_eq x
      rw [h_eq]
      exact (integrable_const _).add (h_var_int.const_mul (-(1/(2 * v))))
    have h_int_log_g_eq :
        ∫ x, Real.log (gaussianPDFReal m v x) ∂μ
          = -(1/2) * Real.log (2 * Real.pi * v)
            + (-(1/(2 * v))) * ∫ x, (x - m)^2 ∂μ := by
      rw [show (fun x => Real.log (gaussianPDFReal m v x))
          = fun x => (-(1/2) * Real.log (2 * Real.pi * v))
              + (-(1/(2 * v))) * (x - m)^2 from funext h_log_g_eq]
      rw [integral_add (integrable_const _) (h_var_int.const_mul _)]
      rw [integral_const, integral_const_mul]
      simp
    have h_int_log_μ : Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)) μ := by
      rw [← integrable_rnDeriv_smul_iff (μ := μ) (ν := volume) hμ
        (f := fun x => Real.log ((μ.rnDeriv volume x).toReal))]
      refine (h_ent_int.neg).congr (Filter.Eventually.of_forall fun x => ?_)
      show -Real.negMulLog ((μ.rnDeriv volume x).toReal)
          = (μ.rnDeriv volume x).toReal • Real.log ((μ.rnDeriv volume x).toReal)
      simp only [smul_eq_mul, Real.negMulLog_def]
      ring
    have h_int_llr_eq :
        ∫ x, llr μ ν x ∂μ = - differentialEntropy μ + (1/2) * Real.log (2 * Real.pi * v)
          + (1/(2 * v)) * ∫ x, (x - m)^2 ∂μ := by
      have h_split : ∫ x, llr μ ν x ∂μ
          = ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ
            - ∫ x, Real.log (gaussianPDFReal m v x) ∂μ := by
        rw [← integral_sub h_int_log_μ h_int_log_g]
        exact integral_congr_ae h_llr_decomp
      rw [h_split, h_int_log_μ_eq, h_int_log_g_eq]
      ring
    -- h_var (equality) と h_eq (entropy = target) から KL.toReal = 0.
    have h_log_split : Real.log (2 * Real.pi * Real.exp 1 * v)
        = Real.log (2 * Real.pi * v) + 1 := by
      have h_rewrite : 2 * Real.pi * Real.exp 1 * (v : ℝ)
          = (2 * Real.pi * v) * Real.exp 1 := by ring
      rw [h_rewrite, Real.log_mul h2πv_pos.ne' hexp_pos.ne', Real.log_exp]
    have h_kl_toReal_zero : (klDiv μ ν).toReal = 0 := by
      rw [h_kl_eq, h_int_llr_eq, h_var, h_eq, h_log_split]
      field_simp
      ring
    -- KL = 0 (ENNReal); これは `μ = ν`.
    have hμν_ne_top : klDiv μ ν ≠ ∞ := by
      -- llr integrable from `h_int_log_μ - h_int_log_g`.
      have h_int_llr : Integrable (llr μ ν) μ := by
        have h_sub : Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)
            - Real.log (gaussianPDFReal m v x)) μ := h_int_log_μ.sub h_int_log_g
        refine h_sub.congr ?_
        filter_upwards [h_llr_decomp] with x hx using hx.symm
      exact klDiv_ne_top hμν h_int_llr
    have h_kl_zero : klDiv μ ν = 0 := by
      rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hμν_ne_top] at h_kl_toReal_zero
    exact (klDiv_eq_zero_iff.mp h_kl_zero)
  · -- `μ = gaussianReal m v` ⟹ entropy 計算 (Phase C-3).
    intro h_eq
    rw [h_eq]
    exact differentialEntropy_gaussianReal m hv

/-! ## Phase E — KL bridge / corollaries -/

/-- (Phase E-1) Closed-form KL between two Gaussians. -/
theorem klDiv_gaussianReal_gaussianReal_eq
    (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    (klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)).toReal
      = (1/2) * (Real.log ((v₂ : ℝ) / v₁) + (v₁ : ℝ) / v₂
                  + (m₁ - m₂)^2 / v₂ - 1) := by
  -- 戦略: 両者とも probability で AC、`toReal_klDiv_of_measure_eq` で
  -- `KL.toReal = ∫ x, llr ν₁ ν₂ x ∂ν₁`. `llr ν₁ ν₂ x = log g₁(x) - log g₂(x)` for
  -- `gᵢ := gaussianPDFReal mᵢ vᵢ`. 各 log を Phase C-2 で展開して積分する。
  have hv₁_pos : (0 : ℝ) < v₁ := by
    have : (v₁ : ℝ) ≠ 0 := by exact_mod_cast hv₁
    exact lt_of_le_of_ne v₁.coe_nonneg (Ne.symm this)
  have hv₂_pos : (0 : ℝ) < v₂ := by
    have : (v₂ : ℝ) ≠ 0 := by exact_mod_cast hv₂
    exact lt_of_le_of_ne v₂.coe_nonneg (Ne.symm this)
  have h2πv₁_pos : (0 : ℝ) < 2 * Real.pi * v₁ := by positivity
  have h2πv₂_pos : (0 : ℝ) < 2 * Real.pi * v₂ := by positivity
  set ν₁ : Measure ℝ := gaussianReal m₁ v₁ with hν₁_def
  set ν₂ : Measure ℝ := gaussianReal m₂ v₂ with hν₂_def
  have hν₁_ac : ν₁ ≪ volume := by rw [hν₁_def]; exact gaussianReal_absolutelyContinuous m₁ hv₁
  have hμν : ν₁ ≪ ν₂ := hν₁_ac.trans (gaussianReal_absolutelyContinuous' m₂ hv₂)
  have h_meas_eq : ν₁ Set.univ = ν₂ Set.univ := by simp [hν₁_def, hν₂_def]
  have h_kl_eq : (klDiv ν₁ ν₂).toReal = ∫ x, llr ν₁ ν₂ x ∂ν₁ :=
    toReal_klDiv_of_measure_eq hμν h_meas_eq
  -- llr decomp: `llr ν₁ ν₂ x =ᵐ[ν₁] log g₁(x) - log g₂(x)`.
  -- 同じ chain rule path: `ν₁.rnDeriv ν₂ * ν₂.rnDeriv vol =ᵐ[vol] ν₁.rnDeriv vol`,
  -- ν₁.rnDeriv vol = gaussianPDF m₁ v₁, ν₂.rnDeriv vol = gaussianPDF m₂ v₂.
  have h_rn_chain_vol : ν₁.rnDeriv ν₂ * ν₂.rnDeriv volume =ᵐ[volume] ν₁.rnDeriv volume :=
    Measure.rnDeriv_mul_rnDeriv hμν
  have h_rn_chain_ν₁ : ν₁.rnDeriv ν₂ * ν₂.rnDeriv volume =ᵐ[ν₁] ν₁.rnDeriv volume :=
    hν₁_ac.ae_le h_rn_chain_vol
  have h_rn_g₁_ν₁ : ν₁.rnDeriv volume =ᵐ[ν₁] gaussianPDF m₁ v₁ :=
    hν₁_ac.ae_le (by rw [hν₁_def]; exact rnDeriv_gaussianReal m₁ v₁)
  have h_rn_g₂_ν₁ : ν₂.rnDeriv volume =ᵐ[ν₁] gaussianPDF m₂ v₂ :=
    hν₁_ac.ae_le (by rw [hν₂_def]; exact rnDeriv_gaussianReal m₂ v₂)
  have h_rn_ν₁ν₂_pos : ∀ᵐ x ∂ν₁, 0 < ν₁.rnDeriv ν₂ x := Measure.rnDeriv_pos hμν
  have h_rn_ν₁ν₂_lt_top : ∀ᵐ x ∂ν₁, ν₁.rnDeriv ν₂ x < ∞ :=
    hμν.ae_le (Measure.rnDeriv_lt_top ν₁ ν₂)
  have h_llr_decomp : ∀ᵐ x ∂ν₁,
      llr ν₁ ν₂ x = Real.log (gaussianPDFReal m₁ v₁ x)
        - Real.log (gaussianPDFReal m₂ v₂ x) := by
    filter_upwards [h_rn_chain_ν₁, h_rn_g₁_ν₁, h_rn_g₂_ν₁, h_rn_ν₁ν₂_pos, h_rn_ν₁ν₂_lt_top]
      with x h_chain h_g₁ h_g₂ h_pos h_lt_top
    have hg₁_pos : 0 < gaussianPDFReal m₁ v₁ x := gaussianPDFReal_pos m₁ v₁ x hv₁
    have hg₂_pos : 0 < gaussianPDFReal m₂ v₂ x := gaussianPDFReal_pos m₂ v₂ x hv₂
    have hν₁ν₂_real_pos : 0 < (ν₁.rnDeriv ν₂ x).toReal :=
      ENNReal.toReal_pos h_pos.ne' h_lt_top.ne
    -- `ν₁.rnDeriv vol x = ν₁.rnDeriv ν₂ x * gaussianPDF m₂ v₂ x` (h_chain + h_g₂).
    -- And LHS = gaussianPDF m₁ v₁ x (h_g₁). So
    -- gaussianPDF m₁ v₁ x = ν₁.rnDeriv ν₂ x * gaussianPDF m₂ v₂ x.
    have h_combine : (gaussianPDF m₁ v₁ x : ℝ≥0∞)
        = ν₁.rnDeriv ν₂ x * gaussianPDF m₂ v₂ x := by
      rw [← h_g₁, ← h_chain, Pi.mul_apply, h_g₂]
    -- llr ν₁ ν₂ x = log (ν₁.rnDeriv ν₂ x).toReal
    --   = log (gaussianPDFReal m₁ v₁ / gaussianPDFReal m₂ v₂)
    --   = log gaussianPDFReal m₁ v₁ - log gaussianPDFReal m₂ v₂.
    show Real.log ((ν₁.rnDeriv ν₂ x).toReal)
        = Real.log (gaussianPDFReal m₁ v₁ x) - Real.log (gaussianPDFReal m₂ v₂ x)
    have h_real_combine : gaussianPDFReal m₁ v₁ x
        = (ν₁.rnDeriv ν₂ x).toReal * gaussianPDFReal m₂ v₂ x := by
      have := congrArg ENNReal.toReal h_combine
      rwa [toReal_gaussianPDF, ENNReal.toReal_mul, toReal_gaussianPDF] at this
    rw [h_real_combine, Real.log_mul hν₁ν₂_real_pos.ne' hg₂_pos.ne']
    ring
  -- 各 piece の積分計算.
  -- Phase C-2 で `log g(x) = -(1/2) log (2πv) - (x-m)²/(2v)`.
  -- `∫(x-m₁)² ∂ν₁ = v₁`, `∫(x-m₂)² ∂ν₁ = v₁ + (m₁-m₂)²` (mean shift identity).
  -- 鍵: `∫ x ∂ν₁ = m₁` (integral_id_gaussianReal).
  have h_mean_ν₁ : ∫ x, x ∂ν₁ = m₁ := by rw [hν₁_def]; exact integral_id_gaussianReal
  have h_var_ν₁ : ∫ x, (x - m₁)^2 ∂ν₁ = (v₁ : ℝ) := by
    have hX : AEMeasurable (fun x : ℝ => x) ν₁ := measurable_id.aemeasurable
    have h_var := variance_eq_integral (μ := ν₁) hX
    have h_var_val : Var[fun x ↦ x; ν₁] = (v₁ : ℝ) := by
      rw [hν₁_def]; exact_mod_cast variance_fun_id_gaussianReal
    rw [h_var_val] at h_var
    have h_mean_id : ∫ x, (id : ℝ → ℝ) x ∂ν₁ = m₁ := h_mean_ν₁
    simp only [id] at h_mean_id
    rw [h_mean_id] at h_var
    exact h_var.symm
  -- 2 次モーメントの可積分性. `MemLp id 2 (gaussianReal m v)` から.
  have h_int_x2_ν₁ : Integrable (fun x : ℝ => x^2) ν₁ := by
    have h_memLp : MemLp (id : ℝ → ℝ) 2 ν₁ := by rw [hν₁_def]; exact memLp_id_gaussianReal 2
    -- `MemLp id 2` says `∫ |id|² ∂ν₁ < ∞`. Via `memLp_two_iff_integrable_sq_norm`.
    have h_int_sq : Integrable (fun x : ℝ => ‖(id : ℝ → ℝ) x‖^2) ν₁ :=
      (memLp_two_iff_integrable_sq_norm h_memLp.aestronglyMeasurable).mp h_memLp
    refine h_int_sq.congr (Filter.Eventually.of_forall fun x => ?_)
    show ‖x‖^2 = x^2
    rw [Real.norm_eq_abs, sq_abs]
  have h_int_xm₁2_ν₁ : Integrable (fun x : ℝ => (x - m₁)^2) ν₁ := by
    have h_eq : (fun x : ℝ => (x - m₁)^2)
        = fun x => x^2 + (-2 * m₁) * x + m₁^2 := by
      funext x; ring
    rw [h_eq]
    refine (h_int_x2_ν₁.add ?_).add (integrable_const _)
    have h_int_x : Integrable (fun x : ℝ => x) ν₁ := by
      have h_memLp1 : MemLp (id : ℝ → ℝ) 1 ν₁ := by rw [hν₁_def]; exact memLp_id_gaussianReal 1
      exact h_memLp1.integrable (le_refl _)
    exact h_int_x.const_mul (-2 * m₁)
  have h_int_xm₂2_ν₁ : Integrable (fun x : ℝ => (x - m₂)^2) ν₁ := by
    have h_eq : (fun x : ℝ => (x - m₂)^2)
        = fun x => x^2 + (-2 * m₂) * x + m₂^2 := by
      funext x; ring
    rw [h_eq]
    refine (h_int_x2_ν₁.add ?_).add (integrable_const _)
    have h_int_x : Integrable (fun x : ℝ => x) ν₁ := by
      have h_memLp1 : MemLp (id : ℝ → ℝ) 1 ν₁ := by rw [hν₁_def]; exact memLp_id_gaussianReal 1
      exact h_memLp1.integrable (le_refl _)
    exact h_int_x.const_mul (-2 * m₂)
  -- mean shift: `∫(x - m₂)² ∂ν₁ = ∫(x - m₁)² ∂ν₁ + (m₁ - m₂)²`.
  -- 展開: `(x-m₂)² = (x-m₁)² + 2(x-m₁)(m₁-m₂) + (m₁-m₂)²`.
  have h_mean_shift : ∫ x, (x - m₂)^2 ∂ν₁ = (v₁ : ℝ) + (m₁ - m₂)^2 := by
    -- 展開: `(x-m₂)² = (x-m₁)² + 2(m₁-m₂)(x-m₁) + (m₁-m₂)²`. ν₁ で積分すれば、
    -- 第 1 項は `v₁`, 第 2 項は `0` (中心化), 第 3 項は `(m₁-m₂)²`.
    have h_int_x : Integrable (fun x : ℝ => x) ν₁ := by
      have h_memLp1 : MemLp (id : ℝ → ℝ) 1 ν₁ := by rw [hν₁_def]; exact memLp_id_gaussianReal 1
      exact h_memLp1.integrable (le_refl _)
    have h_int_xm₁ : Integrable (fun x : ℝ => x - m₁) ν₁ :=
      h_int_x.sub (integrable_const m₁)
    -- 中心化積分.
    have h_zero : ∫ x : ℝ, x - m₁ ∂ν₁ = 0 := by
      rw [integral_sub h_int_x (integrable_const _)]
      simp [h_mean_ν₁]
    have h_int_shift_linear : Integrable
        (fun x : ℝ => 2 * (m₁ - m₂) * (x - m₁)) ν₁ :=
      h_int_xm₁.const_mul (2 * (m₁ - m₂))
    calc ∫ x, (x - m₂)^2 ∂ν₁
        = ∫ x, (x - m₁)^2 + 2 * (m₁ - m₂) * (x - m₁) + (m₁ - m₂)^2 ∂ν₁ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = ∫ x, (x - m₁)^2 ∂ν₁
          + ∫ x, 2 * (m₁ - m₂) * (x - m₁) ∂ν₁
          + ∫ x, (m₁ - m₂)^2 ∂ν₁ := by
          rw [integral_add (f := fun x => (x - m₁)^2 + 2 * (m₁ - m₂) * (x - m₁))
              (g := fun _ => (m₁ - m₂)^2)
              (h_int_xm₁2_ν₁.add h_int_shift_linear) (integrable_const _),
            integral_add (f := fun x => (x - m₁)^2)
              (g := fun x => 2 * (m₁ - m₂) * (x - m₁))
              h_int_xm₁2_ν₁ h_int_shift_linear]
      _ = (v₁ : ℝ) + 2 * (m₁ - m₂) * 0 + (m₁ - m₂)^2 := by
          rw [h_var_ν₁, integral_const_mul, h_zero, integral_const]
          have h_ν₁_real : ν₁.real Set.univ = 1 := by
            rw [measureReal_def]; simp [hν₁_def]
          rw [h_ν₁_real]; simp
      _ = (v₁ : ℝ) + (m₁ - m₂)^2 := by ring
  -- log g₁ / log g₂ の積分計算.
  have h_log_g₁_eq : ∀ x, Real.log (gaussianPDFReal m₁ v₁ x)
      = (-(1/2) * Real.log (2 * Real.pi * v₁)) + (-(1/(2 * v₁))) * (x - m₁)^2 := by
    intro x; rw [log_gaussianPDFReal_eq m₁ hv₁ x]; ring
  have h_log_g₂_eq : ∀ x, Real.log (gaussianPDFReal m₂ v₂ x)
      = (-(1/2) * Real.log (2 * Real.pi * v₂)) + (-(1/(2 * v₂))) * (x - m₂)^2 := by
    intro x; rw [log_gaussianPDFReal_eq m₂ hv₂ x]; ring
  have h_int_log_g₁ : Integrable (fun x => Real.log (gaussianPDFReal m₁ v₁ x)) ν₁ := by
    rw [show (fun x => Real.log (gaussianPDFReal m₁ v₁ x))
        = fun x => (-(1/2) * Real.log (2 * Real.pi * v₁))
            + (-(1/(2 * v₁))) * (x - m₁)^2 from funext h_log_g₁_eq]
    exact (integrable_const _).add (h_int_xm₁2_ν₁.const_mul (-(1/(2 * v₁))))
  have h_int_log_g₂ : Integrable (fun x => Real.log (gaussianPDFReal m₂ v₂ x)) ν₁ := by
    rw [show (fun x => Real.log (gaussianPDFReal m₂ v₂ x))
        = fun x => (-(1/2) * Real.log (2 * Real.pi * v₂))
            + (-(1/(2 * v₂))) * (x - m₂)^2 from funext h_log_g₂_eq]
    exact (integrable_const _).add (h_int_xm₂2_ν₁.const_mul (-(1/(2 * v₂))))
  have h_ν₁_real : ν₁.real Set.univ = 1 := by rw [measureReal_def]; simp [hν₁_def]
  have h_int_log_g₁_eq :
      ∫ x, Real.log (gaussianPDFReal m₁ v₁ x) ∂ν₁
        = -(1/2) * Real.log (2 * Real.pi * v₁) - (1/2) := by
    rw [show (fun x => Real.log (gaussianPDFReal m₁ v₁ x))
        = fun x => (-(1/2) * Real.log (2 * Real.pi * v₁))
            + (-(1/(2 * v₁))) * (x - m₁)^2 from funext h_log_g₁_eq]
    rw [integral_add (f := fun _ => -(1/2) * Real.log (2 * Real.pi * v₁))
        (g := fun x => (-(1/(2 * v₁))) * (x - m₁)^2)
        (integrable_const _) (h_int_xm₁2_ν₁.const_mul _)]
    rw [integral_const, integral_const_mul, h_var_ν₁, h_ν₁_real]
    simp only [smul_eq_mul, one_mul]
    field_simp
    ring
  have h_int_log_g₂_eq :
      ∫ x, Real.log (gaussianPDFReal m₂ v₂ x) ∂ν₁
        = -(1/2) * Real.log (2 * Real.pi * v₂)
          - ((v₁ : ℝ) + (m₁ - m₂)^2) / (2 * v₂) := by
    rw [show (fun x => Real.log (gaussianPDFReal m₂ v₂ x))
        = fun x => (-(1/2) * Real.log (2 * Real.pi * v₂))
            + (-(1/(2 * v₂))) * (x - m₂)^2 from funext h_log_g₂_eq]
    rw [integral_add (f := fun _ => -(1/2) * Real.log (2 * Real.pi * v₂))
        (g := fun x => (-(1/(2 * v₂))) * (x - m₂)^2)
        (integrable_const _) (h_int_xm₂2_ν₁.const_mul _)]
    rw [integral_const, integral_const_mul, h_mean_shift, h_ν₁_real]
    field_simp
    ring
  -- 統合.
  have h_split : ∫ x, llr ν₁ ν₂ x ∂ν₁
      = ∫ x, Real.log (gaussianPDFReal m₁ v₁ x) ∂ν₁
        - ∫ x, Real.log (gaussianPDFReal m₂ v₂ x) ∂ν₁ := by
    rw [← integral_sub h_int_log_g₁ h_int_log_g₂]
    exact integral_congr_ae h_llr_decomp
  rw [h_kl_eq, h_split, h_int_log_g₁_eq, h_int_log_g₂_eq]
  -- 代数恒等式の最終整理.
  -- LHS = -(1/2) log(2πv₁) - 1/2 - (-(1/2) log(2πv₂) - (v₁+(m₁-m₂)²)/(2v₂))
  --     = (1/2) (log(2πv₂) - log(2πv₁)) - 1/2 + (v₁+(m₁-m₂)²)/(2v₂)
  --     = (1/2) log(v₂/v₁) + v₁/(2v₂) + (m₁-m₂)²/(2v₂) - 1/2
  --     = (1/2) [log(v₂/v₁) + v₁/v₂ + (m₁-m₂)²/v₂ - 1]
  have h_log_diff : Real.log ((v₂ : ℝ) / v₁)
      = Real.log (2 * Real.pi * v₂) - Real.log (2 * Real.pi * v₁) := by
    rw [show (v₂ : ℝ) / v₁ = (2 * Real.pi * v₂) / (2 * Real.pi * v₁) by field_simp]
    exact Real.log_div h2πv₂_pos.ne' h2πv₁_pos.ne'
  rw [h_log_diff]
  have hv₁_ne : (v₁ : ℝ) ≠ 0 := hv₁_pos.ne'
  have hv₂_ne : (v₂ : ℝ) ≠ 0 := hv₂_pos.ne'
  field_simp
  ring

/-- (Phase E-2) `h(𝒩(0,1)) = (1/2) log (2π) + 1/2`. -/
theorem differentialEntropy_gaussianReal_std_val :
    differentialEntropy (gaussianReal 0 1)
      = (1/2) * Real.log (2 * Real.pi) + (1/2) := by
  rw [differentialEntropy_gaussianReal_std]
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [Real.log_mul h2π_pos.ne' he_pos.ne', Real.log_exp]
  ring

end Common2026.Shannon
