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
