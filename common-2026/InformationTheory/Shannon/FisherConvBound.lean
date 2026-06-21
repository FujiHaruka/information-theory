import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.Conv.DensitySecondDeriv          -- convDensityAdd_deriv1_gaussian_eq
import InformationTheory.Shannon.FisherInfo.OfDensity
import InformationTheory.Shannon.FisherInfo.DeBruijn   -- V2 Gaussian closed form J(𝒩(0,s))=1/s
import InformationTheory.Shannon.FisherInfo.DeBruijnPerTime        -- convDensityAdd_pos / fisher_from_logDeriv
import InformationTheory.Shannon.StamGaussianBound       -- stam_fisher_arith
import Mathlib.MeasureTheory.Integral.Bochner.Basic          -- integral_mul_le_Lp_mul_Lq_of_nonneg
import Mathlib.MeasureTheory.Measure.Prod                    -- lintegral_lintegral_swap
import Mathlib.Probability.Distributions.Gaussian.Real       -- variance_fun_id_gaussianReal / integral_gaussianReal_eq_integral_smul

/-!
# Stam convolution Fisher information bound `J(pX ∗ g_s) ≤ 1/s`

For any probability density `pX` and Gaussian kernel `g_s` of variance `s`,
the Fisher information of the convolution `pX ∗ g_s` satisfies `J(pX ∗ g_s) ≤ 1/s`.

## Main statements

* `gaussianConv_fisher_le_inv_var` — `fisherInfoOfDensity (pX ∗ g_s) ≤ ENNReal.ofReal (1/s)`.

## Implementation notes

The proof follows a pointwise Cauchy-Schwarz route: the derivative formula
`convDensityAdd_deriv1_gaussian_eq` gives `(deriv p_s x)` as an integral, Hölder's
inequality with `p = q = 2` bounds `(logDeriv p_s x)² · p_s x` pointwise, and
Tonelli's theorem plus the Gaussian second moment `∫ u² g_s u du = s` closes the bound.
-/

namespace InformationTheory.Shannon.FisherInfo

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

/-- `∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, _⟩ u ∂volume = s`.
@audit:ok -/
theorem integral_sq_mul_gaussianPDFReal {s : ℝ} (hs : 0 < s) :
    ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume = s := by
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact hs.ne' (congrArg NNReal.toReal h)
  -- Var[id; 𝒩(0,s)] = ∫ (ω - 0)² ∂𝒩(0,s) = ∫ ω² ∂𝒩(0,s) = (s : ℝ).
  have hvar : Var[fun x => x; gaussianReal 0 ⟨s, hs.le⟩] = ((⟨s, hs.le⟩ : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal (μ := 0) (v := ⟨s, hs.le⟩)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  -- chain: `∫ u² g_s u du = ∫ u² ∂𝒩 = ∫ (u-0)² ∂𝒩 = s`.
  calc ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume
      = ∫ u, gaussianPDFReal 0 ⟨s, hs.le⟩ u • u ^ 2 ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp [smul_eq_mul, mul_comm]
    _ = ∫ u, u ^ 2 ∂(gaussianReal 0 ⟨s, hs.le⟩) :=
        (integral_gaussianReal_eq_integral_smul (μ := 0) (f := fun u => u ^ 2) hv_ne).symm
    _ = ∫ u, (u - 0) ^ 2 ∂(gaussianReal 0 ⟨s, hs.le⟩) := by simp
    _ = s := by rw [hvar]

/-- `u ↦ u ^ 2 * gaussianPDFReal 0 ⟨s, _⟩ u` is integrable over `volume`.
@audit:ok -/
theorem integrable_sq_mul_gaussianPDFReal {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u) volume := by
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact hs.ne' (congrArg NNReal.toReal h)
  -- `u² = id² ∈ L²(gaussianReal)`, hence integrable under `gaussianReal`.
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 ⟨s, hs.le⟩) := memLp_id_gaussianReal 2
  have hsq_int : Integrable (fun u => u ^ 2) (gaussianReal 0 ⟨s, hs.le⟩) := by
    have := (memLp_two_iff_integrable_sq (μ := gaussianReal 0 ⟨s, hs.le⟩)
      (f := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable).mp hmem
    simpa using this
  -- transport to `volume` via `gaussianReal = volume.withDensity gaussianPDF`.
  rw [gaussianReal_of_var_ne_zero _ hv_ne] at hsq_int
  rw [integrable_withDensity_iff (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hsq_int
  refine hsq_int.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]

/-- `y ↦ (x - y) ^ 2 * (pX y * g_s(x - y))` is integrable over `volume` for each `x`.
@audit:ok -/
theorem convSecondMoment_integrand_integrable
    (pX : ℝ → ℝ) (_hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Integrable (fun y => (x - y) ^ 2 * (pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y))) volume := by
  -- global bound for `u ↦ u² · g_s(u)`: `u² exp(-u²/(2s)) = 2s·(u²/(2s))·exp(-u²/(2s)) ≤ 2s·exp(-1)`.
  set C : ℝ := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ * (2 * s * Real.exp (-1)) with hC
  have hcoe : ((⟨s, hs.le⟩ : ℝ≥0) : ℝ) = s := rfl
  have hbnd : ∀ u : ℝ, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ≤ C := by
    intro u
    have h2s : (0 : ℝ) < 2 * s := by positivity
    -- `(u²/(2s)) · exp(-(u²/(2s))) ≤ exp(-1)`
    have hexp := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * s))
    have hpref_nn : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ := by positivity
    -- unfold gaussianPDFReal (centered): `(√(2πs))⁻¹ · exp(-u²/(2s))`; coercion `↑⟨s,_⟩ = s` is defeq.
    rw [hC]
    show u ^ 2 * ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(u - 0) ^ 2 / (2 * s)))
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * (2 * s * Real.exp (-1))
    rw [sub_zero,
      show u ^ 2 * ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)))
          = (Real.sqrt (2 * Real.pi * s))⁻¹ * (u ^ 2 * Real.exp (-u ^ 2 / (2 * s))) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- `u² · exp(-u²/(2s)) ≤ 2s · exp(-1)`
    have heq : u ^ 2 * Real.exp (-u ^ 2 / (2 * s))
        = 2 * s * ((u ^ 2 / (2 * s)) * Real.exp (-(u ^ 2 / (2 * s)))) := by
      rw [neg_div]; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hexp h2s.le
  -- now: integrand = `pX y · ((x-y)² · g_s(x-y))`, bounded factor measurable + ≤ C.
  have hgmeas : Measurable (fun y => (x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) := by
    refine (Measurable.pow_const (measurable_const.sub measurable_id) 2).mul ?_
    exact (measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp (measurable_const.sub measurable_id)
  have hint : Integrable
      (fun y => pX y * ((x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y))) volume := by
    refine hpX_int.mul_bdd (c := C) hgmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hnn : (0 : ℝ) ≤ (x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) :=
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hbnd (x - y)
  refine (integrable_congr (Filter.Eventually.of_forall fun y => ?_)).mpr hint
  ring

/-- Pointwise Cauchy-Schwarz: `(∫ pX y (x-y) g_s(x-y))² ≤ p_s(x) · ∫ pX y (x-y)² g_s(x-y)`.
@audit:ok -/
theorem convScore_sq_le_pointwise
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ y, pX y * (x - y) * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) ∂volume) ^ 2
      ≤ (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x)
        * (∫ y, (x - y) ^ 2 * (pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) ∂volume) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  -- nonneg integrand `w y := pX y · g(x-y) ≥ 0`.
  have hw_nn : ∀ y, 0 ≤ pX y * g (x - y) := fun y =>
    mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- Hölder functions `a := |x-·|·√w`, `b := √w` (both nonneg).
  set a : ℝ → ℝ := fun y => |x - y| * Real.sqrt (pX y * g (x - y)) with ha_def
  set b : ℝ → ℝ := fun y => Real.sqrt (pX y * g (x - y)) with hb_def
  have ha_nn : 0 ≤ᵐ[volume] a :=
    Filter.Eventually.of_forall fun y => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hb_nn : 0 ≤ᵐ[volume] b :=
    Filter.Eventually.of_forall fun y => Real.sqrt_nonneg _
  -- measurability of `w` and its sqrt.
  have hw_meas : Measurable (fun y => pX y * g (x - y)) :=
    hpX_meas.mul ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp (measurable_const.sub measurable_id))
  -- integrability of `w := pX(x-·)·g` (= the convolution integrand, `pX` integrable × bounded Gaussian).
  have hw_int : Integrable (fun y => pX y * g (x - y)) volume := by
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      -- `g_s(u) = (√(2πs))⁻¹·exp(...) ≤ (√(2πs))⁻¹` since `exp(neg) ≤ 1`.
      rw [gaussianPDFReal]
      refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
      rw [neg_div]
      exact neg_nonpos.mpr (by positivity)
  -- `a·b = |x-y|·w`, `a² = (x-y)²·w`, `b² = w`.
  have hab : ∀ y, a y * b y = |x - y| * (pX y * g (x - y)) := by
    intro y
    simp only [ha_def, hb_def]
    rw [mul_assoc, Real.mul_self_sqrt (hw_nn y)]
  have ha_sq : ∀ y, a y ^ 2 = (x - y) ^ 2 * (pX y * g (x - y)) := by
    intro y
    simp only [ha_def, mul_pow, sq_abs, Real.sq_sqrt (hw_nn y)]
  have hb_sq : ∀ y, b y ^ 2 = pX y * g (x - y) := by
    intro y
    simp only [hb_def, Real.sq_sqrt (hw_nn y)]
  -- L² memberships.
  have hb_int : Integrable (fun y => b y ^ 2) volume :=
    (integrable_congr (Filter.Eventually.of_forall hb_sq)).mpr hw_int
  have ha_int : Integrable (fun y => a y ^ 2) volume := by
    refine (integrable_congr (Filter.Eventually.of_forall ha_sq)).mpr ?_
    simpa [hg_def] using convSecondMoment_integrand_integrable pX hpX_meas hpX_int hs x
  have ha_memLp : MemLp a (ENNReal.ofReal 2) volume := by
    rw [show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) from by norm_num]
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact ((measurable_const.sub measurable_id).abs.mul
        (hw_meas.sqrt)).aestronglyMeasurable
    · exact ha_int
  have hb_memLp : MemLp b (ENNReal.ofReal 2) volume := by
    rw [show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) from by norm_num]
    refine (memLp_two_iff_integrable_sq hw_meas.sqrt.aestronglyMeasurable).mpr hb_int
  -- Hölder (p = q = 2).
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq ha_nn hb_nn ha_memLp hb_memLp
  -- rewrite the three integrals to the `w`-form. Hölder's `^ p` are real powers `^ (2:ℝ)`;
  -- bridge them to the nat-power `^ 2` form via `a y ≥ 0`.
  have ha_rpow : ∀ y, a y ^ (2 : ℝ) = (x - y) ^ 2 * (pX y * g (x - y)) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast (a y) 2, ha_sq y]
  have hb_rpow : ∀ y, b y ^ (2 : ℝ) = pX y * g (x - y) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast (b y) 2, hb_sq y]
  simp only [hab, ha_rpow, hb_rpow] at hholder
  -- abbreviations for the two nonneg moment integrals.
  set I0 : ℝ := ∫ y, pX y * g (x - y) ∂volume with hI0
  set I2 : ℝ := ∫ y, (x - y) ^ 2 * (pX y * g (x - y)) ∂volume with hI2
  have hI0_nn : 0 ≤ I0 := integral_nonneg hw_nn
  have hI2_nn : 0 ≤ I2 := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hw_nn y)
  -- `hholder : ∫ |x-y|·w ≤ I2^(1/2)·I0^(1/2)`.
  -- LHS² ≥ (∫ pX(x-y)g)² and RHS² = I2·I0.
  have hconv_eq : convDensityAdd pX g x = I0 := by
    rw [hI0]; rfl
  -- `(∫ pX(x-y)g)² ≤ (∫ |x-y|·w)²`
  have habs_le : |∫ y, pX y * (x - y) * g (x - y) ∂volume|
      ≤ ∫ y, |x - y| * (pX y * g (x - y)) ∂volume := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    rw [show pX y * (x - y) * g (x - y) = (x - y) * (pX y * g (x - y)) from by ring,
      abs_mul, abs_of_nonneg (hw_nn y)]
  -- assemble.
  have hLHS_sq : (∫ y, pX y * (x - y) * g (x - y) ∂volume) ^ 2
      ≤ (∫ y, |x - y| * (pX y * g (x - y)) ∂volume) ^ 2 := by
    rw [← sq_abs (∫ y, pX y * (x - y) * g (x - y) ∂volume)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs_le 2
  refine hLHS_sq.trans ?_
  -- `(∫|x-y|·w)² ≤ (I2^½·I0^½)² = I2·I0`
  have hRHS : (∫ y, |x - y| * (pX y * g (x - y)) ∂volume) ^ 2 ≤ I2 * I0 := by
    have hint_nn : 0 ≤ ∫ y, |x - y| * (pX y * g (x - y)) ∂volume :=
      integral_nonneg fun y => mul_nonneg (abs_nonneg _) (hw_nn y)
    calc (∫ y, |x - y| * (pX y * g (x - y)) ∂volume) ^ 2
        ≤ (I2 ^ (1/2 : ℝ) * I0 ^ (1/2 : ℝ)) ^ 2 := by
          exact pow_le_pow_left₀ hint_nn hholder 2
      _ = I2 * I0 := by
          rw [mul_pow, ← Real.rpow_natCast (I2 ^ (1/2:ℝ)) 2, ← Real.rpow_natCast (I0 ^ (1/2:ℝ)) 2,
            ← Real.rpow_mul hI2_nn, ← Real.rpow_mul hI0_nn]
          norm_num
  rw [hconv_eq, mul_comm I0 I2]
  exact hRHS

/-- `deriv (convDensityAdd pX g_s) x = ∫ y, pX y * g_s(x-y) * (-(x-y)/s) ∂volume`.
@audit:ok -/
theorem convDensityAdd_deriv_eq
    (pX : ℝ → ℝ) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    {s : ℝ} (hs : 0 < s) :
    deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      = fun ζ : ℝ => ∫ y, pX y * (gaussianPDFReal 0 ⟨s, hs.le⟩ (ζ - y)
          * (-((ζ - y) / s))) ∂volume := by
  -- kernel measurability + global bound for `kernel·(-(·/s))` (= `g_s(u)·(-u/s)`).
  have hker_meas : Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) := by
    have : Continuous (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) := by
      unfold heatFlow_density_heat_equation_kernel; fun_prop
    exact this.measurable
  -- global bound `M1` for `|g_s(u)·(-u/s)|`: `(√2πs)⁻¹·(|u|exp(-u²/2s))/s`, `|u|exp(-u²/2s) ≤ √(s·exp(-1))`.
  -- key: `|u|·exp(-u²/(2s)) ≤ √(s·exp(-1))` (square both sides; `(u²/s)exp(-u²/s) ≤ exp(-1)`).
  have hum_bnd : ∀ u : ℝ, |u| * Real.exp (-u ^ 2 / (2 * s)) ≤ Real.sqrt (s * Real.exp (-1)) := by
    intro u
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ |u| * Real.exp (-u ^ 2 / (2 * s)))]
    refine Real.sqrt_le_sqrt ?_
    have hexp := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / s)
    have heq : (|u| * Real.exp (-u ^ 2 / (2 * s))) ^ 2
        = s * ((u ^ 2 / s) * Real.exp (-(u ^ 2 / s))) := by
      rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
      rw [show ((2 : ℕ) : ℝ) * (-u ^ 2 / (2 * s)) = -(u ^ 2 / s) from by push_cast; field_simp]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hexp hs.le
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * (Real.sqrt (s * Real.exp (-1)) / s) with hM1
  have hker_d1_bnd : ∀ u : ℝ,
      |heatFlow_density_heat_equation_kernel s u * (-(u / s))| ≤ M1 := by
    intro u
    rw [heatFlow_density_heat_equation_kernel_eq hs u]
    have hpref_nn : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by positivity
    have hcoe : ((⟨s, hs.le⟩ : ℝ≥0) : ℝ) = s := rfl
    rw [gaussianPDFReal, sub_zero, hM1]
    show |(Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)) * (-(u / s))|
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * (Real.sqrt (s * Real.exp (-1)) / s)
    -- factor the absolute value: `|(√2πs)⁻¹·exp·(-(u/s))| = (√2πs)⁻¹·exp·(|u|/s)`.
    rw [abs_mul, abs_mul, abs_of_nonneg hpref_nn, abs_of_nonneg (Real.exp_nonneg _),
      abs_neg, abs_div, abs_of_pos hs]
    -- `(√2πs)⁻¹·(exp·(|u|/s)) ≤ (√2πs)⁻¹·(√(s exp(-1))/s)`
    rw [show (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)) * (|u| / s)
          = (Real.sqrt (2 * Real.pi * s))⁻¹ * ((|u| * Real.exp (-u ^ 2 / (2 * s))) / s) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ hpref_nn
    gcongr
    exact hum_bnd u
  -- build the 5 deriv1 hyps in kernel form.
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := fun ξ =>
    (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel s v|
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq hs v, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v),
      gaussianPDFReal, sub_zero]
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
    rw [neg_div]; exact neg_nonpos.mpr (by positivity)
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * s))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul (AEStronglyMeasurable.mul ?_ ?_)
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-((ξ - y) / s)))‖
        ≤ (fun y => |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hker_d1_bnd (ξ - y)) (abs_nonneg _)
  have hb1_int : Integrable (fun y => |pX y| * M1) volume := hpX_int.abs.mul_const _
  exact InformationTheory.Shannon.EPIConvDensitySecondDeriv.convDensityAdd_deriv1_gaussian_eq
    pX hs (fun y => |pX y| * M1) hb1_int hF1_meas hF1_int hF1'_meas hb1

/-- `(logDeriv p_s x) ^ 2 * p_s x ≤ (1/s²) * ∫ (x-y)² * (pX y * g_s(x-y)) ∂volume`.
@audit:ok -/
theorem convLogDeriv_sq_mul_le
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩)) x) ^ 2
        * convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x
      ≤ (1 / s ^ 2) * ∫ y, (x - y) ^ 2 * (pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) ∂volume := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  set p_s : ℝ → ℝ := convDensityAdd pX g with hp_def
  -- positivity (`hpX_mass → 0 < ∫ pX`).
  have hmass_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  have hps_pos : 0 < p_s x :=
    convDensityAdd_pos pX hpX_nn hpX_int hmass_pos hs x
  -- deriv formula at `x`.
  have hderiv : deriv p_s x = ∫ y, pX y * (g (x - y) * (-((x - y) / s))) ∂volume := by
    rw [hp_def, hg_def, convDensityAdd_deriv_eq pX hpX_meas hpX_int hs]
  -- `∫ pX·(g·(-(x-y)/s)) = -(1/s)·∫ pX (x-y) g`.
  have hscore : ∫ y, pX y * (g (x - y) * (-((x - y) / s))) ∂volume
      = -(1 / s) * ∫ y, pX y * (x - y) * g (x - y) ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    field_simp
  -- `(deriv p_s x)² = (1/s²)·(∫ pX (x-y) g)²`.
  have hderiv_sq : (deriv p_s x) ^ 2
      = (1 / s ^ 2) * (∫ y, pX y * (x - y) * g (x - y) ∂volume) ^ 2 := by
    rw [hderiv, hscore]
    rw [mul_pow, neg_pow]
    rw [show ((-1 : ℝ)) ^ 2 = 1 from by norm_num, one_mul, div_pow, one_pow]
  -- CS bound.
  have hCS := convScore_sq_le_pointwise pX hpX_nn hpX_meas hpX_int hs x
  rw [← hg_def, ← hp_def] at hCS
  -- `logDeriv p_s x = deriv p_s x / p_s x`, so `(logDeriv)²·p_s = (deriv)²/p_s`.
  have hlog : (logDeriv p_s x) ^ 2 * p_s x = (deriv p_s x) ^ 2 / p_s x := by
    rw [logDeriv_apply, div_pow]
    field_simp
  rw [hlog, hderiv_sq]
  -- `(1/s²)·(∫…)²/p_s ≤ (1/s²)·(∫(x-y)²pX g)`: use CS `(∫…)² ≤ p_s·∫(x-y)²pX g`.
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ hps_pos]
  calc (∫ y, pX y * (x - y) * g (x - y) ∂volume) ^ 2
      ≤ p_s x * ∫ y, (x - y) ^ 2 * (pX y * g (x - y)) ∂volume := hCS
    _ = (∫ y, (x - y) ^ 2 * (pX y * g (x - y)) ∂volume) * p_s x := by ring

/-- Stam convolution Fisher information bound: `J(pX ∗ g_s) ≤ 1/s` for any probability
density `pX` and Gaussian kernel `g_s` of variance `s > 0`.
@audit:ok -/
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  set p_s : ℝ → ℝ := convDensityAdd pX g with hp_def
  have hps_nn : ∀ x, 0 ≤ p_s x := fun x =>
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- second-moment integrand `K x y := (x-y)²·(pX y · g(x-y)) ≥ 0`.
  set K : ℝ → ℝ → ℝ := fun x y => (x - y) ^ 2 * (pX y * g (x - y)) with hK_def
  have hK_nn : ∀ x y, 0 ≤ K x y := fun x y =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _))
  have hK_int : ∀ x, Integrable (fun y => K x y) volume := fun x => by
    simpa [hK_def, hg_def] using convSecondMoment_integrand_integrable pX hpX_meas hpX_int hs x
  -- Step 3: merge the Fisher lintegrand to `ofReal((logDeriv)²·p_s)`.
  have hmerge : fisherInfoOfDensity p_s
      = ∫⁻ x, ENNReal.ofReal ((logDeriv p_s x) ^ 2 * p_s x) ∂volume := by
    unfold fisherInfoOfDensity
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hmerge]
  -- Step 3 bound: pointwise `≤ ofReal((1/s²)·∫ K x y dy)`.
  have hpt : ∀ x, ENNReal.ofReal ((logDeriv p_s x) ^ 2 * p_s x)
      ≤ ENNReal.ofReal ((1 / s ^ 2) * ∫ y, K x y ∂volume) := by
    intro x
    refine ENNReal.ofReal_le_ofReal ?_
    have := convLogDeriv_sq_mul_le pX hpX_nn hpX_meas hpX_int hpX_mass hs x
    rw [← hg_def, ← hp_def] at this
    simpa [hK_def] using this
  refine (lintegral_mono hpt).trans ?_
  -- Step 4: convert to `ofReal(1/s²) · ∫⁻ x ofReal(∫ K x y dy)`, Tonelli, inner moment = s.
  have hrw : ∀ x, ENNReal.ofReal ((1 / s ^ 2) * ∫ y, K x y ∂volume)
      = ENNReal.ofReal (1 / s ^ 2) * ∫⁻ y, ENNReal.ofReal (K x y) ∂volume := by
    intro x
    rw [ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal (hK_int x)
        (Filter.Eventually.of_forall fun y => hK_nn x y)]
  -- measurability of `(x,y) ↦ ofReal (K x y)` and the inner integral.
  have hKofReal_meas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (K p.1 p.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine ((measurable_fst.sub measurable_snd).pow_const 2).mul ?_
    exact (hpX_meas.comp measurable_snd).mul
      ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp (measurable_fst.sub measurable_snd))
  simp_rw [hrw]
  rw [lintegral_const_mul _ hKofReal_meas.lintegral_prod_right]
  -- Tonelli swap: `∫⁻ x ∫⁻ y ofReal(K x y) = ∫⁻ y ∫⁻ x ofReal(K x y)`.
  have hswap : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂volume ∂volume)
      = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (K x y) ∂volume ∂volume :=
    lintegral_lintegral_swap hKofReal_meas.aemeasurable
  rw [hswap]
  -- shifted Gaussian-moment integrability: `x ↦ (x-y)²·g(x-y)` is integrable (for each y).
  have hmom_int : Integrable (fun u => u ^ 2 * g u) volume := by
    simpa [hg_def] using integrable_sq_mul_gaussianPDFReal hs
  have hshift_int : ∀ y, Integrable (fun x => (x - y) ^ 2 * g (x - y)) volume := fun y =>
    hmom_int.comp_sub_right y
  -- shifted Gaussian moment value: `∫_x (x-y)²·g(x-y) = ∫ u²·g(u) = s`.
  have hshift_val : ∀ y, (∫ x, (x - y) ^ 2 * g (x - y) ∂volume) = s := by
    intro y
    rw [integral_sub_right_eq_self (fun u => u ^ 2 * g u) y]
    simpa [hg_def] using integral_sq_mul_gaussianPDFReal hs
  -- inner moment: `∫⁻ x ofReal(K x y) = ofReal(pX y · s)`.
  have hinner : ∀ y, (∫⁻ x, ENNReal.ofReal (K x y) ∂volume) = ENNReal.ofReal (pX y * s) := by
    intro y
    -- `K x y = pX y · ((x-y)²·g(x-y))`, so `∫_x K x y = pX y · ∫_x (x-y)²g(x-y) = pX y · s`.
    have hxint : Integrable (fun x => K x y) volume := by
      refine ((hshift_int y).const_mul (pX y)).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hK_def]; ring
    rw [← ofReal_integral_eq_lintegral_ofReal hxint (Filter.Eventually.of_forall fun x => hK_nn x y)]
    congr 1
    rw [show (fun x => K x y) = (fun x => pX y * ((x - y) ^ 2 * g (x - y))) from by
      funext x; simp only [hK_def]; ring, integral_const_mul, hshift_val y]
  simp_rw [hinner]
  -- `∫⁻ y ofReal(pX y · s) = ofReal(∫ pX·s) = ofReal(s·∫pX) = ofReal s` (hpX_mass).
  have houter : (∫⁻ y, ENNReal.ofReal (pX y * s) ∂volume) = ENNReal.ofReal s := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hpX_int.mul_const s)
      (Filter.Eventually.of_forall fun y => mul_nonneg (hpX_nn y) hs.le)]
    congr 1
    rw [integral_mul_const, hpX_mass, one_mul]
  rw [houter]
  -- `ofReal(1/s²)·ofReal(s) = ofReal(1/s²·s) = ofReal(1/s)`.
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  field_simp

end InformationTheory.Shannon.FisherInfo
