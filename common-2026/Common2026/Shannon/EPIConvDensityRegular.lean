import Common2026.Shannon.EPIConvDensityGaussianGateway
import Common2026.Shannon.FisherInfoV2DeBruijnPerTime
import Common2026.Shannon.FisherInfoV2DeBruijnAssembly
import Common2026.Shannon.EPIBlachmanGaussianWitness
import Common2026.Shannon.FisherInfoGaussian

/-!
# `IsRegularDensityV2 (convDensityAdd pX g_t)` producer — EPI A-5 precondition (1)

For an arbitrary probability density `pX` (nonnegativity + measurability +
integrability + positive mass) and the Gaussian heat kernel
`g_t = gaussianPDFReal 0 ⟨t, _⟩` (`t > 0`), the convolution density
`convDensityAdd pX g_t` is a *regular density* in the V2 sense
(`Common2026.Shannon.FisherInfoV2.IsRegularDensityV2`).

All six fields are discharged from existing `@audit:ok` infrastructure:

* `diff` — `convDensityAdd_differentiable_of_integrable_smoothKernel` (gateway),
  differentiation carried by the smooth Gaussian kernel.
* `pos` — `convDensityAdd_pos` (positive mass ⇒ strictly positive convolution).
* `integrable_deriv` — `deriv f = convDensityAdd pX (deriv g_t)` (gateway
  `HasDerivAt` `.deriv`) + `convKernel_envelope_integrable'` (Tonelli envelope).
* `integral_deriv_eq_zero` — Fubini swap of the same envelope + `∫ deriv g_t = 0`.
* `tail_bot` / `tail_top` — convolution with the Gaussian kernel vanishes at ±∞.

All hypotheses on `pX` are regularity preconditions (no load-bearing core).
-/

namespace Common2026.Shannon.EPIConvDensityRegular

open MeasureTheory Real ProbabilityTheory
open scoped NNReal
open InformationTheory.Shannon.EPIConvDensity
  (convDensityAdd convDensityAddDeriv)

/-- Global sup bound of `gaussianPDFReal 0 v`: `g(x) ≤ (√(2πv))⁻¹` since
`exp(-x²/(2v)) ≤ 1`. -/
theorem gaussianPDFReal_abs_le (v : ℝ≥0) :
    ∀ w, |gaussianPDFReal 0 v w| ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  intro w
  rw [gaussianPDFReal_def]
  set P : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  rw [abs_mul, abs_of_nonneg hP_nn, Real.abs_exp]
  calc P * Real.exp (-(w - 0) ^ 2 / (2 * v))
      ≤ P * 1 := by
        apply mul_le_mul_of_nonneg_left _ hP_nn
        rw [Real.exp_le_one_iff]
        have : (0:ℝ) ≤ (w - 0) ^ 2 / (2 * v) := by positivity
        linarith [neg_div (2 * (v:ℝ)) ((w - 0) ^ 2)]
    _ = P := mul_one _

/-- Global sup bound of `deriv (gaussianPDFReal 0 v)`. With
`deriv g v x = -x/v · g v x` and `|x|·exp(-x²/(2v)) ≤ √(v)·exp(-1/2)·…`, the
derivative is globally bounded. -/
theorem deriv_gaussianPDFReal_abs_le {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ M : ℝ, ∀ w, |deriv (gaussianPDFReal 0 v) w| ≤ M := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  set P : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  -- global bound: `|deriv g w| = (|w|/v)·P·exp(-w²/(2v)) ≤ P·(1+2v·exp(-1))/(2v²)`
  refine ⟨P * ((1 + 2 * (v:ℝ) * Real.exp (-1)) / (2 * (v:ℝ))), fun w => ?_⟩
  rw [deriv_gaussianPDFReal hv w, gaussianPDFReal_def]
  -- |(-(w-0)/v)·(P·exp(-(w-0)²/(2v)))| = (|w|/v)·P·exp(-w²/(2v))
  set E : ℝ := Real.exp (-(w - 0) ^ 2 / (2 * v)) with hE
  have hE_nn : (0:ℝ) ≤ E := (Real.exp_pos _).le
  rw [abs_mul, abs_mul, abs_of_nonneg hP_nn, Real.abs_exp]
  simp only [sub_zero]
  rw [abs_div, abs_neg, abs_of_pos hv_pos]
  -- now goal: `|w| / v * (P * E) ≤ P * ((1 + 2v·e⁻¹)/(2v²))`
  -- key: `E·|w| ≤ (1 + 2v·exp(-1))/2`, then divide by `v`.
  have hE_eq : E = Real.exp (-w ^ 2 / (2 * v)) := by rw [hE]; congr 1; ring
  have hexp_le1 : E ≤ 1 := by
    rw [hE_eq, Real.exp_le_one_iff]
    have : (0:ℝ) ≤ w ^ 2 / (2 * v) := by positivity
    linarith [neg_div (2 * (v:ℝ)) (w ^ 2)]
  have hkey : E * |w| ≤ (1 + 2 * (v:ℝ) * Real.exp (-1)) / 2 := by
    have h2u : 2 * |w| ≤ 1 + w ^ 2 := by nlinarith [sq_nonneg (|w| - 1), sq_abs w]
    have hmul := Real.mul_exp_neg_le_exp_neg_one (w ^ 2 / (2 * v))
    have hexp_eq2 : Real.exp (-(w ^ 2 / (2 * v))) = E := by rw [hE_eq]; congr 1; ring
    rw [hexp_eq2] at hmul
    have h2s : (0:ℝ) < 2 * v := by linarith
    have hu2 : w ^ 2 * E ≤ 2 * (v:ℝ) * Real.exp (-1) := by
      have hmul' := mul_le_mul_of_nonneg_left hmul h2s.le
      have heq : (2 * (v:ℝ)) * ((w ^ 2 / (2 * v)) * E) = w ^ 2 * E := by
        field_simp
      rw [heq] at hmul'; linarith [hmul']
    nlinarith [mul_le_mul_of_nonneg_left h2u hE_nn, hu2, hexp_le1, abs_nonneg w]
  -- assemble
  have hPE : (0:ℝ) ≤ P := hP_nn
  rw [← hE_eq]
  rw [show |w| / (v:ℝ) * (P * E) = P * ((E * |w|) / (v:ℝ)) by ring]
  apply mul_le_mul_of_nonneg_left _ hPE
  calc (E * |w|) / (v:ℝ)
      ≤ ((1 + 2 * (v:ℝ) * Real.exp (-1)) / 2) / (v:ℝ) := by
        gcongr
    _ = (1 + 2 * (v:ℝ) * Real.exp (-1)) / (2 * (v:ℝ)) := by
        rw [div_div]

/-- The derivative of `convDensityAdd pX g_t` is the convolution of `pX` against
`deriv g_t`: `deriv (convDensityAdd pX g_t) z = convDensityAdd pX (deriv g_t) z`. -/
theorem deriv_convDensityAdd_eq {pX : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hpX_int : Integrable pX volume) :
    deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = convDensityAdd pX (deriv (gaussianPDFReal 0 ⟨t, ht.le⟩)) := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg
  have hregY : Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 g :=
    Common2026.Shannon.EPIBlachmanGaussianWitness.isRegularDensityV2_gaussianPDFReal hv_ne
  have hY_bdd : ∃ M : ℝ, ∀ w, |g w| ≤ M :=
    ⟨_, gaussianPDFReal_abs_le ⟨t, ht.le⟩⟩
  have hY'_bdd : ∃ M : ℝ, ∀ w, |deriv g w| ≤ M := deriv_gaussianPDFReal_abs_le hv_ne
  funext z
  -- gateway: `HasDerivAt (convDensityAdd pX g) (∫ x, convDensityAddDeriv pX g z x) z`
  have hderiv :=
    InformationTheory.Shannon.EPIConvDensityGaussianGateway.convDensityAdd_hasDerivAt_of_integrable_smoothKernel
      pX g z hpX_int hregY hY_bdd hY'_bdd
  rw [hderiv.deriv]
  -- `∫ x, convDensityAddDeriv pX g z x = ∫ x, pX x * deriv g (z - x) = convDensityAdd pX (deriv g) z`
  rfl

/-- **Convolution-with-Gaussian tail vanishing** (filter-generic).
For an integrable nonnegative `pX` and the Gaussian kernel `g = gaussianPDFReal 0 v`
that is globally bounded by `M` and vanishes (after the `z - x` shift) along the
filter `l`, the convolution `convDensityAdd pX g` vanishes along `l`. Dominated
convergence with bound `pX · M`. -/
theorem tendsto_convDensityAdd_gaussian_zero {pX : ℝ → ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : Filter.Tendsto (fun z : ℝ => z) l Filter.atTop ∨
          Filter.Tendsto (fun z : ℝ => z) l Filter.atBot) :
    Filter.Tendsto (convDensityAdd pX (gaussianPDFReal 0 v)) l (nhds 0) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 v with hg
  set M : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hM
  -- pointwise limit: for each `x`, `g (z - x) → 0` along `l`.
  have hshift : ∀ x : ℝ, Filter.Tendsto (fun z : ℝ => g (z - x)) l (nhds 0) := by
    intro x
    rcases hl with htop | hbot
    · have hsub : Filter.Tendsto (fun z : ℝ => z - x) l Filter.atTop :=
        Filter.tendsto_atTop_add_const_right l (-x) htop |>.congr (fun z => by ring)
      exact (tendsto_gaussianPDFReal_atTop 0 hv).comp hsub
    · have hsub : Filter.Tendsto (fun z : ℝ => z - x) l Filter.atBot :=
        Filter.tendsto_atBot_add_const_right l (-x) hbot |>.congr (fun z => by ring)
      exact (tendsto_gaussianPDFReal_atBot 0 hv).comp hsub
  -- `convDensityAdd pX g z = ∫ x, pX x * g (z - x)`; the limit is `∫ x, 0 = 0`.
  have hconv_eq : convDensityAdd pX g = fun z => ∫ x, pX x * g (z - x) ∂volume := rfl
  rw [hconv_eq]
  have hbound_int : Integrable (fun x => pX x * M) volume := hpX_int.mul_const M
  have hF_meas : ∀ᶠ z in l, AEStronglyMeasurable (fun x => pX x * g (z - x)) volume := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hg_cont : Continuous g := by
      rw [hg]; exact (Common2026.Shannon.differentiable_gaussianPDFReal 0 v).continuous
    exact hpX_int.aestronglyMeasurable.mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hbound : ∀ᶠ z in l, ∀ᵐ x ∂volume, ‖pX x * g (z - x)‖ ≤ pX x * M := by
    refine Filter.Eventually.of_forall (fun z => Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |pX x| = pX x := abs_of_nonneg (hpX_nn x)
    have h2 : |g (z - x)| ≤ M := by rw [hg, hM]; exact gaussianPDFReal_abs_le v (z - x)
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (hpX_nn x)
  have hlim : ∀ᵐ x ∂volume, Filter.Tendsto (fun z => pX x * g (z - x)) l (nhds 0) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have := (hshift x).const_mul (pX x)
    simpa using this
  have := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := l) (F := fun z x => pX x * g (z - x)) (f := fun _ => (0 : ℝ))
    (fun x => pX x * M) hF_meas hbound hbound_int hlim
  simpa using this

/-- **A-5 precondition (1) producer.** `convDensityAdd pX g_t` is a regular V2
density for `t > 0` and any probability density `pX`. -/
theorem isRegularDensityV2_convDensityAdd_gaussian (pX : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x)
    (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mass : 0 < ∫ x, pX x ∂volume) :
    Common2026.Shannon.FisherInfoV2.IsRegularDensityV2
      (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
        (ProbabilityTheory.gaussianPDFReal 0 ⟨t, ht.le⟩)) := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg
  have hregY : Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 g :=
    Common2026.Shannon.EPIBlachmanGaussianWitness.isRegularDensityV2_gaussianPDFReal hv_ne
  have hY_bdd : ∃ M : ℝ, ∀ w, |g w| ≤ M :=
    ⟨_, gaussianPDFReal_abs_le ⟨t, ht.le⟩⟩
  have hY'_bdd : ∃ M : ℝ, ∀ w, |deriv g w| ≤ M := deriv_gaussianPDFReal_abs_le hv_ne
  -- `deriv g` integrability + measurability (for the envelope)
  have hg'_int : Integrable (deriv g) volume :=
    Common2026.Shannon.integrable_deriv_gaussianPDFReal 0 hv_ne
  have hg'_meas : Measurable (deriv g) := measurable_deriv g
  -- derivative identification
  have hderiv_eq : deriv (convDensityAdd pX g) = convDensityAdd pX (deriv g) :=
    deriv_convDensityAdd_eq ht hpX_int
  refine
    { diff := ?_
      pos := ?_
      tail_bot := ?_
      tail_top := ?_
      integrable_deriv := ?_
      integral_deriv_eq_zero := ?_ }
  · -- diff
    exact
      InformationTheory.Shannon.EPIConvDensityGaussianGateway.convDensityAdd_differentiable_of_integrable_smoothKernel
        pX g hpX_int hregY hY_bdd hY'_bdd
  · -- pos
    intro x
    exact Common2026.Shannon.FisherInfoV2.convDensityAdd_pos
      pX hpX_nn hpX_int hpX_mass ht x
  · -- tail_bot
    exact tendsto_convDensityAdd_gaussian_zero hv_ne hpX_nn hpX_int (Or.inr Filter.tendsto_id)
  · -- tail_top
    exact tendsto_convDensityAdd_gaussian_zero hv_ne hpX_nn hpX_int (Or.inl Filter.tendsto_id)
  · -- integrable_deriv
    rw [hderiv_eq]
    exact Common2026.Shannon.FisherInfoV2.convDensityAdd_envelope_integrable
      pX (deriv g) hpX_int hpX_meas hg'_int hg'_meas
  · -- integral_deriv_eq_zero
    rw [hderiv_eq]
    -- `∫ z, convDensityAdd pX (deriv g) z = ∫ z, ∫ x, pX x * deriv g (z - x) dx dz`
    show (∫ z, ∫ x, pX x * deriv g (z - x) ∂volume ∂volume) = 0
    -- product integrability of `(z,x) ↦ pX x * deriv g (z - x)`
    set f : ℝ → ℝ → ℝ := fun z x => pX x * deriv g (z - x) with hf
    have hf_meas : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => pX p.2) (volume.prod volume) :=
        (hpX_meas.comp measurable_snd).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => deriv g (p.1 - p.2))
          (volume.prod volume) := by
        have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
        exact (hg'_meas.comp hsub).aestronglyMeasurable
      exact h1.mul h2
    have hf_int : Integrable (Function.uncurry f) (volume.prod volume) := by
      rw [integrable_prod_iff' hf_meas]
      refine ⟨?_, ?_⟩
      · refine Filter.Eventually.of_forall (fun z => ?_)
        exact (hg'_int.comp_sub_right z).const_mul (pX z)
      · have heq : (fun x => ∫ z, ‖Function.uncurry f (z, x)‖ ∂volume)
            = (fun x => ‖pX x‖ * ∫ z, ‖deriv g z‖ ∂volume) := by
          funext x
          simp only [hf, Function.uncurry, norm_mul]
          rw [integral_const_mul]
          congr 1
          rw [← integral_sub_right_eq_self (fun z => ‖deriv g z‖) x]
        rw [heq]
        exact hpX_int.norm.mul_const _
    -- swap order of integration
    rw [integral_integral_swap hf_int]
    -- `∫ x, ∫ z, pX x * deriv g (z - x) dz dx`, inner integral `= 0`
    have hinner : ∀ x, (∫ z, f z x ∂volume) = 0 := by
      intro x
      simp only [hf]
      rw [integral_const_mul, integral_sub_right_eq_self (fun z => deriv g z) x,
        Common2026.Shannon.integral_deriv_gaussianPDFReal_eq_zero 0 hv_ne, mul_zero]
    simp_rw [hinner]
    exact integral_zero _ _

end Common2026.Shannon.EPIConvDensityRegular
