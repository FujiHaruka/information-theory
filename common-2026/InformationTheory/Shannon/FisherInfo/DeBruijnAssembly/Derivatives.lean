import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijnPerTime
import InformationTheory.Shannon.FisherConvBound
import InformationTheory.Shannon.EPI.Conv.DensitySecondDeriv
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Core
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Domination

namespace InformationTheory.Shannon.FisherInfo

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-- The square-score density `(logDeriv p_t)² · p_t` of the convolution density
`p_t = convDensityAdd pX g_t` is Lebesgue-integrable, where `g_t = gaussianPDFReal 0 ⟨t, _⟩`.
The Fisher information `J(X + √t · Z) = ∫ (logDeriv p_t)² · p_t` is bounded by `1 / t`
(`gaussianConv_fisher_le_inv_var`) and hence finite, so the integrand is integrable.

@audit:ok -/
theorem convDensityAdd_fisher_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦ (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
      * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_def
  -- Step 2: `p_t ≥ 0` pointwise (convolution of nonnegatives).
  have hp_nn : ∀ x, 0 ≤ p_t x := fun x ↦
    integral_nonneg fun y ↦ mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- the integrand `g x = (logDeriv p_t x)² · p_t x` is pointwise nonnegative.
  have hg_nn : 0 ≤ᵐ[volume] fun x ↦ (logDeriv p_t x) ^ 2 * p_t x :=
    Filter.Eventually.of_forall fun x ↦ mul_nonneg (sq_nonneg _) (hp_nn x)
  -- Step 3: shared Stam-convolution-Fisher wall `J(p_t) ≤ 1/t`.
  have hbound : fisherInfoOfDensity p_t ≤ ENNReal.ofReal (1 / t) :=
    gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int hpX_mass ht
  -- Step 4: hence `J(p_t) < ⊤`.
  have hfin : fisherInfoOfDensity p_t < ⊤ :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  -- Step 5: merge the two `ENNReal.ofReal` factors so the lintegrand is `ofReal g`.
  have hmerge :
      fisherInfoOfDensity p_t
        = ∫⁻ x, ENNReal.ofReal ((logDeriv p_t x) ^ 2 * p_t x) ∂volume := by
    unfold fisherInfoOfDensity
    refine lintegral_congr fun x ↦ ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  -- `∫⁻ ofReal g < ⊤` i.e. `≠ ∞`.
  rw [hmerge] at hfin
  -- Step 6: a.e.-strong-measurability of `g = (logDeriv p_t)² · p_t`.
  -- `p_t = z ↦ ∫ x, pX x · g_t (z - x)` is strongly measurable (parametric integral of a
  -- jointly measurable integrand); `logDeriv p_t = deriv p_t / p_t` with `deriv p_t`
  -- measurable. All genuine plumbing (Mathlib `StronglyMeasurable.integral_prod_right` +
  -- `measurable_deriv`), not a wall.
  have hgt_meas : Measurable (gaussianPDFReal 0 ⟨t, ht.le⟩) :=
    measurable_gaussianPDFReal 0 ⟨t, ht.le⟩
  have hpt_meas : Measurable p_t := by
    have huncurry :
        StronglyMeasurable
          (Function.uncurry fun z x ↦ pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
      apply Measurable.stronglyMeasurable
      apply (hpX_meas.comp measurable_snd).mul
      exact hgt_meas.comp ((measurable_fst).sub measurable_snd)
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [hp_def, convDensityAdd] using h.measurable
  have hderiv_meas : Measurable (deriv p_t) := measurable_deriv p_t
  have hlogderiv_meas : Measurable (logDeriv p_t) := by
    simp only [logDeriv]
    exact hderiv_meas.div hpt_meas
  have hg_aesm :
      AEStronglyMeasurable (fun x ↦ (logDeriv p_t x) ^ 2 * p_t x) volume :=
    ((hlogderiv_meas.pow_const 2).mul hpt_meas).aestronglyMeasurable
  -- Step 6 (concl): `∫⁻ ofReal g ≠ ∞ ↔ Integrable g`.
  exact (lintegral_ofReal_ne_top_iff_integrable hg_aesm hg_nn).mp hfin.ne

/-- `HasDerivAt p_t (deriv p_t x) x` for `p_t = convDensityAdd pX g_t` at every `x` (`t > 0`):
the spatial first derivative of the heat-flow convolution density exists, reconstructed via the
parametric-integral gateway `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
domination supplied by `kernel_x_deriv1_global_bound`.

@audit:ok -/
theorem convDensityAdd_hasDerivAt_self
    (pX : ℝ → ℝ) (_hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) x := by
  -- kernel continuity / measurability.
  have hker_cont : Continuous (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel t u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel t u) :=
    hker_cont.measurable
  -- `convDensityAdd pX g_t = fun ζ => ∫ y, pX y · kernel t (ζ-y)` (t>0).
  have hconv_eq : (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = (fun ζ : ℝ ↦ ∫ y, pX y * heatFlow_density_heat_equation_kernel t (ζ - y) ∂volume) := by
    funext ζ
    unfold convDensityAdd
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq ht (ζ - y)]
  -- the global-sup constant of the kernel 1st spatial derivative.
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + 2 * t * Real.exp (-1)) / (2 * t)) with hM1
  -- domination group for the parametric-integral gateway (`bound1 := |pX y| · M1`).
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y ↦ pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel t v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq ht v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨t, ht.le⟩ v
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y ↦ pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y ↦ pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const t).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))‖ ≤ (fun y ↦ |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound ht (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y ↦ |pX y| * M1) volume := hpX_int.abs.mul_const _
  -- per-y spatial 1st-derivative HasDerivAt (kernel `_x_deriv1` chained through `ξ ↦ ξ-y`).
  have hdiff : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ ↦ pX y * heatFlow_density_heat_equation_kernel t (ξ - y))
        (pX y * (heatFlow_density_heat_equation_kernel t (ξ - y) * (-((ξ - y) / t)))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv1 ht (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ ↦ ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  -- parametric-integral gateway at `x`.
  have hgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ζ y ↦ pX y * heatFlow_density_heat_equation_kernel t (ζ - y))
      (F' := fun ζ y ↦ pX y * (heatFlow_density_heat_equation_kernel t (ζ - y)
        * (-((ζ - y) / t))))
      (bound := fun y ↦ |pX y| * M1) (Filter.univ_mem)
      (Filter.Eventually.of_forall hF1_meas) (hF1_int x) (hF1'_meas x)
      hb1 hb1_int hdiff
  -- `hgate.2 : HasDerivAt p_t (∫ y, pX y · kernel·(-(x-y)/t)) x`.
  have hderiv : HasDerivAt (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      (∫ y, pX y * (heatFlow_density_heat_equation_kernel t (x - y) * (-((x - y) / t))) ∂volume)
      x := by
    rw [hconv_eq]; exact hgate.2
  -- conclude `HasDerivAt p_t (deriv p_t x) x` by rewriting the derivative value.
  rw [hderiv.deriv]
  exact hderiv

/-- `HasDerivAt (deriv p_t) (deriv (deriv p_t) x) x` for `p_t = convDensityAdd pX g_t` at every
`x` (`t > 0`): the spatial second derivative exists. The proof identifies `deriv p_t` as the
kernel-form first-derivative function (`convDensityAdd_deriv1_gaussian_eq`) and differentiates it
via the parametric-integral gateway with domination from `kernel_x_deriv2_global_bound`.

@audit:ok -/
theorem convDensityAdd_deriv_hasDerivAt_self
    (pX : ℝ → ℝ) (_hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      (deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) x := by
  -- kernel continuity / measurability.
  have hker_cont : Continuous (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel t u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel t u) :=
    hker_cont.measurable
  -- global-sup constants of the kernel 1st / 2nd spatial derivatives.
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ * ((1 + 2 * t * Real.exp (-1)) / (2 * t)) with hM1
  set M2 : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ * ((2 * Real.exp (-1) + 1) / t) with hM2
  -- ===== bound1 group (for the deriv1 atom function equality) =====
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y ↦ pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel t v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq ht v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨t, ht.le⟩ v
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y ↦ pX y * heatFlow_density_heat_equation_kernel t (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y ↦ pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const t).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t)))‖ ≤ (fun y ↦ |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound ht (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y ↦ |pX y| * M1) volume := hpX_int.abs.mul_const _
  -- ===== bound2 group (for the 2nd gateway) =====
  have hb2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * ((ξ - y) ^ 2 / t ^ 2 - 1 / t))‖ ≤ (fun y ↦ |pX y| * M2) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv2_global_bound ht (ξ - y)
    rwa [hM2]
  have hb2_int : Integrable (fun y ↦ |pX y| * M2) volume := hpX_int.abs.mul_const _
  have hF2'_meas : AEStronglyMeasurable
      (fun y ↦ pX y * (heatFlow_density_heat_equation_kernel t (x - y)
        * ((x - y) ^ 2 / t ^ 2 - 1 / t))) volume := by
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
        measurable_const |>.aestronglyMeasurable
  have hF2_int : Integrable
      (fun y ↦ pX y * (heatFlow_density_heat_equation_kernel t (x - y)
        * (-((x - y) / t)))) volume := by
    refine Integrable.mono' hb1_int (hF1'_meas x) (Filter.Eventually.of_forall (fun y ↦ ?_))
    have := kernel_x_deriv1_global_bound ht (x - y)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rwa [hM1]
  -- STEP 1: identify `deriv p_t` as the 1st-derivative integral function (deriv1 atom).
  have hd1 := InformationTheory.Shannon.EPIConvDensitySecondDeriv.convDensityAdd_deriv1_gaussian_eq
    pX ht (fun y ↦ |pX y| * M1) hb1_int hF1_meas hF1_int hF1'_meas hb1
  -- the 1st-derivative function, in kernel form.
  have hd1_kernel : (fun ζ : ℝ ↦ ∫ y, pX y * (gaussianPDFReal 0 ⟨t, ht.le⟩ (ζ - y)
        * (-((ζ - y) / t))) ∂volume)
      = (fun ζ : ℝ ↦ ∫ y, pX y * (heatFlow_density_heat_equation_kernel t (ζ - y)
          * (-((ζ - y) / t))) ∂volume) := by
    funext ζ
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq ht (ζ - y)]
  -- so `deriv p_t = kernel-form 1st-derivative function`.
  have hderiv_eq : deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = (fun ζ : ℝ ↦ ∫ y, pX y * (heatFlow_density_heat_equation_kernel t (ζ - y)
          * (-((ζ - y) / t))) ∂volume) := by
    rw [hd1, hd1_kernel]
  -- STEP 2: per-y spatial 2nd-derivative HasDerivAt (kernel `_x_deriv2` chained through `ξ ↦ ξ-y`).
  have hdiff2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ ↦ pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
          * (-((ξ - y) / t))))
        (pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
          * ((ξ - y) ^ 2 / t ^ 2 - 1 / t))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv2 ht (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ ↦ ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  -- the 2nd gateway at `x` (differentiate the kernel-form 1st-derivative function).
  have hgate2 :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ξ y ↦ pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * (-((ξ - y) / t))))
      (F' := fun ξ y ↦ pX y * (heatFlow_density_heat_equation_kernel t (ξ - y)
        * ((ξ - y) ^ 2 / t ^ 2 - 1 / t)))
      (bound := fun y ↦ |pX y| * M2) (Filter.univ_mem)
      (Filter.Eventually.of_forall hF1'_meas) hF2_int hF2'_meas
      hb2 hb2_int hdiff2
  -- `hgate2.2 : HasDerivAt (kernel-form 1st-deriv fn) (∫ y, pX y·kernel·((x-y)²/t²-1/t)) x`.
  have hderiv2 : HasDerivAt (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      (∫ y, pX y * (heatFlow_density_heat_equation_kernel t (x - y)
        * ((x - y) ^ 2 / t ^ 2 - 1 / t)) ∂volume) x := by
    rw [hderiv_eq]; exact hgate2.2
  -- conclude by rewriting the 2nd-derivative value.
  rw [hderiv2.deriv]
  exact hderiv2

/-! ## Entropy-finiteness plumbing

Three integrability lemmas for the entropy of the convolution density, with a uniform
signature: `pX` nonnegative, measurable, integrable, mass `1`, and finite second moment. They
close from the Gaussian envelopes and the log-factor polynomial majorant in this file. -/

/-- The `s`-uniform Gaussian gradient kernel majorant on the window `s ∈ (t/2, 2t)`:
`g_s(u) · |u/s| ≤ gaussGradMaj t u := (√(πt))⁻¹ · exp(−u²/(4t)) · (2|u|/t)`, the
first-derivative analog of `gaussHessMaj`. A Gaussian times a linear factor, hence
Lebesgue-integrable.

@audit:ok -/
private noncomputable def gaussGradMaj (t : ℝ) (u : ℝ) : ℝ :=
  (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (4 * t)) * (2 * |u| / t)

/-- `gaussGradMaj t` is nonnegative. -/
private theorem gaussGradMaj_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ gaussGradMaj t u := by
  unfold gaussGradMaj
  have h1 : (0:ℝ) ≤ (Real.sqrt (Real.pi * t))⁻¹ := by positivity
  have h2 : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  have h3 : (0:ℝ) ≤ 2 * |u| / t := by positivity
  positivity

/-- `gaussGradMaj t` is globally bounded (Gaussian decay kills the linear factor). -/
private theorem gaussGradMaj_bdd {t : ℝ} (ht : 0 < t) :
    ∀ u : ℝ, gaussGradMaj t u
      ≤ (Real.sqrt (Real.pi * t))⁻¹ * ((1 + 4 * t * Real.exp (-1)) / t) := by
  intro u
  unfold gaussGradMaj
  set P : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- key: `exp(-u²/(4t))·|u| ≤ (1 + 4t·exp(-1))/2`, then `·(2/t)`.
  have hkey : Real.exp (-u ^ 2 / (4 * t)) * |u| ≤ (1 + 4 * t * Real.exp (-1)) / 2 := by
    have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (4 * t))
    have hexp_eq : Real.exp (-(u ^ 2 / (4 * t))) = Real.exp (-u ^ 2 / (4 * t)) := by
      congr 1; ring
    rw [hexp_eq] at hmul
    have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) ≤ 4 * t * Real.exp (-1) := by
      have h4s : (0:ℝ) < 4 * t := by linarith
      have hmul' := mul_le_mul_of_nonneg_left hmul h4s.le
      have heq : (4 * t) * ((u ^ 2 / (4 * t)) * Real.exp (-u ^ 2 / (4 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) := by field_simp
      rw [heq] at hmul'
      linarith [hmul']
    have hexp_le1 : Real.exp (-u ^ 2 / (4 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (4 * t) := by positivity
      linarith [neg_div (4 * t) (u ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left h2u hexp_nn, hu2, hexp_le1, abs_nonneg u]
  calc Real.exp (-u ^ 2 / (4 * t)) * (2 * |u| / t)
      = (Real.exp (-u ^ 2 / (4 * t)) * |u|) * (2 / t) := by ring
    _ ≤ ((1 + 4 * t * Real.exp (-1)) / 2) * (2 / t) := by
        apply mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (1 + 4 * t * Real.exp (-1)) / t := by ring

/-- `gaussGradMaj t` is Lebesgue-integrable (Gaussian × linear). -/
private theorem gaussGradMaj_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussGradMaj t) volume := by
  have hb : (0:ℝ) < 1 / (4 * t) := by positivity
  set c : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hc
  -- the two Gaussian building blocks: `exp(-b u²)` and `u²·exp(-b u²)`.
  have hexp : Integrable (fun u : ℝ ↦ Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  have hsq : Integrable (fun u : ℝ ↦ u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)
    refine this.congr (Filter.Eventually.of_forall (fun u ↦ ?_))
    simp only [Real.rpow_two]
  -- majorant `M u = (c/t)·(exp + u²·exp)` integrable; dominates `gaussGradMaj` via `2|u| ≤ 1+u²`.
  have hM_int : Integrable
      (fun u : ℝ ↦ c / t * (Real.exp (-(1 / (4 * t)) * u ^ 2)
        + u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))) volume :=
    (hexp.add hsq).const_mul _
  refine Integrable.mono' hM_int (by unfold gaussGradMaj; fun_prop) ?_
  filter_upwards with u
  have hexp_eq : Real.exp (-u ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * u ^ 2) := by
    congr 1; field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussGradMaj_nonneg ht u)]
  unfold gaussGradMaj
  rw [hexp_eq]
  -- `c·exp·(2|u|/t) ≤ (c/t)·(1+u²)·exp` from `2|u| ≤ 1+u²`.
  have hc_nn : (0:ℝ) ≤ c := by rw [hc]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-(1 / (4 * t)) * u ^ 2) := (Real.exp_pos _).le
  have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hineq : c * Real.exp (-(1 / (4 * t)) * u ^ 2) * (2 * |u| / t)
      ≤ c / t * (Real.exp (-(1 / (4 * t)) * u ^ 2)
        + u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) := by
    have hexpand : c / t * (Real.exp (-(1 / (4 * t)) * u ^ 2)
          + u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))
        = (c / t) * (1 + u ^ 2) * Real.exp (-(1 / (4 * t)) * u ^ 2) := by ring
    have hlhs : c * Real.exp (-(1 / (4 * t)) * u ^ 2) * (2 * |u| / t)
        = (c / t) * (2 * |u|) * Real.exp (-(1 / (4 * t)) * u ^ 2) := by ring
    rw [hexpand, hlhs]
    apply mul_le_mul_of_nonneg_right _ hexp_nn
    apply mul_le_mul_of_nonneg_left h2u (by positivity)
  exact hineq

/-- For constants `a b`, `(a + b·u²)·gaussGradMaj t u` is Lebesgue-integrable
(Gaussian × cubic). -/
private theorem gaussGradMaj_polyWeight_integrable {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    Integrable (fun u : ℝ ↦ (a + b * u ^ 2) * gaussGradMaj t u) volume := by
  have hbpos : (0:ℝ) < 1 / (4 * t) := by positivity
  set c : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hc
  have hc_nn : (0:ℝ) ≤ c := by rw [hc]; positivity
  -- the three Gaussian moment building blocks: `exp`, `u²·exp`, `u⁴·exp`.
  have hexp : Integrable (fun u : ℝ ↦ Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hbpos
  have hsq : Integrable (fun u : ℝ ↦ u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hbpos (by norm_num : (-1:ℝ) < 2)
    refine this.congr (Filter.Eventually.of_forall (fun u ↦ ?_))
    simp only [Real.rpow_two]
  have hquart : Integrable (fun u : ℝ ↦ u ^ 4 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hbpos (by norm_num : (-1:ℝ) < 4)
    refine this.congr (Filter.Eventually.of_forall (fun u ↦ ?_))
    simp only []
    rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- even majorant `M u = (c/t)·(|a|(1+u²) + |b|(u²+u⁴))·exp` integrable.
  have hM_int : Integrable
      (fun u : ℝ ↦ c / t * ((|a| * (1 + u ^ 2) + |b| * (u ^ 2 + u ^ 4))
        * Real.exp (-(1 / (4 * t)) * u ^ 2))) volume := by
    have hcomb : Integrable
        (fun u : ℝ ↦
            (c / t * |b|) * (u ^ 4 * Real.exp (-(1 / (4 * t)) * u ^ 2))
          + (c / t * (|a| + |b|)) * (u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))
          + (c / t * |a|) * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
      ((hquart.const_mul _).add (hsq.const_mul _)).add (hexp.const_mul _)
    refine hcomb.congr (Filter.Eventually.of_forall (fun u ↦ ?_))
    simp only []; ring
  refine Integrable.mono' hM_int (by unfold gaussGradMaj; fun_prop) ?_
  filter_upwards with u
  have hexp_eq : Real.exp (-u ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * u ^ 2) := by
    congr 1; field_simp
  have hexp_nn : (0:ℝ) ≤ Real.exp (-(1 / (4 * t)) * u ^ 2) := (Real.exp_pos _).le
  -- `‖(a+bu²)·gaussGradMaj‖ ≤ (|a|+|b|u²)·gaussGradMaj` (gaussGradMaj ≥ 0).
  have hg_nn : (0:ℝ) ≤ gaussGradMaj t u := gaussGradMaj_nonneg ht u
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg_nn]
  have habs : |a + b * u ^ 2| ≤ |a| + |b| * u ^ 2 := by
    calc |a + b * u ^ 2| ≤ |a| + |b * u ^ 2| := abs_add_le _ _
      _ = |a| + |b| * u ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
  refine le_trans (mul_le_mul_of_nonneg_right habs hg_nn) ?_
  -- `(|a|+|b|u²)·gaussGradMaj = (2c/t)(|a|+|b|u²)|u|·exp ≤ M u` via `2|u|≤1+u²`, `2|u|³≤u²+u⁴`.
  unfold gaussGradMaj
  rw [hexp_eq]
  have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have h2u3 : 2 * |u| ^ 3 ≤ u ^ 2 + u ^ 4 := by
    have hcube : |u| ^ 3 = |u| * u ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [hcube]
    have : 2 * (|u| * u ^ 2) = (2 * |u|) * u ^ 2 := by ring
    rw [this]
    calc (2 * |u|) * u ^ 2 ≤ (1 + u ^ 2) * u ^ 2 :=
          mul_le_mul_of_nonneg_right h2u (sq_nonneg u)
      _ = u ^ 2 + u ^ 4 := by ring
  -- `(|a|+|b|u²)·(c·exp·2|u|/t) = (c/t)·exp·((|a|+|b|u²)·2|u|)`.
  have hlhs : (|a| + |b| * u ^ 2) * (c * Real.exp (-(1 / (4 * t)) * u ^ 2) * (2 * |u| / t))
      = (c / t) * Real.exp (-(1 / (4 * t)) * u ^ 2) * ((|a| + |b| * u ^ 2) * (2 * |u|)) := by
    ring
  rw [hlhs]
  have hrhs : c / t * ((|a| * (1 + u ^ 2) + |b| * (u ^ 2 + u ^ 4))
        * Real.exp (-(1 / (4 * t)) * u ^ 2))
      = (c / t) * Real.exp (-(1 / (4 * t)) * u ^ 2)
        * (|a| * (1 + u ^ 2) + |b| * (u ^ 2 + u ^ 4)) := by ring
  rw [hrhs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- `(|a|+|b|u²)·2|u| = |a|·2|u| + |b|·u²·2|u| ≤ |a|(1+u²) + |b|(u²+u⁴)`.
  have hexpand : (|a| + |b| * u ^ 2) * (2 * |u|)
      = |a| * (2 * |u|) + |b| * (2 * |u| ^ 3) := by
    rw [show |u| ^ 3 = |u| * u ^ 2 by rw [pow_succ, sq_abs]; ring]; ring
  rw [hexpand]
  have ha_nn : (0:ℝ) ≤ |a| := abs_nonneg a
  have hb_nn : (0:ℝ) ≤ |b| := abs_nonneg b
  calc |a| * (2 * |u|) + |b| * (2 * |u| ^ 3)
      ≤ |a| * (1 + u ^ 2) + |b| * (u ^ 2 + u ^ 4) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h2u ha_nn
        · exact mul_le_mul_of_nonneg_left h2u3 hb_nn

/-- For nonneg constants `a b`, `(a + b·u²)·gaussGradMaj t u` is globally bounded. -/
private theorem gaussGradMaj_polyWeight_bdd {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C : ℝ, ∀ u : ℝ, (a + b * u ^ 2) * gaussGradMaj t u ≤ C := by
  set c : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hc
  have hc_nn : (0:ℝ) ≤ c := by rw [hc]; positivity
  -- two scalar bounds: `|u|·exp(-u²/4t) ≤ K1` and `|u|³·exp(-u²/4t) ≤ K2`.
  set K1 : ℝ := (1 + 4 * t * Real.exp (-1)) / 2 with hK1
  set K2 : ℝ := ((1 + 8 * t * Real.exp (-1)) / 2) * (8 * t * Real.exp (-1)) with hK2
  refine ⟨(2 * c / t) * (a * K1 + b * K2), fun u ↦ ?_⟩
  have hexp4_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  have hexp8_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (8 * t)) := (Real.exp_pos _).le
  -- `|u|·exp(-u²/4t) ≤ K1`.
  have hu1 : |u| * Real.exp (-u ^ 2 / (4 * t)) ≤ K1 := by
    have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (4 * t))
    have hexp_eq : Real.exp (-(u ^ 2 / (4 * t))) = Real.exp (-u ^ 2 / (4 * t)) := by congr 1; ring
    rw [hexp_eq] at hmul
    have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) ≤ 4 * t * Real.exp (-1) := by
      have h4s : (0:ℝ) < 4 * t := by linarith
      have hmul' := mul_le_mul_of_nonneg_left hmul h4s.le
      have heq : (4 * t) * ((u ^ 2 / (4 * t)) * Real.exp (-u ^ 2 / (4 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) := by field_simp
      rw [heq] at hmul'; linarith [hmul']
    have hexp_le1 : Real.exp (-u ^ 2 / (4 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (4 * t) := by positivity
      linarith [neg_div (4 * t) (u ^ 2)]
    rw [hK1]; nlinarith [mul_le_mul_of_nonneg_left h2u hexp4_nn, hu2, hexp_le1, abs_nonneg u]
  -- `|u|³·exp(-u²/4t) = (|u|·exp(-u²/8t))·(u²·exp(-u²/8t)) ≤ K2`.
  have hu3 : |u| ^ 3 * Real.exp (-u ^ 2 / (4 * t)) ≤ K2 := by
    have hsplit : Real.exp (-u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t))
        = Real.exp (-u ^ 2 / (4 * t)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    -- `|u|·exp(-u²/8t) ≤ (1+8t e⁻¹)/2`.
    have hf1 : |u| * Real.exp (-u ^ 2 / (8 * t)) ≤ (1 + 8 * t * Real.exp (-1)) / 2 := by
      have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
      have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (8 * t))
      have hexp_eq : Real.exp (-(u ^ 2 / (8 * t))) = Real.exp (-u ^ 2 / (8 * t)) := by congr 1; ring
      rw [hexp_eq] at hmul
      have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) ≤ 8 * t * Real.exp (-1) := by
        have h8s : (0:ℝ) < 8 * t := by linarith
        have hmul' := mul_le_mul_of_nonneg_left hmul h8s.le
        have heq : (8 * t) * ((u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t)))
            = u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by field_simp
        rw [heq] at hmul'; linarith [hmul']
      have hexp_le1 : Real.exp (-u ^ 2 / (8 * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (8 * t) := by positivity
        linarith [neg_div (8 * t) (u ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left h2u hexp8_nn, hu2, hexp_le1, abs_nonneg u]
    -- `u²·exp(-u²/8t) ≤ 8t e⁻¹`.
    have hf2 : u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) ≤ 8 * t * Real.exp (-1) := by
      have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (8 * t))
      have hexp_eq : Real.exp (-(u ^ 2 / (8 * t))) = Real.exp (-u ^ 2 / (8 * t)) := by congr 1; ring
      rw [hexp_eq] at hmul
      have h8s : (0:ℝ) < 8 * t := by linarith
      have hmul' := mul_le_mul_of_nonneg_left hmul h8s.le
      have heq : (8 * t) * ((u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by field_simp
      rw [heq] at hmul'; linarith [hmul']
    have hf1_nn : (0:ℝ) ≤ |u| * Real.exp (-u ^ 2 / (8 * t)) := by positivity
    have hf2_nn : (0:ℝ) ≤ u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by positivity
    have hprod := mul_le_mul hf1 hf2 hf2_nn (by positivity)
    have heq : (|u| * Real.exp (-u ^ 2 / (8 * t))) * (u ^ 2 * Real.exp (-u ^ 2 / (8 * t)))
        = |u| ^ 3 * Real.exp (-u ^ 2 / (4 * t)) := by
      rw [show |u| ^ 3 = |u| * u ^ 2 by rw [pow_succ, sq_abs]; ring, ← hsplit]; ring
    rw [heq] at hprod
    rw [hK2]; exact hprod
  -- assemble: `(a+bu²)·gaussGradMaj = (2c/t)·(a·|u|exp + b·|u|³exp) ≤ (2c/t)(a K1 + b K2)`.
  unfold gaussGradMaj
  rw [← hc]
  have hform : (a + b * u ^ 2) * (c * Real.exp (-u ^ 2 / (4 * t)) * (2 * |u| / t))
      = (2 * c / t) * (a * (|u| * Real.exp (-u ^ 2 / (4 * t)))
          + b * (|u| ^ 3 * Real.exp (-u ^ 2 / (4 * t)))) := by
    rw [show |u| ^ 3 = |u| * u ^ 2 by rw [pow_succ, sq_abs]; ring]; ring
  rw [hform]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hu1 ha
  · exact mul_le_mul_of_nonneg_left hu3 hb

/-- `g_s(u) · |u/s| ≤ gaussGradMaj t u` for `s ∈ (t/2, 2t)`. -/
private theorem gaussianGrad_le_gaussGradMaj {t : ℝ} (ht : 0 < t) {s : ℝ}
    (hs : s ∈ Set.Ioo (t/2) (2*t)) (u : ℝ) :
    gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩ u
        * (|u| / s)
      ≤ gaussGradMaj t u := by
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  have ht2s : t < 2 * s := by have := hs.1; linarith
  have hs2t : s ≤ 2 * t := hs.2.le
  rw [gaussianPDFReal]
  simp only [sub_zero]
  have hpref : (Real.sqrt (2 * Real.pi * s))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ := by
    apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  have hexp : Real.exp (-u ^ 2 / (2 * s)) ≤ Real.exp (-u ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u, hs2t]
  have hpoly : |u| / s ≤ 2 * |u| / t := by
    rw [div_le_div_iff₀ hspos ht]
    have : t ≤ 2 * s := by linarith
    nlinarith [abs_nonneg u, this]
  have hpref_nn : (0:ℝ) ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  have hpoly_nn : (0:ℝ) ≤ |u| / s := by positivity
  have hprefT_nn : (0:ℝ) ≤ (Real.sqrt (Real.pi * t))⁻¹ := by positivity
  have hexpT_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  unfold gaussGradMaj
  calc (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)) * (|u| / s)
      ≤ (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (4 * t)) * (2 * |u| / t) := by
        apply mul_le_mul (mul_le_mul hpref hexp hexp_nn hprefT_nn) hpoly hpoly_nn
        exact mul_nonneg hprefT_nn hexpT_nn

/-- `‖∂_x p_s x‖ ≤ ∫ pX y · gaussGradMaj t (x − y)` for `s ∈ (t/2, 2t)`, the gradient analog of
`convDensityAdd_deriv2_le_gaussHessMaj_conv`. -/
private theorem convDensityAdd_deriv1_le_gaussGradMaj_conv
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioo (t/2) (2*t)) :
    ‖deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩)) x‖
      ≤ ∫ y, pX y * gaussGradMaj t (x - y) ∂volume := by
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  have hker_cont : Continuous (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel s u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel s u) :=
    hker_cont.measurable
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) with hM1
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel s v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq hspos v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨s, hspos.le⟩ v
  -- the `bound1` group of `convDensityAdd_deriv1_gaussian_eq` (= the deriv2 lemma's bound1 group).
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y ↦ pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y ↦ pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y ↦ pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))‖ ≤ (fun y ↦ |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound hspos (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y ↦ |pX y| * M1) volume := hpX_int.abs.mul_const _
  -- the spatial-1st-derivative closed form.
  have hderiv1 :=
    InformationTheory.Shannon.EPIConvDensitySecondDeriv.convDensityAdd_deriv1_gaussian_eq pX hspos
      (fun y ↦ |pX y| * M1) hb1_int hF1_meas hF1_int hF1'_meas hb1
  rw [show (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩)
      = gaussianPDFReal 0 ⟨s, hspos.le⟩ from rfl, hderiv1]
  -- `‖∫ pX y·(g_s(x-y)·(-(x-y)/s))‖ ≤ ∫ ‖·‖ ≤ ∫ pX y·gaussGradMaj t (x-y)`.
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y ↦ norm_nonneg _)) ?_
    (Filter.Eventually.of_forall (fun y ↦ ?_))
  · have hMmeas : Measurable (gaussGradMaj t) := by unfold gaussGradMaj; fun_prop
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ u : ℝ, gaussGradMaj t u ≤ C := by
      refine ⟨(Real.sqrt (Real.pi * t))⁻¹ * ((1 + 4 * t * Real.exp (-1)) / t), fun u ↦ ?_⟩
      exact gaussGradMaj_bdd ht u
    refine hpX_int.mul_bdd (c := C) ?_ ?_
    · exact (hMmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussGradMaj_nonneg ht (x - y))]
      exact hC (x - y)
  · simp only []
    have hg_nn : (0:ℝ) ≤ gaussianPDFReal 0 ⟨s, hspos.le⟩ (x - y) := gaussianPDFReal_nonneg 0 _ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hpX_nn y)]
    apply mul_le_mul_of_nonneg_left _ (hpX_nn y)
    -- `‖g_s(x-y)·(-(x-y)/s)‖ = g_s(x-y)·(|x-y|/s) ≤ gaussGradMaj t (x-y)`.
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg_nn, abs_neg, abs_div, abs_of_pos hspos]
    exact gaussianGrad_le_gaussGradMaj ht hs (x - y)

/-- `Integrable ((- log p_t - 1) · ∂²_x p_t)` for `p_t = convDensityAdd pX g_t`, `t > 0`. Closes
from the joint-domination envelope `debruijnIdentityV2_holds_assembled_chain_domination`
instantiated at `s = t`.

@audit:ok -/
theorem convDensityAdd_logFactor_deriv2_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) volume := by
  -- `_chain_domination` at `s = t` (note `t ∈ Ioo (t/2)(2*t)`): the half-Hessian integrand
  -- `(- log p_t - 1)·((1/2)·∂²p_t)` is dominated by an integrable `bound`. Then `×2`.
  obtain ⟨bound, hbound_int, hb_dom⟩ :=
    debruijnIdentityV2_holds_assembled_chain_domination
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  -- `t ∈ Ioo (t/2)(2*t)`.
  have htmem : t ∈ Set.Ioo (t/2) (2*t) := ⟨by linarith, by linarith⟩
  -- the half-Hessian integrand at `s = t`, with `⟨t, _⟩` variance witness
  -- (= `_chain_domination`'s).
  set f : ℝ → ℝ := fun x ↦
    (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
      * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) with hf_def
  -- a.e.-strong-measurability of `f` (= log-factor × const · 2nd deriv).
  have hpath_meas : Measurable
      (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) := by
    have hg_meas : Measurable (gaussianPDFReal 0 ⟨t, ht.le⟩) :=
      measurable_gaussianPDFReal 0 _
    have huncurry : StronglyMeasurable
        (Function.uncurry fun z x ↦
          pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
      apply Measurable.stronglyMeasurable
      apply (hpX_meas.comp measurable_snd).mul
      exact hg_meas.comp ((measurable_fst).sub measurable_snd)
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [convDensityAdd] using h.measurable
  have hf_meas : AEStronglyMeasurable f volume := by
    rw [hf_def]
    have hlog_meas : Measurable
        (fun x ↦ - Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1) :=
      ((Real.measurable_log.comp hpath_meas).neg).sub_const 1
    have hd2_meas : Measurable
        (fun x ↦ (1:ℝ)/2 * deriv (deriv (convDensityAdd pX
          (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) :=
      (measurable_deriv _).const_mul _
    exact (hlog_meas.mul hd2_meas).aestronglyMeasurable
  -- `f` is integrable: dominated by `bound` (from `_chain_domination` at `s = t`).
  have hf_int : Integrable f volume := by
    refine Integrable.mono' hbound_int hf_meas ?_
    filter_upwards [hb_dom] with x hx
    -- the `⟨t,_⟩`-form half-Hessian at `s = t` equals `_chain_domination`'s `⟨t,_⟩`-form (defeq).
    have hbx := hx t htmem
    rw [hf_def]; exact hbx
  -- target `(- log p_t - 1)·∂²p_t = 2 · f x`.
  have heq : (fun x ↦
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x)
      = fun x ↦ (2 : ℝ) * f x := by
    funext x; rw [hf_def]; ring
  rw [heq]
  exact hf_int.const_mul 2

/-- `Integrable ((- log p_t - 1) · ∂_x p_t)` for `p_t = convDensityAdd pX g_t`, `t > 0`. Closes
from the log-factor polynomial majorant `convDensityAdd_logFactor_poly_majorant` and the
gradient envelope `gaussGradMaj`.

@audit:ok -/
theorem convDensityAdd_logFactor_deriv_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) volume := by
  have htmem : t ∈ Set.Ioo (t/2) (2*t) := ⟨by linarith, by linarith⟩
  -- log-factor polynomial majorant + gradient envelope `E x = ∫ pX y·gaussGradMaj t (x−y)`.
  obtain ⟨A, B, hB_nn, hLog⟩ :=
    convDensityAdd_logFactor_poly_majorant pX hpX_nn hpX_meas hpX_int hpX_mass ht
  set E : ℝ → ℝ := fun x ↦ ∫ y, pX y * gaussGradMaj t (x - y) ∂volume with hE_def
  have hg_meas : Measurable (gaussGradMaj t) := by unfold gaussGradMaj; fun_prop
  have hg_nn : ∀ u, (0:ℝ) ≤ gaussGradMaj t u := gaussGradMaj_nonneg ht
  -- the joint majorant `(A + B·x²)·E x` (same Tonelli route as `_chain_domination`).
  -- (1) the dominating integrable function `H x`.
  set G : ℝ → ℝ := fun u ↦ (|A| + 2 * |B| * u ^ 2) * gaussGradMaj t u with hG_def
  have hG_int : Integrable G volume := gaussGradMaj_polyWeight_integrable ht |A| (2 * |B|)
  have hG_meas : Measurable G := by rw [hG_def]; fun_prop
  have hG_nn : ∀ u, (0:ℝ) ≤ G u := fun u ↦ by
    rw [hG_def]; exact mul_nonneg (by positivity) (hg_nn u)
  have hmomPX_int : Integrable (fun y ↦ y ^ 2 * pX y) volume := hpX_mom
  have hmomPX_meas : Measurable (fun y ↦ y ^ 2 * pX y) := by fun_prop
  have hEnv1_int : Integrable (fun x ↦ ∫ y, pX y * G (x - y) ∂volume) volume :=
    convKernel_envelope_integrable pX G hpX_int hpX_meas hG_int hG_meas
  have hEnv2_int : Integrable (fun x ↦ ∫ y, (y ^ 2 * pX y) * gaussGradMaj t (x - y) ∂volume)
      volume :=
    convKernel_envelope_integrable (fun y ↦ y ^ 2 * pX y) (gaussGradMaj t)
      hmomPX_int hmomPX_meas (gaussGradMaj_integrable ht) hg_meas
  have hH_int : Integrable (fun x ↦ (∫ y, pX y * G (x - y) ∂volume)
      + 2 * |B| * (∫ y, (y ^ 2 * pX y) * gaussGradMaj t (x - y) ∂volume)) volume :=
    hEnv1_int.add (hEnv2_int.const_mul _)
  -- global bound of `gaussGradMaj` for fibre integrabilities (Integrable.mul_bdd).
  obtain ⟨Cg, hCg⟩ : ∃ C : ℝ, ∀ u : ℝ, gaussGradMaj t u ≤ C :=
    ⟨(Real.sqrt (Real.pi * t))⁻¹ * ((1 + 4 * t * Real.exp (-1)) / t), gaussGradMaj_bdd ht⟩
  obtain ⟨CG, hCG⟩ : ∃ C : ℝ, ∀ u : ℝ, G u ≤ C := by
    obtain ⟨C, hC⟩ :=
      gaussGradMaj_polyWeight_bdd ht (abs_nonneg A) (by positivity : (0:ℝ) ≤ 2 * |B|)
    exact ⟨C, fun u ↦ by rw [hG_def]; exact hC u⟩
  -- `E x` nonneg + measurable.
  have hE_meas : AEStronglyMeasurable E volume := by
    rw [hE_def]
    exact (convKernel_envelope_integrable pX (gaussGradMaj t) hpX_int hpX_meas
      (gaussGradMaj_integrable ht) hg_meas).aestronglyMeasurable
  -- a.e.-strong-measurability of the target `(- log p_t - 1)·∂p_t`.
  have hpath_meas : Measurable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) := by
    have hg_pdf : Measurable (gaussianPDFReal 0 ⟨t, ht.le⟩) := measurable_gaussianPDFReal 0 _
    have huncurry : StronglyMeasurable
        (Function.uncurry fun z x ↦ pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
      apply Measurable.stronglyMeasurable
      apply (hpX_meas.comp measurable_snd).mul
      exact hg_pdf.comp ((measurable_fst).sub measurable_snd)
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [convDensityAdd] using h.measurable
  have htarget_meas : AEStronglyMeasurable
      (fun x ↦ (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) volume := by
    have hlog_meas : Measurable
        (fun x ↦ - Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1) :=
      ((Real.measurable_log.comp hpath_meas).neg).sub_const 1
    exact (hlog_meas.mul (measurable_deriv _)).aestronglyMeasurable
  -- pointwise domination `‖(- log p_t - 1)·∂p_t‖ ≤ H x`.
  refine Integrable.mono' hH_int htarget_meas ?_
  filter_upwards [hLog] with x hLogx
  -- `‖-log p_t - 1‖ ≤ A + B·x²` (majorant at `s = t`) and `‖∂p_t x‖ ≤ E x`.
  have hlog_x : ‖- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1‖
      ≤ A + B * x ^ 2 := hLogx t htmem
  have hderiv_x : ‖deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x‖ ≤ E x := by
    rw [hE_def]
    exact convDensityAdd_deriv1_le_gaussGradMaj_conv pX hpX_nn hpX_meas hpX_int ht x htmem
  have hABnn : (0:ℝ) ≤ A + B * x ^ 2 := le_trans (norm_nonneg _) hlog_x
  have hE_nn : (0:ℝ) ≤ E x := by
    rw [hE_def]; exact integral_nonneg (fun y ↦ mul_nonneg (hpX_nn y) (hg_nn (x - y)))
  -- `‖(- log p_t - 1)·∂p_t‖ ≤ (A + B·x²)·E x`.
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1| ≤ A + B * x ^ 2 :=
    by rwa [← Real.norm_eq_abs]
  have h2 : |deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x| ≤ E x := by
    rwa [← Real.norm_eq_abs]
  have hstep1 : |- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1|
        * |deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x|
      ≤ (A + B * x ^ 2) * E x :=
    mul_le_mul h1 h2 (abs_nonneg _) hABnn
  refine le_trans hstep1 ?_
  -- `(A+B·x²)·E x = ∫ (A+Bx²)·pX y·gaussGradMaj t (x-y) ≤ H x` via `x² ≤ 2(x−y)²+2y²`.
  have hpull : (A + B * x ^ 2) * E x
      = ∫ y, (A + B * x ^ 2) * (pX y * gaussGradMaj t (x - y)) ∂volume := by
    rw [hE_def, ← integral_const_mul]
  rw [hpull]
  -- per-`y` fibre integrabilities of the dominating pieces.
  have hEnv_pos_int : Integrable (fun y ↦ pX y * gaussGradMaj t (x - y)) volume := by
    refine hpX_int.mul_bdd (c := Cg) ?_ ?_
    · exact (hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]; exact hCg (x - y)
  have hfib1_int : Integrable (fun y ↦ pX y * G (x - y)) volume := by
    refine hpX_int.mul_bdd (c := CG) ?_ ?_
    · exact (hG_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hG_nn (x - y))]; exact hCG (x - y)
  have hfib2_int : Integrable (fun y ↦ (y ^ 2 * pX y) * gaussGradMaj t (x - y)) volume := by
    refine hmomPX_int.mul_bdd (c := Cg) ?_ ?_
    · exact (hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]; exact hCg (x - y)
  have hlhs_int : Integrable
      (fun y ↦ (A + B * x ^ 2) * (pX y * gaussGradMaj t (x - y))) volume :=
    hEnv_pos_int.const_mul _
  have hdom_int : Integrable
      (fun y ↦ pX y * G (x - y) + 2 * |B| * ((y ^ 2 * pX y) * gaussGradMaj t (x - y))) volume :=
    hfib1_int.add (hfib2_int.const_mul _)
  have hH_eq : (∫ y, pX y * G (x - y) ∂volume)
        + 2 * |B| * (∫ y, (y ^ 2 * pX y) * gaussGradMaj t (x - y) ∂volume)
      = ∫ y, (pX y * G (x - y)
          + 2 * |B| * ((y ^ 2 * pX y) * gaussGradMaj t (x - y))) ∂volume := by
    rw [integral_add hfib1_int (hfib2_int.const_mul _), integral_const_mul]
  rw [hH_eq]
  refine integral_mono hlhs_int hdom_int (fun y ↦ ?_)
  have hpXg_nn : (0:ℝ) ≤ pX y * gaussGradMaj t (x - y) :=
    mul_nonneg (hpX_nn y) (hg_nn (x - y))
  have hx2 : x ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * y ^ 2 := by
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg x]
  -- `A + B·x² ≤ |A| + 2|B|(x−y)² + 2|B|y²` (using `A ≤ |A|`, `B·x² ≤ |B|x² ≤ |B|(2(x-y)²+2y²)`).
  have hcoef : A + B * x ^ 2 ≤ (|A| + 2 * |B| * (x - y) ^ 2) + 2 * |B| * y ^ 2 := by
    have hBabs : (0:ℝ) ≤ |B| := abs_nonneg B
    have hAabs : A ≤ |A| := le_abs_self A
    have hBx : B * x ^ 2 ≤ |B| * x ^ 2 := by
      apply mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg x)
    nlinarith [mul_le_mul_of_nonneg_left hx2 hBabs, hAabs, hBx]
  have hGval : G (x - y) = (|A| + 2 * |B| * (x - y) ^ 2) * gaussGradMaj t (x - y) := by
    rw [hG_def]
  calc (A + B * x ^ 2) * (pX y * gaussGradMaj t (x - y))
      ≤ ((|A| + 2 * |B| * (x - y) ^ 2) + 2 * |B| * y ^ 2) * (pX y * gaussGradMaj t (x - y)) :=
        mul_le_mul_of_nonneg_right hcoef hpXg_nn
    _ = (|A| + 2 * |B| * (x - y) ^ 2) * gaussGradMaj t (x - y) * pX y
          + 2 * |B| * ((y ^ 2 * pX y) * gaussGradMaj t (x - y)) := by ring
    _ = pX y * G (x - y) + 2 * |B| * ((y ^ 2 * pX y) * gaussGradMaj t (x - y)) := by
        rw [hGval]; ring

private theorem convDensityAdd_sq_mul_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t)
    {p_t g : ℝ → ℝ} (hp_t : p_t = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
    (hg_def : g = gaussianPDFReal 0 ⟨t, ht.le⟩) (hp_nn : ∀ x, 0 ≤ p_t x)
    (hg_nn : ∀ u, (0:ℝ) ≤ g u) (hg_meas : Measurable g)
    (hg2_meas : Measurable (fun u ↦ u ^ 2 * g u)) {Pg : ℝ}
    (hg_le : ∀ u, g u ≤ Pg) (hg2_le : ∀ u, u ^ 2 * g u ≤ Pg * (2 * t * Real.exp (-1)))
    (hEnv1_int :
      Integrable (fun x ↦ ∫ y, pX y * (fun u ↦ u ^ 2 * g u) (x - y) ∂volume) volume)
    (hEnv2_int : Integrable (fun x ↦ ∫ y, (y ^ 2 * pX y) * g (x - y) ∂volume) volume) :
    Integrable (fun x ↦ x ^ 2 * p_t x) volume := by
  have hmomPX_int : Integrable (fun y ↦ y ^ 2 * pX y) volume := hpX_mom
  -- dominating function `Hx = 2·∫ pX y·(x-y)²g(x-y) + 2·∫(y²pX)·g(x-y)`.
  have hH_int : Integrable (fun x ↦
      2 * (∫ y, pX y * (fun u ↦ u ^ 2 * g u) (x - y) ∂volume)
      + 2 * (∫ y, (y ^ 2 * pX y) * g (x - y) ∂volume)) volume :=
    (hEnv1_int.const_mul 2).add (hEnv2_int.const_mul 2)
  -- measurability of `x²·p_t`.
  have htarget_meas : AEStronglyMeasurable (fun x ↦ x ^ 2 * p_t x) volume := by
    have hpt_meas : Measurable p_t := by
      rw [hp_t]
      have huncurry : StronglyMeasurable
          (Function.uncurry fun z x ↦ pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
        apply Measurable.stronglyMeasurable
        apply (hpX_meas.comp measurable_snd).mul
        exact (measurable_gaussianPDFReal 0 _).comp ((measurable_fst).sub measurable_snd)
      have h := huncurry.integral_prod_right (ν := volume)
      simpa only [convDensityAdd] using h.measurable
    exact ((by fun_prop : Measurable (fun x : ℝ ↦ x ^ 2)).mul hpt_meas).aestronglyMeasurable
  refine Integrable.mono' hH_int htarget_meas ?_
  filter_upwards with x
  -- `‖x²·p_t x‖ = x²·p_t x = ∫ x²·pX y·g(x-y)`.
  have hx2_pull : x ^ 2 * p_t x = ∫ y, x ^ 2 * (pX y * g (x - y)) ∂volume := by
    rw [hp_t, hg_def]
    show x ^ 2 * (∫ y, pX y * gaussianPDFReal 0 ⟨t, ht.le⟩ (x - y) ∂volume)
      = ∫ y, x ^ 2 * (pX y * gaussianPDFReal 0 ⟨t, ht.le⟩ (x - y)) ∂volume
    rw [← integral_const_mul]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg x) (hp_nn x) : (0:ℝ) ≤ x ^ 2 * p_t x), hx2_pull]
  -- per-`y` fibre integrabilities.
  have hfib1_int : Integrable (fun y ↦ pX y * (fun u ↦ u ^ 2 * g u) (x - y)) volume := by
    refine hpX_int.mul_bdd (c := Pg * (2 * t * Real.exp (-1))) ?_ ?_
    · exact (hg2_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y ↦ ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hg_nn (x - y))
        : (0:ℝ) ≤ (x - y) ^ 2 * g (x - y))]
      exact hg2_le (x - y)
  have hfib2_int : Integrable (fun y ↦ (y ^ 2 * pX y) * g (x - y)) volume := by
    refine hmomPX_int.mul_bdd (c := Pg) ?_ ?_
    · exact (hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]; exact hg_le (x - y))
  have hlhs_int : Integrable (fun y ↦ x ^ 2 * (pX y * g (x - y))) volume := by
    have hfibE_int : Integrable (fun y ↦ pX y * g (x - y)) volume := by
      refine hpX_int.mul_bdd (c := Pg) ?_ ?_
      · exact (hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]; exact hg_le (x - y))
    exact hfibE_int.const_mul _
  have hdom_int : Integrable
      (fun y ↦ 2 * (pX y * (fun u ↦ u ^ 2 * g u) (x - y))
        + 2 * ((y ^ 2 * pX y) * g (x - y))) volume :=
    (hfib1_int.const_mul 2).add (hfib2_int.const_mul 2)
  have hH_eq : 2 * (∫ y, pX y * (fun u ↦ u ^ 2 * g u) (x - y) ∂volume)
        + 2 * (∫ y, (y ^ 2 * pX y) * g (x - y) ∂volume)
      = ∫ y, (2 * (pX y * (fun u ↦ u ^ 2 * g u) (x - y))
          + 2 * ((y ^ 2 * pX y) * g (x - y))) ∂volume := by
    rw [integral_add (hfib1_int.const_mul 2) (hfib2_int.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [hH_eq]
  -- pointwise: `x²·pX y·g(x-y) ≤ 2·pX y·(x-y)²g + 2·(y²pX)·g` via `x² ≤ 2(x-y)²+2y²`.
  refine integral_mono hlhs_int hdom_int (fun y ↦ ?_)
  have hpXg_nn : (0:ℝ) ≤ pX y * g (x - y) := mul_nonneg (hpX_nn y) (hg_nn (x - y))
  have hx2 : x ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * y ^ 2 := by
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg x]
  simp only []
  calc x ^ 2 * (pX y * g (x - y))
      ≤ (2 * (x - y) ^ 2 + 2 * y ^ 2) * (pX y * g (x - y)) :=
        mul_le_mul_of_nonneg_right hx2 hpXg_nn
    _ = 2 * (pX y * ((x - y) ^ 2 * g (x - y))) + 2 * ((y ^ 2 * pX y) * g (x - y)) := by ring

/-- `Integrable (negMulLog p_t)` for `p_t = convDensityAdd pX g_t`, `t > 0`, so the entropy
`h(X + √t · Z) = -∫ negMulLog p_t` is finite. Closes from the log-factor polynomial majorant
(`‖negMulLog p_t‖ = p_t · |log p_t| ≤ p_t · (A + 1 + B·x²)`) and `Integrable (x² · p_t)`.

@audit:ok -/
theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume := by
  classical
  have htmem : t ∈ Set.Ioo (t/2) (2*t) := ⟨by linarith, by linarith⟩
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_t
  have hpX_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  have hp_pos : ∀ x, 0 < p_t x := fun x ↦
    convDensityAdd_pos pX hpX_nn hpX_int hpX_pos ht x
  have hp_nn : ∀ x, 0 ≤ p_t x := fun x ↦ (hp_pos x).le
  -- log-factor polynomial majorant: `|−log p_t − 1| ≤ A + B·x²`.
  obtain ⟨A, B, hB_nn, hLog⟩ :=
    convDensityAdd_logFactor_poly_majorant pX hpX_nn hpX_meas hpX_int hpX_mass ht
  -- the Gaussian kernel `g_t` and the moment kernel `u²·g_t`, both integrable.
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  have hcoe : ((⟨t, ht.le⟩ : ℝ≥0) : ℝ) = t := rfl
  have hg_meas : Measurable g := by rw [hg_def]; exact measurable_gaussianPDFReal 0 _
  have hg_nn : ∀ u, (0:ℝ) ≤ g u := fun u ↦ by rw [hg_def]; exact gaussianPDFReal_nonneg 0 _ _
  have hg_int : Integrable g volume := by rw [hg_def]; exact integrable_gaussianPDFReal 0 _
  -- `Integrable (fun u => u²·g u)` (Gaussian 2nd moment).
  -- pointwise unfold of `g` (used by the moment-kernel integrability + bound).
  have hg_unfold : ∀ u, g u = (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (2 * t)) :=
    fun u ↦ by
      rw [hg_def]
      show (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹ * Real.exp (-(u - 0) ^ 2 / (2 * t))
        = (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (2 * t))
      rw [sub_zero]
  have hg2_int : Integrable (fun u ↦ u ^ 2 * g u) volume := by
    have hb : (0:ℝ) < 1 / (2 * t) := by positivity
    have hsq : Integrable (fun u : ℝ ↦ u ^ 2 * Real.exp (-(1 / (2 * t)) * u ^ 2)) volume := by
      have := integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)
      refine this.congr (Filter.Eventually.of_forall (fun u ↦ ?_))
      simp only [Real.rpow_two]
    have hcomb : Integrable
        (fun u : ℝ ↦ (Real.sqrt (2 * Real.pi * t))⁻¹
          * (u ^ 2 * Real.exp (-(1 / (2 * t)) * u ^ 2))) volume :=
      hsq.const_mul _
    refine hcomb.congr (Filter.Eventually.of_forall (fun u ↦ ?_))
    simp only [hg_unfold u]
    rw [show (-u ^ 2 / (2 * t) : ℝ) = -(1 / (2 * t)) * u ^ 2 by field_simp]
    ring
  have hg2_meas : Measurable (fun u ↦ u ^ 2 * g u) := by fun_prop
  -- `Integrable p_t`.
  have hpt_int : Integrable p_t volume := by
    rw [hp_t, hg_def]
    have := convKernel_envelope_integrable pX (gaussianPDFReal 0 ⟨t, ht.le⟩)
      hpX_int hpX_meas (integrable_gaussianPDFReal 0 _) (measurable_gaussianPDFReal 0 _)
    exact this
  -- `Integrable (fun x => x²·p_t x)` via `x² ≤ 2(x−y)²+2y²` split into two conv envelopes.
  have hmomPX_int : Integrable (fun y ↦ y ^ 2 * pX y) volume := hpX_mom
  have hmomPX_meas : Measurable (fun y ↦ y ^ 2 * pX y) := by fun_prop
  have hEnv1_int :
      Integrable (fun x ↦ ∫ y, pX y * (fun u ↦ u ^ 2 * g u) (x - y) ∂volume) volume :=
    convKernel_envelope_integrable pX (fun u ↦ u ^ 2 * g u) hpX_int hpX_meas hg2_int hg2_meas
  have hEnv2_int : Integrable (fun x ↦ ∫ y, (y ^ 2 * pX y) * g (x - y) ∂volume) volume :=
    convKernel_envelope_integrable (fun y ↦ y ^ 2 * pX y) g hmomPX_int hmomPX_meas hg_int hg_meas
  -- global sup of `g` (Gaussian prefactor) for fibre integrabilities.
  set Pg : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ with hPg
  have hPg_nn : (0:ℝ) ≤ Pg := by rw [hPg]; positivity
  have hg_le : ∀ u, g u ≤ Pg := fun u ↦ by
    rw [hg_def, hPg]
    exact gaussianPDFReal_le_prefactor' ⟨t, ht.le⟩ u
  -- global bound of the moment kernel `u²·g(u) ≤ Pg·2t·e⁻¹`.
  have hg2_le : ∀ u, u ^ 2 * g u ≤ Pg * (2 * t * Real.exp (-1)) := fun u ↦ by
    rw [hg_unfold u, hPg]
    have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * t))
    have hexp_eq : Real.exp (-(u ^ 2 / (2 * t))) = Real.exp (-u ^ 2 / (2 * t)) := by congr 1; ring
    rw [hexp_eq] at hmul
    have h2t : (0:ℝ) < 2 * t := by linarith
    have hmul' := mul_le_mul_of_nonneg_left hmul h2t.le
    have heq : (2 * t) * ((u ^ 2 / (2 * t)) * Real.exp (-u ^ 2 / (2 * t)))
        = u ^ 2 * Real.exp (-u ^ 2 / (2 * t)) := by field_simp
    rw [heq] at hmul'
    calc u ^ 2 * (Pg * Real.exp (-u ^ 2 / (2 * t)))
        = Pg * (u ^ 2 * Real.exp (-u ^ 2 / (2 * t))) := by ring
      _ ≤ Pg * (2 * t * Real.exp (-1)) := mul_le_mul_of_nonneg_left hmul' hPg_nn
  have hx2p_int : Integrable (fun x ↦ x ^ 2 * p_t x) volume :=
    convDensityAdd_sq_mul_integrable pX hpX_nn hpX_meas hpX_int hpX_mom ht hp_t hg_def
      hp_nn hg_nn hg_meas hg2_meas hg_le hg2_le hEnv1_int hEnv2_int
  -- ============ assemble A from the two integrabilities + the majorant. ============
  -- dominating function `D x = (A+1)·p_t x + B·(x²·p_t x)`, integrable.
  have hD_int : Integrable (fun x ↦ (A + 1) * p_t x + B * (x ^ 2 * p_t x)) volume :=
    (hpt_int.const_mul _).add (hx2p_int.const_mul _)
  have hnegMulLog_meas : AEStronglyMeasurable
      (fun x ↦ Real.negMulLog (p_t x)) volume := by
    have hpt_meas : Measurable p_t := by
      rw [hp_t]
      have huncurry : StronglyMeasurable
          (Function.uncurry fun z x ↦ pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
        apply Measurable.stronglyMeasurable
        apply (hpX_meas.comp measurable_snd).mul
        exact (measurable_gaussianPDFReal 0 _).comp ((measurable_fst).sub measurable_snd)
      have h := huncurry.integral_prod_right (ν := volume)
      simpa only [convDensityAdd] using h.measurable
    exact (Real.continuous_negMulLog.measurable.comp hpt_meas).aestronglyMeasurable
  refine Integrable.mono' hD_int hnegMulLog_meas ?_
  filter_upwards [hLog] with x hLogx
  -- `‖negMulLog p_t‖ = p_t·|log p_t| ≤ p_t·(A+1+B·x²)`.
  have hlog_x : |- Real.log (p_t x) - 1| ≤ A + B * x ^ 2 := by
    have := hLogx t htmem
    rwa [hp_t, ← Real.norm_eq_abs]
  -- `|log p_t| ≤ |−log p_t − 1| + 1 ≤ A + 1 + B·x²`.
  have hlog_abs : |Real.log (p_t x)| ≤ A + 1 + B * x ^ 2 := by
    set w : ℝ := - Real.log (p_t x) - 1 with hw
    have hlogw : Real.log (p_t x) = -(w + 1) := by rw [hw]; ring
    have htri : |Real.log (p_t x)| ≤ |w| + 1 := by
      rw [hlogw, abs_neg]
      have h1 : |(1:ℝ)| = 1 := abs_one
      calc |w + 1| ≤ |w| + |(1:ℝ)| := abs_add_le _ _
        _ = |w| + 1 := by rw [h1]
    linarith [hlog_x, htri]
  rw [Real.norm_eq_abs, Real.negMulLog, neg_mul, abs_neg, abs_mul,
    abs_of_nonneg (hp_nn x)]
  calc p_t x * |Real.log (p_t x)|
      ≤ p_t x * (A + 1 + B * x ^ 2) := mul_le_mul_of_nonneg_left hlog_abs (hp_nn x)
    _ = (A + 1) * p_t x + B * (x ^ 2 * p_t x) := by ring

end InformationTheory.Shannon.FisherInfo
