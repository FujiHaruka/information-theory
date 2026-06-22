import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijnPerTime
import InformationTheory.Shannon.FisherConvBound
import InformationTheory.Shannon.EPI.Conv.DensitySecondDeriv
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Core
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Domination
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly.Derivatives

namespace InformationTheory.Shannon.FisherInfo

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-- The de Bruijn integration-by-parts identity at fixed time `t`:
`∫ (- log p_t - 1) · ∂²_x p_t = ∫ (logDeriv p_t)² · p_t`, where `p_t = convDensityAdd pX g_t`.
Applies `debruijn_ibp_step` with the IBP quadruple `u = -log p_t - 1`, `v = ∂_x p_t`,
`u' = -logDeriv p_t`, `v' = ∂²_x p_t`, drawing differentiability from the deriv-existence helpers
and the three integrability preconditions from the entropy- and Fisher-integrability lemmas.

@audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x ∂volume
      = ∫ x, (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2
        * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume := by
  -- abbreviate the time-`t` convolution density.
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_t
  -- STEP 2: strict positivity of `p_t` (genuine; `0 < ∫ pX = 1` from `hpX_mass`).
  have hp_pos : ∀ x, 0 < p_t x := fun x ↦
    convDensityAdd_pos pX hpX_nn hpX_int (by rw [hpX_mass]; norm_num) ht x
  -- IBP quadruple: u, v, u', v'.
  set u : ℝ → ℝ := fun x ↦ - Real.log (p_t x) - 1 with hu_def
  set v : ℝ → ℝ := deriv p_t with hv_def
  set u' : ℝ → ℝ := fun x ↦ - logDeriv p_t x with hu'_def
  set v' : ℝ → ℝ := deriv (deriv p_t) with hv'_def
  -- STEP 3: `hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x` — proved for all `x`.
  have hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x := by
    intro x _
    -- `HasDerivAt p_t (deriv p_t x) x` from the differentiability helper.
    have hpt_diff : HasDerivAt p_t (deriv p_t x) x :=
      convDensityAdd_hasDerivAt_self pX hpX_nn hpX_meas hpX_int ht x
    -- `HasDerivAt (log ∘ p_t) (deriv p_t x / p_t x) x` via `Real.hasDerivAt_log`.
    have hlog : HasDerivAt (fun x ↦ Real.log (p_t x)) (deriv p_t x / p_t x) x := by
      have := (Real.hasDerivAt_log (hp_pos x).ne').comp x hpt_diff
      simpa [one_div, div_eq_mul_inv, mul_comm] using this
    -- `u x = - log (p_t x) - 1`, `u' x = - logDeriv p_t x = - (deriv p_t x / p_t x)`.
    have : HasDerivAt u (-(deriv p_t x / p_t x)) x := by
      simpa [hu_def] using (hlog.neg.sub_const 1)
    have hu'_eq : u' x = -(deriv p_t x / p_t x) := by
      rw [hu'_def]; simp [logDeriv]
    rw [hu'_eq]; exact this
  -- STEP 3': `hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x` — proved for all `x`.
  have hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x := by
    intro x _
    rw [hv_def, hv'_def]
    exact convDensityAdd_deriv_hasDerivAt_self pX hpX_nn hpX_meas hpX_int ht x
  -- STEP 4: the three integrability preconditions.
  -- `huv' = Integrable (u * v')`: entropy-finiteness wall.
  have huv' : Integrable (u * v') := by
    simpa only [Pi.mul_def, hu_def, hv'_def, hp_t] using
      convDensityAdd_logFactor_deriv2_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  -- `huv = Integrable (u * v)`: entropy-finiteness wall.
  have huv : Integrable (u * v) := by
    simpa only [Pi.mul_def, hu_def, hv_def, hp_t] using
      convDensityAdd_logFactor_deriv_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
  -- `hu'v = Integrable (u' * v)`: from the Fisher-finiteness wall (`(logDeriv)²·p_t`),
  --   since `u' x · v x = - logDeriv p_t x · deriv p_t x = -((logDeriv p_t x)²·p_t x)`.
  have hfisher := convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int hpX_mass ht
  -- pointwise identity `u' x · v x = -((logDeriv p_t x)² · p_t x)`, derived once.
  have hpt_pointwise : ∀ x, (u' * v) x
      = -(logDeriv p_t x ^ 2 * p_t x) := by
    intro x
    have hpx := (hp_pos x).ne'
    simp only [Pi.mul_apply, hu'_def, hv_def, logDeriv, Pi.div_apply]
    field_simp
  have hu'v : Integrable (u' * v) := by
    refine (hfisher.neg).congr ?_
    filter_upwards with x
    rw [Pi.neg_apply, hpt_pointwise x]
  -- STEP 5: apply the IBP atom and reconcile.
  have hibp := debruijn_ibp_step u v u' v' hu hv huv' hu'v huv
  -- LHS of the goal = `∫ u x * v' x`; RHS of `hibp` = `- ∫ u' x * v x`.
  rw [show (∫ x, (- Real.log (p_t x) - 1) * deriv (deriv p_t) x ∂volume)
        = ∫ x, u x * v' x ∂volume from rfl, hibp]
  -- `- ∫ u' x * v x = ∫ (logDeriv p_t x)² * p_t x`.
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [show u' x * v x = (u' * v) x from rfl, hpt_pointwise x, neg_neg]

/-- The integrated entropy-derivative equals half the Fisher info of `pPath t`. de Bruijn IBP
moves the spatial second-derivative factor onto `(- log p - 1)`, yielding
`∫ (∂_x p)²/p = ∫ (logDeriv p)² · p`, which `fisher_from_logDeriv` identifies with
`fisherInfoOfDensityReal`. Here `hentDeriv` pins `entDeriv` to the per-`x` closed form.

@audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain_ibp_fisher
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t)
    (entDeriv : ℝ → ℝ)
    (hentDeriv : ∀ᵐ x ∂volume, entDeriv x =
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x)) :
    ∫ x, entDeriv x ∂volume
      = (1/2) * fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) := by
  -- abbreviate the time-`t` convolution density.
  set p_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_t
  -- `p_t ≥ 0` (convolution of nonneg pX with nonneg Gaussian PDF).
  have hp_nn : ∀ x, 0 ≤ p_t x := by
    intro x
    rw [hp_t]
    exact integral_nonneg fun y ↦ mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- (1) rewrite `∫ entDeriv` to `∫ (1/2)·((- log p_t - 1)·∂²_x p_t)` via the a.e. pin
  --     `hentDeriv` (and `ring` to move the `(1/2)` to the front).
  have hstep1 : ∫ x, entDeriv x ∂volume
      = ∫ x, (1/2) * ((- Real.log (p_t x) - 1) * deriv (deriv p_t) x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hentDeriv] with x hx
    rw [hx]; ring
  -- (2) pull out the `(1/2)` constant.
  rw [hstep1, integral_const_mul]
  -- (3) IBP step wall: `∫ (- log p_t - 1)·∂²_x p_t = ∫ (logDeriv p_t)²·p_t`.
  rw [debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step pX hpX_nn hpX_meas hpX_int
        hpX_mass hpX_mom ht]
  -- (4) Fisher value: `∫ (logDeriv p_t)²·p_t = fisherInfoOfDensityReal p_t`,
  --     integrability supplied by the Fisher-finiteness wall.
  rw [fisher_from_logDeriv p_t hp_nn
    (convDensityAdd_fisher_integrable pX hpX_nn hpX_meas hpX_int hpX_mass ht)]

-- Helper: the σ-derivative of `pPath σ x` at `s`, given the heat-equation domination conditions.
-- Packages the 112-line `heatFlow_density_heat_equation` application into a named lemma so that
-- the main `_chain_hdiff` body stays under 150 lines.
private theorem debruijnIdentityV2_chain_hdiff_pathDeriv
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (pPath : ℝ → ℝ → ℝ)
    (pathDeriv1 : ℝ → ℝ → ℝ)
    (pathDeriv2 : ℝ → ℝ → ℝ)
    (hpPath_pos : ∀ (σ : ℝ) (hσ : 0 < σ),
        pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))
    (hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ ↦ pPath σ ξ) (pathDeriv1 σ y) y)
    (hpathDeriv2 : ∀ σ y : ℝ,
        HasDerivAt (fun ξ ↦ pathDeriv1 σ ξ) (pathDeriv2 σ y) y)
    (x : ℝ) (s : ℝ) (hspos : 0 < s)
    (hker_meas : Measurable (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel s u))
    (hker_le : ∀ v : ℝ,
        |heatFlow_density_heat_equation_kernel s v|
          ≤ (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹)
    (Mξ1 : ℝ) (hMξ1 : Mξ1 =
        (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)))
    (Mξ2 : ℝ) (hMξ2 : Mξ2 =
        (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s)) :
    HasDerivAt (fun σ ↦ pPath σ x) ((1/2) * pathDeriv2 s x) s := by
  refine heatFlow_density_heat_equation pX pPath pathDeriv1 pathDeriv2
    hpPath_pos hpathDeriv1 hpathDeriv2 hspos x
    ?boundσ ?hboundσ_int ?hFσ_meas ?hFσ_int ?hFσ'_meas ?hbσ
    ?boundξ1 ?hboundξ1_int ?hFξ1_meas ?hFξ1_int ?hFξ1'_meas ?hbξ1
    ?boundξ2 ?hboundξ2_int ?hFξ2_int ?hFξ2'_meas ?hbξ2
  case boundσ => exact fun y ↦ pX y * gaussHessMaj s (x - y)
  case hboundσ_int =>
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (Real.pi * s))⁻¹ * (16 * Real.exp (-1) / s + 2 / s)) ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      have hM : Measurable (gaussHessMaj s) := by unfold gaussHessMaj; fun_prop
      exact hM.comp (measurable_const.sub measurable_id)
    · refine Filter.Eventually.of_forall (fun y ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussHessMaj_nonneg hspos (x - y))]
      exact gaussHessMaj_bdd hspos (x - y)
  case hFσ_meas =>
    refine Filter.Eventually.of_forall (fun σ ↦ ?_)
    exact (hpX_meas.aestronglyMeasurable).mul
      (((show Measurable (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel σ u) by
          unfold heatFlow_density_heat_equation_kernel; fun_prop).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable)
  case hFσ_int =>
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs]; exact hker_le (x - y))
  case hFσ'_meas =>
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.const_mul ?_ _
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
        measurable_const |>.aestronglyMeasurable
  case hbσ =>
    refine Filter.Eventually.of_forall (fun y σ hσ ↦ ?_)
    have hσpos : (0:ℝ) < σ := by have := hσ.1; linarith
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hpX_nn y)]
    apply mul_le_mul_of_nonneg_left _ (hpX_nn y)
    rw [heatFlow_density_heat_equation_kernel_eq hσpos (x - y)]
    have hmaj := gaussianHess_le_gaussHessMaj hspos hσ (x - y)
    have hg_nn : 0 ≤ gaussianPDFReal 0
        ⟨σ, le_of_lt (by have := hσ.1; linarith : (0:ℝ) < σ)⟩ (x - y) :=
      gaussianPDFReal_nonneg 0 _ _
    have hgM_nn : 0 ≤ gaussHessMaj s (x - y) := gaussHessMaj_nonneg hspos (x - y)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have habs : |gaussianPDFReal 0 ⟨σ, hσpos.le⟩ (x - y) * ((x - y) ^ 2 / σ ^ 2 - 1 / σ)|
        = gaussianPDFReal 0 ⟨σ, hσpos.le⟩ (x - y) * |(x - y) ^ 2 / σ ^ 2 - 1 / σ| := by
      rw [abs_mul, abs_of_nonneg hg_nn]
    rw [habs]
    calc 1 / 2 * (gaussianPDFReal 0 ⟨σ, hσpos.le⟩ (x - y) * |(x - y) ^ 2 / σ ^ 2 - 1 / σ|)
        ≤ 1 / 2 * gaussHessMaj s (x - y) := by
          apply mul_le_mul_of_nonneg_left hmaj (by norm_num)
      _ ≤ gaussHessMaj s (x - y) := by linarith [hgM_nn]
  case boundξ1 => exact fun y ↦ |pX y| * Mξ1
  case hboundξ1_int => exact hpX_int.abs.mul_const _
  case hFξ1_meas =>
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  case hFξ1_int =>
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  case hFξ1'_meas =>
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
  case hbξ1 =>
    refine Filter.Eventually.of_forall (fun y ξ _ ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound hspos (ξ - y)
    rwa [hMξ1]
  case boundξ2 => exact fun y ↦ |pX y| * Mξ2
  case hboundξ2_int => exact hpX_int.abs.mul_const _
  case hFξ2_int =>
    have hbound_int : Integrable (fun y ↦ |pX y| * Mξ1) volume := hpX_int.abs.mul_const _
    refine hbound_int.mono' ?_ (Filter.Eventually.of_forall (fun y ↦ ?_))
    · refine (hpX_meas.aestronglyMeasurable).mul ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := kernel_x_deriv1_global_bound hspos (x - y)
      rwa [hMξ1]
  case hFξ2'_meas =>
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
        measurable_const |>.aestronglyMeasurable
  case hbξ2 =>
    refine Filter.Eventually.of_forall (fun y ξ _ ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv2_global_bound hspos (ξ - y)
    rwa [hMξ2]

/-- The per-`x`, per-`s ∈ Ioo (t/2) (2*t)` chain-rule derivative of the entropy integrand
`fun s => negMulLog (pPath s x)`, with value the closed form
`(- log (pPath s x) - 1) · ((1/2) · ∂²_x pPath_s x)`, where
`pPath s x = convDensityAdd pX g_{max s 0} x`. This is the `hdiff` precondition of the
parametric-diff atom `entropy_hasDerivAt_via_parametric`. The derivation composes
`_chain_entDeriv_formula` with the σ-derivative from `heatFlow_density_heat_equation`, whose
domination hypotheses come from the Gaussian-Hessian majorant and the global kernel bounds.

@audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain_hdiff
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (_hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioo (t/2) (2*t),
      HasDerivAt
        (fun s ↦ Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x))
        ((- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) - 1)
          * ((1/2) * deriv (deriv (convDensityAdd pX
              (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩))) x)) s := by
  classical
  -- positive mass from `∫ pX = 1` (for `convDensityAdd_pos`).
  have hpX_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  -- the heat-flow path and its two spatial derivatives, in `max σ 0` form.
  set pPath : ℝ → ℝ → ℝ :=
    fun σ ↦ convDensityAdd pX (gaussianPDFReal 0 ⟨max σ 0, le_max_right σ 0⟩) with hpPath_def
  set pathDeriv1 : ℝ → ℝ → ℝ := fun σ y ↦ deriv (pPath σ) y with hpathDeriv1_def
  set pathDeriv2 : ℝ → ℝ → ℝ := fun σ y ↦ deriv (deriv (pPath σ)) y with hpathDeriv2_def
  -- definitional pin: on `σ > 0`, `max σ 0 = σ`, so `pPath σ = convDensityAdd pX g_σ`.
  have hpPath_pos : ∀ (σ : ℝ) (hσ : 0 < σ),
      pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩) := by
    intro σ hσ
    show convDensityAdd pX (gaussianPDFReal 0 ⟨max σ 0, le_max_right σ 0⟩)
      = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩)
    have : (⟨max σ 0, le_max_right σ 0⟩ : ℝ≥0) = ⟨σ, hσ.le⟩ := by
      apply NNReal.eq; exact max_eq_left hσ.le
    rw [this]
  -- definitional pin (degenerate σ ≤ 0): `pPath σ = 0` (const).
  have hpPath_nonpos : ∀ (σ : ℝ), σ ≤ 0 → pPath σ = fun _ ↦ (0 : ℝ) := by
    intro σ hσ
    show convDensityAdd pX (gaussianPDFReal 0 ⟨max σ 0, le_max_right σ 0⟩)
      = fun _ ↦ (0 : ℝ)
    have hmax : (⟨max σ 0, le_max_right σ 0⟩ : ℝ≥0) = 0 := by
      apply NNReal.eq
      show max σ 0 = (0 : ℝ)
      exact max_eq_right hσ
    rw [hmax]
    funext z
    show (∫ y, pX y * gaussianPDFReal 0 0 (z - y) ∂volume) = 0
    have hzero : (fun y ↦ pX y * gaussianPDFReal 0 0 (z - y)) = fun _ ↦ (0 : ℝ) := by
      funext y; rw [gaussianPDFReal_zero_var]; simp
    rw [hzero, integral_zero]
  -- pin `hpathDeriv1`: spatial 1st derivative of `pPath σ`, for ALL σ.
  have hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ ↦ pPath σ ξ) (pathDeriv1 σ y) y := by
    intro σ y
    show HasDerivAt (fun ξ ↦ pPath σ ξ) (deriv (pPath σ) y) y
    rcases le_or_gt σ 0 with hσ | hσ
    · -- σ ≤ 0: `pPath σ` is the zero function; deriv is 0.
      rw [hpPath_nonpos σ hσ]
      simpa using hasDerivAt_const y (0 : ℝ)
    · -- σ > 0: use the deriv-existence helper.
      rw [hpPath_pos σ hσ]
      exact convDensityAdd_hasDerivAt_self pX hpX_nn hpX_meas hpX_int hσ y
  -- pin `hpathDeriv2`: spatial 2nd derivative of `pPath σ`, for ALL σ.
  have hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ ↦ pathDeriv1 σ ξ) (pathDeriv2 σ y) y := by
    intro σ y
    show HasDerivAt (fun ξ ↦ deriv (pPath σ) ξ) (deriv (deriv (pPath σ)) y) y
    rcases le_or_gt σ 0 with hσ | hσ
    · -- σ ≤ 0: `pPath σ = 0`, so `deriv (pPath σ) = 0` and the 2nd deriv is 0.
      have hd1 : deriv (pPath σ) = fun _ ↦ (0 : ℝ) := by
        funext ξ; rw [hpPath_nonpos σ hσ]; simp
      rw [hd1]
      simpa using hasDerivAt_const y (0 : ℝ)
    · -- σ > 0: differentiate `deriv (pPath σ) = deriv (convDensityAdd pX g_σ)`.
      have hfun : (fun ξ ↦ deriv (pPath σ) ξ)
          = deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩)) := by
        rw [hpPath_pos σ hσ]
      rw [hfun]
      have hval : deriv (deriv (pPath σ)) y
          = deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))) y := by
        rw [hpPath_pos σ hσ]
      rw [hval]
      exact convDensityAdd_deriv_hasDerivAt_self pX hpX_nn hpX_meas hpX_int hσ y
  -- the per-`x`, per-`s` derivative is now obtained by combining the heat-eq atom
  -- (σ-derivative) with the negMulLog chain rule.
  refine Filter.Eventually.of_forall (fun x s hs ↦ ?_)
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  -- kernel continuity / measurability (shared by the domination groups).
  have hker_cont : Continuous (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel s u) := by
    unfold heatFlow_density_heat_equation_kernel; fun_prop
  have hker_meas : Measurable (fun u : ℝ ↦ heatFlow_density_heat_equation_kernel s u) :=
    hker_cont.measurable
  -- the kernel uniform sup bound `|kernel s v| ≤ (√(2πs))⁻¹`.
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel s v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq hspos v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨s, hspos.le⟩ v
  -- spatial 1st/2nd-derivative global-bound constants.
  set Mξ1 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) with hMξ1
  set Mξ2 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s) with hMξ2
  -- (A) σ-derivative pin from `heatFlow_density_heat_equation` (delegated to helper).
  have hpath_deriv : HasDerivAt (fun σ ↦ pPath σ x) ((1/2) * pathDeriv2 s x) s :=
    debruijnIdentityV2_chain_hdiff_pathDeriv
      pX hpX_nn hpX_meas hpX_int
      pPath pathDeriv1 pathDeriv2
      hpPath_pos hpathDeriv1 hpathDeriv2
      x s hspos hker_meas hker_le
      Mξ1 hMξ1 Mξ2 hMξ2
  -- (B+C) chain rule: pin the `max s 0 = s` reconciliation then apply the chain rule.
  have hmaxs : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hspos.le⟩ := by
    apply NNReal.eq; exact max_eq_left hspos.le
  have hpos : convDensityAdd pX (gaussianPDFReal 0 ⟨s, hspos.le⟩) x ≠ 0 :=
    (convDensityAdd_pos pX hpX_nn hpX_int hpX_pos hspos x).ne'
  -- `hpath_deriv : HasDerivAt (fun σ => pPath σ x) D s`; since `pPath σ x = conv g_{max σ 0} x`
  -- definitionally, this is exactly the `hpath_deriv` shape the chain rule expects.
  have hchain := debruijnIdentityV2_holds_assembled_chain_entDeriv_formula
    pX hspos x ((1/2) * pathDeriv2 s x) hpos hpath_deriv
  -- `hchain` value: `(- log (conv g_{⟨s,_⟩} x) - 1) * ((1/2)·pathDeriv2 s x)`.
  -- goal value: `(- log (conv g_{max s 0} x) - 1) * ((1/2)·deriv(deriv(conv g_{max s 0})) x)`.
  -- the log factor: rewrite `⟨s,_⟩ → ⟨max s 0,_⟩` in hchain; `pathDeriv2 s x` is defeq to the
  -- goal's deriv-deriv form.
  rw [← hmaxs] at hchain
  exact hchain

/-- The entropy integral `∫ negMulLog (pPath s ·)` has its `s`-derivative at `t` given by the
integral of a per-`x` closed-form `entDeriv`, and that integral equals
`(1/2) · fisherInfoOfDensityReal (pPath t)`. Composes `entropy_hasDerivAt_via_parametric` (the
neighborhood version over `Set.Ioo (t/2) (2*t)`) with the per-`x` chain rule (`_chain_hdiff`), the
joint domination (`_chain_domination`), the entropy integrability
(`convDensityAdd_negMulLog_integrable`), and the Fisher value match (`_chain_ibp_fisher`).

@audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain_parametric
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ entDeriv : ℝ → ℝ,
      HasDerivAt
        (fun s ↦ ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume)
        (∫ x, entDeriv x ∂volume) t
      ∧ (∫ x, entDeriv x ∂volume
          = (1/2) *
              fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) := by
  -- the per-`x` closed form `entDerivFn s x`, as a 2-arg function for the atom.
  set entDerivFn : ℝ → ℝ → ℝ := fun s x ↦
    (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) - 1)
      * ((1/2) * deriv (deriv (convDensityAdd pX
          (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩))) x) with hentDerivFn
  -- the witness derivative is `entDerivFn t`.
  refine ⟨fun x ↦ entDerivFn t x, ?_, ?_⟩
  · -- ===== first goal: the HasDerivAt, via the parametric-diff atom. =====
    -- domination: an integrable `bound` dominating `entDerivFn s` on `Ioo (t/2)(2*t)`.
    obtain ⟨bound, hbound_int, hb_dom⟩ :=
      debruijnIdentityV2_holds_assembled_chain_domination
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
    -- `max t 0 = t` reconciliation of the variance witness at the base point.
    have hmaxt : (⟨max t 0, le_max_right t 0⟩ : ℝ≥0) = ⟨t, ht.le⟩ := by
      apply NNReal.eq; exact max_eq_left ht.le
    -- abbreviate the path.
    set pPath : ℝ → ℝ → ℝ := fun s x ↦
      convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x with hpPath
    -- `hint`: entropy-integrand integrability at `t` (entropy-finiteness wall), moved to
    --   the `pPath t = g_{max t 0}` form via `max t 0 = t`.
    have hint : Integrable (fun x ↦ Real.negMulLog (pPath t x)) volume := by
      have h := convDensityAdd_negMulLog_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
      refine h.congr ?_
      filter_upwards with x
      rw [hpPath]; simp only; rw [hmaxt]
    -- `hmeas`: a.e.-strong-measurability of the entropy integrand, for `s` near `t` (genuine).
    have hmeas : ∀ᶠ s in nhds t,
        AEStronglyMeasurable (fun x ↦ Real.negMulLog (pPath s x)) volume := by
      refine Filter.Eventually.of_forall (fun s ↦ ?_)
      -- `convDensityAdd pX g_{max s 0}` is measurable (joint-measurable integrand + Fubini).
      have hg_meas : Measurable (gaussianPDFReal 0 ⟨max s 0, le_max_right s 0⟩) :=
        measurable_gaussianPDFReal 0 _
      have hpath_meas : Measurable
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right s 0⟩)) := by
        have huncurry : StronglyMeasurable
            (Function.uncurry fun z x ↦
              pX x * gaussianPDFReal 0 ⟨max s 0, le_max_right s 0⟩ (z - x)) := by
          apply Measurable.stronglyMeasurable
          apply (hpX_meas.comp measurable_snd).mul
          exact hg_meas.comp ((measurable_fst).sub measurable_snd)
        have h := huncurry.integral_prod_right (ν := volume)
        simpa only [convDensityAdd] using h.measurable
      exact (Real.continuous_negMulLog.measurable.comp hpath_meas).aestronglyMeasurable
    -- `hderiv_meas`: a.e.-strong-measurability of `entDerivFn t` (genuine).
    have hderiv_meas : AEStronglyMeasurable (entDerivFn t) volume := by
      have hg_meas : Measurable (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩) :=
        measurable_gaussianPDFReal 0 _
      have hpath_meas : Measurable
          (convDensityAdd pX (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩)) := by
        have huncurry : StronglyMeasurable
            (Function.uncurry fun z x ↦
              pX x * gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩ (z - x)) := by
          apply Measurable.stronglyMeasurable
          apply (hpX_meas.comp measurable_snd).mul
          exact hg_meas.comp ((measurable_fst).sub measurable_snd)
        have h := huncurry.integral_prod_right (ν := volume)
        simpa only [convDensityAdd] using h.measurable
      have hlog_meas : Measurable
          (fun x ↦ - Real.log (convDensityAdd pX
            (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩) x) - 1) :=
        ((Real.measurable_log.comp hpath_meas).neg).sub_const 1
      have hd2_meas : Measurable
          (fun x ↦ (1:ℝ)/2 * deriv (deriv (convDensityAdd pX
            (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩))) x) :=
        (measurable_deriv _).const_mul _
      exact (hlog_meas.mul hd2_meas).aestronglyMeasurable
    -- `hb`: domination, restated for `entDerivFn s` (= `max s 0` form). On `Ioo (t/2)(2*t)`
    --   each `s > 0` so `max s 0 = s`, matching `_chain_domination`'s `⟨s,_⟩` form.
    have hb : ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioo (t/2) (2*t), ‖entDerivFn s x‖ ≤ bound x := by
      filter_upwards [hb_dom] with x hx
      intro s hs
      have hspos : (0:ℝ) < s := by have := hs.1; linarith
      have hmaxs : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hspos.le⟩ := by
        apply NNReal.eq; exact max_eq_left hspos.le
      have hbx := hx s hs
      rw [hentDerivFn]; simp only; rw [hmaxs]; exact hbx
    -- `hdiff`: per-`x` chain-rule derivative plumbing.
    have hdiff := debruijnIdentityV2_holds_assembled_chain_hdiff
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
    -- apply the parametric-diff atom (its `entDeriv` arg is `entDerivFn`, `pPath` arg is `pPath`).
    exact entropy_hasDerivAt_via_parametric pPath entDerivFn bound ht
      hbound_int hmeas hint hderiv_meas hb hdiff
  · -- ===== second goal: Fisher value, via `_chain_ibp_fisher`. =====
    -- the witness `entDeriv x = entDerivFn t x` equals the `⟨t,_⟩`-form integrand a.e.
    have hmaxt : (⟨max t 0, le_max_right t 0⟩ : ℝ≥0) = ⟨t, ht.le⟩ := by
      apply NNReal.eq; exact max_eq_left ht.le
    have hentDeriv : ∀ᵐ x ∂volume, entDerivFn t x =
        (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
          * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) := by
      filter_upwards with x
      rw [hentDerivFn]; simp only; rw [hmaxt]
    exact debruijnIdentityV2_holds_assembled_chain_ibp_fisher
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht (fun x ↦ entDerivFn t x) hentDeriv

/-- For the heat-flow density path `pPath s = convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩)`
(the convolution density of the law of `X + √s · Z`), the `s`-derivative of the entropy
`∫ negMulLog (pPath s ·)` at `t` equals `(1/2) · fisherInfoOfDensityReal (pPath t)`. Obtained
from `_chain_parametric`.

@audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_chain
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s ↦ ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume)
      ((1/2) * fisherInfoOfDensityReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := by
  -- body assembly: `_parametric` supplies the entropy-derivative and its
  -- value `= (1/2)·fisher`. The `max s 0` neighborhood correction is baked into the
  -- `_parametric` signature (integrand matches the `_chain` conclusion verbatim).
  obtain ⟨entDeriv, hderiv, hval⟩ :=
    debruijnIdentityV2_holds_assembled_chain_parametric pX hpX_nn hpX_meas hpX_int hpX_mass
      hpX_mom ht
  rw [hval] at hderiv
  exact hderiv

/-- Along the heat-flow path, on a neighborhood of `t` the differential entropy of the
pushforward equals the `∫ negMulLog` of the convolution density: for `s` near `t`,
`differentialEntropy (P.map (X + √s · Z)) = ∫ x, negMulLog (convDensityAdd pX g_s x)`. Uses the
density identification `pPath_eq_convDensityAdd` and `differentialEntropy_eq_integral_density`.

@audit:ok -/
private theorem debruijnIdentityV2_holds_assembled_entropy_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    {t : ℝ} (ht : 0 < t) :
    (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      =ᶠ[nhds t] (fun s ↦ ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume) := by
  -- on the neighborhood `s > 0` the two functions are equal pointwise.
  filter_upwards [eventually_gt_nhds ht] with s hs
  -- at `s > 0`: `max s 0 = s`.
  have hmax : max s 0 = s := max_eq_left hs.le
  -- density identification (general noise variance): instantiate at `v_Z := 1`
  --   (recovers `s·1 = s`).
  have h1b := pPath_eq_convDensityAdd X Z hX hZ hXZ (1 : ℝ≥0) one_pos hZ_law
    pX hpX_nn hpX_meas hpX_law hs
  -- unfold differentialEntropy = ∫ negMulLog ((rnDeriv).toReal).
  unfold differentialEntropy
  -- rewrite the variance witness `⟨max s 0, _⟩` to `⟨s, hs.le⟩`.
  have hwit : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hs.le⟩ := by
    apply NNReal.eq; exact hmax
  -- the density-identification result variance `⟨s·1, _⟩` equals `⟨s, hs.le⟩` (`s·1 = s`).
  have hwit1 : (⟨s * (1 : ℝ≥0), by positivity⟩ : ℝ≥0) = ⟨s, hs.le⟩ := by
    apply NNReal.eq; simp
  rw [hwit1] at h1b
  rw [hwit]
  -- congr the two integrands a.e. via the density identification + `toReal_ofReal`
  --   (convDensityAdd ≥ 0).
  refine integral_congr_ae ?_
  filter_upwards [h1b] with x hx
  rw [hx]
  -- `negMulLog ((ofReal (convDensityAdd …)).toReal) = negMulLog (convDensityAdd …)`
  -- needs `convDensityAdd … x ≥ 0` (so `toReal_ofReal`).
  rw [ENNReal.toReal_ofReal]
  -- nonnegativity of `convDensityAdd pX g_s x = ∫ y, pX y · g_s (x-y)`.
  refine integral_nonneg (fun y ↦ ?_)
  exact mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)

/-- The Fisher info of the time-`t` convolution density `convDensityAdd pX g_t` equals the
Fisher info of the density witness `density_t`. Since `density_t_eq` pins `density_t` pointwise
to `convDensityAdd pX g_t`, the two functions are equal and the values coincide. -/
private theorem debruijnIdentityV2_holds_assembled_fisher_match
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z) (_hXZ : IndepFun X Z P)
    (_hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (_hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX)
    (_hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    {t : ℝ}
    (density_t : ℝ → ℝ)
    (hdensity_t_eq : ∀ (ht : 0 < t) (x : ℝ),
      density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)
    (ht : 0 < t) :
    fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = fisherInfoOfDensityReal density_t := by
  have hfun : density_t = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) :=
    funext (hdensity_t_eq ht)
  rw [hfun]

/-- The per-time de Bruijn identity: for `X ⊥ Z` with `Z ∼ 𝒩(0, 1)` and `t > 0`,
`(d/dt) differentialEntropy (P.map (X + √t · Z)) = (1/2) · fisherInfoOfDensityReal h_reg.density_t`.
Proved by assembling the per-time atoms; lives in a separate file from the de Bruijn definitions to
avoid an import cycle. The body threads through `_entropy_eq` (entropy as `∫ negMulLog`), `_chain`
(its `s`-derivative), and `_fisher_match` (the density-witness value), combined via
`HasDerivAt.congr_of_eventuallyEq`.

@audit:ok -/
theorem debruijnIdentityV2_holds_assembled
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  -- pX integrability from `pX_law` + `P` probability.
  have hpX_int : Integrable h_reg.pX volume := by
    rw [Integrable, hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h_reg.pX_nn)]
    refine ⟨h_reg.pX_meas.aestronglyMeasurable, ?_⟩
    have hlint : ∫⁻ x, ENNReal.ofReal (h_reg.pX x) ∂volume = (P.map X) Set.univ := by
      rw [h_reg.pX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
    exact ENNReal.one_lt_top
  -- pX is a genuine probability density ⇒ `∫ pX = 1` (mass = (P.map X) univ = P univ = 1).
  --   Regularity precondition for the convolution Gaussian lower bound
  --   (`convDensityAdd_lower_bound_gaussian`).
  have hpX_mass : (∫ y, h_reg.pX y ∂volume) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h_reg.pX_nn)
      h_reg.pX_meas.aestronglyMeasurable]
    have hlint : ∫⁻ x, ENNReal.ofReal (h_reg.pX x) ∂volume = (P.map X) Set.univ := by
      rw [h_reg.pX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ,
      ENNReal.toReal_one]
  -- the entropy-as-∫negMulLog chain has the half-fisher derivative at t.
  have h_chain := debruijnIdentityV2_holds_assembled_chain h_reg.pX h_reg.pX_nn
    h_reg.pX_meas hpX_int hpX_mass h_reg.pX_mom ht
  -- entropy =ᶠ ∫ negMulLog (convDensityAdd …) near t.
  have h_eq := debruijnIdentityV2_holds_assembled_entropy_eq X Z hX hZ hXZ h_reg.Z_law
    h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law ht
  -- transfer the derivative to the entropy function via eventual equality.
  have h_ent : HasDerivAt
      (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal
        (convDensityAdd h_reg.pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := h_chain.congr_of_eventuallyEq h_eq
  -- rewrite the RHS fisher value to use `h_reg.density_t`.
  rw [debruijnIdentityV2_holds_assembled_fisher_match X Z hX hZ hXZ h_reg.Z_law
    h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law h_reg.density_t h_reg.density_t_eq ht]
    at h_ent
  exact h_ent

end InformationTheory.Shannon.FisherInfo
