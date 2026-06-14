import InformationTheory.Shannon.EPI.DensityForm


/-!
# Explicit-density de Bruijn producer and explicit density-form EPI

This file replaces the canonical `Measure.rnDeriv` representative in the de Bruijn
producer with an explicit density argument.

The canonical `rnDeriv` representative is `Classical.choose`-derived and generically
non-differentiable, so `IsRegularDensityV2` (full pointwise regularity) cannot be
transported from a smoothed density `conv(pX, g_t)` to a mere a.e.-equal canonical
representative. The producer here accepts an explicit `pX : ℝ → ℝ` that the caller
controls.

## Main definitions

- `isDeBruijnRegularityHyp_of_explicitDensity`: explicit-density de Bruijn producer.

## Main statements

- `entropy_power_inequality_of_density_explicit`: explicit-density density-form EPI.

## Implementation notes

All hypotheses (`hpX_nn`/`hpX_meas`/`hpX_int`/`hpX_law`/`hpX_mom`/`hreg_pX`/`hnorm_pX`/`hready_pX`)
are regularity preconditions, not load-bearing: they assert pointwise regularity of the
explicit density, normalization, and finite Fisher information, but do not encode the
de Bruijn / Fisher-monotonicity inequality core.
-/

namespace InformationTheory.Shannon.EPICase1SmoothingLimit

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1RatioLimit
open InformationTheory.Shannon.EPICase1TwoTime
open InformationTheory.Shannon.EPINoiseExtension
open scoped ENNReal NNReal

/-- Explicit-density variant of `isDeBruijnRegularityHyp_of_methodX_unitnoise`.

Replaces the canonical `rnDeriv` prefix with an explicit `pX : ℝ → ℝ` argument,
allowing the caller to pass a pointwise-regular density such as `conv(pX_base, g_t)`
directly without having to transport `IsRegularDensityV2` through an a.e.-equality.
@audit:ok -/
noncomputable def isDeBruijnRegularityHyp_of_explicitDensity
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z_X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (pX : ℝ → ℝ)
    (hpX_nn : ∀ x, 0 ≤ pX x)
    (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hreg_pX : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 pX)
    (hnorm_pX : ∫ x, pX x ∂volume = 1)
    (hready_pX : ∀ v : ℝ≥0, v ≠ 0 →
        InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady pX (gaussianPDFReal 0 v)) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P := by
  classical
  refine
    { density_path := fun t => InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
        (gaussianPDFReal 0 t.toNNReal),
      reg_at := fun t ht =>
        { Z_law := hZX_law
          density_t := InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 ⟨t, ht.le⟩)
          density_t_eq := fun _ _ => rfl
          pX := pX
          pX_nn := hpX_nn
          pX_meas := hpX_meas
          pX_law := hpX_law
          pX_mom := hpX_mom }
      density_t_eq := ?_
      integrable_deriv := ?_ }
  · -- density_t_eq: the V2-internal density_t is pinned to density_path t (both = conv-pin).
    intro t ht
    have : t.toNNReal = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply NNReal.eq; exact Real.coe_toNNReal t ht.le
    rw [this]
  · -- integrable_deriv: PB-2b (`fisherInfoOfDensity_convDensityAdd_le`) gives the uniform bound
    -- `(1/2)·J(density_t).toReal ≤ (1/2)·J(pX).toReal =: C` for every `t ∈ Ioc 0 T`. The
    -- `t`-measurability of the integrand is supplied by `aestronglyMeasurable_fisherInfo_t`.
    intro T hT
    simp only [InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2_def]
    set C : ℝ := (1 / 2) *
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity pX).toReal with hC_def
    have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) T,
        (1 / 2) * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 t.toNNReal))).toReal ≤ C := by
      intro t ht
      have htpos : 0 < t := ht.1
      have hv_ne : t.toNNReal ≠ 0 := by
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact htpos
      have hregY : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
          (gaussianPDFReal 0 t.toNNReal) :=
        InformationTheory.Shannon.EPIBlachmanGaussianWitness.isRegularDensityV2_gaussianPDFReal hv_ne
      have hnormY : ∫ x, gaussianPDFReal 0 t.toNNReal x ∂volume = 1 :=
        ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hv_ne
      have hmono := fisherInfoOfDensity_convDensityAdd_le pX (gaussianPDFReal 0 t.toNNReal)
        hreg_pX hregY hnorm_pX hnormY (hready_pX _ hv_ne)
      simp only [hC_def]
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (by
        simp only [ne_eq]
        exact (measure_Ioc_lt_top).ne)
      ?_meas (M := C) ?_bdd
    · exact InformationTheory.Shannon.EPICase1ProducerMeasurability.aestronglyMeasurable_fisherInfo_t
        hpX_meas hpX_int
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
      intro t ht
      have hnn : (0 : ℝ) ≤ (1 / 2) *
          (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
              (gaussianPDFReal 0 t.toNNReal))).toReal :=
        mul_nonneg (by norm_num) ENNReal.toReal_nonneg
      rw [Real.norm_of_nonneg hnn]
      exact hbound t ht

noncomputable def isHeatFlowEndpointRegular_of_map_eq_rnDeriv
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (W : Ω → ℝ) (W' : α → ℝ) (Zw : α → ℝ) (vZ : ℝ≥0)
    (hW : Measurable W) (hW' : Measurable W') (hZw : Measurable Zw)
    (hWZ : IndepFun W' Zw μ) (hvZ : 0 < vZ) (hZw_law : μ.map Zw = gaussianReal 0 vZ)
    (hmap : μ.map W' = P.map W) (hac : (P.map W) ≪ volume)
    (hmom : Integrable (fun ω => (W ω) ^ 2) P)
    (hent : Integrable (fun x => Real.negMulLog (((P.map W).rnDeriv volume x).toReal)) volume) :
    IsHeatFlowEndpointRegular W' Zw μ := by
  set p : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hp_def
  have hp_nn : ∀ x, 0 ≤ p x := fun x => ENNReal.toReal_nonneg
  have hp_meas : Measurable p := ((P.map W).measurable_rnDeriv volume).ennreal_toReal
  have hp_law : μ.map W' = volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
    rw [hmap]
    have hfin : ∀ᵐ x ∂volume, (P.map W).rnDeriv volume x < ∞ :=
      Measure.rnDeriv_lt_top (P.map W) volume
    have hcongr : (fun x => ENNReal.ofReal (p x)) =ᵐ[volume]
        (P.map W).rnDeriv volume := by
      filter_upwards [hfin] with x hx
      simp only [hp_def, ENNReal.ofReal_toReal hx.ne]
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hac]
  have hp_int : Integrable p volume := by
    have := Measure.integrable_toReal_rnDeriv (μ := P.map W) (ν := volume)
    simpa [hp_def] using this
  have hp_mass : (∫ y, p y ∂volume) = 1 := by
    have hmass := MeasureTheory.Measure.integral_toReal_rnDeriv (μ := P.map W) (ν := volume) hac
    have : IsProbabilityMeasure (P.map W) :=
      MeasureTheory.Measure.isProbabilityMeasure_map hW.aemeasurable
    rw [hp_def, hmass, Measure.real, measure_univ, ENNReal.toReal_one]
  have hp_mom : Integrable (fun y => y ^ 2 * p y) volume := by
    have hsq_law : Integrable (fun y => y ^ 2) (P.map W) := by
      rw [integrable_map_measure
        ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
        hW.aemeasurable]
      simpa [Function.comp] using hmom
    rw [show P.map W = volume.withDensity (fun x => ENNReal.ofReal (p x)) from
      hmap ▸ hp_law] at hsq_law
    rw [integrable_withDensity_iff_integrable_smul₀'
      hp_meas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq_law
    refine hsq_law.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hp_nn x)]; ring
  exact
    { hX_meas := hW'
      hZ_meas := hZw
      hXZ_indep := hWZ
      v_Z := vZ
      hv_Z_pos := hvZ
      hZ_law := hZw_law
      pX := p
      hpX_nn := hp_nn
      hpX_meas := hp_meas
      hpX_law := hp_law
      hpX_int := hp_int
      hpX_mass := hp_mass
      hpX_mom := hp_mom
      hpX_ent := hent }

lemma integral_sub_integral_sq_smoothed_path_le
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (A B : α → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : IndepFun A B μ) (h_mom_A : Integrable (fun p => (A p) ^ 2) μ)
    (v_B : ℝ≥0) (hB_law : μ.map B = gaussianReal 0 v_B)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, (x - (∫ y, y ∂(μ.map (fun p => A p / Real.sqrt t + B p)))) ^ 2
          ∂(μ.map (fun p => A p / Real.sqrt t + B p)))
        ≤ ProbabilityTheory.variance A μ / t + (v_B : ℝ) := by
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  set Zt : α → ℝ := fun ω => A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hW_meas : Measurable (fun ω => Zt ω + B ω) := hZt_meas.add hB
  have hB_memLp : MemLp B 2 μ := by
    have hid : MemLp (id : ℝ → ℝ) 2 (μ.map B) := by
      rw [hB_law]; exact memLp_id_gaussianReal' 2 (by simp)
    have := (memLp_map_measure_iff (p := 2) (μ := μ) (g := (id : ℝ → ℝ))
      aestronglyMeasurable_id hB.aemeasurable).mp hid
    simpa [Function.comp] using this
  have hZt_sq : Integrable (fun ω => (Zt ω)^2) μ := by
    have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
      funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
    rw [this]; exact h_mom_A.const_mul _
  have hZt_memLp : MemLp Zt 2 μ :=
    (memLp_two_iff_integrable_sq_norm hZt_meas.aestronglyMeasurable).mpr (by simpa using hZt_sq)
  have h_indep : IndepFun Zt B μ := by
    have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
    rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
  have hLHS : (∫ x, (x - (∫ y, y ∂(μ.map (fun ω => Zt ω + B ω))))^2
        ∂(μ.map (fun ω => Zt ω + B ω)))
      = ProbabilityTheory.variance (fun ω => Zt ω + B ω) μ := by
    rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
    exact ProbabilityTheory.variance_id_map hW_meas.aemeasurable
  have hVarZt : ProbabilityTheory.variance Zt μ
      = (1 / t) * ProbabilityTheory.variance A μ := by
    have hZt_eq : Zt = fun ω => (1 / Real.sqrt t) * A ω := by
      funext ω; simp only [hZt]; rw [div_eq_inv_mul, one_div]
    rw [hZt_eq, ProbabilityTheory.variance_const_mul]
    congr 1
    rw [div_pow, one_pow, Real.sq_sqrt ht.le]
  have hVarB : ProbabilityTheory.variance B μ = (v_B : ℝ) := by
    rw [← ProbabilityTheory.variance_id_map hB.aemeasurable, hB_law,
      ProbabilityTheory.variance_id_gaussianReal]
  have hVarSum : ProbabilityTheory.variance (fun ω => Zt ω + B ω) μ
      = (1 / t) * ProbabilityTheory.variance A μ + (v_B : ℝ) := by
    rw [ProbabilityTheory.IndepFun.variance_fun_add hZt_memLp hB_memLp h_indep,
      hVarZt, hVarB]
  rw [hLHS, hVarSum, one_div, inv_mul_eq_div]

lemma smoothed_path_absolutelyContinuous_and_negMulLog_integrable
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (A B : α → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : IndepFun A B μ) (hA_ac : (μ.map A) ≪ volume)
    (h_mom_A : Integrable (fun p => (A p) ^ 2) μ)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0) (hB_law : μ.map B = gaussianReal 0 v_B)
    {t : ℝ} (ht : 0 < t) :
    (μ.map (fun p => A p / Real.sqrt t + B p)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((μ.map (fun p => A p / Real.sqrt t + B p)).rnDeriv volume x).toReal)) volume := by
  set Zt : α → ℝ := fun ω => A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hB_ac : (μ.map B) ≪ volume := by
    rw [hB_law]; exact gaussianReal_absolutelyContinuous 0 hv_B
  have h_indep : IndepFun Zt B μ := by
    have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
    rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
  have hμ_ac : (μ.map (fun ω => Zt ω + B ω)) ≪ volume := by
    have hWac : (μ.map (fun ω => B ω + Zt ω)) ≪ volume :=
      map_add_absolutelyContinuous B Zt μ hB hZt_meas h_indep.symm hB_ac
    have h_path : (fun ω => Zt ω + B ω) = (fun ω => B ω + Zt ω) := by funext ω; ring
    rw [h_path]; exact hWac
  refine ⟨hμ_ac, ?_⟩
  have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
  obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
    rescaledInput_density_witness A μ hA hA_ac h_mom_A ht
  have hgconv : InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1
      = fun ω => Zt ω + B ω := by
    funext ω
    simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
      Real.sqrt_one, one_mul]
  have h_path_rnDeriv : (μ.map (fun ω => Zt ω + B ω)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal
        (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
    have := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
      Zt B hZt_meas hB h_indep v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
      (s := 1) one_pos
    rwa [hgconv] at this
  have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B := by
    apply NNReal.coe_injective; show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul]
  have h_asset : Integrable (fun x =>
      Real.negMulLog (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
        (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x)) volume := by
    rw [show (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B from hvar_eq]
    have hv_B_pos' : (0 : ℝ) < v_B := hv_B_pos
    simpa using InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
      hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (t := (v_B : ℝ)) hv_B_pos'
  refine h_asset.congr ?_
  filter_upwards [h_path_rnDeriv] with x hx
  have hcd_nn : 0 ≤ InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
      (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x :=
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
  rw [hx, ENNReal.toReal_ofReal hcd_nn]

/-- Explicit-density variant of `entropy_power_inequality_of_density`.

States regularity hypotheses for `pX`, `pY`, `pXY` as explicit `ℝ → ℝ` arguments
rather than canonical `rnDeriv` representatives, and adds `withDensity` links.
All hypotheses are regularity preconditions; they do not encode the EPI inequality core.
@audit:ok -/
theorem entropy_power_inequality_of_density_explicit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω) ^ 2) P)
    -- explicit X density + regularity
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hreg_pX : FisherInfoV2.IsRegularDensityV2 pX)
    (hnorm_pX : ∫ x, pX x ∂volume = 1)
    (hready_pX : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady pX (gaussianPDFReal 0 v))
    (hent_pX : Integrable (fun x => Real.negMulLog (pX x)) volume)
    -- explicit Y density + regularity
    (pY : ℝ → ℝ) (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY)
    (hpY_int : Integrable pY volume)
    (hpY_law : P.map Y = volume.withDensity (fun x => ENNReal.ofReal (pY x)))
    (hpY_mom : Integrable (fun y => y ^ 2 * pY y) volume)
    (hreg_pY : FisherInfoV2.IsRegularDensityV2 pY)
    (hnorm_pY : ∫ x, pY x ∂volume = 1)
    (hready_pY : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady pY (gaussianPDFReal 0 v))
    (hent_pY : Integrable (fun x => Real.negMulLog (pY x)) volume)
    -- explicit sum density + regularity
    (pXY : ℝ → ℝ) (hpXY_nn : ∀ x, 0 ≤ pXY x) (hpXY_meas : Measurable pXY)
    (hpXY_int : Integrable pXY volume)
    (hpXY_law : P.map (fun ω => X ω + Y ω)
        = volume.withDensity (fun x => ENNReal.ofReal (pXY x)))
    (hpXY_mom : Integrable (fun y => y ^ 2 * pXY y) volume)
    (hreg_pXY : FisherInfoV2.IsRegularDensityV2 pXY)
    (hnorm_pXY : ∫ x, pXY x ∂volume = 1)
    (hready_pXY : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady pXY (gaussianPDFReal 0 v))
    (hent_pXY : Integrable (fun x => Real.negMulLog (pXY x)) volume) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- canonical rnDeriv ≡ explicit density a.e. (for transporting the rnDeriv-form
  -- entropy integrability needed by `endpt_of`).
  have hrnae_X : (fun x => ((P.map X).rnDeriv volume x).toReal) =ᵐ[volume] pX := by
    have h1 : (P.map X).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (pX x) := by
      rw [hpX_law]; exact Measure.rnDeriv_withDensity volume hpX_meas.ennreal_ofReal
    filter_upwards [h1] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpX_nn x)]
  have hrnae_Y : (fun x => ((P.map Y).rnDeriv volume x).toReal) =ᵐ[volume] pY := by
    have h1 : (P.map Y).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (pY x) := by
      rw [hpY_law]; exact Measure.rnDeriv_withDensity volume hpY_meas.ennreal_ofReal
    filter_upwards [h1] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpY_nn x)]
  have hrnae_XY : (fun x => ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)
      =ᵐ[volume] pXY := by
    have h1 : (P.map (fun ω => X ω + Y ω)).rnDeriv volume
        =ᵐ[volume] fun x => ENNReal.ofReal (pXY x) := by
      rw [hpXY_law]; exact Measure.rnDeriv_withDensity volume hpXY_meas.ennreal_ofReal
    filter_upwards [h1] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpXY_nn x)]
  -- rnDeriv-form entropy integrability (transported from explicit hent_p*)
  have hent_X' : Integrable
      (fun x => Real.negMulLog (((P.map X).rnDeriv volume x).toReal)) volume :=
    hent_pX.congr (by filter_upwards [hrnae_X] with x hx; rw [hx])
  have hent_Y' : Integrable
      (fun x => Real.negMulLog (((P.map Y).rnDeriv volume x).toReal)) volume :=
    hent_pY.congr (by filter_upwards [hrnae_Y] with x hx; rw [hx])
  have hent_XY' : Integrable
      (fun x => Real.negMulLog (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume :=
    hent_pXY.congr (by filter_upwards [hrnae_XY] with x hx; rw [hx])
  -- Reduce to a 3-noise-lift-space EPI via `entropy_power_inequality_via_lift3`.
  refine entropy_power_inequality_via_lift3 P X Y hX hY ?_
  set lift : Measure (Ω × ℝ × ℝ × ℝ) := liftMeasure3 P with hlift
  set X' : Ω × ℝ × ℝ × ℝ → ℝ := fun p => X p.1 with hX'
  set Y' : Ω × ℝ × ℝ × ℝ → ℝ := fun p => Y p.1 with hY'
  set ZX : Ω × ℝ × ℝ × ℝ → ℝ := fun p => p.2.1 with hZX
  set ZY : Ω × ℝ × ℝ × ℝ → ℝ := fun p => p.2.2.1 with hZY
  set Z : Ω × ℝ × ℝ × ℝ → ℝ := fun p => p.2.2.2 with hZ
  -- measurability of lift functions
  have hX'_meas : Measurable X' := hX.comp measurable_fst
  have hY'_meas : Measurable Y' := hY.comp measurable_fst
  have hZX_meas : Measurable ZX := measurable_fst.comp measurable_snd
  have hZY_meas : Measurable ZY := (measurable_fst.comp measurable_snd).comp measurable_snd
  have hZ_meas : Measurable Z := (measurable_snd.comp measurable_snd).comp measurable_snd
  -- law transport: lift.map (f∘fst) = P.map f
  have hmap_X' : lift.map X' = P.map X := by
    rw [hlift, hX', show (fun p : Ω × ℝ × ℝ × ℝ => X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  have hmap_Y' : lift.map Y' = P.map Y := by
    rw [hlift, hY', show (fun p : Ω × ℝ × ℝ × ℝ => Y p.1) = Y ∘ Prod.fst from rfl,
      ← Measure.map_map hY measurable_fst, measurePreserving_fst.map_eq]
  have hmap_sum' : lift.map (fun p => X' p + Y' p) = P.map (fun ω => X ω + Y ω) := by
    rw [hlift, hX', hY',
      show (fun p : Ω × ℝ × ℝ × ℝ => X p.1 + Y p.1) = (fun ω => X ω + Y ω) ∘ Prod.fst from rfl,
      ← Measure.map_map (hX.add hY) measurable_fst, measurePreserving_fst.map_eq]
  -- a.c. transport
  have hX'_ac : (lift.map X') ≪ volume := by rw [hmap_X']; exact hX_ac
  have hY'_ac : (lift.map Y') ≪ volume := by rw [hmap_Y']; exact hY_ac
  have hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  have hXY'_ac : (lift.map (fun p => X' p + Y' p)) ≪ volume := by rw [hmap_sum']; exact hXY_ac
  -- second moment of X+Y on base P
  have h_mom_XY : Integrable (fun ω => (X ω + Y ω) ^ 2) P := by
    have hX_memLp : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
    have hY_memLp : MemLp Y 2 P :=
      (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
    have hS_memLp : MemLp (fun ω => X ω + Y ω) 2 P := hX_memLp.add hY_memLp
    simpa using hS_memLp.integrable_sq
  -- moment transport (to the 3-noise lift)
  have h_mom_X' : Integrable (fun p => (X' p) ^ 2) lift := by
    rw [hlift, hX']
    exact h_mom_X.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  have h_mom_Y' : Integrable (fun p => (Y' p) ^ 2) lift := by
    rw [hlift, hY']
    exact h_mom_Y.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  have h_mom_XY' : Integrable (fun p => (X' p + Y' p) ^ 2) lift := by
    rw [hlift, hX', hY']
    exact (h_mom_XY.comp_fst
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))))
  -- noise laws
  have hZX_law : lift.map ZX = gaussianReal 0 1 := by
    rw [hlift, hZX,
      show (fun p : Ω × ℝ × ℝ × ℝ => p.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_fst.map_eq]
  have hZY_law : lift.map ZY = gaussianReal 0 1 := by
    rw [hlift, hZY,
      show (fun p : Ω × ℝ × ℝ × ℝ => p.2.2.1)
        = Prod.fst ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq,
      measurePreserving_fst.map_eq]
  have hZ_law : lift.map Z = gaussianReal 0 1 := by
    rw [hlift, hZ,
      show (fun p : Ω × ℝ × ℝ × ℝ => p.2.2.2)
        = Prod.snd ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq,
      measurePreserving_snd.map_eq]
  -- 5-tuple joint independence
  have h_iIndep : iIndepFun ![X', Y', ZX, ZY, Z] lift := by
    have haem : ∀ i, AEMeasurable (![X', Y', ZX, ZY, Z] i) lift := by
      intro i; fin_cases i
      · exact hX'_meas.aemeasurable
      · exact hY'_meas.aemeasurable
      · exact hZX_meas.aemeasurable
      · exact hZY_meas.aemeasurable
      · exact hZ_meas.aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map haem]
    symm
    refine Measure.pi_eq (fun s hs => ?_)
    have hjoint_meas : Measurable (fun ω i => ![X', Y', ZX, ZY, Z] i ω) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      fin_cases i
      · exact hX'_meas
      · exact hY'_meas
      · exact hZX_meas
      · exact hZY_meas
      · exact hZ_meas
    rw [Measure.map_apply hjoint_meas (MeasurableSet.univ_pi hs)]
    have hm0 : lift.map (![X', Y', ZX, ZY, Z] 0) = P.map X := by simpa using hmap_X'
    have hm1 : lift.map (![X', Y', ZX, ZY, Z] 1) = P.map Y := by simpa using hmap_Y'
    have hm2 : lift.map (![X', Y', ZX, ZY, Z] 2) = gaussianReal 0 1 := by simpa using hZX_law
    have hm3 : lift.map (![X', Y', ZX, ZY, Z] 3) = gaussianReal 0 1 := by simpa using hZY_law
    have hm4 : lift.map (![X', Y', ZX, ZY, Z] 4) = gaussianReal 0 1 := by simpa using hZ_law
    rw [Fin.prod_univ_five, hm0, hm1, hm2, hm3, hm4]
    have hpre : (fun ω i => ![X', Y', ZX, ZY, Z] i ω) ⁻¹' (Set.univ.pi s)
        = (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) ×ˢ (s 2 ×ˢ (s 3 ×ˢ s 4)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨⟨h 0, h 1⟩, h 2, h 3, h 4⟩
      · intro h i
        fin_cases i
        · exact h.1.1
        · exact h.1.2
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2
    rw [hpre, hlift, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
    have hAprod : P (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) = P.map X (s 0) * P.map Y (s 1) := by
      rw [Measure.map_apply hX (hs 0), Measure.map_apply hY (hs 1)]
      exact (indepFun_iff_measure_inter_preimage_eq_mul.1 hXY) (s 0) (s 1) (hs 0) (hs 1)
    rw [hAprod]
    ring
  have hf_meas : ∀ i, Measurable (![X', Y', ZX, ZY, Z] i) := by
    intro i; fin_cases i
    · exact hX'_meas
    · exact hY'_meas
    · exact hZX_meas
    · exact hZY_meas
    · exact hZ_meas
  -- pairwise/joint independences
  have hXZX : IndepFun X' ZX lift := by
    have := h_iIndep.indepFun (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
    simpa using this
  have hYZY : IndepFun Y' ZY lift := by
    have := h_iIndep.indepFun (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
    simpa using this
  have hX'Y'_indep : IndepFun X' Y' lift := by
    have := h_iIndep.indepFun (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
    simpa using this
  have hZX_ZY : IndepFun ZX ZY lift := by
    have := h_iIndep.indepFun (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
    simpa using this
  have hpair_indep : IndepFun (fun p => (X' p, ZX p)) (fun p => (Y' p, ZY p)) lift := by
    have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
    simpa using this
  have hXYZ : IndepFun (fun p => X' p + Y' p) Z lift := by
    have hpair : IndepFun (fun a => (X' a, Y' a)) Z lift := by
      have := h_iIndep.indepFun_prodMk hf_meas 0 1 4 (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun q : ℝ × ℝ => q.1 + q.2) := by fun_prop
    have := hpair.comp hsum measurable_id
    simpa [Function.comp] using this
  have hXY_ZXZY_pair : IndepFun (fun p => X' p + Y' p) (fun p => (ZX p, ZY p)) lift := by
    have hpair : IndepFun (fun a => (X' a, Y' a)) (fun a => (ZX a, ZY a)) lift := by
      have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 1 2 3
        (by decide) (by decide) (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun q : ℝ × ℝ => q.1 + q.2) := by fun_prop
    have := hpair.comp hsum (measurable_id : Measurable (id : ℝ × ℝ → ℝ × ℝ))
    simpa [Function.comp] using this
  -- noise a.c.
  have hZX_ac : (lift.map ZX) ≪ volume := by rw [hZX_law]; exact gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hZY_ac : (lift.map ZY) ≪ volume := by rw [hZY_law]; exact gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hZ_ac : (lift.map Z) ≪ volume := by rw [hZ_law]; exact gaussianReal_absolutelyContinuous 0 one_ne_zero
  -- explicit-density link transport to the lift (lift.map X' = P.map X = withDensity(ofReal∘pX))
  have hpX_law' : lift.map X' = volume.withDensity (fun x => ENNReal.ofReal (pX x)) := by
    rw [hmap_X']; exact hpX_law
  have hpY_law' : lift.map Y' = volume.withDensity (fun x => ENNReal.ofReal (pY x)) := by
    rw [hmap_Y']; exact hpY_law
  have hpXY_law' : lift.map (fun p => X' p + Y' p)
      = volume.withDensity (fun x => ENNReal.ofReal (pXY x)) := by
    rw [hmap_sum']; exact hpXY_law
  -- de Bruijn group (explicit-density producer, all three unit-noise → genuine)
  have h_reg_X : EPIStamDischarge.IsDeBruijnRegularityHyp X' ZX lift :=
    isDeBruijnRegularityHyp_of_explicitDensity X' ZX lift hZX_law
      pX hpX_nn hpX_meas hpX_int hpX_law' hpX_mom hreg_pX hnorm_pX hready_pX
  have h_reg_Y : EPIStamDischarge.IsDeBruijnRegularityHyp Y' ZY lift :=
    isDeBruijnRegularityHyp_of_explicitDensity Y' ZY lift hZY_law
      pY hpY_nn hpY_meas hpY_int hpY_law' hpY_mom hreg_pY hnorm_pY hready_pY
  have h_reg_sum : EPIStamDischarge.IsDeBruijnRegularityHyp
      (fun p => X' p + Y' p) Z lift :=
    isDeBruijnRegularityHyp_of_explicitDensity (fun p => X' p + Y' p) Z lift
      hZ_law
      pXY hpXY_nn hpXY_meas hpXY_int hpXY_law' hpXY_mom hreg_pXY hnorm_pXY hready_pXY
  -- endpoint group: density witnesses (v_Z = 1), reusing the canonical-rnDeriv construction.
  have endpt_of : ∀ (W : Ω → ℝ) (W' : Ω × ℝ × ℝ × ℝ → ℝ) (Zw : Ω × ℝ × ℝ × ℝ → ℝ),
      Measurable W → Measurable W' → Measurable Zw → IndepFun W' Zw lift →
      lift.map Zw = gaussianReal 0 1 → lift.map W' = P.map W → (P.map W) ≪ volume →
      Integrable (fun ω => (W ω) ^ 2) P →
      Integrable (fun x => Real.negMulLog (((P.map W).rnDeriv volume x).toReal)) volume →
      IsHeatFlowEndpointRegular W' Zw lift :=
    fun W W' Zw hW hW' hZw hWZ hZw_law hmap hac hmom hent =>
      isHeatFlowEndpointRegular_of_map_eq_rnDeriv P lift W W' Zw 1 hW hW' hZw hWZ one_pos
        hZw_law hmap hac hmom hent
  have h_endpt_X : IsHeatFlowEndpointRegular X' ZX lift :=
    endpt_of X X' ZX hX hX'_meas hZX_meas hXZX hZX_law hmap_X' hX_ac h_mom_X hent_X'
  have h_endpt_Y : IsHeatFlowEndpointRegular Y' ZY lift :=
    endpt_of Y Y' ZY hY hY'_meas hZY_meas hYZY hZY_law hmap_Y' hY_ac h_mom_Y hent_Y'
  have h_endpt_sum : IsHeatFlowEndpointRegular (fun p => X' p + Y' p) Z lift :=
    endpt_of (fun ω => X ω + Y ω) (fun p => X' p + Y' p) Z (hX.add hY) (hX'_meas.add hY'_meas)
      hZ_meas hXYZ hZ_law hmap_sum' hXY_ac h_mom_XY hent_XY'
  -- variance/scale data
  have hlift_prob : IsProbabilityMeasure lift := by rw [hlift]; infer_instance
  have h_var_general : ∀ (A B : Ω × ℝ × ℝ × ℝ → ℝ), Measurable A → Measurable B →
      IndepFun A B lift → Integrable (fun p => (A p)^2) lift →
      (v_B : ℝ≥0) → lift.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (∫ x, (x - (∫ y, y ∂(lift.map (fun p => A p / Real.sqrt t + B p))))^2
              ∂(lift.map (fun p => A p / Real.sqrt t + B p)))
            ≤ ProbabilityTheory.variance A lift / t + (v_B : ℝ) :=
    fun A B hA hB hAB h_mom_A v_B hB_law t ht =>
      integral_sub_integral_sq_smoothed_path_le lift A B hA hB hAB h_mom_A v_B hB_law ht
  have h_scale_general : ∀ (A B : Ω × ℝ × ℝ × ℝ → ℝ), Measurable A → Measurable B →
      IndepFun A B lift → (lift.map A) ≪ volume → Integrable (fun p => (A p)^2) lift →
      (v_B : ℝ≥0) → v_B ≠ 0 → lift.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (lift.map (fun p => A p / Real.sqrt t + B p)) ≪ volume ∧
        Integrable (fun x => Real.negMulLog
          (((lift.map (fun p => A p / Real.sqrt t + B p)).rnDeriv volume x).toReal)) volume :=
    fun A B hA hB hAB hA_ac h_mom_A v_B hv_B hB_law t ht =>
      smoothed_path_absolutelyContinuous_and_negMulLog_integrable lift A B hA hB hAB hA_ac
        h_mom_A v_B hv_B hB_law ht
  set varX : ℝ := ProbabilityTheory.variance X' lift with hvarX_def
  set varY : ℝ := ProbabilityTheory.variance Y' lift with hvarY_def
  set varS : ℝ := ProbabilityTheory.variance (fun p => X' p + Y' p) lift with hvarS_def
  have h_varX_nn : 0 ≤ varX := ProbabilityTheory.variance_nonneg _ _
  have h_varY_nn : 0 ≤ varY := ProbabilityTheory.variance_nonneg _ _
  have h_varS_nn : 0 ≤ varS := ProbabilityTheory.variance_nonneg _ _
  have h_scale_X := h_scale_general X' ZX hX'_meas hZX_meas hXZX hX'_ac h_mom_X' 1 one_ne_zero hZX_law
  have h_scale_Y := h_scale_general Y' ZY hY'_meas hZY_meas hYZY hY'_ac h_mom_Y' 1 one_ne_zero hZY_law
  have h_scale_sum := h_scale_general (fun p => X' p + Y' p) Z (hX'_meas.add hY'_meas) hZ_meas
    hXYZ hXY'_ac h_mom_XY' 1 one_ne_zero hZ_law
  have h_rescale_X : IsRescaledPathRegular X' ZX lift varX 1 :=
    isRescaledPathRegular_of_methodX X' ZX lift hX'_meas hZX_meas 1 one_ne_zero hZX_law hXZX
      hX'_ac varX h_varX_nn h_mom_X'
      (h_var_general X' ZX hX'_meas hZX_meas hXZX h_mom_X' 1 hZX_law)
  have h_rescale_Y : IsRescaledPathRegular Y' ZY lift varY 1 :=
    isRescaledPathRegular_of_methodX Y' ZY lift hY'_meas hZY_meas 1 one_ne_zero hZY_law hYZY
      hY'_ac varY h_varY_nn h_mom_Y'
      (h_var_general Y' ZY hY'_meas hZY_meas hYZY h_mom_Y' 1 hZY_law)
  have h_rescale_S : IsRescaledPathRegular (fun p => X' p + Y' p) Z lift varS 1 :=
    isRescaledPathRegular_of_methodX (fun p => X' p + Y' p) Z lift (hX'_meas.add hY'_meas)
      hZ_meas 1 one_ne_zero hZ_law hXYZ hXY'_ac varS h_varS_nn h_mom_XY'
      (h_var_general (fun p => X' p + Y' p) Z (hX'_meas.add hY'_meas) hZ_meas hXYZ h_mom_XY'
        1 hZ_law)
  -- h_stam_supply via the two-time producer
  have h_stam_supply := EPIStamSupplyTwoTime.twoTime_stam_supply lift X' Y' ZX ZY Z
    hX'_meas hY'_meas hZX_meas hZY_meas hZ_meas hXZX hYZY hX'Y'_indep hpair_indep
    hZX_law hZY_law hZ_law hX'_ac hY'_ac h_mom_X' h_mom_Y' h_reg_X h_reg_Y h_reg_sum
  -- apply the two-time terminal
  exact entropyPower_add_ge_case1_of_regular_twotime X' Y' ZX ZY Z lift
    hX'_meas hY'_meas hZX_meas hZY_meas hZ_meas hXZX hYZY
    hZX_law hZY_law hZ_law hXYZ hXY_ZXZY_pair hZX_ZY
    hZX_ac hZY_ac hZ_ac
    h_reg_X h_reg_Y h_reg_sum h_endpt_X h_endpt_Y h_endpt_sum
    h_scale_X h_scale_Y h_scale_sum
    varX varY varS h_varX_nn h_varY_nn h_varS_nn
    h_rescale_X h_rescale_Y h_rescale_S h_stam_supply

/-- **Blachman bridge** — `IsBlachmanConvReady (convDensityAdd p_base g_τ) (gaussianPDFReal 0 v)`.

The explicit `entropy_power_inequality_of_density_explicit` requires, for each density
witness `q`, a `hready : ∀ v ≠ 0, IsBlachmanConvReady q (gaussianPDFReal 0 v)`. When `q` is
itself a conv-density `convDensityAdd p_base g_τ`, the bare `IsBlachmanConvReady (conv …) (g_v)`
shape is supplied by the asymmetric producer `isBlachmanConvReady_convDensityAdd_gaussian_asym`:
take its second arm `pY := gaussianPDFReal 0 ⟨v/2,_⟩` at time `v/2`, so its second factor
`convDensityAdd g_{v/2} g_{v/2}` collapses to `gaussianPDFReal 0 v` via the variance-doubling
identity `convDensityAdd_gaussian_variance_double`.

All hypotheses are regularity preconditions; the conclusion (19-field bundle) is genuinely
derived. No bundled analytic core. -/
theorem isBlachmanConvReady_convGaussian_gaussian (p_base : ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hp_nn : ∀ x, 0 ≤ p_base x) (hp_meas : Measurable p_base) (hp_int : Integrable p_base volume)
    (hp_mass : 0 < ∫ x, p_base x ∂volume) (hp_norm : (∫ x, p_base x ∂volume) = 1)
    {v : ℝ≥0} (hv : v ≠ 0) :
    InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
      (InformationTheory.Shannon.EPIConvDensity.convDensityAdd p_base
        (gaussianPDFReal 0 ⟨τ, hτ.le⟩))
      (gaussianPDFReal 0 v) := by
  -- `v/2 > 0` (since `v ≠ 0`).
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    have : (0 : ℝ≥0) < v := pos_iff_ne_zero.mpr hv
    exact_mod_cast this
  set h : ℝ := (v : ℝ) / 2 with hh
  have hh_pos : 0 < h := by rw [hh]; positivity
  -- The asymmetric producer at second arm `pY := g_{h}`, time `t := h`, gives
  -- `IsBlachmanConvReady (conv p_base g_τ) (conv g_h g_h)`.
  have hg_nn : ∀ x, 0 ≤ gaussianPDFReal 0 ⟨h, hh_pos.le⟩ x := gaussianPDFReal_nonneg _ _
  have hg_meas : Measurable (gaussianPDFReal 0 ⟨h, hh_pos.le⟩) := measurable_gaussianPDFReal _ _
  have hg_int : Integrable (gaussianPDFReal 0 ⟨h, hh_pos.le⟩) volume := integrable_gaussianPDFReal _ _
  have hg_ne : (⟨h, hh_pos.le⟩ : ℝ≥0) ≠ 0 := by
    intro hc; exact hh_pos.ne' (congrArg NNReal.toReal hc)
  have hg_norm : (∫ x, gaussianPDFReal 0 ⟨h, hh_pos.le⟩ x ∂volume) = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hg_ne
  have hg_mass : 0 < ∫ x, gaussianPDFReal 0 ⟨h, hh_pos.le⟩ x ∂volume := by rw [hg_norm]; norm_num
  have hbundle := InformationTheory.Shannon.EPIStamSupplyTwoTime.isBlachmanConvReady_convDensityAdd_gaussian_asym
    p_base (gaussianPDFReal 0 ⟨h, hh_pos.le⟩) hτ hh_pos
    hp_nn hp_meas hp_int hp_mass hp_norm
    hg_nn hg_meas hg_int hg_mass hg_norm
  -- collapse `conv g_h g_h = g_{2h} = g_v`.
  have hcollapse : InformationTheory.Shannon.EPIConvDensity.convDensityAdd
      (gaussianPDFReal 0 ⟨h, hh_pos.le⟩) (gaussianPDFReal 0 ⟨h, hh_pos.le⟩)
      = gaussianPDFReal 0 v := by
    rw [InformationTheory.Shannon.EPIConvDensity.convDensityAdd_gaussian_variance_double hh_pos]
    congr 1
    apply NNReal.eq
    show 2 * h = (v : ℝ)
    rw [hh]; ring
  rwa [hcollapse] at hbundle

lemma memLp_two_of_map_eq_gaussianReal_one
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZ_law : P.map Z = gaussianReal 0 1) :
    MemLp Z 2 P := by
  have hid : MemLp (id : ℝ → ℝ) 2 (P.map Z) := by
    rw [hZ_law]; exact memLp_id_gaussianReal' 2 (by simp)
  have := (memLp_map_measure_iff (p := 2) (μ := P) (g := (id : ℝ → ℝ))
    aestronglyMeasurable_id hZ.aemeasurable).mp hid
  simpa [Function.comp] using this

lemma map_eq_withDensity_ofReal_rnDeriv
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → ℝ) (p : ℝ → ℝ) (_hV : Measurable V) (hac : (P.map V) ≪ volume)
    (hp_def : p = (fun x => ((P.map V).rnDeriv volume x).toReal)) :
    P.map V = volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
  have hfin : ∀ᵐ x ∂volume, (P.map V).rnDeriv volume x < ∞ :=
    Measure.rnDeriv_lt_top (P.map V) volume
  have hcongr : (fun x => ENNReal.ofReal (p x)) =ᵐ[volume] (P.map V).rnDeriv volume := by
    filter_upwards [hfin] with x hx
    simp only [hp_def, ENNReal.ofReal_toReal hx.ne]
  rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hac]

lemma integrable_sq_mul_of_map_eq_withDensity_ofReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → ℝ) (p : ℝ → ℝ) (hV : Measurable V)
    (hlaw : P.map V = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hp_nn : ∀ x, 0 ≤ p x) (hp_meas : Measurable p)
    (hmom : Integrable (fun ω => (V ω) ^ 2) P) :
    Integrable (fun y => y ^ 2 * p y) volume := by
  have hsq_law : Integrable (fun y => y ^ 2) (P.map V) := by
    rw [integrable_map_measure
      ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
      hV.aemeasurable]
    simpa [Function.comp] using hmom
  rw [hlaw] at hsq_law
  rw [integrable_withDensity_iff_integrable_smul₀'
    hp_meas.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq_law
  refine hsq_law.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hp_nn x)]; ring

lemma map_smoothed_eq_withDensity_convDensityAdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (U Zw : Ω → ℝ) (p_base : ℝ → ℝ) (v_Z : ℝ≥0)
    (hU : Measurable U) (hZw : Measurable Zw) (hUZw : IndepFun U Zw P) (hv_Z : 0 < v_Z)
    (hZw_law : P.map Zw = gaussianReal 0 v_Z) (hp_nn : ∀ x, 0 ≤ p_base x)
    (hp_meas : Measurable p_base)
    (hp_law : P.map U = volume.withDensity (fun x => ENNReal.ofReal (p_base x)))
    {t : ℝ} (ht : 0 < t)
    (hpath_ac : (P.map (fun ω => U ω + Real.sqrt t * Zw ω)) ≪ volume) :
    P.map (fun ω => U ω + Real.sqrt t * Zw ω)
      = volume.withDensity (fun x => ENNReal.ofReal
          (InformationTheory.Shannon.EPIConvDensity.convDensityAdd p_base
            (gaussianPDFReal 0 ⟨t * (v_Z : ℝ), by positivity⟩) x)) := by
  have hgconv : InformationTheory.Shannon.FisherInfoV2.gaussianConvolution U Zw t
      = fun ω => U ω + Real.sqrt t * Zw ω := rfl
  have hrn := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
    U Zw hU hZw hUZw v_Z hv_Z hZw_law p_base hp_nn hp_meas hp_law (s := t) ht
  rw [hgconv] at hrn
  have hself : P.map (fun ω => U ω + Real.sqrt t * Zw ω)
      = volume.withDensity ((P.map (fun ω => U ω + Real.sqrt t * Zw ω)).rnDeriv volume) :=
    (Measure.withDensity_rnDeriv_eq _ _ hpath_ac).symm
  rw [hself, withDensity_congr_ae hrn]

/-- **Per-`t` smoothing EPI**.

For smoothed variables `X_t = X + √t·Z_X`, `Y_t = Y + √t·Z_Y` (independent standard-normal
noises), the entropy-power inequality holds at every fixed `t > 0`. Proved by instantiating the
explicit-density EPI `entropy_power_inequality_of_density_explicit` at `X := X_t`,
`Y := Y_t`, with conv-density witnesses `convDensityAdd p_base g_τ` (canonical-base densities
convolved with the smoothing Gaussian), and discharging all regularity obligations via the
public conv-Gaussian producers (regularity / normalization / Blachman / finite Fisher /
finite entropy).
@audit:ok -/
theorem entropyPower_smoothed_epi_perT
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z_X Z_Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω) ^ 2) P)
    (hZX_law : P.map Z_X = gaussianReal 0 1) (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P)
    {t : ℝ} (ht : 0 < t) :
    entropyPower (P.map (fun ω => (X ω + Real.sqrt t * Z_X ω) + (Y ω + Real.sqrt t * Z_Y ω)))
      ≥ entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
        + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) := by
  classical
  -- abbreviations
  set Xt : Ω → ℝ := fun ω => X ω + Real.sqrt t * Z_X ω with hXt_def
  set Yt : Ω → ℝ := fun ω => Y ω + Real.sqrt t * Z_Y ω with hYt_def
  have ht_ne : t ≠ 0 := ht.ne'
  -- measurability of smoothed variables
  have hXt_meas : Measurable Xt := hX.add ((measurable_const).mul hZX)
  have hYt_meas : Measurable Yt := hY.add ((measurable_const).mul hZY)
  -- ===== pairwise / joint independences from `iIndepFun ![X,Y,Z_X,Z_Y]` =====
  have hf_meas : ∀ i, Measurable (![X, Y, Z_X, Z_Y] i) := by
    intro i; fin_cases i
    · exact hX
    · exact hY
    · exact hZX
    · exact hZY
  -- X ⊥ Z_X, Y ⊥ Z_Y, Z_X ⊥ Z_Y
  have hX_ZX : IndepFun X Z_X P := by
    have := h_iIndep.indepFun (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide); simpa using this
  have hY_ZY : IndepFun Y Z_Y P := by
    have := h_iIndep.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide); simpa using this
  have hZX_ZY : IndepFun Z_X Z_Y P := by
    have := h_iIndep.indepFun (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide); simpa using this
  -- (X,Z_X) ⊥ (Y,Z_Y)  → IndepFun Xt Yt
  have hpair_XZX_YZY : IndepFun (fun ω => (X ω, Z_X ω)) (fun ω => (Y ω, Z_Y ω)) P := by
    have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
    simpa using this
  -- (X,Y) ⊥ (Z_X,Z_Y)  → IndepFun S W
  have hpair_XY_ZXZY : IndepFun (fun ω => (X ω, Y ω)) (fun ω => (Z_X ω, Z_Y ω)) P := by
    have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 1 2 3
      (by decide) (by decide) (by decide) (by decide)
    simpa using this
  -- IndepFun Xt Yt: both are `f∘(X,Z_X)` / `f∘(Y,Z_Y)`.
  have hXtYt_indep : IndepFun Xt Yt P := by
    have hmap : Measurable (fun q : ℝ × ℝ => q.1 + Real.sqrt t * q.2) := by fun_prop
    have := hpair_XZX_YZY.comp hmap hmap
    simpa [Function.comp, hXt_def, hYt_def] using this
  -- ===== sum-variable identity: Xt + Yt = S + √t·W =====
  set S : Ω → ℝ := fun ω => X ω + Y ω with hS_def
  set W : Ω → ℝ := fun ω => Z_X ω + Z_Y ω with hW_def
  have hS_meas : Measurable S := hX.add hY
  have hW_meas : Measurable W := hZX.add hZY
  have hsum_eq : (fun ω => Xt ω + Yt ω) = (fun ω => S ω + Real.sqrt t * W ω) := by
    funext ω; simp only [hXt_def, hYt_def, hS_def, hW_def]; ring
  -- law of W: sum of independent standard normals = N(0,2)
  have hW_law : P.map W = gaussianReal 0 2 := by
    have := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
      (P := P) hZX_ZY hZX_law hZY_law
    rw [hW_def, show (fun ω => Z_X ω + Z_Y ω) = Z_X + Z_Y from rfl]
    rw [this]; norm_num
  -- S ⊥ W (from (X,Y)⊥(Z_X,Z_Y))
  have hS_W_indep : IndepFun S W P := by
    have hmap : Measurable (fun q : ℝ × ℝ => q.1 + q.2) := by fun_prop
    have := hpair_XY_ZXZY.comp hmap hmap
    simpa [Function.comp, hS_def, hW_def] using this
  -- ===== a.c. of smoothed variables =====
  -- Xt = X + √t·Z_X ; X ⊥ √t·Z_X ; P.map X ≪ volume.
  have hXt_ac : (P.map Xt) ≪ volume := by
    have hindep : IndepFun X (fun ω => Real.sqrt t * Z_X ω) P :=
      hX_ZX.comp measurable_id (measurable_const.mul measurable_id)
    have := map_add_absolutelyContinuous X (fun ω => Real.sqrt t * Z_X ω) P hX
      (measurable_const.mul hZX) hindep hX_ac
    simpa [hXt_def] using this
  have hYt_ac : (P.map Yt) ≪ volume := by
    have hindep : IndepFun Y (fun ω => Real.sqrt t * Z_Y ω) P :=
      hY_ZY.comp measurable_id (measurable_const.mul measurable_id)
    have := map_add_absolutelyContinuous Y (fun ω => Real.sqrt t * Z_Y ω) P hY
      (measurable_const.mul hZY) hindep hY_ac
    simpa [hYt_def] using this
  -- ===== second moments of smoothed variables =====
  -- helper: a standard-normal variable is in `MemLp · 2 P`.
  have hZmemLp : ∀ Z : Ω → ℝ, Measurable Z → P.map Z = gaussianReal 0 1 → MemLp Z 2 P :=
    fun Z hZ hZ_law => memLp_two_of_map_eq_gaussianReal_one P Z hZ hZ_law
  have h_mom_Xt : Integrable (fun ω => (Xt ω) ^ 2) P := by
    have hX_memLp : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
    have hsZ_memLp : MemLp (fun ω => Real.sqrt t * Z_X ω) 2 P :=
      (hZmemLp Z_X hZX hZX_law).const_mul (Real.sqrt t)
    have hsum : MemLp Xt 2 P := by rw [hXt_def]; exact hX_memLp.add hsZ_memLp
    simpa using hsum.integrable_sq
  have h_mom_Yt : Integrable (fun ω => (Yt ω) ^ 2) P := by
    have hY_memLp : MemLp Y 2 P :=
      (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
    have hsZ_memLp : MemLp (fun ω => Real.sqrt t * Z_Y ω) 2 P :=
      (hZmemLp Z_Y hZY hZY_law).const_mul (Real.sqrt t)
    have hsum : MemLp Yt 2 P := by rw [hYt_def]; exact hY_memLp.add hsZ_memLp
    simpa using hsum.integrable_sq
  -- ===== base canonical densities =====
  haveI hPX_prob : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI hPY_prob : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  haveI hPS_prob : IsProbabilityMeasure (P.map S) := Measure.isProbabilityMeasure_map hS_meas.aemeasurable
  -- S ≪ volume
  have hS_ac : (P.map S) ≪ volume := by
    have := map_add_absolutelyContinuous X Y P hX hY
      (by have := h_iIndep.indepFun (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide); simpa using this)
      hX_ac
    simpa [hS_def] using this
  set pX_base : ℝ → ℝ := fun x => ((P.map X).rnDeriv volume x).toReal with hpXb_def
  set pY_base : ℝ → ℝ := fun x => ((P.map Y).rnDeriv volume x).toReal with hpYb_def
  set pS_base : ℝ → ℝ := fun x => ((P.map S).rnDeriv volume x).toReal with hpSb_def
  -- base density regularity (nonneg / meas / int / mass=1)
  have hpXb_nn : ∀ x, 0 ≤ pX_base x := fun x => ENNReal.toReal_nonneg
  have hpYb_nn : ∀ x, 0 ≤ pY_base x := fun x => ENNReal.toReal_nonneg
  have hpSb_nn : ∀ x, 0 ≤ pS_base x := fun x => ENNReal.toReal_nonneg
  have hpXb_meas : Measurable pX_base := ((P.map X).measurable_rnDeriv volume).ennreal_toReal
  have hpYb_meas : Measurable pY_base := ((P.map Y).measurable_rnDeriv volume).ennreal_toReal
  have hpSb_meas : Measurable pS_base := ((P.map S).measurable_rnDeriv volume).ennreal_toReal
  have hpXb_int : Integrable pX_base volume := by
    have := Measure.integrable_toReal_rnDeriv (μ := P.map X) (ν := volume); simpa [hpXb_def] using this
  have hpYb_int : Integrable pY_base volume := by
    have := Measure.integrable_toReal_rnDeriv (μ := P.map Y) (ν := volume); simpa [hpYb_def] using this
  have hpSb_int : Integrable pS_base volume := by
    have := Measure.integrable_toReal_rnDeriv (μ := P.map S) (ν := volume); simpa [hpSb_def] using this
  have hpXb_mass : (∫ y, pX_base y ∂volume) = 1 := by
    rw [hpXb_def, MeasureTheory.Measure.integral_toReal_rnDeriv hX_ac, Measure.real, measure_univ,
      ENNReal.toReal_one]
  have hpYb_mass : (∫ y, pY_base y ∂volume) = 1 := by
    rw [hpYb_def, MeasureTheory.Measure.integral_toReal_rnDeriv hY_ac, Measure.real, measure_univ,
      ENNReal.toReal_one]
  have hpSb_mass : (∫ y, pS_base y ∂volume) = 1 := by
    rw [hpSb_def, MeasureTheory.Measure.integral_toReal_rnDeriv hS_ac, Measure.real, measure_univ,
      ENNReal.toReal_one]
  have hpXb_mass_pos : 0 < ∫ y, pX_base y ∂volume := by rw [hpXb_mass]; norm_num
  have hpYb_mass_pos : 0 < ∫ y, pY_base y ∂volume := by rw [hpYb_mass]; norm_num
  have hpSb_mass_pos : 0 < ∫ y, pS_base y ∂volume := by rw [hpSb_mass]; norm_num
  -- base withDensity links (from canonical rnDeriv + a.c.)
  have base_law : ∀ (V : Ω → ℝ) (p : ℝ → ℝ), Measurable V → (P.map V) ≪ volume →
      p = (fun x => ((P.map V).rnDeriv volume x).toReal) →
      P.map V = volume.withDensity (fun x => ENNReal.ofReal (p x)) :=
    fun V p hV hac hp_def => map_eq_withDensity_ofReal_rnDeriv P V p hV hac hp_def
  have hpXb_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX_base x)) :=
    base_law X pX_base hX hX_ac hpXb_def
  have hpYb_law : P.map Y = volume.withDensity (fun x => ENNReal.ofReal (pY_base x)) :=
    base_law Y pY_base hY hY_ac hpYb_def
  have hpSb_law : P.map S = volume.withDensity (fun x => ENNReal.ofReal (pS_base x)) :=
    base_law S pS_base hS_meas hS_ac hpSb_def
  -- base second moments (from h_mom on P, transported through the law)
  have base_mom : ∀ (V : Ω → ℝ) (p : ℝ → ℝ), Measurable V →
      P.map V = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
      (∀ x, 0 ≤ p x) → Measurable p →
      Integrable (fun ω => (V ω) ^ 2) P →
      Integrable (fun y => y ^ 2 * p y) volume :=
    fun V p hV hlaw hp_nn hp_meas hmom =>
      integrable_sq_mul_of_map_eq_withDensity_ofReal P V p hV hlaw hp_nn hp_meas hmom
  have hpXb_mom : Integrable (fun y => y ^ 2 * pX_base y) volume :=
    base_mom X pX_base hX hpXb_law hpXb_nn hpXb_meas h_mom_X
  have hpYb_mom : Integrable (fun y => y ^ 2 * pY_base y) volume :=
    base_mom Y pY_base hY hpYb_law hpYb_nn hpYb_meas h_mom_Y
  have hpSb_mom : Integrable (fun y => y ^ 2 * pS_base y) volume := by
    have h_mom_S : Integrable (fun ω => (S ω) ^ 2) P := by
      have hX_memLp : MemLp X 2 P :=
        (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
      have hY_memLp : MemLp Y 2 P :=
        (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
      have hS_memLp : MemLp S 2 P := by rw [hS_def]; exact hX_memLp.add hY_memLp
      simpa using hS_memLp.integrable_sq
    exact base_mom S pS_base hS_meas hpSb_law hpSb_nn hpSb_meas h_mom_S
  -- ===== the three smoothing density witnesses =====
  set pXt : ℝ → ℝ := InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX_base
    (gaussianPDFReal 0 ⟨t, ht.le⟩) with hpXt_def
  set pYt : ℝ → ℝ := InformationTheory.Shannon.EPIConvDensity.convDensityAdd pY_base
    (gaussianPDFReal 0 ⟨t, ht.le⟩) with hpYt_def
  set pSt : ℝ → ℝ := InformationTheory.Shannon.EPIConvDensity.convDensityAdd pS_base
    (gaussianPDFReal 0 ⟨2 * t, by positivity⟩) with hpSt_def
  -- ===== withDensity links (via `pPath_eq_convDensityAdd` + `withDensity_rnDeriv_eq`) =====
  -- single-arm link helper: `V_path = U + √s·Zw`, `Zw ~ N(0,v_Z)`, base density `p_base` of U.
  have path_law : ∀ (U Zw : Ω → ℝ) (p_base : ℝ → ℝ) (v_Z : ℝ≥0),
      Measurable U → Measurable Zw → IndepFun U Zw P → 0 < v_Z →
      P.map Zw = gaussianReal 0 v_Z → (∀ x, 0 ≤ p_base x) → Measurable p_base →
      P.map U = volume.withDensity (fun x => ENNReal.ofReal (p_base x)) →
      (P.map (fun ω => U ω + Real.sqrt t * Zw ω)) ≪ volume →
      P.map (fun ω => U ω + Real.sqrt t * Zw ω)
        = volume.withDensity (fun x => ENNReal.ofReal
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd p_base
              (gaussianPDFReal 0 ⟨t * (v_Z : ℝ), by positivity⟩) x)) :=
    fun U Zw p_base v_Z hU hZw hUZw hv_Z hZw_law hp_nn hp_meas hp_law hpath_ac =>
      map_smoothed_eq_withDensity_convDensityAdd P U Zw p_base v_Z hU hZw hUZw hv_Z hZw_law
        hp_nn hp_meas hp_law ht hpath_ac
  -- Xt: `v_Z = 1`, variance witness `⟨t·1,_⟩` collapses to `⟨t,_⟩`.
  have hpXt_law : P.map Xt = volume.withDensity (fun x => ENNReal.ofReal (pXt x)) := by
    have h := path_law X Z_X pX_base 1 hX hZX hX_ZX one_pos hZX_law hpXb_nn hpXb_meas hpXb_law
      (by simpa [hXt_def] using hXt_ac)
    have hvc : (⟨t * ((1 : ℝ≥0) : ℝ), by positivity⟩ : ℝ≥0) = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply NNReal.eq; show t * ((1 : ℝ≥0) : ℝ) = t; simp
    rw [hvc] at h
    simpa [hXt_def, hpXt_def] using h
  have hpYt_law : P.map Yt = volume.withDensity (fun x => ENNReal.ofReal (pYt x)) := by
    have h := path_law Y Z_Y pY_base 1 hY hZY hY_ZY one_pos hZY_law hpYb_nn hpYb_meas hpYb_law
      (by simpa [hYt_def] using hYt_ac)
    have hvc : (⟨t * ((1 : ℝ≥0) : ℝ), by positivity⟩ : ℝ≥0) = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply NNReal.eq; show t * ((1 : ℝ≥0) : ℝ) = t; simp
    rw [hvc] at h
    simpa [hYt_def, hpYt_def] using h
  -- sum: `Xt + Yt = S + √t·W`, `W ~ N(0,2)`, variance witness `⟨t·2,_⟩` collapses to `⟨2t,_⟩`.
  have hsum_ac : (P.map (fun ω => S ω + Real.sqrt t * W ω)) ≪ volume := by
    rw [← hsum_eq]
    have hindep : IndepFun Xt Yt P := hXtYt_indep
    have := map_add_absolutelyContinuous Xt Yt P hXt_meas hYt_meas hindep hXt_ac
    simpa using this
  have hpSt_law : P.map (fun ω => Xt ω + Yt ω)
      = volume.withDensity (fun x => ENNReal.ofReal (pSt x)) := by
    have h := path_law S W pS_base 2 hS_meas hW_meas hS_W_indep (by norm_num) hW_law
      hpSb_nn hpSb_meas hpSb_law hsum_ac
    have hvc : (⟨t * ((2 : ℝ≥0) : ℝ), by positivity⟩ : ℝ≥0) = (⟨2 * t, by positivity⟩ : ℝ≥0) := by
      apply NNReal.eq; show t * ((2 : ℝ≥0) : ℝ) = 2 * t; push_cast; ring
    rw [hvc] at h
    rw [hsum_eq]
    simpa [hpSt_def] using h
  -- ===== regularity of the three smoothing densities =====
  have hreg_pXt : FisherInfoV2.IsRegularDensityV2 pXt :=
    InformationTheory.Shannon.EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian
      pX_base ht hpXb_nn hpXb_meas hpXb_int hpXb_mass_pos
  have hreg_pYt : FisherInfoV2.IsRegularDensityV2 pYt :=
    InformationTheory.Shannon.EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian
      pY_base ht hpYb_nn hpYb_meas hpYb_int hpYb_mass_pos
  have hreg_pSt : FisherInfoV2.IsRegularDensityV2 pSt :=
    InformationTheory.Shannon.EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian
      pS_base (by positivity) hpSb_nn hpSb_meas hpSb_int hpSb_mass_pos
  -- ===== nonneg / meas / int of the three smoothing densities =====
  have hpXt_nn : ∀ x, 0 ≤ pXt x := fun x =>
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_nonneg _ _ hpXb_nn
      (gaussianPDFReal_nonneg _ _) x
  have hpYt_nn : ∀ x, 0 ≤ pYt x := fun x =>
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_nonneg _ _ hpYb_nn
      (gaussianPDFReal_nonneg _ _) x
  have hpSt_nn : ∀ x, 0 ≤ pSt x := fun x =>
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_nonneg _ _ hpSb_nn
      (gaussianPDFReal_nonneg _ _) x
  have hpXt_meas : Measurable pXt :=
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_measurable _ _ hpXb_meas
      (measurable_gaussianPDFReal _ _)
  have hpYt_meas : Measurable pYt :=
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_measurable _ _ hpYb_meas
      (measurable_gaussianPDFReal _ _)
  have hpSt_meas : Measurable pSt :=
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_measurable _ _ hpSb_meas
      (measurable_gaussianPDFReal _ _)
  have hpXt_int : Integrable pXt volume :=
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integrable _ _ hpXb_int hpXb_meas
      (integrable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _)
  have hpYt_int : Integrable pYt volume :=
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integrable _ _ hpYb_int hpYb_meas
      (integrable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _)
  have hpSt_int : Integrable pSt volume :=
    InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integrable _ _ hpSb_int hpSb_meas
      (integrable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _)
  -- ===== normalization ∫ = 1 of the three smoothing densities =====
  have hgt_norm : (∫ x, gaussianPDFReal 0 ⟨t, ht.le⟩ x ∂volume) = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by
      intro hc; exact ht.ne' (congrArg NNReal.toReal hc))
  have hg2t_norm : (∫ x, gaussianPDFReal 0 ⟨2 * t, by positivity⟩ x ∂volume) = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by
      intro hc; exact (by positivity : (0:ℝ) < 2 * t).ne' (congrArg NNReal.toReal hc))
  have hpXt_norm : (∫ x, pXt x ∂volume) = 1 := by
    rw [hpXt_def, InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integral_eq _ _
      hpXb_int (integrable_gaussianPDFReal _ _), hpXb_mass, hgt_norm, one_mul]
  have hpYt_norm : (∫ x, pYt x ∂volume) = 1 := by
    rw [hpYt_def, InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integral_eq _ _
      hpYb_int (integrable_gaussianPDFReal _ _), hpYb_mass, hgt_norm, one_mul]
  have hpSt_norm : (∫ x, pSt x ∂volume) = 1 := by
    rw [hpSt_def, InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integral_eq _ _
      hpSb_int (integrable_gaussianPDFReal _ _), hpSb_mass, hg2t_norm, one_mul]
  -- ===== Blachman readiness (via the bridge) =====
  have hready_pXt : ∀ v : ℝ≥0, v ≠ 0 →
      EPIBlachmanDensity.IsBlachmanConvReady pXt (gaussianPDFReal 0 v) := fun v hv =>
    isBlachmanConvReady_convGaussian_gaussian pX_base ht hpXb_nn hpXb_meas hpXb_int
      hpXb_mass_pos hpXb_mass hv
  have hready_pYt : ∀ v : ℝ≥0, v ≠ 0 →
      EPIBlachmanDensity.IsBlachmanConvReady pYt (gaussianPDFReal 0 v) := fun v hv =>
    isBlachmanConvReady_convGaussian_gaussian pY_base ht hpYb_nn hpYb_meas hpYb_int
      hpYb_mass_pos hpYb_mass hv
  have hready_pSt : ∀ v : ℝ≥0, v ≠ 0 →
      EPIBlachmanDensity.IsBlachmanConvReady pSt (gaussianPDFReal 0 v) := fun v hv =>
    isBlachmanConvReady_convGaussian_gaussian pS_base (by positivity) hpSb_nn hpSb_meas hpSb_int
      hpSb_mass_pos hpSb_mass hv
  -- ===== finite entropy of the three smoothing densities =====
  have hent_pXt : Integrable (fun x => Real.negMulLog (pXt x)) volume := by
    rw [hpXt_def]
    exact InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
      hpXb_nn hpXb_meas hpXb_int hpXb_mass hpXb_mom ht
  have hent_pYt : Integrable (fun x => Real.negMulLog (pYt x)) volume := by
    rw [hpYt_def]
    exact InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
      hpYb_nn hpYb_meas hpYb_int hpYb_mass hpYb_mom ht
  have hent_pSt : Integrable (fun x => Real.negMulLog (pSt x)) volume := by
    rw [hpSt_def]
    exact InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
      hpSb_nn hpSb_meas hpSb_int hpSb_mass hpSb_mom (by positivity)
  -- ===== second moments of the three smoothing densities =====
  have hpXt_mom : Integrable (fun y => y ^ 2 * pXt y) volume := by
    rw [hpXt_def]
    exact InformationTheory.Shannon.convDensityAdd_gaussian_sq_integrable
      hpXb_nn hpXb_meas hpXb_int hpXb_mom ht
  have hpYt_mom : Integrable (fun y => y ^ 2 * pYt y) volume := by
    rw [hpYt_def]
    exact InformationTheory.Shannon.convDensityAdd_gaussian_sq_integrable
      hpYb_nn hpYb_meas hpYb_int hpYb_mom ht
  have hpSt_mom : Integrable (fun y => y ^ 2 * pSt y) volume := by
    rw [hpSt_def]
    exact InformationTheory.Shannon.convDensityAdd_gaussian_sq_integrable
      hpSb_nn hpSb_meas hpSb_int hpSb_mom (by positivity)
  -- ===== assemble the explicit density-form EPI at X := Xt, Y := Yt =====
  have hmain := entropy_power_inequality_of_density_explicit P Xt Yt hXt_meas hYt_meas hXtYt_indep
    hXt_ac hYt_ac h_mom_Xt h_mom_Yt
    pXt hpXt_nn hpXt_meas hpXt_int hpXt_law hpXt_mom hreg_pXt hpXt_norm hready_pXt hent_pXt
    pYt hpYt_nn hpYt_meas hpYt_int hpYt_law hpYt_mom hreg_pYt hpYt_norm hready_pYt hent_pYt
    pSt hpSt_nn hpSt_meas hpSt_int hpSt_law hpSt_mom hreg_pSt hpSt_norm hready_pSt hent_pSt
  -- rewrite Xt/Yt back to the brief's explicit `fun ω => …` form.
  simpa only [hXt_def, hYt_def] using hmain

/-- **Finite-variance classical EPI (Real, no noise)**.

The base-level entropy-power inequality `N(X+Y) ≥ N(X) + N(Y)` for absolutely
continuous, finite-variance, independent `X, Y` — with NO smoothing noise. Obtained
by lifting to a 3-noise space, instantiating the per-`t` smoothing EPI
`entropyPower_smoothed_epi_perT` at every `t > 0`, and pushing `t → 0⁺` via heat-flow
endpoint continuity (`heatFlowEntropyPower_continuousWithinAt_zero`) with
`le_of_tendsto_of_tendsto`.

The entropy-integrability hypotheses `hX_ent`/`hY_ent`/`hent_sum` are regularity
preconditions (finite differential entropy of the marginals/sum); they do NOT encode
the EPI conclusion (load-bearing-free).
@audit:ok -/
theorem entropy_power_add_ge_of_finite_variance
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω) ^ 2) P)
    (hX_ent : Integrable (fun x => Real.negMulLog (((P.map X).rnDeriv volume x).toReal)) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog (((P.map Y).rnDeriv volume x).toReal)) volume)
    (hent_sum : Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- Reduce to a 3-noise lift space EPI.
  refine entropy_power_inequality_via_lift3 P X Y hX hY ?_
  set lift : Measure (Ω × ℝ × ℝ × ℝ) := liftMeasure3 P with hlift
  set X' : Ω × ℝ × ℝ × ℝ → ℝ := fun p => X p.1 with hX'
  set Y' : Ω × ℝ × ℝ × ℝ → ℝ := fun p => Y p.1 with hY'
  set ZX : Ω × ℝ × ℝ × ℝ → ℝ := fun p => p.2.1 with hZX
  set ZY : Ω × ℝ × ℝ × ℝ → ℝ := fun p => p.2.2.1 with hZY
  set Z : Ω × ℝ × ℝ × ℝ → ℝ := fun p => p.2.2.2 with hZ
  haveI hlift_prob : IsProbabilityMeasure lift := by rw [hlift]; infer_instance
  -- measurability of lift functions
  have hX'_meas : Measurable X' := hX.comp measurable_fst
  have hY'_meas : Measurable Y' := hY.comp measurable_fst
  have hZX_meas : Measurable ZX := measurable_fst.comp measurable_snd
  have hZY_meas : Measurable ZY := (measurable_fst.comp measurable_snd).comp measurable_snd
  have hZ_meas : Measurable Z := (measurable_snd.comp measurable_snd).comp measurable_snd
  -- law transport: lift.map (f∘fst) = P.map f
  have hmap_X' : lift.map X' = P.map X := by
    rw [hlift, hX', show (fun p : Ω × ℝ × ℝ × ℝ => X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  have hmap_Y' : lift.map Y' = P.map Y := by
    rw [hlift, hY', show (fun p : Ω × ℝ × ℝ × ℝ => Y p.1) = Y ∘ Prod.fst from rfl,
      ← Measure.map_map hY measurable_fst, measurePreserving_fst.map_eq]
  have hmap_sum' : lift.map (fun p => X' p + Y' p) = P.map (fun ω => X ω + Y ω) := by
    rw [hlift, hX', hY',
      show (fun p : Ω × ℝ × ℝ × ℝ => X p.1 + Y p.1) = (fun ω => X ω + Y ω) ∘ Prod.fst from rfl,
      ← Measure.map_map (hX.add hY) measurable_fst, measurePreserving_fst.map_eq]
  -- a.c. transport
  have hX'_ac : (lift.map X') ≪ volume := by rw [hmap_X']; exact hX_ac
  have hY'_ac : (lift.map Y') ≪ volume := by rw [hmap_Y']; exact hY_ac
  have hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  -- second moment of X+Y on base P
  have h_mom_XY : Integrable (fun ω => (X ω + Y ω) ^ 2) P := by
    have hX_memLp : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
    have hY_memLp : MemLp Y 2 P :=
      (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
    have hS_memLp : MemLp (fun ω => X ω + Y ω) 2 P := hX_memLp.add hY_memLp
    simpa using hS_memLp.integrable_sq
  -- moment transport (to the 3-noise lift)
  have h_mom_X' : Integrable (fun p => (X' p) ^ 2) lift := by
    rw [hlift, hX']
    exact h_mom_X.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  have h_mom_Y' : Integrable (fun p => (Y' p) ^ 2) lift := by
    rw [hlift, hY']
    exact h_mom_Y.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  -- noise laws
  have hZX_law : lift.map ZX = gaussianReal 0 1 := by
    rw [hlift, hZX,
      show (fun p : Ω × ℝ × ℝ × ℝ => p.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_fst.map_eq]
  have hZY_law : lift.map ZY = gaussianReal 0 1 := by
    rw [hlift, hZY,
      show (fun p : Ω × ℝ × ℝ × ℝ => p.2.2.1)
        = Prod.fst ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq,
      measurePreserving_fst.map_eq]
  -- 4-tuple joint independence on the lift
  have h_iIndep : iIndepFun ![X', Y', ZX, ZY] lift := by
    have haem : ∀ i, AEMeasurable (![X', Y', ZX, ZY] i) lift := by
      intro i; fin_cases i
      · exact hX'_meas.aemeasurable
      · exact hY'_meas.aemeasurable
      · exact hZX_meas.aemeasurable
      · exact hZY_meas.aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map haem]
    symm
    refine Measure.pi_eq (fun s hs => ?_)
    have hjoint_meas : Measurable (fun ω i => ![X', Y', ZX, ZY] i ω) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      fin_cases i
      · exact hX'_meas
      · exact hY'_meas
      · exact hZX_meas
      · exact hZY_meas
    rw [Measure.map_apply hjoint_meas (MeasurableSet.univ_pi hs)]
    have hm0 : lift.map (![X', Y', ZX, ZY] 0) = P.map X := by simpa using hmap_X'
    have hm1 : lift.map (![X', Y', ZX, ZY] 1) = P.map Y := by simpa using hmap_Y'
    have hm2 : lift.map (![X', Y', ZX, ZY] 2) = gaussianReal 0 1 := by simpa using hZX_law
    have hm3 : lift.map (![X', Y', ZX, ZY] 3) = gaussianReal 0 1 := by simpa using hZY_law
    rw [Fin.prod_univ_four, hm0, hm1, hm2, hm3]
    have hpre : (fun ω i => ![X', Y', ZX, ZY] i ω) ⁻¹' (Set.univ.pi s)
        = (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) ×ˢ (s 2 ×ˢ (s 3 ×ˢ Set.univ)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Set.mem_inter_iff,
        Set.mem_univ, and_true]
      constructor
      · intro h
        exact ⟨⟨h 0, h 1⟩, h 2, h 3⟩
      · intro h i
        fin_cases i
        · exact h.1.1
        · exact h.1.2
        · exact h.2.1
        · exact h.2.2
    rw [hpre, hlift, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, measure_univ,
      mul_one]
    have hAprod : P (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) = P.map X (s 0) * P.map Y (s 1) := by
      rw [Measure.map_apply hX (hs 0), Measure.map_apply hY (hs 1)]
      exact (indepFun_iff_measure_inter_preimage_eq_mul.1 hXY) (s 0) (s 1) (hs 0) (hs 1)
    rw [hAprod]
    ring
  -- per-`t` smoothing EPI: instantiate `entropyPower_smoothed_epi_perT` on the lift.
  have h_perT : ∀ t : ℝ, 0 < t →
      entropyPower (lift.map (fun p => (X' p + Real.sqrt t * ZX p)
        + (Y' p + Real.sqrt t * ZY p)))
        ≥ entropyPower (lift.map (fun p => X' p + Real.sqrt t * ZX p))
          + entropyPower (lift.map (fun p => Y' p + Real.sqrt t * ZY p)) := by
    intro t ht
    exact entropyPower_smoothed_epi_perT lift X' Y' ZX ZY hX'_meas hY'_meas hZX_meas hZY_meas
      hX'_ac hY'_ac h_mom_X' h_mom_Y' hZX_law hZY_law h_iIndep ht
  -- endpoint density witnesses.
  -- generic builder (variable noise law / variance), mirroring the density-form `endpt_of`.
  have endpt_of : ∀ (W : Ω → ℝ) (W' : Ω × ℝ × ℝ × ℝ → ℝ) (Zw : Ω × ℝ × ℝ × ℝ → ℝ)
      (vZ : ℝ≥0),
      Measurable W → Measurable W' → Measurable Zw → IndepFun W' Zw lift →
      0 < vZ → lift.map Zw = gaussianReal 0 vZ → lift.map W' = P.map W →
      (P.map W) ≪ volume → Integrable (fun ω => (W ω) ^ 2) P →
      Integrable (fun x => Real.negMulLog (((P.map W).rnDeriv volume x).toReal)) volume →
      IsHeatFlowEndpointRegular W' Zw lift :=
    fun W W' Zw vZ hW hW' hZw hWZ hvZ hZw_law hmap hac hmom hent =>
      isHeatFlowEndpointRegular_of_map_eq_rnDeriv P lift W W' Zw vZ hW hW' hZw hWZ hvZ
        hZw_law hmap hac hmom hent
  -- pairwise independences needed by the endpoint builder.
  have hf_meas : ∀ i, Measurable (![X', Y', ZX, ZY] i) := by
    intro i; fin_cases i
    · exact hX'_meas
    · exact hY'_meas
    · exact hZX_meas
    · exact hZY_meas
  have hXZX : IndepFun X' ZX lift := by
    have := h_iIndep.indepFun (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
    simpa using this
  have hYZY : IndepFun Y' ZY lift := by
    have := h_iIndep.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    simpa using this
  have hZX_ZY : IndepFun ZX ZY lift := by
    have := h_iIndep.indepFun (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    simpa using this
  -- sum endpoint data (v_Z = 2): W := ZX + ZY ~ N(0,2), (X'+Y') ⊥ W.
  set Wsum : Ω × ℝ × ℝ × ℝ → ℝ := fun p => ZX p + ZY p with hWsum
  have hWsum_meas : Measurable Wsum := hZX_meas.add hZY_meas
  have hWsum_law : lift.map Wsum = gaussianReal 0 2 := by
    have := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
      (P := lift) hZX_ZY hZX_law hZY_law
    rw [hWsum, show (fun p => ZX p + ZY p) = ZX + ZY from rfl, this]; norm_num
  have hXYsum_W : IndepFun (fun p => X' p + Y' p) Wsum lift := by
    have hpair : IndepFun (fun a => (X' a, Y' a)) (fun a => (ZX a, ZY a)) lift := by
      have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 1 2 3
        (by decide) (by decide) (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun q : ℝ × ℝ => q.1 + q.2) := by fun_prop
    have := hpair.comp hsum hsum
    simpa [Function.comp, hWsum] using this
  -- entropy integrability transported to the lift's marginals.
  have hent_X' : Integrable
      (fun x => Real.negMulLog (((P.map X).rnDeriv volume x).toReal)) volume := hX_ent
  have hent_Y' : Integrable
      (fun x => Real.negMulLog (((P.map Y).rnDeriv volume x).toReal)) volume := hY_ent
  have hent_XY' : Integrable
      (fun x => Real.negMulLog (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      volume := hent_sum
  -- build the three endpoint regularities.
  have h_endpt_X : IsHeatFlowEndpointRegular X' ZX lift :=
    endpt_of X X' ZX 1 hX hX'_meas hZX_meas hXZX one_pos hZX_law hmap_X' hX_ac h_mom_X hent_X'
  have h_endpt_Y : IsHeatFlowEndpointRegular Y' ZY lift :=
    endpt_of Y Y' ZY 1 hY hY'_meas hZY_meas hYZY one_pos hZY_law hmap_Y' hY_ac h_mom_Y hent_Y'
  have h_endpt_sum : IsHeatFlowEndpointRegular (fun p => X' p + Y' p) Wsum lift :=
    endpt_of (fun ω => X ω + Y ω) (fun p => X' p + Y' p) Wsum 2 (hX.add hY)
      (hX'_meas.add hY'_meas) hWsum_meas hXYsum_W (by norm_num) hWsum_law hmap_sum' hXY_ac
      h_mom_XY hent_XY'
  -- endpoint continuity of the three heat-flow entropy-power paths at `t = 0⁺`.
  have hcont_X : ContinuousWithinAt
      (fun t : ℝ => entropyPower (lift.map (fun p => X' p + Real.sqrt t * ZX p)))
      (Set.Ioi (0 : ℝ)) 0 :=
    heatFlowEntropyPower_continuousWithinAt_zero X' ZX lift h_endpt_X
  have hcont_Y : ContinuousWithinAt
      (fun t : ℝ => entropyPower (lift.map (fun p => Y' p + Real.sqrt t * ZY p)))
      (Set.Ioi (0 : ℝ)) 0 :=
    heatFlowEntropyPower_continuousWithinAt_zero Y' ZY lift h_endpt_Y
  have hcont_sum : ContinuousWithinAt
      (fun t : ℝ => entropyPower (lift.map (fun p => (X' p + Y' p) + Real.sqrt t * Wsum p)))
      (Set.Ioi (0 : ℝ)) 0 :=
    heatFlowEntropyPower_continuousWithinAt_zero (fun p => X' p + Y' p) Wsum lift h_endpt_sum
  -- value at `t = 0`: `√0 = 0`, so the path collapses to the base.
  have hval0 : ∀ (V Zw : Ω × ℝ × ℝ × ℝ → ℝ),
      (fun ω => V ω + Real.sqrt (0 : ℝ) * Zw ω) = V := by
    intro V Zw; funext ω; simp
  -- tendsto of the three endpoint paths.
  have htend_X : Filter.Tendsto
      (fun t : ℝ => entropyPower (lift.map (fun p => X' p + Real.sqrt t * ZX p)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (entropyPower (lift.map X'))) := by
    have := hcont_X.tendsto
    rwa [show (fun p => X' p + Real.sqrt (0 : ℝ) * ZX p) = X' from hval0 X' ZX] at this
  have htend_Y : Filter.Tendsto
      (fun t : ℝ => entropyPower (lift.map (fun p => Y' p + Real.sqrt t * ZY p)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (entropyPower (lift.map Y'))) := by
    have := hcont_Y.tendsto
    rwa [show (fun p => Y' p + Real.sqrt (0 : ℝ) * ZY p) = Y' from hval0 Y' ZY] at this
  have htend_sum : Filter.Tendsto
      (fun t : ℝ => entropyPower (lift.map (fun p => (X' p + Y' p) + Real.sqrt t * Wsum p)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (entropyPower (lift.map (fun p => X' p + Y' p)))) := by
    have := hcont_sum.tendsto
    rwa [show (fun p => (X' p + Y' p) + Real.sqrt (0 : ℝ) * Wsum p) = fun p => X' p + Y' p
      from hval0 (fun p => X' p + Y' p) Wsum] at this
  -- RHS sum tendsto.
  have htend_rhs : Filter.Tendsto
      (fun t : ℝ => entropyPower (lift.map (fun p => X' p + Real.sqrt t * ZX p))
        + entropyPower (lift.map (fun p => Y' p + Real.sqrt t * ZY p)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (entropyPower (lift.map X') + entropyPower (lift.map Y'))) :=
    htend_X.add htend_Y
  -- the per-`t` sum path coincides with the per-`t` smoothing-sum path (funext + ring).
  have hsum_path_eq : (fun t : ℝ => entropyPower
        (lift.map (fun p => (X' p + Y' p) + Real.sqrt t * Wsum p)))
      = (fun t : ℝ => entropyPower
        (lift.map (fun p => (X' p + Real.sqrt t * ZX p) + (Y' p + Real.sqrt t * ZY p)))) := by
    funext t
    congr 1
    congr 1
    funext p
    simp only [hWsum]; ring
  -- assemble: `le_of_tendsto_of_tendsto` on `𝓝[Ioi 0] 0` with the per-`t` inequality.
  have heventually : (fun t : ℝ => entropyPower (lift.map (fun p => X' p + Real.sqrt t * ZX p))
        + entropyPower (lift.map (fun p => Y' p + Real.sqrt t * ZY p)))
      ≤ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => entropyPower
        (lift.map (fun p => (X' p + Real.sqrt t * ZX p) + (Y' p + Real.sqrt t * ZY p)))) := by
    refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
    exact h_perT t ht
  have hfinal : entropyPower (lift.map X') + entropyPower (lift.map Y')
      ≤ entropyPower (lift.map (fun p => X' p + Y' p)) := by
    refine le_of_tendsto_of_tendsto htend_rhs ?_ heventually
    rw [hsum_path_eq] at htend_sum
    exact htend_sum
  exact hfinal

/-- **Finite-variance classical EPI (ext, ℝ≥0∞)**.

The `entropyPowerExt` (ℝ≥0∞-valued) version of `entropy_power_add_ge_of_finite_variance`.
Under the same hypotheses, `Nₑ(X+Y) ≥ Nₑ(X) + Nₑ(Y)` in `ℝ≥0∞`. Obtained by lifting the
Real inequality through `entropyPowerExt_of_ac_integrable`
(`entropyPowerExt μ = ENNReal.ofReal (entropyPower μ)` for a.c. + finite-entropy `μ`) and
`ENNReal.ofReal_add` (both entropy powers nonneg).
@audit:ok -/
theorem entropyPowerExt_add_ge_of_finite_variance
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω) ^ 2) P)
    (hX_ent : Integrable (fun x => Real.negMulLog (((P.map X).rnDeriv volume x).toReal)) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog (((P.map Y).rnDeriv volume x).toReal)) volume)
    (hent_sum : Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  classical
  -- a.c. of the sum law.
  have hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  -- for an a.c. + finite-entropy measure, `entropyPowerExt μ = ofReal (entropyPower μ)`.
  have key : ∀ (μ : Measure ℝ), μ ≪ volume →
      Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume →
      entropyPowerExt μ = ENNReal.ofReal (entropyPower μ) := by
    intro μ hac hint
    rw [entropyPowerExt_of_ac_integrable hac hint]
    rfl
  have hX_e := key (P.map X) hX_ac hX_ent
  have hY_e := key (P.map Y) hY_ac hY_ent
  have hXY_e := key (P.map (fun ω => X ω + Y ω)) hXY_ac hent_sum
  -- the Real EPI from D1.
  have hreal := entropy_power_add_ge_of_finite_variance P X Y hX hY hXY hX_ac hY_ac
    h_mom_X h_mom_Y hX_ent hY_ent hent_sum
  -- lift the Real inequality through `ofReal`.
  rw [ge_iff_le, hX_e, hY_e, hXY_e,
    ← ENNReal.ofReal_add (entropyPower_nonneg _) (entropyPower_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## Infinite-variance a.c. classical EPI

The infinite-variance case `entropyPowerExt_add_ge_infinite_variance` is established
in `EPIInfiniteVarianceCapstone.lean` (compact-support truncation + finite-variance
EPI + Gibbs + DCT). It cannot reside here because this file is upstream of the
truncation module (import cycle). -/

end InformationTheory.Shannon.EPICase1SmoothingLimit
