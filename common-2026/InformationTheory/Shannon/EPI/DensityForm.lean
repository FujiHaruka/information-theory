import InformationTheory.Shannon.EPI.Case1.RatioLimit
import InformationTheory.Shannon.EPI.NoiseExtension
import InformationTheory.Shannon.EPI.Stam.FisherCoupling
import InformationTheory.Shannon.EPI.Conv.DensityRegular
import InformationTheory.Shannon.EPI.Blachman.GeneralDensity
import InformationTheory.Shannon.EPI.Conv.DensityAssoc
import InformationTheory.Shannon.EPI.Conv.DensityNormalization
import InformationTheory.Shannon.EPI.Case1.TwoTime
import InformationTheory.Shannon.EPI.Stam.SupplyTwoTime
import InformationTheory.Meta.EntryPoint

/-!
# Density-form entropy power inequality

`entropy_power_inequality_of_density`: EPI for absolutely continuous distributions with
finite second moment and regular densities, proved via a 3-noise lift and two-time terminal.

## Main statements

- `entropy_power_inequality_of_density`: EPI under explicit density regularity hypotheses.

## Implementation notes

The proof lifts the base space `(Ω, P)` to `(Ω × ℝ × ℝ × ℝ, liftMeasure3 P)` and
introduces three independent unit-noise variables `Z_X`, `Z_Y`, `Z`. Smoothing the sum
with a separate unit noise `Z` (rather than using `Z_X + Z_Y ~ 𝒩(0,2)`) ensures that
`isDeBruijnRegularityHyp_of_methodX_unitnoise` (which requires `gaussianReal 0 1`) applies
to the sum-instance as well.
-/

namespace InformationTheory.Shannon.EPIDensityForm

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1RatioLimit
open InformationTheory.Shannon.EPICase1TwoTime
open InformationTheory.Shannon.EPINoiseExtension
open scoped ENNReal NNReal

noncomputable def isHeatFlowEndpointRegular_of_canonical_rnDeriv
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (W : Ω → ℝ) (W' : α → ℝ) (Zw : α → ℝ)
    (hW : Measurable W) (hW' : Measurable W') (hZw : Measurable Zw)
    (hWZ : IndepFun W' Zw μ) (hZw_law : μ.map Zw = gaussianReal 0 1)
    (hmap : μ.map W' = P.map W) (hac : (P.map W) ≪ volume)
    (hmom : Integrable (fun ω ↦ (W ω) ^ 2) P)
    (hent : Integrable (fun x ↦ Real.negMulLog (((P.map W).rnDeriv volume x).toReal)) volume) :
    IsHeatFlowEndpointRegular W' Zw μ := by
  set p : ℝ → ℝ := fun x ↦ ((P.map W).rnDeriv volume x).toReal with hp_def
  have hp_nn : ∀ x, 0 ≤ p x := fun x ↦ ENNReal.toReal_nonneg
  have hp_meas : Measurable p := ((P.map W).measurable_rnDeriv volume).ennreal_toReal
  have hp_law : μ.map W' = volume.withDensity (fun x ↦ ENNReal.ofReal (p x)) := by
    rw [hmap]
    have hfin : ∀ᵐ x ∂volume, (P.map W).rnDeriv volume x < ∞ :=
      Measure.rnDeriv_lt_top (P.map W) volume
    have hcongr : (fun x ↦ ENNReal.ofReal (p x)) =ᵐ[volume]
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
  have hp_mom : Integrable (fun y ↦ y ^ 2 * p y) volume := by
    have hsq_law : Integrable (fun y ↦ y ^ 2) (P.map W) := by
      rw [integrable_map_measure
        ((by fun_prop : Measurable (fun y : ℝ ↦ y ^ 2)).aestronglyMeasurable)
        hW.aemeasurable]
      simpa [Function.comp] using hmom
    rw [show P.map W = volume.withDensity (fun x ↦ ENNReal.ofReal (p x)) from
      hmap ▸ hp_law] at hsq_law
    rw [integrable_withDensity_iff_integrable_smul₀'
      hp_meas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)] at hsq_law
    refine hsq_law.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hp_nn x)]; ring
  exact
    { hX_meas := hW'
      hZ_meas := hZw
      hXZ_indep := hWZ
      v_Z := 1
      hv_Z_pos := one_pos
      hZ_law := hZw_law
      pX := p
      hpX_nn := hp_nn
      hpX_meas := hp_meas
      hpX_law := hp_law
      hpX_int := hp_int
      hpX_mass := hp_mass
      hpX_mom := hp_mom
      hpX_ent := hent }

lemma integral_sub_integral_sq_rescaled_path_le
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (A B : α → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : IndepFun A B μ) (h_mom_A : Integrable (fun p ↦ (A p) ^ 2) μ)
    (v_B : ℝ≥0) (hB_law : μ.map B = gaussianReal 0 v_B)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, (x - (∫ y, y ∂(μ.map (fun p ↦ A p / Real.sqrt t + B p)))) ^ 2
          ∂(μ.map (fun p ↦ A p / Real.sqrt t + B p)))
        ≤ ProbabilityTheory.variance A μ / t + (v_B : ℝ) := by
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  set Zt : α → ℝ := fun ω ↦ A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hW_meas : Measurable (fun ω ↦ Zt ω + B ω) := hZt_meas.add hB
  have hB_memLp : MemLp B 2 μ := by
    have hid : MemLp (id : ℝ → ℝ) 2 (μ.map B) := by
      rw [hB_law]; exact memLp_id_gaussianReal' 2 (by simp)
    have := (memLp_map_measure_iff (p := 2) (μ := μ) (g := (id : ℝ → ℝ))
      aestronglyMeasurable_id hB.aemeasurable).mp hid
    simpa [Function.comp] using this
  have hZt_sq : Integrable (fun ω ↦ (Zt ω)^2) μ := by
    have : (fun ω ↦ (Zt ω)^2) = (fun ω ↦ (1 / t) * (A ω)^2) := by
      funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
    rw [this]; exact h_mom_A.const_mul _
  have hZt_memLp : MemLp Zt 2 μ :=
    (memLp_two_iff_integrable_sq_norm hZt_meas.aestronglyMeasurable).mpr (by simpa using hZt_sq)
  have h_indep : IndepFun Zt B μ := by
    have : Zt = (fun a ↦ a / Real.sqrt t) ∘ A := by funext ω; rfl
    rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
  have hLHS : (∫ x, (x - (∫ y, y ∂(μ.map (fun ω ↦ Zt ω + B ω))))^2
        ∂(μ.map (fun ω ↦ Zt ω + B ω)))
      = ProbabilityTheory.variance (fun ω ↦ Zt ω + B ω) μ := by
    rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
    exact ProbabilityTheory.variance_id_map hW_meas.aemeasurable
  have hVarZt : ProbabilityTheory.variance Zt μ
      = (1 / t) * ProbabilityTheory.variance A μ := by
    have hZt_eq : Zt = fun ω ↦ (1 / Real.sqrt t) * A ω := by
      funext ω; simp only [hZt]; rw [div_eq_inv_mul, one_div]
    rw [hZt_eq, ProbabilityTheory.variance_const_mul]
    congr 1
    rw [div_pow, one_pow, Real.sq_sqrt ht.le]
  have hVarB : ProbabilityTheory.variance B μ = (v_B : ℝ) := by
    rw [← ProbabilityTheory.variance_id_map hB.aemeasurable, hB_law,
      ProbabilityTheory.variance_id_gaussianReal]
  have hVarSum : ProbabilityTheory.variance (fun ω ↦ Zt ω + B ω) μ
      = (1 / t) * ProbabilityTheory.variance A μ + (v_B : ℝ) := by
    rw [ProbabilityTheory.IndepFun.variance_fun_add hZt_memLp hB_memLp h_indep,
      hVarZt, hVarB]
  rw [hLHS, hVarSum, one_div, inv_mul_eq_div]

lemma rescaled_path_absolutelyContinuous_and_negMulLog_integrable
    {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (A B : α → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : IndepFun A B μ) (hA_ac : (μ.map A) ≪ volume)
    (h_mom_A : Integrable (fun p ↦ (A p) ^ 2) μ)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0) (hB_law : μ.map B = gaussianReal 0 v_B)
    {t : ℝ} (ht : 0 < t) :
    (μ.map (fun p ↦ A p / Real.sqrt t + B p)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((μ.map (fun p ↦ A p / Real.sqrt t + B p)).rnDeriv volume x).toReal)) volume := by
  set Zt : α → ℝ := fun ω ↦ A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hB_ac : (μ.map B) ≪ volume := by
    rw [hB_law]; exact gaussianReal_absolutelyContinuous 0 hv_B
  have h_indep : IndepFun Zt B μ := by
    have : Zt = (fun a ↦ a / Real.sqrt t) ∘ A := by funext ω; rfl
    rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
  have hμ_ac : (μ.map (fun ω ↦ Zt ω + B ω)) ≪ volume := by
    have hWac : (μ.map (fun ω ↦ B ω + Zt ω)) ≪ volume :=
      map_add_absolutelyContinuous B Zt μ hB hZt_meas h_indep.symm hB_ac
    have h_path : (fun ω ↦ Zt ω + B ω) = (fun ω ↦ B ω + Zt ω) := by funext ω; ring
    rw [h_path]; exact hWac
  refine ⟨hμ_ac, ?_⟩
  have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
  obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
    rescaledInput_density_witness A μ hA hA_ac h_mom_A ht
  have hgconv : InformationTheory.Shannon.FisherInfo.gaussianConvolution Zt B 1
      = fun ω ↦ Zt ω + B ω := by
    funext ω
    simp only [InformationTheory.Shannon.FisherInfo.gaussianConvolution,
      Real.sqrt_one, one_mul]
  have h_path_rnDeriv : (μ.map (fun ω ↦ Zt ω + B ω)).rnDeriv volume
      =ᵐ[volume] fun z ↦ ENNReal.ofReal
        (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
    have := InformationTheory.Shannon.FisherInfo.pPath_eq_convDensityAdd
      Zt B hZt_meas hB h_indep v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
      (s := 1) one_pos
    rwa [hgconv] at this
  have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B := by
    apply NNReal.coe_injective; show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul]
  have h_asset : Integrable (fun x ↦
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
    integral_nonneg fun y ↦ mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
  rw [hx, ENNReal.toReal_ofReal hcd_nn]

lemma liftMeasure3_map_fst_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    (liftMeasure3 P).map (fun p ↦ X p.1) = P.map X ∧
      (liftMeasure3 P).map (fun p ↦ Y p.1) = P.map Y ∧
      (liftMeasure3 P).map (fun p ↦ X p.1 + Y p.1) = P.map (fun ω ↦ X ω + Y ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  · rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ Y p.1) = Y ∘ Prod.fst from rfl,
      ← Measure.map_map hY measurable_fst, measurePreserving_fst.map_eq]
  · rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ X p.1 + Y p.1) = (fun ω ↦ X ω + Y ω) ∘ Prod.fst from rfl,
      ← Measure.map_map (hX.add hY) measurable_fst, measurePreserving_fst.map_eq]

lemma liftMeasure3_noise_laws
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] :
    (liftMeasure3 P).map (fun p : Ω × ℝ × ℝ × ℝ ↦ p.2.1) = gaussianReal 0 1 ∧
      (liftMeasure3 P).map (fun p : Ω × ℝ × ℝ × ℝ ↦ p.2.2.1) = gaussianReal 0 1 ∧
      (liftMeasure3 P).map (fun p : Ω × ℝ × ℝ × ℝ ↦ p.2.2.2) = gaussianReal 0 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ p.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_fst.map_eq]
  · rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ p.2.2.1) = Prod.fst ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq,
      measurePreserving_fst.map_eq]
  · rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ p.2.2.2) = Prod.snd ∘ Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd (measurable_snd.comp measurable_snd),
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq,
      measurePreserving_snd.map_eq]

lemma liftMeasure3_moment_transport
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (h_mom_X : Integrable (fun ω ↦ (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω ↦ (Y ω) ^ 2) P) :
    Integrable (fun ω ↦ (X ω + Y ω) ^ 2) P ∧
      Integrable (fun p : Ω × ℝ × ℝ × ℝ ↦ (X p.1) ^ 2) (liftMeasure3 P) ∧
      Integrable (fun p : Ω × ℝ × ℝ × ℝ ↦ (Y p.1) ^ 2) (liftMeasure3 P) ∧
      Integrable (fun p : Ω × ℝ × ℝ × ℝ ↦ (X p.1 + Y p.1) ^ 2) (liftMeasure3 P) := by
  have h_mom_XY : Integrable (fun ω ↦ (X ω + Y ω) ^ 2) P := by
    have hX_memLp : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
    have hY_memLp : MemLp Y 2 P :=
      (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
    have hS_memLp : MemLp (fun ω ↦ X ω + Y ω) 2 P := hX_memLp.add hY_memLp
    simpa using hS_memLp.integrable_sq
  refine ⟨h_mom_XY, ?_, ?_, ?_⟩
  · exact h_mom_X.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  · exact h_mom_Y.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))
  · exact h_mom_XY.comp_fst ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))

lemma iIndepFun_liftMeasure3_of_indep
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    iIndepFun
      ![fun p : Ω × ℝ × ℝ × ℝ ↦ X p.1, fun p ↦ Y p.1,
        fun p ↦ p.2.1, fun p ↦ p.2.2.1, fun p ↦ p.2.2.2]
      (liftMeasure3 P) := by
  set X' : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ X p.1 with hX'
  set Y' : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ Y p.1 with hY'
  set ZX : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ p.2.1 with hZX
  set ZY : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ p.2.2.1 with hZY
  set Z : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ p.2.2.2 with hZ
  have hX'_meas : Measurable X' := hX.comp measurable_fst
  have hY'_meas : Measurable Y' := hY.comp measurable_fst
  have hZX_meas : Measurable ZX := measurable_fst.comp measurable_snd
  have hZY_meas : Measurable ZY := (measurable_fst.comp measurable_snd).comp measurable_snd
  have hZ_meas : Measurable Z := (measurable_snd.comp measurable_snd).comp measurable_snd
  obtain ⟨hmap_X', hmap_Y', _⟩ := liftMeasure3_map_fst_eq P X Y hX hY
  obtain ⟨hZX_law, hZY_law, hZ_law⟩ := liftMeasure3_noise_laws P (Ω := Ω)
  have haem : ∀ i, AEMeasurable (![X', Y', ZX, ZY, Z] i) (liftMeasure3 P) := by
    intro i; fin_cases i
    · exact hX'_meas.aemeasurable
    · exact hY'_meas.aemeasurable
    · exact hZX_meas.aemeasurable
    · exact hZY_meas.aemeasurable
    · exact hZ_meas.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map haem]
  symm
  refine Measure.pi_eq (fun s hs ↦ ?_)
  have hjoint_meas : Measurable (fun ω i ↦ ![X', Y', ZX, ZY, Z] i ω) := by
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    fin_cases i
    · exact hX'_meas
    · exact hY'_meas
    · exact hZX_meas
    · exact hZY_meas
    · exact hZ_meas
  rw [Measure.map_apply hjoint_meas (MeasurableSet.univ_pi hs)]
  have hm0 : (liftMeasure3 P).map (![X', Y', ZX, ZY, Z] 0) = P.map X := by simpa using hmap_X'
  have hm1 : (liftMeasure3 P).map (![X', Y', ZX, ZY, Z] 1) = P.map Y := by simpa using hmap_Y'
  have hm2 : (liftMeasure3 P).map (![X', Y', ZX, ZY, Z] 2) = gaussianReal 0 1 := by
    simpa using hZX_law
  have hm3 : (liftMeasure3 P).map (![X', Y', ZX, ZY, Z] 3) = gaussianReal 0 1 := by
    simpa using hZY_law
  have hm4 : (liftMeasure3 P).map (![X', Y', ZX, ZY, Z] 4) = gaussianReal 0 1 := by
    simpa using hZ_law
  rw [Fin.prod_univ_five, hm0, hm1, hm2, hm3, hm4]
  have hpre : (fun ω i ↦ ![X', Y', ZX, ZY, Z] i ω) ⁻¹' (Set.univ.pi s)
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
  rw [hpre, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  have hAprod : P (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) = P.map X (s 0) * P.map Y (s 1) := by
    rw [Measure.map_apply hX (hs 0), Measure.map_apply hY (hs 1)]
    exact (indepFun_iff_measure_inter_preimage_eq_mul.1 hXY) (s 0) (s 1) (hs 0) (hs 1)
  rw [hAprod]
  ring

lemma liftMeasure3_pairwise_indep
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X' Y' ZX ZY Z : Ω × ℝ × ℝ × ℝ → ℝ}
    (hX'_meas : Measurable X') (hY'_meas : Measurable Y')
    (hZX_meas : Measurable ZX) (hZY_meas : Measurable ZY) (hZ_meas : Measurable Z)
    (h_iIndep : iIndepFun ![X', Y', ZX, ZY, Z] (liftMeasure3 P)) :
    IndepFun X' ZX (liftMeasure3 P) ∧
      IndepFun Y' ZY (liftMeasure3 P) ∧
      IndepFun X' Y' (liftMeasure3 P) ∧
      IndepFun ZX ZY (liftMeasure3 P) ∧
      IndepFun (fun p ↦ (X' p, ZX p)) (fun p ↦ (Y' p, ZY p)) (liftMeasure3 P) ∧
      IndepFun (fun p ↦ X' p + Y' p) Z (liftMeasure3 P) ∧
      IndepFun (fun p ↦ X' p + Y' p) (fun p ↦ (ZX p, ZY p)) (liftMeasure3 P) := by
  have hf_meas : ∀ i, Measurable (![X', Y', ZX, ZY, Z] i) := by
    intro i; fin_cases i
    · exact hX'_meas
    · exact hY'_meas
    · exact hZX_meas
    · exact hZY_meas
    · exact hZ_meas
  have hXZX : IndepFun X' ZX (liftMeasure3 P) := by
    have := h_iIndep.indepFun (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide)
    simpa using this
  have hYZY : IndepFun Y' ZY (liftMeasure3 P) := by
    have := h_iIndep.indepFun (i := (1 : Fin 5)) (j := (3 : Fin 5)) (by decide)
    simpa using this
  have hX'Y'_indep : IndepFun X' Y' (liftMeasure3 P) := by
    have := h_iIndep.indepFun (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
    simpa using this
  have hZX_ZY : IndepFun ZX ZY (liftMeasure3 P) := by
    have := h_iIndep.indepFun (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
    simpa using this
  have hpair_indep : IndepFun (fun p ↦ (X' p, ZX p)) (fun p ↦ (Y' p, ZY p)) (liftMeasure3 P) := by
    have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)
    simpa using this
  have hXYZ : IndepFun (fun p ↦ X' p + Y' p) Z (liftMeasure3 P) := by
    have hpair : IndepFun (fun a ↦ (X' a, Y' a)) Z (liftMeasure3 P) := by
      have := h_iIndep.indepFun_prodMk hf_meas 0 1 4 (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun q : ℝ × ℝ ↦ q.1 + q.2) := by fun_prop
    have := hpair.comp hsum measurable_id
    simpa [Function.comp] using this
  have hXY_ZXZY_pair :
      IndepFun (fun p ↦ X' p + Y' p) (fun p ↦ (ZX p, ZY p)) (liftMeasure3 P) := by
    have hpair : IndepFun (fun a ↦ (X' a, Y' a)) (fun a ↦ (ZX a, ZY a)) (liftMeasure3 P) := by
      have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 1 2 3
        (by decide) (by decide) (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun q : ℝ × ℝ ↦ q.1 + q.2) := by fun_prop
    have := hpair.comp hsum (measurable_id : Measurable (id : ℝ × ℝ → ℝ × ℝ))
    simpa [Function.comp] using this
  exact ⟨hXZX, hYZY, hX'Y'_indep, hZX_ZY, hpair_indep, hXYZ, hXY_ZXZY_pair⟩

/-- Entropy power inequality for absolutely continuous distributions with regular densities.

All 16 hypotheses are regularity preconditions (measurability, independence, absolute
continuity, finite second moment, `IsRegularDensityV2`, normalization, `IsBlachmanConvReady`,
finite Fisher information, finite entropy) for `X`, `Y`, and `X + Y`; they do not encode
the EPI inequality core. The proof derives EPI via a 3-noise lift and two-time terminal. -/
@[entry_point]
theorem entropy_power_inequality_of_density
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω ↦ (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω ↦ (Y ω) ^ 2) P)
    -- input-density regularity (producer precondition, not load-bearing)
    (h_fisher_X : FisherInfo.fisherInfoOfDensity
        (fun x ↦ ((P.map X).rnDeriv volume x).toReal) ≠ ∞)
    (hreg_pX : FisherInfo.IsRegularDensityV2
        (fun x ↦ ((P.map X).rnDeriv volume x).toReal))
    (hnorm_pX : ∫ x, ((P.map X).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pX : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady
          (fun x ↦ ((P.map X).rnDeriv volume x).toReal) (gaussianPDFReal 0 v))
    (h_fisher_Y : FisherInfo.fisherInfoOfDensity
        (fun x ↦ ((P.map Y).rnDeriv volume x).toReal) ≠ ∞)
    (hreg_pY : FisherInfo.IsRegularDensityV2
        (fun x ↦ ((P.map Y).rnDeriv volume x).toReal))
    (hnorm_pY : ∫ x, ((P.map Y).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pY : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady
          (fun x ↦ ((P.map Y).rnDeriv volume x).toReal) (gaussianPDFReal 0 v))
    -- sum-density regularity (honest precondition for the 3-noise route, parallel to X/Y)
    (h_fisher_XY : FisherInfo.fisherInfoOfDensity
        (fun x ↦ ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) ≠ ∞)
    (hreg_pXY : FisherInfo.IsRegularDensityV2
        (fun x ↦ ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal))
    (hnorm_pXY : ∫ x, ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pXY : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady
          (fun x ↦ ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) (gaussianPDFReal 0 v))
    -- finite differential entropy of input densities (regularity precondition, not load-bearing)
    (hent_pX : Integrable
        (fun x ↦ Real.negMulLog (((P.map X).rnDeriv volume x).toReal)) volume)
    (hent_pY : Integrable
        (fun x ↦ Real.negMulLog (((P.map Y).rnDeriv volume x).toReal)) volume)
    (hent_pXY : Integrable
        (fun x ↦ Real.negMulLog (((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal)) volume) :
    entropyPower (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- Reduce to a 3-noise-lift-space EPI via `entropy_power_inequality_via_lift3`.
  refine entropy_power_inequality_via_lift3 P X Y hX hY ?_
  -- Lift-space data: `X' := X∘fst`, `Y' := Y∘fst`, noise `Z_X := ·.2.1`, `Z_Y := ·.2.2.1`,
  -- `Z := ·.2.2.2`.
  set lift : Measure (Ω × ℝ × ℝ × ℝ) := liftMeasure3 P with hlift
  set X' : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ X p.1 with hX'
  set Y' : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ Y p.1 with hY'
  set ZX : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ p.2.1 with hZX
  set ZY : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ p.2.2.1 with hZY
  set Z : Ω × ℝ × ℝ × ℝ → ℝ := fun p ↦ p.2.2.2 with hZ
  -- measurability of lift functions
  have hX'_meas : Measurable X' := hX.comp measurable_fst
  have hY'_meas : Measurable Y' := hY.comp measurable_fst
  have hZX_meas : Measurable ZX := measurable_fst.comp measurable_snd
  have hZY_meas : Measurable ZY := (measurable_fst.comp measurable_snd).comp measurable_snd
  have hZ_meas : Measurable Z := (measurable_snd.comp measurable_snd).comp measurable_snd
  -- law transport: lift.map (f∘fst) = P.map f
  obtain ⟨hmap_X', hmap_Y', hmap_sum'⟩ := liftMeasure3_map_fst_eq P X Y hX hY
  -- a.c. transport
  have hX'_ac : (lift.map X') ≪ volume := by rw [hmap_X']; exact hX_ac
  have hY'_ac : (lift.map Y') ≪ volume := by rw [hmap_Y']; exact hY_ac
  have hXY_ac : (P.map (fun ω ↦ X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  have hXY'_ac : (lift.map (fun p ↦ X' p + Y' p)) ≪ volume := by rw [hmap_sum']; exact hXY_ac
  -- second moment of X+Y on base P + moment transport (to the 3-noise lift)
  obtain ⟨h_mom_XY, h_mom_X', h_mom_Y', h_mom_XY'⟩ :=
    liftMeasure3_moment_transport P X Y hX hY h_mom_X h_mom_Y
  -- noise laws (project through the nested products of the 3-noise lift)
  obtain ⟨hZX_law, hZY_law, hZ_law⟩ := liftMeasure3_noise_laws P (Ω := Ω)
  -- 5-tuple joint independence + extracted pairwise/joint independences
  -- (indices: X'=0, Y'=1, ZX=2, ZY=3, Z=4)
  have h_iIndep : iIndepFun ![X', Y', ZX, ZY, Z] lift :=
    iIndepFun_liftMeasure3_of_indep P X Y hX hY hXY
  obtain ⟨hXZX, hYZY, hX'Y'_indep, hZX_ZY, hpair_indep, hXYZ, hXY_ZXZY_pair⟩ :=
    liftMeasure3_pairwise_indep hX'_meas hY'_meas hZX_meas hZY_meas hZ_meas h_iIndep
  -- noise a.c. (Gaussian)
  have hZX_ac : (lift.map ZX) ≪ volume := by
    rw [hZX_law]; exact gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hZY_ac : (lift.map ZY) ≪ volume := by
    rw [hZY_law]; exact gaussianReal_absolutelyContinuous 0 one_ne_zero
  have hZ_ac : (lift.map Z) ≪ volume := by
    rw [hZ_law]; exact gaussianReal_absolutelyContinuous 0 one_ne_zero
  -- density-precondition transport
  have hrn_X : (fun x ↦ ((lift.map X').rnDeriv volume x).toReal)
      = (fun x ↦ ((P.map X).rnDeriv volume x).toReal) := by rw [hmap_X']
  have hrn_Y : (fun x ↦ ((lift.map Y').rnDeriv volume x).toReal)
      = (fun x ↦ ((P.map Y).rnDeriv volume x).toReal) := by rw [hmap_Y']
  have hrn_XY : (fun x ↦ ((lift.map (fun p ↦ X' p + Y' p)).rnDeriv volume x).toReal)
      = (fun x ↦ ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) := by rw [hmap_sum']
  -- de Bruijn group (producer, all three unit-noise → genuine)
  have h_reg_X : StamEPIBridge.IsDeBruijnRegularityHyp X' ZX lift :=
    isDeBruijnRegularityHyp_of_methodX_unitnoise X' ZX lift hX'_meas hZX_meas hXZX hZX_law
      hX'_ac h_mom_X' (hrn_X ▸ h_fisher_X) (hrn_X ▸ hreg_pX) (hrn_X ▸ hnorm_pX)
      (hrn_X ▸ hready_pX)
  have h_reg_Y : StamEPIBridge.IsDeBruijnRegularityHyp Y' ZY lift :=
    isDeBruijnRegularityHyp_of_methodX_unitnoise Y' ZY lift hY'_meas hZY_meas hYZY hZY_law
      hY'_ac h_mom_Y' (hrn_Y ▸ h_fisher_Y) (hrn_Y ▸ hreg_pY) (hrn_Y ▸ hnorm_pY)
      (hrn_Y ▸ hready_pY)
  have h_reg_sum : StamEPIBridge.IsDeBruijnRegularityHyp
      (fun p ↦ X' p + Y' p) Z lift :=
    isDeBruijnRegularityHyp_of_methodX_unitnoise (fun p ↦ X' p + Y' p) Z lift
      (hX'_meas.add hY'_meas) hZ_meas hXYZ hZ_law hXY'_ac h_mom_XY'
      (hrn_XY ▸ h_fisher_XY) (hrn_XY ▸ hreg_pXY) (hrn_XY ▸ hnorm_pXY) (hrn_XY ▸ hready_pXY)
  -- endpoint group: density witnesses (v_Z = 1), via the canonical-rnDeriv construction.
  have h_endpt_X : IsHeatFlowEndpointRegular X' ZX lift :=
    isHeatFlowEndpointRegular_of_canonical_rnDeriv P lift X X' ZX hX hX'_meas hZX_meas hXZX
      hZX_law hmap_X' hX_ac h_mom_X hent_pX
  have h_endpt_Y : IsHeatFlowEndpointRegular Y' ZY lift :=
    isHeatFlowEndpointRegular_of_canonical_rnDeriv P lift Y Y' ZY hY hY'_meas hZY_meas hYZY
      hZY_law hmap_Y' hY_ac h_mom_Y hent_pY
  have h_endpt_sum : IsHeatFlowEndpointRegular (fun p ↦ X' p + Y' p) Z lift :=
    isHeatFlowEndpointRegular_of_canonical_rnDeriv P lift (fun ω ↦ X ω + Y ω)
      (fun p ↦ X' p + Y' p) Z (hX.add hY) (hX'_meas.add hY'_meas) hZ_meas hXYZ hZ_law
      hmap_sum' hXY_ac h_mom_XY hent_pXY
  -- variance/scale data (ported from methodX template), via the extracted path lemmas.
  have hlift_prob : IsProbabilityMeasure lift := by rw [hlift]; infer_instance
  have h_var_general : ∀ (A B : Ω × ℝ × ℝ × ℝ → ℝ), Measurable A → Measurable B →
      IndepFun A B lift → Integrable (fun p ↦ (A p)^2) lift →
      (v_B : ℝ≥0) → lift.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (∫ x, (x - (∫ y, y ∂(lift.map (fun p ↦ A p / Real.sqrt t + B p))))^2
              ∂(lift.map (fun p ↦ A p / Real.sqrt t + B p)))
            ≤ ProbabilityTheory.variance A lift / t + (v_B : ℝ) :=
    fun A B hA hB hAB h_mom_A v_B hB_law t ht ↦
      integral_sub_integral_sq_rescaled_path_le lift A B hA hB hAB h_mom_A v_B hB_law ht
  have h_scale_general : ∀ (A B : Ω × ℝ × ℝ × ℝ → ℝ), Measurable A → Measurable B →
      IndepFun A B lift → (lift.map A) ≪ volume → Integrable (fun p ↦ (A p)^2) lift →
      (v_B : ℝ≥0) → v_B ≠ 0 → lift.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (lift.map (fun p ↦ A p / Real.sqrt t + B p)) ≪ volume ∧
        Integrable (fun x ↦ Real.negMulLog
          (((lift.map (fun p ↦ A p / Real.sqrt t + B p)).rnDeriv volume x).toReal)) volume :=
    fun A B hA hB hAB hA_ac h_mom_A v_B hv_B hB_law t ht ↦
      rescaled_path_absolutelyContinuous_and_negMulLog_integrable lift A B hA hB hAB hA_ac
        h_mom_A v_B hv_B hB_law ht
  set varX : ℝ := ProbabilityTheory.variance X' lift with hvarX_def
  set varY : ℝ := ProbabilityTheory.variance Y' lift with hvarY_def
  set varS : ℝ := ProbabilityTheory.variance (fun p ↦ X' p + Y' p) lift with hvarS_def
  have h_varX_nn : 0 ≤ varX := ProbabilityTheory.variance_nonneg _ _
  have h_varY_nn : 0 ≤ varY := ProbabilityTheory.variance_nonneg _ _
  have h_varS_nn : 0 ≤ varS := ProbabilityTheory.variance_nonneg _ _
  have h_scale_X :=
    h_scale_general X' ZX hX'_meas hZX_meas hXZX hX'_ac h_mom_X' 1 one_ne_zero hZX_law
  have h_scale_Y :=
    h_scale_general Y' ZY hY'_meas hZY_meas hYZY hY'_ac h_mom_Y' 1 one_ne_zero hZY_law
  have h_scale_sum := h_scale_general (fun p ↦ X' p + Y' p) Z (hX'_meas.add hY'_meas) hZ_meas
    hXYZ hXY'_ac h_mom_XY' 1 one_ne_zero hZ_law
  have h_rescale_X : IsRescaledPathRegular X' ZX lift varX 1 :=
    isRescaledPathRegular_of_methodX X' ZX lift hX'_meas hZX_meas 1 one_ne_zero hZX_law hXZX
      hX'_ac varX h_varX_nn h_mom_X'
      (h_var_general X' ZX hX'_meas hZX_meas hXZX h_mom_X' 1 hZX_law)
  have h_rescale_Y : IsRescaledPathRegular Y' ZY lift varY 1 :=
    isRescaledPathRegular_of_methodX Y' ZY lift hY'_meas hZY_meas 1 one_ne_zero hZY_law hYZY
      hY'_ac varY h_varY_nn h_mom_Y'
      (h_var_general Y' ZY hY'_meas hZY_meas hYZY h_mom_Y' 1 hZY_law)
  have h_rescale_S : IsRescaledPathRegular (fun p ↦ X' p + Y' p) Z lift varS 1 :=
    isRescaledPathRegular_of_methodX (fun p ↦ X' p + Y' p) Z lift (hX'_meas.add hY'_meas)
      hZ_meas 1 one_ne_zero hZ_law hXYZ hXY'_ac varS h_varS_nn h_mom_XY'
      (h_var_general (fun p ↦ X' p + Y' p) Z (hX'_meas.add hY'_meas) hZ_meas hXYZ h_mom_XY'
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

end InformationTheory.Shannon.EPIDensityForm
