/-
# Pivot B Phase 1 — explicit-density de Bruijn producer + explicit Phase A EPI

有限分散古典 EPI closure の Pivot B。Phase A `entropy_power_inequality_of_density`
(`EPIDensityForm.lean:70`) は de Bruijn group の producer `isDeBruijnRegularityHyp_of_methodX_unitnoise`
(`EPICase1RatioLimit.lean:1950`) を呼ぶが、その producer は X の密度として
**Mathlib 正準 `Measure.rnDeriv` の代表元** の `IsRegularDensityV2` (完全 pointwise) を要求する。
正準 rnDeriv 代表元は `Classical.choose` 由来で generically 非微分可能なため、平滑化変数
X_t = X + √t·Z の密度 conv(pX, g_t) が正則でも、それと a.e. 一致するだけの正準代表元には
pointwise 述語 `IsRegularDensityV2` を transport できない。よって Phase A は事実上充足不能。

## Approach

producer を **explicit 密度版** に作り替える。canonical rnDeriv から pX を導出する前半を
「explicit `pX : ℝ → ℝ` を引数で受ける」に置換した `isDeBruijnRegularityHyp_of_explicitDensity`
(Deliverable 1) を作り、Phase A body の producer 呼出 3 本をこれに差し替えた explicit Phase A
`entropy_power_inequality_of_density_explicit` (Deliverable 2) を作る。終端 lemma
(`entropyPower_add_ge_case1_of_regular_twotime` + `twoTime_stam_supply`) と endpoint group
(`endpt_of`, canonical rnDeriv を密度に使うが `IsRegularDensityV2` を要求しない) はそのまま再利用。

explicit `pX` は conv(pX_base, g_t) のような pointwise 正則密度を後で渡すための明示 witness
であり、a.e.-pin に弱めてはいけない (pivot の核心)。signature の各正則性前提は EPI を encode
しない load-bearing でない regularity precondition。
-/
import InformationTheory.Shannon.EPIDensityForm

namespace InformationTheory.Shannon.EPICase1SmoothingLimit

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1RatioLimit
open InformationTheory.Shannon.EPICase1TwoTime
open InformationTheory.Shannon.EPINoiseExtension
open scoped ENNReal NNReal

/-- **Deliverable 1 — explicit-density de Bruijn producer**.

`isDeBruijnRegularityHyp_of_methodX_unitnoise` (`EPICase1RatioLimit.lean:1950`) の variant:
「canonical rnDeriv から X の密度 pX を導出する前半」を「explicit `pX : ℝ → ℝ` を引数で受ける」
に置換したもの。これにより consumer は conv(pX_base, g_t) のような **pointwise 正則** な
explicit 密度をそのまま渡せる (canonical rnDeriv の非微分代表元 transport 不能問題を回避)。

全前提 (`hpX_nn`/`hpX_meas`/`hpX_int`/`hpX_law`/`hpX_mom`/`hreg_pX`/`hnorm_pX`/`hready_pX`) は
regularity precondition で load-bearing でない: pX が *正則* L¹ 密度であること
(`IsRegularDensityV2` = 微分可能/正値/tail→0/可積分微分)、正規化、`IsBlachmanConvReady` bundle、
有限 Fisher の主張のみで、de Bruijn / Fisher-monotonicity の不等式核を encode しない。
body は producer の `refine { ... }` 部 (`EPICase1RatioLimit.lean:1995-2068`) を verbatim
コピーし、canonical-rnDeriv 由来の前半を explicit 引数の named 参照に置換。 -/
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

/-- **Deliverable 2 — explicit-density Phase A EPI**.

`EPIDensityForm.entropy_power_inequality_of_density` (`EPIDensityForm.lean:70`) の explicit-density
variant: X/Y/sum の正則性前提を canonical rnDeriv 代表元ではなく **explicit `pX pY pXY : ℝ → ℝ`**
について述べ、各々の withDensity link を追加。body は Phase A body をコピーし、producer 呼出 3 本を
`isDeBruijnRegularityHyp_of_explicitDensity` に差し替え (canonical-rnDeriv bridge `hrn_*` 削除、
endpoint `endpt_of` は再利用、`hent_p*` は `hrnae_*` 経由で rnDeriv 形に transport)。

全前提 (`pX`/`pY`/`pXY` + 各正則性) は load-bearing でない regularity precondition で、
EPI を encode しない。explicit `pX` は pointwise 正則密度を渡すための明示 witness であり、
a.e.-pin に弱めていない (pivot の核心)。proof-done (0 残課題, sorryAx-free)。 -/
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
      IsHeatFlowEndpointRegular W' Zw lift := by
    intro W W' Zw hW hW' hZw hWZ hZw_law hmap hac hmom hent
    set p : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hp_def
    have hp_nn : ∀ x, 0 ≤ p x := fun x => ENNReal.toReal_nonneg
    have hp_meas : Measurable p := ((P.map W).measurable_rnDeriv volume).ennreal_toReal
    have hp_law : lift.map W' = volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
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
            ≤ ProbabilityTheory.variance A lift / t + (v_B : ℝ) := by
    intro A B hA hB hAB h_mom_A v_B hB_law t ht
    have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
    set Zt : Ω × ℝ × ℝ × ℝ → ℝ := fun ω => A ω / Real.sqrt t with hZt
    have hZt_meas : Measurable Zt := hA.div_const _
    have hW_meas : Measurable (fun ω => Zt ω + B ω) := hZt_meas.add hB
    have hB_memLp : MemLp B 2 lift := by
      have hid : MemLp (id : ℝ → ℝ) 2 (lift.map B) := by
        rw [hB_law]; exact memLp_id_gaussianReal' 2 (by simp)
      have := (memLp_map_measure_iff (p := 2) (μ := lift) (g := (id : ℝ → ℝ))
        aestronglyMeasurable_id hB.aemeasurable).mp hid
      simpa [Function.comp] using this
    have hZt_sq : Integrable (fun ω => (Zt ω)^2) lift := by
      have : (fun ω => (Zt ω)^2) = (fun ω => (1 / t) * (A ω)^2) := by
        funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
      rw [this]; exact h_mom_A.const_mul _
    have hZt_memLp : MemLp Zt 2 lift :=
      (memLp_two_iff_integrable_sq_norm hZt_meas.aestronglyMeasurable).mpr (by simpa using hZt_sq)
    have h_indep : IndepFun Zt B lift := by
      have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
      rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
    have hLHS : (∫ x, (x - (∫ y, y ∂(lift.map (fun ω => Zt ω + B ω))))^2
          ∂(lift.map (fun ω => Zt ω + B ω)))
        = ProbabilityTheory.variance (fun ω => Zt ω + B ω) lift := by
      rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
      exact ProbabilityTheory.variance_id_map hW_meas.aemeasurable
    have hVarZt : ProbabilityTheory.variance Zt lift
        = (1 / t) * ProbabilityTheory.variance A lift := by
      have hZt_eq : Zt = fun ω => (1 / Real.sqrt t) * A ω := by
        funext ω; simp only [hZt]; rw [div_eq_inv_mul, one_div]
      rw [hZt_eq, ProbabilityTheory.variance_const_mul]
      congr 1
      rw [div_pow, one_pow, Real.sq_sqrt ht.le]
    have hVarB : ProbabilityTheory.variance B lift = (v_B : ℝ) := by
      rw [← ProbabilityTheory.variance_id_map hB.aemeasurable, hB_law,
        ProbabilityTheory.variance_id_gaussianReal]
    have hVarSum : ProbabilityTheory.variance (fun ω => Zt ω + B ω) lift
        = (1 / t) * ProbabilityTheory.variance A lift + (v_B : ℝ) := by
      rw [ProbabilityTheory.IndepFun.variance_fun_add hZt_memLp hB_memLp h_indep,
        hVarZt, hVarB]
    rw [hLHS, hVarSum, one_div, inv_mul_eq_div]
  have h_scale_general : ∀ (A B : Ω × ℝ × ℝ × ℝ → ℝ), Measurable A → Measurable B →
      IndepFun A B lift → (lift.map A) ≪ volume → Integrable (fun p => (A p)^2) lift →
      (v_B : ℝ≥0) → v_B ≠ 0 → lift.map B = gaussianReal 0 v_B →
      ∀ t : ℝ, 0 < t →
        (lift.map (fun p => A p / Real.sqrt t + B p)) ≪ volume ∧
        Integrable (fun x => Real.negMulLog
          (((lift.map (fun p => A p / Real.sqrt t + B p)).rnDeriv volume x).toReal)) volume := by
    intro A B hA hB hAB hA_ac h_mom_A v_B hv_B hB_law t ht
    set Zt : Ω × ℝ × ℝ × ℝ → ℝ := fun ω => A ω / Real.sqrt t with hZt
    have hZt_meas : Measurable Zt := hA.div_const _
    have hB_ac : (lift.map B) ≪ volume := by
      rw [hB_law]; exact gaussianReal_absolutelyContinuous 0 hv_B
    have h_indep : IndepFun Zt B lift := by
      have : Zt = (fun a => a / Real.sqrt t) ∘ A := by funext ω; rfl
      rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
    have hμ_ac : (lift.map (fun ω => Zt ω + B ω)) ≪ volume := by
      have hWac : (lift.map (fun ω => B ω + Zt ω)) ≪ volume :=
        map_add_absolutelyContinuous B Zt lift hB hZt_meas h_indep.symm hB_ac
      have h_path : (fun ω => Zt ω + B ω) = (fun ω => B ω + Zt ω) := by funext ω; ring
      rw [h_path]; exact hWac
    refine ⟨hμ_ac, ?_⟩
    have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
    obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
      rescaledInput_density_witness A lift hA hA_ac h_mom_A ht
    have hgconv : InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Zt B 1
        = fun ω => Zt ω + B ω := by
      funext ω
      simp only [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution,
        Real.sqrt_one, one_mul]
    have h_path_rnDeriv : (lift.map (fun ω => Zt ω + B ω)).rnDeriv volume
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

end InformationTheory.Shannon.EPICase1SmoothingLimit
