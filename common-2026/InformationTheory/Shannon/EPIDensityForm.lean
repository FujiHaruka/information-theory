/-
# Phase A — 密度あり標準形 EPI (`entropy_power_inequality_of_density`)

無条件 EPI moonshot の Phase A: 密度 (a.c.) + 有限2次モーメント + 入力密度正則性を
honest regularity 前提として付けた標準形 EPI を **lift + producer + step3 + methodX**
assembly で sorryAx-free (理想) に導く。

SoT plan: `docs/shannon/epi-stam-to-conclusion-plan.md` §Phase A。

## Approach (解の全体形)

base `(Ω,P)` を lift `(Ω×ℝ×ℝ, liftMeasure P)` へ持ち上げ、lift 上で雑音
`Z_X := p.2.1` / `Z_Y := p.2.2` (`gaussianReal 0 1` + 独立を lift から genuine 供給) を
使って `entropyPower_add_ge_case1_of_methodX` を適用し、`entropy_power_inequality_via_lift`
で base に戻す。methodX の前提群 (de Bruijn group / endpoint group / h_pos_stam) を
producer (`isDeBruijnRegularityHyp_of_methodX_unitnoise`) + step3
(`isStamInequalityHyp_via_step3`) + 密度前提から discharge する。

## 撤退ライン L-PhA-α (sum-instance 𝒩(0,2))

sum-pair `(X∘fst+Y∘fst, p.2.1+p.2.2)` の雑音は `p.2.1+p.2.2 ~ gaussianReal 0 2` (unit でない)
ため producer (`gaussianReal 0 1` 前提) が直接適用できない。sum-instance の de Bruijn group
(`h_reg_sum`) と h_pos_stam の sum 絡みの conjunct (sum density 正則性 / conv-pin) のみ
`sorry` + `@residual(plan:epi-debruijn-pertime-closure)` で park。X/Y singleton は producer で
genuine。NOT a discharge。
-/
import InformationTheory.Shannon.EPICase1RatioLimit
import InformationTheory.Shannon.EPINoiseExtension
import InformationTheory.Shannon.EPIStamStep3Body
import InformationTheory.Shannon.EPIConvDensityRegular
import InformationTheory.Shannon.EPIBlachmanGeneralDensity
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.EPIConvDensityNormalization

namespace InformationTheory.Shannon.EPIDensityForm

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPINoiseExtension
open InformationTheory.Shannon.EPICase1RatioLimit
open scoped ENNReal NNReal

/-- **Phase A — 密度あり標準形 EPI**.

`X Y : Ω → ℝ` が独立・各々絶対連続 (Lebesgue 密度を持つ) + 有限2次モーメント + 入力密度
正則性 (`IsRegularDensityV2` / normalized / `IsBlachmanConvReady` / Fisher 有限、いずれも
load-bearing でない regularity precondition、producer `isDeBruijnRegularityHyp_of_methodX_unitnoise`
の要求形を verbatim コピー) を満たすとき、entropy power inequality が成立する。

@residual(plan:epi-debruijn-pertime-closure) -/
theorem entropy_power_inequality_of_density
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_mom_Y : Integrable (fun ω => (Y ω) ^ 2) P)
    -- input-density 正則性 (producer precondition、load-bearing でない、verbatim コピー)
    (h_fisher_X : FisherInfoV2.fisherInfoOfDensity
        (fun x => ((P.map X).rnDeriv volume x).toReal) ≠ ∞)
    (hreg_pX : FisherInfoV2.IsRegularDensityV2
        (fun x => ((P.map X).rnDeriv volume x).toReal))
    (hnorm_pX : ∫ x, ((P.map X).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pX : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady
          (fun x => ((P.map X).rnDeriv volume x).toReal) (gaussianPDFReal 0 v))
    (h_fisher_Y : FisherInfoV2.fisherInfoOfDensity
        (fun x => ((P.map Y).rnDeriv volume x).toReal) ≠ ∞)
    (hreg_pY : FisherInfoV2.IsRegularDensityV2
        (fun x => ((P.map Y).rnDeriv volume x).toReal))
    (hnorm_pY : ∫ x, ((P.map Y).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pY : ∀ v : ℝ≥0, v ≠ 0 →
        EPIBlachmanDensity.IsBlachmanConvReady
          (fun x => ((P.map Y).rnDeriv volume x).toReal) (gaussianPDFReal 0 v))
    -- input-density 微分エントロピー有限性 (L-PhA-β honest 強化、load-bearing でない
    -- regularity precondition: `IsHeatFlowEndpointRegular.hpX_ent` 要求形)
    (hent_pX : Integrable
        (fun x => Real.negMulLog (((P.map X).rnDeriv volume x).toReal)) volume)
    (hent_pY : Integrable
        (fun x => Real.negMulLog (((P.map Y).rnDeriv volume x).toReal)) volume) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- Reduce to a lift-space EPI via `entropy_power_inequality_via_lift`.
  refine entropy_power_inequality_via_lift P X Y hX hY ?_
  -- Lift-space data: `X' := X∘fst`, `Y' := Y∘fst`, noise `Z_X := ·.2.1`, `Z_Y := ·.2.2`.
  set lift : Measure (Ω × ℝ × ℝ) := liftMeasure P with hlift
  set X' : Ω × ℝ × ℝ → ℝ := fun p => X p.1 with hX'
  set Y' : Ω × ℝ × ℝ → ℝ := fun p => Y p.1 with hY'
  set ZX : Ω × ℝ × ℝ → ℝ := fun p => p.2.1 with hZX
  set ZY : Ω × ℝ × ℝ → ℝ := fun p => p.2.2 with hZY
  -- measurability of lift functions
  have hX'_meas : Measurable X' := hX.comp measurable_fst
  have hY'_meas : Measurable Y' := hY.comp measurable_fst
  have hZX_meas : Measurable ZX := measurable_fst.comp measurable_snd
  have hZY_meas : Measurable ZY := measurable_snd.comp measurable_snd
  -- law transport: lift.map (f∘fst) = P.map f
  have hmap_X' : lift.map X' = P.map X := by
    rw [hlift, hX', show (fun p : Ω × ℝ × ℝ => X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  have hmap_Y' : lift.map Y' = P.map Y := by
    rw [hlift, hY', show (fun p : Ω × ℝ × ℝ => Y p.1) = Y ∘ Prod.fst from rfl,
      ← Measure.map_map hY measurable_fst, measurePreserving_fst.map_eq]
  have hmap_sum' : lift.map (fun p => X' p + Y' p) = P.map (fun ω => X ω + Y ω) := by
    rw [hlift, hX', hY',
      show (fun p : Ω × ℝ × ℝ => X p.1 + Y p.1) = (fun ω => X ω + Y ω) ∘ Prod.fst from rfl,
      ← Measure.map_map (hX.add hY) measurable_fst, measurePreserving_fst.map_eq]
  -- a.c. transport: (lift.map X') ≪ volume etc.
  have hX'_ac : (lift.map X') ≪ volume := by rw [hmap_X']; exact hX_ac
  have hY'_ac : (lift.map Y') ≪ volume := by rw [hmap_Y']; exact hY_ac
  -- sum a.c. from X a.c. + X ⊥ Y (X+Y density = convolution)
  have hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  have hXY'_ac : (lift.map (fun p => X' p + Y' p)) ≪ volume := by
    rw [hmap_sum']; exact hXY_ac
  -- moment transport
  have h_mom_X' : Integrable (fun p => (X' p) ^ 2) lift := by
    rw [hlift, hX']
    exact h_mom_X.comp_fst ((gaussianReal 0 1).prod (gaussianReal 0 1))
  have h_mom_Y' : Integrable (fun p => (Y' p) ^ 2) lift := by
    rw [hlift, hY']
    exact h_mom_Y.comp_fst ((gaussianReal 0 1).prod (gaussianReal 0 1))
  -- noise laws
  have hZX_law : lift.map ZX = gaussianReal 0 1 := by
    rw [hlift, hZX,
      show (fun p : Ω × ℝ × ℝ => p.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_fst.map_eq]
  have hZY_law : lift.map ZY = gaussianReal 0 1 := by
    rw [hlift, hZY,
      show (fun p : Ω × ℝ × ℝ => p.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd measurable_snd,
      measurePreserving_snd.map_eq, measurePreserving_snd.map_eq]
  -- 4-tuple joint independence
  have h_iIndep : iIndepFun ![X', Y', ZX, ZY] lift := by
    have haem : ∀ i, AEMeasurable (![X', Y', ZX, ZY] i) lift := by
      intro i; fin_cases i
      · exact hX'_meas.aemeasurable
      · exact hY'_meas.aemeasurable
      · exact hZX_meas.aemeasurable
      · exact hZY_meas.aemeasurable
    rw [iIndepFun_iff_map_fun_eq_pi_map haem]
    -- Both sides are measures on `Fin 4 → ℝ`. Use `Measure.pi_eq` (box characterization).
    symm
    refine Measure.pi_eq (fun s hs => ?_)
    -- LHS box value: `lift (joint4 ⁻¹' (pi univ s))`.
    have hjoint_meas : Measurable (fun ω i => ![X', Y', ZX, ZY] i ω) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      fin_cases i
      · exact hX'_meas
      · exact hY'_meas
      · exact hZX_meas
      · exact hZY_meas
    rw [Measure.map_apply hjoint_meas (MeasurableSet.univ_pi hs)]
    -- marginal laws
    have hm0 : lift.map (![X', Y', ZX, ZY] 0) = P.map X := by simpa using hmap_X'
    have hm1 : lift.map (![X', Y', ZX, ZY] 1) = P.map Y := by simpa using hmap_Y'
    have hm2 : lift.map (![X', Y', ZX, ZY] 2) = gaussianReal 0 1 := by simpa using hZX_law
    have hm3 : lift.map (![X', Y', ZX, ZY] 3) = gaussianReal 0 1 := by simpa using hZY_law
    rw [Fin.prod_univ_four, hm0, hm1, hm2, hm3]
    -- preimage as a product set `A ×ˢ (s2 ×ˢ s3)` with `A = X⁻¹ s0 ∩ Y⁻¹ s1`
    have hpre : (fun ω i => ![X', Y', ZX, ZY] i ω) ⁻¹' (Set.univ.pi s)
        = (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) ×ˢ (s 2 ×ˢ s 3) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨⟨h 0, h 1⟩, h 2, h 3⟩
      · intro h i
        fin_cases i
        · exact h.1.1
        · exact h.1.2
        · exact h.2.1
        · exact h.2.2
    rw [hpre, hlift, Measure.prod_prod, Measure.prod_prod]
    -- `P (X⁻¹ s0 ∩ Y⁻¹ s1) = P.map X (s0) * P.map Y (s1)` via `X ⊥ Y`
    have hAprod : P (X ⁻¹' s 0 ∩ Y ⁻¹' s 1) = P.map X (s 0) * P.map Y (s 1) := by
      rw [Measure.map_apply hX (hs 0), Measure.map_apply hY (hs 1)]
      exact (indepFun_iff_measure_inter_preimage_eq_mul.1 hXY) (s 0) (s 1) (hs 0) (hs 1)
    rw [hAprod]
    ring
  -- input-pair independences on lift (from product structure)
  have hXZX : IndepFun X' ZX lift := by
    rw [hlift, hX', hZX]; exact indepFun_prod hX measurable_fst
  have hYZY : IndepFun Y' ZY lift := by
    rw [hlift, hY', hZY]; exact indepFun_prod hY measurable_snd
  -- density-precondition transport: `(lift.map X').rnDeriv = (P.map X).rnDeriv`
  have hrn_X : (fun x => ((lift.map X').rnDeriv volume x).toReal)
      = (fun x => ((P.map X).rnDeriv volume x).toReal) := by rw [hmap_X']
  have hrn_Y : (fun x => ((lift.map Y').rnDeriv volume x).toReal)
      = (fun x => ((P.map Y).rnDeriv volume x).toReal) := by rw [hmap_Y']
  -- de Bruijn group (producer P-3, X/Y singleton genuine; sum-pair parked)
  have h_reg_X' : EPIStamDischarge.IsDeBruijnRegularityHyp X' ZX lift :=
    isDeBruijnRegularityHyp_of_methodX_unitnoise X' ZX lift hX'_meas hZX_meas hXZX hZX_law
      hX'_ac h_mom_X' (hrn_X ▸ h_fisher_X) (hrn_X ▸ hreg_pX) (hrn_X ▸ hnorm_pX)
      (hrn_X ▸ hready_pX)
  have h_reg_Y' : EPIStamDischarge.IsDeBruijnRegularityHyp Y' ZY lift :=
    isDeBruijnRegularityHyp_of_methodX_unitnoise Y' ZY lift hY'_meas hZY_meas hYZY hZY_law
      hY'_ac h_mom_Y' (hrn_Y ▸ h_fisher_Y) (hrn_Y ▸ hreg_pY) (hrn_Y ▸ hnorm_pY)
      (hrn_Y ▸ hready_pY)
  have h_reg_sum : EPIStamDischarge.IsDeBruijnRegularityHyp
      (fun p => X' p + Y' p) (fun p => ZX p + ZY p) lift := by
    -- @residual(plan:epi-debruijn-pertime-closure)
    -- L-PhA-α: sum noise ZX+ZY ~ gaussianReal 0 2, producer requires gaussianReal 0 1.
    sorry
  -- endpoint group: density witnesses for X'/Y' on lift
  have endpt_of : ∀ (W : Ω → ℝ) (W' : Ω × ℝ × ℝ → ℝ) (Z : Ω × ℝ × ℝ → ℝ),
      Measurable W → Measurable W' → Measurable Z → IndepFun W' Z lift →
      lift.map Z = gaussianReal 0 1 → lift.map W' = P.map W → (P.map W) ≪ volume →
      Integrable (fun ω => (W ω) ^ 2) P →
      Integrable (fun x => Real.negMulLog (((P.map W).rnDeriv volume x).toReal)) volume →
      IsHeatFlowEndpointRegular W' Z lift := by
    intro W W' Z hW hW' hZ hWZ hZ_law hmap hac hmom hent
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
        hZ_meas := hZ
        hXZ_indep := hWZ
        v_Z := 1
        hv_Z_pos := one_pos
        hZ_law := hZ_law
        pX := p
        hpX_nn := hp_nn
        hpX_meas := hp_meas
        hpX_law := hp_law
        hpX_int := hp_int
        hpX_mass := hp_mass
        hpX_mom := hp_mom
        hpX_ent := hent }
  have h_endpt_X : IsHeatFlowEndpointRegular X' ZX lift :=
    endpt_of X X' ZX hX hX'_meas hZX_meas hXZX hZX_law hmap_X' hX_ac h_mom_X hent_pX
  have h_endpt_Y : IsHeatFlowEndpointRegular Y' ZY lift :=
    endpt_of Y Y' ZY hY hY'_meas hZY_meas hYZY hZY_law hmap_Y' hY_ac h_mom_Y hent_pY
  have h_endpt_sum : IsHeatFlowEndpointRegular
      (fun p => X' p + Y' p) (fun p => ZX p + ZY p) lift := by
    -- @residual(plan:epi-debruijn-pertime-closure)
    -- L-PhA-α (sum-instance, NOT a discharge): sum noise ZX+ZY ~ gaussianReal 0 2 (v_Z=2),
    -- and the sum density `pXY` entropy finiteness `hpX_ent` is not in the input
    -- preconditions (only pX/pY entropy finiteness are). Belongs to the 𝒩(0,2) reparam wave.
    sorry
  -- h_pos_stam 10-conjunct
  have h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < FisherInfoV2.fisherInfoOfDensityReal ((h_reg_X'.reg_at t ht).density_t)) ∧
      (0 < FisherInfoV2.fisherInfoOfDensityReal ((h_reg_Y'.reg_at t ht).density_t)) ∧
      (0 < FisherInfoV2.fisherInfoOfDensityReal ((h_reg_sum.reg_at t ht).density_t)) ∧
      EPIStamDischarge.IsStamInequalityHyp
        (fun p => X' p + Real.sqrt t * ZX p)
        (fun p => Y' p + Real.sqrt t * ZY p) lift ∧
      FisherInfoV2.IsRegularDensityV2 ((h_reg_X'.reg_at t ht).density_t) ∧
      FisherInfoV2.IsRegularDensityV2 ((h_reg_Y'.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X'.reg_at t ht).density_t x ∂volume = 1) ∧
      (∫ x, (h_reg_Y'.reg_at t ht).density_t x ∂volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = EPIConvDensity.convDensityAdd
                ((h_reg_X'.reg_at t ht).density_t)
                ((h_reg_Y'.reg_at t ht).density_t) x) ∧
      EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X'.reg_at t ht).density_t)
        ((h_reg_Y'.reg_at t ht).density_t) := by
    intro t ht
    -- input densities (producer's internal `pX`/`pY`) and their regularity facts.
    set pX : ℝ → ℝ := (h_reg_X'.reg_at t ht).pX with hpX_def
    set pY : ℝ → ℝ := (h_reg_Y'.reg_at t ht).pX with hpY_def
    -- density_t pins to `convDensityAdd p g_t`
    have hpinX : (h_reg_X'.reg_at t ht).density_t
        = EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) := by
      funext x; exact (h_reg_X'.reg_at t ht).density_t_eq ht x
    have hpinY : (h_reg_Y'.reg_at t ht).density_t
        = EPIConvDensity.convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) := by
      funext x; exact (h_reg_Y'.reg_at t ht).density_t_eq ht x
    -- pX/pY regularity (from the V2 structure fields)
    have hpX_nn : ∀ x, 0 ≤ pX x := (h_reg_X'.reg_at t ht).pX_nn
    have hpX_meas : Measurable pX := (h_reg_X'.reg_at t ht).pX_meas
    have hpY_nn : ∀ x, 0 ≤ pY x := (h_reg_Y'.reg_at t ht).pX_nn
    have hpY_meas : Measurable pY := (h_reg_Y'.reg_at t ht).pX_meas
    -- pX/pY integrability + mass from the X density witness via `pX_law`
    -- (`lift.map X'` is a probability measure, so `∫⁻ ofReal(pX) = 1`).
    have density_facts : ∀ (W' : Ω × ℝ × ℝ → ℝ) (p : ℝ → ℝ),
        Measurable W' → (∀ x, 0 ≤ p x) → Measurable p →
        lift.map W' = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
        Integrable p volume ∧ (∫ x, p x ∂volume) = 1 := by
      intro W' p hW' hp_nn hp_meas hp_law
      have hprob : IsProbabilityMeasure (lift.map W') := by
        rw [hlift]
        exact MeasureTheory.Measure.isProbabilityMeasure_map hW'.aemeasurable
      have hlint : (∫⁻ x, ENNReal.ofReal (p x) ∂volume) = 1 := by
        have := hprob.measure_univ
        rw [hp_law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
        exact this
      have hp_int : Integrable p volume := by
        rw [← lintegral_ofReal_ne_top_iff_integrable hp_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall hp_nn)]
        rw [hlint]; exact ENNReal.one_ne_top
      have hp_mass : (∫ x, p x ∂volume) = 1 := by
        rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hp_nn)
          hp_meas.aestronglyMeasurable, hlint, ENNReal.toReal_one]
      exact ⟨hp_int, hp_mass⟩
    obtain ⟨hpX_int, hpX_norm⟩ :=
      density_facts X' pX hX'_meas hpX_nn hpX_meas (h_reg_X'.reg_at t ht).pX_law
    obtain ⟨hpY_int, hpY_norm⟩ :=
      density_facts Y' pY hY'_meas hpY_nn hpY_meas (h_reg_Y'.reg_at t ht).pX_law
    have hpX_mass : (0 : ℝ) < ∫ x, pX x ∂volume := by rw [hpX_norm]; norm_num
    have hpY_mass : (0 : ℝ) < ∫ x, pY x ∂volume := by rw [hpY_norm]; norm_num
    -- per-time regularity of `density_t = convDensityAdd p g_t` (conv-gaussian producers)
    have hregX_t : FisherInfoV2.IsRegularDensityV2 ((h_reg_X'.reg_at t ht).density_t) := by
      rw [hpinX]
      exact EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
    have hregY_t : FisherInfoV2.IsRegularDensityV2 ((h_reg_Y'.reg_at t ht).density_t) := by
      rw [hpinY]
      exact EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    -- per-time normalization `∫ density_t = 1`
    have hnormX_t : (∫ x, (h_reg_X'.reg_at t ht).density_t x ∂volume = 1) := by
      rw [hpinX]
      exact InformationTheory.Shannon.EPIConvDensity.integral_convDensityAdd_gaussian_eq_one
        pX ht hpX_int hpX_norm
    have hnormY_t : (∫ x, (h_reg_Y'.reg_at t ht).density_t x ∂volume = 1) := by
      rw [hpinY]
      exact InformationTheory.Shannon.EPIConvDensity.integral_convDensityAdd_gaussian_eq_one
        pY ht hpY_int hpY_norm
    -- per-time `IsBlachmanConvReady (density_X_t) (density_Y_t)`
    have hready_t : EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X'.reg_at t ht).density_t) ((h_reg_Y'.reg_at t ht).density_t) := by
      rw [hpinX, hpinY]
      exact EPIBlachmanGeneralDensity.isBlachmanConvReady_convDensityAdd_gaussian pX pY ht
        hpX_nn hpX_meas hpX_int hpX_mass hpX_norm
        hpY_nn hpY_meas hpY_int hpY_mass hpY_norm
    -- Stam inequality hyp via step3: needs `IndepFun (X'+√t ZX)(Y'+√t ZY) lift`
    have hf_meas : ∀ i, Measurable (![X', Y', ZX, ZY] i) := by
      intro i; fin_cases i
      · exact hX'_meas
      · exact hY'_meas
      · exact hZX_meas
      · exact hZY_meas
    have hStam_indep : IndepFun
        (fun p => X' p + Real.sqrt t * ZX p)
        (fun p => Y' p + Real.sqrt t * ZY p) lift := by
      have hpair : IndepFun (fun a => (X' a, ZX a)) (fun a => (Y' a, ZY a)) lift := by
        have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 2 1 3
          (by decide) (by decide) (by decide) (by decide)
        simpa using this
      have hcomb : Measurable (fun q : ℝ × ℝ => q.1 + Real.sqrt t * q.2) := by fun_prop
      have := hpair.comp hcomb hcomb
      simpa [Function.comp] using this
    have hStam : EPIStamDischarge.IsStamInequalityHyp
        (fun p => X' p + Real.sqrt t * ZX p)
        (fun p => Y' p + Real.sqrt t * ZY p) lift := by
      have hmX : Measurable (fun p => X' p + Real.sqrt t * ZX p) := by fun_prop
      have hmY : Measurable (fun p => Y' p + Real.sqrt t * ZY p) := by fun_prop
      exact InformationTheory.Shannon.EPIStamStep3Body.isStamInequalityHyp_via_step3 lift _ _ hmX hmY hStam_indep
    refine ⟨?_, ?_, ?_, hStam, hregX_t, hregY_t, hnormX_t, hnormY_t, ?_, hready_t⟩
    · -- @residual(plan:epi-debruijn-pertime-closure)
      -- L-PhA-δ (Fisher non-degeneracy gap, NOT a discharge): `0 < J(conv pX g_t)`.
      -- In-tree only upper bounds exist (`gaussianConv_fisher_le_inv_var`); the `≠ 0`
      -- (non-degeneracy) direction needs a new lemma: `J=0 ⟹ logDeriv f = 0 a.e. ⟹
      -- deriv f ≡ 0 (deriv continuous for conv-gaussian) ⟹ f constant ⟹ ⊥ with f→0`.
      sorry
    · -- @residual(plan:epi-debruijn-pertime-closure)
      -- L-PhA-δ (Fisher non-degeneracy gap for Y', same as above).
      sorry
    · -- @residual(plan:epi-debruijn-pertime-closure)
      -- L-PhA-α (sum-instance, NOT a discharge): sum-density Fisher positivity depends on
      -- the parked `h_reg_sum` (𝒩(0,2) reparam).
      sorry
    · -- @residual(plan:epi-debruijn-pertime-closure)
      -- L-PhA-α (sum-instance, NOT a discharge): conv-pin `density_sum_t =
      -- convDensityAdd density_X_t density_Y_t` requires the 𝒩(0,2)→𝒩(0,1) reparam
      -- (`convDensityAdd_convGaussian_interchange`: conv(pX∗g_t,pY∗g_t)=conv(pX∗pY,g_{2t}),
      -- variance 2t≠t), depends on the parked `h_reg_sum`.
      sorry
  -- apply methodX
  exact entropyPower_add_ge_case1_of_methodX X' Y' ZX ZY lift
    hX'_meas hY'_meas hZX_meas hZY_meas
    hX'_ac hY'_ac hXY'_ac h_mom_X' h_mom_Y'
    hZX_law hZY_law h_iIndep
    h_reg_sum h_reg_X' h_reg_Y'
    h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam

end InformationTheory.Shannon.EPIDensityForm
