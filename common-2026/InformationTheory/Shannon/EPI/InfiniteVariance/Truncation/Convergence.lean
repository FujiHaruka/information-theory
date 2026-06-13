import InformationTheory.Shannon.EPI.Case1.SmoothingLimit
import InformationTheory.Shannon.EPI.Stam.SupplyTwoTime
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Construction
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Density

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Differential entropy of a measure conditioned on a growing truncation set
`Sn := {|r| ≤ n}` decomposes as
`h(cond μ Sn) = (m_n.toReal)⁻¹ · ∫ Sn.indicator (negMulLog ∘ q) ∂volume + log (m_n.toReal)`,
where `m_n := μ Sn` and `q x := (μ.rnDeriv volume x).toReal`. -/
theorem differentialEntropy_cond_decomp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hpos : μ {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0)
    (hac : μ ≪ volume)
    (hent : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy (ProbabilityTheory.cond μ {r : ℝ | |r| ≤ (n : ℝ)})
      = ((μ {r : ℝ | |r| ≤ (n : ℝ)}).toReal)⁻¹
          * ∫ x, ({r : ℝ | |r| ≤ (n : ℝ)}).indicator
              (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) x ∂volume
        + Real.log ((μ {r : ℝ | |r| ≤ (n : ℝ)}).toReal) := by
  classical
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  set m : ℝ≥0∞ := μ Sn with hm_def
  have hm_ne_top : m ≠ ∞ := measure_ne_top _ _
  set q : ℝ → ℝ := fun x => ((μ.rnDeriv volume x).toReal) with hq_def
  have hq_meas : Measurable q := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hq_int : Integrable q volume := Measure.integrable_toReal_rnDeriv
  set c : ℝ := (m⁻¹).toReal with hc_def
  -- cond density formula: rewrite the cond rnDeriv a.e.
  have h_rn : (ProbabilityTheory.cond μ Sn).rnDeriv volume
      =ᵐ[volume] fun x => m⁻¹ * Sn.indicator (μ.rnDeriv volume) x :=
    rnDeriv_cond_eq μ hSn_meas hpos
  -- `differentialEntropy (cond μ Sn) = ∫ Sn.indicator (q · negMulLog c + c · negMulLog q)`.
  have h_ent_eq : differentialEntropy (ProbabilityTheory.cond μ Sn)
      = ∫ x, Sn.indicator
          (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) x ∂volume := by
    unfold differentialEntropy
    refine integral_congr_ae ?_
    filter_upwards [h_rn] with x hx
    rw [hx]
    by_cases hxs : x ∈ Sn
    · rw [Set.indicator_of_mem hxs
          (f := fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)),
        ENNReal.toReal_mul, Set.indicator_of_mem hxs (f := μ.rnDeriv volume)]
      show Real.negMulLog (c * q x) = q x * Real.negMulLog c + c * Real.negMulLog (q x)
      exact Real.negMulLog_mul c (q x)
    · rw [Set.indicator_of_notMem hxs
          (f := fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)),
        Set.indicator_of_notMem hxs (f := μ.rnDeriv volume)]
      simp only [mul_zero, ENNReal.toReal_zero, Real.negMulLog_zero]
  rw [h_ent_eq]
  -- split the indicator integral into the two terms.
  have hsplit : (fun x => Sn.indicator
      (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) x)
      = fun x => Sn.indicator (fun x => q x * Real.negMulLog c) x
        + Sn.indicator (fun x => c * Real.negMulLog (q x)) x := by
    funext x
    by_cases hxs : x ∈ Sn
    · simp only [Set.indicator_of_mem hxs]
    · simp only [Set.indicator_of_notMem hxs, add_zero]
  rw [hsplit]
  -- integrability of the two indicator pieces.
  have h1_int : Integrable (fun x => Sn.indicator (fun x => q x * Real.negMulLog c) x) volume :=
    (hq_int.mul_const (Real.negMulLog c)).indicator hSn_meas
  have h2_int : Integrable (fun x => Sn.indicator (fun x => c * Real.negMulLog (q x)) x) volume :=
    (hent.const_mul c).indicator hSn_meas
  rw [integral_add h1_int h2_int]
  -- first term: `∫ Sn.indicator (q · negMulLog c) = negMulLog c · (μ Sn).toReal`.
  have h_term1 : ∫ x, Sn.indicator (fun x => q x * Real.negMulLog c) x ∂volume
      = Real.negMulLog c * m.toReal := by
    rw [integral_indicator hSn_meas]
    rw [show (fun x => q x * Real.negMulLog c) = (fun x => Real.negMulLog c * q x) from by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul]
    rw [Measure.setIntegral_toReal_rnDeriv hac Sn, measureReal_def]
  -- second term: `∫ Sn.indicator (c · negMulLog q) = c · ∫ Sn.indicator (negMulLog q)`.
  have h_term2 : ∫ x, Sn.indicator (fun x => c * Real.negMulLog (q x)) x ∂volume
      = c * ∫ x, Sn.indicator (fun x => Real.negMulLog (q x)) x ∂volume := by
    rw [integral_indicator hSn_meas, integral_indicator hSn_meas]
    rw [MeasureTheory.integral_const_mul]
  rw [h_term1, h_term2]
  -- `negMulLog c · m.toReal = log m.toReal` and `c = m.toReal⁻¹`.
  have hm_pos : 0 < m.toReal := ENNReal.toReal_pos hpos hm_ne_top
  have hc_eq : c = (m.toReal)⁻¹ := by
    rw [hc_def, ENNReal.toReal_inv]
  -- `negMulLog c * m.toReal = -c * log c * m.toReal = log m.toReal`.
  have h_negc : Real.negMulLog c * m.toReal = Real.log m.toReal := by
    have h1 : Real.negMulLog c = -c * Real.log c := rfl
    rw [h1, hc_eq, Real.log_inv]
    field_simp
  rw [h_negc, hc_eq]
  ring

/-- Per-component convergence of differential entropy under conditioning truncation:
`h((condTrunc P X Y n).map Z) → h(P.map Z)` for `Z = X` or `Z = Y`. The decomposition
`-∫ p_n log p_n = -(1/m_n) ∫_{truncSet} p log p + log m_n` converges by dominated convergence on
the fixed integrable `p log p` (first term) and `m_n → 1` (second term). -/
theorem differentialEntropy_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => differentialEntropy ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (differentialEntropy (P.map Z))) := by
  classical
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  haveI : IsProbabilityMeasure (P.map Z) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  -- abbreviations: `Sn n = {|r| ≤ n}`, `m_n = (P.map Z) (Sn n)`, `p x = ((P.map Z).rnDeriv vol x).toReal`.
  set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : ∀ n, MeasurableSet (Sn n) := fun n =>
    measurableSet_le measurable_norm measurable_const
  set p : ℝ → ℝ := fun x => ((P.map Z).rnDeriv volume x).toReal with hp_def
  -- the `Sn n` are monotone increasing and exhaust `ℝ`.
  have hSn_mono : Monotone Sn := by
    intro a b hab r hr
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    exact le_trans hr hab'
  have hSn_union : ⋃ n, Sn n = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    obtain ⟨k, hk⟩ := exists_nat_ge (|r|)
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  -- `m_n = (P.map Z) (Sn n) → 1`.
  have hm_tendsto : Tendsto (fun n => (P.map Z) (Sn n)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.map Z) hSn_mono
    rw [hSn_union, measure_univ] at h
    exact h
  -- eventually `(P.map Z) (Sn n) ≠ 0` and `P (truncSet X Y n) ≠ 0`.
  have hSn_pos_ev : ∀ᶠ n in atTop, (P.map Z) (Sn n) ≠ 0 := by
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hm_tendsto.eventually_mem h_nhds
  have hpos_ev : ∀ᶠ n in atTop, P (truncSet X Y n) ≠ 0 :=
    eventually_measure_truncSet_pos P hX hY
  -- `m_n.toReal → 1`.
  have hmreal_tendsto : Tendsto (fun n => ((P.map Z) (Sn n)).toReal) atTop (𝓝 (1 : ℝ)) := by
    have := (ENNReal.tendsto_toReal (ENNReal.one_ne_top)).comp hm_tendsto
    simpa using this
  -- `c_n := (m_n.toReal)⁻¹ → 1`.
  have hc_tendsto : Tendsto (fun n => ((P.map Z) (Sn n)).toReal⁻¹) atTop (𝓝 1) := by
    have := (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hmreal_tendsto
    simpa using this
  -- `log m_n.toReal → log 1 = 0`.
  have hlogm_tendsto : Tendsto (fun n => Real.log ((P.map Z) (Sn n)).toReal) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hmreal_tendsto
    simpa [Real.log_one] using this
  -- `∫ Sn.indicator (negMulLog ∘ p) → ∫ negMulLog ∘ p = h(P.map Z)` via DCT.
  have hint_tendsto :
      Tendsto (fun n => ∫ x, (Sn n).indicator
          (fun x => Real.negMulLog (p x)) x ∂volume) atTop
        (𝓝 (∫ x, Real.negMulLog (p x) ∂volume)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |Real.negMulLog (p x)|) ?_ ?_ ?_ ?_
    · -- AEStronglyMeasurable of each indicator term.
      intro n
      refine (Measurable.aestronglyMeasurable ?_)
      exact (Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).indicator (hSn_meas n)
    · -- bound integrable.
      exact hZ_ent.abs
    · -- pointwise bound: `‖Sn.indicator (negMulLog p) x‖ ≤ |negMulLog p x|`.
      intro n
      refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hxn : x ∈ Sn n
      · rw [Set.indicator_of_mem hxn, Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hxn]; simp [abs_nonneg]
    · -- pointwise limit: for each x, eventually `x ∈ Sn n`, so indicator → value.
      refine Filter.Eventually.of_forall (fun x => ?_)
      obtain ⟨k, hk⟩ := exists_nat_ge (|x|)
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop k] with n hn
      have hxn : x ∈ Sn n := le_trans hk (by exact_mod_cast hn)
      rw [Set.indicator_of_mem hxn]
  -- the integral equals `h(P.map Z)` (= `∫ negMulLog p`).
  have hint_eq : (∫ x, Real.negMulLog (p x) ∂volume) = differentialEntropy (P.map Z) := rfl
  rw [← hint_eq]
  -- now assemble: the RHS sequence `c_n · term + log m_n` tends to `∫ negMulLog p`,
  -- and eventually equals `h(condTrunc.map Z)`.
  have hRHS_tendsto : Tendsto (fun n => ((P.map Z) (Sn n)).toReal⁻¹
      * (∫ x, (Sn n).indicator (fun x => Real.negMulLog (p x)) x ∂volume)
      + Real.log ((P.map Z) (Sn n)).toReal) atTop
      (𝓝 (∫ x, Real.negMulLog (p x) ∂volume)) := by
    have hmul : Tendsto (fun n => ((P.map Z) (Sn n)).toReal⁻¹
        * ∫ x, (Sn n).indicator (fun x => Real.negMulLog (p x)) x ∂volume) atTop
        (𝓝 (1 * ∫ x, Real.negMulLog (p x) ∂volume)) :=
      hc_tendsto.mul hint_tendsto
    have := hmul.add hlogm_tendsto
    simpa using this
  refine hRHS_tendsto.congr' ?_
  filter_upwards [hpos_ev, hSn_pos_ev] with n hpos hSn_pos
  rw [map_condTrunc_eq_cond_map P hX hY hXY hZ hpos,
    differentialEntropy_cond_decomp (P.map Z) hSn_pos hZ_ac hZ_ent]

/-- Per-component convergence of the entropy power under conditioning truncation:
`Nₑ((condTrunc P X Y n).map Z) → Nₑ(P.map Z)`, obtained from the differential-entropy version by
the continuous transform `entropyPowerExt = exp (2 · h)`. -/
theorem entropyPowerExt_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (entropyPowerExt (P.map Z))) := by
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  -- the differential-entropy version.
  have hdiff := differentialEntropy_map_condTrunc_tendsto P hX hY hXY hZ hZ_ac hZ_ent
  -- the continuous exp-lift map `g h := ofReal (exp (2h))`.
  have hcont : Continuous (fun h : ℝ => ENNReal.ofReal (Real.exp (2 * h))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  -- limit side: `Nₑ (P.map Z) = ofReal (exp (2 h(P.map Z)))`.
  have hlim_eq : entropyPowerExt (P.map Z)
      = ENNReal.ofReal (Real.exp (2 * differentialEntropy (P.map Z))) :=
    entropyPowerExt_of_ac_integrable hZ_ac hZ_ent
  rw [hlim_eq]
  -- lift the differential-entropy tendsto through `g`, then `Tendsto.congr'` over the
  -- eventual positive-mass set where `Nₑ (condTrunc.map Z) = ofReal (exp (2 h))`.
  have hlifted := (hcont.tendsto (differentialEntropy (P.map Z))).comp hdiff
  refine hlifted.congr' ?_
  filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
  -- per-n: `(condTrunc.map Z) ≪ vol` and finite entropy ⟹ `Nₑ = ofReal (exp (2h))`.
  have hac_n : ((condTrunc P X Y n).map Z) ≪ volume :=
    map_condTrunc_absolutelyContinuous P hX hZmeas hZ_ac
  have hent_n : Integrable
      (fun x => Real.negMulLog (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) volume :=
    integrable_negMulLog_map_condTrunc P hX hY hXY hZ hZ_ac hZ_ent hpos
  show ENNReal.ofReal (Real.exp (2 * differentialEntropy ((condTrunc P X Y n).map Z)))
      = entropyPowerExt ((condTrunc P X Y n).map Z)
  exact (entropyPowerExt_of_ac_integrable hac_n hent_n).symm

/-- The sequence `h((condTrunc P X Y n).map (X + Y))` is bounded above (`IsBoundedUnder (≤)`) and
cobounded below (`IsCoboundedUnder (≤)`) along `atTop`. These supply the `bddAbove` / `cobdd`
premises for the monotone-continuous `limsup` push in the entropy-power upper semicontinuity
bound.

The upper bound comes from the per-`n` Gibbs bound `h(μ_n) ≤ RHS_n` plus convergence of `RHS_n`;
the coboundedness comes from the per-`n` lower bound `Nₑ(μ_n) ≥ Nₑ(X_n)`, taking logs to get
`h(μ_n) ≥ (1/2) log (Nₑ(X).toReal / 2)` eventually. The entropy finiteness hypotheses are
regularity preconditions.
@audit:ok -/
theorem differentialEntropy_condTrunc_sum_bddUnder (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    IsBoundedUnder (· ≤ ·) atTop
        (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)))
      ∧ IsCoboundedUnder (· ≤ ·) atTop
        (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) := by
  refine ⟨?_, ?_⟩
  · -- bounded above: from Gibbs (C) `h(μ_n) ≤ RHS_n` + RHS_n bounded (D converges).
    have hC : ∀ᶠ n in atTop,
        differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
          ≤ crossEntropySeq P X Y n :=
      differentialEntropy_condTrunc_sum_le_crossEntropy
        P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum
    have hD : Tendsto (fun n => crossEntropySeq P X Y n) atTop
        (𝓝 (differentialEntropy (P.map (fun ω => X ω + Y ω)))) :=
      crossEntropySeq_tendsto P hX hY hXY hX_ac hY_ac hent_sum
    exact hD.isBoundedUnder_le.mono_le hC
  · -- cobounded below: per-n EPI lower bound `h(μ_n) ≥ (1/2) log (Nₑ(X).toReal / 2)`.
    have hsum_meas : Measurable (fun ω => X ω + Y ω) := hX.add hY
    -- `cX = Nₑ(P.map X).toReal = exp (2 h(X)) > 0`.
    have hX_law_pow : entropyPowerExt (P.map X)
        = ENNReal.ofReal (Real.exp (2 * differentialEntropy (P.map X))) :=
      entropyPowerExt_of_ac_integrable hX_ac hX_ent
    set cX : ℝ := (entropyPowerExt (P.map X)).toReal with hcX_def
    have hcX_eq : cX = Real.exp (2 * differentialEntropy (P.map X)) := by
      rw [hcX_def, hX_law_pow, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    have hcX_pos : 0 < cX := by rw [hcX_eq]; exact Real.exp_pos _
    -- `Nₑ(X_n).toReal → cX`.
    have hX_tendsto : Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map X)) atTop
        (𝓝 (entropyPowerExt (P.map X))) :=
      entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inl rfl) hX_ac hX_ent
    have hX_toReal_tendsto :
        Tendsto (fun n => (entropyPowerExt ((condTrunc P X Y n).map X)).toReal) atTop (𝓝 cX) := by
      rw [hcX_def]
      exact (ENNReal.continuousAt_toReal (by rw [hX_law_pow]; exact ENNReal.ofReal_ne_top)).tendsto.comp
        hX_tendsto
    -- eventually `Nₑ(X_n).toReal ≥ cX / 2`.
    have hX_ev : ∀ᶠ n in atTop, cX / 2 ≤ (entropyPowerExt ((condTrunc P X Y n).map X)).toReal := by
      have : (0 : ℝ) < cX / 2 := by linarith
      have hlt : cX / 2 < cX := by linarith
      filter_upwards [hX_toReal_tendsto.eventually_const_lt hlt] with n hn using hn.le
    -- assemble:  for positive-mass `n`,  `h(μ_n) ≥ (1/2) log (cX / 2)`.
    set c : ℝ := (1 / 2) * Real.log (cX / 2) with hc_def
    refine isCoboundedUnder_le_of_eventually_le atTop (x := c) ?_
    filter_upwards [eventually_measure_truncSet_pos P hX hY, hX_ev] with n hpos hXn
    haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
      isProbabilityMeasure_condTrunc P hX hY hpos
    -- `Nₑ(μ_n) = ofReal (exp (2 h(μ_n)))`,  hence `Nₑ(μ_n).toReal = exp (2 h(μ_n))`.
    have hac_n : ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) ≪ volume := by
      have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
        rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
      have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
      exact (h_cond.map hsum_meas).trans (by rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac)
    have hent_n : Integrable
        (fun x => Real.negMulLog
          (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume :=
      integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hX_ent hY_ent hpos
    have hμn_pow : entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
        = ENNReal.ofReal (Real.exp (2 * differentialEntropy
            ((condTrunc P X Y n).map (fun ω => X ω + Y ω)))) :=
      entropyPowerExt_of_ac_integrable hac_n hent_n
    set hμn : ℝ := differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) with hμn_def
    have hμn_toReal : (entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))).toReal
        = Real.exp (2 * hμn) := by
      rw [hμn_pow, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    -- per-n EPI:  `Nₑ(X_n) ≤ Nₑ(μ_n)`  (drop `+ Nₑ(Y_n)`).
    have hepi : entropyPowerExt ((condTrunc P X Y n).map X)
          + entropyPowerExt ((condTrunc P X Y n).map Y)
        ≤ entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) :=
      entropyPowerExt_condTrunc_add_ge P hX hY hXY hX_ac hY_ac hX_ent hY_ent hpos
    have hXn_le : entropyPowerExt ((condTrunc P X Y n).map X)
        ≤ entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) :=
      le_trans le_self_add hepi
    have hμn_ne_top : entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) ≠ ⊤ := by
      rw [hμn_pow]; exact ENNReal.ofReal_ne_top
    -- `exp (2 hμn) = Nₑ(μ_n).toReal ≥ Nₑ(X_n).toReal ≥ cX/2`.
    have hchain : cX / 2 ≤ Real.exp (2 * hμn) := by
      rw [← hμn_toReal]
      exact le_trans hXn (ENNReal.toReal_mono hμn_ne_top hXn_le)
    -- take logs:  `2 hμn = log (exp (2 hμn)) ≥ log (cX/2)`,  so `hμn ≥ (1/2) log (cX/2) = c`.
    have hlog : Real.log (cX / 2) ≤ 2 * hμn := by
      rw [← Real.log_exp (2 * hμn)]
      exact Real.log_le_log (by linarith) hchain
    show c ≤ hμn
    rw [hc_def]; linarith

/-- Upper semicontinuity of differential entropy under conditioning truncation:
`limsupₙ h((condTrunc P X Y n).map (X + Y)) ≤ h(P.map (X + Y))`.

Assembled from the per-`n` Gibbs bound `h(μ_n) ≤ RHS_n`, convergence `RHS_n → h(ν)`, and
boundedness, into `limsup h(μ_n) ≤ limsup RHS_n = h(ν)`. The hypothesis `hent_sum` is a
finite-differential-entropy regularity precondition.
@audit:ok -/
theorem differentialEntropy_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
  set h_seq : ℕ → ℝ :=
    fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) with hseq_def
  set hν : ℝ := differentialEntropy (P.map (fun ω => X ω + Y ω)) with hhν_def
  -- sub-helper C: `h_seq n ≤ RHS_n` eventually.
  have hC : ∀ᶠ n in atTop, h_seq n ≤ crossEntropySeq P X Y n :=
    differentialEntropy_condTrunc_sum_le_crossEntropy
      P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum
  -- sub-helper D: `RHS_n → hν`.
  have hD : Tendsto (fun n => crossEntropySeq P X Y n) atTop (𝓝 hν) :=
    crossEntropySeq_tendsto P hX hY hXY hX_ac hY_ac hent_sum
  -- boundedness of `h_seq`.
  obtain ⟨_hbdd, hcobdd⟩ :=
    differentialEntropy_condTrunc_sum_bddUnder
      P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum
  -- `RHS_n` is bounded above (it converges).
  have hRHS_bdd : IsBoundedUnder (· ≤ ·) atTop (fun n => crossEntropySeq P X Y n) :=
    hD.isBoundedUnder_le
  -- `limsup h_seq ≤ limsup RHS_n = hν`.
  calc Filter.limsup h_seq atTop
      ≤ Filter.limsup (fun n => crossEntropySeq P X Y n) atTop :=
        Filter.limsup_le_limsup hC hcobdd hRHS_bdd
    _ = hν := hD.limsup_eq

/-- Upper semicontinuity of the entropy power under conditioning truncation:
`limsupₙ Nₑ((condTrunc P X Y n).map (X + Y)) ≤ Nₑ(P.map (X + Y))`.

The differential-entropy version is lifted through the monotone continuous map
`g h := ENNReal.ofReal (exp (2 · h))`, rewriting both sides as `g ∘ h` and pushing the `limsup`
through `g` via `Monotone.map_limsup_of_continuousAt`. The hypothesis `hent_sum` is a regularity
precondition.
@audit:ok -/
theorem entropyPowerExt_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ entropyPowerExt (P.map (fun ω => X ω + Y ω)) := by
  set ν := P.map (fun ω => X ω + Y ω) with hν_def
  have hsum_meas : Measurable (fun ω => X ω + Y ω) := hX.add hY
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  have hν_ac : ν ≪ volume := by
    rw [hν_def]
    have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  -- the continuous monotone lift `g h := ofReal (exp (2 h))`.
  set g : ℝ → ℝ≥0∞ := fun h => ENNReal.ofReal (Real.exp (2 * h)) with hg_def
  have hg_mono : Monotone g := by
    intro a b hab
    exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr (by linarith))
  have hg_cont : Continuous g :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  -- abbreviations.
  set h_seq : ℕ → ℝ :=
    fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) with hseq_def
  set hν : ℝ := differentialEntropy ν with hhν_def
  -- per-n rewrite: `Nₑ(μ_n) = g (h_seq n)` eventually.
  have hper_n : ∀ᶠ n in atTop,
      entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) = g (h_seq n) := by
    filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
    have hac_n : ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) ≪ volume := by
      have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
        rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
      have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
      exact (h_cond.map hsum_meas).trans (by rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac)
    have hent_n : Integrable
        (fun x => Real.negMulLog
          (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume :=
      integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hX_ent hY_ent hpos
    rw [entropyPowerExt_of_ac_integrable hac_n hent_n]
  -- limit rewrite: `Nₑ(ν) = g hν`.
  have hlim_eq : entropyPowerExt ν = g hν :=
    entropyPowerExt_of_ac_integrable hν_ac hent_sum
  -- boundedness for the monotone-continuous limsup push.
  obtain ⟨hbdd, hcobdd⟩ :=
    differentialEntropy_condTrunc_sum_bddUnder
      P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum
  -- `limsup Nₑ(μ_n) = limsup (g ∘ h_seq)`.
  have hcongr : Filter.limsup
      (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      = Filter.limsup (fun n => g (h_seq n)) atTop :=
    Filter.limsup_congr hper_n
  rw [hcongr, hlim_eq]
  -- `limsup (g ∘ h_seq) = g (limsup h_seq)` via the continuous-monotone push.
  have hpush : g (Filter.limsup h_seq atTop) = Filter.limsup (fun n => g (h_seq n)) atTop :=
    hg_mono.map_limsup_of_continuousAt h_seq (hg_cont.continuousAt) hbdd hcobdd
  rw [← hpush]
  -- `g (limsup h_seq) ≤ g hν` by monotonicity + the differential-entropy usc (#3).
  refine hg_mono ?_
  exact differentialEntropy_condTrunc_sum_limsup_le
    P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum


end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
