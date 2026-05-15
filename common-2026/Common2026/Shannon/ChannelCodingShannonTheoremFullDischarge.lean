import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.ChannelCodingShannonTheoremGeneral
import Common2026.Shannon.IIDProductInput
import Common2026.Shannon.AEPRate
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# D-1'' Phase D — parent surgery seeds (Phase D.0 + D.0')

[D-1'' ムーンショット plan](../../../docs/shannon/channel-coding-shannon-theorem-general-plan.md)
の parent surgery の **入口** に位置する 2 補題:

* `exists_smooth_capacity_gt_uniform` (Phase D.0): δ-uniform 化形。`R < capacity W` から
  `p₀ ∈ stdSimplex`, `δ_B > 0`, `R₁ > R` を抽出し、`∀ δ ∈ (0, δ_B]` で
  `R₁ < I(p₀; W_smooth δ).toReal` を保証する。
* `pSmooth_smooth_capacity_gt_uniform` (Phase D.0'): full-support 統合形。
  `R < capacity W` から `p₀, δ_p, δ_B` を抽出し、`p := pSmooth p₀ δ_p` が full support
  かつ `∀ δ ∈ (0, δ_B], R < I(p; W_smooth δ).toReal` を保証する。

## Approach

`continuous_mutualInfoOfChannel_right_smooth` (右側 `δ` の連続性、`p` 固定) を pmf
`pSmooth p₀ δ_p` で direct に instantiate する。joint `(p, δ)`-連続性は不要:

1. `capacity_lt_implies_exists_pmf` で `p₀` を取り、`R < I(p₀; W).toReal` を得る。
2. `continuous_mutualInfoOfChannel_left` (左側 `p` の連続性、`W` 固定) と
   `continuous_pSmooth` 合成で `δ_p ↦ I(pSmooth p₀ δ_p; W).toReal` の `δ_p ∈ [0,1]`
   連続性を得る。`δ_p = 0` で `I(p₀; W) > R` なので、十分小さい `δ_p > 0` で
   `I(pSmooth p₀ δ_p; W) > R` 維持。
3. `p := pSmooth p₀ δ_p` を固定し、`continuous_mutualInfoOfChannel_right_smooth` で
   `δ ↦ I(p; Channel.smooth W δ).toReal` の `δ ∈ [0,1]` 連続性。
4. `δ = 0` で `I(p; W) > R`、連続性より小さい `δ_B > 0` で
   `∀ δ ∈ (0, δ_B], R < I(p; W_smooth δ).toReal` 維持。

`Metric.mem_nhdsWithin_iff` で η を抽出 → `δ_B := min(η/2, 1)` パターン (既存
`exists_smooth_capacity_gt` と同形)。
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Phase D.0** (δ-uniform 化形): `R < capacity W` から `p₀ ∈ stdSimplex`、
`δ_B ∈ (0, 1]`、`R₁ > R` を抽出。`∀ δ ∈ (0, δ_B]` で
`R₁ < I(p₀; W_smooth δ).toReal` が成立。 -/
theorem exists_smooth_capacity_gt_uniform
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p₀ ∈ stdSimplex ℝ α, ∃ δ_B : ℝ, 0 < δ_B ∧ δ_B ≤ 1 ∧
      ∃ R₁ : ℝ, R < R₁ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ_B,
        R₁ < (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ)).toReal := by
  -- Step 1: extract p₀ with R < I(p₀; W).toReal.
  obtain ⟨p₀, hp₀_mem, hp₀_lt⟩ := capacity_lt_implies_exists_pmf W hR
  set I₀ : ℝ := (mutualInfoOfChannel (pmfToMeasure p₀) W).toReal with hI₀_def
  -- Midpoint R₁ = (R + I₀) / 2.
  set R₁ : ℝ := (R + I₀) / 2 with hR₁_def
  have hR_lt_R₁ : R < R₁ := by rw [hR₁_def]; linarith
  have hR₁_lt_I₀ : R₁ < I₀ := by rw [hR₁_def]; linarith
  -- Step 2: continuity of f(δ) := I(p₀; W_smooth δ).toReal on [0,1].
  set f : ℝ → ℝ := fun δ =>
    (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ)).toReal with hf_def
  have hf_cont_on : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    continuous_mutualInfoOfChannel_right_smooth hp₀_mem W
  -- f 0 = I₀.
  have hf_zero : f 0 = I₀ := by
    simp only [hf_def, hI₀_def]
    rw [Channel.smooth_zero W]
  have hf_zero_gt : R₁ < f 0 := by rw [hf_zero]; exact hR₁_lt_I₀
  -- Continuity at 0.
  have h_at_zero : ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) 0 :=
    hf_cont_on 0 ⟨le_refl _, by norm_num⟩
  have h_ev_gt : ∀ᶠ δ in (nhdsWithin (0 : ℝ) (Set.Icc 0 1)), R₁ < f δ := by
    have := h_at_zero.tendsto
    exact this.eventually_const_lt hf_zero_gt
  have h_ev_gt_mem : {δ | R₁ < f δ} ∈ 𝓝[Set.Icc (0 : ℝ) 1] 0 := h_ev_gt
  rw [Metric.mem_nhdsWithin_iff] at h_ev_gt_mem
  obtain ⟨η, hη_pos, h_η⟩ := h_ev_gt_mem
  set δ_B : ℝ := min (η / 2) 1 with hδ_B_def
  have hδ_B_pos : 0 < δ_B := by
    rw [hδ_B_def]; exact lt_min (by linarith) (by norm_num)
  have hδ_B_le_1 : δ_B ≤ 1 := min_le_right _ _
  have hδ_B_le_half_η : δ_B ≤ η / 2 := min_le_left _ _
  -- Conclude.
  refine ⟨p₀, hp₀_mem, δ_B, hδ_B_pos, hδ_B_le_1, R₁, hR_lt_R₁, ?_⟩
  intro δ hδ_mem
  -- δ ∈ (0, δ_B] ⟹ δ ∈ Metric.ball 0 η ∩ Set.Icc 0 1.
  obtain ⟨hδ_pos, hδ_le⟩ := hδ_mem
  have hδ_lt_η : δ < η := by
    have h1 : δ ≤ η / 2 := hδ_le.trans hδ_B_le_half_η
    linarith
  have hδ_le_1 : δ ≤ 1 := hδ_le.trans hδ_B_le_1
  have hδ_mem_ball : δ ∈ Metric.ball (0 : ℝ) η := by
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hδ_pos]
    exact hδ_lt_η
  have hδ_mem_Icc : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ_pos.le, hδ_le_1⟩
  exact h_η ⟨hδ_mem_ball, hδ_mem_Icc⟩

/-- **Phase D.0'** (pSmooth full-support 統合形): `R < capacity W` から
`p₀, δ_p, δ_B`、および `I_lb > R` を抽出。`pSmooth p₀ δ_p` は各成分 > 0 の full-support
pmf であり、`∀ δ ∈ (0, δ_B]` で `I_lb < I(pSmooth p₀ δ_p; W_smooth δ).toReal` が成立。 -/
theorem pSmooth_smooth_capacity_gt_uniform
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p₀ ∈ stdSimplex ℝ α, ∃ δ_p δ_B : ℝ,
      0 < δ_p ∧ δ_p ≤ 1 ∧ 0 < δ_B ∧ δ_B ≤ 1 ∧
      ∃ I_lb : ℝ, R < I_lb ∧
      (∀ a, 0 < pSmooth p₀ δ_p a) ∧
      pSmooth p₀ δ_p ∈ stdSimplex ℝ α ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ_B,
        I_lb < (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p)) (Channel.smooth W δ)).toReal := by
  -- Step 1: extract p₀ with R < I(p₀; W).toReal.
  obtain ⟨p₀, hp₀_mem, hp₀_lt⟩ := capacity_lt_implies_exists_pmf W hR
  set I₀ : ℝ := (mutualInfoOfChannel (pmfToMeasure p₀) W).toReal with hI₀_def
  -- Two midpoints: R₂ between R and I₀; I_lb between R and R₂.
  --   R < I_lb < R₂ < I₀.
  set R₂ : ℝ := (R + I₀) / 2 with hR₂_def
  set I_lb : ℝ := (R + R₂) / 2 with hI_lb_def
  have hR_lt_I_lb : R < I_lb := by rw [hI_lb_def, hR₂_def]; linarith
  have hI_lb_lt_R₂ : I_lb < R₂ := by rw [hI_lb_def]; linarith
  have hR₂_lt_I₀ : R₂ < I₀ := by rw [hR₂_def]; linarith
  -- Step 2: continuity in p of I(·; W).toReal at p₀.
  -- Compose: g(δ_p) := I(pSmooth p₀ δ_p; W).toReal is continuous on [0,1].
  set g : ℝ → ℝ := fun δp =>
    (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δp)) W).toReal with hg_def
  have h_curve : ContinuousOn (fun δp : ℝ => pSmooth p₀ δp) (Set.Icc (0 : ℝ) 1) :=
    (continuous_pSmooth p₀).continuousOn
  have h_maps_g : Set.MapsTo (fun δp : ℝ => pSmooth p₀ δp) (Set.Icc 0 1) (stdSimplex ℝ α) :=
    fun δp hδp => pSmooth_mem_stdSimplex hp₀_mem hδp.1 hδp.2
  have hg_cont_on : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    (continuous_mutualInfoOfChannel_left W).comp h_curve h_maps_g
  -- g 0 = I₀.
  have hg_zero : g 0 = I₀ := by
    simp only [hg_def, hI₀_def]
    rw [pSmooth_zero]
  have hg_zero_gt : R₂ < g 0 := by rw [hg_zero]; exact hR₂_lt_I₀
  have h_at_zero_g : ContinuousWithinAt g (Set.Icc (0 : ℝ) 1) 0 :=
    hg_cont_on 0 ⟨le_refl _, by norm_num⟩
  have h_ev_g : ∀ᶠ δp in (nhdsWithin (0 : ℝ) (Set.Icc 0 1)), R₂ < g δp := by
    have := h_at_zero_g.tendsto
    exact this.eventually_const_lt hg_zero_gt
  have h_ev_g_mem : {δp | R₂ < g δp} ∈ 𝓝[Set.Icc (0 : ℝ) 1] 0 := h_ev_g
  rw [Metric.mem_nhdsWithin_iff] at h_ev_g_mem
  obtain ⟨η_p, hη_p_pos, h_η_p⟩ := h_ev_g_mem
  -- Pick δ_p > 0 small.
  set δ_p : ℝ := min (η_p / 2) 1 with hδ_p_def
  have hδ_p_pos : 0 < δ_p := by
    rw [hδ_p_def]; exact lt_min (by linarith) (by norm_num)
  have hδ_p_le_1 : δ_p ≤ 1 := min_le_right _ _
  have hδ_p_lt_η : δ_p < η_p := by
    rw [hδ_p_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ_p_mem_Icc : δ_p ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ_p_pos.le, hδ_p_le_1⟩
  have hδ_p_mem_ball : δ_p ∈ Metric.ball (0 : ℝ) η_p := by
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hδ_p_pos]
    exact hδ_p_lt_η
  have hg_δ_p : R₂ < g δ_p := h_η_p ⟨hδ_p_mem_ball, hδ_p_mem_Icc⟩
  -- p_full := pSmooth p₀ δ_p ∈ stdSimplex, with all components > 0.
  set p_full : α → ℝ := pSmooth p₀ δ_p with hp_full_def
  have hp_full_mem : p_full ∈ stdSimplex ℝ α :=
    pSmooth_mem_stdSimplex hp₀_mem hδ_p_pos.le hδ_p_le_1
  have hp_full_pos : ∀ a, 0 < p_full a :=
    fun a => pSmooth_pos hp₀_mem hδ_p_pos hδ_p_le_1 a
  -- Step 3: continuity of f(δ) := I(p_full; W_smooth δ).toReal on [0,1].
  set f : ℝ → ℝ := fun δ =>
    (mutualInfoOfChannel (pmfToMeasure p_full) (Channel.smooth W δ)).toReal with hf_def
  have hf_cont_on : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    continuous_mutualInfoOfChannel_right_smooth hp_full_mem W
  -- f 0 = I(p_full; W).toReal = g δ_p.
  have hf_zero : f 0 = g δ_p := by
    simp only [hf_def, hg_def]
    rw [Channel.smooth_zero W]
  have hf_zero_gt : I_lb < f 0 := by
    rw [hf_zero]
    exact hI_lb_lt_R₂.trans hg_δ_p
  -- Continuity at 0 ⟹ small δ keeps f > I_lb.
  have h_at_zero_f : ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) 0 :=
    hf_cont_on 0 ⟨le_refl _, by norm_num⟩
  have h_ev_f : ∀ᶠ δ in (nhdsWithin (0 : ℝ) (Set.Icc 0 1)), I_lb < f δ := by
    have := h_at_zero_f.tendsto
    exact this.eventually_const_lt hf_zero_gt
  have h_ev_f_mem : {δ | I_lb < f δ} ∈ 𝓝[Set.Icc (0 : ℝ) 1] 0 := h_ev_f
  rw [Metric.mem_nhdsWithin_iff] at h_ev_f_mem
  obtain ⟨η, hη_pos, h_η⟩ := h_ev_f_mem
  set δ_B : ℝ := min (η / 2) 1 with hδ_B_def
  have hδ_B_pos : 0 < δ_B := by
    rw [hδ_B_def]; exact lt_min (by linarith) (by norm_num)
  have hδ_B_le_1 : δ_B ≤ 1 := min_le_right _ _
  have hδ_B_le_half_η : δ_B ≤ η / 2 := min_le_left _ _
  -- Conclude.
  refine ⟨p₀, hp₀_mem, δ_p, δ_B, hδ_p_pos, hδ_p_le_1, hδ_B_pos, hδ_B_le_1,
    I_lb, hR_lt_I_lb, hp_full_pos, hp_full_mem, ?_⟩
  intro δ hδ_mem
  obtain ⟨hδ_pos, hδ_le⟩ := hδ_mem
  have hδ_lt_η : δ < η := by
    have h1 : δ ≤ η / 2 := hδ_le.trans hδ_B_le_half_η
    linarith
  have hδ_le_1 : δ ≤ 1 := hδ_le.trans hδ_B_le_1
  have hδ_mem_ball : δ ∈ Metric.ball (0 : ℝ) η := by
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hδ_pos]
    exact hδ_lt_η
  have hδ_mem_Icc : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ_pos.le, hδ_le_1⟩
  exact h_η ⟨hδ_mem_ball, hδ_mem_Icc⟩

/-! ## Phase D.1 — δ-asymptotic `pmfLog` bounds for `iidAmbientMeasure p (Channel.smooth W δ)`

Phase D.2 で parent `channel_coding_achievability` の body を `μ := iidAmbientMeasure p (W_smooth δ)`
で呼び出す際、内部の `pmfLogVariance μ iidYs` / `pmfLogVariance μ jointSequence` に対する
δ-asymptotic bound が必要になる。本節は **pointwise pmfLog bound** を 3 形 (`iidXs` /
`iidYs` / `jointSequence`) で publish する。variance への lift (Popoviciu) は parent body
で `variance_le_sq_of_bounded` を直接呼ぶ形で吸収するため、本節では行わない。

最後に解析的補題 `exists_N_log_sq_le_n` (Mathlib 完備の `Real.tendsto_pow_log_div_mul_add_atTop`
からの再構成) を置く。N₁(δ) closed-form 化で `C · (log (n+1))² + 1 ≤ n` を満たす N の存在に使う。
-/

open InformationTheory.Shannon (pmfLog)

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [MeasurableSingletonClass β] in
/-- **D.1.3** — `iidXs` の pmfLog は `W` (および smooth の `δ`) に依存しない。
`iidAmbient_map_iidXs` により marginal は常に `p` に等しいため。 -/
lemma pmfLog_iidXs_const_in_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (a : α) :
    pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidXs a
      = pmfLog (iidAmbientMeasure p W) iidXs a := by
  haveI : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  unfold pmfLog
  rw [iidAmbient_map_iidXs p (Channel.smooth W δ) 0, iidAmbient_map_iidXs p W 0]

omit [DecidableEq α] [Nonempty α] in
/-- **D.1.1** — `iidYs` の pmfLog は smooth で `log(|β|/δ)` で押さえられる。
`(W_smooth δ a).real {b} ≥ δ/|β|` を経由した output 下限。 -/
lemma pmfLog_iidYs_bound_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (b : β) :
    |pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidYs b|
      ≤ Real.log ((Fintype.card β : ℝ) / δ) := by
  classical
  haveI : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  -- |β| ≥ 1.
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_inv_pos : (0 : ℝ) < (Fintype.card β : ℝ)⁻¹ := inv_pos.mpr hβ_pos
  -- Step 1: pmfLog rewritten as -log of the smooth output.
  have h_map : (iidAmbientMeasure p (Channel.smooth W δ)).map (iidYs 0)
      = outputDistribution p (Channel.smooth W δ) :=
    iidAmbient_map_iidYs p (Channel.smooth W δ) 0
  have h_pmfLog_eq : pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidYs b
      = -Real.log ((outputDistribution p (Channel.smooth W δ)).real {b}) := by
    unfold pmfLog
    rw [h_map]
  -- Step 2: lower bound for the output.
  -- (outputDistribution p (W_smooth δ)).real {b} ≥ δ / |β|.
  have h_out_sum : (outputDistribution p (Channel.smooth W δ)).real {b}
      = ∑ a : α, p.real {a} * (Channel.smooth W δ a).real {b} := by
    -- Reuse the inline argument from `ChannelCodingAchievability`.
    have h1 : (outputDistribution p (Channel.smooth W δ)) {b}
        = (jointDistribution p (Channel.smooth W δ)) (Set.univ ×ˢ ({b} : Set β)) := by
      show (jointDistribution p (Channel.smooth W δ)).snd {b} = _
      rw [Measure.snd_apply (measurableSet_singleton _)]
      congr 1; ext ⟨a, b'⟩; simp
    rw [measureReal_def, h1, jointDistribution_def]
    have h2 : (p ⊗ₘ (Channel.smooth W δ)) (Set.univ ×ˢ ({b} : Set β))
        = ∫⁻ a, (Channel.smooth W δ a) {b} ∂p := by
      rw [Measure.compProd_apply (MeasurableSet.univ.prod (measurableSet_singleton _))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      show (Channel.smooth W δ a) (Prod.mk a ⁻¹' (Set.univ ×ˢ ({b} : Set β)))
          = (Channel.smooth W δ a) {b}
      congr 1; ext y; simp
    rw [h2, lintegral_fintype,
        ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
          (measure_ne_top _ _) (measure_ne_top _ _))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ENNReal.toReal_mul]
    show (Channel.smooth W δ a).real {b} * p.real {a}
        = p.real {a} * (Channel.smooth W δ a).real {b}
    ring
  -- Each (W_smooth δ a).real{b} ≥ δ / |β|.
  have h_term_lb : ∀ a : α,
      δ * (Fintype.card β : ℝ)⁻¹ ≤ (Channel.smooth W δ a).real {b} := by
    intro a
    rw [Channel.smooth_real_singleton W hδ_pos.le hδ_le]
    have h1 : 0 ≤ (1 - δ) * (W a).real {b} :=
      mul_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  -- Sum lower bound.
  have h_sum_p : ∑ a : α, p.real {a} = 1 := by
    have h_univ : (∑ a : α, p.real {a}) = p.real (Set.univ : Set α) := by
      rw [measureReal_def]
      have h_sum_ennreal : (∑ a : α, p {a}) = p (Set.univ : Set α) := by
        rw [← measure_biUnion_finset (s := (Finset.univ : Finset α))
          (f := fun a => ({a} : Set α))
          (fun i _ j _ hij => by
            simpa [Set.disjoint_singleton] using hij)
          (fun i _ => measurableSet_singleton _)]
        congr 1
        ext a
        simp
      rw [← h_sum_ennreal, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
      rfl
    rw [h_univ]
    exact MeasureTheory.probReal_univ
  have h_out_lb : δ * (Fintype.card β : ℝ)⁻¹
      ≤ (outputDistribution p (Channel.smooth W δ)).real {b} := by
    rw [h_out_sum]
    calc δ * (Fintype.card β : ℝ)⁻¹
        = (∑ a : α, p.real {a}) * (δ * (Fintype.card β : ℝ)⁻¹) := by
          rw [h_sum_p]; ring
      _ = ∑ a : α, p.real {a} * (δ * (Fintype.card β : ℝ)⁻¹) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ a : α, p.real {a} * (Channel.smooth W δ a).real {b} := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          have hpa_nn : 0 ≤ p.real {a} := ENNReal.toReal_nonneg
          exact mul_le_mul_of_nonneg_left (h_term_lb a) hpa_nn
  -- Upper bound: ≤ 1 (probability measure).
  haveI : IsProbabilityMeasure (outputDistribution p (Channel.smooth W δ)) := by
    unfold outputDistribution; infer_instance
  have h_out_ub : (outputDistribution p (Channel.smooth W δ)).real {b} ≤ 1 := by
    rw [measureReal_def]
    have h_le : (outputDistribution p (Channel.smooth W δ)) {b} ≤ 1 := by
      have h1 := prob_le_one (μ := outputDistribution p (Channel.smooth W δ)) (s := ({b} : Set β))
      exact h1
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by rw [ENNReal.ofReal_one]; exact h_le)
  -- Lower bound of output > 0.
  have h_dlb_pos : 0 < δ * (Fintype.card β : ℝ)⁻¹ := mul_pos hδ_pos hβ_inv_pos
  have h_out_pos : 0 < (outputDistribution p (Channel.smooth W δ)).real {b} :=
    lt_of_lt_of_le h_dlb_pos h_out_lb
  -- Step 3: combine: log of value in [δ/|β|, 1] has |.| ≤ log(|β|/δ).
  rw [h_pmfLog_eq]
  -- log_target := log((outputDistribution).real {b})
  set q : ℝ := (outputDistribution p (Channel.smooth W δ)).real {b} with hq_def
  -- We have q ∈ (0, 1], q ≥ δ / |β|.
  -- log q ∈ [log(δ/|β|), 0], so -log q ∈ [0, -log(δ/|β|)] = [0, log(|β|/δ)].
  have h_log_nonpos : Real.log q ≤ 0 := Real.log_nonpos h_out_pos.le h_out_ub
  have h_log_lb : Real.log (δ * (Fintype.card β : ℝ)⁻¹) ≤ Real.log q :=
    Real.log_le_log h_dlb_pos h_out_lb
  have h_neg_log_lb : 0 ≤ -Real.log q := by linarith
  have h_target_eq : Real.log ((Fintype.card β : ℝ) / δ)
      = -Real.log (δ * (Fintype.card β : ℝ)⁻¹) := by
    rw [show (Fintype.card β : ℝ) / δ = (δ * (Fintype.card β : ℝ)⁻¹)⁻¹ by
      field_simp]
    exact Real.log_inv _
  rw [abs_of_nonneg h_neg_log_lb, h_target_eq]
  linarith

omit [DecidableEq α] [DecidableEq β] in
/-- **D.1.2** — `jointSequence` の pmfLog は smooth で
`log(|α|·|β| / (p_min · δ))` で押さえられる。 -/
lemma pmfLog_jointSequence_bound_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    {p_min : ℝ} (hp_min_pos : 0 < p_min)
    (hp_min_le : ∀ a : α, p_min ≤ p.real {a})
    (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (ab : α × β) :
    |pmfLog (iidAmbientMeasure p (Channel.smooth W δ))
        (jointSequence iidXs iidYs) ab|
      ≤ Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ))
          / (p_min * δ)) := by
  classical
  haveI : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  obtain ⟨a, b⟩ := ab
  -- Cardinality positivity.
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_inv_pos : (0 : ℝ) < (Fintype.card β : ℝ)⁻¹ := inv_pos.mpr hβ_pos
  have hαβ_pos : (0 : ℝ) < (Fintype.card α : ℝ) * (Fintype.card β : ℝ) :=
    mul_pos hα_pos hβ_pos
  have hp_min_δ_pos : (0 : ℝ) < p_min * δ := mul_pos hp_min_pos hδ_pos
  -- Step 1: marginal identification.
  have h_map : (iidAmbientMeasure p (Channel.smooth W δ)).map
      (jointSequence iidXs iidYs 0) = jointDistribution p (Channel.smooth W δ) :=
    iidAmbient_map_jointSequence p (Channel.smooth W δ) 0
  have h_pmfLog_eq : pmfLog (iidAmbientMeasure p (Channel.smooth W δ))
        (jointSequence iidXs iidYs) (a, b)
      = -Real.log ((jointDistribution p (Channel.smooth W δ)).real {(a, b)}) := by
    unfold pmfLog
    rw [h_map]
  -- Step 2: joint singleton real-value = p.real {a} * (W_smooth δ a).real {b}.
  have h_joint_real : (jointDistribution p (Channel.smooth W δ)).real {(a, b)}
      = p.real {a} * (Channel.smooth W δ a).real {b} := by
    rw [measureReal_def, jointDistribution_singleton, ENNReal.toReal_mul]
    rfl
  -- Step 3: lower bound. (W_smooth δ a).real{b} ≥ δ/|β|, p.real{a} ≥ p_min.
  have h_term_lb : δ * (Fintype.card β : ℝ)⁻¹
      ≤ (Channel.smooth W δ a).real {b} := by
    rw [Channel.smooth_real_singleton W hδ_pos.le hδ_le]
    have h1 : 0 ≤ (1 - δ) * (W a).real {b} :=
      mul_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  have h_term_lb_pos : (0 : ℝ) < δ * (Fintype.card β : ℝ)⁻¹ := mul_pos hδ_pos hβ_inv_pos
  have h_smooth_pos : 0 < (Channel.smooth W δ a).real {b} :=
    lt_of_lt_of_le h_term_lb_pos h_term_lb
  -- joint ≥ p_min * (δ/|β|).
  have h_joint_lb : p_min * (δ * (Fintype.card β : ℝ)⁻¹)
      ≤ (jointDistribution p (Channel.smooth W δ)).real {(a, b)} := by
    rw [h_joint_real]
    exact mul_le_mul (hp_min_le a) h_term_lb h_term_lb_pos.le ENNReal.toReal_nonneg
  -- joint > 0.
  have h_joint_lb_pos : (0 : ℝ) < p_min * (δ * (Fintype.card β : ℝ)⁻¹) :=
    mul_pos hp_min_pos h_term_lb_pos
  have h_joint_pos : 0 < (jointDistribution p (Channel.smooth W δ)).real {(a, b)} :=
    lt_of_lt_of_le h_joint_lb_pos h_joint_lb
  -- Step 4: upper bound ≤ 1.
  have h_joint_ub : (jointDistribution p (Channel.smooth W δ)).real {(a, b)} ≤ 1 := by
    rw [measureReal_def]
    have h_le : (jointDistribution p (Channel.smooth W δ)) {(a, b)} ≤ 1 :=
      prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by rw [ENNReal.ofReal_one]; exact h_le)
  -- Step 5: target log.
  -- Loose target: log(|α||β| / (p_min·δ)) ≥ log(|β|/(p_min·δ)) ≥ -log(p_min · (δ/|β|)).
  have h_target_eq_alt : Real.log ((Fintype.card β : ℝ) / (p_min * δ))
      = -Real.log (p_min * (δ * (Fintype.card β : ℝ)⁻¹)) := by
    rw [show ((Fintype.card β : ℝ) / (p_min * δ))
          = (p_min * (δ * (Fintype.card β : ℝ)⁻¹))⁻¹ by
      field_simp]
    exact Real.log_inv _
  -- |α| ≥ 1 ⇒ log(|α|·|β| / (p_min·δ)) ≥ log(|β| / (p_min·δ)).
  have hα_ge_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have h_div_le : (Fintype.card β : ℝ) / (p_min * δ)
      ≤ ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ) := by
    refine div_le_div_of_nonneg_right ?_ hp_min_δ_pos.le
    have hβ_nn : 0 ≤ (Fintype.card β : ℝ) := hβ_pos.le
    calc (Fintype.card β : ℝ)
        = 1 * (Fintype.card β : ℝ) := (one_mul _).symm
      _ ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) :=
          mul_le_mul_of_nonneg_right hα_ge_one hβ_nn
  have h_log_div_le : Real.log ((Fintype.card β : ℝ) / (p_min * δ))
      ≤ Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ)) := by
    refine Real.log_le_log ?_ h_div_le
    exact div_pos hβ_pos hp_min_δ_pos
  -- Combine: -log q ≤ -log(p_min · δ/|β|) = log(|β|/(p_min·δ)) ≤ log(|α|·|β|/(p_min·δ)).
  rw [h_pmfLog_eq]
  set q : ℝ := (jointDistribution p (Channel.smooth W δ)).real {(a, b)} with hq_def
  have h_log_q_nonpos : Real.log q ≤ 0 := Real.log_nonpos h_joint_pos.le h_joint_ub
  have h_log_q_lb : Real.log (p_min * (δ * (Fintype.card β : ℝ)⁻¹)) ≤ Real.log q :=
    Real.log_le_log h_joint_lb_pos h_joint_lb
  have h_neg_log_nn : 0 ≤ -Real.log q := by linarith
  rw [abs_of_nonneg h_neg_log_nn]
  -- -log q ≤ -log(p_min · δ/|β|) = log(|β|/(p_min·δ))
  have h_neg_log_q_le : -Real.log q ≤ Real.log ((Fintype.card β : ℝ) / (p_min * δ)) := by
    rw [h_target_eq_alt]; linarith
  linarith

/-- **D.1.7** (解析的補題) — 任意の `C > 0` に対し `C · (log (n+1))² + 1 ≤ n` を満たす
`N` が存在する。Mathlib `Real.tendsto_pow_log_div_mul_add_atTop` を経由。 -/
lemma exists_N_log_sq_le_n (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (Real.log ((n : ℝ) + 1))^2 + 1 ≤ (n : ℝ) := by
  -- Step 1: (log x)^2 / x → 0 as x → ∞.
  have h_lim : Filter.Tendsto (fun x : ℝ => (Real.log x)^2 / x) Filter.atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    -- `(fun x => log x ^ 2 / (1 * x + 0))` simplifies to `(fun x => (log x)^2 / x)`.
    simpa using h
  -- Step 2: eventually (log x)^2 / x < 1 / (4C).
  have h_pos : (0 : ℝ) < 1 / (4 * C) := by positivity
  have h_ev : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x)^2 / x < 1 / (4 * C) := by
    -- |.| → 0 at nhds 0 gives the eventual upper bound.
    exact h_lim.eventually_lt_const h_pos
  -- Step 3: pick `x₀ ≥ max (1, 4)` so the bound + `x ≥ 4` together suffice.
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨x₀, hx₀⟩ := h_ev
  set N : ℕ := max (Nat.ceil x₀) 4 with hN_def
  refine ⟨N, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := by
    have : (4 : ℕ) ≤ N := le_max_right _ _
    exact this.trans hn
  have hn_x₀ : x₀ ≤ (n : ℝ) := by
    have h1 : (Nat.ceil x₀ : ℕ) ≤ N := le_max_left _ _
    have h2 : x₀ ≤ (Nat.ceil x₀ : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil x₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1.trans hn
    linarith
  -- We want `C * (log (n+1))^2 + 1 ≤ n`. Apply the eventual bound at `x := n + 1`.
  have hn1_x₀ : x₀ ≤ (n : ℝ) + 1 := by linarith
  have hbound : (Real.log ((n : ℝ) + 1))^2 / ((n : ℝ) + 1) < 1 / (4 * C) := hx₀ ((n : ℝ) + 1) hn1_x₀
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    linarith
  -- Multiply the bound by (n+1) > 0:  (log(n+1))^2 < (n+1) / (4C).
  have hsq_bound : (Real.log ((n : ℝ) + 1))^2 < ((n : ℝ) + 1) / (4 * C) := by
    have := (div_lt_iff₀ h_n1_pos).mp hbound
    have h4C_pos : (0 : ℝ) < 4 * C := by linarith
    rw [div_eq_mul_inv, ← div_eq_mul_inv] at this
    -- this : (log (n+1))^2 < (n+1) * (1 / (4C)) = (n+1) / (4C).
    have h_rewrite : ((n : ℝ) + 1) * (1 / (4 * C)) = ((n : ℝ) + 1) / (4 * C) := by
      field_simp
    linarith [this, h_rewrite]
  -- Hence C * (log(n+1))^2 < (n+1) / 4.
  have hCsq : C * (Real.log ((n : ℝ) + 1))^2 < ((n : ℝ) + 1) / 4 := by
    have h_mul := (mul_lt_mul_of_pos_left hsq_bound hC)
    -- C * ((n+1)/(4C)) = (n+1) / 4.
    have h_eq : C * (((n : ℝ) + 1) / (4 * C)) = ((n : ℝ) + 1) / 4 := by
      field_simp
    linarith
  -- Finally: (n+1)/4 + 1 ≤ n iff n ≥ 5/3, but our n ≥ 4 gives a more comfortable margin:
  -- (n+1)/4 + 1 = (n+5)/4. We want (n+5)/4 ≤ n, i.e., n+5 ≤ 4n, i.e., n ≥ 5/3.
  -- Since n ≥ 4, we have n ≥ 2, so 3n ≥ 5.
  have hn_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have h_final : ((n : ℝ) + 1) / 4 + 1 ≤ (n : ℝ) := by linarith
  linarith

/-- **D.1.8** (generalization of D.1.7) — for any `C > 0` and any constant `D`,
there exists `N` such that `C * (log(n+1))² + D ≤ n` for all `n ≥ N`.
Used in Phase D.3 outer-`N` construction. -/
lemma exists_N_log_sq_plus_const_le_n (C D : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (Real.log ((n : ℝ) + 1))^2 + D ≤ (n : ℝ) := by
  -- Use exists_N_log_sq_le_n with `2C`, then absorb D via N ≥ 2|D|.
  obtain ⟨N₁, hN₁⟩ := exists_N_log_sq_le_n (2 * C) (by linarith)
  set N : ℕ := max N₁ (Nat.ceil (2 * D + 2))
  refine ⟨N, fun n hn => ?_⟩
  have hN₁_le : N₁ ≤ n := (le_max_left _ _).trans hn
  have h2D_le : (Nat.ceil (2 * D + 2) : ℕ) ≤ n := (le_max_right _ _).trans hn
  have h2D_real : 2 * D + 2 ≤ (n : ℝ) := by
    have h_le : (2 * D + 2 : ℝ) ≤ (Nat.ceil (2 * D + 2 : ℝ) : ℝ) := Nat.le_ceil _
    have h_nat_le : ((Nat.ceil (2 * D + 2 : ℝ) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h2D_le
    linarith
  -- From hN₁: 2C(log(n+1))² + 1 ≤ n, so C(log(n+1))² ≤ (n - 1)/2.
  have h_log_sq := hN₁ n hN₁_le
  have hC_log_sq_le : C * (Real.log ((n : ℝ) + 1))^2 ≤ ((n : ℝ) - 1) / 2 := by
    have h1 : 2 * C * (Real.log ((n : ℝ) + 1))^2 ≤ (n : ℝ) - 1 := by linarith
    linarith
  -- D ≤ (n - 2)/2 from `2 * D + 2 ≤ n`, i.e., `D ≤ (n - 2)/2`.
  have hD_le : D ≤ ((n : ℝ) - 2) / 2 := by linarith
  linarith

/-! ## Phase D.2 — parent achievability instantiated at `(pSmooth p₀ δ_p, Channel.smooth W δ)`

`channel_coding_achievability` を `p := pmfToMeasure (pSmooth p₀ δ_p)`、
`W := Channel.smooth W δ` で呼び出す wrapper。`hp_pos`/`hW_pos` を内部で導出する。

* `IsMarkovKernel (Channel.smooth W δ)` は `Channel.smooth_isMarkovKernel`。
* `IsProbabilityMeasure (pmfToMeasure (pSmooth p₀ δ_p))` は
  `pmfToMeasure_isProbabilityMeasure ∘ pSmooth_mem_stdSimplex`。
* `hp_pos`: `(pmfToMeasure (pSmooth p₀ δ_p)).real {a} = pSmooth p₀ δ_p a > 0`
  (`pmfToMeasure_real_singleton` + `pSmooth_pos`).
* `hW_pos`: `0 < (Channel.smooth W δ a).real {b}` は `Channel.smooth_pos`.

N(δ) closed-form 化は後段 Phase D.3 に委譲し、本 wrapper は既存 `∃ N` 形を保つ。 -/

/-- **Phase D.2** — parent achievability を smooth な `(p, W)` で呼び出す wrapper。
`p := pmfToMeasure (pSmooth p₀ δ_p)`、`W := Channel.smooth W δ` で
parent `channel_coding_achievability` を発火する。 -/
theorem channel_coding_achievability_smooth_closed_form
    (W : Channel α β) [IsMarkovKernel W]
    (p₀ : α → ℝ) (hp₀_mem : p₀ ∈ stdSimplex ℝ α)
    {δ_p : ℝ} (hδ_p_pos : 0 < δ_p) (hδ_p_le : δ_p ≤ 1)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    {R : ℝ} (hR_pos : 0 < R)
    (hR_lt_I : R <
      (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p))
        (Channel.smooth W δ)).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb (Channel.smooth W δ)).toReal < ε' := by
  -- Markov / probability instances.
  haveI hWsmooth_mk : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  have hp_full_mem : pSmooth p₀ δ_p ∈ stdSimplex ℝ α :=
    pSmooth_mem_stdSimplex hp₀_mem hδ_p_pos.le hδ_p_le
  haveI hp_full_prob : IsProbabilityMeasure (pmfToMeasure (pSmooth p₀ δ_p)) :=
    pmfToMeasure_isProbabilityMeasure hp_full_mem
  -- `hp_pos`: every singleton of `pmfToMeasure (pSmooth p₀ δ_p)` is positive.
  have hp_pos : ∀ a : α, 0 < (pmfToMeasure (pSmooth p₀ δ_p)).real {a} := by
    intro a
    rw [pmfToMeasure_real_singleton hp_full_mem]
    exact pSmooth_pos hp₀_mem hδ_p_pos hδ_p_le a
  -- `hW_pos`: every (a, b) atom of `Channel.smooth W δ` is positive.
  have hW_pos : ∀ a : α, ∀ b : β, 0 < (Channel.smooth W δ a).real {b} :=
    Channel.smooth_pos W hδ_pos hδ_le
  exact channel_coding_achievability (Channel.smooth W δ)
    (pmfToMeasure (pSmooth p₀ δ_p)) hp_pos hW_pos hR_pos hR_lt_I hε'

/-! ## Phase D.2 (closed-form N) — parent achievability with explicit `N` formula

Phase D.3 needs `N` exposed as a closed-form function of the inputs (so that
substituting `δ_n := ε/(8(n+1))` can be verified to satisfy `N(δ_n) ≤ n` via
`exists_N_log_sq_le_n`). This section publishes a variant of Phase D.2 where
the existential `∃ N` is collapsed to `channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε'`
— directly using the AEPRate closed-form lemmas. -/

/-- Closed-form `N(V_X, V_Y, V_Z, I_lb, R, ε')` for the smooth achievability
theorem. The construction matches the parent body's `max (max N₁ N₂) 1` form:

* `N₁` = `jointlyTypicalSetMinN V_X V_Y V_Z (ε'/2) ((I_lb - R)/6)` (joint AEP).
* `N₂` = `expNegMulMinN ((I_lb - R)/2) (ε'/2)` (E2 exponential decay).
* `1` to ensure `0 < M`.

Note: we use the lower bound `I_lb` of the mutual information; the parent's
gap `g = I - R - 3·(I-R)/6 = (I - R)/2` becomes `g ≥ (I_lb - R)/2`, which only
makes `N₂` larger (safe upper bound). -/
noncomputable def channelCodingSmoothMinN
    (V_X V_Y V_Z I_lb R ε' : ℝ) : ℕ :=
  max (max
        (jointlyTypicalSetMinN V_X V_Y V_Z (ε' / 2) ((I_lb - R) / 6))
        (expNegMulMinN ((I_lb - R) / 2) (ε' / 2)))
      1

/-- **Phase D.2 (closed-form N)** — `channel_coding_achievability` with the
existential `N` replaced by `channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε'`.

Caller supplies axis-wise variance upper bounds `V_X, V_Y, V_Z` (which will
typically be `pmfLogBound²` from Phase D.1) and a mutual-information lower
bound `I_lb` (from Phase D.0'). -/
theorem channel_coding_achievability_smooth_at_N_le
    (W : Channel α β) [IsMarkovKernel W]
    (p₀ : α → ℝ) (hp₀_mem : p₀ ∈ stdSimplex ℝ α)
    {δ_p : ℝ} (hδ_p_pos : 0 < δ_p) (hδ_p_le : δ_p ≤ 1)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    {R I_lb : ℝ} (hR_pos : 0 < R) (hR_lt_I_lb : R < I_lb)
    (hI_lb_le_I : I_lb ≤
      (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p))
        (Channel.smooth W δ)).toReal)
    (V_X V_Y V_Z : ℝ)
    (hV_X : pmfLogVariance
        (iidAmbientMeasure (pmfToMeasure (pSmooth p₀ δ_p)) (Channel.smooth W δ))
        iidXs ≤ V_X)
    (hV_Y : pmfLogVariance
        (iidAmbientMeasure (pmfToMeasure (pSmooth p₀ δ_p)) (Channel.smooth W δ))
        iidYs ≤ V_Y)
    (hV_Z : pmfLogVariance
        (iidAmbientMeasure (pmfToMeasure (pSmooth p₀ δ_p)) (Channel.smooth W δ))
        (jointSequence iidXs iidYs) ≤ V_Z)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∀ n, channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb (Channel.smooth W δ)).toReal < ε' := by
  classical
  -- Markov / probability instances.
  haveI hWsmooth_mk : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  have hp_full_mem : pSmooth p₀ δ_p ∈ stdSimplex ℝ α :=
    pSmooth_mem_stdSimplex hp₀_mem hδ_p_pos.le hδ_p_le
  haveI hp_full_prob : IsProbabilityMeasure (pmfToMeasure (pSmooth p₀ δ_p)) :=
    pmfToMeasure_isProbabilityMeasure hp_full_mem
  have hp_pos : ∀ a : α, 0 < (pmfToMeasure (pSmooth p₀ δ_p)).real {a} := by
    intro a
    rw [pmfToMeasure_real_singleton hp_full_mem]
    exact pSmooth_pos hp₀_mem hδ_p_pos hδ_p_le a
  have hW_pos : ∀ a : α, ∀ b : β, 0 < (Channel.smooth W δ a).real {b} :=
    Channel.smooth_pos W hδ_pos hδ_le
  -- Aliases for the parent-body proof.
  set p : Measure α := pmfToMeasure (pSmooth p₀ δ_p) with hp_def
  set Wδ : Channel α β := Channel.smooth W δ with hWδ_def
  -- Step 1: rate slack uses `I_lb` (not the exact mutual info).
  set I : ℝ := (mutualInfoOfChannel p Wδ).toReal with hI_def
  have hI_pos : 0 < I := lt_of_lt_of_le (lt_trans hR_pos hR_lt_I_lb) hI_lb_le_I
  set ε : ℝ := (I_lb - R) / 6 with hε_def
  have hI_lb_R_pos : 0 < I_lb - R := by linarith
  have hε_pos : 0 < ε := by
    rw [hε_def]
    exact div_pos hI_lb_R_pos (by norm_num)
  -- Gap based on `I_lb` (looser than parent's gap based on exact `I`).
  have h_gap_lb_pos : 0 < I_lb - R - 3 * ε := by
    have h1 : 3 * ε = (I_lb - R) / 2 := by rw [hε_def]; ring
    rw [h1]; linarith
  -- Parent's gap is at least the I_lb-gap.
  have h_gap_pos : 0 < I - R - 3 * ε := by
    have : I_lb ≤ I := hI_lb_le_I
    linarith
  have hR_3ε_lt_I : R + 3 * ε < I := by linarith
  -- Step 2: i.i.d. ambient `μ := iidAmbientMeasure p Wδ`.
  set Ω : Type _ := ℕ → α × β
  set μ : Measure Ω := iidAmbientMeasure p Wδ with hμ_def
  haveI : IsProbabilityMeasure μ := by
    rw [hμ_def]; infer_instance
  have hXs : ∀ i, Measurable (iidXs (α := α) (β := β) i) := measurable_iidXs
  have hYs : ∀ i, Measurable (iidYs (α := α) (β := β) i) := measurable_iidYs
  have hindepX_full : iIndepFun (fun i => iidXs (α := α) (β := β) i) μ :=
    iidAmbient_iIndepFun_iidXs p Wδ
  have hindepY_full : iIndepFun (fun i => iidYs (α := α) (β := β) i) μ :=
    iidAmbient_iIndepFun_iidYs p Wδ
  have hindepX_pair : Pairwise fun i j =>
      iidXs (α := α) (β := β) i ⟂ᵢ[μ] iidXs j :=
    iidAmbient_pairwise_indep_iidXs p Wδ
  have hindepY_pair : Pairwise fun i j =>
      iidYs (α := α) (β := β) i ⟂ᵢ[μ] iidYs j :=
    iidAmbient_pairwise_indep_iidYs p Wδ
  have hindepZ : Pairwise fun i j =>
      jointSequence (α := α) (β := β) iidXs iidYs i ⟂ᵢ[μ]
        jointSequence iidXs iidYs j :=
    iidAmbient_pairwise_indep_joint p Wδ
  have hidentX : ∀ i,
      IdentDistrib (iidXs (α := α) (β := β) i) (iidXs 0) μ μ :=
    fun i => iidAmbient_identDistrib_iidXs p Wδ i
  have hidentY : ∀ i,
      IdentDistrib (iidYs (α := α) (β := β) i) (iidYs 0) μ μ :=
    fun i => iidAmbient_identDistrib_iidYs p Wδ i
  have hidentZ : ∀ i,
      IdentDistrib (jointSequence (α := α) (β := β) iidXs iidYs i)
        (jointSequence iidXs iidYs 0) μ μ :=
    fun i => iidAmbient_identDistrib_joint p Wδ i
  have hposX : ∀ x : α, 0 < (μ.map (iidXs (α := α) (β := β) 0)).real {x} :=
    fun x => iidAmbient_iidXs_real_singleton_pos p Wδ hp_pos x
  have hposY : ∀ y : β, 0 < (μ.map (iidYs (α := α) (β := β) 0)).real {y} :=
    fun y => iidAmbient_iidYs_real_singleton_pos p Wδ hp_pos hW_pos y
  have hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence (α := α) (β := β) iidXs iidYs 0)).real {q} :=
    fun q => iidAmbient_joint_real_singleton_pos p Wδ hp_pos hW_pos q
  have h_match_X : μ.map (iidXs (α := α) (β := β) 0) = p :=
    iidAmbient_map_iidXs p Wδ 0
  have h_match_Z : μ.map (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = jointDistribution p Wδ :=
    iidAmbient_map_jointSequence p Wδ 0
  -- Step 3: entropy exponent equation (HZ - HX - HY = -I).
  have h_entZ : InformationTheory.Shannon.entropy μ
      (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = InformationTheory.Shannon.entropy (jointDistribution p Wδ) id := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p Wδ)
      (jointSequence iidXs iidYs 0) id ?_
    refine ⟨(measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs 0).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    rw [iidAmbient_map_jointSequence, Measure.map_id]
  have h_entX : InformationTheory.Shannon.entropy μ (iidXs (α := α) (β := β) 0)
        = InformationTheory.Shannon.entropy (jointDistribution p Wδ) Prod.fst := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p Wδ)
      (iidXs 0) Prod.fst ?_
    refine ⟨(measurable_iidXs 0).aemeasurable, measurable_fst.aemeasurable, ?_⟩
    rw [iidAmbient_map_iidXs]
    show p = (jointDistribution p Wδ).map Prod.fst
    rw [show ((jointDistribution p Wδ).map Prod.fst) = (jointDistribution p Wδ).fst from rfl,
        jointDistribution_def]
    exact (Measure.fst_compProd p Wδ).symm
  have h_entY : InformationTheory.Shannon.entropy μ (iidYs (α := α) (β := β) 0)
        = InformationTheory.Shannon.entropy (jointDistribution p Wδ) Prod.snd := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p Wδ)
      (iidYs 0) Prod.snd ?_
    refine ⟨(measurable_iidYs 0).aemeasurable, measurable_snd.aemeasurable, ?_⟩
    rw [iidAmbient_map_iidYs]
    rfl
  have h_exp_eq : InformationTheory.Shannon.entropy μ
        (jointSequence (α := α) (β := β) iidXs iidYs 0)
      - InformationTheory.Shannon.entropy μ (iidXs 0)
      - InformationTheory.Shannon.entropy μ (iidYs 0) = -I := by
    rw [h_entZ, h_entX, h_entY]
    have hMI := mutualInfoOfChannel_eq_HX_add_HY_sub_HZ p Wδ
    rw [← hI_def] at hMI
    linarith
  -- Step 4-5: closed-form `N₁` from `jointlyTypicalSet_prob_ge_at_N_le`.
  have hε'_half : 0 < ε' / 2 := by linarith
  intro n hn_ge
  -- Extract sub-bounds from `channelCodingSmoothMinN ≤ n`.
  have hn_N₁ : jointlyTypicalSetMinN V_X V_Y V_Z (ε' / 2) ε ≤ n := by
    have h1 : jointlyTypicalSetMinN V_X V_Y V_Z (ε' / 2) ε ≤
        channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' := by
      unfold channelCodingSmoothMinN
      exact (le_max_left _ _).trans (le_max_left _ _)
    exact h1.trans hn_ge
  have hn_N₂ : expNegMulMinN ((I_lb - R) / 2) (ε' / 2) ≤ n := by
    have h1 : expNegMulMinN ((I_lb - R) / 2) (ε' / 2) ≤
        channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' := by
      unfold channelCodingSmoothMinN
      exact (le_max_right _ _).trans (le_max_left _ _)
    exact h1.trans hn_ge
  have hn_one : 1 ≤ n := by
    have h1 : 1 ≤ channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' := by
      unfold channelCodingSmoothMinN
      exact le_max_right _ _
    exact h1.trans hn_ge
  -- Joint AEP closed form.
  have hN₁ := jointlyTypicalSet_prob_ge_at_N_le (β := β) μ iidXs iidYs hXs hYs
      hindepX_pair hidentX hindepY_pair hidentY hindepZ hidentZ
      V_X V_Y V_Z hV_X hV_Y hV_Z hε_pos hε'_half n hn_N₁
  -- E2 closed form with `g := (I_lb - R)/2`. We then bound `-I + 3ε ≤ -I_lb + 3ε`
  -- and apply `channelCoding_E2_lt_at_N` with `(I_lb, R, ε)`.
  -- `channelCoding_E2_lt_at_N` gives:
  --   `(⌈exp(nR)⌉ - 1) * exp(n(-I_lb + 3ε)) < ε'/2`
  -- whenever `expNegMulMinN (I_lb - R - 3ε) (ε'/2) ≤ n` i.e.
  -- `expNegMulMinN ((I_lb - R)/2) (ε'/2) ≤ n`.
  have h_gap_eq : (I_lb - R) / 2 = I_lb - R - 3 * ε := by
    rw [hε_def]; ring
  have hN₂ := channelCoding_E2_lt_at_N (I := I_lb) (R := R) (ε := ε) (ε' := ε' / 2)
      h_gap_lb_pos hε'_half n (by rw [h_gap_eq] at hn_N₂; exact hn_N₂)
  -- Step 8: assemble.
  set M : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R)) with hM_def
  have hM_pos : 0 < M := Nat.ceil_pos.mpr (Real.exp_pos _)
  refine ⟨M, le_refl _, ?_⟩
  have hindepZ_full : iIndepFun
      (fun i : ℕ => jointSequence (α := α) (β := β) iidXs iidYs i) μ :=
    iidAmbient_iIndepFun_joint p Wδ
  have h_avg_bound :=
    random_codebook_average_le (M := M) (n := n) Wδ p hp_pos hM_pos hε_pos μ iidXs iidYs
      hXs hYs hindepX_full hidentX hindepY_full hidentY hindepZ hindepZ_full hidentZ
      hposX hposY hposZ h_match_X h_match_Z
  set E1 : ℝ := μ.real
      {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
            InformationTheory.Shannon.jointRV iidYs n ω) ∉
          jointlyTypicalSet μ iidXs iidYs n ε} with hE1_def
  set E2 : ℝ := ((M : ℝ) - 1) *
      Real.exp ((n : ℝ) *
        ((InformationTheory.Shannon.entropy μ (jointSequence iidXs iidYs 0)
          - InformationTheory.Shannon.entropy μ (iidXs 0)
          - InformationTheory.Shannon.entropy μ (iidYs 0)) + 3 * ε)) with hE2_def
  have h_E2_simp : E2 = ((M : ℝ) - 1) *
      Real.exp ((n : ℝ) * (-I + 3 * ε)) := by
    rw [hE2_def]
    congr 2
    rw [h_exp_eq]
  -- Measurability of joint "good" event.
  have h_meas_good : MeasurableSet
      {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
            InformationTheory.Shannon.jointRV iidYs n ω) ∈
          jointlyTypicalSet μ iidXs iidYs n ε} := by
    have h_meas_pair : Measurable (fun ω =>
        (InformationTheory.Shannon.jointRV (α := α) iidXs n ω,
          InformationTheory.Shannon.jointRV (α := β) iidYs n ω)) :=
      (InformationTheory.Shannon.measurable_jointRV iidXs hXs n).prodMk
        (InformationTheory.Shannon.measurable_jointRV iidYs hYs n)
    exact h_meas_pair (measurableSet_jointlyTypicalSet _ _ _ _ _)
  -- E1 ≤ ε'/2 via the joint-AEP closed form.
  have hE1_le : E1 ≤ ε' / 2 := by
    rw [hE1_def]
    have h_compl_eq :
        {ω | (InformationTheory.Shannon.jointRV (α := α) iidXs n ω,
              InformationTheory.Shannon.jointRV (α := β) iidYs n ω) ∉
            jointlyTypicalSet μ iidXs iidYs n ε}
          = {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                InformationTheory.Shannon.jointRV iidYs n ω) ∈
              jointlyTypicalSet μ iidXs iidYs n ε}ᶜ := rfl
    rw [h_compl_eq, probReal_compl_eq_one_sub h_meas_good]
    have h_good_real_eq : μ.real
        {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
              InformationTheory.Shannon.jointRV iidYs n ω) ∈
            jointlyTypicalSet μ iidXs iidYs n ε}
        = (μ {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
              InformationTheory.Shannon.jointRV iidYs n ω) ∈
            jointlyTypicalSet μ iidXs iidYs n ε}).toReal := rfl
    rw [h_good_real_eq]
    linarith
  -- E2 ≤ ε'/2 — but `hN₂` is at exponent `-I_lb + 3ε`, while `E2` simplifies to `-I + 3ε`.
  -- Since `I_lb ≤ I`, we have `-I + 3ε ≤ -I_lb + 3ε`, so the E2 value is smaller.
  have hE2_lt : E2 < ε' / 2 := by
    rw [h_E2_simp]
    have h_exp_mono :
        Real.exp ((n : ℝ) * (-I + 3 * ε)) ≤ Real.exp ((n : ℝ) * (-I_lb + 3 * ε)) := by
      apply Real.exp_le_exp.mpr
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have h_le : -I + 3 * ε ≤ -I_lb + 3 * ε := by linarith [hI_lb_le_I]
      exact mul_le_mul_of_nonneg_left h_le hn_nn
    have hM_sub_nn : 0 ≤ (M : ℝ) - 1 := by
      have : 1 ≤ (M : ℝ) := by exact_mod_cast hM_pos
      linarith
    have h_E2_le :
        ((M : ℝ) - 1) * Real.exp ((n : ℝ) * (-I + 3 * ε))
          ≤ ((M : ℝ) - 1) * Real.exp ((n : ℝ) * (-I_lb + 3 * ε)) :=
      mul_le_mul_of_nonneg_left h_exp_mono hM_sub_nn
    have hN₂' : ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
          Real.exp ((n : ℝ) * (-I_lb + 3 * ε)) < ε' / 2 := hN₂
    have hM_eq : ((M : ℝ) - 1) = ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) := by
      simp [hM_def]
    rw [hM_eq]
    exact lt_of_le_of_lt (by rw [hM_eq] at h_E2_le; exact h_E2_le) hN₂'
  have h_sum_lt : E1 + E2 < ε' := by linarith
  obtain ⟨codebook, hcb⟩ :=
    exists_codebook_le_avg μ iidXs iidYs Wδ p hM_pos (B := E1 + E2) h_avg_bound
  refine ⟨codebookToCode μ iidXs iidYs hM_pos ε codebook, ?_⟩
  exact lt_of_le_of_lt hcb h_sum_lt

/-! ## Phase D.3 — outer `N` construction (max-error closed form)

We build, for any `R < capacity W` and `ε > 0`, an `N₀` such that for every
`n ≥ N₀` we can simultaneously:

* pick `δ_n ∈ (0, δ_B]` with `2 n δ_n < ε/2` (so the TV bound contributes ≤ `ε/2`);
* build a code at the smooth channel `W_smooth δ_n` with `max-error < ε/2`.

The construction:

1. Phase D.0' gives `p_full := pSmooth p₀ δ_p` (full support) with `R < I_lb <
   I(p_full; W_smooth δ)` for all `δ ∈ (0, δ_B]`.
2. Choose an interior rate `R' := (R + I_lb)/2 < I_lb` for the closed-form
   average-error code; we then upgrade to max-error at rate `R` via the
   subcode trick (giving `max-error ≤ 2 · avg < ε/2`).
3. Choose `δ_n := min(δ_B, ε/(16(n+1)))` and check `2 n δ_n < ε/4 < ε/2`.
4. Bound `V_Y(δ_n), V_Z(δ_n) ≤ const + 2 · (log(n+1))²` via the closed-form
   pmfLog bounds, using `1/δ_n ≤ (1/δ_B + 16/ε)·(n+1)` and `(a+b)² ≤ 2a²+2b²`.
5. The closed-form `channelCodingSmoothMinN` is then `O((log(n+1))²)`;
   `exists_N_log_sq_plus_const_le_n` produces the outer `N₀`.
-/

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Lower bound for `pSmooth p₀ δ`: every entry is ≥ `δ / |α|`. -/
lemma pSmooth_ge {p₀ : α → ℝ} (hp₀ : p₀ ∈ stdSimplex ℝ α)
    {δ : ℝ} (_hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) (a : α) :
    δ / (Fintype.card α : ℝ) ≤ pSmooth p₀ δ a := by
  unfold pSmooth uniformInput
  have h1 : 0 ≤ (1 - δ) * p₀ a := mul_nonneg (by linarith) (hp₀.1 a)
  have h_eq : δ * (Fintype.card α : ℝ)⁻¹ = δ / (Fintype.card α : ℝ) := by
    rw [div_eq_mul_inv]
  linarith [h_eq]

/-- For `δ_n := min(δ_B, ε/(16(n+1)))` with `0 < δ_B` and `0 < ε`,
`1/δ_n ≤ (1/δ_B + 16/ε)·(n+1)`. -/
lemma one_div_smooth_n_le
    {δ_B ε : ℝ} (hδ_B_pos : 0 < δ_B) (hε_pos : 0 < ε) (n : ℕ) :
    let δ_n : ℝ := min δ_B (ε / (16 * ((n : ℝ) + 1)))
    1 / δ_n ≤ (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) := by
  intro δ_n
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hε_n_pos : (0 : ℝ) < ε / (16 * ((n : ℝ) + 1)) := by positivity
  have hδ_n_pos : 0 < δ_n := lt_min hδ_B_pos hε_n_pos
  -- 1/min(a,b) = max(1/a, 1/b) for a,b > 0; bound by sum.
  have h_inv_le : 1 / δ_n ≤ 1 / δ_B + 1 / (ε / (16 * ((n : ℝ) + 1))) := by
    -- 1/δ_n ≤ 1/δ_B and 1/δ_n ≤ 1/(ε/(16(n+1))).
    have h1 : δ_n ≤ δ_B := min_le_left _ _
    have h2 : δ_n ≤ ε / (16 * ((n : ℝ) + 1)) := min_le_right _ _
    have h_inv1 : 1 / δ_B ≤ 1 / δ_n := one_div_le_one_div_of_le hδ_n_pos h1
    have h_inv2 : 1 / (ε / (16 * ((n : ℝ) + 1))) ≤ 1 / δ_n :=
      one_div_le_one_div_of_le hδ_n_pos h2
    -- max(1/δ_B, 1/(ε/(16(n+1)))) ≤ 1/δ_n ≤ max + 0 ≤ sum.
    -- Easier: a/δ_n_min uses 1/δ_n = max(1/δ_B, 1/(...))
    -- But simpler: split cases.
    rcases le_or_gt δ_B (ε / (16 * ((n : ℝ) + 1))) with h_case | h_case
    · -- δ_n = δ_B
      have : δ_n = δ_B := by simp [δ_n, min_eq_left h_case]
      rw [this]
      have h_pos2 : 0 < 1 / (ε / (16 * ((n : ℝ) + 1))) := by positivity
      linarith
    · -- δ_n = ε/(16(n+1))
      have : δ_n = ε / (16 * ((n : ℝ) + 1)) := by
        simp [δ_n, min_eq_right h_case.le]
      rw [this]
      have h_pos1 : 0 < 1 / δ_B := by positivity
      linarith
  -- Now `1/(ε/(16(n+1))) = 16(n+1)/ε`.
  have h_inv_eq : (1 : ℝ) / (ε / (16 * ((n : ℝ) + 1))) = 16 * ((n : ℝ) + 1) / ε := by
    rw [one_div, inv_div]
  rw [h_inv_eq] at h_inv_le
  -- 1/δ_B + 16(n+1)/ε ≤ (1/δ_B + 16/ε)(n+1).
  -- (1/δ_B + 16/ε)(n+1) = (n+1)/δ_B + 16(n+1)/ε ≥ 1/δ_B + 16(n+1)/ε iff (n+1)/δ_B ≥ 1/δ_B, true.
  have h_target : 1 / δ_B + 16 * ((n : ℝ) + 1) / ε ≤ (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) := by
    have h_n1_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h1 : 1 / δ_B ≤ ((n : ℝ) + 1) / δ_B := by
      rw [div_le_div_iff₀ hδ_B_pos hδ_B_pos]
      have h2 : (1 : ℝ) * δ_B ≤ ((n : ℝ) + 1) * δ_B :=
        mul_le_mul_of_nonneg_right h_n1_ge_one hδ_B_pos.le
      linarith
    have h_expand : (1 / δ_B + 16 / ε) * ((n : ℝ) + 1)
        = ((n : ℝ) + 1) / δ_B + 16 * ((n : ℝ) + 1) / ε := by
      rw [add_mul]
      rw [show (1 / δ_B) * ((n : ℝ) + 1) = ((n : ℝ) + 1) / δ_B from by
        rw [one_div, inv_mul_eq_div]]
      rw [show (16 / ε) * ((n : ℝ) + 1) = 16 * ((n : ℝ) + 1) / ε from by
        rw [div_mul_eq_mul_div]]
    linarith
  exact h_inv_le.trans h_target

set_option maxHeartbeats 1200000 in
/-- **Phase D.3** — outer `N` construction with simultaneous `δ_n` and max-error
code. For any `R < capacity W` and `ε > 0`, there exists `N₀` such that for all
`n ≥ N₀` we can pick `δ_n` and a code with the two `ε/2` halves. -/
theorem exists_N_for_smooth_achievability_uniform
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1),
        2 * (n : ℝ) * δ < ε / 2 ∧
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
          (c : Code M n α β),
          ∀ m, (c.errorProbAt (Channel.smooth W δ) m).toReal < ε / 2 := by
  classical
  -- Step 1: Phase D.0' to extract uniform smooth capacity.
  obtain ⟨p₀, hp₀_mem, δ_p, δ_B, hδ_p_pos, hδ_p_le, hδ_B_pos, hδ_B_le,
          I_lb, hR_lt_I_lb, hp_full_pos, hp_full_mem, h_MI_uniform⟩ :=
    pSmooth_smooth_capacity_gt_uniform W hR
  -- Step 2: interior rate `R'` and avg target `ε' := ε/8` (so max-error ≤ 2·ε' = ε/4 < ε/2).
  set R' : ℝ := (R + I_lb) / 2 with hR'_def
  have hR_lt_R' : R < R' := by rw [hR'_def]; linarith
  have hR'_lt_I_lb : R' < I_lb := by rw [hR'_def]; linarith
  have hR'_pos : 0 < R' := lt_trans hR_pos hR_lt_R'
  set ε' : ℝ := ε / 8 with hε'_def
  have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
  -- Step 3: `α`/`β` cardinalities and p_min.
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  set p_min : ℝ := δ_p / (Fintype.card α : ℝ) with hp_min_def
  have hp_min_pos : 0 < p_min := by rw [hp_min_def]; positivity
  -- Lower bound: every `pSmooth p₀ δ_p a ≥ p_min`.
  have hp_min_le : ∀ a : α, p_min ≤ pSmooth p₀ δ_p a :=
    fun a => pSmooth_ge hp₀_mem hδ_p_pos hδ_p_le a
  -- Also for the measure version:
  haveI : IsProbabilityMeasure (pmfToMeasure (pSmooth p₀ δ_p)) :=
    pmfToMeasure_isProbabilityMeasure hp_full_mem
  have hp_min_le_meas : ∀ a : α,
      p_min ≤ (pmfToMeasure (pSmooth p₀ δ_p)).real {a} := by
    intro a
    rw [pmfToMeasure_real_singleton hp_full_mem]
    exact hp_min_le a
  -- Step 4: closed-form constant `V_X` (δ-independent).
  -- We use the absolute-value bound `pmfLogBound (iidAmbientMeasure (pmfToMeasure p_full) W) iidXs`,
  -- and `pmfLog_iidXs_const_in_smooth` to lift to the smooth channel.
  set V_X_B : ℝ :=
    pmfLogBound (iidAmbientMeasure (pmfToMeasure (pSmooth p₀ δ_p)) W) iidXs with hV_X_B_def
  set V_X : ℝ := V_X_B ^ 2 with hV_X_def
  -- Step 5: pre-compute log/exp constants for V_Y, V_Z bounds.
  -- K_Y := log(|β|) + log(1/δ_B + 16/ε); we'll show log(|β|/δ_n) ≤ K_Y + log(n+1).
  set K_Y : ℝ := Real.log ((Fintype.card β : ℝ)) +
    Real.log (1 / δ_B + 16 / ε) with hK_Y_def
  -- K_Z := log(|α|·|β|/p_min) + log(1/δ_B + 16/ε); log(|α||β|/(p_min δ_n)) ≤ K_Z + log(n+1).
  set K_Z : ℝ := Real.log ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) / p_min) +
    Real.log (1 / δ_B + 16 / ε) with hK_Z_def
  -- Step 6: identify the constant `D` and coefficient `C` for outer-N.
  -- V_Y(δ_n) ≤ 2·K_Y² + 2·(log(n+1))², V_Z(δ_n) ≤ 2·K_Z² + 2·(log(n+1))².
  -- jointlyTypicalSetMinN V_X V_Y V_Z (ε'/2) ((I_lb - R')/6)
  --   = max(max(typicalSetMinN V_X (ε'/6) ε_gap, typicalSetMinN V_Y(δ_n) (ε'/6) ε_gap),
  --       typicalSetMinN V_Z(δ_n) (ε'/6) ε_gap)
  -- where ε_gap := (I_lb - R')/6.
  -- typicalSetMinN V η ε_gap = max(1, ⌈V/(η·ε_gap²)⌉ + 1) ≤ V/(η·ε_gap²) + 2 + 1.
  set ε_gap : ℝ := (I_lb - R') / 6 with hε_gap_def
  have hI_lb_gt_R' : 0 < I_lb - R' := by linarith
  have hε_gap_pos : 0 < ε_gap := by rw [hε_gap_def]; positivity
  set η : ℝ := ε' / 2 with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; linarith
  have hη3_pos : 0 < η / 3 := by linarith
  -- Coefficient C absorbs `2 / ((η/3) · ε_gap²)`.
  set C_coef : ℝ := 2 / ((η / 3) * ε_gap ^ 2) with hC_coef_def
  have hC_coef_pos : 0 < C_coef := by
    rw [hC_coef_def]; positivity
  -- D_const = sum of: V_X / ((η/3) · ε_gap²) + 2 (the +1 typicalSetMinN constants for X),
  -- + (2·K_Y² + 2·K_Z²) / ((η/3) · ε_gap²) + 4 (for Y, Z),
  -- + expNegMulMinN ((I_lb-R')/2) (ε'/2)  -- constant
  -- + 1 (for the outer max-with-1 of channelCodingSmoothMinN).
  -- We need a numerical upper bound.
  set V_const : ℝ := V_X + 2 * K_Y ^ 2 + 2 * K_Z ^ 2 with hV_const_def
  set D_const : ℝ := V_const / ((η / 3) * ε_gap ^ 2) + 6
    + (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℕ) + 1 with hD_const_def
  -- Step 7: rate inequality for max-error upgrade: 2 ⌈exp(nR)⌉ ≤ ⌈exp(nR')⌉ eventually.
  obtain ⟨N_rate, hN_rate⟩ := exists_N_two_ceil_exp_le hR_pos hR_lt_R'
  -- Step 8: outer N₀ from log-sq absorption.
  obtain ⟨N_log, hN_log⟩ := exists_N_log_sq_plus_const_le_n (2 * C_coef) D_const
    (by linarith [hC_coef_pos])
  set N₀ : ℕ := max N_log N_rate with hN₀_def
  refine ⟨N₀, fun n hn => ?_⟩
  -- Bind δ_n, n inequalities, etc.
  have hn_log : N_log ≤ n := (le_max_left _ _).trans hn
  have hn_rate : N_rate ≤ n := (le_max_right _ _).trans hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  -- Choose δ_n.
  set δ_n : ℝ := min δ_B (ε / (16 * ((n : ℝ) + 1))) with hδ_n_def
  have hε_n_pos : (0 : ℝ) < ε / (16 * ((n : ℝ) + 1)) := by positivity
  have hδ_n_pos : 0 < δ_n := lt_min hδ_B_pos hε_n_pos
  have hδ_n_le_δ_B : δ_n ≤ δ_B := min_le_left _ _
  have hδ_n_le : δ_n ≤ 1 := hδ_n_le_δ_B.trans hδ_B_le
  have hδ_n_le_target : δ_n ≤ ε / (16 * ((n : ℝ) + 1)) := min_le_right _ _
  -- TV target: 2 n δ_n < ε/2.
  have h_2nδ_lt : 2 * (n : ℝ) * δ_n < ε / 2 := by
    have h_target : 2 * (n : ℝ) * δ_n ≤ 2 * (n : ℝ) * (ε / (16 * ((n : ℝ) + 1))) := by
      have hn_nn : 0 ≤ 2 * (n : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hδ_n_le_target hn_nn
    have h_simp : 2 * (n : ℝ) * (ε / (16 * ((n : ℝ) + 1)))
        = ε * ((n : ℝ) / ((n : ℝ) + 1)) / 8 := by
      field_simp; ring
    have h_n_n1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1_pos]
      linarith
    have h_n_n1_nn : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
      apply div_nonneg (Nat.cast_nonneg _) hn1_pos.le
    have h_chain : ε * ((n : ℝ) / ((n : ℝ) + 1)) / 8 < ε / 2 := by
      have h1 : ε * ((n : ℝ) / ((n : ℝ) + 1)) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left h_n_n1 hε.le
      have h2 : ε * 1 / 8 < ε / 2 := by linarith
      have h3 : ε * ((n : ℝ) / ((n : ℝ) + 1)) / 8 ≤ ε * 1 / 8 := by
        exact div_le_div_of_nonneg_right h1 (by norm_num)
      linarith
    linarith [h_target, h_simp, h_chain]
  -- δ_n is in the smooth-capacity range (0, δ_B], so I_lb < MI(p_full; W_smooth δ_n).
  have hδ_n_mem : δ_n ∈ Set.Ioc (0 : ℝ) δ_B := ⟨hδ_n_pos, hδ_n_le_δ_B⟩
  have hMI_δ_n : I_lb <
      (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p))
        (Channel.smooth W δ_n)).toReal :=
    h_MI_uniform δ_n hδ_n_mem
  have hR'_lt_MI : R' < (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p))
        (Channel.smooth W δ_n)).toReal :=
    hR'_lt_I_lb.trans hMI_δ_n
  -- Variance upper bounds:
  -- V_X bound is via `pmfLog_iidXs_const_in_smooth` + `pmfLogVariance_le_sq_of_bounded`.
  -- We work in `μ := iidAmbientMeasure (pmfToMeasure p_full) (Channel.smooth W δ_n)`.
  haveI hWsmooth_mk : IsMarkovKernel (Channel.smooth W δ_n) :=
    Channel.smooth_isMarkovKernel W hδ_n_pos.le hδ_n_le
  set p_meas : Measure α := pmfToMeasure (pSmooth p₀ δ_p) with hp_meas_def
  set μ : Measure (ℕ → α × β) :=
    iidAmbientMeasure p_meas (Channel.smooth W δ_n) with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hXs : ∀ i, Measurable (iidXs (α := α) (β := β) i) := measurable_iidXs
  have hYs : ∀ i, Measurable (iidYs (α := α) (β := β) i) := measurable_iidYs
  -- V_X bound:
  have hV_X_pointwise : ∀ a : α, |pmfLog μ iidXs a| ≤ V_X_B := by
    intro a
    rw [hμ_def, pmfLog_iidXs_const_in_smooth p_meas W hδ_n_pos hδ_n_le a]
    exact abs_pmfLog_le_bound (iidAmbientMeasure p_meas W) iidXs a
  have hV_X_bound : pmfLogVariance μ iidXs ≤ V_X :=
    pmfLogVariance_le_sq_of_bounded μ iidXs hXs hV_X_pointwise
  -- V_Y pointwise bound: |pmfLog μ iidYs b| ≤ log(|β|/δ_n).
  have hV_Y_pointwise : ∀ b : β,
      |pmfLog μ iidYs b| ≤ Real.log ((Fintype.card β : ℝ) / δ_n) := by
    intro b
    rw [hμ_def]
    exact pmfLog_iidYs_bound_smooth p_meas W hδ_n_pos hδ_n_le b
  -- V_Z pointwise bound: |pmfLog μ joint| ≤ log(|α||β|/(p_min·δ_n)).
  have hV_Z_pointwise : ∀ ab : α × β,
      |pmfLog μ (jointSequence iidXs iidYs) ab| ≤
        Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n)) := by
    intro ab
    rw [hμ_def]
    exact pmfLog_jointSequence_bound_smooth p_meas hp_min_pos hp_min_le_meas
      W hδ_n_pos hδ_n_le ab
  -- Now bound log(|β|/δ_n) ≤ K_Y + log(n+1), and (log(|β|/δ_n))² ≤ 2 K_Y² + 2 (log(n+1))².
  have h_one_div_δ_n_le : 1 / δ_n ≤ (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) :=
    one_div_smooth_n_le hδ_B_pos hε n
  have h_sum_pos : (0 : ℝ) < 1 / δ_B + 16 / ε := by positivity
  have h_log_β_δ_n_le : Real.log ((Fintype.card β : ℝ) / δ_n) ≤ K_Y + Real.log ((n : ℝ) + 1) := by
    -- |β|/δ_n = |β| · (1/δ_n) ≤ |β| · (1/δ_B + 16/ε) · (n+1)
    have h_eq1 : (Fintype.card β : ℝ) / δ_n = (Fintype.card β : ℝ) * (1 / δ_n) := by
      rw [one_div, div_eq_mul_inv]
    have h_β_pos : (0 : ℝ) < (Fintype.card β : ℝ) := hβ_pos
    have h_lhs_le : (Fintype.card β : ℝ) / δ_n
        ≤ (Fintype.card β : ℝ) * (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) := by
      rw [h_eq1]
      have h_mul_le : (Fintype.card β : ℝ) * (1 / δ_n)
          ≤ (Fintype.card β : ℝ) * ((1 / δ_B + 16 / ε) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h_one_div_δ_n_le h_β_pos.le
      linarith [h_mul_le]
    have h_lhs_pos : (0 : ℝ) < (Fintype.card β : ℝ) / δ_n := by positivity
    have h_mid_pos : (0 : ℝ) < (Fintype.card β : ℝ) * (1 / δ_B + 16 / ε) :=
      mul_pos h_β_pos h_sum_pos
    have h_rhs_pos : (0 : ℝ) < (Fintype.card β : ℝ) * (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) :=
      mul_pos h_mid_pos hn1_pos
    have h_log_le := Real.log_le_log h_lhs_pos h_lhs_le
    have h_log_split :
        Real.log ((Fintype.card β : ℝ) * (1 / δ_B + 16 / ε) * ((n : ℝ) + 1))
          = Real.log ((Fintype.card β : ℝ)) + Real.log (1 / δ_B + 16 / ε)
            + Real.log ((n : ℝ) + 1) := by
      rw [Real.log_mul h_mid_pos.ne' hn1_pos.ne',
          Real.log_mul h_β_pos.ne' h_sum_pos.ne']
    have hK_eq : K_Y = Real.log ((Fintype.card β : ℝ)) + Real.log (1 / δ_B + 16 / ε) := by
      rfl
    linarith [h_log_le, h_log_split, hK_eq]
  -- Similarly for V_Z bound.
  have hαβ_pos : (0 : ℝ) < (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := mul_pos hα_pos hβ_pos
  have hαβ_pmin_pos : (0 : ℝ) < (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / p_min := by
    positivity
  have h_log_Z_le : Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))
      ≤ K_Z + Real.log ((n : ℝ) + 1) := by
    -- (|α||β|)/(p_min δ_n) = (|α||β|/p_min) · (1/δ_n) ≤ (|α||β|/p_min) · (1/δ_B + 16/ε) · (n+1)
    set A : ℝ := (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / p_min with hA_def
    have hA_pos : 0 < A := hαβ_pmin_pos
    have h_eq1 : ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n) = A * (1 / δ_n) := by
      rw [hA_def]
      rw [div_mul_eq_div_div]
      rw [div_eq_mul_inv (A) _, one_div]
    have h_lhs_le : ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n)
        ≤ A * (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) := by
      rw [h_eq1]
      have := mul_le_mul_of_nonneg_left h_one_div_δ_n_le hA_pos.le
      linarith
    have h_lhs_pos : (0 : ℝ) < ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n) := by
      positivity
    have h_mid_pos : (0 : ℝ) < A * (1 / δ_B + 16 / ε) := mul_pos hA_pos h_sum_pos
    have h_log_le := Real.log_le_log h_lhs_pos h_lhs_le
    have h_log_split : Real.log (A * (1 / δ_B + 16 / ε) * ((n : ℝ) + 1))
        = Real.log A + Real.log (1 / δ_B + 16 / ε) + Real.log ((n : ℝ) + 1) := by
      rw [Real.log_mul h_mid_pos.ne' hn1_pos.ne',
          Real.log_mul hA_pos.ne' h_sum_pos.ne']
    have hK_eq : K_Z = Real.log A + Real.log (1 / δ_B + 16 / ε) := by
      rfl
    linarith [h_log_le, h_log_split, hK_eq]
  -- (log)² ≤ 2 K² + 2 (log(n+1))² via (a+b)² ≤ 2a² + 2b².
  have hlog_n1_nn : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg; linarith
  -- Define V_Y_n := (log(|β|/δ_n))², V_Z_n := same shape.
  set V_Y_n : ℝ := (Real.log ((Fintype.card β : ℝ) / δ_n)) ^ 2 with hV_Y_n_def
  set V_Z_n : ℝ := (Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ))
                              / (p_min * δ_n))) ^ 2 with hV_Z_n_def
  -- V_Y_n ≤ 2 K_Y² + 2 (log(n+1))².
  have h_V_Y_n_bound : V_Y_n ≤ 2 * K_Y ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2 := by
    rw [hV_Y_n_def]
    -- |log(β/δ_n)| ≤ |K_Y| + |log(n+1)|; squared via (a+b)² ≤ 2(a²+b²).
    have h_abs : |Real.log ((Fintype.card β : ℝ) / δ_n)| ≤ |K_Y| + |Real.log ((n : ℝ) + 1)| := by
      -- log(β/δ_n) is in [-|K_Y|, K_Y + log(n+1)] -- the upper bound, lower trivial via δ_n ≤ 1.
      have h_β_δ_n_pos : (0 : ℝ) < (Fintype.card β : ℝ) / δ_n := by positivity
      -- log(β/δ_n) ≥ 0 since β/δ_n ≥ 1 (since |β| ≥ 1 and δ_n ≤ 1).
      have hβ_ge_one : (1 : ℝ) ≤ (Fintype.card β : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
      have h_β_δ_n_ge : (1 : ℝ) ≤ (Fintype.card β : ℝ) / δ_n := by
        rw [le_div_iff₀ hδ_n_pos]; linarith
      have h_log_nn : 0 ≤ Real.log ((Fintype.card β : ℝ) / δ_n) :=
        Real.log_nonneg h_β_δ_n_ge
      rw [abs_of_nonneg h_log_nn]
      have h_K_Y_plus_log_nn : 0 ≤ K_Y + Real.log ((n : ℝ) + 1) := by
        -- K_Y could be negative; but K_Y + log(n+1) ≥ log(β/δ_n) ≥ 0.
        linarith [h_log_β_δ_n_le, h_log_nn]
      have h_step : Real.log ((Fintype.card β : ℝ) / δ_n) ≤ |K_Y| + |Real.log ((n : ℝ) + 1)| := by
        calc Real.log ((Fintype.card β : ℝ) / δ_n)
            ≤ K_Y + Real.log ((n : ℝ) + 1) := h_log_β_δ_n_le
          _ ≤ |K_Y| + |Real.log ((n : ℝ) + 1)| := by
              have h1 : K_Y ≤ |K_Y| := le_abs_self _
              have h2 : Real.log ((n : ℝ) + 1) ≤ |Real.log ((n : ℝ) + 1)| := le_abs_self _
              linarith
      exact h_step
    have h_sq : (Real.log ((Fintype.card β : ℝ) / δ_n)) ^ 2
        = |Real.log ((Fintype.card β : ℝ) / δ_n)| ^ 2 := by rw [sq_abs]
    rw [h_sq]
    have h_sq_le : |Real.log ((Fintype.card β : ℝ) / δ_n)| ^ 2
        ≤ (|K_Y| + |Real.log ((n : ℝ) + 1)|) ^ 2 := by
      have h_abs_nn : 0 ≤ |Real.log ((Fintype.card β : ℝ) / δ_n)| := abs_nonneg _
      exact pow_le_pow_left₀ h_abs_nn h_abs 2
    refine h_sq_le.trans ?_
    -- (|K_Y| + |log(n+1)|)² ≤ 2 |K_Y|² + 2 |log(n+1)|² = 2 K_Y² + 2 (log(n+1))².
    have h_expand : (|K_Y| + |Real.log ((n : ℝ) + 1)|) ^ 2
        ≤ 2 * |K_Y| ^ 2 + 2 * |Real.log ((n : ℝ) + 1)| ^ 2 := by
      have h := sq_nonneg (|K_Y| - |Real.log ((n : ℝ) + 1)|)
      nlinarith
    have h_eq1 : |K_Y| ^ 2 = K_Y ^ 2 := sq_abs _
    have h_eq2 : |Real.log ((n : ℝ) + 1)| ^ 2 = (Real.log ((n : ℝ) + 1)) ^ 2 := sq_abs _
    linarith
  have h_V_Z_n_bound : V_Z_n ≤ 2 * K_Z ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2 := by
    -- Same structure as V_Y_n_bound.
    rw [hV_Z_n_def]
    have h_abs : |Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))|
        ≤ |K_Z| + |Real.log ((n : ℝ) + 1)| := by
      -- The arg ≥ 1: |α||β| ≥ 1 and p_min δ_n ≤ 1.
      have hαβ_ge_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := by
        have hα1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
        have hβ1 : (1 : ℝ) ≤ (Fintype.card β : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
        nlinarith
      have hp_min_le_one : p_min ≤ 1 := by
        rw [hp_min_def]
        have h1 : δ_p ≤ 1 := hδ_p_le
        have hα1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
        rw [div_le_one hα_pos]; linarith
      have hpd_pos : 0 < p_min * δ_n := mul_pos hp_min_pos hδ_n_pos
      have hpd_le_one : p_min * δ_n ≤ 1 := by
        have : p_min * δ_n ≤ 1 * 1 := by
          exact mul_le_mul hp_min_le_one hδ_n_le hδ_n_pos.le (by norm_num)
        linarith
      have h_arg_ge : (1 : ℝ) ≤ ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n) := by
        rw [le_div_iff₀ hpd_pos]
        calc (1 : ℝ) * (p_min * δ_n) ≤ 1 * 1 :=
              mul_le_mul_of_nonneg_left hpd_le_one (by norm_num)
          _ = 1 := by norm_num
          _ ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) := hαβ_ge_one
      have h_log_nn : 0 ≤ Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n)) :=
        Real.log_nonneg h_arg_ge
      rw [abs_of_nonneg h_log_nn]
      calc Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))
          ≤ K_Z + Real.log ((n : ℝ) + 1) := h_log_Z_le
        _ ≤ |K_Z| + |Real.log ((n : ℝ) + 1)| := by
            have h1 : K_Z ≤ |K_Z| := le_abs_self _
            have h2 : Real.log ((n : ℝ) + 1) ≤ |Real.log ((n : ℝ) + 1)| := le_abs_self _
            linarith
    have h_sq : (Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))) ^ 2
        = |Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))| ^ 2 :=
      by rw [sq_abs]
    rw [h_sq]
    have h_sq_le :
        |Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))| ^ 2
          ≤ (|K_Z| + |Real.log ((n : ℝ) + 1)|) ^ 2 := by
      have h_abs_nn :
          0 ≤ |Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n))| :=
        abs_nonneg _
      exact pow_le_pow_left₀ h_abs_nn h_abs 2
    refine h_sq_le.trans ?_
    have h_expand : (|K_Z| + |Real.log ((n : ℝ) + 1)|) ^ 2
        ≤ 2 * |K_Z| ^ 2 + 2 * |Real.log ((n : ℝ) + 1)| ^ 2 := by
      have h := sq_nonneg (|K_Z| - |Real.log ((n : ℝ) + 1)|)
      nlinarith
    have h_eq1 : |K_Z| ^ 2 = K_Z ^ 2 := sq_abs _
    have h_eq2 : |Real.log ((n : ℝ) + 1)| ^ 2 = (Real.log ((n : ℝ) + 1)) ^ 2 := sq_abs _
    linarith
  -- Variance bounds.
  have hV_Y_bound : pmfLogVariance μ iidYs ≤ V_Y_n :=
    pmfLogVariance_le_sq_of_bounded μ iidYs hYs hV_Y_pointwise
  have hZ_meas : ∀ i, Measurable (jointSequence (α := α) (β := β) iidXs iidYs i) :=
    fun i => measurable_jointSequence iidXs iidYs hXs hYs i
  have hV_Z_bound : pmfLogVariance μ (jointSequence iidXs iidYs) ≤ V_Z_n :=
    pmfLogVariance_le_sq_of_bounded μ (jointSequence iidXs iidYs) hZ_meas hV_Z_pointwise
  -- Step 9: Apply `channel_coding_achievability_smooth_at_N_le` at `R'` with V_X, V_Y_n, V_Z_n.
  --   We need `channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' ≤ n`.
  -- Decompose this max.
  -- a) typicalSetMinN V_X (η/3) ε_gap ≤ V_X / ((η/3)·ε_gap²) + 2.
  -- b) typicalSetMinN V_Y_n (η/3) ε_gap ≤ (2 K_Y² + 2 (log(n+1))²) / ((η/3)·ε_gap²) + 2.
  -- c) typicalSetMinN V_Z_n (η/3) ε_gap ≤ (2 K_Z² + 2 (log(n+1))²) / ((η/3)·ε_gap²) + 2.
  -- d) expNegMulMinN((I_lb - R')/2)(ε'/2) ≤ const.
  -- e) +1 (the outer max-with-1).
  -- Sum: D_const + 2·C_coef·(log(n+1))². Compare against `n`.
  have hηε_sq : 0 < (η / 3) * ε_gap ^ 2 := by positivity
  -- typicalSetMinN bound: max(1, ⌈V/(η·ε²)⌉ + 1) ≤ V/(η·ε²) + 2 (with V ≥ 0).
  have h_tsMinN_le : ∀ V : ℝ, 0 ≤ V →
      (typicalSetMinN V (η / 3) ε_gap : ℝ) ≤ V / ((η / 3) * ε_gap ^ 2) + 2 := by
    intro V hV
    unfold typicalSetMinN
    have h_div_nn : 0 ≤ V / ((η / 3) * ε_gap ^ 2) := div_nonneg hV hηε_sq.le
    have h_ceil_le : (Nat.ceil (V / ((η / 3) * ε_gap ^ 2)) : ℝ)
        ≤ V / ((η / 3) * ε_gap ^ 2) + 1 := by
      have := Nat.ceil_lt_add_one h_div_nn
      linarith
    have h_max_le : ((max 1 (Nat.ceil (V / ((η / 3) * ε_gap ^ 2)) + 1) : ℕ) : ℝ)
        ≤ V / ((η / 3) * ε_gap ^ 2) + 2 := by
      have h_1_le : (1 : ℝ) ≤ V / ((η / 3) * ε_gap ^ 2) + 2 := by linarith
      have h_ceil_plus_1_le :
          ((Nat.ceil (V / ((η / 3) * ε_gap ^ 2)) + 1 : ℕ) : ℝ)
            ≤ V / ((η / 3) * ε_gap ^ 2) + 2 := by
        push_cast; linarith
      have h_max_real : ((max 1 (Nat.ceil (V / ((η / 3) * ε_gap ^ 2)) + 1) : ℕ) : ℝ)
          ≤ max 1 (V / ((η / 3) * ε_gap ^ 2) + 2) := by
        push_cast
        have h1 : (1 : ℝ) ≤ max 1 (V / ((η / 3) * ε_gap ^ 2) + 2) := le_max_left _ _
        have h2 : (Nat.ceil (V / ((η / 3) * ε_gap ^ 2)) + 1 : ℝ)
            ≤ max 1 (V / ((η / 3) * ε_gap ^ 2) + 2) := by
          exact le_max_of_le_right (by linarith)
        exact max_le h1 h2
      have h_max_le_rhs : max 1 (V / ((η / 3) * ε_gap ^ 2) + 2) ≤ V / ((η / 3) * ε_gap ^ 2) + 2 :=
        max_le h_1_le le_rfl
      linarith
    exact h_max_le
  have hV_X_nn : 0 ≤ V_X := by rw [hV_X_def]; exact sq_nonneg _
  have hV_Y_n_nn : 0 ≤ V_Y_n := by rw [hV_Y_n_def]; exact sq_nonneg _
  have hV_Z_n_nn : 0 ≤ V_Z_n := by rw [hV_Z_n_def]; exact sq_nonneg _
  have h_smoothN_le :
      (channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' : ℝ)
        ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
    -- The max can be broken into 3 + 2 components.
    unfold channelCodingSmoothMinN
    -- All bounds:
    have hTS_X := h_tsMinN_le V_X hV_X_nn
    have hTS_Y := h_tsMinN_le V_Y_n hV_Y_n_nn
    have hTS_Z := h_tsMinN_le V_Z_n hV_Z_n_nn
    -- Apply variance-form bounds:
    have hTS_Y_const_form : V_Y_n / ((η / 3) * ε_gap ^ 2) + 2
        ≤ (2 * K_Y ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2) + 2 := by
      have h_div_le : V_Y_n / ((η / 3) * ε_gap ^ 2)
          ≤ (2 * K_Y ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2) := by
        exact div_le_div_of_nonneg_right h_V_Y_n_bound hηε_sq.le
      linarith
    have hTS_Y_full := hTS_Y.trans hTS_Y_const_form
    have hTS_Z_const_form : V_Z_n / ((η / 3) * ε_gap ^ 2) + 2
        ≤ (2 * K_Z ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2) + 2 := by
      have h_div_le : V_Z_n / ((η / 3) * ε_gap ^ 2)
          ≤ (2 * K_Z ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2) := by
        exact div_le_div_of_nonneg_right h_V_Z_n_bound hηε_sq.le
      linarith
    have hTS_Z_full := hTS_Z.trans hTS_Z_const_form
    -- jointlyTypicalSetMinN unfolded: max(max TS_X TS_Y) TS_Z.
    unfold jointlyTypicalSetMinN
    -- Each TS ≤ "2·C·(log)² + D_const" component-wise; max ≤ ...
    -- Build the final inequality. Each individual TS is ≤ bound. The max of three is ≤ bound.
    -- We use: max a b ≤ c ↔ a ≤ c ∧ b ≤ c.
    push_cast
    -- Each typicalSetMinN ≤ 2·C·(log)² + (V_X / ηε² + 2) (resp.) ≤ sum of constants and 2·C·(log)².
    have hAt : (typicalSetMinN V_X (η / 3) ε_gap : ℝ)
        ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
      have h1 := hTS_X
      have h_log_nn_sq : 0 ≤ (Real.log ((n : ℝ) + 1)) ^ 2 := sq_nonneg _
      have h_C_nn : 0 ≤ 2 * C_coef := by linarith
      have h_term_nn : 0 ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 := by positivity
      have hD : V_X / ((η / 3) * ε_gap ^ 2) + 2 ≤ D_const := by
        rw [hD_const_def, hV_const_def]
        have hKY_nn : 0 ≤ 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2) := by positivity
        have hKZ_nn : 0 ≤ 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by positivity
        have h_split : (V_X + 2 * K_Y ^ 2 + 2 * K_Z ^ 2) / ((η / 3) * ε_gap ^ 2)
            = V_X / ((η / 3) * ε_gap ^ 2)
              + 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2)
              + 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by
          rw [add_div, add_div]
        have h_expNeg_nn : 0 ≤ (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) := by
          exact Nat.cast_nonneg _
        linarith
      linarith
    have hAY : (typicalSetMinN V_Y_n (η / 3) ε_gap : ℝ)
        ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
      have hKY_term :
          (2 * K_Y ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2) + 2
            ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
        rw [hD_const_def, hV_const_def, hC_coef_def]
        -- 2·C_coef = 2 · 2 / ((η/3) · ε_gap²) = 4 / (...). And the lhs splits.
        have h_split : (2 * K_Y ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2)
            = 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2)
              + 2 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2) := by
          rw [add_div]
        have h_2C : 2 * (2 / ((η / 3) * ε_gap ^ 2)) * (Real.log ((n : ℝ) + 1)) ^ 2
            = 2 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2) * 2 := by ring
        have h_const_nn1 : 0 ≤ V_X / ((η / 3) * ε_gap ^ 2) := by positivity
        have h_const_nn2 : 0 ≤ 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by positivity
        have h_expNeg_nn : 0 ≤ (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) := by
          exact Nat.cast_nonneg _
        have h_total_split : (V_X + 2 * K_Y ^ 2 + 2 * K_Z ^ 2) / ((η / 3) * ε_gap ^ 2)
            = V_X / ((η / 3) * ε_gap ^ 2) + 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2)
              + 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by
          rw [add_div, add_div]
        -- Combine.
        have h_2_log : 2 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2)
            ≤ 2 * (2 / ((η / 3) * ε_gap ^ 2)) * (Real.log ((n : ℝ) + 1)) ^ 2 := by
          have h_eq : 2 * (2 / ((η / 3) * ε_gap ^ 2)) * (Real.log ((n : ℝ) + 1)) ^ 2
              = 4 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2) := by
            field_simp; ring
          rw [h_eq]
          have h_log_sq_nn : 0 ≤ (Real.log ((n : ℝ) + 1)) ^ 2 := sq_nonneg _
          have h_24 : 2 * (Real.log ((n : ℝ) + 1)) ^ 2 ≤ 4 * (Real.log ((n : ℝ) + 1)) ^ 2 := by
            linarith
          exact div_le_div_of_nonneg_right h_24 hηε_sq.le
        linarith
      linarith [hTS_Y_full, hKY_term]
    have hAZ : (typicalSetMinN V_Z_n (η / 3) ε_gap : ℝ)
        ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
      have hKZ_term :
          (2 * K_Z ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2) + 2
            ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
        rw [hD_const_def, hV_const_def, hC_coef_def]
        have h_split : (2 * K_Z ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2) / ((η / 3) * ε_gap ^ 2)
            = 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2)
              + 2 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2) := by
          rw [add_div]
        have h_const_nn1 : 0 ≤ V_X / ((η / 3) * ε_gap ^ 2) := by positivity
        have h_const_nn2 : 0 ≤ 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2) := by positivity
        have h_expNeg_nn : 0 ≤ (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) := by
          exact Nat.cast_nonneg _
        have h_total_split : (V_X + 2 * K_Y ^ 2 + 2 * K_Z ^ 2) / ((η / 3) * ε_gap ^ 2)
            = V_X / ((η / 3) * ε_gap ^ 2) + 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2)
              + 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by
          rw [add_div, add_div]
        have h_2_log : 2 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2)
            ≤ 2 * (2 / ((η / 3) * ε_gap ^ 2)) * (Real.log ((n : ℝ) + 1)) ^ 2 := by
          have h_eq : 2 * (2 / ((η / 3) * ε_gap ^ 2)) * (Real.log ((n : ℝ) + 1)) ^ 2
              = 4 * (Real.log ((n : ℝ) + 1)) ^ 2 / ((η / 3) * ε_gap ^ 2) := by
            field_simp; ring
          rw [h_eq]
          have h_log_sq_nn : 0 ≤ (Real.log ((n : ℝ) + 1)) ^ 2 := sq_nonneg _
          have h_24 : 2 * (Real.log ((n : ℝ) + 1)) ^ 2 ≤ 4 * (Real.log ((n : ℝ) + 1)) ^ 2 := by
            linarith
          exact div_le_div_of_nonneg_right h_24 hηε_sq.le
        linarith
      linarith [hTS_Z_full, hKZ_term]
    have hAExp : (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ)
        ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
      rw [hD_const_def]
      have h_term_nn : 0 ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 := by positivity
      have h_const_nn1 : 0 ≤ V_const / ((η / 3) * ε_gap ^ 2) := by
        apply div_nonneg
        · rw [hV_const_def]; positivity
        · exact hηε_sq.le
      linarith
    have hA1 : (1 : ℝ) ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const := by
      rw [hD_const_def]
      have h_term_nn : 0 ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 := by positivity
      have h_const_nn1 : 0 ≤ V_const / ((η / 3) * ε_gap ^ 2) := by
        apply div_nonneg
        · rw [hV_const_def]; positivity
        · exact hηε_sq.le
      have h_expNeg_nn : 0 ≤ (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) := Nat.cast_nonneg _
      linarith
    -- Combine via max_le.
    refine max_le (max_le (max_le (max_le ?_ ?_) ?_) hAExp) hA1
    · exact hAt
    · exact hAY
    · exact hAZ
  -- From outer N₀: 2·C_coef · (log(n+1))² + D_const ≤ n.
  have h_log_le_n := hN_log n hn_log
  have h_smoothN_le_n :
      (channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' : ℝ) ≤ (n : ℝ) :=
    h_smoothN_le.trans h_log_le_n
  have h_smoothN_le_n_nat :
      channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' ≤ n := by
    exact_mod_cast h_smoothN_le_n
  -- Step 10: apply the closed-form average-error theorem.
  obtain ⟨M', hM'_lb, c', h_avg_lt⟩ :=
    channel_coding_achievability_smooth_at_N_le W p₀ hp₀_mem hδ_p_pos hδ_p_le
      hδ_n_pos hδ_n_le hR'_pos hR'_lt_I_lb hMI_δ_n.le V_X V_Y_n V_Z_n
      hV_X_bound hV_Y_bound hV_Z_bound hε'_pos n h_smoothN_le_n_nat
  -- Step 11: max-error upgrade via subcode trick (mirror `channel_coding_achievability_max_error`).
  -- Let M' ≥ ⌈exp(nR')⌉ and avg < ε' = ε/8. We pick a subcode with size ≥ ⌈exp(nR)⌉.
  -- The "good" Finset S has avg-error ≤ 2 avg < 2·ε' = ε/4 < ε/2.
  have hK : (1 : ℝ) < 2 := by norm_num
  have h_filter_bound :=
    errorProbAt_filter_card_bound (M := M') (n := n) c' (Channel.smooth W δ_n) hK
  set T : Finset (Fin M') := (Finset.univ : Finset (Fin M')).filter
      (fun m => 2 * (c'.averageErrorProb (Channel.smooth W δ_n)).toReal <
        (c'.errorProbAt (Channel.smooth W δ_n) m).toReal) with hT_def
  set S : Finset (Fin M') := (Finset.univ : Finset (Fin M')).filter
      (fun m => (c'.errorProbAt (Channel.smooth W δ_n) m).toReal ≤
        2 * (c'.averageErrorProb (Channel.smooth W δ_n)).toReal) with hS_def
  have hST_partition : S.card + T.card = M' := by
    have h_union : S ∪ T = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro m
      rw [Finset.mem_union, hS_def, hT_def, Finset.mem_filter, Finset.mem_filter]
      rcases le_or_gt ((c'.errorProbAt (Channel.smooth W δ_n) m).toReal)
          (2 * (c'.averageErrorProb (Channel.smooth W δ_n)).toReal) with h | h
      · exact Or.inl ⟨Finset.mem_univ m, h⟩
      · exact Or.inr ⟨Finset.mem_univ m, h⟩
    have h_disj : Disjoint S T := by
      rw [hS_def, hT_def]
      refine Finset.disjoint_filter.mpr ?_
      intro m _ hm
      exact not_lt_of_ge hm
    have := Finset.card_union_of_disjoint h_disj
    rw [h_union, Finset.card_univ, Fintype.card_fin] at this
    linarith
  have h_T_card_le : 2 * T.card ≤ M' := by
    have h_real : ((T.card : ℝ) * 2 : ℝ) ≤ (M' : ℝ) := h_filter_bound
    have h_real' : ((2 * T.card : ℕ) : ℝ) ≤ ((M' : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h_real'
  have h_2S_ge_M : M' ≤ 2 * S.card := by
    have : M' = S.card + T.card := hST_partition.symm
    omega
  have h_rate_inequality : 2 * Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ 2 * S.card := by
    calc 2 * Nat.ceil (Real.exp ((n : ℝ) * R))
        ≤ Nat.ceil (Real.exp ((n : ℝ) * R')) := hN_rate n hn_rate
      _ ≤ M' := hM'_lb
      _ ≤ 2 * S.card := h_2S_ge_M
  have h_ceil_le_S_card : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ S.card := by
    have h2 : (2 : ℕ) > 0 := by norm_num
    exact Nat.le_of_mul_le_mul_left h_rate_inequality h2
  have h_exp_nR_pos : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR_pos.le
  have h_exp_nR_ge_1 : 1 ≤ Real.exp ((n : ℝ) * R) :=
    Real.one_le_exp h_exp_nR_pos
  have h_ceil_ge_1 : 1 ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
    exact lt_of_lt_of_le zero_lt_one h_exp_nR_ge_1
  have hS_pos : 0 < S.card := lt_of_lt_of_le h_ceil_ge_1 h_ceil_le_S_card
  -- Assemble: ⟨δ_n, ..., S.card, h_ceil_le_S_card, subcode, max-error bound⟩.
  refine ⟨δ_n, hδ_n_pos, hδ_n_le, h_2nδ_lt, S.card, h_ceil_le_S_card,
    c'.subcode S hS_pos, ?_⟩
  intro m'
  -- Per-message max-error bound: each subcode error ≤ 2·avg < 2·ε' = ε/4 < ε/2.
  have h_sub_le := c'.subcode_errorProbAt_le (Channel.smooth W δ_n) S hS_pos m'
  set m₀ : Fin M' := (S.equivFin.symm ⟨m'.val, by simp [Fin.is_lt]⟩).val with hm₀_def
  have hm₀_mem : m₀ ∈ S := (S.equivFin.symm ⟨m'.val, by simp [Fin.is_lt]⟩).property
  have h_m₀_le : (c'.errorProbAt (Channel.smooth W δ_n) m₀).toReal ≤
      2 * (c'.averageErrorProb (Channel.smooth W δ_n)).toReal := by
    rw [hS_def, Finset.mem_filter] at hm₀_mem
    exact hm₀_mem.2
  have h_sub_le_top : c'.errorProbAt (Channel.smooth W δ_n) m₀ ≠ ∞ := by
    haveI : IsProbabilityMeasure
        (Measure.pi (fun i => Channel.smooth W δ_n (c'.encoder m₀ i))) := by infer_instance
    exact ((prob_le_one
      (μ := Measure.pi (fun i => Channel.smooth W δ_n (c'.encoder m₀ i)))
      (s := c'.errorEvent m₀)).trans_lt ENNReal.one_lt_top).ne
  have h_sub_le_toReal :
      ((c'.subcode S hS_pos).errorProbAt (Channel.smooth W δ_n) m').toReal
        ≤ (c'.errorProbAt (Channel.smooth W δ_n) m₀).toReal :=
    (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top h_sub_le_top h_sub_le) h_sub_le_top).mpr h_sub_le
  calc ((c'.subcode S hS_pos).errorProbAt (Channel.smooth W δ_n) m').toReal
      ≤ (c'.errorProbAt (Channel.smooth W δ_n) m₀).toReal := h_sub_le_toReal
    _ ≤ 2 * (c'.averageErrorProb (Channel.smooth W δ_n)).toReal := h_m₀_le
    _ < 2 * ε' := by linarith
    _ = ε / 4 := by rw [hε'_def]; ring
    _ < ε / 2 := by linarith

/-! ## Phase D.4 — main theorem (Shannon noisy channel coding, fully discharged) -/

/-- **D-1'' Phase D 主定理 (full discharge)**: `R < capacity W` で任意 `ε > 0` に対し
十分大きい `n` で max-error < ε を達成する `M ≥ ⌈exp(nR)⌉` 個の符号が存在。
`hW_pos` 完全除去版。 -/
theorem shannon_noisy_channel_coding_theorem_general_full
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε := by
  obtain ⟨N, hN⟩ := exists_N_for_smooth_achievability_uniform W hR_pos hR hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨δ, hδ_pos, hδ_le, h_tv_bd, M, hM_lb, c, hc_err⟩ := hN n hn
  refine ⟨M, hM_lb, c, fun m => ?_⟩
  -- TV bound: |errorProbAt(W_smooth δ) - errorProbAt(W)| ≤ 2 n δ.
  have h_tv := errorProbAt_smooth_TV c W hδ_pos.le hδ_le m
  have h_W_le :
      (c.errorProbAt W m).toReal
        ≤ (c.errorProbAt (Channel.smooth W δ) m).toReal + 2 * (n : ℝ) * δ := by
    have := (abs_le.mp h_tv).1
    linarith
  linarith [hc_err m]

end InformationTheory.Shannon.ChannelCoding
