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

end InformationTheory.Shannon.ChannelCoding
