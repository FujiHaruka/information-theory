import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
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
@[entry_point]
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

end InformationTheory.Shannon.ChannelCoding
