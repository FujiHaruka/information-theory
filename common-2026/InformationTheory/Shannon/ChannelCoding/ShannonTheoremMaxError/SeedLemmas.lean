import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Smooth input distribution and capacity lower bound construction

Constructs, from `R < capacity W`, a full-support smooth input distribution `pSmooth p₀ δ_p`
and a smoothing radius `δ_B > 0` such that `R < I(pSmooth p₀ δ_p; Channel.smooth W δ).toReal`
for all `δ ∈ (0, δ_B]`.

## Implementation notes

Uses `continuous_mutualInfoOfChannel_right_smooth` (continuity in `δ` for fixed `p`) and
`continuous_mutualInfoOfChannel_left` (continuity in `p` for fixed `W`). Joint `(p, δ)`
continuity is not needed: first find `δ_p` making `I(pSmooth p₀ δ_p; W) > R`, then find
`δ_B` keeping `I(pSmooth p₀ δ_p; W_smooth δ) > R` for `δ ∈ (0, δ_B]`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq α] [DecidableEq β] in
/-- From `R < capacity W`, extracts `p₀ ∈ stdSimplex`, `δ_B ∈ (0, 1]`, and `R₁ > R`
such that `R₁ < I(p₀; W_smooth δ).toReal` for all `δ ∈ (0, δ_B]`. -/
@[entry_point]
theorem exists_smooth_capacity_gt_uniform
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p₀ ∈ stdSimplex ℝ α, ∃ δ_B : ℝ, 0 < δ_B ∧ δ_B ≤ 1 ∧
      ∃ R₁ : ℝ, R < R₁ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ_B,
        R₁ < (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ)).toReal := by
  classical
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

omit [DecidableEq α] [DecidableEq β] in
/-- From `R < capacity W`, extracts `p₀, δ_p, δ_B` and `I_lb > R` such that `pSmooth p₀ δ_p`
has full support and `I_lb < I(pSmooth p₀ δ_p; W_smooth δ).toReal` for all `δ ∈ (0, δ_B]`. -/
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
  classical
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
