import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon noisy channel coding theorem — smoothing infrastructure

Smoothing infrastructure for the Shannon noisy channel coding theorem without the
full-support assumption `hW_pos`. The smoothed channel is
`Channel.smooth W δ a := (1-δ) · W a + δ · uniformMeasureβ`.

## Main definitions

* `uniformMeasureβ β`: uniform probability measure on a finite type `β`.
* `Channel.smooth W δ`: convex combination of `W` with the uniform output measure.

## Main statements

* `exists_smooth_capacity_gt`: from `R < capacity W`, extracts `δ_B > 0` and `R₁ > R`
  with `R₁ < capacity (W_smooth δ)` for all `δ ∈ (0, δ_B]`.
* `errorProbAt_smooth_TV`: TV bound `|errorProbAt(W_smooth δ) - errorProbAt(W)| ≤ 2 n δ`.

## Implementation notes

The main theorem `shannon_noisy_channel_coding_theorem_general` is in
`ShannonTheoremMaxError`, which imports this file for the smoothing infrastructure.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Smoothed channel definition and basic properties -/

/-- Uniform probability measure on a nonempty finite type `β`. -/
noncomputable def uniformMeasureβ (β : Type*) [Fintype β] [MeasurableSpace β] : Measure β :=
  (Fintype.card β : ℝ≥0∞)⁻¹ • ∑ b : β, Measure.dirac b

/-- `uniformMeasureβ` is a probability measure (since `β` is nonempty). -/
instance uniformMeasureβ_isProbabilityMeasure :
    IsProbabilityMeasure (uniformMeasureβ β) := by
  refine ⟨?_⟩
  unfold uniformMeasureβ
  have h_card_pos : 0 < (Fintype.card β : ℝ≥0∞) := by
    have : 0 < Fintype.card β := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast this
  have h_card_ne_top : (Fintype.card β : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  -- (univ) measure: smul · sum dirac
  rw [Measure.smul_apply, Measure.finsetSum_apply Finset.univ _ Set.univ]
  -- ∑ b, Measure.dirac b univ = ∑ b, 1 = Fintype.card β
  have h_sum : ∑ b : β, (Measure.dirac b) (Set.univ : Set β) = (Fintype.card β : ℝ≥0∞) := by
    simp [Measure.dirac_apply' _ MeasurableSet.univ, Finset.sum_const, Finset.card_univ]
  rw [h_sum, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h_card_pos.ne' h_card_ne_top

omit [DecidableEq β] in
/-- Atom evaluation: `(uniformMeasureβ).real {b} = 1/|β|`. -/
lemma uniformMeasureβ_real_singleton (b : β) :
    (uniformMeasureβ β).real ({b} : Set β) = (Fintype.card β : ℝ)⁻¹ := by
  classical
  unfold uniformMeasureβ
  -- ((Fintype.card β)⁻¹ • ∑ b', dirac b') {b} = (Fintype.card β)⁻¹ * 1.
  have h_card_pos : 0 < (Fintype.card β : ℝ≥0∞) := by
    have : 0 < Fintype.card β := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast this
  rw [Measure.real, Measure.smul_apply, Measure.finsetSum_apply Finset.univ _ {b}]
  -- ∑ b' : β, dirac b' {b} = 1
  have h_each : ∀ b' ∈ (Finset.univ : Finset β),
      (Measure.dirac b' : Measure β) ({b} : Set β) = if b' = b then 1 else 0 := by
    intro b' _
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton b)]
    by_cases hbb : b' = b
    · subst hbb; simp
    · rw [Set.indicator_of_notMem (show b' ∉ ({b} : Set β) by
          simp only [Set.mem_singleton_iff]; exact hbb), if_neg hbb]
  rw [Finset.sum_congr rfl h_each]
  -- ∑ b', (if b' = b then 1 else 0) = 1
  rw [Finset.sum_ite_eq' Finset.univ b (fun _ ↦ (1 : ℝ≥0∞)), if_pos (Finset.mem_univ b)]
  rw [smul_eq_mul, mul_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- Smoothed channel `W_smooth δ a := (1-δ) W a + δ · uniformMeasureβ`. -/
noncomputable def Channel.smooth (W : Channel α β) (δ : ℝ) : Channel α β :=
  { toFun := fun a ↦ ENNReal.ofReal (1 - δ) • W a + ENNReal.ofReal δ • uniformMeasureβ β
    measurable' := Measurable.of_discrete }

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
@[simp] lemma Channel.smooth_apply (W : Channel α β) (δ : ℝ) (a : α) :
    Channel.smooth W δ a
      = ENNReal.ofReal (1 - δ) • W a + ENNReal.ofReal δ • uniformMeasureβ β := rfl

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- `Channel.smooth W 0 = W`. -/
lemma Channel.smooth_zero (W : Channel α β) [IsMarkovKernel W] :
    Channel.smooth W 0 = W := by
  refine Kernel.ext (fun a ↦ ?_)
  show ENNReal.ofReal (1 - 0) • W a + ENNReal.ofReal 0 • uniformMeasureβ β = W a
  simp

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [MeasurableSingletonClass β] in
/-- For `δ ∈ [0,1]`, `Channel.smooth W δ` is a Markov kernel. -/
lemma Channel.smooth_isMarkovKernel
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsMarkovKernel (Channel.smooth W δ) := by
  refine ⟨fun a ↦ ⟨?_⟩⟩
  show (ENNReal.ofReal (1 - δ) • W a + ENNReal.ofReal δ • uniformMeasureβ β)
        (Set.univ : Set β) = 1
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add (by linarith) hδ0]
  have : (1 : ℝ) - δ + δ = 1 := by ring
  rw [this, ENNReal.ofReal_one]

omit [DecidableEq α] [Nonempty α] [DecidableEq β] in
/-- For `δ ∈ [0,1]`, `(W_smooth δ a).real {b} = (1-δ)(W a).real{b} + δ/|β|`. -/
lemma Channel.smooth_real_singleton
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : α) (b : β) :
    (Channel.smooth W δ a).real ({b} : Set β)
      = (1 - δ) * (W a).real {b} + δ * (Fintype.card β : ℝ)⁻¹ := by
  show (ENNReal.ofReal (1 - δ) • W a + ENNReal.ofReal δ • uniformMeasureβ β).real {b}
        = (1 - δ) * (W a).real {b} + δ * (Fintype.card β : ℝ)⁻¹
  have h_left_ne_top : (ENNReal.ofReal (1 - δ) • W a) ({b} : Set β) ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h_right_ne_top : (ENNReal.ofReal δ • uniformMeasureβ β) ({b} : Set β) ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [measureReal_add_apply h_left_ne_top h_right_ne_top,
      measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
      uniformMeasureβ_real_singleton, ENNReal.toReal_ofReal hδ0,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - δ)]

omit [DecidableEq α] [Nonempty α] [DecidableEq β] in
/-- For `δ ∈ (0,1]`, every atom of `W_smooth δ a` has positive probability. -/
lemma Channel.smooth_pos
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ a b, 0 < (Channel.smooth W δ a).real ({b} : Set β) := by
  intro a b
  rw [Channel.smooth_real_singleton W hδ_pos.le hδ1]
  have h1_nn : 0 ≤ (1 - δ) * (W a).real {b} :=
    mul_nonneg (by linarith) ENNReal.toReal_nonneg
  have h2_pos : 0 < δ * (Fintype.card β : ℝ)⁻¹ := by
    refine mul_pos hδ_pos (inv_pos.mpr ?_)
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  linarith

/-! ## Mutual information continuity in `δ` -/

omit [DecidableEq α] [DecidableEq β] in
/-- Helper: for any Markov channel `K`, the 3-entropy form of MI in terms of `(K a).real {b}`. -/
lemma mutualInfoOfChannel_toReal_three_entropy
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (K : Channel α β) [IsMarkovKernel K] :
    (mutualInfoOfChannel (pmfToMeasure p) K).toReal
      = (∑ a : α, Real.negMulLog (p a))
        + (∑ b : β, Real.negMulLog (∑ a : α, p a * (K a).real {b}))
        - (∑ ab : α × β, Real.negMulLog (p ab.1 * (K ab.1).real {ab.2})) := by
  classical
  haveI : IsProbabilityMeasure (pmfToMeasure p) := pmfToMeasure_isProbabilityMeasure hp
  rw [mutualInfoOfChannel_eq_HX_add_HY_sub_HZ]
  unfold InformationTheory.Shannon.entropy
  -- For p ∈ stdSimplex, the three Map.real-singleton evaluations.
  have h_fst : ∀ a : α,
      ((jointDistribution (pmfToMeasure p) K).map Prod.fst).real {a} = p a := by
    intro a
    have h_fst_eq : (jointDistribution (pmfToMeasure p) K).map Prod.fst = pmfToMeasure p := by
      show ((pmfToMeasure p) ⊗ₘ K).map Prod.fst = pmfToMeasure p
      rw [show ((pmfToMeasure p) ⊗ₘ K).map Prod.fst = ((pmfToMeasure p) ⊗ₘ K).fst from rfl]
      exact Measure.fst_compProd _ K
    rw [h_fst_eq, pmfToMeasure_real_singleton hp]
  have h_snd : ∀ b : β,
      ((jointDistribution (pmfToMeasure p) K).map Prod.snd).real {b}
        = ∑ a : α, p a * (K a).real {b} := by
    intro b
    -- ((p ⊗ₘ K).snd){b} = (p ⊗ₘ K)(univ ×ˢ {b}) = ∫⁻ a, K a {b} ∂(pmfToMeasure p).
    have h1 : (jointDistribution (pmfToMeasure p) K).snd ({b} : Set β)
        = (jointDistribution (pmfToMeasure p) K) (Set.univ ×ˢ ({b} : Set β)) := by
      rw [Measure.snd_apply (measurableSet_singleton _)]
      congr 1; ext ⟨a, b'⟩; simp
    have h_map_eq : (jointDistribution (pmfToMeasure p) K).map Prod.snd
        = (jointDistribution (pmfToMeasure p) K).snd := rfl
    rw [h_map_eq, Measure.real, h1, jointDistribution_def]
    have h2 : ((pmfToMeasure p) ⊗ₘ K) (Set.univ ×ˢ ({b} : Set β))
        = ∫⁻ a, K a {b} ∂(pmfToMeasure p) := by
      rw [Measure.compProd_apply (MeasurableSet.univ.prod (measurableSet_singleton _))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
      show (K a) (Prod.mk a ⁻¹' (Set.univ ×ˢ ({b} : Set β))) = (K a) {b}
      congr 1; ext y; simp
    rw [h2]
    unfold pmfToMeasure
    rw [MeasureTheory.lintegral_finsetSum_measure]
    simp_rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac, smul_eq_mul]
    rw [ENNReal.toReal_sum (by
      intro a _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp.1 a)]
    rfl
  have h_id : ∀ ab : α × β,
      ((jointDistribution (pmfToMeasure p) K).map id).real {ab}
        = p ab.1 * (K ab.1).real {ab.2} := by
    intro ⟨a, b⟩
    rw [Measure.map_id]
    -- {(a, b)} = {a} ×ˢ {b}.
    have h_eq : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
      ext ⟨x, y⟩; simp [Prod.ext_iff]
    rw [Measure.real, jointDistribution_def, h_eq,
        Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
    rw [← MeasureTheory.lintegral_indicator (measurableSet_singleton _)]
    unfold pmfToMeasure
    rw [MeasureTheory.lintegral_finsetSum_measure]
    simp_rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac, smul_eq_mul]
    have h_each : ∀ a' ∈ (Finset.univ : Finset α),
        ENNReal.ofReal (p a') * Set.indicator ({a} : Set α) (fun x ↦ K x {b}) a'
          = if a' = a then ENNReal.ofReal (p a) * K a {b} else 0 := by
      intro a' _
      by_cases hcase : a' = a
      · subst hcase
        rw [if_pos rfl, Set.indicator_of_mem (Set.mem_singleton _)]
      · rw [if_neg hcase, Set.indicator_of_notMem (by simp [hcase])]
        simp
    rw [Finset.sum_congr rfl h_each, Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ a),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp.1 a)]
    rfl
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl (fun a _ ↦ ?_); rw [h_fst a]
    · refine Finset.sum_congr rfl (fun b _ ↦ ?_); rw [h_snd b]
  · refine Finset.sum_congr rfl (fun ab _ ↦ ?_); rw [h_id ab]

omit [DecidableEq α] [DecidableEq β] in
/-- For `δ ∈ [0,1]`, `(mutualInfoOfChannel (pmfToMeasure p) (Channel.smooth W δ)).toReal` expands
in the 3-entropy form with `(W_smooth δ a).real {b}` substituted via `smooth_real_singleton`. -/
lemma mutualInfoOfChannel_toReal_smooth_eq
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (mutualInfoOfChannel (pmfToMeasure p) (Channel.smooth W δ)).toReal
      = (∑ a : α, Real.negMulLog (p a))
        + (∑ b : β, Real.negMulLog
            (∑ a : α, p a * ((1 - δ) * (W a).real {b} + δ * (Fintype.card β : ℝ)⁻¹)))
        - (∑ ab : α × β, Real.negMulLog
            (p ab.1 * ((1 - δ) * (W ab.1).real {ab.2} + δ * (Fintype.card β : ℝ)⁻¹))) := by
  haveI : IsMarkovKernel (Channel.smooth W δ) := Channel.smooth_isMarkovKernel W hδ0 hδ1
  rw [mutualInfoOfChannel_toReal_three_entropy hp (Channel.smooth W δ)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun b _ ↦ ?_)
    congr 1
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [Channel.smooth_real_singleton W hδ0 hδ1]
  · refine Finset.sum_congr rfl (fun ab _ ↦ ?_)
    rw [Channel.smooth_real_singleton W hδ0 hδ1]

omit [DecidableEq α] [DecidableEq β] in
/-- `δ ↦ (mutualInfoOfChannel (pmfToMeasure p) (Channel.smooth W δ)).toReal` is continuous on
`[0,1]`. -/
lemma continuous_mutualInfoOfChannel_right_smooth
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (W : Channel α β) [IsMarkovKernel W] :
    ContinuousOn (fun δ : ℝ ↦
        (mutualInfoOfChannel (pmfToMeasure p) (Channel.smooth W δ)).toReal)
      (Set.Icc (0 : ℝ) 1) := by
  -- Use the 3-entropy form via mutualInfoOfChannel_toReal_smooth_eq.
  set g : ℝ → ℝ := fun δ ↦
    (∑ a : α, Real.negMulLog (p a))
      + (∑ b : β, Real.negMulLog
          (∑ a : α, p a * ((1 - δ) * (W a).real {b} + δ * (Fintype.card β : ℝ)⁻¹)))
      - (∑ ab : α × β, Real.negMulLog
          (p ab.1 * ((1 - δ) * (W ab.1).real {ab.2} + δ * (Fintype.card β : ℝ)⁻¹))) with hg_def
  have h_eq_on : ∀ δ ∈ Set.Icc (0 : ℝ) 1,
      (mutualInfoOfChannel (pmfToMeasure p) (Channel.smooth W δ)).toReal = g δ := by
    intro δ hδ
    exact mutualInfoOfChannel_toReal_smooth_eq hp W hδ.1 hδ.2
  refine ContinuousOn.congr ?_ h_eq_on
  refine Continuous.continuousOn ?_
  -- Continuity of g.
  refine Continuous.sub ?_ ?_
  · refine Continuous.add continuous_const ?_
    refine continuous_finsetSum _ (fun b _ ↦ ?_)
    refine Real.continuous_negMulLog.comp ?_
    refine continuous_finsetSum _ (fun a _ ↦ ?_)
    -- p a * ((1-δ) * (W a).real {b} + δ * (Fintype.card β : ℝ)⁻¹)
    refine continuous_const.mul ?_
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub continuous_id).mul continuous_const
    · exact continuous_id.mul continuous_const
  · refine continuous_finsetSum _ (fun ab _ ↦ ?_)
    refine Real.continuous_negMulLog.comp ?_
    refine continuous_const.mul ?_
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub continuous_id).mul continuous_const
    · exact continuous_id.mul continuous_const

omit [DecidableEq α] [DecidableEq β] in
/-- From `R < capacity W`, extract `δ₀ ∈ (0, 1]` and `p₀ ∈ stdSimplex` with
`R < (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ₀)).toReal`. -/
private lemma exists_smooth_capacity_gt
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p₀ ∈ stdSimplex ℝ α, ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      R < (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ₀)).toReal := by
  -- Step 1: extract p₀ with R < I(p₀; W).toReal.
  obtain ⟨p₀, hp₀_mem, hp₀_lt⟩ := capacity_lt_implies_exists_pmf W hR
  set I₀ : ℝ := (mutualInfoOfChannel (pmfToMeasure p₀) W).toReal with hI₀_def
  -- Midpoint R₁ = (R + I₀) / 2.
  set R₁ : ℝ := (R + I₀) / 2 with hR₁_def
  have hR_lt_R₁ : R < R₁ := by rw [hR₁_def]; linarith
  have hR₁_lt_I₀ : R₁ < I₀ := by rw [hR₁_def]; linarith
  -- Step 2: continuity of f(δ) := I(p₀; W_smooth δ).toReal on [0,1].
  set f : ℝ → ℝ := fun δ ↦
    (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ)).toReal with hf_def
  have hf_cont_on : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    continuous_mutualInfoOfChannel_right_smooth hp₀_mem W
  -- f 0 = I₀.
  have hf_zero : f 0 = I₀ := by
    simp only [hf_def, hI₀_def]
    rw [Channel.smooth_zero W]
  have hf_zero_gt : R₁ < f 0 := by rw [hf_zero]; exact hR₁_lt_I₀
  -- Continuity at 0 from the right.
  have h_at_zero : ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) 0 := by
    refine hf_cont_on 0 ⟨le_refl _, by norm_num⟩
  have h_ev_gt : ∀ᶠ δ in (nhdsWithin (0 : ℝ) (Set.Icc 0 1)), R₁ < f δ := by
    have := h_at_zero.tendsto
    exact this.eventually_const_lt hf_zero_gt
  have h_ev_gt_mem : {δ | R₁ < f δ} ∈ 𝓝[Set.Icc (0 : ℝ) 1] 0 := h_ev_gt
  rw [Metric.mem_nhdsWithin_iff] at h_ev_gt_mem
  obtain ⟨η, hη_pos, h_η⟩ := h_ev_gt_mem
  set δ₀ : ℝ := min (η / 2) 1 with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]; exact lt_min (by linarith) (by norm_num)
  have hδ₀_le_1 : δ₀ ≤ 1 := min_le_right _ _
  have hδ₀_lt_η : δ₀ < η := by
    rw [hδ₀_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ₀_mem_Icc : δ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδ₀_pos.le, hδ₀_le_1⟩
  have hδ₀_mem_ball : δ₀ ∈ Metric.ball (0 : ℝ) η := by
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hδ₀_pos]
    exact hδ₀_lt_η
  have hf_δ₀ : R₁ < f δ₀ := h_η ⟨hδ₀_mem_ball, hδ₀_mem_Icc⟩
  refine ⟨p₀, hp₀_mem, δ₀, hδ₀_pos, hδ₀_le_1, ?_⟩
  exact lt_trans hR_lt_R₁ hf_δ₀

/-! ## TV bound -/

omit [DecidableEq α] [Nonempty α] [DecidableEq β] in
/-- For `δ ∈ [0,1]`, `∑_b |(W a).real {b} - (W_smooth δ a).real {b}| ≤ 2 δ`. -/
private lemma Channel.smooth_TV_bound
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : α) :
    ∑ b : β, |(W a).real {b} - (Channel.smooth W δ a).real {b}| ≤ 2 * δ := by
  -- Pointwise: |(W a).real{b} - (W_smooth δ a).real{b}| = δ · |(W a).real{b} - 1/|β||.
  have h_each : ∀ b : β,
      |(W a).real {b} - (Channel.smooth W δ a).real {b}|
        = δ * |(W a).real {b} - (Fintype.card β : ℝ)⁻¹| := by
    intro b
    rw [Channel.smooth_real_singleton W hδ0 hδ1]
    have h_arith : (W a).real {b} - ((1 - δ) * (W a).real {b} + δ * (Fintype.card β : ℝ)⁻¹)
        = δ * ((W a).real {b} - (Fintype.card β : ℝ)⁻¹) := by ring
    rw [h_arith, abs_mul, abs_of_nonneg hδ0]
  simp_rw [h_each]
  rw [← Finset.mul_sum]
  -- We need ∑_b |(W a).real {b} - 1/|β|| ≤ 2.
  have h_sum_le_2 : ∑ b : β, |(W a).real {b} - (Fintype.card β : ℝ)⁻¹| ≤ 2 := by
    -- Triangle inequality: |x - y| ≤ |x| + |y|.
    have h_le : ∀ b : β,
        |(W a).real {b} - (Fintype.card β : ℝ)⁻¹|
          ≤ (W a).real {b} + (Fintype.card β : ℝ)⁻¹ := by
      intro b
      have h1 : 0 ≤ (W a).real {b} := ENNReal.toReal_nonneg
      have h2 : 0 ≤ (Fintype.card β : ℝ)⁻¹ :=
        inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
      calc |(W a).real {b} - (Fintype.card β : ℝ)⁻¹|
          ≤ |(W a).real {b}| + |(Fintype.card β : ℝ)⁻¹| := abs_sub _ _
        _ = (W a).real {b} + (Fintype.card β : ℝ)⁻¹ := by rw [abs_of_nonneg h1, abs_of_nonneg h2]
    have h_sum_le : ∑ b : β, |(W a).real {b} - (Fintype.card β : ℝ)⁻¹|
        ≤ ∑ b : β, ((W a).real {b} + (Fintype.card β : ℝ)⁻¹) :=
      Finset.sum_le_sum (fun b _ ↦ h_le b)
    -- ∑ b, (W a).real {b} = 1 (Markov).
    have h_card_pos_nat : 0 < Fintype.card β := Fintype.card_pos_iff.mpr inferInstance
    have h_card_pos : (0 : ℝ) < Fintype.card β := by exact_mod_cast h_card_pos_nat
    have h_sum_W : ∑ b : β, (W a).real {b} = 1 := by
      haveI : IsProbabilityMeasure (W a) := IsMarkovKernel.isProbabilityMeasure a
      -- ∑ b, (W a).real {b} = (W a).real (⋃ b, {b}) = (W a).real univ = 1.
      have h_pairwise : Pairwise (Function.onFun Disjoint (fun b : β ↦ ({b} : Set β))) := by
        intro b₁ b₂ hb
        show Disjoint (({b₁} : Set β)) (({b₂} : Set β))
        rw [Set.disjoint_singleton]
        exact hb
      have h_meas : ∀ b : β, MeasurableSet ({b} : Set β) := fun b ↦ measurableSet_singleton b
      have h_iUnion : (⋃ b : β, ({b} : Set β)) = Set.univ := by
        ext x; simp
      have h := measureReal_iUnion_fintype (μ := W a) h_pairwise h_meas
      rw [h_iUnion] at h
      rw [← h, probReal_univ]
    have h_sum_inv : ∑ _b : β, (Fintype.card β : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ h_card_pos.ne'
    rw [Finset.sum_add_distrib, h_sum_W, h_sum_inv] at h_sum_le
    linarith
  linarith [mul_le_mul_of_nonneg_left h_sum_le_2 hδ0]

omit [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] in
/-- Auxiliary: for finite `β` and a finite product, `Measure.pi μ S = ∑_{y ∈ S} ∏_i μ_i {y_i}`
(as ENNReal), where `S : Finset (Fin n → β)`. -/
private lemma measure_pi_eq_sum_singletons
    {n : ℕ} (μ : Fin n → Measure β) [∀ i, SigmaFinite (μ i)]
    (S : Finset (Fin n → β)) :
    (Measure.pi μ) (S : Set (Fin n → β))
      = ∑ y ∈ S, ∏ i, μ i ({y i} : Set β) := by
  classical
  have h_E_eq : (S : Set (Fin n → β)) = ⋃ y ∈ S, ({y} : Set (Fin n → β)) := by
    ext x; simp
  rw [h_E_eq, measure_biUnion_finset]
  · refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    have h_singleton_eq :
        ({y} : Set (Fin n → β)) = Set.pi Set.univ (fun i ↦ ({y i} : Set β)) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
      exact ⟨fun h i ↦ by rw [h], fun h ↦ funext h⟩
    rw [h_singleton_eq, Measure.pi_pi]
  · intro y₁ _ y₂ _ hy
    show Disjoint ({y₁} : Set (Fin n → β)) ({y₂} : Set (Fin n → β))
    rw [Set.disjoint_singleton]
    exact hy
  · intro y _
    exact MeasurableSet.singleton y

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- Inductive TV bound: for `a, b : Fin n → β → ℝ` representing probability mass functions
(values in `[0,1]`, each row sums to 1), the L1-sum-over-`Fin n → β` of `|∏ a - ∏ b|` is bounded
by `∑_i ∑_b |a_i b - b_i b|`. -/
private lemma sum_prod_diff_abs_le_aux : ∀ {n : ℕ} (a b : Fin n → β → ℝ),
    (∀ i, ∀ z, 0 ≤ a i z) → (∀ i, ∀ z, 0 ≤ b i z) →
    (∀ i, ∑ z : β, a i z = 1) → (∀ i, ∑ z : β, b i z = 1) →
    ∑ y : Fin n → β, |∏ i, a i (y i) - ∏ i, b i (y i)|
      ≤ ∑ i : Fin n, ∑ z : β, |a i z - b i z| := by
  intro n
  induction n with
  | zero =>
    intro a b _ _ _ _
    simp
  | succ k ih =>
    intro a b ha_nn hb_nn ha_sum hb_sum
    -- a 0 ∏ a' - b 0 ∏ b' = (a 0 - b 0) ∏ b' + a 0 (∏ a' - ∏ b'), where a', b' index Fin k.
    -- LHS = ∑_y |a 0 (y 0) ∏ a' - b 0 (y 0) ∏ b'|
    --     ≤ ∑_y |a 0 (y 0) - b 0 (y 0)| ∏_{i ≥ 1} b' + ∑_y a 0 (y 0) |∏ a' - ∏ b'|
    -- By Fintype.prod_sum (one direction), ∑_y (...) factors:
    -- First term: (∑_{y_0} |a 0 (y_0) - b 0 (y_0)|) · (∑_{y_1..} ∏_{i ≥ 1} b' i y_i)
    --           = (∑_z |a 0 z - b 0 z|) · 1 (the second factor is 1 by induction-base).
    -- Second term: (∑_{y_0} a 0 (y_0)) · (∑_{y_1..} |∏ - ∏|) = 1 · IH.
    -- Use Fintype.sum_pi as in Fintype.prod_sum, but on (Fin (k+1) → β) = β × (Fin k → β).
    have h_split : ∀ y : Fin (k+1) → β,
        |∏ i : Fin (k+1), a i (y i) - ∏ i : Fin (k+1), b i (y i)|
          ≤ |a 0 (y 0) - b 0 (y 0)| * (∏ i : Fin k, b i.succ (y i.succ))
            + a 0 (y 0)
              * |∏ i : Fin k, a i.succ (y i.succ) - ∏ i : Fin k, b i.succ (y i.succ)| := by
      intro y
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      set A : ℝ := ∏ i : Fin k, a i.succ (y i.succ)
      set B : ℝ := ∏ i : Fin k, b i.succ (y i.succ)
      have hA_nn : 0 ≤ A := Finset.prod_nonneg (fun i _ ↦ ha_nn _ _)
      have hB_nn : 0 ≤ B := Finset.prod_nonneg (fun i _ ↦ hb_nn _ _)
      have ha₀_nn : 0 ≤ a 0 (y 0) := ha_nn _ _
      have h_eq : a 0 (y 0) * A - b 0 (y 0) * B
          = (a 0 (y 0) - b 0 (y 0)) * B + a 0 (y 0) * (A - B) := by ring
      rw [h_eq]
      calc |(a 0 (y 0) - b 0 (y 0)) * B + a 0 (y 0) * (A - B)|
          ≤ |(a 0 (y 0) - b 0 (y 0)) * B| + |a 0 (y 0) * (A - B)| := abs_add_le _ _
        _ = |a 0 (y 0) - b 0 (y 0)| * |B| + |a 0 (y 0)| * |A - B| := by
            rw [abs_mul, abs_mul]
        _ = |a 0 (y 0) - b 0 (y 0)| * B + a 0 (y 0) * |A - B| := by
            rw [abs_of_nonneg hB_nn, abs_of_nonneg ha₀_nn]
    refine (Finset.sum_le_sum (fun y _ ↦ h_split y)).trans ?_
    rw [Finset.sum_add_distrib]
    -- The first sum: ∑_y |a 0 (y 0) - b 0 (y 0)| · ∏ b' = (∑_y ∏ over Fin (k+1) of f) where
    -- f 0 = |..|, f i+1 = b _.
    -- We use the bijection (Fin (k+1) → β) ≃ β × (Fin k → β) via y ↦ (y 0, y ∘ Fin.succ).
    have h_first_eq :
        ∑ y : Fin (k+1) → β,
            |a 0 (y 0) - b 0 (y 0)| * (∏ i : Fin k, b i.succ (y i.succ))
          = (∑ y₀ : β, |a 0 y₀ - b 0 y₀|)
              * (∑ y' : Fin k → β, ∏ i : Fin k, b i.succ (y' i)) := by
      -- Bijection: (Fin (k+1) → β) ≃ β × (Fin k → β) via y ↦ (y 0, y ∘ Fin.succ).
      have h_step1 :
          ∑ y : Fin (k+1) → β,
              |a 0 (y 0) - b 0 (y 0)| * (∏ i : Fin k, b i.succ (y i.succ))
            = ∑ p : β × (Fin k → β),
              |a 0 p.1 - b 0 p.1| * (∏ i : Fin k, b i.succ (p.2 i)) := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) ↦ β))]
        refine Finset.sum_congr rfl (fun p _ ↦ ?_)
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [h_step1]
      rw [show (Finset.univ : Finset (β × (Fin k → β)))
            = (Finset.univ : Finset β) ×ˢ (Finset.univ : Finset (Fin k → β)) from
              Finset.univ_product_univ.symm]
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    -- The second sum: ∑_y a 0 (y 0) · |∏ a' - ∏ b'| = (∑_y₀ a 0 y₀) · (∑_y' |∏ a' - ∏ b'|).
    have h_second_eq :
        ∑ y : Fin (k+1) → β,
            a 0 (y 0)
              * |∏ i : Fin k, a i.succ (y i.succ) - ∏ i : Fin k, b i.succ (y i.succ)|
          = (∑ y₀ : β, a 0 y₀)
              * (∑ y' : Fin k → β,
                  |∏ i : Fin k, a i.succ (y' i) - ∏ i : Fin k, b i.succ (y' i)|) := by
      have h_step1 :
          ∑ y : Fin (k+1) → β,
              a 0 (y 0)
                * |∏ i : Fin k, a i.succ (y i.succ) - ∏ i : Fin k, b i.succ (y i.succ)|
            = ∑ p : β × (Fin k → β),
              a 0 p.1
                * |∏ i : Fin k, a i.succ (p.2 i) - ∏ i : Fin k, b i.succ (p.2 i)| := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) ↦ β))]
        refine Finset.sum_congr rfl (fun p _ ↦ ?_)
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [h_step1]
      rw [show (Finset.univ : Finset (β × (Fin k → β)))
            = (Finset.univ : Finset β) ×ˢ (Finset.univ : Finset (Fin k → β)) from
              Finset.univ_product_univ.symm]
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    rw [h_first_eq, h_second_eq]
    -- ∑ y', ∏ b' (y' i) = ∏ i, ∑ z, b' i z = 1 (by hb_sum).
    have h_prod_b_sum : ∑ y' : Fin k → β, ∏ i : Fin k, b i.succ (y' i)
        = ∏ i : Fin k, ∑ z : β, b i.succ z := by
      rw [Fintype.prod_sum]
    have h_prod_b_one : ∏ i : Fin k, ∑ z : β, b i.succ z = 1 := by
      apply Finset.prod_eq_one
      intro i _; exact hb_sum _
    rw [h_prod_b_sum, h_prod_b_one, mul_one]
    rw [ha_sum, one_mul]
    -- IH on (a ∘ Fin.succ, b ∘ Fin.succ).
    have h_ih := ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)
      (fun i z ↦ ha_nn _ z) (fun i z ↦ hb_nn _ z) (fun i ↦ ha_sum _) (fun i ↦ hb_sum _)
    -- |a₀ - b₀| sum + IH ≤ ∑ i : Fin (k+1), ∑ z, |...|.
    rw [Fin.sum_univ_succ]
    linarith

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
/-- TV bound on `Measure.pi`. For finite types and (per-coord) probability
measures `μ_i, μ'_i`, and any event `E ⊆ Fin n → β`,
`|(Measure.pi μ_·).real E - (Measure.pi μ'_·).real E| ≤ ∑_i ∑_b |μ_i.real{b} - μ'_i.real{b}|`. -/
private lemma Measure_pi_real_event_diff_le
    {n : ℕ} (μ μ' : Fin n → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (μ' i)]
    (E : Set (Fin n → β)) :
    |(Measure.pi μ).real E - (Measure.pi μ').real E|
      ≤ ∑ i : Fin n, ∑ b : β, |(μ i).real {b} - (μ' i).real {b}| := by
  set a : Fin n → β → ℝ := fun i b ↦ (μ i).real ({b} : Set β) with _ha_def
  set b' : Fin n → β → ℝ := fun i b ↦ (μ' i).real ({b} : Set β) with _hb_def
  -- Each coord-sum is 1.
  have h_sum_per_coord : ∀ (ν : Measure β) [IsProbabilityMeasure ν],
      ∑ z : β, ν.real ({z} : Set β) = 1 := by
    intro ν _
    have h_pairwise : Pairwise (Function.onFun Disjoint (fun z : β ↦ ({z} : Set β))) := by
      intro z₁ z₂ hz
      show Disjoint (({z₁} : Set β)) (({z₂} : Set β))
      rw [Set.disjoint_singleton]; exact hz
    have h_meas : ∀ z : β, MeasurableSet ({z} : Set β) := fun z ↦ measurableSet_singleton z
    have h_iUnion : (⋃ z : β, ({z} : Set β)) = Set.univ := by ext x; simp
    have h := measureReal_iUnion_fintype (μ := ν) h_pairwise h_meas
    rw [h_iUnion] at h
    rw [← h, probReal_univ]
  have h_sum_a : ∀ i, ∑ z : β, a i z = 1 := fun i ↦ h_sum_per_coord (μ i)
  have h_sum_b : ∀ i, ∑ z : β, b' i z = 1 := fun i ↦ h_sum_per_coord (μ' i)
  have h_a_nn : ∀ i z, 0 ≤ a i z := fun _ _ ↦ ENNReal.toReal_nonneg
  have h_b_nn : ∀ i z, 0 ≤ b' i z := fun _ _ ↦ ENNReal.toReal_nonneg
  classical
  -- Convert E to a finite set of (Fin n → β) via filter on universe.
  set S : Finset (Fin n → β) := (Finset.univ : Finset (Fin n → β)).filter (· ∈ E) with hS_def
  have h_S_eq_E : (S : Set (Fin n → β)) = E := by
    ext y; simp [hS_def]
  -- Pi measure on E = pi measure on S.coe.
  have h_pi_eq : ∀ (ν : Fin n → Measure β) [∀ i, IsProbabilityMeasure (ν i)],
      (Measure.pi ν).real E
        = ∑ y ∈ S, (∏ i : Fin n, ν i ({y i} : Set β)).toReal := by
    intro ν _
    rw [Measure.real]
    rw [show ((Measure.pi ν) E) = (Measure.pi ν) (S : Set (Fin n → β)) from by rw [h_S_eq_E]]
    rw [measure_pi_eq_sum_singletons]
    rw [ENNReal.toReal_sum (fun y _ ↦ by
      refine ENNReal.prod_ne_top (fun i _ ↦ ?_); exact measure_ne_top _ _)]
  have h_μ_eq : (Measure.pi μ).real E
      = ∑ y ∈ S, ∏ i : Fin n, a i (y i) := by
    rw [h_pi_eq μ]
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [ENNReal.toReal_prod]; rfl
  have h_μ'_eq : (Measure.pi μ').real E
      = ∑ y ∈ S, ∏ i : Fin n, b' i (y i) := by
    rw [h_pi_eq μ']
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [ENNReal.toReal_prod]; rfl
  rw [h_μ_eq, h_μ'_eq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun y _ _ ↦ abs_nonneg _)).trans ?_
  exact sum_prod_diff_abs_le_aux a b' h_a_nn h_b_nn h_sum_a h_sum_b


omit [DecidableEq α] [Nonempty α] [DecidableEq β] in
/-- For `δ ∈ [0,1]`, the difference between `errorProbAt` under `W` and `W_smooth δ`
is bounded by `2 n δ`. -/
@[entry_point]
lemma errorProbAt_smooth_TV
    {M n : ℕ} (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (m : Fin M) :
    |(c.errorProbAt (Channel.smooth W δ) m).toReal - (c.errorProbAt W m).toReal|
      ≤ 2 * n * δ := by
  haveI : IsMarkovKernel (Channel.smooth W δ) := Channel.smooth_isMarkovKernel W hδ0 hδ1
  -- Apply Measure_pi_real_event_diff_le with μ_i := Channel.smooth W δ (c.encoder m i),
  -- μ'_i := W (c.encoder m i).
  have h_TV := Measure_pi_real_event_diff_le
    (fun i ↦ Channel.smooth W δ (c.encoder m i))
    (fun i ↦ W (c.encoder m i))
    (c.errorEvent m)
  -- errorProbAt = Measure.pi (· (encoder m i)) (errorEvent m), and `.toReal` of measure = `.real`.
  show |((Measure.pi (fun i ↦ (Channel.smooth W δ) (c.encoder m i))) (c.errorEvent m)).toReal
        - ((Measure.pi (fun i ↦ W (c.encoder m i))) (c.errorEvent m)).toReal| ≤ 2 * (n : ℝ) * δ
  refine h_TV.trans ?_
  -- Each per-coord sum ≤ 2δ by C.2.1.
  have h_each : ∀ i : Fin n,
      ∑ b : β, |((Channel.smooth W δ) (c.encoder m i)).real ({b} : Set β)
                  - (W (c.encoder m i)).real ({b} : Set β)| ≤ 2 * δ := by
    intro i
    -- Symmetrize: |a - b| = |b - a|.
    have h_sym : ∀ b : β,
        |((Channel.smooth W δ) (c.encoder m i)).real ({b} : Set β)
            - (W (c.encoder m i)).real ({b} : Set β)|
          = |(W (c.encoder m i)).real ({b} : Set β)
              - ((Channel.smooth W δ) (c.encoder m i)).real ({b} : Set β)| := by
      intro b; exact abs_sub_comm _ _
    simp_rw [h_sym]
    exact Channel.smooth_TV_bound W hδ0 hδ1 (c.encoder m i)
  have h_sum : ∑ i : Fin n,
      ∑ b : β, |((Channel.smooth W δ) (c.encoder m i)).real ({b} : Set β)
                  - (W (c.encoder m i)).real ({b} : Set β)|
        ≤ ∑ _i : Fin n, (2 * δ) :=
    Finset.sum_le_sum (fun i _ ↦ h_each i)
  refine h_sum.trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  rfl

/-! ## TV bound -/

end InformationTheory.Shannon.ChannelCoding
