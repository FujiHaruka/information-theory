import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# D-1'' Phase D.2 — parent achievability instantiated at the smooth channel

`ShannonTheoremFullDischarge` から分割した part ファイル。
詳細は冒頭の `Phase D.2` セクション docstring を参照。
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

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

omit [DecidableEq α] [DecidableEq β] in
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

end InformationTheory.Shannon.ChannelCoding
