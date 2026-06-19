import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Achievability at the smooth channel — closed-form N

Part file split from `ShannonTheoremFullDischarge`. Instantiates
`channel_coding_achievability` at the smooth channel with an explicit `N` formula.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Smooth achievability with closed-form N

`channel_coding_achievability` instantiated at `p := pmfToMeasure (pSmooth p₀ δ_p)` and
`W := Channel.smooth W δ`. The instances `hp_pos`/`hW_pos` are derived internally via
`pSmooth_pos` and `Channel.smooth_pos`. The existential `∃ N` is collapsed to the
closed-form `channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε'` using the AEPRate lemmas. -/

/-- Closed-form `N(V_X, V_Y, V_Z, I_lb, R, ε')` for the smooth achievability theorem.

`max (max N₁ N₂) 1` where `N₁ = jointlyTypicalSetMinN V_X V_Y V_Z (ε'/2) ((I_lb - R)/6)`
and `N₂ = expNegMulMinN ((I_lb - R)/2) (ε'/2)`. Uses a mutual information lower bound
`I_lb` so that `N₂` is a safe upper bound. -/
noncomputable def channelCodingSmoothMinN
    (V_X V_Y V_Z I_lb R ε' : ℝ) : ℕ :=
  max (max
        (jointlyTypicalSetMinN V_X V_Y V_Z (ε' / 2) ((I_lb - R) / 6))
        (expNegMulMinN ((I_lb - R) / 2) (ε' / 2)))
      1

theorem jointlyTypicalSetMinN_le_channelCodingSmoothMinN
    (V_X V_Y V_Z I_lb R ε' : ℝ) :
    jointlyTypicalSetMinN V_X V_Y V_Z (ε' / 2) ((I_lb - R) / 6) ≤
      channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' := by
  unfold channelCodingSmoothMinN
  exact (le_max_left _ _).trans (le_max_left _ _)

theorem expNegMulMinN_le_channelCodingSmoothMinN
    (V_X V_Y V_Z I_lb R ε' : ℝ) :
    expNegMulMinN ((I_lb - R) / 2) (ε' / 2) ≤
      channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' := by
  unfold channelCodingSmoothMinN
  exact (le_max_right _ _).trans (le_max_left _ _)

theorem one_le_channelCodingSmoothMinN
    (V_X V_Y V_Z I_lb R ε' : ℝ) :
    1 ≤ channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε' := by
  unfold channelCodingSmoothMinN
  exact le_max_right _ _

omit [DecidableEq α] [DecidableEq β] in
theorem iidAmbient_entropy_exponent_eq
    (p : Measure α) [IsProbabilityMeasure p]
    (Wδ : Channel α β) [IsMarkovKernel Wδ] :
    InformationTheory.Shannon.entropy (iidAmbientMeasure p Wδ)
        (jointSequence (α := α) (β := β) iidXs iidYs 0)
      - InformationTheory.Shannon.entropy (iidAmbientMeasure p Wδ) (iidXs 0)
      - InformationTheory.Shannon.entropy (iidAmbientMeasure p Wδ) (iidYs 0)
        = -(mutualInfoOfChannel p Wδ).toReal := by
  set μ : Measure (ℕ → α × β) := iidAmbientMeasure p Wδ with hμ_def
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
  rw [h_entZ, h_entX, h_entY]
  have hMI := mutualInfoOfChannel_eq_HX_add_HY_sub_HZ p Wδ
  linarith

omit [DecidableEq α] [DecidableEq β] in
/-- The random-codebook average bound at the i.i.d. ambient measure
`iidAmbientMeasure p Wδ`, regenerating the independence / identical-distribution /
positivity / marginal facts from the `iidAmbient_*` lemmas. -/
private theorem channelCodingSmooth_avg_bound
    (p : Measure α) [IsProbabilityMeasure p] (Wδ : Channel α β) [IsMarkovKernel Wδ]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (Wδ a).real {b})
    {M n : ℕ} (hM_pos : 0 < M) {ε : ℝ} (hε_pos : 0 < ε) :
    ∑ codebook : Codebook M n α,
        (codebookMeasure p M n).real {codebook} *
        ((codebookToCode (iidAmbientMeasure p Wδ) iidXs iidYs hM_pos ε codebook).averageErrorProb
          Wδ).toReal
    ≤ (iidAmbientMeasure p Wδ).real
        {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
              InformationTheory.Shannon.jointRV iidYs n ω) ∉
            jointlyTypicalSet (iidAmbientMeasure p Wδ) iidXs iidYs n ε}
      + ((M : ℝ) - 1) *
          Real.exp ((n : ℝ) *
            ((InformationTheory.Shannon.entropy (iidAmbientMeasure p Wδ)
                (jointSequence iidXs iidYs 0)
              - InformationTheory.Shannon.entropy (iidAmbientMeasure p Wδ) (iidXs 0)
              - InformationTheory.Shannon.entropy (iidAmbientMeasure p Wδ) (iidYs 0)) + 3 * ε)) := by
  set μ : Measure (ℕ → α × β) := iidAmbientMeasure p Wδ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  exact random_codebook_average_le (M := M) (n := n) Wδ p hp_pos hM_pos hε_pos μ iidXs iidYs
    measurable_iidXs measurable_iidYs (iidAmbient_iIndepFun_iidXs p Wδ)
    (fun i => iidAmbient_identDistrib_iidXs p Wδ i) (iidAmbient_iIndepFun_iidYs p Wδ)
    (fun i => iidAmbient_identDistrib_iidYs p Wδ i) (iidAmbient_pairwise_indep_joint p Wδ)
    (iidAmbient_iIndepFun_joint p Wδ) (fun i => iidAmbient_identDistrib_joint p Wδ i)
    (fun x => iidAmbient_iidXs_real_singleton_pos p Wδ hp_pos x)
    (fun y => iidAmbient_iidYs_real_singleton_pos p Wδ hp_pos hW_pos y)
    (fun q => iidAmbient_joint_real_singleton_pos p Wδ hp_pos hW_pos q)
    (iidAmbient_map_iidXs p Wδ 0) (iidAmbient_map_jointSequence p Wδ 0)

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β] in
/-- Assembles the smooth-achievability codebook from the random-codebook average
bound `h_avg`, the joint-AEP bound `hN₁`, and the error-exponent bound `hN₂`.
The `E1`/`E2` split mirrors `random_codebook_average_le`'s right-hand side; `hN₂`
is supplied at the `I_lb` exponent and lifted to the exact `I` via `hI_lb_le_I`. -/
private theorem channelCodingSmooth_assemble
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (Wδ : Channel α β) [IsMarkovKernel Wδ]
    (p : Measure α) [IsProbabilityMeasure p]
    {M n : ℕ} (hM_pos : 0 < M) {ε ε' I I_lb : ℝ}
    (hI_lb_le_I : I_lb ≤ I)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_exp_eq : InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
        - InformationTheory.Shannon.entropy μ (Xs 0)
        - InformationTheory.Shannon.entropy μ (Ys 0) = -I)
    (h_avg_bound :
      ∑ codebook : Codebook M n α,
          (codebookMeasure p M n).real {codebook} *
          ((codebookToCode μ Xs Ys hM_pos ε codebook).averageErrorProb Wδ).toReal
      ≤ μ.real
          {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                InformationTheory.Shannon.jointRV Ys n ω) ∉
              jointlyTypicalSet μ Xs Ys n ε}
        + ((M : ℝ) - 1) *
            Real.exp ((n : ℝ) *
              ((InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
                - InformationTheory.Shannon.entropy μ (Xs 0)
                - InformationTheory.Shannon.entropy μ (Ys 0)) + 3 * ε)))
    (hN₁ : 1 - ε' / 2 ≤
        (μ {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                 InformationTheory.Shannon.jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}).toReal)
    (hN₂ : ((M : ℝ) - 1) * Real.exp ((n : ℝ) * (-I_lb + 3 * ε)) < ε' / 2) :
    ∃ codebook : Codebook M n α,
      ((codebookToCode μ Xs Ys hM_pos ε codebook).averageErrorProb Wδ).toReal < ε' := by
  classical
  set E1 : ℝ := μ.real
      {ω | (InformationTheory.Shannon.jointRV Xs n ω,
            InformationTheory.Shannon.jointRV Ys n ω) ∉
          jointlyTypicalSet μ Xs Ys n ε} with hE1_def
  set E2 : ℝ := ((M : ℝ) - 1) *
      Real.exp ((n : ℝ) *
        ((InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
          - InformationTheory.Shannon.entropy μ (Xs 0)
          - InformationTheory.Shannon.entropy μ (Ys 0)) + 3 * ε)) with hE2_def
  have h_E2_simp : E2 = ((M : ℝ) - 1) *
      Real.exp ((n : ℝ) * (-I + 3 * ε)) := by
    rw [hE2_def]
    congr 2
    rw [h_exp_eq]
  -- Measurability of joint "good" event.
  have h_meas_good : MeasurableSet
      {ω | (InformationTheory.Shannon.jointRV Xs n ω,
            InformationTheory.Shannon.jointRV Ys n ω) ∈
          jointlyTypicalSet μ Xs Ys n ε} := by
    have h_meas_pair : Measurable (fun ω =>
        (InformationTheory.Shannon.jointRV (α := α) Xs n ω,
          InformationTheory.Shannon.jointRV (α := β) Ys n ω)) :=
      (InformationTheory.Shannon.measurable_jointRV Xs hXs n).prodMk
        (InformationTheory.Shannon.measurable_jointRV Ys hYs n)
    exact h_meas_pair (measurableSet_jointlyTypicalSet _ _ _ _ _)
  -- E1 ≤ ε'/2 via the joint-AEP closed form.
  have hE1_le : E1 ≤ ε' / 2 := by
    rw [hE1_def]
    have h_compl_eq :
        {ω | (InformationTheory.Shannon.jointRV (α := α) Xs n ω,
              InformationTheory.Shannon.jointRV (α := β) Ys n ω) ∉
            jointlyTypicalSet μ Xs Ys n ε}
          = {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                InformationTheory.Shannon.jointRV Ys n ω) ∈
              jointlyTypicalSet μ Xs Ys n ε}ᶜ := rfl
    rw [h_compl_eq, probReal_compl_eq_one_sub h_meas_good]
    have h_good_real_eq : μ.real
        {ω | (InformationTheory.Shannon.jointRV Xs n ω,
              InformationTheory.Shannon.jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}
        = (μ {ω | (InformationTheory.Shannon.jointRV Xs n ω,
              InformationTheory.Shannon.jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}).toReal := rfl
    rw [h_good_real_eq]
    linarith
  -- E2 ≤ ε'/2 — `hN₂` is at exponent `-I_lb + 3ε`, while `E2` simplifies to
  -- `-I + 3ε`. Since `I_lb ≤ I`, `-I + 3ε ≤ -I_lb + 3ε`, so the E2 value is smaller.
  have hE2_lt : E2 < ε' / 2 := by
    rw [h_E2_simp]
    have h_exp_mono :
        Real.exp ((n : ℝ) * (-I + 3 * ε)) ≤ Real.exp ((n : ℝ) * (-I_lb + 3 * ε)) := by
      apply Real.exp_le_exp.mpr
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have h_le : -I + 3 * ε ≤ -I_lb + 3 * ε := by linarith
      exact mul_le_mul_of_nonneg_left h_le hn_nn
    have hM_sub_nn : 0 ≤ (M : ℝ) - 1 := by
      have : 1 ≤ (M : ℝ) := by exact_mod_cast hM_pos
      linarith
    have h_E2_le :
        ((M : ℝ) - 1) * Real.exp ((n : ℝ) * (-I + 3 * ε))
          ≤ ((M : ℝ) - 1) * Real.exp ((n : ℝ) * (-I_lb + 3 * ε)) :=
      mul_le_mul_of_nonneg_left h_exp_mono hM_sub_nn
    exact lt_of_le_of_lt h_E2_le hN₂
  have h_sum_lt : E1 + E2 < ε' := by linarith
  obtain ⟨codebook, hcb⟩ :=
    exists_codebook_le_avg μ Xs Ys Wδ p hM_pos (B := E1 + E2) h_avg_bound
  exact ⟨codebook, lt_of_le_of_lt hcb h_sum_lt⟩

omit [DecidableEq α] [DecidableEq β] in
/-- **Smooth achievability with closed-form N**: `channel_coding_achievability` with the
existential `N` replaced by `channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε'`.

The caller supplies axis-wise variance upper bounds `V_X, V_Y, V_Z` and a
mutual-information lower bound `I_lb`. -/
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
  -- Step 3: entropy exponent equation (HZ - HX - HY = -I).
  have h_exp_eq : InformationTheory.Shannon.entropy μ
        (jointSequence (α := α) (β := β) iidXs iidYs 0)
      - InformationTheory.Shannon.entropy μ (iidXs 0)
      - InformationTheory.Shannon.entropy μ (iidYs 0) = -I := by
    rw [hμ_def, hI_def]
    exact iidAmbient_entropy_exponent_eq p Wδ
  -- Step 4-5: closed-form `N₁` from `jointlyTypicalSet_prob_ge_at_N_le`.
  have hε'_half : 0 < ε' / 2 := by linarith
  intro n hn_ge
  -- Extract sub-bounds from `channelCodingSmoothMinN ≤ n`.
  have hn_N₁ : jointlyTypicalSetMinN V_X V_Y V_Z (ε' / 2) ε ≤ n := by
    rw [hε_def]
    exact (jointlyTypicalSetMinN_le_channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε').trans hn_ge
  have hn_N₂ : expNegMulMinN ((I_lb - R) / 2) (ε' / 2) ≤ n :=
    (expNegMulMinN_le_channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε').trans hn_ge
  have hn_one : 1 ≤ n :=
    (one_le_channelCodingSmoothMinN V_X V_Y V_Z I_lb R ε').trans hn_ge
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
  have h_avg_bound :=
    channelCodingSmooth_avg_bound (M := M) (n := n) p Wδ hp_pos hW_pos hM_pos hε_pos
  obtain ⟨codebook, hcb⟩ :=
    channelCodingSmooth_assemble μ iidXs iidYs Wδ p hM_pos hI_lb_le_I
      hXs hYs h_exp_eq h_avg_bound hN₁ hN₂
  exact ⟨codebookToCode μ iidXs iidYs hM_pos ε codebook, hcb⟩

end InformationTheory.Shannon.ChannelCoding
