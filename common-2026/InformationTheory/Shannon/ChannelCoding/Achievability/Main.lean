import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import InformationTheory.Shannon.ChannelCoding.Achievability.Core
import InformationTheory.Shannon.ChannelCoding.Achievability.RandomCodebook

/-!
# Channel coding achievability — pigeonhole + main theorem (Phase C-(d) / D)

Part of the longFile split of `Achievability.lean`. This part holds the
probabilistic-method pigeonhole `exists_codebook_le_avg` (Phase C-(d)) and the
headline theorem `channel_coding_achievability` (Phase D), which combines the
random-codebook average bound from `...Achievability.RandomCodebook` with the
pigeonhole.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ### Phase C-(d) — Pigeonhole (probabilistic-method form)

Restated to match the probabilistic-method shape of Phase C-(c): instead of a
uniform average over `Codebook M n α`, we draw codebooks from
`codebookMeasure p M n`. The pigeonhole is unchanged in spirit — if the
expectation `∑ codebook, μ_codebook · f(codebook) ≤ B`, then some `codebook` in
the support has `f(codebook) ≤ B`. The proof uses the fact that the codebook
measure is a probability measure (mass sums to `1` over the finite space) so the
weighted average is a convex combination. -/

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- **Pigeonhole (probabilistic-method form).** If the codebook expectation is
`≤ B`, then there exists a single codebook with `averageErrorProb ≤ B`. -/
theorem exists_codebook_le_avg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (B : ℝ)
    (h_avg :
      ∑ codebook : Codebook M n α,
        (codebookMeasure p M n).real {codebook} *
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B) :
    ∃ codebook : Codebook M n α,
      ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  -- Strategy: a convex combination `∑ w_i x_i ≤ B` with `w_i ≥ 0` and `∑ w_i = 1`
  -- implies `∃ i, x_i ≤ B`. Otherwise `x_i > B ∀ i`, so `∑ w_i x_i > ∑ w_i B = B`,
  -- contradiction.
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- The codebook measure is a probability measure: `∑ codebook, w(codebook) = 1`.
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Codebook M n α) := Pi.instMeasurableSingletonClass
  have h_sum_one : ∑ codebook : Codebook M n α,
      (codebookMeasure p M n).real {codebook} = 1 := by
    -- `Measure.pi` of probability measures is a probability measure.
    haveI : IsProbabilityMeasure (codebookMeasure p M n) :=
      codebookMeasure.instIsProbabilityMeasure p M n
    -- `sum_measureReal_singleton`: `∑ b ∈ Finset.univ, μ.real {b} = μ.real (Finset.univ : Set _)`.
    have h_real_univ : (codebookMeasure p M n).real
        ((Finset.univ : Finset (Codebook M n α)) : Set _) = 1 := by
      rw [Finset.coe_univ]
      rw [measureReal_def, measure_univ]
      rfl
    have h_sum_eq :=
      sum_measureReal_singleton (μ := codebookMeasure p M n)
        (Finset.univ : Finset (Codebook M n α))
    rw [h_sum_eq, h_real_univ]
  -- Each weight is nonneg.
  have h_w_nn : ∀ codebook : Codebook M n α,
      0 ≤ (codebookMeasure p M n).real {codebook} := fun _ => measureReal_nonneg
  -- The contradictory strict inequality.
  have h_contra : B < ∑ codebook : Codebook M n α,
      (codebookMeasure p M n).real {codebook} *
      ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
    calc B = B * 1 := by ring
      _ = B * ∑ codebook : Codebook M n α,
            (codebookMeasure p M n).real {codebook} := by rw [h_sum_one]
      _ = ∑ codebook : Codebook M n α,
            (codebookMeasure p M n).real {codebook} * B := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ < ∑ codebook : Codebook M n α,
            (codebookMeasure p M n).real {codebook} *
            ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
          -- Use `Finset.sum_lt_sum_of_nonempty` style: strict inequality holds for
          -- each codebook with weight > 0, weak inequality for weight = 0.
          -- Actually the codebook space being nonempty + each term contributing
          -- `w · B < w · x` (when w > 0) or `0 = 0` (when w = 0) suffices, but the
          -- sum is strict iff at least one weight is positive — which holds because
          -- `∑ w = 1 ≠ 0`.
          have h_each : ∀ codebook : Codebook M n α,
              (codebookMeasure p M n).real {codebook} * B
                ≤ (codebookMeasure p M n).real {codebook} *
                  ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
            intro codebook
            exact mul_le_mul_of_nonneg_left (h_none codebook).le (h_w_nn codebook)
          -- For the strict inequality, we need at least one codebook with positive weight.
          -- `∑ w = 1 > 0` implies some `w_i > 0`.
          have h_exists_pos : ∃ codebook : Codebook M n α,
              0 < (codebookMeasure p M n).real {codebook} := by
            by_contra h_none_pos
            simp only [not_exists, not_lt] at h_none_pos
            have h_all_zero : ∀ codebook : Codebook M n α,
                (codebookMeasure p M n).real {codebook} = 0 := fun c =>
              le_antisymm (h_none_pos c) (h_w_nn c)
            have : ∑ codebook : Codebook M n α,
                (codebookMeasure p M n).real {codebook} = 0 := by
              refine Finset.sum_eq_zero ?_
              intro c _; exact h_all_zero c
            rw [this] at h_sum_one
            exact one_ne_zero h_sum_one.symm
          obtain ⟨c₀, hc₀_pos⟩ := h_exists_pos
          have h_strict :
              (codebookMeasure p M n).real {c₀} * B
                < (codebookMeasure p M n).real {c₀} *
                  ((codebookToCode μ Xs Ys hM ε c₀).averageErrorProb W).toReal :=
            mul_lt_mul_of_pos_left (h_none c₀) hc₀_pos
          exact Finset.sum_lt_sum (fun i _ => h_each i) ⟨c₀, Finset.mem_univ _, h_strict⟩
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg h_contra)

/-! ### Phase D-(a) — Existence of a low-error codebook for large `n`

The "eventual smallness of random-codebook average" helper is folded into the
main theorem's proof; this section deliberately exposes no extra public lemma.
Subagent fills the proof of `channel_coding_achievability` below by combining
`random_codebook_average_le` (Phase C-(c)), `exists_codebook_le_avg`
(Phase C-(d)), and the rate-slack analysis. -/

/-! ### Phase D-(a) — i.i.d. ambient + entropy-MI bridge (TBD)

The main theorem instantiates `random_codebook_average_le` with the i.i.d. extension
of `(p, W)` on `Ω := ℕ → α × β`, `μ := Measure.infinitePi (jointDistribution p W)`,
`Xs i ω := (ω i).1`, `Ys i ω := (ω i).2`. The bridges to the abstract Phase B / C
formulation are:

* `iIndepFun (Xs/Ys) μ` from `iIndepFun_infinitePi` + composition with `Prod.fst/.snd`.
* `IdentDistrib (Xs i) (Xs 0) μ μ` from `infinitePi_map_eval` (identical marginals).
* `μ.map (Xs 0) = p`, `μ.map (Ys 0) = outputDistribution p W`,
  `μ.map (jointSequence Xs Ys 0) = jointDistribution p W`.
* `hposY` / `hposZ` need a "channel positivity" hypothesis (not currently part of the
  theorem signature). They are discharged by `sorry` until that hypothesis is added.
* The exponent `entropy μ (jointSequence ...) − entropy μ (Xs 0) − entropy μ (Ys 0)
  = −(mutualInfoOfChannel p W).toReal` requires
  `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` (chain rule + commutativity),
  which is not yet exposed in the project and is also discharged by `sorry`. -/

/-! ### Phase D-(b) — Main theorem -/

omit [DecidableEq α] [DecidableEq β] in
/-- **Channel coding achievability (Cover-Thomas 7.7.1, achievability half).**
For any rate `R < I(p; W)` and target error probability `ε' > 0`, there exists
`N` such that for all `n ≥ N` there is a block code of length `n` with at least
`exp (n · R)` messages whose average error probability is `< ε'`.

The proof instantiates the abstract Phase C result `random_codebook_average_le`
on the concrete i.i.d. ambient `Ω := ℕ → α × β`,
`μ := iidAmbientMeasure p W`, then runs `exists_codebook_le_avg` to extract a
single codebook from the codebook average bound. The rate slack
`ε := (I - R)/6` ensures both the E1 term (joint AEP) and the E2 term
`(M-1)·exp(-n(I - 3ε))` tend to 0 as `n → ∞`. -/
@[entry_point]
theorem channel_coding_achievability
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb W).toReal < ε' := by
  classical
  -- Step 1: rate slack. Set `ε := (I - R) / 6` so that `R + 3ε = (R + I)/2 < I`
  -- and `I - R - 3ε = (I - R) / 2 > 0`.
  set I : ℝ := (mutualInfoOfChannel p W).toReal with hI_def
  have hI_pos : 0 < I := lt_trans hR_pos hR
  set ε : ℝ := (I - R) / 6 with hε_def
  have hε_pos : 0 < ε := by
    refine div_pos ?_ (by norm_num)
    linarith
  have hR_3ε_lt_I : R + 3 * ε < I := by
    have : 3 * ε = (I - R) / 2 := by rw [hε_def]; ring
    rw [this]; linarith
  have h_gap_pos : 0 < I - R - 3 * ε := by linarith
  -- Step 2: set up i.i.d. ambient `μ := iidAmbientMeasure p W` on `Ω := ℕ → α × β`.
  set Ω : Type _ := ℕ → α × β
  set μ : Measure Ω := iidAmbientMeasure p W with hμ_def
  haveI : IsProbabilityMeasure μ := by
    rw [hμ_def]; infer_instance
  -- All abstract hypotheses on `(μ, iidXs, iidYs)` come from `IIDProductInput`.
  have hXs : ∀ i, Measurable (iidXs (α := α) (β := β) i) := measurable_iidXs
  have hYs : ∀ i, Measurable (iidYs (α := α) (β := β) i) := measurable_iidYs
  have hindepX_full : iIndepFun (fun i => iidXs (α := α) (β := β) i) μ :=
    iidAmbient_iIndepFun_iidXs p W
  have hindepY_full : iIndepFun (fun i => iidYs (α := α) (β := β) i) μ :=
    iidAmbient_iIndepFun_iidYs p W
  have hindepX_pair : Pairwise fun i j =>
      iidXs (α := α) (β := β) i ⟂ᵢ[μ] iidXs j :=
    iidAmbient_pairwise_indep_iidXs p W
  have hindepY_pair : Pairwise fun i j =>
      iidYs (α := α) (β := β) i ⟂ᵢ[μ] iidYs j :=
    iidAmbient_pairwise_indep_iidYs p W
  have hindepZ : Pairwise fun i j =>
      jointSequence (α := α) (β := β) iidXs iidYs i ⟂ᵢ[μ]
        jointSequence iidXs iidYs j :=
    iidAmbient_pairwise_indep_joint p W
  have hidentX : ∀ i,
      IdentDistrib (iidXs (α := α) (β := β) i) (iidXs 0) μ μ :=
    fun i => iidAmbient_identDistrib_iidXs p W i
  have hidentY : ∀ i,
      IdentDistrib (iidYs (α := α) (β := β) i) (iidYs 0) μ μ :=
    fun i => iidAmbient_identDistrib_iidYs p W i
  have hidentZ : ∀ i,
      IdentDistrib (jointSequence (α := α) (β := β) iidXs iidYs i)
        (jointSequence iidXs iidYs 0) μ μ :=
    fun i => iidAmbient_identDistrib_joint p W i
  have hposX : ∀ x : α, 0 < (μ.map (iidXs (α := α) (β := β) 0)).real {x} :=
    fun x => iidAmbient_iidXs_real_singleton_pos p W hp_pos x
  have hposY : ∀ y : β, 0 < (μ.map (iidYs (α := α) (β := β) 0)).real {y} :=
    fun y => iidAmbient_iidYs_real_singleton_pos p W hp_pos hW_pos y
  have hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence (α := α) (β := β) iidXs iidYs 0)).real {q} :=
    fun q => iidAmbient_joint_real_singleton_pos p W hp_pos hW_pos q
  have h_match_X : μ.map (iidXs (α := α) (β := β) 0) = p :=
    iidAmbient_map_iidXs p W 0
  have h_match_Z : μ.map (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = jointDistribution p W :=
    iidAmbient_map_jointSequence p W 0
  -- Step 3: identify the entropy exponent with `-I.toReal`.
  -- entropy μ (jointSequence iidXs iidYs 0) - entropy μ (iidXs 0) - entropy μ (iidYs 0) = -I.
  have h_entZ : InformationTheory.Shannon.entropy μ
      (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = InformationTheory.Shannon.entropy (jointDistribution p W) id := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p W)
      (jointSequence iidXs iidYs 0) id ?_
    refine ⟨(measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs 0).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    rw [iidAmbient_map_jointSequence, Measure.map_id]
  have h_entX : InformationTheory.Shannon.entropy μ (iidXs (α := α) (β := β) 0)
        = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.fst := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p W)
      (iidXs 0) Prod.fst ?_
    refine ⟨(measurable_iidXs 0).aemeasurable, measurable_fst.aemeasurable, ?_⟩
    -- (μ.map (iidXs 0)) = p, and (jointDistribution p W).map Prod.fst = p.
    rw [iidAmbient_map_iidXs]
    show p = (jointDistribution p W).map Prod.fst
    rw [show ((jointDistribution p W).map Prod.fst) = (jointDistribution p W).fst from rfl,
        jointDistribution_def]
    exact (Measure.fst_compProd p W).symm
  have h_entY : InformationTheory.Shannon.entropy μ (iidYs (α := α) (β := β) 0)
        = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.snd := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p W)
      (iidYs 0) Prod.snd ?_
    refine ⟨(measurable_iidYs 0).aemeasurable, measurable_snd.aemeasurable, ?_⟩
    rw [iidAmbient_map_iidYs]
    rfl
  -- Combine: HZ - HX - HY = -I.
  have h_exp_eq : InformationTheory.Shannon.entropy μ
        (jointSequence (α := α) (β := β) iidXs iidYs 0)
      - InformationTheory.Shannon.entropy μ (iidXs 0)
      - InformationTheory.Shannon.entropy μ (iidYs 0) = -I := by
    rw [h_entZ, h_entX, h_entY]
    have hMI := mutualInfoOfChannel_eq_HX_add_HY_sub_HZ p W
    rw [← hI_def] at hMI
    linarith
  -- Step 4-5: AEP closed-form `N₁` via Phase A (`jointlyTypicalSet_prob_ge_of_rate`).
  -- Gives `1 - ε'/2 ≤ (μ {good n}).toReal` for all `n ≥ N₁`.
  have hε'_half : 0 < ε' / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ :=
    jointlyTypicalSet_prob_ge_of_rate (β := β) μ iidXs iidYs hXs hYs
      hindepX_pair hidentX hindepY_pair hidentY hindepZ hidentZ hε_pos hε'_half
  -- Step 6-7: E2 closed-form `N₂` via Step 2 (`channelCoding_E2_lt_of_rate`).
  obtain ⟨N₂, hN₂⟩ :=
    channelCoding_E2_lt_of_rate (I := I) (R := R) (ε := ε) (ε' := ε' / 2)
      h_gap_pos hε'_half
  -- Step 8: assemble. N := max N₁ N₂ (and ensure n ≥ 1 for `0 < M`).
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn_N₁ : N₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_N₂ : N₂ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_one : 1 ≤ n := le_trans (le_max_right _ _) hn
  set M : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R)) with hM_def
  have hM_pos : 0 < M := Nat.ceil_pos.mpr (Real.exp_pos _)
  refine ⟨M, le_refl _, ?_⟩
  -- Apply `random_codebook_average_le` + `exists_codebook_le_avg`.
  have hindepZ_full : iIndepFun
      (fun i : ℕ => jointSequence (α := α) (β := β) iidXs iidYs i) μ :=
    iidAmbient_iIndepFun_joint p W
  have h_avg_bound :=
    random_codebook_average_le (M := M) (n := n) W p hp_pos hM_pos hε_pos μ iidXs iidYs
      hXs hYs hindepX_full hidentX hindepY_full hidentY hindepZ hindepZ_full hidentZ
      hposX hposY hposZ h_match_X h_match_Z
  -- The RHS of h_avg_bound is E1 + (M-1)*exp(n*(HZ-HX-HY+3ε)) = E1 + E2 (under h_exp_eq).
  -- Show this RHS is < ε'.
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
  -- Measurability of the joint "good" event (needed for the complement-sum identity).
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
  -- Closed-form `hN₁` is `1 - ε'/2 ≤ (μ {good}).toReal`; rewrite `E1 = 1 - μ.real {good}`.
  have hE1_le : E1 ≤ ε' / 2 := by
    have h_good_ge := hN₁ n hn_N₁
    rw [hE1_def]
    have h_compl_eq :
        {ω | (InformationTheory.Shannon.jointRV (α := α) iidXs n ω,
              InformationTheory.Shannon.jointRV (α := β) iidYs n ω) ∉
            jointlyTypicalSet μ iidXs iidYs n ε}
          = {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                InformationTheory.Shannon.jointRV iidYs n ω) ∈
              jointlyTypicalSet μ iidXs iidYs n ε}ᶜ := rfl
    rw [h_compl_eq, probReal_compl_eq_one_sub h_meas_good]
    -- `μ.real S = (μ S).toReal`; `1 - (μ {good}).toReal ≤ ε'/2 ⇐ 1 - ε'/2 ≤ (μ {good}).toReal`.
    have h_good_real_eq : μ.real
        {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
              InformationTheory.Shannon.jointRV iidYs n ω) ∈
            jointlyTypicalSet μ iidXs iidYs n ε}
        = (μ {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
              InformationTheory.Shannon.jointRV iidYs n ω) ∈
            jointlyTypicalSet μ iidXs iidYs n ε}).toReal := rfl
    rw [h_good_real_eq]
    linarith
  -- Closed-form `hN₂` is directly `(M-1) · exp(n·(-I+3ε)) < ε'/2`.
  have hE2_lt : E2 < ε' / 2 := by
    rw [h_E2_simp]
    simpa [hM_def] using hN₂ n hn_N₂
  have h_sum_lt : E1 + E2 < ε' := by linarith
  -- Now apply exists_codebook_le_avg with B := E1 + E2.
  obtain ⟨codebook, hcb⟩ :=
    exists_codebook_le_avg μ iidXs iidYs W p hM_pos (B := E1 + E2) h_avg_bound
  refine ⟨codebookToCode μ iidXs iidYs hM_pos ε codebook, ?_⟩
  exact lt_of_le_of_lt hcb h_sum_lt

end InformationTheory.Shannon.ChannelCoding
