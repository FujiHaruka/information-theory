import Common2026.Shannon.ChannelCoding
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Channel coding achievability theorem (B-3'')

[B-3'' Phase C+D plan](../../../docs/shannon/channel-coding-phase-cd-plan.md).

Phase A+B are completed in `Common2026/Shannon/ChannelCoding.lean` (659 行).
This file adds:

* **Phase C** (random codebook + averaging argument): Codebook + joint typical
  decoder definition; per-codeword error decomposition; random-codebook average
  bound; pigeonhole `∃ codebook, P_err ≤ avg`.
* **Phase D** (main theorem): `R < I(p; W) ⟹ ∃ N, ∀ n ≥ N, ∃ M ≥ exp(nR), ∃ code,
  averageErrorProb < ε`.

Skeleton phase: every lemma/theorem body is `:= by sorry` (or `:= sorry` for
non-`Prop` definitions that are sorry-placeheld). The next agent fills.

## Design choices (verbatim from plan)

* Codebook is `Fin M → (Fin n → α)` (abbrev). The codebook average is the
  uniform `Finset.sum` over `Finset.univ : Finset (Codebook M n α)` rather than
  a probability measure.
* Decoder = `Classical.dec`-based "unique joint-typical `m`, else fallback `⟨0, hM⟩`".
* i.i.d. extension Ω := `Fin n → α × β`, `μ := Measure.pi (fun _ => jointDistribution p W)`.
* Rate slack `ε := (I - R) / 6`; `M := Nat.ceil (Real.exp (n · R))`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Phase 0 — i.i.d. input × channel plumbing -/

section IIDInput

/-- The i.i.d. extension of `(p, W)` to length-`n` blocks: a measure on
`Fin n → α × β` whose `i`-th coordinate has law `jointDistribution p W`. -/
noncomputable def iidJointMeasure
    (p : Measure α) (W : Channel α β) (n : ℕ) : Measure (Fin n → α × β) :=
  Measure.pi (fun _ : Fin n => jointDistribution p W)

instance iidJointMeasure.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsProbabilityMeasure (iidJointMeasure p W n) := by
  unfold iidJointMeasure
  infer_instance

end IIDInput

/-! ### Phase C-(a) — Codebook + joint-typical decoder -/

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- A random codebook is just a function from message indices to length-`n` words. -/
abbrev Codebook (M n : ℕ) (α : Type*) [MeasurableSpace α] :=
  Fin M → (Fin n → α)

/-- **Joint-typical decoder.** Given a received word `y`, returns the unique
message `m` such that `(codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε`, falling
back to `⟨0, hM⟩` if either no such `m` exists or it is not unique. -/
noncomputable def jointTypicalDecoder
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    (Fin n → β) → Fin M := fun y =>
  haveI : Decidable (∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else ⟨0, hM⟩

/-- Bundle a codebook + joint-typical decoder into a `Code`. -/
noncomputable def codebookToCode
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    Code M n α β where
  encoder := codebook
  decoder := jointTypicalDecoder μ Xs Ys hM ε codebook

/-! ### Phase C-(b) — Per-codeword error decomposition -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] [DecidableEq β]
  [Nonempty β] in
/-- **Per-codeword error bound.** The point-wise error probability of message `m`
under the joint-typical decoder is bounded by the (E1) "true codeword not typical"
event plus the (E2) "some alias codeword is typical" union bound. -/
theorem errorProbAt_le_E1_plus_E2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ}
    (codebook : Codebook M n α) (m : Fin M) :
    ((codebookToCode μ Xs Ys hM ε codebook).errorProbAt W m).toReal
      ≤ (Measure.pi (fun i => W (codebook m i))).real
          {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            (Measure.pi (fun i => W (codebook m i))).real
              {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
  classical
  -- Abbreviations.
  set c : Code M n α β := codebookToCode μ Xs Ys hM ε codebook with hc_def
  set ν : Measure (Fin n → β) := Measure.pi (fun i => W (codebook m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by
    rw [hν_def]; infer_instance
  -- Define the (E1) and (E2) sets.
  set E1 : Set (Fin n → β) :=
    {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε} with hE1_def
  set E2_indiv : Fin M → Set (Fin n → β) := fun m' =>
    {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} with hE2_def
  -- Step 1: `c.errorEvent m ⊆ E1 ∪ (⋃ m' ∈ univ.erase m, E2_indiv m')`.
  have h_sub :
      c.errorEvent m ⊆ E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m' := by
    intro y hy
    rw [Code.mem_errorEvent] at hy
    -- `c.decoder y = jointTypicalDecoder μ Xs Ys hM ε codebook y`.
    have hdec : c.decoder y = jointTypicalDecoder μ Xs Ys hM ε codebook y := rfl
    -- Case analyze on whether there is a unique joint-typical `m'`.
    by_cases hu : ∃! m' : Fin M, (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε
    · -- A unique `m'` exists. Decoder returns `Classical.choose hu.exists`.
      have hch : c.decoder y = Classical.choose hu.exists := by
        rw [hdec]
        unfold jointTypicalDecoder
        rw [dif_pos hu]
      set m' := Classical.choose hu.exists with hm'_def
      have hm'_mem : (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε :=
        Classical.choose_spec hu.exists
      have hm'_ne : m' ≠ m := by
        intro hmm
        apply hy
        rw [hch, ← hmm]
      -- Either the true `m` is not typical (E1), or the chosen `m'` ≠ m is typical (E2).
      by_cases hm_typ : (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
      · -- `m` is also typical. Uniqueness ⇒ `m' = m`, contradicting `hm'_ne`.
        have : m' = m := hu.unique hm'_mem hm_typ
        exact absurd this hm'_ne
      · -- `m` is NOT typical: y ∈ E1.
        left
        exact hm_typ
    · -- No unique typical `m'`. Decoder falls back to `⟨0, hM⟩` ≠ … ?
      -- Either NO typical `m'` exists, or multiple do.
      by_cases hexists : ∃ m' : Fin M, (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε
      · -- Multiple typical `m'` exist (because not unique). At least two distinct ones.
        -- We exhibit some `m' ≠ m` that is typical.
        -- Since not unique: either (a) the true `m` is not typical, or
        -- (b) some other typical `m'' ≠ m` exists.
        by_cases hm_typ : (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
        · -- `m` is typical. Since not unique, some `m'' ≠ m` is also typical.
          -- Suppose for contradiction every typical witness equals `m`. Then
          -- `m` is the unique one — contradicting `¬ hu`.
          have h_alias : ∃ m'' : Fin M, (codebook m'', y) ∈ jointlyTypicalSet μ Xs Ys n ε ∧ m'' ≠ m := by
            by_contra h_none
            apply hu
            refine ⟨m, hm_typ, ?_⟩
            intro m'' hm''_typ
            by_contra hne
            exact h_none ⟨m'', hm''_typ, hne⟩
          obtain ⟨m'', hm''_typ, hm''_ne⟩ := h_alias
          right
          refine Set.mem_iUnion.mpr ⟨m'', ?_⟩
          refine Set.mem_iUnion.mpr ⟨?_, hm''_typ⟩
          exact Finset.mem_erase.mpr ⟨hm''_ne, Finset.mem_univ _⟩
        · -- `m` not typical: y ∈ E1.
          left; exact hm_typ
      · -- No typical `m'` at all ⇒ in particular `m` is not typical: y ∈ E1.
        left
        intro hm_typ
        exact hexists ⟨m, hm_typ⟩
  -- Step 2: bound the measure.
  -- First: `c.errorProbAt W m = ν (c.errorEvent m)` (by defeq of `codebookToCode`).
  have h_eq_meas : c.errorProbAt W m = ν (c.errorEvent m) := by
    show (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m) = _
    rfl
  -- The error event is measurable (finite alphabet).
  have h_meas_err : MeasurableSet (c.errorEvent m) :=
    (Set.toFinite _).measurableSet
  -- `ν (c.errorEvent m) ≠ ∞`.
  have h_ne_top : ν (c.errorEvent m) ≠ ∞ := measure_ne_top _ _
  -- Convert to .real.
  have h_real_eq : (c.errorProbAt W m).toReal = ν.real (c.errorEvent m) := by
    rw [h_eq_meas]; rfl
  rw [h_real_eq]
  -- Apply monotonicity and union bound.
  have h_meas_E1 : MeasurableSet E1 := (Set.toFinite _).measurableSet
  have h_meas_union : MeasurableSet (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    (Set.toFinite _).measurableSet
  have h_step1 : ν.real (c.errorEvent m) ≤
      ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    measureReal_mono h_sub (by exact measure_ne_top _ _)
  have h_step2 : ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m')
      ≤ ν.real E1 + ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    measureReal_union_le _ _
  have h_step3 :
      ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m')
      ≤ ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, ν.real (E2_indiv m') := by
    exact measureReal_biUnion_finset_le _ _
  -- Combine.
  calc ν.real (c.errorEvent m)
      ≤ ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') := h_step1
    _ ≤ ν.real E1 + ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') := h_step2
    _ ≤ ν.real E1 + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, ν.real (E2_indiv m') := by
        gcongr

/-! ### Phase C-(c) — Random codebook average bound -/

/-- **Random codebook average.** Averaging the average error probability over a
uniform choice of codebook decomposes (via Fubini-like coordinate swap) into
the Phase B-(a) "joint typical event probability" + the Phase B-(c)
independent-pair bound times `(M - 1)`. -/
theorem random_codebook_average_le
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {q}) :
    (Fintype.card (Codebook M n α) : ℝ)⁻¹ *
      ∑ codebook : Codebook M n α,
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal
    ≤ μ.real
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε}
      + ((M : ℝ) - 1) *
          Real.exp ((n : ℝ) *
            ((entropy μ (jointSequence Xs Ys 0)
              - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3 * ε)) := by
  sorry

/-! ### Phase C-(d) — Pigeonhole -/

omit [DecidableEq α] [MeasurableSingletonClass α] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- **Pigeonhole.** If the codebook average is `≤ B`, then there exists a single
codebook with `averageErrorProb ≤ B`. -/
theorem exists_codebook_le_avg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (B : ℝ)
    (h_avg :
      (Fintype.card (Codebook M n α) : ℝ)⁻¹ *
        ∑ codebook : Codebook M n α,
          ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B) :
    ∃ codebook : Codebook M n α,
      ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B := by
  classical
  -- The codebook space is nonempty: `α` is nonempty and `Fin M` (with `0 < M`) is.
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  haveI : Nonempty (Codebook M n α) := inferInstance
  -- Hence `Fintype.card (Codebook M n α) > 0`.
  have h_card_pos : 0 < Fintype.card (Codebook M n α) := Fintype.card_pos
  have h_card_R_pos : (0 : ℝ) < (Fintype.card (Codebook M n α) : ℝ) := by
    exact_mod_cast h_card_pos
  -- Rewrite the average bound as a sum bound: `∑ … ≤ card · B`.
  have h_sum_le :
      ∑ codebook : Codebook M n α,
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal
        ≤ (Fintype.card (Codebook M n α) : ℝ) * B := by
    have := mul_le_mul_of_nonneg_left h_avg h_card_R_pos.le
    -- LHS: card · (card⁻¹ · ∑) = ∑ when card > 0.
    have h_simp : (Fintype.card (Codebook M n α) : ℝ) *
        ((Fintype.card (Codebook M n α) : ℝ)⁻¹ *
          ∑ codebook : Codebook M n α,
            ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal)
        = ∑ codebook : Codebook M n α,
            ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
      rw [← mul_assoc, mul_inv_cancel₀ h_card_R_pos.ne', one_mul]
    linarith [this, h_simp.symm.le, h_simp.le]
  -- Convert into "∑ f ≤ ∑ (const B)" so we can apply `Finset.exists_le_of_sum_le`.
  have h_sum_const : (Fintype.card (Codebook M n α) : ℝ) * B
      = ∑ _codebook : Codebook M n α, B := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have h_sum_le' :
      ∑ codebook : Codebook M n α,
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal
        ≤ ∑ _codebook : Codebook M n α, B := by
    rw [← h_sum_const]; exact h_sum_le
  have hne : (Finset.univ : Finset (Codebook M n α)).Nonempty :=
    Finset.univ_nonempty
  obtain ⟨codebook, _, h_le⟩ :=
    Finset.exists_le_of_sum_le hne h_sum_le'
  exact ⟨codebook, h_le⟩

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

/-- **Channel coding achievability (Cover-Thomas 7.7.1, achievability half).**
For any rate `R < I(p; W)` and target error probability `ε' > 0`, there exists
`N` such that for all `n ≥ N` there is a block code of length `n` with at least
`exp (n · R)` messages whose average error probability is `< ε'`. -/
theorem channel_coding_achievability
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb W).toReal < ε' := by
  -- Step 1: rate slack.
  set I : ℝ := (mutualInfoOfChannel p W).toReal with hI_def
  have hI_pos : 0 < I := lt_trans hR_pos hR
  set ε : ℝ := (I - R) / 6 with hε_def
  have hε_pos : 0 < ε := by
    refine div_pos ?_ (by norm_num)
    linarith
  -- Step 2: pick a threshold n₀ guaranteeing all asymptotic bounds. Filling this
  -- requires combining Phase B-(a) (E1 → 0) with the exponential decay of E2 under
  -- the rate constraint `R + 3ε < I`. Both steps depend on bridges currently
  -- unavailable in the project (channel positivity, entropy-MI chain identity).
  -- See the section docstring for the precise list of TBDs.
  sorry

end InformationTheory.Shannon.ChannelCoding
