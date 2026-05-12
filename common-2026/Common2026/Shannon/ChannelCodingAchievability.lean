import Common2026.Shannon.ChannelCoding

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
  sorry

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
  sorry

/-! ### Phase D-(a) — Existence of a low-error codebook for large `n`

The "eventual smallness of random-codebook average" helper is folded into the
main theorem's proof; this section deliberately exposes no extra public lemma.
Subagent fills the proof of `channel_coding_achievability` below by combining
`random_codebook_average_le` (Phase C-(c)), `exists_codebook_le_avg`
(Phase C-(d)), and the rate-slack analysis. -/

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
  sorry

end InformationTheory.Shannon.ChannelCoding
