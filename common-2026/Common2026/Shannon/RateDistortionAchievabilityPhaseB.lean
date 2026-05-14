import Common2026.Shannon.RateDistortionAchievability
import Common2026.Shannon.ChannelCodingAchievability

/-!
# Rate-distortion achievability — Phase B (joint-typical lossy encoder + distortion typical set)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)
Phase B MVP. Two pieces of infrastructure for the lossy compression chain.

## Phase B.1 — joint-typical lossy encoder

Symmetric counterpart to `ChannelCodingAchievability.jointTypicalDecoder` on the encoder
side of the lossy compression chain:

* `jointTypicalLossyEncoder` — given a codebook `c : Codebook M n β` and a source word
  `x : Fin n → α`, returns *some* (`Classical.choose`) message index `m` with
  `(x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε`. Falls back to `⟨0, hM⟩` if no such `m` exists.
* `lossyCodeOfCodebook` — bundles the joint-typical encoder + the codebook itself as
  decoder into a `LossyCode M n α β`.
* `jointTypicalLossyEncoder_spec_of_exists` / `_of_not_exists` — `dif_pos` / `dif_neg`
  characterisations of the two branches.

Note: unlike the channel-coding decoder side (`jointTypicalDecoder`), the lossy encoder
does **not** require uniqueness of the typical match — any one is fine because the
encoder's job is only to commit to a single index. Hence we use `Classical.choose`
of `∃ m, _` rather than `Classical.choose` of `∃! m, _`.

## Phase B.3 — distortion typical set

The intersection of `jointlyTypicalSet` with the empirical-distortion constraint
`blockDistortion d n x y ≤ 𝔼[d(X_0, Y_0)] + δ`:

* `expectedJointDistortion μ X Y d` — Bochner integral of `d(X, Y)` under `μ`.
* `distortionTypicalSet μ Xs Ys d n ε δ` — set of `(x, y)` jointly typical *and*
  whose empirical block distortion is within `δ` of the joint expectation.
* basic structure lemmas: subset to `jointlyTypicalSet`, membership iff,
  `MeasurableSet`, finiteness.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding (Codebook jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- **Joint-typical lossy encoder.** Given a codebook `c : Codebook M n β`,
returns the first (any) message index `m` whose codeword is jointly typical with the
source word `x`. Falls back to `⟨0, hM⟩` if no such `m` exists. -/
noncomputable def jointTypicalLossyEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    (Fin n → α) → Fin M := fun x =>
  haveI : Decidable (∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h
    else ⟨0, hM⟩

/-- Bundle a codebook + joint-typical lossy encoder into a `LossyCode`. The codebook
itself serves as the decoder. -/
noncomputable def lossyCodeOfCodebook
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    LossyCode M n α β where
  encoder := jointTypicalLossyEncoder μ Xs Ys hM ε c
  decoder := c

/-- If a typical match exists for `x`, the joint-typical lossy encoder returns one. -/
theorem jointTypicalLossyEncoder_spec_of_exists
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β)
    (x : Fin n → α)
    (h : ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :
    (x, c (jointTypicalLossyEncoder μ Xs Ys hM ε c x))
      ∈ jointlyTypicalSet μ Xs Ys n ε := by
  unfold jointTypicalLossyEncoder
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- If no typical match exists for `x`, the joint-typical lossy encoder returns the
fallback `⟨0, hM⟩`. -/
theorem jointTypicalLossyEncoder_spec_of_not_exists
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β)
    (x : Fin n → α)
    (h : ¬ ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :
    jointTypicalLossyEncoder μ Xs Ys hM ε c x = ⟨0, hM⟩ := by
  unfold jointTypicalLossyEncoder
  exact dif_neg h

/-! ## Phase B.3 — distortion typical set -/

/-- Expected per-symbol distortion `𝔼_μ[d(X, Y)]` as a real Bochner integral. The
bound used in `distortionTypicalSet` references this quantity at `i = 0`; under
stationary i.i.d. hypotheses it is independent of `i`. -/
noncomputable def expectedJointDistortion
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (d : DistortionFn α β) : ℝ :=
  ∫ ω, ((d (X ω) (Y ω) : NNReal) : ℝ) ∂μ

/-- **Distortion typical set.** Pairs `(x, y) ∈ (Fin n → α) × (Fin n → β)` that are
both (a) jointly typical in the entropy sense (`jointlyTypicalSet μ Xs Ys n ε`) and
(b) whose empirical block distortion is within `δ` of the joint expectation
`𝔼[d(X_0, Y_0)]`. The set used by Cover-Thomas 10.5 to bound the distortion on
encoder-success events. -/
noncomputable def distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    Set ((Fin n → α) × (Fin n → β)) :=
  jointlyTypicalSet μ Xs Ys n ε ∩
    {p | blockDistortion d n p.1 p.2
          ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ}

/-- Membership predicate for `distortionTypicalSet`, split into the two component
conditions. -/
theorem mem_distortionTypicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    (x : Fin n → α) (y : Fin n → β) :
    (x, y) ∈ distortionTypicalSet μ Xs Ys d n ε δ ↔
      (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε ∧
      blockDistortion d n x y
        ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ := Iff.rfl

/-- `distortionTypicalSet ⊆ jointlyTypicalSet`. -/
theorem distortionTypicalSet_subset_jointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    distortionTypicalSet μ Xs Ys d n ε δ ⊆ jointlyTypicalSet μ Xs Ys n ε :=
  fun _ h => h.1

/-- Joint typicality follows from membership in `distortionTypicalSet`. -/
theorem mem_jointlyTypicalSet_of_mem_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    {p : (Fin n → α) × (Fin n → β)}
    (h : p ∈ distortionTypicalSet μ Xs Ys d n ε δ) :
    p ∈ jointlyTypicalSet μ Xs Ys n ε := h.1

/-- **B.2.1**: on `distortionTypicalSet`, the empirical block distortion is bounded
by the joint expectation plus `δ`. This is the structural fact that drives the
distortion bound on encoder-success events in Cover-Thomas 10.5 (10.85). -/
theorem blockDistortion_le_of_mem_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    {p : (Fin n → α) × (Fin n → β)}
    (h : p ∈ distortionTypicalSet μ Xs Ys d n ε δ) :
    blockDistortion d n p.1 p.2
      ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ := h.2

/-- `distortionTypicalSet` is finite (subset of a finite ambient `(Fin n → α) × (Fin n → β)`). -/
theorem distortionTypicalSet_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    (distortionTypicalSet μ Xs Ys d n ε δ).Finite :=
  Set.toFinite _

/-- `distortionTypicalSet` is measurable (subset of a finite ambient). -/
theorem measurableSet_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    MeasurableSet (distortionTypicalSet μ Xs Ys d n ε δ) :=
  (distortionTypicalSet_finite μ Xs Ys d n ε δ).measurableSet

end InformationTheory.Shannon
