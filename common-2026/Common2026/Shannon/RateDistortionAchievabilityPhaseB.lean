import Common2026.Shannon.RateDistortionAchievability
import Common2026.Shannon.ChannelCodingAchievability

/-!
# Rate-distortion achievability — Phase B.1 (joint-typical lossy encoder + bundling)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)
Phase B.1 MVP. Symmetric counterpart to `ChannelCodingAchievability.jointTypicalDecoder`
on the encoder side of the lossy compression chain:

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

end InformationTheory.Shannon
