import InformationTheory.Shannon.MultipleAccess.Converse

/-!
# Relay channel — cut-set outer bound (structure + single-letterization)

The relay channel (Cover–Thomas §15.10) has a single sender, a single relay, and a single
receiver. The cut-set outer bound (Thm 15.10.1) bounds any achievable rate by the minimum of
two mutual-information quantities, evaluated at the worst joint input distribution:

* the **broadcast cut** `I(X; Y₁, Y | X₁)` — information leaving the sender, conditioned on
  the relay's transmission;
* the **MAC cut** `I(X, X₁; Y)` — information arriving at the receiver from the
  sender–relay pair.

This file provides the structural definitions (`RelayChannel`, `RelayCode`,
`relayCutsetBound`) and the two **single-letterization** lemmas that turn the block
quantities `I(Xⁿ, X₁ⁿ; Yⁿ)` and `I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ)` into per-letter sums under a
memoryless relay channel. Both single-letterizations are instances of the multiple-access
converse machinery: the MAC cut reuses the unconditional per-letter bound and the broadcast
cut reuses the conditional one, with the joint input `(Xᵢ, X₁ᵢ)` and joint output
`(Y₁ᵢ, Yᵢ)` playing the roles of the MAC's joint input/output.

The memoryless structure is a *precondition* (regularity); the per-letter inequality (the
genuine content) is proven, not assumed. The operational outer bound
`relay_cutset_outer_bound` (Fano + data processing + the `min` combination) lives in a
separate file.

## Main statements

* `relay_mac_cut_singleletterize` — `I(Xⁿ, X₁ⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ)`.
* `relay_broadcast_cut_singleletterize` — `I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ) ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ)`.
-/

namespace InformationTheory.Shannon.Relay

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open InformationTheory.Shannon.MAC
open scoped ENNReal NNReal BigOperators

/-- A **relay channel**: Markov kernel from joint input `(α × α₁)` to joint output `(β × β₁)`
(sender input `α`, relay input `α₁`, receiver output `β`, relay observation `β₁`). -/
abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁] [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

/-- A **relay block code** of length `n` with `M` messages: a sender encoder, a causal relay
function (reads past relay observations `β₁`, emits the next relay input `α₁`), and a decoder. -/
structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁] [MeasurableSpace β] [MeasurableSpace β₁] where
  encoder : Fin M → (Fin n → α)
  relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  decoder : (Fin n → β) → Fin M

/-- **Cut-set outer bound (scalar form)**: the minimum of the broadcast-cut rate
`Ib = I(X; Y₁, Y | X₁)` and the MAC-cut rate `Im = I(X, X₁; Y)`. The outer maximisation over
joint input pmfs `p(x, x₁)` is left to callers. -/
noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im

@[simp] lemma relayCutsetBound_def (Ib Im : ℝ) : relayCutsetBound Ib Im = min Ib Im := rfl

section SingleLetterization

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α α₁ β β₁ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
    [MeasurableSpace α₁] [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
    [MeasurableSpace β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {n : ℕ}

omit [DecidableEq α] [DecidableEq α₁] [DecidableEq β] in
/-- **MAC-cut single-letterization**: under a memoryless relay channel (joint input
`(Xᵢ, X₁ᵢ)` to receiver output `Yᵢ`), the block mutual information `I(Xⁿ, X₁ⁿ; Yⁿ)` is bounded
by the per-letter sum `∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ)`. The memoryless structure is a precondition; the
inequality (the genuine content) is proven, not assumed. -/
theorem relay_mac_cut_singleletterize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys) :
    (mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω)).toReal
      ≤ ∑ i : Fin n, (mutualInfo μ (fun ω ↦ (Xs i ω, X₁s i ω)) (Ys i)).toReal := by
  have hJoint : ∀ i, Measurable (fun ω ↦ (Xs i ω, X₁s i ω)) := fun i ↦
    (hXs i).prodMk (hX₁s i)
  have h_per_letter := per_letter_markov_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys hJoint hYs h_memo
  have h_outputs := outputs_cond_indep_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys hJoint hYs h_memo
  exact mutualInfo_le_sum_per_letter_of_memoryless_strong μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys hJoint hYs h_per_letter h_outputs

omit [DecidableEq α] [DecidableEq β] [DecidableEq β₁] in
/-- **Broadcast-cut single-letterization**: the conditional block mutual information
`I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ)` is bounded by the per-letter sum `∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ)`, under the
memoryless relay channel with joint input `(Xᵢ, X₁ᵢ)` and joint output `(Y₁ᵢ, Yᵢ)`. -/
theorem relay_broadcast_cut_singleletterize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i))
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    (h_memo : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω))) :
    (condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ (Y₁s j ω, Ys j ω)) (fun ω j ↦ X₁s j ω)).toReal
      ≤ ∑ i : Fin n,
          (condMutualInfo μ (Xs i) (fun ω ↦ (Y₁s i ω, Ys i ω)) (X₁s i)).toReal := by
  have hJoint : ∀ i, Measurable (fun ω ↦ (Xs i ω, X₁s i ω)) := fun i ↦
    (hXs i).prodMk (hX₁s i)
  have hJointOut : ∀ i, Measurable (fun ω ↦ (Y₁s i ω, Ys i ω)) := fun i ↦
    (hY₁s i).prodMk (hYs i)
  have h_per_letter := per_letter_markov_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω)) hJoint hJointOut h_memo
  have h_outputs := outputs_cond_indep_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω)) hJoint hJointOut h_memo
  exact condMutualInfo_singleletter_le_of_memoryless μ Xs X₁s
    (fun i ω ↦ (Y₁s i ω, Ys i ω)) hXs hX₁s hJointOut h_per_letter h_outputs

end SingleLetterization

end InformationTheory.Shannon.Relay
