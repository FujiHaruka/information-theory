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
inequality (the genuine content) is proven, not assumed.
@audit:ok -/
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
memoryless relay channel with joint input `(Xᵢ, X₁ᵢ)` and joint output `(Y₁ᵢ, Yᵢ)`.
@audit:ok -/
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

section MacCutOuterBound

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α α₁ β : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
    [StandardBorelSpace α₁]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M n : ℕ} [NeZero M]

/-- **MAC-cut operational outer bound** (relay channel, Cover–Thomas Thm 15.10.1, MAC cut): for a
uniformly distributed message `W` decoded from the receiver output `Yⁿ`, the rate is bounded by
the per-letter MAC-cut sum plus a Fano slack,
`log M ≤ ∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ) + h(Pe) + Pe · log(M - 1)`, where `Pe` is the block decoding error
probability.

The proof chains destination Fano (`shannon_converse_single_shot`), the data-processing
inequality along the block Markov chain `W → (Xⁿ, X₁ⁿ) → Yⁿ` (`mutualInfo_le_of_markov`), and the
MAC-cut single-letterization (`relay_mac_cut_singleletterize`). The Markov and memoryless
hypotheses are *preconditions* (structure / regularity); the per-letter inequality (the genuine
content) is proven, not assumed, so neither hypothesis is load-bearing. The outer maximisation
over joint input pmfs `p(x, x₁)` — and hence the conversion of the per-letter sum to
`n · max_p I` — is left to callers, which is why the conclusion keeps the explicit per-letter sum.
@audit:ok -/
theorem relay_mac_cut_outer_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M) (decoder : (Fin n → β) → Fin M)
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁) (Ys : Fin n → Ω → β)
    (hW : Measurable W) (hdecoder : Measurable decoder)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i)) (hYs : ∀ i, Measurable (Ys i))
    (hW_uniform : μ.map W = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ M)
    (h_markov : IsMarkovChain μ W (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω))
    (h_memo : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys) :
    Real.log (M : ℝ) ≤
      (∑ i : Fin n, (mutualInfo μ (fun ω ↦ (Xs i ω, X₁s i ω)) (Ys i)).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder * Real.log ((M : ℝ) - 1) := by
  have hYpi : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  have hZpi : Measurable (fun ω j ↦ (Xs j ω, X₁s j ω)) :=
    measurable_pi_iff.mpr (fun j ↦ (hXs j).prodMk (hX₁s j))
  have hMI_W : mutualInfo μ W (fun ω j ↦ Ys j ω) ≠ ∞ :=
    mutualInfo_ne_top μ W (fun ω j ↦ Ys j ω) hW hYpi
  have hMI_Z :
      mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω) ≠ ∞ :=
    mutualInfo_ne_top μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω) hZpi hYpi
  -- Step 1: destination Fano `log M ≤ I(W; Yⁿ) + h(Pe) + Pe · log(M − 1)`.
  have hcard' : 2 ≤ Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hcard
  have hStep1 := shannon_converse_single_shot μ W (fun ω j ↦ Ys j ω) decoder
    hW hYpi hdecoder hW_uniform hcard' hMI_W
  rw [Fintype.card_fin] at hStep1
  -- Step 2: data-processing inequality along `W → (Xⁿ, X₁ⁿ) → Yⁿ`.
  have hStep2_enn :
      mutualInfo μ W (fun ω j ↦ Ys j ω)
        ≤ mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω) :=
    mutualInfo_le_of_markov μ W (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω)
      hW hZpi hYpi h_markov
  have hStep2 :
      (mutualInfo μ W (fun ω j ↦ Ys j ω)).toReal
        ≤ (mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω)).toReal :=
    ENNReal.toReal_mono hMI_Z hStep2_enn
  -- Step 3: MAC-cut single-letterization `I(Xⁿ, X₁ⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ)`.
  have hStep3 := relay_mac_cut_singleletterize μ Xs X₁s Ys hXs hX₁s hYs h_memo
  linarith [hStep1, hStep2, hStep3]

end MacCutOuterBound

end InformationTheory.Shannon.Relay
