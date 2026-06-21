import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Feedback
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.MutualInfo

/-!
# Feedback channel coding converse — memoryless complete form

## Main definitions

* `IsMemorylessFeedback`: Per-time-step Markov chain property formalizing a memoryless
  DMC with causal feedback encoder.

## Main statements

* `feedback_per_letter_bound`: Under `IsMemorylessFeedback`, the per-letter inequality
  `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` holds for all `i`.
* `channel_coding_feedback_converse_memoryless`: Variant of `channel_coding_feedback_converse`
  with `h_per_letter` replaced by `IsMemorylessFeedback`.

## Implementation notes

The left RV in `IsMemorylessFeedback` is `(Y^{<i}, Msg)` (prefix first, message second),
aligning with the chain rule shape `mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo`. This
avoids a swap step via `mutualInfo_map_left_measurableEquiv`.
-/

namespace InformationTheory.Shannon.ChannelCodingFeedback

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Memoryless feedback formalization -/

section Memoryless

variable {M : Type*} [MeasurableSpace M] [Nonempty M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Nonempty β] [StandardBorelSpace β]

/-- A memoryless DMC + causal feedback encoder is formalized by the per-time-step
Markov chain property: for each `i : Fin n`, the random variables form a Markov chain

```
(Y^{<i}, Msg) → X_i → Y_i
```

That is, given `X_i`, the output `Y_i` is independent of `(Y^{<i}, Msg)` — which captures
both **memorylessness** (`Y_i` doesn't depend on `Y^{<i}`) and **causality** (`Y_i`
doesn't depend on `Msg` once `X_i` is given).

The left RV is `(Y^{<i}, Msg)` (prefix first, message second), aligning with the chain
rule shape `mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo`. -/
def IsMemorylessFeedback {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop :=
  ∀ i : Fin n,
    Shannon.IsMarkovChain μ
      (fun ω => (fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω, Msg ω))
      (Xs i) (Ys i)

omit [Nonempty α] [StandardBorelSpace α] [Fintype β] [MeasurableSingletonClass β] in
/-- Accessor: extract the `i`-th Markov chain from `IsMemorylessFeedback`. -/
lemma IsMemorylessFeedback.markovChain {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {Msg : Ω → M} {Xs : Fin n → Ω → α} {Ys : Fin n → Ω → β}
    (h : IsMemorylessFeedback μ Msg Xs Ys) (i : Fin n) :
    Shannon.IsMarkovChain μ
      (fun ω => (fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω, Msg ω))
      (Xs i) (Ys i) :=
  h i

end Memoryless

/-! ## Per-letter bound -/

section PerLetter

variable {M : Type*} [MeasurableSpace M] [Nonempty M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- **Per-letter bound**: under `IsMemorylessFeedback`,
`I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` for every `i : Fin n`. -/
theorem feedback_per_letter_bound
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessFeedback μ Msg Xs Ys) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ Msg (Ys i)
          (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        ≤ Shannon.mutualInfo μ (Xs i) (Ys i) := by
  intro i
  -- Prefix of outputs Y^{<i}.
  set Yprev : Ω → (Fin i.val → β) :=
    fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω with hYprev_def
  have hYprev : Measurable Yprev :=
    measurable_pi_iff.mpr (fun j => hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  -- Joint of prefix and message.
  set L : Ω → (Fin i.val → β) × M := fun ω => (Yprev ω, Msg ω) with hL_def
  have hL : Measurable L := hYprev.prodMk hMsg
  -- Step 1: Markov chain L → X_i → Y_i ⇒ I(L; Y_i) ≤ I(X_i; Y_i).
  have h_markov : Shannon.IsMarkovChain μ L (Xs i) (Ys i) := h_memo.markovChain μ i
  have h_step1 : Shannon.mutualInfo μ L (Ys i) ≤ Shannon.mutualInfo μ (Xs i) (Ys i) :=
    Shannon.mutualInfo_le_of_markov μ L (Xs i) (Ys i) hL (hXs i) (hYs i) h_markov
  -- Step 2: chain rule: I(L; Y_i) = I(Y^{<i}; Y_i) + I(Msg; Y_i | Y^{<i}).
  -- mutualInfo_chain_rule signature: I((Zc, Xs); Yo) = I(Zc; Yo) + I(Xs; Yo | Zc)
  -- with Zc := Yprev, Xs := Msg, Yo := Ys i, the LHS is exactly mutualInfo μ L (Ys i).
  have h_chain :
      Shannon.mutualInfo μ L (Ys i)
        = Shannon.mutualInfo μ Yprev (Ys i)
          + Shannon.condMutualInfo μ Msg (Ys i) Yprev :=
    Shannon.mutualInfo_chain_rule μ Msg (Ys i) Yprev hMsg (hYs i) hYprev
  -- Step 3: I(Y^{<i}; Y_i) ≥ 0, so condMI ≤ I(L; Y_i).
  have h_step3 :
      Shannon.condMutualInfo μ Msg (Ys i) Yprev ≤ Shannon.mutualInfo μ L (Ys i) := by
    rw [h_chain]
    exact le_add_left le_rfl
  exact h_step3.trans h_step1

end PerLetter

/-! ## Main converse theorem -/

section MainConverse

variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [Fintype β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq M] in
/-- **Feedback channel coding converse, memoryless form (Cover-Thomas Thm. 7.12)**.

Variant of `channel_coding_feedback_converse` with `h_per_letter` replaced by
`IsMemorylessFeedback`. The per-letter inequality is discharged internally via
`feedback_per_letter_bound`. -/
@[entry_point]
theorem channel_coding_feedback_converse_memoryless
    {n : ℕ} (C : ℝ≥0∞) (hC_finite : C ≠ ∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (h_memo : IsMemorylessFeedback μ Msg Xs Ys)
    (h_capacity : ∀ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) ≤ C)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M) :
    Real.log (Fintype.card M) ≤
      (n : ℝ) * C.toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  have h_per_letter := feedback_per_letter_bound μ Msg Xs Ys hMsg hXs hYs h_memo
  exact channel_coding_feedback_converse C hC_finite μ Msg Xs Ys decoder
    hMsg hYs hdecoder h_per_letter h_capacity hMsg_uniform hcard

end MainConverse

end InformationTheory.Shannon.ChannelCodingFeedback
