import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.Converse
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMutualInfo

/-!
# Channel coding feedback converse — chain-rule form

Cover-Thomas Theorem 7.12: for a DMC with feedback, capacity equals the memoryless
capacity. The per-letter inequality `I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` is left as
a hypothesis `h_per_letter`; its internal proof is in `FeedbackComplete`.

## Main definitions

* `FeedbackCode M n α β`: feedback code structure with causal encoder
  `encoder : ∀ i : Fin n, Fin M → (Fin i.val → β) → α`.

## Main statements

* `mutualInfo_chain_rule_Y_axis_fin`: Y-axis n-variable chain rule
  `I(M; Y^n) = ∑ I(M; Y_i | Y^{<i})`.
* `channel_coding_feedback_converse_chain`: Under the per-letter bound hypothesis,
  `I(M; Y^n) ≤ ∑ I(X_i; Y_i)`.
* `channel_coding_feedback_converse_capacity`: Under `I(X_i; Y_i) ≤ C` for all `i`,
  `I(M; Y^n) ≤ n • C`.
* `channel_coding_feedback_converse`: Combines Fano inequality with the above to give
  `log |M| ≤ n · C + h(Pe) + Pe · log(|M| - 1)`.
-/

namespace InformationTheory.Shannon.ChannelCodingFeedback

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## `FeedbackCode` structure -/

/-- A feedback code of length `n` with `M` messages. The encoder at time `i` takes
the message and the prior outputs `Y_0, …, Y_{i-1}` to produce the input symbol
`X_i ∈ α`. The decoder maps the full output block `Y^n` to a message guess.

`X_i = encoder i m (y_0, …, y_{i-1})` — the causal structure is built into the type
signature: `encoder i : Fin M → (Fin i.val → β) → α` only sees `Fin i.val → β`. -/
structure FeedbackCode (M n : ℕ) (α β : Type*) where
  encoder : (i : Fin n) → Fin M → (Fin i.val → β) → α
  decoder : (Fin n → β) → Fin M

namespace FeedbackCode

variable {M n : ℕ} {α β : Type*}

/-- The decoding region for message `m`. -/
def decodingRegion (c : FeedbackCode M n α β) (m : Fin M) : Set (Fin n → β) :=
  { y | c.decoder y = m }

/-- The error event for message `m`. -/
def errorEvent (c : FeedbackCode M n α β) (m : Fin M) : Set (Fin n → β) :=
  (c.decodingRegion m)ᶜ

/-- A degenerate feedback encoder is one whose `encoder i` ignores its `(Fin i.val → β)`
input. Equivalently: a standard `Code` (no feedback). The achievability statement
`C_FB ≥ C` is trivially captured by the embedding of `Code` into `FeedbackCode` via
this degenerate construction. -/
def ofCode [MeasurableSpace α] [MeasurableSpace β]
    (c : InformationTheory.Shannon.ChannelCoding.Code M n α β) : FeedbackCode M n α β where
  encoder := fun i m _ ↦ c.encoder m i
  decoder := c.decoder

@[simp] lemma ofCode_decoder [MeasurableSpace α] [MeasurableSpace β]
    (c : InformationTheory.Shannon.ChannelCoding.Code M n α β) :
    (ofCode c).decoder = c.decoder := rfl

@[simp] lemma ofCode_encoder [MeasurableSpace α] [MeasurableSpace β]
    (c : InformationTheory.Shannon.ChannelCoding.Code M n α β) (i : Fin n) (m : Fin M)
    (yprev : Fin i.val → β) :
    (ofCode c).encoder i m yprev = c.encoder m i := rfl

@[simp] lemma ofCode_decodingRegion [MeasurableSpace α] [MeasurableSpace β]
    (c : InformationTheory.Shannon.ChannelCoding.Code M n α β) (m : Fin M) :
    (ofCode c).decodingRegion m =
      InformationTheory.Shannon.ChannelCoding.Code.decodingRegion c m := rfl

@[simp] lemma ofCode_errorEvent [MeasurableSpace α] [MeasurableSpace β]
    (c : InformationTheory.Shannon.ChannelCoding.Code M n α β) (m : Fin M) :
    (ofCode c).errorEvent m =
      InformationTheory.Shannon.ChannelCoding.Code.errorEvent c m := rfl

end FeedbackCode

/-! ## Y-axis n-variable chain rule -/

section ChainRuleY

variable {M : Type*} [MeasurableSpace M]
  [Nonempty M] [StandardBorelSpace M]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Nonempty β] [StandardBorelSpace β]

/-- Y-axis n-variable chain rule for mutual information:
`I(Msg; Y_0, …, Y_{n-1}) = ∑ i, I(Msg; Y_i | (Y_0, …, Y_{i-1}))`.

Derived from `mutualInfo_chain_rule_fin` by swapping left/right roles via
`mutualInfo_comm` and `condMutualInfo_comm`. -/
@[entry_point]
theorem mutualInfo_chain_rule_Y_axis_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i)) :
    Shannon.mutualInfo μ Msg (fun ω i ↦ Ys i ω)
      = ∑ i : Fin n,
          Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  -- Step 1: commute MI to put Y on the left.
  have hYpi : Measurable (fun ω (i : Fin n) ↦ Ys i ω) :=
    measurable_pi_iff.mpr hYs
  rw [Shannon.mutualInfo_comm μ Msg _ hMsg hYpi]
  -- Step 2: apply X-axis chain rule with X_i := Ys i.
  rw [Shannon.mutualInfo_chain_rule_fin μ Ys hYs Msg hMsg]
  -- Step 3: each summand: condMutualInfo μ (Ys i) Msg (prefix Ys)
  --   = condMutualInfo μ Msg (Ys i) (prefix Ys)
  apply Finset.sum_congr rfl
  intro i _
  -- Apply condMutualInfo_comm.
  -- Prefix's measurability:
  have hPrefix : Measurable
      (fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr (fun j ↦ hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  exact Shannon.condMutualInfo_comm μ (Ys i) Msg
    (fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
    (hYs i) hMsg hPrefix

end ChainRuleY

/-! ## Chain-rule converse (hypothesis form) -/

section ChainConverse

variable {M : Type*} [MeasurableSpace M] [Nonempty M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Nonempty β] [StandardBorelSpace β]

/-- Chain-rule converse (Cover-Thomas 7.12, chain step, hypothesis form):
under the per-letter bound `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`,
`I(Msg; Y^n) ≤ ∑ i, I(X_i; Y_i)`.

@audit:retract-candidate(superseded-by-memoryless-form) -/
theorem channel_coding_feedback_converse_chain
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter : ∀ i : Fin n,
        Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          ≤ Shannon.mutualInfo μ (Xs i) (Ys i)) :
    Shannon.mutualInfo μ Msg (fun ω i ↦ Ys i ω)
      ≤ ∑ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) := by
  rw [mutualInfo_chain_rule_Y_axis_fin μ Msg Ys hMsg hYs]
  exact Finset.sum_le_sum (fun i _ ↦ h_per_letter i)

/-- Capacity upper bound (Cover-Thomas 7.12, hypothesis form):
per-letter bound + `I(X_i; Y_i) ≤ C` for all `i` implies `I(Msg; Y^n) ≤ n • C`
(where `n • C` is `nsmul` in `ℝ≥0∞`).

@audit:retract-candidate(superseded-by-memoryless-form) -/
theorem channel_coding_feedback_converse_capacity
    {n : ℕ} (C : ℝ≥0∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter : ∀ i : Fin n,
        Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          ≤ Shannon.mutualInfo μ (Xs i) (Ys i))
    (h_capacity : ∀ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) ≤ C) :
    Shannon.mutualInfo μ Msg (fun ω i ↦ Ys i ω) ≤ n • C := by
  have h_chain := channel_coding_feedback_converse_chain μ Msg Xs Ys
    hMsg hYs h_per_letter
  -- ∑ i, I(X_i; Y_i) ≤ ∑ i, C = n • C
  have h_sum_le : (∑ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i)) ≤
      ∑ _i : Fin n, C := Finset.sum_le_sum (fun i _ ↦ h_capacity i)
  have h_sum_const : (∑ _i : Fin n, C) = n • C := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact h_chain.trans (h_sum_le.trans h_sum_const.le)

end ChainConverse

/-! ## Main converse theorem -/

section MainConverse

variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [Fintype β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq M] in
/-- Feedback channel coding converse (Cover-Thomas Theorem 7.12) — hypothesis form.

Under the per-letter bound `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` and `I(X_i; Y_i) ≤ C`
for all `i`, combined with the Fano inequality:

```
log |M| ≤ n · C.toReal + h(Pe) + Pe · log(|M| - 1)
```

where `Pe := μ {Msg ≠ decoder ∘ Y^n}`. The capacity `C` is an arbitrary `ℝ≥0∞` value;
callers supply the DMC capacity bound. Unlike `channel_coding_converse_iid`, no
Markov chain on `Msg → encoder ∘ Msg → Y^n` is required (feedback breaks it).

@audit:retract-candidate(superseded-by-memoryless-form) -/
@[entry_point]
theorem channel_coding_feedback_converse
    {n : ℕ} (C : ℝ≥0∞) (hC_finite : C ≠ ∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg)
    (hYs : ∀ i, Measurable (Ys i)) (hdecoder : Measurable decoder)
    (h_per_letter : ∀ i : Fin n,
        Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          ≤ Shannon.mutualInfo μ (Xs i) (Ys i))
    (h_capacity : ∀ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) ≤ C)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M) :
    Real.log (Fintype.card M) ≤
      (n : ℝ) * C.toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i ↦ Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i ↦ Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  -- The Y^n channel output.
  set Yo : Ω → (Fin n → β) := fun ω i ↦ Ys i ω with hYo_def
  have hYo : Measurable Yo := measurable_pi_iff.mpr hYs
  -- The capacity bound on I(Msg; Y^n).
  have h_capacity_bound :
      Shannon.mutualInfo μ Msg Yo ≤ n • C :=
    channel_coding_feedback_converse_capacity C μ Msg Xs Ys
      hMsg hYs h_per_letter h_capacity
  -- n • C = ↑n * C in ℝ≥0∞, and C is finite.
  have h_nsmul_eq : (n • C : ℝ≥0∞) = (n : ℝ≥0∞) * C := nsmul_eq_mul n C
  have h_nsmul_finite : (n • C : ℝ≥0∞) ≠ ∞ := by
    rw [h_nsmul_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hC_finite
  have hMI_finite : Shannon.mutualInfo μ Msg Yo ≠ ∞ :=
    ne_top_of_le_ne_top h_nsmul_finite h_capacity_bound
  -- Apply single-shot Shannon converse (Markov chain hypothesis not needed).
  have h_single :=
    Shannon.shannon_converse_single_shot (Y := Fin n → β)
      μ Msg Yo decoder hMsg hYo hdecoder hMsg_uniform hcard hMI_finite
  -- Need: (Shannon.mutualInfo μ Msg Yo).toReal ≤ n * C.toReal
  have h_toReal_le :
      (Shannon.mutualInfo μ Msg Yo).toReal ≤ (n : ℝ) * C.toReal := by
    have h := ENNReal.toReal_mono h_nsmul_finite h_capacity_bound
    rw [h_nsmul_eq, ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
    exact h
  -- Chain bounds.
  linarith

end MainConverse

end InformationTheory.Shannon.ChannelCodingFeedback
