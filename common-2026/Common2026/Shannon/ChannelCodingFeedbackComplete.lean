import Common2026.Shannon.ChannelCodingFeedback
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.MutualInfo

/-!
# Feedback channel coding converse — memoryless 完全形 (E-10')

[E-10' ムーンショット plan](../../../docs/shannon/dmc-feedback-per-letter-bound-plan.md)
の本体。親 file `ChannelCodingFeedback.lean` の `channel_coding_feedback_converse` は
per-letter inequality `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` を `h_per_letter` 仮定形に
していたが、本 file はこれを **memoryless 性 + 因果性** から導出して剥がす。

## MVP scope (本 file)

1. `IsMemorylessFeedback` 述語: 各時刻 `i` で Markov chain `(Y^{<i}, Msg) → X_i → Y_i`
   が成り立つ。
2. `feedback_per_letter_bound` (Phase C): 上記述語下で per-letter inequality
   `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` を 0 sorry で publish。
3. `channel_coding_feedback_converse_memoryless` (Phase D): 上を `h_per_letter` に
   流し込んで親 `channel_coding_feedback_converse` の memoryless 完全形に。

## 判断ログ

* **Phase A `IsMemorylessFeedback` の RV 順を `(Y^{<i}, Msg)` 採用**:
  既存 `mutualInfo_chain_rule` (`CondMutualInfo.lean:219`) は左 RV を
  `fun ω => (Zc ω, Xs ω)` 形にする。`Zc := Y^{<i}, Xs := Msg, Yo := Y_i` で
  chain rule 左辺 = `mutualInfo μ (Y^{<i}, Msg) Y_i` = `mutualInfo_le_of_markov` で
  bound する LHS と一致する形を採るため、Phase A の Markov chain 左 RV も
  `(Y^{<i}, Msg)` 順に揃える。plan の Phase A 案 `(Msg, Y^{<i})` 順から変更、Step 3
  swap (`mutualInfo_map_left_measurableEquiv` 経由) を 0 行に削減。

* **Phase B 0 行で完走**:
  既存 `mutualInfo_le_of_markov` + `mutualInfo_chain_rule` + `mutualInfo_nonneg` で
  per-letter bound に必要十分。新規補題 0 行。
-/

namespace InformationTheory.Shannon.ChannelCodingFeedback

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Phase A — memoryless 性の formal 定式化 -/

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

/-! ## Phase C — per-letter bound 本体 -/

section PerLetter

variable {M : Type*} [MeasurableSpace M] [Nonempty M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- **Per-letter bound (E-10' main, Phase C)**.

Under memoryless + causal feedback (`IsMemorylessFeedback`), the per-letter
inequality

```
I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)
```

holds for every `i : Fin n`. This is the **internal proof** of the `h_per_letter`
hypothesis used in `channel_coding_feedback_converse`.

### Strategy (Step 1-3)

Fix `i`. Let `L ω := (Y^{<i} ω, Msg ω)` (the joint of prefix and message).

* **Step 1**: From `IsMemorylessFeedback` we have Markov chain
  `L → X_i → Y_i`. Apply `mutualInfo_le_of_markov`:
  `I(L; Y_i) ≤ I(X_i; Y_i)`.
* **Step 2**: Chain rule `I(L; Y_i) = I(Y^{<i}; Y_i) + I(Msg; Y_i | Y^{<i})`.
* **Step 3**: `mutualInfo_nonneg` gives `I(Y^{<i}; Y_i) ≥ 0`, so
  `I(Msg; Y_i | Y^{<i}) ≤ I(L; Y_i)`. Combine with Step 1. -/
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

/-! ## Phase D — 主定理 `channel_coding_feedback_converse_memoryless` -/

section MainConverse

variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [Fintype β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Feedback channel coding converse — memoryless 完全形 (Cover-Thomas Thm 7.12)**.

Variant of `channel_coding_feedback_converse` with `h_per_letter` replaced by the
**memoryless feedback assumption** `IsMemorylessFeedback`. The per-letter inequality
is derived internally via `feedback_per_letter_bound` (Phase C). -/
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
  have h_per_letter := feedback_per_letter_bound μ Msg Xs Ys hMsg hXs hYs h_memo
  exact channel_coding_feedback_converse C hC_finite μ Msg Xs Ys decoder
    hMsg hYs hdecoder h_per_letter h_capacity hMsg_uniform hcard

end MainConverse

end InformationTheory.Shannon.ChannelCodingFeedback
