import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingConverse
import Common2026.Shannon.Converse
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.CondMutualInfo

/-!
# Channel coding feedback converse — chain-rule 段 (E-10 MVP)

[E-10 ムーンショット plan](../../../docs/shannon/dmc-feedback-capacity-plan.md) の
本体。Cover-Thomas Theorem 7.12 — feedback あり DMC でも capacity は同じ。

## MVP scope (本 file)

Cover-Thomas 7.12 の **chain rule 段** を 0 sorry で publish:

```
log |M| ≤ n · C + h(Pe) + Pe · log(|M| - 1)
```

per-letter inequality (`I(M; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`, memoryless ⇒) は
仮定形 `h_per_letter` に抽出。完全形 (per-letter bound 内部証明) は E-10' deferred。

## 主定理

* `FeedbackCode M n α β`: feedback 符号構造 (`encoder : ∀ i : Fin n, Fin M → (Fin i.val → β) → α`)。
* `mutualInfo_chain_rule_Y_axis_fin`: Y 軸 n 変数 chain rule
  `I(M; Y^n) = ∑ I(M; Y_i | Y^{<i})`。
* `channel_coding_feedback_converse_chain`:
  仮定 `condMutualInfo μ Msg (Ys i) Y^{<i} ≤ mutualInfo μ (Xs i) (Ys i)` で
  `I(M; Y^n) ≤ ∑ I(X_i; Y_i)`。
* `channel_coding_feedback_converse_capacity`:
  各 i で `I(X_i; Y_i) ≤ C` 仮定で `I(M; Y^n) ≤ n • C`。
* `channel_coding_feedback_converse`: Fano + 上記合成、
  `log|M| ≤ n·C + h(Pe) + Pe · log(|M| - 1)`。
-/

namespace InformationTheory.Shannon.ChannelCodingFeedback

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Phase A — `FeedbackCode` 構造 -/

/-- A **feedback code** of length `n` with `M` messages. The encoder at time `i` takes
the message and the **prior outputs** `Y_0, …, Y_{i-1}` to produce the input symbol
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

/-- A **degenerate feedback encoder** is one whose `encoder i` ignores its `(Fin i.val → β)`
input. Equivalently: a standard `Code` (no feedback). The achievability statement
`C_FB ≥ C` is trivially captured by the embedding of `Code` into `FeedbackCode` via
this degenerate construction. -/
def ofCode [MeasurableSpace α] [MeasurableSpace β]
    (c : InformationTheory.Shannon.ChannelCoding.Code M n α β) : FeedbackCode M n α β where
  encoder := fun i m _ => c.encoder m i
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

/-! ## Phase B — Y 軸 n 変数 chain rule -/

section ChainRuleY

variable {M : Type*} [MeasurableSpace M]
  [Nonempty M] [StandardBorelSpace M]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Nonempty β] [StandardBorelSpace β]

/-- **Y-axis n-variable chain rule for mutual information** (本 plan Phase B 主結果).

```
I(Msg; Y_0, …, Y_{n-1}) = ∑ i, I(Msg; Y_i | (Y_0, …, Y_{i-1}))
```

Derived from `mutualInfo_chain_rule_fin` (X-axis form
`I(X_0,…,X_{n-1}; Yo) = ∑ I(X_i; Yo | X^{<i})`) by symmetry: swap left/right with
`mutualInfo_comm` and `condMutualInfo_comm`. -/
theorem mutualInfo_chain_rule_Y_axis_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i)) :
    Shannon.mutualInfo μ Msg (fun ω i => Ys i ω)
      = ∑ i : Fin n,
          Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  -- Step 1: commute MI to put Y on the left.
  have hYpi : Measurable (fun ω (i : Fin n) => Ys i ω) :=
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
      (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr (fun j => hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  exact Shannon.condMutualInfo_comm μ (Ys i) Msg
    (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
    (hYs i) hMsg hPrefix

end ChainRuleY

/-! ## Phase C — chain-rule converse (hypothesis 形) -/

section ChainConverse

variable {M : Type*} [MeasurableSpace M] [Nonempty M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Nonempty β] [StandardBorelSpace β]

/-- **Chain-rule converse (Cover-Thomas 7.12, chain step、hypothesis 形)**:

Assuming the per-letter bound `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` (which, for a
memoryless channel + causal feedback encoder, follows from `Y_i ⊥ (Msg, Y^{<i}) | X_i`),
the total mutual information is bounded by the sum of per-letter mutual informations:

```
I(Msg; Y^n) ≤ ∑ i, I(X_i; Y_i)
```

The per-letter inequality is left as hypothesis — its purely-internal proof is **E-10'
deferred** (judgement log 1).

`@audit:suspect(dmc-feedback-capacity-plan)` -/
theorem channel_coding_feedback_converse_chain
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter : ∀ i : Fin n,
        Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          ≤ Shannon.mutualInfo μ (Xs i) (Ys i)) :
    Shannon.mutualInfo μ Msg (fun ω i => Ys i ω)
      ≤ ∑ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) := by
  rw [mutualInfo_chain_rule_Y_axis_fin μ Msg Ys hMsg hYs]
  exact Finset.sum_le_sum (fun i _ => h_per_letter i)

/-- **Capacity 上界 (Cover-Thomas 7.12 main bound、hypothesis 形)**:
Per-letter bound + per-letter `I(X_i; Y_i) ≤ C` ⇒ `I(Msg; Y^n) ≤ n • C`.

In `ℝ≥0∞` arithmetic the conclusion is `(n : ℕ) • C` — `nsmul` of `ℝ≥0∞`.

`@audit:suspect(dmc-feedback-capacity-plan)` -/
theorem channel_coding_feedback_converse_capacity
    {n : ℕ} (C : ℝ≥0∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter : ∀ i : Fin n,
        Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          ≤ Shannon.mutualInfo μ (Xs i) (Ys i))
    (h_capacity : ∀ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) ≤ C) :
    Shannon.mutualInfo μ Msg (fun ω i => Ys i ω) ≤ n • C := by
  have h_chain := channel_coding_feedback_converse_chain μ Msg Xs Ys
    hMsg hYs h_per_letter
  -- ∑ i, I(X_i; Y_i) ≤ ∑ i, C = n • C
  have h_sum_le : (∑ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i)) ≤
      ∑ _i : Fin n, C := Finset.sum_le_sum (fun i _ => h_capacity i)
  have h_sum_const : (∑ _i : Fin n, C) = n • C := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact h_chain.trans (h_sum_le.trans h_sum_const.le)

end ChainConverse

/-! ## Phase D — Fano 合成 main theorem -/

section MainConverse

variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [MeasurableSpace α]
variable {β : Type*} [Fintype β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Feedback channel coding converse (Cover-Thomas Theorem 7.12)** — chain rule 段
を hypothesis 形に分離した MVP form。

`Msg : Ω → M` を一様分布 (`μ.map Msg = |M|⁻¹ • Measure.count`)、`Xs i ω : α` を時刻 `i`
の入力、`Ys i ω : β` を時刻 `i` の出力、`decoder : (Fin n → β) → M` とする。

Per-letter bound `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)` + 各 i で `I(X_i; Y_i) ≤ C` の
仮定下で、Fano 不等式と組み合わせて:

```
log |M| ≤ n · C.toReal + h(Pe) + Pe · log(|M| - 1)
```

ここで `Pe := μ {Msg ≠ decoder ∘ Y^n}` (`MeasureFano.errorProb`)。

Capacity `C` 自体は `C := sup_p I(p; W)` のような大域定義に縛らず、本定理 signature では
任意の `ℝ≥0∞` 値 `C` を許容。callers が DMC capacity の存在 + 有限性を付与して
具体的な `C` を渡す形。

**注**: 既存 `channel_coding_converse_iid` は Markov chain `Msg → encoder ∘ Msg → Y^n`
仮定下で `I(X^n; Y^n) = n · I(X_0; Y_0)` を経由するが、feedback 下ではこの Markov chain
自体が成立しない (`X_i` が prior `Y` に依存)。本定理は `shannon_converse_single_shot`
(Markov 仮定なしの単発形) を `Yo := Y^n` で呼び、per-letter chain rule で `n·C` を直接
組み立てる。

`@audit:suspect(dmc-feedback-capacity-plan)` -/
theorem channel_coding_feedback_converse
    {n : ℕ} (C : ℝ≥0∞) (hC_finite : C ≠ ∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg)
    (hYs : ∀ i, Measurable (Ys i)) (hdecoder : Measurable decoder)
    (h_per_letter : ∀ i : Fin n,
        Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          ≤ Shannon.mutualInfo μ (Xs i) (Ys i))
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
  -- The Y^n channel output.
  set Yo : Ω → (Fin n → β) := fun ω i => Ys i ω with hYo_def
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
