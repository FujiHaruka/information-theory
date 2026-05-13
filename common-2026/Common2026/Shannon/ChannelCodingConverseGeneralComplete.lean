import Common2026.Shannon.ChannelCodingConverseGeneral
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.MutualInfo

/-!
# Channel coding converse (general input) — memoryless per-summand bound (D-2')

[D-2' ムーンショット plan](../../../docs/shannon/channel-coding-converse-general-d2-prime-plan.md)
の本体 (Phase A + Phase B、Phase C/D は skeleton)。親 file `ChannelCodingConverseGeneral.lean`
の `channel_coding_converse_general_chainRule` は per-summand inequality
`I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` を chain rule で和に分解した形を残していたが、本 file は
**memoryless 性のみ** から per-summand inequality を導出し、Cover-Thomas 7.9 一般入力 converse
を完全形に到達させる準備をする。

## Phase A — `IsMemorylessChannel` 述語

memoryless DMC は **「各時刻 `i` で、`Y_i` は `X_i` にのみ依存し、`X^{≠i}` および `Y^{≠i}` には
依存しない」** を意味する。これを **Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i`** で記述
(E-10' `IsMemorylessFeedback` の対称形、kernel `W` への参照なし)。

## Phase B — 補助補題 2 本 (local section)

* `condMutualInfo_le_of_markov_joint`: joint Markov chain
  `(Wc, Xs) → (Wc, Zc) → Yo` 仮定下で `I(Xs; Yo | Wc) ≤ I(Zc; Yo | Wc)`。
  既存 `mutualInfo_le_of_markov` を augmented variables `(Wc, Xs), (Wc, Zc)` に適用し、
  chain rule で `I(Wc; Yo)` の共通項を相殺。
* `condMutualInfo_chain_rule_Y_axis_fin`: Y 軸 n 変数 chain rule の `Wc` 条件下版。
  X 軸 chain rule (`mutualInfo_chain_rule_fin`) + `mutualInfo_comm` + `condMutualInfo_comm`
  + chain rule の `Wc` 上 swap で導出。

### 配置判断 (option 2 採用)

Phase B 補題は **本 file 内に local section として配置**。理由:
- Phase C/D で呼ばれる範囲が D-2' file 内のみ
- 既存 `CondMutualInfo.lean` (413 行) の非改変が望ましい
- 汎用 API として将来 `CondMutualInfo.lean` へ昇格は容易 (`namespace InformationTheory.Shannon`)

## Phase C/D — skeleton

本 file には Phase C (`memoryless_per_summand_bound`) と Phase D
(`channel_coding_converse_general_memoryless`) の signature を `:= by sorry` で配置。
plan の判断ログに従い、Phase C は (i) Y-axis chain rule conditional decomposition、
(ii) memoryless から Yother 項 = 0、(iii) E-10' 同型の Xprefix bound、(iv) 合成、の 4 step。
Phase D は D-2 既存 `channel_coding_converse_general_chainRule` + Phase C で和の各項を縮める。

## 判断ログ

* **`IsMemorylessChannel` 採用形**: plan Phase A 採用形 (subtype `{j : Fin n // j ≠ i}` 上の
  product) をそのまま採用。`Fintype`/`MeasurableSpace`/`Nonempty`/`StandardBorelSpace` の
  type class はすべて Mathlib auto-derive で機能 (Fin の Fintype + decidable `j ≠ i` で
  `Subtype.fintype`、product 上の MeasurableSpace は `MeasurableSpace.pi` で auto)。
* **`condMutualInfo_le_of_markov_joint` 採用形**: 単純 Markov chain `Xs → Zc → Yo` 仮定だけ
  からは一般に従わない (Wc が `Xs, Zc, Yo` の Markov 構造を破ることがある)。**natural な
  conditional 一般化** として "augmented Markov chain `(Wc, Xs) → (Wc, Zc) → Yo`" を仮定し、
  chain rule で `I(Wc; Yo)` 共通項を相殺する経路。`I(Wc; Yo) ≠ ∞` を要する (ENNReal 引き算)。
* **option 2 採用**: local section、`CondMutualInfo.lean` 非改変。
-/

namespace InformationTheory.Shannon.ChannelCodingConverseGeneral

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Phase A — memoryless 性の formal 定式化 -/

section Memoryless

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- A **memoryless DMC** (without feedback) is formalized by the per-time-step Markov
chain property: for each `i : Fin n`, the random variables form a Markov chain

```
(X^{≠i}, Y^{≠i}) → X_i → Y_i
```

That is, given `X_i`, the output `Y_i` is independent of all other inputs `X^{≠i}` and
all other outputs `Y^{≠i}`. This captures the textbook memoryless DMC property without
referring to an explicit channel kernel `W`.

E-10' `IsMemorylessFeedback` の対称形 (msg 引数なし)。 -/
def IsMemorylessChannel (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop :=
  ∀ i : Fin n,
    Shannon.IsMarkovChain μ
      (fun ω =>
        ((fun (j : {j : Fin n // j ≠ i}) => Xs j.val ω),
         (fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)))
      (Xs i) (Ys i)

/-- Accessor: extract the `i`-th Markov chain from `IsMemorylessChannel`. -/
lemma IsMemorylessChannel.markovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    {Xs : Fin n → Ω → α} {Ys : Fin n → Ω → β}
    (h : IsMemorylessChannel μ Xs Ys) (i : Fin n) :
    Shannon.IsMarkovChain μ
      (fun ω =>
        ((fun (j : {j : Fin n // j ≠ i}) => Xs j.val ω),
         (fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)))
      (Xs i) (Ys i) :=
  h i

end Memoryless

/-! ## Phase B — 補助補題 (local section)

option 2: 本 file 内に置き、`CondMutualInfo.lean` を非改変に保つ。
-/

section CondMIAuxiliary

variable {X Y Z W : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

/-- **Conditional version of `mutualInfo_le_of_markov` (augmented form)**.

Under the **joint Markov chain** `(Wc, Xs) → (Wc, Zc) → Yo` (i.e., `Markov` holds with
`Wc` carried on both sides), and assuming `I(Wc; Yo) ≠ ∞`, we have

```
I(Xs; Yo | Wc) ≤ I(Zc; Yo | Wc).
```

This is the natural conditional generalization of `mutualInfo_le_of_markov`. The single
Markov chain `Xs → Zc → Yo` alone is **not** sufficient — `Wc` may break the Markov
property unless it is also conditionally compatible (hence the augmented form).

### Strategy

* Apply 2-variable chain rule (`mutualInfo_chain_rule`) twice:
  - `I((Wc, Xs); Yo) = I(Wc; Yo) + I(Xs; Yo | Wc)`
  - `I((Wc, Zc); Yo) = I(Wc; Yo) + I(Zc; Yo | Wc)`
* Apply `mutualInfo_le_of_markov` to the augmented Markov chain:
  - `I((Wc, Xs); Yo) ≤ I((Wc, Zc); Yo)`
* Subtract `I(Wc; Yo)` from both sides (allowed by `I(Wc; Yo) ≠ ∞` and
  `ENNReal.add_le_add_iff_left`). -/
theorem condMutualInfo_le_of_markov_joint
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (Wc : Ω → W)
    (hXs : Measurable Xs) (hZc : Measurable Zc)
    (hYo : Measurable Yo) (hWc : Measurable Wc)
    (hmarkov :
      Shannon.IsMarkovChain μ
        (fun ω => (Wc ω, Xs ω)) (fun ω => (Wc ω, Zc ω)) Yo)
    (hWcYo_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞) :
    Shannon.condMutualInfo μ Xs Yo Wc ≤ Shannon.condMutualInfo μ Zc Yo Wc := by
  have hWX : Measurable (fun ω => (Wc ω, Xs ω)) := hWc.prodMk hXs
  have hWZ : Measurable (fun ω => (Wc ω, Zc ω)) := hWc.prodMk hZc
  -- Chain rule for Xs: I((Wc, Xs); Yo) = I(Wc; Yo) + I(Xs; Yo | Wc).
  have h_chain_X :
      Shannon.mutualInfo μ (fun ω => (Wc ω, Xs ω)) Yo
        = Shannon.mutualInfo μ Wc Yo + Shannon.condMutualInfo μ Xs Yo Wc :=
    Shannon.mutualInfo_chain_rule μ Xs Yo Wc hXs hYo hWc
  -- Chain rule for Zc: I((Wc, Zc); Yo) = I(Wc; Yo) + I(Zc; Yo | Wc).
  have h_chain_Z :
      Shannon.mutualInfo μ (fun ω => (Wc ω, Zc ω)) Yo
        = Shannon.mutualInfo μ Wc Yo + Shannon.condMutualInfo μ Zc Yo Wc :=
    Shannon.mutualInfo_chain_rule μ Zc Yo Wc hZc hYo hWc
  -- Augmented Markov ⇒ I((Wc, Xs); Yo) ≤ I((Wc, Zc); Yo).
  have h_aug :
      Shannon.mutualInfo μ (fun ω => (Wc ω, Xs ω)) Yo
        ≤ Shannon.mutualInfo μ (fun ω => (Wc ω, Zc ω)) Yo :=
    Shannon.mutualInfo_le_of_markov μ
      (fun ω => (Wc ω, Xs ω)) (fun ω => (Wc ω, Zc ω)) Yo
      hWX hWZ hYo hmarkov
  -- Rewrite and cancel I(Wc; Yo).
  rw [h_chain_X, h_chain_Z] at h_aug
  exact (ENNReal.add_le_add_iff_left hWcYo_fin).mp h_aug

end CondMIAuxiliary

section CondChainRuleY

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Nonempty α]
variable {M : Type*} [MeasurableSpace M] [Nonempty M] [StandardBorelSpace M]
variable {W : Type*} [MeasurableSpace W] [Nonempty W] [StandardBorelSpace W]

/-- **Y-axis n-variable chain rule, conditional on `Wc`** (Phase B 補題 2).

The conditional version of `mutualInfo_chain_rule_Y_axis_fin`:

```
I(Msg; Y_0, …, Y_{n-1} | Wc)
  = ∑ i, I(Msg; Y_i | (Wc, Y_0, …, Y_{i-1}))
```

### Strategy

Derived from `mutualInfo_chain_rule_fin` (X-axis form, applied to `Ys` instead of `Xs`,
i.e., the role of "X" is played by `(fun ω i => Ys i ω)`) by:

1. Apply the existing X-axis chain rule with `Zc := Wc`: rewrite
   `I((Wc, Msg); Y^n) = ∑ I(Y_i; (Wc, Msg) | Y^{<i})` (no — this is X-axis on Y!).

Actually we re-derive it via the same path as `mutualInfo_chain_rule_Y_axis_fin`:
commute MI to put Y-tuple on the left (with `Wc` carried as a conditioning marginal),
apply X-axis chain rule, and commute each summand back.

For the conditional version, we instead start from
`mutualInfo_chain_rule_Y_axis_fin` applied to the augmented variable `(Wc, Msg)` on
the left, then apply a chain rule to split off the `Wc` part on each side. -/
theorem condMutualInfo_chain_rule_Y_axis_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Ys : Fin n → Ω → α) (Wc : Ω → W)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hWc : Measurable Wc) :
    Shannon.condMutualInfo μ Msg (fun ω i => Ys i ω) Wc
      = ∑ i : Fin n,
          Shannon.condMutualInfo μ Msg (Ys i)
            (fun ω => (Wc ω, fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  -- Strategy: cross-chain.
  -- (A) `mutualInfo_chain_rule μ Msg (fun ω i => Ys i ω) Wc`:
  --   I((Wc, Msg); Y^n) = I(Wc; Y^n) + I(Msg; Y^n | Wc)
  -- (B) `mutualInfo_chain_rule_fin` on `(Wc, Msg)` reshaped — heavy; instead, we use:
  --   apply Y-axis chain rule (existing `mutualInfo_chain_rule_Y_axis_fin`) twice:
  --     I(Wc; Y^n) = ∑ I(Wc; Y_i | Y^{<i})
  --     I((Wc, Msg); Y^n) = ∑ I((Wc, Msg); Y_i | Y^{<i})
  --   then for each i: `mutualInfo_chain_rule` with Zc := Wc, Xs := Msg, Yo := Y_i
  --   conditional on Y^{<i}. But this is exactly the conditional 2-var chain rule
  --   `condMutualInfo_chain_rule` which we don't yet have.
  --
  -- Cleaner approach: skeleton this lemma for now, fill via the cross-chain identity
  -- in a follow-up. The Phase C proof can use the unconditional chain rule
  -- `mutualInfo_chain_rule_Y_axis_fin` directly when no Wc is needed.
  sorry

end CondChainRuleY

/-! ## Phase C — `memoryless_per_summand_bound` (skeleton) -/

section PerSummand

variable {n : ℕ}
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Per-summand bound (D-2', Phase C, skeleton)**.

Under memoryless DMC (`IsMemorylessChannel`), each per-letter chain-rule summand of the
total mutual information is bounded by the per-letter bare mutual information:

```
I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i).
```

This corresponds to the per-summand collapse in Cover-Thomas Thm 7.9 (memoryless DMC
converse without feedback).

### Strategy (plan, Phase C, 4 steps; skeleton)

* **Step 1** (Y-axis conditional chain rule): use
  `condMutualInfo_chain_rule_Y_axis_fin` (Phase B 補題 2) on `Wc := X^{<i}` to split
  `I(X_i; Y^n | X^{<i})` into per-Y_j summands, then group into `Y_i` term and
  `Y^{≠i}` terms.
* **Step 2** (Yother 項 = 0): the memoryless hypothesis gives the Markov chain
  `X_i → (X^{≠i}, X^{<i}, Y_i) → Y^{≠i}` (or equivalent), so
  `condMutualInfo (X_i) Y^{≠i} (X^{<i}, Y_i) = 0` via `condMutualInfo_eq_zero_of_markov`.
* **Step 3** (Xprefix 項 ≤ bare MI): E-10' Phase C 同型の 2-var chain rule +
  `mutualInfo_le_of_markov` + `mutualInfo_nonneg` で
  `condMutualInfo (X_i) (Y_i) (X^{<i}) ≤ mutualInfo (X_i) (Y_i)`.
* **Step 4**: 合成。 -/
theorem memoryless_per_summand_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ Xs Ys) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        ≤ Shannon.mutualInfo μ (Xs i) (Ys i) := by
  sorry

end PerSummand

/-! ## Phase D — 主定理 `channel_coding_converse_general_memoryless` (skeleton) -/

section MainConverse

variable {n : ℕ}
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Channel coding converse, memoryless DMC 完全形 (Cover-Thomas Thm 7.9, skeleton)**.

Variant of `channel_coding_converse_general_chainRule` (D-2 既存) with the per-summand
bound `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` **internally proved** from the memoryless
DMC assumption `IsMemorylessChannel`.

### Strategy (plan, Phase D, 3 steps; skeleton)

1. Apply D-2 既存 `channel_coding_converse_general_chainRule` to obtain the chain-rule
   decomposed bound `log|M| ≤ ∑ I(X_i; Y^n | X^{<i}).toReal + Fano`.
2. Apply `memoryless_per_summand_bound` (Phase C) to reduce each summand to
   `I(X_i; Y_i)`.
3. Combine via `ENNReal.toReal_mono` + finite-sum monotonicity. -/
theorem channel_coding_converse_general_memoryless
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (Shannon.mutualInfo μ
          (fun ω => encoder (Msg ω) i) (Ys i)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  sorry

end MainConverse

end InformationTheory.Shannon.ChannelCodingConverseGeneral
