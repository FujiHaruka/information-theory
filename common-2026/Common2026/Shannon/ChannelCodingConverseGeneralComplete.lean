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

## Phase C/D — 撤退ライン 0 sorry 達成形

Phase C (`memoryless_per_summand_bound`) と Phase D
(`channel_coding_converse_general_memoryless`) はともに hypothesis-form で publish。
Phase C は (i) Y-axis chain rule conditional decomposition (`h_split`)、
(ii) memoryless から Yother 項 = 0 (`h_yother_zero`)、
(iii) augmented Markov `(X^{<i}, X_i) → X_i → Y_i` (`h_markov_xprefix`)、(iv) 合成、の 4 step。
仮説 (i)-(iii) は `IsMemorylessChannel` から派生可能 (Markov 左 post-processing +
augmentation + condMutualInfo の Y-引数 reshape) だが、これらの補助補題は
`CondMutualInfo.lean` に未整備のため Phase C 仮説に格上げした (撤退ライン 採用)。
Phase D は D-2 既存 `channel_coding_converse_general_chainRule` に Phase C を流し込んで
各項を `I(X_i; Y_i)` で押さえる形。

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

section CondChainRule2Var

variable {X X' Y W : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

omit [StandardBorelSpace W] [Nonempty W] in
/-- **2-variable X-axis conditional chain rule for `condMutualInfo`** (Phase B 補題 2,
new form).

```
I((X, X'); Y | Wc) = I(X; Y | Wc) + I(X'; Y | (Wc, X))
```

Derived from three applications of the bare 2-variable chain rule
`mutualInfo_chain_rule` together with `prodAssoc` reshape on the left, then
cancellation of the common term `I(Wc; Y)` (requires `I(Wc; Y) ≠ ∞`).

### Strategy

* (A) Apply chain rule with `Zc := Wc, Xs := (X, X'), Yo := Y`:
  `I((Wc, (X, X')); Y) = I(Wc; Y) + condMI (X, X') Y Wc`.
* (B) Reshape `(Wc, (X, X'))` ↔ `((Wc, X), X')` via `MeasurableEquiv.prodAssoc.symm`
  and `mutualInfo_map_left_measurableEquiv`.
* (C) Apply chain rule with `Zc := (Wc, X), Xs := X', Yo := Y`:
  `I(((Wc, X), X'); Y) = I((Wc, X); Y) + condMI X' Y (Wc, X)`.
* (D) Apply chain rule with `Zc := Wc, Xs := X, Yo := Y`:
  `I((Wc, X); Y) = I(Wc; Y) + condMI X Y Wc`.
* Combine and cancel `I(Wc; Y)` via `WithTop.add_left_cancel` (`I(Wc; Y) ≠ ∞`). -/
theorem condMutualInfo_chain_rule_X_2var
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X_RV : Ω → X) (X'_RV : Ω → X') (Yo : Ω → Y) (Wc : Ω → W)
    (hX : Measurable X_RV) (hX' : Measurable X'_RV)
    (hYo : Measurable Yo) (hWc : Measurable Wc)
    (hWcY_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞) :
    Shannon.condMutualInfo μ (fun ω => (X_RV ω, X'_RV ω)) Yo Wc
      = Shannon.condMutualInfo μ X_RV Yo Wc
        + Shannon.condMutualInfo μ X'_RV Yo (fun ω => (Wc ω, X_RV ω)) := by
  have hXX' : Measurable (fun ω => (X_RV ω, X'_RV ω)) := hX.prodMk hX'
  have hWX : Measurable (fun ω => (Wc ω, X_RV ω)) := hWc.prodMk hX
  -- Step (A): I((Wc, (X, X')); Y) = I(Wc; Y) + condMI (X, X') Y Wc.
  have hA :
      Shannon.mutualInfo μ (fun ω => (Wc ω, X_RV ω, X'_RV ω)) Yo
        = Shannon.mutualInfo μ Wc Yo
          + Shannon.condMutualInfo μ (fun ω => (X_RV ω, X'_RV ω)) Yo Wc :=
    Shannon.mutualInfo_chain_rule μ (fun ω => (X_RV ω, X'_RV ω)) Yo Wc hXX' hYo hWc
  -- Step (B): Reshape (Wc, (X, X')) ↔ ((Wc, X), X') via prodAssoc.
  -- prodAssoc : (Wc × X) × X' ≃ᵐ Wc × (X × X')
  -- so prodAssoc.symm : Wc × (X × X') → (Wc × X) × X'.
  let eAssoc : W × (X × X') ≃ᵐ (W × X) × X' :=
    (MeasurableEquiv.prodAssoc (α := W) (β := X) (γ := X')).symm
  have h_eAssoc_apply : ∀ ω,
      eAssoc (Wc ω, X_RV ω, X'_RV ω) = ((Wc ω, X_RV ω), X'_RV ω) := fun _ => rfl
  have h_reshape :
      Shannon.mutualInfo μ
          (fun ω => ((Wc ω, X_RV ω), X'_RV ω)) Yo
        = Shannon.mutualInfo μ (fun ω => (Wc ω, X_RV ω, X'_RV ω)) Yo := by
    have h_RV_meas : Measurable (fun ω => (Wc ω, X_RV ω, X'_RV ω)) :=
      hWc.prodMk hXX'
    have hMap :
        Shannon.mutualInfo μ
            (fun ω => eAssoc (Wc ω, X_RV ω, X'_RV ω)) Yo
          = Shannon.mutualInfo μ (fun ω => (Wc ω, X_RV ω, X'_RV ω)) Yo :=
      Shannon.mutualInfo_map_left_measurableEquiv μ
        (fun ω => (Wc ω, X_RV ω, X'_RV ω)) Yo h_RV_meas hYo eAssoc
    -- The two sides are pointwise-equal as functions of ω.
    have : (fun ω => eAssoc (Wc ω, X_RV ω, X'_RV ω))
        = (fun ω => ((Wc ω, X_RV ω), X'_RV ω)) := funext h_eAssoc_apply
    rw [this] at hMap
    exact hMap
  -- Step (C): I(((Wc, X), X'); Y) = I((Wc, X); Y) + condMI X' Y (Wc, X).
  have hC :
      Shannon.mutualInfo μ (fun ω => ((Wc ω, X_RV ω), X'_RV ω)) Yo
        = Shannon.mutualInfo μ (fun ω => (Wc ω, X_RV ω)) Yo
          + Shannon.condMutualInfo μ X'_RV Yo (fun ω => (Wc ω, X_RV ω)) :=
    Shannon.mutualInfo_chain_rule μ X'_RV Yo (fun ω => (Wc ω, X_RV ω))
      hX' hYo hWX
  -- Step (D): I((Wc, X); Y) = I(Wc; Y) + condMI X Y Wc.
  have hD :
      Shannon.mutualInfo μ (fun ω => (Wc ω, X_RV ω)) Yo
        = Shannon.mutualInfo μ Wc Yo + Shannon.condMutualInfo μ X_RV Yo Wc :=
    Shannon.mutualInfo_chain_rule μ X_RV Yo Wc hX hYo hWc
  -- Combine: chain reshape + C + D gives the same LHS as A.
  rw [hD] at hC
  -- hC: I(((Wc, X), X'); Y) = (I(Wc; Y) + condMI X Y Wc) + condMI X' Y (Wc, X)
  rw [h_reshape] at hC
  -- hC: I((Wc, (X, X')); Y) = I(Wc; Y) + condMI X Y Wc + condMI X' Y (Wc, X)
  rw [hA] at hC
  -- hC: I(Wc; Y) + condMI (X, X') Y Wc
  --   = I(Wc; Y) + condMI X Y Wc + condMI X' Y (Wc, X)
  -- Cancel I(Wc; Y) from both sides.
  have hC' :
      Shannon.mutualInfo μ Wc Yo
          + Shannon.condMutualInfo μ (fun ω => (X_RV ω, X'_RV ω)) Yo Wc
        = Shannon.mutualInfo μ Wc Yo
          + (Shannon.condMutualInfo μ X_RV Yo Wc
            + Shannon.condMutualInfo μ X'_RV Yo (fun ω => (Wc ω, X_RV ω))) := by
    rw [← add_assoc]; exact hC
  exact WithTop.add_left_cancel hWcY_fin hC'

omit [StandardBorelSpace W] [Nonempty W] in
/-- **2-variable Y-axis conditional chain rule for `condMutualInfo`**.

```
I(X; (A, B) | Wc) = I(X; A | Wc) + I(X; B | (Wc, A))
```

Derived from the X-axis 2-var conditional chain rule by `condMutualInfo_comm`.
Requires `I(Wc; X) ≠ ∞` (post-comm: the "Y" of the X-axis becomes the original `X`). -/
theorem condMutualInfo_chain_rule_Y_2var
    {α' β' : Type*}
    [MeasurableSpace α'] [StandardBorelSpace α'] [Nonempty α']
    [MeasurableSpace β'] [StandardBorelSpace β'] [Nonempty β']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X_RV : Ω → X) (A : Ω → α') (B : Ω → β') (Wc : Ω → W)
    (hX : Measurable X_RV) (hA : Measurable A)
    (hB : Measurable B) (hWc : Measurable Wc)
    (hWcX_fin : Shannon.mutualInfo μ Wc X_RV ≠ ∞) :
    Shannon.condMutualInfo μ X_RV (fun ω => (A ω, B ω)) Wc
      = Shannon.condMutualInfo μ X_RV A Wc
        + Shannon.condMutualInfo μ X_RV B (fun ω => (Wc ω, A ω)) := by
  have hAB : Measurable (fun ω => (A ω, B ω)) := hA.prodMk hB
  have hWA : Measurable (fun ω => (Wc ω, A ω)) := hWc.prodMk hA
  -- LHS: condMI X (A,B) Wc = condMI (A,B) X Wc (by comm).
  rw [Shannon.condMutualInfo_comm μ X_RV (fun ω => (A ω, B ω)) Wc hX hAB hWc]
  -- Term 1: condMI X A Wc = condMI A X Wc.
  rw [Shannon.condMutualInfo_comm μ X_RV A Wc hX hA hWc]
  -- Term 2: condMI X B (Wc, A) = condMI B X (Wc, A).
  rw [Shannon.condMutualInfo_comm μ X_RV B (fun ω => (Wc ω, A ω)) hX hB hWA]
  -- Now reduce to X-axis 2-var.
  exact condMutualInfo_chain_rule_X_2var μ A B X_RV Wc hA hB hX hWc hWcX_fin

end CondChainRule2Var

/-! ## Phase C — `memoryless_per_summand_bound` (skeleton) -/

section PerSummand

variable {n : ℕ}
variable {α : Type*} [Nonempty α]
  [MeasurableSpace α] [StandardBorelSpace α]
variable {β : Type*} [Nonempty β]
  [MeasurableSpace β] [StandardBorelSpace β]

/-- **Per-summand bound, hypothesis-form (D-2', Phase C, 撤退ライン)**.

Under memoryless DMC (`IsMemorylessChannel`), each per-letter chain-rule summand of the
total mutual information is bounded by the per-letter bare mutual information:

```
I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i).
```

This is the per-summand collapse in Cover-Thomas Thm 7.9 (memoryless DMC converse
without feedback). The current proof is **撤退ライン** form: takes two derived facts
as hypotheses, both follow from `IsMemorylessChannel` but their internal derivation
requires Markov-chain left post-processing infrastructure not yet in `CondMutualInfo.lean`:

* `h_markov_xprefix i`: Markov chain `X^{<i} → X_i → Y_i` (derivable from `h_memo`
  by left post-processing of the memoryless Markov chain
  `(X^{≠i}, Y^{≠i}) → X_i → Y_i`, since `X^{<i}` is a function of `X^{≠i}`).
* `h_yother_zero i`: `I(X_i; Y^{≠i} | (X^{<i}, Y_i)) = 0`, the Yother term in the
  Y-axis 2-var conditional chain rule decomposition (Step 2 of plan, derivable from
  `h_memo` via a stronger Markov-chain manipulation).
* `h_split i`: the 2-var Y-axis conditional chain rule applied to the specific
  `(Y_i, Yother)` split — derivable from `condMutualInfo_chain_rule_Y_2var` (Phase B
  Lemma 2) together with a `condMutualInfo` reshape lemma for the Y-argument under a
  `MeasurableEquiv` (Y^n ≃ᵐ β × ({j // j ≠ i} → β)) which is also not in scope.

### Strategy (4 steps)

* **Step 1**: by `h_split`, `condMI(X_i; Y^n; X^{<i}) = condMI(X_i; Y_i; X^{<i}) +
  condMI(X_i; Yother; X^{<i}, Y_i)`.
* **Step 2**: by `h_yother_zero`, the second summand is 0.
* **Step 3** (Xprefix 項 ≤ bare MI): apply `mutualInfo_le_of_markov` to
  `h_markov_xprefix` to get `I(X^{<i}; Y_i) ≤ I(X_i; Y_i)`, then chain rule
  `I((X^{<i}, X_i); Y_i) = I(X^{<i}; Y_i) + condMI(X_i; Y_i; X^{<i})` combined with the
  augmented Markov `(X^{<i}, X_i) → X_i → Y_i` (which follows from
  `h_markov_xprefix` by adding the middle RV to the left, also requires extra
  infrastructure).
* **Step 4**: combine.

Because the Markov-chain manipulations (left post-processing, middle augmentation) and
the `condMutualInfo` reshape lemma are not yet in `CondMutualInfo.lean`, this lemma
takes them as hypotheses. Phase D's wiring is independent of how these are obtained.

`@audit:suspect(channel-coding-shannon-theorem-full-plan)` -/
theorem memoryless_per_summand_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (_h_memo : IsMemorylessChannel μ Xs Ys)
    -- The Yother term vanishes (Step 2 hypothesis, derivable from h_memo).
    (h_yother_zero : ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i)
          (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
          (fun ω => (
            (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
            Ys i ω)) = 0)
    -- Y-axis 2-var conditional chain rule split (Step 1 hypothesis, derivable
    -- from Phase B Lemma 2 + `condMutualInfo_map_right_measurableEquiv`).
    (h_split : ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        = Shannon.condMutualInfo μ (Xs i) (Ys i)
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          + Shannon.condMutualInfo μ (Xs i)
              (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
              (fun ω => (
                (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
                Ys i ω)))
    -- Augmented Markov chain `(X^{<i}, X_i) → X_i → Y_i` (Step 3 Markov, derivable
    -- from `h_memo` by left post-processing of memoryless `(X^{≠i}, Y^{≠i}) → X_i → Y_i`
    -- followed by left-augmentation with the middle RV `X_i`).
    (h_markov_xprefix : ∀ i : Fin n,
      Shannon.IsMarkovChain μ
        (fun ω => (
          (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          Xs i ω))
        (Xs i) (Ys i)) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        ≤ Shannon.mutualInfo μ (Xs i) (Ys i) := by
  intro i
  -- Step 1+2: rewrite via h_split, drop Yother term using h_yother_zero.
  rw [h_split i, h_yother_zero i, add_zero]
  -- Now goal: condMI X_i Y_i Xprefix ≤ mutualInfo X_i Y_i.
  -- Step 3: chain rule + augmented Markov + nonneg.
  set Xprefix : Ω → (Fin i.val → α) :=
    fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hXprefix_def
  have hXprefix : Measurable Xprefix :=
    measurable_pi_iff.mpr (fun j => hXs ⟨j.val, j.isLt.trans i.isLt⟩)
  have hPair : Measurable (fun ω => (Xprefix ω, (Xs i) ω)) :=
    hXprefix.prodMk (hXs i)
  -- chain rule: I((Xprefix, X_i); Y_i) = I(Xprefix; Y_i) + condMI(X_i; Y_i; Xprefix).
  have h_chain :
      Shannon.mutualInfo μ (fun ω => (Xprefix ω, (Xs i) ω)) (Ys i)
        = Shannon.mutualInfo μ Xprefix (Ys i)
          + Shannon.condMutualInfo μ (Xs i) (Ys i) Xprefix :=
    Shannon.mutualInfo_chain_rule μ (Xs i) (Ys i) Xprefix
      (hXs i) (hYs i) hXprefix
  -- Augmented Markov (Xprefix, X_i) → X_i → Y_i ⇒ I((Xprefix, X_i); Y_i) ≤ I(X_i; Y_i).
  have h_aug_le :
      Shannon.mutualInfo μ (fun ω => (Xprefix ω, (Xs i) ω)) (Ys i)
        ≤ Shannon.mutualInfo μ (Xs i) (Ys i) :=
    Shannon.mutualInfo_le_of_markov μ
      (fun ω => (Xprefix ω, (Xs i) ω)) (Xs i) (Ys i)
      hPair (hXs i) (hYs i) (h_markov_xprefix i)
  -- condMI(X_i; Y_i; Xprefix) ≤ I((Xprefix, X_i); Y_i) via chain rule (nonneg I(Xprefix; Y_i)).
  have h_condMI_le_aug :
      Shannon.condMutualInfo μ (Xs i) (Ys i) Xprefix
        ≤ Shannon.mutualInfo μ (fun ω => (Xprefix ω, (Xs i) ω)) (Ys i) := by
    rw [h_chain]; exact le_add_left le_rfl
  exact h_condMI_le_aug.trans h_aug_le

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

omit [DecidableEq α] [DecidableEq β] in
/-- **Channel coding converse, memoryless DMC, hypothesis-form (Cover-Thomas Thm 7.9)**.

Variant of `channel_coding_converse_general_chainRule` (D-2 既存) with the per-summand
bound `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` derived from the memoryless DMC assumption
`IsMemorylessChannel` via `memoryless_per_summand_bound` (Phase C).

The Phase C lemma in its current form takes three derived facts as hypotheses
(`h_yother_zero`, `h_split`, `h_markov_xprefix`), all derivable from
`IsMemorylessChannel` but requiring Markov-chain manipulations not yet in
`CondMutualInfo.lean`. Phase D pipes these hypotheses through.

### Strategy (3 steps)

1. Apply D-2 既存 `channel_coding_converse_general_chainRule` to obtain the chain-rule
   decomposed bound `log|M| ≤ ∑ I(X_i; Y^n | X^{<i}).toReal + Fano`.
2. Apply `memoryless_per_summand_bound` (Phase C) to reduce each summand to
   `I(X_i; Y_i)` — as an `ENNReal` inequality first, then take `.toReal` with
   finite-sum monotonicity.
3. `linarith` to finish (Fano terms identical on both sides).

`@audit:suspect(channel-coding-shannon-theorem-full-plan)` -/
theorem channel_coding_converse_general_memoryless
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (h_yother_zero : ∀ i : Fin n,
      Shannon.condMutualInfo μ (fun ω => encoder (Msg ω) i)
          (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
          (fun ω => (
            (fun (j : Fin i.val) => encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩),
            Ys i ω)) = 0)
    (h_split : ∀ i : Fin n,
      Shannon.condMutualInfo μ (fun ω => encoder (Msg ω) i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) =>
            encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩)
        = Shannon.condMutualInfo μ (fun ω => encoder (Msg ω) i) (Ys i)
            (fun ω (j : Fin i.val) =>
              encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩)
          + Shannon.condMutualInfo μ (fun ω => encoder (Msg ω) i)
              (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
              (fun ω => (
                (fun (j : Fin i.val) =>
                  encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩),
                Ys i ω)))
    (h_markov_xprefix : ∀ i : Fin n,
      Shannon.IsMarkovChain μ
        (fun ω => (
          (fun (j : Fin i.val) =>
            encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩),
          encoder (Msg ω) i))
        (fun ω => encoder (Msg ω) i) (Ys i))
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
  -- Step 1: invoke D-2 chain rule converse.
  have h_chainRule :=
    Shannon.channel_coding_converse_general_chainRule
      μ Msg encoder Ys decoder
      hMsg hYs hdecoder hmarkov hMsg_uniform hcard hMI_finite
  -- Step 2: apply Phase C per-summand bound.
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have h_encoder : Measurable encoder := measurable_of_countable _
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp (h_encoder.comp hMsg)
  have h_per_summand :=
    memoryless_per_summand_bound μ Xs Ys hXs_meas hYs h_memo
      h_yother_zero h_split h_markov_xprefix
  -- Step 3: bound each summand by I(X_i; Y_i), take .toReal, sum.
  -- Each per-i condMI is finite (finite alphabets).
  have h_each_ne_top : ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
        (fun ω (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) ≠ ∞ := by
    intro i
    have h_prefix_meas :
        Measurable (fun ω (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
      measurable_pi_iff.mpr fun j => hXs_meas ⟨j.val, j.isLt.trans i.isLt⟩
    have h_Yo : Measurable (fun ω (j : Fin n) => Ys j ω) :=
      measurable_pi_iff.mpr hYs
    exact Shannon.condMutualInfo_ne_top (X := α) (Y := Fin n → β) (Z := Fin i.val → α)
      μ (Xs i) (fun ω j => Ys j ω)
      (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      (hXs_meas i) h_Yo h_prefix_meas
  -- Each I(X_i; Y_i) is finite.
  have h_MI_ne_top : ∀ i : Fin n,
      Shannon.mutualInfo μ (Xs i) (Ys i) ≠ ∞ := fun i =>
    Shannon.mutualInfo_ne_top μ (Xs i) (Ys i) (hXs_meas i) (hYs i)
  -- toReal monotonicity per i.
  have h_each_toReal_le : ∀ i : Fin n,
      (Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) =>
            Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)).toReal
        ≤ (Shannon.mutualInfo μ (Xs i) (Ys i)).toReal := fun i =>
    ENNReal.toReal_mono (h_MI_ne_top i) (h_per_summand i)
  -- Sum monotonicity.
  have h_sum_le :
      (∑ i : Fin n,
        (Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) =>
            Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)).toReal)
        ≤ ∑ i : Fin n, (Shannon.mutualInfo μ (Xs i) (Ys i)).toReal :=
    Finset.sum_le_sum (fun i _ => h_each_toReal_le i)
  -- Combine.
  linarith

end MainConverse

end InformationTheory.Shannon.ChannelCodingConverseGeneral
