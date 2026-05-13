# Channel coding converse — memoryless per-summand bound (D-2') ムーンショット計画 🌙

(D-2' / 親 plan [`channel-coding-converse-general-plan.md`](./channel-coding-converse-general-plan.md) の "後継 deferred"、2026-05-14 起草)

D-2' は親 plan D-2 完了 (chain rule 1 段、`channel_coding_converse_general_chainRule`、148 行) の次の段。Cover-Thomas 7.9 一般入力 converse の "memoryless ⇒ per-summand bound":

```
I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)
```

を **memoryless DMC 性のみ** から導く純粋証明。

## 進捗

- [ ] Phase 0 — Mathlib API inventory 📋
- [ ] Phase A — `IsMemorylessChannel` 述語 📋
- [ ] Phase B — CondMutualInfo.lean 補助補題 2 本 📋
- [ ] Phase C — `memoryless_per_summand_bound` 本体 📋
- [ ] Phase D — 主定理 `channel_coding_converse_general_memoryless` 📋

## ゴール / Approach

**ゴール**:
```
memoryless_per_summand_bound :
  ∀ i : Fin n,
    condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
        (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      ≤ mutualInfo μ (Xs i) (Ys i)
```

### Approach (3 段戦略、E-10' との比較)

**E-10' との比較**: E-10' は LHS = `I(Msg; Y_i | Y^{<i})` (Y 軸単独)、Markov chain 1 段で完走。D-2' は LHS = `I(X_i; Y^n | X^{<i})` (Y 軸 n 変数)、`Y^n = (Y_i, Y^{≠i})` 分割が必要。

**採用経路 (B 案、kernel-form Markov chain over `Y^n`)**:

**Step 1** (Y-axis chain rule conditional on `X^{<i}`):
```
condMutualInfo μ (Xs i) Y^n X^{<i}
  = condMutualInfo μ (Xs i) Y_i X^{<i}
    + condMutualInfo μ (Xs i) Y^{≠i} (X^{<i}, Y_i)
```

**Step 2** (Yother 項 = 0): memoryless から Markov chain `X_i → (X^{<i}, X^{>i}, Y_i) → Y^{≠i}` ⇒ `condMutualInfo (X_i) Y^{≠i} (X^{<i}, Y_i) = 0`。

**Step 3** (Xprefix 項 ≤ bare mutualInfo): Markov chain `X^{<i} → X_i → Y_i` + chain rule + `mutualInfo_le_of_markov` + `nonneg` で `I(X_i; Y_i | X^{<i}) ≤ I(X_i; Y_i)`。

### 規模見積

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | inventory | 0 |
| A | `IsMemorylessChannel` + accessor | 80-120 |
| B | conditional 補題 2 本 | 150-200 |
| C | 本体 | 150-200 |
| D | 主定理 | 50-80 |
| **合計** | | **~430-600 行** |

E-10' (198 行) の 2-3 倍。主因: Y^n n 変数扱い + conditional 補題 2 本。

## Phase 0 — Mathlib API inventory

### 新規 Mathlib API

1. **`MeasurableEquiv.piFinSuccAbove`** — `Y^n = (Y_i, Y^{≠i})` reshape
2. **`MeasurableEquiv.piEquivPiSubtypeProd`** — Subtype index 形での分割
3. **`Measure.pi_pi`** — memoryless product 検証
4. **`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`** — memoryless 形式化の β-form 候補

### 既存 Common2026 補題 (E-10' inventory を再利用)

1. `Shannon.mutualInfo_chain_rule` (`CondMutualInfo.lean:219`)
2. `Shannon.IsMarkovChain` (`CondMutualInfo.lean:71`)
3. `Shannon.mutualInfo_le_of_markov` (`CondMutualInfo.lean:378`)
4. `Shannon.mutualInfo_nonneg` (`MutualInfo.lean:42`)
5. `Shannon.condMutualInfo_eq_zero_of_markov` (`CondMutualInfo.lean:353`)
6. `Shannon.condMutualInfo_comm` (`CondMutualInfo.lean:295`)
7. `Shannon.mutualInfo_map_left_measurableEquiv` / `right` (`MIChainRule.lean:43, 75`)
8. `mutualInfo_chain_rule_Y_axis_fin` (`ChannelCodingFeedback.lean:117`)

### D-2' で新規

1. **`Shannon.IsMemorylessChannel`** (Phase A)
2. **`Shannon.condMutualInfo_le_of_markov`** (Phase B、~80-120 行)
3. **`Shannon.condMutualInfo_chain_rule_Y_axis`** (Phase B、~50-80 行)

## Phase A — `IsMemorylessChannel` 述語

### 採用形

```lean
def IsMemorylessChannel {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop :=
  ∀ i : Fin n,
    Shannon.IsMarkovChain μ
      (fun ω =>
        ((fun (j : {j : Fin n // j ≠ i}) => Xs j ω),
         (fun (j : {j : Fin n // j ≠ i}) => Ys j ω)))
      (Xs i) (Ys i)
```

E-10' `IsMemorylessFeedback` の対称形。kernel `W` への参照なし。

### Phase A — checklist

- [ ] (A.1) def 導入
- [ ] (A.2) per-i `IsMarkovChain` accessor
- [ ] (A.3) StandardBorel/Nonempty plumbing for `{j : Fin n // j ≠ i} → α/β`

## Phase B — CondMutualInfo.lean 補助補題

### 補題 1: `condMutualInfo_le_of_markov`

```lean
theorem condMutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (Wc : Ω → W)
    (hXs : Measurable Xs) (hZc : Measurable Zc)
    (hYo : Measurable Yo) (hWc : Measurable Wc)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    condMutualInfo μ Xs Yo Wc ≤ condMutualInfo μ Zc Yo Wc
```

### 補題 2: `condMutualInfo_chain_rule_Y_axis`

Y-axis n 変数 chain rule の conditional 版。`mutualInfo_chain_rule_Y_axis_fin` を Wc 条件下で。

### Phase B — checklist

- [ ] (B.1) `condMutualInfo_le_of_markov` 追加 (~80-120 行)
- [ ] (B.2) `condMutualInfo_chain_rule_Y_axis` 追加 (~50-80 行)
- [ ] (B.3) (optional) `condMutualInfo_eq_zero_of_markov_cond` (Wc 条件下の Markov、~50 行)

## Phase C — 本体 `memoryless_per_summand_bound`

### 戦略

i を fix、Setup:
- `Xprefix ω := fun j => Xs ⟨j.val, ..⟩ ω`
- `Yfull ω := fun j => Ys j ω`
- `Yi := Ys i`、`Yother ω := fun (j : {k // k ≠ i}) => Ys j ω`

**Step 1**: Y-axis conditional chain rule で 2 項分解
**Step 2**: memoryless から Yother 項 = 0
**Step 3**: E-10' 同型の chain rule + `mutualInfo_le_of_markov` + `nonneg`
**Step 4**: 合成

## Phase D — 主定理 `channel_coding_converse_general_memoryless`

### 戦略

1. `channel_coding_converse_general_chainRule` (D-2 既存) call
2. `memoryless_per_summand_bound` で sum を縮める
3. 合成

## 判断ログ

1. **memoryless 性 formal 化を per-i Markov chain (E-10' 同型) で確定**: kernel-form 候補は `Kernel.pi` Mathlib 不在で却下。
2. **Approach 経路を B 案で確定**: 経路 C (上界分解) は中間ステップ不成立、経路 D (kernel.pi) は Mathlib 不在で却下。
3. **`condMutualInfo_le_of_markov` 新規補題 1 本**: E-10' で不要だった理由は LHS が bare mutualInfo。D-2' は LHS = condMI なので conditional 版が要。
4. **Step 3 で一般 `condMI ≤ MI` 不等式を回避**: 一般には成立しない。代わりに Markov chain `X^{<i} → X_i → Y_i` + chain rule + `mutualInfo_le_of_markov` + nonneg で E-10' Step 2-3 同型。
5. **E-10' 転用範囲**: 既存 10 本流用、新規補題 2 本 + memoryless 述語 1 本。

## 参考

- 親 plan: [`channel-coding-converse-general-plan.md`](./channel-coding-converse-general-plan.md)
- 兄弟 plan (E-10' 完成形): [`dmc-feedback-per-letter-bound-plan.md`](./dmc-feedback-per-letter-bound-plan.md)
- moonshot template: [`docs/moonshot-plan-template.md`](../moonshot-plan-template.md)
