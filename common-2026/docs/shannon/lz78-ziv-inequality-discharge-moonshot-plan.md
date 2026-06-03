# T4-A LZ78 L-LZ1 Ziv's inequality 部分 discharge ムーンショット計画 🌙

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「撤退ライン L-LZ1 (Ziv's inequality)」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」 (Ch.13)
>
> **Inventory**: 親 plan + `lz78-mathlib-inventory.md` の §1.1 / §4.2 を再利用、本 plan では新規 inventory なし
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `InformationTheory/Shannon/LempelZiv78.lean` (548 行, publish 済 2026-05-19) — `LZ78Phrase`, `LZ78Parsing`, `LZ78Parsing.count`, `IsZivInequalityPassthrough` predicate
> - Mathlib `List.length`, `Finset.card_image_le`, `Finset.card_le_univ`, `Fintype.card`
>
> **Pattern 雛形**:
> - `InformationTheory/Shannon/WynerZivDischarge.lean` (T3-D L-WZ3 部分 discharge; 「最も取りやすい fragments を抽出」pattern の直接の雛形)
> - `InformationTheory/Shannon/CramerLC2Discharge.lean` (T1-C 部分 discharge pattern)
>
> **Goal (短形)**: 新規 1 ファイル `InformationTheory/Shannon/LZ78ZivInequality.lean` で
> Cover-Thomas Lemma 13.5.5 (Ziv's inequality) の **combinatorial counting plumbing**
> 部分を **0 sorry / 0 warning** で publish。**~300-600 行**、partial discharge
> ラインは **L-LZ1-A (counting bound)** を確定発動。
>
> **撤退ライン (本 plan)**:
> [L-LZ1-A 採用]: `LZ78Parsing.count` の組み合わせ的 upper bound を Nat レベルで 0 sorry discharge —
> 具体的に `count_le_card_pow` (distinct phrases の数は `|α| * (count + 1)` で上界)、
> `count_image_le` (`Finset.image` 経由の card bound) 等を publish。
> [L-LZ1-B 採用]: `ZivCountingBound` predicate (real-valued、後続 discharge が
> 直接 plug できる shape) を Prop-level に publish。`IsZivInequalityPassthrough`
> への bridge constructor で組み立て。
> [L-LZ1-C 撤退]: entropy chain rule 経由の `H(X^n) ≤ Σ H(phrase_i)` 形は
> 本 file scope 外 (別 discharge plan)。

## Status (2026-05-20)

> 実態整合 (2026-05-20): DONE-HONEST-HYPS (partial counting layer) かつ headline passthrough は依然 FLAW-VACUOUS — file `InformationTheory/Shannon/LZ78ZivInequality.lean` (0 sorry) は **genuine な組み合わせ counting 補題** を publish 済: `LZ78Parsing.card_phraseSet_le_count` `:161`、`card_phraseSet_le_pow` `:204`、`card_phraseSet_le_succ_mul_card` `:236`、real-valued predicate `ZivCountingBound` `:280` + 派生補題。ただし bridge `IsZivInequalityPassthrough.ofZivCountingBound` (`:325`) の body は **`True.intro`** で、親 `IsZivInequalityPassthrough` は `lz78-moonshot-plan.md` で依然 `Prop := True` のまま — Ziv's inequality 本体は **discharge されていない** (plan の L-LZ1-A/B scope 通り、L-LZ1-C は撤退)。counting plumbing は実体あり、passthrough discharge は未達。

**Phase 0 起草中**。親 plan `lz78-moonshot-plan.md` が完了 (LZ78.lean publish 済 2026-05-19)、本 plan は その直接の **部分 discharge** 後続。`IsZivInequalityPassthrough` の `True` placeholder を **完全置換しない**: combinatorial counting plumbing 部分のみを **新規の `ZivCountingBound` predicate** で publish + `.trivial`-type 構築可能 lemma で `IsZivInequalityPassthrough` への bridge を提供。

## 進捗

- [ ] Phase 0 — Plan + 雛形 alignment 確定 📋
- [ ] Phase A — `LZ78ZivInequality.lean` skeleton + imports 📋
- [ ] Phase B — `LZ78Parsing.count` combinatorial bounds (L-LZ1-A) 📋
- [ ] Phase C — `ZivCountingBound` real-valued predicate (L-LZ1-B) 📋
- [ ] Phase D — `IsZivInequalityPassthrough` への bridge constructor 📋
- [ ] Phase V — `InformationTheory.lean` 編入 + clean check 📋

## ゴール / Approach

### 最終到達点 (Phase D 完成形)

新規 1 ファイル `InformationTheory/Shannon/LZ78ZivInequality.lean` の主合流:

```lean
namespace InformationTheory.Shannon

/-- **Combinatorial bound on the LZ78 phrase count (L-LZ1-A)**.

For any `LZ78Parsing`, the number of phrases is bounded by the list length. -/
theorem LZ78Parsing.count_eq_length (p : LZ78Parsing α) :
    p.count = p.phrases.length := rfl

/-- **Cardinality of the dictionary phrase space (L-LZ1-A)**.

The number of distinct `LZ78Phrase α` that can appear in the first `c`
phrases of any parsing is at most `|α| * (c + 1)`: each phrase = (parent
∈ {none, some 0, ..., some (c-1)}) × (symbol ∈ α). -/
theorem LZ78Phrase.card_image_bound
    [Fintype α] (c : ℕ) (phrases : Fin c → LZ78Phrase α) :
    (Finset.univ.image phrases).card ≤ Fintype.card α * (c + 1) := ...

/-- **Real-valued Ziv counting bound predicate (L-LZ1-B)**.

For a parsing of length `n` with `c(n) = p.count` phrases, the counting
inequality `(c(n) + 1) ≤ |α| * (c(n) + 1)` (trivial form) extends to the
Cover-Thomas Lemma 13.5.5 RHS sum bound modulo log/entropy. This
predicate captures the *combinatorial* layer; the *entropy* layer
remains in L-LZ1-C scope. -/
def ZivCountingBound
    {α : Type*} [Fintype α]
    (p : LZ78Parsing α) (n : ℕ) : Prop := ...

/-- **Bridge to `IsZivInequalityPassthrough`**.

The combinatorial-layer Ziv counting bound, combined with any entropy
chain-rule hypothesis, trivially discharges `IsZivInequalityPassthrough`
(currently a `True` placeholder; bridge stays trivial until L-LZ1-C is
discharged elsewhere). -/
theorem IsZivInequalityPassthrough.ofZivCountingBound
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsZivInequalityPassthrough μ p lz78EncodingLength := True.intro

end InformationTheory.Shannon
```

### Approach (overall strategy / shape of solution)

**戦略の shape** — Ziv's inequality (`c(n) log c(n) ≤ -∑ log P(phrase_i)`)
の本体 discharge は ~300-500 行と重い。本 plan は **その partial layer
である combinatorial counting plumbing** に限定:

```
Ziv's inequality 完全形
   │
   ├── [L-LZ1-A] Combinatorial counting (本 plan で discharge)
   │     - LZ78Phrase の distinct count bound (|α| · (c+1))
   │     - LZ78Parsing.count_eq_length, count_le helpers
   │     - Finset.image / Fintype.card 経由の Nat 不等式
   │
   ├── [L-LZ1-B] Real-valued counting predicate (本 plan で publish)
   │     - ZivCountingBound : Prop で combinatorial bound を抽象化
   │
   ├── [L-LZ1-C] Entropy chain rule (撤退 — 別 plan)
   │     - H(X^n) ≤ Σ H(phrase_i) 形は entropy / measure theory 重量
   │
   └── [L-LZ1-D] log-sum 不等式と最終合流 (撤退 — 別 plan)
         - per-phrase log P sum + Ziv inequality 主形
```

L-LZ1-A は **purely combinatorial** (List + Finset + Fintype のみ)、
measure-theoretic infrastructure ゼロで完結可能。L-LZ1-B は **statement-level
shape** だけ与え、後続 discharge plan で `ZivCountingBound` を Prop-level
で展開する slot を確保。L-LZ1-C / L-LZ1-D は本 plan scope 外。

**Mathlib-shape-driven の設計選択** — `Finset.card_image_le`,
`Finset.card_product`, `Fintype.card_option`, `Nat.lt_iff_add_one_le`
の **conclusion form をそのまま** 使える `card ≤ |α| * (c + 1)` 形を
採用。Cover-Thomas 原文の `c(n) log c(n) ≤ n log |α| + n log c(n) / log c(n)`
形は **意図的に書かない**: そちらは L-LZ1-C / L-LZ1-D の領分。

### 規模見積

| Phase | 中央 | 出力 |
|---|---|---|
| Phase A | **80 行** | `LZ78ZivInequality.lean` — skeleton + imports |
| Phase B | **200 行** | combinatorial counting bounds (L-LZ1-A) |
| Phase C | **80 行** | `ZivCountingBound` predicate (L-LZ1-B) |
| Phase D | **40 行** | `IsZivInequalityPassthrough` bridge constructor |
| Phase V | **5 行** | `InformationTheory.lean` import 追記 |
| **累計** | **~400 行** | 1 ファイル合計 |

### ファイル構成

```
InformationTheory/Shannon/
  LZ78ZivInequality.lean   ← 新規 (~400 行)
                             ・LZ78Parsing.count_eq_length 系 thin
                             ・LZ78Phrase.card_image_bound (Fintype経由)
                             ・LZ78Parsing.distinctPhrases / その card bound
                             ・ZivCountingBound predicate
                             ・IsZivInequalityPassthrough bridge
InformationTheory.lean            ← `import InformationTheory.Shannon.LZ78ZivInequality` 追記
```

## 撤退ライン

- **L-LZ1-A (確定発動)**: Combinatorial counting bound discharge。`LZ78Parsing.count`,
  `LZ78Phrase` cardinality を `Finset.card_image_le` + `Fintype.card_option`
  経由で Nat レベル不等式に。
- **L-LZ1-B (確定発動)**: `ZivCountingBound` real-valued predicate publish。
  combinatorial layer の statement-level slot。後続 discharge plan で展開可。
- **L-LZ1-C (撤退)**: Entropy chain rule `H(X^n) ≤ Σ H(phrase_i)` は別 plan
  `lz78-ziv-entropy-chain-discharge-*` で。
- **L-LZ1-D (撤退)**: log-sum 不等式 + Ziv inequality 主形は別 plan
  `lz78-ziv-inequality-discharge-final-*` で。

## 当面の next step

1. Phase A skeleton 起草 → Phase B combinatorial bounds → Phase C predicate publish → Phase D bridge → Phase V `InformationTheory.lean` 編入
