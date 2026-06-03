# MI chain rule (B-7) Mathlib + 既存 InformationTheory 在庫

> [mi-chain-rule-moonshot-plan.md](mi-chain-rule-moonshot-plan.md) Phase 0 で実施する API 在庫調査結果 (2026-05-11)。loogle (`./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index`) + `rg` 併用。

## 一行サマリ

**Mathlib に `mutualInfo` / `condMutualInfo` の chain rule 形は不在 (loogle で 0 件)。`klDiv_compProd_eq_add` (`Mathlib.InformationTheory.KullbackLeibler.ChainRule:204`) + 既存 InformationTheory `mutualInfo_chain_rule` (2 変数版、`CondMutualInfo.lean:219`) + `MeasurableEquiv.piFinSuccAbove` の 3 つだけで n 変数化は閉じる。i.i.d. corollary は `klDiv_prod_const_left` (既存 `MutualInfo.lean:80`) + `klDiv_compProd_eq_add` で chain rule 経由せずに直接書ける。`Fintype α + MeasurableSpace α + MeasurableSingletonClass α + Nonempty α` ⇒ `StandardBorelSpace α` が自動 derive されることを動作確認済 (existing `mutualInfo_chain_rule` の SBS 仮定が α への明示要求にならない)。**

---

## A. Mathlib `klDiv` chain rule (Phase 4-M0 既存、B-7 用に再評価)

| 補題名 | file:line | signature (`[...]` verbatim) | 結論形 verbatim | B-7 での扱い |
|---|---|---|---|---|
| **`klDiv_compProd_eq_add`** | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | `theorem klDiv_compProd_eq_add {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | i.i.d. corollary 経路の主役 (Phase C base induction) |
| **`klDiv_compProd_left`** | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:182` | `@[simp] lemma klDiv_compProd_left {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β) [IsFiniteKernel κ] : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` | kernel 共有時 (B-7 では使わない見込み、Markov ⇒ condMI = 0 系で既使) |

Mathlib に **mutualInfo / condMutualInfo は存在せず** (`loogle "mutualInfo"` `Found 0`)。chain rule 系も同様。

---

## B. 既存 InformationTheory `mutualInfo` / `condMutualInfo` (B-7 直近依存)

| 補題名 | file:line | signature verbatim | 結論形 verbatim | B-7 での扱い |
|---|---|---|---|---|
| **`mutualInfo` (定義)** | `InformationTheory/Shannon/MutualInfo.lean:36` | `noncomputable def mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ := klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `klDiv (μ.map (Xs, Yo)) ((μ.map Xs).prod (μ.map Yo))` | n 変数化の基本形 (Xs が pi 値) |
| **`klDiv_map_measurableEquiv`** | `InformationTheory/Shannon/MutualInfo.lean:52` | `theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv (μ.map e) (ν.map e) = klDiv μ ν` | `klDiv (μ.map e) (ν.map e) = klDiv μ ν` | **Phase A の核**: `e × id` を介した joint reshape |
| **`klDiv_prod_const_left`** | `InformationTheory/Shannon/MutualInfo.lean:80` | `theorem klDiv_prod_const_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ] (ν₁ ν₂ : Measure β) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] : klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂` | `klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂` | i.i.d. corollary で `n` 番目の項を `(n-1)` 番目に圧縮するのに使う |
| **`mutualInfo_comm`** | `InformationTheory/Shannon/MutualInfo.lean:93` | `theorem mutualInfo_comm (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : mutualInfo μ Xs Yo = mutualInfo μ Yo Xs` | `mutualInfo μ Xs Yo = mutualInfo μ Yo Xs` | i.i.d. corollary 終盤で必要なら使用 |
| **`mutualInfo_eq_zero_iff_indep`** | `InformationTheory/Shannon/MutualInfo.lean:109` | `theorem mutualInfo_eq_zero_iff_indep (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ` | `mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ` | base case `n=0` で `Fin 0 → α` 上の constant ⇒ trivially independent ⇒ MI = 0 |
| **`mutualInfo_ne_top`** | `InformationTheory/Shannon/MutualInfo.lean:192` | `theorem mutualInfo_ne_top [Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : mutualInfo μ Xs Yo ≠ ∞` | `mutualInfo μ Xs Yo ≠ ∞` | i.i.d. corollary で `n • I` を `ENNReal.toReal` 経路で扱うときに使用可能 (本シードでは使わない) |
| **`condMutualInfo` (定義)** | `InformationTheory/Shannon/CondMutualInfo.lean:46` | `noncomputable def condMutualInfo (μ : Measure Ω) [IsFiniteMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞ := klDiv ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ) ((μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)))` | `klDiv ((μ.map Zc) ⊗ₘ ...) ((μ.map Zc) ⊗ₘ ...)` | **n 変数化の RHS の構成要素**。X, Y に `StandardBorelSpace + Nonempty` 必須、Z には不要 |
| **`mutualInfo_chain_rule`** (2 変数版) | `InformationTheory/Shannon/CondMutualInfo.lean:219` | `theorem mutualInfo_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) : mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | `mutualInfo μ (Zc, Xs) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | **Phase B の step case の核**。Zc = `Fin i.val → α` (prefix) で適用 |
| **`condMutualInfo_nonneg`** | `InformationTheory/Shannon/CondMutualInfo.lean:55` | `theorem condMutualInfo_nonneg ... : 0 ≤ condMutualInfo μ Xs Yo Zc := bot_le` | `0 ≤ condMutualInfo μ Xs Yo Zc` | RHS の項が非負 (signature 上自明) |

**鍵観察**: `condMutualInfo` は `[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]` を要求するが、**Z (prefix) には課されない**。一方 `mutualInfo_chain_rule` は `[StandardBorelSpace X]`/`[Nonempty X]` を Xs と Yo に課す (Z にも `StandardBorelSpace + Nonempty` は不要)。n 変数化で各 `Xs i : Ω → α` に SBS + Nonempty が必要 → `α` レベルで仮定 (`Fintype α` 等で自動 derive)。

---

## C. Han Phase B chain rule (参考: 完全対称な induction)

| 補題名 | file:line | signature verbatim | 結論形 verbatim | B-7 での扱い |
|---|---|---|---|---|
| **`jointEntropy_chain_rule`** | `InformationTheory/Shannon/Han.lean:56` | `theorem jointEntropy_chain_rule {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) : jointEntropy μ Xs = ∑ i : Fin n, InformationTheory.MeasureFano.condEntropy μ (Xs i) (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)` | `jointEntropy μ Xs = ∑ i, condEntropy μ (Xs i) (prefix)` | **n 変数 induction の構造の見本**。MI chain rule (B-7 Phase B) もこの shape を踏襲 |

**Han Phase B の induction 構造** (要点):
- `n = 0`: 空和 + `entropy` of `Fin 0 → α` constant ⇒ 0
- `n+1`: `MeasurableEquiv.piFinSuccAbove (Fin.last n)` で `Fin (n+1) → α ≃ᵐ α × (Fin n → α)` → `entropy_pair_eq_entropy_add_condEntropy` で 1 段分解 → IH → `Fin.sum_univ_castSucc` で和合体

---

## D. MeasurableEquiv reshape (Pi 値)

| 補題名 | file:line | signature verbatim | 結論形 verbatim | B-7 での扱い |
|---|---|---|---|---|
| **`MeasurableEquiv.piFinSuccAbove`** | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean` (lemma name `piFinSuccAbove`) | `def piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, MeasurableSpace (α i)] (i : Fin (n + 1)) : (∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)` | `(∀ j, α j) ≃ᵐ α i × ∀ j, α (i.succAbove j)` | Phase B step case: `Fin (n+1) → α ≃ᵐ α × (Fin n → α)` (i = Fin.last n) |
| `measurePreserving_piFinSuccAbove` | `Mathlib/MeasureTheory/Constructions/Pi.lean:805` | `theorem measurePreserving_piFinSuccAbove {n : ℕ} (α : Fin (n + 1) → Type*) {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i : Fin (n + 1)) : MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ) ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j))` | `MeasurePreserving (piFinSuccAbove α i) (Measure.pi μ) ((μ i).prod (Measure.pi ...))` | i.i.d. corollary の product 分解 (Phase C) で `Measure.pi (n+1) ≃ μ_i × Measure.pi n` の plumbing |

---

## E. StandardBorelSpace 自動 derive 確認 (Phase 0 動作確認済)

`/tmp/sbs_test*.lean` で `lake env lean` 通過 (silent):

```lean
variable {n : ℕ} {α : Type*} [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Nonempty α]

example : StandardBorelSpace α := by infer_instance        -- ✅
example : StandardBorelSpace (Fin n → α) := by infer_instance  -- ✅
example : Nonempty (Fin n → α) := by infer_instance         -- ✅
example : MeasurableSingletonClass (Fin n → α) := by infer_instance  -- ✅
```

**帰結**: B-7 では `α` に `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]` のみ仮定すれば、`StandardBorelSpace α`、`StandardBorelSpace (Fin i → α)`、`Nonempty (Fin i → α)` は全部自動発火。明示的に `[StandardBorelSpace α]` を仮定として書く必要はない。

---

## F. 既存 Han Phase B induction の transferable parts

Han Phase B (`Han.lean:64-141`) 内で **B-7 の Phase B にも転用できる** plumbing:

- `MeasurableEquiv.piFinSuccAbove` の使い方 (`h_e_eq` の pattern match)
- `entropy_measurableEquiv_comp` (entropy 不変性) ↔ B-7 では `mutualInfo_map_left_measurableEquiv` を新規追加 (Phase A)
- 空 fold (`Fin.sum_univ_zero`, `Subsingleton.elim`, `negMulLog_one`) — base case `n=0` の handling
- `Fin.sum_univ_castSucc` — step case の和合体

---

## G. i.i.d. corollary の依存補題候補

| 経路 | 鍵補題 | file | 評価 |
|---|---|---|---|
| **直接 (Phase C 採用)**: `klDiv (Π ν_i) (Π (μ.prod ν_i))` を induction で展開 | `klDiv_compProd_eq_add`, `klDiv_prod_const_left`, `MeasurableEquiv.piFinSuccAbove`, `measurePreserving_piFinSuccAbove` | Mathlib + 既存 | **採用**: chain rule (Phase B) より短い (各 inductive step が KL の compProd 加法性 1 段)。150-200 行見込み |
| Chain rule 経由 | Phase B の `mutualInfo_chain_rule_fin` + 「i.i.d. ⇒ 各 condMI = unconditional MI」補題 | 自作 | 不採用: condMI の reduction が plumbing-heavy、本シードでは Phase B を独立に publish して B-3 で必要なら再演奏 |

---

## H. B-3 への引き継ぎ予定 API

本シードで publish される (`InformationTheory.Shannon` namespace):

- `mutualInfo_map_left_measurableEquiv` (Phase A) — `MeasurableEquiv` reshape 不変性
- `mutualInfo_map_right_measurableEquiv` (Phase A) — 右側 (Y) reshape 不変性
- `mutualInfo_chain_rule_fin` (Phase B) — n 変数 chain rule
- `mutualInfo_iid_eq_nsmul` (Phase C) — i.i.d. corollary (B-3 で直接使用)
- `mutualInfo_iid_eq_nsmul_of_copy` (Phase C 簡略形) — n 同分布コピー版 (i.i.d. の標準実装が「単一 RV を `Fin n` でコピー」する場合の便利形)

---

## 参照

- 親 plan: [`mi-chain-rule-moonshot-plan.md`](mi-chain-rule-moonshot-plan.md)
- ムーンショット seed カード: [`../moonshot-seeds.md`](../moonshot-seeds.md) §B-7
- 関連既存 inventory: [`shannon-condmi-inventory.md`](shannon-condmi-inventory.md) (2 変数 chain rule の original inventory)
- 対称 induction 参考: [`../han/han-moonshot-plan.md`](../han/han-moonshot-plan.md) Phase B
