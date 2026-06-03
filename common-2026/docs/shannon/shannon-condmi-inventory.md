# Phase 4-δ-(b) 条件付き相互情報量 Mathlib 在庫調査

> Phase 4-δ-(b) (Markov chain 版 Shannon converse) 着手前の Mathlib 在庫調査。Phase 4-M0 (`docs/shannon/shannon-mathlib-inventory.md`) の続編。
>
> **調査日**: 2026-05-10。subagent 3 並列で 1 ターン (`condIndepFun` / `condMutualInfo` / kernel chain rule plumbing 各 1 名)。

## 一行サマリ

**`condDistrib` + `condIndepFun` + `compProd_map_condDistrib` の三点セットは完備。`condMutualInfo` 自体は Mathlib 不在で 80〜120 行の自作必須。Markov chain 述語も不在だが `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (`condDistrib` factorization 形) を介して 1 行定義可能。最大の障壁は 3 重 compProd の Measure 層 nested prod ↔ kernel compProd の plumbing で、Phase 4-α 級の作業量が見込まれる。**

---

## A. `condIndepFun` / 条件付き独立 (Conditional.lean)

| 補題名 | file:line | signature 要点 | 状態 | δ-(b) での扱い |
|---|---|---|---|---|
| **`CondIndepFun`** | `Probability/Independence/Conditional.lean:155` | `def CondIndepFun (m' : MeasurableSpace Ω) (f : Ω → β) (g : Ω → γ) μ : Prop := Kernel.IndepFun f g (condExpKernel μ m') ...` | ✅ | Markov chain 仮定の本体 (β 形式と組み合わせる) |
| **`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`** | `Conditional.lean:867` | `g ⟂ᵢ[k] f ↔ condDistrib f (k, g) μ =ᵐ (condDistrib f k μ).prodMkRight _` | ✅ | **β 形式 Markov 定式化の核**。`condDistrib Yo (Z, Msg) = condDistrib Yo Z` を独立性に変換 |
| `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` | `Conditional.lean:817` | `f ⟂ᵢ[k] g ↔ μ.map (k, f, g) = (Kernel.id ×ₖ (condDistrib f k μ ×ₖ condDistrib g k μ)) ∘ₘ μ.map k` | ✅ | 結合分布形の独立性。chain rule との橋渡しに使える |
| `iCondIndepFun` | `Conditional.lean:145` | 複数変数版 (将来の多段 Markov 拡張用) | ✅ | 今回 (3 変数) は不要 |
| **`IsMarkovChain` (3 変数の Markov chain 述語)** | — | (X → Z → Y のような連鎖を直接表す述語) | ❌ | 自作: 1〜2 行で `condIndepFun (encoder∘Msg).comap σ Yo Msg μ` を `def`、または condDistrib 等式形で `def` |

---

## B. `condDistrib` 等式形 (CondDistrib.lean)

| 補題名 | file:line | signature 要点 | 状態 | δ-(b) での扱い |
|---|---|---|---|---|
| **`condDistrib`** | `Probability/Kernel/CondDistrib.lean:64` | `noncomputable def condDistrib (Y : Ω → β) (X : Ω → α) (μ : Measure Ω) : Kernel α β := (μ.map (fun ω => (X ω, Y ω))).condKernel` | ✅ | Phase 3 Fano で既用、δ-(b) でも主軸 |
| **`compProd_map_condDistrib`** | `CondDistrib.lean:82` | `(μ.map X) ⊗ₘ condDistrib Y X μ = μ.map (fun a => (X a, Y a))` | ✅ | **Bayes 規則の kernel 形**。chain rule で結合分布を分解する核 |
| **`condDistrib_comp_self`** | `CondDistrib.lean:196` | `condDistrib (f ∘ X) X μ =ᵐ Kernel.deterministic f hf` | ✅ | `encoder ∘ Msg` の Msg 条件下分布が deterministic |
| `condDistrib_comp` | `CondDistrib.lean:183` | `condDistrib (f ∘ Y) X μ =ᵐ condDistrib Y X μ ∘ₖ f` | ✅ | post-process の condDistrib への波及 (DPI 系) |
| `condDistrib_comp_map` | `CondDistrib.lean:86` | `condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y` | ✅ | 周辺化 (chain rule の項を合算) |
| **`condDistrib_ae_eq_of_measure_eq_compProd`** | `CondDistrib.lean:163` | `μ.map (X, Y) = μ.map X ⊗ₘ κ → condDistrib Y X μ =ᵐ[μ.map X] κ` | ✅ | **条件付き分布の一意性**。自作 Markov 定式の正当化に使う |
| `IsMarkovKernel (condDistrib Y X μ)` | `CondDistrib.lean:68` (instance) | auto-derive | ✅ | klDiv の前提条件 (`IsMarkovKernel`) を自動充足 |

---

## C. KL chain rule (Phase 4-M0 で確認済、δ-(b) 用に再評価)

| 補題名 | file:line | signature 要点 | 状態 | δ-(b) での扱い |
|---|---|---|---|---|
| **`klDiv_compProd_eq_add`** | `KullbackLeibler/ChainRule.lean:204` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | ✅ | **chain rule の主役**。`κ = η` 特例で 1 段、独立 kernel ⇒ 0 で Markov 系を導出 |
| `klDiv_compProd_left` | `ChainRule.lean:182` | `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` (`@[simp]`) | ✅ | kernel 共有時の分解、Markov ⇒ condMI = 0 の補助 |
| `integrable_llr_compProd_iff` | `ChainRule.lean:115` | (Real 値 chain rule の前提) | ✅ | toReal 経路で chain rule を使うときに |

---

## D. kernel composition / 結合則 (CompProd.lean)

| 補題名 | file:line | signature 要点 | 状態 | δ-(b) での扱い |
|---|---|---|---|---|
| **`Kernel.compProd_assoc`** | `Probability/Kernel/Composition/CompProd.lean:467` | `(κ ⊗ₖ (η ⊗ₖ ξ)).map prodAssoc.symm = κ ⊗ₖ η ⊗ₖ ξ` | ✅ | 3 重 compProd の結合則。chain rule plumbing の基盤 |
| `compProd_const` | `Measure/MeasureCompProd.lean:141` | `μ ⊗ₘ (Kernel.const α ν) = μ.prod ν` | ✅ | `Measure.prod` と `Kernel.compProd` の同一視 (Phase 4-α で既用) |
| `Kernel.deterministic` | `Probability/Kernel/Composition/Deterministic.lean:68` | `IsDeterministic (deterministic f hf)` | ✅ | `encoder ∘ Msg` を kernel 化 |
| `prodMkRight_apply` | `Probability/Kernel/Composition/MapComap.lean:249` | `prodMkRight γ κ (a, c) = κ a` | ✅ | β 形式 Markov の右辺で使う |

---

## E. 条件付きエントロピー / 条件付き MI (高レベル)

| 補題名 | file:line | signature 要点 | 状態 | δ-(b) での扱い |
|---|---|---|---|---|
| **`condEntropy` (Measure 版)** | `InformationTheory/Fano/Measure.lean:68` | `∫ y, ∑ x, negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)` (自作) | ✅ | Phase 3 Fano 既存。condMI を `H − H|·` 経由で書く道もあるが、KL 直接の方が短いはず |
| **`condMutualInfo`** | — | (`I(X; Y \| Z)`) | ❌ | **自作必須**。3〜5 行 (klDiv の `condDistrib` 形を `μ.map Z` で積分) |
| `Mathlib/InformationTheory/` 内の Shannon 系 | — | entropy / mutualInfo / channelCapacity | ❌ | Phase 4-M0 で確認済、不在 |

---

## 設計判断: Markov chain の定式化

**結論: β 形式 (condDistrib 等式形) を採用する。**

```lean
/-- Markov chain `Msg → Z → Yo`: `Yo` の条件付き分布が `Z` のみに依存。 -/
def IsMarkovChain (μ : Measure Ω) (Msg : Ω → M) (Z : Ω → X) (Yo : Ω → Y) : Prop :=
  condDistrib Yo (fun ω => (Msg ω, Z ω)) μ
    =ᵐ[μ.map (fun ω => (Msg ω, Z ω))]
    (condDistrib Yo Z μ).prodMkRight M
```

または `condIndepFun` を経由する形 (どちらが下流の補題で扱いやすいかは skeleton 着手時に判断):

```lean
def IsMarkovChain (μ : Measure Ω) (Msg : Ω → M) (Z : Ω → X) (Yo : Ω → Y) : Prop :=
  CondIndepFun (MeasurableSpace.comap Z mX) Msg Yo μ
```

**β 形式採用の根拠**:

1. `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (Conditional.lean:867) で β 形式 ↔ `condIndepFun` が直結 → どちらでも書ける
2. β 形式は `condDistrib_ae_eq_of_measure_eq_compProd` で `μ.map (Msg, Z, Yo)` の compProd 分解と直接結びつき、chain rule (`klDiv_compProd_eq_add`) の前提に乗せやすい
3. `condDistrib_comp_self` で `condDistrib (encoder ∘ Msg) Msg μ = Kernel.deterministic encoder` が出るため、`encoder ∘ Msg` を `Z` の役を果たす kernel として処理しやすい
4. Phase 3 Fano で `condDistrib` を既用しており、Phase 4-α/β/γ も `condDistrib_comp_map` を 1 箇所で使用済 → 既存スタイルと整合

---

## chain rule の plumbing 障壁 (Phase 4-α 比)

**最大の障壁**: `μ.map (Msg, Z, Yo)` を 3 重 compProd `μ.map Msg ⊗ₘ condDistrib Z Msg ⊗ₘ condDistrib Yo (Msg, Z)` に分解するとき、Measure 層の nested `prod` (左結合) と Kernel 層の nested `compProd` (右結合 / 結合則) の plumbing で `MeasurableEquiv.prodAssoc` を通す必要がある。

具体的には:
- `Kernel.compProd_assoc` (`CompProd.lean:467`) は **`map prodAssoc.symm` 形**で書かれており、そのままでは Measure 側の `(α × β) × γ` の Measure と直接照合できない
- Phase 4-α では 2 重 compProd しか扱っておらず (`(μ.map Xs).prod (μ.map Yo)`)、associativity を通すのは初めて
- 推定 plumbing 量: **40〜60 行** (associativity 補題 1 本 + chain rule 適用部 30〜40 行)

**chain rule 全体の plumbing 見積**:

| 構成要素 | 推定行数 | 根拠 |
|---|---|---|
| `condMutualInfo` 定義 | 5〜10 | `noncomputable def condMutualInfo := ∫⁻ z, klDiv ((condDistrib (X, Y) Z μ) z) ((condDistrib X Z μ z).prod (condDistrib Y Z μ z)) ∂(μ.map Z)` 形、または KL の compProd 形で簡潔に |
| 3 重 compProd 結合則の plumbing | 40〜60 | `compProd_assoc` を Measure 側に下ろす補題 + 主応用での書き換え |
| chain rule `I(X, Z; Y) = I(Z; Y) + I(X; Y \| Z)` | 30〜50 | `klDiv_compProd_eq_add` を 1 段適用 + condDistrib factorization |
| Markov ⇒ condMI = 0 | 20〜30 | β 形式 ⇒ kernel 共有 ⇒ `klDiv_compProd_left` で 0 |
| DPI for `Prod.fst` (`I(Msg; Yo) ≤ I(Msg, Z; Yo)`) | 10〜15 | Phase 4-α DPI を `f := Prod.fst` で適用 |
| converse 主応用 (Converse.lean) | 30 | 上を組み合わせて bridge |
| **合計** | **135〜195 行** | Phase 4-α DPI (80 行) + Bridge (50 行) + α 補強分の Phase 4-α 級 |

---

## 撤退ライン (再評価)

- **3 重 compProd associativity の plumbing が 1 週間で書けない**場合 → β 形式 Markov を `condIndepFun` 形に切り替え、`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` を public API として使う形にすると associativity を回避できる可能性あり
- **chain rule の整合が取れない**場合 (Markov ⇒ condMI = 0 が出ない / 符号が合わない) → 条件付き MI の定義を `klDiv_compProd_eq_add` の **第 2 項 = condMI** という entailment 形に変える (定義から chain rule が trivially 出る形)
- **両方詰まる**場合 → Phase 4-δ-(b) を「定義 + 性質の skeleton + Markov 系 sorry」で打ち止め、proof-log で「Mathlib 在庫の不足を可視化」として記録 (撤退ラインの計画書記載通り)

---

## 着手順 (Phase 4-δ-(b) skeleton)

1. **`InformationTheory/Shannon/CondMutualInfo.lean` 新設** — `condMutualInfo` 定義 + 基本性質 (nonneg) を `:= sorry` skeleton で
2. **`IsMarkovChain` 定義** — β 形式で同じファイルに
3. **chain rule** — `klDiv_compProd_eq_add` を経由する形で skeleton (sorry 1 個)
4. **`condMutualInfo_eq_zero_of_markov`** — sorry 1 個
5. **`mutualInfo_le_of_markov`** — chain rule + condMI = 0 + DPI for Prod.fst を合成
6. **`InformationTheory/Shannon/Converse.lean` 末尾に `shannon_converse_single_shot_markov_encoder`** — `mutualInfo_le_of_markov` + 既存 `shannon_converse_single_shot` の合成

各ステップで `lake env lean` silent を確認しながら進める。

---

## 参照

- 親 plan: [`shannon-encoder-extensions-plan.md`](shannon-encoder-extensions-plan.md) — 本ファイルは §Phase 4-δ-(b) の inventory 結果
- Phase 4-M0 inventory: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md)
- ムーンショット親計画: [`shannon-moonshot-plan.md`](shannon-moonshot-plan.md)
