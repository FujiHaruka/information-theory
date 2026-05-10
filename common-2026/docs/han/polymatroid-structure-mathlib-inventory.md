# Polymatroid structure 化: Mathlib インベントリ サブ計画 (Phase 0)

> **Parent**: [`polymatroid-structure-plan.md`](polymatroid-structure-plan.md) §Phase 0
>
> **Status (2026-05-11):** 起草 / 軸 1〜4 全件 ✅。前 plan
> ([`polymatroid-mathlib-inventory.md`](polymatroid-mathlib-inventory.md))
> の 軸 1 (Polymatroid / Submodular structure 不在) を再検証し、本 plan 用に
> structure 化視点のシグネチャ (Mathlib `structure Matroid` の field 流儀、
> `[DecidableEq ι]` instance 要求の有無、`Finset ι → ℝ` 用 `Monotone` の API)
> を追加調査した結果を記録する。

## 進捗

- [x] 軸 1: `Polymatroid` / `Submodular` (集合関数版) structure 不在の **再検証** ✅
- [x] 軸 2: Mathlib における「rank 関数 + 公理」style の `structure` 例 (Matroid を rank として読む) ✅
- [x] 軸 3: `Monotone` / 集合関数版 `Submodular` 系のクラス / predicate 探索 ✅
- [x] 軸 4: `[DecidableEq ι]` / `[Fintype ι]` の必要性確認 (Finset 演算 + `Polymatroid` field 用) ✅

## ゴール / Approach

structure 化を着手する判断材料として、(1) Mathlib の同型既存物がない再確認、(2) 同 family の既存 `structure` の field 流儀 (`Matroid`) を mirror すべきかの判断、(3) `Monotone` / `IsSubmodular` 系の既存 class が利用可能かどうかを記録する。

### 結論サマリ

| 軸 | 結果 | structure 化への影響 |
|---|---|---|
| (1) Polymatroid / 集合関数 Submodular structure | **再検証で再度不在**。`loogle` も literal 文字列の suggest しか返さない。Matroid rank 上の submodularity 補題のみ存在 | 本 plan で `structure Polymatroid` を新規導入 |
| (2) Mathlib `structure Matroid` の field 流儀 | **`structure ... where` で data field + Prop field を bundle**。`@[mk_iff] protected class Matroid.Finite` のように追加 typeclass は別出し | 本 plan も同流儀: `structure Polymatroid` で rank + 3 Prop axiom を bundle |
| (3) `Monotone` / `IsSubmodular` (集合関数) | `Monotone f` (`f : Finset ι → ℝ`) は `Mathlib.Order.Monotone.Basic` で利用可。集合関数 `IsSubmodular` クラスは **不在**。submodular は `Matroid.eRk_inter_add_eRk_union_le` のような単発 lemma としてのみ | 公理は **`Prop` field を直接書く** (`Monotone` 一個だけ採用、submodular / empty は専用 Prop field) |
| (4) `[DecidableEq ι]` / `[Fintype ι]` 必要性 | `Finset ι` の `∪ / ∩` 演算自体は `[DecidableEq ι]` を必要とする (`Finset.union` 定義側)。`[Fintype ι]` は **rank function 単独では不要**。`Polymatroid (Fin n)` で entropyPolymatroid を組むときは両方 instance 自動発火 | structure 定義は `[DecidableEq ι]` のみ要求、`[Fintype ι]` は導入しない |

## Phase 詳細

### 軸 1: `Polymatroid` / `Submodular` (集合関数版) structure — **再検証**

#### 結論 (1 行)

**前回 (2026-05-11 朝) の確認 から状況不変、Mathlib に集合関数版 `Polymatroid` / `Submodular` / `IsSubmodular` structure / class はいずれも存在しない**。

#### 確認手順 (2026-05-11 再実行)

```bash
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Polymatroid"
# → unknown identifier 'Polymatroid' / Maybe you meant: "Polymatroid"
#   (literal 文字列の suggest のみ。実体不在)

./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Submodular"
# → unknown identifier 'Submodular' / Maybe you meant: "Submodular"

./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "IsSubmodular"
# → unknown identifier 'IsSubmodular' / Maybe you meant: "IsSubmodular"

rg -i "polymatroid|submodular" .lake/packages/mathlib/Mathlib/ -l
# → 3 件のみ:
#   .lake/packages/mathlib/Mathlib/Combinatorics/Additive/VerySmallDoubling.lean
#   .lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean
#   .lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Rank/ENat.lean

rg -n "structure Polymatroid|class Polymatroid" .lake/packages/mathlib/Mathlib/
# → 0 件

rg -n "IsRankFunction|RankFunction|rank_function" .lake/packages/mathlib/Mathlib/
# → 1 ファイルのみ (SimplicialSet/AnodyneExtensions/RelativeCellComplex.lean
#   `SSet.Subcomplex.Pairing.RankFunction` — simplicial set の rank function、無関係)
```

#### Mathlib に存在する submodularity 関連 (本 plan で **使わない** ことの記録)

##### `Matroid.eRk_inter_add_eRk_union_le`

- **位置**: `.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Rank/ENat.lean`
- **コメント verbatim** (rg より):
  ```
  /-! ### Submodularity -/
  /-- The `ℕ∞`-valued rank function is submodular. -/
  ```
- **使い所 (本 plan)**: 使わない。`ℕ∞` 値で本 plan の `ℝ` 値 entropy と統合不可

##### `Matroid` (本 plan で field 流儀として mirror)

- **位置**: `.lake/packages/mathlib/Mathlib/Combinatorics/Matroid/Basic.lean:192`
- **シグネチャ** (verbatim):
  ```
  structure Matroid (α : Type*) where
    /-- `M` has a ground set `E`. -/
    (E : Set α)
    /-- `M` has a predicate `Base` defining its bases. -/
    (IsBase : Set α → Prop)
    /-- `M` has a predicate `Indep` defining its independent sets. -/
    (Indep : Set α → Prop)
    /-- The `Indep`endent sets are those contained in `Base`s. -/
    (indep_iff' : ∀ ⦃I⦄, Indep I ↔ ∃ B, IsBase B ∧ I ⊆ B)
    (exists_isBase : ∃ B, IsBase B)
    (isBase_exchange : Matroid.ExchangeProperty IsBase)
    (maximality : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
    (subset_ground : ∀ B, IsBase B → B ⊆ E)
  ```
- **観察**:
  - `structure ... where` で **data field + Prop field を全部一括 bundle**。`(field_name : Type)` の形で揃える
  - 各 field に **docstring を `/-- ... -/` で 1 行ずつ** 付ける
  - 追加の typeclass (`Matroid.Finite`, `Matroid.Nonempty`) は `protected class` として **別出し**
  - `attribute [local ext] Matroid` を付けて `ext` lemma を自動生成
- **使い所 (本 plan)**: `structure Polymatroid` の field 流儀の reference。同じく `(rank : Finset ι → ℝ)` + 3 Prop field の形で書く

#### Phase 影響

- **軸 1 結論不変**。本 plan で `Polymatroid` を新規導入する判断は維持
- **field 流儀は Matroid を mirror**: `structure ... where` で data + Prop を bundle、各 field に docstring 1 行

---

### 軸 2: Mathlib における「rank 関数 + 公理」style の `structure` 例

#### 結論 (1 行)

**`Matroid` が直接 mirror 対象**。`structure Matroid (α : Type*) where ...` は data field (`E`, `IsBase`, `Indep`) と Prop field (`indep_iff'`, `exists_isBase`, `isBase_exchange`, `maximality`, `subset_ground`) を一体で bundle する流儀。本 plan の `Polymatroid` も同じく `(rank : Finset ι → ℝ)` data + 3 axiom Prop で bundle。

#### 採用方針

```lean
structure Polymatroid (ι : Type*) [DecidableEq ι] where
  /-- The real-valued rank function on subsets of the ground set. -/
  rank : Finset ι → ℝ
  /-- The rank of the empty set is zero. -/
  rank_empty : rank ∅ = 0
  /-- The rank function is monotone in the subset relation. -/
  rank_mono : Monotone rank
  /-- The rank function is submodular. -/
  rank_submodular : ∀ S T, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T
```

`Monotone rank` は `S ⊆ T → rank S ≤ rank T` と equivalent (`Finset` は order に `⊆` を持つ。下の軸 3)。

#### `class` vs `structure` の判断

- Mathlib では `Matroid` も `structure`、`Polymatroid` も同じく **`structure`** (data, not a typeclass)。
- Polymatroid は具体的 data (rank function そのもの) を持ち、同じ index type に複数の polymatroid 構造が乗りうる (entropy / matroid rank / submodular partition function / 等)。typeclass にすると一意性が崩れて `synthInstance` で曖昧になるので不適。
- 既存 Mathlib `Matroid` も同じ理由で `structure` を採用している。

---

### 軸 3: `Monotone` / 集合関数版 `Submodular` 系のクラス / predicate

#### 結論 (1 行)

`Monotone f` は **そのまま使える** (`Finset ι` は `⊆` で `LE`、`f : Finset ι → ℝ` で `Monotone f ↔ ∀ {S T}, S ⊆ T → f S ≤ f T`)。**集合関数版 `IsSubmodular` クラスは Mathlib に不在**、submodular は専用 Prop field として手書きする。

#### 採用候補

##### `Monotone`

- **位置**: `.lake/packages/mathlib/Mathlib/Order/Monotone/Basic.lean` (約 line 50 周辺、Mathlib の最も基本的な定義)
- **シグネチャ** (verbatim):
  ```
  def Monotone (f : α → β) : Prop :=
    ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
  ```
- **引数**: `α β : Type*` (implicit, with `[Preorder α] [Preorder β]`), `f : α → β` (explicit)
- **結論形**: `Prop`
- **使い所**: `rank_mono : Monotone rank` の field 直接記述。`Finset ι` の `LE` instance は `⊆` で発火、`ℝ` の `LE` は標準。

##### `Finset` の `LE` instance

- **位置**: `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean` (Order instance 周辺)
- **要点**: `Finset ι` は `LE` を持ち `s ≤ t ↔ s ⊆ t`。`Monotone (rank : Finset ι → ℝ)` は `S ⊆ T → rank S ≤ rank T` と直接 unfold できる
- **使い所**: `Polymatroid` field の `rank_mono` を `Monotone rank` で書いたとき、projection で `pm.rank_mono h` (`h : S ⊆ T`) が直接通るかを確認

#### 集合関数版 `IsSubmodular` 不在の確認

```bash
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "IsSubmodular"
# → unknown identifier 'IsSubmodular'

rg -n "class IsSubmodular|def IsSubmodular|structure IsSubmodular" .lake/packages/mathlib/Mathlib/
# → 0 件

rg -n "submodular_set|Set.Submodular" .lake/packages/mathlib/Mathlib/
# → 0 件
```

→ **不在を裏取り済み**。submodular は本 plan で `Prop` field 直書き (`∀ S T, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T`) する。将来 Mathlib に `IsSubmodular` 等が入った場合は field を class 経由に切り替える migration を検討。

#### Phase 影響

- `rank_mono` は `Monotone rank` で 1 行
- `rank_submodular` は **直接 Prop 書き** (専用 class なし)
- `rank_empty` は `rank ∅ = 0` で直書き

---

### 軸 4: `[DecidableEq ι]` / `[Fintype ι]` 必要性

#### 結論 (1 行)

`structure Polymatroid` の **rank field を書くだけ**なら `[DecidableEq ι]` のみで十分 (`rank ∅ = 0` で `(∅ : Finset ι)` は `[DecidableEq ι]` 不要、`rank (S ∪ T)` の `∪` で `[DecidableEq ι]` が必要)。`[Fintype ι]` は **不要** (Polymatroid は Finset 上で完結し全体集合 `Finset.univ` を要求しない)。

#### 詳細

- `(∅ : Finset ι)` — `Finset.empty` は `[DecidableEq ι]` 不要 (Mathlib `Finset.empty` 定義側は EmptyCollection で type class 不要)
- `S ∪ T : Finset ι` — `Finset.union` は `[DecidableEq ι]` を要求 (`Finset` 内部表現の重複除去のため)
- `S ∩ T : Finset ι` — `Finset.inter` も同様 `[DecidableEq ι]` を要求
- `S ⊆ T` — `Finset` の `LE` instance は `[DecidableEq ι]` 不要
- `Monotone (rank : Finset ι → ℝ)` — `Monotone` 自体は `[DecidableEq ι]` 不要、ただし `rank_mono` を呼ぶ時の `S ⊆ T` 引数で `Finset.LE` 経由で `[DecidableEq ι]` 不要

→ **`structure Polymatroid (ι : Type*) [DecidableEq ι] where ...` で十分**、`[Fintype ι]` は付けない。

`entropyPolymatroid` を `Fin n` で作るときは `[DecidableEq (Fin n)]` (instance 自動発火、`Fin.decEq`) で発火。

#### Phase 影響

- `structure Polymatroid (ι : Type*) [DecidableEq ι] where ...` で書く
- `entropyPolymatroid` の宣言で `ι := Fin n` 固定、`[DecidableEq (Fin n)]` 自動発火
- `[Fintype ι]` を不要に保つことで、将来 `ι` を可算無限 (e.g., `ℕ`) に拡張しても定義が通る余地を残す (本 plan の delivery ではないが、Mathlib upstream PR 候補化への布石)

---

## Phase 0 着手判定 (本 plan 用)

| 項目 | 確認 | 判断 |
|---|---|---|
| Polymatroid / Submodular structure 不在 | ✅ 再検証済 | 新規導入 OK |
| Matroid 流儀 mirror 可能性 | ✅ field 流儀確認済 | mirror 採用 |
| `Monotone` 直接利用 | ✅ Mathlib 標準 | `rank_mono : Monotone rank` 採用 |
| `IsSubmodular` class 不在 | ✅ 確認済 | Prop 直書き |
| `[DecidableEq ι]` のみで十分 | ✅ 確認済 | `[Fintype ι]` 不要 |

→ **Phase A skeleton (`Common2026/Polymatroid/Basic.lean` の sorry-driven 出だし) を書ける状態**。

## 全体的な Phase A〜B 工数 (本 plan)

| Phase | 工数 | 行数 |
|---|---|---|
| Phase 0 | 1 ターン | 0 (本 ファイル + plan 反映) |
| Phase A — `Polymatroid` structure 導入 | 0.5 日 | 30〜50 行 (structure + docstring + `attribute [ext]`) |
| Phase B — `entropyPolymatroid` 登録 | 0.5〜1 日 | 30〜50 行 (`def entropyPolymatroid` + 4 axiom 充足) |
| Phase C (オプション) — projection helper | 0〜0.5 日 | 0〜30 行 (`Polymatroid.mono` projection alias など、必要なら) |
| **合計** | **0.5〜1 週間** | **60〜130 行** |

要点: Mathlib に既存物がない以上、structure 自体は新規だが内容は薄い (data 1 + Prop 3)。`entropyPolymatroid` は既存 4 主定理 (`jointEntropySubset_empty` / `jointEntropySubset_mono` / `jointEntropySubset_submodular` (+ `_disjoint_union` は internal helper なので不要)) をそのまま field に流すだけで完成。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。
