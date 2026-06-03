# Polymatroid Structure 化 ムーンショット計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND — Phase A/B 共に完了済 (進捗欄の 📋 は STALE)。`structure Polymatroid` は `InformationTheory/Polymatroid/Basic.lean:34` に存在 (`[DecidableEq ι]` のみ、`rank`/`rank_empty`/`rank_mono`/`rank_submodular`)、`entropyPolymatroid : Combinatorics.Polymatroid (Fin n)` は `InformationTheory/Shannon/Polymatroid.lean:268` で 4 field を既存主定理に wrap (新証明なし)。両ファイル `lake env lean` silent、0 sorry。Phase C はオプションで未着手だが本体 DoD は達成。
> **Status (2026-05-11): 起草。** Polymatroid 主 plan
> ([`polymatroid-moonshot-plan.md`](polymatroid-moonshot-plan.md)) Phase D
> 「(D-b) 別 plan に切り出し」の判断に従って独立 plan として立て直した
> structure 化サブムーンショット。前 plan で 3 性質単発 theorem
> (`jointEntropySubset_empty` / `jointEntropySubset_mono` /
> `jointEntropySubset_submodular`) が `InformationTheory/Shannon/Polymatroid.lean`
> (288 行 / 0 sorry) で立っているのを起点に、`Polymatroid` structure を
> 導入し entropy をその term として登録する。
>
> ゴールは Mathlib 不在の `Polymatroid` structure を InformationTheory に新規導入し、
> 既存 4 主定理を `Polymatroid` の field を充足する形で wrap、
> 「entropy is a polymatroid」を Lean 上の **structure level statement** として
> 表明することである。

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅ → [`polymatroid-structure-mathlib-inventory.md`](polymatroid-structure-mathlib-inventory.md)
- [x] Phase A — `Polymatroid` structure 導入 (`InformationTheory/Polymatroid/Basic.lean:34`) ✅ 実態整合 2026-05-20
- [x] Phase B — `entropyPolymatroid` 登録 (`InformationTheory/Shannon/Polymatroid.lean:268`) ✅ 実態整合 2026-05-20
- [ ] Phase C (オプション) — projection alias / API helper 整備 📋 (未着手、本体 DoD は Phase B で達成)

## ゴール / Approach

**ゴール**: 任意の `ι : Type*` `[DecidableEq ι]` に対し `Polymatroid ι` structure を定義し、`InformationTheory/Shannon/Polymatroid.lean` の `jointEntropySubset` 4 主定理を充足する形で `entropyPolymatroid : Polymatroid (Fin n)` を構成する。

```lean
-- 達成形 (Phase B 後):
noncomputable def entropyPolymatroid
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    Polymatroid (Fin n) where
  rank S := jointEntropySubset μ Xs S
  rank_empty := jointEntropySubset_empty μ Xs
  rank_mono h := jointEntropySubset_mono μ Xs hXs h
  rank_submodular := jointEntropySubset_submodular μ Xs hXs
```

### Approach (戦略の shape)

structure 化の本質は **「既存 4 主定理に新しい証明を付け足さず、wrapper の形で structure projection に乗せ替えるだけ」**。formalism 整理 plan であって新規定理は無し。判断ポイントは **設計の 4 軸** (where / field shape / instance form / API style):

1. **(設計 a) Where** — `InformationTheory/Polymatroid/Basic.lean` (新規ディレクトリ)。Shannon 領域に閉じない構造体 (情報理論専用ではなく組合せ最適化や Matroid 理論との接点) なので、`InformationTheory/Shannon/` から外に出して再利用しやすくする。`InformationTheory/Shannon/Polymatroid.lean` に `entropyPolymatroid` だけ追記。
2. **(設計 b) Field shape** — Mathlib `structure Matroid` を mirror。`structure Polymatroid (ι : Type*) [DecidableEq ι]` で **data 1 (`rank : Finset ι → ℝ`) + Prop 3 (`rank_empty` / `rank_mono` / `rank_submodular`)** を bundle。`rank_mono` は `Monotone rank` (Mathlib 標準、`Finset` の `LE` instance で `S ⊆ T → rank S ≤ rank T` と同値) で 1 行。`Polymatroid` 自体は `class` ではなく **`structure`** (一意の data を持たない構造体、Matroid 同流儀)。
3. **(設計 c) Entropy registration form** — `noncomputable def entropyPolymatroid : Polymatroid (Fin n)` (anonymous constructor `where ... ` 流儀)。`instance` ではなく `def`: Polymatroid は `class` ではなく `structure` なので `instance` 不適、また同じ `Fin n` に複数の polymatroid 構造 (entropy / matroid rank / etc.) が乗りうるので一意性を typeclass で固めるべきでない。
4. **(設計 d) Existing 主定理の扱い** — `jointEntropySubset_*` 4 件は **そのまま残す** (削除 / rename しない)。`entropyPolymatroid` は wrapper に過ぎず、proof の本体は既存定理。projection alias (`Polymatroid.mono` / `Polymatroid.submodular` 等) は **Phase C で必要時のみ追加** (現時点では `pm.rank_mono` / `pm.rank_submodular` の field 名直接アクセスで足りる、追加 API は call site が増えてから)。

ファイル構成 (Phase B 終了時):

```
InformationTheory/
  Polymatroid/
    Basic.lean              ← 新規: structure Polymatroid + 基本 API
  Shannon/
    Polymatroid.lean        ← 既存 (4 主定理) + entropyPolymatroid def 末尾追記
                              import InformationTheory.Polymatroid.Basic を追加
```

`InformationTheory.lean` (library root) に `import InformationTheory.Polymatroid.Basic` を追記 (Shannon.Polymatroid の前)。

### Phase 完了後の API surface

```lean
-- structure 自体
structure Polymatroid (ι : Type*) [DecidableEq ι] where  -- universe annotation 省略 (`Finset ι → ℝ` が `u_1+1` に住むため `: Type` だと universe error)
  rank : Finset ι → ℝ
  rank_empty : rank ∅ = 0
  rank_mono : Monotone rank
  rank_submodular : ∀ S T, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T

-- entropy が polymatroid であることの structure level statement
noncomputable def entropyPolymatroid (μ Xs hXs) : Polymatroid (Fin n)

-- (Phase C オプション) projection alias
@[simp] theorem Polymatroid.rank_mono_iff (pm : Polymatroid ι) {S T} :
    S ⊆ T → pm.rank S ≤ pm.rank T := pm.rank_mono
-- 等
```

## Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅

サブ計画: [`polymatroid-structure-mathlib-inventory.md`](polymatroid-structure-mathlib-inventory.md)

- [x] 軸 1: `Polymatroid` / `Submodular` (集合関数版) structure **再検証** → 不在
- [x] 軸 2: Mathlib `structure Matroid` field 流儀 → mirror 採用
- [x] 軸 3: `Monotone` / `IsSubmodular` 系 → `Monotone` 採用、submodular Prop 直書き
- [x] 軸 4: `[DecidableEq ι]` / `[Fintype ι]` 必要性 → `[DecidableEq ι]` のみ

`Done` 条件: structure 定義 + entropyPolymatroid skeleton が書ける状態 → ✅ 達成。

## Phase A — `Polymatroid` structure 導入 📋

ターゲット: `InformationTheory/Polymatroid/Basic.lean` 新規作成、`structure Polymatroid` を Matroid mirror 流儀で定義。

### スコープ (skeleton)

```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic

/-!
# Polymatroid

A polymatroid is a finite ground set together with a real-valued rank
function on its subsets satisfying three axioms (empty, monotone, submodular).

Mathlib does not (yet) carry a set-function `Polymatroid` / `Submodular`
structure (Matroid rank exists at `ℕ∞`-value, see
`Mathlib.Combinatorics.Matroid.Rank.ENat`); this file introduces the
`ℝ`-valued set-function version, mirroring the field style of
`Mathlib.Combinatorics.Matroid.Basic`.

The canonical example is the joint entropy of a finite collection of
random variables (`InformationTheory.Shannon.entropyPolymatroid` in
`InformationTheory/Shannon/Polymatroid.lean`).
-/

namespace Combinatorics  -- or InformationTheory.Polymatroid; decide in Phase A

/-- A polymatroid is a finite ground set `ι` together with a real-valued
rank function on `Finset ι` satisfying:

* `rank ∅ = 0`               — the empty set has rank 0,
* `Monotone rank`             — rank is monotone in the subset relation,
* submodularity               — `rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T`.

The ground set type `ι` only needs `[DecidableEq ι]` (for `Finset` union /
intersection); finiteness of `ι` itself is not required. -/
structure Polymatroid (ι : Type*) [DecidableEq ι] where  -- universe annotation 省略 (`Finset ι → ℝ` が `u_1+1` に住むため `: Type` だと universe error)
  /-- The real-valued rank function on subsets of the ground set. -/
  rank : Finset ι → ℝ
  /-- The rank of the empty set is zero. -/
  rank_empty : rank ∅ = 0
  /-- The rank function is monotone in the subset relation. -/
  rank_mono : Monotone rank
  /-- The rank function is submodular. -/
  rank_submodular :
    ∀ S T : Finset ι, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T

attribute [local ext] Polymatroid

end Combinatorics
```

### 鍵となる作業

- [ ] **ディレクトリ作成**: `InformationTheory/Polymatroid/` 新規作成 (`mkdir`)
- [ ] **namespace 決定**: `Combinatorics.Polymatroid` / `InformationTheory.Polymatroid` / 単独 `Polymatroid` のどれにするか。Mathlib `Matroid` は **bare `Matroid`** (root namespace) なので、本 plan も **bare `Polymatroid`** または `Combinatorics.Polymatroid` を第 1 候補にする。Phase A 着手時に最終決定 (本 plan のデフォルトは `Combinatorics.Polymatroid`、Mathlib Matroid と同階層 `Combinatorics.*` に揃える)
- [ ] **import policy**: `import Mathlib` 禁止 (CLAUDE.md)。`Mathlib.Data.Finset.Basic` (Finset 自体)、`Mathlib.Order.Monotone.Basic` (Monotone)、`Mathlib.Data.Real.Basic` (ℝ) の 3 本のみ。`lake env lean` で何が足りないか確認しつつ追加
- [ ] **`attribute [ext]`** を付ける (Mathlib Matroid 流儀)。Polymatroid の field 等価性で `ext` tactic が走るように
- [ ] **docstring**: structure 全体 docstring + 各 field docstring (Matroid 流儀)。Mathlib 不在事実 + canonical example へのポインタ (entropyPolymatroid)
- [ ] **`InformationTheory.lean` に `import InformationTheory.Polymatroid.Basic`** を追加 (Shannon.Polymatroid より前の位置)
- [ ] `lake env lean InformationTheory/Polymatroid/Basic.lean` で silent 化

### Done 条件

- `Polymatroid` structure が定義されている
- `lake env lean InformationTheory/Polymatroid/Basic.lean` が silent
- Phase B 着手判定 (entropyPolymatroid 用に必要な field 4 件 + 名前が確定)

### 工数感

0.5 日 (30〜50 行)。新規定理 0、純 structure 定義 + import + namespace 判断のみ。

## Phase B — `entropyPolymatroid` 登録 📋

ターゲット: `InformationTheory/Shannon/Polymatroid.lean` 末尾に `entropyPolymatroid : Polymatroid (Fin n)` を追加。

### スコープ (skeleton)

```lean
-- InformationTheory/Shannon/Polymatroid.lean 末尾追記:

import InformationTheory.Polymatroid.Basic  -- ファイル先頭に追加

namespace InformationTheory.Shannon

/-- Joint entropy as a polymatroid rank function.

The four polymatroid axioms are exactly the four theorems
`jointEntropySubset_empty` / `jointEntropySubset_mono` /
`jointEntropySubset_submodular` (and `Monotone` packaging of the second).

This wraps the existing 主定理 into the `Polymatroid` structure;
the proofs themselves are not duplicated. -/
noncomputable def entropyPolymatroid
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    Combinatorics.Polymatroid (Fin n) where
  rank S := jointEntropySubset μ Xs S
  rank_empty := jointEntropySubset_empty μ Xs
  rank_mono := fun {S T} h => jointEntropySubset_mono μ Xs hXs h
  rank_submodular := jointEntropySubset_submodular μ Xs hXs

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **`import InformationTheory.Polymatroid.Basic`** を `InformationTheory/Shannon/Polymatroid.lean` 先頭に追加 (HanD import の隣)
- [ ] **`Monotone rank` 充足の coersion** — `jointEntropySubset_mono` の signature は
  ```
  {S T : Finset (Fin n)} (h : S ⊆ T) → jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T
  ```
  で、`Monotone (jointEntropySubset μ Xs)` (= `∀ ⦃a b⦄, a ≤ b → ...`) と直接合致する見込み (`Finset` の `≤` は `⊆`)。`Monotone` の implicit binder `⦃ ⦄` と `jointEntropySubset_mono` の implicit binder `{ }` の差異に注意。1 行ラムダ `fun {S T} h => jointEntropySubset_mono μ Xs hXs h` で吸収できる見込み、ハマったら `Monotone.mk` / `fun h => ...` パターンで詰める
- [ ] **`rank_submodular` 充足** — `jointEntropySubset_submodular` の signature が `S T` explicit + `≤` 形で field と直接合致、ラムダ不要見込み
- [ ] **`rank_empty` 充足** — `jointEntropySubset_empty` は `Xs` のみ取る (no `hXs`)、field と直接合致
- [ ] **`entropyPolymatroid` の引数を絞れるか**: `jointEntropySubset_empty` は `hXs` 不要だが他 3 件は必要、`hXs` は def 引数として受ける (4 件で共通の measurability 仮定なので 1 回だけ書く)
- [ ] `lake env lean InformationTheory/Shannon/Polymatroid.lean` で silent 化
- [ ] (smoke test) `#check entropyPolymatroid` で型が正しく `Polymatroid (Fin n)` に解決されることを確認

### Done 条件

- `entropyPolymatroid` が `lake env lean InformationTheory/Shannon/Polymatroid.lean` で silent
- 既存 4 主定理は **無変更** (削除 / signature 変更ナシ)
- Phase A の `Polymatroid` structure が exercise される

### 工数感

0.5〜1 日 (30〜50 行 = `def entropyPolymatroid` + import + docstring)。`Monotone` への coersion で 1 行詰まる程度の覚悟、それ以外は wrapper 写経。

## Phase C (オプション) — projection alias / API helper 整備 📋

### 着手判断のフロー

1. **Phase B 完了時に `entropyPolymatroid.rank_mono` / `.rank_submodular` の直接呼び出しで call site が困っていないか確認**:
   - 困っていない → **(C-skip)** 採用、本 plan は Phase B で close
   - call site で「`Monotone` 形より `S ⊆ T → ...` 形が欲しい」「submodular の symmetric form (`S T` 引数順入替) が欲しい」等のニーズが生じている → (C-add) で API helper 追加
2. **デフォルト**: (C-skip)。Polymatroid の利用先 (Seed 4 / Seed 5 / Sanov / etc.) が立ち上がるまで API helper を premature に増やさない。

### スコープ (C-add 採用時のみ)

```lean
namespace Combinatorics.Polymatroid

variable {ι : Type*} [DecidableEq ι] (pm : Polymatroid ι)

/-- Subset form of monotonicity (alias for `pm.rank_mono`). -/
theorem rank_le_of_subset {S T : Finset ι} (h : S ⊆ T) : pm.rank S ≤ pm.rank T :=
  pm.rank_mono h

/-- Symmetric form of submodularity (`S` and `T` swapped). -/
theorem rank_submodular' (S T : Finset ι) :
    pm.rank (T ∪ S) + pm.rank (T ∩ S) ≤ pm.rank T + pm.rank S := by
  rw [Finset.union_comm, Finset.inter_comm]; exact pm.rank_submodular S T

-- Phase D / 後続 plan で必要に応じて追加: rank_nonneg, rank_le_card, etc.

end Combinatorics.Polymatroid
```

### Done 条件 (C-add 採用時)

- 各 helper が silent
- 不採用なら判断ログに「(C-skip) で close」と記録

### 工数感

C-add なら 0.5 日 (10〜30 行)。C-skip なら 0 日 (判断ログ + close)。

## 失敗判定 / 撤退ライン

- **Phase A namespace 判断で 1 ターン以上溶ける** → `bare Polymatroid` (root namespace) で固定。Mathlib `Matroid` 流儀を最も近く mirror できる
- **Phase B `Monotone` coersion でハマる** → `rank_mono` field を `Monotone rank` から `∀ {S T : Finset ι}, S ⊆ T → rank S ≤ rank T` の直接 Prop 形に変更。Mathlib `Monotone` API との連携性は落ちるが、本 plan の delivery は変わらない
- **`Polymatroid` namespace 衝突** (Mathlib に同名が将来追加された) → `InformationTheory.Polymatroid` に rename。本 plan の影響はファイル先頭の `namespace` 1 行のみ
- **`InformationTheory/Polymatroid/Basic.lean` の import policy 違反** (`import Mathlib` を入れてしまう) → `Mathlib.Data.Finset.Basic` / `Mathlib.Order.Monotone.Basic` / `Mathlib.Data.Real.Basic` の 3 本に絞る。`lake env lean` で silent 化を確認
- **既存 4 主定理の signature 変更が必要に見える** → やめる。本 plan は wrapper plan なので既存定理は不変。`entropyPolymatroid` 側を field shape に合わせるラムダで吸収。signature 変更が本当に必要なら別の refactor plan に切り出す
- **Phase B 完了時点で「polymatroid structure が wrapper 以上の価値を持っていない」と判断** → 本 plan を撤退、`entropyPolymatroid` を削除して既存 4 主定理だけ残す。proof-log で「structure 化は次 polymatroid 利用先 (Sanov / matroid 理論) が立ち上がってから再評価」と記録

## Definition of Done (本 plan 全体)

- `InformationTheory/Polymatroid/Basic.lean` が新規作成、`structure Polymatroid` 定義済、`lake env lean InformationTheory/Polymatroid/Basic.lean` silent
- `InformationTheory/Shannon/Polymatroid.lean` に `entropyPolymatroid` 追加、`lake env lean InformationTheory/Shannon/Polymatroid.lean` silent
- 既存 4 主定理 (`jointEntropySubset_empty` / `jointEntropySubset_mono` / `jointEntropySubset_disjoint_union` / `jointEntropySubset_submodular`) は **無変更**
- `InformationTheory.lean` に `import InformationTheory.Polymatroid.Basic` 追加
- `lake build InformationTheory.Polymatroid.Basic` + `lake build InformationTheory.Shannon.Polymatroid` 緑通過
- (Phase C オプション採用時) projection alias 群が silent

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。
