# Hypercube edge-boundary (B-2') ムーンショット計画 🌙

> オーケストレータ指示: 既存 B-2 (`hypercube_product_projection_bound` singleton-cover 形) を
> 起点に、Boolean cube `Fin n → Bool` 上の **edge-boundary 形 isoperimetric bound** を
> 一段組合せ寄りに publish。Han-Bregman 流の「内辺数 = LW projection の和との恒等式」と
> Loomis–Whitney + AM-GM の合わせ技で、`SimpleGraph.edgeBoundary` を持ち込まずに完結。

## Status / 目標

deferred `B-2'`. 主目標は以下 3 件:

1. **Edge boundary count `edgeBoundaryCount A`** を独自定義 (Mathlib に `SimpleGraph.edgeBoundary` 既存なし、`Sym2` 回避)。
2. **Counting identity `edgeBoundary_count_eq`**: `|∂_e A| = 2 Σ_i |π_{≠i}(A)| - n · |A|`。
3. **AM-GM 型 edge isoperimetric bound `edgeBoundary_ge_AMGM`**: `|∂_e A| ≥ 2n · |A|^((n-1)/n) - n · |A|`。

副目標: `2 · internal + |∂_e| = n · |A|` の identity を `internal_edges_eq` として publish (counting identity の途中段)。

## Approach

**全体方針**: Boolean cube に `SimpleGraph` 構造を載せて `edgeBoundary`-style Sym2 操作を行うのは,
Mathlib 上流側の API gap (graph 自体は無いが LW projection の `Finset.image` は完備) と
比較してコスト過多。代わりに **directed edge / coordinate flip** で edge boundary を組合せ的に
counts し、entropy 経由ではなく `loomis_whitney` の純粋な代数 corollary として
isoperimetric bound を出す。

**鍵となる恒等式** (Bool case): 各 `i : Fin n` で `A` を `i`-coord で `A_{i,0} ⊔ A_{i,1}` に分割すると,
`|π_{≠i}(A)| = |A| - |D_i|` (`D_i` = doubly-covered fibres in direction `i`) なので,
`|D_i| = |A| - |π_{≠i}(A)|`、`internal edges in direction i = |D_i|`、
`boundary edges in direction i = |A| - 2|D_i|`。

- `Σ_i (internal edges in direction i) = n|A| - Σ_i |π_{≠i}(A)|`
- `|∂_e A| = Σ_i (boundary edges in direction i) = Σ_i (|A| - 2|D_i|) = -n|A| + 2 Σ_i |π_{≠i}(A)|`

AM-GM (`Real.inner_le_nnreal_inner_self` でなく `pow_arith_mean_le_arith_mean_pow`) を `(|π_{≠i}(A)|)_{i}` に適用すると, LW (`|A|^{n-1} ≤ ∏ |π_{≠i}(A)|`) と組み合わせて `Σ_i |π_{≠i}(A)| ≥ n · |A|^{(n-1)/n}` を得るので, **counting identity + LW + AM-GM** で edge bound が出る。

**entropy-sharp 形** (`|∂_e A| ≥ |A| (n - log₂|A|)`) は **B-2'' deferred** に再切り出し:
`condEntropy μ X_i X_{≠i} = (2|D_i|/|A|) · log 2` の bridge が ~80-120 行追加、独立着手で着手判断する。

## Phase 0 — Mathlib API inventory ✅

**loogle / rg 結果**:

- `SimpleGraph.edgeBoundary` — **Mathlib に存在しない** (loogle で `unknown identifier`)。
- `SimpleGraph.boxProd` — `Mathlib/Combinatorics/SimpleGraph/Prod.lean:43` に存在: `def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β)`。binary product のみ、n-fold は無し。
- `Mathlib.InformationTheory.Hamming` — metric space `Hamming` (`hammingDist`, `hammingNorm`) は存在するが **graph 構造はなし**。
- `SimpleGraph.completeGraph` — `Mathlib/Combinatorics/SimpleGraph/Basic.lean` に存在 (`completeGraph α : SimpleGraph α`)。
- `SimpleGraph.incidenceFinset` / `edgeFinset` — `Mathlib/Combinatorics/SimpleGraph/Finite.lean` に基本 API あり。
- **`Function.update`** (`Mathlib/Logic/Function/Defs.lean`) — coord flip に使用、bool 限定で `!` (`Bool.not`) と組み合わせる。

**判断**: SimpleGraph 構造に乗せると `Sym2` 経由の edge handling が増えるため, **directed pair `(x, i)` で counts する素朴な定義**を採用 (boundary edge `{x, x ⊕ e_i}` は `x ∈ A`, `x ⊕ e_i ∉ A` の唯一の `x` で代表される → unordered count に一致)。

**既存 Common2026 補題で再利用予定**:

- `InformationTheory.Shannon.loomis_whitney` (`LoomisWhitney.lean:351`) — `A.card ^ (n-1) ≤ ∏ i, (projectionExcept i A).card`。
- `InformationTheory.Shannon.projectionExcept` (`LoomisWhitney.lean:263`) — `(j : {j // j ≠ i}) → α` 値 projection.
- `Real.rpow_natCast`, `Real.rpow_le_rpow_left_iff_of_base_lt_one` — AM-GM 後段 castで使用見込み。

## Phase A — `edgeBoundaryCount` / `internalEdgeCount` 定義 + identity ✅

新規 `Common2026/Shannon/HypercubeEdgeBoundary.lean`:

- [x] `def edgeBoundaryCount (A : Finset (Fin n → Bool)) : ℕ` — `(x, i)` 対の数で `x ∈ A`, `flipCoord i x ∉ A` を満たすもの。
- [x] `def internalEdgePairCount (A : Finset (Fin n → Bool)) : ℕ` — `(x, i)` 対で `x ∈ A`, `flipCoord i x ∈ A`。`internal edges × 2` に等しい (各 unordered internal edge は両端点で 2 回 counts)。
- [x] **Theorem `edge_total_count`**: `edgeBoundaryCount A + internalEdgePairCount A = n * A.card`。`(x, i)` 対は `x ∈ A` の場合に限り両 disjoint case のいずれかに属する。`Finset.card_union_of_disjoint` + `A.product Finset.univ` 経由で `S.card = n * A.card`。
- [x] **Theorem `two_sum_projection_eq`** (key counting identity): `2 * Σ_i (projectionExcept i A).card = n * A.card + edgeBoundaryCount A`。各 `i` で fibre size ∈ {1,2} 分類 (`Finset.card_eq_sum_card_fiberwise`) + 4-case 結合 (両 extension の `A` 帰属) で proof。
- [x] **Theorem `internal_pair_count_eq_projection_sum`**: `internalEdgePairCount A + 2 * Σ_i (projectionExcept i A).card = 2 * (n * A.card)`。上 2 件の `omega` corollary。
- [x] **Theorem `edgeBoundary_count_eq`**: `edgeBoundaryCount A + n * A.card = 2 * Σ_i (projectionExcept i A).card` (整数差を `+` で回避)。

## Phase B — LW + AM-GM corollary ✅

- [x] **Theorem `sum_projection_card_ge_amgm`**: `(n : ℝ) * (A.card : ℝ)^((n-1)/n) ≤ Σ_i ((projectionExcept i A).card : ℝ)` (`x ^ ((n : ℝ)⁻¹)` 形)。LW (`loomis_whitney` cast to ℝ) + AM-GM (`Real.geom_mean_le_arith_mean_weighted` with `w := 1/n`) + `Real.finsetProd_rpow` で `∏ z_i^(1/n) = (∏ z_i)^(1/n)`。
- [x] **Theorem `edgeBoundary_ge_AMGM`** (主結果): for nonempty `A`:
  `2 * (n : ℝ) * (A.card : ℝ)^((n-1)/n) ≤ (edgeBoundaryCount A : ℝ) + n * A.card` (= `|∂_e A| ≥ 2n |A|^{(n-1)/n} - n |A|`)。
  `edgeBoundary_count_eq` を ℝ に push + `sum_projection_card_ge_amgm` を `× 2` で結合。

## Phase C — Boolean cube graph structure note 🔄 (見送り、上流 PR 候補)

`booleanHypercubeGraph : SimpleGraph (Fin n → Bool)` は **publish せず**, `Approach` 節記載のとおり `edgeBoundaryCount` の組合せ的定義のみで完結。`SimpleGraph` 経路の `edgeBoundary` 形は B-2''/上流 Mathlib PR で扱う想定。

## 見積行数 / 検証条件

- 行数見積: 200〜300 行 (Phase A 定義 + 2 identity ~120 行, Phase B AM-GM corollary ~80 行, ヘッダ + namespace)。
- 検証: `lake env lean Common2026/Shannon/HypercubeEdgeBoundary.lean` silent (0 sorry / 0 error)。
- `Common2026.lean` に `import Common2026.Shannon.HypercubeEdgeBoundary` 追記。

## 判断ログ

1. **Phase 0 起草時**: `SimpleGraph.edgeBoundary` が Mathlib に無いことを loogle で確認 (`unknown identifier`)。`SimpleGraph.boxProd` (`Mathlib/Combinatorics/SimpleGraph/Prod.lean:43`) は binary product のみで n-fold への昇格に追加 ~150 行が必要。SimpleGraph 構造に乗せると `Sym2` 経由で edge handling が重くなるため, **directed coordinate-flip pair で counts する素朴な定義**を採用。
2. **entropy-sharp 形 (`|∂_e A| ≥ |A|(n - log₂|A|)`) 見送り**: `condEntropy μ X_i X_{≠i}` を Boolean fibre count に bridge する補題が独立 ~80-120 行で, B-2' 本体 (AM-GM corollary) と独立。B-2'' deferred に再切り出し、本 plan は **counting identity + LW + AM-GM** に絞る。
3. **Phase A 4-case 結合**: 各 `y ∈ projectionExcept i A` で `2 = (A.filter ... = y).card + (bdir.filter ... = y).card` を示すのに, `(extension i false y ∈ A) × (extension i true y ∈ A)` の 4 case 結合が最も clean (両方 ∈ A / 一方のみ ∈ A の 2 case)。`Finset.disjoint_filter_filter` で singleton-filter 間の disjoint 性を `Finset.disjoint_singleton` 経由で渡す。`Finset.card_union_of_disjoint` を 2 回適用 + 各 4 filter set の equality を `show ... from by ...` で局所宣言 + `simp [Finset.card_singleton]` で締める, ~110 行。

## 実装結果サマリ

- **行数**: 692 行 (`Common2026/Shannon/HypercubeEdgeBoundary.lean`)。Phase 0 inventory 完了 + 4 helper def (`flipCoord`, `projMap`, `extension`, `boundaryDirSet`) + 3 main theorem (`edge_total_count`, `two_sum_projection_eq`, `edgeBoundary_ge_AMGM`) + 2 補題 (`edgeBoundary_count_eq`, `internal_pair_count_eq_projection_sum`) + AM-GM corollary `sum_projection_card_ge_amgm`。
- **graph 構造**: `SimpleGraph` 一切使わず, `(Fin n → Bool) × Fin n` 上の predicate `p.1 ∈ A ∧ flipCoord p.2 p.1 ∉ A` で edge boundary を組合せ的に publish。
- **主補題 signature**:
  ```
  theorem edgeBoundary_ge_AMGM {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
      2 * (n : ℝ) * ((A.card : ℝ) ^ (n - 1 : ℕ)) ^ ((n : ℝ)⁻¹)
        ≤ (edgeBoundaryCount A : ℝ) + n * A.card
  ```
  整数差を `+` で回避する形 (`|∂_e A| ≥ 2n |A|^{(n-1)/n} - n |A|` に等価)。
- **検証**: `lake env lean Common2026/Shannon/HypercubeEdgeBoundary.lean` silent (0 sorry / 0 error / 0 warning)。
- **Mathlib 上流 PR 切り出し可能性**: 中程度。`edgeBoundaryCount` の `SimpleGraph.edgeBoundary` 形への昇格は別 PR で着手すべき (n-fold `boxProd` of `K_2` で Boolean cube graph を構成 → `edgeBoundary` API を独立 PR、~150-250 行)。本 plan の `edgeBoundary_ge_AMGM` 等は Mathlib の `Combinatorics/Isoperimetric` 系新規ファイル候補。entropy-sharp 形 (B-2'') は独立 PR で着手判断。
