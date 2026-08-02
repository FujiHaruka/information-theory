# 補助変数の基数境界 — Mathlib / in-project 在庫

> **Parent**: [`bc-open-problem-t3-plan.md`](bc-open-problem-t3-plan.md)

前提となる棚卸し: [`bc-t3-lean-inventory.md`](bc-t3-lean-inventory.md) §4 / §5。

本書の §1–§5 は**逐語**（`#check` で elaborate した署名、loogle の出力、`rg` の出力、
`scripts/dep_consumers.sh` の出力）に限る。そこから導いた判断は §6 にのみ書く。

環境: Mathlib rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (2026-06-15)、
loogle index は同 checkout に対して構築済 (`.lake/build/loogle.index`)。

---

## 一行サマリ

**Carathéodory 本体・アフィン独立から基数への橋・単体のコンパクト性は Mathlib に全部在り、
測度↔単体点の座標化と情報量の連続性は in-project に既に在る (`entropy` の定義がそもそも
`∑ negMulLog` のベクトル形)。無いのは Fenchel–Eggleston (連結版) と「測度 ↔ `stdSimplex`」の
同一視で、前者は本件に不要。⟹ gate は COSTLY (壁ではない)。**

⚠ ただし最大の危険は Lean 側ではない — §6.4 を見よ。

---

## §1 Mathlib の Carathéodory 一式（逐語）

出典ファイル: `.lake/packages/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean`（全 187 行、
`@[expose] public section` 配下なので**下記 9 本がこのファイルの公開宣言の全部**）。

共通の `variable` ブロック（`Caratheodory.lean:48-49`、逐語）:

```lean
variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
```

⚠ **位相も内積もノルムも要らない**（`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
[AddCommGroup E] [Module 𝕜 E]` のみ）。有限次元性も要らない。

| # | decl | file:line | 種別 |
|---|---|---|---|
| 1 | `Caratheodory.mem_convexHull_erase` | `Mathlib/Analysis/Convex/Caratheodory.lean:55` | theorem |
| 2 | `Caratheodory.minCardFinsetOfMemConvexHull` | 同 `:107` | noncomputable def |
| 3 | `Caratheodory.minCardFinsetOfMemConvexHull_subseteq` | 同 `:113` | theorem |
| 4 | `Caratheodory.mem_minCardFinsetOfMemConvexHull` | 同 `:116` | theorem |
| 5 | `Caratheodory.minCardFinsetOfMemConvexHull_nonempty` | 同 `:120` | theorem |
| 6 | `Caratheodory.minCardFinsetOfMemConvexHull_card_le_card` | 同 `:124` | theorem |
| 7 | `Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull` | 同 `:128` | theorem |
| 8 | `convexHull_eq_union` | 同 `:149` | theorem（**Carathéodory 本体**） |
| 9 | `eq_pos_convex_span_of_mem_convexHull` | 同 `:162` | theorem |

### 1.1 完全署名（`#check @…` の逐語出力）

```
@Caratheodory.mem_convexHull_erase : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] [inst_5 : DecidableEq E] {t : Finset E},
  ¬AffineIndependent 𝕜 Subtype.val → ∀ {x : E}, x ∈ (convexHull 𝕜) ↑t → ∃ y, x ∈ (convexHull 𝕜) ↑(t.erase ↑y)
```

```
@Caratheodory.minCardFinsetOfMemConvexHull : {𝕜 : Type u_2} →
  {E : Type u_1} →
    [inst : Field 𝕜] →
      [inst_1 : LinearOrder 𝕜] →
        [IsStrictOrderedRing 𝕜] →
          [inst_3 : AddCommGroup E] → [inst_4 : Module 𝕜 E] → {s : Set E} → {x : E} → x ∈ (convexHull 𝕜) s → Finset E
```

```
@Caratheodory.minCardFinsetOfMemConvexHull_subseteq : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜]
  [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E}
  {x : E} (hx : x ∈ (convexHull 𝕜) s), ↑(Caratheodory.minCardFinsetOfMemConvexHull hx) ⊆ s
```

```
@Caratheodory.mem_minCardFinsetOfMemConvexHull : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜]
  [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E}
  {x : E} (hx : x ∈ (convexHull 𝕜) s), x ∈ (convexHull 𝕜) ↑(Caratheodory.minCardFinsetOfMemConvexHull hx)
```

```
@Caratheodory.minCardFinsetOfMemConvexHull_nonempty : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜]
  [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E}
  {x : E} (hx : x ∈ (convexHull 𝕜) s), (Caratheodory.minCardFinsetOfMemConvexHull hx).Nonempty
```

```
@Caratheodory.minCardFinsetOfMemConvexHull_card_le_card : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜]
  [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E}
  {x : E} (hx : x ∈ (convexHull 𝕜) s) {t : Finset E},
  ↑t ⊆ s → x ∈ (convexHull 𝕜) ↑t → (Caratheodory.minCardFinsetOfMemConvexHull hx).card ≤ t.card
```

```
@Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜]
  [inst_1 : LinearOrder 𝕜] [inst_2 : IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E}
  {x : E} (hx : x ∈ (convexHull 𝕜) s), AffineIndependent 𝕜 Subtype.val
```

```
@convexHull_eq_union : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E},
  (convexHull 𝕜) s = ⋃ t, ⋃ (_ : ↑t ⊆ s), ⋃ (_ : AffineIndependent 𝕜 Subtype.val), (convexHull 𝕜) ↑t
```

```
@eq_pos_convex_span_of_mem_convexHull : ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : Module 𝕜 E] {s : Set E} {x : E},
  x ∈ (convexHull 𝕜) s →
    ∃ ι x_1 z w,
      Set.range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ (i : ι), (0 : 𝕜) < w i) ∧ ∑ i, w i = (1 : 𝕜) ∧ ∑ i, w i • z i = x
```

ソース側の逐語（`Caratheodory.lean:162-165`、`#check` が `∃ ι x_1 z w` と潰した部分の原文）:

```lean
theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜), Set.range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x
```

### 1.2 ⚠ Carathéodory 本体は「`d+1` 点」を**直接は言っていない**

`convexHull_eq_union` / `eq_pos_convex_span_of_mem_convexHull` の結論に現れるのは
`AffineIndependent 𝕜 z` であって `Fintype.card ι ≤ d + 1` ではない。基数へ落とす橋は別ファイルに在る:

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| アフィン独立 ⟹ 点数 ≤ 次元 + 1 | `AffineIndependent.card_le_finrank_succ` | `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:245` | ✅ 既存 |

```
@AffineIndependent.card_le_finrank_succ : ∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} {ι : Type u_4}
  [inst : DivisionRing k] [inst_1 : AddCommGroup V] [inst_2 : Module k V] [inst_3 : AddTorsor V P] [inst_4 : Fintype ι]
  {p : ι → P}, AffineIndependent k p → Fintype.card ι ≤ Module.finrank k ↥(vectorSpan k (Set.range p)) + (1 : ℕ)
```

⟹ `eq_pos_convex_span_of_mem_convexHull` が返す `⟨ι, _, z, w, _, hAI, …⟩` の `hAI` にこれを当てると
`Fintype.card ι ≤ finrank 𝕜 (vectorSpan 𝕜 (range z)) + 1` が出る。周囲空間が `V₂ × α → ℝ` などの
有限次元なら `finrank ≤ Fintype.card (V₂ × α)` で押さえられる。**「`d+1` 点版 Carathéodory」は
この 2 本の合成で得られ、Mathlib 内に閉じている。**

再検証コマンドと出力（結論形での検索、`|- Fintype.card _ ≤ _` 系）:

```
$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "AffineIndependent, Fintype.card"
Found 11 declarations mentioning AffineIndependent and Fintype.card.
（11 本すべて Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional 由来、うち基数の上界を結論に持つのは
 AffineIndependent.card_le_finrank_succ の 1 本）
```

```
$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "convexHull, Module.finrank"
Found one declaration mentioning convexHull and Module.finrank.
exists_mem_interior_convexHull_affineBasis (from Mathlib.Analysis.Normed.Affine.Convex)
```

⟹ **`convexHull` と次元を直接結ぶ補題は Mathlib に 1 本しかなく、それは内点の存在についてで
基数境界ではない。基数へは `AffineIndependent` を経由するしかない。**

---

## §2 Fenchel–Eggleston（連結版 Carathéodory）— **Mathlib に無い**

### 2.1 一段目: 名前・語での探索

```
$ rg -n -i 'eggleston' .lake/packages/mathlib/Mathlib/
（ヒットなし）
$ rg -n -i 'fenchel' .lake/packages/mathlib/Mathlib/
（ヒットなし）
```

（同じ `rg` 呼び出しで `-i 'caratheodory|carathéodory'` は 20 ファイル超にヒットするので、
コマンド自体は機能している。）

loogle:

```
$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "IsConnected, convexHull"
Found 0 declarations mentioning IsConnected and convexHull.

$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "IsPreconnected, convexHull"
Found 0 declarations mentioning convexHull and IsPreconnected.

$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "IsCompact, convexHull, AffineIndependent"
Found 0 declarations mentioning AffineIndependent, convexHull, and IsCompact.
```

### 2.2 二段目 (a): 結論形での再検索

⚠ CLAUDE.md「壁を宣言するとき」の要求どおり、識別子ではなく結論パターンで引き直す。

```
$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "|- _ ∈ convexHull _ _"
Found 58 declarations mentioning ChainCompletePartialOrder.instOfCompleteLattice, PartialOrder.toPreorder, Membership.mem,
ClosureOperator.instFunLike, ClosureOperator, ChainCompletePartialOrder.toPartialOrder, convexHull,
CompleteBooleanAlgebra.toCompleteLattice, Set.instMembership, DFunLike.coe,
CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra, Set.instCompleteAtomicBooleanAlgebra, and Set.
Of these, 11 match your pattern(s).

Finset.centroid_mem_convexHull (from Mathlib.Analysis.Convex.Combination)
Finset.centerMass_id_mem_convexHull (from Mathlib.Analysis.Convex.Combination)
Finset.centerMass_id_mem_convexHull_of_nonpos (from Mathlib.Analysis.Convex.Combination)
Finset.centerMass_mem_convexHull (from Mathlib.Analysis.Convex.Combination)
Finset.centerMass_mem_convexHull_of_nonpos (from Mathlib.Analysis.Convex.Combination)
mem_convexHull_of_exists_fintype (from Mathlib.Analysis.Convex.Combination)
mem_convexHull_pi (from Mathlib.Analysis.Convex.Combination)
affineCombination_mem_convexHull (from Mathlib.Analysis.Convex.Combination)
mk_mem_convexHull_prod (from Mathlib.Analysis.Convex.Combination)
Caratheodory.mem_minCardFinsetOfMemConvexHull (from Mathlib.Analysis.Convex.Caratheodory)
IsVisible.mem_convexHull_isVisible (from Mathlib.Analysis.Convex.Visible)
```

⟹ **凸包メンバシップを結論に持つ Mathlib 補題 11 本のうち、集合の連結性を仮定に使うものは 0 本**
（`IsVisible.mem_convexHull_isVisible` は可視性であって連結性ではない）。
§2.1 の 0-hit は名前の付け方の問題ではない。

### 2.3 二段目 (b): 自己構築の見積り

テンプレート補題の指名: **`convexHull_eq_union`（`Caratheodory.lean:149`）+
`Caratheodory.mem_convexHull_erase`（同 `:55`）**。標準版から連結版を導くには、

1. `x` が `d+1` 点のアフィン独立な凸結合であるところまでは `convexHull_eq_union` で到達する。
2. そこから 1 点落とすには「`s` が連結なら、`x` を通る超平面が `s` を 2 つの弧に切り、
   一方の弧上の `d` 点で `x` を表せる」という**位相の議論**が要る。`mem_convexHull_erase` の
   アフィン従属性を使った消去とは別の機構であり、Mathlib に部品が無い（§2.2）。
3. 中間値定理 (`intermediate_value_Icc` 系) と `IsPreconnected.subset_or_subset` を土台に
   自作する形になる。

⚠ **我々の見積り**: **150–250 行**（連結成分の分離補題 + 超平面パラメータ化 + `d+1 → d` の
消去ステップ）。標準版 Carathéodory（`Caratheodory.lean` の実装本体、行 53–187 で約 135 行）と
同程度かやや重い。

### 2.4 ⚠ 最重要の判断 — 本件に Fenchel–Eggleston は**要らない**

⚠ **我々の演繹**（在庫ではなく論理。根拠 3 行）:

1. Fenchel–Eggleston が標準 Carathéodory に対して改善するのは**点数を `d+1` から `d` に
   下げる**ことだけで、「有限の上界が存在するか」は両者で変わらない。
2. 我々の目的は `⋃ (k₁ k₂ : ℕ)` を**ある有限の `N` まで**に切り詰めることであって、
   `N` の最小値を出すことではない（`martonRegionUnion` は closure かつ lower set なので、
   どんな有限 `N` でも領域の同一性は同じ強さで言える）。
3. ⟹ **gate は Fenchel–Eggleston の有無に依存しない。** §1 の
   `convexHull_eq_union` + `AffineIndependent.card_le_finrank_succ` で使える `N` が出る。

⚠ **したがって本書は Fenchel–Eggleston を `wall:` として起票しない**。「Mathlib に無い」は
§2.1–2.3 で確定した事実だが、本件の gate に対しては**不要な補題**なので壁ではない。
（定数を教科書と一致させたい場合にのみ 150–250 行の自作が要る。）

---

## §3 support lemma を組むのに要る周辺資産（Mathlib）

### 3.1 `Finset.centerMass` / 凸結合の出し入れ — **全部在る**

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 重心が凸包に入る | `Finset.centerMass_mem_convexHull` | `Mathlib/Analysis/Convex/Combination.lean:253` | ✅ |
| 同（添字が集合自身） | `Finset.centerMass_id_mem_convexHull` | 同 `:266` | ✅ |
| 凸包メンバの有限型分解（⟺） | `mem_convexHull_iff_exists_fintype` | 同 `:378` | ✅ |
| 同（宇宙多相な逆向き） | `mem_convexHull_of_exists_fintype` | 同 `:367` | ✅ |
| 弱 Carathéodory（有限部分集合の合併） | `convexHull_eq_union_convexHull_finite_subsets` | 同 `:429` | ✅ |
| `Finset` 版メンバシップ（重み形） | `Finset.mem_convexHull'` | 同 `:415` | ✅ |

```
@Finset.centerMass_mem_convexHull : ∀ {R : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Field R]
  [inst_1 : AddCommGroup E] [inst_2 : Module R E] {s : Set E} [inst_3 : LinearOrder R] [IsStrictOrderedRing R]
  (t : Finset ι) {w : ι → R},
  (∀ i ∈ t, (0 : R) ≤ w i) →
    (0 : R) < ∑ i ∈ t, w i → ∀ {z : ι → E}, (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ (convexHull R) s
```

```
@mem_convexHull_iff_exists_fintype : ∀ {R : Type u_1} {E : Type u_2} [inst : Field R] [inst_1 : AddCommGroup E]
  [inst_2 : Module R E] [inst_3 : LinearOrder R] [IsStrictOrderedRing R] {s : Set E} {x : E},
  x ∈ (convexHull R) s ↔
    ∃ ι x_1 w z, (∀ (i : ι), (0 : R) ≤ w i) ∧ ∑ i, w i = (1 : R) ∧ (∀ (i : ι), z i ∈ s) ∧ ∑ i, w i • z i = x
```

ソース側逐語（`Combination.lean:378-380`、`#check` が潰した束縛子の原文）:

```lean
lemma mem_convexHull_iff_exists_fintype {s : Set E} {x : E} :
    x ∈ convexHull R s ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → R) (z : ι → E), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x
```

```
@mem_convexHull_of_exists_fintype : ∀ {R : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Field R]
  [inst_1 : AddCommGroup E] [inst_2 : Module R E] [inst_3 : LinearOrder R] [IsStrictOrderedRing R] {s : Set E} {x : E}
  [inst_5 : Fintype ι] (w : ι → R) (z : ι → E),
  (∀ (i : ι), (0 : R) ≤ w i) → ∑ i, w i = (1 : R) → (∀ (i : ι), z i ∈ s) → ∑ i, w i • z i = x → x ∈ (convexHull R) s
```

```
@convexHull_eq_union_convexHull_finite_subsets : ∀ {R : Type u_1} {E : Type u_2} [inst : Field R]
  [inst_1 : AddCommGroup E] [inst_2 : Module R E] [inst_3 : LinearOrder R] [IsStrictOrderedRing R] (s : Set E),
  (convexHull R) s = ⋃ t, ⋃ (_ : ↑t ⊆ s), (convexHull R) ↑t
```

```
@Finset.mem_convexHull' : ∀ {R : Type u_1} {E : Type u_2} [inst : Field R] [inst_1 : AddCommGroup E]
  [inst_2 : Module R E] [inst_3 : LinearOrder R] [IsStrictOrderedRing R] {s : Finset E} {x : E},
  x ∈ (convexHull R) ↑s ↔ ∃ w, (∀ y ∈ s, (0 : R) ≤ w y) ∧ ∑ y ∈ s, w y = (1 : R) ∧ ∑ y ∈ s, w y • y = x
```

### 3.2 有限型上の測度を凸結合として書く — **積分側は在る / 「測度 ↔ `stdSimplex`」の同一視は無い**

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| Bochner 積分 = 単体点との内積 | `MeasureTheory.integral_fintype` | `Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean:209` | ✅ |
| Lebesgue 積分の有限和形 | `MeasureTheory.lintegral_fintype` | `Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean:153` | ✅ |
| `Measure α` (α 有限) ↔ `stdSimplex ℝ α` の同一視 | — | — | ❌ **不在** |

```
@MeasureTheory.integral_fintype : ∀ {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]
  {f : X → E} [inst_1 : NormedSpace ℝ E] [CompleteSpace E] [MeasurableSingletonClass X] {μ : MeasureTheory.Measure X}
  [inst_4 : Fintype X], MeasureTheory.Integrable f μ → ∫ (x : X), f x ∂μ = ∑ x, μ.real {x} • f x
```

```
@MeasureTheory.lintegral_fintype : ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
  [MeasurableSingletonClass α] [inst_2 : Fintype α] (f : α → ENNReal), ∫⁻ (x : α), f x ∂μ = ∑ x, f x * μ {x}
```

不在の再検証コマンドと出力:

```
$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "MeasureTheory.ProbabilityMeasure, stdSimplex"
Found 0 declarations mentioning MeasureTheory.ProbabilityMeasure and stdSimplex.

$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "PMF, stdSimplex"
Found 0 declarations mentioning PMF and stdSimplex.

$ ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "convexHull, MeasureTheory.Measure"
Found 0 declarations mentioning MeasureTheory.Measure and convexHull.
```

⟹ **Mathlib の凸幾何と測度論は接続されていない。**「有限型上の確率測度を単体の点として扱う」
座標化は自作（または in-project 資産の再利用 → §4.3）になる。

### 3.3 単体のコンパクト性・凸性・連結性 — **全部在る**

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 標準単体 | `stdSimplex` | `Mathlib/Analysis/Convex/StdSimplex.lean`（def） | ✅ |
| 凸性 | `convex_stdSimplex` | `Mathlib/Analysis/Convex/StdSimplex.lean:42` | ✅ |
| コンパクト性 | `isCompact_stdSimplex` | 同 `:189` | ✅ |
| 弧状連結性 | `isPathConnected_stdSimplex` | 同 `:217` | ✅ |
| 凸 ⟺ 連結（ℝ 上） | `Real.convex_iff_isPreconnected` | `Mathlib/Analysis/Convex/Topology.lean:44` | ✅ |
| `ProbabilityMeasure E` のコンパクト性 | `instCompactSpaceProbabilityMeasure` | `Mathlib/MeasureTheory/Measure/Prokhorov.lean` | ✅ |

```
stdSimplex : (𝕜 : Type u_2) → (ι : Type u_1) → [Semiring 𝕜] → [PartialOrder 𝕜] → [Fintype ι] → Set (ι → 𝕜)
```

```
convex_stdSimplex : ∀ (𝕜 : Type u_2) (ι : Type u_1) [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : Fintype ι]
  [IsOrderedRing 𝕜], Convex 𝕜 (stdSimplex 𝕜 ι)
```

```
isCompact_stdSimplex : ∀ (𝕜 : Type u_1) (ι : Type u_2) [inst : Fintype ι] [inst_1 : TopologicalSpace 𝕜]
  [inst_2 : Semiring 𝕜] [inst_3 : PartialOrder 𝕜] [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜] [CompactIccSpace 𝕜]
  [IsOrderedAddMonoid 𝕜], IsCompact (stdSimplex 𝕜 ι)
```

```
isPathConnected_stdSimplex : ∀ (ι : Type u_1) [inst : Fintype ι] [Nonempty ι], IsPathConnected (stdSimplex ℝ ι)
```

```
@Real.convex_iff_isPreconnected : ∀ {s : Set ℝ}, Convex ℝ s ↔ IsPreconnected s
```

```
@instCompactSpaceProbabilityMeasure : ∀ {E : Type u_1} [inst : MeasurableSpace E] [inst_1 : TopologicalSpace E]
  [T2Space E] [inst_3 : BorelSpace E] [CompactSpace E], CompactSpace (MeasureTheory.ProbabilityMeasure E)
```

⚠ **型クラス前提の注意**: `isCompact_stdSimplex` は `[CompactIccSpace 𝕜] [OrderClosedTopology 𝕜]
[ContinuousAdd 𝕜] [IsOrderedAddMonoid 𝕜]` を要求する（`𝕜 = ℝ` ならすべて自動）。
`instCompactSpaceProbabilityMeasure` は `[T2Space E] [BorelSpace E] [CompactSpace E]` を要求し、
`[StandardBorelSpace]` は**要らない**。

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| `Real.negMulLog` の連続性 | `Real.continuous_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | ✅ |

---

## §4 in-project の橋渡し在庫（⚠ loogle は Mathlib しか見ない）

### 4.1 `bcAuxMeasurableEquiv` — **向きは「上げる」/ しかも `private`**

宣言の逐語（`InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean:399-408`）:

```lean
/-- A finite nonempty alphabet, as the auxiliary alphabet of the union of its own cardinality:
the discrete measurable structure makes the indexing bijection of `Fintype.equivFin` measurable
both ways, and the universe lift carries it into the universe of the input alphabet. -/
private noncomputable def bcAuxMeasurableEquiv (V : Type*) [Fintype V] [Nonempty V]
    [MeasurableSpace V] [MeasurableSingletonClass V] :
    V ≃ᵐ bcAuxAlphabet.{u} (Fintype.card V - 1) where
  toEquiv := (Fintype.equivFin V).trans
    ((finCongr (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm).trans Equiv.ulift.symm)
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _
```

⟹ **在庫の読み（「逆向き」）は正しい**。`V` を**その基数ちょうど**のインデックスの `bcAuxAlphabet`
へ写す**同型**であって、基数を落とす写像ではない。基数を落とすには `V → V'` の**非単射**な
写像（併合）が要り、この decl はその形をしていない。

`private` の帰結（逐語）:

```
$ cat PrivCheck.lean
import InformationTheory
#check @InformationTheory.Shannon.BroadcastChannel.Marton.bcAuxMeasurableEquiv
$ lake env lean PrivCheck.lean
PrivCheck.lean:2:8: error(lean.unknownIdentifier): Unknown identifier `InformationTheory.Shannon.BroadcastChannel.Marton.bcAuxMeasurableEquiv`
```

⟹ **`MartonUnion.lean` の外からは名前で参照できない**（CLAUDE.md「`private` は file-scoped」）。
基数境界を別ファイルに書くなら、この decl は使えない（同ファイルに書くか、公開版を作り直す）。

### 4.2 合併に対する単調性 / 添字付け替え

| 要るもの | 判定 | decl / 根拠 |
|---|---|---|
| 型同値による領域の不変性 | **在る** | `Marton.martonRegion_map_relabel` (`MartonUnion.lean:372`) |
| 任意の有限補助アルファベットが合併に吸収される（上げる向き） | **在る** | `Marton.martonRegion_subset_union` (`MartonUnion.lean:415`, `@[entry_point]`) |
| `k ≤ k'` での包含（合併の `k` 方向の単調性） | **無い** | 下の走査 |
| `⋃ (k : ℕ)` を有限個の `k` に切り詰める補題 | **無い** | 同 |

```
@InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion_map_relabel : ∀ {α : Type u_1} {β₁ : Type u_2}
  {β₂ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β₁] [inst_2 : MeasurableSpace β₂] {V₁ : Type u_4}
  {V₂ : Type u_5} {V₁' : Type u_6} {V₂' : Type u_7} [inst_3 : MeasurableSpace V₁] [inst_4 : MeasurableSpace V₂]
  [inst_5 : MeasurableSpace V₁'] [inst_6 : MeasurableSpace V₂'] [inst_7 : Fintype V₁] [Nonempty V₁]
  [MeasurableSingletonClass V₁] [inst_10 : Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [inst_13 : Fintype V₁'] [Nonempty V₁'] [MeasurableSingletonClass V₁'] [inst_16 : Fintype V₂'] [Nonempty V₂']
  [MeasurableSingletonClass V₂'] [inst_19 : Fintype β₁] [Nonempty β₁] [MeasurableSingletonClass β₁]
  [inst_22 : Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂] (pV : MeasureTheory.Measure (V₁ × V₂))
  [MeasureTheory.IsProbabilityMeasure pV] (K : ProbabilityTheory.Kernel (V₁ × V₂) α)
  [ProbabilityTheory.IsMarkovKernel K] (W : InformationTheory.Shannon.BroadcastChannel.BCChannel α β₁ β₂)
  [ProbabilityTheory.IsMarkovKernel W] (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂'),
  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion (MeasureTheory.Measure.map (⇑(e₁.prodCongr e₂)) pV)
      (K.comap ⇑(e₁.prodCongr e₂).symm ⋯) W =
    InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion pV K W
```

⚠ **`e₁ e₂` は `≃ᵐ`（同型）であって一般の可測写像ではない**。基数を落とす併合写像には
そのままでは使えない — 併合後の情報量は等号ではなく不等号でしか制御できないため、
`martonInfo₁_map_relabel` / `martonInfo₂_map_relabel` / `martonInfoV₁V₂_map_relabel`
（`MartonUnion.lean:249,288,329`）の**非同型版**を新たに書く必要がある。

```
@InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion_subset_union : ∀ {α : Type u_1} {β₁ : Type u_2}
  {β₂ : Type u_3} [inst : MeasurableSpace α] [inst_1 : Fintype β₁] [Nonempty β₁] [inst_3 : MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [inst_5 : Fintype β₂] [Nonempty β₂] [inst_7 : MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] {V₁ : Type u_4} {V₂ : Type u_5} [inst_9 : Fintype V₁] [Nonempty V₁]
  [inst_11 : MeasurableSpace V₁] [MeasurableSingletonClass V₁] [inst_13 : Fintype V₂] [Nonempty V₂]
  [inst_15 : MeasurableSpace V₂] [MeasurableSingletonClass V₂] (pV : MeasureTheory.Measure (V₁ × V₂))
  [MeasureTheory.IsProbabilityMeasure pV] (K : ProbabilityTheory.Kernel (V₁ × V₂) α)
  [ProbabilityTheory.IsMarkovKernel K] (W : InformationTheory.Shannon.BroadcastChannel.BCChannel α β₁ β₂)
  [ProbabilityTheory.IsMarkovKernel W],
  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion pV K W ⊆
    InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion W
```

「無い」の根拠 — `martonRegionUnion` の**全消費者**（`scripts/dep_consumers.sh` の逐語出力。
`rg` の近似ではなく項レベル）:

```
$ scripts/dep_consumers.sh InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion
  target : InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion
           InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean:67
  scan   : InformationTheory decl 5052 件を逆引き (証明本体+型シグネチャ)

-- direct consumers : 7 decl / 2 file --
  InformationTheory/Shannon/BroadcastChannel/MartonFullSupport.lean
      227  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion_subset_capacity
  InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean
       91  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion_subset_uv
      104  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnionFullSupport_subset_union
      160  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion_subset_union_of_bcAux  [private]
      169  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion_isLowerSet
      179  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion_nonempty
      410  InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion_subset_union
```

⟹ **7 本すべてが「合併へ入れる」「合併の形を言う」向きで、`k` を落とす向きの decl は 0 本。**
新規補題を足すだけなので**既存署名の変更は発生しない**（ripple = 0）。

### 4.3 ⚠ `martonRegionUnion` の署名に `[Fintype α]` が**無い**（逐語確認済）

```
@InformationTheory.Shannon.BroadcastChannel.Marton.martonRegionUnion : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [inst : MeasurableSpace α] →
        [Fintype β₁] →
          [inst_2 : MeasurableSpace β₁] →
            [Fintype β₂] →
              [inst_4 : MeasurableSpace β₂] → InformationTheory.Shannon.BroadcastChannel.BCChannel α β₁ β₂ → Set (ℝ × ℝ)
```

（`MartonUnion.lean:57-60` の `variable` ブロックには `[Fintype α] [Nonempty α]` が書かれているが、
def 本体が使わないので elaborate 後の署名から落ちている。）

⟹ 基数境界 `|V| ≤ f(Fintype.card α)` は `[Fintype α]` を**新たに要求する**。先例として
`martonRegionUnion_subset_capacity` (`MartonFullSupport.lean:231`) は既に `[Fintype α] [Nonempty α]
[MeasurableSingletonClass α]` を取っているので、同じ列を写せばよい（新規の型クラス設計は不要）。

### 4.4 ⚠ **BC 家系に「基数を落とす機構」の実物が既に在る** — `OuterBoundUV/Quantization.lean`

前在庫 §4.3 の「Carathéodory 型の基数境界補題は 0 件」は**文字どおりには正しい**が、
**Carathéodory ではない別機構による基数削減が、UV 外界側に 1 ファイル丸ごと実装済**である。

ファイル: `InformationTheory/Shannon/BroadcastChannel/OuterBoundUV/Quantization.lean`
（351 行 / 20 decl / **sorry 0 件**、`scripts/sig_view.ts --names` で確認）。
モジュール docstring 逐語（`:5-11`）:

> `# Broadcast channel — truncating the countable auxiliary of the UV outer region`
> The UV outer region is indexed by five-tuple laws whose two auxiliaries range over `ℕ`, while an
> inner bound reads its auxiliary off a finite alphabet.  Truncating the first auxiliary at a level
> `m`, folding every letter at or above `m` into a single one, moves a law of the outer region onto
> the finite alphabet `Fin (m + 1)`, …

主要 decl（逐語署名）:

```
InformationTheory.Shannon.BroadcastChannel.uvQuantize : (m : ℕ) → ℕ → ULift.{u_1, 0} (Fin (m + 1))
```

```
@InformationTheory.Shannon.BroadcastChannel.uvQuantizeLaw : {α : Type u_1} →
  {β₁ : Type u_2} →
    {β₂ : Type u_3} →
      [inst : MeasurableSpace α] →
        [inst_1 : MeasurableSpace β₁] →
          [inst_2 : MeasurableSpace β₂] →
            MeasureTheory.Measure (ℕ × ℕ × α × β₁ × β₂) →
              (m : ℕ) → MeasureTheory.Measure (ULift.{u_1, 0} (Fin (m + 1)) × ℕ × α × β₁ × β₂)
```

```
@InformationTheory.Shannon.BroadcastChannel.uvQuantizeLaw_isUVChannelLaw : ∀ {α : Type u_1} {β₁ : Type u_2}
  {β₂ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β₁] [inst_2 : MeasurableSpace β₂]
  (W : InformationTheory.Shannon.BroadcastChannel.BCChannel α β₁ β₂) [ProbabilityTheory.IsMarkovKernel W]
  {ν : MeasureTheory.Measure (ℕ × ℕ × α × β₁ × β₂)} [MeasureTheory.SFinite ν],
  InformationTheory.Shannon.BroadcastChannel.IsUVChannelLaw W ν →
    ∀ (m : ℕ),
      InformationTheory.Shannon.BroadcastChannel.IsUVChannelLaw W
        (InformationTheory.Shannon.BroadcastChannel.uvQuantizeLaw ν m)
```

```
@InformationTheory.Shannon.BroadcastChannel.uvInfo₁_uvQuantizeLaw : ∀ {α : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3}
  [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β₁] [inst_2 : MeasurableSpace β₂]
  (ν : MeasureTheory.Measure (ℕ × ℕ × α × β₁ × β₂)) [MeasureTheory.IsProbabilityMeasure ν] (m : ℕ),
  InformationTheory.Shannon.BroadcastChannel.uvInfo₁ (InformationTheory.Shannon.BroadcastChannel.uvQuantizeLaw ν m) =
    InformationTheory.Shannon.BroadcastChannel.uvInfo₁ ν
```

```
@InformationTheory.Shannon.BroadcastChannel.uvInfo₂_le_uvQuantizeLaw_add_slack : ∀ {α : Type u_1} {β₁ : Type u_2}
  {β₂ : Type u_3} [Fintype α] [Nonempty α] [inst : MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β₁]
  [Nonempty β₁] [inst_4 : MeasurableSpace β₁] [MeasurableSingletonClass β₁] [inst_6 : Fintype β₂] [Nonempty β₂]
  [inst_8 : MeasurableSpace β₂] [MeasurableSingletonClass β₂] (ν : MeasureTheory.Measure (ℕ × ℕ × α × β₁ × β₂))
  [MeasureTheory.IsProbabilityMeasure ν] (m : ℕ),
  InformationTheory.Shannon.BroadcastChannel.uvInfo₂ ν ≤
    InformationTheory.Shannon.BroadcastChannel.uvInfo₂ (InformationTheory.Shannon.BroadcastChannel.uvQuantizeLaw ν m) +
      InformationTheory.Shannon.BroadcastChannel.uvQuantizeSlack ν m
```

```
@InformationTheory.Shannon.BroadcastChannel.tendsto_uvQuantizeSlack : ∀ {α : Type u_1} {β₁ : Type u_2} {β₂ : Type u_3}
  [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β₁] [inst_2 : Fintype β₂] [inst_3 : MeasurableSpace β₂]
  (ν : MeasureTheory.Measure (ℕ × ℕ × α × β₁ × β₂)) [MeasureTheory.IsProbabilityMeasure ν],
  Filter.Tendsto (InformationTheory.Shannon.BroadcastChannel.uvQuantizeSlack ν) Filter.atTop (nhds 0)
```

「補助変数を可測写像で潰すと条件付き相互情報は増える」という一般補題も同ファイルに在る:

```
@InformationTheory.Shannon.BroadcastChannel.IsUVChannelLaw.condMutualInfo_le_map_cond : ∀ {α : Type u_1} {β₁ : Type u_2}
  {β₂ : Type u_3} [inst : Fintype α] [inst_1 : Nonempty α] [inst_2 : MeasurableSpace α]
  [inst_3 : MeasurableSingletonClass α] [inst_4 : Fintype β₁] [inst_5 : Nonempty β₁] [inst_6 : MeasurableSpace β₁]
  [inst_7 : MeasurableSingletonClass β₁] [Fintype β₂] [Nonempty β₂] [inst_10 : MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] {U : Type u_4} {V : Type u_5} [inst_12 : MeasurableSpace U] [StandardBorelSpace U]
  [Nonempty U] [inst_15 : MeasurableSpace V] [StandardBorelSpace V] [Nonempty V] {U' : Type u_6}
  [inst_18 : MeasurableSpace U'] [StandardBorelSpace U'] [Nonempty U']
  {W : InformationTheory.Shannon.BroadcastChannel.BCChannel α β₁ β₂} [ProbabilityTheory.IsMarkovKernel W]
  {ν : MeasureTheory.Measure (U × V × α × β₁ × β₂)} [inst_22 : MeasureTheory.IsProbabilityMeasure ν],
  InformationTheory.Shannon.BroadcastChannel.IsUVChannelLaw W ν →
    ∀ {f : U → U'},
      Measurable f →
        (InformationTheory.Shannon.condMutualInfo ν (fun q => q.2.2.1) (fun q => q.2.2.2.1) fun q => q.1) ≤
          InformationTheory.Shannon.condMutualInfo ν (fun q => q.2.2.1) (fun q => q.2.2.2.1) fun q => f q.1
```

⚠ **ただし領域レベルの結論は無い**。`Quantization.lean` の decl は情報量スロットの評価で止まっており、
`bcOuterRegionUV W = closure (⋃ m, …有限アルファベット…)` の形の定理は在庫に無い
（同ファイルの consumer は `Superposition/TimeShare.lean` 1 本のみ、`rg -n 'Quantization' InformationTheory/`）。

### 4.5 測度 ↔ ベクトル（単体点）の座標化 — **in-project に在る**

⚠ Mathlib には無い（§3.2）が、in-project には揃っている。

| 概念 | in-project decl | file:line | 逐語 |
|---|---|---|---|
| 有限型上の確率測度の質量は単体点 | `InformationTheory.sum_measureReal_singleton_univ_eq_one` | `InformationTheory/Probability/SingletonMass.lean:30` | `∑ z, μ.real {z} = 1` |
| 押し出しの質量 = ファイバー上の和（**併合写像の効果**） | `InformationTheory.map_real_singleton_fiber_sum` | 同 `:38` | `(Measure.map f μ).real {x} = ∑ q with f q = x, μ.real {q}` |
| ベクトル → 測度 | `InformationTheory.Shannon.ChannelCoding.pmfToMeasure` | `InformationTheory/Shannon/ChannelCoding/ShannonTheorem.lean:55` | `∑ a : α, ENNReal.ofReal (p a) • Measure.dirac a` |
| 同（原子評価） | `…ChannelCoding.pmfToMeasure_apply_singleton` | 同 `:60` | `(pmfToMeasure p) {a} = ENNReal.ofReal (p a)` |
| **エントロピーの定義がそもそもベクトル形** | `InformationTheory.Shannon.entropy` | `InformationTheory/Shannon/Bridge.lean:40` | 下記 |
| pmf 形相互情報 | `InformationTheory.Shannon.mutualInfoPmf` | `InformationTheory/Shannon/RateDistortion/Achievability.lean:198` | 下記 |
| その連続性 | `InformationTheory.Shannon.continuous_mutualInfoPmf` | 同 `:204` | 下記 |
| 入力分布に関する相互情報の連続性 | `…ChannelCoding.continuous_mutualInfoOfChannel_left` | `InformationTheory/Shannon/ChannelCoding/ShannonTheorem.lean:292` | 下記 |

```lean
-- InformationTheory/Shannon/Bridge.lean:39-41 逐語
/-- Shannon entropy of a discrete random variable taking values in a finite alphabet. -/
noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
  ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})
```

⚠ **`entropy` は定義からしてベクトル形の有限和**である。実際、`MaxEntropy/Basic.lean:244` は
`have hent : entropy μ X = ∑ x : α, Real.negMulLog (P.real {x}) := rfl` と**`rfl` で**書いている。
⟹ 測度形エントロピー ↔ pmf ベクトル形の橋は**自作不要**（定義的一致）。

```
@InformationTheory.Shannon.mutualInfoPmf : {α : Type u_1} → {β : Type u_2} → [Fintype α] → [Fintype β] → (α × β → ℝ) → ℝ
```

```lean
-- RateDistortion/Achievability.lean:198-201 逐語
noncomputable def mutualInfoPmf (q : α × β → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (marginalFst q a))
    + (∑ b, Real.negMulLog (marginalSnd q b))
    - (∑ p, Real.negMulLog (q p))
```

```
@InformationTheory.Shannon.continuous_mutualInfoPmf : ∀ {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] [inst : Fintype α] [inst_1 : Fintype β],
  Continuous fun q => InformationTheory.Shannon.mutualInfoPmf q
```

⚠ **`Continuous`（`ContinuousOn` ではない）**。単体上に制限せず `α × β → ℝ` 全体で連続。

```
@InformationTheory.Shannon.ChannelCoding.continuous_mutualInfoOfChannel_left : ∀ {α : Type u_1} {β : Type u_2}
  [inst : Fintype α] [Nonempty α] [inst_2 : MeasurableSpace α] [MeasurableSingletonClass α] [Fintype β] [Nonempty β]
  [inst_6 : MeasurableSpace β] [MeasurableSingletonClass β] (W : InformationTheory.Shannon.ChannelCoding.Channel α β)
  [ProbabilityTheory.IsMarkovKernel W],
  ContinuousOn
    (fun p =>
      (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
          (InformationTheory.Shannon.ChannelCoding.pmfToMeasure p) W).toReal)
    (stdSimplex ℝ α)
```

在庫にある「単体のコンパクト性を実際に使っている」先例（`RateDistortion/Achievability.lean:185-189`、逐語）:

```lean
lemma RDConstraint_isCompact (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsCompact (RDConstraint P_X d D) :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (α × β))
    (RDConstraint_isClosed P_X d D)
    (RDConstraint_subset_stdSimplex P_X d D)
```

### 4.6 `Set (ℝ × ℝ)` 上の凸包機構 — **同じ周囲空間の先例が在る**

| decl | file:line | 逐語結論 |
|---|---|---|
| `InformationTheory.Shannon.MAC.mac_avgPentagon_mem_convexHull` | `InformationTheory/Shannon/MultipleAccess/TimeSharingConverse/Bridge.lean:99` | `(R₁, R₂) ∈ (convexHull ℝ) (⋃ i, {p \| 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ a i ∧ p.2 ≤ b i ∧ p.1 + p.2 ≤ c i})` |

`Bridge.lean:37,74` は `mem_convexHull_iff_exists_fintype` / `mem_convexHull_of_exists_fintype` を
実際に使っている ⟹ **§3.1 の Mathlib API は in-project で稼働実績がある**（配線リスクは低い）。

---

## §5 gate 判定 — **COSTLY**

**WALL ではない**。CLAUDE.md の壁宣言要件（二段検索 + テンプレート補題の指名 + 自己構築行数見積り）
のうち、二段検索は §2 で通したが、**テンプレート補題を指名でき、行数も見積もれる**（下記）ので、
壁の要件「これが書けないなら壁判定を保留せよ」の反対側に落ちる。
**OPEN でもない**。既存資産の配線だけでは閉じず、下記 5 部品の自作が要る。

### 5.1 自作する部品の内訳

| # | 部品 | テンプレートにする既存 decl（file:line） | ⚠ 見積り |
|---|---|---|---|
| 1 | 併合写像（非同型）に沿った 3 情報量の制御 | `Marton.martonInfo₁_map_relabel` / `martonInfo₂_map_relabel` / `martonInfoV₁V₂_map_relabel` (`MartonUnion.lean:249` / `:288` / `:329`)、`IsUVChannelLaw.condMutualInfo_le_map_cond` (`Quantization.lean:84`) | 120–200 行 |
| 2 | `(pV, K)` ↔ 単体点ベクトルの座標化 | `InformationTheory.map_real_singleton_fiber_sum` (`SingletonMass.lean:38`)、`entropy` の定義（`Bridge.lean:40`、橋は `rfl`） | 60–100 行 |
| 3 | support lemma 本体（Carathéodory → 点数 ≤ 次元 + 1） | `convexHull_eq_union` (`Caratheodory.lean:149`) + `AffineIndependent.card_le_finrank_succ` (`FiniteDimensional.lean:245`) + `eq_pos_convex_span_of_mem_convexHull` (`Caratheodory.lean:162`) | 150–250 行 |
| 4 | 得られた重みから `pV'` / `K'` を `bcAuxAlphabet k'` 上に再構成 + インスタンス | `ChannelCoding.pmfToMeasure` (`ShannonTheorem.lean:55`)、`uvQuantizeLaw` + `uvQuantizeLaw_isProbabilityMeasure` (`Quantization.lean:154` / `:163`) | 100–150 行 |
| 5 | 領域レベルの切り詰め定理 + closure / 単調性の糊 | `martonRegionUnion_subset_uv` (`MartonUnion.lean:94`、本体 6 行)、`martonRegionUnionFullSupport_subset_union` (同 `:104`、本体 9 行) | 60–100 行 |

⚠ **合計 490–800 行**。比較対象: 同型の仕事を UV 側でやりきった `Quantization.lean` は
**351 行 / 20 decl / sorry 0**（§4.4）。今回は写像が「切り捨て」でなく「Carathéodory が返す
併合」になる分、部品 3 と 4 が増える。

### 5.2 最初に書くべき補題の署名案

⚠ **定数 `martonAuxBound` は本書では確定させない**（→ §6.4）。抽象の `def` として先に切り、
値の確定は一次文献の逐語確認に回す。

```lean
/-- The cardinality cap on each Marton auxiliary alphabet. -/
def martonAuxBound (α : Type*) [Fintype α] : ℕ := sorry  -- ⚠ 値は一次文献から逐語で

theorem exists_bounded_card_martonRegion_subset
    {α : Type u} {β₁ β₂ : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    (k₁ k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂)) [IsProbabilityMeasure pV]
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∃ (k₁' k₂' : ℕ) (_ : k₁' < martonAuxBound α) (_ : k₂' < martonAuxBound α)
      (pV' : Measure (bcAuxAlphabet.{u} k₁' × bcAuxAlphabet.{u} k₂'))
      (_ : IsProbabilityMeasure pV')
      (K' : Kernel (bcAuxAlphabet.{u} k₁' × bcAuxAlphabet.{u} k₂') α) (_ : IsMarkovKernel K'),
      martonRegion pV K W ⊆ martonRegion pV' K' W
```

その帰結として書く領域レベルの定理:

```lean
theorem martonRegionUnion_eq_bounded (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegionUnion W
      = closure (⋃ (k₁ : ℕ) (_ : k₁ < martonAuxBound α) (k₂ : ℕ) (_ : k₂ < martonAuxBound α)
          (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂)) (_ : IsProbabilityMeasure pV)
          (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α) (_ : IsMarkovKernel K),
          martonRegion pV K W)
```

⚠ **署名上の 2 点**（どちらも §4 の逐語から）:
`[Fintype α]` は `martonRegionUnion` の署名に無いので**新規に足す**（§4.3）。
包含の向きは `⊆` で足りる（`martonRegion` は `InMartonRegion` の 3 不等式なので、
3 情報量を保存すれば `=` が出るが、`⊆` だけ要求しておけば併合が情報量を下げない場合も拾える）。

### 5.3 ripple（既存署名の変更）— **ゼロ**

§4.2 の `dep_consumers` 逐語出力のとおり `martonRegionUnion` の直接消費者は **7 decl / 2 file**
だが、上記は**新規追加のみ**で既存署名を変えないため、7 本のいずれも touch 不要。

---

## §6 我々の演繹（§1–§5 の逐語から導いた判断。逐語ではない）

### 6.1 Fenchel–Eggleston は本件の gate に無関係

→ §2.4 に 3 行で書いた。要旨: 改善するのは**定数だけ**で、有限の上界の存在は標準 Carathéodory で
既に出る。`⋃ (k : ℕ)` を有限に切り詰めるという目的は定数の最小性を要求しない。
⟹ `wall:` 起票の対象にしない。

### 6.2 前在庫の「Carathéodory 型は 0 件」は正しいが、**機構は在庫に在った**

前在庫 §4.3 の `rg -ni 'carath|cardinality bound'` は文字どおり 0 件だが、
`OuterBoundUV/Quantization.lean`（351 行 / sorry 0）が**補助アルファベットの基数を落とす仕事を
UV 側で完遂している**（§4.4）。検索語が "Carathéodory" だったために見えなかった典型で、
CLAUDE.md の `cause:loogle-blind` と同じ形（「Mathlib に無い ⟹ 自作」の前に in-project を
`rg` する）。**本書はこれを在庫の追加として記録し、前在庫を訂正する。**

⚠ **ただし補題としては再利用できない**（機構の転用のみ）。理由: Quantization の写像は
「裾を 1 文字に畳む切り捨て」で、失う量 `uvQuantizeSlack` が `m → ∞` で 0 に行く
（`tendsto_uvQuantizeSlack`）ことに全面的に依存している。Marton 側は各インデックスが**既に有限**の
アルファベットなので裾が無く、`k+1` 文字を `m+1` 文字に畳むと失う量は 0 に行かない。
⟹ Marton 側は**厳密保存**の機構（= Carathéodory）でなければならず、Quantization.lean は
**ファイルの形（写像を定義 → 各スロットを評価 → 領域へ上げる）のテンプレート**として効く。

### 6.3 Lean 側の部品はほぼ揃っている

- Carathéodory 本体 + 基数への橋 = Mathlib（§1）。位相もノルムも要らない前提の軽さは有利。
- 単体のコンパクト性・凸性・連結性 = Mathlib（§3.3）。
- 「測度 ↔ 単体点」は Mathlib に無い（§3.2）が、**in-project では `entropy` の定義自身が
  `∑ negMulLog (μ.real {x})` のベクトル形**で、橋は `rfl`（§4.5）。ここは自作コストがほぼゼロ。
- 押し出し（併合）の質量は `map_real_singleton_fiber_sum` がファイバー和で与える（§4.5）。
- 情報量の連続性は `continuous_mutualInfoPmf`（`Continuous`、単体に制限すら不要）が既にある。
- `Set (ℝ × ℝ)` 上の凸包 API は MAC 家系で稼働実績あり（§4.6）。

⟹ **「Mathlib の壁」に当たる部品は 1 つも無い。COSTLY の中身は分量であって難度ではない**
— ただし次項を除く。

### 6.4 ⚠ 最も危険な所見 — 危険は Lean 側ではなく**数学の核**にある

標的の support lemma は「補助変数 `U` 上の分布を `|U| ≤ f(|X|)` の有限台に置き換えて
`d` 個の連続汎関数の値を保つ」だが、Marton 内界の 3 汎関数は
`martonInfo₁ = I(V₁;Y₁)` / `martonInfo₂ = I(V₂;Y₂)` / `martonInfoV₁V₂ = I(V₁;V₂)`
（`Marton/Setup.lean:244,252,262`）であって、**`V₁` と `V₂` の同時分布の汎関数**である。
教科書の support lemma は「補助変数 **1 本**を、残りの同時法を固定したまま」縮める道具なので、

- `|V₁|` を縮める際に固定すべき対象には `p_{V₂ Y₂}`（`V₂ × β₂` 上の**分布**）が含まれ、
  これはスカラー有限個ではない。
- ⟹ **「support lemma を 2 回当てれば済む」かどうかは、本書では未確認**である。

⚠ **これは我々の演繹であって、文献の主張ではない**。CLAUDE.md「Textbook-object strength diff」
に従い、**§5 の 490–800 行という見積りは「教科書の証明が『support lemma を 2 回』の形で
存在する」という未検証の前提の上に立っている**。前提が崩れると見積りは無効になる
（Gohari–Anantharam 系の摂動法が要るなら部品 3 は 250 行では済まない）。

⟹ **次の一手は Lean ではなく一次文献の逐語確認**である。確認事項は 2 つだけ:
(a) El Gamal–Kim Appendix C の support lemma と、Marton 内界の基数境界（Theorem 8.4 系）の
**証明が同じ道具でつながっているか**、(b) 定数 `f(|X|)` の**逐語の値**
（§5.2 の `martonAuxBound` に入れる値。⚠ 直感で `|X| + 1` などと置かない）。

### 6.5 撤退ラインとの距離

親プラン [`bc-open-problem-t3-plan.md`](bc-open-problem-t3-plan.md) §6 の 3 本に対して:

| 撤退ライン | 触れるか | 判定 |
|---|---|---|
| L8 の棚卸しで T3-α が gate を通らず T3-β / γ も第一手を返さない | **触れない** | 本書は T3-α / β の gate ではなく層 3 の実装コスト調査 |
| L14 の棚卸しで層 3 に載せられる散文が 1 本も無い | **触れない（今のところ）** | 基数境界は載せる候補として生きている（COSTLY = 載る） |
| 20 leg 使い切って未達 | **触れない** | — |

⚠ ただし**予算の警告が 1 つある**（撤退ラインではないので発動はしない）。
親プラン §5 の層 3 集中枠は **L16–L18 の 3 leg** で、§5.1 の見積り 490–800 行はその枠を
基数境界 1 本で埋めうる。⟹ **基数境界を層 3 の主目標に据えるなら、L16–L18 に他の形式化を
同居させない前提で配分を決める必要がある**。これは配分の話であって完了条件ではない
（親 §6 の言葉で言えば `GOAL-CHANGE` ではない）。

⚠ **代替の縮退案（提案であって決定ではない）**: §5.2 の 2 本のうち
`exists_bounded_card_martonRegion_subset` だけを目標にし、領域レベルの
`martonRegionUnion_eq_bounded` を後段に回す。前者が閉じれば「基数有界」の実質は取れる。
どうしても閉じない場合の退出は **`sorry` + `@residual(wall:<slug>)`**（仮説束ね禁止）。
⚠ 本書時点では `wall:` slug を起票しない — §6.3 のとおり壁に当たる部品が特定できていないため、
slug を先に切ると存在しない壁を宣言することになる。

---

## §7 一次文献による §6.4 の決着 (L7)

⚠ 本節は **追記であり、§1–§6 は書き換えていない**。逐語の出典と再検証コマンドは
[`bc-facts.md`](bc-facts.md) `## L7 (T3)` の 7 行が SoT。ここには **§5 の見積りに効く結論だけ**を書く。

### 7.1 §6.4 の 2 つの確認事項への答

| §6.4 の問い | 答 | 逐語の根拠 (facts §L7 の行) |
|---|---|---|
| (a) support lemma と Marton 基数境界は同じ道具でつながるか | **つながらない**。教科書の道具は摂動法 | 行 3 |
| (b) 定数 `f(\|X\|)` の逐語の値 | **`\|X\|` ちょうど**（`\|X\|+1` ではない） | 行 2 |

⟹ **§6.4 の警告は的中した**。[GA09] abstract は "the traditional use of the Carathéodory theorem …
**does not yield a finite cardinality result**"、[EGK] Appendix C は標準 support lemma を提示した直後に
"**This technique, however, does not provide cardinality bounds** … Most notably, cardinality bounds for
`U0, U1, U2` in the Marton inner bound have been recently proved based on **a perturbation method**" と
書いている。⟹ **§5.1 の部品 3「support lemma 本体（Carathéodory → 点数 ≤ 次元 + 1）」は
標的として誤り**である。

⚠ ただし §6.4 が想定していなかった**逆向きの朗報**も出た（7.2）。

### 7.2 Q3 の結論 — (ii) だが、摂動法は**回避できる**

答は形式的には **(ii)**（素朴な support lemma では足りない）だが、**摂動法（Fisher 情報・
Shannon エントロピーの二階微分）を Lean に持ち込む必要は無い**。一次文献 [GA09] 自身が、
我々の 2 補助変数版に対応する Lemma 1 に対して §V-B "**Alternative proof**" を併記しており、
そこで使う道具は次の 3 つだけである（facts §L7 行 4 に逐語）:

1. `p₀(v,x|u)` を固定し、`p₀(x)` を保つよう **`q(u)` だけを動かす**。
2. 目的関数が `q(u)` について **凸**（`−H(Y|U)+H(V|U)` は線型、`−H(V|Z)` は凸）⟹ 最大は**端点**。
3. 定義域は `{q ≥ 0, Σ_u q(u)p₀(v,x|u) = p₀(x)}` という多面体で、等式は `|X|` 本しかない
   ⟹ 端点は `|U| − |X|` 本以上の `q(u) = 0` を拾う ⟹ **台 ≤ `|X|`**。

そして [GA09] Theorem 1 の証明本体はこの Lemma 1 にしか落ちない
（`ga09.txt:707` 逐語: "When λ4 > 0, after a normalization we get the problem studied in section IV.
When λ4 = 0, clearly `Û = V̂ = X` works."）。⟹ **摂動法が本質的に要るのは `|W| ≤ |X|+4` 側と
[GA09] の他の結果であって、`|U|,|V| ≤ |X|` は初等証明だけで閉じる**。

⚠ **循環（§6.4 が心配した点）を破る仕掛けはここ**である — **3 汎関数の値を保存するのをやめ**、
保存するのは `p₀(x)`（`|X|` 本の線型制約）だけにして、目的関数については凸性で
「**減らない**」ことしか言わない。値を保存しようとする限り循環は破れない（7.3）。

### 7.3 Q4 の結論 — 緩い定数への抜け道は**無い**

[GA09] が逐語で答えている（`ga09.txt:107-110`）: 素朴な Carathéodory が返すのは
`|U| ≤ |V||X|+1` と `|V| ≤ |U||X|+1` という**相互再帰の対**であり、"**This does not lead to fixed
cardinality bounds** on the auxiliary random variables `U` and `V`"。

⚠ **我々の演繹（なぜ定数を緩めても駄目か、循環の所在）**: [EGK] の support lemma は
`Σ_u q(u) gj(p(·|u))` の形の `d` 個の量しか保存できない。3 汎関数を分解すると
`I(V₁;Y₁)` は `p(x)`（`|X|−1` 本）+ 条件付きエントロピー（1 本）で**安い**が、
`I(V₂;Y₂)` の `H(Y₂|V₂)` は集約分布 `p(v₂,x) = Σ_u q(u)p(v₂,x|u)` の**非線型関数**であって
`Σ_u q(u) gj(·)` の形に書けない ⟹ 保存には同時分布丸ごと（`|V₂||X|−1` 本）が要る。
これが右辺に `|V₂|` が現れる根拠で、交互適用は `m ← n|X|+1`, `n ← m|X|+1` と**単調増加**して
発散する。⟹ `|X|·|Y₁|·|Y₂|` でも `2^{|X|}` でも、**「値を保存する」道からは有限値が出ない**。
抜け道は「定数を緩める」方向ではなく「**保存をあきらめる**」方向にしかない（= 7.2 の凸性論法）。

### 7.4 ⚠ 代わりに出た重い所見 — §5.2 の**署名**が文献のどの言明よりも強い

**これが L7 の最重要の発見であり、§6.4 が見落としていた軸**である（facts §L7 行 6）。

⚠ **我々の演繹**。`martonRegion` は `{(R₁,R₂) : R₁ ≤ I₁, R₂ ≤ I₂, R₁+R₂ ≤ I₁+I₂−I₁₂}` で
下に非有界なので、方向 `(1,0)/(0,1)/(1,1)` の支持関数はそれぞれ `I₁ / I₂ / I₁+I₂−I₁₂`
（`I₁₂ = I(V₁;V₂) ≥ 0` より `min(I₁+I₂, I₁+I₂−I₁₂) = I₁+I₂−I₁₂`）。
⟹ §5.2 の `martonRegion pV K W ⊆ martonRegion pV' K' W` は
**`I₁ ≤ I₁'` かつ `I₂ ≤ I₂'` かつ `I₁+I₂−I₁₂ ≤ I₁'+I₂'−I₁₂'` の 3 本同時**と同値である。

ところが文献の 2 つの道はどちらも **1 本の重み付き和**しか保証しない:

- 摂動法（[EGK] Appendix C）は**最大化点で** 1 本の目的関数を不変にするだけ。
- 凸性論法（[GA09] §V-B）は 1 本の重み付き和を減らさないだけ。凸関数 3 本が
  **同一の端点で同時に最大化される保証は無い**。

文献の修復手順は「領域を汎関数ベクトルの下方閉包 `C_{M−I}` に置き換え、**凸かつ閉**であることを
使って集合包含を支持関数のスカラー最大化へ落とす」（`ga09.txt:662-663` 逐語）。
⚠ **その凸性が我々には無い** — [GA09] Appendix A の凸性証明はタイムシェア変数 `Q` を
**`W` に吸収させる**（`ga09.txt:1098-1100`）が、我々の領域に `W` は無い。しかも背理法で
**不可能が言える**: `W` 抜きの `C_{M−I} ⊂ ℝ³` が凸なら線型写像 `(R₁,R₂) ↦ (R₁,R₂,R₁+R₂)` の
逆像である Marton 内界も凸になるが、[EGK] Theorem 2 の Remark は
"**This region is not convex in general**"（`egk4.txt:10058`）と述べている。

⟹ **§5.2 の署名はそのままでは文献の証明で閉じない。言い直しが要る。**

### 7.5 §5 の見積り 490–800 行はどう変わるか

| §5.1 の部品 | L7 後の判定 | 差分 |
|---|---|---|
| 1 併合写像に沿った 3 情報量の制御 | **有効** | ±0（120–200 行） |
| 2 `(pV, K)` ↔ 単体点ベクトルの座標化 | **有効**（凸性論法でも `q(u)` ベクトル化は同じ形で要る） | ±0（60–100 行） |
| 3 support lemma 本体（Carathéodory → 点数 ≤ 次元 + 1） | ⚠ **無効 — 標的が違う** | **入れ替え**（下記） |
| 4 重みから `pV'`/`K'` を再構成 + インスタンス | **有効** | ±0（100–150 行） |
| 5 領域レベルの切り詰め + 単調性の糊 | ⚠ **7.4 の言明変更に連動** | 未確定 |

**部品 3 の入れ替え先**（§7.2 の 3 段に対応。⚠ Mathlib 在庫は本 leg では未調査 = 次の一手）:

- (3a) 目的関数の `q(u)` についての**凸性**（線型部分 + `−H(V|Z)` の凸性）。
- (3b) 多面体 `{q ≥ 0, Aq = b}` の**端点の台が `rank A` 以下**であること。
  ⚠ これは §1 の `convexHull` 側 Carathéodory の**双対側**であり、§1 で棚卸しした
  `convexHull_eq_union` / `eq_pos_convex_span_of_mem_convexHull` は**テンプレートにならない**。
- (3c) 凸関数が**コンパクト凸集合の端点で最大**を取ること。

⟹ **§5 の合計 490–800 行という数字は、そのままでは使えない**。理由は 2 つで、
(i) 部品 3 が別物に入れ替わる（行数は同程度かやや増、粗く **200–350 行**）、
(ii) より本質的に、**7.4 の言明変更が決まるまで部品 5 の行数が確定しない**。

### 7.6 次の一手 — 行数見積りではなく**言明の選択**

⚠ **これは壁ではなく scope の選択**である（facts §L7 行 7: 文献側では 2009–2011 に閉じており、
"only since then did Marton's inner bound become computable"）。⟹ `@residual(wall:…)` を切っては
ならない。一方で「文献に在るのだから配線するだけ」と読むのも誤りである（7.4）。

選択肢は 2 つ:

- **(a) 標的をスカラー版に下げる** — [EGK] Appendix C 逐語の形（重み付き和の最大値について
  `|V₁|,|V₂| ≤ |X|` で足りる）を標的にする。§5.2 の `martonRegion` の包含は主張しない。
  凸性論法（7.2）がそのまま乗るので**部品 3 の入れ替えだけで閉じる**。
  ⚠ 代償: これ単体では `martonRegionUnion` の切り詰め（`martonRegionUnion_eq_bounded`）に届かない。
- **(b) 領域定義にタイムシェア変数を足して凸性を回復する** — `gea11.txt:71-76` の
  `R₁ ≤ I(U;Y|Q)` 形にならう。⚠ `martonRegionUnion` の**定義変更**なので §5.3 の
  「ripple ゼロ」は崩れ、`dep_consumers` が挙げた **7 decl / 2 file** に波及する。

⚠ **(a) と (b) の差は「計算可能性の主張がどこまで出るか」**であって難度ではない。
親プラン [`bc-open-problem-t3-plan.md`](bc-open-problem-t3-plan.md) の層 3 が要求するのが
「領域の有限切り詰め」なら (b) が要る。⚠ この判断は本書ではなく親プラン側で行う。

### 7.7 §5.2 の定数スロットは確定した

`def martonAuxBound (α : Type*) [Fintype α] : ℕ := sorry` の値は **`Fintype.card α`**
（facts §L7 行 2、独立な 5 本の一次文献が `|U|,|V| ≤ |X|` で一致）。

⚠ **off-by-one は合っている（逐語確認済）** — `abbrev bcAuxAlphabet (k : ℕ) : Type u :=
ULift.{u} (Fin (k + 1))`（`MartonUnion.lean:65`、docstring も "the auxiliary alphabet of
cardinality `k + 1`"、同 `:16`）なので `|V₁'| = k₁' + 1`。文献の `|V₁'| ≤ |X|` は
`k₁' + 1 ≤ Fintype.card α` すなわち **`k₁' < Fintype.card α`** と同値であり、
§5.2 が既に書いている真の不等号 `k₁' < martonAuxBound α` と**そのまま一致**する。
⟹ `martonAuxBound α := Fintype.card α` で補正項は要らない。
⚠ **`|X| + 1` と書いてはならない** — `+1` / `+4` が付くのは共通メッセージ版の第 3 変数 `W` だけで、
我々の 2 補助変数版には無関係である。

---

## §8 標的言明の選択 (L8)

⚠ 本節は **追記であり、§1–§7 は書き換えていない**。§7.6 の 2 択 (a)/(b) に、第 3 案 (c) と
本節で出た第 4 案 (a′) を加えて判定する。逐語の出典は [`bc-facts.md`](bc-facts.md) `## L7 (T3)` が SoT。

### 8.1 (c) の判定 — **NO。逃げ道ではない**（ただし「3 本同時」は本当に緩む）

(c) = 標的の右辺を有界合併にする形
`martonRegion pV K W ⊆ ⋃ (k₁' < martonAuxBound α) (k₂' < …) (pV') (K'), martonRegion pV' K' W`。

**(i) 緩む部分は本物である**（⚠ 我々の演繹）。`martonRegion` は 3 本の線型不等式で切られた lower set
`Q(a,b,s) = {R₁ ≤ a, R₂ ≤ b, R₁+R₂ ≤ s}`（`a = I₁`, `b = I₂`, `s = I₁+I₂−I₁₂`）であり、
線分 `L = {(t, s−t) : s−b ≤ t ≤ a}` の下方閉包に等しい。各 `Q` が lower set なので (c) は
「`L` の各点が有界 witness の `Q(a',b',s')` に入る」ことと同値で、点ごとの要求は

    (t, s−t) ∈ Q(a',b',s')  ⟺  t ≤ a' かつ s−t ≤ b' かつ s ≤ s'

⟹ 目標値が `t` とともに動くので、§5.2 が要求する 3 本同時 `a ≤ a'` / `b ≤ b'` / `s ≤ s'` は
**要求されない**。⟹ §7.4 の「3 汎関数の同時改善」は (c) の必要条件では**ない**。ここまでは正しい。

**(ii) 潰れる部分**（⚠ 我々の演繹）。`L` の端点 `p₁ = (a, s−a)` では 3 本のうち **2 本が満強度で残る** —
`a' ≥ a`（方向 `(1,0)`）と `s' ≥ s`（方向 `(1,1)`）。3 本目 `b' ≥ s−a` は `I₁₂' ≥ 0` から
`b' = s'−a'+I₁₂' ≥ s−a` で自動に従う。対称に `p₂ = (s−b, b)` は `b' ≥ b` と `s' ≥ s`。
⟹ **3 本同時 → 2 本同時に減っただけ**であり、「1 つの witness が複数方向で同時に支配する」という
§7.4 の障害の**型はそのまま残る**。文献（§7.2、facts §L7 行 4）が与えるのは **1 方向 1 回**の最大化である。

**(iii) 反例の形**（⚠ 我々の演繹。3 つ組の水準の反例であり、実チャネルでの実現は主張しない。
示すのは「文献のスカラー保証から (c) は導けない」ことであって「(c) が偽」ではない）:
有界 witness が返す `(I₁,I₂,I₁₂)` が `T' = (2,0,0)` と `T'' = (0,2,0)` の 2 つだけ、無界 witness が
`T₀ = (1,1,0)` を返すとする。`(a,b,s)` は順に `(2,0,2)` / `(0,2,2)` / `(1,1,2)`。

- **スカラー版は全方向で成立する**: 任意の重み `μ ≥ 0` に対し `max(2μ₁, 2μ₂) + 2μ₃ ≥ μ₁ + μ₂ + 2μ₃`。
- **(c) は壊れる**: `(1,1) ∈ Q(T₀)` だが `Q(T')` は `R₂ ≤ 0` を、`Q(T'')` は `R₁ ≤ 0` を要求するので
  どちらにも入らない。しかも `(1,1)` はまさに角点 `p₁ = (a, s−a)` である。

⟹ **(c) は (a) と §5.2 の中間の強さ**で、証明側の障害は §5.2 と同型（次元が 1 減っただけ）。

**(iv) 定数を `+1` して買えるか — 片側だけ買えて反復しない**（⚠ 我々の演繹、未検証）。
`V₁` を縮める段では、`p₀(x)` を保つ多面体上で `I₁ = H(Y₁) − Σ q(v₁)H(Y₁\|v₁)` が `q` について
**アフィン**である（facts §L7 行 4 逐語 "The term `−H(Y\|U)+H(V\|U)` is **linear** in `q(u)`"）
⟹ `I₁` 保存を**等式制約として多面体に足せる**（端点の台は `\|X\|+1` に増える）。`S = I₁+I₂−I₁₂` は
凸なので端点で減らない ⟹ `p₁` の 2 本同時が `\|V₁\| ≤ \|X\|+1` で取れる。
⚠ **しかし `V₂` を縮める段で要る 2 本（`I₁` と `S`）はどちらも `p(v₂)` についてアフィンでない**
（両方とも凸）ので同じ手が反復しない。⟹ (c) は定数を緩めても閉じない。

### 8.2 推奨 — **(a′) スカラー版を「閉凸包の等式」として述べる** ✓ 推奨

⚠ **(a′) は §7.6 の 2 択に無かった第 4 案**である。中身は (a) と同じだが、言明を領域の水準へ上げる。

```lean
-- (a′-1) 文献の結論形そのまま（∃ 形。sSup を経由しない）
theorem exists_bounded_card_ge_martonWeightedSum
    … (μ₁ μ₂ μ₃ : ℝ) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂) (hμ₃ : 0 ≤ μ₃) … :
    ∃ (k₁' k₂' : ℕ) (_ : k₁' < martonAuxBound α) (_ : k₂' < martonAuxBound α)
      (pV') (_ : IsProbabilityMeasure pV') (K') (_ : IsMarkovKernel K'),
      μ₁ * martonInfo₁ pV K W + μ₂ * martonInfo₂ pV K W
        + μ₃ * (martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W)
      ≤ μ₁ * martonInfo₁ pV' K' W + μ₂ * martonInfo₂ pV' K' W
        + μ₃ * (martonInfo₁ pV' K' W + martonInfo₂ pV' K' W - martonInfoV₁V₂ pV' K' W)

-- (a′-2) 領域版（§5.2 の martonRegionUnion_eq_bounded の閉凸包版）
theorem closure_convexHull_martonRegionUnion_eq_bounded (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    closure (convexHull ℝ (martonRegionUnion W))
      = closure (convexHull ℝ (⋃ (k₁ : ℕ) (_ : k₁ < martonAuxBound α) (k₂ : ℕ)
          (_ : k₂ < martonAuxBound α) (pV : Measure _) (_ : IsProbabilityMeasure pV)
          (K : Kernel _ α) (_ : IsMarkovKernel K), martonRegion pV K W))
```

⚠ **(a′-1) の署名は本ルート (C) の射程より広い — L11 の実測で判明**（⚠ 我々の演繹。展開は
`Marton/Setup.lean:244` / `:252` / `:262` の逐語定義から機械的。`H(·)` は
`entropy (martonJointDistribution pV K W) ·` の略記）。`U := V₁` と置き `pV = q ⊗ₘ κ`（`κ` 固定）
として `q = p(v₁)` だけを動かすと:

- `martonInfo₂ − martonInfoV₁V₂ = (H(Y₂) − H(V₂,Y₂)) + (H(V₁,V₂) − H(V₁))`
  ⟹ **`H(V₂)` は完全に相殺する**。第 1 括弧は `−H(V₂|Y₂)` = 凸核（§9.1、`convexOn_negCondEntropy`
  (`Marton/ObjectiveConvexity.lean:43`) の `f`）、第 2 括弧は `H(V₂|V₁) = ∑_u q(u)·H(κ_u)` で
  `q` について**線型** ⟹ `auxWeightObjective` (`同:86`) の `w` slot にそのまま載る。
- `martonInfo₁ = H(Y₁) + (H(V₁) − H(V₁,Y₁)) = H(Y₁) − H(Y₁|V₁)` ⟹ `H(Y₁|V₁)` は線型、
  `H(Y₁)` は集約 `p(x)` のみの関数なので `exists_support_card_le_of_convexOn_add_aggregate`
  (`Marton/SupportReduction.lean:219`) の `g` に吸収される（`g` に凸性も可測性も要らない）。
- ⚠ **しかし一般の `μ₂ > 0` では `μ₂·H(V₂)` が残る**。`p(v₂) = ∑_u q(u)·κ(v₂|u)` は `q` について
  線型で `Real.concaveOn_negMulLog`（§9.4 の表）より `H(V₂)` は `q` について**凹**、
  **かつ集約 `p(x)` の関数でもない**（`p(v₂)` は `p(x)` から決まらない）⟹ **凸 slot・線型 slot・
  集約 slot のどれにも載らない = 本機構の射程外**。`p(v₂)` も集約に足すと `X := α ⊕ V₂` となり
  基数定数が `\|α\|+\|V₂\|` に膨らむ（= §L7 が記録した発散する相互再帰）。

⟹ **上の (a′-1) は `μ₁ μ₂ μ₃ ≥ 0` の全域を量化しているが、C ルートで届くのは `μ₂ = 0` 系列と
対称の `μ₁ = 0` 系列だけ**である。⚠ **署名側を 2 系列に絞ること**（`(hμ₂ : μ₂ = 0)` を足した版と
その対称版の 2 本に割る、あるいは本節末尾の `(μ₁−μ₂)I₁ + μ₂S` 形で述べる）— 全域版のまま実装へ
渡すと under-hypothesis になる。⚠ これは L7 が記録した「標的言明が文献より強い」の再演である。
なお本節末尾の 3 段（`geometric_hahn_banach_closed_point` → 分離汎関数 → 支持関数）が要求する重みは
**まさにその 2 系列だけ**（本節末尾の逐語「⚠ ここで要る重みは `μ₂ = 0` 系列と `μ₁ = 0` 系列だけ」）
なので、**射程を絞っても (a′-2) は閉じる**。

| 案 | 定義変更 | 文献の証明が届くか | 領域の切り詰めが出るか | 追加債務 |
|---|---|---|---|---|
| (a) スカラーのみ | 無し | **届く** | 出ない（§7.6 の代償） | 無し |
| **(a′)** ✓ | **無し** | **届く**（(a) と同内容） | **出る（閉凸包の水準で）** | 容量領域の凸性 1 本（消費段で） |
| (b) `Q` 追加 | 有り | 届く | 出る | 容量領域の凸性 + **§8.3 の 2 本** |
| (c) 点ごと合併 | 無し | ⚠ **届かない**（§8.1） | 出る | — |
| §5.2 単一 witness | 無し | ⚠ 届かない（§7.4） | 出る | — |

**なぜ (a′) が T3 のゴールに対して最も多く言えるか**（親プラン §1.1 (C1) に照らす）:

1. (C1) が要求するのは「各 `n` の Marton 領域が**計算可能**（有界時間 `ε` 近似）」である。
   凸閉集合の `ε` 近似の標準構成は**有限個の方向で支持関数を評価する**ことであり、(a′-1) はその
   評価式そのもの、(a′-2) はその評価が定める対象の同定である ⟹ **(a′) は T3 が実際に消費する形**。
   非凸のままの合併は近似の形すら定まらない。
2. **凸化しても内界であり続ける**（容量領域は time-sharing で凸）。⚠ ただし in-project に
   `Convex ℝ (bcCapacityRegion W)` は**無い**（BC 家系の `Convex` は `martonRegion_convex`
   (`MartonUnion.lean:133`) の 1 本のみ）⟹ 凸化した対象を内界として消費する段で債務が 1 本立つ。
   ⚠ **この債務は (b) を採っても同じだけ立つ**（しかも (b) は既存 2 本を壊す形で立てる、§8.3）。
3. **(b) と (a′) は同じ対象を指す**（⚠ 我々の演繹）: `Q` 付き領域は 3 つ組の凸結合に対する
   `Q(Σλᵢtᵢ)` であり、支持関数が一致するので `Q(Σλᵢtᵢ) = Σλᵢ Q(tᵢ) ⊆ conv(⋃ᵢ Q(tᵢ))`、逆包含は
   各不等式が 3 つ組について線型であることから直ちに従う ⟹ **`⋃_Q (Q 付き領域) = conv(⋃ martonRegion)`**。
   ⟹ (b) が買うものを (a′) は**定義を触らずに**買う。
4. §7.6 が (a) の代償とした「`martonRegionUnion` の切り詰めに届かない」は、**閉凸包を取れば届く**。
   届かないのは非凸のままの合併の切り詰め = (c) だけで、それは §8.1 のとおり文献の射程外である。

**行数の見積り**（§7.5 の更新。⚠ 我々の演繹）: (a′-1) = §7.5 の部品 1 / 2 / 4（有効、280–450 行）
+ 部品 3 の入れ替え先 (3a)(3b)(3c)（200–350 行）⟹ **480–800 行**（§5 の総額と同程度）。
(a′-2) は追加で **60–120 行**。

**最初の一手**: §7.5 が「本 leg では未調査 = 次の一手」と書いた唯一の項目、部品 **(3b)
「多面体 `{q ≥ 0, Aq = b}` の端点の台が `rank A` 以下」の Mathlib 在庫調査**。⚠ §1 で棚卸しした
`convexHull` 側 Carathéodory は双対側なのでテンプレートにならない（§7.5）。gateway-atom-first で 1 本投げる。

**(a′-2) の 3 段**（Mathlib 資産は確認済）: `geometric_hahn_banach_closed_point`
(`Mathlib/Analysis/LocallyConvex/Separation.lean:230`) で右辺の外の点を分離 → 両辺が lower set である
ことから分離汎関数 `μ ≥ 0` を出す（`μᵢ < 0` なら右辺上の上限が `+∞` になり分離と矛盾）→ 方向 `μ` の
支持関数を `μ₁ ≥ μ₂` のとき `(μ₁−μ₂)I₁ + μ₂S`（対称形も同様）へ落として (a′-1) を当てる。
⚠ ここで**要る重みは `μ₂ = 0` 系列と `μ₁ = 0` 系列だけ**であり、これは [GA09] Lemma 1 の
`γ = 0` / `λ = 0` に対応する。`μ₃ = 0`（純方向 `(1,0)` / `(0,1)`）は `ga09.txt:707` 逐語の
"clearly `Û = V̂ = X` works" で閉じる（§7.2 に既出）。
⚠ `closedConvexHull_eq_closure_convexHull` (`Mathlib/Analysis/Convex/Topology.lean:332`) が在るので
`closedConvexHull` 表記でもよい。

**進まないときの退出**: (3b) が Mathlib に無く自己構築が 150 行を超えるなら、(a′-1) を
`sorry` + `@residual(plan:<slug>)` で骨格だけ立て、**独立に閉じられる (a′-2) を先に閉じる**
（(a′-1) を仮定に取らず `sorry` の補題として参照する）。⚠ `@residual(wall:…)` は切らない
（facts §L7 行 7: 文献側では 2009–2011 に閉じている）。

### 8.3 (b) の波及 — 「7 decl に波及」では済まず、**`@[entry_point]` 2 本の証明が通らなくなる**

`scripts/dep_consumers.sh …Marton.martonRegionUnion` の逐語出力（`direct consumers : 7 decl / 2 file`）:

| file:line | decl | (b) の下で |
|---|---|---|
| `MartonFullSupport.lean:227` | `martonRegionUnion_subset_capacity` `@[entry_point]` | ⚠ **証明が通らない** |
| `MartonUnion.lean:91` | `martonRegionUnion_subset_uv` `@[entry_point]` | ⚠ **証明が通らない** |
| `MartonUnion.lean:104` | `martonRegionUnionFullSupport_subset_union` | 機械的（⚠ `martonRegionUnionFullSupport` も定義変更が要る = 波及 +1） |
| `MartonUnion.lean:160` | `martonRegion_subset_union_of_bcAux` `[private]` | 機械的（`Q` を退化させる index を選ぶ） |
| `MartonUnion.lean:169` | `martonRegionUnion_isLowerSet` | 機械的 |
| `MartonUnion.lean:179` | `martonRegionUnion_nonempty` | 機械的 |
| `MartonUnion.lean:410` | `martonRegion_subset_union` | 機械的 |

⚠ **2 本が壊れる理由（逐語）**:

- `martonRegionUnion_subset_capacity` の本体は `closure_minimal` + 各 index で
  `marton_region_subset_capacity_of_channel_fullSupport pV K W hW` を当てるだけである
  (`MartonFullSupport.lean:234-237`)。`Q` 付きの点は**単一の `(pV,K)` の四角形に入らない**ので
  この per-index 還元は届かない。再証明には time-sharing（符号の連接）による新規の operational 証明が要る。
- `martonRegionUnion_subset_uv` も同型 (`MartonUnion.lean:96-100`)。`Q` 付きだと `bcOuterRegionUV` の
  **凸性**が要るが in-project に無い。迂回は `bcCapacityRegion W ⊆ bcOuterRegionUV W`
  (`OuterBoundUV/Assembly.lean:853`) 経由だが、それには 1 本目の再証明が先に要る ⟹ 依存が 1 本目に集約される。

⟹ **(b) のコストは §7.6 の見積り（「7 decl / 2 file に波及」）より遥かに大きい**。壊れる 2 本はどちらも
sorryAx-free の headline であり、必要なのは署名の修正ではなく**新しい数学**である。⚠ しかも §8.2-3 の
とおり (b) が買う対象は (a′) が定義を触らずに買う対象と等しい。

### 8.4 撤退ライン判定 — **3 本とも触れない**

| 親 §6 の撤退ライン | 触れるか | 判定 |
|---|---|---|
| L8 の棚卸しで T3-α が gate を通らず T3-β / γ も第一手を返さない | **触れない** | 本節は軸の gate ではなく層 3 の標的言明の選択。T3-α の gate 判定は別 leg |
| L14 の棚卸しで層 3 に載せられる散文が 1 本も無い | **触れない** | (a′) が載る候補として生きている（§8.2）。むしろ載せる形が確定した |
| 20 leg を使い切って未達 | **触れない** | — |

⚠ §6.5 の予算警告（層 3 集中枠 L16–L18 を基数境界 1 本が埋めうる）は**そのまま有効**である
— (a′) を採っても 480–800 行 + 60–120 行という見積りは動かない（§8.2）。
⚠ `@residual(wall:…)` を切らないという §7.6 / facts §L7 行 7 の判定も動かない。(a′) は
「文献の結論形をそのまま標的にする」選択であって、壁の回避ではない。

---

## §9 目的関数の凸性の在庫 (L10)

### 9.0 一行判定

**Q1 の凸核 = (i) 既存資産で閉じる。** 文献が「唯一の非自明な核」とした `−H(V|Z)` の凸性は、
**同じ repo の Wyner–Ziv 家系に proof-done で既に在る** — `negMulLog_marginal_gap_le_joint_gap`
(`InformationTheory/Shannon/WynerZiv/ConditionalEntropyConvexity.lean:75`、0 sorry) が
逐語で `−H(V|Z)` の同時分布に関する 2 点凸性そのものである。
ルート A (perspective) / ルート B (Gibbs 変分) の**どちらも要らない** ⟹ 第 3 のルート C を推奨。

⚠ **本節の主張は散文ではなく機械検証済**である。scratchpad で実際に

```lean
ConvexOn ℝ {r : V × Z → ℝ | 0 ≤ r}
  (fun r ↦ (∑ z, Real.negMulLog (∑ v, r (v, z))) - ∑ p : V × Z, Real.negMulLog (r p))
```

を上記 1 本から導き、さらに線型写像 `q ↦ (fun p ↦ ∑ u, q u * k u p)` と合成して
`ConvexOn ℝ {q : U → ℝ | 0 ≤ q} …`（= `exists_support_card_le_of_convexOn` の `hf` の型）まで
落とすところまで `lake env lean` clean を確認した（**計 45 行 / 新規補題 0 本 / Mathlib 壁 0 件**）。

| Q | 問い | 判定 |
|---|---|---|
| Q1 | 条件付きエントロピーの同時分布に関する凹性 | **in-project に在る**（Mathlib には無い） |
| Q2 | KL の**同時**凸性 | **in-project に在る** (`klDiv_joint_convex`)。**Mathlib は 0 件**（片側すら無い） |
| Q3 | Gibbs / 変分表示ルート | **在るのは片側 (Donsker–Varadhan の `≤`) だけ**。`inf` 表示は無い ⟹ ルート B は不成立 |
| Q4 | `ConvexOn` コンビネータ | `.comp_linearMap` / `.comp_affineMap` / `.add` / `.sub` / `.smul` / `.neg` / `.subset` 全部在る。**`ConvexOn.sum` と perspective と `iSup/iInf` 版は無い** |
| Q5 | `entropy` のベクトル形 = `rfl` という §4.5 の主張 | **逐語確認済 = 正しい**（ただし方向に注意、§9.5） |
| Q6 | 前在庫「BC 家系の凸性は `martonRegion_convex` 1 本」 | **BC 家系に限れば正しい**。ただし**家系の外に凸性の主資産が 3 本在り、前在庫はそれを数えていない**（§9.6） |

### 9.1 Q1 — 凸核の実体（**最重要**）

#### 9.1.1 主資産（`#check @…` の逐語出力）

```
@negMulLog_marginal_gap_le_joint_gap : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β]
  [MeasurableSpace α] [MeasurableSpace β] (r₁ r₂ : α × β → ℝ),
  (∀ (p : α × β), 0 ≤ r₁ p) →
    (∀ (p : α × β), 0 ≤ r₂ p) →
      ∀ (a b : ℝ),
        0 ≤ a →
          0 ≤ b →
            a + b = 1 →
              ∑ y,
                  ((∑ x, (a * r₁ (x, y) + b * r₂ (x, y))).negMulLog - a * (∑ x, r₁ (x, y)).negMulLog -
                    b * (∑ x, r₂ (x, y)).negMulLog) ≤
                ∑ y,
                  ∑ x,
                    ((a * r₁ (x, y) + b * r₂ (x, y)).negMulLog - a * (r₁ (x, y)).negMulLog - b * (r₂ (x, y)).negMulLog)
```

- **file:line**: `InformationTheory/Shannon/WynerZiv/ConditionalEntropyConvexity.lean:75`
- **完全修飾名**: `InformationTheory.Shannon.negMulLog_marginal_gap_le_joint_gap`
- **型クラス前提（逐語）**: `[Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]`
- **引数の順**: `{α β : Type*}` → 4 instance → `(r₁ r₂ : α × β → ℝ)` → `(hr₁ hr₂ : ∀ p, 0 ≤ · p)`
  → `(a b : ℝ)` → `(ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)`
- **状態**: 0 sorry（ファイル全体 7 decl / 0 sorry、`scripts/sig_view.ts` 逐語）

⚠ **`[MeasurableSpace α] [MeasurableSpace β]` は使われていないのに署名に載っている**
（同ファイル `:40-42` の `variable` ブロックからの漏れ。`:38` に
`set_option linter.unusedSectionVars false` が置かれているのでリンタも黙っている）。
消費側に測度空間インスタンスを要求する。BC 家系では `V₁ V₂ α β₁ β₂` すべてに
`[MeasurableSpace _]` が既に付いている（`martonRegion_convex` 署名の逐語で確認）ので**実害は無い**が、
`exists_support_card_le_of_convexOn` の側は `[Fintype ι] [Fintype X]` **のみ**で測度空間を要求しない
（§9.4 の逐語）ため、**この 1 本を挟むと消費側の署名に `MeasurableSpace` が 2 本増える**。

#### 9.1.2 なぜこれが `−H(V|Z)` の凸性なのか（⚠ 我々の演繹、ただし機械検証済）

`Hmarg(r) := ∑_z negMulLog(∑_v r(v,z))`、`Hjoint(r) := ∑_{v,z} negMulLog(r(v,z))` と置くと
上の結論は `Hmarg(m) − a·Hmarg(r₁) − b·Hmarg(r₂) ≤ Hjoint(m) − a·Hjoint(r₁) − b·Hjoint(r₂)`
（`m = a·r₁ + b·r₂`）であり、移項すると

```
(Hmarg − Hjoint)(m) ≤ a·(Hmarg − Hjoint)(r₁) + b·(Hmarg − Hjoint)(r₂)
```

`Hjoint − Hmarg = H(V,Z) − H(Z) = H(V|Z)` なので `Hmarg − Hjoint = −H(V|Z)`。
⟹ **`−H(V|Z)` は同時分布 `r = p(v,z)` について `{r | 0 ≤ r}` 上で凸**。

⚠ **正規化 (`∑ r = 1`) を要求しない**。前提は `∀ p, 0 ≤ rᵢ p` だけであり、これは
`exists_support_card_le_of_convexOn` の定義域 `{q | 0 ≤ q}` と**完全に一致する**（単体へ制限する
必要が無い）。文献の分解が「`q(u)` だけを動かす」形であることと整合する。

#### 9.1.3 ルート C — 機械検証済の橋（**そのまま実装に使える 45 行**）

以下は scratchpad で `lake env lean` clean（0 error / 0 warning）を確認した実物である。
⚠ 本在庫は `InformationTheory/**.lean` を書き換えていない。下記は**実装エージェントへの入力**であり、
コミット済のコードではない。

```lean
import InformationTheory.Shannon.WynerZiv.ConditionalEntropyConvexity
import Mathlib.Analysis.Convex.Function

open InformationTheory InformationTheory.Shannon Finset

variable {V Z U : Type*} [Fintype V] [Fintype Z] [Fintype U]
  [MeasurableSpace V] [MeasurableSpace Z]

theorem negCondEnt_convexOn :
    ConvexOn ℝ {r : V × Z → ℝ | 0 ≤ r}
      (fun r ↦ (∑ z, Real.negMulLog (∑ v, r (v, z)))
                 - ∑ p : V × Z, Real.negMulLog (r p)) := by
  constructor
  · intro r₁ h₁ r₂ h₂ a b ha hb _ p
    exact add_nonneg (mul_nonneg ha (h₁ p)) (mul_nonneg hb (h₂ p))
  · intro r₁ h₁ r₂ h₂ a b ha hb hab
    have key := negMulLog_marginal_gap_le_joint_gap r₁ r₂ h₁ h₂ a b ha hb hab
    have hflip : ∀ g : V × Z → ℝ, ∑ z, ∑ v, g (v, z) = ∑ p : V × Z, g p := by
      intro g; rw [Finset.sum_comm]; exact (Fintype.sum_prod_type (f := g)).symm
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at key
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hflip fun p ↦ Real.negMulLog (r₁ p), ← hflip fun p ↦ Real.negMulLog (r₂ p),
      ← hflip fun p ↦ Real.negMulLog (a * r₁ p + b * r₂ p)]
    linarith [key]

theorem convex_nonneg_pi {ι : Type*} : Convex ℝ {q : ι → ℝ | 0 ≤ q} := by
  intro x hx y hy a b ha hb _ i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem negCondEnt_comp_convexOn (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) :
    ConvexOn ℝ {q : U → ℝ | 0 ≤ q}
      (fun q ↦ (∑ z, Real.negMulLog (∑ v, ∑ u, q u * k u (v, z)))
                 - ∑ p : V × Z, Real.negMulLog (∑ u, q u * k u p)) := by
  classical
  let L : (U → ℝ) →ₗ[ℝ] (V × Z → ℝ) :=
    { toFun := fun q p ↦ ∑ u, q u * k u p
      map_add' := fun q₁ q₂ ↦ by
        funext p; simp only [Pi.add_apply, add_mul]; exact Finset.sum_add_distrib
      map_smul' := fun c q ↦ by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hcomp := negCondEnt_convexOn.comp_linearMap (E := (U → ℝ)) L
  have hsub : {q : U → ℝ | 0 ≤ q} ⊆ (⇑L) ⁻¹' {r : V × Z → ℝ | 0 ≤ r} := by
    intro q hq
    exact fun p ↦ Finset.sum_nonneg fun u _ ↦ mul_nonneg (hq u) (hk u p)
  exact (hcomp.subset hsub convex_nonneg_pi)
```

⚠ **`convex_nonneg_pi` は Mathlib に無い**（`convex_Ici` は `Set.Ici` 形であり、
`{q | 0 ≤ q}` を `Set.Ici (0 : ι → ℝ)` と同一視する `simp` 補題を通す必要がある）ので
**上の 3 行で自作するのが最短**である。`SupportReduction.lean` 側もこれを持っていない。

#### 9.1.4 Mathlib 側は 0 件（逐語）

| クエリ（逐語） | 出力（逐語） |
|---|---|
| `ConvexOn _ _ (fun _ => Real.negMulLog _)` | `Found 0 declarations mentioning Real.partialOrder, Real, Real.negMulLog, Real.instAddCommMonoid, and ConvexOn.` / `Of these, 0 match your pattern(s).` |
| `ConcaveOn, Real.negMulLog` | `Found one declaration mentioning Real.negMulLog and ConcaveOn.` → `Real.concaveOn_negMulLog` |
| `"condEntropy"` | `Found 0 declarations whose name contains "condEntropy".` |
| `"mutualInfo"` | `Found 0 declarations whose name contains "mutualInfo".` |
| `ConvexOn _ _ (fun _ => Finset.sum _ _)` | `Found 4 declarations mentioning Finset.sum and ConvexOn.` / `Of these, 0 match your pattern(s).` |

⟹ Mathlib が持つのは**スカラー 1 変数の `Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici 0) Real.negMulLog`
1 本だけ**で、多変数のエントロピー凹性・相互情報量・条件付きエントロピーは**概念ごと存在しない**
（`condEntropy` / `mutualInfo` という名前が 0 件）。Fano 在庫 (`docs/fano/fano-mathlib-inventory.md:54-56`)
の判定と整合する。

### 9.2 Q2 — KL の同時凸性

**結論: Mathlib は 0 件（片側凸性すら無い）。in-project には measure 形の同時凸性が proof done で在る。**

| 概念 | decl | file:line | 型クラス前提（逐語） | 結論形（逐語） |
|---|---|---|---|---|
| **KL の同時凸性**（両引数を同時に混合） | `InformationTheory.Shannon.klDiv_joint_convex` | `InformationTheory/Shannon/RateDistortion/Convexity.lean:280` | `[MeasurableSpace Ω]` `[IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]` | `klDiv (ENNReal.ofReal lam • μ₁ + ENNReal.ofReal (1 - lam) • μ₂) (ENNReal.ofReal lam • σ₁ + ENNReal.ofReal (1 - lam) • σ₂) ≤ ENNReal.ofReal lam * klDiv μ₁ σ₁ + ENNReal.ofReal (1 - lam) * klDiv μ₂ σ₂` |
| 相互情報量の混合凸性 | `InformationTheory.Shannon.klDiv_mixture_le` | 同 `:336` | `[MeasurableSpace α] [MeasurableSpace β]` `[IsProbabilityMeasure P] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]` | `klDiv (mixtureMeasure lam ν₁ ν₂) (…prod…) ≤ ENNReal.ofReal lam * klDiv ν₁ (…) + ENNReal.ofReal (1 - lam) * klDiv ν₂ (…)` |
| KL の**左引数のみ**の狭義凸性（pmf 形） | `InformationTheory.Shannon.CsiszarProjection.klDivPmf_strictConvexOn_left` | `InformationTheory/Shannon/CsiszarProjection.lean:99` | `[Fintype α]` | `StrictConvexOn ℝ (stdSimplex ℝ α) fun P => klDivPmf P Q`（`(hQ_pos : ∀ a, 0 < Q a)` 付き） |
| スカラー核 | `InformationTheory.convexOn_klFun` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` | 無し | `ConvexOn ℝ (Set.Ici 0) InformationTheory.klFun` |
| 同（狭義） | `InformationTheory.strictConvexOn_klFun` | 同上 | 無し | `StrictConvexOn ℝ (Set.Ici 0) InformationTheory.klFun` |

⚠ **`klDivPmf_strictConvexOn_left` は片側だけ**なので本件には**足りない**
（`q(u)` を動かすと `p(v,z)` と `p(z)` が**両方**動く）。

**Mathlib 側の 0 件（逐語）**:

| クエリ（逐語） | 出力（逐語） |
|---|---|
| `ConvexOn, InformationTheory.klDiv` | `Found 0 declarations mentioning InformationTheory.klDiv and ConvexOn.` |
| `ConvexOn, InformationTheory.klFun, Finset.sum` | `Found 0 declarations mentioning InformationTheory.klFun, Finset.sum, and ConvexOn.` |

⟹ Mathlib の `klDiv` には**凸性補題が 1 本も無い**（同時どころか片側も）。スカラーの `klFun` の凸性で
止まっている。⚠ これは前在庫が触れていなかった事実である。

⚠ **`klDiv_joint_convex` の `(_hlam₀ : 0 ≤ lam) (_hlam₁ : lam ≤ 1)` は本体で未使用**
（アンダースコア接頭辞、`Convexity.lean:282` 逐語）。不使用仮定は言明を**弱く**するだけなので
honesty 上の欠陥ではないが、消費時に「この 2 本を供給しないと通らない」と誤読しないこと。

### 9.3 Q3 — Gibbs / 変分表示ルート（**ルート B は不成立**）

指示された 7 ファイルを実際に開いた結果:

| ファイル | 在るもの | 変分表示として使えるか |
|---|---|---|
| `Shannon/EPI/G2/KLVariationalLower.lean:87` | `klDiv_variational_lower_bound` | ⚠ **片側 (`≤`) のみ**。下記逐語 |
| `Shannon/CsiszarProjection.lean:99` | `klDivPmf_strictConvexOn_left` | ✗ 左引数のみ（§9.2） |
| `Shannon/MaxEntropy/Basic.lean:230,266` | **Gibbs *不等式*** `H ≤ log \|α\|` とその等号条件 | ✗ 変分表示ではない（名前が紛らわしい） |
| `Fano/Entropy.lean` / `Fano/BinaryJensen.lean:33` | `ConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy` | ✗ 二値スカラー |
| `Shannon/RateDistortion/Convexity.lean` | §9.2 の 3 本 | ○ ただし変分表示ではなく直接の凸性 |
| `Shannon/WynerZiv/ObjectiveConvexity.lean:212` | `WynerZivCondEntDiffConvex`（`Prop` 述語） | — 述語。実体は §9.1 |
| `Shannon/MultipleAccess/TimeSharing.lean:566` | `Convex ℝ (macCapacityRegion W)` | ✗ 領域の凸性 |

```
-- InformationTheory/Shannon/EPI/G2/KLVariationalLower.lean:87-91 逐語
theorem klDiv_variational_lower_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    {g : α → ℝ} (hg_meas : Measurable g) {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) :
    (∫ x, g x ∂μ) - Real.log (∫ x, Real.exp (g x) ∂ν) ≤ (klDiv μ ν).toReal
```

⚠ **Donsker–Varadhan の `≤` 方向だけ**である。「アフィン族の `inf` ⟹ 凹」を回すには
**等号 / 上限到達**が要るが、それは in-project に無い。さらに Mathlib 側のコンビネータも無い:

| クエリ（逐語） | 出力（逐語） |
|---|---|
| `ConcaveOn _ _ (fun _ => iInf _)` | `Found 0 declarations mentioning iInf and ConcaveOn.` / `Of these, 0 match your pattern(s).` |
| `"convexOn_iSup"` | `Found 0 declarations whose name contains "convexOn_iSup".` |

⟹ **ルート B（Gibbs 変分）は「片側だけの資産 + コンビネータ 0 件」で二重に詰まっている。**
仮に採るなら (i) 上限到達の証明 + (ii) `ConcaveOn` の `iInf` コンビネータ自作の 2 本が新規に立つ。
**ルート C（§9.1.3、45 行 / 新規 0 本）と比べる意味が無い。**

### 9.4 Q4 — `ConvexOn` コンビネータ在庫（`#check` の逐語）

**在る**（すべて Mathlib、`#check @…` 逐語の型クラス前提つき）:

| decl | 型クラス前提（逐語） | 結論形（逐語） |
|---|---|---|
| `ConvexOn.comp_linearMap` | `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid β] [PartialOrder β] [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]` | `ConvexOn 𝕜 s f → ∀ (g : E →ₗ[𝕜] F), ConvexOn 𝕜 (⇑g ⁻¹' s) (f ∘ ⇑g)` |
| `ConvexOn.comp_affineMap` | `[Field 𝕜] [LinearOrder 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommMonoid β] [PartialOrder β] [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]` | `ConvexOn 𝕜 s f → ConvexOn 𝕜 (⇑g ⁻¹' s) (f ∘ ⇑g)`（`(g : E →ᵃ[𝕜] F)` は明示引数） |
| `ConcaveOn.comp_affineMap` | 同上 | `ConcaveOn 𝕜 s f → ConcaveOn 𝕜 (⇑g ⁻¹' s) (f ∘ ⇑g)` |
| `ConvexOn.add` | `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [DistribMulAction 𝕜 β]` | `ConvexOn 𝕜 s f → ConvexOn 𝕜 s g → ConvexOn 𝕜 s (f + g)` |
| `ConvexOn.sub` | `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]` | `ConvexOn 𝕜 s f → **ConcaveOn** 𝕜 s g → ConvexOn 𝕜 s (f - g)` |
| `ConvexOn.smul` | `[CommSemiring 𝕜] [PartialOrder 𝕜] … [PosSMulMono 𝕜 β]` | `0 ≤ c → ConvexOn 𝕜 s f → ConvexOn 𝕜 s fun x => c • f x` |
| `ConvexOn.neg` / `ConcaveOn.neg` | `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]` | `ConvexOn 𝕜 s f → ConcaveOn 𝕜 s (-f)` / `ConcaveOn 𝕜 s f → ConvexOn 𝕜 s (-f)` |
| `ConvexOn.subset` | `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 E] [SMul 𝕜 β]` | `ConvexOn 𝕜 t f → s ⊆ t → Convex 𝕜 s → ConvexOn 𝕜 s f` |
| `LinearMap.convexOn` | `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid β] [PartialOrder β] [Module 𝕜 E] [Module 𝕜 β]` | `(f : E →ₗ[𝕜] β) → Convex 𝕜 s → ConvexOn 𝕜 s ⇑f` |
| `convexOn_const` | `[Semiring 𝕜] [PartialOrder 𝕜] … [Module 𝕜 β]` | `(c : β) → Convex 𝕜 s → ConvexOn 𝕜 s fun x => c` |
| `Real.concaveOn_negMulLog` | 無し | `ConcaveOn ℝ (Set.Ici 0) Real.negMulLog` |
| `Real.strictConcaveOn_negMulLog` | 無し | `StrictConcaveOn ℝ (Set.Ici 0) Real.negMulLog` |
| `Real.convexOn_mul_log` | 無し | `ConvexOn ℝ (Set.Ici 0) fun x => x * Real.log x` |
| `convex_Ici` | — | `Convex 𝕜 (Set.Ici _)` |

⚠ **`LinearMap.convexOn` + `convexOn_const` が在るので、文献分解の「線型な項」と「定数項」は
1 行ずつで載る**（自作ゼロ）。

**無い**（Mathlib、逐語 0 件）:

| 欲しかったもの | クエリ（逐語） | 出力（逐語） | 代替 |
|---|---|---|---|
| perspective 関数 | `"perspective"` | `Found 0 declarations whose name contains "perspective".` | **ルート A は Mathlib 資産ゼロから** ⟹ 却下 |
| `ConvexOn.sum`（有限和） | `"ConvexOn.sum"` | `Found 0 declarations whose name contains "ConvexOn.sum".` | **in-project に `ConcaveOn` 版が在る**（下記） |
| `iSup` / `iInf` 版 | `"convexOn_iSup"` / `ConcaveOn _ _ (fun _ => iInf _)` | 両方 0 件 | ルート B が詰まる主因（§9.3） |

**`ConvexOn.sum` の in-project 代替（`#check` 逐語）**:

```
@InformationTheory.Shannon.Portfolio.concaveOn_finset_sum : ∀ {E : Type u_1} [inst : AddCommMonoid E]
  [inst_1 : Module ℝ E] {s : Set E},
  Convex ℝ s →
    ∀ {ι : Type u_2} (f : ι → E → ℝ) (t : Finset ι),
      (∀ i ∈ t, ConcaveOn ℝ s (f i)) → ConcaveOn ℝ s fun x => ∑ i ∈ t, f i x
```

`InformationTheory/Shannon/Portfolio/Basic.lean:93`（`Convexity.lean:91-92` のコメントが
「Mathlib lacks a `ConcaveOn.sum`」と逐語で述べている）。⚠ **`ConcaveOn` 版しか無い**ので
`ConvexOn` 版が要るなら `.neg` で挟むか同型の 10 行を写す。
⚠ ただし**ルート C ではこれを使わない**（`negCondEnt_convexOn` が和ごと 1 本で出るため）。

### 9.5 Q5 — §4.5 の「`entropy` の橋は `rfl`」の逐語確認 → **正しい**

```lean
-- InformationTheory/Shannon/Bridge.lean:39-41 逐語（今回 Read で再確認）
/-- Shannon entropy of a discrete random variable taking values in a finite alphabet. -/
noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
  ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})
```

⚠ 同ファイル `:34-37` の `variable` ブロックは
`{Ω : Type*} [MeasurableSpace Ω]` / `{X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
[MeasurableSpace X] [MeasurableSingletonClass X]` である（`entropy` の署名に載る）。

**判定: §4.5 の主張は正しい。ただし方向と水準を分けて読むこと（⚠ 我々の演繹）**:

- **測度 → ベクトル / 水準 1（`entropy` の展開）**: `entropy μ Xs = ∑ x, negMulLog (P.real {x})`
  （`P := μ.map Xs`）は**定義的一致**。`MaxEntropy/Basic.lean:244` が実際に `:= rfl` で書いている
  ⟹ **この段だけは `rfl`、コスト 0**。
- ⚠ **測度 → ベクトル / 水準 2（marginal の分解）は `rfl` ではない**（L11 の実測。前版はこの 2 水準を
  分けずに「橋は `rfl`、コスト 0」と書いていた）。`(μ.map g).real {x}` を `∑ u, q u * k u x` の形へ
  書き換える段は**周辺化の計算**であり、`map_real_singleton_fiber_sum`
  (`InformationTheory/Probability/SingletonMass.lean:35`) で fiber 和へ開いてから
  `martonJointDistribution_real_singleton`
  (`Shannon/BroadcastChannel/Marton/MarkovCore/Prelim.lean:63`) を各項に当てる 2 段が要る。
  ⚠ **壁ではない** — この 2 資産の合成で埋まり、L11 で実測 95 行 / proof done（§10）。
- **ベクトル → 測度**: 逆向き（任意の `q : X → ℝ` を測度に持ち上げる）は `rfl` ではなく
  `pmfToMeasure` + `pmfToMeasure_apply_singleton`（§4.5 の表）を経由する。

⟹ **本 leg の座標化は「測度 → ベクトル」向きだけで足りる**（`f` はベクトル上で定義し、
消費側で `entropy` に `rfl` で戻す）ので、§4.5 の「座標化は安い」は**維持される**。
⚠ 前提は崩れていないが、「安い」の内訳は「水準 1 が 0 行 / 水準 2 が §10 の実測」である。

### 9.6 Q6 — in-project 凸性資産の棚卸し（**前在庫の主張を一部修正**）

実測: `rg -l 'ConvexOn|ConcaveOn|Convex ℝ' InformationTheory/` = **27 ファイル**
（前在庫のブリーフは 34 と述べていたが実測は 27）。そのうち
**エントロピー / 相互情報量 / KL の凹凸そのものを述べているもの**だけを抜くと:

| # | decl | file:line | 型クラス前提（逐語） | 結論形（逐語） |
|---|---|---|---|---|
| 1 | `InformationTheory.Shannon.negMulLog_marginal_gap_le_joint_gap` | `Shannon/WynerZiv/ConditionalEntropyConvexity.lean:75` | `[Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]` | §9.1.1 に逐語 |
| 2 | `InformationTheory.Shannon.wzCondEntDiff_block_convex` | 同 `:213` | `[Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β] (U) [Fintype U] [MeasurableSpace U]` | `∑ y, (wzMarginalYU U (a • q₁ + b • q₂) (y, u)).negMulLog - ∑ x, (wzMarginalXU U (a • q₁ + b • q₂) (x, u)).negMulLog ≤ a * (…) + b * (…)` |
| 3 | `InformationTheory.Shannon.wynerZivCondEntDiffConvex_holds` | 同 `:354` | 同上 | `(∀ p, 0 ≤ P_XY p) → WynerZivCondEntDiffConvex U P_XY` |
| 4 | `InformationTheory.Shannon.klDiv_joint_convex` | `Shannon/RateDistortion/Convexity.lean:280` | `[MeasurableSpace Ω] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]` | §9.2 に逐語 |
| 5 | `InformationTheory.Shannon.klDiv_mixture_le` | 同 `:336` | `[MeasurableSpace α] [MeasurableSpace β] [IsProbabilityMeasure P] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]` | §9.2 に逐語 |
| 6 | `InformationTheory.Shannon.rateDistortionFunction_convexOn` | 同 `:378` | `[MeasurableSpace α] [MeasurableSpace β] [IsProbabilityMeasure P]` | `rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂) ≤ ENNReal.ofReal lam * rateDistortionFunction d P D₁ + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P D₂` |
| 7 | `InformationTheory.Shannon.CsiszarProjection.klDivPmf_strictConvexOn_left` | `Shannon/CsiszarProjection.lean:99` | `[Fintype α]` | `StrictConvexOn ℝ (stdSimplex ℝ α) fun P => klDivPmf P Q` |
| 8 | `InformationTheory.Shannon.WynerZiv…` の述語 `WynerZivCondEntDiffConvex` | `Shannon/WynerZiv/ObjectiveConvexity.lean:212` | `[Fintype α] [Fintype β] (U) [Fintype U] [MeasurableSpace U]` | `Prop`（述語。実体は #3） |
| 9 | `InformationTheory.Shannon.BroadcastChannel.Marton.martonRegion_convex` | `Shannon/BroadcastChannel/MartonUnion.lean:133` | `[MeasurableSpace α] [Fintype β₁] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂] [Fintype V₁] [MeasurableSpace V₁] [Fintype V₂] [MeasurableSpace V₂]` | `Convex ℝ (martonRegion pV K W)` |

（除外したもの: `binEntropy` の凹性 (`Fano/BinaryJensen.lean:33`)、`log(1+x/N)` の凹性
(`DifferentialEntropy.lean:786` / `ShannonHartley/Waterfill.lean:85` / `AWGN/ConverseCapacityBound.lean:541`)、
`growthRate` の凹性 (`Portfolio/Basic.lean:141`)、Chernoff / Hoeffding の凸性、領域の凸性
(`TimeSharing.lean:566` ほか) — いずれもエントロピー汎関数の凹凸ではない。）

**判定**: 「BC 家系の `Convex` は `martonRegion_convex` 1 本のみ」（§8.2 の 2. 逐語）は
**BC 家系に限れば正しい**。しかし前在庫は **#1–#6 の 6 本を数えていない** — これらは
`WynerZiv` / `RateDistortion` 家系に在り、**本 leg の凸核そのもの**である。
⚠ **これが本調査の最も重要な発見**であり、CLAUDE.md「Search in-project before concluding 絶対」
（Shannon–Hartley Leg B Leaf 2 の実例: 一般形が **2 ファイル隣の同家系**に在った）の再現である。

### 9.7 ルート比較 — **C を採る**

| ルート | 核 | Mathlib 資産 | in-project 資産 | 見積り | 判定 |
|---|---|---|---|---|---|
| **C. WZ 資産の再利用** ✓ | `negMulLog_marginal_gap_le_joint_gap` を移項 | 不要（コンビネータのみ） | **proof done で在る** | **45 行 / 新規補題 0**（機械検証済） | **✓ 採用** |
| A. perspective 同時凸性 | `(a,b) ↦ a·log(a/b)` の同時凸性 | **`"perspective"` = 0 件** | 無し | 同時凸性の自作 120–200 行 + 和への持ち上げ | ✗ |
| B. Gibbs 変分 | `H(V\|Z) = inf_r …` + アフィン族の inf | **`iInf` コンビネータ 0 件** | **片側 (`≤`) のみ** | 上限到達 + コンビネータ自作、200 行超 | ✗ |
| D. measure 形 KL 同時凸性 | `klDiv_joint_convex` | 0 件 | **proof done で在る** | `ℝ≥0∞ → ℝ` の `.toReal` 橋 + 有限性 + `IsFiniteMeasure` 供給で 80–150 行 | ⚠ **不要（C が通過）** |

⚠ **D を予備としていた理由と、それが消えた経緯**: C は `Fintype V/Z` のベクトル形で完結するが、
消費側の `martonInfo₁ / martonInfo₂ / martonInfoV₁V₂` は**測度形**である（`martonRegion_convex` の
署名逐語: `pV : Measure (V₁ × V₂)` / `K : Kernel (V₁ × V₂) α`）。C を採る場合、
§9.5 の「測度 → ベクトル」で降ろす段が要る。**その段が L11 で proof done で通った**（§10）ので、
**D は逃げ道として不要になった**。⚠ ただし `klDiv_joint_convex` 自体は在庫として生きている
（別の目的関数形が要る場合の資産、§9.2）。

### 9.8 自己構築が要る要素（優先順）

| # | 要素 | 推奨実装 | 見積り | 落とし穴 |
|---|---|---|---|---|
| 1 | `negCondEnt_convexOn`（`−H(V\|Z)` の凸性、ベクトル形） | §9.1.3 逐語をそのまま | **20 行**（機械検証済） | `∑ p : V × Z` と `∑ z, ∑ v` の順序差 — `Finset.sum_comm` + `Fintype.sum_prod_type` の 2 段が要る（`simp` の高階単一化は**発火しない**ので `rw [← hflip …]` を明示する） |
| 2 | `convex_nonneg_pi` | §9.1.3 逐語 | **3 行** | Mathlib の `convex_Ici` は `Set.Ici` 形。`{q \| 0 ≤ q}` との同一視を挟むより自作が短い |
| 3 | 線型写像との合成 | §9.1.3 の `negCondEnt_comp_convexOn` | **22 行**（機械検証済） | `ConvexOn.comp_linearMap` は `(⇑g ⁻¹' s)` を返すので `ConvexOn.subset` で `{q \| 0 ≤ q}` に落とす段が必須 |
| 4 | 線型項 `−H(Y\|U)+H(V\|U)` を載せる | `LinearMap.convexOn` + `ConvexOn.add` | ⚠ **#6 に吸収**（同じ 2 補題の再適用） | `q(u)` について線型であることの証明（`p₀(v,x\|u)` 固定の逐語確認が要る） |
| 5 | 定数項 `H(Y)` | `convexOn_const` / ⚠ 実際には `exists_support_card_le_of_convexOn_add_aggregate` の `g` | ⚠ **#6 に吸収** | 定数ではなく**集約 `p(x)` の関数**だった（`H(Y₁)` は `p(x)` から決まる）⟹ `convexOn_const` ではなく集約系で処理する |
| 6 | 測度形 ↔ ベクトル形の降ろし | §9.5 水準 1（`rfl`）+ `map_real_singleton_fiber_sum` + `martonJointDistribution_real_singleton` + `Measure.condKernel` 系 | ⚠ **40–90 行 → 105–175 行に改訂**（内訳は下記） | ⚠ 水準 2 は `rfl` ではない（§9.5）。`pmfToMeasure` は**この向きでは使わない** |

**#6 の内訳（L11 の実測に基づく改訂。⚠ 我々の演繹）**: master 補題（任意射影 `g` の 5 重和 + `if`）
25–40 行 / `(V₂,Y₂)`-周辺 atom 20–35 行 / `A` 行（`A u x = ∑ v₂, (κ u).real {v₂} * (K (u,v₂)).real {x}`）
とその行和 1 で 15–25 行 / `H(Y₁)` の集約表示 15–25 行 / `pV = q ⊗ₘ κ` の disintegration 20–40 行 /
集約系（`…_add_aggregate` への接続）8–12 行 ⟹ **105–175 行**。

**合計の見積り更新**: #4（30–60）と #5（5–10）は**同じ 2 補題の再適用**なので #6 に吸収され、
**#4+#5+#6 = 75–160 → 130–210 行**。⟹ §8.2 が (a′-1) = 480–800 行としたうちの
「部品 (3a) 凸性そのもの」は **120–210 → 175–275 行**（#1–#3 の 45 行が確定値）。
⚠ **これは §8.2 の (3a) 原予算 200–350 行の内側**である。
⚠ **総額 (a′-1) 480–800 行 + (a′-2) 60–120 行は動かさない** — 動いたのは (3a) の内数だけであり、
部品 1 / 2 / 4 は未着手のままである。⚠ 「凸性が既に在ったのだから全体が軽くなった」と読むのは
§7.4 / §9.10 の誤読の再演になる。

### 9.9 Mathlib の壁の列挙 — **本 leg に壁は 0 件**

⚠ **`@residual(wall:…)` は 1 本も切らない。** 以下は「Mathlib に無い」という事実の列挙であり、
**すべて in-project 資産または 45 行の自作で埋まる**ので壁ではない
（親プラン `bc-open-problem-t3-plan.md` **§5「leg 予算と配分」**の leg 台帳
「⚠ `@residual(wall:…)` は切らない」の項 / facts §L7 行 7 の判定と整合。
⚠ 行番号での参照は leg ごとにずれるので**節名で参照する**）。

| Mathlib に無いもの | loogle 逐語 | 埋め方 | 壁か |
|---|---|---|---|
| 条件付きエントロピー（概念ごと） | `"condEntropy"` → `Found 0 declarations whose name contains "condEntropy".` | in-project #1（§9.6） | **否** |
| 相互情報量（概念ごと） | `"mutualInfo"` → `Found 0 declarations whose name contains "mutualInfo".` | in-project `mutualInfoPmf`（§4.5） | **否** |
| `klDiv` の凸性（同時・片側とも） | `ConvexOn, InformationTheory.klDiv` → `Found 0 declarations mentioning InformationTheory.klDiv and ConvexOn.` | in-project #4（§9.6） | **否** |
| perspective 関数 | `"perspective"` → `Found 0 declarations whose name contains "perspective".` | **不要**（ルート A を採らない） | **否** |
| `ConvexOn.sum`（有限和） | `"ConvexOn.sum"` → `Found 0 declarations whose name contains "ConvexOn.sum".` | in-project `concaveOn_finset_sum` / ルート C では不要 | **否** |
| `iSup`/`iInf` の凸凹コンビネータ | `"convexOn_iSup"` → 0 件 / `ConcaveOn _ _ (fun _ => iInf _)` → 0 件 | **不要**（ルート B を採らない） | **否** |

⟹ **共有 sorry 補題の候補は無い。** 本 leg で `sorry` を置く必要のある命題が 1 本も見つからなかった。

### 9.10 撤退ラインとの距離 — **3 本とも触れない / 発火しない**

| 親 §6 の撤退ライン | 触れるか | 判定 |
|---|---|---|
| L8 の棚卸しで T3-α が gate を通らず T3-β / γ も第一手を返さない | **触れない** | 本節は L10 の部品調査。むしろ gate の残り 1 部品 (3a) が**通った**（§9.0） |
| L14 の棚卸しで層 3 に載せられる散文が 1 本も無い | **触れない** | (a′) が生きているどころか、その最重量部品の見積りが下がった |
| 20 leg を使い切って未達 | **触れない** | L10 時点。予算は §9.8 のとおり総額据え置き |

⚠ **§6.5 の予算警告（層 3 集中枠 L16–L18 を基数境界 1 本が埋めうる）は依然有効**である。
(3a) が 200–350 行 → 120–210 行に下がっただけで、部品 1 / 2 / 4 と (a′-2) は手つかずである。
**「凸性が既に在ったのだから全体が軽くなった」と読むのは §7.4 の誤読の再演**になる。

### 9.11 着手スケルトン

新規ファイル `InformationTheory/Shannon/BroadcastChannel/Marton/ObjectiveConvexity.lean`
（`SupportReduction.lean` の隣）。⚠ §9.1.3 の 3 本は**既に `lake env lean` clean**なので、
`sorry` を置くのは #4–#6 の段だけでよい。

```lean
import InformationTheory.Shannon.BroadcastChannel.Marton.SupportReduction
import InformationTheory.Shannon.WynerZiv.ConditionalEntropyConvexity
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of the Marton objective in the auxiliary weights

The support-reduction mechanism (`SupportReduction.lean`) consumes a convex objective on the
nonnegative orthant.  This file supplies that objective for the Marton inner bound: with the
conditional law `p(v, x | u)` held fixed, the weighted sum of the three Marton functionals is
convex in the weight vector `q`.

## Main statements

* `negCondEnt_convexOn` — the negated conditional entropy is convex in the joint law.
* `martonObjective_convexOn` — the Marton objective is convex in the auxiliary weights.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open InformationTheory.Shannon Finset

variable {V Z U : Type*} [Fintype V] [Fintype Z] [Fintype U]
  [MeasurableSpace V] [MeasurableSpace Z]

-- §9.1.3 の 3 本をここに置く（機械検証済、sorry 不要）
theorem negCondEnt_convexOn : … := …
theorem convex_nonneg_pi {ι : Type*} : Convex ℝ {q : ι → ℝ | 0 ≤ q} := …
theorem negCondEnt_comp_convexOn (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) : … := …

-- 残る段（#4–#6）。ここだけ sorry + @residual(plan:bc-open-problem-t3) で立てる
theorem martonObjective_convexOn
    (k : U → V × Z → ℝ) (hk : ∀ u p, 0 ≤ k u p) (lin : (U → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ {q : U → ℝ | 0 ≤ q}
      (fun q ↦ c + lin q
        + ((∑ z, Real.negMulLog (∑ v, ∑ u, q u * k u (v, z)))
            - ∑ p : V × Z, Real.negMulLog (∑ u, q u * k u p))) :=
  ((convexOn_const c convex_nonneg_pi).add (lin.convexOn convex_nonneg_pi)).add
    (negCondEnt_comp_convexOn k hk)

end InformationTheory.Shannon.BroadcastChannel.Marton
```

⚠ 最後の `martonObjective_convexOn` の**証明項は未検証**（`ConvexOn.add` の連鎖が
`fun q ↦ c + lin q + …` の構文形にそのまま当たるかは実装時に確認）。
⚠ **`martonInfo₁ / martonInfo₂ / martonInfoV₁V₂`（測度形）をこの `f` に載せる段は本調査の範囲外**
であり、そこが §9.8 の #6 = C ルートの唯一の未検証段である。実装は gateway-atom-first で
#6 を 1 本投げてから残りを決めること。⟹ **その 1 本は L11 で通った（§10）**。

---

## §10 L11–L12 の実測 — 測度形 → ベクトル形の降ろし

### 10.0 一行判定

**§9.8 の #6（C ルートの唯一の未検証段）は 3 汎関数が要る 7 射影すべてが proof done で降り、壁は 0 件。**
L11 の gateway atom に続き、L12 で残り 6 射影 + 集約行 + 行和 1 が `@[entry_point]` で landing（§10.1）。
残件は **1 つだけ**（`pV = q ⊗ₘ κ` の disintegration、§10.3）で、その先は目的関数の組み立て。
⚠ 実測は見積りを超えた（§10.7）が、超過は §8.2 の (3a) の**内数の再配分**として記録するのみで、
**総額（(a′-1) 480–800 行 + (a′-2) 60–120 行）は据え置き**。

### 10.1 landing した宣言（すべて `sorry` 0 / `@residual` 0）

| decl | file:line | 型クラス前提（逐語） | 結論形 |
|---|---|---|---|
| `marton_map_V₂Y₂_real_singleton_eq_sum` `@[entry_point]` | `Shannon/BroadcastChannel/Marton/ObjectiveVectorForm.lean:274` | `[Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]`（`V₂ α β₁ β₂` も同型の 4 本ずつ）+ 引数側の `[IsProbabilityMeasure q] [IsMarkovKernel κ] [IsMarkovKernel K] [IsMarkovKernel W]` | `((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ (p.2.1, p.2.2.2.2))).real {(v₂, y₂)} = ∑ u : V₁, q.real {u} * ((κ u).real {v₂} * ∑ x : α, (K (u, v₂)).real {x} * ∑ y₁ : β₁, (W x).real {(y₁, y₂)})` |
| `martonJointDistribution_map_real_singleton` `[private]` | 同 `:64` | 上記 + `{γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq γ]` | 任意射影 `g` について 5 重和 + `if` の master 形（他の 5 本のエントロピーもこれの再適用で出る） |
| `martonAuxRow`（def）/ `sum_martonAuxRow_eq_one` `@[entry_point]` | 同 `:61` / `:114` | 変数ブロックは上と同（後者は `omit [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [Nonempty α] in` 付き）+ `[IsMarkovKernel κ] [IsMarkovKernel K]` | `martonAuxRow κ K u x = ∑ v₂ : V₂, (κ u).real {v₂} * (K (u, v₂)).real {x}` / `∑ x : α, martonAuxRow κ K u x = 1`（= §10.3 前版が挙げた「保存すべき行」と「行和 1」） |
| `marton_map_X_real_singleton_eq_sum` `@[entry_point]` | 同 `:128` | 変数ブロックは上と同 + `[IsProbabilityMeasure q] [IsMarkovKernel κ] [IsMarkovKernel K] [IsMarkovKernel W]` | `((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ p.2.2.1)).real {x} = ∑ u : V₁, q.real {u} * martonAuxRow κ K u x`（= 集約の実体） |
| `marton_map_V₁_real_singleton_eq` / `marton_map_V₂_real_singleton_eq_sum` / `marton_map_V₁V₂_real_singleton_eq` / `marton_map_V₁Y₁_real_singleton_eq_sum` `@[entry_point]` | 同 `:150` / `:179` / `:208` / `:240` | 同上 | 順に `… .real {u} = q.real {u}` / `= ∑ u : V₁, q.real {u} * (κ u).real {v₂}` / `= q.real {u} * (κ u).real {v₂}` / `= q.real {u} * ∑ v₂ : V₂, (κ u).real {v₂} * ∑ x : α, (K (u, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)}` |
| ⚠ `marton_map_Y₁_real_singleton_eq_aggregate` / `marton_map_Y₂_real_singleton_eq_aggregate` `@[entry_point]` | 同 `:301` / `:333` | 同上 | `((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ p.2.2.2.1)).real {y₁} = ∑ x : α, (∑ u : V₁, q.real {u} * martonAuxRow κ K u x) * ∑ y₂ : β₂, (W x).real {(y₁, y₂)}`（`Y₂` 版は `β₁`/`β₂` を入替え）。⚠ 右辺が `q` を**集約を通してのみ**読むことが構文で見える = `exists_support_card_le_of_convexOn_add_aggregate` の `g` に載る根拠 |
| `exists_support_card_le_of_convexOn_add_aggregate` `@[entry_point]` | `…/Marton/SupportReduction.lean:219` | `{ι : Type*} [Fintype ι] {X : Type*} [Fintype X]` | `f q + g (fun x ↦ ∑ i, q i * A i x) ≤ f q' + g (fun x ↦ ∑ i, q' i * A i x)` ほか 3 連言。⚠ **`g` に凸性も可測性も仮定しない** |
| `auxWeightObjective`（`t : ℝ` slot 追加） | `…/Marton/ObjectiveConvexity.lean:86` | `[Fintype U] [Fintype V] [Fintype Z] [Fintype X]` | `c + (∑ u, q u * w u) + t * ((∑ z, negMulLog (∑ v, ∑ u, q u * k u (v, z))) - ∑ p : V × Z, negMulLog (∑ u, q u * k u p))` |
| `convexOn_auxWeightObjective` / `exists_support_card_le_auxWeightObjective` | 同 `:94` / `:103` | 同上 | ⚠ **`(ht : 0 ≤ t)` が追加**（`ConvexOn.smul` で 1 行） |

### 10.2 消費した既存資産（新規補題を書かずに済んだもの）

| 資産 | file:line | 何を与えたか |
|---|---|---|
| `InformationTheory.map_real_singleton_fiber_sum` | `InformationTheory/Probability/SingletonMass.lean:35` | `(μ.map f).real {x}` を fiber 上の `μ.real` の和へ開く（`[SigmaFinite μ]` + `[DecidableEq δ]` が要る） |
| `…Marton.martonJointDistribution_real_singleton` | `…/Marton/MarkovCore/Prelim.lean:63` | 5 つ組の singleton 質量 = `pV.real * (K _).real * (W _).real` |
| `…Shannon.jointDistribution_singleton` | `Shannon/IIDProductInput/Basic.lean:244` | `⊗ₘ` の singleton 質量（`ℝ≥0∞` 形。`.real` 形は §10.5） |

### 10.3 残件 1 つ（§9.8 #6 の未着手分）

⚠ 前版が挙げた 4 件のうち 3 件 — 集約行 `A u x = ∑ v₂, (κ u).real {v₂} * (K (u,v₂)).real {x}` と
その行和 1 / 線型項 `w`（`H(Y₁\|V₁)` と `H(κ_u)`）の射影 / `H(Y₁)` の集約表示 — は L12 で
closing した（§10.1 の下 4 行。いずれも型クラス前提の追加なし）。残るのは次の 1 件のみ。

| 残件 | 見込みの経路 | ⚠ 型クラス前提の逐語確認 |
|---|---|---|
| `pV = q ⊗ₘ κ` の disintegration | `Measure.disintegrate` (`Mathlib/Probability/Kernel/Disintegration/Basic.lean:63`) + `Measure.condKernel.instIsCondKernel` (`…/StandardBorel.lean:370`) + `Measure.instIsMarkovKernelCondKernel` (`同:382`) | ⚠ **`[StandardBorelSpace Ω] [Nonempty Ω]`**（`…/StandardBorel.lean:77` の `variable` 逐語）**+ `[IsFiniteMeasure ρ]` を要求する**。BC 家系では `[Fintype _] → [Countable _]` と `[MeasurableSingletonClass _]` から `MeasurableSingletonClass.toDiscreteMeasurableSpace` (`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:551`) → `standardBorelSpace_of_discreteMeasurableSpace` (`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:119`) で解決し、`[Nonempty V₂]` は変数ブロックに既在 ⟹ **署名に増えない**（前例 `Shannon/Entropy.lean:53` も同じ経路） |

### 10.4 設計判断（⚠ 我々の演繹）

- **`pV = q ⊗ₘ κ` の disintegration は必須**。代替案「`U := V₁ × V₂` として `q := pV` 全体を動かす」は
  **却下**: そのとき線型項だった `H(V₂|V₁)` が `q` について**凹**になり
  （`convexOn_negCondEntropy` (`…/Marton/ObjectiveConvexity.lean:43`) が `−H(V|Z)` の同時法則に関する
  凸性を述べている = `H(V₂|V₁)` は同時法則について凹）、`auxWeightObjective` の線型 slot に載らない。
- **`t : ℝ` slot の必要性**: 凸括弧の係数は §8.2 の展開で `μ₂ + μ₃` になり、退化重み `0` も取る
  ⟹ 係数 1 固定では届かない。`(ht : 0 ≤ t)` は `ConvexOn.smul`（§9.4 の表）の前提そのもので、
  **`μ ≥ 0` から自動で供給される**（load-bearing ではなく regularity）。

### 10.5 掃除候補（低優先）

`(pV ⊗ₘ K).real {(p,x)} = pV.real {p} * (K p).real {x}` の `have` が
`…/Marton/MarkovCore/Receiver1.lean:571` / `Receiver2.lean:500` の `have hcompProd` と、L12 で
`private lemma compProd_real_singleton_mul` (`ObjectiveVectorForm.lean:86`) として括り出した 1 本の
**3 箇所に重複**している（いずれも `jointDistribution_singleton` + `jointDistribution_def` +
`ENNReal.toReal_mul` の同じ 4 行で、Marton 固有の要素をひとつも含まない）。公開 1 本を
`InformationTheory/Probability/SingletonMass.lean` か `…/Marton/MarkovCore/Prelim.lean` に置けば
3 箇所が一度に消える ⟹ 新規追加なので**波及 0**。

### 10.6 壁と撤退ライン

⚠ **L11 / L12 のいずれでも `@residual(wall:…)` は 1 本も立っていない / 共有 sorry 補題の候補も 0 件。**
§9.9 の壁 0 件判定はそのまま有効で、追加すべき行も無い。
撤退ライン 3 本（親プラン §6）は**どれも触れず、発火しない** — L11 は §9.8 #6 の gateway atom、
L12 はその残り 6 射影の同型反復であり、軸の gate でも層 3 の棚卸しでもない。
⚠ §6.5 の予算警告は依然有効（§9.10）。

### 10.7 ⚠ 見積りとの差（L12 の実測。総額は動かさない）

- **行数**: 見積り 120–200 行に対し**実測 +267 行**（`ObjectiveVectorForm.lean` 95 → 362 行）。
  増分は master 補題（§10.1）が返す 5 重和の `if` を潰す**定型句**であって新規の数学ではない
  — `compProd_real_singleton_mul` / `sum_bcChannel_real_singleton_eq_one` /
  `sum_compProd_mul_kernel_real_singleton` など private 補助 4 本
  （`ObjectiveVectorForm.lean:64`–`:109`）に括り出して圧縮済み。⚠ 超過は §8.2 の (3a) の
  **内数の再配分**として記録するだけであり、「全体が軽く / 重くなった」ではない（§7.4 の誤読の再演を避ける）。
- **和の順序入れ替えは想定より軽かった**: 前版が「最も手数が要る見込み」とした `Y₁`/`Y₂` の
  3 重和の巡回置換は Mathlib の `Finset.sum_comm_cycle` **1 本**で片付いた
  （`ObjectiveVectorForm.lean:326` / `:358` で両定理とも一発でコンパイル）。乗法版の逐語 =
  `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:127` `theorem prod_comm_cycle
  {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ → α → κ → β} :
  (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z) = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z`。
  加法版は同 `:126` の `@[to_additive]` 生成、型クラス前提は同 `:28` の `variable [CommMonoid β]`
  の加法版 `[AddCommMonoid β]` のみ。
- ⚠ **検索語の粒度の教訓**（逐語）: 名前を推測して丸ごと引く `loogle "Finset.sum_comm₃"` は
  `unknown identifier 'Finset.sum_comm₃'` を返すだけで実名に届かない。部分文字列クエリ
  `loogle '"sum_comm"'` は `Found 17 declarations whose name contains "sum_comm".` として
  `Finset.sum_comm_cycle` を出す。**名前を当てにいく前に部分文字列で引くこと**。

---

## §11 L13–L15 の実測 — 目的関数の組み立てと測度形への回収

⚠ 本節は**追記であり §1–§10 は書き換えていない**。ただし §10.3（残件 1 つ）と §8.2（C ルートの
射程）については、本節の実測が**外していた / 訂正の公算が高い**ことを明示する（§11.1 / §11.6）。

### 11.0 一行判定

**L13–L15 で新規に立った宣言は 19 本、すべて proof done（`sorry` 0 / `@residual` 0）で、
Mathlib 側の不足は 0 件**（壁 0 / 共有 sorry 補題の候補 0）。⚠ 再導出は
`scripts/sig_view.ts --sorry <file>` と `#print axioms <decl>`（本節は値をキャッシュしない）。
⚠ **§10.3 が「残件 1 つ」とした disintegration は新規宣言 0 本・実測 ~2 行で、代わりに §10.3 が
落としていた橋が 2 件あった**（§11.1）。標的言明 (a′-1) には**まだ 2 件の残件**があり、
うち 1 件（`V₂` 側）は次 leg の設計を決める分岐である（§11.6）。
⚠ **行数は (a′-1) の見積り 480–800 行を既に超えている**（実測 1070 行、§11.5）。

### 11.1 §10.3 の残件は外れていた — disintegration に新規宣言 0 本 / 代わりに漏れが 2 件

| 項目 | 実測 | 逐語の根拠 |
|---|---|---|
| `pV = q ⊗ₘ κ` の disintegration | ⚠ **新規宣言 0 本 / 消費側 1 行**。`pV.disintegrate pV.condKernel` が 1 term で `pV.fst ⊗ₘ pV.condKernel = pV` を返し、消費側は `conv_lhs => rw [← pV.disintegrate pV.condKernel]` で既存 7 射影がそのまま一般 `pV` に効く ⟹ §10.3 の見積り「20–40 行」に対し**実測 ~2 行** | `MeasureTheory.Measure.disintegrate`（`Mathlib/Probability/Kernel/Disintegration/Basic.lean:63`）の `#check` 逐語: `∀ {α : Type u_1} {Ω : Type u_2} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} (ρ : Measure (α × Ω)) (ρCond : Kernel α Ω) [ρ.IsCondKernel ρCond], ρ.fst ⊗ₘ ρCond = ρ` |
| 型クラス連鎖 3 段 | ⚠ **機械検証済で繋がる / import 追加 0 本 / 署名に増える前提 0 個**。最小前提は `[Countable V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]` + `[IsFiniteMeasure pV]` で、BC 家系の変数ブロックは `[Fintype V₂]` → `Countable` を含むのでそのまま通る | scratch で `example (pV : Measure (V₁ × V₂)) [IsFiniteMeasure pV] : pV.fst ⊗ₘ pV.condKernel = pV := pV.disintegrate pV.condKernel` が 0 error。連鎖の逐語 = `MeasurableSingletonClass.toDiscreteMeasurableSpace : ∀ {α} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α], DiscreteMeasurableSpace α` → `standardBorelSpace_of_discreteMeasurableSpace : ∀ {α} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace α` → `Measure.condKernel : … [StandardBorelSpace Ω] → [Nonempty Ω] → (ρ : Measure (α × Ω)) → [IsFiniteMeasure ρ] → Kernel α Ω`。`IsMarkovKernel pV.condKernel` / `IsProbabilityMeasure pV.fst` も `inferInstance` で出る |
| ⚠ **名前の罠** | **`MeasureTheory.Measure.compProd_fst_condKernel` は宣言として存在しない** — 在庫がこの名前を採ると unknown identifier。正しくは `Measure.disintegrate` | loogle 逐語 2 本: `loogle "MeasureTheory.Measure.compProd_fst_condKernel"` → `unknown identifier 'MeasureTheory.Measure.compProd_fst_condKernel'` / `loogle '"compProd_fst_condKernel"'` → `Found one declaration whose name contains "compProd_fst_condKernel".` `ProbabilityTheory.Kernel.compProd_fst_condKernelReal`。実体は `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean:63-64` の**docstring 内の文字列**（`## Main statements` の箇条書き）だけである |

⚠ **§10.3 の残件リストが落としていた橋が 2 件あった**。目的関数は `entropy`
（`InformationTheory/Shannon/Bridge.lean:40-41` 逐語:
`noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})`）
の和差なので、singleton 質量の**積形**を与える 7 射影（§10.1）だけでは `negMulLog` の側が繋がらない:

- **GAP A** = chain-rule 恒等式（`H(V₁,V₂) − H(V₁)` / `H(V₁,Y₁) − H(V₁)` を `q` について線型な形へ）。
  `Real.negMulLog_mul`（`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:177`、**前提なし**）で閉じ、
  private 補題 `sum_negMulLog_mul_sub_eq` 1 本（12 行）に括り出た。
- **GAP B** = `auxWeightObjective` が内部生成する `Y₂` 周辺が、既在の集約形
  `marton_map_Y₂_real_singleton_eq_aggregate`（`ObjectiveVectorForm.lean:344`）と一致すること。
  `Finset.sum_comm_cycle` 1 本 + `Finset.sum_comm` 1 本で閉じた
  （`ObjectiveVectorForm.lean:479` / `:484`）。

⟹ **教訓（⚠ 我々の演繹）**: 残件の洗い出しを「**測度側で何が要るか**」だけで作ると、
**目的関数側の関数形（`negMulLog` の中に何が入るか）で要る橋を落とす**。射影表と目的関数の
定義展開を**両側から突き合わせる**まで残件リストは閉じない。

### 11.2 landing した宣言の逐語署名（L13 / L14 / L15）

`ObjectiveVectorForm.lean:62-67` と `ObjectiveAssembly.lean:43-48` の変数ブロックは**逐語で同一**
（以下 **VB5** と呼ぶ。`#check` で elaborate して確認済）:

```lean
variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
```

⚠ **`ObjectiveConvexity.lean` の変数ブロックは別物**（`:39` 逐語）:
`variable {U V Z X : Type*} [Fintype U] [Fintype V] [Fintype Z] [Fintype X]` — **可測空間も
`MeasurableSingletonClass` も無いベクトル層**である。

**L13（`ObjectiveVectorForm.lean`、7 本）**

| decl | file:line | 型クラス前提（逐語） | 結論形（逐語） |
|---|---|---|---|
| `sum_negMulLog_mul_sub_eq` `[private]` | `…/Marton/ObjectiveVectorForm.lean:373` | 宣言自身の binder のみ = `{ι σ : Type*} [Fintype ι] [Fintype σ]`（VB5 は使わない）⚠ 外部からは `#check` 不可（`Unknown identifier` が返る = file-scoped private の逐語確認） | `(∑ i : ι, ∑ s : σ, Real.negMulLog (q i * c i s)) - ∑ i : ι, Real.negMulLog (q i) = ∑ i : ι, q i * ∑ s : σ, Real.negMulLog (c i s)`（仮引数 `(q : ι → ℝ) (c : ι → σ → ℝ) (hc : ∀ i, ∑ s : σ, c i s = 1)`） |
| `marton_entropy_V₁V₂_sub_entropy_V₁_eq_sum` `@[entry_point]` | 同 `:389` | VB5 全 20 個 + `(q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]` | `entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ (p.1, p.2.1)) - entropy (martonJointDistribution (q ⊗ₘ κ) K W) Prod.fst = ∑ u : V₁, q.real {u} * ∑ v₂ : V₂, Real.negMulLog ((κ u).real {v₂})` |
| `martonAuxOutput₁Row`（def） | 同 `:404` | `#check` 逐語 = `[MeasurableSpace V₁] [Fintype V₂] [MeasurableSpace V₂] [Fintype α] [MeasurableSpace α] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂]`（VB5 のうち def が実際に使う 8 個だけが残る） | `martonAuxOutput₁Row κ K W u y₁ = ∑ v₂ : V₂, (κ u).real {v₂} * ∑ x : α, (K (u, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)}` |
| `sum_martonAuxOutput₁Row_eq_one` `@[entry_point]` | 同 `:413` | VB5 から `omit [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [Nonempty α] [Nonempty β₁] [Nonempty β₂] in`（`:408-409` 逐語）+ `[IsMarkovKernel κ] [IsMarkovKernel K] [IsMarkovKernel W]` | `∑ y₁ : β₁, martonAuxOutput₁Row κ K W u y₁ = 1` |
| `marton_entropy_V₁Y₁_sub_entropy_V₁_eq_sum` `@[entry_point]` | 同 `:433` | VB5 全 20 個 + 上と同じ 4 引数 | `entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ (p.1, p.2.2.2.1)) - entropy (martonJointDistribution (q ⊗ₘ κ) K W) Prod.fst = ∑ u : V₁, q.real {u} * ∑ y₁ : β₁, Real.negMulLog (martonAuxOutput₁Row κ K W u y₁)` |
| `martonAuxKernelSlot`（def） | 同 `:450` | `#check` 逐語 = `[MeasurableSpace V₁] [MeasurableSpace V₂] [Fintype α] [MeasurableSpace α] [Fintype β₁] [MeasurableSpace β₁] [MeasurableSpace β₂]` | `martonAuxKernelSlot κ K W u p = (κ u).real {p.1} * ∑ x : α, (K (u, p.1)).real {x} * ∑ y₁ : β₁, (W x).real {(y₁, p.2)}`（型は `V₁ → V₂ × β₂ → ℝ`） |
| `sum_martonAuxKernelSlot_mixture_eq_aggregate` `@[entry_point]` | 同 `:461` | VB5 から `omit [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [MeasurableSingletonClass V₂] [Nonempty α] [MeasurableSingletonClass α] [Nonempty β₁] [MeasurableSingletonClass β₁] [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂] in`（`:454-456` 逐語）+ `[IsProbabilityMeasure q] [IsMarkovKernel κ] [IsMarkovKernel K] [IsMarkovKernel W]` | `∑ v₂ : V₂, ∑ u : V₁, q.real {u} * martonAuxKernelSlot κ K W u (v₂, y₂) = ∑ x : α, (∑ u : V₁, q.real {u} * martonAuxRow κ K u x) * ∑ y₁ : β₁, (W x).real {(y₁, y₂)}` |

**L14（受け口 1 本 + `ObjectiveAssembly.lean` 9 本）**

| decl | file:line | 型クラス前提（逐語） | 結論形（逐語） |
|---|---|---|---|
| `exists_support_card_le_auxWeightObjective_add_aggregate` `@[entry_point]` | `…/Marton/ObjectiveConvexity.lean:119` | `{U V Z X : Type*} [Fintype U] [Fintype V] [Fintype Z] [Fintype X]` **のみ**（`:39`）⟹ ⚠ 可測構造も `MeasurableSingletonClass` も要らない | `∃ q' : U → ℝ, 0 ≤ q' ∧ (∀ x, ∑ u, q' u * A u x = ∑ u, q u * A u x) ∧ auxWeightObjective k w c t q + g (fun x ↦ ∑ u, q u * A u x) ≤ auxWeightObjective k w c t q' + g (fun x ↦ ∑ u, q' u * A u x) ∧ {u \| q' u ≠ 0}.ncard ≤ Fintype.card X`（仮引数 `(A) (hA : ∀ u, ∑ x, A u x = 1) (k) (hk : ∀ u p, 0 ≤ k u p) (w) (c t : ℝ) (ht : 0 ≤ t) (g : (X → ℝ) → ℝ) (q) (hq : 0 ≤ q)`）。本体は `exists_support_card_le_of_convexOn_add_aggregate` + `convexOn_auxWeightObjective` の適用 1 term |
| `martonAuxCoeff`（def） | `…/Marton/ObjectiveAssembly.lean:53` | `#check` 逐語 = `[MeasurableSpace V₁] [Fintype V₂] [MeasurableSpace V₂] [Fintype α] [MeasurableSpace α] [Fintype β₁] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂]` | `martonAuxCoeff κ K W μ₁ μ₃ u = μ₃ * (∑ v₂ : V₂, Real.negMulLog ((κ u).real {v₂})) - (μ₁ + μ₃) * (∑ y₁ : β₁, Real.negMulLog (martonAuxOutput₁Row κ K W u y₁))` |
| `martonOutput₁Aggregate`（def） | 同 `:60` | `#check` 逐語 = `{α β₁ β₂} [Fintype α] [MeasurableSpace α] [Fintype β₁] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂]`（⚠ `V₁ V₂` に**依存しない** = 集約 slot `g` の実体である根拠） | `martonOutput₁Aggregate W μ₁ μ₃ a = (μ₁ + μ₃) * ∑ y₁ : β₁, Real.negMulLog (∑ x : α, a x * ∑ y₂ : β₂, (W x).real {(y₁, y₂)})` |
| `martonAuxKernelSlot_nonneg` / `sum_mul_martonAuxCoeff_eq_sub` / `sum_negMulLog_martonAuxKernelSlot_eq_entropy` / `sum_negMulLog_martonAuxKernelSlot_mixture_eq_entropy` / `martonOutput₁Aggregate_eq_mul_entropy` `[private]` | 同 `:66` / `:74` / `:90` / `:101` / `:112` | VB5 から各々 `omit …`（`:63-65` / `:71-73` の逐語。後ろ 3 本は omit 無し = VB5 全 20 個）+ 後ろ 3 本は `[IsProbabilityMeasure q] [IsMarkovKernel κ] [IsMarkovKernel K] [IsMarkovKernel W]` | 順に `0 ≤ martonAuxKernelSlot κ K W u p` / 係数ベクトルの和の分配 / `∑ p : V₂ × β₂, Real.negMulLog (∑ u : V₁, q.real {u} * martonAuxKernelSlot κ K W u p) = entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ (p.2.1, p.2.2.2.2))` / 同 `(fun p ↦ p.2.2.2.2)` の集約版 / `martonOutput₁Aggregate W μ₁ μ₃ (fun x ↦ ∑ u, q.real {u} * martonAuxRow κ K u x) = (μ₁ + μ₃) * entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ p.2.2.2.1)` |
| `martonWeightedSum_eq_auxWeightObjective_add_aggregate` `@[entry_point]` | 同 `:127` | VB5 全 20 個 + `(q : Measure V₁) [IsProbabilityMeasure q] (κ) [IsMarkovKernel κ] (K) [IsMarkovKernel K] (W) [IsMarkovKernel W] (μ₁ μ₃ : ℝ)` ⚠ **`μ` の符号仮定は 0 個** | `μ₁ * martonInfo₁ (q ⊗ₘ κ) K W + μ₃ * (martonInfo₁ (q ⊗ₘ κ) K W + martonInfo₂ (q ⊗ₘ κ) K W - martonInfoV₁V₂ (q ⊗ₘ κ) K W) = auxWeightObjective (martonAuxKernelSlot κ K W) (martonAuxCoeff κ K W μ₁ μ₃) 0 μ₃ (fun u ↦ q.real {u}) + martonOutput₁Aggregate W μ₁ μ₃ (fun x ↦ ∑ u, q.real {u} * martonAuxRow κ K u x)` ⟹ ⚠ **`c := 0` / 凸 slot の係数 `t := μ₃`** |
| `exists_support_card_le_martonWeightedSum` `@[entry_point]` | 同 `:150` | 上と同じ + ⚠ **`(hμ₃ : 0 ≤ μ₃)` の 1 本だけ**（`hμ₁` は無い） | `∃ q' : V₁ → ℝ, 0 ≤ q' ∧ (∀ x, ∑ u, q' u * martonAuxRow κ K u x = ∑ u, q.real {u} * martonAuxRow κ K u x) ∧ μ₁ * martonInfo₁ … + μ₃ * (…) ≤ auxWeightObjective … q' + martonOutput₁Aggregate … ∧ {u \| q' u ≠ 0}.ncard ≤ Fintype.card α` |

**L15（`ObjectiveAssembly.lean`、2 本。⚠ 自作の新規補題は private 1 本のみ）**

| decl | file:line | 型クラス前提（逐語） | 結論形（逐語） |
|---|---|---|---|
| `sum_eq_one_of_martonAuxRow_aggregate` `[private]` | `…/Marton/ObjectiveAssembly.lean:172` | VB5 から `omit [Nonempty V₁] [Nonempty V₂] [Nonempty α] in`（`:171` 逐語）+ `(q : Measure V₁) [IsProbabilityMeasure q] (κ) [IsMarkovKernel κ] (K) [IsMarkovKernel K] (q' : V₁ → ℝ) (hagg : ∀ x, ∑ u, q' u * martonAuxRow κ K u x = ∑ u, q.real {u} * martonAuxRow κ K u x)` | `∑ u, q' u = 1`（= 集約保存だけから `stdSimplex` 入りが出る。⚠ 行和 1 を 2 度使う 5 段 `calc`） |
| `exists_support_card_le_martonWeightedSum_measure` `@[entry_point]` | 同 `:194` | VB5 全 20 個 + `(q : Measure V₁) [IsProbabilityMeasure q] (κ) [IsMarkovKernel κ] (K) [IsMarkovKernel K] (W) [IsMarkovKernel W] (μ₁ μ₃ : ℝ) (hμ₃ : 0 ≤ μ₃)` | `∃ (q' : Measure V₁) (_ : IsProbabilityMeasure q'), {u \| q'.real {u} ≠ 0}.ncard ≤ Fintype.card α ∧ μ₁ * martonInfo₁ (q ⊗ₘ κ) K W + μ₃ * (martonInfo₁ (q ⊗ₘ κ) K W + martonInfo₂ (q ⊗ₘ κ) K W - martonInfoV₁V₂ (q ⊗ₘ κ) K W) ≤ μ₁ * martonInfo₁ (q' ⊗ₘ κ) K W + μ₃ * (martonInfo₁ (q' ⊗ₘ κ) K W + martonInfo₂ (q' ⊗ₘ κ) K W - martonInfoV₁V₂ (q' ⊗ₘ κ) K W)` ⚠ **両辺が同じ型の `Measure V₁` 上の量** = (a′-1) の形に一番近い landing 点 |

### 11.3 L15 は自作 0 件 — 消費した既存資産（すべて import 閉包内に既在）

| 資産 | file:line | 型クラス前提（`#check` 逐語） | 何を与えたか |
|---|---|---|---|
| `ChannelCoding.pmfToMeasure` | `InformationTheory/Shannon/ChannelCoding/ShannonTheorem.lean:55` | `{α : Type u_1} → [Fintype α] → [inst : MeasurableSpace α] → (α → ℝ) → Measure α` ⚠ **`DecidableEq` も `Nonempty` も `MeasurableSingletonClass` も落ちている**（def の直前 `variable` には在るが def が使わないため） | ベクトル `q' : V₁ → ℝ` を `Measure V₁` へ戻す実体 `∑ a, ENNReal.ofReal (p a) • Measure.dirac a` |
| `ChannelCoding.pmfToMeasure_isProbabilityMeasure` | 同 `:76` | `∀ {α} [Fintype α] [MeasurableSpace α] {p : α → ℝ}, p ∈ stdSimplex ℝ α → IsProbabilityMeasure (pmfToMeasure p)` | `IsProbabilityMeasure` の witness |
| `ChannelCoding.pmfToMeasure_real_singleton` | 同 `:95` | `∀ {α} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {p : α → ℝ}, p ∈ stdSimplex ℝ α → ∀ (a : α), (pmfToMeasure p).real {a} = p a` | 台の集合の一致（`{u \| (pmfToMeasure qv).real {u} ≠ 0} = {u \| qv u ≠ 0}`）と重み付き和の再展開 |
| `InformationTheory.sum_measureReal_singleton_univ_eq_one` | `InformationTheory/Probability/SingletonMass.lean:30` | `∀ {γ} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (μ : Measure γ) [IsProbabilityMeasure μ], ∑ z, μ.real {z} = 1` | `stdSimplex` の第 2 成分 |
| `sum_martonAuxRow_eq_one` | `…/Marton/ObjectiveVectorForm.lean:125` | `∀ {V₁ V₂ α} [MeasurableSpace V₁] [Fintype V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (κ) [IsMarkovKernel κ] (K) [IsMarkovKernel K] (u : V₁), ∑ x, martonAuxRow κ K u x = 1` | 集約保存 ⟹ `∑ q' = 1` の 5 段 `calc` の両端 |

⚠ **見つけ方の教訓（4 度目の再演。§10.7 / handoff が記録する「結論形・部分文字列で引く」と同型）**:
決め手は名前ではなく**式の部分項**での `rg`。逐語:

- 効いた検索 `rg -n 'ENNReal.ofReal .* • Measure.dirac' InformationTheory/` ⟹ 9 hit、
  2 hit 目・3 hit 目が `ShannonTheorem.lean:54`（docstring）と `:56`（def 本体）。
- 届かなかった検索 `rg -ln 'PMF|toMeasure|ofFintype' InformationTheory/` ⟹ 先頭が
  `InformationTheory/Fano.lean` / `Fano/Measure.lean` / `Fano/CondEntropy.lean` … と
  `Fano` の `diracPMF` ノイズで埋まり、`ChannelCoding/ShannonTheorem.lean` は上位に出ない。
- **loogle は 1 本も要らなかった**（in-project 資産なので原理的に見えない = `cause:loogle-blind` の型）。

⟹ ブリーフが立てた「汎用の橋 1 本を `SingletonMass.lean` に置く」案は**不要**で、具体 witness を
直接置くほうが短かった（新規 private 1 本 = 17 行）。

### 11.4 代数の核心（⚠ 我々の演繹だが、証明項として機械検証済）

`S := martonInfo₁ + martonInfo₂ − martonInfoV₁V₂` を `Marton/Setup.lean:244` / `:252` / `:262` の
定義から展開すると:

1. **`H(V₂)` が相殺する** — `martonInfo₂` の `+H(V₂)` と `martonInfoV₁V₂` の `−H(V₂)`。
2. **GAP A の 2 本（`marton_entropy_V₁V₂_sub_entropy_V₁_eq_sum` /
   `marton_entropy_V₁Y₁_sub_entropy_V₁_eq_sum`）を当てると `H(V₁)` も相殺する**（`martonInfo₁` の
   `+H(V₁)` と `martonInfoV₁V₂` の `+H(V₁)` が、2 本の左辺の `−H(V₁)` と組む）。
3. 残るのは
   `(μ₁+μ₃)·H(Y₁) + μ₃·[H(Y₂) − H(V₂,Y₂)] + ∑_u q_u·(μ₃·h₂(u) − (μ₁+μ₃)·h₁(u))`
   （`h₂ u = ∑ v₂ negMulLog ((κ u).real {v₂})`、`h₁ u = ∑ y₁ negMulLog (martonAuxOutput₁Row κ K W u y₁)`）。
4. ⟹ **集約 slot `g` = `martonOutput₁Aggregate` / 凸 slot（`t := μ₃`）= `−H(V₂\|Y₂)` /
   線型 slot `w` = `martonAuxCoeff`** にちょうど 3 分割され、**定数 slot は `c := 0`**。

- ⚠ **`hμ₁ : 0 ≤ μ₁` は不要**（署名で機械確認、§11.2 の表）。恒等式側は `ring` で閉じて `μ` の符号を
  使わず、台縮小が要求するのは `ht : 0 ≤ t`（= `μ₃`）1 本だけ。`μ₁` は符号仮定のない線型 slot `w` と
  何の仮定も持たない集約 slot `g` にしか入らない。
- ⚠ **退化境界 2 つで結論が生きる**（⚠ 我々の再導出）: `μ₃ = 0` では凸 slot が消えて主張は
  「線型 + 集約だけの目的関数が台縮小で減らない」— 集約が厳密保存なので**非自明なまま生きる**。
  `μ₁ = −μ₃` では目的関数が `μ₃·(martonInfo₂ − martonInfoV₁V₂)` に縮み、これも実質的な主張である
  （どちらも vacuous ではない = `hμ₁` を落としたことが under-hypothesis を生んでいない根拠）。
- ⚠ **補題化の粒度についての所見**: 上の 4 段のうち補題化が要ったのは「同定 3 本」
  （`sum_negMulLog_martonAuxKernelSlot_eq_entropy` / `…_mixture_eq_entropy` /
  `martonOutput₁Aggregate_eq_mul_entropy`）だけで、**`H(V₁)` の 2 度の相殺は
  `martonWeightedSum_eq_auxWeightObjective_add_aggregate` 末尾の `ring` 1 発に吸収された**
  ⟹ **「代数のステップ数」ではなく「`rw` が要る接続点の数」で補題を切る**のが正しい粒度。

### 11.5 行数の実測と (a′-1) 予算の突き合わせ — ⚠ **既に上限超過**

`wc -l` 逐語（HEAD `925e28a4`）:

| file | 行 |
|---|---|
| `…/Marton/SupportReduction.lean` | 230 |
| `…/Marton/ObjectiveConvexity.lean` | 129 |
| `…/Marton/ObjectiveVectorForm.lean` | 489 |
| `…/Marton/ObjectiveAssembly.lean` | 222 |
| **合計** | **1070** |

§8.2 の (a′-1) 見積りは **480–800 行**（部品 1/2/4 = 280–450 行 + (3a)(3b)(3c) = 200–350 行）。
⟹ ⚠ **実測 1070 行は上限 800 を 270 行（+34%）超えている**。しかも **(a′-1) はまだ立っていない**
（§11.6 の残件 2 件が未着手。現在の到達点は `exists_support_card_le_martonWeightedSum_measure` で、
`V₁` の**台の大きさ**しか縛れていない）。

⚠ **これは「内数の再配分」では説明できない**（§10.7 の言い回しをここへ流用してはならない）。
超過の内訳（⚠ 我々の演繹）:

- **(3b) の実体 `SupportReduction.lean` 230 行 + `ObjectiveConvexity.lean` 129 行 = 359 行**は
  見積り (3a)(3b)(3c) 200–350 行の枠にほぼ収まる。
- **超過の主因は §10.7 で記録済の `ObjectiveVectorForm.lean`**（見積り 120–200 行 → 実測 489 行）
  で、そこに L13 の GAP A / GAP B（§11.1、127 行）が**見積りに無かった項目として**上乗せされた。
- ⟹ 超過は「測度形 ↔ ベクトル形の橋」1 箇所に集中しており、**凸性・端点・台縮小の数学側は
  見積り通り**である。⚠ ただし §11.6 (ii) が要求する `V₂` 側の鏡像は**同じ橋をもう一度**なので、
  超過の主因がそのまま倍化する構造にある（次 leg の見積りはこの実測から起こすこと）。

### 11.6 残件 — 標的言明 (a′-1) までに何が残っているか

§8.2 の (a′-1) は
`∃ (k₁' k₂' : ℕ) (_ : k₁' < martonAuxBound α) (_ : k₂' < martonAuxBound α) (pV') … `
と **2 つの補助アルファベット両方**の基数を縛る。L15 までで縛れたのは **`V₁` の台の大きさだけ**
（`κ` を固定して `q` のみを動かす機構）。⚠ **`martonAuxBound` はまだコードに存在しない** —
`rg -n 'martonAuxBound' InformationTheory/` は **0 hit**（§7.7 は値 `Fintype.card α` を確定させた
だけで、`def` は未実装）。

#### (i) 台の小ささ → **基数の小さい型への付け替え** に何が要るか

⚠ **在るもの / 無いものを分けて書く。**

| 項目 | 実測 | 逐語の根拠 |
|---|---|---|
| 付け替え先の型 | 在る。`abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))` ⟹ `\|bcAuxAlphabet k\| = k+1`。§7.7 の off-by-one（`k₁' < Fintype.card α` ⟺ `\|V₁'\| ≤ \|α\|`）は**現 HEAD でもそのまま**成立 | `MartonUnion.lean:65` |
| 3 汎関数の再ラベル不変性 | ⚠ **`≃ᵐ`（全単射）版しか無い** ⟹ **基数を落とせない**。`martonInfo₁_map_relabel` / `martonInfo₂_map_relabel` / `martonInfoV₁V₂_map_relabel` / `martonRegion_map_relabel` はいずれも `(e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂')` を取る | `MartonUnion.lean:249` / `:288` / `:329` / `:372`。`#check` 逐語（`martonRegion_map_relabel`）: `… (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂'), martonRegion (Measure.map ⇑(e₁.prodCongr e₂) pV) (K.comap ⇑(e₁.prodCongr e₂).symm ⋯) W = martonRegion pV K W` |
| `V ≃ᵐ bcAuxAlphabet (card V - 1)` | 在るが ⚠ **`private`** ⟹ 他ファイルから使えない（§4.1 の指摘は現 HEAD でも有効）。再導出は `(Fintype.equivFin V).trans ((finCongr …).trans Equiv.ulift.symm)` + `measurable_of_countable` の 5 行 | `MartonUnion.lean:402` `private noncomputable def bcAuxMeasurableEquiv` |
| **単射（非全射）版のエントロピー不変性** | ⚠ **在る — ただし別家系**。`wz_entropy_map_injective`「Shannon entropy is invariant under an injective (measurable) relabeling of the alphabet」。⚠ **`≃ᵐ` を要求しない**ので、これが (i) の心臓部を埋める | `InformationTheory/Shannon/WynerZiv/Achievability/Covering.lean:1189`。`#check` 逐語: `∀ {Ω γ₀ δ₀} [MeasurableSpace Ω] [Fintype γ₀] [DecidableEq γ₀] [Nonempty γ₀] [MeasurableSpace γ₀] [MeasurableSingletonClass γ₀] [Fintype δ₀] [DecidableEq δ₀] [Nonempty δ₀] [MeasurableSpace δ₀] [MeasurableSingletonClass δ₀] (μ : Measure Ω) (X : Ω → γ₀), Measurable X → ∀ (g : γ₀ → δ₀), Function.Injective g → Measurable g → (entropy μ fun ω => g (X ω)) = entropy μ X`。⚠ 消費者 3 decl / 2 file（`scripts/dep_consumers.sh InformationTheory.Shannon.wz_entropy_map_injective`: `Concentration.lean:205` / `:957` / `MassBound.lean:168`）⟹ **移設するなら 3 decl に触る / 汎用版を別置きするなら波及 0** |
| 同時分布の輸送 | ⚠ **`≃ᵐ` 版の証明が単射版へほぼそのまま延びる**（⚠ 我々の演繹、未実装）。`martonJointDistribution_map_relabel` が equiv を使う唯一の箇所は `hKcomap : (K.comap E.symm E.symm.measurable).comap E E.measurable = K` で、これは**左逆元 `g ∘ f = id` があれば足りる**。主力の `compProd_comap_map_prodMap` は `{g : A → A'} (hg : Measurable g)` しか要求しない | `MartonUnion.lean:198`（`:209` が `hKcomap`）/ `InformationTheory/Shannon/ChannelCoding/CodeToAmbient.lean:401` 逐語: `lemma compProd_comap_map_prodMap {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace B] (μ : Measure A) [SFinite μ] (κ : Kernel A' B) [IsMarkovKernel κ] {g : A → A'} (hg : Measurable g) : (μ ⊗ₘ κ.comap g hg).map (fun z ↦ (g z.1, z.2)) = (μ.map g) ⊗ₘ κ` |
| ⚠ **本当に無いもの** | **「台 `ncard ≤ Fintype.card α` の測度を、基数 `≤ Fintype.card α` の型の上の測度として書き直す」段**。⚠ `\|V₁\| > \|α\|` のとき **`V₁ → T` の大域単射は存在しない**ので、上の単射版をそのまま当てることはできず、**先に台の部分型 `↥{u \| q'.real {u} ≠ 0}`（あるいは同値な小さい型）へ落とす**段が要る。in-project にこの段の資産は見当たらない（下の検索を実施） | 検索（結論形）: `rg -n 'entropy [^=]*= entropy' InformationTheory/ --glob '*.lean'` の 25 hit を全走査 ⟹ 出るのは `wz_entropy_map_injective` / `entropy_measurableEquiv_comp`（`Shannon/Pi.lean:36`）/ `entropy_eq_of_identDistrib`（`AEP/Basic/Converse.lean:55`）/ `entropy_map_comp`（`Shannon/Bridge.lean:53`）の 4 型だけで、**台への制限を扱うものは 0 件** |

⚠ **`OuterBoundUV/Quantization.lean` は (i) に使えない**（§6.2 / plan §5 の L6 所見の再確認）。
中身は `ℕ` 上の補助変数を `Fin (m+1)` へ**裾を畳んで**落とす粗視化で、代償が
`uvQuantizeSlack ν m`（`Quantization.lean:160`）として残り `m → ∞` で 0 に行くことに依存している。
(i) が要るのは**厳密保存**なので、効くのは**ファイルの形だけ**である。

⟹ **(i) の結論（分かったこと）**: 3 部品のうち 2 部品（単射版エントロピー不変性 / 同時分布の輸送）は
**既存資産で埋まる公算が高く、新規の数学は要らない**。残るのは「台の部分型へ落とす」1 段と
`bcAuxMeasurableEquiv` の `private` 解除（または 5 行の再導出）、および `martonAuxBound` の `def` である。
⚠ **分からないこと**: (a) 台への制限を**測度の水準**でやるのと、L11–L15 のベクトル層を**部分型の上で
もう一度走らせる**のとどちらが短いか（後者は 4 ファイルの型引数を差し替えるだけの可能性がある）、
(b) 単射版 relabel 4 本を書き下ろす実行数（`≃ᵐ` 版が `MartonUnion.lean:198-383` の 185 行なので
同程度と見るのが素直だが未検証）。

#### (ii) ⚠ **`V₂` 側の基数も縛れるのか** — 次 leg の設計を決める分岐

**一次文献 [GA09] の逐語**（`$LIT/ga09.txt`。`$LIT` は facts `## L7 (T3)` 冒頭の定義）:

- `ga09.txt:292-294` 逐語: "For this problem, we would like to show that **it suffices to take the
  maximum over random variables U and V with the cardinality bounds of min(|X|, Su) and
  min(|X|, Sv)**. It suffices to prove the following lemma:"
- `ga09.txt:295-296, 319-320` 逐語（Lemma 1）: "Given an arbitrary broadcast channel `q(y, z|x)`,
  an arbitrary input distribution `p(x)`, non-negative reals `λ` and `γ`, and natural numbers `Su`
  and `Sv` **where `Su > |X|`** the following holds: `sup … = …` where … **`|Û| < Su`, `|V̂| ≤ Sv`**."
- `ga09.txt:587-589` 逐語（§V-B の初等証明、`U` 側の凸性を見る所）: "Next, note that
  **`λI(U;Y) = λH(Y) − λH(Y|U)` is linear in `q(u)`, and `γI(V;Z) = γH(Z) − γH(Z|V)` is convex in
  `q(u)`. The latter is because the marginal distribution of X is preserved and hence H(Z) is
  fixed.**"

⟹ **文献の答は「同じ機構の 2 度適用で閉じる」**（⚠ 分かったこと）。根拠 3 点:

1. **Lemma 1 は片側だけを 1 減らし、他方の上界を触らない**（`|Û| < Su` **かつ** `|V̂| ≤ Sv`）
   ⟹ 交互に当てても増えない。§L7 行 4 (Q4) が記録した**発散する相互再帰は起きない** —
   あれは「3 汎関数の**値**を保存しようとする素朴 Carathéodory」の話で、ここで保存するのは
   **`p₀(x)` だけ**、目的関数には**減らないこと**しか要求しない。
2. **目的関数 `I(U;Y)+I(V;Z)−I(U;V)+λI(U;Y)+γI(V;Z)` は `(U,Y,λ) ↔ (V,Z,γ)` の入れ替えで
   それ自身に写る**（⚠ 我々の演繹だが上の逐語式から機械的）⟹ `V` 側の証明は `U` 側の鏡像。
3. 我々の Lean 版は**最大点の存在を仮定しない**分だけ文献より扱いが軽い — [GA09] §V-B は
   "Assume that the maximum … is obtained at some joint distribution `p₀`"（`ga09.txt:575-576` 逐語）
   から始まるが、`exists_support_card_le_martonWeightedSum` は**任意の `q` に対し witness を返す**
   形（端点で減らないことだけを使う）なので、`Su` を 1 ずつ減らす帰納も要らない。

⚠ **ただし Lean 側の代償が 1 つある（⚠ 我々の演繹、未実装）**。鏡像フレーム
（`q₂` を動かし `p₀(v₁,x\|v₂)` を固定）で目的関数を分解すると、slot の配り方が**変わる**:

| 項 | `V₁` 側（実装済） | `V₂` 側（鏡像） |
|---|---|---|
| `H(Y₁)` / `H(Y₂)` | 集約 slot `g` | 集約 slot `g`（両方） |
| `−H(Y₁\|V₁)` | **線型**（`martonAuxCoeff` の第 2 項） | ⚠ **凸**（`q₂` について。第 2 の凸 slot） |
| `−H(Y₂\|V₂)` | 凸 slot（`t := μ₃`、`martonAuxKernelSlot`） | **線型** |
| `H(V₂\|V₁)` / `H(V₁\|V₂)` | 線型 | 線型 |
| `−H(V₁)` | （相殺して消える） | ⚠ **凸**（`Z := Fin 1` に退化させた同型の bracket） |

⟹ **鏡像側は凸 slot が 2 本要る**（`auxWeightObjective` は `t` を 1 本しか持たない、
`ObjectiveConvexity.lean:88` 逐語）。⚠ ただし**凸性の数学は新規 0**:
`convexOn_negCondEntropy_mixture (k : U → V × Z → ℝ)`（同 `:62`）は `V` `Z` について完全に多相で、
**転置した slot を渡すだけで `−H(Y₂\|V₂)` 型の bracket が出る**ことを機械確認した（scratch の
`example … := convexOn_negCondEntropy_mixture (fun u p ↦ martonAuxKernelSlot κ K W u (p.2, p.1)) hk`
が 0 error）。台縮小の受け口 `exists_support_card_le_of_convexOn_add_aggregate`
（`SupportReduction.lean:219`）は**任意の `ConvexOn f`** を取るので、2 本の和のままでも消費できる。

⚠ **§8.2 の射程限定は分解の取り方の産物である公算が高い（訂正候補）**。§8.2 は
「一般の `μ₂ > 0` では `μ₂·H(V₂)` が残り、凹かつ集約の関数でもない ⟹ 本機構の射程外」と書いたが、
[GA09] の grouping（`ga09.txt:587-589` 逐語）は `μ₂I₂ = μ₂H(Y₂) − μ₂H(Y₂\|V₂)` と切り、
`H(Y₂)` は**既に集約形で証明済**（`marton_map_Y₂_real_singleton_eq_aggregate`、
`ObjectiveVectorForm.lean:344`）、`−H(Y₂\|V₂) = H(V₂) − H(V₂,Y₂)` は**上の転置 bracket そのもの**である。
⚠ **確認できたのは凸 slot の可用性（型検査）まで**で、`μ₂ * martonInfo₂ = 集約 + 転置 bracket` の
**恒等式は未検証**（要る周辺は `marton_map_V₂Y₂_real_singleton_eq_sum`（同 `:285`）と
`marton_map_V₂_real_singleton_eq_sum`（同 `:190`）で既に在るので短い見込み）。
⟹ **§8.2 の「2 系列に絞れ」を実装へ渡す前に、この 1 本を試すこと**（潰れれば §8.2 が正しい）。

⚠ **分からないこと（次 leg が最初に決めるべきこと）**:

1. 鏡像を**既存補題の型引数の入れ替えで得られるか**、それとも書き下ろしか。
   `martonInfo₁` / `martonInfo₂` は 5 つ組の**座標順が固定**された定義
   （`Marton/Setup.lean:244` / `:252` の `Prod.fst` / `fun q ↦ q.2.1` / `fun q ↦ q.2.2.2.1` /
   `fun q ↦ q.2.2.2.2`）なので、鏡像には `pV.map Prod.swap` と **`W : BCChannel α β₁ β₂` の出力の
   入れ替え**を伴う変換補題が要る。⚠ **その swap 対称性補題は in-project に無い**
   （`rg -n 'Prod.swap|swap' …/Marton/*.lean …/MartonUnion.lean` の hit は
   `ErrorAnalysis.lean:91-99` と `Covering.lean:72/87/100` の**典型集合側**だけで、3 汎関数の
   入れ替えを述べたものは 0 件）。
2. 2 系列（`μ₂ = 0` / `μ₁ = 0`）で足りるのか、上の訂正候補が通って**全域 `μ ≥ 0`** で閉じるのか。
   これは §8.2 の (a′-2) の 3 段（分離 → 支持関数）が要求する重みの範囲に直結する。
3. `V₁` 側と `V₂` 側を**同時に**縛る順序（先に `V₁` を縛った後、`V₂` の縮約が `V₁` の台を壊さないこと）
   の Lean での言い方。⚠ 文献側では Lemma 1 の `|V̂| ≤ Sv` が保証しているが、我々の per-instance 形では
   「2 回目の適用が 1 回目の `ncard` 上界を保つ」ことを**別途言う**必要がある（`κ` の側を触らない
   構成なので自明に近いが、未検証）。

### 11.7 壁と撤退ライン

⚠ **L13 / L14 / L15 のいずれでも `@residual(wall:…)` は 1 本も立っていない / 共有 sorry 補題の
候補も 0 件**。§9.9 の壁 0 件判定はそのまま有効で、追加すべき行も無い。再導出コマンド:
`rg -n 'sorry|@residual' InformationTheory/Shannon/BroadcastChannel/Marton/Objective*.lean
InformationTheory/Shannon/BroadcastChannel/Marton/SupportReduction.lean`。

- **親プラン §6 の撤退ライン 3 本は不発火**（逐語で照合）:
  「L8 の棚卸しで軸 T3-α が gate を通らない」= L8 で (a′) 決定済 ⟹ 触れない。
  「L14 の棚卸しで層 3 に載せられる散文が 1 本も無い」= 層 3 に載る成果
  （`exists_support_card_le_martonWeightedSum_measure`）が landing 済 ⟹ 不発火。
  「20 leg 使い切って未達」= 未到達。
- ⚠ **ただし予算の位置は正直に書く**: 親プラン §5 の可変枠 **L2–L15 は L15 で使い切り**、
  残るのは L16–L18（層 3 の集中枠 3 本）+ L19（収穫）+ L20（記録）である。§11.6 の残件 2 件
  （うち (ii) は鏡像 1 式）を **3 leg で入れる**のが次 leg の前提条件になる。⚠ §11.5 の実測
  （橋 1 箇所で +270 行）を踏まえると、**(ii) をフルに鏡像化する路線は 3 leg に収まらない公算がある**
  ⟹ 次 leg の最初の判断は「(ii) を鏡像化するか、標的を `V₁` 側 1 変数の基数境界へ**明示的に**
  絞って (a′-1) を言い直すか」である。⚠ 後者を採る場合も**撤退ではなく標的の再選択**なので、
  §8.2 の表と同じ形式で「何が言えて何が言えないか」を書くこと（`@residual(wall:…)` は切らない —
  facts §L7 行 7 のとおり文献側では 2009–2011 に閉じている）。
- honesty ゲートは launch 条件外で不発火（新規 `sorry` / `@residual` の導入 0 / honesty 上意味の
  変わる署名変更 0）。規約ゲートは L13 / L14 / L15 の 3 回とも **PASS**。

### 11.8 掃除候補（低優先。§10.5 の更新）

1. **§10.5 の `compProd_real_singleton_mul` 3 重複は未着手のまま**
   （`…/Marton/MarkovCore/Receiver1.lean:571` / `Receiver2.lean:500` の `have hcompProd` と
   `ObjectiveVectorForm.lean:97` の private 1 本）。新規追加なので**波及 0**。
2. ⚠ **新規 1 件 — `wzPmfMeasure` が `ChannelCoding.pmfToMeasure` の逐語同一コピー**。
   `InformationTheory/Shannon/WynerZiv/Converse/Prelim.lean:100`（`def`）+ `:104` / `:118` / `:129`
   （補題 3 本）が、`ShannonTheorem.lean:55` / `:60` / `:76` / `:95` と**本体まで逐語同一**
   （`∑ t, ENNReal.ofReal (p t) • Measure.dirac t`、証明も `Measure.finsetSum_apply` →
   `Finset.sum_eq_single` の同じ手順）。docstring 自身が重複を認めている
   （`Prelim.lean:89-93` の節コメント逐語: "Mirrors `ChannelCoding.pmfToMeasure` (kept local to
   avoid a heavy `ShannonTheorem` import)."）。
   ⚠ **その回避理由は現 HEAD では成立しない（機械確認）**: `Prelim.lean` の import 4 本
   （`WynerZiv.Operational` / `WynerZiv.FactorizableRate` / `WynerZiv.ConverseGateway` /
   `ChannelCoding.ConverseMemorylessMarkov`）だけを import した scratch で
   `#check @InformationTheory.Shannon.ChannelCoding.pmfToMeasure` が
   `{α : Type u_1} → [Fintype α] → [inst : MeasurableSpace α] → (α → ℝ) → Measure α` を返す
   ⟹ **`pmfToMeasure` は既に import 閉包内に在る**（前 2 本のどちらかが引き込んでいる。
   ⚠ 4 本のうち後ろ 2 本だけでは届かない = 経路は前 2 本側）。
   さらに**同じ WynerZiv 家系の別ファイルは既に共有版を消費している**
   （`WynerZiv/Achievability/Concentration.lean:650-658` の `wz_pmfToMeasure_isFiniteMeasure` が
   `ChannelCoding.pmfToMeasure` を直接 `unfold` している）⟹ 局所コピーの理由は残っていない。
   ⚠ 削除は `private` 4 本の差し替えなので**外部波及 0**（`private` = file-scoped）。
3. ⚠ **移設候補 1 件 — `wz_entropy_map_injective`**（§11.6 (i)）。`entropy_measurableEquiv_comp`
   （`Shannon/Pi.lean:36`）の真の一般化であり、置き場所は WynerZiv の
   `Achievability/Covering.lean`（1384 行、WynerZiv 7 本 import）で**他家系から呼びにくい**。
   ⚠ **移設なら 3 decl / 2 file に触る**（`scripts/dep_consumers.sh` 実測、§11.6 の表）、
   **`Shannon/Pi.lean` 側に汎用版を新規に置くなら波及 0**（ただし一時的に重複が 1 件増える）。
