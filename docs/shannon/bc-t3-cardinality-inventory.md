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
