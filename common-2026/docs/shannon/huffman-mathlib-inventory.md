# T1-A Huffman 最適性 — Mathlib 在庫調査

> Parent plan: 未起草 (本 inventory 後に lean-planner が起こす)
> Roadmap: `docs/textbook-roadmap.md` §「Tier 1 — T1-A. Huffman 最適性」
> 出力規約: `docs/shannon/shannon-mathlib-inventory.md` / `general-dmc-mathlib-inventory.md` と同形。

## 一行サマリ

**Huffman 木 / prefix-code structure / sibling-property / 最適性 induction の本体は Mathlib 完全不在**
(`Huffman` `PrefixCode` `Tree (Fin D)` がいずれも `Found 0`)。一方で **(i) InformationTheory 側の `IsPrefixFree` + `shannonFanoCode` ペア + `expectedLength` + `entropyD_le_expectedLength_of_kraft` + `exists_prefix_code_of_kraft` は完成済み 0-sorry**、**(ii) Mathlib 側 `InformationTheory.kraft_mcmillan_inequality` (`UniquelyDecodable` over `Finset (List α)` 形) も完成済み**、**(iii) priority-queue / argmin / sort / strong-induction の周辺 API (List.argmin, Finset.exists_min_image, Multiset.sort, Multiset.strongInductionOn, Finset.induction) は揃っている**。よって T1-A の自作必要箇所は：

1. Huffman 木表現 + `huffmanCode : (Fin n → ℝ) → α → List (Fin 2)` 構成 (~150 行)
2. sibling property (Cover-Thomas Lemma 5.8.1: 「最小 2 確率の codeword は同じ最深 leaf の兄弟である」) (~150 行)
3. `n → n-1` 縮約 induction による最適性証明 (~250-350 行)
4. KraftReverse 既存 API への bridge (`length-only` 表現と Huffman 木の対応) (~50-100 行)

合計 ~500-700 行 (roadmap 規模見積もりと一致)。

**最大の発見**: Mathlib `kraft_mcmillan_inequality` は **`Finset (List α)` (codeword 集合) 水準** で publish されている。一方 `InformationTheory/Shannon/ShannonCode.lean` の `kraftSum` は **`α → ℕ` (語長関数) 水準**。Huffman の最適性ステートメントを書く際に **どちらの抽象水準を選ぶか** が最初の design judgement。 KraftReverse 既存 (`exists_prefix_code_of_kraft`) は `α → ℕ` 水準で構成しているので、自然な路線は語長水準で `expectedLength p l` 形に揃え、最後に prefix-code を `exists_prefix_code_of_kraft` で取り出す方式。

**撤退ライン**: roadmap 提示の 500-700 行を上回るリスクは「sibling property を多倍数アルファベット (D-ary, D ≥ 2) に一般化しようとした場合」のみ。binary (D=2) 限定で着手し、D-ary 拡張は **stretch goal** に切り出す方針なら撤退ライン非発動の見込み。

---

## 主定理の最終形 (推定 signature)

roadmap T1-A 抜粋:

```
任意の pmf `p : Fin n → ℝ` に対し、Huffman 木が生成する prefix code が
  ∀ C : PrefixCode, expectedLength p (huffmanCode p) ≤ expectedLength p C
を満たす。
```

抽象水準を `α → ℕ` (語長) 路線で書いた場合の Lean signature 候補:

```lean
namespace InformationTheory.Shannon.Huffman

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Huffman 構成からの語長関数 (binary, D = 2). -/
noncomputable def huffmanLength (p : α → ℝ) : α → ℕ := sorry

/-- Huffman 語長は Kraft 不等式を充足 (D = 2). -/
theorem huffmanLength_kraft_le_one (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    ∑ a : α, (2 : ℝ) ^ (-(huffmanLength p a : ℤ)) ≤ 1 := sorry

/-- **主定理**: Huffman 語長は任意の Kraft-feasible 語長関数より expected length が小さい. -/
theorem huffmanLength_optimal
    (p : α → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, (2 : ℝ) ^ (-(l a : ℤ)) ≤ 1) :
    (∑ a : α, p a * (huffmanLength p a : ℝ)) ≤ (∑ a : α, p a * (l a : ℝ)) := sorry

end InformationTheory.Shannon.Huffman
```

証明戦略 (pseudo-Lean 8 行, `Fintype.card α = n` 上の strong induction):

```lean
-- induction on n := Fintype.card α
-- base n = 1: huffmanLength = 0, expectedLength = 0, RHS ≥ 0 by hl_pos
-- step n → n-1:
--   sibling property: ∃ a b, a ≠ b ∧ huffmanLength p a = huffmanLength p b
--     ∧ ∀ c, p c ≥ p a ∨ p c ≥ p b (smallest 2 are siblings, Cover-Thomas Lemma 5.8.1)
-- merged distribution p' on α' := α / {a~b}, p'(ab) := p a + p b
-- IH: expectedLength p' (huffmanLength p') ≤ expectedLength p' (lift l)
-- bridge: expectedLength p (huffmanLength p) = expectedLength p' (huffmanLength p') + (p a + p b)
-- bridge: expectedLength p l ≥ expectedLength p' (lift l) + (p a + p b)  -- 鍵 lemma
```

---

## API 在庫テーブル

### §A. 既存 InformationTheory 資産 (基盤)

| name | file:line | signature (verbatim, `[...]` 含む) | 結論形 (verbatim) | T1-A での扱い |
| --- | --- | --- | --- | --- |
| `entropyD` | `InformationTheory/Shannon/ShannonCode.lean:45` | `noncomputable def entropyD (D : ℝ) (P : Measure α) : ℝ` (variable `{α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`) | `:= -∑ a : α, P.real {a} * Real.logb D (P.real {a})` | reuse (lower bound H ≤ E[L] で Shannon 最適性を読み替え可、しかし Huffman 主張は **任意 l との比較**で entropy を経由しないので必須ではない) |
| `shannonLength` | `InformationTheory/Shannon/ShannonCode.lean:51` | `noncomputable def shannonLength (D : ℝ) (P : Measure α) (a : α) : ℕ` (同 variable) | `:= ⌈- Real.logb D (P.real {a})⌉₊` | non-reuse (Huffman 語長は別構成) |
| `expectedLength` | `InformationTheory/Shannon/ShannonCode.lean:55` | `noncomputable def expectedLength (P : Measure α) (l : α → ℕ) : ℝ` (同 variable) | `:= ∑ a : α, P.real {a} * (l a : ℝ)` | **reuse 確定** (Huffman 主定理の比較対象 metric)。ただし入力が `Measure α` であることに注意 — `pmf : α → ℝ` 路線にするなら別 def が要る (下記 §F-3 参照) |
| `kraftSum` | `InformationTheory/Shannon/ShannonCode.lean:59` | `noncomputable def kraftSum (D : ℝ) (l : α → ℕ) : ℝ` (同 variable) | `:= ∑ a : α, (D : ℝ) ^ (-(l a : ℤ))` | reuse (Huffman 語長の Kraft 充足を結語で主張) |
| `shannonCode_expected_length_bounds` | `InformationTheory/Shannon/ShannonCode.lean:345` | `theorem shannonCode_expected_length_bounds {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a})` | `: entropyD D P ≤ expectedLength P (shannonLength D P) ∧ expectedLength P (shannonLength D P) < entropyD D P + 1` | non-reuse 本体 (Shannon code の sandwich) だが、`entropyD_le_expectedLength_of_kraft` が Gibbs 下界として Huffman の任意 l との比較に **使える** |
| `entropyD_le_expectedLength_of_kraft` | `InformationTheory/Shannon/ShannonCode.lean:164` | `theorem entropyD_le_expectedLength_of_kraft {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1)` | `: entropyD D P ≤ expectedLength P l` | reuse (Gibbs 下界, Huffman 上界が `H + 1` 以下なので **Huffman ≤ Shannon → entropy ≤ Huffman** の chain で entropy ≤ Huffman ≤ Shannon を結べる) |
| `IsPrefixFree` | `InformationTheory/Shannon/ShannonCodeKraftReverse.lean:47` | `def IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop` (variable `{α : Type*} [Fintype α] [DecidableEq α]`) | `:= ∀ a b : α, a ≠ b → ¬ c a <+: c b` | reuse 確定 (Huffman code の prefix-free 性主張 + injective とのペア) |
| `exists_prefix_code_of_kraft` | `InformationTheory/Shannon/ShannonCodeKraftReverse.lean:482` | `theorem exists_prefix_code_of_kraft {D : ℕ} (hD : 2 ≤ D) (l : α → ℕ) (hl : ∀ a, 0 < l a) (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1)` | `: ∃ c : α → List (Fin D), Function.Injective c ∧ (∀ a, (c a).length = l a) ∧ IsPrefixFree c` | reuse 確定 (Huffman 語長 → Huffman prefix code の構成 bridge) |
| `shannonFanoCode` | `InformationTheory/Shannon/ShannonCodeKraftReverse.lean:319` | `noncomputable def shannonFanoCode {D : ℕ} [NeZero D] (l : α → ℕ) (L : ℕ) (a : α) : List (Fin D)` | `:= toBaseDLen D (l a) (slotStart D l L (sortedIndex l a) / D ^ (L - l a))` | non-reuse (Huffman は別構成だが、KraftReverse の `exists_prefix_code_of_kraft` 経由で Huffman 語長 → 何らかの prefix code 存在を結ぶ手段になる) |
| `commonDepth` | `InformationTheory/Shannon/ShannonCodeKraftReverse.lean:475` | `noncomputable def commonDepth (l : α → ℕ) : ℕ` | `:= Finset.univ.sup l` | reuse (Huffman 木の最大深度を読み替える際の bridge) |

**`pmf : α → ℝ` vs `Measure α` の不整合**: roadmap 提示 statement は `pmf : Fin n → ℝ` だが、既存 `expectedLength` / `entropyD` は `Measure α` 引数。**§F-3 で要 design judgement**。

### §B. Mathlib — Huffman / prefix code 関連

| name | file:line | signature | 結論形 | T1-A での扱い |
| --- | --- | --- | --- | --- |
| `Huffman` | — | Found 0 declarations | — | **完全不在**、自作必須 |
| `PrefixCode` | — | Found 0 declarations | — | **完全不在**、自作 (KraftReverse 既存 `IsPrefixFree` で代用可) |
| `BinaryTree` / `Tree (Fin 2)` | — | (Mathlib `rg "BinaryTree"` も `rg "Tree Bool"` も hit 0) | — | **完全不在**、自作 (構造体 `inductive HuffmanTree (α : Type*) : Type*` を新規定義) |
| `InformationTheory.UniquelyDecodable` | `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean:35` | `def UniquelyDecodable (S : Set (List α)) : Prop` (variable `{α : Type*}`) | `:= ∀ (L₁ L₂ : List (List α)), (∀ w ∈ L₁, w ∈ S) → (∀ w ∈ L₂, w ∈ S) → L₁.flatten = L₂.flatten → L₁ = L₂` | (informational) Mathlib 流の prefix-code 仕様、Huffman 主張は InformationTheory `IsPrefixFree` 路線でよく、UniquelyDecodable は強すぎる |
| `InformationTheory.kraft_mcmillan_inequality` | `Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149` | `public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α] (h : UniquelyDecodable (S : Set (List α)))` | `: ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1` | (informational) `Finset (List α)` 表現での Kraft 不等式版 — InformationTheory `kraftSum` の `α → ℕ` 表現との **直接交換は不可能** (要 bridge ~50 行)。Huffman 内では InformationTheory 既存 `kraftSum` で完結し、Mathlib 版は呼ばない |

### §C. Mathlib API — sibling property 補助 (priority queue / argmin)

Huffman 構成の核「最小 2 確率を merge」用。

| name | file:line | signature | 結論形 | 用途 |
| --- | --- | --- | --- | --- |
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean:180` | `def min' (s : Finset α) (H : s.Nonempty) : α` (section variable `[LinearOrder α]`) | `:= inf' s H id` | Finset 上の min 取得 (α 自身に linear order が要る) |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean:191` | `theorem min'_mem : s.min' H ∈ s` (同 section, `(s : Finset α) (H : s.Nonempty)`) | `: s.min' H ∈ s` | merge 後の min element 存在性 |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean:194` | `theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x` | `: s.min' ⟨x, H2⟩ ≤ x` | 「他の任意 element は min 以上」 |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean:197` | `theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H` | `: x ≤ s.min' H` | 下界 → min |
| `Finset.exists_min_image` | `Mathlib/Data/Finset/Max.lean:531` | `theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) : ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x'` (section variable `[LinearOrder α]`) | `: ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x'` | **本命**: 「`α : Finset` 上で `p : α → ℝ` 最小の要素」を取り出す (probabilities の最小 2 element を順次取り出す) |
| `Multiset.exists_min_image` | `Mathlib/Data/Finset/Max.lean:567` | `theorem Multiset.exists_min_image {α R : Type*} [LinearOrder R] (f : α → R) {s : Multiset α} (hs : s ≠ 0) : ∃ y ∈ s, ∀ z ∈ s, f y ≤ f z` | `: ∃ y ∈ s, ∀ z ∈ s, f y ≤ f z` | alt 経路: priority queue を Multiset で表現 |
| `Multiset.sort` | `Mathlib/Data/Multiset/Sort.lean:30` | `def sort (s : Multiset α) (r : α → α → Prop := by exact fun a b => a ≤ b) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α` | `: List α` | 確率順 sort (Huffman queue を Multiset から List 化) |
| `Multiset.pairwise_sort` | `Mathlib/Data/Multiset/Sort.lean:47` | `theorem pairwise_sort : (sort s r).Pairwise r` | `: (sort s r).Pairwise r` | sort 後の order 保証 |
| `Multiset.sort_eq` | `Mathlib/Data/Multiset/Sort.lean:51` | `theorem sort_eq : ↑(sort s r) = s` | `: ↑(sort s r) = s` | sort は permutation (multiset 不変) |
| `List.argmin` | `Mathlib/Data/List/MinMax.lean:91` | `def argmin (f : α → β) (l : List α) : Option α` (section variable `[Preorder β] [DecidableLT β]`) | `:= l.foldl (argAux fun b c => f b < f c) none` | alt: `List.argmin` で priority-queue 不要に Huffman 可能 |
| `List.argmin_mem` | `Mathlib/Data/List/MinMax.lean:132` | `theorem argmin_mem : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l` | `: m ∈ l` | argmin element 存在 |
| `List.le_of_mem_argmin` | `Mathlib/Data/List/MinMax.lean:151` | `theorem le_of_mem_argmin : a ∈ l → m ∈ argmin f l → f m ≤ f a` (section variable `[LinearOrder β]`) | `: f m ≤ f a` | min image lower bound |

priority-queue は Mathlib 未提供 (`rg "PriorityQueue"` hit 0)。**「`Finset.exists_min_image` + 再帰」経路で十分** (Cover-Thomas 5.6 標準的構成、~80-100 行)。

### §D. Mathlib API — 最適性 induction の基盤

`n → n-1` の strong induction (`n := Fintype.card α`) で Huffman 最適性を回す.

| name | file:line | signature | 結論形 | 用途 |
| --- | --- | --- | --- | --- |
| `Finset.induction` | `Mathlib/Data/Finset/Insert.lean:480` | `protected theorem induction {α : Type*} {motive : Finset α → Prop} [DecidableEq α] (empty : motive ∅) (insert : ∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)) : ∀ s, motive s` | `: ∀ s, motive s` | empty → insert 1 element の induction (`α`-on-Finset 帰納) |
| `Finset.induction_on` | `Mathlib/Data/Finset/Insert.lean:491` | `protected theorem induction_on {α : Type*} {motive : Finset α → Prop} [DecidableEq α] (s : Finset α) (empty : motive ∅) (insert : ∀ (a : α) (s : Finset α), a ∉ s → motive s → motive (insert a s)) : motive s` | `: motive s` | 上の `s` 適用版 |
| `Multiset.strongInductionOn` | `Mathlib/Data/Multiset/Basic.lean:72` | `def strongInductionOn {p : Multiset α → Sort*} (s : Multiset α) (ih : ∀ s, (∀ t < s, p t) → p s) : p s` (termination by `card s`, decreasing by `card_lt_card`) | `: p s` | **alt 経路 (本命)**: 「Huffman queue を Multiset 化 + strong induction」 で `n → n-2 + 1` の縮約を直接書ける (cardinality strict-mono なので decreasing 自動) |
| `Finset.card_erase_of_mem` | `Mathlib/Data/Finset/Card.lean:143` | `theorem card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1` | `: #(s.erase a) = #s - 1` | `n → n-1` の card 計算 |
| `Finset.card_lt_card` | `Mathlib/Data/Finset/Card.lean:298` | `nonrec lemma card_lt_card (h : s ⊂ t) : #s < #t` | `: #s < #t` | well-founded recursion 用 (Multiset 路線で代用可) |
| `Finset.one_lt_card` | `Mathlib/Data/Finset/Card.lean:721` | `theorem one_lt_card : 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b` | `: 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b` | sibling property 前提 (`n ≥ 2` の場合に異なる 2 element 存在) |
| `Finset.one_lt_card_iff` | `Mathlib/Data/Finset/Card.lean:724` | `theorem one_lt_card_iff : 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b` | `: 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b` | 同上、∃ unfold 形 |
| `Finset.sum_le_sum` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:108` | `theorem prod_le_prod' [MulLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` (additive版 `sum_le_sum`、section variable `[OrderedCommMonoid N] {f g : ι → N} {s t : Finset ι}`) | `: ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | 期待長の不等式比較 (additive version は同名 `sum_le_sum` で `[OrderedAddCommMonoid N]` + `MulLeftMono` の足し算特殊化) |
| `Finset.sum_lt_sum` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:453` | `theorem prod_lt_prod' [MulLeftStrictMono M] (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) : ∏ i ∈ s, f i < ∏ i ∈ s, g i` (additive 版 `sum_lt_sum`、section variable `[CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M]`) | `: ∑ i ∈ s, f i < ∑ i ∈ s, g i` | (use 余地) Huffman が strict より小なら strict inequality も結べる |
| `Finset.sum_insert` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:49` (additive of `prod_insert`) | `theorem prod_insert [DecidableEq ι] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x` (section variable `{ι : Type*} [CommMonoid M] {a : ι} {s : Finset ι} {f : ι → M}`) | `: ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x` | merge 後の expectedLength の項分け |

### §E. Mathlib API — Kraft 不等式 (逆向き bridge)

| name | file:line | signature | 結論形 | T1-A での扱い |
| --- | --- | --- | --- | --- |
| `InformationTheory.kraft_mcmillan_inequality` | `Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149` | `public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α] (h : UniquelyDecodable (S : Set (List α)))` | `: ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1` | informational のみ。InformationTheory 路線 (`α → ℕ` 語長) で Huffman を書く前提なら不要 |
| `InformationTheory.UniquelyDecodable.epsilon_not_mem` | `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean:47` | `lemma UniquelyDecodable.epsilon_not_mem (h : UniquelyDecodable S) : [] ∉ S` | `: [] ∉ S` | (informational) Huffman 主張は ε ∉ code として既に `0 < l a` 仮定で書ける |
| `InformationTheory.Shannon.ShannonCodeKraftReverse.exists_prefix_code_of_kraft` | `InformationTheory/Shannon/ShannonCodeKraftReverse.lean:482` | (再掲、§A 参照) | (再掲) | **reuse 確定**: Huffman 語長関数 → Huffman prefix code 存在 |

---

## 主要前提条件ボックス

- `Finset.exists_min_image` / `Finset.min'`: image の codomain (`α` or `R`) に `[LinearOrder _]` が要る → Huffman は probabilities `α → ℝ` 上で argmin を取るので `ℝ` の linear order でOK。
- `Finset.induction` / `Finset.induction_on`: `[DecidableEq α]` 必須 → Huffman 木の merge step で `α` (の quotient) に `DecidableEq` が要る。merge 後の type は **新しい sum type** `α ⊕ Unit` を作るか **記号レベルの quotient** で扱うかで分岐 → §F-1 参照。
- `Multiset.strongInductionOn` / `Multiset.sort`: sort 用に `[DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]` 必須 → probabilities 順は `ℝ` 上の linear order なので満たす。
- `Finset.sum_le_sum`: `[OrderedAddCommMonoid N]` 必須 → `ℝ` 上 OK。
- `exists_prefix_code_of_kraft`: `D ≥ 2` 仮定 → Huffman binary なら `D = 2` で OK。
- `entropyD_le_expectedLength_of_kraft`: `[IsProbabilityMeasure P]` + `full support (∀ a, 0 < P.real {a})` 必須 → roadmap statement の `pmf` が **full support か否か** が境界条件 (§F-3 参照)。
- `InformationTheory expectedLength`: 引数が `Measure α` → roadmap `pmf : Fin n → ℝ` と整合させるなら **新 def `expectedLengthOfPmf (p : α → ℝ) (l : α → ℕ) : ℝ := ∑ a, p a * l a` を導入し、`Measure α` 版との同値補題を 1 行で結ぶ** のが最低コスト (§F-3)。

---

## 自作が必要な要素

| 優先度 | 名前 | 推奨実装 | 工数感 | 落とし穴 |
| --- | --- | --- | --- | --- |
| 1 | `HuffmanTree (α : Type*)` (inductive) | `inductive HuffmanTree (α : Type*) where | leaf : α → HuffmanTree α | node : HuffmanTree α → HuffmanTree α → HuffmanTree α` | ~30 行 | Huffman 構成は `α → ℕ` (語長) 表現と二重に持つほうが proof simpler の可能性大 — 木構造を捨てて **「sorted list of probabilities + merge」のみ** で `huffmanLength` 関数化する route (no inductive type) が proof 上は安全 |
| 1 | `huffmanLength (p : α → ℝ) : α → ℕ` | `Finset.exists_min_image` で smallest 2 を取り、`α` を一時的に `α ⊕ Unit` に拡張し再帰. termination は `Fintype.card α` 上の strong induction | ~150 行 | `α` を merge 後に変えると proof が type-级で複雑化 → **alternative: probabilities を `Multiset ℝ` で持ち、Huffman 構成完了後に α への対応を取る** (Cover-Thomas Algorithm 5.8.1 の標準形)。 ただしこれは語長関数 `α → ℕ` の **存在** に止まる non-computable な定義になる |
| 1 | `huffmanLength_kraft_le_one` | `Σ 2^(-l a) ≤ 1` を induction で示す。merge step で `2^(-(L+1)) + 2^(-(L+1)) = 2^(-L)` が key | ~80 行 | `Real.rpow` と `Nat.pow_neg` の cast 地獄 (ShannonCode 既存実装と同じ落とし穴) |
| 2 | **sibling property** (Cover-Thomas Lemma 5.8.1) | 任意の最適 prefix code に対し、最小 2 確率 element の codeword は同一 parent の兄弟 leaf である | ~150 行 | **核心の non-trivial part**。証明は: (a) 任意最適 code で最深 leaf の確率は最小 element と交換可能、(b) 最深 leaf の兄弟も最深、(c) よって最小 2 element が兄弟になる code が存在。各 step で `expectedLength` の swap 不変性 + 単調性を使う |
| 2 | `huffmanLength_optimal` (主定理) | sibling property + `n → n-1` induction (merge して IH 適用) | ~250 行 | bridge lemma: `expectedLength p (huffmanLength p) = expectedLength p' (huffmanLength p') + (p a + p b)` の **両方向**を `expectedLength p` 形と `p'`-merged 形で書くと長くなる。`huffmanLength p` の merge step での差 `+1` が直接効くので、merge step を **明示的 def** にすると short |
| 3 | `expectedLengthOfPmf (p : α → ℝ) (l : α → ℕ) : ℝ` + `Measure α` 版との同値 | ~30 行 | `pmf : α → ℝ` 路線を採るなら必須 (§F-3 参照) |
| 4 | Huffman 語長 → prefix code 存在 bridge | `exists_prefix_code_of_kraft` を呼ぶだけ | ~30 行 | `D = 2` で `hl_pos : ∀ a, 0 < huffmanLength p a` を別途示す必要 (`n ≥ 2` で `huffmanLength` の像が ≥ 1) |

**規模見積もり**: 30 + 150 + 80 + 150 + 250 + 30 + 30 = **~720 行** (roadmap 上限 700 とほぼ一致)。Huffman 木 inductive 不採用ルート (上記 priority 1 first row 削除) なら ~690 行に圧縮可能。

---

## 撤退ラインへの距離

roadmap T1-A 規模 `~500-700 行` に対し、上記積算 **720 行**。**ぎりぎり境界**。

**触れる撤退ライン**:
- **D-ary (D ≥ 3) 一般化**: sibling property を `D` 個の最小 element merge に一般化すると追加 ~200 行 → roadmap 上限を超過。**binary (D=2) 限定で着手し、D-ary 拡張は T1-A' に切り出す**ことが推奨 (撤退ライン発動回避)。
- **任意 `pmf : α → ℝ` での full support 不要化**: support 外で `p a = 0` の場合の `huffmanLength` の値が不定 → `if p a = 0 then 0 else huffmanLength p a` の対応で吸収可能だが、**最適性主張も support 外 element を含む `l : α → ℕ` を許す**と 0-確率語の長さが「いくらでも大」になり主張が trivial 化 → **support 限定** (full support `∀ a, 0 < p a` を仮定) で着手し、後で general に。撤退ライン非発動。
- **非発動条件**: binary + full support + 既存 KraftReverse の `exists_prefix_code_of_kraft` を black box 利用、Multiset-based 構成 (HuffmanTree inductive 不採用) で着手すれば、**roadmap 規模内に収まる見込み高**。

**縮退案** (規模が 700 行を超えそうな場合):
- (a) sibling property の証明を **Cover-Thomas exposition そのまま** (swap-based) で書き、algebraic な induction を最小に: ~50 行縮小可能。
- (b) Huffman 木 inductive を完全に省略し、`huffmanLength : (α → ℝ) → α → ℕ` を直接 `Multiset` 上の構成で書く: ~30 行縮小可能。
- (c) `exists_prefix_code_of_kraft` を bridge 経由で適用するのを最終 `theorem huffman_exists_prefix_code` 1 件に限定し、本体は `huffmanLength` の語長水準で完結: ~30 行縮小可能。

---

## §F. 想定 design judgement の材料

### F-1. Huffman 木の表現

3 候補：

| 候補 | 利点 | 欠点 |
| --- | --- | --- |
| (a) `inductive HuffmanTree (α : Type*)` (leaf + node) | 直感的、Cover-Thomas exposition と一致 | `α` の構造が merge step ごとに変わる (`α → α ⊕ Unit → ...`) → proof で type generality に苦しむ |
| (b) `Multiset ℝ` で確率順 queue を持ち、Huffman 語長は **存在のみ主張** (non-computable def) | 既存 `Multiset.strongInductionOn` + `exists_min_image` で induction が綺麗、`α` の type は不変 | non-computable、計算例が書けない |
| (c) `α → ℕ` の語長関数として直接定義し、木構造は捨てる | proof 上最も simple、既存 `expectedLength` `kraftSum` と直接結合 | Huffman algorithm の「木」のメンタルモデルから乖離 |

**推奨**: (c) + (b) のハイブリッド。`huffmanLength : (α → ℝ) → α → ℕ` を主役にし、内部実装で `Multiset ℝ` の strong induction を回す。`HuffmanTree` inductive は **書かない**。

### F-2. `PrefixCode` の表現 (ShannonCode.lean の既存形を継承するか新規 def か)

既存 `IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop` (KraftReverse.lean:47) + `Function.Injective c` のペアを **再利用**。新規 `structure PrefixCode` は **作らない**。

主定理の「∀ C : PrefixCode, ...」の表現は:
```
∀ (c : α → List (Fin 2)), Function.Injective c → IsPrefixFree c →
  expectedLength p (huffmanLength p) ≤ expectedLength p (fun a => (c a).length)
```
で十分。`PrefixCode` を structure 化すると signature が冗長化する。

### F-3. `expectedLength` の reuse 可否

既存 `expectedLength (P : Measure α) (l : α → ℕ) : ℝ := ∑ a, P.real {a} * l a`。

roadmap statement の `pmf : Fin n → ℝ` と整合させるには **2 路線**：

| 路線 | 実装 | 工数 |
| --- | --- | --- |
| (i) `Measure α` で統一 | `pmf` を `Measure α` (with `[IsProbabilityMeasure]`) に lift してから既存 `expectedLength` を呼ぶ。`InformationTheory/Shannon/ShannonCode.lean` の API を 100% 再利用 | bridge 補題 0 行 (既存 entropy 等が直接結合) |
| (ii) 新 def `expectedLengthOfPmf (p : α → ℝ) (l : α → ℕ) : ℝ := ∑ a, p a * l a` | 既存 `expectedLength` との同値補題 1 件 (~5 行) + 全ての主定理を新 def で書き直し | ~30 行追加 |

**推奨**: (i) (`Measure α` 統一)。`Measure.real {a}` 経由で書けば既存 Gibbs lower bound (`entropyD_le_expectedLength_of_kraft`) との結合が無コスト。roadmap statement の `pmf` 表記は **expository convention** と読み替え、Lean signature は `(P : Measure α) [IsProbabilityMeasure P]` 形で publish。

### F-4. sibling property の statement form

| 候補 | 利点 | 欠点 |
| --- | --- | --- |
| (a) intermediate lemma 化 (separate `theorem sibling_exists` で publish) | proof structure 明確、後続再利用 (D-ary 拡張等) 可 | API 表面積増 |
| (b) 主定理 induction step の **inline** 化 | 規模圧縮 (~50 行節約) | proof が monolithic、復旧困難 |

**推奨**: (a) lemma 化。signature 候補:
```lean
theorem exists_sibling_min_pair_in_optimal_code
    (p : α → ℝ) (hp_nonneg : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) (h_card : 2 ≤ Fintype.card α) :
    ∃ (l : α → ℕ) (a b : α), a ≠ b ∧ l a = l b ∧ (∀ c, l c ≤ l a) ∧
      (∀ (l' : α → ℕ), (∀ c, 0 < l' c) → (∑ c, (2 : ℝ) ^ (-(l' c : ℤ))) ≤ 1 →
        (∑ c, p c * (l c : ℝ)) ≤ (∑ c, p c * (l' c : ℝ))) := sorry
```
これは「最適 code の存在 + sibling 性」を一つに束ねるが、分解して2件にしてもよい。

### F-5. Mathlib priority queue 不在の場合の workaround

**確定**: Mathlib に priority queue 抽象は無い (`rg "PriorityQueue"` hit 0)。

3 候補：

| 候補 | 利点 | 欠点 |
| --- | --- | --- |
| (a) `Finset.exists_min_image` を使った再帰 | 標準的、`α` 上で全部完結 | 再帰の termination 証明が `Fintype.card α` に依存 → wf-rec が必要 |
| (b) `Multiset.strongInductionOn` (Multiset を確率 multiset として持つ) | termination が `card_lt_card` で自動、wf-rec 不要 | Multiset → α の対応 (sortedIndex 的 bridge) が要る |
| (c) `Multiset.sort` で sorted list を作ってから List 上 induction | 直感的 | Multiset と List の往復が proof でコスト高 |

**推奨**: (b) Multiset.strongInductionOn。`ShannonCodeKraftReverse.lean` の `sortedByLen` / `slotStart` で List ベースの sort + 累積和を作る pattern が既にあるので、proof author としては **Multiset 上で抽象化** のほうが既存 ShannonCode 路線と差別化されて clean。

---

## 着手 skeleton (`InformationTheory/Shannon/Huffman.lean`, ~30 行)

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import InformationTheory.Shannon.ShannonCode
import InformationTheory.Shannon.ShannonCodeKraftReverse

/-!
# Huffman 最適性

T1-A シードカード (`docs/textbook-roadmap.md` §Tier 1)。
binary (D = 2) prefix code に対し、Huffman 構成が任意の Kraft-feasible 語長関数より
expected length が小さいことを示す (Cover-Thomas Theorem 5.8.1)。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Huffman 語長関数 (binary, 構成的). -/
noncomputable def huffmanLength (P : Measure α) : α → ℕ := sorry

/-- Huffman 語長は Kraft 不等式 (D = 2) を充足. -/
theorem huffmanLength_kraft_le_one (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) :
    ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) ≤ 1 := sorry

/-- Huffman 語長は正値 (`Fintype.card α ≥ 2` のとき). -/
theorem huffmanLength_pos (P : Measure α) [IsProbabilityMeasure P]
    (h_card : 2 ≤ Fintype.card α) (a : α) :
    0 < huffmanLength P a := sorry

/-- **Sibling property (Cover-Thomas Lemma 5.8.1)**:
    最小 2 確率の要素の Huffman 語長が等しく、最深. -/
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c}) := sorry

/-- **主定理**: Huffman 語長は任意の Kraft-feasible 語長より expected length が小さい. -/
theorem huffmanLength_optimal
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := sorry

/-- **副系**: Huffman 語長から prefix code が構成できる
(`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由). -/
theorem exists_huffman_prefix_code
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ c : α → List (Fin 2),
      Function.Injective c ∧
      (∀ a, (c a).length = huffmanLength P a) ∧
      InformationTheory.Shannon.ShannonCodeKraftReverse.IsPrefixFree c := sorry

end InformationTheory.Shannon.Huffman
```

`InformationTheory.lean` に append する import 行:
```lean
import InformationTheory.Shannon.Huffman
```

---

## 既存率 / 自作見積もりサマリ

- **既存 API 利用率**: 補助 lemma (sort / argmin / induction / sum_le_sum / Kraft 逆向き) は **100% Mathlib + InformationTheory 既存**で揃っている。
- **自作必要 (主要定義 + 主要定理)**: **6 件** (`huffmanLength` def, `huffmanLength_kraft_le_one`, `huffmanLength_pos`, `exists_sibling_min_pair`, `huffmanLength_optimal`, `exists_huffman_prefix_code`)
- **撤退ライン発動**: **no** (binary + full support + Multiset 構成 + KraftReverse 既存 reuse で 700 行以内に収まる見込み)
- **最も危険な発見**: Mathlib `kraft_mcmillan_inequality` の signature が `Finset (List α)` (codeword 集合) 水準なのに対し、InformationTheory `kraftSum` は `α → ℕ` (語長関数) 水準で、**直接の交換が不可能**。Huffman を `α → ℕ` 路線で書く前提なら不問だが、もし途中で Mathlib の Kraft 不等式 (有限 codeword 集合) を呼ぶ羽目になると **bridge ~50 行が新規に発生**。Huffman 主定理を `α → ℕ` 水準で完結させる方針 (= 推奨 §F-3 の (i) 路線) を planner で確定させること。
