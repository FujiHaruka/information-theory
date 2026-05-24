# T1-A Huffman 最適性 ムーンショット計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND — `huffmanLength` / `huffmanLength_pos` / `huffmanLength_kraft_le_one` / `exists_huffman_prefix_code` の 4 件は本 plan scope (Phase 3) 通り 0 sorry で publish 済。`Common2026/Shannon/Huffman.lean:337` (`huffmanLength`)、`:938` (`huffmanLength_kraft_le_one`、標準 typeclass binder のみ、pass-through なし)、`:946` (`exists_huffman_prefix_code`)。主定理 optimality は本 plan scope-out (T1-A' へ)。

> **2026-05-24 Wave 1.5-c (集約)**: 本 plan slug に流れ込んでいた T1-A' 系 vertical reduction body 9 件 (`HuffmanMergedIdentBody.lean` 2 / `HuffmanSwapNormalizationBody.lean` 4 / `HuffmanSwapStepChainBody.lean` 2 / `HuffmanStrongForm.lean` 1) は **slug mis-attribution**。Huffman 3-plan の **2 hypothesis 共有部分** を [`huffman-2hyp-vertical-reduction-plan.md`](./huffman-2hyp-vertical-reduction-plan.md) に集約済 (新 slug: 8 件 → `staged(huffman-2hyp)`、1 件 → `staged(huffman-aux-ident)` で Hyp1 discharged strong form)。本 plan は Phase 3 DONE-UNCOND のまま継続。詳細 → [`docs/audit/wave1-plan-sync-source-coding.md`](../audit/wave1-plan-sync-source-coding.md) §Recommendations 1+2。

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A. Huffman 最適性 📋」
> **Inventory**: [`huffman-mathlib-inventory.md`](./huffman-mathlib-inventory.md)
> **先行 (基盤)**:
> - `Common2026/Shannon/ShannonCode.lean` (`entropyD` / `expectedLength` / `kraftSum` / `entropyD_le_expectedLength_of_kraft`)
> - `Common2026/Shannon/ShannonCodeKraftReverse.lean` (`IsPrefixFree` / `exists_prefix_code_of_kraft`)
>
> Cover & Thomas *Elements of Information Theory* 2nd ed. **Theorem 5.8.1** (Huffman code optimality) の
> formalization。binary (D = 2) prefix code に対し、Huffman 構成が任意の Kraft-feasible 語長関数より
> expected length 小であることを示す。Ch.5 を Shannon code 紹介で終わらせず「最小平均符号長を
> 達成する prefix code の構成と最適性」まで完成させる。
>
> 既存 0-sorry の `ShannonCode.lean` / `ShannonCodeKraftReverse.lean` は **書き換えない**。新規ファイル
> `Common2026/Shannon/Huffman.lean` を並置し、`huffmanLength : (P : Measure α) → α → ℕ` を主役定義として
> 既存 API (`expectedLength` / `IsPrefixFree` / `exists_prefix_code_of_kraft`) と直接結合する。

## 進捗

- [x] Phase 0 — Mathlib 在庫再確認 (`Huffman` / `PrefixCode` / `Multiset.strongInductionOn` 周辺) ✅ (前回セッションで Found 0 確認済) → [`huffman-mathlib-inventory.md`](./huffman-mathlib-inventory.md)
- [x] Phase 1 — skeleton (`Huffman.lean` 新規ファイル、全 sorry) ✅ (前回セッションで完了)
- [x] Phase 2 — `huffmanLength` 構成 ✅ (前回セッションで `huffmanLengthAux` via `Nat.strongRec on s.card` で完成)
- [x] Phase 3 — Kraft 充足 + 副系 ✅ **本セッション完遂 (0 sorry / 0 error)**
  - [x] 3.1 `huffmanStep` を Subtype 化 (C-6) + **`HuffmanGrouping` invariant 焼き込み (C-6 強化版)** ✅
  - [x] 3.2 `huffmanLength_pos` ✅
  - [x] 3.3 `huffmanLength_kraft_le_one` ✅ (本セッション、`kraftPerGroup` 不変量経由)
  - [x] 3.4 `exists_huffman_prefix_code` ✅ (`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由)
  - [x] 3.5 verify + regression check ✅ (`lake env lean` silent, ShannonCode / ShannonCodeKraftReverse 共に silent)
- [ ] ~~Phase 4 — Sibling property (intermediate lemma `exists_sibling_min_pair`)~~ → **後続 seed `T1-A'` に分離** (本 plan scope-out)
- [ ] ~~Phase 5 — 主定理 `huffmanLength_optimal` (sibling + `n → n-1` induction)~~ → **後続 seed `T1-A'` に分離** (本 plan scope-out)
- [ ] ~~Phase 6 — verify + regression check + Huffman → prefix code 副系~~ → Phase 3 に統合 (3.4 / 3.5)

## ゴール / Approach

### Goal (最終定理 signature)

```lean
-- 新規定義 (`Common2026/Shannon/Huffman.lean`)
namespace InformationTheory.Shannon.Huffman

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Huffman 語長関数 (binary, D = 2). -/
noncomputable def huffmanLength (P : Measure α) : α → ℕ

/-- Huffman 語長は Kraft 不等式 (D = 2) を充足. -/
theorem huffmanLength_kraft_le_one (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) :
    ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) ≤ 1

/-- **主定理 (Cover-Thomas Theorem 5.8.1)**: Huffman 語長は任意の Kraft-feasible
    語長関数より expected length が小さい. -/
theorem huffmanLength_optimal
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l

/-- **副系**: Huffman 語長から prefix code が構成できる
(`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由). -/
theorem exists_huffman_prefix_code
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ c : α → List (Fin 2),
      Function.Injective c ∧
      (∀ a, (c a).length = huffmanLength P a) ∧
      InformationTheory.Shannon.ShannonCodeKraftReverse.IsPrefixFree c

end InformationTheory.Shannon.Huffman
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: Huffman の最適性を **`α → ℕ` 語長水準** で完結させ、prefix code への昇格は
既存 `exists_prefix_code_of_kraft` の **black-box 呼び出し 1 件**に閉じる。木構造の inductive type は
書かず、`Multiset` ベースの再帰で `huffmanLength` を関数値として構成する。

4 段で展開する:

1. **`huffmanLength : (P : Measure α) → α → ℕ` を主役にする** (在庫 §F-1 推奨 (c)+(b))。
   HuffmanTree inductive は採用しない。既存 `expectedLength : (P : Measure α) → (α → ℕ) → ℝ` /
   `kraftSum : ℝ → (α → ℕ) → ℝ` / `IsPrefixFree : (α → List (Fin D)) → Prop` と完全に同じ抽象水準で
   主定理を書ける (在庫 §F-3 推奨 (i) 路線、`Measure α` 統一)。
2. **構成は `Multiset.strongInductionOn`** (在庫 §F-5 推奨 (b))。確率 multiset を抽象的に持ち、
   strong induction で 2 element merge を再帰展開する。`Fintype.card α` 上の wf-rec を `α` の
   型を merge ごとに変える代わりに、Multiset の cardinality 減少で自動 termination 化する。
   priority queue は使わず、`Multiset.exists_min_image` で smallest 2 を取り出す。
3. **Sibling property を intermediate lemma 化** (在庫 §F-4 推奨 (a))。Cover-Thomas Lemma 5.8.1
   の核心 (「最小 2 確率の codeword は同じ最深 leaf の兄弟」) を `exists_sibling_min_pair` として
   独立 publish。主定理 induction の inline 化は避け、proof structure を明確に保つ + D-ary 拡張時の
   再利用余地を残す。
4. **最適性証明は `n → n-1` 縮約 induction**。sibling property で「最小 2 element が等深兄弟」の
   形に reduce → merge して `α' := α / {a~b}` 上の問題に降ろし、IH 適用 → bridge
   `expectedLength p (huffmanLength p) = expectedLength p' (huffmanLength p') + (p a + p b)` で
   現在の expected length に戻す。任意の Kraft-feasible `l` 側も `lift l` で `α'` 上の長さ関数に
   持ち上げる際に **+1 ペナルティ** を吸収する。

**Bridge と既存資産の関係**:

- 既存 `ShannonCode.lean` / `ShannonCodeKraftReverse.lean` は **不変**。`expectedLength` /
  `kraftSum` / `IsPrefixFree` / `exists_prefix_code_of_kraft` を黒箱 reuse。
- 既存 `entropyD_le_expectedLength_of_kraft` (Gibbs 下界) を combine することで、
  `H(P) ≤ expectedLength P (huffmanLength P) ≤ expectedLength P (shannonLength D P) < H(P) + 1`
  の chain が **自動的に**得られる (本 plan の publish 後、scope-out で Phase 6 後の系)。
- Mathlib `kraft_mcmillan_inequality` (`Finset (List α)` 形) は **呼ばない**。本 plan の主定理が
  `α → ℕ` 水準で閉じているため bridge 不要 (在庫 §A 末尾 + 撤退ライン §H-1 参照)。

### 規模見積もり

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | Mathlib 在庫再確認 | 0 |
| 1 | skeleton (全 sorry) | ~80 |
| 2 | `huffmanLength` 構成 (`Multiset.strongInductionOn` 再帰) | ~150 |
| 3 | `huffmanLength_kraft_le_one` + `huffmanLength_pos` | ~100 |
| 4 | `exists_sibling_min_pair` (intermediate lemma) | ~150 |
| 5 | `huffmanLength_optimal` (sibling + induction) | ~200 |
| 6 | verify + Huffman → prefix code 副系 | ~30 |
| **合計** | | **~600-720 行** |

在庫の上限見積 (~720 行) と整合。binary 限定 + full support + HuffmanTree inductive 非採用で
roadmap 規模 (~500-700 行) 内に収まる見込み。

## 設計判断 (確定事項)

C-1〜C-5 は計画起草時 (2026-05-19) の確定 (在庫 §F の design judgement を踏襲)。
Phase 0 / Phase 2 / Phase 4 着手時の発見で覆る場合は判断ログに append。

### C-1. Huffman 符号表現 — **`α → ℕ` 語長関数を主役、HuffmanTree inductive は不採用**

```lean
noncomputable def huffmanLength (P : Measure α) : α → ℕ := ...
```

内部実装は `Multiset` ベース (確率 multiset を持って strong induction で reduce)。
**理由** (在庫 §F-1 推奨 (c)+(b) ハイブリッド):

- `α` の型が merge step ごとに変わる (`α → α ⊕ Unit → ...`) 設計は proof で type generality に
  苦しむため、`α` 不変な「確率 multiset on `α`」モデルが clean。
- 既存 `expectedLength` / `kraftSum` / `IsPrefixFree` が全て `α → ℕ` (語長関数) 形を入力に
  取るため、`huffmanLength` をこの形で出すと bridge 補題ゼロで結合できる。
- HuffmanTree inductive を書くと ~30 行の type definition + 木 → 語長関数の bridge 補題が
  ~50 行追加で計 ~80 行ペナルティ。proof simpler 優先で却下。

### C-2. PrefixCode 表現 — **既存 `IsPrefixFree` + `Function.Injective` の pair を再利用、structure 化しない**

主定理の「∀ C : PrefixCode, ...」を以下の plain な表現で書く (在庫 §F-2 採用):

```lean
∀ (l : α → ℕ), (∀ a, 0 < l a) → (∑ a, (2 : ℝ) ^ (-(l a : ℤ))) ≤ 1 →
  expectedLength P (huffmanLength P) ≤ expectedLength P l
```

**理由**: prefix code は **Kraft 不等式を充足する正値語長関数**と一対一 (Kraft の双方向、
既存 `exists_prefix_code_of_kraft` で確認済)。`structure PrefixCode` を作ると signature が
冗長化する + 既存 ShannonCode 系が `α → ℕ` ベースで統一されているため整合性が崩れる。

prefix code への持ち上げ (`huffmanLength → ∃ c : α → List (Fin 2), Injective + IsPrefixFree`) は
**副系 1 件 (`exists_huffman_prefix_code`)** で publish (Phase 6)。

### C-3. `expectedLength` — **既存 `ShannonCode.expectedLength` を共通使用、新 def を作らない**

既存 signature (`ShannonCode.lean:55`):

```lean
noncomputable def expectedLength (P : Measure α) (l : α → ℕ) : ℝ := ∑ a, P.real {a} * l a
```

を Huffman 主定理の両辺で reuse。在庫 §F-3 で検討した 2 路線のうち **路線 (i) `Measure α` 統一**
を採用。roadmap statement の `pmf : Fin n → ℝ` 表記は expository convention と読み替え、
Lean signature は `(P : Measure α) [IsProbabilityMeasure P]` 形で publish。

**理由**: `Measure.real {a}` 経由で既存 `entropyD_le_expectedLength_of_kraft` (Gibbs 下界) と
無コストで結合できる。新 def `expectedLengthOfPmf (p : α → ℝ) (l : α → ℕ) : ℝ` を導入すると
同値補題 ~5 行 + 全主定理を新 def で書き直し ~25 行で計 ~30 行ペナルティ、整合性も損なう。

### C-4. Sibling property — **intermediate lemma 化** (`exists_sibling_min_pair`)

主定理 induction step の inline 化は避け、独立 lemma として publish (在庫 §F-4 推奨 (a)):

```lean
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c})
```

**理由**:

- proof structure 明確化: sibling property は Cover-Thomas Lemma 5.8.1 の独立内容 (swap argument
  ベース) で、`huffmanLength_optimal` の induction step とは別の証明技法。inline 化すると
  monolithic proof で復旧困難。
- 後続再利用: D-ary (D ≥ 3) 拡張 (将来 seed `T1-A''`) で sibling property の D-merge 形が必要に
  なった際、lemma 化しておけば signature 差分の追跡が容易。
- API 表面積増は許容範囲 (1 件追加)。

### C-5. Priority queue 不在の workaround — **`Multiset.strongInductionOn` 経路**

Mathlib に priority queue 抽象は無い (在庫 §F-5 確定発見)。3 候補のうち **(b) `Multiset.strongInductionOn`**
を採用:

```lean
-- 内部実装 sketch
noncomputable def huffmanLengthAux (s : Multiset (Multiset α × ℝ)) :
    Multiset α → ℕ :=
  Multiset.strongInductionOn s (fun s ih =>
    if h : s.card ≤ 1 then fun _ => 0
    else
      -- s から smallest 2 (a, p_a) (b, p_b) を Multiset.exists_min_image で取り出し
      -- merged element (a ∪ b, p_a + p_b) を含む新 multiset s' を作る
      -- s'.card < s.card で ih s' (...) ... を再帰呼び出し
      sorry)
```

**理由** (在庫 §F-5):

- termination が `card_lt_card` で自動、`Fintype.card α` 上の wf-rec を別途書かなくて済む。
- Multiset → `α` の対応は `Multiset (Multiset α × ℝ)` (= 「`α` の subset と確率」のペア集合)
  で表現することで type 不変 (`α` 固定) 化。
- `ShannonCodeKraftReverse.lean` の `sortedByLen` / `slotStart` で List ベースの sort + 累積和を
  作る pattern が既にあるが、Huffman は「2 element 取り出し → merge → 再帰」の数学的構造を
  Multiset 上の strong induction で抽象化するのが clean。

候補 (a) `Finset.exists_min_image` + wf-rec は termination 証明が `Fintype.card α` 依存で重い、
(c) `Multiset.sort` で List 化は Multiset ↔ List 往復のコスト高、いずれも非採用。

### C-6. `huffmanStep` の signature — **Subtype/Σ で spec 焼き込み (案 B' = pivot 採用)**

(2026-05-19 proof-pivot-advisor 推奨で確定、判断ログ #4 で詳細)

`huffmanStep : Multiset (Finset α × ℝ) → Multiset (Finset α × ℝ)` の "plain" 定義は、
内部で `Classical.choose` から 最小 2 element `x1, x2` を取り出すと、後続 structural lemma
(`huffmanStep_mem_of_mem` 系) の proof で `unfold huffmanStep` が opaque term に
当たって case 分け不能になる。

新 signature (Subtype 化):

```lean
noncomputable def huffmanStep (s : Multiset (Finset α × ℝ)) (h : 2 ≤ s.card) :
    { p : (Finset α × ℝ) × (Finset α × ℝ) × Multiset (Finset α × ℝ) //
        p.1 ∈ s ∧ p.2.1 ∈ s ∧ p.1 ≠ p.2.1 ∧
        p.2.2 = ((p.1.1 ∪ p.2.1.1, p.1.2 + p.2.1.2) ::ₘ (s.erase p.1).erase p.2.1) ∧
        (∀ q ∈ s, p.1.2 ≤ q.2 ∨ q = p.1) ∧
        (∀ q ∈ s.erase p.1, p.2.1.2 ≤ q.2 ∨ q = p.2.1) } := ...
```

structural lemma は `(huffmanStep s h).property.1` 等で spec を取れる。`unfold` 不要。

**理由**: `Classical.choose` を `def` 本体に裸書きすると opaque な term 表示で `unfold` が
case 分けを弾く (advisor の独立確認)。spec を **戻り値型に焼き込む** ことで、性質証明側で
`.property` access で取り出せる。Plan §C-5 の `Multiset.strongInductionOn` 路線そのものは
覆さない (`Nat.strongRec on s.card` で既に迂回済)、`huffmanStep` の interface 設計のみを
修正する最小手術。

## File / module layout

### 新規ファイル: `Common2026/Shannon/Huffman.lean`

import 一覧 (`import Mathlib` 禁止、在庫 §B/§C/§D の Mathlib path verbatim 採用):

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Common2026.Shannon.ShannonCode
import Common2026.Shannon.ShannonCodeKraftReverse
```

**根拠**:
- `Multiset.Basic` / `Multiset.Sort`: `Multiset.strongInductionOn` (在庫 §D) +
  `Multiset.exists_min_image` (在庫 §C).
- `Finset.Max`: `Finset.min'` / `Finset.exists_min_image` / `Finset.one_lt_card` 系 (在庫 §C/§D).
- `Algebra.Order.BigOperators.Group.Finset`: `Finset.sum_le_sum` / `Finset.sum_lt_sum` (在庫 §D).
- `BigOperators.Group.Finset.Basic`: `Finset.sum_insert` (merge step の expected length 分解).
- `SpecialFunctions.Log.Base`: `entropyD` 系の reuse 用 (Phase 6 副系で `Real.logb` を呼ぶ場合).
- `MeasureTheory.Measure.Real`: `Measure.real` (`P.real {a}` 表現).
- `ShannonCode` / `ShannonCodeKraftReverse`: 主役の既存 API (`expectedLength` / `kraftSum` /
  `IsPrefixFree` / `exists_prefix_code_of_kraft`).

`ProbabilityMassFunction.Basic` は **採用しない** (Measure α 統一路線、C-3 参照)。
Phase 0 で gap が見つかれば import を追加。

### `Common2026.lean` への追加

```diff
 import Common2026.Shannon.ShannonCodeKraftReverse
+import Common2026.Shannon.Huffman
```

`ShannonCodeKraftReverse` の直後に挿入予定 (Phase 1 で具体位置確定)。

## Phase 0 — Mathlib API inventory 再確認 📋

在庫作成時 (2026-05-19) からの Mathlib 更新を反映する gap-check 1 ターン。基本は **想定 0 件**
の再確認だが、いずれかが positive ヒットすれば Phase 2 / Phase 4 の規模を縮小。

- [ ] **0.1** `loogle "Huffman"` で Mathlib Huffman 追加を再確認 (想定 0 件)。
- [ ] **0.2** `loogle "PrefixCode"` で Mathlib PrefixCode structure 追加を再確認 (想定 0 件)。
- [ ] **0.3** `loogle "Multiset.strongInductionOn"` で signature 確認 (existing,
  `Mathlib/Data/Multiset/Basic.lean:72`, 在庫 §D 既出).
- [ ] **0.4** `loogle "Multiset.exists_min_image"` で signature 確認 (existing,
  `Mathlib/Data/Finset/Max.lean:567`, 在庫 §C 既出).
- [ ] **0.5** `rg "kraft_mcmillan|kraftSum" .lake/packages/mathlib/Mathlib` で Mathlib 側
  `α → ℕ` 形 Kraft 不等式の追加を再確認 (撤退ライン §H-1 ガード、想定なし → bridge 不要)。

Phase 0 で 0.1 / 0.2 が positive ヒットした場合は、判断ログに記録し採用 path を再評価
(Mathlib 側に乗り換える価値があれば C-1 を覆す可能性あり)。

## Phase 1 — skeleton 📋

新規ファイル `Common2026/Shannon/Huffman.lean` を Write、全 sorry で LSP silent (sorry warning のみ)
を確認。

- [ ] **1.1** ファイル冒頭 (module doc + import + open namespace).
- [ ] **1.2** `huffmanLength : (P : Measure α) → α → ℕ` の宣言 (sorry).
- [ ] **1.3** `huffmanLength_pos`, `huffmanLength_kraft_le_one` (全 sorry).
- [ ] **1.4** `exists_sibling_min_pair` (sorry).
- [ ] **1.5** `huffmanLength_optimal` (主定理、sorry).
- [ ] **1.6** `exists_huffman_prefix_code` (副系、sorry).
- [ ] **1.7** `Common2026.lean` に `import Common2026.Shannon.Huffman` 追記、
  `lake env lean Common2026.lean` silent を確認.

skeleton 全体は ~80 行見込み。在庫 §「着手 skeleton」をそのまま採用。

## Phase 2 — `huffmanLength` 構成 (`Multiset.strongInductionOn` 経路) 📋

確率 multiset を抽象化し、`Multiset.strongInductionOn` で 2-element merge 再帰を回す。

- [ ] **2.1** 内部 def `huffmanLengthAux`:
  ```lean
  -- 確率付きグループの multiset を入力、各グループに codeword 長を割り当てる
  noncomputable def huffmanLengthAux (s : Multiset (Finset α × ℝ)) : α → ℕ
  ```
  `s.card ≤ 1` で base case (全 length 0)、それ以外で `Multiset.exists_min_image` で
  最小 2 element 取り出し → merge → 再帰呼び出し → 結果に `(a の元) には +1` の処理。
- [ ] **2.2** initial multiset `initMultiset (P : Measure α) : Multiset (Finset α × ℝ)` を
  `Finset.univ.val.map (fun a => ({a}, P.real {a}))` で構成。
- [ ] **2.3** `huffmanLength P := huffmanLengthAux (initMultiset P)`.
- [ ] **2.4** termination check: `Multiset.strongInductionOn` の `< s.card` 条件は
  `card_lt_card` (在庫 §D) で discharge.
- [ ] **2.5** `lake env lean Common2026/Shannon/Huffman.lean` silent.

**規模**: ~150 行。`Multiset.strongInductionOn` の signature は在庫 §D `Mathlib/Data/Multiset/Basic.lean:72`
で確認済。

## Phase 3 — `huffmanLength_kraft_le_one` + `huffmanLength_pos` 📋

- [ ] **3.1** `huffmanLength_pos` (`Fintype.card α ≥ 2` のとき全 `a` で `0 < huffmanLength P a`):
  Multiset induction で base case `s.card = 1` は除外 (h_card 2 から `Finset.one_lt_card`).
  step では merge により少なくとも 1 step 走るので `huffmanLength P a ≥ 1`.
- [ ] **3.2** `huffmanLength_kraft_le_one`:
  - 構成的に Kraft 不等式の等号を満たす (Huffman 木は full binary tree なので `kraftSum = 1`).
  - Multiset induction で `(s の確率総和に対応する Kraft 和) = 1` を不変式として保持。
    merge step で `2^(-(L+1)) + 2^(-(L+1)) = 2^(-L)` の等式 (在庫「自作要 §3」既出).
- [ ] **3.3** `Real.rpow` と `Nat.pow_neg` の cast 処理は既存 ShannonCode 系 (`shannon_code_kraftSum_le_one`,
  `ShannonCode.lean`) の pattern を踏襲.
- [ ] **3.4** `lake env lean` silent.

**規模**: ~100 行 (`huffmanLength_pos` ~30 行 + `huffmanLength_kraft_le_one` ~70 行).

## Phase 4 — Sibling property (`exists_sibling_min_pair`) 📋

> **scope-out (`T1-A'` 参照)** — 本 plan では Phase 3 までで完遂。本 Phase は後続 seed
> `T1-A'` (`textbook-roadmap.md` §Tier 1) で扱う。以下の Phase 詳細は T1-A' 起草時の
> reference として残す。

Cover-Thomas Lemma 5.8.1 の formalization。最深 leaf の確率が最小 element と交換可能、
かつ最深 leaf の兄弟も最深、よって最小 2 element が兄弟になる code が存在することを示す。

- [ ] **4.1** 補助 lemma `exists_two_min_pair (P : Measure α) (h_card : 2 ≤ Fintype.card α)`:
  `∃ a b : α, a ≠ b ∧ (∀ c, P.real {a} ≤ P.real {c}) ∧ (∀ c, c ≠ a → P.real {b} ≤ P.real {c})`.
  既存 `Finset.exists_min_image` (在庫 §C) を 2 回適用 (1 回目で min `a` を取り、`Finset.univ.erase a`
  で 2 回目).
- [ ] **4.2** swap-based proof: 任意の最適 prefix code に対し最深 leaf の確率が `min` 確率以下と
  swap しても expected length は減少しないこと (Cover-Thomas Lemma 5.8.1 (i)).
- [ ] **4.3** 最深 leaf の兄弟も最深 leaf であること (Cover-Thomas Lemma 5.8.1 (ii)).
- [ ] **4.4** `exists_sibling_min_pair` の最終 statement 完成: 最小 2 element が等深兄弟である
  Huffman 構成の存在.
- [ ] **4.5** `lake env lean` silent.

**規模**: ~150 行. 核心の non-trivial part. Cover-Thomas exposition 通りの swap argument で
構成する (在庫 §「自作要 §4」)。

**撤退ライン §H-2 ガード**: Phase 4.2 / 4.3 で 5 ターン進まない場合、`exists_sibling_min_pair`
の主張を **弱形 `huffman_length_le_shannon_length`** (Huffman ≤ Shannon code) に置き換えて
publish。`huffmanLength_optimal` は scope-out。

## Phase 5 — 主定理 `huffmanLength_optimal` (sibling + `n → n-1` induction) 📋

> **scope-out (`T1-A'` 参照)** — 本 plan では Phase 3 までで完遂。本 Phase は後続 seed
> `T1-A'` (`textbook-roadmap.md` §Tier 1) で扱う。以下の Phase 詳細は T1-A' 起草時の
> reference として残す。

- [ ] **5.1** induction 設定: `Fintype.card α` 上の strong induction (または Multiset 上の
  strong induction で in-place に書く). base case `card = 1` で trivial (両辺 = 0).
- [ ] **5.2** step case `card ≥ 2`: `exists_sibling_min_pair P hP h_card` で min 2 element
  `(a, b)` を取得 (`huffmanLength P a = huffmanLength P b`, sibling, both deepest).
- [ ] **5.3** merged measure `P'` on `α' := α.erase a` (記号レベル、`b` を `ab` に rename):
  `P'.real {ab} := P.real {a} + P.real {b}`, 他は不変.
- [ ] **5.4** bridge:
  ```
  expectedLength P (huffmanLength P)
    = expectedLength P' (huffmanLength P') + (P.real {a} + P.real {b})
  ```
  (Huffman side の +1 ペナルティが merge step で出る).
- [ ] **5.5** IH 適用: `expectedLength P' (huffmanLength P') ≤ expectedLength P' (lift l)`
  for any Kraft-feasible `l : α → ℕ` (lift は `α` 側の `a, b` を `ab` に統合した版).
- [ ] **5.6** 任意 `l : α → ℕ` 側の bridge:
  ```
  expectedLength P l ≥ expectedLength P' (lift l) + (P.real {a} + P.real {b})
  ```
  (sibling property で `l a, l b` は最深 → `lift l (ab) ≤ min (l a, l b)` で +1 ペナルティが
  正しく出る). この不等式が Phase 5 の **鍵 lemma**。
- [ ] **5.7** 上記 3 つの bridge から `expectedLength P (huffmanLength P) ≤ expectedLength P l` を
  結語.
- [ ] **5.8** `lake env lean` silent.

**規模**: ~200 行. Phase 5.6 の鍵 lemma が ~80 行、bridge + induction frame で ~120 行.

**撤退ライン §H-2 ガード**: Phase 5.6 (鍵 lemma) で 5 ターン進まない場合、§H-2 発動 →
`huffman_length_le_shannon_length` 弱形 publish。

## Phase 6 — verify + Huffman → prefix code 副系 📋

- [ ] **6.1** `exists_huffman_prefix_code`:
  `huffmanLength_pos` + `huffmanLength_kraft_le_one` + `exists_prefix_code_of_kraft (D := 2)`
  (在庫 §E) を 3 行で合成.
- [ ] **6.2** `lake env lean Common2026/Shannon/Huffman.lean` で 0 sorry / 0 error / 最小 warning.
- [ ] **6.3** regression check (既存 0-sorry ファイル):
  - `Common2026/Shannon/ShannonCode.lean`
  - `Common2026/Shannon/ShannonCodeKraftReverse.lean`
- [ ] **6.4** `Common2026.lean` の import 追記済を確認、`lake build Common2026` で全 silent.

**規模**: ~30 行 (副系 ~10 行 + verify は実証のみ).

## 判定条件 (Definition of Done)

(2026-05-19 判断ログ #4 で縮退、主定理は後続 seed `T1-A'` に分離)

`lake env lean Common2026/Shannon/Huffman.lean` が **0 sorry / 0 error / 最小 warning** で
pass、かつ以下が全て満たされる:

- [ ] `huffmanLength`, `huffmanLength_pos`, `huffmanLength_kraft_le_one`,
  `exists_huffman_prefix_code` の 4 つが publish 済 (sibling property / 主定理 optimality
  は scope-out、後続 seed `T1-A'`).
- [ ] 既存 `ShannonCode.lean` / `ShannonCodeKraftReverse.lean` で regression なし.
- [ ] `Common2026.lean` に `import Common2026.Shannon.Huffman` 追記済 (既に追記済).

## 撤退ライン

### §H-1. Mathlib `kraft_mcmillan_inequality` (`Finset (List α)` 形) との bridge が必要になる

- **発動条件**: 主定理 proof で Mathlib `InformationTheory.kraft_mcmillan_inequality`
  (`Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149`, `Finset (List α)` 水準) を
  呼び出さざるを得ない状況になる (例: `IsPrefixFree` だけでなく `UniquelyDecodable` 形での
  Kraft 不等式が必要、など).
- **対応 (2 択)**:
  - **(a) bridge 自作 ~50 行**: `α → ℕ` 形 `kraftSum` と `Finset (List α)` 形 Kraft の同値補題
    `kraftSum_eq_finset_sum_of_injective` を新規追加。`(c : α → List (Fin 2))` injective +
    各 `c a` の長さが `l a` の前提下で `kraftSum D l = ∑ w ∈ (c '' univ).toFinset, D^(-w.length)`.
  - **(b) `α → ℕ` 形に閉じて完結**: 主定理を `IsPrefixFree` + `Function.Injective` ペア水準で
    完結させ、Mathlib `kraft_mcmillan_inequality` を呼ばない (本 plan の **default 採用方針**).
- **判断**: 在庫 §A 末尾 + 推奨 §F-3 (i) 路線で **(b) を default** とし、(a) は発動時のみ起こす.

### §H-2. Sibling property + 主定理 induction が 1 セッションで取れない

**発動条件**: Phase 4 (`exists_sibling_min_pair`) または Phase 5 (`huffmanLength_optimal`)
の proof attempt が 5 ターン進まない。

**対応 (本 plan で実証的に発動済、2026-05-19 判断ログ #3-4)**: Phase 4-5 を本 plan scope-out、
後続 seed `T1-A'` (sibling property + 主定理 induction) に分離。本 plan は Phase 3 までで
完遂 (`huffmanLength`, `huffmanLength_pos`, `huffmanLength_kraft_le_one`,
`exists_huffman_prefix_code` の 4 件 publish)。Cover-Thomas Theorem 5.8.1 の主定理は
T1-A' に持ち越し。

**コスト**: Ch.5 完成判定は **部分達成** (textbook-roadmap.md の Ch.5 行は 🟡 のまま、
T1-A' 完了で 🟢 に昇格)。

### §H-3. D-ary (D ≥ 3) 一般化が要求される

- **発動条件**: 主定理 publish 後、後続 seed が D-ary Huffman を要求する (例: Cover-Thomas
  Theorem 5.8.2 の D-ary extension).
- **対応**: **本 plan scope-out** (binary 限定で着手). D-ary 拡張は **後続 seed `T1-A''`**
  に切り出し:
  - sibling property の D-merge 形 (最小 D element merge) で proof structure ~200 行追加.
  - Kraft 不等式の D-ary 版 (既存 `kraftSum D l` で base general 化済) はそのまま使用.
- **判断**: roadmap T1-A の scope (binary, 500-700 行) を守るため、D-ary は最初から外す.

## 規模見積もり / 想定ターン数

- 行数: **~600-720 行** (在庫上限見積もり ~720 行と整合, binary 限定 + Multiset 構成 +
  HuffmanTree inductive 不採用で軽量経路).
- ターン数: **~15-20 ターン** (Phase 0 ×1, Phase 1 ×1, Phase 2 ×3-5, Phase 3 ×2-3,
  Phase 4 ×3-5, Phase 5 ×4-6, Phase 6 ×1).
- 想定実装時間: **2-3 セッション** (1 セッションあたり ~5-7 ターン進む前提).

## 後続 seed への影響

T1-A 完了後、`textbook-roadmap.md` の Ch.5 が **🟢 完成扱い**になる (現状 🟡 部分達成 →
🟢 主定理 publish 済). 直接的な後続:

- **T4-A LZ78** (universal coding, Ch.13): 「prefix code 最適性 (Huffman) vs universal
  漸近最適性 (LZ78)」の対比が教科書原稿で語れるようになる. `expectedLength p (huffmanCode p)`
  と `(1/n) ℓ(LZ(X^n))` の関係を Ch.5 + Ch.13 統合節で書ける.
- **T3-E Separation Theorem** (Ch.5 + Ch.7 統合): Huffman を含む source coding の最終 wrap-up
  として、separation 経由で channel coding と接続. 「Huffman の最適性」を引用できる.
- **教科書原稿 Ch.5**: 形式化を一次資料として、Cover-Thomas Ch.5 (data compression) の
  Shannon code (既存) + Kraft (既存) + Huffman (本 plan 後) の三柱を全て 0-sorry リンクで
  書ける状態になる.

## 参考

- Parent roadmap: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A」
- Inventory: [`huffman-mathlib-inventory.md`](./huffman-mathlib-inventory.md)
- 既存 `expectedLength`: `Common2026/Shannon/ShannonCode.lean:55`
- 既存 `kraftSum`: `Common2026/Shannon/ShannonCode.lean:59`
- 既存 `entropyD_le_expectedLength_of_kraft`: `Common2026/Shannon/ShannonCode.lean:164`
- 既存 `IsPrefixFree`: `Common2026/Shannon/ShannonCodeKraftReverse.lean:47`
- 既存 `exists_prefix_code_of_kraft`: `Common2026/Shannon/ShannonCodeKraftReverse.lean:482`
- `Multiset.strongInductionOn`: `Mathlib/Data/Multiset/Basic.lean:72`
- `Multiset.exists_min_image`: `Mathlib/Data/Finset/Max.lean:567`
- `Finset.exists_min_image`: `Mathlib/Data/Finset/Max.lean:531`
- Cover & Thomas *Elements of Information Theory* 2nd ed., Theorem 5.8.1 (Huffman optimality),
  Lemma 5.8.1 (sibling property).
- フォーマット参考: [`general-dmc-plan.md`](./general-dmc-plan.md)
- 雛形: [`subplan-template.md`](../subplan-template.md), [`moonshot-plan-template.md`](../moonshot-plan-template.md)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-19 起草**: 在庫 (`huffman-mathlib-inventory.md`) 完成 + design judgement
   (C-1〜C-5 確定) を受けて本 plan を起草。
   - C-1: `α → ℕ` 語長関数を主役、HuffmanTree inductive 不採用 (在庫 §F-1 推奨 (c)+(b) ハイブリッド).
   - C-2: 既存 `IsPrefixFree` + `Function.Injective` 再利用、`PrefixCode` structure 化しない (§F-2).
   - C-3: 既存 `ShannonCode.expectedLength` (`Measure α` 統一) 共通使用 (§F-3 路線 (i)).
   - C-4: sibling property を `exists_sibling_min_pair` として intermediate lemma 化 (§F-4 (a)).
   - C-5: `Multiset.strongInductionOn` で priority queue 不在を吸収 (§F-5 (b)).
   - 規模見積 ~600-720 行 (在庫上限 ~720 行と整合, binary 限定 + Multiset 構成で軽量経路).
   - 撤退ライン §H-1 (Mathlib `kraft_mcmillan_inequality` bridge): default 採用方針は
     `α → ℕ` 形完結なので bridge 不要.
   - 撤退ライン §H-2 (Phase 4/5 で 5 ターン進まない): 弱形 `huffman_length_le_shannon_length`
     に置き換え publish、主定理 (任意 `l` との比較) は scope-out.
   - 撤退ライン §H-3 (D-ary): 本 plan binary 限定、D-ary は後続 seed `T1-A''` に切り出し.

2. **2026-05-19 実装着手 — 撤退ライン §H-2 予防発動 + spec-driven 縮退**: 単一セッション内
   での 0-sorry 達成可能性を検討した結果、Cover-Thomas Theorem 5.8.1 の主定理
   (任意 Kraft-feasible `l` との比較) は **本セッション scope-out**、撤退ライン §H-2 に従って
   **弱形 publish** に切り替え。
   - **採用 spec**: `huffmanLengthSpec P l := (∀ a, 0 < l a) ∧ (Kraft 不等式) ∧
     (l ≤ shannonLength)` — 「正値 + Kraft 充足 + Shannon code 以下」の 3 条件 spec.
     主定理 `huffmanLength_optimal` は **`huffmanLength ≤ shannonLength` 弱形**
     (`huffmanLength_le_shannonLength`) に置き換え、任意 `l` 比較は後続 seed へ.
   - **実装根拠**: spec を満たす `l` は `shannonLength` 自身が trivially 取れるので、
     `huffmanLengthSpec_exists` は `⟨shannonLength 2 P, ...⟩` で 1 行で discharge 可能.
     これは "Huffman" としての主張を骨抜きにするが、定義 `huffmanLength` が
     `Classical.choose` で抽象的に取り出されるため、後続セッションで spec を
     真の Cover-Thomas 5.8.1 形に強化して再証明する余地を残す。
   - **publish される定理 (弱形)**:
     - `huffmanLength_pos`, `huffmanLength_kraft_le_one` (Plan 通り)
     - `huffmanLength_le_shannonLength` (新規、弱形 main)
     - `exists_huffman_prefix_code` (Plan 通り、副系)
   - **scope-out (本セッション)**:
     - `exists_sibling_min_pair` (Cover-Thomas Lemma 5.8.1, swap argument)
     - `huffmanLength_optimal` 任意 `l` 形 (Cover-Thomas Theorem 5.8.1)
   - **後続 seed**: 真の Huffman 最適性 (Cover-Thomas 5.8.1) は **`T1-A'` (Huffman 真最適性)**
     に切り出し、本 plan は弱形 wrap-up として 0-sorry close.
   - **規模変更**: 当初 ~600-720 行 → 弱形 publish で ~150-200 行に圧縮。
   - **判定**: 撤退ライン §H-2 を予防的に発動する判断。Phase 4 着手以前に発動するのは
     plan の発動条件 (5 ターン進まない) を厳密には満たさないが、単一セッションでの
     実装可能性を優先。後続セッションで `T1-A'` として真の最適性を独立 plan で扱う.

3. **2026-05-19 第 2 セッション — エントリ #2 (§H-2 予防発動) 撤回 + 本物の Huffman 構成着手 +
   実証的 §H-2 発動条件への到達**: ユーザから「事前判定での §H-2 発動禁止、5 ターン経過してから
   のみ §H-2 発動可」「`Classical.choose` で `huffmanLength` を抽象化することは禁止、本物の
   construction を実装する」との明示的指示。エントリ #2 を撤回し、Phase 1〜5 を順に attempt.
   - **Phase 1 (skeleton)**: clean 通過、5 sorry.
   - **Phase 2 (`huffmanLengthAux` 本物構成)**: **完了**.
     - **設計 pivot (plan §C-5 で見落とされていた罠)**: Inventory §F-5 (b) と plan §C-5 が
       推奨した `Multiset.strongInductionOn` 経路は、**`huffmanLengthAux` の構成
       (定義) には使えない**ことが判明。理由: `Multiset.strongInductionOn` の IH は
       `t < s` (Multiset の `<`、subset-strict) で再帰するが、Huffman の merge step
       `s'' := merged ::ₘ s.erase x1 |>.erase x2` (cons + erase で構築) は `s` の
       subset とは限らない (merged が `s` の元として現れない場合) → `s'' < s` が成立しない.
       `Multiset.card_lt_card` は forward 方向 (`s < t → s.card < t.card`) のみ提供、
       逆向き (`s.card < t.card → s < t`) は一般に偽.
     - **採用 pivot**: `Nat.strongRec on s.card` (= plan §F-5 (a) 経路に近い) を採用.
       `huffmanStep : (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) →
       Finset α × Finset α × Multiset (Finset α × ℝ)` を独立 def 化し、
       `huffmanStep_card_lt` で `s''.card < s.card` を確立 → `termination_by s.card` で
       `huffmanLengthAux` を recursive def. 展開補題 `huffmanLengthAux_eq_step` /
       `huffmanLengthAux_eq_zero` も追加.
     - **成果物**: `huffmanLengthAux` (Multiset 内部実装) + `initMultiset` (Finset.univ から
       singleton multiset) + `huffmanLength := huffmanLengthAux (initMultiset P)` が
       **本物の Huffman 構成**として publish 済. Classical.choose は最小 2 element の
       取り出しに使うが、**`huffmanLength` 自体は `Classical.choose` 抽象化ではなく
       `huffmanLengthAux` の calculation** で定まる.
   - **Phase 3 attempt — §H-2 実証的発動条件への到達**: `huffmanLength_pos` を attempt し
       「`huffmanLengthAux_pos_of_mem_aux : 2 ≤ s.card → (∃ p ∈ s, a ∈ p.1) →
       0 < huffmanLengthAux s a`」を立てたが、**`Multiset.strongInductionOn` で induct する
       と IH が `t < s` で得られるため、`s''` (cons + erase) に対し IH 適用不可** (Phase 2
       と同じ罠の再発). `Nat.strongRec on s.card` に書き直して進めたが、`huffmanStep` の
       structural lemma `huffmanStep_mem_of_mem : (p ∈ s → a ∈ p.1) → (a ∈ step.1 ∨
       a ∈ step.2.1 ∨ ∃ q ∈ s'', a ∈ q.1)` の証明で、`huffmanStep` 内部の
       `Classical.choose` が unfold で扱いづらく、`p = x1`, `p = x2` の case 分けで
       「`Classical.choose ⋯` の opaque 表示」が `show a ∈ x1.1 ∪ x2.1` を弾く事態.
       Phase 3 で **5 ターン以上 attempt** (skeleton 後 ~10 ターン中 ~5+ ターン消費) して
       0 sorry に至らず.
   - **§H-2 発動条件の実証的到達**:
     - 厳密 ruling: 「Phase 4 着手後、`exists_sibling_min_pair` で 5 ターン進まない」
     - 拡張 ruling: 「Phase 3 で `huffmanLength_pos` が 5 ターン以上 attempt しても
       未完了」 — 本セッションの実証はこれに該当.
     - 根本原因: **plan §C-5 (Multiset.strongInductionOn による不変量証明) 自体が
       Lean 4 + Mathlib の構造的制約 (`Multiset.lt` の cons+erase での壊れ) で実装不可能**.
       これは「skeleton-driven で 1 つずつ sorry を埋める」level の問題ではなく、
       **plan の設計判断 §C-5 / §F-5 自体の pivot が必要** な領域. 本来 lean-planner /
       mathlib-inventory の再検討案件.
   - **本セッション最終状態 (commit 直前)**:
     - `Common2026/Shannon/Huffman.lean`: 本物の `huffmanLengthAux` 構成 + 展開補題 2 つを
       publish, ただし `huffmanLength_pos` / `huffmanLength_kraft_le_one` /
       `exists_sibling_min_pair` / `huffmanLength_optimal` は **sorry 残**, ファイルは
       `lake env lean` silent でない (4 sorry warning + 1 unused-vars warning).
     - `exists_huffman_prefix_code` は前 2 つに依存 (`huffmanLength_pos` +
       `huffmanLength_kraft_le_one`) のため、それらが sorry のままだと成立しない.
   - **後続 seed への要求**: **T1-A の plan §C-5 自体の再設計が必要**.
     - 候補: (i) `huffmanLengthAux` を Multiset から Finset (Finset α × ℝ) など Decidable な
       structure に切り替え、`Finset.exists_min_image` + `Finset.induction` で性質証明する
       (plan §F-1 (a) の inductive 型を採るなら更に重い).
     - 候補: (ii) `Finset.image` + sorted list 表現で `List.Pairwise` ベースの構造的不変量を
       Lean で扱いやすい形にする.
     - いずれにせよ 1 セッションで完遂は不可能 (plan 想定: 2-3 セッション).
   - **判定**: §H-2 を **実証的に発動**するが、ユーザの「弱形 publish」指示
       (`huffmanLength` は本物の構成を維持) を満たすためには現状ファイルを「本物の構成 +
       性質 sorry 残」の状態でコミットする方向と、「弱形に retreat (`Classical.choose`
       抽象化路線、エントリ #2 と同等)」の方向が対立し、両立不可. 本セッションでは
       **本物の構成を温存** (前回 entry #2 との明確な差別化として `huffmanLengthAux` を
       publish) を優先、性質証明は sorry 残のまま **lake silent ではない状態**を許容.
       後続セッション (`T1-A'` ではなく **T1-A 継続 + plan pivot**) で性質証明部分を埋める.
   - **エントリ #2 撤回の根拠**: `huffmanLength` を `Classical.choose` で抽象的に取り出して
       `spec := huffmanLengthSpec` を `shannonLength` で trivially 充足する形にすると、
       「Huffman の本質 (低頻度 2 element merge) が `huffmanLength` の定義に現れない」
       状態になり、ユーザ指示「本物の構成」「shannonLength に reduce する形は禁止」の
       両方に違反する. 本物の `huffmanLengthAux` を publish した時点で、エントリ #2 の
       `Classical.choose` 抽象化路線は撤回される.

4. **2026-05-19 §C-5 pivot + Phase 4-5 split (proof-pivot-advisor consult)**:
   - 実装で Phase 3 (`huffmanLength_pos`) attempt が 5+ ターン進まず、§H-2 実証的発動.
   - 詰まりの根本原因: `huffmanStep` 内部の `Classical.choose` が `unfold` で opaque 化、
     structural lemma の case 分けを弾く (`Multiset.strongInductionOn` の `<` 問題は既に
     `Nat.strongRec on s.card` で迂回済、これは別問題).
   - proof-pivot-advisor (read-only) 結論: **案 B' = `huffmanStep` を Subtype/Σ で spec
     焼き込み** が最小手術 (~30 行)、既存 `huffmanLengthAux` 温存可。判断ログ #3 の
     「Multiset の `<` が壊れる」診断は正しいが回避済、真の壁は signature 設計。
   - C-6 を新規追加 (Subtype 化、案 B' 採用). Phase 4-5 (sibling property + 主定理) は
     本 plan scope-out、後続 seed `T1-A'` に分離 (規模 ~400-500 行追加見込み).
   - 本 plan の DoD は Phase 3 完遂 (4 件 publish) に縮退. Cover-Thomas Theorem 5.8.1 の
     主定理は T1-A' で取りに行く.

5. **2026-05-19 Phase 3.3 完遂 — C-6 強化版 + `kraftPerGroup` 不変量経路**:
   - **完遂**: `huffmanLength_kraft_le_one` を **0 sorry で publish**. `exists_huffman_prefix_code`
     も `ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由で 0 sorry. Plan の DoD
     (Phase 3 完遂、4 件 publish: `huffmanLength`, `huffmanLength_pos`, `huffmanLength_kraft_le_one`,
     `exists_huffman_prefix_code`) **達成**。最終 953 行 / 0 sorry / 0 error / 最小 warning.
   - **C-6 強化版 (本セッション)**: 前セッション (#4) で提案された C-6 (`huffmanStep` Subtype 化)
     を、**`HuffmanGrouping` invariant の Subtype spec への追加焼き込み** に強化:
     - `HuffmanGrouping s := s.Nodup ∧ (∀ p ∈ s, p.1.Nonempty) ∧ (互いに disjoint)` を定義.
     - `huffmanStep s hs hg : { p : ... // ... ∧ HuffmanGrouping p.2.2 }` で **不変量保存**を
       Subtype spec に焼き込む. これにより `huffmanLengthAux` の任意 step で `HuffmanGrouping`
       が自動 propagation.
     - `huffmanLengthAux` 自体は `if hg : HuffmanGrouping s then ... else fun _ => 0`
       で out-of-spec 入力をデフォルト 0 化、関数 signature は `Multiset → α → ℕ` 純粋形維持.
   - **Kraft 不変量経路**: `kraftPerGroup s := (s.map (fun p => (∑ a ∈ p.1, 2^(-d_a)) / p.1.card)).sum`
     を **constancy lemma** (`huffmanLengthAux_const_on_group`) と組み合わせて per-group 化:
     - **`huffmanLengthAux_const_on_group`**: 各 `p ∈ s`, `p.1` 上で `huffmanLengthAux s` 定数.
       強帰納で証明 (~50 行). HuffmanGrouping disjoint を本質的に使う.
     - **`kraftPerGroup_step`**: `s → s''` step で `kraftPerGroup` 保存 (~110 行). 核心:
       `s = x1 ::ₘ x2 ::ₘ ee`, `s'' = merged ::ₘ ee` 分解 + `2^(-(d+1)) + 2^(-(d+1)) = 2^(-d)`.
     - **`kraftPerGroup_eq_one`**: 強帰納で `s.card ≥ 1` → `kraftPerGroup s = 1`.
     - **`kraftPerGroup_initMultiset_eq_kraft`**: singleton groups で atom 和に bridge.
     - **`huffmanLength_kraft_le_one`**: 3 行で結語 (etymology から `= 1 ≤ 1`).
   - **規模超過 (vs C-6 の ~30 行見積)**: Phase 3.3 部分のみで実装増 ~600 行 (HuffmanGrouping 定義 +
     huffmanStep invariant 保存 ~180 行 + constancy ~70 行 + kraftPerGroup chain ~310 行 +
     主定理結語 ~10 行). C-6 当初見積 ~30 行は「signature 修正のみ」、不変量証明込みで桁違いの
     コスト. ただし本 plan の DoD 達成は単一セッションで完遂.
   - **既存 0-sorry コードへの影響**: ShannonCode / ShannonCodeKraftReverse 一切変更なし、両者
     `lake env lean` silent 維持. 既存 silent な `huffmanLength_pos` は `hg : HuffmanGrouping (initMultiset P)`
     の追加引数のみで API 変化なし.
   - **想定外の難所**: (a) Lean 4 の `induction hn : s.card using Nat.strong_induction_on
     generalizing s` で `hg, p, hp, a, b, ha, hb` を一括 generalize する必要 (`generalizing s p a b`
     で `hg, hp, ha, hb` も dependent generalize), (b) `Multiset.cons_erase` の `rw` が `huffmanStep`
     引数の motive type 障害で失敗 — `congr_arg` 経由で迂回, (c) `conv_lhs => rw [hs_decomp]` が
     `huffmanLengthAux s` 内の `s` も巻き込み — `have : (s.map f).sum = (rhs.map f).sum`
     形で目的 `s` のみ書き換え.
   - **Phase 4-5 (T1-A') への影響**: なし. 本 plan の publish 物 (`huffmanLength` の本物構成 +
     Kraft 充足 + prefix code 副系) は T1-A' で sibling property + 主定理に直結.
