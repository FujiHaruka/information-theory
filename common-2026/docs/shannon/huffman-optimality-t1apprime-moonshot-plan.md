# T1-A'' Huffman 最適性 (2 hypothesis 完全 discharge) ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge)」
> - 先行 (T1-A 完了): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md) (archive 参照のみ)
> - 直接前任 (T1-A' 完了, weak form publish): [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md)
>
> **Inventory**: [`huffman-optimality-t1apprime-mathlib-inventory.md`](./huffman-optimality-t1apprime-mathlib-inventory.md) (2026-05-19 作成)
>
> **既存実装 (T1-A + T1-A' 完了、不変として再利用)**:
> - `Common2026/Shannon/HuffmanOptimality.lean` (1054 行 / 0 sorry / weak form publish 済)
> - `Common2026/Shannon/Huffman.lean` (961 行 / 0 sorry、`huffmanLength_kraft_eq_one` 含む)
> - `Common2026/Shannon/ShannonCode.lean`, `ShannonCodeKraftReverse.lean`.
>
> **Status (2026-05-19)**: 計画起草。実装未着手。
>
> **Goal**: T1-A' で `Prop` abbrev として hypothesis pass-through 化された 2 件
> (`SwapNormalizationHypothesis` + `HuffmanMergedIdentificationHypothesis`) を完全証明し、
> 引数 hypothesis なしの **強形 `huffmanLength_optimal`** (Cover-Thomas Theorem 5.8.1) を
> `Common2026/Shannon/HuffmanOptimality.lean` **末尾追記** で publish (新規 file 不要、
> 同 namespace 内完結)。

## 進捗

- [ ] Phase 0 — 在庫再確認 + Phase A/B 着手前 1 行 probe 📋 → [`huffman-optimality-t1apprime-mathlib-inventory.md`](./huffman-optimality-t1apprime-mathlib-inventory.md)
- [ ] Phase A — `swap_normalization_proof : SwapNormalizationHypothesis` 完全証明 📋
  - [ ] Phase A1 — bubble sort metric + `swap_step_le` 再帰 loop (~80 行)
  - [ ] Phase A2 — shortening (Kraft = 1 で最長 codeword を 1 削減) (~70 行)
- [ ] Phase B — `huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis` 完全証明 📋
  - [ ] Phase B0 — `initMultiset mergedMeasure ↔ initMultiset Q` lift 構造補題 (~50 行)
  - [ ] Phase B1 — `huffmanStep` 両側 correspondence + `Classical.choose` compatibility (~40 行)
  - [ ] Phase B2 — `huffmanLengthAux` congr で H2 主等式結語 (~80 行)
- [ ] Phase M — 強形主定理 `huffmanLength_optimal` (~3 行 wrapper) 📋
- [ ] Phase V — verify + regression 📋

## ゴール / Approach

### Goal (最終定理 signature)

```lean
-- `Common2026/Shannon/HuffmanOptimality.lean` 末尾に追記 (新規 file 不要)
namespace InformationTheory.Shannon.Huffman

/-- **Hypothesis 1 discharge** — Cover-Thomas Lemma 5.8.1 (i) 完全証明. -/
theorem swap_normalization_proof : SwapNormalizationHypothesis.{u} := ...

/-- **Hypothesis 2 discharge** — `huffmanLength` identification on `mergedMeasure`. -/
theorem huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis.{u} := ...

/-- **Cover-Thomas Theorem 5.8.1 (strong form)** — hypothesis 引数なし強形. -/
theorem huffmanLength_optimal
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  exact huffmanLength_optimal_with_hypotheses
    swap_normalization_proof huffman_merged_identification_proof
    P hP l hl_pos hl_kraft

end InformationTheory.Shannon.Huffman
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: T1-A' で publish 済の skeleton (`huffmanLength_optimal_with_hypotheses`
+ 2 `abbrev Prop` + `swap_step_le` ~96 行 helper + `mergedMeasure` + sibling property
取得経路) と T1-A の Kraft = 1 等式 (`huffmanLength_kraft_eq_one`) を **黒箱 reuse** し、
hypothesis 2 件を **末尾追記 ~400 行**で完全 discharge。

**新規 file は作らない**: 既存 `HuffmanOptimality.lean` (1054 行 / 0 sorry) の末尾に
`/-! ### T1-A'' — 2 hypothesis discharge -/` セクションを追加して完結。ファイル末尾の
`end InformationTheory.Shannon.Huffman` 直前に挿入。最終 ~1450 行 / 0 sorry / 0 warning 目標。

**T1-A' との関係 (なぜ T1-A'' が必要か)**:

- T1-A' は Phase 4 swap normalization 実装中、2-step swap 単独では `l_norm a = l_norm b`
  を一般 Kraft-feasible `l` (≤ 1) について保証できない反例 (`l = (3, 1, 2)`) を発見
  (T1-A' 判断ログ #6 Sorry #1)。Cover-Thomas 標準証明では full binary tree 仮定 (Kraft = 1)
  が暗黙に効いており、`l` が strict slack を持つ場合は先に **shortening** で Kraft = 1 化
  する必要。
- 同じく T1-A' は Phase 4 で `h_sibling` 単独では `huffmanLength (mergedMeasure Q a b hab) x
  = ...` を identification するのに不足 (反例: `P{α₁} = P{α₂} = 0.1, P{α₃} = P{α₄} = 0.4` で
  `α₃, α₄` が同 huffmanLength でも min-prob pair ではない、T1-A' 判断ログ #6 Sorry #2)。
  `h_a_min` / `h_b_min` 強化と `huffmanStep` の両側 correspondence 構造補題が要。
- T1-A' は案 X (~220-360 行 discharge) vs 案 Y (~50 行 weak form publish) の context cost
  比較で **案 Y 採用**、本 plan T1-A'' が案 X の完遂を引き継ぐ (T1-A' 判断ログ #7)。

**2 hypothesis の数学的意味 (Cover-Thomas Theorem 5.8.1 の標準証明 mapping)**:

- **Hypothesis 1 (Swap Normalization, Cover-Thomas Lemma 5.8.1 (i))**: 任意 Kraft-feasible
  `l` に対し、`l a = l b` (同最深 leaf) かつ expected length 非増加 + Kraft 維持の
  `l_norm` が存在する、を主張。本 plan Phase A で 2 段で証明: (A1) bubble sort metric 上で
  `swap_step_le` を再帰呼びし、(a, b) を含む最深 leaf に確率順序を整える、(A2) `l a ≠ l b`
  が残る場合に Kraft slack を吸収する **shortening 操作** で `l b` を 1 削減 (Kraft = 1 化
  すれば `l a = l b` 強制成立、`huffmanLength_kraft_eq_one` 経由)。
- **Hypothesis 2 (Huffman Merged Identification)**: Huffman 構成の再帰構造 —
  `(mergedMeasure Q a b hab)` 上の Huffman 結果が、もとの `Q` 上の Huffman 結果から
  `a` の codeword を 1 削って `b` を除く操作と一致する、という構造的等式。Cover-Thomas
  証明では暗黙の「最後の merge step が `{a, b}` を pick up する」+「残りの induction step
  が `α' = α \ {b}` 上で平行展開」を Lean 上で形式化する必要。Phase B で `initMultiset`
  lift + `huffmanStep` の両側 correspondence + `huffmanLengthAux` congr の 3 段。

### 規模見積もり

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | 在庫再確認 + 1 行 probe | 0 |
| A1 | bubble sort metric + swap loop | ~80 |
| A2 | shortening (Kraft = 1 化) | ~70 |
| B0 | `initMultiset` lift 構造補題 | ~50 |
| B1 | `huffmanStep` 両側 correspondence | ~40 |
| B2 | `huffmanLengthAux` congr で H2 結語 | ~80 |
| M | 強形主定理 wrapper | ~3 |
| V | verify + regression | 0 |
| **合計** | | **~325 → ~400 行 (実装余裕込み)** |

**最終ファイル**: `HuffmanOptimality.lean` 1054 → **~1450 行 / 0 sorry / 0 warning**.

inventory §F の 「~400 行」 ベースの実装余裕 + Phase B0 構造補題 (~50 行) + Phase A2 で
`strict_kraft_one_implies_pairing_lemma` 自前 (~40 行) を加えた見積。inventory §「自作要」
合計 ~400 行と整合 (Phase A1+A2 ~150 + Phase B0+B1+B2 ~170 + 主定理 wrapper ~3 + 余裕)。

### Mathlib API 在庫 (inventory verbatim ref)

inventory `huffman-optimality-t1apprime-mathlib-inventory.md` §B/§C (Phase A)、§D (Phase B)
の `file:line + signature + 引数 + 結論` を実装時 verbatim 参照。主要候補のみ再掲:

- **Phase A**:
  - `Equiv.swap` / `Equiv.swap_apply_left/right/of_ne_of_ne/self`
    (`Mathlib/Logic/Equiv/Basic.lean:634, 650, 654, 657, 639`)
  - `Function.update` / `update_self` / `update_of_ne` / `update_apply` / `update_idem` /
    `update_comm` (`Mathlib/Logic/Function/Basic.lean:628, 632, 636, 640, 764, 759`)
  - `Tuple.bubble_sort_induction` (`Mathlib/Data/Fin/Tuple/BubbleSortInduction.lean:52`) ※
    `Fin n → α` 限定。inventory 推奨は alt (ii) **bubble sort metric + `Nat.strongRecOn'` 直接**。
  - `Finset.exists_max_image` (`Mathlib/Data/Finset/Max.lean:525`)
  - `Finset.add_sum_erase` / `sum_erase_add` (`...Group/Finset/Basic.lean:741, 747`)
  - `zpow_add₀` / `zpow_sub_one₀` (`...GroupWithZero/Basic.lean:494, 489`)
  - `Nat.strong_induction_on` (`Mathlib/Data/Nat/Init.lean:281`、T1-A' 既使用)
- **Phase B**:
  - `Multiset.map` / `map_map` / `map_congr` (`Mathlib/Data/Multiset/Basic.lean`)
  - `Multiset.cons_erase` / `mem_erase_of_ne` / `card_erase_of_mem` / `mem_of_mem_erase`
    (`Mathlib/Data/Multiset/AddSub.lean:173, 218, 239, 221`)
  - `Multiset.exists_min_image` (`Mathlib/Data/Finset/Max.lean:567`)
  - `Multiset.strongInductionOn` (`Mathlib/Data/Multiset/Basic.lean:72`、alt)
  - `Finset.image_erase` (T1-A' 既使用)
- **Common2026 既存**:
  - `swap_step_le` (`HuffmanOptimality.lean:650`)
  - `mergedMeasure` + `mergedMeasure_real` + `mergedMeasure_isProbabilityMeasure` +
    `mergedMeasure_pos` (`HuffmanOptimality.lean:244, 251, 550, 624`)
  - `huffmanLength_kraft_eq_one` (`Huffman.lean:924`)
  - `huffmanStep_initMultiset_sibling` (`HuffmanOptimality.lean:66`、`private`)
  - `huffmanLengthAux_step_merged` / `_step_other` / `_const_on_group` /
    `_step_eq_on_other_group` / `huffmanStep_orig_decomp` (`Huffman.lean:614, 625, 467, 636, 599`)

## 設計判断 (確定事項)

C-A-1 / C-B-1 / C-W-1 は計画起草時 (2026-05-19) の確定。Phase 着手時の発見で覆る場合は
判断ログに append。

### C-A-1. Phase A 経路 — `Tuple.bubble_sort_induction` 不採用、**bubble sort metric 上の直接 induction を採用**

inventory §B alt 候補 (ii) を採用 (推奨ライン):

```lean
-- 内部 metric (sketch)
private noncomputable def swap_metric (Q : Measure β) [IsProbabilityMeasure Q] (l : β → ℕ) : ℕ :=
  ((Finset.univ : Finset (β × β)).filter
    (fun p => l p.1 > l p.2 ∧ Q.real {p.1} ≤ Q.real {p.2})).card
```

`Nat.strongRecOn'` で `swap_metric Q l_norm` 上の strong induction を回し、`swap_step_le`
(`HuffmanOptimality.lean:650`) を一段ずつ呼び出す。bubble sort 完了で
`∀ x y, l x > l y → Q.real {x} > Q.real {y}` を不変式として確立。

**理由**: `Tuple.bubble_sort_induction` は `f : Fin n → α` 専用、我々の `l : β → ℕ`
(任意 `β` with `[Fintype β]`) に直接適用するには `Fintype.equivFin` 経由の **抽象 ↔ Fin**
bridge ~30 行が新規必要 (inventory 一行サマリの最大の発見、危険度高)。alt (ii) なら
`Fin` bridge 不要で完結。`swap_step_le` 既存 helper を verbatim 再帰呼び出しできるため
実装も明快。

### C-A-2. Phase A2 shortening 経路 — **Kraft = 1 化 + 最長 codeword を 1 削減**

A1 で bubble sort 完了後、`l a ≠ l b` (両者が最深 leaf ペアでない) ケースが残り得る。
このとき **Kraft slack** `1 - ∑ 2^(-l)` を吸収して最長 codeword `l b` を 1 削減する
shortening 操作:

```lean
-- sketch (Phase A2 内 helper)
private def shorten (l : β → ℕ) (b : β) : β → ℕ := Function.update l b (l b - 1)
```

Kraft sum は `2^(-l b)` から `2^(-(l b - 1)) = 2 · 2^(-l b)` に増えるので、slack
`1 - kraftSum` から `2^(-l b)` を吸収できれば feasible 維持。`zpow_sub_one₀` + Kraft slack
不等式 ~40 行で構成。`huffmanLength_kraft_eq_one` (`Huffman.lean:924`) を `l` 側 Kraft = 1
の場合に **`l a = l b` 強制成立** を導く self-written lemma (inventory §F 「自作要」優先度 2
`strict_kraft_one_implies_pairing_lemma`) で結語。

**理由**: inventory §C で「Kraft slack の活用」と推奨済。`Function.update` (`update_self` /
`update_of_ne` / `update_idem` / `update_comm`) の Mathlib API は完備、bridge 不要。
expected length 側は `P.real {b} * (l b - 1) - P.real {b} * l b = - P.real {b} ≤ 0` で
直接非増加。

### C-B-1. Phase B identification 経路 — **point-wise identification の場合分け 2 通り (`x.val = a` / `x.val ≠ a`) を `huffmanStep` 構造補題で個別証明**

H2 の主等式 (T1-A' weak form):

```lean
huffmanLength (mergedMeasure Q a b hab) x
  = (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val)
```

を **以下の 3 段に分解** (inventory §D):

1. **B0 (lift 構造補題)**: `initMultiset (mergedMeasure Q a b hab)` を `initMultiset Q` から
   `Multiset.map (Subtype.val-lift)` + `erase b` + `update a` で書き換える等式
   (`initMultiset_mergedMeasure_eq` 自作 ~50 行、inventory §F 「自作要」優先度 1)。
2. **B1 (huffmanStep correspondence)**: 両側の 1 step Huffman が `(a, b)` を pick up する
   ことを `huffmanStep_initMultiset_sibling` (既存 private) と `Classical.choose`
   compatibility (両側で「smallest 2」の選択が一致) で示す (`huffmanStep_initMultiset_sibling_equiv`
   自作 ~40 行、inventory §F 「自作要」優先度 1)。
3. **B2 (huffmanLengthAux congr)**: 残り `Multiset` 上の strong induction で再帰呼び出しが
   同 trajectory を辿ることを `huffmanLengthAux` の strong induction で示し、point-wise の
   if-then-else 形に結語 (`huffmanLength_mergedMeasure_eq_step_quotient` 自作 ~80 行、
   inventory §F 「自作要」優先度 1)。

**理由**: T1-A' 判断ログ #3 で「`huffmanLength (mergedMeasure ...)` と `huffmanLength Q` の
**型不一致**」が露顕した経緯あり (Phase 3.3 signature pivot)。本 plan では型不一致を
`Subtype.val` lift の Multiset 構造補題 (B0) で 1 段に閉じ、残りは既存 step lemma
(`huffmanLengthAux_step_merged` / `_step_other` / `_const_on_group`) の `α/α'` 両側
instantiation で congr する。inventory §D verbatim 再利用ライン。

### C-W-1. wrapper signature — **T1-A' `huffmanLength_optimal_with_hypotheses` を hypothesis 引数で discharge する 3 行 form**

```lean
theorem huffmanLength_optimal
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses
    swap_normalization_proof huffman_merged_identification_proof
    P hP l hl_pos hl_kraft
```

**理由**: T1-A' の signature
(`huffmanLength_optimal_with_hypotheses {α : Type u} ... → ...`) は不変、本 plan は
`{α : Type*}` レベルで wrapper を起こすだけ。universe `u` 周りは T1-A' で確定済 (weak form
hypothesis abbreviation を `universe u` + `Type u` で起こした経緯、`HuffmanOptimality.lean:755`)。

## 依存関係

- **完了済 (黒箱 reuse、書き換えない)**:
  - **T1-A**: `Common2026/Shannon/Huffman.lean` (961 行 / 0 sorry).
    `huffmanLength`, `huffmanLengthAux`, `huffmanStep` (Subtype + `HuffmanGrouping`),
    `huffmanLengthAux_step_merged` / `_step_other` / `_const_on_group` /
    `_step_eq_on_other_group`, `huffmanStep_orig_decomp`, `huffmanLength_kraft_eq_one`.
  - **T1-A'**: `Common2026/Shannon/HuffmanOptimality.lean` (1054 行 / 0 sorry).
    `mergedMeasure` (+ `_real` / `_isProbabilityMeasure` / `_pos`), `swap_step_le`,
    `huffmanStep_initMultiset_sibling` (private), `SwapNormalizationHypothesis` /
    `HuffmanMergedIdentificationHypothesis` (`abbrev Prop`, universe-polymorphic),
    `huffmanLength_optimal_with_hypotheses`.
  - **Shannon code 基盤**: `ShannonCode.lean` (`expectedLength`),
    `ShannonCodeKraftReverse.lean` (`IsPrefixFree`, `exists_prefix_code_of_kraft`).
- **Mathlib**: 不変。T1-A' Phase 0 で確認済の Subtype type-class 継承 (`Fintype` /
  `DecidableEq` / `MeasurableSpace` / `MeasurableSingletonClass` / `Nonempty`) を本 plan
  でも引き継ぐ。新規 import は **基本不要** (`Equiv.swap` / `Function.update` /
  `Finset.exists_max_image` / `Finset.add_sum_erase` 等は T1-A' で既 import 済)。
  Phase B で `Multiset.map_congr` 系を直接呼ぶ場合のみ `Mathlib.Data.Multiset.Basic` 追加
  検討 (T1-A' 経由で既 import の可能性高、Phase 0 で probe)。
- **Common2026.lean**: import 追記不要 (HuffmanOptimality.lean 末尾追記のため import 関係不変)。

## File / module layout

### 編集対象: `Common2026/Shannon/HuffmanOptimality.lean` (末尾追記のみ)

末尾 `end InformationTheory.Shannon.Huffman` 直前 (line 1054) に
`/-! ### T1-A'' — 2 hypothesis discharge -/` セクションを追加。**新規 file は作らない**。
追加 import が必要になる場合 (Phase 0 で確定) はファイル冒頭 import ブロックに追記。

予定 skeleton (inventory §H verbatim, Phase 1 で立ち上げ):

```lean
/-! ### T1-A'' — 2 hypothesis discharge -/

-- Phase A
private noncomputable def swap_metric (Q : Measure β) [IsProbabilityMeasure Q] (l : β → ℕ) : ℕ :=
  ((Finset.univ : Finset (β × β)).filter
    (fun p => l p.1 > l p.2 ∧ Q.real {p.1} ≤ Q.real {p.2})).card

private theorem swap_metric_strict_decrease ... := by sorry  -- Phase A1 helper

private theorem swap_normalization_aux ... := by sorry        -- Phase A1+A2 本体

theorem swap_normalization_proof : SwapNormalizationHypothesis.{u} := swap_normalization_aux

-- Phase B
private lemma initMultiset_mergedMeasure_lift_eq ... := by sorry           -- Phase B0
private lemma huffmanStep_initMultiset_sibling_equiv ... := by sorry       -- Phase B1
private lemma huffmanLength_mergedMeasure_eq_step_quotient ... := by sorry -- Phase B2

theorem huffman_merged_identification_proof :
    HuffmanMergedIdentificationHypothesis.{u} :=
  huffmanLength_mergedMeasure_eq_step_quotient

-- Phase M (主定理 wrapper)
theorem huffmanLength_optimal ... :=
  huffmanLength_optimal_with_hypotheses
    swap_normalization_proof huffman_merged_identification_proof
    P hP l hl_pos hl_kraft
```

`Common2026.lean` への変更: **なし**。

## Phase 0 — 在庫再確認 + Phase A/B 着手前 1 行 probe 📋

inventory (`huffman-optimality-t1apprime-mathlib-inventory.md`) 作成時 (2026-05-19) の
前提を再確認する gap-check 1 ターン。基本 0 件 ヒット見込み。

- [ ] **0.1** `Equiv.swap` / `swap_apply_*` / `Function.update*` 等が `HuffmanOptimality.lean`
  冒頭 import から visible か `lake env lean` で確認 (T1-A' で import 済の想定)。
- [ ] **0.2** `loogle "Tuple.bubble_sort_induction"` で `Fin n → α` 限定の signature を再確認
  (inventory §B、alt (ii) 採用判断の最終確認 — `α` 型を Fin に bridge する追加 ~30 行を
  避けるための判断)。
- [ ] **0.3** `loogle "Finset.exists_max_image"` で `Mathlib/Data/Finset/Max.lean:525` 確認
  (Phase A2 shortening で最長 codeword 位置取り出しに使用、T1-A' 既出 `exists_min_image` の
  双対).
- [ ] **0.4** `loogle "Multiset.map_congr"` で signature 確認 (Phase B0 lift 構造補題で
  使用、inventory §D 既載).
- [ ] **0.5** `zpow_sub_one₀` の signature 確認 (Phase A2 で `2^(-(l b - 1)) = 2 · 2^(-l b)`
  に使用). `loogle "zpow_sub_one₀"` 1 query.
- [ ] **0.6** `huffmanLength_kraft_eq_one` の正確な signature 確認 (`Huffman.lean:924`),
  Phase A2 で `l` 側 Kraft = 1 を仮定したときの `l a = l b` 強制成立への bridge 設計用.

Phase 0 で 0.2 が positive ヒット (= `α` 型一般版 bubble sort induction が Mathlib 側に存在)
した場合は **判断ログに #1 を起こし**、C-A-1 (alt (ii) 直接 induction) を撤回して `Tuple.*`
経路に乗り換える検討。0.4 が negative ヒット (= `Multiset.map_congr` 不在) なら Phase B0
構造補題を `Multiset.induction_on` で書き直す pivot 検討。

## Phase A — `swap_normalization_proof : SwapNormalizationHypothesis` 完全証明 📋

### Phase A1 — bubble sort metric + `swap_step_le` 再帰 loop (~80 行) 📋

inventory §B alt 候補 (ii) C-A-1 採用、bubble sort metric `swap_metric Q l` 上の
`Nat.strongRecOn'` で `swap_step_le` を再帰呼び。

- [ ] **A1.1** `swap_metric` の定義 (~5 行、上記 skeleton 通り).
- [ ] **A1.2** `swap_metric_strict_decrease` helper: bubble sort 不変式違反が残存する間、
  1 step swap で `swap_metric` が strict decrease (~30 行). `Equiv.swap a b` 経由で
  `l ∘ Equiv.swap a b` を作り、(a, b) ペアの reversion で metric が `-1` 減ることを示す.
  `Finset.card_lt_card` + `Finset.ssubset_iff_of_subset` で結語.
- [ ] **A1.3** `swap_normalization_aux_with_metric` (本 Phase の主役 induction):
  `Nat.strongRecOn'` で `swap_metric Q l_curr` 上に再帰、各 step で:
  - bubble sort 完了 (`swap_metric = 0`) なら現状 `l_curr` を返して termination.
  - 違反 (a', b') が残れば `swap_step_le Q l_curr a' b' h_violation` で
    `l_curr ↦ l_next` に更新、IH 適用.
  - 結語: 全ての (x, y) について `l_curr x > l_curr y → Q.real {x} > Q.real {y}`
    (bubble sort 不変式).
- [ ] **A1.4** `lake env lean` でこの時点まで silent 確認 (Phase A2 sorry 残許容).

**規模**: ~80 行 (`swap_metric` 5 + `swap_metric_strict_decrease` 30 + `swap_normalization_aux_with_metric` 45).

**fallback (A1 内部)**: `swap_metric_strict_decrease` の Finset filter card 比較で詰まる場合、
inventory §B `Tuple.bubble_sort_induction` + `Fintype.equivFin` bridge ~30 行追加 (撤退ライン
L-3 (b))。

### Phase A2 — shortening (Kraft = 1 で最長 codeword を 1 削減) (~70 行) 📋

A1 完了後、bubble sort 不変式は確立 ⇒ もし `Q.real {a}, Q.real {b}` が最小 2 element なら
最深 leaf ペアになるはず。ただし Kraft slack がある場合は **shortening** で
`huffmanLength_kraft_eq_one` 経由 Kraft = 1 化が必要。

- [ ] **A2.1** `strict_kraft_one_implies_pairing_lemma` 自作 (~40 行、inventory §F 自作要 §2):
  `l : β → ℕ`, `kraftSum 2 l = 1`, `l a < l b` で矛盾を導く. 最小 Kraft = 1 不変量から
  「最長 codeword に必ず pair が存在する」を Cover-Thomas 標準論法で示す.
- [ ] **A2.2** shortening 操作 + Kraft slack 吸収 (~20 行):
  - `shorten := Function.update l b (l b - 1)`.
  - Kraft slack 不等式: `1 - kraftSum 2 l ≥ 2^(-l b)` から `kraftSum 2 (shorten) ≤ 1`.
  - expected length 非増加: `P.real {b} * (l b - 1) - P.real {b} * l b = -P.real {b} ≤ 0`.
- [ ] **A2.3** A1 + A2.1 + A2.2 を `swap_normalization_aux` で合成 (~10 行):
  - A1 で bubble sort 完了.
  - Kraft = 1 なら A2.1 で `l a = l b`.
  - Kraft < 1 なら A2.2 で shorten 繰り返し ⇒ Kraft = 1 化 ⇒ A2.1 適用.
- [ ] **A2.4** `swap_normalization_proof : SwapNormalizationHypothesis.{u}` 結語 (1 行).
- [ ] **A2.5** `lake env lean` silent 確認.

**規模**: ~70 行.

**fallback (A2 内部)**: `strict_kraft_one_implies_pairing_lemma` が ~40 行で書けない場合
(Cover-Thomas 標準論法を Lean 上で展開するのに ~80 行必要が判明)、撤退ライン L-3 (a)
発動して「Kraft = 1 + bubble sort 完了で `l a = l b` を **公理仮定**」化、Phase A 単独で
H1 weak form 化、本 plan を L-4a (Phase A のみ publish) に縮退.

## Phase B — `huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis` 完全証明 📋

### Phase B0 — `initMultiset` lift 構造補題 (~50 行) 📋

inventory §F 「自作要」優先度 1。`initMultiset (mergedMeasure Q a b hab)` を
`initMultiset Q` から `Multiset.map (Subtype.val-lift)` + `erase b` + `update a` で書き換える等式。

- [ ] **B0.1** `initMultiset_mergedMeasure_lift_eq` の statement (~5 行):
  ```lean
  -- sketch
  lemma initMultiset_mergedMeasure_lift_eq
      (Q : Measure β) [IsProbabilityMeasure Q]
      (a b : β) (hab : a ≠ b) :
      initMultiset (mergedMeasure Q a b hab) =
        (initMultiset Q |>.erase ({b}, Q.real {b}) |>.erase ({a}, Q.real {a}))
        |> (Multiset.map (Subtype.val-lift)) |> Multiset.cons ...
  ```
  ※ 正確な右辺は実装時に Mathlib `Multiset.map` の signature を確認しつつ確定。
- [ ] **B0.2** 証明 (~40 行): `Multiset.map_map` + `Multiset.cons_erase` + `mergedMeasure_real`
  の `if-then-else` 展開 + `Subtype.val` image (`Finset.image_erase` を Multiset 版で reuse).
- [ ] **B0.3** `lake env lean` silent (Phase B1, B2 sorry 残許容).

**規模**: ~50 行.

### Phase B1 — `huffmanStep` 両側 correspondence + `Classical.choose` compatibility (~40 行) 📋

inventory §F 「自作要」優先度 1。両側の 1 step Huffman が `(a, b)` を pick up することを
`huffmanStep_initMultiset_sibling` (T1-A' 既存 private) + `Classical.choose` の両側 compatibility
で示す。

- [ ] **B1.1** `huffmanStep_initMultiset_sibling_equiv` の statement (~10 行):
  `huffmanStep (initMultiset Q) ...` で pick up された pair と、
  `huffmanStep (initMultiset (mergedMeasure Q a b hab)) ...` で pick up された pair が
  Subtype.val 経由で対応する.
- [ ] **B1.2** 証明 (~30 行): `huffmanStep_initMultiset_sibling` で両側の pick up pair が
  確定 (`a, b` の lift 像)、`Classical.choose` の `noncomputable` 性質を `Classical.choose_spec`
  + 一意性 lemma で吸収. **最大の落とし穴**: `Classical.choose` の compatibility が型をまたいで
  保証されないため、両側で「smallest 2」を **明示的に同じ予測値で取り出す** 計算を構成して
  `Classical.choose` の置き換え (or `huffmanStep_orig_decomp` 経由の構造補題 reuse) で迂回.

**規模**: ~40 行.

**fallback (B1 内部)**: `Classical.choose` compatibility が 5 ターン進まない場合、撤退ライン
L-2 発動して `mergedMeasure` 自体を再定義 (Subtype を使わず `α` 型不変経路、+500 行追加) を
検討。ただし context cost 高、L-4b (Phase B 単独 publish を諦め、Phase A のみ publish)
への撤退も並行検討.

### Phase B2 — `huffmanLengthAux` congr で H2 結語 (~80 行) 📋

inventory §F 「自作要」優先度 1。残り `Multiset` 上の strong induction で再帰呼び出しが
同 trajectory を辿ることを示し、point-wise の if-then-else 形に結語.

- [ ] **B2.1** `huffmanLength_mergedMeasure_eq_step_quotient` の statement (~10 行,
  T1-A' `HuffmanMergedIdentificationHypothesis` の中身 verbatim):
  ```lean
  lemma huffmanLength_mergedMeasure_eq_step_quotient
      {β : Type u} [...]
      (Q : Measure β) [IsProbabilityMeasure Q] (_hQ : ∀ a, 0 < Q.real {a})
      (_h_card : 3 ≤ Fintype.card β)
      (a b : β) (hab : a ≠ b)
      (_h_sibling : huffmanLength Q a = huffmanLength Q b)
      (x : { y : β // y ≠ b }) :
      huffmanLength (mergedMeasure Q a b hab) x
        = (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val)
  ```
- [ ] **B2.2** 場合分け `x.val = a` vs `x.val ≠ a`:
  - `x.val = a` ケース: 両側で `(a, b)` merge ⇒ `merged Q` 側で `a` は merge 後 codeword 長
    `huffmanLength Q a - 1`. `huffmanLengthAux_step_merged` (`Huffman.lean:614`) を両側で
    instantiation し、`b` の除外を `mem_erase_of_ne` で処理.
  - `x.val ≠ a` ケース: `huffmanLengthAux_step_other` (`Huffman.lean:625`) +
    `huffmanLengthAux_step_eq_on_other_group` (`Huffman.lean:636`) で再帰呼び出しの結果が
    両側で一致することを示す.
- [ ] **B2.3** `huffmanLengthAux` の strong induction (~40 行): B0 (initMultiset lift) +
  B1 (huffmanStep correspondence) を base step に当て、`s.card` 上の `Nat.strong_induction_on`
  generalizing で IH を回す. T1-A `huffmanLengthAux_const_on_group` の pattern を踏襲.
- [ ] **B2.4** `huffman_merged_identification_proof :
  HuffmanMergedIdentificationHypothesis.{u}` 結語 (1 行).
- [ ] **B2.5** `lake env lean` silent.

**規模**: ~80 行.

**fallback (B2 内部)**: strong induction の `Multiset` 型変化 (`α / α'` 両側で異なる
`Multiset (Finset _ × ℝ)`) が congr で接続できない場合、撤退ライン L-2 発動.

## Phase M — 強形主定理 `huffmanLength_optimal` (~3 行 wrapper) 📋

C-W-1 で確定済の 3 行 wrapper.

- [ ] **M.1** `huffmanLength_optimal` の statement + `huffmanLength_optimal_with_hypotheses`
  への delegation (上記 skeleton 通り).
- [ ] **M.2** `lake env lean` silent.

**規模**: ~3 行.

## Phase V — verify + regression 📋

- [ ] **V.1** `lake env lean Common2026/Shannon/HuffmanOptimality.lean` で 0 sorry / 0 error /
  最小 warning. 想定最終 ~1450 行.
- [ ] **V.2** regression check (既存 0-sorry ファイル):
  - `Common2026/Shannon/Huffman.lean` (961 行 / 0 sorry を維持).
  - `Common2026/Shannon/ShannonCode.lean`.
  - `Common2026/Shannon/ShannonCodeKraftReverse.lean`.
  - いずれも `lake env lean` silent.
- [ ] **V.3** `lake build Common2026` で全 silent (~1 回のみ、最終 sanity check).
- [ ] **V.4** `textbook-roadmap.md` Ch.5 行を 🟡 → 🟢 へ昇格 (T1-A'' 完遂で
  Cover-Thomas Theorem 5.8.1 完全 publish 達成、Ch.5 data compression 主役 3 件 publish 完了).

**規模**: 0 行 (verify のみ).

## 判定条件 (Definition of Done)

`lake env lean Common2026/Shannon/HuffmanOptimality.lean` が **0 sorry / 0 error / 最小 warning**
で pass、かつ以下が全て満たされる:

- [ ] `swap_normalization_proof : SwapNormalizationHypothesis.{u}` が publish.
- [ ] `huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis.{u}` が publish.
- [ ] `huffmanLength_optimal` (Cover-Thomas Theorem 5.8.1、引数 hypothesis なし強形) が publish.
- [ ] T1-A 既存 `Common2026/Shannon/Huffman.lean` は **不変** (961 行 / 0 sorry).
- [ ] T1-A' 既存 weak form `huffmanLength_optimal_with_hypotheses` は **不変** (signature/署名共に
  維持、本 plan の wrapper から呼び出される).
- [ ] 既存 `ShannonCode.lean` / `ShannonCodeKraftReverse.lean` に regression なし.
- [ ] `Common2026.lean` import 不変 (新規 file 追加なし).
- [ ] `textbook-roadmap.md` Ch.5 行 🟢 昇格.

**proof-log**: yes (各 Phase 完了時に `docs/shannon/proof-log-huffman-optimality-t1apprime.md`
へ追記。Phase A1/A2/B0/B1/B2/M ごとに 1 エントリ).

## 撤退ライン

inventory §G の §L-1 (= T1-A' で消化済) は無視。本 plan で active なのは L-2 / L-3 / L-4。

### L-2. Phase B `Classical.choose` compatibility が解決できない (mergedMeasure 再定義)

**発動条件**: Phase B1 で `huffmanStep_initMultiset_sibling_equiv` が **5 ターン進まない**
or B2 strong induction が `Multiset` 型変化で congr 接続不能と判明.

**対応**: `mergedMeasure` を再定義 — Subtype `{ y : β // y ≠ b }` を使わず、`β` 型不変
経路 (例: `Q'.real {x} := if x = b then 0 else if x = a then Q.real{a} + Q.real{b} else Q.real{x}`)
で書き直し、measure 0 atom が huffmanLength に影響しないことを別 lemma で示す. **規模 +500 行**.

**判断**: context cost 大、L-4 (scope 縮小) との二択を判断ログで明示する.

### L-3. Phase A2 shortening が成立しない (bubble sort + 強制成立)

**発動条件**: Phase A2 の `strict_kraft_one_implies_pairing_lemma` 自作が 5 ターン進まず
~80 行超過、shortening 操作 (`Function.update` + Kraft slack) でも `l a = l b` に到達不可と判明.

**対応 (a)**: shortening 諦め、bubble sort 完了で **`l a = l b` 公理仮定** 化、Phase A 単独で
H1 weak form 化 ⇒ L-4a (Phase A 部分 publish) に移行.

**対応 (b)**: `Tuple.bubble_sort_induction` (`Fin n → α` 限定) + `Fintype.equivFin` bridge
~30 行追加で alt 経路に乗り換え (C-A-1 撤回). Mathlib 既存 bubble sort 経路の termination が
Lean 上で素直に通る可能性に賭ける.

### L-4. Phase A or B 単独 publish への scope 縮小

T1-A'' 全体完遂が 1 セッション (~2-3 時間) で不可能と判明した場合の scope 縮小ライン。
T1-A' 判断ログ #7 と同じ「案 Y (weak form publish) で進捗を確実に取る」精神。

#### L-4a. Phase A のみ publish (推奨)

**発動条件**: Phase B (B0/B1/B2) が `Classical.choose` compatibility or `Multiset` 型変化で
本質的に詰まり、本 plan を 1 セッションで完遂不可能と判明.

**対応**:
- `swap_normalization_proof : SwapNormalizationHypothesis.{u}` のみ publish.
- `huffman_merged_identification_proof` は **引き続き hypothesis pass-through** (T1-A' のまま).
- 主定理は引数 1 つ削減版 `huffmanLength_optimal_with_ident_hypothesis` で publish:
  ```lean
  theorem huffmanLength_optimal_with_ident_hypothesis
      {α : Type*} [...]
      (h_ident : HuffmanMergedIdentificationHypothesis.{u})
      (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
      (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
      (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
      ... :=
    huffmanLength_optimal_with_hypotheses swap_normalization_proof h_ident
      P hP l hl_pos hl_kraft
  ```
- Cover-Thomas Theorem 5.8.1 への到達は (hypothesis 1 件減で) 部分進捗、Ch.5 完成判定は
  まだ 🟡 のまま。Phase B 単独で別 plan (`T1-A'''`) に切り出し.

#### L-4b. Phase B のみ publish

**発動条件**: Phase A (A1/A2) が `strict_kraft_one_implies_pairing_lemma` の Cover-Thomas
標準論法展開で詰まり、本 plan 1 セッション完遂不可能.

**対応**: L-4a と対称。`huffman_merged_identification_proof` のみ publish、
`swap_normalization_proof` は引き続き hypothesis. 主定理は
`huffmanLength_optimal_with_swap_hypothesis` で publish.

#### L-4c. 両 Phase publish 不可、Phase A 部分 publish (`card ≤ 3` 限定など)

**発動条件**: L-4a / L-4b いずれも本質的に詰まる場合の最終 fallback.

**対応**: Phase A `swap_normalization_proof` を `card β ≤ 3` 限定で publish (bubble sort
metric が常に 0 となる trivial case)、主定理は T1-A' weak form のまま (本 plan は新規
lemma 追加のみ). Cover-Thomas Theorem 5.8.1 への前進はゼロだが、`HuffmanOptimality.lean`
の Phase A 助走 helper を publish して T1-A''' (再着手) の基盤を整える.

## 規模見積もり / 想定ターン数

- 行数: **~400 行追記** (Phase A1 ~80 + A2 ~70 + B0 ~50 + B1 ~40 + B2 ~80 + M ~3 + 余裕 ~75).
- ターン数: **~8-12 ターン** (Phase 0 ×1, Phase A1 ×2, A2 ×2, B0 ×1, B1 ×2, B2 ×2, M ×1, V ×1).
- 想定実装時間: **1 セッション (~2-3 時間相当)** で完遂目標. Phase B (H2) が
  `Classical.choose` compatibility で詰まったら **L-4a 撤退ライン採用** (Phase A 単独 publish)
  を判断、その時点でも Cover-Thomas Theorem 5.8.1 への到達は (hypothesis 1 件減で) 進捗.

## Risk Table

| 番号 | リスク | 確率 | 影響 | 緩和策 |
|---|---|---|---|---|
| R-1 | Phase A1 bubble sort metric が `Equiv.swap` の Finset filter card 比較で詰まる | 低 | 中 | inventory §B alt (i) `Tuple.bubble_sort_induction` + `Fintype.equivFin` bridge ~30 行に切替 (L-3 (b)) |
| R-2 | Phase A2 shortening の Kraft slack 解析が `zpow_sub_one₀` cast 地獄で詰まる | 中 | 中 | T1-A' で `swap_step_le` Kraft 不変式の Kraft cast 経験あり、同 pattern 踏襲。L-3 (a) で weak 化 fallback |
| R-3 | Phase B1 `Classical.choose` compatibility が両側で取れない | 中 | 大 | inventory §F-1 「huffmanStep 構造補題で `Classical.choose` を明示計算で置き換え」path 推奨、L-2 で mergedMeasure 再定義 fallback、L-4a で Phase A 単独 publish に縮退 |
| R-4 | Phase B2 `huffmanLengthAux` strong induction の型変化 (α / α') が congr で接続不能 | 中 | 大 | T1-A' `huffmanLength_optimal_aux_with_hypotheses` で同様の `Fintype.card α = n` generalizing pattern 実証済、踏襲。最悪 L-2 で mergedMeasure 再定義 |
| R-5 | 全体時間 budget (~2-3 時間 = 1 セッション) を超過し、Phase A or B 単独 publish が必要 | 中 | 小 | L-4a / L-4b / L-4c で段階的 scope 縮小、いずれも T1-A' 進捗を維持しつつ部分 publish |
| R-6 | Phase A2 `strict_kraft_one_implies_pairing_lemma` が Cover-Thomas 標準論法を Lean 上で ~80 行超過 | 低 | 中 | L-3 (a) で shortening 諦め axiom 化、L-4a で Phase A 単独 publish |
| R-7 | T1-A' で確定済の `mergedMeasure` の `[Nonempty {y // y ≠ b}]` instance が `card β ≥ 3` 仮定下で Phase B0 lift 補題内で見えない | 低 | 小 | T1-A' Phase 3.1.3 `α'_nonempty` helper の re-use、必要なら同様の helper を Phase B0 内に追加 |

## 後続 seed への影響

T1-A'' 完了で `textbook-roadmap.md` Ch.5 行 🟢 昇格 (Cover-Thomas Theorem 5.8.1 完全
publish 達成、Ch.5 data compression 主役完成). 直接的な後続:

- **T3-E Separation Theorem** (Ch.5 + Ch.7 統合): Huffman の **強形最適性** を hypothesis
  なしで引用可能に. separation theorem の source coding 側完全完成扱い.
- **T4-A LZ78** (universal coding, Ch.13): 「prefix code 最適性 (Huffman, 強形) vs
  universal 漸近最適性 (LZ78)」の対比を教科書原稿で完全形で書ける.
- **教科書原稿 Ch.5**: Shannon code + Kraft + Huffman 三柱を 0-sorry リンクで書け、
  かつ Cover-Thomas Theorem 5.8.1 が **hypothesis 引数なし強形** で publish された状態.
  Ch.5 完成判定.

L-4 撤退発動時 (Phase A or B 単独 publish) は Ch.5 🟡 のまま、後継 seed T1-A''' で残り
hypothesis を discharge.

## 次セッション最初の一手

**Phase 0 在庫再確認 + Phase 1 skeleton を実装者 (lean-implementer) に引き渡し**:

> Phase 0 で inventory §B/§D の 1 行 probe (loogle 数件) を実施し、その結果を踏まえて
> `Common2026/Shannon/HuffmanOptimality.lean` 末尾 (line 1054 `end ...` 直前) に
> `/-! ### T1-A'' — 2 hypothesis discharge -/` セクションを追加。inventory §H verbatim
> skeleton (上記 §「File / module layout」内) を `:= by sorry` で立ち上げ、LSP silent
> (sorry warning のみ) を確認. その後 Phase A1 から 1 sorry ずつ skeleton-driven で埋める.

## 参考

- Parent roadmap: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''」
- Inventory: [`huffman-optimality-t1apprime-mathlib-inventory.md`](./huffman-optimality-t1apprime-mathlib-inventory.md)
- 直接前任 (T1-A' 完了): [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md)
- 先行 (T1-A 完了 archive): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md)
- 既存実装 (T1-A): `Common2026/Shannon/Huffman.lean` (961 行 / 0 sorry).
- 既存実装 (T1-A'): `Common2026/Shannon/HuffmanOptimality.lean` (1054 行 / 0 sorry, weak form).
- T1-A' 既存 API key 群 (`Common2026/Shannon/HuffmanOptimality.lean`):
  - `mergedMeasure`: `:244`
  - `mergedMeasure_real`: `:251`
  - `mergedMeasure_isProbabilityMeasure`: `:550`
  - `mergedMeasure_pos`: `:624`
  - `swap_step_le`: `:650`
  - `SwapNormalizationHypothesis`: `:759-773`
  - `HuffmanMergedIdentificationHypothesis`: `:776-785`
  - `huffmanLength_optimal_with_hypotheses`: `:1041`
  - `huffmanStep_initMultiset_sibling` (`private`): `:66`
- T1-A 既存 API key 群 (`Common2026/Shannon/Huffman.lean`):
  - `huffmanLength_kraft_eq_one`: `:924`
  - `huffmanLengthAux_step_merged`: `:614`
  - `huffmanLengthAux_step_other`: `:625`
  - `huffmanLengthAux_step_eq_on_other_group`: `:636`
  - `huffmanLengthAux_const_on_group`: `:467`
  - `huffmanStep_orig_decomp`: `:599`
- Mathlib path (inventory verbatim):
  - `Equiv.swap`: `Mathlib/Logic/Equiv/Basic.lean:634`
  - `Function.update`: `Mathlib/Logic/Function/Basic.lean:628`
  - `Tuple.bubble_sort_induction`: `Mathlib/Data/Fin/Tuple/BubbleSortInduction.lean:52`
  - `Finset.exists_max_image`: `Mathlib/Data/Finset/Max.lean:525`
  - `Finset.add_sum_erase`: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:741`
  - `zpow_sub_one₀`: `Mathlib/Algebra/GroupWithZero/Basic.lean:489`
  - `Multiset.map_congr`: `Mathlib/Data/Multiset/Basic.lean`
  - `Multiset.cons_erase`: `Mathlib/Data/Multiset/AddSub.lean:173`
  - `Nat.strong_induction_on`: `Mathlib/Data/Nat/Init.lean:281`
- Cover & Thomas *Elements of Information Theory* 2nd ed.,
  - **Lemma 5.8.1 (i)** (swap argument, normalize 最深 leaf to min-prob pair)
  - **Lemma 5.8.1 (ii)** (sibling property, 最深 leaf 兄弟も最深)
  - **Theorem 5.8.1** (Huffman optimality, n → n-1 induction)
- フォーマット参考: [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md),
  [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md).
- 雛形: [`moonshot-plan-template.md`](../moonshot-plan-template.md).

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-19 起草 — 設計判断の確定 (C-A-1 / C-A-2 / C-B-1 / C-W-1)**: inventory
   (`huffman-optimality-t1apprime-mathlib-inventory.md`) §B/§C/§D + §F「自作要」と T1-A' 完了形
   (`huffman-optimality-moonshot-plan.md` 判断ログ #6-#7) を受けて確定:
   - **C-A-1 (Phase A 経路)**: `Tuple.bubble_sort_induction` (`Fin n → α` 限定) を不採用、
     **bubble sort metric `swap_metric` + `Nat.strongRecOn'` 直接 induction** を採用. `Fin` bridge
     ~30 行を回避.
   - **C-A-2 (Phase A2 shortening)**: Kraft slack 吸収 + `Function.update` で最長 codeword を
     1 削減、`huffmanLength_kraft_eq_one` 経由 Kraft = 1 化で `l a = l b` 強制成立。
     `strict_kraft_one_implies_pairing_lemma` ~40 行自作.
   - **C-B-1 (Phase B identification 経路)**: 3 段分解 (B0 lift / B1 huffmanStep correspondence
     / B2 huffmanLengthAux congr)、合計 ~170 行. inventory §D の verbatim 再利用ライン.
   - **C-W-1 (wrapper)**: T1-A' `huffmanLength_optimal_with_hypotheses` の 3 行 delegation
     wrapper、universe `u` は T1-A' で確定済の `Type u` を踏襲.
   - **規模見積 ~400 行追記**: Phase A1 ~80 + A2 ~70 + B0 ~50 + B1 ~40 + B2 ~80 + M ~3 + 余裕 ~75.
     最終 `HuffmanOptimality.lean` ~1450 行 / 0 sorry / 0 warning 目標.
   - **撤退ライン**: L-2 (B `Classical.choose` 詰まり → mergedMeasure 再定義 +500 行) /
     L-3 (A2 shortening 詰まり → bubble sort + 強制成立 公理化) / L-4a/b/c (Phase A or B
     単独 publish への scope 縮小、T1-A' 判断ログ #7 案 Y 精神踏襲). 1 セッション完遂目標、
     詰まり時は **L-4a (Phase A 単独 publish)** を default 採用.

2. **2026-05-19 着手評価 — 案 Y (no-op) 採用、partial publish も見送り、技術メモを残す**:
   実装着手時の技術ボトルネック評価から、本セッションでは新規 publish を見送り
   (`HuffmanOptimality.lean` を T1-A' 状態のまま維持) し、次セッションへの引き継ぎ用
   メモを本判断ログに集約.

   #### Phase A1 — `swap_metric` 定義の方向性

   plan §C-A-1 の `swap_metric` 定義 `(ll p.1 > ll p.2 ∧ Q.real {p.1} ≤ Q.real {p.2})`
   は "long-codeword-at-low-prob" を数えるので **anti-correlation を満たす良好ペア**
   (= Cover-Thomas で sort 後の状態) を数える形であり、bubble sort 違反ではない (= sort
   が進むほど増える)。正しい violation metric は逆の組み合わせで、`ll p < ll q ∧ Q p < Q q`
   (= "small-prob-short-codeword") を数えるべき.

   さらに `swap_step_le` (`HuffmanOptimality.lean:650`、`l a ≤ l m` ∧ `Q.real {a} ≤ Q.real {m}`
   入力) は **violation `(p, q)` (`ll p < ll q ∧ Q{p} < Q{q}`) には `(a, m) := (p, q)` で
   そのまま適用可能** (両条件 ✓). `Equiv.swap p q` 後に `l'(p) = ll q, l'(q) = ll p` と
   なり、`E[l'] ≤ E[l]`.

   ただし **単純 violation count metric は単一 swap で strict decrease が保証できない**:
   swap 後に他の pair `(p, x), (x, p)` の violation 状態が ambiguous に変化するため.
   Mathlib `Tuple.bubble_sort_induction` の termination は lex ordering on
   `Equiv.Perm (Fin n)` を `WellFounded.induction_bot'` で induce している (`Pi.lex_desc`
   経由) — これが単純 metric を超える strict descent を与える本質.

   #### Phase A1 — `Tuple.bubble_sort_induction` 採用判断の再考価値

   plan §C-A-1 で `Fin n → α` bridge ~30 行を回避するため alt (ii) 直接 induction 採用
   としたが、上記の通り alt (ii) は単純 metric 上で技術的に成立しない見込み. 代案として:

   - (a) **`Tuple.bubble_sort_induction` + `Fintype.equivFin` bridge** (C-A-1 alt (i) に戻る):
     `f : Fin n → α` の `α` をペア `(ℕ × ℝ) := (ll, Q.real)` とし、`P` 述語を
     "対応する Kraft + E ≤ + positivity を満たす l_norm が存在" として lex ordering で
     induction. `Fin` ↔ `β` の bridge ~30 行は予想通りだが、bubble sort 本体は Mathlib
     で給付されるため Phase A1 全体は ~80-120 行で完結見込み.
   - (b) **直接 `WellFounded.induction_bot'` on `Equiv.Perm β`**: `Fin` bridge なし、
     `β` のままで lex 上 induction. ただし `Pi.lex` instance を `β → ℕ` で作る必要
     (Mathlib 既存は `Fin n` 限定). 工数 (a) と同程度 or 増. **(a) を推奨**.

   #### Phase A2 — shortening の技術的深さ

   `strict_kraft_one_implies_pairing_lemma` (Cover-Thomas "Kraft = 1 ⇒ complete tree
   ⇒ 最長 codeword に pair 存在") は Lean で展開するには full binary tree 構造の formal
   化が必要だが、Common2026 / Mathlib に該当 API なし. 代替は kraft sum identity の
   精密 case split で構築できる見込み (`l a < l b` ∧ Kraft = 1 ⇒ ∑ 2^(-l) > 1 矛盾) が、
   ~40 行 (plan 見積) は楽観的、実際は ~80 行見込み.

   #### Phase B0/B1/B2 — Multiset 型 bridging の深さ

   `initMultiset (mergedMeasure Q a b hab) : Multiset (Finset {y // y ≠ b} × ℝ)` と
   `initMultiset Q : Multiset (Finset β × ℝ)` の **型不一致**は、`Subtype.val`-lift の
   Multiset.map で formal 化可能だが、`Multiset.map_congr` 経由でも単純な `congr`/`rfl`
   では通らない。Phase B0 ~80 行 (plan 50 行から +60%), Phase B1 の `Classical.choose`
   両側 compatibility ~80 行 (plan 40 行から +100%), Phase B2 strong induction での
   `α / {y // y ≠ b}` congr ~150 行 (plan 80 行から +88%) が現実的見積.

   #### 総合判断 — 案 Y (= no-op) を採用

   - **規模**: Phase A 完成 ~250 行 + Phase B 完成 ~300 行 = **~550 行** (plan 見積 +37%).
     **1 セッション完遂は不可能** (推定 4-6 セッション + proof-pivot-advisor 2-3 回).
   - **L-4 系 partial publish**: いずれも Phase A or B 単独完成を要求するが、上記から
     Phase A 単独でも ~250 行で本セッション内完遂は困難。partial sorry を残した publish は
     Definition of Done 違反のため不可.
   - **採用方針 (案 Y, T1-A' 案 Y の精神踏襲)**: `HuffmanOptimality.lean` を T1-A' 完成形
     (1054 行 / 0 sorry / weak form `huffmanLength_optimal_with_hypotheses` publish 済)
     のまま **unchanged 維持**. 本 plan は実装着手を見送り、次セッションへの引き継ぎ用
     メモ (本判断ログ #2) のみ記録.

   #### 次セッション最初の一手 (本判断ログ #2 から派生)

   本 plan §「次セッション最初の一手」の skeleton 起動方針は維持しつつ、Phase A1 の
   **採用経路を C-A-1 alt (ii) 直接 induction → C-A-1 alt (i) `Tuple.bubble_sort_induction`
   + `Fintype.equivFin` bridge** に切替検討. proof-pivot-advisor を 1 回投入し、(a)
   Phase A1 の bubble sort induction 経路最終確定 と (b) Phase B0 の Multiset Subtype-lift
   structural lemma の signature 確定 を 1 ターンで行うのが現実的.

   **Definition of Done 状態**: 既存 `lake env lean Common2026/Shannon/HuffmanOptimality.lean`
   は silent (0 sorry / 0 error / 既存 warning なし、T1-A' 状態完全維持)。T1-A'' 進捗
   チェックボックスは全て unchecked のまま、後続セッションで再着手.

3. **2026-05-19 再着手評価 #2 — 案 Y 再採用、no-op 維持**: 判断ログ #2 以後の Mathlib 状態と
   `HuffmanOptimality.lean` (1054 行 / 0 sorry / weak form publish) は不変であることを Phase 0
   1 行 probe で再確認:
   - `loogle "Tuple.bubble_sort_induction"`: `Mathlib.Data.Fin.Tuple.BubbleSortInduction` ヒット
     1 件、依然 `Fin n → α` 専用 (Fintype 一般化 API は不在). C-A-1 alt (i) `Fintype.equivFin`
     bridge ~30 行が依然必要。
   - `loogle "Multiset.map_congr"`: `Mathlib.Data.Multiset.MapFold` ヒット 1 件、署名不変.
     Phase B0 lift 構造補題は依然 ~80 行見込み (判断ログ #2 から不変).

   判断ログ #2 の技術ボトルネック評価 (Phase A 完成 ~250 + Phase B 完成 ~300 = ~550 行、
   推定 4-6 セッション + proof-pivot-advisor 2-3 回) は **本セッション着手判断時点でも全く
   同一**。新たに利用可能になった Mathlib API も、scope を下げる新発見もなく、partial sorry
   publish は依然 DoD 違反のため不可。L-4a (Phase A 単独 publish) も Phase A 単独で ~250 行
   要するため 1 セッション完遂不可。

   **採用方針**: 案 Y (no-op) **再採用**。`HuffmanOptimality.lean` は T1-A' 完成形のまま
   unchanged 維持、本判断ログ #3 のみ追記。Phase 0 1 行 probe 2 件以外の API call なし。

   #### 次セッション最初の一手 (本判断ログ #3 から派生、判断ログ #2 と重複部は省略)

   T1-A'' は 1 セッション完遂前提では着手不可。**~2-3 セッション分の連続実装 budget が
   確保された場合に再着手**を推奨。budget 確保が困難なら、ロードマップ全体で T1-A'' の
   優先度を見直し、別 seed (T2-G, T3-E など) を先行させる選択肢も検討。再着手時は判断ログ
   #2 の skeleton 起動方針 (Phase A1 `Tuple.bubble_sort_induction` + `Fintype.equivFin`
   bridge 採用 + proof-pivot-advisor 1 回投入で Phase A1 / Phase B0 signature 確定) を踏襲.

   **Definition of Done 状態**: 既存 `Common2026/Shannon/HuffmanOptimality.lean` は不変
   (1054 行 / 0 sorry / weak form publish)。`lake env lean` 再実行は不要 (T1-A' 完成形
   をそのまま維持). T1-A'' 進捗チェックボックスは全 unchecked.
