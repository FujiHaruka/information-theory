# T1-A'' Huffman Optimality Strong Form — Mathlib + InformationTheory API Inventory

> Parent: `docs/textbook-roadmap.md` § Tier 1 — **T1-A''. Huffman optimality (full discharge of 2 weak-form hypotheses)**
> Predecessor: `docs/shannon/huffman-optimality-mathlib-inventory.md` (T1-A' inventory, ~440 行)
> Existing artefact: `InformationTheory/Shannon/HuffmanOptimality.lean` (1054 行 / 0 sorry / weak form publish), `InformationTheory/Shannon/Huffman.lean` (961 行 / 0 sorry)
> Goal: discharge `SwapNormalizationHypothesis` (`HuffmanOptimality.lean:759`) and `HuffmanMergedIdentificationHypothesis` (`HuffmanOptimality.lean:776`), then expose strong form `huffmanLength_optimal` (no hypothesis args).
> Note: APIs already cataloged in the T1-A and T1-A' inventories are **not re-listed** unless their role specifically changes in T1-A''.

---

## 一行サマリ

**T1-A'' で discharge する 2 hypothesis のうち Hypothesis 1 (SwapNormalization) は Mathlib 既存 API ~95% でカバー可、Hypothesis 2 (Identification) は InformationTheory 既存補題 (`huffmanLengthAux_step_merged` / `_step_other` / `_const_on_group`) ~85% でカバー可。新規に必要な API はすべて既存 (`Equiv.swap` + `Function.update` + `Tuple.bubble_sort_induction` + `huffmanLength_kraft_eq_one` + `swap_step_le`)。自前構築が必要なのは "shortening 操作" (Kraft = 1 のとき最長 codeword を 1 減らす変形 — Mathlib 不在、自前 ~40 行) と "`mergedMeasure ↔ initMultiset` の構造的同値" (1 step Huffman の identification — 自前 ~150 行)。撤退ラインは発動しない見込み。**最大の発見 (危険度高)**: `Tuple.bubble_sort_induction` は `Fin n → α` 専用、我々の `l : α → ℕ` (任意 `α : Type*` with `[Fintype α]`) に直接適用するには `Fintype.equivFin` 経由の **抽象 ↔ Fin** bridge ~30 行が必要。代案: bubble sort を使わず、**2-step swap を `(l a, l b)` を arg-pair で sort できるまで再帰** する直接 induction (~50 行)。

---

## 主定理の最終形 (T1-A'' で publish 予定)

```lean
/-- **Cover-Thomas Theorem 5.8.1 (strong form)** — argument hypothesis なし。 -/
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
```

---

## §A. T1-A' 既存資産 (T1-A'' で直接 reuse)

| name | file:line | role |
| --- | --- | --- |
| `swap_step_le` | `InformationTheory/Shannon/HuffmanOptimality.lean:650` | H1 main step。 (a, m) = (min-prob symbol, current longest position) で順次呼ぶ |
| `mergedMeasure` | `InformationTheory/Shannon/HuffmanOptimality.lean:244` | H2 LHS の measure |
| `mergedMeasure_real` | `InformationTheory/Shannon/HuffmanOptimality.lean:251` | H2 各 group の確率値 |
| `mergedMeasure_isProbabilityMeasure` | `InformationTheory/Shannon/HuffmanOptimality.lean:550` | H2 [IsProbabilityMeasure] |
| `mergedMeasure_pos` | `InformationTheory/Shannon/HuffmanOptimality.lean:624` | H2 huffmanLength_pos 前提 |
| `SwapNormalizationHypothesis` | `InformationTheory/Shannon/HuffmanOptimality.lean:759-773` | **discharge 対象** (H1) |
| `HuffmanMergedIdentificationHypothesis` | `InformationTheory/Shannon/HuffmanOptimality.lean:776-785` | **discharge 対象** (H2) |
| `huffmanLength_optimal_with_hypotheses` | `InformationTheory/Shannon/HuffmanOptimality.lean:1041` | 主定理 entry。両 hypothesis を渡して強形を得る |
| `huffmanLength_kraft_eq_one` | `InformationTheory/Shannon/Huffman.lean:924` | H1 Kraft = 1 contradiction |
| `huffmanStep_initMultiset_sibling` (`private`) | `InformationTheory/Shannon/HuffmanOptimality.lean:66` | H2 で `(a, b)` が huffmanStep pick up された pair であることの identification |

---

## §B. T1-A'' Hypothesis 1 (SwapNormalization) discharge — bubble sort 経路

**alt 候補 (i)**: `Tuple.bubble_sort_induction` (`Mathlib/Data/Fin/Tuple/BubbleSortInduction.lean:52`)。
**alt 候補 (ii) — 推奨**: bubble sort metric `∑ indicator(l i > l j ∧ P i ≤ P j)` 上の `Nat.strongRecOn'` で `swap_step_le` を直接再帰呼び。`Fin` bridge 不要、~150 行で完結。

主要 Mathlib API:

| name | file:line | signature |
| --- | --- | --- |
| `Tuple.bubble_sort_induction` | `Mathlib/Data/Fin/Tuple/BubbleSortInduction.lean:52` | `theorem bubble_sort_induction {n : ℕ} {α : Type*} [LinearOrder α] {f : Fin n → α} {P : (Fin n → α) → Prop} (hf : P f) (h : ∀ (g : Fin n → α) (i j : Fin n), i < j → g j < g i → P g → P (g ∘ Equiv.swap i j)) : P (f ∘ sort f)` |
| `Equiv.swap` | `Mathlib/Logic/Equiv/Basic.lean:634` | `def swap (a b : α) : Perm α` (`[DecidableEq α]`) |
| `Equiv.swap_apply_left/right/of_ne_of_ne/self` | `Mathlib/Logic/Equiv/Basic.lean:650/654/657/639` | basic facts |
| `Equiv.sum_comp` | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:730` | sum invariance under equiv |
| `Fintype.equivFin` | `Mathlib/Data/Fintype/EquivFin.lean` (要確認) | `noncomputable def : α ≃ Fin (Fintype.card α)` (`[Fintype α]` only) |
| `Function.update` / `update_self` / `update_of_ne` / `update_apply` / `update_idem` / `update_comm` | `Mathlib/Logic/Function/Basic.lean:628/632/636/640/764/759` | shortening の Function.update |
| `Finset.exists_max_image` | `Mathlib/Data/Finset/Max.lean:525` | longest codeword 位置の取り出し |
| `Finset.exists_min_image` | `Mathlib/Data/Finset/Max.lean:531` | T1-A' 既出 |
| `Finset.add_sum_erase` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:741` | shortening の Kraft 解析 |
| `Finset.sum_erase_add` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:747` | 同上 |
| `Finset.sum_subtype` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:462` | T1-A' 既使用 |
| `Finset.sum_le_sum` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:108` | reuse |
| `Finset.sum_lt_sum` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:453` | Kraft strict inequality |
| `Finset.sum_le_sum_of_subset_of_nonneg` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:131` | reuse |
| `zpow_add₀` / `zpow_sub_one₀` | `Mathlib/Algebra/GroupWithZero/Basic.lean:494/489` | `2^(-(l-1)) = 2·2^(-l)` |
| `zpow_pos` | `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:958` | Kraft sum > 0 |
| `Nat.strong_induction_on` | `Mathlib/Data/Nat/Init.lean:281` | T1-A' 既使用 |

---

## §C. T1-A'' Hypothesis 1 (Shortening 段) — Kraft = 1 の場合の縮退

bubble sort 終了後、`l a ≠ l b` のときの shortening が必要。**Kraft slack の活用**。

| name | file:line | role |
| --- | --- | --- |
| `huffmanLength_kraft_eq_one` | `InformationTheory/Shannon/Huffman.lean:924` | H1 内で `ll = huffmanLength` のとき `l a = l b` 自動成立、一般 `ll` 側で slack 活用 |
| `Function.update_apply` | `Mathlib/Logic/Function/Basic.lean:640` | shortening 後の各 `l' x` の値計算 |
| `Function.update_idem` | `Mathlib/Logic/Function/Basic.lean:764` | 複数回 shortening の合成 |
| `Function.update_comm` | `Mathlib/Logic/Function/Basic.lean:759` | reuse |

**自前で必要**: `shortening_step` lemma — Kraft slack が `2^(-l a) - 2^(-(l a - 1))` を吸収できれば shortening 後も Kraft-feasible。スラック条件は `huffmanLength_kraft_eq_one` 相当の "Kraft = 1 ⇒ complete tree" を `l` 側に必要、Mathlib 不在、自前 ~40 行。

---

## §D. T1-A'' Hypothesis 2 (Identification) discharge — `mergedMeasure ↔ huffmanStep` 構造

最大の難所。`initMultiset (mergedMeasure Q a b hab) : Multiset (Finset { y // y ≠ b } × ℝ)` vs `(huffmanStep (initMultiset Q) ...).val.2.2 : Multiset (Finset α × ℝ)` — **型が異なる**。

| name | file:line | role |
| --- | --- | --- |
| `initMultiset` | `InformationTheory/Shannon/Huffman.lean:298` | `Multiset (Finset α × ℝ)`. 両側で計算 |
| `initMultiset_huffmanGrouping` | `InformationTheory/Shannon/Huffman.lean:416` | HuffmanGrouping 保存 |
| `huffmanStep_card_eq` | `InformationTheory/Shannon/Huffman.lean:251` | cardinality bridge |
| `huffmanLengthAux_step_merged` | `InformationTheory/Shannon/Huffman.lean:614` | **本命**: `a ∈ merged` のとき +1 |
| `huffmanLengthAux_step_other` | `InformationTheory/Shannon/Huffman.lean:625` | **本命**: `a ∉ merged` のとき不変 |
| `huffmanLengthAux_step_eq_on_other_group` | `InformationTheory/Shannon/Huffman.lean:636` | other group 上で `s` と `s''` 値一致 |
| `huffmanLengthAux_const_on_group` | `InformationTheory/Shannon/Huffman.lean:467` | **本命** |
| `huffmanStep_orig_decomp` | `InformationTheory/Shannon/Huffman.lean:599` | `s = x1 ::ₘ x2 ::ₘ ee` |
| `huffmanStep_initMultiset_sibling` | `InformationTheory/Shannon/HuffmanOptimality.lean:66` | `(a, b)` が huffmanStep pick up された pair |

**Mathlib 側**:

| name | file:line | role |
| --- | --- | --- |
| `Multiset.map` | (Mathlib/Data/Multiset/Basic.lean) | `Subtype-lift` で `α' → α` lift |
| `Multiset.map_map` | 同 | map 合成 |
| `Multiset.map_congr` | 同 | reuse |
| `Multiset.cons_erase` | `Mathlib/Data/Multiset/AddSub.lean:173` | T1-A 既使用 |
| `Multiset.mem_erase_of_ne` | `Mathlib/Data/Multiset/AddSub.lean:218` | reuse |
| `Multiset.card_erase_of_mem` | `Mathlib/Data/Multiset/AddSub.lean:239` | reuse |
| `Multiset.mem_of_mem_erase` | `Mathlib/Data/Multiset/AddSub.lean:221` | reuse |
| `Multiset.exists_min_image` | `Mathlib/Data/Finset/Max.lean:567` | `Classical.choose` 元の min property |
| `Multiset.strongInductionOn` | `Mathlib/Data/Multiset/Basic.lean:72` | (alt) |
| `Finset.image_erase` | (T1-A' inv §E-i 既載) | `Subtype.val` image |

**自前で必要** (Identification の核):

| 優先度 | 名前 | 推奨実装 | 工数感 | 落とし穴 |
| --- | --- | --- | --- | --- |
| 1 | `initMultiset_mergedMeasure_eq` | `α' → α` lift の Multiset 構造補題 | ~50 行 | `Subtype.val` image が `Finset.univ.erase b`, `mergedMeasure_real` で `{a}` 位置 +Q.real{b} |
| 1 | `huffmanStep_initMultiset_sibling_equiv` | huffmanStep が両側で対応する pair を選ぶ | ~40 行 | `Classical.choose` compatibility |
| 1 | `huffmanLength_mergedMeasure_eq_step_quotient` | H2 主等式 | ~80 行 | `huffmanLengthAux` の `α/α'` 型変化を congr、strong induction の base を揃える |

**規模**: 50 + 40 + 80 = **~170 行** + reuse ~30 行 = **~200 行**.

---

## §E. 主要前提条件ボックス

- `swap_step_le` (`HuffmanOptimality.lean:650`): `omit [Nonempty α] [MeasurableSingletonClass α]`. `[MeasurableSpace α]` のみ要求.
- `huffmanLength_kraft_eq_one`: `omit [MeasurableSingletonClass α]`. `[Fintype/DecidableEq/Nonempty/MeasurableSpace] + [IsProbabilityMeasure]`.
- `mergedMeasure`: `[Fintype/DecidableEq/Nonempty/MeasurableSpace/MeasurableSingletonClass]`. `{ y // y ≠ b }` 側に type class auto-derive で OK (T1-A' Phase 0 確認済).
- `Tuple.bubble_sort_induction`: `f : Fin n → α` 限定 — `α` 型のままでは不可、`Fintype.equivFin` bridge ~30 行 or alt (直接 induction) 推奨.
- `Equiv.swap` / `Function.update`: `[DecidableEq α]`.
- `huffmanLengthAux` termination は `s.card`. `initMultiset Q` (card = n) と `initMultiset (mergedMeasure Q a b hab)` (card = n - 1) で 1 違うが、`Nat.strong_induction_on n` with `hn : Fintype.card α = n` generalizing pattern で揃う (T1-A' `huffmanLength_optimal_aux_with_hypotheses:793` と同 pattern).

---

## §F. 自作が必要な要素 (T1-A'' 全体)

| 優先度 | 名前 | 推奨実装 | 工数感 | 落とし穴 |
| --- | --- | --- | --- | --- |
| 1 | `swap_normalization_proof : SwapNormalizationHypothesis` | metric 上 `Nat.strongRecOn'` で `swap_step_le` 再帰 + shortening | ~150 行 | metric strict decrease ~30, shortening Kraft 解析 ~40, "Kraft = 1 ⇒ complete tree" を `l` 側に複製 (ShannonCodeKraftReverse 既存 lemma 活用検討) |
| 1 | `huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis` | Multiset.map (Subtype-lift) 構造補題 + `huffmanStep` 対応 congr | ~200 行 | `Classical.choose` 両側 compatibility ~50, `huffmanLengthAux` strong induction base bridge ~30 |
| 2 | `strict_kraft_one_implies_pairing_lemma` (H1 shortening 用) | `l : α → ℕ`, Kraft = 1, `l a < l b` ⇒ 矛盾 | ~40 行 | Mathlib 不在、自前 |
| 3 | `huffmanLength_optimal` (T1-A'' 主定理 強形) | wrapper, 3 行 | ~3 行 | trivial |

**合計**: 150 + 200 + 40 + 3 = **~400 行**. 既存 1054 行 + 400 ~ **1450 行 / 0 sorry** 目標.

---

## §G. 撤退ラインへの距離

- **L-1**: T1-A' で消化 (hypothesis pass-through 採用).
- **L-2 (T1-A'' 新規)**: H2 構造補題が書けない場合 mergedMeasure 再定義 (Subtype 不使用、α 型不変経路) → +500 行. **発動リスク中** — `Classical.choose` compatibility が最大の不確実性.
- **L-3 (T1-A'' 新規)**: "Kraft = 1 ⇒ complete tree" を `l` 側に複製不可なら、shortening 諦め bubble sort + `l a = l b` 強制成立 ~80 行追加. **発動リスク低**.

→ 全体として **T1-A'' は計画通り完遂可能** 見込み。

---

## §H. 着手 skeleton

`InformationTheory/Shannon/HuffmanOptimality.lean` 末尾 (現 1054 行) に追記推奨。新規 file 不要、同 namespace 内で完結。

```lean
/-! ### T1-A'' — 2 hypothesis discharge -/

private noncomputable def swap_metric (P : Measure α) [IsProbabilityMeasure P] (l : α → ℕ) : ℕ :=
  ((Finset.univ : Finset (α × α)).filter
    (fun p => l p.1 > l p.2 ∧ P.real {p.1} ≤ P.real {p.2})).card

private theorem swap_normalization_proof_aux ... := by sorry  -- Phase A1+A2

theorem swap_normalization_proof : SwapNormalizationHypothesis.{u} := swap_normalization_proof_aux

private lemma initMultiset_mergedMeasure_lift_eq ... := by sorry  -- Phase B0

private theorem huffman_merged_identification_proof_aux ... := by sorry  -- Phase B1+B2

theorem huffman_merged_identification_proof : HuffmanMergedIdentificationHypothesis.{u} := huffman_merged_identification_proof_aux

theorem huffmanLength_optimal ... :=
  huffmanLength_optimal_with_hypotheses
    swap_normalization_proof huffman_merged_identification_proof
    P hP l hl_pos hl_kraft
```
