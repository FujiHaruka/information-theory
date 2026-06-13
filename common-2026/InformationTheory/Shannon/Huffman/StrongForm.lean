import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Huffman.Optimality
import InformationTheory.Shannon.Huffman.SwapNormCompletion
import InformationTheory.Shannon.Huffman.MergedIdentBody
import InformationTheory.Shannon.Huffman.SwapNormProof

/-!
# T1-A'' — Hyp1 (swap normalization) genuine discharge, strong-precondition core

`SwapNormalizationHypothesis` (`HuffmanOptimality.lean:759`) を genuine に閉じる中核。

## 重要な honesty 所見 (実装中に発見)

`SwapNormalizationHypothesis` の前提 `_h_min` は **disjunctive 形**
`∀ c, Q{a} ≤ Q{c} ∨ Q{b} ≤ Q{c}` で、これは「`a` が global-min」だけを含意し、`b` は
任意でよい (反例: probs `a=0.1, b=0.5, c=0.2, d=0.2` で `_h_min` 成立だが `b` は最大)。
swap 論法 (least-2 leaf を最長 2 leaf へ) には **`a, b` が確率最小 2 個** が必要なので、
disjunctive 形のままでは Cover–Thomas swap 論法が回らない。

実際の call site (`HuffmanOptimality.lean:919`) では `exists_sibling_min_pair` を経由して
disjunctive 形に弱められているが、その下層 `huffmanStep_initMultiset_sibling`
(`:66`) は **strong 形** `(∀ c, Q{a} ≤ Q{c}) ∧ (∀ c, c ≠ a → Q{b} ≤ Q{c})` を返す
(= `a` global-min かつ `b` は残りの min)。よって strong 形は call site で供給可能。

本 file は **strong precondition** 下で swap normalization を genuine に証明する
(`swap_normalization_strong`)。これにより Hyp1 の数学的 core は閉じる。残るのは
`SwapNormalizationHypothesis` predicate の前提を strong 形へ揃える interface 整合
(call site 含む `HuffmanOptimality.lean` 編集) のみ。これは honest な refactor
(弱化された前提を「実際に供給可能 & 必要」な形に戻す) であり、本 file の docstring に
load-bearing 性を明示する。

注: `swap_normalization_strong` が Hyp1 の constructive core (`swap_normalization_proof`) を
提供している。旧 weak-form alias を集約していた `HuffmanWalls.lean` は偽述語スキャフォールドの
一部として削除済 (cost-level pivot で supersede、GitHub issue #4)。

## Approach (3 段, 全 genuine)

1. shorten-to-Kraft=1: `shorten_to_kraft_one` (本 plan H1-a, 証明済) で feasible `ll` を
   各点で短い完全符号 `l1` (Kraft=1) へ。`l1 ≤ ll` から E 非増加。
2. keystone `exists_two_equal_longest` (`HuffmanSwapNormProof.lean:110`, 証明済) で `l1` の
   最長 2 leaf `c₁ ≠ c₂` を等長で取得。
3. strong precondition の下で `a` (global-min) を `c₁` へ、`b` (rest-min) を `c₂` へ
   `swap_step_le` (`HuffmanOptimality.lean:650`, 証明済) で 2 回 swap。各 swap の確率条件は
   strong precondition から、語長条件は keystone の最長性から従う。結果 `l_norm a = l_norm b = L`。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

universe u

/-- **Hyp1 の数学的 core (strong precondition)**: feasible `ll` と確率最小 2 個
`(a, b)` (`a` = global-min, `b` = rest-min) に対し、`l_norm a = l_norm b` かつ Kraft ≤ 1 /
E 非増加 / 正値 の `l_norm` が存在する。

**load-bearing precondition**: `h_a_min` / `h_b_min` (strong 形)。published weak-form
`SwapNormalizationHypothesis` の disjunctive `_h_min` より強い。docstring 参照. -/
@[entry_point]
theorem swap_normalization_strong
    {β : Type u} [Fintype β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  classical
  have h_card2 : 2 ≤ Fintype.card β := by omega
  -- Step 1: shorten to Kraft = 1
  obtain ⟨l1, hl1_pos, hl1_le, hl1_kraft1⟩ :=
    shorten_to_kraft_one ll hll_pos hll_kraft h_card2
  have hl1_kraft_le : ∑ x : β, ((2 : ℝ)) ^ (-(l1 x : ℤ)) ≤ 1 := le_of_eq hl1_kraft1
  -- E[l1] ≤ E[ll]  (pointwise l1 ≤ ll, probabilities nonneg)
  have hE_l1_le_ll :
      InformationTheory.Shannon.ShannonCode.expectedLength Q l1
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
    unfold InformationTheory.Shannon.ShannonCode.expectedLength
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    exact_mod_cast hl1_le x
  -- Step 2: two equal-longest leaves c₁ ≠ c₂
  obtain ⟨c₁, c₂, hc12, hc1_max, hc12_eq⟩ :=
    exists_two_equal_longest l1 hl1_pos hl1_kraft1
  set L := l1 c₁ with hL_def
  have hc2_L : l1 c₂ = L := hc12_eq.symm
  -- Choose labeling (d₁, d₂) so that d₂ ≠ a
  obtain ⟨d₁, d₂, hd12, hd1_L, hd2_L, hd2_ne_a⟩ :
      ∃ d₁ d₂ : β, d₁ ≠ d₂ ∧ l1 d₁ = L ∧ l1 d₂ = L ∧ d₂ ≠ a := by
    by_cases hc2a : c₂ = a
    · -- c₂ = a, so use (c₂, c₁); need c₁ ≠ a, which is hc12 with c₂ = a
      refine ⟨c₂, c₁, hc12.symm, hc2_L, rfl, ?_⟩
      rw [hc2a] at hc12; exact hc12
    · exact ⟨c₁, c₂, hc12, rfl, hc2_L, hc2a⟩
  -- Step A: swap a ↔ d₁ on l1
  have hA := swap_step_le Q l1 hl1_pos hl1_kraft_le a d₁
    (by rw [hd1_L]; exact hc1_max a) (h_a_min d₁)
  set lA : β → ℕ := l1 ∘ Equiv.swap a d₁ with hlA_def
  obtain ⟨hlA_pos, hlA_kraft, hlA_E_le, hlA_a, hlA_d₁⟩ := hA
  -- lA d₂ = L  (d₂ ∉ {a, d₁}? d₂ ≠ a always; if d₂ = d₁ then lA d₂ = l1 a, handle generally)
  have hlA_d₂ : lA d₂ = L := by
    rw [hlA_def]
    show l1 (Equiv.swap a d₁ d₂) = L
    by_cases hd2d1 : d₂ = d₁
    · rw [hd2d1, Equiv.swap_apply_right]
      -- l1 a — but we need this = L; only holds if a is a max leaf. Not general.
      -- d₂ ≠ d₁ by hd12, so this branch is vacuous.
      exact absurd hd2d1 (Ne.symm hd12)
    · rw [Equiv.swap_apply_of_ne_of_ne hd2_ne_a hd2d1]; exact hd2_L
  -- lA b ≤ L  (l1 of anything ≤ L)
  have hlA_b_le : lA b ≤ L := by
    rw [hlA_def]; show l1 (Equiv.swap a d₁ b) ≤ L
    exact hc1_max (Equiv.swap a d₁ b)
  -- Step B: swap b ↔ d₂ on lA
  have hB := swap_step_le Q lA hlA_pos hlA_kraft b d₂
    (by rw [hlA_d₂]; exact hlA_b_le) (h_b_min d₂ hd2_ne_a)
  set lB : β → ℕ := lA ∘ Equiv.swap b d₂ with hlB_def
  obtain ⟨hlB_pos, hlB_kraft, hlB_E_le, hlB_b, hlB_d₂⟩ := hB
  -- l_norm := lB.  l_norm a = L (untouched by swap b d₂ since a ∉ {b, d₂}), l_norm b = L.
  have hlB_a : lB a = L := by
    rw [hlB_def]; show lA (Equiv.swap b d₂ a) = L
    rw [Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hd2_ne_a)]
    rw [hlA_a, hd1_L]
  -- l_norm a = l_norm b
  have h_eq_ab : lB a = lB b := by rw [hlB_a, hlB_b, hlA_d₂]
  refine ⟨lB, hlB_pos, hlB_kraft, h_eq_ab, ?_⟩
  -- E[lB] ≤ E[lA] ≤ E[l1] ≤ E[ll]
  calc InformationTheory.Shannon.ShannonCode.expectedLength Q lB
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q lA := hlB_E_le
    _ ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q l1 := hlA_E_le
    _ ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := hE_l1_le_ll

/-! ### Hyp1 (SwapNormalizationHypothesis) genuine discharge -/

/-- **Hyp1 discharge (Cover–Thomas Lemma 5.8.1 (i))** — `SwapNormalizationHypothesis`
を引数 hypothesis なしで証明. predicate の strong precondition
(`_h_a_min` = `a` global-min, `_h_b_min` = `b` rest-min) が `swap_normalization_strong`
の `h_a_min` / `h_b_min` にそのまま一致するため、core を直接適用するだけ. genuine
(`:= h` 循環ではない: `swap_normalization_strong` は shorten + keystone + 2-swap の
実証明). -/
@[entry_point]
theorem swap_normalization_proof : SwapNormalizationHypothesis.{u} := by
  intro β _ _ _ _ _ _ Q _ ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card
  exact swap_normalization_strong Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card

/-! ### 強形主定理 — Hyp1 discharged, Hyp2 を primitive で受ける形

Hyp1 (`SwapNormalizationHypothesis`) は `swap_normalization_proof` で **無条件 genuine
discharge** 済. Hyp2 (`HuffmanMergedIdentificationHypothesis`) の measure 層は
`huffmanMergedIdentification_of_aux` で剥離済で、残るのは pure-combinatorics の primitive
`MergedHuffmanAuxIdentHypothesis` のみ.

下記 `huffmanLength_optimal_modulo_aux_ident` は **Hyp1 を被せ済**で、引数として残るのは
`MergedHuffmanAuxIdentHypothesis` 一つだけ. この primitive の genuine discharge
(Part C, `huffmanLengthAux` の carrier-crossing 対応) は本 session で閉じられていない
残タスク (下記 docstring 参照). -/

/-- **強形主定理 (Hyp1 discharged)** — `MergedHuffmanAuxIdentHypothesis` を **唯一の
load-bearing hypothesis** として受け、Cover–Thomas Theorem 5.8.1 強形を結論する.

Hyp1 (swap normalization) は `swap_normalization_proof` で無条件に genuine discharge 済.
よって残る open hypothesis は `h_aux : MergedHuffmanAuxIdentHypothesis` の **1 つだけ**.

注: `h_aux` は load-bearing hypothesis (型は「`huffmanLengthAux (mergedInitMultiset Q a b) x
= (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val)`」 — Huffman 再帰を
2 carrier (`β` と `{y // y ≠ b}`) 間で関連付ける genuine な combinatorial 恒等式)。

**Superseded (2026-05-30)**: cost-level pivot (`huffman-cost-level-optimality`) で帰納核から
`h_aux`/`h_ident` 依存を除去した無引数 genuine 後継 `huffmanLength_optimal` (本 file:225、
`@audit:ok`、`#print axioms` sorryAx 非依存) が同結論を hypothesis なしで与える。本 wrapper は
body に実 sorry を持たず FALSE `h_aux` (`MergedHuffmanAuxIdentHypothesis`) を load-bearing
hypothesis として取るだけなので、`@residual(plan:...)` が指す closure 対象の sorry は存在しない
(旧 `@residual` を撤回)。weak-form API 後方互換のため残置。

@audit:superseded-by(huffmanLength_optimal) -/
@[entry_point]
theorem huffmanLength_optimal_modulo_aux_ident
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_aux : MergedHuffmanAuxIdentHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses
    swap_normalization_proof
    (huffmanMergedIdentification_of_aux h_aux)
    P hP l hl_pos hl_kraft

/-! ### T1-A'' — 無条件 strong form (cost-level pivot) -/

/-- **Cover–Thomas Theorem 5.8.1 (strong form) — hypothesis 引数なし**.

Huffman 語長は任意の Kraft-feasible 語長関数 `l` より期待長が小さい。**無条件**
(swap normalization は `swap_normalization_proof` で genuine discharge 済、
merged-carrier の bridge は cost-level
(`expectedLength_merged_cost_bridge`、per-symbol depth identity FALSE を経由しない)
で閉じている)。

前任 `huffmanLength_optimal_modulo_aux_ident` は FALSE predicate
`MergedHuffmanAuxIdentHypothesis` を hypothesis に取る weak form だったが、本定理は
cost-level pivot (`docs/shannon/huffman-cost-level-optimality-plan.md`) で帰納核から
`h_ident` 依存を除去した新 motor `huffmanLength_optimal_aux` を経由するため、FALSE
predicate を **一切経由しない**。
@audit:ok -/
@[entry_point]
theorem huffmanLength_optimal
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_aux (Fintype.card α) swap_normalization_proof
    P hP l hl_pos hl_kraft rfl

end InformationTheory.Shannon.Huffman
