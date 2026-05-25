import Common2026.Shannon.HuffmanStrongForm
import Common2026.Shannon.HuffmanSwapStepChainBody

/-!
# Huffman — shared wall lemmas (sorry-based migration aggregation)

`Common2026/Shannon/Huffman*.lean` 全体の load-bearing hypothesis predicate を **1 ヶ所に
集約した shared wall lemma 群**. 各 consumer wrapper は本 file の wall lemma を呼ぶことで
hypothesis 引数を削除でき、新規 sorry を作らずに済む。closure 責任は本 file の wall lemma
の `@residual(plan:...)` タグが一元的に保有する。

## 設計判断 (`huffman-sorry-migration-plan.md` 判断ログ #2 L-MIG-4 発動の帰結)

import cycle を避けるため、`HuffmanOptimality.lean:778/:1028` (`huffmanLength_optimal_aux_with_hypotheses`
/ `huffmanLength_optimal_with_hypotheses`) は **本 file を import しない**:

- `HuffmanWalls.lean` → `HuffmanStrongForm.lean` → `HuffmanSwapNormCompletion.lean` → ... →
  `HuffmanOptimality.lean` の import chain があり、`HuffmanOptimality.lean` から
  `HuffmanWalls.lean` を import すると循環。
- 解決: `HuffmanOptimality.lean:778/:1028` は signature 不変・body 不変、docstring タグだけ
  `@residual(plan:huffman-2hyp-vertical-reduction)` 化 (load-bearing predicate hypothesis を
  引数で受け取る top-most weak-form API として残置)。完全 honest 化は後続 plan 完遂時に
  wall closure と同タイミングで実施。
- 下流 wrapper (`HuffmanStrongForm.lean:175` / `HuffmanMergedIdentBody.lean:171` /
  `HuffmanT1APPrimeBody.lean` 13 件 / `HuffmanT1APPrimePartial.lean` 4 件 / 他) は本 file を
  import 可能なので wall 経由に書換 (hypothesis 引数削除)。

## Wall lemma の構成

- **Hyp1 (`SwapNormalizationHypothesis`)**: `swap_normalization_proof` (`HuffmanStrongForm.lean:144`)
  が **constructive proof 済** のため direct alias、sorry なし。
- **Hyp2 (`HuffmanMergedIdentificationHypothesis`)**: 未 proved、direct sorry +
  `@residual(plan:huffman-2hyp-vertical-reduction)`。
- **Hyp_aux (`MergedHuffmanAuxIdentHypothesis`)**: 未 proved、direct sorry +
  `@residual(plan:huffman-strong-form-completion)`。
- **Combined (`HuffmanCombinedHypothesis`)**: Hyp1 + Hyp2 の constructive `And` composition、
  sorry なし。
- **Chain combined (`HuffmanChainCombinedHypothesis`)**: Hyp1 + Hyp2 + `SwapStepLeChainHypothesis`
  の constructive composition (chain は `swapStepLeChainHypothesis_holds` が trivial discharge 済)、
  sorry なし。

合計: direct sorry 2 件 + constructive composition 3 件 = 5 wall lemma。
-/

namespace InformationTheory.Shannon.Huffman

universe u

/-- **Wall lemma (Hyp1, constructive)**: swap normalization の存在主張。
`HuffmanStrongForm.lean:144` `swap_normalization_proof` が genuine constructive proof で
閉じているため direct alias。本 lemma は **sorry を持たない** (proof done)。

@audit:ok -/
theorem swap_normalization_hypothesis_holds : SwapNormalizationHypothesis.{u} :=
  swap_normalization_proof

/-- **Wall lemma (Hyp2)**: `huffmanLength` identification on `mergedMeasure`。
完全 discharge は後続 plan `huffman-2hyp-vertical-reduction-plan` で予定。

@residual(plan:huffman-2hyp-vertical-reduction) -/
theorem huffman_merged_identification_hypothesis_holds :
    HuffmanMergedIdentificationHypothesis.{u} := by
  sorry

/-- **Wall lemma (Hyp_aux)**: merged measure 上の `huffmanLengthAux` 識別の primitive 形。
完全 discharge は後続 plan `huffman-strong-form-completion-plan` で予定。

@residual(plan:huffman-strong-form-completion) -/
theorem merged_huffman_aux_ident_hypothesis_holds : MergedHuffmanAuxIdentHypothesis.{u} := by
  sorry

/-- **Wall lemma (combined, constructive)**: Hyp1 + Hyp2 の `And` composition。
Hyp1 は constructive、Hyp2 は wall lemma 経由なので本 wall も sorry を持たないが、
Hyp2 wall の closure に transitively 依存する。 -/
theorem huffman_combined_hypothesis_holds : HuffmanCombinedHypothesis.{u} :=
  ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds⟩

/-- **Wall lemma (chain combined, constructive)**: Hyp1 + Hyp2 + chain hypothesis の triple
`And` composition。chain hypothesis は `swapStepLeChainHypothesis_holds` で trivial に
discharge 済。本 wall も sorry を持たないが、Hyp2 wall の closure に transitively 依存する。 -/
theorem huffman_chain_combined_hypothesis_holds : HuffmanChainCombinedHypothesis.{u} :=
  ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds,
   swapStepLeChainHypothesis_holds⟩

end InformationTheory.Shannon.Huffman
