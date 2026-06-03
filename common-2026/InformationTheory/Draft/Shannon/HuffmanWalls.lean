import InformationTheory.Shannon.HuffmanStrongForm
import InformationTheory.Shannon.HuffmanSwapStepChainBody
import InformationTheory.Meta.EntryPoint

/-!
# Huffman — shared wall lemmas (sorry-based migration aggregation)

`InformationTheory/Shannon/Huffman*.lean` 全体の load-bearing hypothesis predicate を **1 ヶ所に
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
  が **constructive proof 済** のため direct alias、sorry なし (`@audit:ok`)。
- **Hyp2 (`HuffmanMergedIdentificationHypothesis`)**: ⚠ **FALSE STATEMENT** (2026-05-30 機械確定)。
  direct sorry は discharge 可能性ではなく false-statement の honest marker として残置。
  `@audit:defect(false-statement) @audit:retract-candidate(false-hypothesis)` (independent audit
  2026-05-30: 機構固有名 reason を正規 vocab `false-hypothesis` に統一、機構説明は各 lemma 散文に保持)。
- **Hyp_aux (`MergedHuffmanAuxIdentHypothesis`)**: ⚠ **FALSE STATEMENT** (Hyp2 と同一 statement、
  同じ反例で偽)。direct sorry は false-statement の honest marker。同上タグ。
- **Combined (`HuffmanCombinedHypothesis`)**: Hyp1 + Hyp2 の constructive `And` composition、
  body は ⟨...⟩ で sorry を直接持たないが Hyp2 が false のため transitively false-premised。
- **Chain combined (`HuffmanChainCombinedHypothesis`)**: Hyp1 + Hyp2 + `SwapStepLeChainHypothesis`
  の constructive composition (chain は `swapStepLeChainHypothesis_holds` が trivial discharge 済)、
  body は ⟨...⟩ で sorry を直接持たないが Hyp2 が false のため transitively false-premised。

合計: false-statement direct sorry 2 件 + transitively false-premised composition 2 件
+ constructive `@audit:ok` 1 件 = 5 wall lemma。merged-identity 経路 (per-symbol depth identity)
は全体が dead — pivot 方向は tie-invariant な cost-level merge identity
(反例 / 根本原因 → `docs/shannon/verify/merged_huffman_aux_ident_counterexample.py` +
`huffman-strong-form-completion-plan.md` 判断ログ #5)。
-/

namespace InformationTheory.Shannon.Huffman

universe u

/-- **Wall lemma (Hyp1, constructive)**: swap normalization の存在主張。
`HuffmanStrongForm.lean:144` `swap_normalization_proof` が genuine constructive proof で
閉じているため direct alias。本 lemma は **sorry を持たない** (proof done)。

@audit:ok -/
@[entry_point]
theorem swap_normalization_hypothesis_holds : SwapNormalizationHypothesis.{u} :=
  swap_normalization_proof

/-- **Wall lemma (Hyp2)** — ⚠ **FALSE STATEMENT, discharge 不能**.

`HuffmanMergedIdentificationHypothesis` は `MergedHuffmanAuxIdentHypothesis` と
**同一 statement** (measure-level、`initMultiset_mergedMeasure_eq` 経由で aux 形に帰着)。
従って下記の aux 反例がそのまま適用され、本 statement も FALSE。

反例 (機械検証済、`docs/shannon/verify/merged_huffman_aux_ident_counterexample.py`):
β = {0,1,2,3} (card 4)、weights `[1,2,1,1]`、`a=0`, `b=2`。全強前提 (a global-min /
b rest-min / a≠b / huffmanLength 一致) を充足し、かつ a,b は実際に first-merged 対だが、
x=0 で恒等式が要求する `huffmanLength Q a - 1 = 1` に対し merged depth = 2 で MISMATCH。
根本原因: 決定的 colex tie-break が merge 操作で不安定 (merge 後 singleton {0}(確率2/5)
が再 Huffman で {3}(1/5) と先に対になり depth 2 に戻る → 元木の collapse に対応しない)。

`sorry` は discharge 可能性を示すものではなく、false statement の honest marker として
残置 (consumer 設計を cost-level identity に pivot するまで撤回保留)。

independent audit (2026-05-30): 反例独立再現 + simulator↔Lean 定義忠実性照合済。retract reason は
機構固有名 `deterministic-colex-merge-instability` ではなく正規 vocab `false-hypothesis` に統一
(audit-tags.md Reason 表 L247、def/Prop 自身が機械検証可能に FALSE の場合の標準 reason)。機構の説明は
上記散文に保持。
@audit:defect(false-statement) @audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-cost-level-optimality) -/
@[entry_point]
theorem huffman_merged_identification_hypothesis_holds :
    HuffmanMergedIdentificationHypothesis.{u} := by
  sorry

/-- **Wall lemma (Hyp_aux)** — ⚠ **FALSE STATEMENT, discharge 不能**.

merged measure 上の `huffmanLengthAux` 識別の primitive 形。`MergedHuffmanAuxIdentHypothesis`
は universal statement として FALSE と機械的に確定 (2026-05-30)。

反例 (機械検証済、`docs/shannon/verify/merged_huffman_aux_ident_counterexample.py`):
β = {0,1,2,3} (card 4)、weights `[1,2,1,1]`、`a=0`, `b=2`。全強前提 (a global-min /
b rest-min / a≠b / `huffmanLength Q 0 = huffmanLength Q 2 = 2`) を充足し、かつ a,b は
実際に first-merged 対 (元木の最初の merge = {0},{2}) だが、x=0 で恒等式が要求する
`huffmanLength Q a - 1 = 1` に対し merged depth = 2 で MISMATCH (x=1 でも depth 1 vs
期待 2 で失敗)。根本原因: 決定的 colex tie-break が merge 操作で不安定 — merge 後 singleton
{0}(確率 2/5) が再 Huffman で {3}(1/5) と先に対になり depth 2 に戻り、元木の {0,2} 部分木を
collapse した構造に対応しない。tie が無ければ恒等式は常に成立 (870 distinct-weight case で
反例 0、検証済) であり collapse 補題 (前セッション FALSE 確定) と同根。「strong precondition
(first-merged) なら成立」という旧 docstring 主張も上記反例で誤りと確定。

`sorry` は discharge 可能性を示すものではなく、false statement の honest marker として残置。

independent audit (2026-05-30): 反例独立再現 (script 再実行 + 手計算 + a,b first-merged 確認) +
simulator↔Lean 定義 (`groupKey`/`huffmanStep`/`huffmanLengthAux`) 忠実性照合済。retract reason は
正規 vocab `false-hypothesis` に統一。
@audit:defect(false-statement) @audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-cost-level-optimality) -/
@[entry_point]
theorem merged_huffman_aux_ident_hypothesis_holds : MergedHuffmanAuxIdentHypothesis.{u} := by
  sorry

/-- **Wall lemma (combined)** — ⚠ **transitively false-premised**.

Hyp1 + Hyp2 の `And` composition。body は ⟨...⟩ constructive で sorry を直接持たないが、
Hyp2 (`huffman_merged_identification_hypothesis_holds`) が false-statement wall のため、
本 composition も transitively false-premised (Hyp2 wall closure 不能 = 本 wall も genuine 化不能)。

@audit:defect(false-statement) -/
@[entry_point]
theorem huffman_combined_hypothesis_holds : HuffmanCombinedHypothesis.{u} :=
  ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds⟩

/-- **Wall lemma (chain combined)** — ⚠ **transitively false-premised**.

Hyp1 + Hyp2 + chain hypothesis の triple `And` composition。chain hypothesis は
`swapStepLeChainHypothesis_holds` で trivial に discharge 済。body は ⟨...⟩ constructive で
sorry を直接持たないが、Hyp2 (`huffman_merged_identification_hypothesis_holds`) が
false-statement wall のため、本 composition も transitively false-premised。

@audit:defect(false-statement) -/
@[entry_point]
theorem huffman_chain_combined_hypothesis_holds : HuffmanChainCombinedHypothesis.{u} :=
  ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds,
   swapStepLeChainHypothesis_holds⟩

end InformationTheory.Shannon.Huffman
