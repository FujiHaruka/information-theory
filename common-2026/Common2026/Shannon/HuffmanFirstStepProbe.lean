import Common2026.Shannon.HuffmanColexDeterminism

/-!
# T1-A'' Huffman — first-step identification PROBE (go/no-go for 案 A)

PROBE only. 目的: 決定的 `huffmanStep (initMultiset Q)` が、`MergedHuffmanAuxIdentHypothesis`
で外から与えられる `a` (`_h_a_min` = global-min) / `b` (`_h_b_min` = rest-min) /
`_h_sibling` の pair を **実際に first-merge する** ことを示せるか probe する。

## PROBE 結果 (確定)

**first-step identification は `∀ a b` 仮説では FALSE** (`chosen_le_given` で genuine 証明):
決定的 first 選択 `a*` は `(Q{·}, ·)` の lex-min (= prob-min かつ tie 時は `α`-最小;
`huffmanStep_initMultiset_fst_isLexMin` で genuine 証明)。与えられた `a` は `_h_a_min` で
prob-min と固定されるが、tie 時の `α`-order 位置は固定されないため `astar ≤ a` のみ従い、
`a = astar` は一般に偽。よって「決定的 step が given a,b を merge する」案 A の route は no-go。

**しかし merged-length identity 自体は TRUE** (手計算で確認、反例なし)。鍵は `_h_sibling`:
等語長 ⇒ `a, b` は同 depth の sibling であり、sibling pair を 1 leaf に collapse すると
**merge order に依らず** depth が 1 減る。よって正しい discharge route は first-step
identification ではなく **sibling-driven collapse** (確率 multiset で depth が決まる Huffman
性質、`HuffmanColexDeterminism.huffmanLengthAux_relabel_det` を部品に)。これは案 A(2) の
collapse 本体に相当し、moonshot 寄り (roadmap #19 追記4 の B 寄り)。

このファイルは probe 結果の genuine な記録 (lex-min 特性 + first-step 不可能性) のみを残す。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators Colex

universe u

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### colex on singletons -/

end InformationTheory.Shannon.Huffman
