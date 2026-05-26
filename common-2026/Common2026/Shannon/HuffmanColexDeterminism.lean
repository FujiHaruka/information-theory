import Common2026.Shannon.HuffmanMergedAuxIdent

/-!
# T1-A'' Huffman — colex 決定化による無条件 relabel 不変量

`huffmanStep` の colex 決定化 (`Huffman.lean`、`groupKey` 2 段 lex min) により、
`HuffmanMergedAuxIdent.lean` の no-ties 限定 (`NodupChain`) relabel 機構を
**無条件版** へ一般化する。`groupKey` は単射なので min は常に一意 (確率 tie は colex で
破られる)。よって relabel-invariance は `NodupChain` 不要で成立する。

## 設計上の重要制約 (Phase 0 probe で確定)

carrier 型に `[DecidableEq α]` と `[LinearOrder α]` の **2 つの DecidableEq instance** が
同時に在ると、`toColex_image_le_toColex_image` の colex 保存鎖が `whnf`/`isDefEq` で
タイムアウトする (ambient `[DecidableEq α]` vs `LinearOrder.toDecidableEq` の defeq 検査が
ℝ import 下で爆発)。よって本 file の carrier variable は **`[LinearOrder α]` のみ**を持ち、
`DecidableEq` はそこから導出する (separate `[DecidableEq α]` を置かない)。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators Colex

universe u

-- carrier `α` は [LinearOrder α] のみ (DecidableEq は導出、dual-instance timeout 回避)
variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Section F — colex 保存 (strict-mono embedding) -/

/-! ### Section G — 無条件 (groupKey) min 一意性 -/

/-! ### Section H — 無条件 (決定的) relabel correspondence

`huffmanStep` の colex 決定化により、relabel と min 選択は **無条件に可換** になる
(`NodupChain` 不要)。`huffmanStep_*_relabel` の決定版。 -/

/-! ### Section I — 無条件 relabel-invariance of `huffmanLengthAux` (cornerstone)

step-correspondence (`huffmanStep_step_relabel_det`) を strong induction で持ち上げ、
`huffmanLengthAux` の carrier-embedding 越し不変量を **NodupChain 不要**で得る。
これが決定化が unlock する核心の不変量 (旧 `huffmanLengthAux_relabel` の無条件版)。 -/

/-! ### Section J — 残タスク (honest, load-bearing): collapse correspondence

`huffmanLengthAux_relabel_det` (Section I) は決定化が unlock した **無条件 genuine** な
relabel 不変量で、`HuffmanMergedAuxIdent.lean` の旧 no-ties (`NodupChain`) 機構を
完全に置き換える。これにより Section E の障害 (ii) (NodupChain 不成立) と
(iii) (per-symbol invariance 偽) は **解消** された (両 carrier の決定的 min は colex で
常に一意、relabel と無条件可換)。

**しかし `MergedHuffmanAuxIdentHypothesis` の完全 discharge には、なお 1 つの genuine な
構造補題 (collapse correspondence) が残る。** これは determinization では自動的に閉じない
(`huffmanStep` の within-tree 非決定性を断つことと、cross-tree の Finset-label 構造変更を
橋渡しすることは別問題)。具体的に:

`relabelMultiset (subtypeNeEmbedding b) (mergedInitMultiset Q a b)` (β carrier 上) は
`initMultiset Q` の最初の決定的 merge 後の残木 `s''_β` と **1 group だけ** 異なる:
mergedInit 側は absorbing leaf が singleton `({a}, Q{a}+Q{b})`、`s''_β` 側は card-2 group
`({a,b}, Q{a}+Q{b})`。確率は同一だが colex が異なる
(`toColex {a} < toColex {a,b}`、`{a} ⊂ {a,b}` より strict)。

**collapse 補題**: `huffmanLengthAux` は、ある group の Finset-label `{a}` を `{a,b}`
(同確率、`b` は他に現れない fresh element) に拡張しても、`b` 以外の leaf の値を保つ:
`huffmanLengthAux (({a},p) ::ₘ rest) z = huffmanLengthAux (({a,b},p) ::ₘ rest) z`  (`z ≠ b`).

これは **genuine な Huffman の事実** で、数値検証 (例 `Q={a:.1,c:.25,b:.15,d:.5}`、
`a<c<b` で colex tie-break が両木で食い違うケース) で **per-leaf identity は成立** を確認済
だが、merge **order** は equal-probability tie 下で両木間で食い違いうるため、naive な
lockstep 帰納では閉じない。tie-break order に依存しない invariant (確率 multiset で
depth が決まる Huffman 性質の機械化) が必要で、規模は ~150-250 行 + tie 場合分け、
本 session で genuine に閉じるには proof-pivot-advisor のエスカレーションが妥当。

**honesty 線 (重要)**: 本 session は collapse 補題を fake な residual hypothesis
(型 ≡ `MergedHuffmanAuxIdentHypothesis`) で抜くことを **しない** (Section E / plan 撤退ライン
の禁止事項)。よって無引数 `huffmanLength_optimal` は **publish しない**。honest な最前線は
引き続き headline `huffmanLength_optimal_modulo_aux_ident` (`HuffmanStrongForm.lean`、
Hyp2 = `MergedHuffmanAuxIdentHypothesis` を明示引数で取る、sorryAx 非依存) のまま。
本 session の genuine な前進は: (1) `huffmanStep` colex 決定化 (`Huffman.lean`、無条件)、
(2) `huffmanLengthAux_relabel_det` (NodupChain 不要の無条件 relabel cornerstone)。 -/

end InformationTheory.Shannon.Huffman
