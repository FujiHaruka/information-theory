# LZ78 passthrough scaffolding consolidation plan

**Status**: ✅ CLOSED (commit `602b1ad`) — dead scope-out passthrough scaffolding
削除済。漸近最適性核心は `GreedyParsingImpl.lean` の wall sorry lemma 2本
(`lz78GreedyImpl_converse_ae` = `wall:lz78-converse-aseventual` /
`lz78GreedyImpl_achievability_ae` = `wall:lz78-aseventual-ziv`) に一本化。

**Parent**: `docs/textbook-roadmap.md` (Ch.13 Universal Coding)

## 結論 (1 段)

scope-out statement を 2 形で重複 publish していた状態を解消した honesty hygiene
cleanup。`Basic.lean §2` の dead statement-only predicate 3本
(`IsZivInequalityPassthrough` / `IsLZ78ConversePassthrough` /
`IsSMBSandwichPassthrough`、tier-4 legacy) と唯一の consumer
`IsLZ78PhraseCountAsymptotic.of_passthrough` (`_h` discard の dead-hyp bridge) を
物理削除し、漸近最適性の「honest 残課題マーカー」を `GreedyParsingImpl.lean` の
wall sorry lemma 2本に集約。実 sorry 数は不変 (2)。

その後の符号長 def-fix (commit `5d08566`) で当該 2 sorry は dummy parse 時代の
defect (false-statement / degenerate) から genuine M3/M4 壁に格上げ済 (本 plan の
対象外、`docs/shannon/lz78-completion-roadmap.md` §0 参照)。

`GreedyParsing.lean` の `IsLZ78CountBoundPassthrough` /
`IsLZ78EncodingLengthBoundPassthrough` は genuine な count/length 上界 passthrough
(M2 系) で本 plan の削除対象ではない (dead scaffolding ではない)。
