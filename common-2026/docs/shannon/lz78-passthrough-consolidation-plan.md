# LZ78 passthrough scaffolding consolidation plan

> **2026-06-21 (073c48a) obsoleted**: worst-case passthrough scaffolding (`IsLZ78CountBoundPassthrough` + worst-case encoding-length passthrough) を退役・削除し、genuine な impl-prefix 付き encoding-length passthrough 述語を空いた `IsLZ78EncodingLengthBoundPassthrough` 名へリネーム → 本 plan が提案した consolidation は退役側で事実上達成済。以下の本文 §結論の `IsLZ78CountBoundPassthrough` 存在前提の記述は退役前のスナップショット (履歴は git)。

**Status**: ✅ CLOSED (commit `602b1ad`) — dead scope-out passthrough scaffolding
削除済。漸近最適性核心は `AsymptoticOptimality.lean` の 2 本の sorry lemma
(`lz78Greedy_converse_ae` / `lz78Greedy_achievability_ae`) に一本化していた。
**後日談 (本 plan の対象外、参考)**: 当該 2 本はいずれも genuine に CLOSED 済 —
achievability `lz78Greedy_achievability_ae` は leg 11 で sorryAx-free
(commit `c22f2d5`、旧 `wall:lz78-aseventual-ziv` 解消)、converse
`lz78Greedy_converse_ae` は M4 で sorryAx-free (commit `bd28e0e`、旧
`plan:lz78-m4-plan` discharge) → headline `lz78_asymptotic_optimality_with_greedy`
sorryAx-free = LZ78 漸近最適性 完遂。詳細 → `docs/shannon/lz78-completion-roadmap.md`。

**Parent**: `docs/textbook-roadmap.md` (Ch.13 Universal Coding)

## 結論 (1 段)

scope-out statement を 2 形で重複 publish していた状態を解消した honesty hygiene
cleanup。`Basic.lean §2` の dead statement-only predicate 3本
(`IsZivInequalityPassthrough` / `IsLZ78ConversePassthrough` /
`IsSMBSandwichPassthrough`、tier-4 legacy) と唯一の consumer
`IsLZ78PhraseCountAsymptotic.of_passthrough` (`_h` discard の dead-hyp bridge) を
物理削除し、漸近最適性の「honest 残課題マーカー」を `AsymptoticOptimality.lean` の
wall sorry lemma 2本に集約。実 sorry 数は不変 (2)。

その後の符号長 def-fix (commit `5d08566`) で当該 2 sorry は dummy parse 時代の
defect (false-statement / degenerate) から genuine M3/M4 壁に格上げ済 (本 plan の
対象外、`docs/shannon/lz78-completion-roadmap.md` §0 参照)。

(退役前スナップショット) `IsLZ78CountBoundPassthrough` /
`IsLZ78EncodingLengthBoundPassthrough` は genuine な count/length 上界 passthrough
(M2 系) で本 plan の削除対象ではない (dead scaffolding ではない)。
→ 073c48a で worst-case 側が退役され、genuine `IsLZ78EncodingLengthBoundPassthrough`
のみ `AsymptoticOptimality.lean` に残置 (冒頭 obsoleted note 参照)。
