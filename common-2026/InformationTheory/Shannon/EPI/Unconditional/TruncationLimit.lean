import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Core
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Mono
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Limit

/-!
# EPI 無条件化 W-Y2 — route β' (truncation + monotone-limit) skeleton

無限エントロピー a.c. 入力 (`h(W) = ⊤` の a.c.) で gateway 単調性の ⊤ 伝播
`differentialEntropyExt_top_of_indep_add` を **無条件** (整数 truncation 近似経由) で
genuine 着地させるための skeleton。route T (`EPIInfiniteVarianceTruncation` /
`EPIInfiniteVarianceCapstone`、sorryAx-free CLOSED) の機構を `W` 単独 truncation に
読み替えて再利用する。

ターゲットは無条件版② chain rule の等式 (finiteness-free 証明不能確定) でなく、
gateway 単調性の ⊤ 枝不等式 (`h(W) = ⊤ ⟹ h(W+V) = ⊤`)。LSC/liminf は `≤` しか出さないが、
⊤ 枝は `le_top` 一発で閉じるため極限と相性が良い。

route β' Phase 1 skeleton (本 file は signature 確定のみ、本体は Phase 2-4)。

SoT 計画: `docs/shannon/epi-uncond-truncation-lsc-plan.md`
(Parent: `docs/shannon/epi-unconditional-moonshot-plan.md` §S5 W-Y2)。
-/
