# Rate-distortion achievability — E-3''' fully-discharged サブ計画

**Status**: CLOSED ✅ — strong-encoder track で headline `rate_distortion_achievability` を publish 済 (weak-encoder track は数学的に行き詰まり strong track へ移行)。核 `codebookAvgFailureStrong_tendsto_zero` も実証明。
**SoT**: `docs/textbook-roadmap.md` Ch.10。詳細履歴は git。
> **Parent**: [`rate-distortion-achievability-plan.md`](rate-distortion-achievability-plan.md) §Phase E (strong-typicality variant)

## 要点 (任意, ≤5 行)
- Cover-Thomas 10.5 の random-coding 失敗確率を strong-typicality 経路で分解 (E1 source 非 typical / E2 どの codeword も joint-typical でない / E3 strong-JTS encoder が distortion-typical を自動保証)。
- 中核は Cover-Thomas Lemma 10.6.1 strong form の per-source-typical match-probability 下界 (conditional strongly typical slice の size lower bound から導出)。
- encoder は in-place 改修ではなく strong 版 `jointStronglyTypicalLossyEncoder` を並立 (既存 weak chain 温存)。
- 残る honest pass-through hyp: strong-JTS⊆distortion-typical bridge + rate-gap/distortion-budget/KL-dominate 各条件 + `hqStar_pos`。
