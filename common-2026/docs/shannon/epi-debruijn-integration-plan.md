# EPI de Bruijn integration — discharge plan

**Status**: CLOSED ✅ — de Bruijn integration 経路 (heat-flow density → time-derivative → 区間積分 → L-EPI3 form) を整備し、general unconditional EPI closure に合流済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
**Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md)

## 要点 (≤5 行)
- slug `@residual(plan:epi-debruijn-integration)` は EPI/Stam/L3Integration 配線にまだコード残存 (linter は不検知)。
- V2 Fisher info sub-predicate decomposition (`IsHeatSpatialDerivHyp`/`IsHeatTimeDerivHyp`/`IsHeatFlowConvolutionHyp`/`IsIBPHypothesis`) を所与に積分恒等式部を組む設計。
- 再利用判断軸: integration identity 系 predicate は退化 path (恒等 0 density) で trivial 充足しないか必ず検算 — `∀ fPath` は `∃ fPath` に切替、bounded-T window に逃げる選択肢を常に検討。
