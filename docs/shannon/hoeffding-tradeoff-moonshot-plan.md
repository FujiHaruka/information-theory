# Hoeffding tradeoff (T1-D) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Cover-Thomas Thm 11.7.x の Hoeffding tradeoff を sandwich (hypothesis) 形で publish。headline `hoeffding_tradeoff` (unconditional Tendsto) は L-H4 適用で defer、achievability/converse を仮説に取る `hoeffding_tradeoff_with_hypothesis` で close (tier-4 marker)。残スコープ (Phase C/D = achievability/converse の analytical closure) は `hoeffding-tradeoff-sandwich-plan.md` に切り出し。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。

## 要点 (≤5 行)
- `hoeffdingE2` family (定義 / 達成性 / 一意性 / 非負性 / constraint set 凸性) は `Chernoff.lean` で publish 済、本 plan は import して再利用。
- 設計は Mathlib-shape-driven: textbook の `min_{D(Q‖P₁)≤α} D(Q‖P₂)` を直書きせず、Csiszar projection + Sanov LDP equality + Stein typicality template の結論形に Qstar 経由で合わせる。
- L-H4 (Qstar full-support が log-singularity gradient 引数を要し本セッション discharge 不可) で Phase C/D を defer。full-support は hypothesis 形で publish。
- 残スコープ closure の核 (sandwich-plan 側): abstract full-support を `alpha` の 3-case 分割で構成的に回避、残リスクは Type-I AEP に局所化。
