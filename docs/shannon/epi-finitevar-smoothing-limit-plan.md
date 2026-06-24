# 有限分散 classical EPI closure — Phase-A smoothing-limit 実装計画

**Status**: CLOSED ✅ — 有限分散 a.c. 古典 EPI を Pivot B (explicit 密度版 de Bruijn + per-t smoothing EPI + 3 endpoint 連続性 + t→0 極限) で genuine closure。旧 bundled a.c. 古典壁を正則/有限分散/無限分散に 3 分解し、有限分散部を閉じた。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
**親**: [`epi-uncond-deffix-monotone-plan.md`](epi-uncond-deffix-monotone-plan.md)

## 要点 (≤5 行)
- slug `@residual(plan:epi-finitevar-smoothing-limit-plan)` (撤退口記録)。残壁 epi-infinite-variance-classical (無限分散 a.c.) は route T で FALSE WALL 判明 → genuine closure 済 (2026-06-07)、code から消滅 = CLOSED。
- 設計判断 (Pivot 教訓): Phase A `entropy_power_inequality_of_density` の `hreg_pX` は Mathlib 正準 `rnDeriv` toReal 代表元の pointwise `IsRegularDensityV2` を要求し、conv 密度とは a.e. 一致のみゆえ供給不能 (over-hypothesized) → explicit 密度版 producer (canonical rnDeriv 回避) を手組みする経路に切替。
- 再利用資産: smoothed 正則性 producer `isRegularDensityV2_convDensityAdd_gaussian` / sum 密度の `convDensityAdd_convGaussian_interchange` / 順序極限 `epi_of_csiszarLogRatioGap_tendsto` (`le_of_tendsto` 形)。
