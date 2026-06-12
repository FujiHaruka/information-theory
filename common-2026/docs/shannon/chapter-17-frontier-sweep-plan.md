# Shannon Ch.17: Frontier Sweep — Rename + Minkowski Promote

**Status**: CLOSED ✅ — Ch.17 Inequalities は EPI closure の一部として handled。frontier 3 アイテム (Gaussian additivity rename / CT 17.9 Minkowski determinant inequality promote / `_exp_form`·`_log_form` 用語整合) の sweep workstream は決着済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: 親 moonshot 不在 (Ch.17 EPI 周辺の frontier 統合 plan)。

## 要点
- Tier 1 declaration の identifier rename は意味不変の pure refactor ゆえ一括 search-replace を default (deprecated alias は緊急 fallback のみ — プロジェクトに前例なし)。
- CT 17.9 Minkowski determinant inequality は二重壁構造: `Matrix.det_add` 系が Mathlib 絶対不在 + multivariate Gaussian の entropy/entropyPower 形が不在。multivariate Gaussian 自体は `multivariateGaussian` (Mathlib/Probability/Distributions/Gaussian/Multivariate.lean) として実在 — 旧 plan の `gaussianMultivariate` typo 由来 false negative を訂正済。
