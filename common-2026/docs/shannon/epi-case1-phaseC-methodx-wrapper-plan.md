# EPI case 1 Phase C: 方針X wrapper `entropyPower_add_ge_case1_of_methodX` サブ計画

**Status**: CLOSED ✅ — case-1 EPI を方針X regularity + de Bruijn per-time regularity に還元する wrapper を実装、結線は 3-noise lift route + 無条件 ℝ≥0∞ route で達成。EPI family は DONE。
**SoT**: `docs/textbook-roadmap.md` Ch.17 EPI（+ `docs/shannon/epi-facts.md`）。詳細履歴は git。

> **Parent**: [`epi-case1-ratio-limit-plan.md`](epi-case1-ratio-limit-plan.md)（grandparent: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)）

## 要点 (≤5 行)
- de Bruijn per-time regularity 群は honest precondition として thread する設計（code 側 `@residual(plan:epi-debruijn-pertime-closure)` が SoT）。
- 独立性は 4-tuple `iIndepFun ![X, Y, Z_X, Z_Y]` 1 本に集約、`_of_regular` の個別 indep を body で group-split。
- variance bound は body で `Var[·;P]` を construct（caller に出さない）。命名は `_of_methodX`（`_unconditional` 禁止）。
- 当初の 2-noise lift route-B は uninhabitable な sum-instance 構造制約で撤退、実装は 3-noise lift（`liftMeasure3` + two-time terminal）。
