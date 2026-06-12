# AWGN M5 — true sorry-based migration plan (Path 1)

**Status**: CLOSED ✅ — 10 件の load-bearing predicate を Tier 3 bookkeeping から Tier 2 (`sorry` + `@residual`) へ格上げ完了。achievability 側は完全 proof done (`@audit:ok`)、converse 側も shared sorry 補題化で honest 撤退口に揃え、AWGN 形式化ラインは CLOSED。機械検証状態は SoT 参照。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)
> + [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> + [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md)
> + [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md)
> + [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md)

## 要点 (再利用可能な一行)

- Route 分類: sub-bound predicate は shared sorry 補題化、bundle は削除 + consumer signature 書換。EPI-Stam Cluster C (`debruijnIdentityV2_holds` 共有 sorry 補題) と同型のパターン。
- achievability の strict-slack witness `awgnPowerWitness_exists` は中点構成 (`P_min := N·(exp(2R)−1)`) で genuine 化でき、power-constraint の honest 化に再利用可能。
- 撤退ライン: predicate を shared sorry 補題に降格しても Tier 2 移行自体は完遂できる (honest sorry を別所で抱えるだけ)。
