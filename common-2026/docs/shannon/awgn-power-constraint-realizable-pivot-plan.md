# AWGN — `IsAwgnPowerConstraintRealizable` predicate pivot サブ計画

**Status**: CLOSED ✅ — `IsAwgnPowerConstraintRealizable` の false-statement defect を honest staged bundle (`IsAwgnRandomCodingFeasible`、`P' < P` スラック付き) へ reshape し、consumer 3 件を 1 hyp に縮約して再封止。後続 M5 migration で Tier 2 (sorry + @residual) 化を完了し、AWGN 形式化ラインは CLOSED。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent / Sibling**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)

## 要点 (再利用可能な一行)

- pivot の核: Cover-Thomas 9.2 の「codeword を variance `P' < P` で生成 → SLLN slack」を predicate 側に押し付ける。codebook は P' 生成、constraint target は `n·P` のまま (両者の差が chi-square mass bound に乗る)。
- Phase A 補題が `σsq` 抽象なので consumer body の P→P' 書換は `gaussianCodebook M n P'.toNNReal` の sed 主体で済む (3 hyp → 1 bundle 統合で P' 整合性も構造的に保証)。
- 教訓: 「P_cb / P_target 分離」型 predicate は consumer 側で sub-bound 毎の rate-bound の P_cb / P_target 側を追跡する必要。`P' = P` 退化を許す non-strict は genuine discharge 時に strict へ upgrade する責務を残す。
