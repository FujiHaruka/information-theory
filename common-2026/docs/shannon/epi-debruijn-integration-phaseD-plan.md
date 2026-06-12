# EPI de Bruijn integration — Phase D mini-plan (`IsStamToEPIBridgeHyp` 入口形式整形)

**Status**: CLOSED ✅ — `csiszarGap` 定義 + endpoint lemma + sister export を実装、Phase C 出力の reshape は docs-only sister 委譲で決着。EPI family は DONE。
**SoT**: `docs/textbook-roadmap.md` Ch.17 EPI（+ `docs/shannon/epi-facts.md`）。詳細履歴は git。

> **Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) §Phase D
> **Sister consumer**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A
> **Mathlib inventory**: [`epi-debruijn-integration-mathlib-inventory.md`](epi-debruijn-integration-mathlib-inventory.md)

## 要点 (≤5 行)
- `csiszarGap` の shape は sister `IsStamToEPIScalingHyp` の `AntitoneOn` 引数と verbatim 一致するよう設計（Mathlib-shape-driven）— `heatFlowPath2` 形を採用。
- D-2 の `Y := 0` 退化検算: `entropyPower (Dirac 0) = 1`（plan の予測「0」は誤り）→ 退化 gap = 定数 = degenerate-definition exploitation 直撃のため戦略 γ（docs-only sister 委譲）に honest 降格。
- 14 件タグ降格は sister Phase A 完了後 cleanup として本 mini-plan 責務外。
