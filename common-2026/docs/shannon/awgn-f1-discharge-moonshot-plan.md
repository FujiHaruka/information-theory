# AWGN F-1 (kernel measurability) discharge ムーンショット計画 🌙

**Status**: CLOSED ✅ — `isAwgnChannelMeasurable N` を完全証明 (0 sorry)、`awgn_theorem_F1_discharged` を `h_meas` 引数なし形で再 publish。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-4 (kernel measurability)」 + 判断ログ #1。Seed プロンプト側では同じ箇所を「F-1」と呼ぶ (どちらも `Measurable (fun x : ℝ => gaussianReal x N)`)。

## 要点 (将来作業で再利用しうる路)
- 戦略: `gaussianReal x N = (gaussianReal 0 N).map (x + ·)` (Mathlib `gaussianReal_map_const_add` の `μ=0` 特殊化) に書換 → Giry-monad measurability (`Measure.measurable_of_measurable_coe` + root namespace `measurable_measure_prodMk_left`) に帰着。`m`-measurability 直接構成 (parametric integral / Fubini) より ~5x 短い。
- 嵌り点: `measurable_measure_prodMk_left` は `namespace MeasureTheory` の外にあり root namespace 名で呼ぶ。`Measure.map_apply` 後の preimage 等式は `rfl` で抜けた (`congr 1` は "No goals")。
