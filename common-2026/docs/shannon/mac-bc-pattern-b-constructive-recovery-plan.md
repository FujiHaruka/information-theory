# Shannon: MAC-BC Pattern B constructive recovery サブ計画

**Status**: CLOSED ✅ — MAC `_three_bounds` + BC `_corner_limit` の 2 outer-bound wrapper を、既存 in-tree 部品の直接組合せ (Pattern B constructive recovery) で proof done に到達。MAC / BC / Relay 系 main は scope-out (textbook-roadmap Ch.15)。
**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**: [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) Round 2 残課題 follow-up

## 要点 (再利用しうる観察)

- **Pattern B 適用条件**: 結論型 (`InMACCapacityRegion` / `InBCCapacityRegion`) が 2-3 不等式を bundle した structure で、入力 hyp がその不等式そのもの (または 1 つの `linarith` で接続可能) のとき、新規 wall promotion / signature 改変なしで constructive closure 可能。MAC `_three_bounds` は `mac_region_combine ⟨h₁,h₂,hs⟩` 直接構築、BC `_corner_limit` は `bc_capacity_region_outer_bound` 戻り + `ε ≤ 0` transitive。
- **Chernoff 対照**: 結論型が `limsup rate ≤ -log Z(λ)` 等の load-bearing claim だと rate inequality を hypothesis inject せねば閉じず constructive recovery 不可 — そちらは 19 件全件不適。区別軸は「結論 structure を構築する部品が in-tree に揃っているか」。
