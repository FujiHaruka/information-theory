# Shannon: BrunnMinkowski — `entropy_eq_logVolume_iff_uniform` + `brunn_minkowski_linear_from_prekopa_leindler` signature rewrite plan

**Status**: CLOSED ✅ — Ch.17 Inequalities は EPI closure の一部として handled。2 declaration の tier 5 `false-statement` 残置を linkage-hypothesis 形 + body sorry に移す signature rewrite workstream は決着済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`brunn-minkowski-sorry-migration-plan.md`](brunn-minkowski-sorry-migration-plan.md) §「Phase 2.3 — 第一選択 (定義書換) を試みる」の後追い独立 plan

## 要点
- 第一選択は textbook formulation の直 def 化ではなく、`(volume A).toReal` ベースの linkage hypothesis を Mathlib-shape-driven に追加し core を body sorry へ降ろす形 (Closure §F convention に揃える)。自由 scalar 引数のまま放置すると degenerate 代入で反証できる (false-statement の根源)。
- 両 declaration とも downstream consumer 0 件で 1 PR scope に収まる。
