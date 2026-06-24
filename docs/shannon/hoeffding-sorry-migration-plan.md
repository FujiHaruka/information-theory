# Shannon: Hoeffding `@audit:suspect` → sorry-based migration plan

**Status**: CLOSED ✅ — Hoeffding family の legacy `@audit:suspect` 語彙を sorry-based に移行する pilot sweep 完遂。proof completion ではなく honesty 強化が目的で、Phase C/D の analytical closure は別 workstream に残し scope 外。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。
> **Parent**: [`hoeffding-tradeoff-moonshot-plan.md`](hoeffding-tradeoff-moonshot-plan.md)

## 要点 (≤5 行)
- 残 residual は単一 plan slug `plan:hoeffding-tradeoff-moonshot-plan` に揃える方針 (該当 wall name register なし、shared wall 補題集約は不要)。
- 3 つの load-bearing predicate (`IsHoeffdingInteriorGradient` / `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp`) は `@audit:retract-candidate(load-bearing-predicate)` 付きで残す。`IsHoeffdingMinimizerFullSupport` (= `∀ a, 0 < Qstar a`) / `IsHoeffdingTiltMinimal` は純 regularity / in-tree 構成済 primitive なので touch しない。
- variational pass-through wrapper (`h_liminf` / `h_limsup` 取りの slim wrapper) は load-bearing でないと判断し tag 削除のみ。headline `hoeffding_tradeoff_with_hypothesis` は achievability + converse を hypothesis に取る形のまま (tier-4 marker)。
- pilot 知見: transitive sorry の表現語彙が未整備 → docstring 散文で処理 (`@residual` の `:transitive` suffix 等は導入せず)。
