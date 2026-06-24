# Shannon: LZ78 legacy-tag → sorry-based migration plan

**Status**: CLOSED ✅ — LZ78 (Ch.13) は 🟢 within scope。本 plan が対象とした legacy tag (`@audit:suspect` / 散文 `🟢ʰ` / `@audit:defect(*)`) → `sorry + @residual` migration の対象 file 群 (`LZ78ConverseDischarge` / `LZ78FinalGlue` / `LZ78ZivCombinatorics` / `LZ78ZivTreeNode` / `LZ78SMBSandwich` 系) は M3/M4 scope-out で削除済のため migration 不要。
**SoT**: `docs/textbook-roadmap.md` Ch.13。詳細履歴は git。

> **Parent**: [`lz78-moonshot-plan.md`](lz78-moonshot-plan.md) +
> [`lz78-residual-discharge-plan.md`](lz78-residual-discharge-plan.md) +
> [`lz78-ziv-inequality-discharge-moonshot-plan.md`](lz78-ziv-inequality-discharge-moonshot-plan.md) +
> [`lz78-blockrv-refactor-plan.md`](lz78-blockrv-refactor-plan.md) +
> [`lz78-achievability-converse-plan.md`](lz78-achievability-converse-plan.md)
> + [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md)
> + [`audit/audit-tags.md`](../audit/audit-tags.md)。

## 要点
- `IsLZ78ZivCombinatorialCoreOverhead` は mathematically FALSE (constant process 反例)、依存定理は vacuously conditioned。FALSE predicate を hypothesis に取る wrapper は defect kind `false-hypothesis` で扱う (Pattern H)。`not_isLZ78ZivCombinatorialCoreOverhead` で genuine refutation 済だった。
- migration の主眼は load-bearing predicate (`Is*ChainHyp` 等) consumer の body sorry 化であり proof completion ではない。regularity hyp (`hreg` / factorization の regularity-constructible 版) は precondition なので残す対象だった。`IsSMBToLZ78ConverseChainBridge` は literally alias = name-laundering defect。
