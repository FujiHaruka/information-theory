# Shannon: small-cluster legacy-tag → sorry-based migration plan

**Status**: CLOSED ✅ — 8 小規模 file (各 1-2 件、計 12 declaration) の legacy `@audit:suspect` を `sorry + @residual(plan:<slug>)` 化 (P pattern 10) または closed-by-successor 化 (2 件、StationaryKernel / BirkhoffErgodic)。type-check done が DoD、proof done は各親 plan の workstream。
**SoT**: `docs/textbook-roadmap.md` Ch.15 (SeparationTheorem 該当)。詳細履歴は git。
> **Parents (per file)**:
> [`multivariate-diffentropy-subadditivity-plan.md`](multivariate-diffentropy-subadditivity-plan.md) /
> [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md) /
> [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) /
> [`epi-convolution-density-plan.md`](epi-convolution-density-plan.md) /
> [`separation-theorem-moonshot-plan.md`](separation-theorem-moonshot-plan.md) /
> [`birkhoff-ergodic-plan.md`](birkhoff-ergodic-plan.md) /
> [`channel-coding-shannon-theorem-full-plan.md`](channel-coding-shannon-theorem-full-plan.md)
> + [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md)
> + [`audit/audit-tags.md`](../audit/audit-tags.md).

## 要点
- 1 plan で 8 file を一括 sweep する形式 (各 file 1-2 件で per-file plan の overhead が本体を上回るため、Phase 0 inventory / audit / verify を共通骨格に集約、Phase 2.x のみ file 単位分離)。pilot 7 family の延長。
- 移行レシピ: load-bearing hypothesis を削除して結論型を保ち body を sorry 化 + `@residual(plan:<slug>)` (パターン P)。後継 unconditional 形が同 file 内にあり consumer 0 件なら retract-candidate 化 (closed-by-successor、sorry なし)。regularity hyp は precondition として残す。
- 空 slug `@audit:suspect()` (StationaryKernel) は slug 規約違反 → closed-by-successor 路線で救済。🟢ʰ prose marker (ContChannelMIDecomp 2 件) は incidental に genuine 散文へ書換。
