# Shannon: Cramér `@audit:suspect` → sorry-based migration plan

**Status**: CLOSED ✅ — Cramér family の legacy `@audit:suspect` 語彙を sorry-based に移行する sweep 完遂。新規 proof completion ではなく honesty 強化が目的の workstream で、Cramér Phase B/C の Mathlib gap closure は scope 外のまま archival。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。
> **Parent**: [`cramer-moonshot-plan.md`](cramer-moonshot-plan.md) §Phase B/C/D

## 要点 (≤5 行)
- 残 residual は `plan:` slug で揃える方針 (`cramer-moonshot-plan` / `cramer-lc2-discharge-moonshot-plan` / `cramer-chernoff-clt-closure-moonshot-plan`)。新 wall 命名 (`infinite-pi-tilted-rn`) は見送り、shared sorry 補題への集約もしない。
- 3 つの load-bearing predicate (`IsMeasureInfinitePiTiltedEq` / `IsCramerNLetterRNCylinder` / `IsCaratheodoryExtensionHyp`) は `@audit:retract-candidate(load-bearing-predicate)` 付きで残す (hypothesis-form consumer は 0、producer/projection は transitive sorry)。
- `IsCramerChernoffNLetterRNUnified` structure の retract 判断は Chernoff family sweep との順序依存のため保留 (L-MIG-2)。
- `cramer_lower_at` の sorry 化で headline `cramer_lower_at_cgfDeriv_unconditional` が transitive sorry に降格 (constructive 経路の毀損リスク = L-MIG-3、デフォルト sweep で適用済)。rewrite recovery は `cramer_lower` も sorry のため不可と判定。
