# Shannon: RateDistortion + ParallelGaussianPerCoord `@audit:suspect` / `@audit:closed-by-successor` → sorry-based migration plan

**Status**: CLOSED ✅ — RateDistortion (6 decl) + PGPC (5 closed-by-successor) の legacy `@audit:suspect()` / `@audit:closed-by-successor` 語彙を honesty 強化 (sorry-based / タグ削除) で整理する独立 workstream。proof completion は対象外、各親 plan の defer 状態は不変。
**SoT**: `docs/textbook-roadmap.md` Ch.10。詳細履歴は git。
> **Parents**:
> - RateDistortion 系: [`rate-distortion-achievability-plan.md`](rate-distortion-achievability-plan.md) /
>   [`rate-distortion-achievability-phase-e-strong-plan.md`](rate-distortion-achievability-phase-e-strong-plan.md) /
>   [`rate-distortion-convexity-plan.md`](rate-distortion-convexity-plan.md) /
>   [`rate-distortion-converse-plan.md`](rate-distortion-converse-plan.md)
> - PGPC 系: [`parallel-gaussian-l-pg1-discharge-plan.md`](parallel-gaussian-l-pg1-discharge-plan.md) /
>   [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md)
>
> SoT: [`../audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) + [`../audit/audit-tags.md`](../audit/audit-tags.md)。Pilot reference: [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md)。

## 要点 (任意, ≤5 行)
- 移行レシピ 3 パターン: P (load-bearing predicate hyp 削除 + sorry+`@residual(plan:<slug>)`) / V (regularity pass-through、タグ削除のみ) / S (PGPC superseded-by-completed-plan、タグ削除のみ)。
- 空 slug `@audit:suspect()` の closure 担当 plan は declaration 単位 verbatim 確認 + 親 plan match で確定 (複数候補があるため一括 shared lemma 化しない)。
- PGPC は EPI/Stam に依存しない (Round 3 dependency 仮定を import 逆検証で否定) → 独立 sweep 可能。
- `@audit:closed-by-successor(SLUG)` の後継 plan 完結後の扱い: 同 file に sorry あれば `@residual(plan:<SLUG>)` 置換、無ければタグ削除。
