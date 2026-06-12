# Shannon: Chernoff legacy-tag → sorry-based migration plan

**Status**: CLOSED ✅ — Chernoff family の legacy tag (`@audit:closed-by-successor` 主体 + 散文 🟢ʰ) を `sorry + @residual` honesty 強化 sweep の plan。3 sub-pattern (CS-honest / CS-false / CS-genuine-hyps) の decision tree + closed-by-successor migration recipe を確立。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11 + `docs/audit/audit-tags.md`。詳細履歴は git。
> **Parent**: [`chernoff-moonshot-plan.md`](chernoff-moonshot-plan.md)
> + [`chernoff-converse-moonshot-plan.md`](chernoff-converse-moonshot-plan.md)
> + [`chernoff-converse-sanov-discharge-plan.md`](chernoff-converse-sanov-discharge-plan.md)
> + 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)。

## 要点 (≤5 行)
- closed-by-successor migration の recipe を 3 sub-pattern に分岐: CS-honest (honest band-mass hyp) / CS-false (一般に偽の predicate 経由) / CS-genuine-hyps (claim hypothesis pass-through)。各 wrapper は signature から load-bearing hyp を削除 + body sorry + `@residual(plan:...)`。
- proof completion は後継 file (`ChernoffBandMassDischarge`) 内で regularity-only 完成済。本 sweep は consumer wrapper の honesty 強化のみ (predicate def 側は既存 tier 5 マーカー維持)。
- 一般に偽の predicate (`IsBayesErrorPerTiltLowerBound` / `IsChernoffNLetterRN` / `IsChernoffPerTiltDischargeable`) は著者が docstring で FALSE を明示済 — touch しない。
