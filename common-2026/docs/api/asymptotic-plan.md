# I-3 Asymptotic / Exponent Framework サブ計画

**Status**: CLOSED ✅ — `InformationTheory/Asymptotic.lean` に `DotEq`（`≐` notation）+ 基本性質 + `dotEq_iff_tendsto_log_div` bridge + `exp_decay_N_of_pos` rate extraction wrapper を実装。Phase 1〜4 完了。
**SoT**: `docs/textbook-roadmap.md` §「Tier ∞ — Infrastructure」。詳細履歴は git。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §「Tier ∞ — Infrastructure / I-3. Asymptotic / exponent framework」
> **Mathlib inventory**: [`asymptotic-mathlib-inventory.md`](asymptotic-mathlib-inventory.md)

## 要点 (≤5 行)
- `DotEq a b := (log∘a − log∘b) =o[atTop] (·:ℝ)`（候補 B = `IsLittleO`）。InformationTheory inline の `ℝ` 値表現と型がマッチ。
- notation `≐`（U+2250）は `scoped[InformationTheory.Asymptotic]`、operand precedence 51（`Iff` 右辺パース回避）。
- positivity は述語に組み込まず use site で渡す。`DotEq.inv` は `Real.log_inv` 無条件成立により `hPos` 不要と判明。
- `exp_decay_N_of_pos` は既存 `AEPRate.exp_neg_mul_lt_of_rate` の family-agnostic 版（callsite migration は範囲外、既存 inline は不変）。
