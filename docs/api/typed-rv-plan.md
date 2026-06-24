# I-1 Typed Random Variable API サブ計画

**Status**: CLOSED ✅ — `InformationTheory/Shannon/TypedRV.lean` に `klDivRV` / `differentialEntropyRV` / `condEntropy` re-export + notation 5 つ + `_def` lemma + typed-form 主補題層を実装。Phase 1〜5 完了。
**SoT**: `docs/textbook-roadmap.md` §「Tier ∞ — Infrastructure」。詳細履歴は git。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §「Tier ∞ — Infrastructure / I-1. Typed Random Variable API」
> **Mathlib inventory**: [`typed-rv-mathlib-inventory.md`](typed-rv-mathlib-inventory.md)

## 要点 (≤5 行)
- `klDivRV` は 1 測度版のみ publish（2 測度版は後付）。全 alias は既存 measure-form への薄い wrapper（新数学なし）。
- notation は `scoped[InformationTheory.Shannon] notation3` precedence `:max`（`≤` 右辺パース回避）、`μ` placeholder 不可のため `μ` 明示形に縮退（`H(μ; X)` 等）。`D` の区切りは `∥`（U+2225、norm `‖` 衝突回避）。
- callsite migration は範囲外（既存 `entropy μ X` 形は不変、opt-in な notation 層）。
- Phase 5 で typed-form 主補題（`mutualInfo_comm_rv` 等）を `_rv` suffix で追加、衝突なしは無印再公開。
