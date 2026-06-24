# DMC feedback per-letter bound (E-10') ムーンショット計画 🌙

**Status**: CLOSED ✅ — `feedback_per_letter_bound` (`I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`) を memoryless 性 + 因果性のみから導出。親 E-10 の `h_per_letter` 仮定を剥がし Cover-Thomas 7.12 を完全形で完走。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
> **親**: [`dmc-feedback-capacity-plan.md`](./dmc-feedback-capacity-plan.md)

## 要点 (任意, ≤5 行)
- memoryless 性を 3 変数 Markov chain `(Msg, Y^{<i}) → X_i → Y_i` (`IsMemorylessFeedback`) に reformulate → 既存 `mutualInfo_le_of_markov` 1 段 + chain rule + `mutualInfo_nonneg` で完走 (CondMutualInfo.lean 新規補題ゼロ)。
- Phase A の RV 順を chain rule LHS `(Y^{<i}, Msg)` に揃えたことで Step 3 の左 RV swap が 0 行に。
