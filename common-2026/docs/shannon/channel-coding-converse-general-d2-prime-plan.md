# Channel coding converse — memoryless per-summand bound (D-2') ムーンショット計画 🌙

**Status**: CLOSED ✅ (PASS-THROUGH) — Cover-Thomas 7.9 一般入力 converse の memoryless ⇒ per-summand bound 形を publish (`channel_coding_converse_general_memoryless`)。3 仮説 (`h_yother_zero` / `h_split` / `h_markov_xprefix`) を pass-through で受け取る形。これらの `IsMemorylessChannel` からの内部派生 (= pure 形) は後継 ychain サブ計画で完成。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
後継 (pure 形): [`channel-coding-converse-memoryless-ychain-plan.md`](./channel-coding-converse-memoryless-ychain-plan.md)
親 plan (D-2): [`channel-coding-converse-general-plan.md`](./channel-coding-converse-general-plan.md)

## 要点 (≤5 行)
- E-10' (feedback per-letter bound) と同型だが LHS = `I(X_i; Y^n | X^{<i})` で Y^n n 変数分割が必要。
- 新規補題: `condMutualInfo_chain_rule_X_2var` / `_Y_2var` (条件付き chain rule、X/Y 軸 2 変数)。
- Step 3 で一般 `condMI ≤ MI` を回避 — 一般には不成立、Markov chain + chain rule + nonneg で迂回。
