# Channel coding converse — pure `IsMemorylessChannel` form via Strong wrapper (D-2'' γ-chain bridge) サブ計画

**Status**: CLOSED ✅ — `IsMemorylessChannel` **単独** (pass-through Prop 仮説なし) で pure 形 `channel_coding_converse_general_memoryless_pure` を publish。内部で `IsMemorylessChannelStrong` を bridge 補題 2 本 (`per_letter_markov_of_memoryless` + `outputs_cond_indep_of_memoryless`) で派生し既存 `_strong` wrapper を呼ぶ。これで親 D-2'' の deferred を解消。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
> **Parent**: [`channel-coding-converse-d2-doubleprime-plan.md`](./channel-coding-converse-d2-doubleprime-plan.md) (deferred), [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md)

## 要点 (≤5 行)
- 核心: Strong axiom (`per_letter_markov` + `outputs_cond_indep`) は γ-form `(X^{≠i}, Y^{≠i}) → X_i → Y_i` から graphoid (marginalize + weak union) で構造的に導出可能、`h_yother_zero` を経由しないので encoder degenerate 反例にも頑健。
- `[StandardBorelSpace Ω]` を追加せず γ-form 直経路で通した (既存 `_strong` との signature 互換維持)。
- graphoid 補題 (drop-right-in-left / weak-union-middle) は将来 feedback 系 / Slepian-Wolf bridge で再利用余地あり。
