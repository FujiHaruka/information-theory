# D-1'' Phase D parent surgery — `h_passthrough` discharge ムーンショット計画 🌙

**Status**: CLOSED ✅ (UNCONDITIONAL) — `hW_pos` 完全除去版 `shannon_noisy_channel_coding_theorem_general_full` を publish: `R < capacity W` のみ (full-support 仮説も `h_passthrough` も無し、完全無条件) で max-error 達成形を結論。MVP 形 (`_general`、`h_passthrough` 形) は `@audit:retract-candidate(superseded-by-full-discharge)` に再分類済。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
親 plan (D-1' Phase A-C): [`channel-coding-shannon-theorem-general-plan.md`](./channel-coding-shannon-theorem-general-plan.md)
親 plan (D-1 full-support 形): [`channel-coding-shannon-theorem-plan.md`](./channel-coding-shannon-theorem-plan.md)

## 要点 (≤5 行)
- Two-layer smoothing: 入力側 `pSmooth p₀ δ_p` (n-独立) で `hp_pos`、channel 側 `Channel.smooth W δ_n` (`δ_n → 0`) で `hW_pos`。
- `δ_n := min(δ_B, ε/(8(n+1)))` — TV bound `2nδ_n < ε/2` を満たしつつ `V_max(δ_n) ≲ (log n)²` の polynomial decay (exponential decay は破綻)。
- parent body は existential N を返すため δ ごとの再呼出しが循環 → closed-form N(δ) を signature に export する inline copy が必須 (判断 #1)。
- 新規 Mathlib gap は 1 つ (mutualInfoOfChannel の (p, δ)-joint continuity) のみ、~50 行。
