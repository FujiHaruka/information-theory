# Channel coding converse — pure memoryless per-summand bound (D-2'') ムーンショット計画 🌙

**Status**: CLOSED ✅ (SUPERSEDED) — 当初 `h_yother_zero` を `IsMemorylessChannel` 単独から派生する経路を狙ったが、これは encoder degenerate で数学的に偽と判明し deferred。後継 ychain サブ計画が encoder-agnostic な Strong 経路 (graphoid weak union) で bypass し pure 形 `channel_coding_converse_general_memoryless_pure` を完成。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
後継 (完成形): [`channel-coding-converse-memoryless-ychain-plan.md`](./channel-coding-converse-memoryless-ychain-plan.md)
親 plan (D-2'): [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md)

## 要点 (≤5 行)
- `h_yother_zero` (= `condMI(X_i; Y^{≠i} | (X^{<i}, Y_i)) = 0`) は encoder 任意では偽 — per-summand 経路の本質的な落とし穴。
- 正解は per-summand bound を経由せず Cover-Thomas Thm 7.9 のエントロピー劣加法 (Strong 経路) を通すこと。
- 本セッションで CondMutualInfo の reshape API + Markov 左 post-processing を整備し ychain 後継に引き継いだ。
