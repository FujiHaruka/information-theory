# Channel coding (Shannon) full theorem (D-1) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Cover-Thomas 7.7.1 完全形 `shannon_noisy_channel_coding_theorem`: `R < capacity W` (+ 正直な full-support `hW_pos`) で max-error 達成形を結論。固定 `p` 仮定除去 (入力分布最大化) + average→max (expurgation) + `hp_pos` 除去 (smoothing) を既存 achievability の wrapper として被せる。`hW_pos` 除去版は後継 D-1' / D-1'' で完成。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。
後継 (`hW_pos` 除去): [`channel-coding-shannon-theorem-full-plan.md`](./channel-coding-shannon-theorem-full-plan.md)

## 要点 (≤5 行)
- `capacity W := sSup {I(p; W).toReal | p ∈ stdSimplex}` (`ℝ` 値) — `lt_csSup_iff` で `R < C ⟹ ∃ p, R < I(p; W)` が直接出る、達成元存在は不要。
- MI の `p` 連続性は 3-entropy 展開 + `Real.continuous_negMulLog` で構成、capacity 達成は `IsCompact.exists_isMaxOn` (documentation only)。
- `hp_pos` 除去は smoothing `p_δ := (1-δ) p₀ + δ·uniform` で迂回 (sub-channel 切り出し経路は未使用)。
- expurgation = Markov on Finset (`Finset.card_filter_le`) で上位半分の max error 抽出、rate 損失 `log 2 / n → 0`。
