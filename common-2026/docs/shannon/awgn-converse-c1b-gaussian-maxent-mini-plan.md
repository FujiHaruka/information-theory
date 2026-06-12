# AWGN converse C-1b — per-letter Gaussian max-entropy 4 hyp 充足 mini 計画

**Status**: CLOSED ✅ — `awgn_per_letter_mi_le_log_var` を genuine closure (per-letter Gaussian max-entropy 4 hyp 充足)。機械検証状態は SoT 参照。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C」 C-1b 項

## 要点 (将来作業で再利用しうる路)
- 戦略: 「`h(Y_i) − h(Z_i)` 差分形」(F-2 bridge hyp で外注供給) + 「Gaussian max-entropy 4 hyp 形」(`differentialEntropy_le_gaussian_of_variance_le`) の 2 段組合せ。
- `perLetterYLaw` は mixture-of-Gaussians `(1/M) ∑ₘ gaussianReal (encoder m i) N` で、`gaussianReal_add_gaussianReal_of_indepFun` 直適用不可 (X_i marginal が discrete law) → AC / mean / variance helper は mixture 経由で self-derive。
- `Var(Y_i) = Var(X_i) + N ≤ E[X_i²] + N`、max-entropy `(v : ℝ≥0)` には `(perLetterInputSecondMoment + N).toNNReal` を渡す。
