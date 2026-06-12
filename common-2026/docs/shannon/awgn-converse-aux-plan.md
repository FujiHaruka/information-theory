# AWGN Converse aux — F-3 analytic discharge ムーンショット計画 🌙

**Status**: CLOSED ✅ — Cover-Thomas 9.1.2 converse (Fano + DPI + memoryless chain + per-letter Gaussian max-entropy) を `AWGNConverseDischarge.lean` に publish。`awgn_converse` body は `awgn_converse_F3_discharged` への 1 行 `exact` で discharge、file scope proof done。残存 sorry は子 mini-plan (c1b / c1c / c5) で回収。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-3」。
> **子 mini-plan**: [`awgn-converse-c1b-gaussian-maxent-mini-plan.md`](awgn-converse-c1b-gaussian-maxent-mini-plan.md) / [`awgn-converse-c1c-jensen-mini-plan.md`](awgn-converse-c1c-jensen-mini-plan.md) / [`awgn-converse-c5-mi-finite-bridge-mini-plan.md`](awgn-converse-c5-mi-finite-bridge-mini-plan.md)

## 要点 (将来作業で再利用しうる路)
- 最大圧縮: `shannon_converse_single_shot` (`Converse.lean`) が Fano + DPI postprocess + entropy chain + `H(W uniform)=log M` を 1 補題に packaging 済 (Y 側無制約) → Fano 段が 1 行呼出。
- per-letter Gaussian max-entropy = `differentialEntropy_le_gaussian_of_variance_le` 4-hyp 形。DPI continuous は `mutualInfo_le_of_markov` で genuine 化可。
- 計画外 fix: per-letter `E[X_i²] ≤ P` 形が AWGN per-message block constraint から genuine 化不能 (false-statement defect) → sum-form + Jensen 構造で直接 publish に再設計、`awgn_per_letter_mi_le_capacity` 撤回。
- `AWGNConverse.lean:70` 置換は `AWGNMain.lean` とセットで実施 (`awgn-main-converse-wiring-mini-plan.md`)。`awgn_converse` 採用 tag = `@audit:closed-by-successor`。
