# 多変量 differential entropy subadditivity discharge 計画

**Status**: CLOSED ✅ — 2 変数 + n 変数の subadditivity (`jointDifferentialEntropy_le_sum` / `jointDifferentialEntropyPi_le_sum`) を genuine 着地。Bayes density split の honest hyp を Mathlib density API + 自作 `withDensity_map_equiv` で discharge。

**SoT**: `docs/textbook-roadmap.md` Ch.8 (multivariate-diffentropy)。詳細履歴は git。

> **Parent**: (新規 family、近接 plan: [`differential-entropy-plan.md`](differential-entropy-plan.md) §E (1-D) / [`brunn-minkowski-closure-plan.md`](brunn-minkowski-closure-plan.md) §Phase 3 / [`parallel-gaussian-chain-rule-plan.md`](parallel-gaussian-chain-rule-plan.md) §撤退ライン D-1 / [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) §Phase B-0)

## 要点 (再利用可能)
- 2 変数 bridge は `prod_withDensity` + `rnDeriv_withDensity` + `rnDeriv_mul_rnDeriv` + `volume_eq_prod` (rfl) の chain で density split を genuine produce。KL ≥ 0 部分は元から genuine。
- structural bridge (KL → llr 積分 → log-density sum) は density split 抜きで genuine 化でき、壁を density split 1 点に局所化できる。density split を honest hyp に戻す bundling は禁止 (tier 5)。
- n 変数の壁は generic `withDensity_map` (Mathlib 不在) のみ。rnDeriv 特化版 (`MeasurableEmbedding.map_withDensity_rnDeriv`) を ~13 行で脱特化して self-build (誤診された「不在=不能」を覆した)。`pi_withDensity` は `measurePreserving_piFinSuccAbove` induction + `prod_withDensity` で構築。
- codomain は `Fin n → ℝ` / `ℝ × ℝ` を採用 (EuclideanSpace でなく) — product Lebesgue API と直結。
- AWGN 側 continuous-AEP (continuous SMB / n-dim entropy) は別系統で本 plan scope 外。
