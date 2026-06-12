# Parallel Gaussian ② converse — #5 joint log-density integrability closure サブ計画

**Status**: CLOSED ✅ — joint output log-density integrability (`parallelOutput_joint_logDensity_integrable`) を genuine 着地、converse の唯一残 residual #5 を解消、headline 含め proof done。

**SoT**: `docs/textbook-roadmap.md` Ch.9 (parallel-gaussian) + `docs/shannon/awgn-facts.md`。詳細履歴は git。

> **Parent**: [`parallel-gaussian-converse-closure-plan.md`](parallel-gaussian-converse-closure-plan.md)

## 要点 (再利用可能)
- core 戦略は 1-D AWGN mixture log-density integrability の座標積 (`Fin n`) 持ち上げ — 新規数学ゼロ。
- joint mixture density は入力 `p` の絶対連続性を使わず (`SFinite p` のみ、Tonelli が `p` 非依存) 閉形で書けるため、相関入力でも withDensity 手定義ルートで成立。`rnDeriv` の積 factor 不能とは別物 (旧 wall 主張の混同点)。
- 集中集合は ball でなく座標箱 (`Fin n → ℝ` の norm は sup norm ≠ L2)、quadratic majorant は座標和で立てる。
