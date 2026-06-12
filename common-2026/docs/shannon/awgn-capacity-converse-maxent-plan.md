# AWGN single-letter capacity converse (max-entropy 壁) closure 計画 🌙

**Status**: CLOSED ✅ — single-letter capacity converse の Mathlib gap を genuine closure (`awgn_capacity_closed_form_genuine` publish、独立監査 `@audit:ok`)。機械検証状態は SoT 参照。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §撤退ライン **F-3** の下流 (single-letter capacity converse の Mathlib gap closure)

## 要点 (将来作業で再利用しうる路)
- 主路 = `I(X;Y) = h(Y) − h(Y|X)` chain rule → Gaussian max-entropy 上界 + 分散評価 (Cover-Thomas 9.1 converse)。MI を直接押さえる DPI / variational 形は Mathlib 不在で不可。
- 依存 DAG の頂点 = output log-density 可積分性。self-derive 路: mixture 密度の二次優関数 `|log f_q| ≤ c₀ + c₁·y²` (上界 = Gaussian pdf sup、下界 = Chebyshev + Gaussian tail) + `q` 二次モーメント有限 + `Integrable.mono'`。
- 隣接壁 `awgn-per-letter-integrability` (n-letter joint marginal) は同型の mixture-density-lift 手法で closure 済。
- 計画外 fix: `awgnCapacity` constraint set の false-statement defect (Bochner `∫x²≤P` で非可積分入力が紛れ converse を偽に) → lintegral 形 `awgnPowerConstraintSet` に pivot。
