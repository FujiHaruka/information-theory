# EPI per-time de Bruijn identity — closure サブ計画

**Status**: CLOSED ✅ — per-time de Bruijn identity (density 同定 → heat equation → parametric diff → 無限区間 IBP → fisher congr) を general `X` で genuine 化し、general EPI closure に寄与。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
**Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md)

## 要点 (≤5 行)
- slug `@residual(plan:epi-debruijn-pertime-closure)` + 共有壁 `@residual(wall:fisher-finiteness)` (convolution Fisher bound、Mathlib/repo 不在) はコード残存 (linter 不検知)。
- 解析核は density-route の atom 分解で積む。真壁は Fisher integrability 1 本のみ (Stam convolution Fisher bound) で共有壁 `gaussianConv_fisher_le_inv_var` に局所化。
- 再利用判断軸: convolution envelope の integrability は Tonelli で moment 側に流すのが正路 (pointwise closed-form `x^k·exp(-x²/c)` 経由は heavy-tail pX で破綻)。closure mechanism は実装前に numerics 検算。
- honesty 教訓: lemma 結論形 (`g_s ≤ pref(s)` の x-定数化等) の verbatim 確認は数式論法にも必須。sorry 分割先が false だと「genuine plumbing 化」ラベルが defect を隠蔽し得る。
