# Entropy Power Inequality (T2-D) ムーンショット計画 🌙

**Status**: CLOSED ✅ — EPI signature + entropyPower 定義 + Gaussian saturation case を publish した最初の足場。一般 EPI は後続 sub-plan 群で unconditional に discharge 済 (Ch.17 row ✅ DONE)。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-D. Entropy Power Inequality」
>
> **Predecessor**:
> - T2-A `AWGN.lean` (pass-through publish)
> - T2-F `FisherInfo.lean` + `FisherInfoGaussian.lean`
> - E-9 `DifferentialEntropy.lean` (Gaussian entropy + max entropy)

## 要点 (frozen 参照点)

- **凍結スラグ L-EPI1 / L-EPI2 / L-EPI3** (Stam inequality / de Bruijn integration / EPI conclusion の撤退ライン三本立て) は本 plan が初出で、`docs/moonshot-seeds.md` ほか複数 sub-plan / inventory から参照される。番号は凍結 (削除・再番号しない)。
- 一般 EPI discharge は 3 sub-plan に分割済 (Stam discharge / de Bruijn integration / stam-to-conclusion)。本 plan は history record。
- entropyPower 定義は `Real.exp (2 * differentialEntropy μ)` 形を採用 (Mathlib-shape-driven、`(2πe)` 係数は scaling corollary 吸収)。
