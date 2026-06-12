# EPI G2 de la Vallée-Poussin 機構自作 ムーンショット計画 🌙

**Status**: CLOSED ✅ — de la VP 判定法の汎用補題 (`unifIntegrable_of_superlinear_lintegral` + `Superlinear` 述語) を genuine 化し UI 壁を superlinear-moment 1 点に surface-shrink。本体 superlinear-moment 構成は別 sandwich/klFun-Fatou route で EPI G2 を一般形 genuine closure し、本 route は superseded。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) Phase B/C
> （その親: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md)）

## 要点 (≤5 行)

- 教訓: 退化定義罠 — `Tendsto (G·/·) atTop atTop` (`t : ℝ≥0∞`) は `atTop` が `{∞}` 主フィルタに潰れ空虚。非退化な閾値形 `Superlinear G := ∀ K, ∃ M, ∀ t, M ≤ t → K*t ≤ G t` を採用。
- 教訓: thin-tail counterexample — bounded density は peak 領域のみ closure、tail は sub-Gaussian 裾 (下限) に支配され boundedness と直交。最小十分条件は sub-Gaussian tail であって bounded density でない。
- 汎用 de la VP criterion は他 family / Mathlib upstream PR 候補として再利用可。
