# EPI G2: 3 Vitali witness 閉鎖 (UI / UT / ae) サブ計画

**Status**: CLOSED ✅ — ae witness は部分列ルートで genuine 除去、UT は 2次モーメント tail で closure。UI の de la VP core は別ルート (sandwich/klFun-Fatou) で最終的に EPI G2 端点連続性が一般形 genuine 完成し、本 witness ルートは superseded。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-g2-layer2-moonshot-plan.md`](epi-g2-layer2-moonshot-plan.md) §Phase 1/2

## 要点 (≤5 行)

- 確定 positive: `mul_meas_ge_le_lintegral` は測度非依存で `volume` 上 Chebyshev 回避の核 (`meas_ge_le_variance_div_sq` は `[IsFiniteMeasure]` 要求で不可) — UT 再利用判断軸。
- 教訓: parked sorry でも signature が偽を主張していたら honesty defect (`hu_bdd : BddAbove (Set.range u)` 欠落で UnifTight/UnifIntegrable が genuine に偽だった under-hypothesized 例)。
- ae の full列 vs 部分列 gap は `tendsto_of_subseq_tendsto` を層2 で直接使う第三の道で迂回 (Mathlib 自身の同 device 流用)。
