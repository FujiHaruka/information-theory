# 無限分散 a.c. 古典 EPI 構築 — truncation ルート moonshot 計画 🌙

**Status**: CLOSED ✅ — 無限分散 a.c. 古典 EPI を route T (conditioning truncation + Gibbs + DCT で crux usc を閉じ R→∞) で genuine closure。`wall:epi-infinite-variance-classical` は FALSE WALL (sharp Young/Brascamp-Lieb 不要) と判明し general unconditional EPI を完成。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。
**親**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md)

## 要点 (≤5 行)
- slug `@residual(wall:epi-infinite-variance-classical)` はコード残存だが本ルートで body は genuine 化済 (wall は他 dispatch 配線の参照に残る、linter 不検知)。
- 採用ルート T の核 (再利用判断軸): 有限分散 EPI を黒箱再利用し `X_R = X|{|X|≤R}` (compact support → 有限分散+有限エントロピー+a.c. 保存 via `cond_absolutelyContinuous`) に適用 → R→∞。素朴 indicator truncation は law に atom を作り a.c. を壊すので conditioning を採る。
- crux usc 機構: 優関数 `p_R∗q_R ≤ C²(p∗q)` (a.c. + DCT 両供給) + Gibbs (`toReal_klDiv_of_measure_eq`、template `differentialEntropy_le_gaussian_of_variance_le` を一般参照 generalize) + cross-entropy DCT。分散発散は red herring。
- 教訓: closure mechanism は実装前に proof-pivot-advisor で numerics 検算 (analytic 壁の標準手順) — feasibility gate で usc が FALSE WALL と確定したことが route T 採用の決め手。
