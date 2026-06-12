# Shannon EPI: `wall:fisher-finiteness` closure 計画

**Status**: CLOSED ✅ — Ch.17 Inequalities / EPI closure の一部として handled。Stam convolution Fisher bound (`J(pX∗g_s) ≤ 1/s`) を shared sorry 補題 `gaussianConv_fisher_le_inv_var` に集約し EPI per-time line の 3 consumer を gate する設計は決着済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: per-time de Bruijn line (`FisherInfoV2DeBruijnAssembly`)。

## 要点
- `@residual(wall:fisher-finiteness)` は依然コード側 SoT の生きた slug (`FisherConvBound.lean` の `gaussianConv_fisher_le_inv_var` 集約点 + per-time line consumer)。詳細は code タグ参照。
- 推奨 route は Stam 凸 Fisher 上界 (density-level score Cauchy-Schwarz → λ→0 極限 → 有限性→可積分性の純 plumbing)。核は density-level score-of-convolution Cauchy-Schwarz で、`stam-step2-density` 核との重複度が PR スコープを左右する最大の不確実性。
- shared 補題は regularity 引数のみで結論 `≤ 1/s` が core (load-bearing なし)。consumer は lemma call で受け、壁 closure で一斉 genuine 化する。
