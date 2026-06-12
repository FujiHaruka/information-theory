# Chernoff Information sandwich Tendsto ムーンショット計画 🌙 (T1-B 独立)

**Status**: CLOSED ✅ — Chernoff `Tendsto` headline を achievability (既存) + converse (hypothesis pass-through) + boundedness の sandwich で publish。converse は後継 plan で per-tilt 形まで縮減、最終的に regularity-only で genuine discharge 済。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。

## 要点 (≤5 行)
- `HoeffdingTradeoff` の hypothesis pass-through pattern と同型: achievability を黒箱再利用、converse + bdd-le を hypothesis として外出し (撤退ライン L-Ch1 / L-Ch2)、bdd-ge は internal discharge。
- 結論は `tendsto_of_le_liminf_of_limsup_le` 一発。DotEq corollary は `dotEq_iff_tendsto_log_div` 経由。
- 外出しした converse hypothesis はその後 sanov-discharge plan で discharge され、無条件 headline に到達。
