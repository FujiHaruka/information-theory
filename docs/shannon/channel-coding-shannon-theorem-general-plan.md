# Channel coding (Shannon) full theorem — `hW_pos` 緩和 (D-1') ムーンショット計画 🌙

**Status**: CLOSED ✅ — smoothing infrastructure (`Channel.smooth` + TV bound `2 n δ`) を publish。`hW_pos` 除去版主定理は後継 D-1'' で完全 discharge 済。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。

## 要点 (任意, ≤5 行)
- 経路: `W_smooth W δ := (1-δ)·W + δ·uniform` で full support 化 → 既存 D-1 を黒箱適用 → `δ→0⁺` の TV bound で一般 W に持ち上げ。
- 二重 limit (δ, n) は TV tensorization (`‖pi(W_smooth δ) − pi(W)‖ ≤ n δ`) で `K=n` 線型に落として回避。
- 主定理本体は本 plan から削除し、parent surgery 込みの D-1'' へ移管 (uniform-N bound が本 plan budget 外だったため)。
