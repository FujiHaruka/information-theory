# EPI case 1 (両 a.c. = 古典 EPI): ratio chain の t→∞ 極限経路 feasibility 査定

**Status**: CLOSED ✅ — ratio chain を `csiszarLogRatioGap_tendsto_zero_atTop` (t→∞ 極限補題) で閉じる路の feasibility 査定。当初 NO-GO 判定 (entropic CLT 壁) は後の scaling 簡約発見で覆り、後継 closure plan (`epi-case1-difference-g3-closure-plan`) が genuine な R(t)→0 squeeze で本路を実現。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A-close
> **関連**: [`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md)

## 要点 (再利用可能な判断軸)
- **本査定の NO-GO は over-pessimism だった**: 「ratio t→∞ は entropic CLT 級の壁」判定は √t スケーリング簡約を omit していた。scaling 恒等式で t 因子を log 内相殺し、独立ノイズ加算の単調性 (下界) + 分散→1 の最大エントロピー (上界) で両側 squeeze すれば、分布収束→entropy 収束の一般持ち上げを経ずに `R(t)→0` が genuine に組める。「分布収束に entropy が非連続」は一般論としては正しいが、この特殊 path では sandwich で回避できる — 壁判定の前に必ず代替ルートを 1 本探す原則の実例。
- **antitone の domain が `Set.Ici 0` (全 ray) なので t→∞ 経路に好都合**: closed interval `Icc 0 1` でなく、antitone + 極限 `lim_{t→∞} R(t)=0` から `R(0) ≥ 0` が純 order 議論 (`ge_of_tendsto`) で出る。
