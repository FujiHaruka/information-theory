# EPI case-1 difference G3 closure サブ計画 🌙

**Status**: CLOSED ✅ — case-1 (両 a.c. = 古典 EPI) を方針 X (a.c. + 有限分散 + 有限エントロピー precondition) で閉じる路の起草。中核の ratio+scaling saturation architecture (`EPICase1RatioLimit.lean`、entropic CLT 回避) を landing。general unconditional EPI は後継ルート群で達成済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Phase 3 (a.c. EPI core / case 1)

## 要点 (再利用可能な proof route / 判断軸)
- **ratio+scaling 挟み撃ちが entropic CLT を回避する鍵**: difference 経由を捨て、genuine ratio antitone を直接使い `R(0) ≥ lim_{t→∞} R(t) = 0` を組む。`R(t)→0` は分布収束→entropy 収束の一般持ち上げ (壁) でなく、scaling 恒等式 `entropyPower_map_mul_const` で t 因子を log 内で相殺し、各成分を独立ノイズ加算の単調性 (下界) + 分散→1 の最大エントロピー (上界) で両側 bound する。
- **difference 形は s=1 で pure Gaussian に有限端点 saturate / ratio 形は t=1 が Gaussian でなく t→∞ でしか saturate しない**: bridge body は difference アーキ (`heatFlowPath2 = √(1-s)X+√s Z`) を保つこと。ratio 化すると pure-Gaussian 端点を失う。
- **一般密度 Blachman は壁ではなかった**: 一般密度 producer が任意 a.c. 密度から per-t を供給するので、case-1 を block する Mathlib 壁はなく、残りは regularity precondition の供給/thread (load-bearing でない)。「producer 不在」の壁判定は producer landing が判定後だった drift だった。
- **joint-indep `hXYZXY` は under-hyp であって壁でない**: pairwise 独立からは出ない (4-tuple joint が要る)。grouping machinery (`indepFun_prodMk_prodMk`+`comp`) で product 構造から自己導出するか threaded hypothesis 化する。
