# Brunn-Minkowski (entropy form) `from EPI` discharge 計画 🌙

**Status**: CLOSED ✅ — Ch.17 Inequalities は EPI closure の一部として handled。本 plan が起草した EPI route (1-D EPI → n-dim EPI → CT 17.7.4 bridge → entropy 形 BM) は実装に至らず、BM entropy 形は別 route で着地済。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`brunn-minkowski-moonshot-plan.md`](brunn-minkowski-moonshot-plan.md) §残① / "撤退ラインの discharge 想定 L-BM1"

## 要点
- L-BM1 (BM entropy 形) には直交する 2 route があった: closure plan の Fubini 直接路 (Mathlib 壁不在) と本 plan の EPI route (CT 教科書順整合)。closure 経路が成功したため EPI route は撤退候補。
- EPI route は 1-D EPI の Stam 残仮定を n-dim へ propagate する設計で、stand-alone closure ではなく Stam 解析に transitively 依存する点が主な判断軸だった。
