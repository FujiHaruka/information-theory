# AWGN F-1/F-3 撤退ライン peer 同時第一選択 migration plan 🌙

**Status**: CLOSED ✅ — `IsAwgnTypicalityHypothesis` (F-1) + `IsAwgnConverseHypothesis` (F-3) を predicate 削除 + wrapper body `sorry` + `@residual(plan:...)` に第一選択 migration (Tier 5 circular → Tier 2)。F-2/F-3 verbatim-equivalent alias 2 件も削除。後続の analytic discharge plan が body を埋めて Tier 1 へ。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) §「撤退ライン F-1/F-3」

## 要点 (将来作業で再利用しうる路)
- peer の構造的対称性を活かし 1 PR 統合 sweep: predicate 削除 → wrapper signature の hyp 1 本削除 + body sorry 化 → downstream wrapper の thread 連動修正 (~9 file 横断)。F-1 → F-3 sequential (共通 downstream 7 file が衝突するため並列不可)。
- 注意点: `AWGNAchievabilityDischarge.lean` の `isAwgnTypicalityHypothesis` constructor は predicate を return type として消費 → predicate 削除時は結論型 inline 展開 / theorem 削除の判定が必要。
- 本 plan は honesty 強化のみ (circular def を消す)、proof completion ではない。
