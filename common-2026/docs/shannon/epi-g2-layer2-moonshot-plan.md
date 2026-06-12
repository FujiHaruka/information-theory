# EPI G2: 層2 (エントロピー汎関数への持ち上げ) ムーンショットサブ計画 🌙

**Status**: CLOSED ✅ — 層2 machinery (列化 + Vitali + L¹→積分) を `volume` 上 genuine 化し、壁を密度 L¹ 収束 (近似単位元) に surface-shrink。最終的に sandwich route で一般形 genuine 完成。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-g2-continuity-plan.md`](epi-g2-continuity-plan.md) §「Route B — machinery 自前構築」

## 要点 (≤5 行)

- 確定 positive: 層2 Vitali / L¹→積分 machinery は `[IsFiniteMeasure]` 非要求で無限測度 `volume` on ℝ で通る (壁は machinery でなく入力側に局在) — 再利用判断軸。
- `MemLp (negMulLog pX) 1 volume` (= h(X) 有限) は L¹+2次モーメントから出ない → precondition 追加 (regularity、非 load-bearing) が正規対処。
- 3 Vitali witness 精密設計は [`epi-g2-vitali-closure-plan.md`](epi-g2-vitali-closure-plan.md) に分離。
