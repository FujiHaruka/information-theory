# Chernoff Information + Hoeffding Tradeoff ムーンショット計画 🌙 (T1-B + T1-D)

**Status**: CLOSED ✅ — Chernoff achievability (rate-side lower bound) + Chernoff/Hoeffding 定義・凸性・min 達成性・一意性を publish。converse side と Hoeffding tradeoff `Tendsto` 形は後継 plan へ分離 (scope 縮退 L-S1 / L-S2)。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。

## 要点 (≤5 行)
- `chernoffInfo` / `hoeffdingE2` は textbook 形でなく pmf 形 (`α → ℝ`) で統一 publish。Mathlib `Measure.tilted` への lift は後段 (Sanov LDP per-tilt) 着手時のみ必要。
- achievability は per-point Hölder degenerate (`min ≤ a^{1-λ}·b^λ`) + n-IID sum reshape で Measure plumbing 不要に閉じた。
- `logZ` 凸性は `Set.Ioo 0 1` 内部で Hölder 起動 + 端点別 case。Hoeffding min 達成性は Csiszar projection の直接適用。
- converse は Sanov LDP per-tilt + pmf↔Measure bridge が必要なため別 plan に defer (後に sanov-discharge plan で genuine 完成)。
