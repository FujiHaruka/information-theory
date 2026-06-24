# SMB: 2-sided stationary extension `μ_ℤ` サブ計画 🌙

**Status**: CLOSED ✅ — 2-sided 定常拡張 `μZ : Measure (ℤ → α)` 完成 (`TwoSidedExtension.lean`、real-sorry 0)。主要 decl: `μZ` / `shiftZ` + `measurePreserving_shiftZ` / `ergodic_shiftZ` / `natProj` + `measurePreserving_natProj` / `forwardEmbed`。無条件 `shannon_mcmillan_breiman` の `liminf ≥ entropyRate` 段 (`algoet_cover_liminf_bound`) を支える。全 Phase M0–H 達成。
**SoT**: `docs/textbook-roadmap.md` Ch.4 (SMB)。詳細履歴は git。
**Parent**: [`shannon-mcmillan-breiman-phase-d-plan.md`](shannon-mcmillan-breiman-phase-d-plan.md) §"残: Algoet–Cover sandwich" `h_liminf` 段

## 要点 (≤5 行)
- Route A (Hahn-Kolmogorov on cylinder semiring): shifted finite-marginal の projective family → `projectiveFamilyContent` → `AddContent.measure` で Carathéodory 拡張。Route B (Ionescu-Tulcea backward via Bayes kernel inversion) は non-Markov reverse kernel が delicate で却下。
- σ-additivity は Fintype α ⇒ `ℤ → α` compact ⇒ closedCompactCylinders 経由の有限交差性で自動成立 (本サブ計画 最大の山場 Phase C)。Mathlib `infinitePi` pipeline がテンプレ。
- backward filtration は `MeasurableSpace.cylinderEvents {i : ℤ | i ≤ -k}` で直接取得、Levy downward は本プロジェクト `BackwardMartingale.ae_tendsto` を流用。
- ergodicity transfer (Phase E.4) は coupling (Phase F) 経由で `(Ω, T, μ)` 側から push する cross-phase 依存。

## 参考
- E-8 主 plan: [`shannon-mcmillan-breiman-plan.md`](shannon-mcmillan-breiman-plan.md)
- Algoet–Cover (1988) "A sandwich proof of the Shannon-McMillan-Breiman theorem" (Annals of Probability) — lower bound direction
