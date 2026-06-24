# Cramér L-C2 discharge ムーンショット計画 🌙 (T1-C follow-up)

**Status**: CLOSED ✅ — `cramer_lower` の `h_tilted_lower` を tilted IID plumbing + Mathlib LLN で discharge する plan。Phase A (tilted ambient n-IID 構成) のみ自身で publish (L-D3 撤退)、Phase B/C は後継チェーン (cramer-lc2-ext → infinitepi-tilted → cramer-chernoff-clt-closure) で実質達成。sorry-based 移行も完了済。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。
> **Parent**: [`cramer-moonshot-plan.md`](cramer-moonshot-plan.md) §Phase C (L-C2 撤退記録) + §撤退ライン L-C2

## 要点 (≤5 行)
- 戦略: 親 plan の `h_tilted_lower` を「tilted ambient 下 n-IID + `strong_law_ae_real` + Cramér change-of-measure」の 3 段で構成。tilted single の infinitePi 乗積測度を ambient に据える。
- L-D3 撤退理由: Phase B の `strong_law_ae_real` 起動で `IsProbabilityMeasure (Measure.infinitePi (fun _ => μ.tilted ...))` の型クラス検索が repeatedly stuck (Lean instance synthesis の beta reduction 不安定)。Phase A scaffolding を独立 infrastructure として publish して着地。
- load-bearing predicate `IsMeasureInfinitePiTiltedEq` には `@audit:retract-candidate(load-bearing-predicate)` 付与 (コード側 SoT、現存)。
