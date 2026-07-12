# Rate-distortion theorem achievability ムーンショット計画 🌙

**Status**: CLOSED ✅ — Phase A-E すべて landing 済。headline `rate_distortion_achievability` を strong-typicality track で publish 済。`R(D)` 定義 (`RDConstraint` / `mutualInfoPmf` / `rateDistortionFunctionPmf`) + 達成性 + 連続性 + 単調性も完成。**無条件 operational 形 `rate_distortion_achievability_operational` も closure 済** (pass-through 仮説を全 discharge、[unconditional](rate-distortion-achievability-unconditional-plan.md) CLOSED ✅、`@audit:ok`)。
**SoT**: `docs/textbook-roadmap.md` Ch.10。詳細履歴は git。

## 要点 (任意, ≤5 行)
- `R(D)` は test-channel 形でなく joint dist `q ∈ stdSimplex ℝ (α × β)` 側で定義 (CsiszarProjection の stdSimplex machinery 再利用、constraint が linear)。
- `mutualInfoPmf q := H(fst) + H(snd) − H(q)` (negMulLog 経由 entropy 形)。KL/log 比形は marginal 0 境界で連続性が崩れるため不採用。
- `rateDistortionFunctionPmf := sInf (mutualInfoPmf '' RDConstraint)` (binder-`⨅` は ℝ の CCL で BddBelow 副条件で詰まるため image-sInf 形)。
- 経路は Cover-Thomas 10.5 random codebook + joint typical encoder の lossy mirror。strong-typicality 詳細は phase-e-strong サブ計画参照。

## Sub-plan 一覧
- [phase-e-strong](rate-distortion-achievability-phase-e-strong-plan.md) — E-3''' fully-discharged (CLOSED ✅)
- [unconditional](rate-distortion-achievability-unconditional-plan.md) — headline の honest pass-through 仮説を discharge しクリーンな operational 文へ (CLOSED ✅ `rate_distortion_achievability_operational`)
