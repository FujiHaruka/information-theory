# Cramér family — settled-facts ledger

> 列 = claim / confidence / 再検証コマンド / last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証) / `loogle-neg` (Found 0) / `human-judgment` (低信頼、独立 pivot で再確認)。
> プラン散文に settled fact をキャッシュせず、ここにリンクする (re-derive > cache)。

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| `CramerCltBoundaryClosure.lean` の headline 群 (`cramer_lower_boundary_unconditional`, `cramer_lower_boundary`, `boundary_liminf_lower_of_eps`, `tiltedWindow_eventually_large_of_boundary`, `tilted_halfline_tendsto_gaussian`, `tilted_halfline_tendsto_half`, `gaussianReal_Ici_eq_half` 他、計 10 decl) は sorryAx-free | machine | `lake env lean InformationTheory/Shannon/CramerCltBoundaryClosure.lean` (silent) + `#print axioms cramer_lower_boundary_unconditional` (= `[propext, Classical.choice, Quot.sound]`) | `9cdc485` | CLT-boundary closure moonshot 達成 (Phase 1-6, 独立監査 `@audit:ok` 全 10)。roadmap 判断ログ #25 / 子 plan `cramer-chernoff-clt-closure-moonshot-plan.md` 判断ログ #4 |
| `gaussianReal_Ici_eq_half` (Gaussian median 1/2) は Mathlib 不在 | loogle-neg | `loogle "ProbabilityTheory.gaussianReal, Set.Ici"` (Found 0)、median パターンも 0 | `1a19915` | symmetry-by-map (`gaussianReal_map_neg` + `noAtoms_gaussianReal`) で自作、~62 行。Mathlib PR 候補 |
| consumer root `cramer_lower_phaseC_partial_discharge` (`Draft/Shannon/CramerLC2PhaseC.lean:165`) は依然 body=`sorry` | machine | `rg -n "sorry" InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean` | `9cdc485` | **closed-but-unwired**: 上の closure asset が穴を埋める genuine 資産 (結論形 verbatim 一致、監査確認済) だが **import cycle** (`CramerLC2PhaseC` ← `InfinitePiTiltedChangeOfMeasure` ← closure file) で in-place 書換不可。root の `@residual(plan:cramer-chernoff-clt-closure-moonshot-plan)` は「閉じた closure を指す live residual」。差し替え経路は別 plan |
