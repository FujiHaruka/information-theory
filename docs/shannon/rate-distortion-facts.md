# Rate-distortion family — settled-facts ledger

> family `rate-distortion` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> 列 = claim / confidence / 再検証コマンド / last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) / `human-judgment` (解析的判断、低信頼)。
> プラン散文に settled fact をキャッシュせず、ここにリンクする (re-derive > cache)。

## 達成 (proof-done / sorryAx-free — キャッシュでなく再導出レシピ)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| headline `rate_distortion_achievability_operational` (`AchievabilityUnconditional.lean:568`, `@[entry_point]`, full-support source) sorryAx-free | machine | `#print axioms InformationTheory.Shannon.rate_distortion_achievability_operational` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/RateDistortion/AchievabilityUnconditional.lean` (silent) | `16c3d391` | conditional `rate_distortion_achievability` の pass-through 仮説を Piece B/C/A で内部 discharge。`hP_supp : ∀ a, 0<P_X a` は regularity precondition (load-bearing でない、`@audit:ok`) |
| headline `rate_distortion_achievability_operational_general` (`AchievabilityGeneralSource.lean:410`, `@[entry_point]`, 任意 source) sorryAx-free | machine | `#print axioms InformationTheory.Shannon.rate_distortion_achievability_operational_general` (= `[propext, Classical.choice, Quot.sound]`) + `lake env lean InformationTheory/Shannon/RateDistortion/AchievabilityGeneralSource.lean` (silent) | `(本セッション audit commit)` | full-support 版から `hP_supp` を落としただけ、新 load-bearing hyp ゼロ (独立監査 `@audit:ok`)。台 subtype `{a // 0<P_X a}` 制限 → full-support 版適用 → retraction で code lift |

## 手法・再利用パターン (measure plumbing)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| source-alphabet 制限 (台 subtype) での期待歪み一致に **自作 `Measure.pi` null 積補題は不要**、Mathlib 既存で賄える | machine | `AchievabilityGeneralSource.lean` の `expectedBlockDistortion_lift_le` / `pmfToMeasure_map_retract` が `Measure.pi_map_pi` + `measurePreserving_eval` + `integral_map` のみで閉じることを確認 (`lake env lean` silent) | `(本セッション)` | general-source plan の Approach は「`Measure.pi` の null 積補題を self-build (無ければ)」と予測したが、pushforward/marginal は `Measure.pi_map_pi` + `measurePreserving_eval` で完結。retraction は**named def** にしないと `integral_map` の `φ x` 抽象化が higher-order unification で発火しない (inlined lambda は不可)。今後の RD/AWGN の同型 measure-plumbing を過大見積もりしないための所見 |
