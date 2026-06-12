# Shannon EPI: case-1 de Bruijn regularity **producer** サブ計画

**Status**: CLOSED ✅ — done (producer `isDeBruijnRegularityHyp_of_methodX_unitnoise` は transitively sorryAx-free に着地、`:2041` measurability sorry 解消済、コード側 `@residual(plan:epi-case1-debruijn-producer-plan)` retired)。一般 EPI 自体は別ルート (route T) で 2026-06-08 無条件 closure 済。進捗ブロックの PB-2/4/5/6 `[ ]` は stale。

> **Parent**: [`epi-case1-ratio-limit-plan.md`](epi-case1-ratio-limit-plan.md) + [`epi-case1-phaseC-methodx-wrapper-plan.md`](epi-case1-phaseC-methodx-wrapper-plan.md)
> **Status**: 📋 draft (案B、PB-1 done / PB-3 active、実装は `lean-implementer` dispatch)
> **撤退口 slug**: `@residual(plan:epi-case1-debruijn-producer-plan)`
> **fork-sizing advisor**: [`epi-case1-debruijn-producer-fork-sizing.md`](epi-case1-debruijn-producer-fork-sizing.md)

## ゴール

case-1 EPI wrapper `entropyPower_add_ge_case1_of_methodX` (`EPICase1RatioLimit.lean:1470`) が thread
する de Bruijn regularity 群 (`IsDeBruijnRegularityHyp` ×3 / `IsHeatFlowEndpointRegular` ×3 /
`h_pos_stam` bundle) を方針X の前提 (a.c. / 2次モーメント / **unit-variance** 雑音 Gaussian law /
4-tuple 独立) から **producer 補題で供給**し、最終 wrapper `entropyPower_add_ge_case1_of_methodX_unitnoise`
の前提を「方針X (unit-noise) のみ」に縮約する。

## 進捗サマリ (2026-06-06 実機械検証)

de Bruijn 解析核は `#print axioms` で **CLOSED (sorryAx-free)** 確認済
(`debruijnIdentityV2_holds_assembled` / `deBruijn_identity_v2` / `debruijnIntegrationIdentity_holds`
= `[propext, Classical.choice, Quot.sound]`) — 姉妹 plan `epi-debruijn-pertime-closure` の Wall SoT は
proof-done 済、本 plan は核に非依存。producer 構造的構成は genuine 完了し **残 sorry はただ 1 個** =
`isDeBruijnRegularityHyp_of_methodX_unitnoise` (`EPICase1RatioLimit.lean:1936`) の `integrable_deriv`
field 内 `:2041` **parameter-measurability** (`AEStronglyMeasurable` 引数、bound は genuine)。3 層分解済
(→ L-Prod-meas)。

## 進捗

- [x] M0/M1/B-0/B-0' (案D 調査 / blast radius / path-identification 代数 / wrapper latent defect 解消方針) — 完了、結論は判断ログ #2-4
- [x] PB-1 wrapper restate (unit-noise 固定) ✅
- [ ] PB-2 path-identification reduction 補題 `gaussianConvolution_rescale_eq` 構築 📋
- [~] PB-3 `IsDeBruijnRegularityHyp` producer X/Y (unit-noise 直接) — 構造 genuine 完了、残 1 sorry = `:2041` (L-Prod-meas) 🔄
- [ ] PB-4 sum-instance producer (W=(Z_X+Z_Y)/√2 unit + time-reparam) 📋
- [ ] PB-5 `h_pos_stam` producer (Stam/Blachman genuine 既存配線) 📋
- [ ] PB-6 最終 wrapper `entropyPower_add_ge_case1_of_methodX_unitnoise` 結線 📋
- [ ] PB-7 incidental: `IsIBPHypothesis` retract 📋
- [ ] PB-V verify + 独立 honesty audit 📋

## 文脈 — 唯一の構造的障害

`IsRegularDeBruijnHypV2.Z_law : P.map Z = gaussianReal 0 1` (**unit variance ハードコード**、
`FisherInfoV2DeBruijn.lean:210`) を `IsDeBruijnRegularityHyp.reg_at` が継承するため、
`P.map Z_X = gaussianReal 0 v_X` (v_X≠1) からは group を型レベルで構成不能。sum 側は
`Z_X+Z_Y ∼ gaussianReal 0 (v_X+v_Y)` でさらに v=2 不整合。case-1 wrapper が v_X 任意を取りながら
unit `Z_law` group を要求するのは **v_X≠1 で vacuously true な latent defect** (producer 不在で未顕在)。

## Approach — 案B (noise 標準化 + time-reparam)

案A (`Z_law` 値一般化) は破棄: density-level core は v_Z-agnostic だが **de Bruijn 微分値の v_Z 依存を
見落とし** — 一般 v_Z では genuine 微分値が `(v_Z/2)·J(at s·v_Z)`、値据置は false statement、値一般化は
ratio core `csiszarLogRatioGap_deriv_le_zero` (harmonic-Stam arith) が項毎 v_Z factor で偽化 (判断ログ #2)。
正路 = **path を unit 形に reparam して吸収** (structure 無改変、EPI 一般 line の unit-noise 設計と整合)。

4 段:
1. **PB-1 wrapper restate**: noise law を `gaussianReal 0 1` 固定、v_X/v_Y 引数除去。noise は結論に
   現れない補助変数 (`:1519`) ゆえ一般性を失わない。`entropyPower_add_ge_case1_of_regular` (`:1343`) の
   §3/§4 side は v_B 任意 (`entropyPower_rescaled_path_tendsto:296`) ゆえ v=1/v=1/v=2 を渡すだけ。**done**。
2. **PB-2 path-identification 補題** `gaussianConvolution_rescale_eq`: `Z'=Z/√v` (v>0) で
   `gaussianConvolution X Z' (t·v) = gaussianConvolution X Z t` は **点ごと厳密恒等式** (B-0、`Real.sqrt_mul`
   + `field_simp` + `ring`、`v>0` 厳格で degenerate 回避)。sum-instance N(0,2)→unit-W 橋渡しに使う。
3. **PB-3 (X/Y) / PB-4 (sum) producer**: X/Y は restate 後 unit-noise ゆえ reparam 不要で
   `IsDeBruijnRegularityHyp` 直接構成。sum は `W:=(Z_X+Z_Y)/√2` (unit) + PB-2 で N(0,2) を吸収、reparam
   factor は producer 内 `density_t` (`convDensityAdd pX_sum g_{s·2}`、Phase 1b v_Z=2) に閉じ ratio core に
   到達しない (B-0 系)。
4. **PB-5 `h_pos_stam` + PB-6 wrapper 結線**: Stam/Blachman conjunct は genuine 既存
   (`isStamInequalityHyp_via_step3` `EPIStamStep3Body.lean:119` / `isBlachmanConvReady_convDensityAdd_gaussian`)
   を配線。`IsHeatFlowEndpointRegular` は既に一般 variance (`EPIG2HeatFlowContinuity.lean:488`、`@audit:ok`) で
   v=1/v=1/v=2 を渡すだけ (障害なし、`EPIStamToBridge.lean:1435-1452` の既存 producer pattern)。

**B-0 系 (sum-instance の構造的制約)**: `IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` の `reg_at` の
`Z_law : gaussianReal 0 1` は N(0,2) と **型不充足**。path-identification は path を unit-W 形に同一視できるが
`Z_law` は noise law を直接主張するため reparam で救えない → sum-instance は X/Y と同じ unit-hardcode 壁
(v=2)。PB-4 で skeleton 型確認を最優先し、閉じなければ L-Sum-struct で park。

## PB-3 active 詳細 + 残 sorry (`:2041`)

`isDeBruijnRegularityHyp_of_methodX_unitnoise` (`:1936`) は `density_path` / `reg_at` / 全 `pX` series
(`pX`/`pX_nn`/`pX_meas`/`pX_law`/`pX_mom`) / `density_t_eq := fun _ _ => rfl` / `hbound`
(PB-2b `fisherInfoOfDensity_convDensityAdd_le` 経由) を **genuine 構成済**。`pX` series は a.c.→rnDeriv
density witness で供給 (regularity precondition、load-bearing でない)。`#print axioms` の sorryAx は
`:2041` 単一 sorry に trace。

**`:2041` = parameter-measurability**: `integrable_deriv` field の
`MeasureTheory.Measure.integrableOn_of_bounded` の `AEStronglyMeasurable` 引数。goal ≈
`AEStronglyMeasurable (fun t => (1/2)·(fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal))).toReal) (volume.restrict (Set.Ioc 0 T))`。bound は genuine、measurability のみ残課題。closure route → L-Prod-meas (3 層)。

## 撤退ライン

- **L-A-esc** (発火済): 案A は数学的に通らない (値据置=false statement、値一般化=ratio core 偽化)。案B へ
  エスカレート済、案A 逆戻り禁止。
- **L-Prod-meas** (PB-3、active): `:2041` parameter-measurability の 3 層分解 (implementer 撤退診断):
  - **Layer A** `measurable_convDensityAdd_gaussian_uncurry`: `Measurable (fun p:ℝ×ℝ => convDensityAdd pX
    (gaussianPDFReal 0 p.1.toNNReal) p.2)`。`Measurable pX` + `gaussianPDFReal` joint 可測 (port 元
    `Shannon/AWGN/ContChannelMIDecomp.lean:378 measurable_gaussianPDFReal_uncurry`) +
    `StronglyMeasurable.integral_prod_right` (`Integral/Prod.lean:76`)。**genuine 可能 ~40-60 行**。
  - **Layer B** lintegral param-measurability: `Measurable.lintegral_prod_right` (`Measure/Prod.lean:145`,
    `[SFinite ν]`) + `.toReal`。Layer A+C が揃えば genuine。
  - **Layer C** `measurable_logDeriv_convDensityAdd_gaussian_uncurry` (**真の壁**): `logDeriv (conv pX g_t) x`
    の `(t,x)` joint 可測。Mathlib `measurable_deriv_with_param` (`FDeriv/Measurable.lean:920`) は
    **`Continuous f.uncurry` (畳み込みの `(t,x)` 同時連続性)** を要求するが、available 仮説
    (`IsRegularDensityV2 pX`/`IsBlachmanConvReady`) は per-`t` のみで joint 連続性を供給しない。
    - **designated 突破口**: 畳み込み `(t,x)↦convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) x` の
      `t∈Ioc 0 T × x∈ℝ` 同時連続性を独立 brick として先立てる (Gaussian-tail uniform-on-compacts
      domination + dominated convergence) → `measurable_deriv_with_param` で Layer C closure → Layer B 経由で
      `:2041` 全消去。brick が当該 session で立たなければ `:2041` 据置 (type-check done)。
  - closure は Layer A+B+C を内部 genuine に閉じる形のみ。**producer signature への measurability load-bearing
    追加は禁止** (tier-5)。
- **L-Prod-park** (PB-3): `pX` series (特に `pX_mom` の 2次モーメント push-forward / `pX_law` の rnDeriv 整合)
  が `hX_ac`/`h_mom_X` から genuine に組めない → 該当 field のみ sorry+`@residual`。regularity precondition
  なので最終 wrapper の追加 precondition に外出しする選択肢もある。
- **L-Sum-struct** (PB-4): sum-instance `Z_law` が N(0,2) を主張できず path-identification でも橋渡し不能と
  判明 → sum producer の `reg_at` を park。`Z_law` field のみ general-variance 化する structure 改変 (案A とは
  別物: conv-pin variance は触らず微分値 `(1/2)·J` を保つので ratio core 偽化なし) を別 plan に切出す closure
  計画を判断ログに記録。
- **L-Stam-deleg** (PB-5): `h_pos_stam` の Fisher>0 / IsRegularDensityV2 / 正規化 conjunct を既存資産に
  delegate できず新 sorry が必要 → 該当 conjunct を park。Stam/Blachman conjunct (genuine 既存) は park 不可。
- **L-DBD** (全 Phase): time-reparam `t→t·v` の `v=0` / `Y:=0` 退化を突く degenerate-definition exploitation
  禁止 (v>0 厳格化 + noise が結論に現れない構造で回避)。

## Done 条件

proof done を目指す (PB-4 sum が park の場合は X/Y 系 proof done + sum type-check done):
`entropyPower_add_ge_case1_of_methodX_unitnoise` の前提から de Bruijn regularity 群が消え方針X
(unit-noise) のみ残る / touched file `lake env lean` silent / `IsIBPHypothesis` retract (PB-7、`rg` 0 hit) /
独立 honesty audit (`honesty-auditor`) verdict 全 OK。**honesty 不変条件**: producer 前提に load-bearing
`*Hypothesis` predicate を bundle しない。PB-1 restate + 新規 sorry 導入で audit 起動条件該当 (PB-V)。

## 参考 file (verbatim file:line、主要のみ)

- `EPICase1RatioLimit.lean:1470/1488-1518/1481-1483` — wrapper + de Bruijn 群前提 + latent v 任意 noise
- `EPICase1RatioLimit.lean:1343` / `:293` — `_of_regular` / `entropyPower_rescaled_path_tendsto` (§3/§4 side、v 任意)
- `EPICase1RatioLimit.lean:1936` (`:2041`) — PB-3 producer + 残 sorry
- `FisherInfoV2DeBruijn.lean:127` / `:205-288` — `gaussianConvolution` def / `IsRegularDeBruijnHypV2` (Z_law :210、案B 無改変)
- `FisherInfoV2DeBruijnGenuine.lean:51` — `deBruijn_identity_v2` (consumer、`(1/2)·J`)
- `FisherInfoV2DeBruijnPerTime.lean:80` / `:215` — `gaussianConvolution_law_conv` / `pPath_eq_convDensityAdd` (一般 v_Z)
- `EPIStamDischarge.lean:251-288` — `IsDeBruijnRegularityHyp` (producer 構成対象)
- `EPIG2HeatFlowContinuity.lean:488` / `EPIStamToBridge.lean:1435-1452` — `IsHeatFlowEndpointRegular` (一般 v_Z) + producer pattern
- `EPIStamToBridge.lean:1346,1352-1353` — `isStamToEPIScalingHyp_of_stam_debruijn` (unit-noise 要求 = PB-1 根拠)
- `EPIStamStep3Body.lean:119` — `isStamInequalityHyp_via_step3` (Stam conjunct、genuine)
- `FisherConvBound.lean:385` — `gaussianConv_fisher_le_inv_var` (`integrable_deriv` Fisher 有界、`wall:fisher-finiteness` CLOSED)
- `FisherInfoV2DeBruijnBody.lean:209` — `IsIBPHypothesis` (PB-7 retract 対象)
- `Mathlib/Data/Real/Sqrt.lean:352` — `Real.sqrt_mul` (PB-2)

## 判断ログ (key のみ)

決着済 entry (#1 案A 確定 / #3 B-0 代数 / #4 B-0' 3択 / #5 sum 制約) は削除 (git 履歴 + 上記 Approach/撤退ライン)。

2. **2026-06-05 — 案A REVERT (L-A-esc) → 案B 採用**: fork-sizing advisor verdict で案A 致命欠陥判明。M0 は
   density-level core の v_Z-agnostic を正しく確認したが **de Bruijn 微分値 `(1/2)·J` の v_Z 依存を見落とし** —
   一般 v_Z では `(v_Z/2)·J(at s·v_Z)`。値据置=false statement (tier 5 degenerate)、値一般化=ratio core
   `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) が項毎 v_Z factor で偽化 (advisor Q1)。正路 =
   path を unit 形に reparam (案B)。**教訓**: density-level core の v_Z-agnostic は微分値の v_Z 非依存を意味しない。
6. **2026-06-06 — 実機械検証で残 sorry を `:2041` measurability に局所化**: PB-3 producer 構造的構成 genuine
   完了、`#print axioms` の sorryAx は `:2041` (parameter-measurability) 単一に trace。3 層分解 (Layer A genuine /
   Layer B 中継 / Layer C = `measurable_deriv_with_param` が `Continuous f.uncurry` を要求するが available 仮説は
   per-`t` のみで joint 連続性を供給しない真の壁) → L-Prod-meas 追加。designated 突破口 = 畳み込みの `(t,x)` 同時
   連続性 brick (Gaussian-tail uniform-on-compacts domination)。`:2041` は honest classification 保持、producer
   signature への measurability load-bearing 追加禁止。
