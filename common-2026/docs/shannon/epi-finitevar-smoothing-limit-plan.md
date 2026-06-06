# 有限分散 classical EPI closure — Phase-A smoothing-limit 実装計画

> **親**: [`epi-uncond-deffix-monotone-plan.md`](epi-uncond-deffix-monotone-plan.md) → 残壁 `wall:epi-finite-entropy-ac-classical` の **有限分散 sub-case** を genuine close する。無限分散 sub-case は genuine Mathlib 壁 (Lieb-Young 不在) ゆえ別 named wall に隔離 (touch しない、ユーザー確定 2026-06-06)。
> **status**: 2026-06-06 scoping workflow (`wf_47d024fe-b0e`, 4 thread + synth) で route 確定 + skeleton 産出。実装未着手。
> **slug**: `epi-finitevar-smoothing-limit-plan`。

## ルート確定: Route A (Phase A smoothing-limit)

X, Y 両 a.c. + 有限分散 + 有限エントロピー。`X_t = X+√t·Z_X`, `Y_t = Y+√t·Z_Y` (Z 標準正規、独立)。t>0 で smoothed 密度は正則 → **Phase A `entropy_power_inequality_of_density` を各 t で適用** → endpoint 連続性 (t→0⁺) で base へ降ろし極限で EPI。

**機械検証で訂正済 (scoping synth §0、重要)**: scoping thread が「壁」とした 2 件は **誤り**:
- `heatFlowDifferentialEntropy_continuousWithinAt_zero` (`EPIG2HeatFlowContinuity.lean:350`) は `@audit:ok` sorryAx-free (2026-06-05 CLOSED)。upstream 壁は無い。
- de Bruijn producer `isDeBruijnRegularityHyp_of_methodX_unitnoise` (`EPICase1RatioLimit.lean:1950`) は sorryAx-free (`integrable_deriv` leaf も 2026-06-06 CLOSED)。

**sum-density gap = composes-cleanly (Mathlib 壁でない)**: base で X+Y は general∗general 畳込み (正則性 producer 無し) だが、smoothed sum `X_t+Y_t` の密度 `conv(conv pX g_t, conv pY g_t)` を `convDensityAdd_convGaussian_interchange` (`EPIConvDensityAssoc.lean:206`, `@audit:ok`) で `conv(conv(pX,pY), g_{2t})` に書換 → `isRegularDensityV2_convDensityAdd_gaussian(pX∗pY, 2t)` で正則化。`pX∗pY` の base 正則性は `convDensityAdd_pXpY_{nonneg:152/measurable:73/integrable:159/integral_eq:167}` (`EPIConvDensityAssoc.lean`) が供給。

## 確認済 sorryAx-free 資産 (全て `#print axioms = [propext, Classical.choice, Quot.sound]` 実測)
- Phase A core `entropy_power_inequality_of_density` (`EPIDensityForm.lean:70`)。
- endpoint 連続性 `heatFlowEntropyPower_continuousWithinAt_zero` (`EPIG2HeatFlowContinuity.lean:583`、`IsHeatFlowEndpointRegular` は v_Z 一般、sum は v_Z=2)。
- 3-noise lift `liftMeasure3`/`entropy_power_inequality_via_lift3` (`EPINoiseExtension.lean:168/184`)。
- Real→ℝ≥0∞ bridge `entropyPowerExt_of_ac_integrable` (`EntropyPowerExt.lean:118`)。
- smoothed 正則性 producer: `isRegularDensityV2_convDensityAdd_gaussian` (`EPIConvDensityRegular.lean:203`)、`isBlachmanConvReady_convDensityAdd_gaussian` (`EPIBlachmanGeneralDensity.lean:224`)、Fisher `gaussianConv_fisher_le_inv_var` (`FisherConvBound.lean:387`)、entropy `convDensityAdd_negMulLog_integrable` (`EPIG2HeatFlowContinuity.lean:131`)。
- 順序極限パターン `epi_of_csiszarLogRatioGap_tendsto` (`EPICase1RatioLimit.lean:104`、`le_of_tendsto` 形) + Mathlib `Filter.Tendsto.add`/`ContinuousWithinAt.add`/`le_of_tendsto`。
- **代替 (要検討)**: `entropyPower_add_ge_case1_of_methodX` (`EPICase1RatioLimit.lean:1499`, sorryAx-free) が methodX regularity から case-1 EPI を直接供給 (de Bruijn group は producer 経由 supply 可)。smoothing-limit を自前で組むより、各 t で此れを呼ぶ方が短い可能性 — 実装時に比較。

## 実装 skeleton (新 file `InformationTheory/Shannon/EPICase1SmoothingLimit.lean`、L1-L7、依存順)

- **L1 `smoothedDensity_regularity_bundle`**: ∀t>0、smoothed 入力 (X_t/Y_t/sum) の 5 正則性 (Fisher≠∞ ∧ IsRegularDensityV2 ∧ ∫=1 ∧ IsBlachmanConvReady∀v ∧ negMulLog integrable) を供給。前提 = a.c. + 有限2次moment + measurable。body = 上記 producer 群、sum は interchange 経由。**最大量、Mathlib 壁なし** (最初は conjunct 毎 `have := by sorry` で skeleton → producer 置換)。
- **L2 `entropyPower_smoothed_epi_perT`**: ∀t>0、`entropyPower(P.map(X_t+Y_t)) ≥ entropyPower(P.map X_t)+entropyPower(P.map Y_t)`。body = Phase A core 直呼 + L1 threading。
- **L3 `entropyPower_endpoint_tendsto`** (L1 と独立並列可): X/Y/sum の 3 endpoint 連続性 (`ContinuousWithinAt (fun t => entropyPower(P.map X_t)) (Ioi 0) 0`)。body = `heatFlowEntropyPower_continuousWithinAt_zero` ×3。要 `IsHeatFlowEndpointRegular` 14-field 構築 (sum は v_Z=2、`EPIDensityForm.lean:304-353` の `endpt_of` パターン参照、最初 sorry 可)。
- **L4 `entropyPower_add_ge_of_finite_variance`** (Real): body = noise 導入 (base に Z 無ければ `Ω×ℝ×ℝ` lift) + L2 + L3 を `Filter.Tendsto.add` + `le_of_tendsto` で合成 (`f(t)≥g(t)∀t>0 ∧ f→f(0) ∧ g→g(0) ⟹ f(0)≥g(0)`)。
- **L5 `entropyPowerExt_add_ge_of_finite_variance`** (ℝ≥0∞): body = `entropyPowerExt_of_ac_integrable` で 3 項を ofReal 化 + L4 を `ENNReal.ofReal_le_ofReal`+`ofReal_add` で lift。LHS=∞ 枝は `le_top` 自明。
- **L6 `entropyPowerExt_add_ge_infinite_variance`** (wall 隔離、touch しない): body `sorry` + `@residual(wall:epi-infinite-variance-classical)`。docstring に Lieb-Young 不在 (loogle Found 0)。
- **L7 (既存 `EPIUncondMixedCase.lean:256` 編集)**: `entropyPowerExt_add_ge_finite_ac` body の bare sorry を `by_cases hfv : Integrable((X·)²) P ∧ Integrable((Y·)²) P` で 2 分 → 真 L5、偽 L6。`InformationTheory.lean` に新 file import 追加。

## Phase 分割 (implementer dispatch)
- **Phase 1 (並列 2 agent)**: 1a=L1 (正則性供給、最大量)、1b=L3 (endpoint 連続性 + IsHeatFlowEndpointRegular 構築)。各 `lake env lean` + `#print axioms`。
- **Phase 2 (単独)**: L2+L4+L5 (Phase A 適用 + limit-passing + ext bridge)。L1/L3 依存。
- **Phase 3 (単独、小)**: L6 (wall) + L7 (dispatch body 差替) + import。`entropyPowerExt_add_ge_finite_ac` の sorry が infinite-variance 1 本のみ transitive になることを `#print axioms` 確認。
- **honesty-auditor (Phase 3 後 必須)**: (a) L6 wall 分類 (Lieb-Young Found 0 裏取り)、(b) L1-L5 が 0 sorry genuine + `h_mom_X/Y` が finite-variance 表明であって EPI を encode していないこと、(c) `IsHeatFlowEndpointRegular` 14-field が regularity precondition であること。

## 残 honest residual (closure 後)
sorry 1 本のみ: `entropyPowerExt_add_ge_infinite_variance` (`@residual(wall:epi-infinite-variance-classical)`)。無限分散 a.c. 古典 EPI = Lieb-Young sharp Young / Brascamp-Lieb (Mathlib 不在、別 thread)。`wall:epi-finite-entropy-ac-classical` は分裂し有限分散部分は閉じる。

## 撤退ライン
- L1 sum interchange で型詰まり → 当該 conjunct `sorry`+`@residual(plan:epi-finitevar-smoothing-limit-plan)`、signature 保持。
- L3 sum IsHeatFlowEndpointRegular (v_Z=2 density witness) 詰まり → 当該 endpoint `sorry`+同 slug、X/Y 単独は先に閉じる。
- L4 noise lift 詰まり → noise 既存前提版で park。順序極限合成自体は確実。
- 無限分散 (L6) は **一切 touch しない** (別 wall、Lieb-Young 待ち)。
