# Proof log — EPI case-1 G3 closure, Phase B(i)-cont

対象: `isRescaledPathRegular_of_methodX` (`InformationTheory/Shannon/EPICase1RatioLimit.lean`)
の 9 個の park された integrability conjunct の genuine 化。

## 結果サマリ

- **6 / 9 conjunct を genuine 化** (type-check done、本体内で sorryAx-free に閉じた)。
- 残 **3 conjunct** を honest park 継続 (`@residual(plan:epi-case1-difference-g3-closure-plan)`)。
- 追加 precondition: **`hA_ac : P.map A ≪ volume`** (方針 X / case-1 の honest regularity、非 load-bearing)。
- `#print axioms isRescaledPathRegular_of_methodX` = `[propext, sorryAx, Classical.choice, Quot.sound]`
  (3 conjunct 未閉鎖ゆえ sorryAx 残存、全閉じれば消える)。
- `lake env lean` 0 errors (sorry warning のみ)。

## 閉じた 6 conjunct と使った資産

| conjunct | bundle | 鍵となった資産 |
|---|---|---|
| 1. joint-≪-product | lower | `AbsolutelyContinuous.compProd_right` + `volume ≪ P.map W` (`convDensityAdd_pos` の strict positivity → `withDensity_absolutelyContinuous'`) + 各 fibre `gaussianReal z v_B ≪ volume` |
| 2. fibre self-entropy (∀ᵐ z) | lower | `integrable_density_log_density_of_gaussian` (DifferentialEntropy.lean:86) + `rnDeriv_gaussianReal` + `toReal_gaussianPDF` |
| 3. fibre entropy over z | lower | `differentialEntropy_gaussianReal` (定数 `(1/2)log(2πe v_B)`) + `integrable_const` (確率測度上) |
| 4. log(path rnDeriv) wrt path | lower | path 密度同定 `pPath_eq_convDensityAdd` + `integrable_withDensity_iff_integrable_smul₀'` + entropy-finiteness `convDensityAdd_negMulLog_integrable_pub` (`g·log g = -negMulLog g`) |
| 5. squared-deviation | upper | `integrable_map_measure` (path → P) + `MemLp 2` moment transport (`memLp_id_gaussianReal'` for B, `h_mom_A` scaled for A/√t) + `(x-m)²` 展開 |
| 6. negMulLog (path) | upper | path 密度同定 `pPath_eq_convDensityAdd` + `convDensityAdd_negMulLog_integrable_pub` + a.e. `toReal_ofReal` transfer |

### 自作した private helper (2 本、いずれも genuine / 本体 sorry 無し)

- `map_div_sqrt_absolutelyContinuous`: `P.map A ≪ volume ⟹ P.map (A/√t) ≪ volume`。
  `Real.map_volume_mul_right` (Lebesgue スケーリング) + `AbsolutelyContinuous.map` + `Measure.smul_absolutelyContinuous`。
- `rescaledInput_density_witness`: `hA_ac` + `h_mom_A` から `A/√t` の Real 密度 witness `pX` を構成し、
  `≥0` / measurable / `withDensity` law / `Integrable` / `∫=1` / 2 次モーメント `Integrable (y²·pX)` を一括供給。
  `withDensity_rnDeriv_eq` + `rnDeriv_lt_top` (`ofReal∘toReal =ᵐ id`) + `integrable_withDensity_iff_integrable_smul₀'`
  でモーメント transport。これが 4/6 path 系 conjunct の共通基盤。

## 残 3 conjunct (park 継続、honest)

すべて lower bundle の **conditional-KL analytic core** (`condDifferentialEntropy_le` の `h_int` / `hκ_cross_int` / `h_cross_int` に対応):

1. **llr(joint, product) integrable** — KL divergence integrand。
2. **fibre-rnDeriv · log(path-rnDeriv) integrand (∀ᵐ z)** — per-z cross-entropy 項 `∫ gauss_z(x)·log g(x) dx`。
3. **z-averaged cross-term integrable** — 上記の z 平均。

park 理由: いずれも path 密度 `g = convDensityAdd pX g_{v_B}` の **`log g` を Gaussian fibre に対して積分する cross-entropy** を要する。`g` は closed-form 無し (convolution)、`log g` の tail control 補題が in-tree 不在。entropy-finiteness 資産 (`negMulLog (convDensityAdd ...)`) は **path 測度 (= withDensity g) 上の self-entropy** には効くが、**別の Gaussian fibre に対する cross 積分** には直接使えない (測度が違う)。Gaussian-fibre tractable だが本補題の bridge budget 超過。後続 plan で cross-entropy tail-control 補題を立てれば閉じる見込み。

## grep / loogle メモ (空振り含む)

- `Integrable, gaussianPDFReal` → `integrable_gaussianPDFReal` 1 件のみ。Gaussian negMulLog / self-entropy 直接補題は Mathlib 不在 → in-tree `integrable_density_log_density_of_gaussian` (DifferentialEntropy.lean) を発見・使用。
- `convDensityAdd` は loogle index に未登録 (`unknown identifier`) → `rg` で in-tree 補題を探索 (`convDensityAdd_pos` / `convDensityAdd_pXpY_nonneg` / `convDensityAdd_negMulLog_integrable_pub`)。
- `convDensityAdd_nonneg` という名は不在 → `integral_nonneg` を inline (convDensityAdd は Bochner 積分定義)。
- `convDensityAdd` の measurability: `fun_prop` 不可 (convDensityAdd unfold せず) → `rnDeriv` の measurability + a.e. 同定 (`AEMeasurable.congr`) で迂回。

## 設計判断

- 当初 brief は「9 conjunct 全閉じれば sorryAx-free」を目標にしたが、conditional-KL の 3 cross 項は真の analytic gap (cross-entropy tail control の Mathlib/in-tree 不在) と判明 → 6 閉じ + 3 honest park で着地。over-claim 回避。
- `hA_ac` 追加は case-1 (両 a.c.) の正当な regularity precondition。load-bearing でない (結論の核 = entropy 単調性 / max-ent は別 genuine 補題側、本補題は regularity bundle 構成のみ)。
