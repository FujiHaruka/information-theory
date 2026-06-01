# EPI A-5 caller-supplied precondition feasibility — Mathlib/in-house inventory

> Scope: the 4 path-density regularity preconditions newly localized into the
> `h_pos_stam` per-`t` bundle of the EPI chain apex
> `isStamToEPIBridgeHyp_of_stam_debruijn` / `isStamToEPIScalingHyp_of_stam_debruijn`
> (`Common2026/Shannon/EPIStamToBridge.lean:1287-1322` / `1402-1322`), threaded by the
> 2026-06-01 R-3‴ closure. End-to-end closure needs an A-5 producer that discharges them.
> Read-only inventory; no implementation / plan authoring.

## 一行サマリ

4 項目のうち **(1)(2)(3) は in-house で closeable**（部品が `@audit:ok` で揃っている、新規補題 ~150-220 行）。**(4) `IsBlachmanConvReady` の非 Gaussian producer が唯一の重い壁**：現 producer は Gaussian 専用、conv-with-Gaussian density (任意 `pX`) 用は 19 field 中 ~6-8 field が `pX` に追加 regularity（`deriv` 有界・tail decay・各種 Tonelli 可積分）を要し、Mathlib 不在の `HasCompactSupport`-free convolution-smoothness を in-house parametric-integral gateway で個別に組む必要がある。**真の Mathlib 壁ではなく in-house 工数壁（~400-700 行）。** 撤退ライン: 既存 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` の枠内で吸収でき、新規撤退発動は不要。

---

## A-5 で充足すべき 4 項目（再掲、signature verbatim）

`h_pos_stam` バンドル（`EPIStamToBridge.lean:1287-1322`）は各 `(Z_X, Z_Y, t>0)` に対し、本調査対象の 4 種を含む。**重要**: ターゲット密度は **Gaussian ではなく** `(h_reg_X.reg_at t ht).density_t`、これは `IsRegularDeBruijnHypV2.density_t_eq`（`FisherInfoV2DeBruijn.lean:259-260`）により

```
density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x       -- conv-pin
```

`pX` は X の任意密度（Gaussian とは限らない）で、`IsRegularDeBruijnHypV2` が供給する pX regularity は **`pX_nn` / `pX_meas` / `pX_law` / `pX_mom`（第2モーメント `∫ y²·pX < ∞`）の 4 件のみ**（`FisherInfoV2DeBruijn.lean:226-267`）。

調査対象 4 項目（`density_X := (h_reg_X.reg_at t ht).density_t` 等を略記）:

| # | precondition（verbatim） | 出現行 |
|---|---|---|
| (1) | `IsRegularDensityV2 density_X` ∧ `IsRegularDensityV2 density_Y` | `1309-1312` |
| (2) | `∫ x, density_X x ∂volume = 1` ∧ `∫ density_Y = 1` | `1313-1314` |
| (3) | `∀ x, density_sum x = convDensityAdd density_X density_Y x` | `1315-1318` |
| (4) | `IsBlachmanConvReady density_X density_Y` | `1319-1321` |

---

## verdict サマリ表

| # | precondition | feasibility | 主要根拠 file:line |
|---|---|---|---|
| (1) | `IsRegularDensityV2 (convDensityAdd pX g_t)` | **in-house で closeable**（gateway 部品揃い、新規 ~150 行） | `EPIConvDensity.lean:187` `convDensityAdd_hasDerivAt_of_regular` (@audit:ok), `FisherInfoV2DeBruijnPerTime.lean:786` `convDensityAdd_pos` (@audit:ok) |
| (2) | `∫ convDensityAdd pX g_t = 1` | **in-house で closeable**（Mathlib Fubini + 既存正規化、~40-70 行） | `Mathlib/Analysis/Convolution.lean:843` `integral_convolution`, `Mathlib/.../Gaussian/Real.lean:121` `integral_gaussianPDFReal_eq_one` |
| (3) | `density_sum = convDensityAdd density_X density_Y` | **in-house で closeable**（assoc/comm 自作必要だが代数のみ、~120-200 行） | `EPIConvDensity.lean:45` `convDensityAdd_comm` (@audit:ok), `FisherInfoV2DeBruijnPerTime.lean:198` `pPath_eq_convDensityAdd`; ⚠ `convDensityAdd_assoc` **不在** |
| (4) | `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)` | **in-house 工数壁**（非 Gaussian producer 不在、~400-700 行） | producer は `EPIBlachmanGaussianWitness.lean:335` の **Gaussian 専用** 1 件のみ。一般 density 用は不在 |

---

## (1) `IsRegularDensityV2 (convDensityAdd pX g_t)` producer — closeable

`IsRegularDensityV2` の field（`FisherInfoV2.lean:124-138`、verbatim）:
- `diff : Differentiable ℝ f`
- `pos : ∀ x, 0 < f x`
- `tail_bot : Filter.Tendsto f Filter.atBot (nhds 0)`
- `tail_top : Filter.Tendsto f Filter.atTop (nhds 0)`
- `integrable_deriv : Integrable (deriv f) volume`
- `integral_deriv_eq_zero : ∫ x, deriv f x ∂volume = 0`

### 既存 in-house 部品（field 別）

| field | gateway 補題 | file:line | 状態 |
|---|---|---|---|
| `diff` | `convDensityAdd_hasDerivAt_of_regular (fX fY : ℝ → ℝ) (z₀ : ℝ) (hregX hregY : IsRegularDensityV2 _) (hX_int : Integrable fX volume) (hY_bdd : ∃ M, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M, ∀ w, |deriv fY w| ≤ M) : HasDerivAt (convDensityAdd fX fY) (∫ x, convDensityAddDeriv fX fY z₀ x ∂volume) z₀` | `EPIConvDensity.lean:187` | ✅ @audit:ok（per-`z₀`、Differentiable 化は `∀ z₀` 量化で組む） |
| `pos` | `convDensityAdd_pos (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume) (hpX_mass : 0 < ∫ y, pX y ∂volume) {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x` | `FisherInfoV2DeBruijnPerTime.lean:786` | ✅ @audit:ok（conv-with-Gaussian 専用、まさにターゲット形） |
| `tail_*` | （新規）`pX` 可積分 + Gaussian tail → conv の tail。直接の in-house 補題は **未確認**、Gaussian decay 遺伝を組む | — | 🟡 要新規（dominated convergence + Gaussian envelope、~40-60 行） |
| `integrable_deriv` | `convDensityAddDeriv` の可積分性。`convKernel_envelope_integrable (pX K : ℝ → ℝ) (hpX_int hpX_meas hK_int hK_meas) : Integrable (fun x => ∫ y, pX y * K (x - y) ∂volume) volume` を `K := deriv g_t` で | `FisherInfoV2DeBruijnAssembly.lean:787`（private） | 🟡 private、同 file 内なら可。別 file からは re-export 要 |
| `integral_deriv_eq_zero` | FTC + tail vanishing。`tail_*` から従う標準パターン（`FisherInfoGaussian.lean:231-292` の Gaussian 版が雛形） | — | 🟡 要新規（~30 行、`tail_*` 依存） |

### verdict: in-house で closeable
`diff` / `pos` は `@audit:ok` で完備。残り（`tail_*` / `integral_deriv_eq_zero`、`integrable_deriv` の re-export）は標準解析で **新規 ~150 行**。`pX` 側は `IsRegularDensityV2` を仮定できる（後述: 但しその producer 自体が (4) と同根の循環リスク — `pX` は単に density で、**`IsRegularDensityV2 pX` は供給されていない**）。

⚠ **落とし穴（最重要）**: `convDensityAdd_hasDerivAt_of_regular` は `hregX : IsRegularDensityV2 fX` と `hregY : IsRegularDensityV2 fY` を **両方**要求する。ターゲットは `convDensityAdd pX g_t` で、`fX := pX`（X 密度）、`fY := g_t`（Gaussian）。`g_t` 側は `isRegularDensityV2_gaussianPDFReal`（`EPIBlachmanGaussianWitness.lean:275`）で供給可。しかし **`pX` 側は `IsRegularDensityV2 pX` が `IsRegularDeBruijnHypV2` から供給されていない**（`pX_nn/meas/law/mom` のみ）。`pX` の smoothness（`Differentiable`・`pos`）は一般の X 密度には成立しない。
→ **したがって gateway は `fX := pX, fY := g_t` の形では直接は使えない場合がある**。ただし conv-with-Gaussian の差別化点として: `convDensityAdd pX g_t` の smoothness は **Gaussian kernel 側の smoothness が遺伝する**（`∂_z ∫ pX(x) g(z-x) = ∫ pX(x) g'(z-x)`、微分は Gaussian factor が担う）。gateway を `fX := pX`（可積分のみ）`fY := g_t`（smooth kernel）で呼ぶには gateway の hyp 構造を確認すると、`hregX : IsRegularDensityV2 fX` は **`fX = pX` 側にも smoothness を要求している**（`hX_cont := hregX.diff.continuous` を内部使用、`EPIConvDensity.lean:198`）。
→ **gateway の現 signature では `pX` smoothness が必須**。これを回避する「`pX` integrable-only + Gaussian-kernel-smooth」版 gateway は **新規に組む必要がある**（gateway の `h_diff` field で微分を Gaussian factor 側に寄せれば `pX` は可積分のみで足りる、~80-120 行）。**これが (1) の実質コスト**。

---

## (2) `∫ convDensityAdd pX g_t = 1` 正規化 producer — closeable

### Mathlib 部品

**`MeasureTheory.integral_convolution`** — `Mathlib/Analysis/Convolution.lean:843`（verbatim）:
```
theorem integral_convolution [MeasurableAdd₂ G] [MeasurableNeg G] [NormedSpace ℝ E]
    [NormedSpace ℝ E'] [CompleteSpace E] [CompleteSpace E'] (hf : Integrable f ν)
    (hg : Integrable g μ) : ∫ x, (f ⋆[L, ν] g) x ∂μ = L (∫ x, f x ∂ν) (∫ x, g x ∂μ)
```
- 結論 `∫ (f ⋆[L,ν] g) = L (∫f) (∫g)`。`L := ContinuousLinearMap.mul`、`∫pX·∫g_t = 1·1`。
- ⚠ ただし `convDensityAdd`（Bochner `∫ x, pX x * g(z-x)`）は `⋆[L,ν]` 形ではない。bridge `convDensityAdd pX g = (pX ⋆[mul, volume] g)` を 1 行で立てる必要（定義展開で一致、~10 行）。

代替（より直接）: **`MeasureTheory.integral_integral_swap`**（Fubini、`Mathlib/MeasureTheory/Integral/Prod.lean`）で `∫_z ∫_x pX(x)·g(z-x) = ∫_x pX(x) ∫_z g(z-x) = ∫_x pX(x)·1 = 1`。reflection `integral_sub_right_eq_self` で `∫_z g(z-x) = ∫ g = 1`。

### 既存正規化
- `integral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫ x, gaussianPDFReal μ v x = 1` — `Mathlib/.../Gaussian/Real.lean:121`。Gaussian factor の `∫ = 1`。
- `∫ pX = 1`: `pX_law : P.map X = withDensity (ofReal∘pX)` + `P` 確率測度から `∫ pX = (P.map X) univ = 1`。`pPath_eq_convDensityAdd` の body（`FisherInfoV2DeBruijnPerTime.lean:214-220`）に `Integrable pX` 導出 + mass=1 の雛形が既にある。

### verdict: in-house で closeable
Fubini ルート（reflection 不変性 + Gaussian/pX 各 `∫=1`）で **新規 ~40-70 行**。可積分性は `convDensityAdd_integrand_integrable`（`FisherInfoV2DeBruijnPerTime.lean` で参照済）+ `convKernel_envelope_integrable` から供給。

---

## (3) convolution 同定 `density_sum = convDensityAdd density_X density_Y` — closeable（assoc 自作要）

ターゲット: `density_sum = convDensityAdd p_{X+Y} g_t` を `convDensityAdd (convDensityAdd pX g_t) (convDensityAdd pY g_t)` に等値。数学的内訳:

### 部品 (3a) 和の密度 = 畳み込み: `p_{X+Y} = convDensityAdd pX pY`
- **`pPath_eq_convDensityAdd`**（`FisherInfoV2DeBruijnPerTime.lean:198`、verbatim 抜粋）:
  ```
  theorem pPath_eq_convDensityAdd {P : Measure Ω} [IsProbabilityMeasure P]
      (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
      (hZ_law : P.map Z = gaussianReal 0 1)
      (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
      (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
      {s : ℝ} (hs : 0 < s) :
      (P.map (gaussianConvolution X Z s)).rnDeriv volume
        =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) z)
  ```
  これは X⊥(Gaussian) 専用。X⊥Y 一般和には対応する一般版が必要。
- **Mathlib `IndepFun.pdf_add_eq_lconvolution_pdf`**（loogle 確認: `from Mathlib.Probability.Density`、1 件）— ⚠ ただし `rg` で `Mathlib/Probability/Density.lean` に grep ヒットせず別 file の可能性。density-level `convDensityAdd`（Real-valued Bochner）への bridge（`⋆ₗ`/`lconvolution` ENNReal → `convDensityAdd` Real）は `convDensityAdd_gaussian_closed_form` の body（`EPIBlachmanGaussianWitness.lean:179-` の `h_lconv_pt`）に雛形あり。

### 部品 (3b) 結合則・可換則
- `convDensityAdd_comm (pX pY : ℝ → ℝ) : convDensityAdd pX pY = convDensityAdd pY pX` — `EPIConvDensity.lean:45` ✅ @audit:ok
- **`convDensityAdd_assoc` 不在**（`rg` 確認: `EPIConvDensity.lean` に該当行 0 件）。`convDensityAdd (convDensityAdd pX g) (convDensityAdd pY g) = convDensityAdd (convDensityAdd pX pY) (convDensityAdd g g)` のような並べ替えに必要 → **自作要**（Fubini + reflection、~60-100 行）。

### 部品 (3c) Gaussian 和の variance 整合
- Z_X, Z_Y iid `gaussianReal 0 1` → Z_X+Z_Y `~ gaussianReal 0 2`。**`gaussianReal_add_gaussianReal_of_indepFun`**（`Mathlib/.../Gaussian/Real.lean:624`、verbatim）:
  ```
  lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
      {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
      (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
      P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)
  ```
- density-level: `convDensityAdd_gaussian_closed_form {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) : convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) = gaussianPDFReal (mX + mY) (vX + vY)` — `EPIBlachmanGaussianWitness.lean:168` ✅。heat kernel variance `t + t`／`2t` 整合はここで処理。
- **`ProbabilityTheory.gaussianReal_conv_gaussianReal`** — `Mathlib/.../Gaussian/Real.lean:613`、measure-level convolution。

### verdict: in-house で closeable（重め）
部品の多くが `@audit:ok` で揃うが、(3a) の **X⊥Y 一般版 `pPath`（現状 X⊥Gaussian 専用）** と (3b) `convDensityAdd_assoc` が新規。代数 + Fubini 中心で **~120-200 行**。原理的壁なし。

---

## (4) `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)` producer — in-house 工数壁（最重要）

### 現 producer は Gaussian 専用
唯一の producer **`isBlachmanConvReady_gaussianPDFReal`**（`EPIBlachmanGaussianWitness.lean:335`、verbatim）:
```
theorem isBlachmanConvReady_gaussianPDFReal
    {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) :
    IsBlachmanConvReady (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)
```
入力 `fX/fY` が **両方 Gaussian PDF**。ターゲットは `fX := convDensityAdd pX g_t`（非 Gaussian、X が Gaussian でない限り）。**非 Gaussian 用 producer は in-house に 0 件**（`rg "IsBlachmanConvReady" Common2026/Shannon/*.lean` → producer は Gaussian 1 件のみ）。

### 19 field の分類（`EPIBlachmanDensity.lean:712-761`、verbatim field 名）

`f := convDensityAdd pX g_t`、`g := convDensityAdd pY g_t` と置く（両者 conv-with-Gaussian）。各 field を「conv-with-Gaussian で Gaussian smoothness が遺伝して満たせる」vs「`pX/pY` に追加 regularity を要する」で分類:

| field | 内容（verbatim 結論型） | conv-with-Gaussian での充足性 |
|---|---|---|
| `int_fX` | `Integrable fX volume` | ✅ 遺伝（(2) 同様 Fubini、`pX` 可積分から） |
| `int_fY` | `Integrable fY volume` | ✅ 同上 |
| `bdd_fX` | `∃ M, ∀ w, |fX w| ≤ M` | 🟡 `convDensityAdd pX g_t` の上界 = `(sup g_t)·∫pX = (sup g_t)·1`（Gaussian sup 有界が遺伝、~20 行） |
| `bdd_fX'` | `∃ M, ∀ w, |deriv fX w| ≤ M` | 🟡 `deriv (conv) = ∫ pX(x)·g_t'(z-x)`、`|·| ≤ (sup|g_t'|)·∫pX`。Gaussian `deriv` 有界遺伝（~30 行） |
| `bdd_fY` / `bdd_fY'` | 同上（Y 側） | 🟡 同上 |
| `pos_pZ` | `∀ z, 0 < convDensityAdd fX fY z` | 🟡 `convDensityAdd_pos` 雛形（`FisherInfoV2DeBruijnPerTime.lean:786`）の 2 段 conv 版。`fX/fY` 正値 + 可積分 + mass>0 から（~40 行） |
| `int_X` | `∀ z, Integrable (fun x => deriv fX x * fY (z - x)) volume` | 🟡 `deriv fX` 有界（`bdd_fX'`）+ `fY` 可積分 → `bdd_mul`（~20 行/field、`convKernel_envelope` 流用） |
| `int_Y` | `∀ z, Integrable (fun x => fX x * deriv fY (z - x)) volume` | 🟡 同上 |
| `cond_int` | `∀ z, Integrable (condDensityX fX fY z) volume` | 🟡 `condDensityX` 定義依存、`fX·fY(z-·)/pZ` 形（~30 行） |
| `int_W` / `int_Wsq` | `∀ lam ∈[0,1], ∀ z, Integrable (scoreWeight·condDensityX [^2]) volume` | 🔴 `scoreWeight` は `logDeriv` 含む。**conv の logDeriv 有界性**が要 → `pX` の追加 regularity（tail decay rate）に依存しうる（~60-100 行/field） |
| `int_inner` | `∀ lam ∈[0,1], Integrable (fun z => (∫ scoreWeight²·condDensityX) · convDensityAdd fX fY z)` | 🔴 inner integral の `z`-可積分性、第2モーメント（`pX_mom`）が効く（~80 行） |
| `int_fisherX` | `Integrable (fun x => (logDeriv fX x)^2 * fX x) volume` | 🔴 conv の Fisher 情報量有限性。Stam の核心近傍、`pX` regularity 依存（~60 行） |
| `int_fisherY` / `int_fisherZ` | 同上（Y / Z=conv 側） | 🔴 同上 |
| `int_prod1/2/3` | `Integrable (Function.uncurry …) (volume.prod volume)`（Tonelli 3 項） | 🔴 product-measure 可積分。Gaussian 版は `measurePreserving_prod_sub_swap` shear で組む（`EPIBlachmanGaussianWitness.lean:320-326` 雛形）。一般 density 版は `pX_mom` 等が効く（各 ~60-80 行） |

**分類集計**: ✅ 自動遺伝 2 件（`int_fX/int_fY`）、🟡 Gaussian smoothness 遺伝で組める 8 件（`bdd_*` 4・`pos_pZ`・`int_X/int_Y`・`cond_int`）、🔴 `pX/pY` 追加 regularity（特に Fisher 有限性・第2モーメント・logDeriv 制御）を要する 9 件（`int_W/int_Wsq/int_inner/int_fisher{X,Y,Z}/int_prod{1,2,3}`）。

### `IsRegularDeBruijnHypV2` が供給する pX regularity（再掲、`FisherInfoV2DeBruijn.lean:226-267`）
- `pX_nn : ∀ x, 0 ≤ pX x`
- `pX_meas : Measurable pX`
- `pX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))`
- `pX_mom : Integrable (fun y => y ^ 2 * pX y) volume`（**第2モーメント有限**）

→ **足りる field**: `int_fX/int_fY`（可積分は `pX_law` + 確率測度から導出可）、🟡 群の多く（`pos_pZ` は `pX_nn`+mass、`bdd_*` は Gaussian kernel 側）。
→ **不足 field**: 🔴 群の `int_fisher*`（conv の logDeriv² 可積分＝Fisher 有限性は `pX_mom` だけでは出ない、conv-with-Gaussian の smoothness が logDeriv を抑えるが定量評価が要る）、`int_W/int_Wsq`（logDeriv 含む）。`pX_mom` は `int_inner/int_prod*` の envelope（`convKernel_envelope_integrable`）に効くが、Fisher 系には不足。

### verdict: in-house 工数壁（真の Mathlib 壁ではない）
- **Mathlib 壁ではない**: 必要なのは「conv-with-Gaussian の可積分性／有界性／正値性」で、これは Gaussian kernel の smoothness 遺伝で原理的に構成可能。Mathlib の `HasCompactSupport.contDiff_convolution_right`（`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:423`）は **Gaussian が compact support を持たないため使えない**が、これは既に in-house parametric-integral gateway（`EPIConvDensity.lean`）で回避済の既知パターン。
- **工数壁**: 19 field のうち 🔴 9 件が個別に conv-with-Gaussian 用の解析補題を要し、特に Fisher 有限性（`int_fisher*`）は Stam の核心近傍で慎重さが要る。**総計 ~400-700 行**。
- **核心バンドルではない**: 19 field は全て regularity/integrability/boundedness/positivity（`EPIBlachmanDensity.lean:695-711` の `@audit:ok` 監査が「core を bundle しない」を確認済）。conv-Fisher 不等式の核は `convex_fisher_bound` body に genuine に存在。したがって producer を組むのは load-bearing hyp 化ではなく honest な precondition 充足。

---

## 主要前提条件ボックス（事故りやすい lemma）

- **`convDensityAdd_hasDerivAt_of_regular`（`EPIConvDensity.lean:187`）**: `hregX : IsRegularDensityV2 fX` を **fX 側にも要求**。`fX := pX`（X 密度）には `IsRegularDensityV2` が供給されない（`pX_nn/meas/law/mom` のみ）。→ `pX` integrable-only + Gaussian-kernel-smooth 版 gateway を新規に組む必要（微分を Gaussian factor に寄せる）。これが (1)(4) 共通の地雷。
- **`integral_convolution`（`Convolution.lean:843`）**: `[CompleteSpace E] [CompleteSpace E']` 等の型クラス前提。`convDensityAdd`（Bochner `∫`）↔ `⋆[L,ν]`（convolution）の bridge を立てないと直接適用不可。Fubini（`integral_integral_swap`）直接ルートの方が `convDensityAdd` 定義に近い。
- **`gaussianReal_add_gaussianReal_of_indepFun`（`Real.lean:624`）**: `hXY : IndepFun X Y P` + 各 law を要求。Z_X+Z_Y の variance は `1+1=2`（heat kernel `√t·Z_X + √t·Z_Y` 経由で `t+t=2t`）。variance 算術の整合が (3c) の落とし穴。
- **`IsBlachmanConvReady` の 19 field（`EPIBlachmanDensity.lean:712-761`）**: `int_W/int_Wsq/int_inner` は `∀ lam ∈ [0,1]` 量化（consuming predicate が `∀ lam` bound を結論）。`int_prod{1,2,3}` は `volume.prod volume` 上の可積分（Tonelli）。producer はこれら 19 を **全て** 構成する必要。

---

## 自作が必要な要素（優先度順）

1. **【最優先・(1)(4) 共通基盤】`pX` integrable-only + Gaussian-kernel-smooth 版 conv gateway**
   推奨: `convDensityAdd_hasDerivAt_of_regular` の variant で `fY := g_t`（Gaussian、smooth）に微分を寄せ、`fX := pX` は可積分のみ要求。~80-120 行。落とし穴: `h_diff` field で `HasDerivAt (fun z => pX x * g_t(z-x))` を Gaussian factor の `HasDerivAt` から組む（現 gateway body `EPIConvDensity.lean:245-263` の雛形流用可）。
2. **【(1)】`IsRegularDensityV2 (convDensityAdd pX g_t)` producer** — gateway(1) + `convDensityAdd_pos` + tail decay 補題 + `integral_deriv_eq_zero`。~150 行。
3. **【(2)】`∫ convDensityAdd pX g_t = 1`** — Fubini + reflection 不変 + `integral_gaussianPDFReal_eq_one`。~40-70 行。
4. **【(3)】`convDensityAdd_assoc` + X⊥Y 一般版 `pPath_eq_convDensityAdd`** — 代数 + Fubini。~120-200 行。
5. **【(4)・最重 ~400-700 行】非 Gaussian `IsBlachmanConvReady` producer** — 19 field を conv-with-Gaussian 用に個別構成。🔴 9 field（Fisher 有限性中心）が本体。**shared sorry 補題化推奨**（後述）。

工数感: (1)-(3) で ~310-420 行、(4) で ~400-700 行。**合計 ~700-1100 行**、複数 Phase に分割推奨。

---

## Mathlib 壁の列挙（真の不在）

調査の結果、**真の Mathlib 壁（原理的不在）は 0 件**。確認した「不在」は全て in-house で迂回済 or 迂回可能:

- `HasCompactSupport.contDiff_convolution_right`（`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:423`）: **Gaussian heat kernel が compact support を持たないため適用不可**。ただし in-house parametric-integral gateway（`EPIConvDensity.lean`）で既に迂回済（同 file 冒頭 docstring `:14-24` が明記）。→ **Mathlib 壁ではなく既知の設計選択**。
- 一般 density 用 `IsBlachmanConvReady` producer: in-house 不在だが、これは in-house の未実装であって Mathlib の責務外（`IsBlachmanConvReady` は Common2026 定義）。

**shared sorry 補題化推奨**: (4) の非 Gaussian `IsBlachmanConvReady` producer は、もし 1 セッションで closeable でない場合、`sorry` + `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` の **単一 shared 補題**（例: `isBlachmanConvReady_convDensityAdd_gaussian`）に集約し、A-5 wrapper から呼ぶ形を推奨。複数 file に散らさない（`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」）。loogle 確認: `IsBlachmanConvReady` の非 Gaussian producer は `Found 0`（`rg` 確認、producer は Gaussian 1 件のみ）。

---

## 撤退ラインへの距離

親計画 `epi-stam-to-conclusion-phaseA-plan` の A-5 line は既に `h_pos_stam` バンドルに 4 項目を caller 供給として localize 済（R-3‴ closure の設計）。本調査の結論:

- **新規撤退ライン発動: なし**。4 項目とも in-house で closeable（(1)-(3) 確実、(4) 工数大だが原理的壁なし）。
- 既存の `sorry` + `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`（`EPIStamToBridge.lean:1342/1344` の `hXYZXY` joint independence、`csiszarGap_antitoneOn_Icc_zero_one:1259` rescale、`csiszarGap1Source_continuousOn:1179` continuity）の枠内に、本 4 項目の producer 未完成も吸収できる。
- ただし **(4) が ~400-700 行で 1 Phase に収まらない**場合、`isBlachmanConvReady_convDensityAdd_gaussian` を独立 shared sorry 補題として切り出し、A-5 producer はそれを呼ぶ形に縮退（撤退口は sorry + `@residual`、仮説束化は禁止）。これは縮退案であって新規撤退ラインではない（signature は本来形を保つ）。

---

## end-to-end closure feasibility 総合判定

| 項目 | closeable? | 工数 | 本体難所 |
|---|---|---|---|
| (1) `IsRegularDensityV2` | ✅ | ~150 行（+ gateway variant ~100） | `pX` integrable-only gateway 新規 |
| (2) `∫ = 1` | ✅ | ~40-70 行 | Fubini bridge |
| (3) `h_conv_id` | ✅ | ~120-200 行 | `convDensityAdd_assoc` + X⊥Y 一般 pPath |
| (4) `IsBlachmanConvReady` | ✅（工数大） | ~400-700 行 | 🔴 9 field（Fisher 有限性・logDeriv 制御） |

**総合**: 4 項目すべて in-house で closeable、**真の Mathlib 壁は 0 件**。最重は (4) の非 Gaussian `IsBlachmanConvReady` producer（~400-700 行）。

**次 Phase 推奨着手順**:
1. **共通基盤先行**: `pX` integrable-only + Gaussian-kernel-smooth gateway variant（(1)(4) の 🟡 group が依存）。
2. **(2) → (1)** の順（軽い (2) で Fubini/normalization パターンを確立、それを (1) の `integral_deriv_eq_zero` / tail に再利用）。
3. **(3)**: `convDensityAdd_assoc` + X⊥Y 一般 pPath（独立、並行可）。
4. **(4) 最後**: 🟡 group（10 件）を gateway variant + `convDensityAdd_pos` 2-段版で先に潰し、🔴 group（9 件、Fisher 中心）を shared sorry 補題に集約しつつ個別 close。1 Phase で無理なら `isBlachmanConvReady_convDensityAdd_gaussian` を sorry + `@residual` で切り出し、A-5 を type-check done で先に通す。
