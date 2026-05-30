# EPI Blachman density route — Gaussian witness `IsBlachmanConvReady` 在庫調査

> 親計画: [`docs/shannon/epi-wall-reattack-plan.md`](epi-wall-reattack-plan.md)（撤退ライン参照）。
> 対象述語: `IsBlachmanConvReady` (`Common2026/Shannon/EPIBlachmanDensity.lean:708`, 20 field) + `IsRegularDensityV2` (`Common2026/Shannon/FisherInfoV2.lean:124`, 6 field)。
> 目的: `fX = gaussianPDFReal mX vX`, `fY = gaussianPDFReal mY vY` で両述語を満たす **proven inhabitant** を構築して density route の非vacuousness を機械確認する。
> 本ファイルは inventory のみ。実装・計画起草はしない。

---

## 一行サマリ

**★linchpin (Gaussian PDF 点ごと畳み込み閉形式) は Mathlib 不在 (`Found 0` × 2)。ただし Mathlib に measure-level 経路 (`gaussianReal_conv_gaussianReal` + `mconv_withDensity_eq_mlconvolution₀` + `gaussianReal_of_var_ne_zero`) が全部揃っており、repo self-build で導出可能 (壁ではない、見積 ~120–200 行、ENNReal↔Real + a.e.→pointwise の橋が難所)。** 20 field の内訳: **既存直結 6 / 軽い self-build 8 / 重い (linchpin 依存 or 2D shear) 6**。最重要難所は `int_prod1/2/3` (非分離 2D Gaussian-tail 可積分性、shear 変数変換 `(z,x)↦(z,z-x)` が必要)。**撤退ライン発動: NO** (真の Mathlib 壁は 0 件、全 field は self-build 可能と判定)。`IsRegularDensityV2` 6 field は全て既存の Gaussian discharge (`isRegularDensity_gaussianReal_of_law` の field 群) で **直結**。

---

## linchpin の結論 (最優先)

**問い**: `convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z = gaussianPDFReal (mX+mY) (vX+vY) z` (点ごと、`convDensityAdd p q z := ∫ x, p x * q (z-x) ∂volume`, `EPIConvDensity.lean:40`) は Mathlib にあるか？

**結論: 点ごと密度畳み込み閉形式は Mathlib 不在。だが measure-level 経路が完備で repo self-build 可能 (壁ではない)。**

### loogle 結果 (verbatim)
- `ProbabilityTheory.gaussianPDFReal, MeasureTheory.convolution` → **`Found 0 declarations`**
- `(ProbabilityTheory.gaussianPDFReal _ _ _) * (ProbabilityTheory.gaussianPDFReal _ _ _)` → `Found 5 ... Of these, 0 match your pattern(s)` (= 点ごと畳み込み積の閉形式なし)
- `HMul.hMul, ProbabilityTheory.gaussianPDFReal, Eq` → `Found 5`: `gaussianPDFReal_def` / `gaussianPDFReal_inv_mul` / `gaussianPDFReal_mul` / `gaussianReal_comap_apply` / `gaussianReal_map_symm_apply` — どれも畳み込みではない (`gaussianPDFReal_mul` はスケーリング `gaussianPDFReal μ v (c x)` 型)

### measure-level 経路 (Mathlib に全部存在 — self-build の素材)
| 部品 | file:line | verbatim signature (型クラス前提含む) | 役割 |
|---|---|---|---|
| `gaussianReal_conv_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | **measure 畳み込み閉形式** (`∗` = additive `mconv`)。型クラス前提なし |
| `gaussianReal_of_var_ne_zero` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:203` | `lemma gaussianReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` | `gaussianReal = withDensity (gaussianPDF …)` の同一視。`gaussianPDF : ℝ≥0∞`-valued (note: `gaussianPDFReal = (gaussianPDF …).toReal`) |
| `mconv_withDensity_eq_mlconvolution₀` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:757` | `theorem mconv_withDensity_eq_mlconvolution₀ {f g : G → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : μ.withDensity f ∗ₘ μ.withDensity g = μ.withDensity (f ⋆ₘₗ[μ] g)` — 前提 `variable {G : Type*} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [SFinite μ] [IsMulLeftInvariant μ]`。`to_additive` 版が `volume` (= ℝ の加法群) に適用可 | **density-level 畳み込み**へ橋渡し: `withDensity f ∗ withDensity g = withDensity (f ⋆ₘₗ g)` |
| `mlconvolution` (notation `⋆ₘₗ`) | `Mathlib/Analysis/LConvolution.lean:50` (`mlconvolution_def:68`) | `(f ⋆ₘₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`、additive 版 `∫⁻ y, f y * g (x - y) ∂μ` | **`ℝ≥0∞`-valued lintegral 畳み込み** (≠ `convDensityAdd` の `ℝ`-valued Bochner ∫) |

### 難所 (なぜ「直結」ではないか)
1. **`mlconvolution` は `ℝ≥0∞`-valued lintegral**、`convDensityAdd` は `ℝ`-valued Bochner `∫`。両者の橋には `ofReal_integral_eq_lintegral_ofReal` 系 + 非負性 + 可積分性 (= 既に `int_fX`/`int_fY` で確保) が要る。
2. measure 等式 `withDensity (gaussianPDF mX vX ⋆ₘₗ gaussianPDF mY vY) = withDensity (gaussianPDF (mX+mY)(vX+vY))` から密度の **a.e.-equality** しか出ない (`withDensity` injective は a.e. レベル)。`convDensityAdd … z = gaussianPDFReal (sum) z` は **点ごと (∀z)** が欲しい (`pos_pZ` / `int_fisherZ` が ∀z を要求)。a.e.→pointwise の upgrade には両辺の連続性 (`gaussianPDFReal` は `Continuous`、`convDensityAdd` の連続性は別途) が要る。
3. additive `to_additive` 名 (`conv_withDensity_eq_mlconvolution₀` 等) の存在は loogle で確認済 (`MeasureTheory.conv_withDensity_eq_lconvolution` / `conv_withDensity_eq_mlconvolution₀` が `Found`)。

**self-build 見積: ~120–200 行** (measure 等式 → withDensity → mlconvolution → ENNReal↔Real → a.e.→pointwise の 5 段)。**真の Mathlib 壁ではない** (素材は全部存在、組み立てのみ)。

**代替**: linchpin を経由せず `pos_pZ` を「2 つの正値関数の畳み込みは正」(`integral_pos` 型 generic atom) で、`int_fisherZ` を `convDensityAdd_comm` + 直接可積分性で個別に閉じる route も理論上あるが、`int_fisherZ` の `logDeriv (convDensityAdd …)` を扱うには結局 Gaussian sum 形への帰着が最短なので、linchpin の self-build が全体最短と判定。

---

## 既存 repo Gaussian 部品 (verbatim 確認済)

| 補題 | file:line | verbatim signature (`[型クラス前提]` + 引数型 + 結論形) | 用途 |
|---|---|---|---|
| `differentiable_gaussianPDFReal` | `FisherInfoGaussian.lean:68` | `lemma differentiable_gaussianPDFReal (m : ℝ) (v : ℝ≥0) : Differentiable ℝ (gaussianPDFReal m v)` | `IsRegularDensityV2.diff` |
| `deriv_gaussianPDFReal` | `FisherInfoGaussian.lean:75` | `lemma deriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : deriv (gaussianPDFReal m v) x = -(x - m) / v * gaussianPDFReal m v x` | `bdd_fX'`/`int_X`/`int_Y` の deriv 形 |
| `logDeriv_gaussianPDFReal` | `FisherInfoGaussian.lean:298` | `lemma logDeriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : logDeriv (gaussianPDFReal m v) x = -(x - m) / v` | `scoreWeight`/`int_W`/`int_Wsq`/`int_fisherX/Y` の score 形 |
| `tendsto_gaussianPDFReal_atBot` | `FisherInfoGaussian.lean:127` | `lemma tendsto_gaussianPDFReal_atBot (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Filter.Tendsto (gaussianPDFReal m v) Filter.atBot (nhds 0)` | `IsRegularDensityV2.tail_bot` |
| `tendsto_gaussianPDFReal_atTop` | `FisherInfoGaussian.lean:154` | `lemma tendsto_gaussianPDFReal_atTop (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Filter.Tendsto (gaussianPDFReal m v) Filter.atTop (nhds 0)` | `IsRegularDensityV2.tail_top` |
| `integrable_deriv_gaussianPDFReal` | `FisherInfoGaussian.lean:210` | `lemma integrable_deriv_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable (deriv (gaussianPDFReal m v)) volume` | `IsRegularDensityV2.integrable_deriv` |
| `integral_deriv_gaussianPDFReal_eq_zero` | `FisherInfoGaussian.lean:231` | `lemma integral_deriv_gaussianPDFReal_eq_zero (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫ x, deriv (gaussianPDFReal m v) x ∂volume = 0` | `IsRegularDensityV2.integral_deriv_eq_zero` |
| `integrable_sub_mul_gaussianPDFReal` | `FisherInfoGaussian.lean:178` (**`private`**) | `private lemma integrable_sub_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable (fun x => (x - m) * gaussianPDFReal m v x) volume` | `int_X`/`int_Y` の素材。**private = file-scoped。witness を別 file に置くと不可視 → witness は同 file か public 化が必要** |
| `integrable_logDeriv_sq_mul_gaussianPDFReal` | `FisherInfoV2.lean:181` (**`private`**) | `private lemma integrable_logDeriv_sq_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable (fun x => ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x) volume` | **`int_fisherX`/`int_fisherY` の直接素材** (`(logDeriv f)² f = ((x-m)/v)² f`)。**private 注意** |
| `fisherInfoOfDensity_gaussianPDFReal` | `FisherInfoV2.lean:273` | `theorem fisherInfoOfDensity_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1 / (v : ℝ))` | 非vacuousness 確認後の Fisher 値 (`1/v`) |
| `isRegularDensity_gaussianReal_of_law` | `FisherInfoGaussian.lean:280` | `noncomputable def isRegularDensity_gaussianReal_of_law {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hX_law : P.map X = gaussianReal m v) : IsRegularDensity X P` | **V1 `IsRegularDensity` 用** (V2 ではない)。field 構成は V2 の素材として再利用可 |

### Mathlib Gaussian 部品 (witness が直接呼ぶ)
| 補題 | file:line | verbatim signature | 用途 |
|---|---|---|---|
| `gaussianPDFReal_pos` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:61` | `lemma gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x` | `IsRegularDensityV2.pos` |
| `gaussianPDFReal_nonneg` | `…Gaussian/Real.lean:66` | `lemma gaussianPDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPDFReal μ v x` | 非負性 (ENNReal 橋) |
| `integrable_gaussianPDFReal` | `…Gaussian/Real.lean:82` | `lemma integrable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Integrable (gaussianPDFReal μ v)` (= `Integrable (gaussianPDFReal μ v) volume`, 型クラス前提なし) | **`int_fX`/`int_fY` 直結** |
| `integral_gaussianPDFReal_eq_one` | `…Gaussian/Real.lean:121` | `lemma integral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫ x, gaussianPDFReal μ v x = 1` | witness の `hnorm` (∫=1) |
| `measurable_gaussianPDFReal` | `…Gaussian/Real.lean:72` (`@[fun_prop]`) | `lemma measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDFReal μ v)` | 各 field の AEStronglyMeasurable side |

---

## witness signature の形 (consumer 確認済)

`IsStamCauchySchwarzOptimal` (`EPIStamInequalityBody.lean:282`) / `IsStamCondExpCSHyp` (`EPIStamStep12Body.lean:214`) が要求するのは:
- `IsRegularDensityV2 fX` / `IsRegularDensityV2 fY`
- `∫ x, fX x ∂volume = 1` / 同 fY
- `IsBlachmanConvReady fX fY`

`convex_fisher_bound_of_ready` (`EPIBlachmanDensity.lean:783`) verbatim:
```
theorem convex_fisher_bound_of_ready (fX fY : ℝ → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hnormX : ∫ x, fX x ∂volume = 1) (hnormY : ∫ x, fY x ∂volume = 1)
    (hready : IsBlachmanConvReady fX fY) : …
```
→ **witness が供給すべきもの**: `hregX/hregY` (= `IsRegularDensityV2 (gaussianPDFReal m v)`, 下記 §IsRegularDensityV2 で全 field 直結), `hnormX/hnormY` (= `integral_gaussianPDFReal_eq_one`, 直結), `hready` (= 本調査の 20 field 構築)。型クラス前提は **`ℝ → ℝ` 上の述語なので追加 `[…]` なし** (Ω 不在版)。witness signature には `{mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0)` のみ漏れる見込み。

---

## `IsRegularDensityV2 (gaussianPDFReal m v)` — 6 field (全て直結)

| field | 型 | 当て先 (file:line) | 状態 |
|---|---|---|---|
| `diff` | `Differentiable ℝ f` | `differentiable_gaussianPDFReal m v` (`FisherInfoGaussian.lean:68`) | ✅ 既存直結 |
| `pos` | `∀ x, 0 < f x` | `fun x => gaussianPDFReal_pos m v x hv` (`Gaussian/Real.lean:61`) | ✅ 既存直結 |
| `tail_bot` | `Tendsto f atBot (nhds 0)` | `tendsto_gaussianPDFReal_atBot m hv` (`:127`) | ✅ 既存直結 |
| `tail_top` | `Tendsto f atTop (nhds 0)` | `tendsto_gaussianPDFReal_atTop m hv` (`:154`) | ✅ 既存直結 |
| `integrable_deriv` | `Integrable (deriv f) volume` | `integrable_deriv_gaussianPDFReal m hv` (`:210`) | ✅ 既存直結 |
| `integral_deriv_eq_zero` | `∫ deriv f = 0` | `integral_deriv_gaussianPDFReal_eq_zero m hv` (`:231`) | ✅ 既存直結 |

→ **`IsRegularDensityV2 (gaussianPDFReal m v)` は ~10 行で構築可能** (V1 の `isRegularDensity_gaussianReal_of_law:280` と同じ field 群を V2 structure に再配線するだけ)。これ自体が in-tree に未だ無い (`rg` で `IsRegularDensityV2 (gaussianPDFReal` → 0 hit) ので witness 構築の最初の step。

---

## `IsBlachmanConvReady` — 20 field per-field 在庫

凡例: 状態 = **既存直結** / **軽 self-build** (~5–30 行、既存補題 + 標準 measure 論) / **重** (linchpin 依存 or 2D shear、~30–80 行)。

| # | field | 型 (verbatim integrand) | 必要 API (file:line, verbatim sig, `[型クラス]`) | 状態 | 見積 | 難所 |
|---|---|---|---|---|---|---|
| 1 | `int_fX` | `Integrable fX volume` | `integrable_gaussianPDFReal mX vX` (`Gaussian/Real.lean:82`, `Integrable (gaussianPDFReal μ v)`, 前提なし) | ✅ 既存直結 | 1 行 | — |
| 2 | `int_fY` | `Integrable fY volume` | 同上 (mY vY) | ✅ 既存直結 | 1 行 | — |
| 3 | `bdd_fX` | `∃ M, ∀ w, \|fX w\| ≤ M` | `gaussianPDFReal m v ≤ (√(2πv))⁻¹` (sup at `x=m`)。当て先: `Real.exp_le_one`/`exp_neg…≤1` + `gaussianPDFReal_nonneg:66`。Mathlib に `gaussianPDFReal` の sup 補題は無い (loogle 確認は下記壁節) | 🟡 軽 self-build | ~12 行 | `exp(-(x-m)²/2v) ≤ 1` |
| 4 | `bdd_fX'` | `∃ M, ∀ w, \|deriv fX w\| ≤ M` | `deriv_gaussianPDFReal:75` (`= -(x-m)/v · f`) → `\|(x-m)/v\| · f(x)` の sup。`(x-m)·exp(-(x-m)²/2v)` の有界性 (= `sup_x \|x\|exp(-ax²)` 評価)。Mathlib に直接補題なし | 🟡 軽 self-build | ~25 行 | linear×Gaussian decay の sup。`x·exp(-ax²)` の最大値 (微分=0 点) or 粗い `\|x\|exp(-ax²/2)·exp(-ax²/2)` bound |
| 5 | `bdd_fY` | `∃ M, ∀ w, \|fY w\| ≤ M` | #3 と同型 | 🟡 軽 self-build | ~12 行 | #3 と同 |
| 6 | `bdd_fY'` | `∃ M, ∀ w, \|deriv fY w\| ≤ M` | #4 と同型 | 🟡 軽 self-build | ~25 行 | #4 と同 |
| 7 | `pos_pZ` | `∀ z, 0 < convDensityAdd fX fY z` | **(A) linchpin 経由**: `convDensityAdd … z = gaussianPDFReal (mX+mY)(vX+vY) z` → `gaussianPDFReal_pos:61`。**(B) generic atom**: `∫ x, fX x·fY(z-x) > 0` を `integral_pos`/`setIntegral_pos` 型 + 被積分関数 > 0 a.e. + 可積分 (#int_fX 経由) で。route B は linchpin 不要 | 🔴 重 (route A) / 🟡 (route B) | A: linchpin / B: ~30 行 | route B は `0 < ∫ (>0 連続関数)` の Mathlib atom (`integral_pos_of_pos`?) 当て先確認要 |
| 8 | `int_X` | `∀ z, Integrable (fun x => deriv fX x · fY(z-x)) volume` | `deriv_gaussianPDFReal:75` → `(linear)·gaussian·gaussian(z-x)`。`integrable_sub_mul_gaussianPDFReal:178` (private!) + `gaussianPDFReal(z-x)` 有界 (#bdd_fY) → `Integrable.bdd_mul` 型 | 🟡 軽 self-build | ~20 行 | private 補題依存 (visibility)。`(x-m)gaussian` integrable × bounded shift |
| 9 | `int_Y` | `∀ z, Integrable (fun x => fX x · deriv fY(z-x)) volume` | `int_fX` + `deriv fY(z-x)` 有界 (#bdd_fY') → `Integrable.bdd_mul` | 🟡 軽 self-build | ~18 行 | bounded×integrable |
| 10 | `cond_int` | `∀ z, Integrable (condDensityX fX fY z) volume` | `condDensityX fX fY z x = fX x·fY(z-x)/pZ(z)` (`EPIBlachmanDensity.lean:49`, pZ(z) は定数) = `(1/pZ z)·(fX x · fY(z-x))`。`int_fX`×bounded(#bdd_fY) → `Integrable.bdd_mul` → `.const_mul` | 🟡 軽 self-build | ~20 行 | `pZ z ≠ 0` (= `pos_pZ` #7 依存) |
| 11 | `int_W` | `∀lam∈[0,1] ∀z, Integrable (scoreWeight·condDensityX) volume` | `scoreWeight = lam·logDeriv fX x + (1-lam)·logDeriv fY(z-x)` (`:53`), `logDeriv_gaussianPDFReal:298` (= `-(x-m)/v`, linear)。linear × cond_int(#10)。`(x-m)`·integrable は `integrable_sub_mul`/`Integrable.bdd_mul` 組合せ | 🟡 軽 self-build | ~30 行 | 2 項 (logDeriv fX linear in x、logDeriv fY linear in z-x) × cond_int |
| 12 | `int_Wsq` | `∀lam∈[0,1] ∀z, Integrable (scoreWeight²·condDensityX) volume` | scoreWeight² = (linear in x,z-x)²、×cond_int。`integrable_logDeriv_sq_mul_gaussianPDFReal:181` (private!) が `((x-m)/v)²·gaussian` を供給。展開 (a+b)² = 3 項 | 🔴 重 | ~40 行 | quadratic×gaussian×gaussian(shift)。展開項数多、private 依存 |
| 13 | `int_inner` | `∀lam∈[0,1], Integrable (fun z => (∫ x, scoreWeight²·condDensityX) · convDensityAdd) volume` | 内側 ∫ (= weighted Fisher of cond) × pZ(z)。z についての可積分性。**`int_Wsq` の z-積分 × pZ** | 🔴 重 | ~50 行 | 内側積分が z の関数として可積分か。Gaussian の場合 closed-form (= score variance) で `c/(vX+vY)` 型定数になる見込みだが証明は重 |
| 14 | `int_fisherX` | `Integrable (fun x => (logDeriv fX x)²·fX x) volume` | **`integrable_logDeriv_sq_mul_gaussianPDFReal mX hvX` (`FisherInfoV2.lean:181`, private!)** + `logDeriv_gaussianPDFReal:298` で `(logDeriv f)² = ((x-m)/v)²` 書換 | 🟡 軽 self-build (private visibility が課題) | ~8 行 | **private 補題を public 化 or witness を同 file に** |
| 15 | `int_fisherY` | `Integrable (fun x => (logDeriv fY x)²·fY x) volume` | 同上 (mY vY) | 🟡 軽 self-build | ~8 行 | #14 と同 (private) |
| 16 | `int_fisherZ` | `Integrable (fun z => (logDeriv pZ z)²·pZ z) volume` | **linchpin 必須**: `pZ = convDensityAdd fX fY = gaussianPDFReal (mX+mY)(vX+vY)` に帰着 → `int_fisherX` と同補題。linchpin 無しでは `logDeriv (convDensityAdd …)` の閉形式が無く詰む | 🔴 重 (linchpin 依存) | linchpin + ~10 行 | **linchpin self-build がここで効く** |
| 17 | `int_prod1` | `Integrable (uncurry fun z x => (logDeriv fX x)²·fX x·fY(z-x)) (volume.prod volume)` | **2D 非分離 (z-x 結合)**。shear `(z,x)↦(z,z-x)` (`measurePreserving_prod_sub`/`measurePreserving_prod_div:368`) で `(z',x)` に変数変換 → 分離形 `g(x)·h(z')` → `Integrable.mul_prod` (`Prod.lean:346`) | 🔴 重 | ~50 行 | shear + `mul_prod`。素材は揃うが組立重 |
| 18 | `int_prod2` | `Integrable (uncurry fun z x => (logDeriv fY(z-x))²·fX x·fY(z-x)) (volume.prod volume)` | 同 shear、`(logDeriv fY)²·fY` 側を z'=z-x に集約 | 🔴 重 | ~50 行 | #17 と同 |
| 19 | `int_prod3` | `Integrable (uncurry fun z x => logDeriv fX x·fX x·(logDeriv fY(z-x)·fY(z-x))) (volume.prod volume)` | 同 shear、cross 項。`(logDeriv fX·fX)` と `(logDeriv fY·fY)` が分離 → `mul_prod` | 🔴 重 | ~45 行 | #17 と同 |
| 20 | (`pos_pZ` は #7、フィールド総数 20 = int_fX/fY + bdd×4 + pos_pZ + int_X/Y + cond_int + int_W/Wsq + int_inner + int_fisherX/Y/Z + int_prod1/2/3) | | | | | |

### 重要 API verbatim (上テーブル参照先)
- `Integrable.mul_prod` (`Mathlib/MeasureTheory/Integral/Prod.lean:346`):
  `theorem Integrable.mul_prod {L : Type*} [NormedRing L] {f : α → L} {g : β → L} (hf : Integrable f μ) (hg : Integrable g ν) : Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν)`
  — **分離形 `f z.1 * g z.2` のみ**。`int_prod` の `fY(z-x)` 結合は分離でないので shear 前処理が必須。
- `measurePreserving_prod_div` (`Mathlib/MeasureTheory/Group/Prod.lean:368`, additive 名 `measurePreserving_prod_sub`):
  `theorem measurePreserving_prod_div [IsMulRightInvariant ν] : MeasurePreserving (fun z : G × G => (z.1, z.2 / z.1)) (μ.prod ν) (μ.prod ν)` — additive: `(x,y) ↦ (x, y-x)`。前提 `variable {G} [Group G] {mG : MeasurableSpace G} ... [MeasurableInv G]` + `[IsMulRightInvariant ν]`。`ℝ`+`volume` で発火。
- `integrable_prod_iff` (`Mathlib/MeasureTheory/Integral/Prod.lean:278`):
  `theorem integrable_prod_iff ⦃f : α × β → E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ` — shear を使わない代替 route (Fubini-Tonelli 直接)。

---

## 主要前提条件ボックス (事故が起きやすい lemma)

- **`mconv_withDensity_eq_mlconvolution₀`** (linchpin の心臓): 前提 `[Group G] [MeasurableMul₂ G] [MeasurableInv G] [SFinite μ] [IsMulLeftInvariant μ]` + `(hf hg : AEMeasurable …)`。`ℝ` の加法群 + `volume` で全 instance 発火するが、結論は **`μ.withDensity f ∗ₘ μ.withDensity g = μ.withDensity (f ⋆ₘₗ g)`** = measure 等式 (≠ 点ごと密度)。点ごとに落とすのは別作業 (a.e.→pointwise)。
- **`gaussianReal_of_var_ne_zero`**: 結論は `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` で **`gaussianPDF` (ℝ≥0∞-valued)**、`gaussianPDFReal` ではない。`gaussianPDFReal = (gaussianPDF …).toReal` の橋 (`toReal_gaussianPDF`, `FisherInfoGaussian.lean:64` で既使用) が要る。
- **`Integrable.mul_prod`**: 分離 `f z.1 * g z.2` 専用。`int_prod` は非分離 → **必ず shear が先**。これを忘れると LSP 第 1 戻りで型 mismatch。
- **`measurePreserving_prod_div`**: `[IsMulRightInvariant ν]` が要る (`volume` on `ℝ` は両側不変なので OK)、additive 名 (`measurePreserving_prod_sub`) で呼ぶこと。
- **private 補題 2 件** (`integrable_sub_mul_gaussianPDFReal:178`, `integrable_logDeriv_sq_mul_gaussianPDFReal:181`): **file-scoped private**。witness を別 file に置くと不可視。→ witness を同 file (`FisherInfoV2.lean`/`FisherInfoGaussian.lean`) に置くか、これらを public 化 (CLAUDE.md「private は file-scoped」)。`int_fisherX/Y` (#14/#15) と `int_X/Y` (#8/#9) が直撃。

---

## 自作が必要な要素 (優先度順)

1. **linchpin: `convDensityAdd_gaussian_closed_form`** (#7A/#16): `convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) = gaussianPDFReal (mX+mY)(vX+vY)` (a.e. → 連続性で pointwise)。~120–200 行。**最優先 — #16 `int_fisherZ` は linchpin 無しでは詰む**。route B (#7B generic positivity) で `pos_pZ` だけは linchpin 回避可能だが `int_fisherZ` は不可避。
2. **`IsRegularDensityV2 (gaussianPDFReal m v)`** instance (~10 行、6 field 全直結): witness 構築の前提。
3. **`int_prod1/2/3`** の shear route (~50 行 × 3): `measurePreserving_prod_div` + `Integrable.mul_prod`。素材完備だが組立が最重量級。
4. **private 補題 2 件の public 化** (or witness 同居): visibility 解決。
5. **`bdd_fX'`/`bdd_fY'`** (#4/#6): `\|x\|·exp(-ax²)` の sup 評価 (~25 行 × 2)。Mathlib に直接補題なし、粗 bound で十分。
6. **`int_Wsq`/`int_inner`** (#12/#13): quadratic score × cond density の可積分性 (~40–50 行)。

工数感: **linchpin (~150) + RegularV2 (~10) + 残 18 field (~400) = ~560 行**。Fano Phase 3 (~150 行) の 3–4 倍。density route の plumbing は EPIBlachmanDensity 本体 (`convex_fisher_bound`, @audit:ok 達成済) と同規模。

---

## Mathlib 壁の列挙 (真に不在 = `@residual(wall:…)` 対象)

**真の Mathlib 壁は 0 件。** 全 field は既存素材の組立で self-build 可能と判定。以下は「直接補題が無い」が「素材から導出可能」なもの (壁ではない):

| 項目 | loogle 確認 | 判定 |
|---|---|---|
| Gaussian PDF 点ごと畳み込み閉形式 | `gaussianPDFReal, convolution` → `Found 0`; `(gaussianPDFReal _)*(gaussianPDFReal _)` → `0 match` | **壁ではない** (measure-level `gaussianReal_conv_gaussianReal` + `mconv_withDensity_eq_mlconvolution₀` で self-build) |
| `gaussianPDFReal` の sup (有界性) | (#3 用) Mathlib に sup 補題なし | **壁ではない** (`exp ≤ 1` で粗 bound) |
| `\|x\|·exp(-ax²)` の sup | (#4 用) | **壁ではない** (初等解析 self-build) |
| 非分離 2D Gaussian-tail 可積分性 | `Integrable, prod, gaussianPDFReal` → `Found 0` | **壁ではない** (shear `measurePreserving_prod_div` + `Integrable.mul_prod`) |

→ **shared sorry 補題化候補なし** (壁が無いため)。linchpin (`convDensityAdd_gaussian_closed_form`) は壁ではなく self-build target なので `@residual` でなく通常の補題として実装する。万一 self-build が当該セッションで詰まった場合の撤退口は `sorry + @residual(wall:gaussian-conv-closed-form)` (linchpin 1 点のみ)、ただし素材完備のため壁分類は誤りになる見込み (plan 1 つで closure 可能 = `@residual(plan:…)` が正しい分類)。

---

## 撤退ラインへの距離

親計画 `epi-wall-reattack-plan.md` の非vacuousness 撤退ライン (`IsBlachmanConvReady` の Gaussian witness が構築できない → density route を staged のまま据置):

**判定: 発動しない (NO)。**
- 真の Mathlib 壁が 0 件。linchpin を含め全 field の素材が Mathlib + repo に揃う。
- linchpin は measure-level 経路 (`gaussianReal_conv_gaussianReal` + `mconv_withDensity_eq_mlconvolution₀` + `gaussianReal_of_var_ne_zero`) で self-build 可能と確認済 (壁ではない)。
- 工数 ~560 行は大きいが「組立のみ」で数学的未解決点なし。

**新規撤退ライン提案** (縮退案、sorry + `@residual` 形式、仮説束化禁止):
- **撤退 R1**: linchpin self-build が 1 セッションで閉じない場合 → linchpin のみ `sorry + @residual(plan:gaussian-conv-closed-form)` (壁ではないので `wall:` でなく `plan:`)、残 19 field は genuine 構築を継続。これで「#16 `int_fisherZ` 以外の 19 field は proven」状態を作り、非vacuousness の **partial** 確認 (= `IsBlachmanConvReady` から `int_fisherZ` だけ抜いた 19-field 版 witness) を達成。
- **撤退 R2**: `int_prod1/2/3` の shear 組立が詰まる場合 → 該当 3 field のみ `sorry + @residual(plan:gaussian-prod-shear)`、残 17 field genuine。
- いずれも **load-bearing hypothesis bundling は禁止**: witness を `IsGaussianWitnessHypothesis` 等の predicate に核を抱えさせて `sorry` を消すのは不可。各 field は genuine 構築 or sorry+residual で正直に残す。

---

## 着手 skeleton

`Common2026/Shannon/EPIBlachmanGaussianWitness.lean` (private 補題依存のため `FisherInfoV2.lean`/`FisherInfoGaussian.lean` 拡張も選択肢) の出だし:

```lean
import Common2026.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.LConvolution
import Common2026.Shannon.FisherInfoV2          -- IsRegularDensityV2, fisherInfoOfDensity, private Gaussian 素材
import Common2026.Shannon.FisherInfoGaussian    -- gaussianPDFReal 微分/tail/integrable 群
import Common2026.Shannon.EPIConvDensity        -- convDensityAdd
import Common2026.Shannon.EPIBlachmanDensity    -- IsBlachmanConvReady, condDensityX, scoreWeight

namespace Common2026.Shannon.EPIBlachmanGaussianWitness

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EPIConvDensity
open InformationTheory.Shannon.EPIBlachmanDensity
open scoped ENNReal NNReal

/-- linchpin: 密度レベル Gaussian 畳み込み閉形式 (measure-level 経路 self-build)。
@residual(plan:gaussian-conv-closed-form) — measure 経路素材は完備、組立のみ。 -/
theorem convDensityAdd_gaussian_closed_form
    {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) :
    convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)
      = gaussianPDFReal (mX + mY) (vX + vY) := by
  sorry

/-- `IsRegularDensityV2 (gaussianPDFReal m v)` — 6 field 全直結。 -/
theorem isRegularDensityV2_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Common2026.Shannon.FisherInfoV2.IsRegularDensityV2 (gaussianPDFReal m v) := by
  sorry

/-- **Gaussian witness**: density route の非vacuousness 確証。 -/
theorem isBlachmanConvReady_gaussianPDFReal
    {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) :
    IsBlachmanConvReady (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) := by
  sorry  -- 20 field 構築 (per-field テーブル参照)

end Common2026.Shannon.EPIBlachmanGaussianWitness
```

最初に埋めるのは `convDensityAdd_gaussian_closed_form` (linchpin) → `isRegularDensityV2_gaussianPDFReal` (6 field) → witness の 20 field を分類順 (既存直結 → 軽 → 重) で。
