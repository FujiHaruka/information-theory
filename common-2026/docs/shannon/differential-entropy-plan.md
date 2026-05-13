# 微分エントロピー + Gaussian 最大エントロピー ムーンショット計画 🌙 (E-9)

(E-9 / [docs/moonshot-seeds.md](../moonshot-seeds.md), 2026-05-13 起草)

Cover-Thomas 8.1 (微分エントロピー定義), 8.6.1 (translation / scaling), 9.6 (Gaussian
max-entropy)。**現プロジェクトの discrete 一辺倒からの最大の枝分かれ**で、Gaussian channel
capacity (Cover-Thomas 9.1) / EPI (17) への入り口。Mathlib `differentialEntropy` は不在のため
**新規定義 + 上流 PR 候補多数**。

## 進捗

- [ ] Phase 0 — Mathlib 整備度調査結果サマリ ✅ (plan 起草時点で完了)
- [ ] Phase A — `differentialEntropy` 定義 + 基本可積分性 📋
- [ ] Phase B — 基本性質: translation invariance / scaling 📋
- [ ] Phase C — `h(𝒩(μ, σ²)) = (1/2) log (2πe σ²)` 計算 📋
- [ ] Phase D — Max-entropy 定理 (variance 固定下の上界 + 等号 iff Gaussian) 📋
- [ ] Phase E — KL bridge: `klDiv μ (gaussianReal m σ²) = h_𝒩 - h(μ) + (μ-差)` 形 📋

## ゴール / Approach

**最終定理 (Phase D 主形)**: 確率測度 `μ : Measure ℝ` が Lebesgue 絶対連続 + 平均 `m`, 分散 ≤
`σ² > 0` のとき
```
differentialEntropy μ ≤ (1/2) * Real.log (2 * π * Real.exp 1 * σ²)
```
等号は `μ = gaussianReal m ⟨σ², _⟩`。

**Approach (3 段戦略)**:

1. **定義 (Phase A)**: `differentialEntropy μ := -∫ x, (μ.rnDeriv volume x).toReal *
   Real.log ((μ.rnDeriv volume x).toReal) ∂volume`。
   - **shape-driven 選択**: Mathlib `Real.negMulLog x = -x * Real.log x` (`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog:?`) に合わせて
     `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume`
     と書く。`Real.negMulLog` 経由なら `negMulLog_zero = 0`, `negMulLog_nonneg` (on `[0,1]`),
     `continuous_negMulLog` などが直接呼べる。これは **既存 `Entropy.lean` (discrete) と同じ
     shape** (`entropy μ X := ∑ x, Real.negMulLog ((μ.map X).real {x})`), `Bridge.lean` の
     継承性を維持。
2. **Gaussian 計算 (Phase C)**: `gaussianReal m ⟨σ², _⟩` の rnDeriv が `gaussianPDF m σ²`
   (Mathlib `rnDeriv_gaussianReal` で `=ₐₛ`)。PDF `f(x) = (√(2πσ²))⁻¹ exp(-(x-m)²/(2σ²))`
   ⟹ `log f(x) = -(1/2) log (2πσ²) - (x-m)²/(2σ²)`。よって
   `h(𝒩) = ∫ f(x) [(1/2) log(2πσ²) + (x-m)²/(2σ²)] dx = (1/2) log(2πσ²) + (1/2)`
   `= (1/2) log(2πe σ²)`。第 2 項は分散積分 `variance_id_gaussianReal` (= `σ²`) で計算。
3. **Max-entropy (Phase D)**: 任意 `μ ≪ volume`, 平均 `m`, 分散 ≤ `σ²` で
   ```
   0 ≤ klDiv μ (gaussianReal m ⟨σ², _⟩) = -h(μ) + (1/2) log(2πσ²) + ∫(x-m)²/(2σ²) dμ
                                       ≤ -h(μ) + (1/2) log(2πe σ²)
   ```
   ENNReal `klDiv ≥ 0` を `klDiv_nonneg` で受け、`klDiv_eq_zero_iff` (Mathlib) で等号を取る。
   分散仮定 `∫ (x-m)² dμ ≤ σ²` を `1/(2σ²)` 倍で右辺の `1/2` を上から押さえる。

**規模見積**: ~1500 行 (Phase 内訳 A:300, B:200, C:400, D:400, E:200)。Mathlib `gaussianReal` /
`gaussianPDFReal` / `rnDeriv_gaussianReal` / `variance_id_gaussianReal` がすべて既存である事実が
判明したため見積は seed の "重量" 評価より楽観方向に振れる。Phase C の PDF 計算 (`Real.log`
の積分式変形) が最大の山。

## Phase 0 — Mathlib 整備度調査結果 ✅

調査日 2026-05-13、`loogle` index で確認。**E-9 plan 起草に十分な土台が Mathlib 既存**である
ことが判明。`differentialEntropy` 自体は不在で新規定義の余地あり (上流 PR 候補)。

### 既存 (Mathlib そのまま流用可能)

#### Gaussian 一族 (`Mathlib.Probability.Distributions.Gaussian.Real`)
- **`ProbabilityTheory.gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ`** (line 48):
  ```
  (√(2 * π * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * v))
  ```
  シンプル直接形 (ℝ-valued)。`gaussianPDF` (`ℝ≥0∞`-valued) も併存。
- **`ProbabilityTheory.gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ`** (line 200):
  ```
  if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)
  ```
- `instance instIsProbabilityMeasureGaussianReal` (line 209) — 確率測度。
- **`rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v`**
  (line 240) — Radon-Nikodym a.e. 同値。**Phase A 定義のために必須**。
- `gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume`
  (line 228)。
- `noAtoms_gaussianReal {μ} {v} (h : v ≠ 0) : NoAtoms (gaussianReal μ v)` (line 213)。
- **Transformations**:
  - `gaussianReal_map_add_const (y) : (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v`
    (line 278) — translation。Phase B `h(X + y) = h(X)` の鍵。
  - `gaussianReal_map_const_add (y)` (line 292) — 同。
  - `gaussianReal_map_mul_const (c)` (line 325) — scaling。Phase B `h(cX) = h(X) + log |c|` の鍵。
  - `gaussianReal_map_div_const`, `gaussianReal_const_mul`, etc. も整備。
- `integral_id_gaussianReal (μ) (v) : ∫ x, x ∂(gaussianReal μ v) = μ`。
- `variance_id_gaussianReal (μ) (v) : variance id (gaussianReal μ v) = v` (`ℝ≥0` 形)。
- `variance_fun_id_gaussianReal` (関数形)。
- `integral_gaussianReal_eq_integral_smul (hv) : ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x`
  (line 249) — Phase C で `h(𝒩) = -∫ f log f` を `∫ ... ∂(gaussianReal)` 形に直接書くか, `∫ ... ∂volume` で直接計算するかの切り替えに使う。
- `integrable_gaussianPDFReal (μ) (v) : Integrable (gaussianPDFReal μ v)` (line 82)。
- `lintegral_gaussianPDFReal_eq_one`, `integral_gaussianPDFReal_eq_one`。

#### IsGaussian typeclass (`Mathlib.Probability.Distributions.Gaussian.Basic`)
- `ProbabilityTheory.IsGaussian` — measure 上の Gaussian 判別。E-9 の主結果は `gaussianReal m v`
  特化形で書き、`IsGaussian` 経由の一般化は scope-deferred。

#### KL divergence (`Mathlib.InformationTheory.KullbackLeibler.Basic`)
- `InformationTheory.klDiv (μ ν : Measure α) : ℝ≥0∞` — 一般 measure 上 (discrete / continuous
  共通)。本 plan の Phase D / E で `μ vs gaussianReal m v` で使う。
- **`klDiv_eq_lintegral_klFun_of_ac`**: `μ ≪ ν` のもとで `klDiv μ ν` が rnDeriv 経由の lintegral
  に展開される。**Phase D 鍵**: `μ ≪ gaussianReal` ⟹ `klDiv μ (gaussianReal m v) = ∫⁻ x, klFun ((μ.rnDeriv (gaussianReal m v) x).toReal) ∂(gaussianReal m v)`。
- `toReal_klDiv_eq_integral_klFun`, `toReal_klDiv_of_measure_eq` — `.toReal` 形 (Bochner)。
- `klDiv_eq_zero_iff : klDiv μ ν = 0 ↔ μ = ν` (両者 `IsFiniteMeasure`)。**Phase D 等号鍵**。
- `klDiv_ne_top_iff`, `klDiv_ne_top`, `klDiv_zero_left/right`, `klDiv_self`。
- `mul_log_le_klDiv` (Gibbs ineq の Mathlib 形)。

#### Radon-Nikodym (`Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue`)
- `Measure.rnDeriv (μ ν : Measure α) : α → ℝ≥0∞` — 166 declarations 整備。
- `Measure.rnDeriv_self`, `rnDeriv_ne_top`, `rnDeriv_lt_top`, `rnDeriv_withDensity`,
  `eq_rnDeriv`, `eq_withDensity_rnDeriv`, `absolutelyContinuous_withDensity_rnDeriv`。
- 一般 σ-finite 設定 (Lebesgue `volume` は σ-finite なので Phase A 適用 OK)。

#### Lebesgue volume / withDensity
- `MeasureTheory.volume` (Lebesgue) — `ℝ` 上で既存。
- `MeasureTheory.withDensity_apply`, `withDensity_apply'`, `lintegral_withDensity_eq_lintegral_mul`,
  `integral_withDensity_eq_integral_toReal_smul` — `withDensity` 上の積分計算が揃う (19 件)。

#### 関数 `negMulLog`
- `Real.negMulLog (x : ℝ) : ℝ` — `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`。
- `negMulLog_def`, `negMulLog_zero = 0`, `negMulLog_one = 0`。
- `continuous_negMulLog`, `concaveOn_negMulLog`, `strictConcaveOn_negMulLog`,
  `negMulLog_nonneg` (on `[0,1]`), `negMulLog_le_one_sub_self`, `negMulLog_mul`,
  `hasDerivAt_negMulLog`, `deriv_negMulLog`, `deriv2_negMulLog`。
- **整備度極めて高い**。Phase A / C で直接呼ぶ。

### 不在 (新規 / 自前で構築)
- `differentialEntropy` (本 plan の主目的)。
- `differentialEntropy_translation_invariance` (Phase B)。
- `differentialEntropy_scaling` (Phase B)。
- `differentialEntropy_gaussianReal` (Phase C)。
- `gaussian_max_entropy_under_variance` (Phase D 主定理)。
- `gaussian_max_entropy_eq_iff` (Phase D 等号条件)。

これらは Mathlib に PR 候補。Phase D まで完結したら `Mathlib.InformationTheory.DifferentialEntropy.*`
として上流送付の検討対象。

### 既存 Common2026 資産
- `Common2026/Shannon/Entropy.lean` — discrete entropy。**`Real.negMulLog`-shape を採用済み**。
  Phase A の continuous 版を同 shape で書くと自然に並立。
- `Common2026/Shannon/Bridge.lean` — `entropy μ X := ∑ x, Real.negMulLog ((μ.map X).real {x})`。
  本 plan は **新規 file** `Common2026/Shannon/DifferentialEntropy.lean` に切り出し、Bridge.lean
  は touch せず。
- `Common2026/Shannon/MaxEntropy.lean` — discrete max-entropy (`entropy μ X ≤ log |α|`, B-6)。
  Phase D の continuous 版が直接対応 (`differentialEntropy μ ≤ (1/2) log (2πe σ²)`)。
- `Common2026/Shannon/CsiszarProjection.lean` — `klDivPmf` Pythagorean (E-6)。本 plan は
  `Measure ℝ` ambient なので **`klDivPmf` は使わず、`InformationTheory.klDiv` 直接**。

## Phase A — `differentialEntropy` 定義 + 基本可積分性 📋

新規 file: `Common2026/Shannon/DifferentialEntropy.lean`。

### Phase A-1 定義

```lean
/-- 微分エントロピー: `μ ≪ volume` なる `Measure ℝ` の Lebesgue 微分 `f := dμ/dvolume` に
対して `h(μ) := ∫ f(x) · negMulLog (f(x)) ∂volume = -∫ f log f`。
注: `f` は `ℝ≥0∞` 値だが `Real.negMulLog` 経由の Bochner 積分で書く。`negMulLog 0 = 0` で
support 外を自然に切る。 -/
noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
  ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
```

**設計判断 (judging-log A-1)**:
- **Bochner `∫` (Real 値)** を採用、`∫⁻` (ENNReal) ではない。理由: `Real.negMulLog` が **signed**
  (`negMulLog x ≤ 0` for `x ≥ 1`), `ENNReal` では受けられない。Mathlib `Bochner.integral` の
  signed 値が必要。
- **`∂volume` (not `∂μ`)**: `f log f` の積分は **Lebesgue 上**で取る (`f := rnDeriv` で重み済み)。
  これは Cover-Thomas 8.1 (`-∫ f(x) log f(x) dx` の `dx` = Lebesgue) と shape 一致。
- **`Real.negMulLog (...)` 採用、`f log f` 直書きしない**: `negMulLog` の Mathlib 既存補題
  (`continuous_negMulLog` / `concaveOn_negMulLog` / `negMulLog_zero` etc.) を直接呼べる。
  `discrete` の `Bridge.entropy` と shape 一致。

### Phase A-2 基本同値形

- [ ] `differentialEntropy_eq_integral_withDensity`: `μ = volume.withDensity f` (with `f` measurable
  `ℝ≥0∞`-valued) なら `differentialEntropy μ = ∫ x, Real.negMulLog (f x).toReal ∂volume` (rnDeriv の
  `=ₐₛ` 経由)。
- [ ] `differentialEntropy_eq_integral_density`: `μ ≪ volume` + measurable density `f` (Real 値)
  形 `differentialEntropy μ = ∫ x, f x * Real.log (f x) ∂volume` (上の `-1` 倍, `negMulLog_def` 展開)。
- [ ] `integrable_density_log_density_of_gaussian`: `gaussianReal m v` (`v ≠ 0`) で
  `Integrable (fun x => gaussianPDFReal m v x * Real.log (gaussianPDFReal m v x)) volume`。
  経路: Mathlib `integrable_gaussianPDFReal` + `log f(x) = -(1/2) log(2πv) - (x-m)²/(2v)` 展開で
  `log f` が **二次多項式** ⟹ `f · log f` が二次多項式と Gaussian PDF の積で Integrable
  (`integrable_gaussianPDFReal` の polynomial-weighted 版 / `variance_id_gaussianReal` の
  存在から `(x-m)²` Integrable on `volume.withDensity gaussianPDF`)。

### Phase A-3 `differentialEntropy μ`, `μ` not abs cont の縮退

- [ ] `differentialEntropy_of_not_absolutelyContinuous`: `¬ μ ≪ volume` のとき `rnDeriv μ volume`
  は singular part を含むが `=ₐₛ 0` on the singular part の補集合外。素朴に値が信頼できないため
  本 plan では **暗黙仮定 `μ ≪ volume`** を主定理 signature に常時含める。
  - 縮退ケース (例: `Measure.dirac` 系) は Mathlib `rnDeriv_dirac` / `MutuallySingular` で
    `differentialEntropy μ = 0` などの計算を Phase A-3 補助補題として用意。

## Phase B — Translation invariance / scaling 📋

### Phase B-1 translation invariance

```lean
theorem differentialEntropy_map_add_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) (y : ℝ) :
    differentialEntropy (μ.map (· + y)) = differentialEntropy μ
```

**戦略**:
1. `(μ.map (· + y)).rnDeriv volume x = μ.rnDeriv volume (x - y)` (translation 不変性、Mathlib
   `Measure.rnDeriv_map` 系 or 直接 `withDensity` 展開)。
2. `∫ x, negMulLog (μ.rnDeriv volume (x - y)).toReal ∂volume = ∫ x, negMulLog (μ.rnDeriv volume x).toReal ∂volume`
   (Lebesgue translation invariance, `integral_sub_right_eq_self`)。

**鍵 Mathlib API**:
- `MeasureTheory.integral_sub_right_eq_self : ∫ x, f (x - y) ∂volume = ∫ x, f x ∂volume`
  (Lebesgue translation invariance).
- `Measure.rnDeriv_map` / `Measure.map_rnDeriv_eq` (rnDeriv の map 公式) — 整備度未確認、
  Phase B 着手時に loogle 再確認。

**仮説**: `μ ≪ volume`。`gaussianReal_map_add_const` 既存 ⟹ Gaussian 上では translation
で形が保存される事実は別途使える。

### Phase B-2 scaling

```lean
theorem differentialEntropy_map_mul_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) {c : ℝ} (hc : c ≠ 0) :
    differentialEntropy (μ.map (· * c)) = differentialEntropy μ + Real.log |c|
```

**戦略**:
1. `(μ.map (· * c)).rnDeriv volume x = (1/|c|) * μ.rnDeriv volume (x / c)` (change of variable for
   density)。
2. `f' := (1/|c|) * f(x/c)` ⟹ `negMulLog (f'(x)) = negMulLog ((1/|c|) f(x/c))`
   `= (1/|c|) f(x/c) * [log |c| - log f(x/c)]`
   `= (1/|c|) f(x/c) * log |c| - (1/|c|) f(x/c) * log f(x/c)`。
3. 積分 (Lebesgue で `dx = |c| · d(x/c)` 換算) ⟹ 第 1 項 = `log |c| · ∫ f` = `log |c|` (確率測度),
   第 2 項 = `-∫ f log f` = `differentialEntropy μ`。

**鍵 Mathlib API**:
- `MeasureTheory.integral_smul_eq_integral_div_const` / `Real.integral_comp_mul_left` 系。
- `Measure.map_mul_left_eq` (push-forward of `Measure.map (· * c)` の Lebesgue 上計算)。
- `MeasurableEquiv` での pushforward は Mathlib 整備。

### Phase B-3 affine 系の corollary

- [ ] `differentialEntropy_map_affine`: `h(aX + b) = h(X) + log |a|` (B-1 + B-2 直結)。

## Phase C — `differentialEntropy (gaussianReal m v) = (1/2) log (2πe v)` 📋

### Phase C-1 `gaussianReal` の rnDeriv 形

- [ ] `differentialEntropy_gaussianReal_form`: `(0 < v)` のもとで
  ```
  differentialEntropy (gaussianReal m ⟨v, hv⟩)
    = ∫ x, gaussianPDFReal m v x * (- Real.log (gaussianPDFReal m v x)) ∂volume
  ```
  - `rnDeriv_gaussianReal` で rnDeriv が `gaussianPDF m v` に `=ₐₛ`。
  - `gaussianPDF.toReal = gaussianPDFReal` (Mathlib `toReal_gaussianPDF`)。
  - `Real.negMulLog_def` で `negMulLog f = -f * log f`。

### Phase C-2 `Real.log (gaussianPDFReal m v x)` 展開

- [ ] `log_gaussianPDFReal_eq` (`v ≠ 0`):
  ```
  Real.log (gaussianPDFReal m v x) = -(1/2) * Real.log (2 * π * v) - (x - m)^2 / (2 * v)
  ```
  - `Real.log (a * b) = Real.log a + Real.log b` (`Real.log_mul` for nonneg).
  - `Real.log ((√(2πv))⁻¹) = -(1/2) Real.log (2πv)` (`Real.log_inv` + `Real.log_sqrt`)。
  - `Real.log (exp (...)) = ...` (`Real.log_exp`)。

### Phase C-3 主計算

```lean
theorem differentialEntropy_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
```

**戦略**: C-1 + C-2 直結で
```
h(𝒩) = ∫ f(x) * [(1/2) log(2πv) + (x-m)²/(2v)] dx
     = (1/2) log(2πv) · ∫ f dx  +  (1/(2v)) · ∫ (x-m)² f(x) dx
     = (1/2) log(2πv) · 1       +  (1/(2v)) · v
     = (1/2) log(2πv) + 1/2
     = (1/2) log(2πv) + (1/2) log e
     = (1/2) log(2πev).
```

**鍵 Mathlib API**:
- `integral_gaussianPDFReal_eq_one` — 第 1 項の `∫ f = 1`。
- `variance_id_gaussianReal` — 第 2 項の `∫ (x-m)² f = v` (variance の定義経由)。
  - 注: `variance` は `id` (i.e., `X = id`) で書かれる、Phase C 着手時に signature 再確認。
- `integral_add`, `integral_const_mul`, `Real.exp_one` 系。

### Phase C-4 corollary `h(𝒩(0, 1)) = (1/2) log(2πe)`

- [ ] `differentialEntropy_gaussianReal_std`: 簡単な代入。Phase D check 用。

## Phase D — Gaussian Max-entropy 定理 📋

### Phase D-1 主定理 (上界)

```lean
theorem differentialEntropy_le_gaussian_of_variance_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m)
    (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) :
    differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
```

**戦略 (KL ≥ 0 経路)**:
1. `0 ≤ (klDiv μ (gaussianReal m v)).toReal` (`klDiv` ENNReal nonneg + finite から)。
2. `μ ≪ gaussianReal m v` (∵ `μ ≪ volume` + `gaussianReal_absolutelyContinuous'`)。
3. **代数恒等式 (鍵)** `klDiv_eq_differentialEntropy_diff_plus_var`:
   ```
   (klDiv μ (gaussianReal m v)).toReal
     = -differentialEntropy μ + (1/2) log (2πv) + (1/(2v)) · ∫ (x-m)² dμ
   ```
   - 展開: `klDiv μ ν = ∫ x, log (dμ/dν) dμ`。`dμ/dν = (dμ/dvol) / (dν/dvol)` で
     `dν/dvol = gaussianPDFReal m v x` (Phase C-1 同様)。
   - `log (dμ/dν) = log (dμ/dvol) - log (gaussianPDFReal m v) = log f - log g` for `f := rnDeriv μ vol`,
     `g := gaussianPDFReal m v`。
   - `∫ (log f - log g) dμ = -h(μ) - ∫ log g dμ`。
   - `∫ log g dμ = -(1/2) log(2πv) - (1/(2v)) ∫ (x-m)² dμ` (Phase C-2)。
4. **不等式合成**:
   ```
   0 ≤ -h(μ) + (1/2) log(2πv) + (1/(2v)) · ∫ (x-m)² dμ
     ≤ -h(μ) + (1/2) log(2πv) + (1/(2v)) · v     ← h_var
     = -h(μ) + (1/2) log(2πv) + 1/2
     = -h(μ) + (1/2) log(2πev).
   ```

**鍵 Mathlib API**:
- `InformationTheory.klDiv_eq_lintegral_klFun_of_ac` (`μ ≪ ν` ⟹ klDiv の `∫⁻ klFun` 形)。
- `InformationTheory.toReal_klDiv_eq_integral_klFun` (Bochner 形)。
- `InformationTheory.klDiv_eq_zero_iff` (等号条件 Phase D-2 で使う)。
- `gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : volume ≪ gaussianReal μ v` —
  `μ ≪ volume` + `volume ≪ gaussianReal` ⟹ `μ ≪ gaussianReal` (`AbsolutelyContinuous.trans`)。
- `Measure.rnDeriv_mul_rnDeriv` (chain rule for rnDeriv) — `dμ/dgaussianReal = (dμ/dvol) / gaussianPDF`。

### Phase D-2 等号条件

```lean
theorem differentialEntropy_eq_gaussian_iff
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ = (v : ℝ)) :
    differentialEntropy μ = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
      ↔ μ = gaussianReal m ⟨v, _⟩
```

**戦略**: D-1 の不等式が両側 equality になる条件 ⟺ `(klDiv μ (gaussianReal m v)).toReal = 0`
+ `h_var = v` (等号)。`klDiv_eq_zero_iff` で `μ = gaussianReal m v`。逆向きは Phase C-3 直結。

### Phase D-3 縮退ケース

- `v = 0` (Dirac): `differentialEntropy (Measure.dirac m) = ?` — 解析的に `-∞` (atom があると
  rnDeriv が定義しがたい)。本 plan では `v ≠ 0` 仮定で scope を制限し、Dirac 退化は
  scope-deferred の判断。

## Phase E — KL bridge / corollaries 📋

### Phase E-1 KL closed-form

- [ ] `klDiv_gaussianReal_gaussianReal_eq` (`v₁, v₂ ≠ 0`):
  ```
  (klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)).toReal
    = (1/2) [log(v₂/v₁) + v₁/v₂ + (m₁ - m₂)²/v₂ - 1]
  ```
  Cover-Thomas 8.6 / 一般 textbook 公式。Phase C-2 を 2 度展開して計算。

### Phase E-2 Sanity check / 数値検証

- [ ] `differentialEntropy_gaussianReal_std_val`: `h(𝒩(0,1)) = (1/2) log (2π) + 1/2` (Phase C-4
  別形)。`Real.log_exp` で `(1/2) log e = 1/2` を確認。

### Phase E (scope-deferred 候補)
- **Gaussian channel capacity (Cover-Thomas 9.1)**: AWGN チャネル `Y = X + Z`, `Z ~ 𝒩(0, N)`,
  入力分散制約 ≤ P で `C = (1/2) log(1 + P/N)`。E-9 plan の **直接の延長** だが別 seed/plan
  に切り出し (~1000 行追加見込み)。
- **EPI (Cover-Thomas 17)**: `e^{2h(X+Y)} ≥ e^{2h(X)} + e^{2h(Y)}` for indep X, Y。微分エントロピー
  + Fisher information の重い物。本 plan の **3 段ロケット最終段**、別 seed (~2000 行)。

## Mathlib API inventory (Phase 0 取得結果から)

### Gaussian (`Mathlib.Probability.Distributions.Gaussian.Real`)

| 名前 | line | シグネチャ (verbatim) | 用途 |
|---|---|---|---|
| `gaussianPDFReal` | 48 | `(μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (√(2 * π * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * v))` | Phase A / C 計算の主役 |
| `gaussianReal` | 200 | `(μ : ℝ) (v : ℝ≥0) : Measure ℝ := if v = 0 then dirac μ else volume.withDensity (gaussianPDF μ v)` | 主測度 |
| `instIsProbabilityMeasureGaussianReal` | 209 | `IsProbabilityMeasure (gaussianReal μ v)` | 自動 instance |
| `rnDeriv_gaussianReal` | 240 | `(μ : ℝ) (v : ℝ≥0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v` | Phase A 定義から Phase C 計算への bridge |
| `gaussianReal_absolutelyContinuous` | 228 | `(μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume` | Phase D 仮説 |
| `gaussianReal_absolutelyContinuous'` | 233 | `(μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : volume ≪ gaussianReal μ v` | Phase D `μ ≪ gaussianReal` chain |
| `gaussianReal_apply_eq_integral` | 221 | `(μ) {v} (hv) (s) : gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x)` | Phase C 補助 |
| `integral_gaussianPDFReal_eq_one` | 121 | `(μ) {v} (hv : v ≠ 0) : ∫ x, gaussianPDFReal μ v x = 1` | Phase C 第 1 項 |
| `lintegral_gaussianPDFReal_eq_one` | 104 | `(μ) {v} (h : v ≠ 0) : ∫⁻ x, ENNReal.ofReal (gaussianPDFReal μ v x) = 1` | 上の ENNReal 形 |
| `integrable_gaussianPDFReal` | 82 | `(μ) (v) : Integrable (gaussianPDFReal μ v)` | Phase A-2 可積分性 |
| `gaussianPDFReal_pos` | 61 | `(μ) (v) (x) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x` | Phase B / D 0-避け |
| `gaussianPDFReal_nonneg` | 66 | `(μ) (v) (x) : 0 ≤ gaussianPDFReal μ v x` | 一般 nonneg |
| `gaussianReal_map_add_const` | 278 | `(y : ℝ) : (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v` | Phase B-1 (Gaussian の translation 性) |
| `gaussianReal_map_mul_const` | 325 | `(c : ℝ) : (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (⟨c^2, _⟩ * v)` (要確認) | Phase B-2 scaling sanity |
| `integral_id_gaussianReal` | ? | `(μ) (v) : ∫ x, x ∂(gaussianReal μ v) = μ` | Phase C mean 確認 |
| `variance_id_gaussianReal` | ? | `(μ) (v) : variance id (gaussianReal μ v) = v` | Phase C 第 2 項 |
| `integral_gaussianReal_eq_integral_smul` | 249 | `{f} (hv : v ≠ 0) : ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x` | Phase C 計算経路の選択肢 |

### KL divergence (`Mathlib.InformationTheory.KullbackLeibler.Basic`)

| 名前 | シグネチャ (verbatim 取得は Phase A 着手時に) | 用途 |
|---|---|---|
| `klDiv` | `(μ ν : Measure α) : ℝ≥0∞` | Phase D 主役 |
| `klDiv_eq_lintegral_klFun_of_ac` | `μ ≪ ν → klDiv μ ν = ∫⁻ x, klFun ((μ.rnDeriv ν x).toReal) ∂ν` | Phase D 代数恒等式の起点 |
| `toReal_klDiv_eq_integral_klFun` | Bochner 形 | Phase D `.toReal` 経路 |
| `klDiv_eq_zero_iff` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv μ ν = 0 ↔ μ = ν` | Phase D-2 等号 |
| `klDiv_ne_top_iff` | finiteness | Phase D `.toReal` 取得 |
| `klFun` | `Mathlib.InformationTheory.KullbackLeibler.KLFun` (既知) | rnDeriv-level kernel |

### Real / Lebesgue / Bochner

| 名前 | 用途 |
|---|---|
| `Real.negMulLog (x : ℝ) : ℝ := -x * Real.log x` | Phase A 定義 |
| `Real.negMulLog_def`, `negMulLog_zero`, `negMulLog_one` | Phase A 計算 |
| `continuous_negMulLog` | 連続性 |
| `Real.log_mul`, `Real.log_inv`, `Real.log_sqrt`, `Real.log_exp` | Phase C-2 展開 |
| `Real.exp_one` | Phase C-3 `e` |
| `MeasureTheory.integral_sub_right_eq_self` | Phase B-1 translation |
| `MeasureTheory.integral_map`, `Measure.integral_map_equiv` | Phase B-2 push-forward |
| `MeasureTheory.Measure.rnDeriv`, `rnDeriv_self`, `rnDeriv_withDensity` | Phase A / B |
| `MeasureTheory.lintegral_withDensity_eq_lintegral_mul` | withDensity 経由の積分 |
| `MeasureTheory.integral_withDensity_eq_integral_toReal_smul` | Bochner 形 (Phase C 経路) |

## 規模見積

| Phase | 内容 | 見積行数 |
|---|---|---|
| A | 定義 + 可積分性 + 縮退補題 | ~300 |
| B | translation / scaling / affine | ~200 |
| C | gaussianReal の h 計算 | ~400 |
| D | max-entropy 主定理 + 等号 | ~400 |
| E | KL closed-form + corollaries | ~200 |
| 合計 |  | **~1500 行** |

**前提**: `gaussianReal` / `gaussianPDFReal` / `rnDeriv_gaussianReal` / `klDiv_eq_lintegral_klFun_of_ac`
/ `variance_id_gaussianReal` がすべて Mathlib 既存 (確認済み) ⟹ 自前で構築する Mathlib 補題は **ゼロ**。
Phase C / D の解析計算 (`log` 展開, Lebesgue 上の integral 換算) が最大の山。

## 判断ログ

書き出し時 (2026-05-13、起草):

1. **`Real.negMulLog`-shape 採用** (定義 Phase A):
   Mathlib `Real.negMulLog` (`-x * Real.log x`) + `negMulLog_zero = 0` で support 外を自然に切れる。
   既存 `Common2026/Shannon/Bridge.lean` の discrete `entropy` も同 shape (`∑ x, Real.negMulLog (...)`)、
   並立性を維持して bridge 補題が短く済む見込み。
   **代替**: `differentialEntropy μ := -∫ x, f log f dx` を直書きする手もあるが, `f = 0` の場合の
   `0 * log 0 = 0` 規約を自前で書く必要があり、Mathlib `negMulLog_zero = 0` を直接使えない。却下。

2. **Bochner `∫` (Real) 採用、`∫⁻` (ENNReal) 不採用** (定義 Phase A):
   `negMulLog x ≤ 0` for `x ≥ 1` から signed 値。ENNReal で受けると `0 - ε` の取り扱いで折れる。
   `Integrable (fun x => negMulLog (f x))` 仮説 (Phase A-2 で `gaussianReal` 上は OK と確認) を
   付帯することで Bochner 経路を維持。

3. **`μ ≪ volume` 暗黙仮定で scope 制限** (Phase A-3):
   Singular 部分 (Dirac 等) は `rnDeriv = 0` a.e. で `differentialEntropy = 0` という縮退値に
   なるが、Cover-Thomas 文脈では abs cont 仮定が標準。`v = 0` の Gaussian (= Dirac) も自然に
   除外される。

4. **`InformationTheory.klDiv` 採用、`klDivPmf` (E-6) 不採用** (Phase D 設計):
   ambient が `Measure ℝ` 連続空間で `klDivPmf` (有限 alphabet, `α → ℝ`) は適用外。Mathlib
   `klDiv` の ENNReal 形 + `klDiv_eq_lintegral_klFun_of_ac` を rnDeriv 経由で展開する経路を主軸。
   E-6 の Pythagorean (`klDivPmf` ベース) は本 plan で **使わない**。

5. **`gaussianReal_map_mul_const` の正確な statement は Phase B 着手時に再確認** (Phase B-2):
   `(gaussianReal μ v).map (· * c) = gaussianReal (c * μ) ?v'` の `?v'` (scaling 後の variance)
   が `c^2 * v` の `ℝ≥0` 形にどう pack されているか実装時に loogle 再確認。signature ミスれば
   Phase B-2 計算の `1/|c|` 係数も狂う。

6. **Lagrangian / variational 経路 (路線 2) は不採用** (Phase D 経路選択):
   Cover-Thomas 12.1 の Lagrange multiplier 経路 (variance 制約 + entropy 最大化を直接 PDE 化)
   は EulerLagrange + 関数空間の議論で重い。`KL ≥ 0` 経路 (路線 1) は **代数恒等式 + ENNReal
   nonneg** だけで 400 行で済むため路線 1 で進む。Lagrangian 経路は EPI 時に再考。

7. **`gaussianReal_map_mul_const` の Phase B-2 検証で対称性 sanity が取れる**: Phase B-2 の
   `h(cX) = h(X) + log |c|` を `μ = gaussianReal 0 v` で適用すると左辺 = `(1/2) log(2πe c²v)`
   (Phase C 経由), 右辺 = `(1/2) log(2πe v) + log |c|`、両者一致 ⟹ Phase B + C の整合性チェック
   になる。Phase D 着手前の必須 regression test として Phase E に置く。

8. **上流 Mathlib PR 候補リスト枠** (現時点での候補):
   - `Mathlib.InformationTheory.DifferentialEntropy.Basic`: `differentialEntropy` 定義 + translation
     invariance + scaling (Phase A + B 一括)。
   - `Mathlib.InformationTheory.DifferentialEntropy.Gaussian`: `differentialEntropy_gaussianReal` 計算式
     + Gaussian max-entropy (Phase C + D)。
   - `Mathlib.InformationTheory.KullbackLeibler.Gaussian`: KL between two Gaussians closed-form
     (Phase E-1)。
   - 上記 3 件は **independent**。Phase A 完了時点で 1 件目を PR 化、Phase D 完了で 2 件目、
     Phase E で 3 件目、と段階的 publish が現実的。

9. **判断ログ更新枠 (Phase 0 完了後の見積見直し)**:
   現在の見積 ~1500 行は **Phase 0 (Mathlib 整備度未確認段階) の見積からの下方修正版**。
   `rnDeriv_gaussianReal` / `klDiv_eq_lintegral_klFun_of_ac` / `variance_id_gaussianReal` /
   `gaussianReal_map_*` がすべて既存と判明したため、自前 Mathlib 補題は 0、Phase C / D の
   解析計算に集中できる。Phase A 完了時点で再見積、Phase D 着地点で最終確定。
