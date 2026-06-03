# Stam Fisher 壁 `gaussianConv_fisher_le_inv_var` — pointwise Cauchy-Schwarz route 在庫調査

> 対象壁: `InformationTheory/Shannon/FisherConvBound.lean:73` `gaussianConv_fisher_le_inv_var`
> (`@residual(wall:fisher-finiteness)`、共有 Stam convolution Fisher 壁の唯一の sorry carrier)。
> 親 closure plan: [`docs/shannon/fisher-finiteness-closure-plan.md`](fisher-finiteness-closure-plan.md)
> 本ファイルは **inventory のみ**。実装・計画起草はしない。

## 一行サマリ

**pointwise (各 x 固定) Cauchy-Schwarz route で `gaussianConv_fisher_le_inv_var` は genuine 閉じられる見込み。conditional expectation / disintegration は不要 — closure plan の Step 1 「conditional expectation / score-of-convolution Cauchy-Schwarz」framing は過大評価。** 必要 Mathlib API の実体は ~85% 既存 (Hölder `integral_mul_le_Lp_mul_Lq_of_nonneg` / Gaussian 分散 `variance_fun_id_gaussianReal` / Tonelli `lintegral_lintegral_swap` / withDensity 橋 `integral_gaussianReal_eq_integral_smul` 全て存在)。自作必要は 3 件 (pointwise-CS 補題の volume-level 組立 / Gaussian 2次モーメント=`s` over volume の橋 / lintegrand plumbing)。**ただし壁 signature に `hpX_mass:(∫pX=1)` 追加が必要** (consumer chain で thread 可、判定 (d) 参照)。撤退ライン 1 件に触れるが発動せず (縮退不要)。

---

## 主定理の最終形 (再掲) + 証明戦略

```lean
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s)
```

verbatim 確認済:
- `fisherInfoOfDensity f := ∫⁻ x, ENNReal.ofReal ((logDeriv f x) ^ 2) * ENNReal.ofReal (f x) ∂volume`
  (`FisherInfoV2.lean:89-90`、verbatim)。
- `convDensityAdd pX pY := fun z => ∫ x, pX x * pY (z - x) ∂volume` (`EPIConvDensity.lean:40-41`、verbatim)。
- `gaussianPDFReal μ v x := (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))` (Mathlib `Gaussian/Real.lean:48-49`)。

pointwise-CS route (pseudo-Lean):

```
set p_s := convDensityAdd pX g_s,  g_s := gaussianPDFReal 0 ⟨s, hs.le⟩
-- Step 1: deriv1 形 (既存資産 convDensityAdd_deriv1_gaussian_eq)
--   deriv p_s ζ = ∫ y, pX y * (g_s(ζ-y) * (-((ζ-y)/s))) dy = -(1/s)∫ pX y (ζ-y) g_s(ζ-y) dy
-- Step 2: pointwise Cauchy-Schwarz (各 x 固定, 測度 dν_x(y)=pX y · g_s(x-y) dy)
--   (∫ pX y (x-y) g_s(x-y) dy)² ≤ (∫ pX y g_s(x-y) dy)(∫ pX y (x-y)² g_s(x-y) dy)
--                              = p_s(x) · ∫ pX y (x-y)² g_s(x-y) dy
--   ⇒ (deriv p_s x)² = (1/s²)(…)² ≤ (1/s²) p_s(x) ∫ pX y (x-y)² g_s(x-y) dy
--   ÷ p_s(x)>0 (convDensityAdd_pos):  (logDeriv p_s x)² · p_s x ≤ (1/s²)∫ pX y (x-y)² g_s(x-y) dy
-- Step 3: lintegrand へ持ち上げ
--   merge ofReal((logDeriv)²)·ofReal(p_s) → ofReal((logDeriv)²·p_s)  [← ENNReal.ofReal_mul (sq_nonneg _)]
--   lintegral_mono_ae + ENNReal.ofReal_le_ofReal
-- Step 4: Tonelli + Gaussian 2次モーメント
--   ∫⁻ x, ofReal((1/s²)∫ pX y (x-y)² g_s(x-y) dy) = ofReal(1/s)
--   swap → ∫ pX y [∫ (x-y)² g_s(x-y) dx] dy = ∫ pX y · s dy = s·(∫pX=1) = s  [要 hpX_mass]
--   (1/s²)·s = 1/s
```

---

## API 在庫テーブル

### A. 既存 repo 資産 (deriv1 形 + 正値性 + lintegrand plumbing)

| 概念 | repo API | file:line | 状態 | route での扱い |
|---|---|---|---|---|
| deriv1 形 (Step 1) | `EPIConvDensitySecondDeriv.convDensityAdd_deriv1_gaussian_eq` | `EPIConvDensitySecondDeriv.lean:58-112` | ✅ 既存 `@audit:ok` (sorryAx-free) | `deriv p_s = fun ζ => ∫ y, pX y * (g_s(ζ-y) * (-((ζ-y)/s))) ∂volume` を供給。Step 1 の核 |
| `convDensityAdd` 定義 | `EPIConvDensity.convDensityAdd` | `EPIConvDensity.lean:40-41` | ✅ 既存 | `fun z => ∫ x, pX x * pY (z - x) ∂volume` |
| 正値性 (Step 2 の `÷p_s(x)`) | `FisherInfoV2DeBruijnPerTime.convDensityAdd_pos` | `FisherInfoV2DeBruijnPerTime.lean:784-811` | ✅ 既存 (genuine) | `0 < convDensityAdd pX g_s x`。**前提 `hpX_mass : 0 < ∫ y, pX y ∂volume` を要求** (下記判定 (d)) |
| lintegrand merge | `← ENNReal.ofReal_mul (sq_nonneg _)` 前例 | `FisherInfoV2DeBruijnPerTime.lean:734`, `FisherInfoV2DeBruijnAssembly.lean:1584` | ✅ 前例あり | `ofReal((logDeriv)²)·ofReal(p_s) → ofReal((logDeriv)²·p_s)`。`fisher_from_logDeriv` body と同手 |
| Fisher→logDeriv 形 | `FisherInfoV2DeBruijnPerTime.fisher_from_logDeriv` | `FisherInfoV2DeBruijnPerTime.lean:721-736` | ✅ 既存 `@audit:ok` | 参考: 同じ `ofReal_mul` merge + `.toReal` round-trip パターン |

#### deriv1 補題の仮説 discharge 再利用サイト (判定 (c))

`convDensityAdd_deriv1_gaussian_eq` の 5 仮説 (`bound1`/`hbound1_int`/`hF1_meas`/`hF1_int`/`hF1'_meas`/`hb1`) は
**`convDensityAdd_deriv_hasDerivAt_self` (`FisherInfoV2DeBruijnAssembly.lean:1747-1872`、`@audit:ok`) の body 内
`FisherInfoV2DeBruijnAssembly.lean:1758-1797`** で `hpX_meas` + `hpX_int` + `ht` のみから完全に構築済:

| deriv1 仮説 | discharge 行 | 構築方法 (verbatim) |
|---|---|---|
| `bound1 := fun y => \|pX y\| * M1`, `M1` global sup | `:1758` (`set M1`) | `(√(2π t))⁻¹ * ((1+2t·exp(-1))/(2t))` (kernel_x_deriv1_global_bound) |
| `hbound1_int` (= `hb1_int`) | `:1797` | `hpX_int.abs.mul_const _` |
| `hF1_meas` | `:1761-1766` | `hpX_meas.aestronglyMeasurable.mul (hker_meas.comp …)` |
| `hF1_int` | `:1773-1780` | `hpX_int.mul_bdd … hker_le` |
| `hF1'_meas` | `:1781-1788` | `hpX_meas.aestronglyMeasurable.mul (… .neg)` |
| `hb1` | `:1789-1796` | `kernel_x_deriv1_global_bound ht (ξ-y)` + `mul_le_mul_of_nonneg_left` |

→ **判定 (c) ✅**: deriv1 補題の仮説 discharge は `hpX_meas`/`hpX_int`/`hs` のみから既存サイトと逐語同形で再構築可能。
壁 signature の `hpX_meas`/`hpX_int`/`hs` で揃う。`heatFlow_density_heat_equation_kernel` ↔ `gaussianPDFReal`
変換 (`heatFlow_density_heat_equation_kernel_eq`) も既存。**新 discharge 不要、コピー再利用で済む。**

### B. Mathlib — pointwise Cauchy-Schwarz / Hölder (Step 2 の核、判定 (a))

| 概念 | Mathlib API | file:line | 状態 | route での扱い |
|---|---|---|---|---|
| **Hölder 積分 (nonneg ℝ)** | `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1237-1254` | ✅ 既存 (loogle 確認: Found one) | **Step 2 第一候補** (p=q=2)。下記前提ボックス参照 |
| Hölder 積分 (norm 版) | `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1190-1232` | ✅ 既存 | `of_nonneg` 版の下請け。バックアップ |
| Hölder lintegral (ℝ≥0∞) | `ENNReal.lintegral_mul_le_Lp_mul_Lq` | `Mathlib/MeasureTheory/Integral/MeanInequalities.lean` | ✅ 既存 | lintegral-level で組むなら候補 |
| Hölder 共役 `(2,2)` | `Real.HolderConjugate` (`abbrev … := HolderTriple p q 1`) | `Mathlib/Analysis/MeanInequalities.lean` | ✅ 既存 | `(2:ℝ).HolderConjugate 2` を `Real.holderConjugate_iff` 等で供給 |

**`integral_mul_le_Lp_mul_Lq_of_nonneg` 完全 signature (verbatim, bracket drop なし):**

```lean
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)
```

- 暗黙型クラス: `{α} [MeasurableSpace α] {μ : Measure α}` (section variable、`[IsFiniteMeasure]` **不要** — `MemLp` 経由で finiteness を吸収)。
- 引数順: `hpq`(共役) → `hf_nonneg`/`hg_nonneg`(a.e.非負) → `hf`/`hg`(`MemLp ... (ENNReal.ofReal p)`)。
- 結論 verbatim: `∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)`。

> **L² 内積 CS (`inner_mul_le_norm_mul_norm`) は loogle で `Unknown identifier` — 在庫しない名前。** measure 版 L² inner CS を直接呼ぶより、上記 Hölder (p=q=2) を `volume` 上で
> `f := (x-·)·√(pX·g_s(x-·))`, `g := √(pX·g_s(x-·))` に適用する route が確実。
> `f·g = (x-y)·(pX y·g_s(x-y))`, `f² = (x-y)²·pX y·g_s(x-y)`, `g² = pX y·g_s(x-y)`、
> `(∫f²)^½·(∫g²)^½` を 2乗して `(∫(x-y)pX g_s)² ≤ (∫(x-y)²pX g_s)(∫pX g_s = p_s(x))`。
> `√` の符号処理 (pX·g_s ≥ 0) が plumbing コストだが elementary。

### C. Mathlib — Gaussian 2次モーメント = `s` (Step 4、判定 (b))

| 概念 | Mathlib API | file:line | 状態 | 値 (verbatim 確認) |
|---|---|---|---|---|
| **Gaussian 分散 = パラメータ** | `ProbabilityTheory.variance_fun_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:517-538` | ✅ 既存 | `Var[fun x ↦ x; gaussianReal μ v] = v` |
| Gaussian 平均 = パラメータ | `ProbabilityTheory.integral_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:508-513` | ✅ 既存 `@[simp]` | `∫ x, x ∂gaussianReal μ v = μ` |
| withDensity 積分橋 | `ProbabilityTheory.integral_gaussianReal_eq_integral_smul` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:249-254` | ✅ 既存 | `∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x` (要 `hv : v ≠ 0`) |
| `gaussianReal = withDensity` | `gaussianReal_of_var_ne_zero` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:201-204` | ✅ 既存 | `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` (v≠0) |

**値 verbatim 確認 (CLAUDE.md「具体的数値・型予測の verbatim 確認」遵守):**

- `variance_fun_id_gaussianReal` の body (`:521-527`) は
  `∫ ω, (ω-μ)² ∂gaussianReal μ v = … = v` を計算しており、中心 case `μ=0` では
  `∫ ω, ω² ∂gaussianReal 0 v = v`。
- `integral_gaussianReal_eq_integral_smul` (`μ=0`, `f := (·)^2`) で
  **`∫ x, x² · gaussianPDFReal 0 v x ∂volume = ∫ x, x² ∂gaussianReal 0 v = v`** が橋渡し可能
  (`smul` は `ℝ` 上 `gaussianPDFReal • f = gaussianPDFReal x * f x`)。
- Tonelli 内側で `u := x - y` 平行移動 (`integral_sub_right_eq_self` / `volume` 平行移動不変) すると
  `∫ x, (x-y)² g_s(x-y) ∂volume = ∫ u, u² g_s(u) ∂volume = s`。
- **値 = `s` (= 分散パラメータ、s² ではない)** を確定。`g_s = gaussianPDFReal 0 ⟨s, hs.le⟩` の `v = ⟨s, hs.le⟩`、
  `(⟨s,hs.le⟩ : ℝ≥0).toReal = s`。`(1/s²)·s = 1/s` が壁 RHS `ofReal(1/s)` と一致。

→ **判定 (b) ✅**: Gaussian 2次モーメント = `s` over volume は既存 `variance_fun_id_gaussianReal` +
`integral_gaussianReal_eq_integral_smul` の橋で derive 可能。専用 `∫ x², gaussianPDFReal 0 v x = v` 補題は
Mathlib/repo どちらにも**直接の名前では不在** (`rg` 確認) なので、橋を 1 本自作 (10-25 行) する。

### D. Mathlib — Tonelli swap / lintegral plumbing (Step 3-4)

| 概念 | Mathlib API | file:line | 状態 | 結論 (verbatim) |
|---|---|---|---|---|
| Tonelli swap (lintegral) | `MeasureTheory.lintegral_lintegral_swap` | `Mathlib/MeasureTheory/Measure/Prod.lean:1058` | ✅ 既存 | `∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν` |
| Bochner swap | `MeasureTheory.integral_integral_swap` | `Mathlib/MeasureTheory/Integral/Prod.lean:532` | ✅ 既存 | `∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν` |
| lintegrand mono | `MeasureTheory.lintegral_mono_ae` | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:217` | ✅ 既存 | `(∀ᵐ a ∂μ, f a ≤ g a) → ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ` |
| ofReal 単調 | `ENNReal.ofReal_le_ofReal` | `Mathlib/Data/ENNReal/Real.lean:137` | ✅ 既存 | `(h : p ≤ q) → ENNReal.ofReal p ≤ ENNReal.ofReal q` |
| ofReal 乗法 | `ENNReal.ofReal_mul` | `Mathlib/Data/ENNReal/Real.lean:297` | ✅ 既存 | `(hp : 0 ≤ p) → ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q` |

**`lintegral_lintegral_swap` 完全 signature (verbatim):**

```lean
theorem lintegral_lintegral_swap [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν
```

- 型クラス: `[SFinite μ]` (`volume : Measure ℝ` は `SFinite`、自動)。`ν` は `[SFinite ν]` 暗黙 (section)。
- 引数: `hf : AEMeasurable (uncurry f) (μ.prod ν)` (joint 可測性、plumbing で discharge)。

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`integral_mul_le_Lp_mul_Lq_of_nonneg` (Hölder, Step 2)**:
  - `hpq : p.HolderConjugate q` — `(2:ℝ).HolderConjugate 2` を供給 (`1/2+1/2=1`)。
  - `hf_nonneg : 0 ≤ᵐ[μ] f`, `hg_nonneg : 0 ≤ᵐ[μ] g` — `f,g := (x-·)·√(pX·g_s), √(pX·g_s)` の非負性。`g` は √ なので非負自明、`f` は `(x-y)` の符号により**非負でない** → `f := |x-·|·√(…)` に取るか、norm 版 `integral_mul_norm_le_Lp_mul_Lq` を使う (絶対値で 2乗時に消える)。
  - `hf : MemLp f (ENNReal.ofReal 2) μ`, `hg : MemLp g (ENNReal.ofReal 2) μ` — **L² membership**。`∫ f² = ∫(x-y)²pX g_s < ∞`, `∫ g² = ∫ pX g_s = p_s(x) < ∞` を `MemLp` 形で供給する plumbing が必要 (Gaussian-tail × pX 可積分から)。**最大の plumbing 箇所**。
  - `[IsFiniteMeasure μ]` は**不要** (`MemLp` が finiteness を内包)。`μ = volume` で OK。
- **`convDensityAdd_pos` (Step 2 の `÷p_s(x)`)**:
  - `hpX_mass : 0 < ∫ y, pX y ∂volume` を**要求** (`FisherInfoV2DeBruijnPerTime.lean:786`)。壁 signature には不在 → 判定 (d)。
- **`integral_gaussianReal_eq_integral_smul` / `variance_fun_id_gaussianReal` (Step 4)**:
  - `hv : v ≠ 0` を要求。`v = ⟨s, hs.le⟩`、`hs : 0 < s` から `v ≠ 0` を `convDensityAdd_pos` body (`:789-790`) と同手で discharge。
- **`lintegral_lintegral_swap` (Step 4 Tonelli)**:
  - `[SFinite volume]` (自動)、`hf : AEMeasurable (uncurry …) (volume.prod volume)` (joint 可測性 plumbing)。被積分 `(x,y) ↦ ofReal((x-y)² pX y g_s(x-y))` は非負なので Tonelli (swap) が無条件で効く。

---

## 判定 (d) — 壁 signature への `hpX_mass` 追加要否 + consumer thread 可否

**要追加。** route は 2 箇所で `∫ pX = 1` / `0 < ∫ pX` を要する:

1. **Step 2 の `÷ p_s(x)`**: `convDensityAdd_pos` は `hpX_mass : 0 < ∫ y, pX y ∂volume` を要求 (`FisherInfoV2DeBruijnPerTime.lean:786`)。
2. **Step 4 の最終段**: `∫ pX y · s dy = s · (∫ pX = 1) = s`。`hpX_int` だけでは `∫ pX` の値は不明 (確率密度とは限らない)。

現壁 signature は `hpX_nn`/`hpX_meas`/`hpX_int`/`hs` のみ (`hpX_mass` 不在)。

**consumer thread 可否 ✅:**

| 呼出元 | file:line | `hpX_mass` scope | 備考 |
|---|---|---|---|
| 直接 consumer `convDensityAdd_fisher_integrable` | `FisherInfoV2DeBruijnAssembly.lean:1560-1574` | **現在なし** | 呼出は `gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int ht` (`:1573-1574`)。`hpX_mass` を追加 thread 要 |
| 間接 consumer `…_chain_ibp_fisher` | `FisherInfoV2DeBruijnAssembly.lean:2880-2912` | **あり** `hpX_mass : (∫ y, pX y ∂volume) = 1` (`:2882`) | この上流から供給可能 |
| 上流 assembled 定理 (`hpX_mass:∫pX=1` 保持) | `FisherInfoV2DeBruijnAssembly.lean:164` 等 | **あり** | entropy wave で確認済の通り上流は `hpX_mass` 保持 |

→ **`hpX_mass : (∫ y, pX y ∂volume) = 1` を壁 signature に追加し、`convDensityAdd_fisher_integrable` の signature にも 1 仮説追加して
`…_chain_ibp_fisher` (`:2882` が保持) から thread する** という 2-hop の mechanical な signature 拡張で閉じる。
`hpX_mass` は **regularity precondition (確率密度の正規化)** であり load-bearing ではない (honesty OK)。
`0 < ∫pX` 形が要るのは `convDensityAdd_pos` 側のみで、`∫pX=1 → 0 < ∫pX` は `by rw [hpX_mass]; norm_num` (前例 `:2908` 近傍に同パターン)。

---

## 自作が必要な要素 (優先度順)

1. **pointwise Cauchy-Schwarz 補題 (volume-level 組立)** — 優先度 高
   - 推奨: `∀ x, (∫ y, pX y * (x-y) * g_s(x-y) ∂volume)² ≤ (∫ y, pX y * g_s(x-y) ∂volume) * (∫ y, pX y * (x-y)² * g_s(x-y) ∂volume)`。
   - 実装: `integral_mul_norm_le_Lp_mul_Lq` (p=q=2) を `f := (x-·)·√(pX·g_s(x-·))`, `g := √(pX·g_s(x-·))` に適用 → 2乗。
   - 工数感: 中 (40-70 行)。落とし穴: `MemLp ... 2` の供給 (L² membership)、√ の非負・可測 plumbing、`f²·g²` を元の積分に戻す `√·√ = id` 書換。
2. **Gaussian 2次モーメント over volume の橋** — 優先度 高
   - 推奨: `∫ u, u² * gaussianPDFReal 0 ⟨s,hs.le⟩ u ∂volume = s`。
   - 実装: `integral_gaussianReal_eq_integral_smul (μ:=0) (f:=(·)²)` ← `variance_fun_id_gaussianReal` (中心 case `∫ω²∂gaussianReal 0 v = v`)。
   - 工数感: 小〜中 (10-25 行)。落とし穴: `smul` ↔ `*` 書換、`(⟨s,hs.le⟩:ℝ≥0).toReal = s`、`v ≠ 0` discharge。
3. **lintegrand plumbing (Step 3 持ち上げ + Step 4 Tonelli 組立)** — 優先度 中
   - 推奨: pointwise bound を `lintegral_mono_ae` + `ENNReal.ofReal_le_ofReal` で lintegrand 同士へ、`← ENNReal.ofReal_mul (sq_nonneg _)` で merge、`lintegral_lintegral_swap` で `∫⁻∫⁻` swap、内側を `ofReal(…)` の Bochner 化。
   - 工数感: 中 (50-80 行)。落とし穴: `ℝ≥0∞` ↔ `ℝ` の `ofReal/.toReal` round-trip、Tonelli の `AEMeasurable (uncurry …)` discharge、内側 `∫⁻ → ∫` 化 (`lintegral_ofReal …`)。

**合計工数感**: 既存資産 (deriv1 形 / 正値性 / lintegrand 前例 / Gaussian variance / Hölder) が揃っているため
**100-175 行程度の self-written + 既存補題 chain** で genuine closure 見込み。conditional expectation / disintegration
インフラ (StandardBorel / condKernel) は **一切不要** — 各 x 固定の elementary Hölder で sharp に出る。

---

## Mathlib 壁の列挙 (真に Mathlib 不在 = `@residual(wall:…)` 対象)

loogle 確認:
- `fisherInfo` → `unknown identifier 'fisherInfo'` (= **Found 0**、Mathlib に Fisher 情報そのものが不在)。
- `Blachman` → `unknown identifier 'Blachman'` (= **Found 0**、convolution Fisher bound 皆無)。

**結論: pointwise-CS route 内に真の Mathlib 壁は残らない。**

route の各 Step は全て既存 Mathlib API (Hölder / Gaussian variance / Tonelli / withDensity 橋) + 既存 repo
資産 (deriv1 形 / convDensityAdd_pos) + elementary self-written plumbing に分解される。`fisherInfo` / `Blachman`
そのものが不在というのは**「Fisher 情報を扱う高レベル定理が無い」という意味であって、Stam bound の証明に必要な
低レベル道具 (CS / Gaussian moment / Tonelli) は全部ある**。closure plan が壁と framing していた
「score-of-convolution Cauchy-Schwarz」は、conditional expectation を経由しない pointwise Hölder で代替できるため
**genuine な Mathlib gap ではなく self-contained に閉じられる plumbing** に降格する。

→ **shared sorry 補題集約は不要** (closure 後は `wall:fisher-finiteness` の sorry が消えるため、共有壁ごと解消)。
closure 完了まで `gaussianConv_fisher_le_inv_var` が `wall:fisher-finiteness` の唯一 carrier であり続ける現状維持で良い。

---

## 撤退ラインへの距離

closure plan ([`fisher-finiteness-closure-plan.md`](fisher-finiteness-closure-plan.md)) の関連撤退ライン
(Step 1 を「conditional expectation / score-of-convolution Cauchy-Schwarz」と framing し、
これが書けなければ縮退):

**触れるが発動しない。** 本 inventory は plan の Step 1 framing (conditional expectation) を **過大評価と判定**し、
代替 route (pointwise Hölder) が全 API 既存で genuine 閉じられることを示す。conditional expectation route が
書けなくても、より elementary な pointwise-CS で同じ sharp bound `≤ 1/s` に到達するため、縮退は不要。

ただし以下を**新規撤退ライン候補**として記録 (発動時は sorry + `@residual`、仮説束化禁止):

- **pointwise-CS の L² membership plumbing (`MemLp f 2 volume` 供給) が想定外に重い**場合
  (heavy-tail pX で `∫ (x-y)² pX g_s < ∞` の x-uniform 評価が詰まる)
  → 当該 `MemLp` 補題のみを `sorry + @residual(plan:fisher-stam-memLp)` で localized 撤退し、
  CS の骨格 + Gaussian moment + Tonelli は genuine に組む (壁を `MemLp` 1 点に縮退)。
  **load-bearing hypothesis bundling は禁止** — `MemLp` 不成立を仮説に抱えさせず sorry で正直に残す。

---

## 着手 skeleton

`InformationTheory/Shannon/FisherConvBound.lean` 内 (壁 declaration の body を pointwise-CS route に置換)。
import は既存 (`EPIConvDensity` / `FisherInfoV2` / `FisherInfoV2DeBruijn` / `StamGaussianBound`) に加え
Hölder / Gaussian variance / Prod 用を追加:

```lean
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensitySecondDeriv         -- convDensityAdd_deriv1_gaussian_eq
import InformationTheory.Shannon.FisherInfoV2
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime       -- convDensityAdd_pos / fisher_from_logDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic         -- integral_mul_(norm_)le_Lp_mul_Lq(_of_nonneg)
import Mathlib.MeasureTheory.Measure.Prod                   -- lintegral_lintegral_swap
import Mathlib.Probability.Distributions.Gaussian.Real      -- variance_fun_id_gaussianReal / integral_gaussianReal_eq_integral_smul

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

/-- Gaussian 2次モーメント over volume (自作要素 2): `∫ u², g_s(u) du = s`. -/
theorem integral_sq_mul_gaussianPDFReal {s : ℝ} (hs : 0 < s) :
    ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume = s := by
  sorry -- @residual(plan:fisher-stam-gaussian-moment)  -- via variance_fun_id_gaussianReal + integral_gaussianReal_eq_integral_smul

/-- pointwise Cauchy-Schwarz (自作要素 1). -/
theorem convScore_sq_le_pointwise
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ y, pX y * (x - y) * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) ∂volume) ^ 2
      ≤ (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x)
        * (∫ y, pX y * (x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) ∂volume) := by
  sorry -- @residual(plan:fisher-stam-pointwise-cs)  -- via integral_mul_norm_le_Lp_mul_Lq p=q=2

/-- 壁本体 (pointwise-CS route, `hpX_mass` 追加版). -/
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s) := by
  sorry -- @residual(wall:fisher-finiteness)  -- closure target: Step1 deriv1 + Step2 CS + Step3 lintegrand + Step4 Tonelli/moment

end InformationTheory.Shannon.FisherInfoV2
```

> **注**: `hpX_mass` 追加は壁 signature 改変 (判定 (d))。実装時は `convDensityAdd_fisher_integrable`
> (`FisherInfoV2DeBruijnAssembly.lean:1560`) の signature にも `hpX_mass` を 1 仮説追加し `…_chain_ibp_fisher`
> (`:2882` が保持) から thread。signature 改変を伴うため独立 honesty audit 起動条件 (CLAUDE.md「既存 declaration の
> signature を変更」) に該当 — closure session で fresh auditor を回すこと。
