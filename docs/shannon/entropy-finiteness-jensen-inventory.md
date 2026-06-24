# Entropy-finiteness Jensen log-poly majorant — closure feasibility inventory

> Scope: the **Jensen log-poly majorant core** behind the 3
> `sorry + @residual(wall:entropy-finiteness)` lemmas in
> `InformationTheory/Shannon/EntropyConvFinite.lean` (A `_negMulLog`:95 / B `_logFactor_deriv`:72 /
> C `_logFactor_deriv2`:50). The brief proposed reducing all 3 to one shared core
> `convDensityAdd_negLog_poly_majorant : -log p_t x ≤ A + B·x²` proved via Jensen
> (`ConcaveOn.le_map_integral`). This inventory tests whether that Jensen core is *needed*.
> **Inventory only — no implementation, no plan.**

## 一行サマリ (最重要判定)

**Jensen 核は不要。** 求める log-poly majorant `‖- log p_s x - 1‖ ≤ A + B·x²` は **既に repo に
genuine（`@audit:ok`, 0 sorry, sorryAx-free）で存在する** — `convDensityAdd_logFactor_poly_majorant`
(`FisherInfoV2DeBruijnAssembly.lean:336`)。しかも **Jensen 経由ではなく Gaussian 下界経由**
(`convDensityAdd_lower_bound_gaussian_uniformR`:220 + `Real.log_le_log` + 閉形 log 展開)。
さらに **product 積分可能性核** `(- log p_s - 1)·(1/2)·∂²p_s` の可積分 majorant も
`debruijnIdentityV2_holds_assembled_chain_domination` (`:1322`, `@audit:ok`, 0 sorry) で
route II (Tonelli + even Gaussian moment, `hpX_mom` 消費) により**既に閉じている**。
→ entropy-finiteness wall 3 本は **真の Mathlib 壁ではなく、既存 `@audit:ok` 資産への配線
(plumbing)**。`wall:entropy-finiteness` 分類は **誤分類の疑いが濃厚** で、`plan:` 級
(family-internal plumbing) に降格すべき。Jensen (`ConcaveOn.le_map_integral`) / `IsClosed s` /
`withDensity→IsProbabilityMeasure` のいずれも**不要**（既存 Gaussian-下界ルートが回避済）。

**残る懸念 (2 点)**:
1. 既存 majorant は `hpX_mass : (∫ y, pX y) = 1` (等式) を要求する。3 wall は現状 `hpX_int` のみで
   `hpX_mass` を持たない → signature に `hpX_mass` (+ B/C は `hpX_mom`) 追加が必要。regularity
   precondition であり honesty defect ではない。
2. **⚠ import cycle 確認済（決定的）**: `FisherInfoV2DeBruijnAssembly.lean:4` は
   `import InformationTheory.Shannon.EntropyConvFinite` し、3 wall を `Assembly:1973/1978/2432` で呼ぶ。
   即ち #1/#2/#3 (`@audit:ok` majorant) は wall の **下流** (Assembly) にある。
   → **EntropyConvFinite から Assembly を import すると循環**。配線 closure には
   #1/#2/#3 を Assembly から **両者の共通上流 file（または新規 shared file）へ移設**するか、
   3 wall 自体を Assembly 内へ移すかの構造判断が要る（plan 側責務、本 inventory の最重要 follow-up）。

---

## 主定理の最終形（再掲）と既存資産による証明骨格

```lean
-- wall C (deriv2): 現 signature (EntropyConvFinite.lean:50)
theorem convDensityAdd_logFactor_deriv2_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) volume
```

既存資産で閉じる手順骨格 (lemma チェーン、Jensen 不使用):

```
-- 必要 signature 追加: hpX_mass : (∫ y, pX y) = 1   (+ B/C: hpX_mom : Integrable (y²·pX))
obtain ⟨A, B, hB_nn, hLog⟩ :=                              -- ‖- log p_s -1‖ ≤ A + B·x²
  convDensityAdd_logFactor_poly_majorant pX … hpX_mass ht  -- Assembly:336, @audit:ok
obtain ⟨bnd, hbnd_int, hbnd⟩ :=                            -- ‖∂²p_s‖ ≤ bnd, Integrable bnd
  convDensityAdd_deriv2_poly_moment_majorant pX … hpX_mom ht -- Assembly:1199, @audit:ok
-- 積 (A+Bx²)·bnd の可積分性 = route II (Tonelli + even moment) は
-- debruijnIdentityV2_holds_assembled_chain_domination:1322 (@audit:ok) が既に実証
-- → 同型の Integrable.mono' で C を閉じる。s=t 固定版は ∀ᵐ over Ioo を 1 点 specialize。
exact Integrable.mono' (product-envelope) (aestronglyMeasurable …) (a.e. ‖integrand‖ ≤ env)
```

A (negMulLog) は `|negMulLog p_t| = p_t·|log p_t| ≤ p_t·(A + B·x²)`、
`∫ p_t·(A+Bx²) = A + B·E[(X+√tZ)²] = A + B·(E[X²]+t) < ∞`（`hpX_mom` で `E[X²]<∞`）。

---

## API 在庫テーブル

### A. 既存 repo 資産（決定的 — Jensen を不要にする本体）

各 declaration は `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean`。signature verbatim、
type-class 前提は無し（全て explicit arg）。全て `@audit:ok` / 0 local sorry / sorryAx-free。

| # | declaration | file:line | 結論 verbatim | 状態 |
|---|---|---|---|---|
| 1 | `convDensityAdd_logFactor_poly_majorant` | `Assembly:336` | `∃ A B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) → ‖- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩) x) - 1‖ ≤ A + B * x ^ 2` | ✅ `@audit:ok` **= 求める log-poly 核そのもの** |
| 2 | `convDensityAdd_deriv2_poly_moment_majorant` | `Assembly:1199` | `∃ bound : ℝ → ℝ, Integrable bound volume ∧ ∀ᵐ x ∂volume, ∀ s, (hs : s ∈ Set.Ioo (t/2)(2*t)) → ‖deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩))) x‖ ≤ bound x` | ✅ `@audit:ok` (consumes `hpX_mom`) = ∂²p_t 可積分 envelope |
| 3 | `debruijnIdentityV2_holds_assembled_chain_domination` | `Assembly:1322` | `∃ bound, Integrable bound volume ∧ (∀ᵐ x ∂volume, ∀ s, (hs : s ∈ Ioo (t/2)(2*t)) → ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩) x) - 1) * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩))) x)‖ ≤ bound x)` | ✅ `@audit:ok`, **product 可積分性核を既に実証** (route II Tonelli+even moment, `hpX_mom` 消費) |
| 4 | `convDensityAdd_lower_bound_gaussian_uniformR` | `Assembly:220` | `∃ R : ℝ, 0 < R ∧ ∀ (s : ℝ) (hs : 0 < s) (x : ℝ), (1/2) * gaussianPDFReal 0 ⟨s, hs.le⟩ (|x| + R) ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x` | ✅ `@audit:ok` = #1 の Jensen 代替ルート (s-uniform Gaussian 下界) |

#1 の引数 (verbatim):
```lean
(pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX)
(hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1) {t : ℝ} (ht : 0 < t)
```
#2 / #3 の引数 (verbatim、#1 に加えて):
```lean
(hpX_meas : Measurable pX)        -- #2/#3 は meas を genuine 使用
(hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
```
注: #3 の docstring 末尾「hpX_mass remains unused (only hpX_mom is load-bearing for the
integrability); kept for caller compatibility」 — #3 は `hpX_mass` を取るが実体は `hpX_mom` のみ消費。

### B. 補助 envelope 部品（#1–#3 の内部、再利用可）

| 概念 | declaration | file:line | signature / 結論 verbatim | 状態 |
|---|---|---|---|---|
| Gaussian×quartic 可積分 | `gaussHessMaj_polyWeight_integrable` | `Assembly:582` | `{t : ℝ} (ht : 0 < t) (a b : ℝ) : Integrable (fun u : ℝ => (a + b * u ^ 2) * gaussHessMaj t u) volume` | ✅ `@audit:ok` (= **poly-weight x² 版の envelope は既存**) |
| Gaussian×quartic 有界 | `gaussHessMaj_polyWeight_bdd` | `Assembly:628` | `{t : ℝ} (ht : 0 < t) {a b : ℝ} (ha : 0 ≤ a)(hb : 0 ≤ b) (u) : … ≤ const` | ✅ `@audit:ok` |
| Hessian kernel majorant | `gaussHessMaj` (def) | `Assembly:477` | `(t u : ℝ) : ℝ := (√(π*t))⁻¹ * exp(-u^2/(4*t)) * (4*u^2/t^2 + 2/t)` | ✅ `@audit:ok` |
| `gaussHessMaj` 可積分 | `gaussHessMaj_integrable` | `Assembly:545` | `{t}(ht : 0 < t) : Integrable (gaussHessMaj t) volume` | ✅ `@audit:ok` |
| conv envelope 可積分 (Tonelli) | `convKernel_envelope_integrable` | `Assembly:784` | `(pX K : ℝ → ℝ) (hpX_int : Integrable pX volume) (hpX_meas : Measurable pX) (hK_int : Integrable K volume) (hK_meas : Measurable K) : Integrable (fun x => ∫ y, pX y * K (x - y) ∂volume) volume` | ✅ `@audit:ok` |
| p_s 上界 (prefactor) | `convDensityAdd_le_prefactor` | `Assembly:163` | `(pX)(hpX_nn)(hpX_int : Integrable pX volume)(hpX_mass : (∫ y, pX y ∂volume) = 1){s}(hs : 0 < s)(x) : convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹` | ✅ `@audit:ok` |
| p_s 正値 | `convDensityAdd_pos` | `PerTime:784` | `(pX)(hpX_nn)(hpX_int : Integrable pX volume)(hpX_mass : 0 < ∫ y, pX y ∂volume){s}(hs : 0 < s)(x) : 0 < convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x` | ✅ |

### C. Jensen for concave log（**結論: 不使用で良い**。衝突回避済の確認として記録）

| 概念 | Mathlib API | file:line | signature / 前提 verbatim | 状態 |
|---|---|---|---|---|
| Jensen (concave, 確率測度) | `ConcaveOn.le_map_integral` | `Mathlib/Analysis/Convex/Integral.lean:208` | `[IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ)` | ✅ 存在。だが下記 `IsClosed s` 衝突 |
| log 凹性 (開区間) | `strictConcaveOn_log_Ioi` | `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67` | `theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log` | ✅ 但し **domain = `Ioi 0` (開)** |
| log 凹性 (`Ici 0`) | — | — | loogle `ConcaveOn ℝ (Set.Ici _) Real.log` = **Found 0**。`Ici 0` 版は不在 | ❌ 不在 |
| log 凹性 (下区間) | `strictConcaveOn_log_Iio` | `…/SpecificFunctions/Basic.lean` | `StrictConcaveOn ℝ (Iio 0) log` (負側、無関係) | ✅ 無関係 |

**`IsClosed s` 衝突の構造**: `ConcaveOn.le_map_integral` は `hsc : IsClosed s` を要求するが、
`log` の凹性は `Ioi 0` (**開区間、`IsClosed` でない**) でしか Mathlib に無い (`Ici 0` 版不在)。
Jensen を `s = Ioi 0` で適用しようとすると `IsClosed (Ioi 0)` が偽で詰まる。
→ **既存 repo は Jensen を一切使わず、Gaussian 下界 (#4) で log-poly 核 (#1) を作ることでこの衝突を構造的に回避済**。
よって Jensen 経由の再実装は不要かつ不利（`IsClosed s` 障害を新規に持ち込むだけ）。

### D. log の初等下界（Jensen 代替の elementary 部品、#1 が実際に使うのは log_le_log だが参考記録）

| 概念 | Mathlib API | file:line | signature verbatim | 用途 |
|---|---|---|---|---|
| `log x ≤ x - 1` | `Real.log_le_sub_one_of_pos` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:306` | `theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1` | 上界（負側 log の発散を避ける形では#1 は不使用、docstring 参照） |
| `1 - x⁻¹ ≤ log x` | `Real.one_sub_inv_le_log_of_pos` | `…/Log/Basic.lean:311` | `lemma one_sub_inv_le_log_of_pos (hx : 0 < x) : 1 - x⁻¹ ≤ log x` | log 下界（だが exp(+x²) 爆発のため #1 は採らない、下記注） |
| `x + 1 ≤ exp x` | `Real.add_one_le_exp` | `Mathlib/Analysis/Complex/Exponential.lean:646` | `theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` | 上記の素 |

注 (#1 docstring verbatim 抜粋): 「The route is "log of the lower bound" (`Real.log_le_log`+`Real.log_exp`),
NOT `-log p ≤ p⁻¹-1` (which would blow up as `exp(+x²)`)」。`one_sub_inv_le_log_of_pos` 系を log 下界に
使うと `-log p ≤ p⁻¹ - 1`、`p ~ g_t ~ exp(-x²)` のとき `p⁻¹ ~ exp(+x²)` で majorant が爆発するため
**採用不可**。#1 は Gaussian 下界 (#4) の `log` を直接展開する正しいルート。

### E. gaussianPDFReal の log 明示形（**Mathlib 不在、定義展開で導出**）

| 概念 | API | file:line | 状態 |
|---|---|---|---|
| `gaussianPDFReal` 定義 | `ProbabilityTheory.gaussianPDFReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:48` | ✅ `(μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))` (verbatim) |
| `Real.log (gaussianPDFReal …)` 補題 | — | — | ❌ loogle `Real.log (ProbabilityTheory.gaussianPDFReal _ _ _)` = **Found 0**。明示 log 補題不在 |

導出ルート (Mathlib 部品、#1 が実際に使う展開):
- `Real.log_mul` / `Real.log_inv` / `Real.log_sqrt` (`Log/Basic.lean:302`: `log (√x) = log x / 2`) /
  `Real.log_exp`。
- **検証済の値** (#1 body `hlog_pref`:367 verbatim):
  `log (√(2π·s))⁻¹ = -((1/2) * log (2*π*s))`。
  ∴ `log (gaussianPDFReal 0 ⟨s,_⟩ z) = -(1/2)·log(2πs) - z²/(2s)` （定義展開で機械的に出る、専用補題不要）。
  これは brief 想定の `-log√(2πt) - z²/(2t)` と **一致** (`log√(2πs) = (1/2)log(2πs)`)。

### F. withDensity → IsProbabilityMeasure / 積分橋（**Jensen 採るなら要、本ルートでは不使用**）

| 概念 | Mathlib API | file:line | signature verbatim | 状態 |
|---|---|---|---|---|
| `∫ over withDensity` (ENNReal density) | `MeasureTheory.integral_withDensity_eq_integral_toReal_smul` | `Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:317` | `{f : X → ℝ≥0∞} (f_meas : Measurable f) (hf_lt_top : ∀ᵐ x ∂μ, f x < ∞) (g : X → E) : ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ` | ✅ 存在 |
| 同 (NNReal density) | `MeasureTheory.integral_withDensity_eq_integral_smul` | `…/ContinuousLinearMap.lean:250` | `{f : X → ℝ≥0} (f_meas : Measurable f) (g : X → E) : ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ` | ✅ 存在 |
| 同 (AEMeasurable, ENNReal) | `MeasureTheory.integral_withDensity_eq_integral_toReal_smul₀` | `…/ContinuousLinearMap.lean:310` | `{f : X → ℝ≥0∞} (f_meas : AEMeasurable f μ) (hf_lt_top : ∀ᵐ x ∂μ, f x < ∞) (g : X → E) : ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ` | ✅ 存在 |
| `withDensity → IsProbabilityMeasure` | — | — | ❌ **不在**: loogle `MeasureTheory.isProbabilityMeasure_withDensity` = unknown identifier (no decl); `IsProbabilityMeasure (Measure.withDensity _ _)` 結論検索 = 該当宣言 0。`isFiniteMeasure_withDensity` (`Mathlib/MeasureTheory/Measure/WithDensity.lean`, `lintegral ≠ ∞ → IsFiniteMeasure`) はあるが Probability 版は手作り (`lintegral = 1` → `⟨…⟩` 構成) 必要 | ❌ 自作要（但し本ルートでは**不使用**） |

→ Jensen ルートを採るなら `pX dy` を確率測度化する F が要るが、`IsProbabilityMeasure (withDensity …)`
が Mathlib 不在で手作りになる。**既存 Gaussian-下界ルート (#1/#4) はこの手作りを完全に回避している**ので
F 全体が不要。

### G. ∫ pX(y)(x-y)² dy の poly 評価部品（Jensen ルート想定、本ルート不使用）

| 概念 | 評価 / 部品 | 状態 |
|---|---|---|
| `∫ pX(y)(x-y)² dy = x²∫pX - 2x∫y·pX + ∫y²·pX` | 機械的展開 | 本ルート不使用 (#1 が Gaussian 下界で直接 x² majorant 出す) |
| 1 次モーメント `∫ y·pX` 可積分性 | `hpX_int.add hpX_mom` 経由、`2|y| ≤ 1 + y²` 支配 | #3 docstring:1239 verbatim「the first moment is dominated by `2|y| ≤ 1+y²`」で実証済 |
| 2 次モーメント `∫ y²·pX` | `hpX_mom` そのもの | ✅ |
| Gaussian moment 素 | `integrable_rpow_mul_exp_neg_mul_sq (hb : 0 < b) (hk : -1 < k)` / `integrable_exp_neg_mul_sq (hb : 0 < b)` | ✅ Mathlib (#2/#3/B が利用) |

---

## 主要前提条件ボックス

- **`convDensityAdd_logFactor_poly_majorant` (#1)**: 要 `hpX_nn` / `hpX_int` / **`hpX_mass : (∫ pX) = 1`
  (等式!)** / `ht : 0 < t`。`_hpX_meas` は取るが unused。`hpX_mass` は等式（`> 0` でなく `= 1`）で、
  内部 `convDensityAdd_le_prefactor`（質量正規化 `∫(pX·pref)=pref`）と `_uniformR` 緊密化
  （`∫_{[-R,R]} pX ≥ 1/2`）で genuine 消費。**3 wall は現状 `hpX_mass` を持たない → signature 追加要**。
- **`convDensityAdd_deriv2_poly_moment_majorant` (#2)** / **`_chain_domination` (#3)**: 上記に加え
  `hpX_meas`（genuine 使用）+ `hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume`。`hpX_mom` は
  heavy-tail（Cauchy 等、分散∞）を honest に排除する **regularity precondition**（load-bearing でない、
  audit 済）。
- **`ConcaveOn.le_map_integral` (Jensen)**: `[IsProbabilityMeasure μ]` + `ContinuousOn g s` +
  **`IsClosed s`** + `∀ᵐ x ∂μ, f x ∈ s` + `Integrable f μ` + `Integrable (g ∘ f) μ`。
  `IsClosed s` が `log` 凹性 domain `Ioi 0`（開）と衝突 → **本核では使わない**。
- **`integrable_rpow_mul_exp_neg_mul_sq`**: `(hb : 0 < b)` + `(hk : -1 < k)`（`rpow` 指数下限）。

---

## 自作が必要な要素（優先度順）

**核（majorant）は全て既存。残るのは "既存 `@audit:ok` 資産 → 3 wall への配線" のみ。**

1. **(最優先) wall C の配線**: `convDensityAdd_logFactor_deriv2_integrable` を #1 + #2 + #3 の
   pattern で閉じる。#3 が既に `(- log p_s - 1)·(1/2)·∂²p_s` の `∀ᵐ over Ioo` 可積分 majorant を
   与えるので、(i) `s = t` 固定への specialize（`∀ᵐ over Ioo (t/2,2t)` を内点 `t` で評価）、
   (ii) `(1/2)` 因子の除去（`Integrable.const_mul` の逆 / `2 *`）、(iii) `Integrable.mono'` で
   `‖integrand‖ ≤ env` を a.e. で立てる。工数: **小〜中 (~40-80 行)**。Jensen 核実装は**ゼロ**。
   落とし穴: #3 は `∀ s ∈ Ioo` の uniform 形 → 単一 `t` への落とし込みで `a.e.` 量化子の
   specialize（`hbnd x` の `s := t` 適用に `t ∈ Ioo (t/2)(2*t)` = `⟨by linarith, by linarith⟩` 要）。
2. **wall B (∂p_t 版)**: #2/#3 の deriv2 を deriv1 に差し替えた envelope が必要。#3 は deriv2 専用なので、
   **deriv1 版の `_chain_domination` 相当（`(- log p_s -1)·∂p_s` の可積分 majorant）が未整備の可能性**。
   `gaussHessMaj`（Hessian = 2 階）に対応する 1 階 Gaussian-deriv kernel majorant が要る。
   loogle/rg で `gaussGradMaj` 等の 1 階版が repo にあるか **要追加確認**（本 inventory 未確認、
   時間制約）。無ければ `gaussHessMaj` と同型で 1 階 kernel を 1 本自作（~60-100 行、`gaussHessMaj`
   の証明をテンプレに）。
3. **wall A (negMulLog)**: `|negMulLog p_t| ≤ p_t·(A+Bx²)`（#1 + `p_t ≤ C_t`）、
   `∫ p_t·(A+Bx²) = A·1 + B·E[(X+√tZ)²] = A + B·(E[X²]+t)`。E[X²]<∞ は `hpX_mom`、
   E[(X+√tZ)²] = E[X²] + t（独立和の 2 次モーメント、Z は標準）。最も軽い (~40-60 行)。
   conv 2 次モーメント `∫ x²·p_t = E[X²]+t` の補題が repo にあるか **要追加確認**（#3 が内部で
   `∫ y²·pX` を扱うので部品は近い）。

---

## Mathlib 壁の列挙（`@residual(wall:entropy-finiteness)` 対象 — **再分類提案**）

**真に Mathlib 不在で残る核は無い（majorant は既存 `@audit:ok`）。** loogle 確認:

1. `Real.log (ProbabilityTheory.gaussianPDFReal _ _ _)` → **Found 0**（明示 log 補題不在だが、
   定義展開 `log_mul`/`log_inv`/`log_sqrt`/`log_exp` で導出可、#1 が既にやっている → 壁でない）。
2. `ConcaveOn ℝ (Set.Ici _) Real.log` → **Found 0**（`Ici 0` 版 log 凹性不在 → Jensen ルートの
   `IsClosed s` 障害の根。但し **Gaussian-下界ルートで回避済なので壁にならない**）。
3. `MeasureTheory.isProbabilityMeasure_withDensity` → **unknown identifier / Found 0**
   （`withDensity → IsProbabilityMeasure` 不在。但し Jensen ルート専用 → 本ルートで不使用、壁にならない）。

→ **3 wall は `wall:entropy-finiteness` ではなく `plan:` 級（family-internal plumbing）。**
既存 `@audit:ok` の #1/#2/#3 へ配線するだけで genuine closure 可能。`docs/audit/audit-tags.md`
「Mathlib 壁の誤用: 実は選択(big)を blocked(hard)と偽る」に該当する誤分類の疑い。
**shared sorry 補題化は不要**（共有核は既に `@audit:ok` で実在、`sorry` を持たない）。
配線 plan（`plan:entropy-finiteness-plumbing` 等）への再分類を強く推奨。

---

## 撤退ラインへの距離

親計画（de Bruijn per-time row, system W）の撤退ライン: **発動しない。むしろ後退でなく前進。**

- 本 wall は integrability precondition であり、de Bruijn 同定の数学的本筋（IBP + Fisher = `½J(p_t)`）
  には触れない。
- 既存 #1/#2/#3 が `@audit:ok` で核を実証済 → 3 wall は **wall → plan 降格（honesty 改善）** が可能。
  これは撤退ではなく、誤分類された壁を正しく plumbing に直す **net honesty 向上**。
- 縮退案（万一 deriv1 envelope (#2 の B 用 1 階版) が想定外に困難な場合）: B のみ `hpX_mom` で閉じない
  なら **compact-support pX 制限版を新規撤退ライン**に。但し #3（deriv2, より高階で困難な側）が既に
  `@audit:ok` で閉じている以上、より易しい deriv1 が閉じない可能性は低い。撤退口は sorry + `@residual`、
  仮説束化は禁止。

---

## 着手 skeleton

```lean
-- ⚠ import InformationTheory.Shannon.FisherInfoV2DeBruijnAssembly は CYCLE のため不可:
--   Assembly:4 が EntropyConvFinite を import し 3 wall を呼ぶ (Assembly:1973/1978/2432)。
-- → #1/#2/#3 + envelope 部品を shared 上流 file へ切り出してから import する（構造変更, plan 責務）:
import InformationTheory.Shannon.ConvDensityMajorant   -- (仮) #1/#2/#3 を切り出した新規 shared file
-- 現状 EntropyConvFinite.lean:1 は import InformationTheory.Shannon.EPIConvDensity のみ。

namespace InformationTheory.Shannon.EntropyConvFinite

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

-- wall A: hpX_mass + hpX_mom 追加（negMulLog、p_t·(A+Bx²) 支配 + E[(X+√tZ)²]<∞）
theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume := by
  sorry -- @residual(plan:entropy-finiteness-plumbing)  -- 再分類提案: wall → plan

-- wall B: hpX_mass + hpX_mom 追加（1 階 envelope = gaussGradMaj 相当が要、要追加確認）
theorem convDensityAdd_logFactor_deriv_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) volume := by
  sorry -- @residual(plan:entropy-finiteness-plumbing)

-- wall C: hpX_mass + hpX_mom 追加（#3 _chain_domination を s=t specialize + /2 除去 + mono'）
theorem convDensityAdd_logFactor_deriv2_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) volume := by
  sorry -- @residual(plan:entropy-finiteness-plumbing)

end InformationTheory.Shannon.EntropyConvFinite
```

**consumer 側の付随変更**（wall-inventory `:75-90` 既出）: 3 wall に `hpX_mass`/`hpX_mom` を追加すると、
`Assembly:1930 _ibp_step` / `:2043 _ibp_fisher` の signature に両引数 thread が要る。最終呼出元
`_chain_parametric` (`:2399`) は既に `hpX_mass`/`hpX_mom` 保持（`:2402`, `convDensityAdd_logFactor_poly_majorant`
を既に呼んでいるため scope 内）。機械的 thread のみ。

---

## 未確認事項（次タスクで詰めるべき、本 inventory の時間制約で未到達）

1. **deriv1 (∂p_t) 用の 1 階 Gaussian-deriv kernel majorant** が repo にあるか
   （`gaussHessMaj` の 1 階版 `gaussGradMaj` 等）。無ければ wall B は #3 の deriv2 envelope を流用できず、
   1 本自作（`gaussHessMaj` テンプレ ~60-100 行）。**wall B の工数はこれ次第**。
2. **conv 2 次モーメント `∫ x²·p_t = E[X²]+t` の補題**が repo にあるか（wall A の `∫ p_t·Bx²` 評価用）。
3. **import cycle = 確認済（CONFIRMED、skeleton の `import Assembly` は不可）**:
   `FisherInfoV2DeBruijnAssembly.lean:4` が `import InformationTheory.Shannon.EntropyConvFinite` し、
   3 wall を `Assembly:1973`（C）/`:1978`（B）/`:2432`（A）で実際に呼ぶ。よって #1/#2/#3 の
   `@audit:ok` majorant は wall の **下流**にあり、`EntropyConvFinite` から直接 import できない（循環）。
   **closure には構造変更が必須**: (a) #1/#2/#3 + envelope 部品（`gaussHessMaj` 系, `convKernel_envelope_integrable`,
   `convDensityAdd_le_prefactor`, `_lower_bound_gaussian_uniformR` 等）を Assembly から
   `EntropyConvFinite` の上流（または新規 shared file, 例 `InformationTheory/Shannon/ConvDensityMajorant.lean`）へ
   切り出し、Assembly と EntropyConvFinite の双方がそれを import する、または (b) 3 wall を Assembly 内へ移設。
   いずれも plan 側の構造判断。**上の skeleton の `import …Assembly` は cycle のため不可** — shared file 経由に
   差し替えること。
