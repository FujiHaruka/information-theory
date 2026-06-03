# EPI de Bruijn **per-time** identity — Mathlib API re-attack inventory

> **Scope**: `debruijnIdentityV2_holds` (`InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:245`,
> `@residual(wall:debruijn-integration)`) を genuine 化するのに必要な Mathlib API の
> 構造化在庫。**per-time** の de Bruijn 微分恒等式
> `(d/dt) differentialEntropy(P.map(X+√t·Z)) = (1/2)·J(X+√t·Z)` (Cover-Thomas
> Lemma 17.7.2 の time-derivative form、一般 `X`) が対象。
>
> **積分形** (`∫_0^T` の FTC lift) は別 wall (`debruijnIntegrationIdentity_holds`,
> 同じ slug) で、`epi-debruijn-integration-mathlib-inventory.md` (FTC) +
> `epi-debruijn-tail-mathlib-inventory.md` (EReal tail) が既出。本 inventory は
> **per-time HasDerivAt** の解析核 (heat eq + dominated diff + IBP) に焦点を絞り、
> 既出 lemma は「既出 (参照)」で済ませ、新規軸 (parametric integral / heat kernel /
> 無限区間 IBP / rnDeriv↔withDensity / convolution density 再利用) に注力する。
>
> **Parent plan**: `epi-debruijn-integration-plan.md` Phase B (撤退ライン L-EPI2,
> per-time wall は Gaussian 限定で genuine、一般 `X` は wall sorry)。
> **Wall SoT**: `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:245`。

---

## 0. 一行サマリ

per-time wall を genuine 化する解析パイプラインは **5 軸中 3 軸が Mathlib 完備
(parametric integral diff, 無限区間 IBP, rnDeriv↔withDensity)、1 軸が repo 内 genuine
資産で代替可 (convolution density = `EPIConvDensity.lean`、`@audit:ok` sorryAx-free)、
1 軸 (Gaussian heat kernel / heat semigroup) のみ完全不在** (`"heat"` / `"Mehler"` /
`"OrnsteinUhlenbeck"` / `"FokkerPlanck"` すべて `Found 0`)。最も重要な発見:
**無限区間 IBP は Mathlib に存在する** (`MeasureTheory.integral_mul_deriv_eq_deriv_mul`
+ `integral_Ioi_mul_deriv_eq_sub`、`IntegralEqImproper.lean:1307/1352`) — 旧
`epi-debruijn-integration-mathlib-inventory.md:262` の「無限区間 FTC は bounded only」
記述は **誤り (per-time IBP には適用可)**。per-time 解析の closure route は
**density-route (`convDensityAdd`) 再利用 → parametric-integral diff → IBP** が
最有望、自作見積 **~150-220 行** (density witness の regularity 供給が主コスト)。
**`@residual(wall:debruijn-integration)` の wall 性は「選択 (big)」寄り** — 解析核は
Mathlib に出揃っており、不在は Gaussian 専用 closed-form (heat kernel) のみ。一般 `X`
の genuine 化は「hard wall」ではなく「long but present」。

---

## 1. 主定理の最終形 (wall の verbatim 再掲)

`InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:245-254`:

```lean
theorem debruijnIdentityV2_holds
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    {t : ℝ} (_ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  sorry -- @residual(wall:debruijn-integration)
```

`IsRegularDeBruijnHypV2` (`:200-207`、Phase 2.B で `derivAt_entropy_eq_half_fisher_v2`
field 削除済の現行 2-field 形):

```lean
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (t : ℝ) where
  Z_law : P.map Z = gaussianReal 0 1
  density_t : ℝ → ℝ
```

**RHS の Fisher info** (`FisherInfoV2.lean:89,103`):
```lean
noncomputable def fisherInfoOfDensity (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv f x) ^ 2) * ENNReal.ofReal (f x) ∂volume
noncomputable def fisherInfoOfDensityReal (f : ℝ → ℝ) : ℝ := (fisherInfoOfDensity f).toReal
```

### 証明戦略 (pseudo-Lean、density-route 経由 ~7 段)

```text
-- p_t := density of P.map(X+√t·Z) at time t (= convDensityAdd p_X (heatKernel-density))
-- 1. P.map (X+√t Z) ≪ volume, density = h_reg.density_t  (regularity / withDensity 表現)
have hpdf : P.map (gaussianConvolution X Z s)
              = volume.withDensity (ENNReal.ofReal ∘ pPath s)              -- 軸4
-- 2. differentialEntropy(...) = ∫ x, negMulLog (pPath s x) ∂volume         -- 既出 (DifferentialEntropy.lean:51/65)
rw [differentialEntropy_eq_integral_density ...]
-- 3. (d/ds) ∫ x, -(pPath s x) log (pPath s x) ∂volume                      -- 軸1 parametric integral diff
have := hasDerivAt_integral_of_dominated_loc_of_deriv_le ...
-- 4. ∂_s pPath via heat equation  ∂_s p = (1/2) ∂²_x p                     -- 軸2 (Mathlib 不在 → 自作 / convDensityAdd_hasDerivAt 経由)
-- 5. de Bruijn 計算: ∫ negMulLog' · ∂_s p  →IBP→  (1/2) ∫ (∂_x p)²/p       -- 軸3 無限区間 IBP
have := integral_mul_deriv_eq_deriv_mul ...
-- 6. ∫ (∂_x p)²/p = ∫ (logDeriv p)² · p = fisherInfoOfDensity (p t) .toReal -- 軸5 logDeriv 表現 (EPIConvDensity)
-- 7. RHS shape を fisherInfoOfDensityReal h_reg.density_t に一致させる congr
```

---

## 2. 軸 1 — Parametric integral の微分 (differentiation under the integral sign)

| 概念 | Mathlib API | file:line | 状態 | per-time での扱い |
|---|---|---|---|---|
| deriv under ∫ (deriv-bound 形) | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:289` | PRESENT | 段 3 の核 (entropy 積分の `(d/ds)`) |
| deriv under ∫ (Lipschitz 形) | `hasDerivAt_integral_of_dominated_loc_of_lip` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:263` | PRESENT | 代替 (bound が Lipschitz の場合) |
| fderiv under ∫ (deriv-bound) | `hasFDerivAt_integral_of_dominated_of_fderiv_le` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:~233` | PRESENT | 多変数版、本軸では不要 (1-param) |
| intervalIntegral 版 deriv | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` | `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` | PRESENT | bounded 区間 ∫ への deriv (積分形 wall 用、本軸 per-time では ∫ over volume 全体なので非使用) |
| intervalIntegral 版 lip | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip` | `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` | PRESENT | 同上 |

### 核 lemma 完全署名 (verbatim、型クラス `[...]` 含む)

`Mathlib/Analysis/Calculus/ParametricIntegral.lean:67-71` の section variable (全 lemma 共有):
```lean
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
-- (:257 で再宣言) variable {F : 𝕜 → α → E} {x₀ : 𝕜} {s : Set 𝕜}
```

`:289-294`:
```lean
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀
```

**引数型 (順)**: `hs : s ∈ 𝓝 x₀` / `hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ` /
`hF_int : Integrable (F x₀) μ` / `{F' : 𝕜 → α → E}` (implicit) /
`hF'_meas : AEStronglyMeasurable (F' x₀) μ` /
`h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a` / `bound_integrable : Integrable bound μ` /
`h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x`。
**結論形 (verbatim)**: `Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀`。

**この軸の Mathlib 充足度**: **完備**。`EPIConvDensity.convDensityAdd_hasDerivAt`
(`@audit:ok`) が既にこの lemma を repo 内で genuine に使用済 (`EPIConvDensity.lean:99-103`)、
同じパターンを per-time entropy 積分 `∫ x, negMulLog (pPath s x) ∂volume` の `s`-微分に
適用すれば良い。**落とし穴**: `[RCLike 𝕜]` なので `𝕜 := ℝ` 明示、`H := ℝ`、`E := ℝ`;
`bound` の Integrable 供給 (Gaussian-tail dominating function) が regularity precondition
として外出し必要 (`density_t` には pinned されていない — `IsRegularDeBruijnHypV2` 拡張要、
parent plan の `_hX/_hZ/_hXZ` 復元議論と同じ forward-looking 負債)。

---

## 3. 軸 2 — Gaussian heat kernel / heat semigroup

| 概念 | loogle query | 結果 | 状態 |
|---|---|---|---|
| heat kernel (名前) | `"heatKernel"` | `Found 0 declarations` | **全不在** |
| heat (任意名) | `"heat"` | `Found 0 declarations` | **全不在** |
| Fokker-Planck | `"FokkerPlanck"` | `Found 0 declarations` | **全不在** |
| Mehler kernel | `"Mehler"` | `Found 0 declarations` | **全不在** |
| Ornstein-Uhlenbeck semigroup | `"OrnsteinUhlenbeck"` | `Found 0 declarations` | **全不在** |
| `Mathlib.Analysis.PDE.*` folder | (既出: `rg "PDE"` no folder) | 不在 | **全不在** (`epi-debruijn-integration-mathlib-inventory.md:258` 既出) |

### Gaussian density は存在するが微分 lemma が無い

| 概念 | Mathlib API | file:line | 状態 | 備考 |
|---|---|---|---|---|
| Gaussian density (実数値) | `ProbabilityTheory.gaussianPDFReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | PRESENT (def) | `"gaussianPDFReal"` で 14 件、すべて measurability / 非負 / 積分 = 1 / `_add` / `_mul` 系。**`HasDerivAt` lemma は `Found 0`** (`"gaussianPDFReal", HasDerivAt` → 0 件) |
| Gaussian conv 加算則 | `ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | PRESENT | 既出 (tail inventory D-1)、Gaussian case の law 計算用 |
| negMulLog の deriv | `Real.deriv_negMulLog` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | PRESENT | `"negMulLog", deriv` → `Real.deriv_negMulLog` + `Real.deriv2_negMulLog` 2 件。段 5 の entropy 積分被積分関数の x-微分に使用可 |

**この軸の Mathlib 充足度**: **全不在 (heat semigroup)** + 部分 (Gaussian density は def
のみ、微分 lemma 不在)。**Found 0 断定**: `"heat"` / `"Mehler"` / `"OrnsteinUhlenbeck"` /
`"FokkerPlanck"` すべて `Found 0 declarations`。Gaussian heat-flow path の closed-form
微分は完全自作 (heat equation `∂_s p = (1/2) ∂²_x p` の per-density 検証)。**ただし
per-time wall では heat kernel の closed-form は必須ではない** — density-route
(`convDensityAdd` の parametric diff、軸 5) で `∂_s pPath` を `convDensityAddDeriv` 形に
取り出せれば heat-kernel 経由を回避できる。Gaussian 専用 closed-form discharge
(`deBruijn_identity_v2_gaussian`, `FisherInfoV2DeBruijn.lean:360`、既出 integration
inventory A-7) は既に genuine なので、wall の残りは **一般 `X` のみ**。

---

## 4. 軸 3 — Integration by parts on ℝ (無限区間)

> **重要な是正**: `epi-debruijn-integration-mathlib-inventory.md:262` は「Unbounded
> interval FTC は bounded only」と記述したが、これは **誤り**。Mathlib には無限区間
> (`(-∞,∞)` と `(a,∞)`) の **IBP** が `IntegralEqImproper.lean` に揃っている。per-time
> de Bruijn の段 5 (entropy 微分 → Fisher info への IBP 変換) はこれで直接書ける。

| 概念 | Mathlib API | file:line | 状態 | per-time での扱い |
|---|---|---|---|---|
| IBP 有界区間 (基準) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean` | PRESENT | 既出 (integration inventory 周辺)、bounded |
| **IBP `(-∞,∞)`** | `MeasureTheory.integral_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1307` | **PRESENT (新規発見)** | 段 5 の核 (entropy 微分 → Fisher) |
| **IBP `(-∞,∞)` 全可積分版** | `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1318` | **PRESENT** | 境界項 0 (Gaussian-tail decay) の場合に最簡 |
| IBP `(-∞,∞)` (和形) | `MeasureTheory.integral_deriv_mul_eq_sub` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1296` | PRESENT | `u'v + uv'` 形 |
| **IBP `(a,∞)`** | `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1352` | PRESENT | 半無限区間版 |
| IBP `(a,∞)` 和形 | `MeasureTheory.integral_Ioi_deriv_mul_eq_sub` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1331` | PRESENT | 同上 |
| compact-support `(a,∞)` FTC | `HasCompactSupport.integral_Ioi_deriv_eq` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean` | PRESENT | 境界項処理が compact support 経由の場合 |

### 核 lemma 完全署名 (verbatim)

`IntegralEqImproper.lean:1290-1293` の section variable (IntegrationByPartsAlgebra):
```lean
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℝ} {a' b' : A} {u : ℝ → A} {v : ℝ → A} {u' : ℝ → A} {v' : ℝ → A}
```

`:1307-1314`:
```lean
theorem integral_mul_deriv_eq_deriv_mul [CompleteSpace A]
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ), u x * v' x = b' - a' - ∫ (x : ℝ), u' x * v x
```

**引数型 (順)**: `[CompleteSpace A]` (inst) / `hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x` /
`hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x` / `huv' : Integrable (u * v')` /
`hu'v : Integrable (u' * v)` / `h_bot : Tendsto (u * v) atBot (𝓝 a')` /
`h_top : Tendsto (u * v) atTop (𝓝 b')`。
**結論形 (verbatim)**: `∫ (x : ℝ), u x * v' x = b' - a' - ∫ (x : ℝ), u' x * v x`。

`:1318-1324` (境界項消去版):
```lean
theorem integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x
```
(注: この版は `[NormedRing A] [NormedAlgebra ℝ A]` のみ、`[CompleteSpace A]` は `:1326`
の `variable [CompleteSpace A]` 後に来る `integral_Ioi_*` 系で要求。`A := ℝ` なら全部満たす。)

**この軸の Mathlib 充足度**: **完備**。`A := ℝ` で `[NormedRing ℝ] [NormedAlgebra ℝ ℝ]
[CompleteSpace ℝ]` すべて自動。**落とし穴**: (1) `hu`/`hv` の `∀ x ∈ tsupport v/u` は
support 全域での `HasDerivAt` 要求 — entropy 被積分関数 `negMulLog ∘ p` と `p` が滑らかで
ない領域 (density の zero set / 非可微点) で破綻しうる → density `p` の global `C¹`
regularity が precondition (Gaussian-tail で自然だが、`density_t` には pinned されていない)。
(2) 境界項 `Tendsto (u*v) atBot/atTop (𝓝 0)` は Gaussian-tail decay で成立だが、一般 `X`
では別途証明が要る。(3) `u*v` は `Pi.mul` (pointwise) — `integral_Ioi_*` 内部で
`Pi.mul_def` rewrite している点に注意。

---

## 5. 軸 4 — rnDeriv of pushforward の微分可能性 / withDensity 経由

| 概念 | Mathlib API | file:line | 状態 | per-time での扱い |
|---|---|---|---|---|
| entropy の withDensity 表現 | `InformationTheory.Shannon.differentialEntropy_eq_integral_withDensity` | `InformationTheory/Shannon/DifferentialEntropy.lean:51` | PRESENT (repo, 既出) | 段 2、`μ = volume.withDensity f` 形へ |
| entropy の実数密度表現 | `InformationTheory.Shannon.differentialEntropy_eq_integral_density` | `InformationTheory/Shannon/DifferentialEntropy.lean:65` | PRESENT (repo) | 段 2、`-∫ f log f` 形 (negMulLog の符号付き) |
| `withDensity ∘ rnDeriv = μ` | `MeasureTheory.Measure.withDensity_rnDeriv_eq` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean` | PRESENT | `μ ≪ volume` 往復 |
| `rnDeriv (withDensity f) = f` (ae) | `MeasureTheory.Measure.rnDeriv_withDensity` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` | PRESENT | 段 1-2 の核 (repo の `differentialEntropy_eq_integral_withDensity:57` で既使用) |
| `rnDeriv_withDensity₀` (ae-meas 版) | `MeasureTheory.Measure.rnDeriv_withDensity₀` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` | PRESENT | f が ae-measurable のみの場合 |
| pushforward → withDensity (PDF) | `MeasureTheory.map_eq_withDensity_pdf` | `Mathlib/Probability/Density.lean` | PRESENT | `P.map g` の PDF 表現 |
| PDF 一意性 | `MeasureTheory.pdf.eq_of_map_eq_withDensity` | `Mathlib/Probability/Density.lean` | PRESENT | density witness 同定 |

`MeasureTheory.Measure.rnDeriv_withDensity` の使用実績 (repo, `DifferentialEntropy.lean:57`):
```lean
have h := Measure.rnDeriv_withDensity (volume : Measure ℝ) hf  -- hf : Measurable f
-- h : (volume.withDensity f).rnDeriv volume =ᵐ[volume] f
```

**この軸の Mathlib 充足度**: **完備**。pushforward → withDensity → 実数密度 → entropy
積分の往復は repo の `differentialEntropy_eq_integral_withDensity/density` が既に閉路を
実演済。**落とし穴**: per-time では密度が **時刻 `s` に依存** (`pPath s : ℝ → ℝ`) する。
各 `s` で `P.map (gaussianConvolution X Z s) = volume.withDensity (ENNReal.ofReal ∘ pPath s)`
を立てる必要があり、この `pPath s` が `convDensityAdd p_X (Gaussian density at √s)` に
一致することの証明が **軸 5 と接続**。pushforward `(P.map g).rnDeriv volume` の閉形式
(convolution density) を Mathlib が直接与えるかは確認できず — 独立和の密度 = 畳み込みは
`convDensityAdd` (repo) で自作済 (Mathlib `MeasureTheory.convolution` 直結 lemma は本軸では
未使用、`convDensityAdd` が Bochner `∫` 形で entropy 積分と shape 整合)。

---

## 6. 軸 5 — convolution の密度と微分 (repo `EPIConvDensity.lean` 再利用)

> `EPIConvDensity.lean` は density-route の **genuine 資産** (3 件 `@audit:ok`,
> sorryAx-free, independent audit 2026-05-30 PASS)。per-time wall の `∂_s pPath` 取り出しに
> 直接再利用可能。

| 概念 | repo API | file:line | 状態 | per-time での扱い |
|---|---|---|---|---|
| 畳み込み密度 (Bochner ∫ 形) | `InformationTheory.Shannon.convDensityAdd` | `InformationTheory/Shannon/EPIConvDensity.lean:40` | PRESENT (`def`) | `pPath s = convDensityAdd p_X (gaussian density √s)` の同定 |
| 畳み込み密度の z-微分被積分 | `convDensityAddDeriv` | `InformationTheory/Shannon/EPIConvDensity.lean:64` | PRESENT (`def`) | `∂_z (p_X x · p_Y(z-x)) = p_X x · p_Y'(z-x)` |
| 畳み込み密度の HasDerivAt | `convDensityAdd_hasDerivAt` | `InformationTheory/Shannon/EPIConvDensity.lean:86` | **PRESENT (`@audit:ok`, sorryAx-free)** | `convDensityAdd` の z-微分 (parametric integral diff 経由) |
| 畳み込み密度の logDeriv (score) | `convDensityAdd_logDeriv` | `InformationTheory/Shannon/EPIConvDensity.lean:113` | **PRESENT (`@audit:ok`)** | 段 6: `logDeriv p = (∫ p_X p_Y')/p` → Fisher info |
| 公開 gateway | `convDensity_add_differentiable` | `InformationTheory/Shannon/EPIConvDensity.lean:140` | **PRESENT (`@audit:ok`)** | 上記 2 atom の bundle |
| 畳み込み交換律 | `convDensityAdd_comm` | `InformationTheory/Shannon/EPIConvDensity.lean:45` | PRESENT (genuine) | 補助 |

### `convDensityAdd_hasDerivAt` 完全署名 (verbatim)

`EPIConvDensity.lean:86-98`:
```lean
theorem convDensityAdd_hasDerivAt
    (pX pY : ℝ → ℝ) (z₀ : ℝ) {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ nhds z₀)
    (hF_meas : ∀ᶠ z in nhds z₀,
        AEStronglyMeasurable (fun x => pX x * pY (z - x)) volume)
    (hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume)
    (hF'_meas : AEStronglyMeasurable (fun x => convDensityAddDeriv pX pY z₀ x) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖convDensityAddDeriv pX pY z x‖ ≤ bound x)
    (bound_integrable : Integrable bound volume)
    (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s,
        HasDerivAt (fun z => pX x * pY (z - x)) (convDensityAddDeriv pX pY z x) z) :
    HasDerivAt (convDensityAdd pX pY)
      (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) z₀
```

**型クラス前提**: なし (すべて explicit/implicit value 引数、`volume` 固定)。
**結論形 (verbatim)**: `HasDerivAt (convDensityAdd pX pY) (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) z₀`。

**この軸の Mathlib 充足度**: **部分 (repo 資産で代替可)**。convolution density の
**z (空間) 微分**は `convDensityAdd_hasDerivAt` で genuine。しかし per-time wall に必要なのは
**s (時刻) 微分** (`∂_s pPath`) であり、これは「Gaussian factor `pY = gaussian density at √s`
の `s`-依存微分」= heat equation 接続 (軸 2 不在部) と組み合わさる。`convDensityAdd` の枠組み
自体は s-微分にも転用可能だが、`pY = (fun y => gaussianPDFReal 0 ⟨s,_⟩ y)` の `s`-微分 lemma
が Mathlib 不在 (軸 2)。**自作見積の主因**はここ (heat equation の per-density 検証 ~80-120 行)。

---

## 7. 主要前提条件ボックス (前提事故の起きやすい lemma)

- **`hasDerivAt_integral_of_dominated_loc_of_deriv_le`** (軸1): `[RCLike 𝕜]` →
  `𝕜 := ℝ` で OK だが、`bound : α → ℝ` の `Integrable bound μ` が **load-bearing でない
  regularity precondition**。`IsRegularDeBruijnHypV2` は `density_t` を unpinned で持つだけ
  なので、bound 関数 (Gaussian-tail dominating) を供給する field/引数の追加が必要
  (parent plan `_hX/_hZ/_hXZ` 復元議論と同根)。`h_diff` は **per-`x` 被積分関数**の微分を
  量化 — 積分そのものの微分を仮定してはいけない (load-bearing bundling 回避)。
- **`integral_mul_deriv_eq_deriv_mul`** (軸3): `hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x`
  は **support 全域**での `HasDerivAt`。entropy 被積分 `negMulLog ∘ p` は `p = 0` の領域で
  `negMulLog` の微分が `0` に landing するが、`p` の zero set 上の `HasDerivAt` は density
  の `C¹` global regularity を要求。境界項 `Tendsto (u*v) atBot/atTop (𝓝 0)` は Gaussian-tail
  decay 前提。一般 `X` では tail decay が別証明。
- **`differentialEntropy_eq_integral_density`** (軸4, repo): `hf_nn : ∀ x, 0 ≤ f x` 必須
  (密度の非負性)。`hμ : μ = volume.withDensity (ENNReal.ofReal ∘ f)` で `μ ≪ volume` を
  暗黙に要求 (singular part があると密度表現が崩れる) — pushforward `P.map(X+√s·Z)` が
  `s > 0` で volume-AC なのは Gaussian smoothing の効果 (`s = 0` では `P.map X` が singular
  でも可)。`_ht : 0 < t` がこの AC 性を保証 (per-time wall が `t > 0` 限定なのはこのため)。
- **`Measure.rnDeriv_withDensity`** (軸4): 結論は `=ᵐ[volume]` (ae 等式)。`HasDerivAt` へ
  繋ぐとき pointwise 等式が要る箇所では `Filter.EventuallyEq` + `HasDerivAt.congr_of_eventuallyEq`
  経由が必要 (repo の整合済 pattern)。
- **`convDensityAdd_hasDerivAt`** (軸5, repo `@audit:ok`): z-微分専用。s-微分への転用時、
  `pY` の `s`-依存性 (Gaussian factor) を別 chain rule で剥がす必要 (軸2 不在部に接続)。

---

## 8. 自作が必要な要素 (優先度順)

| 優先 | 補題 | 推奨実装 | 工数感 | 落とし穴 |
|---|---|---|---|---|
| 1 | `pPath_eq_convDensityAdd` — `P.map(gaussianConvolution X Z s)` の density が `convDensityAdd p_X (gaussian density √s)` に一致 | `gaussianConvolution_law` + `map_eq_withDensity_pdf` + 独立和の density = 畳み込み | ~40-60 行 | 独立和の密度 = 畳み込みの Mathlib 直結 lemma 不在、`convDensityAdd` (Bochner ∫) との shape 整合を repo 側で立てる |
| 2 | `heatFlow_density_heat_equation` — `∂_s pPath s x = (1/2) ∂²_x pPath s x` (heat equation per-density) | 軸2 不在 → Gaussian factor の `s`-微分を chain rule + `convDensityAddDeriv` で自作 | ~80-120 行 | **本 wall の最大コスト**、Gaussian heat kernel closed-form 不在 (`"heat"` Found 0) を density-route で迂回 |
| 3 | `entropy_hasDerivAt_via_parametric` — `(d/ds) ∫ negMulLog(pPath s) ∂vol = ∫ (∂_s negMulLog ∘ pPath) ∂vol` | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (軸1) | ~30-50 行 | `bound` 関数供給 + `Measurable`/`Integrable` regularity を `IsRegularDeBruijnHypV2` 拡張 or 引数復元で pin |
| 4 | `debruijn_ibp_step` — `∫ negMulLog'(p)·∂_s p = -(1/2)∫ (∂_x p)²/p` の IBP | `integral_mul_deriv_eq_deriv_mul_of_integrable` (軸3) | ~30-50 行 | 境界項 0 (tail decay)、`tsupport` 全域 `HasDerivAt`、`Real.deriv_negMulLog` |
| 5 | `fisher_from_logDeriv` — `∫ (logDeriv p)²·p = fisherInfoOfDensity p .toReal` shape congr | `convDensityAdd_logDeriv` (軸5) + `fisherInfoOfDensity` unfold | ~20-30 行 | `ℝ≥0∞`↔`ℝ` の `.toReal`、`logDeriv` vs `(∂_x p)/p` の同定 |

**合計**: ~200-310 行 (中央値 **~250 行**)。最大コストは優先 2 (heat equation per-density、
軸2 不在の迂回)。優先 1,3,4,5 はすべて Mathlib/repo 完備 API への plumbing。

---

## 9. Mathlib 壁の列挙 (真に不在 = `@residual` 対象)

| wall slug | 内容 | loogle 確認 | shared sorry 補題 集約状態 |
|---|---|---|---|
| (軸2) Gaussian heat semigroup closed-form | heat kernel / Mehler / OU semigroup / Fokker-Planck | `"heat"` `"Mehler"` `"OrnsteinUhlenbeck"` `"FokkerPlanck"` すべて `Found 0 declarations` | per-density heat equation は **density-route 自作で迂回可** (軸5 `convDensityAdd` 経由)、真の hard wall ではなく「自作要 (long)」 |
| `wall:debruijn-integration` (既存) | per-time `debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean:245`) + 積分形 `debruijnIntegrationIdentity_holds` (同 file) | (現行 `sorry` 保持点) | **既に shared sorry 補題に集約済** (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)。本 inventory が示すのは「この壁は big choice (~250 行 plumbing) であって hard absence ではない」点 |

**重要 (honesty)**: `@residual(wall:debruijn-integration)` の classification は本 inventory の
所見では **「真の Mathlib 不在 (hard wall)」ではなく「長大だが現存 API で書ける (big)」寄り**。
唯一の真の不在は Gaussian heat-kernel closed-form だが、それは density-route で迂回でき、
かつ Gaussian case は既に `deBruijn_identity_v2_gaussian` で genuine 化済。よって一般 `X` の
per-time wall は **plan 1〜2 本で closure 可能な candidate** であり、`wall:` slug より
`plan:` slug への再分類が妥当かもしれない (auditor 判断事項、本 inventory は所見のみ提示、
コード変更しない)。同一壁が `FisherInfoV2DeBruijnBody.lean` / `FisherInfoV2DeBruijn.lean` /
`EPIL3Integration.lean` に transitive 依存で散在 (per-time wall 1 点 + 積分形 1 点) するが、
既に shared sorry 補題 2 本に集約済 (これ以上の分散なし)。

---

## 10. 撤退ラインへの距離

親 plan `epi-debruijn-integration-plan.md` の撤退ライン:

- **L-EPI2** (de Bruijn integration の genuine discharge を本 sub-plan が担当): per-time wall は
  その**下流の解析核**。本 inventory は「per-time wall の解析核が Mathlib + repo で書ける
  (~250 行)」を確認 → **L-EPI2 を緩和する方向の所見** (hard wall ではなく long plumbing)。
  **発動なし**。
- **L-FV2DB-C** (`FisherInfoV2DeBruijnBody.lean:63`、body discharge が IBP/heat eq の Mathlib
  不在に突き当たる): 本 inventory が **再評価する撤退ライン**。所見では IBP は **PRESENT**
  (軸3、`IntegralEqImproper.lean`)、heat eq のみ density-route 自作要 → **「Mathlib 不在」の
  範囲が IBP を含まない形に縮小**。L-FV2DB-C の根拠 (「IBP の bounded/unbounded 形が無い」) は
  **部分的に誤り**。**発動状態は据え置き** (heat eq per-density は依然自作要) だが、撤退理由の
  記述更新を推奨。

**新規撤退ライン提案** (sorry + `@residual`、仮説束化禁止):

- **L-PT-α** (許容): 優先 2 (heat equation per-density) が `convDensityAdd` 経由でも ~120 行を
  超え当該 session で書けない場合 → per-time wall を **Gaussian case は genuine
  (`deBruijn_identity_v2_gaussian` 既存)、一般 `X` は `sorry + @residual(wall:debruijn-integration)`
  維持** に据え置き。`IsRegularDeBruijnHypV2` に density witness の regularity field を
  bundle する撤退は **禁止** (load-bearing になりうる — regularity hyp と core の判定が
  density witness では微妙、`density_t` を「証明の核心」化しないこと)。
- **L-PT-β** (許容): 優先 1 (独立和 density = 畳み込み) が Mathlib 直結 lemma 不在で repo 側
  bridge が ~60 行超 → density 同定を別 lemma に切出し独立 `@residual` 化 (本体 wall とは別
  slug、`plan:` で)。

→ **本 inventory による既存撤退ライン発動: NO**。むしろ L-EPI2 / L-FV2DB-C の
「Mathlib 不在」根拠を **縮小** する所見 (IBP PRESENT 発見)。

---

## 11. 着手 skeleton

`InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean` (新規、wall discharge 専用) の出だし:

```lean
import Mathlib.Analysis.Calculus.ParametricIntegral       -- hasDerivAt_integral_of_dominated_loc_of_deriv_le (軸1)
import Mathlib.MeasureTheory.Integral.IntegralEqImproper   -- integral_mul_deriv_eq_deriv_mul (軸3, 無限区間 IBP)
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue -- rnDeriv_withDensity (軸4)
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog      -- Real.deriv_negMulLog (軸2 補)
import InformationTheory.Shannon.EPIConvDensity                    -- convDensityAdd_hasDerivAt (軸5, @audit:ok)
import InformationTheory.Shannon.FisherInfoV2DeBruijn              -- debruijnIdentityV2_holds (wall SoT), IsRegularDeBruijnHypV2
import InformationTheory.Shannon.DifferentialEntropy              -- differentialEntropy_eq_integral_density (軸4)

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-- per-time de Bruijn identity (一般 `X`), density-route discharge target.
Genuine 化の解析核: 軸1 parametric diff → 軸2 heat eq (density-route 自作) →
軸3 無限区間 IBP → 軸5 logDeriv→Fisher。Gaussian case は既存
`deBruijn_identity_v2_gaussian` で genuine。一般 `X` は本 file で attempt。
`@residual(wall:debruijn-integration)` (closure 試行中、~250 行見積)。 -/
theorem debruijnIdentityV2_holds_pertime
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  sorry  -- @residual(wall:debruijn-integration) — 軸1-5 plumbing 段、~250 行

end InformationTheory.Shannon
```

(本 skeleton は inventory 用。実装は `lean-implementer` の責務であり、`density_t` への
regularity bundle 判断 = parent plan の `_hX/_hZ/_hXZ` 復元議論を先に解決すること。)

---

## 12. 一覧サマリ (軸別充足度)

| 軸 | 内容 | 充足度 | 件数 |
|---|---|---|---|
| 1 | parametric integral diff | **完備** | Mathlib 5 件 PRESENT (repo `convDensityAdd_hasDerivAt` 既使用) |
| 2 | Gaussian heat kernel / semigroup | **全不在** (`Found 0`×4) + Gaussian density def のみ | 0 件 (density-route 自作で迂回) |
| 3 | 無限区間 IBP | **完備 (新規発見)** | Mathlib 7 件 PRESENT (`IntegralEqImproper.lean`) |
| 4 | rnDeriv↔withDensity / pushforward density | **完備** | Mathlib 7 件 + repo 2 件 PRESENT |
| 5 | convolution density + 微分 | **部分 (repo `@audit:ok` 資産で代替)** | repo 6 件 (3 件 `@audit:ok` sorryAx-free) |

**既存率**: ~80% (4/5 軸が Mathlib/repo 完備、軸2 のみ自作だが density-route で迂回可)。
**自作必要**: 5 件 (~250 行)、すべて plumbing or density-route 自作 (新 hard wall なし)。
**撤退ライン発動**: NO (むしろ L-EPI2/L-FV2DB-C の「Mathlib 不在」根拠を縮小)。
