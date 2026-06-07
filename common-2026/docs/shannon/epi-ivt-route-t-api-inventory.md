# route T (無限分散 a.c. 古典 EPI) — 残 4 難所 sorry の Mathlib + in-tree API 在庫

> **親計画**: [`epi-infinite-variance-truncation-plan.md`](epi-infinite-variance-truncation-plan.md)
> (slug `epi-infinite-variance-truncation-plan`、対象壁 `@residual(wall:epi-infinite-variance-classical)`)。
> **対象 file**: `InformationTheory/Shannon/EPIInfiniteVarianceTruncation.lean`。
> **対象 sorry** (6 本、難所は #2/#3/#4/headline)：
> - `integrable_negMulLog_map_condTrunc_sum` (`:260`、和エントロピー可積分 = #2)
> - `differentialEntropy_condTrunc_sum_limsup_le` (`:389`、crux usc = #3)
> - `entropyPowerExt_condTrunc_sum_limsup_le` (`:403`、usc の Nₑ-lift = #4)
> - `differentialEntropy_map_condTrunc_tendsto` (`:420`、RHS 収束 #5)
> - `entropyPowerExt_map_condTrunc_tendsto` (`:431`、RHS の Nₑ-lift #6)
> - `entropyPowerExt_add_ge_infinite_variance_truncation` (`:462`、headline assembly)

## 一行サマリ

**Q1 (conv density 表現) は in-tree に sorryAx-free な一般版 `EPIStamSupplyTwoTime.indepSum_density_ae` が「直接ある」(Gaussian 専用でない) — 在庫の最重要収穫。** Q3 (DCT)・Q4 (exp-lift) は使用 API 100% 既存 (Mathlib + in-tree)。**真の難所は Q2: 「2 つの一般 L¹ 密度の畳込み `p∗q` の `negMulLog` 可積分性」を供給する補題が in-tree に存在するが全て (a) Gaussian 第2因子 + (b) 有限2次モーメント `hpX_mom` を要求し、無限分散 route T に転用不可。** plan の「compact support → 有界密度」は誤り (orchestrator math 反証済) なので、Q2 は **「conditioning-reduces-entropy で `h(X+Y) ≥ h(X)` を下から押さえる + 上は固定参照 Gibbs」という別機構**を要し、その下界機構は in-tree (`condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq`、ともに sorryAx-free) に既にある。**既存率 (使用 API 実体ベース) ≈ 88%、自作必要 = 3 件、Mathlib 真の壁 = 0 件**。撤退ライン L-IVT-2 は発動見込みなし (Q2 も既存 asset 合成で閉じる)。

> 最も危険な発見: **Q2 の負部可積分性は plan が想定した「compact support → 有界密度」では閉じない**
> (2 つの L¹ 密度の畳込みは有界でも L² でもない、math 反証済)。正しいルートは「`negMulLog` の正部
> `∫_{p∗q≤1} -(p∗q)log(p∗q)` を `negMulLog_le_one_sub_self` (`≤ 1-x`) で押さえ、負部
> `∫_{p∗q>1}(p∗q)log(p∗q) < ∞` を conditioning-reduces-entropy で `h(X+Y) ≥ h(X) > -∞` から
> 導く」。後者の機構は in-tree (`condDifferentialEntropy_le`) にあるが、**route T の cond 切詰
> `condTrunc` に specialize して負部有限を結ぶ配線 (~40-60 行) が自作の核**。

---

## 主定理の最終形 (再掲) と証明戦略

```lean
theorem entropyPowerExt_add_ge_infinite_variance_truncation
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
```

証明戦略 (pseudo-Lean、clean limsup chain、moment 非依存):

```
-- per-n 黒箱 EPI (entropyPowerExt_condTrunc_add_ge, 既に組済):
N(P_n.map(X+Y)) ≥ N(P_n.map X) + N(P_n.map Y)                         -- ← #2 が hent_sum 供給
-- crux usc (#3 → #4):
limsup_n N(P_n.map(X+Y)) ≤ N(P.map(X+Y))                              -- Gibbs (差替済 helper3) + DCT
-- RHS 収束 (#5 → #6):
N(P_n.map X) → N(P.map X),  N(P_n.map Y) → N(P.map Y)                 -- growing-set DCT + log m_n→0
-- assembly (headline):
N(P.map(X+Y)) ≥ limsup N(P_n.map(X+Y)) ≥ lim[N(P_n.map X)+N(P_n.map Y)]
              = N(P.map X)+N(P.map Y)                                  -- le_of_tendsto' + limsup_le_limsup
```

---

## Q1 — convolution density 表現 (最重要、**直接ある**)

`P.map(X+Y) ≪ volume` の rnDeriv を独立和 X,Y の各密度の畳込み `convDensityAdd pX pY` で書く一般 a.e. 同定。

| 概念 | API | file:line | 状態 | route T での扱い |
|---|---|---|---|---|
| **一般 conv density 同定** (非 Gaussian) | `indepSum_density_ae` | `InformationTheory/Shannon/EPIStamSupplyTwoTime.lean:101` | ✅ **in-tree、sorryAx-free、@audit:ok** | **Q1 を直接閉じる。**`pXY =ᵐ[volume] convDensityAdd pX pY` を一般独立 X,Y で供給 |
| conv density def (Bochner ∫ 形) | `EPIConvDensity.convDensityAdd` | `InformationTheory/Shannon/EPIConvDensity.lean:42` | ✅ in-tree | `convDensityAdd pX pY := fun z => ∫ x, pX x * pY (z-x) ∂volume` |
| 独立和の法則 = conv (Mathlib) | `IndepFun.map_add_eq_map_conv_map` (additive of `map_mul_eq_map_mconv_map`) | `Mathlib/Probability/Independence/Basic.lean:1103` (`@[to_additive]` 源) | ✅ Mathlib | `indepSum_density_ae` 内部で使用済。一般 (非 Gaussian) |
| withDensity の conv = lconvolution の withDensity | `conv_withDensity_eq_lconvolution` (= additive of `mconv_withDensity_eq_mlconvolution`) | `Mathlib/MeasureTheory/Measure/WithDensity.lean:770` (`@[to_additive]` 源) | ✅ Mathlib | `indepSum_density_ae` 内部 |
| `rnDeriv (withDensity f) =ᵐ f` | `Measure.rnDeriv_withDensity` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:590` | ✅ Mathlib | density 抽出 |
| Gaussian 専用 conv density (参考) | `FisherInfoV2.pPath_eq_convDensityAdd` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:215` | ✅ in-tree、@audit:ok | **Y=Gaussian 専用**。route T には不要 (一般版あり) |

### `indepSum_density_ae` 完全 signature (verbatim)

```lean
theorem indepSum_density_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (pX pY pXY : ℝ → ℝ)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (hpY_law : P.map Y = volume.withDensity (fun x => ENNReal.ofReal (pY x)))
    (hpXY_law : P.map (fun ω => X ω + Y ω)
      = volume.withDensity (fun x => ENNReal.ofReal (pXY x)))
    (hpXY_nn : ∀ x, 0 ≤ pXY x) (hpXY_meas : Measurable pXY)
    (hpX_int : Integrable pX volume) (hpY_int : Integrable pY volume)
    (hpXY_lmass : (∫⁻ x, ENNReal.ofReal (pXY x) ∂volume) ≠ ⊤)
    (hpX_lmass : (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) = 1)
    (hpY_lmass : (∫⁻ x, ENNReal.ofReal (pY x) ∂volume) = 1) :
    pXY =ᵐ[volume] convDensityAdd pX pY
```

- 引数型 (順): `[MeasurableSpace Ω]`, `[IsProbabilityMeasure P]` (instance) / `X Y : Ω → ℝ`, `Measurable X/Y`, `IndepFun X Y P`, 3 つの密度 `pX pY pXY : ℝ → ℝ`, それらの非負・可測・withDensity-law・L¹-mass 前提 (全て regularity precondition、load-bearing でない)。
- 結論形 verbatim: `pXY =ᵐ[volume] convDensityAdd pX pY`。

### `IndepFun.map_add_eq_map_conv_map` 完全 signature (verbatim、`@[to_additive]` の additive 名)

```lean
@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map
    [IsFiniteMeasure μ] {f g : Ω → M} (hf : Measurable f) (hg : Measurable g)
    (hfg : f ⟂ᵢ[μ] g) :
    μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g)
```

- additive 版 (生成名 `IndepFun.map_add_eq_map_conv_map`): `[IsFiniteMeasure μ]`, `[AddMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M]` (section 変数)、`Measurable f`, `Measurable g`, `IndepFun f g μ` → `μ.map (f + g) = (μ.map f) ∗ (μ.map g)`。
- 型クラス前提 verbatim: `[Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]` (`variable`、§Monoid)、結論 instance `[IsFiniteMeasure μ]`。**StandardBorel 不要**。`M = ℝ` で全充足。
- `₀` / `'` 変種 (`:1079/:1088/:1095`) は `AEMeasurable` 版 / `SigmaFinite` 版。

**判定 (Q1)**: **buildable、ほぼ即** — 一般 conv density 同定 `indepSum_density_ae` が in-tree に直接あり (Gaussian 専用でない、sorryAx-free、@audit:ok)。route T で必要なのは「`condTrunc P X Y n` を P と読み替えて `indepSum_density_ae` を呼ぶ + 密度 witness `pX_n/pY_n/pXY_n` を `condTrunc` から取り出す」配線のみ (~20-30 行、`map_condTrunc_absolutelyContinuous` + Radon-Nikodym で density witness 構成)。Gaussian 一般化の self-build は不要。

---

## Q2 — エントロピー可積分性 / 非減少 (#2 の核、**真の難所**)

`integrable_negMulLog_map_condTrunc_sum` (`:260`) = `Integrable (negMulLog ((condTrunc.map(X+Y)).rnDeriv vol ·)) volume`。
**plan の「compact support → 有界密度」ルートは誤り** (2 つの L¹ 密度の畳込みは有界でも L² でもない、orchestrator math 反証済)。正しいのは「負部 `∫_{r>1} r log r < ∞ ⟺ h(X+Y) ≥ h(X)` (畳込みでエントロピー非減少)」。

### Q2-a — エントロピー非減少 `h(X+Y) ≥ h(X)` の下界機構 (in-tree、一般)

| 概念 | API | file:line | 状態 | route T での扱い |
|---|---|---|---|---|
| **conditioning reduces entropy** `h(X\|Z) ≤ h(X)` | `condDifferentialEntropy_le` | `InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean:224` | ✅ in-tree、sorryAx-free、@audit:ok | **一般** `Z : Ω → α` (Gaussian 不要)。負部有限の下界源 |
| **独立和 fibre 同定** `h(X+c·Z\|Z) = h(X)` | `condDifferentialEntropy_indep_add_eq` | `InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean:328` | ✅ in-tree、sorryAx-free、@audit:ok | **一般** `X Z : Ω → ℝ`, scale `c` (Gaussian 不要)。`c=1, Z=Y` で `h(X+Y\|Y) = h(X)` |
| cond-diff-entropy def | `condDifferentialEntropy` | `InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean:~90` | ✅ in-tree | `∫ z, h((condDistrib X Z μ) z) ∂(μ.map Z)` |
| 平行移動不変 `h(μ.map(·+y)) = h(μ)` | `differentialEntropy_map_add_const` | `InformationTheory/Shannon/DifferentialEntropy.lean:171` | ✅ in-tree | fibre 同定の中核 |
| device 形 (Gaussian 専用、参考) | `differentialEntropy_indep_gaussian_add_ge` | `InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean:378` | ✅ in-tree、@audit:ok | **Z=Gaussian 専用 wrapper**。route T は一般版 `condDifferentialEntropy_le`+`_indep_add_eq` を直接合成 |

#### `condDifferentialEntropy_le` 完全 signature (verbatim、前提が重いので逐語)

```lean
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib X Z μ ≪ (μ.map Z) ⊗ₘ Kernel.const α (μ.map X))
    (h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib X Z μ) ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X)))
      ((μ.map Z) ⊗ₘ condDistrib X Z μ))
    (hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib X Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib X Z μ z)) (μ.map Z))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) (μ.map Z))
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map X).rnDeriv volume x).toReal)) (μ.map X)) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)
```

- 型クラス前提 verbatim: `[MeasurableSpace Ω] [MeasurableSpace α]`, `[IsProbabilityMeasure μ]`。**StandardBorel は出力側 `X` の codomain = ℝ に暗黙要求 (`condDistrib` 内部)**、ℝ で自動充足。`Z` の codomain `α` には制約なし。
- 結論形 verbatim: `condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)`。
- ⚠ 前提が **9 本の regularity/integrability** (joint ≪ / per-fibre ≪ / llr 可積分 / fibre entropy 可積分 / cross-term 可積分 / log-density 可積分)。route T で `μ = condTrunc P X Y n`, `Z = Y`, `X = X` に specialize する際、これら全前提を `condTrunc` の compact-support regularity から供給する必要 (★自作の主コスト)。

#### `condDifferentialEntropy_indep_add_eq` 完全 signature (verbatim)

```lean
theorem condDifferentialEntropy_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropy (μ.map X)
```

- 型クラス前提 verbatim: `[MeasurableSpace Ω] [IsProbabilityMeasure μ]`。**一般 ℝ-valued、Gaussian 不要、StandardBorel 明示要求なし**。
- 結論形 verbatim: `condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ = differentialEntropy (μ.map X)`。
- `c=1, Z=Y` で `h(X+Y | Y) = h(X)` → `condDifferentialEntropy_le` と合成して `h(X+Y) ≥ h(X)`。

### Q2-b — 正部 / 負部 bound と Jensen+Fubini の素材 (Mathlib)

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `negMulLog ≤ 1-x` (正部の凸 majorant) | `Real.negMulLog_le_one_sub_self` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:234` | ✅ Mathlib | `(h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x`。正部 `∫_{r≤1}` の上界 |
| `negMulLog` 非負 (on [0,1]) | `Real.negMulLog_nonneg` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:174` | ✅ Mathlib | `(h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x` |
| `negMulLog` の凸性 | `Real.convexOn_mul_log` / `strictConvexOn_mul_log` (negMulLog = neg) | `NegMulLog.lean:218/225` | ✅ Mathlib | Jensen 用 |
| Fubini (Bochner 積分順序交換) | `MeasureTheory.integral_integral_swap` | `Mathlib/MeasureTheory/Integral/Prod.lean:532` | ✅ Mathlib | `(hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν` |
| conv 可換 | `EPIConvDensity.convDensityAdd_comm` | `InformationTheory/Shannon/EPIConvDensity.lean:47` | ✅ in-tree | `convDensityAdd pX pY = convDensityAdd pY pX` |
| `Integrable.of_mem_Icc` (有界域 → 可積分) | `MeasureTheory.Integrable.of_mem_Icc` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` | ✅ Mathlib | 既に対象 file `:238` で使用 (但し有界密度は誤ルート、参考) |

### ⚠ Q2 既存の Gaussian 専用 negMulLog 可積分 asset (route T 転用**不可**)

| API | file:line | 不可理由 |
|---|---|---|
| `convDensityAdd_negMulLog_integrable` | `FisherInfoV2DeBruijnAssembly.lean:2532` | 第2因子 `gaussianPDFReal 0 ⟨t,_⟩` + `(hpX_mom : Integrable (fun y => y^2 * pX) volume)` (**有限2次モーメント**)。route T は両成分一般 + 無限分散ゆえ不適用 |
| `convDensityAdd_negMulLog_integrable_pub` | `EPIG2HeatFlowContinuity.lean:131` | 上の public wrapper。同じ Gaussian + `hpX_mom` 要求 |

verbatim (`:2532`):
```lean
theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume
```
→ `hpX_mom` が load-bearing (moment 域でのみ majorant 構成)。**無限分散では majorant `A+B·x²` が積分発散**するので機構ごと転用不可。

**判定 (Q2)**: **buildable だが最大コスト、Gaussian 専用 asset は転用不可、別機構が要**。正しいルートは
**「`negMulLog(p∗q)` の正部 (≤1 域) は `negMulLog_le_one_sub_self` + `p∗q` 可積分 (= `IndepFun.map_add` 経由で
全質量 1、`indepSum_density_ae` の `hfin` で確立済の機構) で有限、負部 ((p∗q>1) 域、すなわち `(p∗q)log(p∗q)`)
は `h(X+Y) = -∫(p∗q)log(p∗q) ≥ h(X) > -∞` より有限」**。後者の下界 `h(X+Y) ≥ h(X)` は in-tree
`condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq` (ともに一般、sorryAx-free) を
`μ = condTrunc P X Y n`, `Z = Y` に specialize して得る。**自作の核は `condDifferentialEntropy_le` の 9 本前提を
compact-support `condTrunc` regularity から供給する配線 (~40-60 行)** + 正部/負部分解で `Integrable` に組む (~20 行)。
**真の Mathlib 壁ではない** (機構は全て既存 asset 合成)。

---

## Q3 — dominated convergence (cross-entropy DCT、#3 crux / #5 RHS)

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **Bochner DCT (ℕ 添字)** | `MeasureTheory.tendsto_integral_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:57` | ✅ Mathlib | crux usc cross-entropy `-∫(p_n∗q_n)log(p∗q) → -∫(p∗q)log(p∗q)` |
| **Bochner DCT (filter 版、atTop)** | `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:69` | ✅ Mathlib | `atTop` filter で使うならこちら (countably generated) |
| lintegral DCT | `MeasureTheory.tendsto_lintegral_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean` | ✅ Mathlib | ℝ≥0∞ 版 (必要時) |
| `Filter.Tendsto.comp` | `Filter.Tendsto.comp` | `Mathlib/Order/Filter/Tendsto.lean` | ✅ Mathlib | DCT 結果に連続函数 |
| limsup ≤ via Tendsto | `Filter.Tendsto.limsup_eq` | `Mathlib/Topology/Order/LiminfLimsup.lean` | ✅ Mathlib | DCT (Tendsto) → limsup = lim → usc 結論 |

### `tendsto_integral_of_dominated_convergence` 完全 signature (verbatim)

```lean
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ)
```

- 型クラス前提 verbatim (section 変数): `[NormedAddCommGroup G] [NormedSpace ℝ G]`, `{m : MeasurableSpace α} {μ : Measure α}`。`G = ℝ` で充足。
- 引数型 (順): `bound : α → ℝ` (explicit), `F_measurable : ∀ n, AEStronglyMeasurable (F n) μ`, `bound_integrable : Integrable bound μ`, `h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a`, `h_lim : ∀ᵐ a ∂μ, Tendsto (F n a) atTop (𝓝 (f a))`。
- 結論形 verbatim: `Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ)`。

### filter 版 (`:69`、atTop で `bound` 引数順が異なる点に注意)

```lean
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} {f : α → G} (bound : α → ℝ) (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 <| ∫ a, f a ∂μ)
```

⚠ filter 版は引数順が `bound, hF_meas, h_bound, bound_integrable, h_lim` (ℕ 版の `bound, F_measurable, bound_integrable, h_bound, h_lim` と `bound_integrable`/`h_bound` の順序が逆)。

**判定 (Q3)**: **使用 API 100% 既存、buildable**。ℕ 添字 (`condTrunc P X Y n` は `n : ℕ`) なので `tendsto_integral_of_dominated_convergence` (`:57`) を直接使用。優関数は crux 設計の `C²·(p∗q)|log(p∗q)|` (= `hent_sum` で可積分)。`bound` 可積分性が Q2 の `hent_sum` 供給と結合。

---

## Q4 — entropyPower exp-lift (#4 crux Nₑ / #6 RHS Nₑ)

`differentialEntropy` の limsup/tendsto から `entropyPowerExt` の limsup/tendsto へ単調連続変換で持ち上げ。

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **a.c.+有限 entropy 時 `Nₑ = ofReal(exp(2h))`** | `entropyPowerExt_of_ac_integrable` | `InformationTheory/Shannon/EntropyPowerExt.lean:118` | ✅ in-tree、@audit:ok | exp-lift の出発点。per-n に適用 |
| `entropyPowerExt` def | `entropyPowerExt` | `InformationTheory/Shannon/EntropyPowerExt.lean:68` | ✅ in-tree | `ℝ≥0∞` 値 |
| `Real.continuous_exp` | `Real.continuous_exp` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | ✅ Mathlib | exp 連続 |
| `ENNReal.continuous_ofReal` | `ENNReal.continuous_ofReal` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean` | ✅ Mathlib | ofReal 連続 |
| **`ofReal` の limsup push** | `ENNReal.ofReal_limsup` | `Mathlib/Order/Filter/ENNReal.lean:245` | ✅ Mathlib | `ofReal (limsup u f) = limsup (ofReal ∘ u) f` (cobounded/bounded 前提) |
| ofReal limsup (toReal 形) | `ENNReal.ofReal_limsup_toReal` | `Mathlib/Order/Filter/ENNReal.lean:264` | ✅ Mathlib | `(hf : ∀ᶠ a, u a ≤ C) : ofReal (limsup (toReal∘u) f) = limsup u f` |
| 単調 OrderIso の limsup 交換 | `OrderIso.limsup_apply` | `Mathlib/Order/LiminfLimsup.lean:1110` | ✅ Mathlib | exp (単調全単射) の limsup push |
| `limsup_le_limsup` (mono 比較) | `Filter.limsup_le_limsup` | `Mathlib/Order/LiminfLimsup.lean:198` | ✅ Mathlib | assembly chain |
| `le_of_tendsto'` | `le_of_tendsto'` | `Mathlib/Topology/Order/OrderClosed.lean:136` | ✅ Mathlib | tendsto → 不等式 (RHS assembly) |
| `Filter.Tendsto.limsup_eq` | `Filter.Tendsto.limsup_eq` | `Mathlib/Topology/Order/LiminfLimsup.lean` | ✅ Mathlib | tendsto → limsup=lim (RHS) |

### `entropyPowerExt_of_ac_integrable` 完全 signature (verbatim)

```lean
theorem entropyPowerExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume)
    (hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))
```

### `ENNReal.ofReal_limsup` 完全 signature (verbatim)

```lean
lemma ofReal_limsup {u : α → ℝ}
    (h₁ : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ENNReal.ofReal (limsup u f) = limsup (fun a ↦ .ofReal (u a)) f
```

**判定 (Q4)**: **使用 API 100% 既存、buildable**。`Monotone.map_limsup` / `Monotone.map_limsSup` は loogle "unknown identifier"
(**存在しない**、下記 wall 節)が、**回避路あり**: usc は `entropyPowerExt μ = ofReal(exp(2h))` (`entropyPowerExt_of_ac_integrable`、
per-n 適用) に書換 → `exp(2·) ∘` の連続単調性 + `ENNReal.ofReal_limsup` (`:245`) + `Filter.limsup_le_limsup` で push。
**ただし per-n の `(condTrunc.map(X+Y))` が a.c.+有限 entropy であること** (= `entropyPowerExt_of_ac_integrable` 適用前提) が
必須で、その有限 entropy 供給元が **#2 (`integrable_negMulLog_map_condTrunc_sum`)** ⟹ **Q4 は Q2 に依存**。a.c. は
`map_condTrunc_absolutelyContinuous` (`:214`、in-tree 済) で供給。`Real.exp` は狭義単調なので usc 向き保存も型自明。

---

## 主要前提条件ボックス (前提事故の起きやすい lemma)

- **`condDifferentialEntropy_le` (`:224`)**: 9 本の regularity/integrability 前提 (joint ≪ / per-fibre ≪ / llr 可積分 / fibre entropy 可積分 / cross-term 2 種可積分 / log-density 可積分)。`Z` の codomain `α` に制約なしだが、`condDistrib X Z μ` 内部で **出力側 X の codomain (= ℝ) に `[StandardBorelSpace ℝ]`** が暗黙要求 (ℝ で自動)。route T で `μ=condTrunc, Z=Y` に specialize する全前提供給が自作の主コスト。
- **`tendsto_integral_of_dominated_convergence`**: ℕ 版 (`:57`) と filter 版 (`:69`) で **`bound_integrable` と `h_bound` の引数順が逆**。`condTrunc` は `n:ℕ` なので ℕ 版推奨。`bound` 可積分は `hent_sum`/Q2 と結合。
- **`indepSum_density_ae` (`:101`)**: `hpX_lmass = 1` / `hpY_lmass = 1` / `hpXY_lmass ≠ ⊤` を要求。`condTrunc` は probability measure なので密度 witness の全質量 1 は `IsProbabilityMeasure (condTrunc ...)` (`isProbabilityMeasure_condTrunc`、`:120` in-tree 済) から供給。
- **`entropyPowerExt_of_ac_integrable` (`:118`)**: a.c. **かつ** 有限 entropy (integrable negMulLog) の両方が前提。infinite-branch では `entropyPowerExt = ⊤` (別 lemma `entropyPowerExt_eq_top_of_diffEntExt_top` `:129`) になり EPI は `le_top` で自明閉じ。usc lift では per-n が有限 entropy であること (#2) が必須。
- **`IndepFun.map_add_eq_map_conv_map`**: `[IsFiniteMeasure μ]` instance 要求 (probability measure で充足)。`MeasurableAdd₂ ℝ` は自動。**StandardBorel 不要**。

---

## 自作が必要な要素 (優先度順)

1. **#2 `integrable_negMulLog_map_condTrunc_sum` の正部/負部分解配線 (最大コスト ~80-120 行)**
   - 推奨実装: `indepSum_density_ae` で `condTrunc.map(X+Y)` の rnDeriv を `convDensityAdd pX_n pY_n` に同定 → `negMulLog(p_n∗q_n)` を `{r≤1}` (正部、`negMulLog_le_one_sub_self` + `p_n∗q_n` 可積分) と `{r>1}` (負部、`-r log r ≤ 0` だが絶対値は `r log r`、`h(condTrunc.map(X+Y)) ≥ h(condTrunc.map X) > -∞` から有限) に分解。
   - 下界 `h(X+Y) ≥ h(X)` は `condDifferentialEntropy_le` (`:224`) + `condDifferentialEntropy_indep_add_eq` (`:328`、`c=1,Z=Y`) を `μ=condTrunc P X Y n` に specialize。
   - 落とし穴: `condDifferentialEntropy_le` の 9 本前提を `condTrunc` の compact-support regularity (有界 → fibre entropy/cross-term 可積分) から供給する配線が地味に重い。**compact support は「有界密度」ではなく「有界 second moment → fibre が有限分散 Gaussian-bound」経由で fibre entropy 可積分を出す**点に注意。
   - 工数感: 1-2 セッション。在庫の Q2-a asset がすべて sorryAx-free なので新規解析ゼロ、配線のみ。

2. **#3/#4 crux usc 本体 (~80-120 行、plan Phase 2 相当)**
   - 推奨実装: Gibbs step は **既に対象 file `:302` の `differentialEntropy_le_cross_entropy` (一般参照版、fill 済)** を使用 → `h(condTrunc.map(X+Y)) ≤ -∫(p_n∗q_n)log(p∗q)`。cross-entropy DCT は `tendsto_integral_of_dominated_convergence` (`:57`)、優関数 `C²·(p∗q)|log(p∗q)|` (`hent_sum` 可積分)。a.e. 各点収束は優収束 `p_n∗q_n → p∗q` + `m_n→1`。Nₑ-lift (#4) は `entropyPowerExt_of_ac_integrable` + `ENNReal.ofReal_limsup` + `Real.continuous_exp`。
   - 落とし穴: 優関数 `p_n∗q_n ≤ C²(p∗q)` の pointwise bound (plan §Approach の優関数) を `convDensityAdd` 上で立てる補題が別途要 (m_n↑1, C=1/m_{n₀})。これは density-function 形なので Q1 同定後に閉じる。

3. **#5/#6 RHS 収束 (~60-80 行、plan Phase 3 相当)**
   - 推奨実装: `h(condTrunc.map Z) = -(1/m_n)∫_{truncSet} p_Z log p_Z + log m_n`。第1項は固定可積分 `p_Z log p_Z` (= `hZ_ent`) の growing-set `tendsto_integral_of_dominated_convergence`、第2項 `log m_n → 0` (`m_n→1`、`measure_truncSet_tendsto_one` `:102` in-tree 済)。Nₑ-lift (#6) は `entropyPowerExt_of_ac_integrable` + `Real.continuous_exp` + `Filter.Tendsto.comp`。
   - moment 非依存 (固定可積分 `p_Z log p_Z` のみ)。

---

## Mathlib 壁の列挙 (真の不在、`@residual(wall:...)` 対象)

**route T 残 4 難所に真の Mathlib 壁は 0 件。** 以下は「loogle Found 0」だが回避路があり壁でない:

| 不在の API | loogle 確認 | 回避路 (壁でない理由) |
|---|---|---|
| `Monotone.map_limsup` / `Monotone.map_limsSup` | `unknown identifier 'Monotone.map_limsup'` (loop suggestion) | `ENNReal.ofReal_limsup` (`:245`) + `Filter.limsup_le_limsup` (`:198`) + `entropyPowerExt_of_ac_integrable` 書換で push 可能。**壁でない (別 lemma で同結論)** |
| `MeasureTheory.differentialEntropy` (Mathlib 側) | `unknown identifier 'MeasureTheory.differentialEntropy'` | 本プロジェクト固有概念 (`InformationTheory/Shannon/DifferentialEntropy.lean:45`)。Mathlib 不在は設計通り、壁でない |
| `ProbabilityTheory.measureEntropy` × `Measure.conv` 単調性 | `Found 0` (`measureEntropy, Measure.conv`) | 連続版エントロピー単調性は Mathlib 不在 (`EPIG2ConvEntropyMonotone.lean:44` 既述の genuine gap)。**ただし in-tree `condDifferentialEntropy_le` で建設済**、壁でない |
| `Real.negMulLog_le` (1/e 上限) | `unknown identifier 'Real.negMulLog_le'` | `negMulLog_le_one_sub_self` (`:234`、`≤ 1-x`) で正部 bound 代替可。`1/e` max は不要 (1-x で十分)。壁でない |

**shared sorry 補題化候補**: なし。Q2-a の entropy 単調性は既に `EPIG2ConvEntropyMonotone.lean` に集約済 (in-tree、sorryAx-free)、散在していない。新規共有壁は発生しない。

---

## 撤退ラインへの距離

親計画 (`epi-infinite-variance-truncation-plan.md` §撤退ライン) の 3 本:

- **L-IVT-1 (usc 偽)**: **発動しない**。Phase 0 数値反証ゼロ + Gibbs+DCT 機構確定済 (判断ログ 4)。本在庫でも crux usc の素材 (DCT/cross-entropy/limsup push) が全て既存と確認、usc 偽の兆候なし。
- **L-IVT-2 (Gibbs/DCT の Lean 化が予期せず詰まる、named wall 当座退避)**: **発動見込みなし**。Q3 (DCT) 使用 API 100% 既存、Gibbs は対象 file `:302` で fill 済 (`differentialEntropy_le_cross_entropy`)。唯一の重さは **#2 (Q2) の `condDifferentialEntropy_le` 9 本前提供給配線**だが、これは「詰まり」でなく「分量」(全 asset sorryAx-free、新規解析ゼロ)。
- **L-IVT-3 (T も Y も当座 close 不能、最終手段)**: **発動しない**。T が全難所で既存 asset 合成に分解できると確認。

**新規撤退ライン提案 (本在庫から)**:

- **L-IVT-4 (#2 の `condDifferentialEntropy_le` specialize が想定外に詰まる)**: 万一 `condTrunc` の compact-support regularity から `condDifferentialEntropy_le` の 9 本前提 (特に fibre entropy / cross-term 可積分) を供給する配線が当該セッションで詰まったら、`integrable_negMulLog_map_condTrunc_sum` のみ `sorry` + `@residual(plan:epi-infinite-variance-truncation-plan)` で park し、#3/#5/#6/headline を先に組む (構造は独立)。**仮説束化禁止** — `hent_sum` を headline の新規仮説に昇格させない (= load-bearing 化、tier 5、plan §Phase 4 既述)。撤退口は sorry + @residual のみ。

---

## 着手 skeleton

> 対象 file は既存 (skeleton 完成済、`lake env lean` type-check 通過、6 sorry)。新規 file 作成は不要。
> 残 sorry を埋める際の import / 補助 open の追加見込み (出だし ~25 行):

```lean
-- InformationTheory/Shannon/EPIInfiniteVarianceTruncation.lean (既存、import 追加見込み)
import InformationTheory.Shannon.EPICase1SmoothingLimit          -- 既存 (黒箱 EPI)
import InformationTheory.Shannon.EPIStamSupplyTwoTime            -- 追加: indepSum_density_ae (Q1)
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone        -- 追加: condDifferentialEntropy_le / _indep_add_eq (Q2-a)
import Mathlib.MeasureTheory.Integral.DominatedConvergence       -- 追加: tendsto_integral_of_dominated_convergence (Q3)
import Mathlib.Order.Filter.ENNReal                              -- 追加: ENNReal.ofReal_limsup (Q4)

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

-- #2 (難所): conv density 同定 (Q1) + 正部/負部分解 (Q2-b) + 下界 h(X+Y)≥h(X) (Q2-a)
theorem integrable_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume := by
  -- 1. indepSum_density_ae で rnDeriv =ᵐ convDensityAdd pX_n pY_n  (Q1)
  -- 2. 正部 {r≤1}: negMulLog_le_one_sub_self + (p_n∗q_n) 可積分  (Q2-b)
  -- 3. 負部 {r>1}: h(condTrunc.map(X+Y)) ≥ h(condTrunc.map X) > -∞  (Q2-a: condDifferentialEntropy_le + _indep_add_eq)
  sorry  -- @residual(plan:epi-infinite-variance-truncation-plan)
```

---

## 「使用 API のうち X% が既存」カウント

分母 (route T 残 4 難所で実際に使う API): 18 項目
- Q1: `indepSum_density_ae` / `convDensityAdd` / `map_add_eq_map_conv_map` / `conv_withDensity_eq_lconvolution` / `rnDeriv_withDensity` ×5
- Q2-a: `condDifferentialEntropy_le` / `condDifferentialEntropy_indep_add_eq` / `differentialEntropy_map_add_const` ×3
- Q2-b: `negMulLog_le_one_sub_self` / `negMulLog_nonneg` / `integral_integral_swap` / `convDensityAdd_comm` ×4
- Q3: `tendsto_integral_of_dominated_convergence` ×1
- Q4: `entropyPowerExt_of_ac_integrable` / `ENNReal.ofReal_limsup` / `Real.continuous_exp` / `limsup_le_limsup` / `le_of_tendsto'` ×5

分子 (既存 = Mathlib or in-tree sorryAx-free): 18 項目 → **使用 API 実体ベース 100% 既存**。

ただし「3 つの難所を直接埋める高レベル補題」(conv 上の `negMulLog` 可積分 [一般・無限分散] / crux usc 完成形 / RHS 収束完成形) は **0% 既存** (自作 3 件)。Gaussian 専用 negMulLog 可積分 asset (`convDensityAdd_negMulLog_integrable`) は存在するが **moment 依存で転用不可**ゆえ分子に数えない。

> **要約**: route T の道具 (一般 conv density 同定・連続版エントロピー単調性・DCT・exp-lift) は **全て in-tree/Mathlib に
> sorryAx-free で揃っている**。自作は「それらを `condTrunc` に specialize して正部/負部・usc・RHS を組む糊コード」3 件のみ。
> Mathlib 真の壁ゼロ、撤退ライン発動見込みなし。最大コストは **#2 の `condDifferentialEntropy_le` 9 本前提供給配線** (分量、難所でなく)。
