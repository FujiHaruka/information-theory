# EPI 有限分散 closure — `hent_sum` のための Mathlib + in-tree 在庫調査

> 対象 sorry: `InformationTheory/Shannon/EPIUncondDispatch.lean:72-94`（`entropyPowerExt_add_ge_finite_ac` の有限分散枝、`@residual(plan:epi-finitevar-smoothing-limit-plan)`）。
> 親計画: `docs/shannon/epi-finitevar-smoothing-limit-plan.md`。
> 本ファイルは **在庫調査のみ**（実装・計画起草はしない）。
> last-verified commit: `7bac457`（調査時 HEAD）。

## 一行サマリ

**`hent_sum`（一般独立和 X+Y の有限微分エントロピー = negMulLog density 可積分性）を閉じる API のうち、組立部品（密度表現・Young・上界 maxent・negMulLog 上界）は分子ベースで約 60% が既存。だが「一般 `pX ∗ pY` の negMulLog **負部**可積分性を出す決定的補題」が in-tree にも Mathlib にも無く（in-tree 資産は全て Gaussian 平滑化固有、Mathlib に L^p Young 不在）、自作必要は 2〜3 件。** これは genuine な実解析 gap（Mathlib 壁ではない、closeable だが工数大）。撤退ライン判定: **発動懸念あり（後述）**。最危険な発見は「上界 `differentialEntropy_le_gaussian_of_variance_le` は Bochner 積分**値**の上界であって integrand の **integrability** を produce しない」点。

---

## 主定理の最終形（再掲）

`EPIUncondDispatch.lean:72-94` の `have hent_sum`（文脈の仮説は調査依頼の通り）:

```lean
-- 文脈: X Y : Ω → ℝ, P : Measure Ω [IsProbabilityMeasure P]
--   hX : Measurable X, hY : Measurable Y, hXY : IndepFun X Y P
--   hX_ac : (P.map X) ≪ volume, hY_ac : (P.map Y) ≪ volume
--   h_mom_X : Integrable (fun ω => (X ω)^2) P, h_mom_Y : Integrable (fun ω => (Y ω)^2) P
--   hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume
--   hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume
hent_sum : Integrable (fun x => Real.negMulLog
    (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume
```

教科書的証明戦略（pseudo-Lean）:

```text
1. p_W := (P.map (X+Y)).rnDeriv volume = convDensityAdd pX pY   -- 一般和の密度 = 畳み込み
   （IndepFun.map_add_eq_map_conv_map + withDensity_rnDeriv_eq + conv_withDensity_eq_lconvolution）
2. negMulLog p_W = posPart − negPart を分けて両方 integrable を示す:
   2a. 正部 (p_W ≤ 1 領域、p log(1/p) ≥ 0): negMulLog p ≤ 1 − p ≤ 1（negMulLog_le_one_sub_self）
       → 1 − p_W は integrable（p_W が L¹）なので正部支配 OK
   2b. 負部 (p_W > 1 領域、p log p ≥ 0): ここが核心。p_W·log p_W の上側裾を抑える必要。
       一般には spike 状密度で log が暴れるが、有限分散 Var(X+Y) で密度の集中が制限される。
       Gaussian maxent ½log(2πe·Var) は Bochner 積分「値」を抑えるが integrand を抑えない（落とし穴）。
3. Integrable.sub で結合 → hent_sum。
```

実際に成立している事実（h(X) ≤ h(X+Y) ≤ ½log(2πe·Var(X+Y)) の両側有界）は **値**の有界であり、それだけでは Bochner 積分の被積分関数の可積分性に直結しない。

---

## A. in-tree（InformationTheory/）資産

### A-1. `differentialEntropy` 定義と integrand-integrability の関係

| 概念 | API / file:line | signature（verbatim 抜粋） | 状態 | hent_sum での扱い |
|---|---|---|---|---|
| 定義 | `differentialEntropy` `DifferentialEntropy.lean:45` | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | ✅ | hent_sum はこの **被積分関数** の integrability。definition 値（Bochner）とは別概念 |
| Dirac 値 | `differentialEntropy_dirac` `DifferentialEntropy.lean:155` | `differentialEntropy (Measure.dirac m) = 0` | ✅ | 退化境界の sanity（spike の極限）|

**重要（落とし穴・verbatim 確認済）**: `differentialEntropy μ` は `∫ negMulLog ((μ.rnDeriv vol ·).toReal) ∂vol`（`DifferentialEntropy.lean:45`）。Mathlib の Bochner `∫` は **被積分関数が非可積分なら `0` を返す**。よって「`differentialEntropy μ` が有限実数」だけでは hent_sum（= 被積分関数が `Integrable`）は **follow しない**。in-tree に「`differentialEntropy` 有限 ⟹ negMulLog integrable」の橋は **存在しない**（`rg` で 0 件、後述）。

### A-2. Gaussian maxent 上界（上界ルートの本体）

| API | file:line | signature（`[...]` verbatim） | 状態 | hent_sum での扱い |
|---|---|---|---|---|
| maxent 上界 | `differentialEntropy_le_gaussian_of_variance_le` `DifferentialEntropy.lean:520` | `theorem ... {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | ✅ Gaussian 非依存（一般 a.c. に適用可）| **致命的: `h_ent_int`（= hent_sum そのもの）を前提に取る**。上界補題は hent_sum を produce しない、逆に **要求** する。循環 |

**結論形 verbatim**: `differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`。これは Real 値の不等式（`differentialEntropy μ` という Bochner 積分**値**の上界）であって `Integrable _ _` ではない。さらに前提 `h_ent_int` に hent_sum と同型の可積分性を **要求** する。→ **上界 maxent は hent_sum の供給源にならない**（むしろ消費者）。

### A-3. negMulLog density 可積分性を produce する in-tree 補題（全列挙）

| API | file:line | 前提の核（verbatim 抜粋） | 一般 `pX ∗ pY` に効くか |
|---|---|---|---|
| `convDensityAdd_negMulLog_integrable` | `FisherInfoV2DeBruijnAssembly.lean:2532` | `(pX : ℝ → ℝ) (hpX_nn ...) (hpX_meas ...) (hpX_int ...) (hpX_mass : ∫ pX = 1) (hpX_mom : Integrable (fun y => y^2 * pX y) volume) {t : ℝ} (ht : 0 < t) : Integrable (fun x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume` | ❌ **Gaussian 核 `g_t` 専用**。第二因子が `gaussianPDFReal 0 ⟨t,_⟩` に固定 |
| `convDensityAdd_negMulLog_integrable_pub` | `EPIG2HeatFlowContinuity.lean:131` | 同上を public 再公開（delegation のみ）| ❌ 同上（Gaussian 核固定）|
| `negMulLog_convDensity_entropy_ge_density` (β下界・密度形) | `EPIG2ConvEntropyDensity.lean:124` | `{pX} (hpX_nn ...) ... (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) {v_Z : ℝ≥0} (hv_Z_pos ...) (u : ℕ → ℝ) (hu_pos ...) (n : ℕ) : (∫ negMulLog pX) ≤ ∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩) x)` | ❌ Gaussian 核 + **値の不等式**（integrability でない）|
| `negMulLog_convDensity_entropy_ge` (β下界・Ω形) | `EPIG2ConvEntropyMonotone.lean:431` | `(X Z : Ω → ℝ) ... (hZ_law : μ.map Z = gaussianReal 0 v_Z) ...` 結論 `(∫ negMulLog pX) ≤ ∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n,_⟩))` | ❌ **Z が Gaussian** 必須、かつ値の不等式 |
| `negMulLog_convDensityAdd_gaussian_entropy_upper` (maxent上界) | `EPIVitaliUI.lean:383` | `{pX} ... {t : ℝ} (ht : 0 < t) {V : ℝ≥0} (hV : (∫ x² pX) + t ≤ V) (hV0 : V ≠ 0) : (∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩) x)) ≤ (1/2) * Real.log (2πe·V)` | ❌ Gaussian 核 + 値の不等式 |

**核心判定**: produce する補題（`convDensityAdd_negMulLog_integrable` 系）の証明は `convDensityAdd_logFactor_poly_majorant`（`FisherInfoV2DeBruijnAssembly.lean:343`）に決定的に依存。この majorant の上界部分は `convDensityAdd_lower_bound_gaussian_uniformR`（**Gaussian 平滑化が density に Gaussian の裾 `(1/2)·g_s(|x|+R) ≤ p_s x` を注入する**ことで `-log p_s ≤ A + B·x²` を保証、docstring `:312-322` verbatim）に依存。一般 `pX ∗ pY` ではこの Gaussian 下界減衰が無く、negMulLog 負部が多項式で抑えられない。→ **in-tree 資産は一般和に転用不能**。

### A-4. 一般和の密度表現（`P.map(X+Y)` の rnDeriv = `pX ∗ pY`）

| API | file:line | signature（核） | 一般化可否 |
|---|---|---|---|
| `pPath_eq_convDensityAdd` | `FisherInfoV2DeBruijnPerTime.lean:215` | `(X Z : Ω → ℝ) ... (hZ_law : P.map Z = gaussianReal 0 v_Z) (pX ...) (hpX_law : P.map X = volume.withDensity (ofReal∘pX)) {s} (hs : 0 < s) : (P.map (gaussianConvolution X Z s)).rnDeriv volume =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨s*v_Z,_⟩) z)` | ❌ そのままは Z=Gaussian 専用。**だが証明構造は一般化可能**（後述、gateway atom）|
| `convDensityAdd` 定義 | `EPIConvDensity.lean:42` | `noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ x, pX x * pY (z - x) ∂volume` | ✅ 一般 |
| `convDensityAdd_comm` | `EPIConvDensity.lean:47` | `convDensityAdd pX pY = convDensityAdd pY pX` | ✅ 一般 |
| `convDensityAdd_pXpY_integrable` | `EPIConvDensityAssoc.lean:159` | `(pX pY : ℝ → ℝ) (hpX_int ...) (hpX_meas ...) (hpY_int ...) (hpY_meas ...) : Integrable (convDensityAdd pX pY) volume` | ✅ **一般**（両 L¹）|
| `convDensityAdd_pXpY_integral_eq` | `EPIConvDensityAssoc.lean:167` | `... : ∫ z, convDensityAdd pX pY z ∂volume = (∫ pX)·(∫ pY)` | ✅ 一般（質量 1 になる）|
| `convDensityAdd_second_moment` | `EPIVitaliUnifTight.lean:123` | `{pX} ... {t} (ht : 0 < t) : ∫ x² · convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩) x = (∫ x² pX) + (∫ pX)·t` | ❌ **第二因子 Gaussian 専用**（二次モーメント値）|

**密度表現の一般化見込み**: `pPath_eq_convDensityAdd` の証明（`:240-256` verbatim）は `gaussianConvolution_law_conv`（和の law=conv）+ `gaussianReal_of_var_ne_zero`（Gaussian を withDensity 化）+ `conv_withDensity_eq_lconvolution` + `Measure.rnDeriv_withDensity` の 4 段。Gaussian 固有なのは「`gaussianReal_of_var_ne_zero` で Z 側を密度化」する所のみ。一般版は `IndepFun.map_add_eq_map_conv_map` + 両側 `withDensity_rnDeriv_eq`（`hX_ac`/`hY_ac`）+ `conv_withDensity_eq_lconvolution` で組める見込み。→ **gateway atom 候補**（後述）。

### A-5. negMulLog 上界・正部支配の素材

| API | file:line | signature verbatim | hent_sum での扱い |
|---|---|---|---|
| `Real.negMulLog_le_one_sub_self` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:234` | `lemma negMulLog_le_one_sub_self {x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x` | ✅ **正部支配の主役**（`negMulLog p ≤ 1 − p`、`1 − p_W` は L¹）|
| `Real.negMulLog_nonneg` | 同上 | `0 ≤ x → x ≤ 1 → 0 ≤ x.negMulLog` | ✅ 正部の符号管理 |
| `Real.negMulLog_def` | 同上 | `negMulLog x = -x * Real.log x` | ✅ 分解 |

---

## B. Mathlib 資産

| 概念 | API / file:line | signature（`[...]` verbatim） | 状態 | hent_sum での扱い |
|---|---|---|---|---|
| 独立和の law=conv | `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map` `Mathlib/Probability/Independence/Basic.lean`（loogle Found 1）| `(μ.map(X+Y)) = μ.map X ∗ μ.map Y`（in-tree で使用済 `EPIUncondMixedCase.lean:61`）| ✅ | 密度表現の出発点 |
| conv の a.c. 伝播 | `MeasureTheory.Measure.conv_absolutelyContinuous` / `Measure.conv_comm`（in-tree `EPIUncondMixedCase.lean:55-62` で使用済）| 既存 | ✅ | X+Y の a.c.（既に `map_add_absolutelyContinuous` で利用）|
| withDensity の rnDeriv | `Measure.withDensity_rnDeriv_eq` `Mathlib/.../Decomposition/RadonNikodym.lean:60` | `theorem withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDeriv μ ν) = μ` | ✅ | a.c. measure を密度形に |
| conv↔lconvolution withDensity | `conv_withDensity_eq_lconvolution`（loogle: from `Mathlib.MeasureTheory.Measure.WithDensity`; in-tree 使用 `EPIStamSupplyTwoTime.lean:126`）| in-tree で利用実績あり | ✅ | rnDeriv = convDensityAdd 橋の中核 |
| 独立和の分散加法 | `ProbabilityTheory.IndepFun.variance_add` `Mathlib/Probability/Moments/Variance.lean:406` | `nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ]` | ✅ | Var(X+Y) 有限 を h_mom から（maxent の v に必要）|
| Integrable 支配 | `MeasureTheory.Integrable.mono'` `Mathlib/.../L1Space/Integrable.lean`（loogle Found 1）| 既存 | ✅ | 上界関数経由の integrability |
| Integrable 正部 | `MeasureTheory.Integrable.pos_part` `Mathlib/.../L1Space/Integrable.lean`（loogle Found 1）| 既存 | ✅ | posPart/negPart 分解の道具 |
| **conv の L^p Young** | — | — | ❌ **不在**（loogle Found 0）| 負部支配の本命が無い |
| **density 有界/連続 from L¹×L²** | — | — | ❌ **不在**（`MeasureTheory.convolution` は内積空間値で `Measure.conv` と別物、L^p 評価なし）| spike-free を保証できない |

### Mathlib `convolution` の注記

`MeasureTheory.convolution`（`Mathlib/Analysis/Convolution.lean`）は **関数値（内積空間値）の畳み込み** であり、確率測度の `MeasureTheory.Measure.conv` とは別 API。loogle で `convolution, eLpNorm` / `convolution, MemLp` ともに **Found 0**。`convolution, _ ≤ _` は 7 件あるが `dist_convolution_le` / `convolution_mono_*`（点ごと評価）で **L^p ノルム Young ではない**。`convolution, Continuous` 10 件は `HasCompactSupport.continuous_convolution_right` / `BddAbove.continuous_convolution_*_of_integrable` 等で、片側に **有界性/コンパクト台** を要求し一般 a.c. 密度には効かない。

---

## C. 主要前提条件ボックス（前提事故が起きやすい lemma）

- **`differentialEntropy_le_gaussian_of_variance_le`（DifferentialEntropy.lean:520）**:
  - `[IsProbabilityMeasure μ]`、`hμ : μ ≪ volume`、`hv : v ≠ 0`。
  - `h_var : ∫ (x-m)² ∂μ ≤ v`（一般和では Var(X+Y) = Var(X)+Var(Y) を `IndepFun.variance_add` で構成し v に）。
  - `h_var_int : Integrable (fun x => (x-m)²) μ`（h_mom_X/Y + memLp.add から）。
  - **`h_ent_int : Integrable (fun x => negMulLog ((μ.rnDeriv vol ·).toReal)) volume`** ← **これが hent_sum そのもの**。上界補題は hent_sum を要求する側で、供給しない。
  - 結論は **Real の不等式（値の上界）**であって `Integrable` ではない。
- **`convDensityAdd_negMulLog_integrable`（FisherInfoV2DeBruijnAssembly.lean:2532）**:
  - 第二因子が `gaussianPDFReal 0 ⟨t, ht.le⟩` に固定（Gaussian 核専用）。
  - `hpX_mass : ∫ pX = 1`、`hpX_mom : Integrable (fun y => y² * pX y) volume`（正則性）。
  - 証明は Gaussian 下界減衰（`convDensityAdd_lower_bound_gaussian_uniformR`）に依存 → 一般 `pY` に転用不能。
- **`pPath_eq_convDensityAdd`（FisherInfoV2DeBruijnPerTime.lean:215）**:
  - `hZ_law : P.map Z = gaussianReal 0 v_Z`（Z=Gaussian 必須）。一般版は要自作（atom）。
- **`conv_withDensity_eq_lconvolution`**: 両因子 `Measurable`（`hF_meas`/`hG_meas`）。a.c. 密度の measurability は rnDeriv の `Measure.measurable_rnDeriv` から確保。

---

## D. 自作が必要な要素（優先度順）

1. **【gateway atom・優先度最高】一般独立和の密度表現補題**
   `(P.map (fun ω => X ω + Y ω)).rnDeriv volume =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd pX pY z)`
   （`hX_ac`/`hY_ac` から両周辺密度 `pX := ((P.map X).rnDeriv vol ·).toReal` / `pY := ((P.map Y).rnDeriv vol ·).toReal` を取り、`IndepFun.map_add_eq_map_conv_map` + 両側 `withDensity_rnDeriv_eq` + `conv_withDensity_eq_lconvolution` + `Measure.rnDeriv_withDensity` で組む）。
   - 推奨: `pPath_eq_convDensityAdd`（FisherInfoV2DeBruijnPerTime.lean:215）から `gaussianReal_of_var_ne_zero` の段を一般 `withDensity_rnDeriv_eq` に差し替えた generic 版。
   - 工数感: 中（~40〜70 行）。in-tree に類似 5 段証明があるので template あり。
   - 落とし穴: `pX`/`pY` を `.toReal` で取ると non-negativity / measurability の `ae` 管理が必要（`Measure.measurable_rnDeriv` + `Measure.lintegral_rnDeriv` 系）。`hX_ac` が必須（hent_sum の文脈にあり OK）。

2. **【核心・優先度最高】一般 `pX ∗ pY` の negMulLog 可積分性補題（負部支配）**
   `Integrable (fun z => Real.negMulLog (convDensityAdd pX pY z)) volume`
   （前提: 両 density が L¹ + 有限二次モーメント + 各々 negMulLog integrable）。
   - **これが真の障害**。in-tree の `convDensityAdd_negMulLog_integrable` は Gaussian 核専用で転用不能。
   - 正部（`p_W ≤ 1`）は `negMulLog_le_one_sub_self` + `convDensityAdd_pXpY_integrable`（L¹）で `Integrable.mono'` 支配 OK（~20 行）。
   - 負部（`p_W > 1`、`p_W·log p_W`）が問題。一般和では Gaussian の裾下界が無く、`-log p_W ≤ A + B·z²` 形の多項式 majorant が **density の有界性なしには立たない**。有限分散だけでは spike 状密度の和で `p_W` が局所的に大きくなり log の正側裾が暴れる可能性。**closure には p_W の bounded density 性（例えば片方が L² 密度なら Young で `pX ∗ pY ∈ L∞`）が要る**が、それは「両有限分散 + 両 a.c.」からは出ない（撤退理由 (c) は本質的）。
   - 工数感: 大（負部支配の解析が non-trivial、~150〜250 行 or 追加 regularity 仮説）。

3. **【補助】Var(X+Y) 有限 + ½log(2πe·Var) 上界の配線**
   `IndepFun.variance_add`（Mathlib:406）で Var(X+Y) = Var(X)+Var(Y) < ∞ を確立し、上界 maxent の `v` を供給。
   - ただし上記の通り maxent は **値**の上界で hent_sum（integrability）を直接出さない。これは「hent_sum が成立する**根拠**」を数学的に保証するだけで、Lean 上の `Integrable` 証明には項目 2 の負部支配が別途必要。
   - 工数感: 小（~15 行、Mathlib API 直結）。

---

## E. Mathlib / in-tree 壁の列挙（`@residual` 対象判定）

| 壁候補 | loogle 確認 | 判定 |
|---|---|---|
| conv の L^p Young 不等式（`eLpNorm (pX ∗ pY) ≤ ...`）| `MeasureTheory.convolution, MeasureTheory.eLpNorm` → **Found 0**; `convolution, MemLp` → **Found 0** | **Mathlib 不在**。だが hent_sum 閉鎖の唯一の道ではない（項目 2 の負部直接支配で迂回可能性あり）。`@residual(wall:...)` ではなく `plan:` 分類が妥当 |
| density 有界 from L¹×L²（一般 conv ∈ L∞）| `convolution, _ ≤ _` 7 件は点評価のみ、L^p 無し | Mathlib 不在だが、これは項目 2 の**一手段**であって必須ではない |
| Lieb 鋭 Young / Brascamp-Lieb | （既存 `wall:epi-infinite-variance-classical` で確認済、in-tree docstring `EPICase1SmoothingLimit.lean:1404`）`entropyPower`/`Lieb`/`Brascamp`/sharp-Young on `Measure ℝ` → **Found 0** | 既知 Mathlib 壁。**ただし hent_sum は有限分散枝なので無限分散壁とは別**。hent_sum 自体は Lieb 不要 |

**共有 sorry 補題化の推奨**: 項目 2（一般 `pX ∗ pY` negMulLog 可積分性）が closure できない場合、これは **Gaussian 平滑化版 `convDensityAdd_negMulLog_integrable` の一般核版** という明確な単位なので、`InformationTheory/Shannon/EPIConvDensity*.lean` 系に **共有 sorry 補題**（`convDensityAdd_negMulLog_integrable_general` 等、`sorry` + `@residual`）として 1 本に集約推奨（複数 file 散在を防ぐ。詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」）。**現状 `hent_sum` の `@residual(plan:epi-finitevar-smoothing-limit-plan)` 分類は妥当**（真の Mathlib 壁 `wall:` ではなく、closeable な実解析 gap で plan 管理）。ただし負部支配が「両有限分散だけからは genuine に出ない（撤退理由 (c) 本質的）」なら、**追加 regularity 仮説（片方 L² 密度 / bounded density）を入れて closeable に格下げするか、`wall:` 再分類するか**の判断が必要（後述）。

---

## F. 撤退ラインへの距離（核心判定材料）

### 撤退理由 (c) の本質性 — **本質的（迂回には追加仮説が要る）**

> (c) 負部（p>1）の可積分性を分けると、負部は ∫p²<∞（密度 L²）を要求し、一般 a.c. 密度 + 有限分散だけからは出ない。

**判定: (c) は本質的に正しい。** 理由を 3 点で確定:

1. **上界 maxent は integrability を produce しない（最重要）**: `differentialEntropy_le_gaussian_of_variance_le`（DifferentialEntropy.lean:520）の結論は `differentialEntropy μ ≤ ½log(2πe·v)` という **Bochner 積分値の Real 不等式**。Mathlib の Bochner `∫` は非可積分時 `0` を返すため、この上界が成り立っても被積分関数 `negMulLog ∘ density` が `Integrable` とは限らない。しかも当該補題は `h_ent_int`（= hent_sum 同型）を **前提に要求** する。→ 「h(X)≤h(X+Y)≤½log(2πe·Var) の両側有界」は **値**の有界であって、hent_sum（integrability）の供給源にならない。

2. **下界 `h(X)≤h(X+Y)` も値の不等式**: `differentialEntropy_add_ge_of_indep`（EPIUncondMixedCase.lean:76）の結論は `differentialEntropy (P.map X) ≤ differentialEntropy (P.map (X+Y))`（値）。これも被積分関数の可積分性を produce しない（依頼の撤退理由 (b) と整合、確認済）。

3. **in-tree の唯一の integrability producer は Gaussian 核固有**: `convDensityAdd_negMulLog_integrable`（FisherInfoV2DeBruijnAssembly.lean:2532）の証明は `convDensityAdd_logFactor_poly_majorant` → `convDensityAdd_lower_bound_gaussian_uniformR`（Gaussian 下界減衰で `-log p_s ≤ A+B·x²`）に依存。一般 `pX ∗ pY` ではこの下界が無いため、負部の多項式 majorant が立たない。spike 状密度の和では `p_W` が局所的に大きく log 正側裾が暴れうる。

**「両側有界 ⟹ integrable」の道は Mathlib/in-tree に無い**（A-1 の通り、`differentialEntropy` 有限から negMulLog integrable を出す橋は不在、削除された `negMulLog_integrable_of_density` が「L¹+二次モーメント ⟹ entropy 有限」を false-as-stated として削除された経緯あり、`EPIG2HeatFlowContinuity.lean:487-489` verbatim 確認）。

### 撤退ライン判定

親計画 `docs/shannon/epi-finitevar-smoothing-limit-plan.md` の撤退ラインを直接 Read していないため断定は避けるが、本調査の所見:

- **hent_sum を「両 a.c. + 両有限分散 + 両有限微分エントロピー」だけから genuine に閉じるのは、現 Mathlib では困難**（項目 2 の負部支配が立たない）。撤退ライン（「素朴ルートで閉じない場合」系）に**触れる可能性が高い**。
- **縮退案（新規撤退ラインとして提案、撤退口は sorry + `@residual`）**:
  - **縮退案 α（推奨）**: hent_sum の signature に **追加 regularity 仮説**を入れて closeable に格下げ。具体的には「片方の周辺密度が L²（`MemLp pX 2 volume`）」を足すと、Young（`pX ∈ L², pY ∈ L¹ ⟹ pX ∗ pY ∈ L²`）→ bounded-ish → 負部支配可能。ただし **Mathlib に conv Young が無い**（E 参照、Found 0）ので Young 自体も自作要 → 工数大。
  - **縮退案 β**: hent_sum を「`P.map(X+Y)` の bounded density 性」を追加 precondition とする honest regularity 仮説に変える（load-bearing でない: bounded density は X+Y の正則性であって EPI を encode しない）。これなら負部 `p_W·log p_W ≤ p_W·log‖p_W‖∞` で `Integrable.mono'` 支配可能。**最も実装コスト低い縮退**。
  - **縮退案 γ（park）**: hent_sum を共有 sorry 補題 `convDensityAdd_negMulLog_integrable_general`（`sorry` + `@residual(plan:epi-finitevar-smoothing-limit-plan)` または新 `wall:` slug）に集約し、現状維持で park。`entropyPowerExt_add_ge_of_finite_variance`（delegate 先、`EPICase1SmoothingLimit.lean:1351`）は hent_sum を仮説に取るので、hent_sum を closeable にできれば下流は配線で済む。

**反証義務（過大評価対策）**: 上記「(c) 本質的」判定は loogle Found 0（conv Young）+ 実コード verbatim（Gaussian 依存 3 補題）+ template lemma（`differentialEntropy_le_gaussian_of_variance_le` が値の上界で integrability を出さない）の 3 点で裏取り済。ただし **小サンプル反例は未実行** — 「両有限分散の独立和で negMulLog density が実際に非可積分になる具体例」は数学的には Cauchy 的 heavy-tail を二次モーメントで排除してもなお log 裾が問題になりうるが、本当に反例が構成できるかは未確認。**closeable 判定の最終確証には `lean-implementer` への gateway atom dispatch（項目 1 の一般密度表現 + 項目 2 の正部のみ）を 1 回試す**ことを推奨（gateway-atom-first 原則）。

### gateway atom 候補（名指し）

**「これ 1 本が通れば残りが配線で済む」atom = 項目 1 の一般密度表現 `convDensityAdd_eq_rnDeriv_map_add`（仮称）**:
`(P.map (fun ω => X ω + Y ω)).rnDeriv volume =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd pX pY z)`（`pX := ((P.map X).rnDeriv vol ·).toReal`, `pY := 同`）。
- これが通れば、hent_sum は「`convDensityAdd pX pY` の negMulLog 可積分性」（項目 2）に reduce され、in-tree の正部素材 + 上界 maxent の配線で **正部は確定**、残り負部だけが真の gap として孤立する。負部の孤立化により縮退案 α/β の影響範囲が最小化される。
- 実装難度: 中（in-tree `pPath_eq_convDensityAdd` の generic 化、~40〜70 行）。**最初に dispatch すべき 1 本**。

---

## G. 着手 skeleton（参考・実装は別 agent）

> `lean-implementer` が gateway atom から着手する際の出だし。`EPIConvDensity.lean` 拡張 or 新 file。

```lean
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensityAssoc
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **gateway atom**: 一般独立和の密度 = 周辺密度の畳み込み。
`hX_ac`/`hY_ac` 必須。`pPath_eq_convDensityAdd` の Gaussian 段を一般 `withDensity_rnDeriv_eq` に
差し替えた generic 版。 -/
theorem convDensityAdd_eq_rnDeriv_map_add
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) :
    (P.map (fun ω => X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal
        (convDensityAdd (fun x => ((P.map X).rnDeriv volume x).toReal)
          (fun y => ((P.map Y).rnDeriv volume y).toReal) z) := by
  sorry -- @residual(plan:epi-finitevar-smoothing-limit-plan) [gateway atom、最初に試す]

/-- **核心**: 一般 `pX ∗ pY` の negMulLog 可積分性（負部支配が真の gap）。
正部は `negMulLog_le_one_sub_self` + `convDensityAdd_pXpY_integrable` で支配。
負部（p>1, p·log p）は一般 a.c.+有限分散だけからは立たない可能性（撤退理由 (c) 本質的）。 -/
theorem convDensityAdd_negMulLog_integrable_general
    (pX pY : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpY_nn : ∀ x, 0 ≤ pY x)
    (hpX_int : Integrable pX volume) (hpY_int : Integrable pY volume)
    (hpX_meas : Measurable pX) (hpY_meas : Measurable pY)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpY_mom : Integrable (fun y => y ^ 2 * pY y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
    (hpY_ent : Integrable (fun x => Real.negMulLog (pY x)) volume) :
    Integrable (fun z => Real.negMulLog (convDensityAdd pX pY z)) volume := by
  sorry -- @residual(plan:epi-finitevar-smoothing-limit-plan) [負部支配が真の gap、縮退案 α/β 検討]

end InformationTheory.Shannon
```

---

## 既存率 / 自作 / 撤退 サマリ

- **既存率**: 組立部品（密度表現素材・正部支配・Var 加法・Integrable 道具）は分子ベース約 60% 既存（A-4 一般 conv 系 4 本 + A-5 negMulLog 上界 3 本 + B の Mathlib 5 本が ✅、対して Gaussian 専用で転用不能 5 本 + 不在 2 本が ❌）。
- **自作必要**: 3 件（gateway 密度表現 / 一般 negMulLog 可積分性 / Var 配線）。うち真の難所は **1 件（一般 negMulLog 負部支配）**。
- **撤退ライン**: **発動懸念あり（要 gateway atom dispatch で確証）**。「両 a.c.+両有限分散+両有限微分エントロピー」だけでの genuine closure は現 Mathlib では困難。縮退案 β（X+Y の bounded density を honest regularity precondition に追加）が最低コスト。
