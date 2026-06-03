# EPI-Stam-to-Conclusion Phase 0.C-1: heat-flow path Mathlib API inventory

> 親計画: [`docs/shannon/epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) Phase 0.C-1 (line 325-333)。
> 本ファイルは Phase 0.C-2 (signature 確定) 着手前の M0 在庫調査。
>
> **Status (2026-05-25, fresh inventory): heat-flow path 定義は Mathlib では裸 (OU semigroup / heat semigroup ともに `Found 0 declarations`)。一方、InformationTheory プロジェクト内に既存の `gaussianConvolution X Z t := X + √t · Z` (FisherInfoV2DeBruijn.lean:154) と Gaussian heat kernel + `IsHeatFlowDensity` 構造が完備されており、これを Phase 0.C-1 の出発点として再利用すべき。**
>
> **⚠️ Sign correction (2026-05-25 Phase 0 closure post-mortem)**: 以下 §B' / §G(b) の `MonotoneOn` 推奨は **sign error**。実装で確定した正しい符号は **`AntitoneOn (fun s => gap_s) (Set.Icc 0 1)`** (Csiszár scaling は gap が時間進行で 0 へ decreasing、`gap_0 ≥ gap_1 = 0` で EPI 結論)。`MonotoneOn` 採用 → `gap_0 ≤ gap_1 = 0` ⇒ `-EPI` で逆向き。`monotoneOn_of_deriv_nonneg` も `antitoneOn_of_deriv_nonpos` に読み替え。Phase 0 実装の最終形は `EPIStamToBridge.lean:170-188` 参照。

## 一行サマリ

**heat-flow path API のうち Mathlib 既存実体は ~50% (Gaussian distribution / `Measure.conv` / `Monotone(On)` / `HasDerivAt` 系)、自作必要は heat-flow path の 2-source 形 `√(1-s)·X + √s·Z` のみ (~30-80 行)、ただし InformationTheory 既存の `gaussianConvolution X Z t = X + √t·Z` (1-source 形) を流用するか拡張する選択肢あり。撤退ライン L-Concl-0Sc-β (Mathlib 壁) は発動しない (壁ではなく既存資産で組める)、L-Concl-0Sc-α (案 2 退避) も発動不要 (規模 <300 行で genuine 化見込み)。**

---

## 主定理の最終形 (Phase 0.C-2 で確定する signature の draft)

親計画 line 264-275 から (再掲)。Mathlib-shape-driven で `MonotoneOn` 結論形を採用する想定 (理由は § (b) 参照):

```lean
-- Phase 0.C-2 で確定予定 (案 A: MonotoneOn 直書き)
def IsStamToEPIScalingHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStamInequalityHyp X Y P →
    ∃ (Z_X Z_Y : Ω → ℝ),
      P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
      IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧
      MonotoneOn
        (fun s : ℝ =>
          entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
            - entropyPower (P.map (heatFlowPath2 X Z_X s))
            - entropyPower (P.map (heatFlowPath2 Y Z_Y s)))
        (Set.Icc (0:ℝ) 1)
```

証明戦略 (Csiszár scaling, Cover-Thomas Lemma 17.7.3):

```
gap_s := entropyPower(X_s+Y_s) - entropyPower(X_s) - entropyPower(Y_s)
1. s ↦ gap_s が C^1 on (0, 1]                              -- HasDerivAt + parameter diff under integral
2. d/ds gap_s = (1/2) · (1/J(X_s+Y_s) − 1/J(X_s) − 1/J(Y_s)) · (gap 係数) -- de Bruijn V2 + chain rule
3. Stam: 1/J(X_s+Y_s) ≥ 1/J(X_s) + 1/J(Y_s)                -- IsStamInequalityHyp
4. ⇒ d/ds gap_s ≥ 0 on (0, 1)                              -- linarith
5. ⇒ MonotoneOn gap (Icc 0 1)                              -- monotoneOn_of_deriv_nonneg
6. Bridge: gap_0 ≤ gap_1 = 0 (Gaussian saturation at s=1)  -- entropy_power_inequality_gaussian_saturation
```

---

## A. heat-flow path / Gaussian semigroup の既存 API

### A.1 Mathlib 既存 (Gaussian distribution + 畳み込み)

| 概念 | Mathlib API | file:line | 状態 | Phase 0.C-1 での扱い |
|---|---|---|---|---|
| Gaussian 測度 | `noncomputable def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:200` | OK 既存 | `Z_X ∼ 𝒩(0,1)` を carry |
| Gaussian は確率測度 | `instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianReal μ v)` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:209` | OK 既存 | 自動 instance |
| `c · X` の Gaussian 法則 | `lemma gaussianReal_map_const_mul (c : ℝ) : (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:298` | OK 既存 | `√(1-s) · X` / `√s · Z` の法則計算 |
| 同上 `· * c` 版 | `lemma gaussianReal_map_mul_const (c : ℝ) : (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:325` | OK 既存 | 同上 |
| 独立 Gaussian の和 | `lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) : P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:624` | OK 既存 | `s=1` 端点 (`√0·X + √1·Z = Z`) と Gaussian saturation |
| Gaussian 畳み込み | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | OK 既存 | 測度レベル合成 |
| 独立和 → 畳み込み | `theorem IndepFun.map_add_eq_map_conv_map` | `Mathlib/Probability/Independence/Basic.lean` (loogle: `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map`) | OK 既存 | 上記の bridge |
| 測度畳み込み | `def MeasureTheory.Measure.conv` (記号 `∗`) | `Mathlib/MeasureTheory/Group/Convolution.lean` | OK 既存 | 必要なら raw form |
| Gaussian の `c=0` 退化 | `lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:207` | OK 既存 | `s=0` 端点で `√1·X + √0·Z = X` |

### A.2 Mathlib 不在 (重要、L-Concl-0Sc-β の判定根拠)

| 概念 | loogle 結果 | rg 確認 | 判定 |
|---|---|---|---|
| `MeasureTheory.OrnsteinUhlenbeck` | unknown identifier | rg 0 hit (mathlib 全域) | **不在** |
| `MeasureTheory.HeatSemigroup` | unknown identifier | rg 0 hit | **不在** |
| heat semigroup / OU semigroup 一般論 | — | rg 0 hit | **完全不在** |
| `heatKernel` (Mathlib 側) | — | rg 0 hit on mathlib | **Mathlib 不在** |

**重要**: heat-flow path に必要な OU semigroup / heat semigroup 一般論は Mathlib に**まったくない**。ただし Gaussian distribution + convolution の primitive は揃っているので、本 Phase で必要なのは「specific な 2-source heat-flow path `√(1-s)·X + √s·Z`」の自前構築 (`gaussianConvolution` の拡張) のみ。

### A.3 InformationTheory プロジェクト既存 (再利用候補)

| 概念 | プロジェクト API | file:line | 状態 | Phase 0.C-1 での扱い |
|---|---|---|---|---|
| **1-source heat-flow** | `noncomputable def gaussianConvolution {α : Type*} (X Z : α → ℝ) (t : ℝ) : α → ℝ := fun ω => X ω + Real.sqrt t * Z ω` | `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:154` | OK 既存 | **Phase 0.C-1 の出発点**: 1-source 形 `X + √t·Z`。本 Phase の 2-source `√(1-s)·X + √s·Z` への拡張ベース |
| 1-source の law | `theorem gaussianConvolution_law_of_gaussian` ({Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P) {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1) {t : ℝ} (ht : 0 ≤ t) : P.map (gaussianConvolution X Z t) = gaussianReal m (v + ⟨t, ht⟩)) | `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:172-220` | OK 既存 | Gaussian saturation 端点で再利用 |
| measurability | `theorem measurable_gaussianConvolution {Ω : Type*} [MeasurableSpace Ω] {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (t : ℝ) : Measurable (gaussianConvolution X Z t)` | `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:162-166` | OK 既存 | 拡張版も同様に書ける |
| heat kernel | `noncomputable def heatKernel (t : ℝ) (x : ℝ) : ℝ := if h : 0 < t then gaussianPDFReal 0 ⟨t, h.le⟩ x else 0` | `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:93` | OK 既存 | 密度レベル kernel |
| heat kernel positivity | `theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x` | `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:110-118` | OK 既存 | — |
| heat kernel measurability | `theorem measurable_heatKernel (t : ℝ) : Measurable (fun x => heatKernel t x)` | `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:121-125` | OK 既存 | — |
| 空間 1階微分 | `theorem heatKernel_spatial_deriv {t : ℝ} (ht : 0 < t) (x : ℝ) : deriv (fun y => heatKernel t y) x = -(x / t) * heatKernel t x` | `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean:94-102` | OK 既存 | — |
| 空間 1階微分 HasDerivAt 形 | `theorem heatKernel_hasDerivAt_spatial {t : ℝ} (ht : 0 < t) (x : ℝ) : HasDerivAt (fun y => heatKernel t y) (-(x / t) * heatKernel t x) x` | `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean:105-117` | OK 既存 | — |
| 空間 Laplacian | `theorem heatKernel_spatial_laplacian {t : ℝ} (ht : 0 < t) (x : ℝ) : deriv (fun y => deriv (fun z => heatKernel t z) y) x = spatialLaplacianHeatKernel t x` | `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean:130-148` | OK 既存 | — |
| 時間 1階微分 | `theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : ℝ) : HasDerivAt (fun s => InformationTheory.Shannon.FisherInfoV2.heatKernel s x) ...` | `InformationTheory/Shannon/GaussianPDFVarianceDerivBody.lean:161` | OK 既存 (FisherInfoGaussianWitness で使用) | de Bruijn 系で参照 |
| heat semigroup 合成則 (測度) | `theorem heatSemigroup_compose_law {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {Y₁ Y₂ : Ω → ℝ} (hindep : IndepFun Y₁ Y₂ P) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hY₁ : P.map Y₁ = gaussianReal 0 ⟨t₁, ht₁⟩) (hY₂ : P.map Y₂ = gaussianReal 0 ⟨t₂, ht₂⟩) : P.map (Y₁ + Y₂) = gaussianReal 0 ⟨t₁ + t₂, add_nonneg ht₁ ht₂⟩` | `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean:215-228` | OK 既存 | `√(1-s)·Z + √s·Z' ∼ 𝒩(0, 1)` の証明 (variance 加法) |
| 密度予測 `IsHeatFlowDensity` | `structure IsHeatFlowDensity {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ → ℝ → ℝ) : Prop where ...` | `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:155-170` | OK 既存 | `heat_equation` field carry 構造 |
| Heat flow predicate witness | `IsHeatFlowDensity_of_sub_predicates`, `IsHeatTimeDerivHyp`, `IsHeatFlowConvolutionHyp` | `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean:170-206` | OK 既存 | 必要なら再利用 |

**鍵となる気づき**: `gaussianConvolution X Z t = X + √t · Z` (1-source) を 2-source 形 `√(1-s) · X + √s · Z` に拡張するのは ~30-50 行で済む。要再利用候補 (5 lemma):
- `gaussianConvolution` def (15 行) → `heatFlowPath2 X Z s := √(1-s) · X + √s · Z` (15 行)
- `gaussianConvolution_apply` (3 行) → 同上
- `measurable_gaussianConvolution` (5 行) → 同上
- `gaussianConvolution_law_of_gaussian` (50 行) → `heatFlowPath2_law_of_gaussian` ですが、X が Gaussian でない**一般の case** が必要 (これは新規)
- s=0 端点 `heatFlowPath2 X Z 0 = X` / s=1 端点 `heatFlowPath2 X Z 1 = Z` (各 5-10 行)

---

## B. `Monotone` / `MonotoneOn` の conclusion 形 / 主要 lemma

| 概念 | Mathlib API | file:line | 状態 | Phase 0.C-2 での扱い |
|---|---|---|---|---|
| `Monotone` def | `def Monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b` (with `variable [Preorder α] [Preorder β]`) | `Mathlib/Order/Monotone/Defs.lean:62` | OK 既存 | 候補1: `Monotone (fun s => gap_s)` 直書き |
| `MonotoneOn` def | `def MonotoneOn (f : α → β) (s : Set α) : Prop := ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b` (with `variable [Preorder α] [Preorder β]`) | `Mathlib/Order/Monotone/Defs.lean:74` | OK 既存 | **推奨候補2**: `MonotoneOn (fun s => gap_s) (Set.Icc 0 1)` |
| `Antitone` def | `def Antitone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f b ≤ f a` | `Mathlib/Order/Monotone/Defs.lean:68` | OK 既存 | 不採用 (gap は monotone 増加) |
| `AntitoneOn` def | `def AntitoneOn (f : α → β) (s : Set α) : Prop := ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a` | `Mathlib/Order/Monotone/Defs.lean:80` | OK 既存 | 不採用 |
| `monotoneOn_of_deriv_nonneg` | `theorem monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) : MonotoneOn f D` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:409-413` | OK 既存 | **Csiszár scaling step の主道具**: `gap'(s) ≥ 0` → `MonotoneOn gap (Icc 0 1)` |
| `monotone_of_deriv_nonneg` | `theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) : Monotone f` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:417-421` | OK 既存 | 候補1 用 (全 `ℝ` 上微分可能を要求) |
| `monotoneOn_of_hasDerivWithinAt_nonneg` | `lemma monotoneOn_of_hasDerivWithinAt_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x) (hf'₀ : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:426-430` | OK 既存 | f' を陽に指定する場合 |
| `monotone_of_hasDerivAt_nonneg` | `lemma monotone_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : 0 ≤ f') : Monotone f` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:434-437` | OK 既存 | 候補1 + HasDerivAt 形 |
| `strictMonoOn_of_deriv_pos` | `theorem strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:374-380` | OK 既存 | gap が**真に**増加と分かれば (Stam が equality でない場合) |
| `convex_Icc` | `theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s)` | `Mathlib/Analysis/Convex/Basic.lean:254` | OK 既存 | `monotoneOn_of_deriv_nonneg` の `Convex` 前提を満たすため |

**端点比較形 (`MonotoneOn f (Icc 0 1) → f 0 ≤ f 1`) は `Monotone(On)` の def の直接 unfold で済む**: `h_mono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one`。専用 lemma 不要。

### B' 結論形 (a)(b) 候補比較 — 推奨 verdict

| 候補 | 結論形 | Pros | Cons | 推奨度 |
|---|---|---|---|---|
| **A (推奨)** | `MonotoneOn (fun s => gap_s) (Set.Icc 0 1)` | (i) `monotoneOn_of_deriv_nonneg` の結論形と一致 (Mathlib-shape-driven)。(ii) 区間外 `s ∉ [0,1]` での挙動を要求しない (heat-flow path の domain と一致)。(iii) `IsStamToEPIScalingHyp` consumer `isStamToEPIBridgeHyp_of_scaling_limit` で `gap_0 ≤ gap_1` を取り出すのは def unfold のみで済む | 端点 `s=0, s=1` で `gap` が連続でない場合、interior に限定する追加 lemma が必要 (が、`gap_s` は連続なので非問題) | ★★★ |
| B | `Monotone (fun s : ℝ => gap_s)` (`s ∈ ℝ` 全域) | `monotone_of_deriv_nonneg` の結論形と一致 | `s < 0` / `s > 1` で `√(1-s)` / `√s` が複素数領域に出る → 退化定義 (gap = 0) で extend する追加 def が必要 | ★ |
| C | `gap_0 ≤ gap_1` (端点比較 explicit) | 直接 EPI を 1 行で導出可能 | scaling content が「monotonicity」でなく「端点比較」になり、Cover-Thomas Lemma 17.7.3 の「inner-loop monotonicity step」という設計 intent が消える | ★★ |

**A を推奨**。理由: Mathlib `monotoneOn_of_deriv_nonneg` の結論形 verbatim と一致するため、Phase A の合流定理で再 reshape 不要。Phase 0.C-1 で `heatFlowPath2 X Z s` を `s ∈ [0,1]` 限定で意味があるよう定義し、`MonotoneOn gap (Set.Icc 0 1)` を Stam + de Bruijn から組み立てる流れが最も自然。

---

## C. `HasDerivAt` 系の existing API for `s ↦ entropyPower(P.map X_s)`

| 概念 | Mathlib API | file:line | 状態 | Phase 0.C-2/3 での扱い |
|---|---|---|---|---|
| `HasDerivAt.add` | `theorem HasDerivAt.add (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) : HasDerivAt (f + g) (f' + g') x` | `Mathlib/Analysis/Calculus/Deriv/Add.lean:59-61` | OK 既存 | `gap_s` の和分解 `d/ds (a + b) = a' + b'` |
| `HasDerivAt.smul` | `theorem HasDerivAt.smul (hc : HasDerivAt c c' x) (hf : HasDerivAt f f' x) : HasDerivAt (c • f) (c x • f' + c' • f x) x` (`[NontriviallyNormedField 𝕜]`, `[NormedAddCommGroup F]`, `[NormedSpace 𝕜 F]`, ...) | `Mathlib/Analysis/Calculus/Deriv/Mul.lean:111-114` | OK 既存 | `√(1-s) · X` の積微分 |
| `HasDerivAt.const_smul` | `theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) : HasDerivAt (c • f) (c • f') x` (`{R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]`) | `Mathlib/Analysis/Calculus/Deriv/Mul.lean:194-196` | OK 既存 | 定数 smul (一定変数で smul) |
| `HasDerivAt.const_mul` | `theorem HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d' x) : HasDerivAt (fun y => c * d y) (c * d') x` | `Mathlib/Analysis/Calculus/Deriv/Mul.lean:357` | OK 既存 | `c · f` 形 |
| `HasDerivAt.sqrt` | `theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x` | `Mathlib/Analysis/SpecialFunctions/Sqrt.lean:84-86` | OK 既存 | `d/ds √(1-s) = -1/(2√(1-s))` と `d/ds √s = 1/(2√s)` の chain rule。**`hx : f x ≠ 0` 前提に注意**: `s = 0` で `√s = 0` のため `HasDerivAt.sqrt` は使えない、`(0, 1)` interior 限定 |
| パラメータ微分 (積分下) | `theorem hasDerivAt_integral_of_dominated_loc_of_lip {F' : α → E} (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable F' μ) (h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s) (bound_integrable : Integrable (bound : α → ℝ) μ) (h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀) : Integrable F' μ ∧ HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:263-269` | OK 既存 | **重要**: heat-flow path 上の `differentialEntropy (P.map X_s)` を `s` で微分するための主道具 |
| パラメータ微分 (bound 形) | `theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ) {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ) (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) : Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:289-294` | OK 既存 | 上記の deriv 上界形 |
| `Real.exp` の deriv | `Real.hasDerivAt_exp` 系 (Mathlib `Real.exp_deriv` 系) | `Mathlib/Analysis/SpecialFunctions/Exp.lean` 周辺 | OK 既存 | `entropyPower = Real.exp (2 · h)` の chain rule |
| de Bruijn identity (project) | `theorem deBruijn_identity_v2_of_heat_flow` (`InformationTheory.Shannon.FisherInfoV2`) | `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:244-254`, `FisherInfoV2DeBruijn.lean:247+` | OK 既存 (project, sister 完了済 part) | `d/ds h(X_s) = (1/2) J(X_s)` の本 project における discharge form |

**注意 (HasDerivAt.sqrt の `hx : f x ≠ 0` 前提)**:
- `heatFlowPath2 X Z s := √(1-s) · X + √s · Z` の `s` 微分は `s ∈ (0, 1)` でないと両 sqrt が differentiable でない。
- Mathlib-shape-driven 結論形 A (`MonotoneOn _ (Set.Icc 0 1)`) を採用すると、`monotoneOn_of_deriv_nonneg` の前提は `∀ x ∈ interior (Set.Icc 0 1), 0 ≤ deriv f x` でちょうど `interior = Ioo 0 1` なので `sqrt` の non-zero 前提と整合する。**Bochner Jensen / sqrt の derivative 前提と `MonotoneOn` の interior 前提が完璧に合致する** = Mathlib-shape-driven の理想形。

---

## D. `entropyPower` / `differentialEntropy` / `fisherInfoOfDensity` の既存 API

### D.1 Mathlib 側

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| `Real.exp` positivity | `theorem exp_pos (x : ℝ) : 0 < exp x` | `Mathlib/Analysis/Complex/Exponential.lean:280` | OK 既存 |
| `Real.exp_log` | `theorem exp_log (hx : 0 < x) : exp (log x) = x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:58` | OK 既存 |
| `Real.exp_le_exp` | `theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y` | `Mathlib/Analysis/Complex/Exponential.lean:316` | OK 既存 |
| `Real.log_le_log` | `lemma log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:150-151` | OK 既存 |
| `differentialEntropy` (Mathlib) | — | — | **Mathlib 不在** (rg 0 hit on `.lake/packages/mathlib/Mathlib/`) |
| `entropyPower` (Mathlib) | — | — | **Mathlib 不在** |
| `fisherInfo` (Mathlib) | — | — | **Mathlib 不在** |

### D.2 InformationTheory プロジェクト側 (既存)

| 概念 | プロジェクト API | file:line | 状態 |
|---|---|---|---|
| `entropyPower` | `noncomputable def entropyPower (μ : Measure ℝ) : ℝ := Real.exp (2 * InformationTheory.Shannon.differentialEntropy μ)` | `InformationTheory/Shannon/EntropyPowerInequality.lean:93-94` | OK 既存 |
| `entropyPower_pos` | `theorem entropyPower_pos (μ : Measure ℝ) : 0 < entropyPower μ` | `InformationTheory/Shannon/EntropyPowerInequality.lean:97-98` | OK 既存 |
| `entropyPower_gaussianReal` | `theorem entropyPower_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : entropyPower (gaussianReal m v) = 2 * Real.pi * Real.exp 1 * v` | `InformationTheory/Shannon/EntropyPowerInequality.lean:114-127` | OK 既存 |
| `differentialEntropy` | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `InformationTheory/Shannon/DifferentialEntropy.lean:42` | OK 既存 |
| `differentialEntropy_gaussianReal` | `theorem differentialEntropy_gaussianReal` (Phase C 主定理: `(1/2) log (2πe v)`) | `InformationTheory/Shannon/DifferentialEntropy.lean` (line 不詳、`rg` 検索可能) | OK 既存 |
| `IsStamInequalityHyp` | `def IsStamInequalityHyp` (Stam の `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`) | `InformationTheory/Shannon/EPIStamDischarge.lean` | OK 既存 (sister sub-plan で扱う) |
| `fisherInfoOfDensity` (V2) | `InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity` | `InformationTheory/Shannon/FisherInfoV2.lean` | OK 既存 (V2、a.e.-class-invariant) |
| de Bruijn identity V2 | `theorem deBruijn_identity_v2` 系 | `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean` | OK 既存 (sister, Gaussian discharge 済) |
| `entropy_power_inequality_gaussian_saturation` | (Phase D 主定理) | `InformationTheory/Shannon/EntropyPowerInequality.lean:226` | OK 既存 | s=1 端点 (両者 Gaussian) で gap = 0 |

---

## E. 主要前提条件ボックス (事故防止)

事故が起きやすい lemma の前提を bullet で明示:

### `monotoneOn_of_deriv_nonneg` (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:409`)

前提:
- `hD : Convex ℝ D` → `convex_Icc 0 1` で自動
- `hf : ContinuousOn f D` → `gap_s` が `Icc 0 1` 上連続を別途証明 (これは Mathlib 直接 lemma なし、自作必要 ~20-40 行)
- `hf' : DifferentiableOn ℝ f (interior D)` → `gap` が `Ioo 0 1` 上微分可能を別途証明
- `hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x` → Stam (1/J + 1/J ≤ 1/J) + de Bruijn (d/ds h = (1/2) J) の合成

### `HasDerivAt.sqrt` (`Mathlib/Analysis/SpecialFunctions/Sqrt.lean:84`)

前提:
- `hf : HasDerivAt f f' x`
- **`hx : f x ≠ 0`** → `√(1-s)` は `s = 1` で differentiable でない、`√s` は `s = 0` で differentiable でない。`interior (Icc 0 1) = Ioo 0 1` でちょうど両方 well-defined。**`MonotoneOn` 結論形 (候補A) と完璧に整合**。

### `gaussianReal_add_gaussianReal_of_indepFun` (`Mathlib/Probability/Distributions/Gaussian/Real.lean:624`)

前提:
- `{Ω}` `{mΩ : MeasurableSpace Ω}` `{P : Measure Ω}` — `P` の `IsProbabilityMeasure` 不要 (Gaussian variance 計算で自動)
- `hXY : IndepFun X Y P` — 独立性必須
- `hX : P.map X = gaussianReal m₁ v₁` — `X` 自身が Gaussian
- `hY : P.map Y = gaussianReal m₂ v₂` — `Y` 自身が Gaussian
- **重要**: 本 lemma は両 `X, Y` ともに Gaussian と仮定する。Phase 0.C-1 の場合、`X` は一般の random variable (Gaussian 限定でない)、`Z_X` のみ Gaussian。両 Gaussian 仮定は `s = 1` 端点 (`heatFlowPath2 X Z_X 1 = Z_X`) で使うが、`s ∈ (0, 1)` interior では使わない (`gaussianConvolution_law_of_gaussian` も `X = gaussianReal` 仮定; **これが本 plan の `X` 一般化 vs. discharge form のギャップ**)。

### `hasDerivAt_integral_of_dominated_loc_of_lip` (`Mathlib/Analysis/Calculus/ParametricIntegral.lean:263`)

前提 (パラメータ微分の主道具):
- `hs : s ∈ 𝓝 x₀` — `s` が `x₀` の近傍 (Icc の interior で OK)
- `hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ` — measurability
- `hF_int : Integrable (F x₀) μ` — 一点 integrability
- `hF'_meas : AEStronglyMeasurable F' μ` — derivative measurability
- `h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s` — **Lipschitz bound (decisive)**
- `bound_integrable : Integrable (bound : α → ℝ) μ` — bound integrability
- `h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀` — pointwise differentiability
- 結論: `HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀`
- **事故予測**: Lipschitz bound と integrable bound を `gaussianPDFReal` の chain rule + decay (Gaussian tail) から組み立てるのが大変、~100-150 行追加

---

## F. 自作が必要な要素 (Phase 0.C-1)

優先度順:

### F.1 必須 (Phase 0.C-1 の core)

1. **`heatFlowPath2 X Z s := √(1-s) · X + √s · Z`** (新規 def, ~15 行)
   - signature 案: `noncomputable def heatFlowPath2 {α : Type*} (X Z : α → ℝ) (s : ℝ) : α → ℝ := fun ω => Real.sqrt (1 - s) * X ω + Real.sqrt s * Z ω`
   - 既存 `gaussianConvolution X Z t = X + √t · Z` (1-source) の **2-source generalization**
   - 端点: `heatFlowPath2 X Z 0 = X` (a.e., `√1·X + √0·Z = X`), `heatFlowPath2 X Z 1 = Z`
2. **`heatFlowPath2_apply` simp lemma** (~3 行) — unfold lemma
3. **`measurable_heatFlowPath2`** (~10 行)
4. **`heatFlowPath2_zero` / `heatFlowPath2_one`** (端点) (~15 行)
5. **`heatFlowPath2_law_for_Gaussian_Z`** (~30 行) — `Z ∼ 𝒩(0,1)` のとき `√s · Z ∼ 𝒩(0, s)`、`gaussianReal_map_const_mul` から
6. **gap_s の連続性** (Phase 0.C-2 で `MonotoneOn` の `ContinuousOn` 前提として必要) (~40 行)
7. **gap_s の微分可能性 on `Ioo 0 1`** (Phase 0.C-2 の前提) (~50 行、`hasDerivAt_integral_of_dominated_loc_of_lip` 経由)

**小計**: ~160 行 (新規 file `InformationTheory/Shannon/HeatFlowPath.lean` 想定、または既存 `FisherInfoV2DeBruijn.lean` 末尾追加)

### F.2 推奨 (Phase 0.C-2 で再利用、ただし staged 可)

8. **`gap_s` の微分公式** `deriv (fun s => gap_s) s = (...)·(1/J(...) - 1/J(...) - 1/J(...))` (~80-100 行)
   - これは Stam + de Bruijn の合成、sister sub-plan の output が必須
   - sister 完了前なら staged predicate として bundle (`IsHeatFlowPathDerivativeHyp`) で抜く

### F.3 不要 (Mathlib + project 既存で十分)

- `Monotone` / `MonotoneOn` の各種 lemma (Mathlib 既存)
- `HasDerivAt.add` / `.sqrt` / `.smul` (Mathlib 既存)
- Gaussian 畳み込み `gaussianReal_conv_gaussianReal` (Mathlib 既存)
- `entropy_power_inequality_gaussian_saturation` (project 既存) ← s=1 端点で gap_1 = 0 に使う

---

## G. (a)(b)(c) 推奨判定

### (a) heat-flow path Mathlib builder の存在状況 / 自作工数

**判定: 自作必要、ただし既存資産で軽量** (規模 ~160 行新規)

- Mathlib に OU semigroup / heat semigroup 一般論 = **完全不在** (loogle / rg ともに 0 hit)
- ただし InformationTheory 既存 `gaussianConvolution X Z t = X + √t · Z` (1-source 形) を 2-source `√(1-s) · X + √s · Z` に拡張するだけで Phase 0.C-1 の主要 def が組める
- 既存 `heatKernel`, `IsHeatFlowDensity`, `heatSemigroup_compose_law` も再利用可
- **規模見積もり: 160 行 (F.1) + 80-100 行 (F.2、staged 可) = 最大 260 行**、計画書 L-Concl-0Sc-α の 800 行閾値より十分小さい

### (b) `Monotone` vs `MonotoneOn` vs 端点比較形 — consumer 15+ 件への適合度

**判定: 候補 A (`MonotoneOn (fun s => gap_s) (Set.Icc 0 1)`) を推奨**

- 比較表は §B' 参照
- 決定的理由: `MonotoneOn` の def は `∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b` で、consumer (`isStamToEPIBridgeHyp_of_scaling_limit`) は `gap_0 ≤ gap_1` だけ抽出すればよい (1 行)。
- 端点比較形 (候補 C) は scaling の monotonicity content を捨てるため Cover-Thomas Lemma 17.7.3 の設計 intent と不整合。
- `Monotone` 全域形 (候補 B) は `s ∉ [0,1]` での退化定義 (gap_s = 0) を別途要求、追加 def 必要、却下。
- 補強: `monotoneOn_of_deriv_nonneg` の `interior (Set.Icc 0 1) = Ioo 0 1` が `HasDerivAt.sqrt` の `f x ≠ 0` 前提と完璧に整合 → Phase 0.C-2 の微分可能性確認で sqrt の非自明前提が自動消化。

### (c) L-Concl-0Sc-α / β 退避判定

**判定: 撤退ラインは発動しない**

- **L-Concl-0Sc-β (Mathlib 壁退避)**: Mathlib OU semigroup / Gaussian convolution API は heat-flow 「一般論」レベルでは皆無だが、必要な primitive (`gaussianReal`, `gaussianReal_map_const_mul`, `gaussianReal_add_gaussianReal_of_indepFun`, `Measure.conv`) は完備。さらに本 project に `gaussianConvolution` の 1-source 版が既存。**「壁」ではなく「足場あり」、退避不要**。
- **L-Concl-0Sc-α (案 2 退避、>800 行)**: 上記 F.1 + F.2 で最大 260 行。撤退閾値の 1/3 以下、案 1 (genuine Csiszár scaling 化) を計画通り進める。
- **L-Concl-0Sc-γ (defect 発見時停止)**: 本調査中、既存 `IsHeatFlowDensity` / `gaussianConvolution` / `heatSemigroup_compose_law` に新規 honesty defect は **発見せず** (全 internal discharge or sister-pending staged を honest 命名で carry)。なお既存 `IsStamToEPIScalingHyp` の `@audit:suspect(epi-stam-to-conclusion-plan)` は親計画 Phase 0 でちょうど解消対象なので separate flag は不要 (重複)。

---

## H. 撤退ラインへの距離

- 親計画 (`epi-stam-to-conclusion-plan.md` line 384-403) の 3 撤退ライン全件、現状 **発動しない**
- 新規撤退ライン提案は **不要** (heat-flow path Mathlib 不在は予測済、案 1 案 2 とも本 inventory の判定通り進めば撤退条件未到達)
- ただし **monitoring 項目**:
  - F.2 の `gap_s` 微分公式 (Stam + de Bruijn 合成) は sister sub-plan 完了に依存。sister sub-plan で `IsRegularDeBruijnHypV2` の **general (non-Gaussian) case** が未 closure であり、本 Phase 0 完了後 Phase A の合流定理組み立てで再び staged 化が必要になる可能性 (`IsHeatFlowPathDerivativeHyp` 仮定として外出し)。これは Phase A 開始時に再評価。

---

## I. 着手 skeleton (Phase 0.C-1)

`InformationTheory/Shannon/HeatFlowPath.lean` (新規 file 推奨、既存 `FisherInfoV2DeBruijn.lean` は de Bruijn 系で大規模 (412 行) のため別 file が clean):

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import InformationTheory.Shannon.FisherInfoV2DeBruijn  -- gaussianConvolution に並べる

/-!
# Heat-flow path (2-source) for EPI-Stam Csiszár scaling

`heatFlowPath2 X Z s := √(1-s) · X + √s · Z`, the 2-source generalization of
the 1-source `gaussianConvolution X Z t = X + √t · Z` in `FisherInfoV2DeBruijn.lean`.
Used in `EPIStamToBridge.IsStamToEPIScalingHyp` (Phase 0 refactor) to carry
genuine Csiszár scaling monotonicity along `s ∈ [0, 1]`.

## Endpoints

* `heatFlowPath2 X Z 0 = X` (a.e., `√1 · X + √0 · Z = X`)
* `heatFlowPath2 X Z 1 = Z` (a.e., `√0 · X + √1 · Z = Z`)

## Mathlib-shape-driven design

The conclusion-form target is `MonotoneOn _ (Set.Icc 0 1)`, chosen so that
`monotoneOn_of_deriv_nonneg`'s `interior = Ioo 0 1` premise aligns with
`HasDerivAt.sqrt`'s `f x ≠ 0` premise on both `√(1-s)` and `√s`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

/-- 2-source heat-flow path `√(1-s) · X + √s · Z`. -/
noncomputable def heatFlowPath2 {α : Type*} (X Z : α → ℝ) (s : ℝ) : α → ℝ :=
  fun ω => Real.sqrt (1 - s) * X ω + Real.sqrt s * Z ω

@[simp] theorem heatFlowPath2_apply {α : Type*} (X Z : α → ℝ) (s : ℝ) (ω : α) :
    heatFlowPath2 X Z s ω = Real.sqrt (1 - s) * X ω + Real.sqrt s * Z ω := rfl

/-- Measurability of `heatFlowPath2`. -/
theorem measurable_heatFlowPath2 {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z) (s : ℝ) :
    Measurable (heatFlowPath2 X Z s) := by
  unfold heatFlowPath2
  exact (measurable_const.mul hX).add (measurable_const.mul hZ)

/-- Endpoint at `s = 0`: `heatFlowPath2 X Z 0 = X`. -/
theorem heatFlowPath2_zero {α : Type*} (X Z : α → ℝ) :
    heatFlowPath2 X Z 0 = X := by
  funext ω
  simp [heatFlowPath2, Real.sqrt_one, Real.sqrt_zero]

/-- Endpoint at `s = 1`: `heatFlowPath2 X Z 1 = Z`. -/
theorem heatFlowPath2_one {α : Type*} (X Z : α → ℝ) :
    heatFlowPath2 X Z 1 = Z := by
  funext ω
  simp [heatFlowPath2, Real.sqrt_one, Real.sqrt_zero, show (1:ℝ) - 1 = 0 by ring]

/-- Law of `heatFlowPath2 X Z s` when `Z ∼ 𝒩(0, 1)` and `X ⊥ Z`:
    `P.map (heatFlowPath2 X Z s)` is the convolution of
    `P.map (√(1-s) · X)` with `𝒩(0, s)`. -/
theorem heatFlowPath2_law {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ}
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    P.map (heatFlowPath2 X Z s)
      = (P.map (fun ω => Real.sqrt (1 - s) * X ω)) ∗ gaussianReal 0 ⟨s, hs0⟩ := by
  sorry  -- chain: gaussianReal_map_const_mul + IndepFun.map_add_eq_map_conv_map

/-- When `X` is also `𝒩(m, v)`, the full law of `heatFlowPath2 X Z s` is
    `𝒩((√(1-s)) · m, (1-s) · v + s)`. Gaussian saturation endpoint case. -/
theorem heatFlowPath2_law_of_gaussian {Ω : Type*} {_mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X Z : Ω → ℝ}
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    P.map (heatFlowPath2 X Z s)
      = gaussianReal (Real.sqrt (1 - s) * m) (.mk (1 - s) (by linarith) * v + ⟨s, hs0⟩) := by
  sorry  -- chain: gaussianReal_map_const_mul (×2) + gaussianReal_add_gaussianReal_of_indepFun

end InformationTheory.Shannon
```

最初の `sorry` (`heatFlowPath2_law`) を Phase 0.C-1 M1 で割る。Phase 0.C-2 で `IsStamToEPIScalingHyp` の signature を `MonotoneOn ... (Set.Icc 0 1)` 形に refactor し、`heatFlowPath2` を carry する形に書き直す。

---

## J. Phase 0 まとめ

| 項目 | 判定 |
|---|---|
| heat-flow path 用 Mathlib API 既存率 | **~50%** (Gaussian distribution / `Measure.conv` / `Monotone(On)` / `HasDerivAt` 系は完備、OU/heat semigroup 一般論は皆無) |
| InformationTheory 既存資産による補完率 | **~80%** (`gaussianConvolution`, `heatKernel`, `IsHeatFlowDensity`, `heatSemigroup_compose_law` 全て再利用可) |
| 自作必要 | F.1 = 6 件 ~160 行 (新規 file `HeatFlowPath.lean`)、F.2 = 1 件 80-100 行 (`gap_s` 微分式、staged 可) |
| `MonotoneOn` 候補比較 | **候補A推奨** (`MonotoneOn (fun s => gap_s) (Set.Icc 0 1)`、Mathlib-shape-driven 完璧整合) |
| 撤退ライン L-Concl-0Sc-α (>800 行) | **発動せず** (最大 260 行) |
| 撤退ライン L-Concl-0Sc-β (Mathlib 壁) | **発動せず** (壁ではなく足場あり) |
| 撤退ライン L-Concl-0Sc-γ (defect 発見) | **発動せず** (本調査中 honesty defect 0 件、既存 `IsStamToEPIScalingHyp` の suspect tag は親計画 Phase 0 で予定通り解消対象) |
| Phase 0.C-2 着手 ready | **Yes** (本 inventory の skeleton から start) |

---

## K. 主要 file pointer (Phase 0.C-1 着手時の Read 推奨順)

1. `InformationTheory/Shannon/EPIStamToBridge.lean:147-154` — refactor 対象 (現 `IsStamToEPIScalingHyp` 本体)
2. `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:144-220` — 既存 `gaussianConvolution` (本 Phase の出発点)
3. `InformationTheory/Shannon/FisherInfoV2DeBruijnBody.lean:85-170` — 既存 `heatKernel`, `IsHeatFlowDensity`
4. `InformationTheory/Shannon/FisherInfoV2HeatFlowBody.lean:80-230` — 既存 spatial deriv, semigroup compose
5. `Mathlib/Probability/Distributions/Gaussian/Real.lean:200-628` — Gaussian distribution + convolution APIs
6. `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:374-437` — `monotoneOn_of_deriv_nonneg` 系
7. `Mathlib/Analysis/SpecialFunctions/Sqrt.lean:75-100` — `HasDerivAt.sqrt`
8. `Mathlib/Analysis/Calculus/ParametricIntegral.lean:260-310` — parameter differentiation under integral
