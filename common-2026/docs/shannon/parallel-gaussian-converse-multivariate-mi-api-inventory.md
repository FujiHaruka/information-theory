# Parallel-Gaussian converse #5 — multivariate-MI Mathlib API inventory

> Scope: close the last residual `parallelOutput_joint_logDensity_integrable`
> (`InformationTheory/Shannon/ParallelGaussianConverse.lean:1093`, `@residual(wall:multivariate-mi)`).
> Parent plan: [`parallel-gaussian-converse-closure-plan.md`](parallel-gaussian-converse-closure-plan.md).
> Inventory only — no implementation, no plan edits.

## 一行サマリ

**#5 で使う API のうち実体は ~90% 既存。自作必要なのは 3 本（多変量 conv 出力等式 + Gaussian 包絡上下界 + 座標箱 Chebyshev）。**
最重要発見: **`wall:multivariate-mi` 分類は overstated（tier-4 寄り defect 候補）**。
docstring が「多変量 mixture-density 表現は原理的に存在しない」と断じているが、Mathlib の
`rnDeriv_conv'` / `conv_eq_withDensity_lconvolution_rnDeriv`（additive 版、`to_additive` 生成）が
**`Fin n → ℝ` + `volume` でそのまま適用でき**、joint 出力密度を lconvolution
`(p.rnDeriv volume) ⋆ₗ[volume] (∏ gaussianPDF)` として閉形で与える（`#check` + project context で
コンパイル確認済）。「rnDeriv が marginal rnDeriv の積に factor しない」（真）と「多変量 mixture density が
存在しない」（偽）を混同している。**撤退ライン発動: no**（縮退不要、むしろ wall 格上げの逆 — 自作可能タスク）。

---

## #5 の最終形（再掲）

`InformationTheory/Shannon/ParallelGaussianConverse.lean:1093`:

```lean
theorem parallelOutput_joint_logDensity_integrable (P : ℝ) (hP : 0 ≤ P)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    Integrable
      (fun z => Real.log
        ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).rnDeriv
          volume z).toReal)
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) := by
  sorry
```

ここで `parallelGaussianChannel N _ _ x = Measure.pi (fun i => gaussianReal (x i) (N i))`
（`ParallelGaussian.lean:98`）、入力 `p : Measure (Fin n → ℝ)` は **相関あり**（積測度でない）、
ノイズは座標独立 = 積 Gaussian。

### 1-D 手本との対応（`AwgnCapacityConverseMaxent.lean` Phase 6）

| 1-D lemma | file:line | 役割 |
|---|---|---|
| `outputMixtureDensity N p y := ∫⁻ x, gaussianPDF x N y ∂p` | `:338` | scalar mixture density def |
| `output_eq_withDensity_mixture` | `:368` | `p ∗ 𝒩(0,N) = volume.withDensity mixture` |
| `output_rnDeriv_ae_mixture` | `:409` | rnDeriv a.e. = mixture |
| `outputMixtureDensity_le_sup` | `:420` | 上界 `≤ (√2πN)⁻¹` → log 上界 |
| `output_logDensity_lower_bound` (★ 唯一の hard) | `:440` | `−log f_q ≤ a·y²+b`、Chebyshev集中 + Gaussian tail |
| `outputMixtureDensity_log_abs_le` | `:557` | `|log f_q| ≤ c₀+c₁y²` |
| consumer: `output_sq_sub_integrable` | `:162` | quadratic majorant が conv 出力上で integrable（`integrable_conv_iff`） |

証明戦略の多変量版（pseudo-Lean）:

```
-- 1. 出力 = 多変量 convolution
μY = p ∗ (Measure.pi (fun i => gaussianReal 0 (N i)))         -- 自作 (1-D outputDistribution_awgn_eq_conv の n版)
-- 2. joint mixture density を Mathlib で閉形に
μY.rnDeriv volume =ᵐ[volume]
    (p.rnDeriv volume) ⋆ₗ[volume] (∏ᵢ gaussianPDF 0 (N i) ·)  -- rnDeriv_conv' （既存）
-- 3. f_Y(z) = ∫⁻ x, p.rnDeriv volume x · ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂volume  -- lconvolution_def
--    （= ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p  via withDensity_rnDeriv_eq）
-- 4. 上界 |log f_Y| ≤ c₀ + c₁ ‖z‖² : 各座標 Gaussian の積に sup/tail 上下界
-- 5. quadratic majorant が μY 上 integrable : 多変量 second moment（power constraint）+ integrable_conv_iff
```

---

## カテゴリ 1 — 多変量 convolution

| 概念 | Mathlib API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| additive conv of measures | `MeasureTheory.Measure.conv` (= `mconv` の `to_additive`、`∗` 記法) | `Mathlib/MeasureTheory/Group/Convolution.lean:35` (mult source) | ✅ 既存 | `μY = p ∗ (Measure.pi 𝒩)` の右辺 |
| conv の lintegral 展開 | `MeasureTheory.Measure.lintegral_conv` | `Convolution.lean:51` (mult `lintegral_mconv`) | ✅ 既存 | Fubini swap（1-D `:375` の n版） |
| conv の AC | `MeasureTheory.Measure.conv_absolutelyContinuous` | `Convolution.lean:166` (mult) | ✅ 既存 | 既に `parallelOutput_absolutelyContinuous_volume` で別証明済 |
| conv 上の integrable 判定 | `MeasureTheory.integrable_conv_iff` | `Mathlib/MeasureTheory/Group/IntegralConvolution.lean` (docstring `:21` 参照) | ✅ 既存 | step 5 の quadratic majorant integrability（1-D `:170` の n版） |
| conv 上の Bochner 積分 | `MeasureTheory.integral_conv` | `Mathlib/MeasureTheory/Group/IntegralConvolution.lean` | ✅ 既存 | second-moment 計算（1-D `:172`、`parallelOutput_centered_secondMoment_eq:1142` で既使用） |

**完全 signature（mult source、additive は `to_additive` で `mconv→conv`, `mul→add`, `IsMulLeftInvariant→IsAddLeftInvariant` 置換）:**

```lean
-- Convolution.lean:35
noncomputable def mconv {M : Type*} [Monoid M] [MeasurableSpace M]
    (μ : Measure M) (ν : Measure M) : Measure M :=
  Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)

-- Convolution.lean:51
theorem lintegral_mconv {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    {μ ν : Measure M} [SFinite ν] {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ
```

**インスタンス確認（compile 済）:** `Fin n → ℝ` は
`MeasurableAdd₂ (Fin n → ℝ)` / `MeasurableNeg (Fin n → ℝ)` / `AddGroup (Fin n → ℝ)` /
`SigmaFinite (volume : Measure (Fin n → ℝ))` / `(volume : Measure (Fin n → ℝ)).IsAddLeftInvariant`
を全て自動 `infer_instance`（project context `InformationTheory.Shannon.ParallelGaussianConverse` import 下）。

**Mathlib gap 判定:** convolution 基盤は完全に存在（gap なし）。
唯一の自作 = 「出力 = conv」等式 `μY = p ∗ (Measure.pi (fun i => gaussianReal 0 (N i)))`。
1-D `outputDistribution_awgn_eq_conv` (`:85`) は `bind_eq_conv_of_translation_kernel` 経由。
**建材として既存**: `parallelOutput_marginal_eq_conv` (`:701`、sorryAx-free) が marginal レベルで
同じ conv 表現を出しており、joint 版は `Measure.snd_compProd` + translation-kernel 橋（noise = `Measure.pi 𝒩` は
`x` の各座標を平行移動）で構成可能。

**自作が必要な補題:**
- `parallelOutput_eq_conv` : `μY = p ∗ (Measure.pi (fun i => gaussianReal 0 (N i)))`（~30-50 行、1-D 手本 + Wave 3 の marginal 版を joint に持ち上げ）

---

## カテゴリ 2 — joint mixture density（★ wall 主張の核心、実は既存）

| 概念 | Mathlib API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| **conv の rnDeriv = lconvolution（σ-finite 版）** | `MeasureTheory.rnDeriv_conv'` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:664` (mult `rnDeriv_mconv'`, additive `to_additive`) | ✅ **既存** | **joint mixture density を閉形で供給** |
| conv = withDensity(lconvolution)（rnDeriv 版） | `MeasureTheory.conv_eq_withDensity_lconvolution_rnDeriv` | `RadonNikodym.lean:638` (mult `mconv_eq_withDensity_mlconvolution_rnDeriv`) | ✅ 既存 | step 2 別ルート |
| conv の HaveLebesgueDecomposition | `MeasureTheory.HaveLebesgueDecomposition.conv` | `RadonNikodym.lean:646` (mult) | ✅ 既存 | rnDeriv_conv' の前提供給 |
| lconvolution def | `MeasureTheory.lconvolution` (= `mlconvolution` to_additive、`⋆ₗ[μ]` 記法) | `Mathlib/Analysis/LConvolution.lean:50` (mult `mlconvolution`) | ✅ 既存 | mixture density の被積分形 |
| lconvolution 展開 | `MeasureTheory.lconvolution_def` | `LConvolution.lean:68` (mult `mlconvolution_def`) | ✅ 既存 | `(f ⋆ₗ[μ] g) x = ∫⁻ y, f y · g(−y+x) ∂μ`（= 多変量 mixture 積分） |
| lconvolution の可測性 | `MeasureTheory.measurable_lconvolution` | `LConvolution.lean` | ✅ 既存 | mixture density 可測 |
| `Fin n → ℝ` product withDensity | `InformationTheory pi_withDensity_fin` | `InformationTheory/Shannon/MultivariateDiffEntropy.lean:260` | ✅ 自作既存 | `∏ gaussianPDF = rnDeriv (Measure.pi 𝒩)` |

**完全 signature（additive、`#check` で verbatim 取得済）:**

```lean
-- RadonNikodym.lean:664 (additive to_additive of rnDeriv_mconv')
theorem rnDeriv_conv' {G : Type*} [AddGroup G] {mG : MeasurableSpace G}
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant] [SigmaFinite μ]
    {ν₁ ν₂ : Measure G} [SigmaFinite ν₁] [SigmaFinite ν₂]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ ⋆ₗ[μ] ν₂.rnDeriv μ

-- RadonNikodym.lean:638 (additive to_additive)
theorem conv_eq_withDensity_lconvolution_rnDeriv {G : Type*} [AddGroup G] {mG : MeasurableSpace G}
    [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant] [SFinite μ]
    {ν₁ ν₂ : Measure G} [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    ν₁ ∗ ν₂ = μ.withDensity (ν₁.rnDeriv μ ⋆ₗ[μ] ν₂.rnDeriv μ)

-- LConvolution.lean:68 (additive to_additive of mlconvolution_def)
theorem lconvolution_def {G : Type*} {mG : MeasurableSpace G} [Add G] [Neg G]
    {f g : G → ℝ≥0∞} {μ : Measure G} {x : G} :
    (f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (-y + x) ∂μ
```

**コンパイル証拠（`/tmp/test_inst3.lean`, `/tmp/test_inst4.lean`、project context で silent）:**

```lean
example (n : ℕ) (ν₁ ν₂ : Measure (Fin n → ℝ)) [SigmaFinite ν₁] [SigmaFinite ν₂]
    (h₁ : ν₁ ≪ volume) (h₂ : ν₂ ≪ volume) :
    (ν₁ ∗ ν₂).rnDeriv volume =ᵐ[volume]
      ν₁.rnDeriv volume ⋆ₗ[(volume : Measure (Fin n → ℝ))] ν₂.rnDeriv volume :=
  rnDeriv_conv' h₁ h₂                                    -- ✅ compiles
example (n : ℕ) (f g : (Fin n → ℝ) → ℝ≥0∞) (x : Fin n → ℝ) :
    (f ⋆ₗ[(volume : Measure (Fin n → ℝ))] g) x = ∫⁻ y, f y * g (-y + x) ∂volume := rfl  -- ✅
```

**Mathlib gap 判定:** **gap なし**。docstring `:1066-1074` の
「no corresponding multivariate mixture-density representation」「principled-impossible」は
**誤り**。`rnDeriv_conv'` がまさにその表現（lconvolution mixture density）を `Fin n → ℝ` + `volume` で供給。
ノイズ `ν₂ = Measure.pi (fun i => gaussianReal 0 (N i))` の rnDeriv は `pi_withDensity_fin` で
`z ↦ ∏ᵢ gaussianPDF 0 (N i) (z i)`（既存自作）。入力 `ν₁ = p`、`p ≪ volume` は
**相関入力では一般に成立しない**（後述・落とし穴①）— ここが唯一の本質的制約だが
回避可能（後述）。

**自作が必要な補題:** カテゴリ 2 単体では **0**（既存 API の組合せ）。

---

## カテゴリ 3 — `volume` on `Fin n → ℝ`（基盤）

| 概念 | Mathlib API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| `volume = Measure.pi (fun _ => volume)` | `MeasureTheory.volume_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:655` | ✅ 既存 | 既使用（`pi_absolutelyContinuous:172` 等） |
| product withDensity → 積密度 | `InformationTheory pi_withDensity_fin` | `MultivariateDiffEntropy.lean:260` | ✅ 自作既存 | noise rnDeriv = ∏ pdf |

`signature`:
```lean
-- Pi.lean:655
theorem volume_pi {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (α i)] :
    (volume : Measure (∀ i, α i)) = Measure.pi (fun i => volume)

-- MultivariateDiffEntropy.lean:260
theorem pi_withDensity_fin {n : ℕ} (ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (ν i)]
    {f : Fin n → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] :
    Measure.pi (fun i => (ν i).withDensity (f i))
      = (Measure.pi ν).withDensity (fun z => ∏ i, f i (z i))
```

**Mathlib gap 判定:** gap なし。**自作必要 0**。

---

## カテゴリ 4 — `Measure.pi` 上の lintegral / Fubini

| 概念 | Mathlib API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| `lintegral_eq_lintegral_pi`（pi Fubini） | `MeasureTheory.lintegral_eq_lintegral_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean` | ✅ 既存（loogle "Maybe you meant" 確認） | noise 積分の座標分解（直接は不要、lconvolution が吸収） |
| `lintegral_finset_prod` | `MeasureTheory.lintegral_finset_prod` | （loogle "Maybe you meant" = 存在） | ✅ 既存 | 必要時のみ |
| conv の lintegral Fubini | `Measure.lintegral_conv` | カテゴリ1 | ✅ 既存 | 主に使うのはこちら |

**Mathlib gap 判定:** gap なし。`rnDeriv_conv'` 経由なら pi Fubini を明示展開する必要すら薄い。**自作必要 0**。

---

## カテゴリ 5 — 多変量 Chebyshev / 集中

| 概念 | Mathlib API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| Markov 不等式 | `MeasureTheory.meas_ge_le_lintegral_div` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:104` | ✅ 既存・**`Fin n → ℝ` でそのまま使用可**（compile 済） | 各座標 `p{|xᵢ|>Rᵢ}` 集中 |
| EuclideanSpace L2 norm | `EuclideanSpace.norm_eq` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | ✅ 既存 | **不要**（座標箱で回避） |

**完全 signature（compile 確認、generic measure space）:**
```lean
-- Markov.lean:104
theorem meas_ge_le_lintegral_div {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
    μ {x | ε ≤ f x} ≤ (∫⁻ a, f a ∂μ) / ε
```

**落とし穴②（norm の選択）:** `Fin n → ℝ` の `‖·‖` は **sup norm**（Pi instance）であって
L2 ではない。よって 1-D 手本の `{|x| ≤ R}` ball を素朴に `{‖x‖ ≤ R}` に持ち上げると
`∑ᵢ (xᵢ)²` と直接つながらない。**回避策**: 集中集合を ball ではなく **座標箱**
`S = {x | ∀ i, |x i| ≤ Rᵢ}` に取る。power constraint は座標ごとの second moment
`∫ (xᵢ)² ∂p`（既に `parallelGaussianPowerConstraintSet_mem_iff_integrable:191` が供給）を与え、
`meas_ge_le_lintegral_div` を各座標に適用 → `p {|xᵢ| > Rᵢ} ≤ 1/(2n)` → 和集合補で
`p S ≥ 1/2`。EuclideanSpace を経由しないので `norm_sq_eq_inner` 不要。

**Mathlib gap 判定:** Markov は gap なし（generic）。**自作必要 = 座標箱 Chebyshev 補題 1 本**
（1-D `hSc_le`/`hS_ge`（`:458-494`）の n-座標 union-bound 版、~40-60 行）。

---

## カテゴリ 6 — rnDeriv of withDensity / pi

| 概念 | Mathlib API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| `rnDeriv_withDensity` | `MeasureTheory.Measure.rnDeriv_withDensity` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:590` | ✅ 既存 | 1-D `:415` で使用、多変量でも適用可 |
| `withDensity_rnDeriv_eq` | `MeasureTheory.Measure.withDensity_rnDeriv_eq` | （`pi_absolutelyContinuous:161` で使用） | ✅ 既存 | mixture density ↔ rnDeriv |
| `withDensity_absolutelyContinuous'`（a.e.≠0） | `MeasureTheory.withDensity_absolutelyContinuous'` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:564` | ✅ 既存 | reverse AC（既使用 `:204`） |

```lean
-- Lebesgue.lean:590
theorem Measure.rnDeriv_withDensity {α : Type*} {m : MeasurableSpace α} (ν : Measure α)
    [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f
```

**Mathlib gap 判定:** gap なし。**自作必要 0**。

---

## カテゴリ 7 — Gaussian PDF（包絡 building blocks）

| 概念 | Mathlib / InformationTheory API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| `gaussianPDF (= ofReal gaussianPDFReal)` | `ProbabilityTheory.gaussianPDF` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:157` | ✅ 既存 | noise 積密度の因子 |
| `gaussianPDFReal_pos` | `ProbabilityTheory.gaussianPDFReal_pos` | `Gaussian/Real.lean:61` | ✅ 既存 | 包絡下界 / 正値性（reverse AC、`:260` で使用） |
| `measurable_gaussianPDF` | `ProbabilityTheory.measurable_gaussianPDF` | `Gaussian/Real.lean`（loogle 確認） | ✅ 既存 | mixture density 可測 |
| `gaussianReal_of_var_ne_zero`（= withDensity 表現） | `ProbabilityTheory.gaussianReal_of_var_ne_zero` | `Gaussian/Real.lean:203` | ✅ 既存 | noise = withDensity（`:241` 使用） |
| `gaussianReal_absolutelyContinuous` | `ProbabilityTheory.gaussianReal_absolutelyContinuous` | `Gaussian/Real.lean:228` | ✅ 既存 | noise ≪ volume |
| **`gaussianPDFReal_le_sup`（上界 `≤(√2πv)⁻¹`）** | `InformationTheory (AWGN)` | `InformationTheory/Shannon/AWGN/CapacityConverseMaxent.lean:65` | ✅ 自作既存（1-D） | log 上界、座標ごとに適用 |

**Mathlib gap 判定:** 1-D Gaussian primitive は完全。多変量 product の
jointly-measurable / 上下界は **既存 1-D を座標で組むだけ**（`Finset.prod` + `gaussianPDFReal_le_sup` /
`gaussianPDFReal_pos`）。**自作必要 = Gaussian 積の quadratic 包絡補題 1 本**（次節）。

---

## カテゴリ 8 — power-constraint → second-moment 接続

| 概念 | InformationTheory API | file:line | 状態 | #5 での扱い |
|---|---|---|---|---|
| 座標ごと second-moment integrability + Bochner 和 | `parallelGaussianPowerConstraintSet_mem_iff_integrable` | `InformationTheory/Shannon/ParallelGaussian.lean:191` | ✅ 自作既存・sorryAx-free | 各座標 `∫(xᵢ)² ≤ P` → 座標箱 Chebyshev の入力 |
| constraint set 定義（lintegral 形） | `parallelGaussianPowerConstraintSet` | `ParallelGaussian.lean:175` | ✅ 自作既存 | `∑ᵢ ∫⁻ ofReal((xᵢ)²) ≤ ofReal P` |
| marginal の constraint 継承 | `parallelMarginal_mem_awgnPowerConstraintSet` | `ParallelGaussianConverse.lean:796` | ✅ 自作既存 | 座標箱 Chebyshev で各座標を 1-D に落とす場合に再利用可 |
| marginal = conv | `parallelOutput_marginal_eq_conv` | `ParallelGaussianConverse.lean:701` | ✅ 自作既存・sorryAx-free | joint conv 等式の建材 |

**完全 signature（建材）:**
```lean
-- ParallelGaussian.lean:191
theorem parallelGaussianPowerConstraintSet_mem_iff_integrable {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (p : Measure (Fin n → ℝ))
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    (∀ i, Integrable (fun x : Fin n → ℝ => (x i) ^ 2) p) ∧
      ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p ≤ P
```

**Mathlib gap 判定:** InformationTheory 内で完備。**自作必要 0**（建材として既存）。

---

## 主要前提条件ボックス（前提事故が起きやすい lemma）

- **`rnDeriv_conv'`** — `[μ.IsAddLeftInvariant]`（base measure 並進不変、`volume` でOK）+
  `[SigmaFinite μ]` + `[SigmaFinite ν₁]` `[SigmaFinite ν₂]` + `ν₁ ≪ μ` `ν₂ ≪ μ`。
  **ν₁ ≪ volume（= p ≪ volume）が落とし穴①** → 下記。
- **`conv_eq_withDensity_lconvolution_rnDeriv`** — `[SFinite μ]` + `[ν₁.HaveLebesgueDecomposition μ]`
  `[ν₂.HaveLebesgueDecomposition μ]` + `ν₁ ≪ μ` `ν₂ ≪ μ`。
- **`integrable_conv_iff`** — fibre integrability + 外側 fibre-norm integrability の連言（1-D `:170` 参照）。
- **`meas_ge_le_lintegral_div`** — `AEMeasurable f μ` + `ε ≠ 0` + `ε ≠ ∞`。座標 measure 上 generic。
- **`gaussianReal_of_var_ne_zero` / `gaussianReal_absolutelyContinuous`** — `v ≠ 0`（`hN` で供給）。

### 落とし穴①（最重要、設計分岐点）— `p ≪ volume` は相関入力で成立しない

`rnDeriv_conv' (h₁ : ν₁ ≪ μ) (h₂ : ν₂ ≪ μ)` は **両因子の AC** を要求する。
ノイズ `ν₂ = Measure.pi 𝒩 ≪ volume` は OK（`hN`、`pi_absolutelyContinuous` で既証明）だが、
**入力 `p` は power-constraint だけでは `p ≪ volume` を満たさない**（Dirac at 0 ∈ constraint set、
`p` は離散でも相関でも可）。1-D 手本 `output_eq_withDensity_mixture` (`:368`) はこの問題を
**`ν₂` 側の AC のみ**で回避している（mixture density = `∫⁻ x, gaussianPDF x N y ∂p`、`p` は
そのまま積分測度として残し AC 不要）。

→ **設計選択**: `rnDeriv_conv'`（両因子 AC 要求）を直接使わず、1-D 手本と同じく
**joint mixture density を手で定義** `f_Y(z) := ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p` し、
`μY = volume.withDensity f_Y` を `Measure.lintegral_conv` + `pi_withDensity_fin` で証明する方が
**`p` への AC 仮定が要らず素直**（1-D `output_eq_withDensity_mixture` の n版、~40-60 行）。
`rnDeriv_conv'` は「Mathlib に多変量 mixture density が無い」という wall 主張の **反証** としては
決定的だが、`p ≪ volume` を避けたいので実際の closure では withDensity-手定義ルートを推奨。
（補足: `μY ≪ volume` は `parallelOutput_absolutelyContinuous_volume:819` で既証明済なので
`μY.rnDeriv volume =ᵐ f_Y` は `output_rnDeriv_ae_mixture` 型で従う。）

---

## 自作が必要な要素（優先度順）

1. **`parallelOutput_joint_eq_withDensity_mixture`**（最優先、~40-60 行）
   `μY = volume.withDensity (fun z => ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p)`。
   推奨実装: 1-D `output_eq_withDensity_mixture` (`:368`) を n版に。`Measure.lintegral_conv`
   （Tonelli swap）+ `pi_withDensity_fin` で noise を積密度に。`p` の AC 不要。
   落とし穴: Fubini swap で `whnf` が `gaussianReal`/`gaussianPDFReal` を unfold して heartbeat
   timeout（1-D が `set g := …` で opaque 化、`:377`/`:501` 参照）— 同じく opaque local 必須。

2. **`parallelOutputMixture_log_abs_le`**（~50-80 行）
   `∃ c₀ c₁, 0 ≤ c₁ ∧ ∀ z, |log f_Y(z)| ≤ c₀ + c₁ ∑ᵢ (z i)²`。
   - 上界（容易）: 各座標 `gaussianPDFReal_le_sup` の積 → `∏ ≤ (∏(√2πNᵢ)⁻¹)`、`p` 確率測度。
   - 下界（★ hard）: 座標箱 Chebyshev で `p S ≥ 1/2`、`S` 上で各座標 Gaussian tail 下界
     `∏ᵢ gaussianPDF (x i)(N i)(z i) ≥ ∏ᵢ Kr(zᵢ)`（1-D `output_logDensity_lower_bound:440` の
     座標積）→ `f_Y(z) ≥ (1/2)∏Kr(zᵢ)` → quadratic `−log` 上界。
   工数: 1-D `output_logDensity_lower_bound`（~120 行）の n-座標版、最も重い。~80-120 行見込み。

3. **座標箱 Chebyshev 補題**（2 の内部、~40-60 行）
   `p {x | ∀ i, |x i| ≤ Rᵢ} ≥ 1/2`。各座標に `meas_ge_le_lintegral_div`
   （`ε = ofReal(Rᵢ²)`、`f = ofReal((xᵢ)²)`）+ union-bound（`measure_iUnion_le` / `Fin n`）。
   入力 = `parallelGaussianPowerConstraintSet_mem_iff_integrable` の per-coord second moment。

4. **`parallelOutput_joint_logDensity_integrable`（= #5 本体、~20-30 行）**
   1, 2 を `integrable_conv_iff` または直接 `Integrable.mono'`（`|log f_Y| ≤ c₀+c₁∑(zᵢ)²` が
   `μY` 上 integrable: 出力 second moment = `parallelOutput_centered_secondMoment_eq:1142` で各座標既証明）
   で締める。1-D consumer 構造（`outputDistribution_logDensity_integrable_joint` 型）に対応。

**合計工数感:** ~180-270 行。docstring の "~150-250 line" 見積りと整合だが、
**「原理的困難」ではなく「1-D 手本の座標積版」= big-but-mechanical**。最重いのは項目 2 の下界。

---

## Mathlib 壁の列挙（真の不在）

**真に Mathlib 不在で `@residual(wall:*)` 相当のものは 0 件**（このスコープに限れば）。

- multivariate mixture density: **不在ではない** — `rnDeriv_conv'`（`RadonNikodym.lean:664`）が供給。
  loogle: `MeasureTheory.rnDeriv_conv'` = `Found one declaration`、`#check` + project context compile
  で `Fin n → ℝ`/`volume` 適用確認済。
- joint conv 出力等式 / quadratic 包絡 / 座標箱 Chebyshev: いずれも **Mathlib 不在だが
  InformationTheory 自作タスク**（1-D 手本 + 既存 helper の座標積）。`wall` ではなく `plan`/`self-buildable`。

→ **共有 sorry 補題化候補:** なし（#5 は単独 leaf、他 file に同型壁は散在していない）。

---

## 撤退ラインへの距離

親計画 [`parallel-gaussian-converse-closure-plan.md`] の撤退ラインに対し:

- **発動: no。** #5 は「縮退して逃げる」対象ではなく「自作で閉じられる」leaf。
- むしろ **逆方向の修正提案**: コード docstring（`ParallelGaussianConverse.lean:1059-1091`）の
  `wall:multivariate-mi` 分類は **overstated**。「principled-impossible factorization」は
  `rnDeriv_conv'` の存在で反証される。これは tier-4/tier-5 寄りの **classification defect 候補**
  （`wall` と書いてあるが実は self-buildable）。CLAUDE.md「検証の誠実性 → 『Mathlib 壁』の誤用:
  実は選択（big）を blocked（hard）と偽る」に該当する可能性。
  **本 inventory は分類の再評価材料を提示するのみ**（docstring 書換は実装/監査 task の責務）。
  推奨: honesty-auditor に「`wall:multivariate-mi` vs `plan:parallel-gaussian-converse-closure`
  の再判定」を回す。

新規撤退ライン提案（万一 項目 2 下界が想定超過した場合）:
- 着手 1 週で `parallelOutputMixture_log_abs_le` の **下界**が書けない場合
  → 上界のみ（log 上界 = `negMulLog` 側）+ 下界は `@residual(plan:parallel-joint-lower-envelope)`
    の sorry leaf に細分化して分割 commit（撤退口は sorry + `@residual`、仮説束化禁止）。

---

## #5 closure に向けた建材マップ（1-D 手本 → 多変量）

| 1-D lemma (file:line) | 多変量版の入手手段 | 判定 |
|---|---|---|
| `outputMixtureDensity:338`（scalar mixture def） | `fun z => ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p` を def | ② 自作（def、~5 行） |
| `output_eq_withDensity_mixture:368` | `Measure.lintegral_conv`(既) + `pi_withDensity_fin`(既) | ② 自作（~40-60 行、Fubini opaque-g 必須） |
| （別ルート確認）`rnDeriv_conv':664` | Mathlib そのまま（ただし `p≪volume` 要、回避推奨） | ① そのまま使える（wall 反証用） |
| `output_rnDeriv_ae_mixture:409` | `rnDeriv_withDensity`(既) + 上の withDensity 等式 | ① ほぼそのまま（~5 行） |
| `outputMixtureDensity_le_sup:420` | `gaussianPDFReal_le_sup`(既) の `Finset.prod` | ② 自作（容易、~15 行） |
| `output_logDensity_lower_bound:440`（★唯一の hard） | 座標箱 Chebyshev（`meas_ge_le_lintegral_div`(既)） + Gaussian tail 座標積 | ② 自作（最重、~80-120 行）— 原理的困難では**ない** |
| `outputMixtureDensity_log_abs_le:557` | 上下界の合成 | ② 自作（~20 行） |
| consumer `output_sq_sub_integrable:162` / joint integrable | `integrable_conv_iff`(既) + `parallelOutput_centered_secondMoment_eq:1142`(既) | ① ほぼそのまま（~20-30 行） |

**③ 原理的に困難: 0 件。** 全項目が ①（既存 API）か ②（1-D 手本の座標積、mechanical）。

---

## 着手 skeleton（参考、実装 task が書く）

```lean
import InformationTheory.Shannon.ParallelGaussianConverse
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace InformationTheory.Shannon.ParallelGaussian

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {n : ℕ} (N : Fin n → ℝ≥0)
  (h_meas : IsParallelAwgnChannelMeasurable N)
  (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
  (p : Measure (Fin n → ℝ))

/-- 多変量 mixture density: f_Y(z) = ∫⁻ x, ∏ᵢ gaussianPDF (x i)(N i)(z i) ∂p. -/
noncomputable def parallelOutputMixtureDensity (z : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Fin n → ℝ, ∏ i, gaussianPDF (x i) (N i) (z i) ∂p

/-- μY = volume.withDensity (mixture). 1-D output_eq_withDensity_mixture の n版。 -/
theorem parallelOutput_eq_withDensity_mixture (hN : ∀ i, (N i : ℝ) ≠ 0) [SFinite p] :
    outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)
      = volume.withDensity (parallelOutputMixtureDensity N p) := by
  sorry  -- @residual(plan:parallel-gaussian-converse-closure)

/-- |log f_Y| ≤ c₀ + c₁ ∑ᵢ(zᵢ)². 上界=積 sup、下界=座標箱 Chebyshev + Gaussian tail. -/
theorem parallelOutputMixture_log_abs_le (P : ℝ) (hP : 0 ≤ P) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (hp : p ∈ parallelGaussianPowerConstraintSet P) [IsProbabilityMeasure p] :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ z : Fin n → ℝ,
      |Real.log ((parallelOutputMixtureDensity N p z).toReal)| ≤ c₀ + c₁ * ∑ i, (z i) ^ 2 := by
  sorry  -- @residual(plan:parallel-gaussian-converse-closure)

end InformationTheory.Shannon.ParallelGaussian
```
