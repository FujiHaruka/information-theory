# AWGN Achievability typicality — Mathlib inventory (Axis 2: continuous AEP / n-dim Gaussian SLLN)

> **Scope**: Phase 0 inventory for **Axis 2** of
> [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md).
> Axis 2 is the decisive axis for **判断 #1** (T-2 採用 / 不採用): does Mathlib carry
> enough infrastructure to discharge the 3 continuous AEP bounds (B-2, B-3, B-4) of
> Cover-Thomas 9.2 directly, or do we need to externalize them as the regularity
> hypothesis `IsContinuousAEPGaussian P N`?
>
> Sibling axes (Axis 1 codebook / Axis 3 union bound / Axis 4 expurgation / Axis 5
> shell volume) are tracked in separate per-axis inventory files. This file only
> covers SLLN + 1-d Gaussian moments + n-dim lifting + log-composition.
>
> **Source-of-truth lemma format** (CLAUDE.md「Subagent Inventory of Mathlib
> Lemmas」厳守): `file:line` + 完全 signature (`[...]` ブラケット verbatim、paraphrase 禁止) + conclusion form verbatim.

## 一行サマリ

**T-2 採用 (最有力)**. Mathlib に SLLN 単体 (`strong_law_ae` / `strong_law_ae_real`) と 1-d
Gaussian の `MemLp_p` (`memLp_id_gaussianReal'`) と `Filter.Tendsto.log` は全て揃って
おり、原理的には B-2 (joint typical → 1) を `(1/n) log p(X^n,Y^n) → h(X,Y)` の形で
本物 discharge できる。しかし **n-dim Gaussian SLLN を 1 本で出す lemma**、**continuous
AEP / SMB を直接結論する lemma**、**typical set volume bound (B-3) を Lebesgue 測度に
持っていく統合 lemma** はいずれも Mathlib 不在 + InformationTheory 不在。Phase B 全体を本物
discharge すると 200-400 行の自作。Phase A/C/D との合計が 700 行超に膨らむと撤退ライン
T-4 (plan 2 分割) を発動する確率が中-高。**T-2 採用 (`IsContinuousAEPGaussian P N` を
regularity hyp 化、achievability core は Phase C-D で genuine 維持) が Phase 0 中央
判断**。

## 主定理の最終形 (再掲、本 plan §Goal より)

```lean
namespace InformationTheory.Shannon.AWGN

/-- F-1 撤退ラインの本物 discharge (Cover-Thomas 9.2 の Lean 化)。
T-2 採用時は signature に `(h_aep : IsContinuousAEPGaussian P N)` が 1 本残る。 -/
theorem isAwgnTypicalityHypothesis (P : ℝ) (hP : 0 < P) (N : ℝ≥0)
    (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (h_aep : IsContinuousAEPGaussian P N) :
    IsAwgnTypicalityHypothesis P N h_meas
```

**証明戦略** (Cover-Thomas 9.2、Lean 4 pseudo-code):

```
1. construct gaussianCodebook M n (P-δ)                       -- Phase A
2. obtain joint typical set A_ε^{(n)} ⊆ ℝⁿ × ℝⁿ (Phase B-1)   -- Phase B (T-2 hyp/直 discharge)
3. obtain 3 AEP bounds B-2/B-3/B-4 from h_aep or SLLN+ε       -- Phase B
4. union bound: Pe_avg ≤ ε + (M-1)·exp(-n(I-3ε)) ≤ 2ε         -- Phase C
5. expurgate: ∃ codebook with Pe_max ≤ 4ε                     -- Phase D
6. translate to AwgnCode + power constraint                   -- Phase D
7. integrate to isAwgnTypicalityHypothesis                    -- Phase E
```

T-2 採用時のみ Step 2-3 が hyp 経由、Step 1, 4-7 は本物 discharge を維持。これにより
achievability core (codebook + union bound + expurgation) は genuine、AEP gap のみが
load-bearing でない regularity hyp として残る (CLAUDE.md「regularity hyp の 3 条件」を
満たす)。

---

## API 在庫テーブル (カテゴリごと)

凡例 **状態**:
- **🟢 既存**: そのまま usable
- **🟡 部分**: 一部前提条件・形が合わない、要 bridge
- **🔴 不在**: Mathlib + InformationTheory ともに無し、自作必要

### Cat-1 SLLN 系 (Mathlib `Probability/StrongLaw.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase B での扱い |
|---|---|---|---|---|
| 1-d 実数 SLLN (Etemadi) | `ProbabilityTheory.strong_law_ae_real` | `Mathlib/Probability/StrongLaw.lean:598` | 🟢 | B-2 で `X_i²` / `log p(X_i)` 系の i.i.d. avg → expectation の base |
| Banach-valued SLLN | `ProbabilityTheory.strong_law_ae` | `Mathlib/Probability/StrongLaw.lean:788` | 🟢 (使うなら `[BorelSpace E]`) | n-dim SLLN を `EuclideanSpace ℝ (Fin n)` で一発でやりたいなら候補。ただし B-2 の最終形は scalar、coordinate-wise + Tendsto.add で十分 |
| L^p SLLN | `ProbabilityTheory.strong_law_Lp` | `Mathlib/Probability/StrongLaw.lean:832` | 🟢 | 本 Phase で直は不使用 (a.s. 版で足りる) |
| 確率収束への落とし込み | `MeasureTheory.tendstoInMeasure_of_tendsto_ae` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223` | 🟢 (`[IsFiniteMeasure μ]`) | B-2 で a.s. → in-prob → P[typical] → 1 への変換 |
| pairwise-indep + identDistrib lifting | `ProbabilityTheory.IdentDistrib.comp` | `Mathlib/Probability/IdentDistrib.lean:` (loogle 経由確認済) | 🟢 | i.i.d. の `X_i² ↦ logPDF(X_i)` 経由 ident lifting |

#### `ProbabilityTheory.strong_law_ae_real`

- **file:line**: `Mathlib/Probability/StrongLaw.lean:598`
- **signature** (verbatim):
  ```lean
  theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
      (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0])
  ```
- **type-class prerequisites**: なし(明示)。`IsProbabilityMeasure` は本体内で由来 (`Integrable + IndepFun + not-all-zero` から導出) — つまり外側で `IsProbabilityMeasure` 仮定不要
- **explicit args**: `X : ℕ → Ω → ℝ`, `hint : Integrable (X 0) μ`, `hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)`, `hident : ∀ i, IdentDistrib (X i) (X 0) μ μ`
- **conclusion**: `∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0])`
- **applicability to 軸 2**: B-2 の SLLN base。`X_i := |Y_i|²` (Y i.i.d. Gaussian) や
  `X_i := -log gaussianPDFReal 0 v (Y_i)` を入れることで `(1/n) ∑ X_i ω → 𝔼[X_0]` を a.s. に得る。
  `Pairwise IndepFun + IdentDistrib` の 2 仮定が必要、Phase A の `gaussianCodebook` 構造から導出可能。

#### `ProbabilityTheory.strong_law_ae`

- **file:line**: `Mathlib/Probability/StrongLaw.lean:788`
- **signature** (verbatim、`omit [IsProbabilityMeasure μ]` 含む):
  ```lean
  variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
  omit [IsProbabilityMeasure μ] in
  theorem strong_law_ae (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])
  ```
- **type-class prerequisites**: `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`,
  `[CompleteSpace E]`, `[MeasurableSpace E]`, `[BorelSpace E]`
- **explicit args**: 同上 + `E`-valued
- **conclusion**: `∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])`
- **applicability to 軸 2**: もし「n 次元 Gaussian ベクトル `Y_i ∈ EuclideanSpace ℝ (Fin n)`
  の i.i.d. sample」を一発で SLLN したいなら本定理。ただし B-2 で必要なのは sample
  サイズ k 方向の平均 (n は固定)、scalar 集約 `(1/n) ∑ X_i²` の形。Banach 形は不要、
  scalar 版で十分。**重要な前提**: `[BorelSpace E]` 要求 — `EuclideanSpace ℝ (Fin n)` は
  Borel space なので OK だが、`(Fin n → ℝ)` ではなく Euclidean 版を使う必要あり。

#### `MeasureTheory.tendstoInMeasure_of_tendsto_ae`

- **file:line**: `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223`
- **signature** (verbatim):
  ```lean
  theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ] (hf : ∀ n, AEStronglyMeasurable (f n) μ)
      (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g
  ```
- **type-class prerequisites**: `[IsFiniteMeasure μ]`
- **applicability to 軸 2**: B-2 で a.s. SLLN を `P[|(1/n) log p - h| < ε] → 1` に変換。
  `gaussianCodebook` は `IsProbabilityMeasure` (Phase A で構築) なので `[IsFiniteMeasure]` OK。

---

### Cat-2 1-d Gaussian の Integrable/MemLp (Mathlib `Probability/Distributions/Gaussian/Real.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase B での扱い |
|---|---|---|---|---|
| `gaussianReal μ v` 定義 | `ProbabilityTheory.gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:200` | 🟢 | Phase A codebook の各座標 marginal |
| `gaussianPDFReal` 定義 | `ProbabilityTheory.gaussianPDFReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:48` | 🟢 | B-2 の `log p(X_i)` 展開で使う |
| `IsProbabilityMeasure` instance | `ProbabilityTheory.instIsProbabilityMeasureGaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:209` | 🟢 | SLLN の前提 |
| `rnDeriv = gaussianPDF` | `ProbabilityTheory.rnDeriv_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:240` | 🟢 | B-2/B-3 の `(1/n) log p(X^n)` を pdf 形で展開 |
| `MemLp id p`(任意 p) | `ProbabilityTheory.memLp_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:548` | 🟢 | B-2 で `X_i^2` の SLLN を起動するための `Integrable` 由来 |
| `MemLp id p`(`ℝ≥0∞`) | `ProbabilityTheory.memLp_id_gaussianReal'` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:553` | 🟢 | 同上 (より柔軟) |
| `E[X]=m` | `ProbabilityTheory.integral_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:508` | 🟢 | SLLN の極限の同定 |
| `Var[X]=v` (with `μ` 引数) | `ProbabilityTheory.variance_fun_id_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:518` | 🟢 | `E[X²] = v + m²` 経由で SLLN 極限を `(P-δ) + 0` に同定 |
| `Var = E[X²] - E[X]²` | `ProbabilityTheory.variance_eq_sub` | `Mathlib/Probability/Moments/Variance.lean:225` (`[IsProbabilityMeasure μ]`) | 🟢 | `E[X²]` 直接計算の bridge |

#### `ProbabilityTheory.gaussianPDFReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:48`
- **signature** (verbatim):
  ```lean
  noncomputable
  def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
    (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))
  ```
- **type-class prerequisites**: なし
- **explicit args**: `μ : ℝ`, `v : ℝ≥0`, `x : ℝ`
- **conclusion (定義値)**: `(√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))`
- **applicability to 軸 2**: B-2 において `-log p(X_i) = (1/2) log (2πv) + (X_i - μ)²/(2v)`
  に展開し、SLLN を `(X_i - μ)²` に適用する道筋を作る上で必須。

#### `ProbabilityTheory.memLp_id_gaussianReal'`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:553`
- **signature** (verbatim):
  ```lean
  lemma memLp_id_gaussianReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (gaussianReal μ v)
  ```
- **type-class prerequisites**: なし(implicit `μ v`)
- **explicit args**: `p : ℝ≥0∞`, `hp : p ≠ ∞`
- **conclusion**: `MemLp id p (gaussianReal μ v)`
- **applicability to 軸 2**: `p = 2` で `MemLp id 2 (gaussianReal m v)`、`MemLp.integrable_sq`
  等を通じて `Integrable (· ^ 2)` を得る道。B-2 で `X_i²` を SLLN にかける Integrable
  仮定の base。

#### `ProbabilityTheory.variance_fun_id_gaussianReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:518`
- **signature** (verbatim):
  ```lean
  @[simp]
  lemma variance_fun_id_gaussianReal : Var[fun x ↦ x; gaussianReal μ v] = v
  ```
- **type-class prerequisites**: なし(implicit `μ v`)
- **conclusion**: `Var[fun x ↦ x; gaussianReal μ v] = v`
- **applicability to 軸 2**: `m = 0` の場合は `E[X²] = v` に直結。B-2 の SLLN 極限値を
  `v` に同定する。

#### `ProbabilityTheory.variance_eq_sub`

- **file:line**: `Mathlib/Probability/Moments/Variance.lean:225`
- **signature** (verbatim):
  ```lean
  theorem variance_eq_sub [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
      Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2
  ```
- **type-class prerequisites**: **`[IsProbabilityMeasure μ]`** ← Phase A の codebook 構築で
  確保される
- **applicability to 軸 2**: SLLN 極限 `μ[X²]` を `Var + (E[X])² = v + m²` に同定する bridge。

---

### Cat-3 n-dim Gaussian / Multivariate / EuclideanSpace (Mathlib `Probability/Distributions/Gaussian/Multivariate.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase B での扱い |
|---|---|---|---|---|
| `stdGaussian E` 定義 | `ProbabilityTheory.stdGaussian` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:66` | 🟢 | T-1 採用時の codebook flatten 候補。`E := EuclideanSpace ℝ (Fin (M*n))` |
| `stdGaussian` 確率測度 | `ProbabilityTheory.isProbabilityMeasure_stdGaussian` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:72` | 🟢 (`[BorelSpace E]`) | 同上 |
| `multivariateGaussian μ S` 定義 | `ProbabilityTheory.multivariateGaussian` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:168` | 🟢 (`[DecidableEq ι]`) | 一般 covariance の n-d Gaussian、B-2/B-3 で AWGN joint $(X,Y)$ の構築候補 |
| 1-d marginal が `gaussianReal` | `ProbabilityTheory.measurePreserving_eval_multivariateGaussian` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:229` | 🟢 (`hS : S.PosSemidef`) | n-d Gaussian の各座標 marginal を 1-d Gaussian に reduce、SLLN 起動 |
| Pi version = stdGaussian | `ProbabilityTheory.map_pi_eq_stdGaussian` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:137` | 🟢 | `Measure.pi` 形と `stdGaussian` 形の bridge、Axis 1 (codebook) で利用 |
| `IsGaussian.integrable_id` | `ProbabilityTheory.IsGaussian.integrable_id` | `Mathlib/Probability/Distributions/Gaussian/Fernique.lean:205` | 🟢 (`[CompleteSpace E]`, `[SecondCountableTopology E]`, `[IsGaussian μ]`) | n-d 版で `‖X‖` の Integrable を確保 |
| `IsGaussian.memLp_id` | `ProbabilityTheory.IsGaussian.memLp_id` | `Mathlib/Probability/Distributions/Gaussian/Fernique.lean:186` | 🟢 (`[CompleteSpace E]`, `[SecondCountableTopology E]`, `[IsGaussian μ]`) | n-d 版で `‖X‖^p` の MemLp 保証、Banach SLLN 起動 |
| n-d Gaussian density (rnDeriv vs Lebesgue) | — | — | 🔴 | **Mathlib に存在せず**。`stdGaussian E` や `multivariateGaussian μ S` の `rnDeriv` を 1-d 形式で書く `multivariateGaussianPDF` 系は無し。B-3 (volume bound) の自作必要箇所 |
| n-d differential entropy | — | — | 🔴 | InformationTheory にも n-d 版なし。1-d しかない (`InformationTheory/Shannon/DifferentialEntropy.lean`)。本物 discharge には自作必要 |

#### `ProbabilityTheory.measurePreserving_eval_multivariateGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:229`
- **signature** (verbatim):
  ```lean
  lemma measurePreserving_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
      MeasurePreserving (fun x ↦ x i) (multivariateGaussian μ S)
        (gaussianReal (μ i) (S i i).toNNReal)
  ```
- **type-class prerequisites**: 暗黙的に `[Fintype ι]`, `[DecidableEq ι]` (file-level
  `variable`), `hS : S.PosSemidef`
- **explicit args**: `hS : S.PosSemidef`, `{i : ι}`
- **conclusion**: `MeasurePreserving (fun x ↦ x i) (multivariateGaussian μ S) (gaussianReal (μ i) (S i i).toNNReal)`
- **applicability to 軸 2**: AWGN joint $(X_i, Y_i)$ の n-d Gaussian を構築できれば、
  各座標 evaluation が 1-d Gaussian、`strong_law_ae_real` を coordinate-wise に起動可。
  **ただし Axis 1 で AWGN joint を `multivariateGaussian` 形に流し込めるかが課題**
  (AWGN は加法 noise なので `(X, X+N)` の共分散行列を作る必要、行列代数 + PosSemidef 仮定が
  Phase A で plumbing コストになる)。

---

### Cat-4 `Real.log` / log-composition (Mathlib `Analysis/SpecialFunctions/Log/Basic.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase B での扱い |
|---|---|---|---|---|
| `Tendsto f → Tendsto (log ∘ f)` | `Filter.Tendsto.log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:471` | 🟢 (要 `x ≠ 0` at limit) | SLLN `(1/n) ∑ X_i² → v` を `log ((1/n) ∑ X_i²) → log v` に持っていく場合 (但し B-2 は log の外側に SLLN 起動するルートが標準) |
| `Real.continuous_log` | `Real.continuous_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:` (周辺) | 🟢 | continuity 経由の代替 |
| `Tendsto.add` (Finset 合成) | `tendsto_finsetSum` | `Mathlib/Topology/Algebra/Monoid.lean:917` | 🟢 | coordinate-wise SLLN を n-d に持ち上げる:各座標 SLLN → ∑ で 1 つの Tendsto |
| `ae_all_iff` | `ae_all_iff` | `Mathlib/MeasureTheory/OuterMeasure/AE.lean:95` (`[Countable ι]`) | 🟢 | n 座標を `[Fintype (Fin n)]` で countable に通して `∀ᵐ ω, ∀ i, ...` を `∀ i, ∀ᵐ ω, ...` に交換、`Tendsto.add` で集約 |
| direct `(1/n) log p(X^n) → h(X)` 系 | — | — | 🔴 | **Mathlib 不在**。差分: log を SLLN の外で / 中で / pdf 展開して個別に処理、いずれにせよ自作 ~40-80 行 |

#### `Filter.Tendsto.log`

- **file:line**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:471`
- **signature** (verbatim):
  ```lean
  theorem Filter.Tendsto.log {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
      Tendsto (fun x => log (f x)) l (𝓝 (log x))
  ```
- **type-class prerequisites**: なし
- **explicit args**: `(h : Tendsto f l (𝓝 x))`, `(hx : x ≠ 0)`
- **conclusion**: `Tendsto (fun x => log (f x)) l (𝓝 (log x))`
- **applicability to 軸 2**: B-2 で `log` を SLLN の外に動かす場合の sealing。B-2 直接ルート
  (= `Real.log (gaussianPDFReal 0 v (X_i))` を `c + (X_i - 0)² / (2v)` に展開) のほうが
  推奨 — `Tendsto.log` は `f → 0` の場合を扱えないので `(1/n) ∑ log p(X_i)` 形を直接
  扱う方が安全。

#### `tendsto_finsetSum`

- **file:line**: `Mathlib/Topology/Algebra/Monoid.lean:917`
- **signature** (verbatim):
  ```lean
  @[to_additive]
  theorem tendsto_finsetProd {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
      (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
        Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c))
  ```
- **type-class prerequisites**: `[CommMonoid M]`, `[TopologicalSpace M]`, `[ContinuousMul M]` (file-level)
- **applicability to 軸 2**: n 個の 1-d SLLN を結合して n-d 形を作る canonical 経路。
  各座標の `Tendsto ((1/k) ∑_{j=1}^k X_{i,j}²) ((P-δ))` を Finset.range n 上で sum。

---

### Cat-5 `differentialEntropy` AEP 系 (InformationTheory 既存 / Mathlib gap)

| 概念 | API | file:line | 状態 | Phase B での扱い |
|---|---|---|---|---|
| 1-d `differentialEntropy` 定義 | `InformationTheory.Shannon.differentialEntropy` | `InformationTheory/Shannon/DifferentialEntropy.lean:42` | 🟢 (InformationTheory) | Gaussian の場合の値 `(1/2) log (2πe v)` を `differentialEntropy_gaussianReal` で取得 |
| 1-d Gaussian entropy 値 | `InformationTheory.Shannon.differentialEntropy_gaussianReal` | `InformationTheory/Shannon/DifferentialEntropy.lean:406` | 🟢 (InformationTheory) | B-3 で SLLN 極限を `(1/2) log (2πe v)` に同定 |
| n-d differential entropy 定義 | — | — | 🔴 | InformationTheory にも n-d 版なし、joint entropy `h(X^n, Y^n)` を直接扱える Mathlib-shape predicate は無い。B-3 直 discharge には自作 ~50-100 行 |
| (1/n) log p(X^n) → h(X) 連続 AEP | — | — | 🔴 | Mathlib 全体に **continuous AEP** 単体定理は存在せず。discrete 版 `aep_ae` (InformationTheory) を continuous に転用するには `[Fintype α]` を外す必要があり、`logLikelihood` も `(μ.map X).real {x}` から `rnDeriv` 経由に書き換える必要、API 不適合 |
| Shannon-McMillan-Breiman (continuous) | — | — | 🔴 | Mathlib 不在、InformationTheory にも discrete sandwich のみ (`ShannonMcMillanBreiman.lean`, `[Fintype α]` 要求) |
| KL divergence | `InformationTheory.klDiv` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` (29 lemma 群) | 🟢 (Mathlib) | 代替 AEP 経路の候補 (`klDiv` の Phase B-4 (indep-product) への活用は理論可能、ただし achievability に近づく 30-60 行 bridge が要る) |

#### `InformationTheory.Shannon.differentialEntropy`

- **file:line**: `InformationTheory/Shannon/DifferentialEntropy.lean:42`
- **signature** (verbatim):
  ```lean
  noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
    ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
  ```
- **type-class prerequisites**: なし(明示)、Measure ℝ の `rnDeriv volume` を `.toReal` で取り
  Bochner 実数値積分
- **applicability to 軸 2**: B-3 で 1-d marginal の entropy を取得、coordinate-wise + sum
  で n-d joint entropy の上から評価。**ただし定義は 1-d 限定**、n-d 版を自作する場合は
  `Measure (Fin n → ℝ)` で同型に書き直すコストが Phase B-3 の主要部分。

#### `InformationTheory.Shannon.differentialEntropy_gaussianReal`

- **file:line**: `InformationTheory/Shannon/DifferentialEntropy.lean:406`
- **signature** (verbatim):
  ```lean
  theorem differentialEntropy_gaussianReal
      (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      differentialEntropy (gaussianReal m v)
        = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
  ```
- **type-class prerequisites**: なし
- **explicit args**: `m : ℝ`, `{v : ℝ≥0}`, `hv : v ≠ 0`
- **conclusion**: `differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`
- **applicability to 軸 2**: 各座標 marginal の entropy が `(1/2) log (2πe v)` であることを
  使う key lemma。

#### `InformationTheory.klDiv` (代替ルート)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` (loogle: 29 lemma 群、`klDiv` 本体)
- **applicability to 軸 2**: B-4 (`P[(X', Y) ∈ A_ε]` の indep-product 上界) を
  `klDiv (μ ⊗ ν) (joint) ≥ ...` の form で書ければ regularity を介さず直接得られる可能性。
  ただし Cover-Thomas 9.2 経路と非標準、bridge 30-60 行 + 個別検証必要。**最有力ルートではない**。

---

### Cat-6 `iIndepFun` / `Measure.pi` infrastructure (Mathlib `Probability/Independence/Basic.lean`)

| 概念 | Mathlib API | file:line | 状態 | Phase B での扱い |
|---|---|---|---|---|
| pi-measure of iid → iIndepFun | `ProbabilityTheory.iIndepFun_pi` | `Mathlib/Probability/Independence/Basic.lean:784` | 🟢 (`[∀ i, IsProbabilityMeasure (μ i)]`) | Phase A の codebook で「同じ word 内の sample が iid」を確立、SLLN の indep 仮定に変換 |
| ae_all_iff (countable lifting) | `ae_all_iff` | `Mathlib/MeasureTheory/OuterMeasure/AE.lean:95` | 🟢 (`[Countable ι]`) | n 座標 `Fin n` は countable、各座標で a.s. を `∀ᵐ ω, ∀ i, ...` に集約 |

#### `ProbabilityTheory.iIndepFun_pi`

- **file:line**: `Mathlib/Probability/Independence/Basic.lean:784`
- **signature** (verbatim):
  ```lean
  variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
      {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
      {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : (i : ι) → Ω i → 𝓧 i}
  lemma iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
      iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)
  ```
- **type-class prerequisites**: **`[Fintype ι]`, `[∀ i, MeasurableSpace (Ω i)]`,
  `[∀ i, IsProbabilityMeasure (μ i)]`, `[∀ i, MeasurableSpace (𝓧 i)]`**
- **explicit args**: `mX : ∀ i, AEMeasurable (X i) (μ i)`
- **conclusion**: `iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)`
- **applicability to 軸 2**: Phase A の `gaussianCodebook` が `Measure.pi (gaussianReal 0 v)`
  形なら、座標投影が iIndepFun になる。SLLN の `Pairwise IndepFun` 仮定への変換は
  `iIndepFun.indepFun (Set.pairwise_univ.symm)` 等で 1-2 行。

---

## 主要前提条件ボックス (使用時に注意)

- **`strong_law_ae_real`** は `[IsProbabilityMeasure μ]` を**外側に要求しない** — Integrable +
  Pairwise IndepFun + IdentDistrib から本体内で導出される。**ただし `μ ≠ 0` の場合のみ**、
  `X 0` が all-zero でない (= `IdentDistrib` 経由で 0 でない法則) という条件は必要。
  AWGN codebook 系 `gaussianReal 0 (P-δ)` で `P-δ > 0` なら自動成立。

- **`strong_law_ae` (Banach 版)** は `[BorelSpace E]` を要求 — `EuclideanSpace ℝ (Fin n)` は
  OK、しかし生 `Fin n → ℝ` (product topology) は `BorelSpace` が pi-borel と一致するか
  type-class が立たないことがある。**Phase A の codebook 型選択 (判断 #2) に直結**。

- **`tendstoInMeasure_of_tendsto_ae`** は `[IsFiniteMeasure μ]` 要求 — `IsProbabilityMeasure`
  から自動 derive される (`IsProbabilityMeasure ≤ IsFiniteMeasure`)。

- **`variance_eq_sub`** は `[IsProbabilityMeasure μ]` を要求 — finite measure では不十分。

- **`iIndepFun_pi`** は `[∀ i, IsProbabilityMeasure (μ i)]` を要求 — `gaussianReal 0 v` は
  確率測度なので OK。

- **`measurePreserving_eval_multivariateGaussian`** は `hS : S.PosSemidef` を要求 — AWGN joint
  $(X, Y) = (X, X+N)$ の共分散行列 `[[P-δ, P-δ]; [P-δ, P-δ+N]]` が PosSemidef であること
  の証明が Axis 3 (B-4) で約 20 行必要。

- **`IsGaussian.memLp_id` / `integrable_id`** は `[CompleteSpace E]`, `[SecondCountableTopology E]`,
  `[IsGaussian μ]` 全て要求 — `EuclideanSpace ℝ (Fin n)` は満足、`(Fin n → ℝ)` (raw pi) は
  CompleteSpace / SecondCountableTopology は OK だが `IsGaussian` instance を `Measure.pi` から
  作る lemma が見当たらない (Phase A の判断 #2 で `EuclideanSpace` flatten を強く推奨)。

---

## 自作が必要な要素 (T-2 採用 / 不採用 に分けて整理)

### T-2 採用時 (Phase B が ~50 行に縮退、推奨)

優先度 **高**:

1. **`IsContinuousAEPGaussian P N : Prop` 定義** (Phase B-0、`~30-50 行`)
   - 3 AEP bound (B-2/B-3/B-4) を 1 つの bundle に packaging
   - 結論型 ≠ `IsAwgnTypicalityHypothesis` を厳守 (honesty 必須条件)
   - docstring で "Mathlib gap, NOT load-bearing for achievability core" を明記
   - 落とし穴: bundle 中身が「∃ codebook, ∀ m, errorProb < ε」 を含むと conclusion-as-hypothesis
     になる ⇒ AEP **そのもの** (entropy convergence) のみを packing、achievability の
     構造 (codebook / decoder / Pe_max) は含めない

優先度 **中**:

2. **AWGN joint $(X, Y) = (X, X+N)$ の 1-d Gaussian 構築** (Phase A で part、~20 行)
   - `Measure.pi (gaussianReal 0 (P-δ))` × push-forward で `(X, X+N)` を作る
   - これは `IsContinuousAEPGaussian` を起動するための前段で、Phase B 内で完了

優先度 **低 (T-2 採用なら回避)**:

- n-d differential entropy 定義
- Continuous SMB 系
- 直 `(1/n) log p(X^n) → h(X)` 補題

### T-2 不採用時 (Phase B 200-400 行、本物 discharge)

優先度 **高**:

1. **B-2 (P[typical] → 1) 本物 discharge** (~150 行)
   - 直接 `(1/n) ∑ log p(X_i, Y_i)` を SLLN に流す経路:
     - 1-d `log p(X_i)`: pdf 展開 → `c₁ + (X_i - m)² / (2v)`
     - SLLN を `(X_i - m)²` に適用 (`memLp_id_gaussianReal' 2` + `Integrable.sub`)
     - 同様に `log p(Y_i | X_i)`, `log p(X_i, Y_i)` を展開
   - **落とし穴**: AWGN は `Y = X + N`、`(X, Y)` 同時の pdf は 2-d Gaussian。Axis 3 で
     共分散行列構築済か Phase B で再構築するか judgement #3 に影響
   - **落とし穴 2**: SLLN の `IdentDistrib` 仮定 — `((X_i - m)², (Y_i - m')²)` の i.i.d. を
     codebook 構造から derive する補題が Phase A で必要 (40-60 行追加)

2. **B-3 (volume bound) 本物 discharge** (~80 行)
   - typical set = `{(x^n, y^n) : |(1/n) log p(x^n, y^n) + h(X,Y)| < ε}`
   - 集合上で indicator × pdf を `lintegral` 評価
   - **落とし穴**: typical set の measurability — `Measurable_const_div`, `Measurable.abs`,
     `Measurable_setOf_lt` を chain。standard だが ~20 行
   - **落とし穴 2**: n-d Gaussian pdf を `volume.withDensity` 形で書く Mathlib lemma が無く、
     `multivariateGaussian` + `rnDeriv` 経由で個別構築 ~30 行

3. **B-4 (indep-product upper) 本物 discharge** (~80 行)
   - `(X', Y) indep ⇒ (X', Y) ~ p_X × p_Y` (marginal)
   - typical set 上 indicator × `p_X(x') p_Y(y)` を bound `exp(-n(h(X,Y) - ε))` で書き換え
   - **落とし穴**: `marginal p_X = (joint p_{X,Y}).map Prod.fst` の同定が n-d 単位で必要、
     `Measure.map_prod_dist` 系 lemma が pi-formula で書かれているか確認 (loogle 未到達)
   - **落とし穴 2**: typical set 上限の bound は Markov-type の自作 (`measure_le_lintegral_mul`
     系も Mathlib 不在 = loogle 確認、~20 行手書き)

優先度 **中**:

4. **n-d differential entropy 定義** (~50 行、判断 #3 で形を確定)
   - `Measure (Fin n → ℝ)` 上の Bochner version
   - InformationTheory 既存 1-d を Pi 形に lift

---

## 撤退ラインへの距離 (本 plan §撤退ライン との関係)

### T-1 (`Measure.pi` 型クラス壁)

- **影響**: Axis 2 単独では影響しない (SLLN は scalar 経由)、Axis 1 (codebook 型選択) と
  連動。**Axis 2 から見て T-1 採用は中立** (どちらでも SLLN は起動可)
- **本 inventory での発動**: なし

### T-2 (continuous AEP の Mathlib 不在、本 inventory の中心判断)

- **影響**: **発動 (推奨)**。本 inventory の決定打。Mathlib に continuous AEP / SMB 単体が
  存在しないこと、`(1/n) log p(X^n) → h(X)` の直接導出が ~200-300 行の自作になることが確認
  済。
- **本 inventory での結論**: **T-2 採用** = `IsContinuousAEPGaussian P N` regularity hyp 化を
  Phase 0 中央判断として採用
- **honesty 規律 (本 plan §honesty 撤退ライン より) を満たすか**: ✅ 全 3 条件:
  - (a) 結論型 ≠ `IsAwgnTypicalityHypothesis` (entropy convergence のみ、`∃ codebook` を含まない)
  - (b) docstring で "Mathlib gap, NOT load-bearing" を明記
  - (c) Phase C-D の codebook + union bound + expurgation は本物 discharge

### T-3 (expurgation lemma 不在)

- **影響**: 本 inventory のスコープ外 (Axis 4 の inventory が判断)。Axis 2 とは独立

### T-4 (全体 700 行超で plan 2 分割)

- **影響**: T-2 採用すれば Phase B が 50 行に縮退 → 全体 ~360-560 行で T-4 不発動の見込み。
  T-2 不採用なら Phase B が 200-400 行 → 全体 510-810 行で T-4 中-高確率発動
- **本 inventory での扱い**: T-2 採用判断とセット。T-2 採用で T-4 回避が想定

### 新規縮退ライン提案

新規縮退ラインは不要 (T-2 採用で既存撤退ラインが期待通り機能)。ただし以下を補足:

- **T-2 採用時の最小 honesty 失格パターン (本 inventory での発見)**:
  - `IsContinuousAEPGaussian P N` 中身が以下を含むと honesty 違反:
    - `∃ codebook, ...` (= codebook の構築まで肩代わり)
    - `errorProb < ε` (= Pe の評価まで肩代わり)
    - 「H(X,Y)」を Lean に持ち上げる定義として `0 = 0` の vacuous form
  - 許容される中身: entropy convergence (`(1/n) log p(X^n) → h(X,Y) ± ε`)、typical set 集合
    の存在 + 3 つの measure-theoretic bound、これら **解析的事実** のみ

---

## 着手 skeleton (Phase B-0、T-2 採用時)

`InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` の Phase B 部分 (skeleton 形、Phase A
の `gaussianCodebook` 定義が確定したあと貼る):

```lean
import InformationTheory.Shannon.AWGN
import InformationTheory.Shannon.AWGNAchievability
import InformationTheory.Shannon.AWGNF1Discharge
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

/-! ## Phase B-0 — `IsContinuousAEPGaussian` predicate (T-2 採用、Axis 2 inventory より)

**Mathlib gap predicate (NOT load-bearing for achievability)**. The codebook + union
bound + expurgation core of AWGN achievability (Phases C-D) is genuinely discharged
without this hypothesis. This predicate only packages the 3 classical AEP bounds whose
direct Lean discharge is blocked by:

* Absence of continuous AEP / Shannon-McMillan-Breiman for general (non-discrete)
  alphabet in Mathlib.
* Absence of n-dim Gaussian density and `differentialEntropy` lifting in both Mathlib
  and InformationTheory.

See `docs/shannon/awgn-achievability-typicality-mathlib-inventory-axis2-aep.md` for the
discharge ledger. This hypothesis is the staged-completion strategy described in
parent plan §撤退ライン T-2 and CLAUDE.md「Mathlib 壁の 4 分類」(category (b) -
analytic Mathlib gap). It is intentionally distinct in shape from
`IsAwgnTypicalityHypothesis` (which is the achievability *conclusion*); this
predicate only carries the entropy-convergence inputs to that conclusion. -/
def IsContinuousAEPGaussian (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ {ε : ℝ}, 0 < ε →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        MeasurableSet A ∧
        -- B-2: joint typicality probability tends to 1
        (1 - ENNReal.ofReal ε ≤ (jointAwgnLaw P N n) A) ∧
        -- B-3: typical set Lebesgue volume bound
        ((MeasureTheory.volume.prod MeasureTheory.volume) A
            ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * (jointDifferentialEntropy P N + ε)))) ∧
        -- B-4: independent-product upper bound
        ((marginalX P n).prod (marginalY P N n)) A
            ≤ ENNReal.ofReal (Real.exp (- (n : ℝ) *
                (awgnMutualInfo P N - 3 * ε)))

end InformationTheory.Shannon.AWGN
```

(上の `jointAwgnLaw`, `jointDifferentialEntropy`, `awgnMutualInfo`, `marginalX/Y` は
Phase A-B 着手時に確定する補助 noncomputable def。Axis 1, 3 inventory に依存。)

---

## 推奨判断 #1 (T-2 採用 or 不採用) — Axis 2 結論

### **判定: T-2 採用 (最有力)**

#### 根拠 1 — 「直接 discharge できる lemma が Mathlib に存在しない」

以下が **全て 🔴 不在**:

- `(1/n) log p(X^n) → h(X)` の continuous AEP 本体
- n-dim Gaussian density (multi-dim `gaussianPDF`)
- n-dim differential entropy
- continuous Shannon-McMillan-Breiman

#### 根拠 2 — 「迂回ルート (SLLN + log + pdf 展開) は実装可能だが高コスト」

- `strong_law_ae_real` (🟢) + `memLp_id_gaussianReal'` (🟢) + `gaussianPDFReal` (🟢) +
  `Filter.Tendsto.log` (🟢) + `variance_eq_sub` (🟢) を chain すれば、B-2 は **理論的に
  本物 discharge 可能**
- ただし pdf 展開・i.i.d. lifting・joint AWGN 法則構築の合計で **B-2 単体で ~150 行、
  B-3/B-4 で 80 + 80 = 160 行追加、合計 ~390 行**
- これは Phase B 単独の見積で、Phase A/C/D との合計が ~750-810 行になり **T-4 (plan 2
  分割) を高確率発動**

#### 根拠 3 — 「Phase B 内訳のうち決定的に止まるのは Mathlib 壁ではなく "選択 (big)"」

- CLAUDE.md「Mathlib 壁の 4 分類」に照らすと、本軸は **category (b) "analytic Mathlib gap"**
  に該当 (誰でも書けるが量が多い)、(a) (hard) ではない
- T-2 採用は (b) gap を staged で外出しする honest な選択 (parallel-gaussian / EPI と同型
  pattern、本 plan §honesty 規律 で明示)
- T-2 採用は **「実は選択 (big) を blocked (hard) と偽る」** という defect (本 CLAUDE.md
  「honesty defect の tells」) には**該当しない** — 親 plan §撤退ラインで明示的に staged
  pattern として宣言済、name laundering でも循環でもない

#### 結論 (1 行)

**T-2 採用** = Phase B-0 で `IsContinuousAEPGaussian P N` を 1 本の regularity hypothesis
として定義し、Phase C-D で codebook / decoder / expurgation を本物 discharge。最終的に
`isAwgnTypicalityHypothesis` の signature に `(h_aep : IsContinuousAEPGaussian P N)` 1 引数
が残るが、これは **achievability core の core ではなく n-dim Gaussian の AEP の Mathlib gap
のみを切り出した regularity hyp** であり、CLAUDE.md「regularity hyp の 3 条件」を全て満たす。

### 判断 #1 サブ判断 (Phase 0 残)

本 inventory (Axis 2) の管轄外、後続 axis inventory に委ねる:

- **判断 #2 (codebook 測度 type)**: Axis 1 (codebook) inventory の管轄
  - Axis 2 観点での示唆: `strong_law_ae` (Banach 版) を起動するなら `[BorelSpace E]` 要求から
    **`EuclideanSpace ℝ (Fin (M*n))` flatten 推奨** (T-1 採用)。ただし scalar SLLN (`strong_law_ae_real`)
    で十分なら `(Fin M → Fin n → ℝ)` のままでも問題なし
- **判断 #3 (typical set 定義形)**: Phase B 着手時 (T-2 採用なら predicate 内側の bundle 設計)、
  Axis 5 (volume) inventory と連動
  - Axis 2 観点での示唆: T-2 採用なら predicate 内部の typical set 定義は **`Set` レベルで
    `MeasurableSet` 仮定 + 3 bound のみ** の純粋 abstract 形で十分、`rnDeriv` / `differentialEntropy`
    / `klDiv` のどれを使うかは選択不要 (regularity hyp の自由度として確保)

---

## Appendix: loogle / rg 確認コマンド一覧

本 inventory 作成に用いた検索コマンド (再現用):

```bash
LO="./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index"

# SLLN
rg -n "^theorem strong_law|^lemma strong_law" .lake/packages/mathlib/Mathlib/Probability/StrongLaw.lean
$LO "ProbabilityTheory.strong_law_ae"

# Gaussian moments
$LO "ProbabilityTheory.gaussianReal, MeasureTheory.MemLp"
$LO "ProbabilityTheory.IsGaussian.integrable_id"
rg -n "memLp_id" .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/

# n-d Gaussian
ls .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/
rg -n "^(def|theorem|lemma|noncomputable def|instance)" .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Multivariate.lean

# Log composition
$LO "Filter.Tendsto.log"
$LO "Real.continuous_log"

# differentialEntropy / AEP gap (negative confirmation)
$LO "ProbabilityTheory.differentialEntropy"  # → Found 0
$LO "ProbabilityTheory.IsGaussian.differentialEntropy"  # → Found 0
rg -l "AEP|asymptoticEquipartition" .lake/packages/mathlib/Mathlib/Probability/  # → no match
rg -n "ShannonMcMillan|smb" .lake/packages/mathlib/Mathlib/  # → no match

# Independence
$LO "ProbabilityTheory.iIndepFun"

# KL (alternate route, not adopted)
$LO "InformationTheory.klDiv"
```
