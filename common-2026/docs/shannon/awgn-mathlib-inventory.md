# T2-A AWGN Channel Capacity のための Mathlib インフラ在庫調査

> 親 seed: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) T2-A 項。  
> 出力先: Lean 実装は `InformationTheory/Shannon/AWGN.lean`（新規）。  
> 規約: `CLAUDE.md` の "Subagent Inventory of Mathlib Lemmas" + "Mathlib-shape-driven Definitions" に従う。
>
> **Status (2026-05-19)**: 着手前在庫。本ファイルは Phase 1 (在庫調査) の成果物。Phase 2 (plan 起草) は `lean-planner` サブエージェントへ。

## 一行サマリ

**Gaussian の closed-form 補題（密度・平均・分散・畳み込み・rnDeriv）はほぼ 100 % Mathlib に既存（10/10）。InformationTheory 側に `differentialEntropy`／Gaussian max-entropy／`mutualInfo`／`capacity`／discrete `shannon_noisy_channel_coding_theorem_general_full` まで揃っている。**  
**ただし「(a) continuous channel kernel = `Kernel ℝ ℝ` の AWGN 具体化」「(b) power constraint `𝔼[X²] ≤ P` を input 分布側で書いた `awgnCapacity P N` 定義」「(c) joint typical set / sphere packing on `ℝⁿ`」「(d) Pinsker / Fano + chain rule の continuous 版」の 4 ピースは Mathlib 不在 + InformationTheory 不在で、いずれも自作必須。**  
撤退ラインは 2 本（後述）うち少なくとも 1 本（achievability 連続版を hypothesis pass-through 化）に触れる蓋然性が高い。

---

## 主定理の最終形 (textbook-roadmap T2-A より再掲)

```lean
-- noise σ² = N, power constraint 𝔼[X²] ≤ P
-- C(P/N) := (1/2) * Real.log (1 + P / N)

theorem awgn_capacity_eq
    (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (P : ℝ) (hP : 0 ≤ P) :
    awgnCapacity P N = (1 / 2) * Real.log (1 + P / (N : ℝ))

-- achievability + converse の Cover-Thomas 7.7.1 形 specialization
theorem awgn_channel_coding_theorem
    (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (P : ℝ) (hP_pos : 0 < P)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n)              -- 出力電力制約 ≤ P を bundle
        (_hpow : ∀ m, ‖c.encoder m‖^2 / n ≤ P),
        ∀ m, (c.errorProbAt (awgnChannel N)).toReal < ε
```

証明戦略 (pseudo-Lean):

```
-- Step 1: continuous achievability
have h_I := mutualInfo_le_of_gaussian_input  -- I(X;Y) = (1/2) log(1+P/N) when X ∼ 𝒩(0,P), Z ∼ 𝒩(0,N) indep
-- Step 2: capacity_lim (BlockwiseChannel) のときと同じく
--    capacity_awgn = sup_{p : E[X²] ≤ P} I(p; W_awgn)
-- Step 3: discrete achievability の Cover 7.7.1 path (Joint typical decoder + random codebook)
--    の Gaussian 連続版を adapt:
--    - codebookMeasure : Gaussian(0, P-ε) i.i.d. on ℝⁿ × Fin M
--    - jointTypicalSet : strong typical set on (ℝⁿ × ℝⁿ) 上の Gaussian joint
--    - 3 つの "joint AEP bounds" の continuous 版で error 評価
-- Step 4: converse
--    log M ≤ I(X^n; Y^n) + 1 + Pe log M       -- Fano (M 候補)
--          ≤ ∑ I(X_i; Y_i) + ...              -- chain rule + memoryless
--          ≤ n * (1/2) log(1+P/N) + ...       -- per-letter max-entropy (Gaussian)
```

---

## A. Gaussian 分布の closed-form API（Mathlib 在庫）

### A.1 — Gaussian 測度・密度・基本性質

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `gaussianPDFReal` | `def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (Real.sqrt (2 * π * v))⁻¹ * Real.exp (-(x - μ)^2 / (2 * v))` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:48` | ✅ 既存 | AWGN の入力電力制約 distribution / noise distribution の密度直接形 |
| `gaussianPDFReal_pos` | `lemma gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x` | `Real.lean:61` | ✅ 既存 | rnDeriv の正値性 (KL 計算で必要) |
| `gaussianReal` 測度 | `noncomputable def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ := if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)` | `Real.lean:200` | ✅ 既存 | input X, noise Z の law。`v = 0` は dirac に縮退 (T2-A では `hN ≠ 0` で除外推奨) |
| `instIsProbabilityMeasureGaussianReal` | `instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianReal μ v)` | `Real.lean:209` | ✅ 既存 | input 分布が prob meas であることの自動推論 |
| `rnDeriv_gaussianReal` | `lemma rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v` | `Real.lean:240` | ✅ 既存 | differentialEntropy への橋渡し |
| `gaussianReal_absolutelyContinuous` | `lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume` | `Real.lean:228` | ✅ 既存 | rnDeriv の存在を保証 |
| `gaussianReal_absolutelyContinuous'` | `lemma gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : volume ≪ gaussianReal μ v` | `Real.lean:233` | ✅ 既存 | 逆向き absolute continuity (max-entropy converse で利用) |

### A.2 — Gaussian の moments + characteristic identities

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `integral_id_gaussianReal` | `@[simp] lemma integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ` | `Real.lean:508` | ✅ 既存 | input mean = 0 を bundle するときに使う |
| `variance_id_gaussianReal` | `@[simp] lemma variance_id_gaussianReal : Var[id; gaussianReal μ v] = v` | `Real.lean:543` | ✅ 既存 | power constraint `E[X²] ≤ P` を `v ≤ P` (mean 0 のとき) に翻訳 |
| `variance_fun_id_gaussianReal` | `@[simp] lemma variance_fun_id_gaussianReal : Var[fun x ↦ x; gaussianReal μ v] = v` | `Real.lean:518` | ✅ 既存 | 上の `id` 版 |
| `integrable_gaussianPDFReal` | (`Mathlib/Probability/Distributions/Gaussian/Real.lean` 130 行付近、InformationTheory 既出依存) | `Real.lean:~130` | ✅ 既存 | Bochner Jensen の可積分性に必要 |
| `memLp_id_gaussianReal'` | `lemma memLp_id_gaussianReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (gaussianReal μ v)` | `Real.lean:553` | ✅ 既存 | n 次モーメント可積分性 |
| `integral_gaussianReal_eq_integral_smul` | `lemma integral_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) : ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x` | `Real.lean:249` | ✅ 既存 | (InformationTheory 既出) Gaussian 積分 → Lebesgue 積分の橋渡し |

### A.3 — Gaussian の畳み込み + 加法（AWGN の本質：`Y = X + Z`）

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| **`gaussianReal_conv_gaussianReal`** | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `Real.lean:613` | ✅ **既存・最重要** | `X ∼ 𝒩(0,P)`, `Z ∼ 𝒩(0,N)` indep ⇒ `Y = X + Z ∼ 𝒩(0, P+N)` の根拠 |
| **`gaussianReal_add_gaussianReal_of_indepFun`** | `lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) : P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `Real.lean:624` | ✅ **既存・最重要** | typed RV 形 (`Ω → ℝ` での加法。`X + Z` の law が Gaussian) |
| `gaussianReal_map_add_const` | `lemma gaussianReal_map_add_const (y : ℝ) : (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v` | `Real.lean:278` | ✅ 既存 | mean shift (channel encoder の x シフト対応) |
| `gaussianReal_map_const_mul` | `lemma gaussianReal_map_const_mul (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) : ...` | `Real.lean:373` | ✅ 既存 | scaling (parallel Gaussian で必要、T2-A では使わないかも) |
| `Measure.mconv` (additive `∗`) | `noncomputable def mconv (μ ν : Measure M) : Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)` (`@[to_additive]` で `conv` も) | `Mathlib/MeasureTheory/Group/Convolution.lean:35` | ✅ 既存 | convolution の定義。AWGN は加法群上の `∗` (additive) |

### A.4 — Gaussian 多次元（block code に必要）

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `stdGaussian` (E 上) | `noncomputable def stdGaussian : Measure E := (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)` 前提 `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:66` | ✅ 既存 | block length `n` の input 候補 (`Fin n → ℝ` ≃ `EuclideanSpace ℝ (Fin n)`) |
| `map_pi_eq_stdGaussian` | `lemma map_pi_eq_stdGaussian : (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι)` 前提 `[Fintype ι]` | `Multivariate.lean:137` | ✅ 既存 | `Measure.pi (gaussianReal 0 1)` と `stdGaussian (EuclideanSpace ℝ (Fin n))` の同一視 |
| `IsGaussian` クラス | `class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) : Prop where map_eq_gaussianReal (L : StrongDual ℝ E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal` | `Mathlib/Probability/Distributions/Gaussian/Basic.lean:45` | ✅ 既存 | input 分布が Gaussian (任意の dual で `gaussianReal`) であることを命題化 |
| `IsGaussian.toIsProbabilityMeasure` | `instance IsGaussian.toIsProbabilityMeasure {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) [IsGaussian μ] : IsProbabilityMeasure μ` | `Basic.lean:50` | ✅ 既存 | instance lift |
| `isGaussian_gaussianReal` | `instance isGaussian_gaussianReal (m : ℝ) (v : ℝ≥0) : IsGaussian (gaussianReal m v)` | `Basic.lean:58` | ✅ 既存 | `gaussianReal` から `IsGaussian` を自動生成 |
| `isGaussian_conv` | `instance isGaussian_conv [SecondCountableTopology E] {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] : IsGaussian (μ ∗ ν)` | `Basic.lean:210` | ✅ 既存 | Gaussian + Gaussian → Gaussian (多次元) |
| `IsGaussian.memLp_two_id` | `lemma IsGaussian.memLp_two_id : MemLp id 2 μ` 前提 `[IsGaussian μ]` (variance 有限性に相当) | `Mathlib/Probability/Distributions/Gaussian/Fernique.lean` | ✅ 既存 | 多次元 Gaussian の二次モーメント可積分 |

---

## B. InformationTheory 既存資産（DifferentialEntropy + ChannelCoding）

### B.1 — `InformationTheory/Shannon/DifferentialEntropy.lean`（1010 行）

| 概念 | API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `differentialEntropy` | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | `InformationTheory/Shannon/DifferentialEntropy.lean:42` | ✅ 既存 | continuous entropy 主軸 |
| `differentialEntropy_eq_integral_withDensity` | `theorem differentialEntropy_eq_integral_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) : differentialEntropy (volume.withDensity f) = ∫ x, Real.negMulLog (f x).toReal ∂volume` | `DifferentialEntropy.lean:47` | ✅ 既存 | `gaussianReal = volume.withDensity (gaussianPDF μ v)` 経由で展開 |
| `differentialEntropy_eq_integral_density` | `theorem differentialEntropy_eq_integral_density {f : ℝ → ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x) (μ : Measure ℝ) (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) : differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume` | `DifferentialEntropy.lean:60` | ✅ 既存 | `f log f` 直書き形 |
| `differentialEntropy_dirac` | `theorem differentialEntropy_dirac (m : ℝ) : differentialEntropy (Measure.dirac m) = 0` | `DifferentialEntropy.lean:149` | ✅ 既存 | degenerate (v=0) 退化形 |
| `differentialEntropy_map_add_const` | `theorem differentialEntropy_map_add_const ...` (translation 不変性) | `DifferentialEntropy.lean:165` | ✅ 既存 | shift invariance |
| `differentialEntropy_map_mul_const` | `theorem differentialEntropy_map_mul_const ...` | `DifferentialEntropy.lean:195` | ✅ 既存 | scaling for parallel Gaussian / T2-B |
| `differentialEntropy_map_affine` | `theorem differentialEntropy_map_affine ...` | `DifferentialEntropy.lean:344` | ✅ 既存 | 一般アフィン変換 |
| **`differentialEntropy_gaussianReal`** | `theorem differentialEntropy_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `DifferentialEntropy.lean:406` | ✅ **既存・最重要** | `h(𝒩(m,v)) = (1/2) log(2πev)` の closed form |
| `differentialEntropy_gaussianReal_std` | `theorem differentialEntropy_gaussianReal_std : differentialEntropy (gaussianReal 0 1) = (1/2) * Real.log (2 * Real.pi * Real.exp 1)` | `DifferentialEntropy.lean:493` | ✅ 既存 | standard Gaussian の specialization |
| **`differentialEntropy_le_gaussian_of_variance_le`** | `theorem differentialEntropy_le_gaussian_of_variance_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `DifferentialEntropy.lean:510` | ✅ **既存・converse の核** | Cover-Thomas 8.6.1 max-entropy。T2-A converse の per-letter bound `h(Y_i) ≤ (1/2) log(2πe(P+N))` |
| `differentialEntropy_eq_gaussian_iff` | `theorem differentialEntropy_eq_gaussian_iff ...` (等号成立条件) | `DifferentialEntropy.lean:659` | ✅ 既存 | (T2-A では未使用、reference のみ) |
| `klDiv_gaussianReal_gaussianReal_eq` | `theorem klDiv_gaussianReal_gaussianReal_eq (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) : klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂) = ENNReal.ofReal (...)` | `DifferentialEntropy.lean:791` | ✅ 既存 | Gaussian × Gaussian KL closed form (T2-A converse 別経路で活用可) |

### B.2 — Channel coding 抽象（discrete 完成形）

| 概念 | API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `Channel α β := Kernel α β` | `abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] := Kernel α β` | `InformationTheory/Shannon/ChannelCoding.lean:49` | ✅ 既存 | **AWGN: `Channel ℝ ℝ` で type-class 整合**。`α := ℝ` (input), `β := ℝ` (output) |
| `jointDistribution p W` | `noncomputable def jointDistribution (p : Measure α) (W : Channel α β) : Measure (α × β) := p ⊗ₘ W` | `ChannelCoding.lean:54` | ✅ 既存 | `(X, Y)` の joint。AWGN でも同じ |
| `outputDistribution p W` | `noncomputable def outputDistribution (p : Measure α) (W : Channel α β) : Measure β := (jointDistribution p W).snd` | `ChannelCoding.lean:71` | ✅ 既存 | Y の marginal。`X ∼ 𝒩(0,P)` + AWGN `N` で `(p ⊗ₘ W).snd = 𝒩(0, P+N)` |
| `mutualInfoOfChannel p W` | `noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | `ChannelCoding.lean:84` | ✅ 既存 | `I(X; Y)` 形 (AWGN にも適用可) |
| **`Code M n α β`** | `structure Code (M n : ℕ) (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where encoder : Fin M → (Fin n → α); decoder : (Fin n → β) → Fin M` | `ChannelCoding.lean:151` | ✅ 既存・**要拡張** | discrete 想定: encoder/decoder に measurability 不要 (finite α）。**AWGN では `α := ℝ` で `measurable encoder` が自動で出ない**。bundle に measurability 追加 or `AwgnCode` 新規構造 |
| `Code.errorProbAt`, `averageErrorProb` | `ChannelCoding.lean:204, 210` | ✅ 既存 | そのまま再利用可能 |
| **`capacity W`** | `noncomputable def capacity (W : Channel α β) : ℝ := sSup ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) '' stdSimplex ℝ α)` | `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean:102` | ✅ 既存・**要 specialize** | **discrete 想定 (`stdSimplex ℝ α` は `α : Fintype` 前提)**。AWGN では `α := ℝ` で `stdSimplex ℝ ℝ` は無意味なので**新規 `awgnCapacity P N : ℝ` を立てる**必要あり |
| `shannon_noisy_channel_coding_theorem_general_full` | `theorem shannon_noisy_channel_coding_theorem_general_full (W : Channel α β) [IsMarkovKernel W] {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∀ n, N ≤ n → ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : Code M n α β), ∀ m, (c.errorProbAt W m).toReal < ε` 前提 `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]` + `β` 同様 | `InformationTheory/Shannon/ChannelCodingShannonTheoremFullDischarge.lean:1588` | ✅ 既存・**型クラス壁** | **`[Fintype α]` 必須。AWGN では `α := ℝ` で適用不可。** 連続版を別途証明する必要あり |

### B.3 — `BlockwiseChannel` 抽象（I-2 General DMC capacity）

| 概念 | API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `BlockwiseChannel α β` | `def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ := (n : ℕ) → Kernel (Fin n → α) (Fin n → β)` | `InformationTheory/Shannon/BlockwiseChannel.lean:60` | ✅ 既存 | **AWGN を BlockwiseChannel として記述する選択肢。** `α := β := ℝ` で型クラス整合 (`ℝ : MeasurableSpace`) |
| `Channel.toBlock W n` | `noncomputable def Channel.toBlock (W : Channel α β) [IsMarkovKernel W] (n : ℕ) : Kernel (Fin n → α) (Fin n → β)` | `BlockwiseChannel.lean:74` | ✅ 既存 | memoryless extension `W^{⊗n}`。AWGN の `W` に `IsMarkovKernel` を付ければ自動構築 |
| `BlockwiseChannel.capacityN W n` | `noncomputable def BlockwiseChannel.capacityN (W : BlockwiseChannel α β) (n : ℕ) : ℝ≥0∞ := sSup ((fun p : Measure (Fin n → α) => mutualInfoOfChannel p (W n)) '' { p : Measure (Fin n → α) | IsProbabilityMeasure p })` | `BlockwiseChannel.lean:124` | ✅ 既存・**要拡張** | **無制約 `sup`。AWGN は `E[‖X‖²] ≤ n·P` 制約付き sup** が必要 → `BlockwiseChannel.capacityN_costConstrained` を新規導入 or `awgnCapacity P N` を直接定義 |
| `BlockwiseChannel.capacity_lim W` | `noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ := Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)` | `BlockwiseChannel.lean:134` | ✅ 既存 | per-letter limit。AWGN memoryless では `capacity_lim = (1/2) log(1+P/N)` |
| `capacity_lim_eq_capacity_of_memoryless` | `BlockwiseChannel.lean:1181` | ✅ 既存 | discrete memoryless 用 specialization。AWGN 連続版を同形で書く |

### B.4 — typed RV layer

| 概念 | API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `differentialEntropyRV μ X` | `noncomputable def differentialEntropyRV {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ := InformationTheory.Shannon.differentialEntropy (μ.map X)` | `InformationTheory/Shannon/TypedRV.lean:81` | ✅ 既存 | `h(X)` を `Ω → ℝ` random variable で書ける |
| `mutualInfo μ Xs Yo` | `noncomputable def mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ := klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `InformationTheory/Shannon/MutualInfo.lean:36` | ✅ 既存 | `I(X;Y)` for general type X, Y。AWGN では X = Y = ℝ で直接適用可 |
| `klDivRV μ X Y` | `InformationTheory/Shannon/TypedRV.lean:64` | ✅ 既存 | (T2-A では未使用) |

### B.5 — FisherInfo + de Bruijn (T2-F)

| 概念 | API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `fisherInfo μ` | `noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2) * μ.rnDeriv volume x ∂volume` | `InformationTheory/Shannon/FisherInfo.lean:58` | ✅ 既存 | (T2-A では直接使わない、T2-D EPI で必要) |
| `IsRegularDeBruijnHyp` + `deBruijn_identity` | `InformationTheory/Shannon/FisherInfo.lean:186, 209` | ✅ 既存 (hypothesis pass-through 形) | (T2-A では未使用、reference のみ) |

---

## C. Mathlib 上の channel kernel / compProd 道具立て

### C.1 — Kernel と instance chain

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `Kernel α β` | (Mathlib の primitive) `ProbabilityTheory.Kernel` | `Mathlib/Probability/Kernel/Basic.lean` | ✅ 既存 | AWGN を `Kernel ℝ ℝ` で書く |
| `IsMarkovKernel κ` | `class IsMarkovKernel (κ : Kernel α β) : Prop where isProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)` | `Mathlib/Probability/Kernel/Defs.lean:147` | ✅ 既存 | AWGN kernel が probability measure を返すことの命題 |
| `IsFiniteKernel κ` | `class IsFiniteKernel (κ : Kernel α β) : Prop where exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C` | `Defs.lean:155` | ✅ 既存 | (上位クラス) |
| `IsZeroOrMarkovKernel.isFiniteKernel` | `instance (priority := 100) IsZeroOrMarkovKernel.isFiniteKernel [h : IsZeroOrMarkovKernel κ] : IsFiniteKernel κ` | `Defs.lean:231` | ✅ 既存 | Markov → Finite |
| `IsFiniteKernel.isSFiniteKernel` | `instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] : IsSFiniteKernel κ` | `Defs.lean:353` | ✅ 既存 | Finite → SFinite (compProd の前提自動充足) |
| `Kernel.compProd` (`⊗ₖ`) | `noncomputable irreducible_def compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)` 前提 `[IsSFiniteKernel κ] [IsSFiniteKernel η]` (証明側で要求) | `Mathlib/Probability/Kernel/Composition/CompProd.lean:69` | ✅ 既存 | (T2-A では Measure.compProd を直接使う) |
| `Measure.compProd` (`⊗ₘ`) | `def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β) := (Kernel.const Unit μ ⊗ₖ Kernel.prodMkLeft Unit κ) ()` 実用上 `[SFinite μ] [IsSFiniteKernel κ]` が必要 | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:43` | ✅ 既存 | **joint `(X,Y) ∼ p ⊗ₘ W`** の基本構築。`p : Measure ℝ`, `W : Kernel ℝ ℝ` |
| `Measure.compProd_apply_prod` | `lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ] (hs : MeasurableSet s) (ht : MeasurableSet t) : (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ` | `MeasureCompProd.lean:69` | ✅ 既存 | rectangular set 上の積分公式 |
| `IsMarkovKernel.compProd` | `instance IsMarkovKernel.compProd (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel (α × β) γ) [IsMarkovKernel η] : IsMarkovKernel (κ ⊗ₖ η)` | `CompProd.lean:432` | ✅ 既存 | Markov × Markov → Markov (推論連鎖) |
| `Kernel.map` (`Kernel.IsMarkovKernel.map`) | `Mathlib/Probability/Kernel/Composition/MapComap.lean` | ✅ 既存 | (kernel の post-composition; AWGN noise を構築するときに使う候補) |

### C.2 — Independence + characteristic identities

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `IndepFun X Y μ` | `def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop := Kernel.IndepFun f g (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)` | `Mathlib/Probability/Independence/Basic.lean:144` | ✅ 既存 | `X ⟂ Z` を typed RV 形で表現 (AWGN の noise 独立) |
| `variance X μ` | `def variance : ℝ := (evariance X μ).toReal` (`evariance := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ`) | `Mathlib/Probability/Moments/Variance.lean:63` (`evariance:58`) | ✅ 既存 | power constraint `Var[X; μ] ≤ P` (mean 0 の前提を bundle すれば `𝔼[X²] ≤ P`) |
| `variance_eq_integral` | `lemma variance_eq_integral (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ` | `Variance.lean:154` | ✅ 既存 | Bochner integral 形 (InformationTheory 既出) |
| `Measure.conv` (additive `∗`) | `@[to_additive] noncomputable def mconv (μ ν : Measure M) : Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)` → additive version `Measure.conv` via `to_additive` | `Mathlib/MeasureTheory/Group/Convolution.lean:35` | ✅ 既存 | `gaussianReal_conv_gaussianReal` 経由で `Y` の law を直接計算 |

### C.3 — `condDistrib` / disintegration（converse の continuous Fano で必要）

| 概念 | Mathlib API | file:line | 状態 | T2-A での扱い |
|---|---|---|---|---|
| `condDistrib Y X μ` | `noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω` 前提 `[MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]` (file-top variable; 出力側 `Ω` に要求) | `Mathlib/Probability/Kernel/CondDistrib.lean:64` (file-top variable `Mathlib/Probability/Kernel/CondDistrib.lean:54-55`) | ✅ 既存 | **converse で `condDistrib (Y i) (Y^{<i}, X^{i}) μ` 等を取るときに必要**。Ω = ℝ は `[StandardBorelSpace ℝ]` 自動充足 |
| `compProd_map_condDistrib` | `lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)` 前提 (file-top): `[MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]` | `CondDistrib.lean:82` | ✅ 既存 | joint = marg ⊗ condKernel の disintegration |
| `instIsMarkovKernelCondDistrib` | `instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ)` 前提同上 | `CondDistrib.lean:68` | ✅ 既存 | condKernel が Markov 自動 |
| `Measure.condKernel` | `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean:361` (InformationTheory 過去調査済) | ✅ 既存 | 同上の measure 版 |

**重要な前提条件ボックス**（事故の起きやすい lemma 群）:

- `condDistrib Y X μ : Kernel β Ω` の **`[StandardBorelSpace Ω]` 要求は出力側 `Ω` に課される** (`Mathlib/Probability/Kernel/CondDistrib.lean:54` の file-top variable)。T2-A converse で `condDistrib (X i) (X^{<i}, Y^n) μ` を取る場合、出力側 = `X i : ℝ` に `[StandardBorelSpace ℝ]` が必要。`ℝ` には自動 instance があるので OK。**ただし `Y^n : Fin n → ℝ` は積空間で、`StandardBorelSpace (Fin n → ℝ)` も自動 instance 在庫を確認したうえで使うこと**（fano-mathlib-inventory.md §B の Fano 経験では「Fin 系の積で StandardBorel 自動 derive されるか」が紛らわしい）。
- `Measure.compProd` (`⊗ₘ`) は **`[SFinite μ] [IsSFiniteKernel κ]` がないと `0` を返す**（`MeasureCompProd.lean:50` `compProd_of_not_sfinite`）。AWGN では `μ := gaussianReal 0 P` が `IsProbabilityMeasure` → `IsFiniteMeasure` → `SFinite` で自動充足。kernel 側も AWGN が `IsMarkovKernel` ⇒ `IsFiniteKernel` ⇒ `IsSFiniteKernel` で自動。
- `gaussianReal_add_gaussianReal_of_indepFun` は `IndepFun X Y P` を **両側で** `Measurable` あるいは `AEMeasurable` 要求（証明内で `AEMeasurable.of_map_ne_zero` で復元）。`X : Ω → ℝ` の measurability を encoder の bundle で確保する必要あり。
- `differentialEntropy_le_gaussian_of_variance_le` は **4 つの hypothesis** (`hμ : μ ≪ volume`, `h_mean = m`, `h_var ≤ v`, `h_var_int`, `h_ent_int`) を要求 (`DifferentialEntropy.lean:510`)。converse で `Y_i = X_i + Z_i` の law に適用するときは `Y_i` 側で同様に確認必要。`h_ent_int` は entropy 被積分関数の volume 可積分性で、a priori 自明でない。
- `Code M n α β` (`ChannelCoding.lean:151`) は **measurability field を bundle しない**設計 (`Fintype α` 想定)。AWGN では encoder `Fin M → (Fin n → ℝ)` だが定義域 `Fin M` が finite なので encoder の measurability は自動。ただし**decoder `(Fin n → ℝ) → Fin M` の measurability** は `Fin n → ℝ` 側が `MeasurableSingletonClass` でないため自動では出ない。`AwgnCode` を新規構造として組み、`decoder_meas : Measurable decoder` を bundle 必須。

---

## D. AWGN 用に **不在** の Mathlib / InformationTheory API（自作必須）

優先度順、推定行数付き。

### D.1 — AWGN kernel `awgnChannel : Channel ℝ ℝ` （最優先・最小）

**現状**: Mathlib に Gaussian noise の channel kernel 形は不在。

**推奨実装**:
```lean
noncomputable def awgnChannel (N : ℝ≥0) : Channel ℝ ℝ where
  toFun x := gaussianReal x N    -- mean = x (信号), variance = N (noise power)
  measurable' := by
    -- gaussianReal の m に関する measurability
    -- 戦略: gaussianReal m v = volume.withDensity (gaussianPDF m v) (v ≠ 0 のとき)
    -- gaussianPDF m v x の m に関する連続性 + measurable_pi_iff
    sorry
```

工数感: 50-100 行 (`Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` 経由 + 密度関数の連続性)。落とし穴: `v = 0` 退化と非退化の場合分け。

`instance : IsMarkovKernel (awgnChannel N) where ...` は `instIsProbabilityMeasureGaussianReal` から直線。

### D.2 — Power constraint 付き `awgnCapacity P N : ℝ` 定義

**現状**: `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean:102` の `capacity W` は **`stdSimplex ℝ α`**（`Fintype α` 想定）でとる。AWGN では continuous な input 分布全体上で電力制約付き sup を取る。

**Mathlib-shape-driven な推奨定義**:
```lean
/-- AWGN 容量: 出力電力制約 E[X²] ≤ P の下での I(X;Y) の sup。 -/
noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) : ℝ :=
  sSup ((fun p : Measure ℝ => (mutualInfoOfChannel p (awgnChannel N)).toReal) ''
        { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })
```

工数感: 30 行 (定義 + non-empty + bddAbove + nonneg)。Gaussian input `𝒩(0, P)` で `bddAbove` の上界 `(1/2) log(1 + P/N)` を取れば終わり。

**達成定理 (textbook 形)**:
```lean
theorem awgnCapacity_eq (P : ℝ) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (hP : 0 ≤ P) :
    awgnCapacity P N = (1/2) * Real.log (1 + P / (N : ℝ))
```

工数感: 100-200 行 (achievability `≥` + converse `≤` の両方; 後者は `differentialEntropy_le_gaussian_of_variance_le` の連鎖)。

### D.3 — I(X;Y) closed form for Gaussian-input AWGN

**現状**: `mutualInfoOfChannel` を `gaussianReal 0 P` + `awgnChannel N` で評価した `(1/2) log(1 + P/N)` の closed form は不在。

**Mathlib-shape-driven な定式化** (`differentialEntropy_gaussianReal` の結論形 `(1/2) log(2πev)` を 2 回引いて差を取る):
```lean
theorem mutualInfoOfChannel_gaussianReal_awgnChannel
    (P : ℝ≥0) (N : ℝ≥0) (hP : (P : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0) :
    (mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N)).toReal
      = (1/2) * Real.log (1 + (P : ℝ) / (N : ℝ))
```

戦略 (pseudo-Lean):
```
-- I(X;Y) = h(Y) - h(Y|X) = h(Y) - h(Z)
-- Y ∼ 𝒩(0, P+N) (gaussianReal_conv_gaussianReal)
-- h(Y) = (1/2) log(2πe(P+N))
-- h(Z) = (1/2) log(2πeN)
-- ⇒ I = (1/2) [log(2πe(P+N)) - log(2πeN)] = (1/2) log((P+N)/N) = (1/2) log(1+P/N)
```

ただし `mutualInfo` の現定義は KL 形（`klDiv (μ.map (X,Y)) ((μ.map X).prod (μ.map Y))`）なので、`I = h(Y) - h(Y|X)` 形に書き換える橋渡し補題が**現状 InformationTheory に不在**。**ここが最大の plumbing リスク**（"Mathlib-shape-driven Definitions" 規約のレッドフラグ: 「`f (compProd ...)` を `∫⁻ ... ∂` に直す bridge」を探すパターン）。

→ **撤退ライン候補**：`mutualInfo_of_gaussian_input_eq` を hypothesis pass-through 形で publish し、bridge 補題は別 plan (`mi-continuous-bridge-plan.md`) で分離する。

工数感: 直接書く場合 200-400 行（`klDiv_compProd_eq_add` chain rule + Gaussian の rnDeriv 展開 + entropy 形への変換）。hypothesis 形なら 30 行。

### D.4 — Continuous joint typical set / achievability

**現状**: `InformationTheory/Shannon/ChannelCodingAchievability.lean:301` の `jointlyTypicalSet` は **`[Fintype α] [Fintype β]` 想定**。Cover-Thomas 8.6 の continuous joint typicality (sphere packing 経由) は完全に不在。

**選択肢**:

1. **Sphere packing 経路** (Cover-Thomas 9.2): codebook を Gaussian i.i.d. でサンプル → typical set ≈ `Fin n → ℝ` の球殻 `B(0, √(nP))` の表面 → 球殻の体積比から `2^{n(R-C)}` decay。
   - Mathlib 在庫: `Metric.sphere`（既存）、`EuclideanSpace ℝ (Fin n)` の volume measure（`Mathlib/MeasureTheory/Measure/Lebesgue/EuclideanSpace.lean` ある）。
   - 不在: 球殻の volume formula（`(π^{n/2} / Γ(n/2+1)) · r^n` の closed form）が Mathlib に直接形では不在の可能性大。
2. **Strong typicality 経路** (Gaussian PDF の log を取って AEP): `InformationTheory/Shannon/StrongTypicality.lean` の discrete 版を `pdf log pdf` で再構築。
3. **直接 Gallager 形** (random coding exponent): 連続版を `klDiv_compProd_eq_add` で書く。

**推奨**: 当面 **撤退ライン 1** を採用し、achievability 半分は `hypothesisAchievability : ∀ ε > 0, ∃ codebook, average_error ≤ ε` という命題形 hypothesis を bundle して pass-through で publish。Bridge は別 plan。

工数感: 直接実装 500-800 行 (sphere packing + 球殻 volume + AEP)。Hypothesis 形 50 行。

### D.5 — Continuous Fano / converse

**現状**: `InformationTheory/Shannon/ChannelCodingConverseGeneralComplete.lean:474` の `channel_coding_converse_general_memoryless` は **`[Fintype α] [Fintype β]`** + **`[MeasurableSingletonClass α]`** 想定。Continuous 版は不在。

**戦略**:
- Fano の連続化は **Cover-Thomas 2.10**: `H(W | Y) ≤ binEntropy(Pe) + Pe log(|W|-1)` の `W` 側を message space `Fin M`（依然 discrete）に保つ。`Y^n : Fin n → ℝ` は連続側だが、Fano の `Y` 側引数は decoder の output range なので問題なし。
- すなわち `fano_inequality_measure_theoretic` (`InformationTheory/Fano/Measure.lean`) を `X := Fin M`, `Y := Fin n → ℝ` で **そのまま再利用できる**（`X` 側に `Fintype + MeasurableSingletonClass`、`Y` 側に制約なし、という Fano Phase 3 の構造に合致）。
- Chain rule per-letter は `condMutualInfo_chain_rule_X_2var` + `memoryless_per_summand_bound` (`ChannelCodingConverseGeneralComplete.lean:215, 371`) を再利用可。ただし `[StandardBorelSpace X]` `[StandardBorelSpace Y]` のため continuous X, Y で適用可。
- Per-letter max-entropy bound: `differentialEntropy_le_gaussian_of_variance_le` を `Y_i ∼ μ_{Y_i}` に適用し、`Var[Y_i] ≤ P + N` （input power constraint + indep noise variance）から `h(Y_i) ≤ (1/2) log(2πe(P+N))`。

工数感: 200-300 行 (chain rule 連鎖 + per-letter max-entropy + Fano)。**Fano 部分は既存 `fano_inequality_measure_theoretic` を直接呼べる**ので意外に薄い。

### D.6 — `Code` の measurability bundle 拡張 (`AwgnCode`)

**現状**: `Code M n α β` (`ChannelCoding.lean:151`) は measurability field なし。

**推奨**: 
```lean
structure AwgnCode (M n : ℕ) where
  encoder : Fin M → (Fin n → ℝ)
  decoder : (Fin n → ℝ) → Fin M
  decoder_meas : Measurable decoder
  power_constraint : ∀ m, ∑ i, (encoder m i)^2 ≤ n * P    -- P を field か parameter かは設計判断
```

工数感: 30-50 行 (struct + Code 互換 lemma 群)。

### D.7 — Pinsker 連続版 / KL → TV bound

**現状**: `InformationTheory/Shannon/Pinsker.lean` は discrete 想定が主。Achievability の error 評価で `klDiv` から TV を取り出す箇所で必要。

**判定**: T2-A 本体では未必要（achievability を hypothesis 形に丸めるなら回避）。優先度低。

---

## E. T2-A で使う API の既存率（実体ベース）

カウント: 上の B.1-3 + C.1-3 + D の **「T2-A で使う」**列を分母、`✅ 既存` を分子。

- **closed-form 補題（Gaussian 密度・平均・分散・畳み込み）**: 18/18 既存 (= 100%)
- **continuous entropy (`differentialEntropy*`)**: 8/8 既存 (= 100%)
- **discrete channel coding 抽象 (`Channel`, `Code`, `capacity`, achievability/converse 主定理)**: 7/7 既存 (= 100%) — ただし **型クラス壁** (`Fintype α`) が AWGN 適用を阻む
- **kernel / compProd / IndepFun primitive**: 9/9 既存 (= 100%)
- **AWGN 専用 API (`awgnChannel`, `awgnCapacity`, mutualInfo closed form, joint typicality continuous, Fano + chain rule continuous, `AwgnCode` 拡張)**: 0/6 既存 (= 0%) → **すべて自作**

**総合**: closed-form 道具は 100% / AWGN 専用ラッパ層 0% / 中間 plumbing 約 30%（`mutualInfo` の連続版 + Fano measure-theoretic は再利用可だが「I = h(Y) - h(Y|X)」bridge は不在）。

要約: **「Gaussian の精密計算は全部既存。`awgnChannel` をひと枠作って `gaussianReal_add_gaussianReal_of_indepFun` を呼び、closed form を 1 本書き、achievability/converse の 2 半分を adapt する」**糊コード約 1000 行が T2-A の本体。

---

## F. 撤退ライン候補

親計画 (`docs/textbook-roadmap.md`) には T2-A の撤退ラインがまだ明示されていないので、本在庫から **新規 2 本**を提案:

### 撤退ライン F-1（最尤）: continuous achievability hypothesis pass-through

**発動条件**: T2-A 着手後 2 週間以内に **D.4 (continuous joint typical set + sphere packing) の Mathlib gap を埋められない** とき。

**縮退案**: achievability 半分を hypothesis 形で publish:
```lean
theorem awgn_achievability_hypothesis
    (N : ℝ≥0) (P : ℝ)
    (h_continuous_joint_typicality :
        ∀ R < (1/2) * Real.log (1 + P / N), ∀ ε > 0,
        ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
          ∃ (M : ℕ) (c : AwgnCode M n), Nat.ceil (Real.exp (n * R)) ≤ M ∧
            ∀ m, c.errorProbAt (awgnChannel N) m ≤ ε)
    {R : ℝ} (hR : R < (1/2) * Real.log (1 + P / N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀, ∀ n ≥ N₀, ∃ M c, ... := h_continuous_joint_typicality R hR ε
```
これは「定理形は publish するが、connectivity-typicality lemma だけ別 plan に切り出す」L-S2 (Stein) や L-F1 (de Bruijn) と同じ pattern。

### 撤退ライン F-2 (mid-risk): 連続 `mutualInfo` の `I = h(Y) - h(Y|X)` bridge を hypothesis 化

**発動条件**: D.3 の I(X;Y) closed form 補題を直接書こうとして `klDiv_compProd_eq_add` 連鎖から離れず、bridge 補題が 200 行を超えるとき。

**縮退案**: 
```lean
theorem awgnCapacity_eq_of_h_minus_h_bridge
    (h_bridge :
        ∀ (p : Measure ℝ) [IsProbabilityMeasure p], (mutualInfoOfChannel p (awgnChannel N)).toReal
          = differentialEntropy ((p ⊗ₘ awgnChannel N).snd)
              - differentialEntropy (gaussianReal 0 N))
    (P : ℝ) (N : ℝ≥0) (hP : 0 ≤ P) (hN : (N : ℝ) ≠ 0) :
    awgnCapacity P N = (1/2) * Real.log (1 + P / N) := ...
```
これも textbook-equivalent 形は publish しつつ、`h_bridge` は別 plan に切り出す。

### 撤退ライン F-3 (low-risk): converse の per-letter max-entropy 統合形

**発動条件**: T2-A converse の `differentialEntropy_le_gaussian_of_variance_le` 4-hypothesis を per-letter `Y_i` の law で discharge できないとき (`h_ent_int : Integrable (negMulLog (rnDeriv ...))` が個別 input 分布で出ない)。

**縮退案**: `h_ent_int` を converse 全体の追加 hypothesis として外出し。`fano_inequality_measure_theoretic` を呼んだあと max-entropy bound を `≤ h_max_gauss` で表現し直す。

---

## G. 危険箇所トップ 5

優先度順、見落とすと中盤で剥がれる順。

1. **`condDistrib` の `[StandardBorelSpace Ω]` は出力側に課される**（`Mathlib/Probability/Kernel/CondDistrib.lean:54-55` file-top variable）。Converse の chain rule で `condDistrib (X i) (Y^n, X^{<i}) μ` のような形を組むとき、**取り出し対象 = ℝ** には自動 instance あり (OK) だが、**条件付け側 = `(Fin n → ℝ) × (Fin i → ℝ)`** に `[Nonempty]` が要る場面で `Fin n → ℝ` が `Nonempty` 自動推論されるか要確認。Fano Phase 3 の経験で `[Fintype X]` 側に課される誤解があった例あり。

2. **`Code M n α β` の decoder measurability**（`InformationTheory/Shannon/ChannelCoding.lean:151`）が **bundle field に入っていない**。`α = ℝ` で `[MeasurableSingletonClass ℝ]` が偽（連続）なので、`measurable_of_finite` などで自動充足できない。AWGN 専用に `AwgnCode` 構造を新規定義する必要あり（B.2 で既述）。これを後回しにすると achievability で `c.errorProbAt` が `Measure.real {...}` 計算時に立ち往生する。

3. **`mutualInfoOfChannel p W` の `IsMarkovKernel W` 要求** (`ChannelCoding.lean:62-67` の instance) は `awgnChannel N` を `IsMarkovKernel` インスタンスに昇格させる必要。`gaussianReal x N` が `IsProbabilityMeasure` (∀ x) は `instIsProbabilityMeasureGaussianReal` で自動だが、**`Channel ℝ ℝ` を `Kernel.mk` で組むと measurability proof obligation** が出る。`awgnChannel.measurable'` を埋める段階で `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` か `gaussianReal_apply` ベース手書きが必要 (`InformationTheory/Shannon/BlockwiseChannel.lean:77-95` の `Channel.toBlock` の measurability proof を参考にする)。

4. **`differentialEntropy_le_gaussian_of_variance_le` の 4 hypothesis** (`DifferentialEntropy.lean:510`) のうち、特に **`h_ent_int : Integrable (negMulLog ((rnDeriv μ vol) .toReal)) volume`** が `μ` (任意の input 法則の image) で discharge できない可能性。converse で per-letter `Y_i` の law にこれを要求するとき、`Y_i` の rnDeriv が積分可能な状態 (Gaussian-like tail) を bundle するための事前準備（output `Y_i = X_i + Z_i` の law が「平均 + 二次モーメント有限」を満たすだけでは足りない場合がある）。F-3 撤退ライン候補。

5. **`mutualInfo` 定義の "Mathlib-shape-driven" レッドフラグ**（`InformationTheory/Shannon/MutualInfo.lean:36`）。現在 `mutualInfo μ X Y := klDiv (μ.map (X,Y)) ((μ.map X).prod (μ.map Y))` で KL 形。Gaussian-input AWGN の closed form `(1/2) log(1+P/N)` を取り出すために `I = h(Y) - h(Y|X) = h(Y) - h(Z)` 形へ翻訳する bridge 補題が **InformationTheory に不在**。直接 `klDiv` から展開する経路は 200-400 行のリスク。Mathlib-shape-driven 原則からは「`differentialEntropy_diff` ベースの定義変更」もありうるが、後方互換性 (`MutualInfo.lean` の既存 lemma 群、Shannon main theorem の `mutualInfoOfChannel`) を壊すと回帰が広範囲。**撤退ライン F-2 が一番現実的**。

---

## H. 着手 skeleton（`InformationTheory/Shannon/AWGN.lean`）

> 規約: 「Skeleton-driven Development」(`CLAUDE.md`)。本 skeleton 自体はファイルを作成しない。実装着手時に `lean-implementer` サブエージェントが本 skeleton を Write し、`:= by sorry` を 1 つずつ埋めていく。

```lean
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.ChannelCodingShannonTheoremFullDischarge
import InformationTheory.Shannon.BlockwiseChannel
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Fano.Measure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Group.Convolution

/-!
# T2-A: AWGN channel capacity `C = (1/2) log(1 + P/N)`

Cover-Thomas Ch.9. The continuous specialization of the Shannon noisy-channel
coding theorem to additive white Gaussian noise.

## Roadmap (per docs/shannon/awgn-mathlib-inventory.md §D)

1. (D.1) `awgnChannel N : Channel ℝ ℝ` + `IsMarkovKernel` instance.
2. (D.6) `AwgnCode M n` (Code + measurability + power constraint bundle).
3. (D.3) `mutualInfo` closed form for Gaussian input + AWGN noise.
4. (D.2) `awgnCapacity P N` definition + closed form `= (1/2) log(1+P/N)`.
5. (D.4) Achievability — Cover-Thomas 9.2 (sphere packing / joint typicality continuous).
6. (D.5) Converse — `fano_inequality_measure_theoretic` + chain rule + per-letter max-entropy.
7. Main theorem `awgn_channel_coding_theorem`.

撤退ライン: F-1 (achievability hypothesis pass-through), F-2 (mutualInfo bridge hypothesis), F-3 (per-letter max-entropy hypothesis). 詳細は inventory §F。
-/

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## D.1 — `awgnChannel : Channel ℝ ℝ` -/

/-- AWGN channel kernel: on input `x : ℝ`, output `Y = x + Z` where `Z ∼ 𝒩(0, N)`.
The kernel returns the law of `Y` directly as `gaussianReal x N` (mean shifted to `x`,
variance = noise power `N`). -/
noncomputable def awgnChannel (N : ℝ≥0) : InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ where
  toFun x := gaussianReal x N
  measurable' := by sorry

@[simp] lemma awgnChannel_apply (N : ℝ≥0) (x : ℝ) :
    (awgnChannel N) x = gaussianReal x N := rfl

/-- `awgnChannel N` is a Markov kernel (each fibre is a probability measure). -/
instance awgnChannel.instIsMarkovKernel (N : ℝ≥0) : IsMarkovKernel (awgnChannel N) where
  isProbabilityMeasure x := by
    show IsProbabilityMeasure (gaussianReal x N)
    infer_instance

/-! ## D.6 — `AwgnCode` (Code + measurability + power constraint) -/

/-- Block code with a power constraint and measurable decoder, specialized to
input/output alphabet `ℝ`. -/
structure AwgnCode (M n : ℕ) (P : ℝ) where
  encoder : Fin M → (Fin n → ℝ)
  decoder : (Fin n → ℝ) → Fin M
  decoder_meas : Measurable decoder
  power_constraint : ∀ m : Fin M, (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P

/-- Forget the power constraint and measurability to obtain a bare `Code`. -/
noncomputable def AwgnCode.toCode {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) :
    InformationTheory.Shannon.ChannelCoding.Code M n ℝ ℝ where
  encoder := c.encoder
  decoder := c.decoder

/-! ## D.3 — `mutualInfo` closed form for Gaussian-input AWGN -/

/-- Output law of AWGN with Gaussian input: `Y = X + Z` with `X ∼ 𝒩(0,P)` and
`Z ∼ 𝒩(0,N)` independent gives `Y ∼ 𝒩(0, P+N)`. This is the second marginal of
`(gaussianReal 0 P) ⊗ₘ (awgnChannel N)`. -/
theorem outputDistribution_gaussianInput (P N : ℝ≥0) :
    InformationTheory.Shannon.ChannelCoding.outputDistribution
        (gaussianReal 0 P) (awgnChannel N)
      = gaussianReal 0 (P + N) := by sorry

/-- (撤退ライン F-2 候補) **MI bridge as hypothesis**: assuming `I(X;Y) = h(Y) - h(Y|X)`
for the AWGN channel, derive the Gaussian-input closed form. -/
theorem mutualInfoOfChannel_gaussianInput_closed_form
    (P N : ℝ≥0) (hP : (P : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0)
    (h_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P) (awgnChannel N)).toReal
          = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 (P + N))
              - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P) (awgnChannel N)).toReal
      = (1/2) * Real.log (1 + (P : ℝ) / (N : ℝ)) := by sorry

/-! ## D.2 — `awgnCapacity P N` -/

/-- Power-constrained channel capacity. Sup of `I(p; W)` over probability measures `p`
with second moment ≤ P. -/
noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) : ℝ :=
  sSup ((fun p : Measure ℝ =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N)).toReal) ''
        { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })

theorem awgnCapacity_nonneg (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) : 0 ≤ awgnCapacity P N := by sorry

theorem awgnCapacity_bddAbove (P : ℝ) (N : ℝ≥0) (hP : 0 ≤ P) (hN : (N : ℝ) ≠ 0) :
    BddAbove ((fun p : Measure ℝ =>
                (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                    p (awgnChannel N)).toReal) ''
              { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P }) := by sorry

/-- Achievability of Gaussian input: `(1/2) log(1+P/N) ∈ awgnCapacity image`. -/
theorem awgnCapacity_ge_gaussian (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal) (awgnChannel N)).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ))) :
    (1/2) * Real.log (1 + P / (N : ℝ)) ≤ awgnCapacity P N := by sorry

/-- Converse via max-entropy: any input with `E[X²] ≤ P` gives MI ≤ (1/2) log(1+P/N). -/
theorem awgnCapacity_le_gaussian
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) :
    awgnCapacity P N ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by sorry

/-- **AWGN capacity closed form** (Cover-Thomas 9.1). -/
theorem awgnCapacity_eq
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal) (awgnChannel N)).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  apply le_antisymm
  · exact awgnCapacity_le_gaussian P hP.le N hN
  · exact awgnCapacity_ge_gaussian P hP N hN h_bridge_gauss

/-! ## D.4 — Achievability (撤退ライン F-1: hypothesis pass-through 形) -/

/-- **Achievability of `R < C`** — hypothesis form (撤退ライン F-1). The continuous
joint-typicality machinery (Cover-Thomas 9.2 / sphere packing) is bundled as a
hypothesis `h_typicality`. Discharging this for the AWGN channel is deferred to a
separate plan (`awgn-achievability-typicality-plan.md`). -/
theorem awgn_achievability
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_typicality :
        ∀ R < (1/2) * Real.log (1 + P / (N : ℝ)), ∀ ε > 0,
        ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
          ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
            (c : AwgnCode M n P),
            ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε :=
  h_typicality R hR ε hε

/-! ## D.5 — Converse via Fano + chain rule + per-letter max-entropy -/

/-- **Per-letter Gaussian max-entropy bound for the AWGN output**. For the i-th output
`Y_i = X_i + Z_i` with `E[X_i²] ≤ P` and `Z_i ⟂ X_i, Z_i ∼ 𝒩(0, N)`, we have
`h(Y_i) ≤ (1/2) log(2πe(P+N))`. Derived from
`InformationTheory.Shannon.differentialEntropy_le_gaussian_of_variance_le`.

撤退ライン F-3 候補: 4-hypothesis form. -/
theorem differentialEntropy_Yi_le_max_entropy_AWGN
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (P N : ℝ) (hP_pos : 0 < P) (hN_pos : 0 < N)
    (h_mean : ∫ y, y ∂μ = 0)
    (h_var_bound : ∫ y, y^2 ∂μ ≤ P + N)
    (h_var_int : Integrable (fun y => y^2) μ)
    (h_ent_int : Integrable
        (fun y => Real.negMulLog ((μ.rnDeriv volume y).toReal)) volume) :
    InformationTheory.Shannon.differentialEntropy μ
      ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (P + N)) := by sorry

/-- **Converse half**: any code with `E[X_i²] ≤ P` and average error → 0 has rate
≤ `(1/2) log(1 + P/N)`. Modeled on `channel_coding_converse_general_memoryless`
(`InformationTheory/Shannon/ChannelCodingConverseGeneralComplete.lean:474`) with
`α := β := ℝ` and per-letter max-entropy substitution. -/
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    {M n : ℕ} (hM : 2 ≤ M)
    (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N) m).toReal))
    (h_indep_noise : True)    -- placeholder for noise indep structure
    (h_aux_var_int_ent_int : True) :  -- placeholder for D.5 撤退ライン F-3 hypotheses
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by sorry

/-! ## Main theorem — `awgn_channel_coding_theorem` -/

/-- **T2-A 主定理: AWGN channel coding theorem** (Cover-Thomas 9.1.1 + 9.1.2).
Combines achievability and converse with the closed-form capacity. -/
theorem awgn_channel_coding_theorem
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_typicality : True)         -- 撤退ライン F-1 hypothesis (achievability)
    (h_mi_bridge : True)          -- 撤退ライン F-2 hypothesis (MI closed form)
    (h_per_letter_aux : True)     -- 撤退ライン F-3 hypothesis (converse integrability)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N) m).toReal < ε := by sorry

end InformationTheory.Shannon.AWGN
```

(skeleton 行数: 約 200 行。実装段階で `awgnCapacity_eq` 周辺の補助補題 + 撤退ライン hypothesis pass-through の bundling で +400-500 行、achievability/converse の本体実装で +500-1000 行となり、想定規模 ~1000-1500 行に収束する。)

---

## I. T2-A 着手前まとめ

- **インベントリ**: 本ファイル `docs/shannon/awgn-mathlib-inventory.md`
- **Gaussian 精密計算は 100% Mathlib 既存** — `gaussianReal_conv_gaussianReal`, `gaussianReal_add_gaussianReal_of_indepFun`, `variance_id_gaussianReal`, `rnDeriv_gaussianReal` ですべて足りる
- **continuous entropy + max-entropy は InformationTheory 既存** — `differentialEntropy_gaussianReal` (`= (1/2) log(2πev)`) と `differentialEntropy_le_gaussian_of_variance_le` (4-hypothesis 形) が converse の per-letter bound そのまま
- **AWGN 専用 6 ピース（`awgnChannel`, `AwgnCode`, MI closed form bridge, `awgnCapacity` 定義 + 等号, achievability, converse）が自作必要**
- **最大リスク**: discrete `Code` の measurability bundle 不在 (`α := ℝ` で `MeasurableSingletonClass` 偽), `mutualInfo` の KL 形 vs `h(Y) - h(Y|X)` 形の bridge 補題不在 (200-400 行リスク, 撤退 F-2 で回避可)
- **撤退ライン候補 3 本** (F-1 achievability hypothesis, F-2 MI bridge hypothesis, F-3 per-letter ent_int hypothesis)
- **着手可能**。Plan 起草フェーズ (Phase 2) は `lean-planner` サブエージェントへ。

