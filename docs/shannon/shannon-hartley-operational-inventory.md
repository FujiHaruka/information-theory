# 連続時間 Shannon-Hartley operational capacity — Phase 0 Mathlib + InformationTheory API 在庫

> 親計画: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md)（Phase 0 節が本ファイルを在庫ターゲットとして指名）。
> 本ファイルは docs-only 成果物。コード / 他 docs は触らない。
> 検証日: 2026-07-14（loogle index `.lake/build/loogle.index`、Mathlib は `.lake/packages/mathlib`）。

## 一行サマリ

**mainline（Phase 1 infra → Phase 5-min）が必要とする API はすべて Mathlib 既存 or in-project 定義可能で、経路上に Mathlib 壁は 0 → mainline は inventory 的に GO。**
唯一の genuine Mathlib 壁は stretch 側の `wall:nyquist-2w-dof`（prolate 固有値集中の asymptotic count = Landau-Pollak-Slepian、loogle Found 0）で、これは Phase 2/4 のみに効く。ただし Phase 2 の「壁でない周辺」も **想定より重い**: 計画が compactness の建設に想定した Hilbert-Schmidt / Schatten / trace-class 作用素理論は Mathlib **完全不在**（loogle Found 0）、無限次元の固有値**列**（→0 収束）も不在（有限次元 `eigenvalues : Fin n → ℝ` のみ）。真の壁核（LPS asymptotic count）に加え、その手前の spectral 装置自体が ~700-1200 行の genuine self-build。

- surveyed API atoms のうち **既存 ≈ 75%**、**self-build 7 項目**（うち genuine Mathlib 壁は 1 = LPS count のみ、残 6 は大きいが in-project 建設可能）。
- **雑音測度 route: α（関数空間 Gaussian）は BLOCKED**（Kolmogorov 拡張定理が Mathlib 不在）。**route β（iid サンプル無限積 `Measure.infinitePi`）/ route γ（有限窓 `Measure.pi`）は完全サポート → route β/γ 推奨**。

---

## 最終形（親計画から再掲）

```lean
-- Phase 5（wire、mainline = 5-min）
theorem contAwgn_eq_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P
```

証明戦略（サンドイッチ、stretch = 5-full）:

```
bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P          -- achievability (Phase 3, 壁非依存の公算)
  via awgn_achievability（per-sample、genuine）+ whittaker_shannon_bandlimited（CLOSED）+ Parseval 電力橋
∧ contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P        -- converse (Phase 4, 壁核消費)
  via 上位 ≈2WT 個の prolate 固有関数への射影 + awgn_converse（genuine）+ prolate_eigenvalue_count（★壁）
→ le_antisymm で等号。                                                        -- Phase 5-full
-- mainline = 5-min: contAwgn_eq_shannonHartley body を sorry + @residual(wall:nyquist-2w-dof) で publish、
--                   IsTwoWDegreesOfFreedom（load-bearing free-C predicate）を除去。
```

---

## Target 1 — コンパクト自己共役作用素のスペクトル理論 + 固有値カウント【最優先・feasibility gate / Phase 2 crux】

### 1a. 既存 = genuine buildable 資産（壁でない。作用素構成 + 自己共役 + コンパクト性 + 固有分解の土台）

| 概念 | Mathlib API | file:line | 状態 | Phase 2 での扱い |
|---|---|---|---|---|
| コンパクト作用素の述語 | `def IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂] (f : M₁ → M₂) : Prop` | `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean:69` | ✅ 既存 | `timeBandLimitingOp` のコンパクト性の目標述語 |
| コンパクト作用素の代数 | `IsCompactOperator.add / .sub / .neg / .smul / .comp_clm / .clm_comp` | 同上（`Compact/Basic.lean`） | ✅ 既存（52 decls） | `P_W ∘ Q_T ∘ P_W` の合成でコンパクト性を持ち上げる |
| 対称作用素 | `structure LinearMap.IsSymmetric` | `Mathlib/Analysis/InnerProductSpace/Symmetric.lean` | ✅ 既存（119 decls） | 自己共役性の LinearMap 版 |
| 対称 ↔ 自己共役 | `theorem LinearMap.isSymmetric_iff_isSelfAdjoint` / `theorem ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` | `Mathlib/Analysis/InnerProductSpace/Adjoint.lean` | ✅ 既存 | `timeBandLimitingOp_isSelfAdjoint` への橋 |
| 固有値は実 | `theorem LinearMap.IsSymmetric.conj_eigenvalue_eq_self` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`（general、compactness/finite-dim 不要） | ✅ 既存 | prolate 固有値が実であること |
| 固有空間の直交性 | `theorem LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`（general） | ✅ 既存 | 固有関数系の直交性 |
| **スペクトル定理（コンパクト自己共役、無限次元 OK）**: 固有空間の稠密性 | `theorem ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot (hT : IsCompactOperator T) (hT' : T.IsSymmetric) : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:443` | ✅ 既存 | prolate 固有関数系が完全（受信信号を固有基底展開できる） |
| コンパクト自己共役: 非零固有値の有限多重度 | `theorem ContinuousLinearMap.finite_dimensional_eigenspace (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ)` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:463` | ✅ 既存 | 各固有値の重複度が有限（カウント可能性の前提） |
| Rayleigh 商 → 固有ベクトル（max） | `theorem ContinuousLinearMap.IsSelfAdjoint.hasEigenvector_of_isMaxOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0) (hextr : IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) : HasEigenvector (T : E →ₗ[𝕜] E) (⨆ x : {x : E // x ≠ 0}, T.rayleighQuotient x : ℝ) x₀` | `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean:276` | ✅ 既存 | 変分表示（top 固有値のみ、`[CompleteSpace E]`） |
| Rayleigh 商 → 固有ベクトル（min） | `theorem ContinuousLinearMap.IsSelfAdjoint.hasEigenvector_of_isMinOn (…hextr : IsMinOn …) : HasEigenvector (T : E →ₗ[𝕜] E) (⨅ x …, T.rayleighQuotient x : ℝ) x₀` | `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean:295` | ✅ 既存 | 同上（bottom 固有値） |

型クラス文脈（Spectrum.lean / Rayleigh.lean 共通）: `{𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]`。コンパクト作用素節（`ContinuousLinearMap`、Spectrum.lean:429–470）は追加で `[CompleteSpace E] {T : E →L[𝕜] E}`。

### 1b. 有限次元でのみ既存（無限次元へは未拡張 = self-build 対象）

| 概念 | Mathlib API | file:line | 状態 | 備考 |
|---|---|---|---|---|
| 固有値列（降順、**有限次元限定**） | `noncomputable irreducible_def LinearMap.IsSymmetric.eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : Fin n → ℝ` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:279` | 🟡 有限次元のみ | `hn : finrank 𝕜 E = n` 必須。**無限次元コンパクト作用素の `ℕ → ℝ` 固有値列は不在** |
| 固有ベクトル基底（有限次元） | `noncomputable irreducible_def LinearMap.IsSymmetric.eigenvectorBasis (hT) (hn : finrank 𝕜 E = n) : OrthonormalBasis (Fin n) 𝕜 E` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:300` | 🟡 有限次元のみ | 同上 |
| 固有値降順（有限次元） | `theorem LinearMap.IsSymmetric.eigenvalues_antitone (hT) (hn) : Antitone (hT.eigenvalues hn)` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:312` | 🟡 有限次元のみ | |
| 固有値カウント（**多重度のみ**、有限次元、閾値なし） | `theorem LinearMap.IsSymmetric.card_filter_eigenvalues_eq (hT) (hn) (μ : 𝕜) : Finset.card {i | hT.eigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ)` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:289` | 🟡 有限次元のみ | **壁核 `prolate_eigenvalue_count` の最近傍 template**（下記壁節参照）。ただし `= μ`（多重度）であって `> c`（閾値超え）でなく、asymptotic も持たない |
| 特異値（**有限次元限定**、finitely supported） | `noncomputable def LinearMap.singularValues : ℕ →₀ ℝ` | `Mathlib/Analysis/InnerProductSpace/SingularValues.lean:94` | 🟡 有限次元のみ | module docstring: "For a linear map `T` between **finite-dimensional** inner product spaces"。無限個の非零特異値（→0）を持つ真のコンパクト作用素版ではない |
| trace（**有限次元限定**） | `LinearMap.trace_eq_sum_inner` / `IsSymmetric.trace_eq_sum_eigenvalues` | `Mathlib/Analysis/InnerProductSpace/Trace.lean` | 🟡 `[Fintype ι] [FiniteDimensional 𝕜 E]` 必須 | |

### 1c. 不在（Mathlib Found 0）= 壁 or 大規模 self-build

| 概念 | loogle / rg 証拠 | 位置づけ |
|---|---|---|
| **prolate / Slepian / spheroidal** | loogle `"prolate"` → `unknown identifier 'prolate'`（Found 0）; `"Slepian"` → `unknown identifier`（Found 0）; `"spheroidal"` → Found 0（2026-07-14） | **真の壁核** → `wall:nyquist-2w-dof` |
| **固有値カウント関数 `#{i : λᵢ > c}` / Weyl 法則 / asymptotic count** | `rg -i "weyl.law\|eigenvalue.count\|asymptotic.*eigenvalue"` → prime counting のみ（無関係）。conclusion-shape 二段検索でも該当 0 | **壁核**（下記壁節） |
| **無限次元コンパクト作用素の固有値列（`ℕ → ℝ`、降順、→0 収束）** | `rg "eigenvalues.*Tendsto\|eigenvalueSeq\|ℕ →.*eigenvalue"` → Found 0。Spectrum.lean TODO: "Spectral theory for bounded self-adjoint operators" | 🔨 大規模 self-build（Mathlib 貢献余地。壁ではないが ~400-700 行） |
| **min-max / Courant-Fischer 変分表示（無限次元）** | Rayleigh.lean は top/bottom の iSup/iInf のみ（有限次元）。compact 版 top/bottom すら TODO（Rayleigh.lean docstring） | 🔨 self-build |
| **Hilbert-Schmidt / Schatten / trace-class 作用素理論** | loogle `"HilbertSchmidt"` → `unknown identifier`（Found 0）; `rg "Schatten\|IsHilbertSchmidt"` → Found 0 | 🔨 **計画が compactness 建設に想定した「Hilbert-Schmidt 経由」は不可**。代替: 有限ランク近似の極限 or 積分作用素 + Arzelà-Ascoli で compactness を直接示す（~300-500 行） |

**Phase 2 feasibility 判定（壁 vs plumbing の峻別）**:
- **genuine wall（確定）**= `prolate_eigenvalue_count`（`#{n | 1/2 < prolateEigenvalues T W n} ≈ ⌊2WT⌋ + O(log WT)` の集中不等式）。loogle Found 0（prolate/Slepian/spheroidal）+ conclusion-shape 二段検索でも eigenvalue-counting asymptotic は皆無。**最近傍 template = `card_filter_eigenvalues_eq`（Spectrum.lean:289、有限次元・多重度・閾値なし・asymptotic なし）から出発、self-build ~500-800 行**（LPS の核）。
- **壁でないが大規模 self-build（計画の見積り超過リスク）**= 作用素構成 `timeBandLimitingOp = P_W ∘ Q_T ∘ P_W` + 自己共役 + **コンパクト性（HS 不在のため代替ルート要）** + **無限次元固有値列の構成（Mathlib 不在、有限次元のみ）**。合計 ~700-1200 行。計画の「800-1500 行」見積りは概ね妥当だが、その大半は壁でなく genuine 建設で、`wall:nyquist-2w-dof` に集約されるのは asymptotic count のみ。

---

## Target 2 — Gaussian 過程 / 白色雑音測度【Phase 1 雑音、route α/β/γ 判定】

| 概念 | Mathlib API | file:line | 状態 | Phase 1 での扱い |
|---|---|---|---|---|
| 1 次元 Gaussian 測度 | `noncomputable def ProbabilityTheory.gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:220` | ✅ 既存 | per-sample 雑音 `gaussianReal 0 (N₀/2)`。`v = 0` で `Measure.dirac μ` に退化（要注意、下記 precondition box） |
| 有限直積測度 | `protected irreducible_def MeasureTheory.Measure.pi (μ : ∀ i, Measure (α i)) : Measure (∀ i, α i)`（`{ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]`） | `Mathlib/MeasureTheory/Constructions/Pi.lean:212` | ✅ 既存 | **route γ**: 有限窓 `Measure.pi (fun _ : Fin n => gaussianReal 0 σ)`（`n` 自由 → C4 遵守） |
| **無限直積測度（iid、Kolmogorov 拡張不要）** | `noncomputable def MeasureTheory.Measure.infinitePi (μ : (i : ι) → Measure (X i)) : Measure (Π i, X i)`（`{ι : Type*} {X : ι → Type*} [mX : ∀ i, MeasurableSpace (X i)]`、prob-measure は def 内 `if` で処理） | `Mathlib/Probability/ProductMeasure.lean:356` | ✅ 既存 | **route β**: `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σ)` = iid Gaussian 列測度。Ionescu-Tulcea `traj` 経由で構成、**Kolmogorov 拡張を要さない** |
| ℕ 添字無限直積（補助） | `noncomputable def MeasureTheory.Measure.infinitePiNat (μ : (n : ℕ) → Measure (X n)) : Measure (Π n, X n)`（`[hμ : ∀ n, IsProbabilityMeasure (μ n)]`） | `Mathlib/Probability/ProductMeasure.lean:112` | ✅ 既存 | `infinitePi` の ℕ 実装（`traj (const _ (μ (n+1))) 0 ∘ₘ Measure.pi …`） |
| Gaussian 過程の述語（**構成子でない**） | `public structure ProbabilityTheory.IsGaussianProcess {Ω E T : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop where hasGaussianLaw : ∀ I : Finset T, HasGaussianLaw (fun ω ↦ I.restrict (X · ω)) P` | `Mathlib/Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean:30` | ✅ 既存 | **述語であって測度を構成しない**。「既存の過程が Gaussian」を主張するのみ。関数空間測度の建設には使えない |
| Brownian の projective family（有限次元 marginal のみ） | `noncomputable def ProbabilityTheory.BrownianReal.projectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ)` + `isProjectiveMeasureFamily_projectiveFamily` | `Mathlib/Probability/BrownianMotion/GaussianProjectiveFamily.lean:81` | 🟡 marginal 止まり | module docstring: **"Kolmogorov's extension theorem (not in Mathlib yet)"** → 関数空間測度 `ℝ≥0 → ℝ` へ拡張**できない** |
| Ionescu-Tulcea 軌道核 | `noncomputable def ProbabilityTheory.Kernel.traj (a : ℕ) : Kernel (Π i : Iic a, X i) (Π n, X n)` / `trajMeasure` | `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:518,762` | ✅ 既存 | `infinitePiNat` の内部で使用済。iid 積測度の構成基盤 |

**不在（route α ブロッカー）**: **Kolmogorov 拡張定理**（有限次元 marginal → 関数空間測度）が Mathlib **不在**（GaussianProjectiveFamily.lean module docstring 明記）。したがって「共分散/projective family から `Lp ℂ 2` 上や `ℝ≥0 → ℝ` 上の Gaussian 測度を直接構成」する **route α は BLOCKED**。

**Phase 1 雑音測度 feasibility 判定（route 推奨）**:
- **route α（関数空間 Gaussian 直接）= BLOCKED**（Kolmogorov 拡張不在）。採るなら Kolmogorov 拡張を self-build する必要があり、これは prolate とは別の大規模壁。**非推奨**。
- **route β（iid サンプル無限積 pushforward）= 推奨・完全サポート**。`Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σ)` で ℕ 添字 iid Gaussian 列を構成 → 標本化再構成の pushforward。Kolmogorov 拡張不要。`n` を自由に保つ（C4 遵守）。
- **route γ（有限窓 `Measure.pi`）= 最小コスト・サポート**。per-T 窓の `n` サンプルを `Measure.pi (fun _ : Fin n => gaussianReal 0 σ)` で構成、`n` を自由 ℕ パラメータに保つ。operational capacity は各窓の有限次元計算のみ要するので、**mainline にはこれで十分**（無限積すら不要）。
- **判定**: 雑音測度は壁でない（route β/γ で genuine 構成可能）。計画の proposed `wall:cont-awgn-noise-measure` は **発動しない見込み**（route α のみが詰まる、それは選ばなければよい）。

---

## Target 3 — FourierTransform + 帯域制限 support + L² isometry【Phase 1 `IsBandlimited`】

| 概念 | Mathlib API | file:line | 状態 | Phase 1 での扱い |
|---|---|---|---|---|
| Fourier 積分（実 1 次元、`𝓕` 記法） | `def Real.fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) : E`（scoped `𝓕`） | `Mathlib/Analysis/Fourier/FourierTransform.lean:340` | ✅ 既存 | `IsBandlimited f W := ∀ ξ, W < |ξ| → 𝓕 f ξ = 0` の `𝓕`。WhittakerShannon が既に使用 |
| Fourier 積分（一般 VectorFourier） | `def VectorFourier.fourierIntegral (e) (μ) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) …` | `Mathlib/Analysis/Fourier/FourierTransform.lean:82` | ✅ 既存 | 多次元版（当面 1 次元で足りる） |
| **L² Fourier 変換（線形等長同型 = Plancherel）** | `def MeasureTheory.Lp.fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2)`（`[NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`、`[NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]`） | `Mathlib/Analysis/Fourier/LpSpace.lean:50` | ✅ 既存 | `E = ℝ`, `F = ℂ` で成立。帯域制限信号の L² 所属・エネルギー保存 |
| Plancherel（ノルム保存） | `theorem MeasureTheory.Lp.norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖` | `Mathlib/Analysis/Fourier/LpSpace.lean:89` | ✅ 既存 | Parseval 電力橋（per-sample 電力 ↔ 連続電力） |
| Plancherel（内積保存） | `theorem MeasureTheory.Lp.inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` | `Mathlib/Analysis/Fourier/LpSpace.lean:93` | ✅ 既存 | prolate 固有関数系での Parseval |
| Fourier 反転（積分形） | `theorem VectorFourier.integral_fourierIntegral_smul_eq_flip …` | `Mathlib/Analysis/Fourier/FourierTransform.lean:242` | ✅ 既存 | WhittakerShannon `fourier_eq_boxcar` で使用済のルート |
| 標本化定理（帯域制限、CLOSED） | `theorem …WhittakerShannon.whittaker_shannon_bandlimited (f : ℝ → ℂ) (hcont : Continuous f) (hf : Integrable f) (hFf : Integrable (𝓕 f)) (hband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) → 𝓕 f ξ = 0) (t : ℝ) : HasSum (fun n : ℤ => f n • (sincN (t - n) : ℂ)) (f t)` | `InformationTheory/Shannon/WhittakerShannon.lean:218` | ✅ 既存（sorryAx-free） | **規約 = 正規化 `[-1/2, 1/2]`**。実 W への scaling 橋が要る（下記） |

**不在 / self-build（小、壁でない）**:
- `IsBandlimited f W : Prop` in-project 述語（自明に定義可: `∀ ξ, W < |ξ| → 𝓕 f ξ = 0`、または `Set.Icc (-W) W` 補集合で 0）。基本補題（scaling / linearity / 帯域制限信号の `Lp ℂ 2` 所属）も数十行。
- **W スケーリング橋**: WhittakerShannon の正規化 `[-1/2, 1/2]`（サンプル間隔 1）↔ ShannonHartley の実 `W`（Hz、サンプル間隔 `1/(2W)`）。dilation 補題（`𝓕 (f ∘ (· * a))`）が要るが Mathlib の Fourier scaling 系（`Real.fourier_smul_convolution_eq` 等、Convolution.lean）から数十行。壁でない。

**Phase 1 IsBandlimited feasibility 判定**: 全て既存 or 小 self-build。壁でない。

---

## Target 4 — `Filter.limsup` / rate 機構【Phase 1 capacity def】

| 概念 | Mathlib API | file:line | 状態 | Phase 1 での扱い |
|---|---|---|---|---|
| limsup（一般フィルタ） | `def Filter.limsup (u : β → α) (f : Filter β) : α` | `Mathlib/Order/LiminfLimsup.lean:64` | ✅ 既存 | `contAwgnOperationalCapacity := Filter.limsup (fun T => log (M T) / T) atTop` |
| limsup 上界 | `theorem Filter.limsup_le_of_le {f : Filter β} {u : β → α} {a} …` | `Mathlib/Order/LiminfLimsup.lean:140` | ✅ 既存 | converse（≤）方向 |
| limsup 下界（頻繁） | `theorem Filter.le_limsup_of_frequently_le' …` | `Mathlib/Order/LiminfLimsup.lean:517` | ✅ 既存 | achievability（≥）方向 |
| limsup ≤ 判定 | `theorem Filter.limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault) …` | `Mathlib/Order/LiminfLimsup.lean:866` | ✅ 既存 | |
| ≤ limsup 判定 | `theorem Filter.le_limsup_iff {x : β} (h₁ …) …` | `Mathlib/Order/LiminfLimsup.lean:894` | ✅ 既存 | |
| in-project limsup 使用実績 | `InformationTheory/Shannon/BirkhoffErgodic.lean`（`birkhoffAverageReal_limsup_comp_T_ae` 等多数）、`Probability/TwoSidedExtension/Core.lean` | — | ✅ 既存実績 | limsup 機構は in-project で十分に運用済 |

**不在 / self-build（新規、壁でない）**:
- in-project に operational-capacity-as-limsup の既存 def は**無い**。`EntropyRate.lean:67` の `entropyRate` は `Filter.atTop.limUnder`（limsup でない）。→ `contAwgnOperationalCapacity` は新規 def（`Filter.limsup` ベース、straightforward）。
- `ε → 0` の織り込み（inf over ε / 二重極限）は capacity def の設計判断（親計画 Phase 1 feasibility unknown (c)）。limsup 自体は既存で、設計のみ要決定。

**Phase 1 capacity def feasibility 判定**: limsup 機構完備。新規 def は straightforward。壁でない。

---

## Target 5 — 既存 in-project 再利用面【Phase 3/4 橋、verbatim signature】

| 資産 | verbatim signature（型クラス前提込み） | file:line | 状態 | Phase 3/4 での接続 |
|---|---|---|---|---|
| per-sample 達成可能性 | `theorem awgn_achievability (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ))) {ε : ℝ} (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P), ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε` | `InformationTheory/Shannon/AWGN/Achievability.lean:52` | ✅ 既存（`@audit:ok`、genuine） | **Phase 3 主 leg**。per T 窓 `n = ⌊2WT⌋` サンプルで codebook |
| per-sample 逆定理 | `theorem awgn_converse (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P) (Pe : ℝ) (hPe : Pe = ((1/M : ℝ) * ∑ m : Fin M, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) : Real.log M ≤ (n : ℝ) * ((1/2) * Real.log (1 + P / (N : ℝ))) + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)` | `InformationTheory/Shannon/AWGN/Converse.lean:607` | ✅ 既存（`@[entry_point]`、genuine） | **Phase 4 主 leg**。上位固有関数射影後の per-letter 適用 |
| AWGN code 構造 | `structure AwgnCode (M n : ℕ) (P : ℝ) where encoder : Fin M → (Fin n → ℝ); decoder : (Fin n → ℝ) → Fin M; decoder_meas : Measurable decoder; power_constraint : ∀ m : Fin M, (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P` | `InformationTheory/Shannon/AWGN/Basic.lean:91` | ✅ 既存 | encoder = **固定長サンプルベクトル `Fin n → ℝ`**（per-sample 積み木、証明内構成用。C1 に注意: 連続 `ContAwgnCode` の def をこれに縮約してはならない） |
| AWGN チャネル | `noncomputable def awgnChannel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : …ChannelCoding.Channel ℝ ℝ`（`awgnChannel N h_meas x = gaussianReal x N`、`IsMarkovKernel` instance あり） | `InformationTheory/Shannon/AWGN/Basic.lean:67` | ✅ 既存 | per-sample チャネル核 |
| AWGN 容量 | `noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : ℝ := sSup ((fun p => (mutualInfoOfChannel p (awgnChannel N h_meas)).toReal) '' awgnPowerConstraintSet P)` | `InformationTheory/Shannon/AWGN/Basic.lean:146` | ✅ 既存 | per-sample 容量（`(1/2)log(1+P/N)`、`awgnCapacity_eq` で証明） |
| 標本化定理（HasSum 版） | `theorem whittaker_shannon_hasSum (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) : HasSum (fun n : ℤ => wsSignal F n • (sincN (t - n) : ℂ)) (wsSignal F t)` | `InformationTheory/Shannon/WhittakerShannon.lean:147` | ✅ 既存（sorryAx-free） | 信号 ↔ サンプル橋（Phase 3 reconstruct） |
| 標本化定理（帯域制限版） | `whittaker_shannon_bandlimited`（Target 3 に verbatim 記載） | `InformationTheory/Shannon/WhittakerShannon.lean:218` | ✅ 既存（sorryAx-free） | 同上 |
| 帯域制限容量（閉形式） | `noncomputable def bandlimitedAwgnCapacity (W N₀ P : ℝ) : ℝ := W * Real.log (1 + P / (N₀ * W))` | `InformationTheory/Shannon/ShannonHartley.lean:64` | ✅ 既存 | サンドイッチ両端の目標値 |
| per-sample 容量（2W 還元） | `noncomputable def perSampleAwgnCapacity (W N₀ P : ℝ) : ℝ := (1/2) * Real.log (1 + P / (N₀ * W))` | `InformationTheory/Shannon/ShannonHartley.lean:73` | ✅ 既存 | Phase 3/4 で per-sample ↔ 連続の橋 |
| 2W 恒等式（代数 leg、sorryAx-free） | `theorem twoW_perSample_eq_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) : 2 * W * perSampleAwgnCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P` | `InformationTheory/Shannon/ShannonHartley.lean:131` | ✅ 既存（`unfold; ring`） | Phase 5-full の代数 leg |
| load-bearing predicate（除去対象） | `def IsTwoWDegreesOfFreedom (W N₀ P C : ℝ) : Prop := C = 2 * W * perSampleAwgnCapacity W N₀ P`（`@audit:retract-candidate(load-bearing-predicate)`） | `InformationTheory/Shannon/ShannonHartley.lean:123` | 🟡 defect-leaning | **Phase 5-min で削除**。consumer = `shannon_hartley_formula` 1 decl のみ（下記 ripple） |
| 現行 headline（書換対象） | `theorem shannon_hartley_formula (W N₀ P : ℝ) (hW) (hN₀) (hP) (C : ℝ) (h_sampling : IsBandlimitedSamplingHypothesis W N₀ P) (h_kernel : IsBandlimitedKernel W) (h_two_w : IsTwoWDegreesOfFreedom W N₀ P C) : C = bandlimitedAwgnCapacity W N₀ P`（`@[entry_point]`、`@residual(wall:nyquist-2w-dof)`） | `InformationTheory/Shannon/ShannonHartley.lean:159` | 🟡 free-C load-bearing | **Phase 5-min で genuine 結論に書換**（`C := contAwgnOperationalCapacity …` で自由変数消滅） |

**ripple（`IsTwoWDegreesOfFreedom` 削除の blast radius、`scripts/dep_consumers.sh` の代替で機械確認済み）**: 直接 consumer = `shannon_hartley_formula` **1 decl / 同一 file**（`ShannonHartley.lean`）。ShannonHartley.lean 外の term-level 参照 0（`rg` で NormalizedSinc.lean は docstring 言及のみ）。effort は Phase 5 に ~50-120 行で吸収。

---

## 重要 preconditions box（事故が起きやすい前提）

- **`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`（スペクトル定理、Spectrum.lean:443）**: `[CompleteSpace E]` + `hT : IsCompactOperator T` + `hT' : T.IsSymmetric` が必須。`T : E →L[𝕜] E`（**continuous** linear map、`LinearMap` でなく）。`timeBandLimitingOp` は `Lp ℂ 2 →L[ℂ] Lp ℂ 2`（CompleteSpace OK）で建てること。
- **`finite_dimensional_eigenspace`（Spectrum.lean:463）**: `hμ : μ ≠ 0` 必須（零固有値の固有空間は無限次元でも可 = time-band 作用素の核）。カウント対象は非零固有値のみ。
- **`LinearMap.IsSymmetric.eigenvalues`（Spectrum.lean:279）**: `hn : Module.finrank 𝕜 E = n` を要求 = **有限次元専用**。無限次元 `Lp ℂ 2` には直接使えない → 固有値列は self-build。
- **`Measure.infinitePi`（ProductMeasure.lean:356）**: 各 `μ i` が `IsProbabilityMeasure` でないと `0`（def 内 `if h : ∀ i, IsProbabilityMeasure (μ i) then … else 0`）。`gaussianReal 0 σ` は `σ ≠ 0` で prob measure（`σ = 0` は `Measure.dirac 0`、これも prob measure なので OK だが退化）。
- **`gaussianReal μ v`（Real.lean:220）**: `v = 0` で `Measure.dirac μ`（退化）。雑音分散 `N₀/2 > 0` を保証すること（`N₀ > 0` 前提から従うが `.toNNReal` の非零を明示）。
- **`Measure.pi`（Pi.lean:212）**: `[Fintype ι]` 必須（有限窓 `Fin n` で OK）。SigmaFinite が要る補題あり（gaussianReal は finite measure なので充足）。
- **`fourierTransformₗᵢ`（LpSpace.lean:50）**: `E` に `[FiniteDimensional ℝ E] [BorelSpace E] [InnerProductSpace ℝ E]`、`F` に `[InnerProductSpace ℂ F] [CompleteSpace F]`。1 次元は `E = ℝ`, `F = ℂ`。
- **WhittakerShannon 規約**: 正規化 `[-1/2, 1/2]`（サンプル間隔 1）。実 W への変換はサンプル間隔 `1/(2W)` の dilation。電力/雑音簿記（per-sample `P/(2W)` ↔ 連続 `P`、per-sample 雑音 `N₀/2` ↔ PSD `N₀`）は ShannonHartley.lean:67-74 の docstring 規約に整合させること。

---

## 自作が必要な要素（優先度順）

1. **`contAwgnOperationalCapacity` / `ContAwgnCode` / 雑音測度 / `IsBandlimited`（Phase 1、mainline）** — 全て Mathlib 既存 primitive の糊。route γ（有限窓 `Measure.pi (gaussianReal)`）推奨、`n` 自由（C4）。~300-500 行。壁なし。**推奨実装**: capacity は `Filter.limsup`、code の encoder は `Fin M → (ℝ → ℂ)`（サンプルベクトルでない、C1）。pitfall: `ε → 0` の織り込み設計（inf over ε）。
2. **prolate 作用素の構成 + 自己共役 + コンパクト性（Phase 2 前半、stretch）** — `timeBandLimitingOp = P_W ∘ Q_T ∘ P_W : Lp ℂ 2 →L[ℂ] Lp ℂ 2`。自己共役は `isSelfAdjoint_iff_isSymmetric` + 射影の対称性。**コンパクト性は HS 不在のため代替ルート**（有限ランク近似の作用素ノルム極限 or 積分核の連続性 + Arzelà-Ascoli）。~300-500 行。壁ではないが計画の HS 前提が崩れている。
3. **無限次元コンパクト自己共役作用素の固有値列（降順・→0）（Phase 2 中盤、stretch）** — Mathlib は有限次元のみ。`orthogonalComplement_iSup_eigenspaces_eq_bot`（完全性）+ `finite_dimensional_eigenspace`（有限多重度）から `ℕ → ℝ` 降順列を構成し、→0 を示す。~400-700 行。Mathlib 貢献余地。壁ではないが大規模。
4. **`prolate_eigenvalue_count`（Phase 2 核、★真の壁）** — `#{n | 1/2 < prolateEigenvalues T W n} = ⌊2WT⌋ + O(log WT)`。loogle Found 0（prolate/Slepian/spheroidal/Weyl）。最近傍 template `card_filter_eigenvalues_eq`（Spectrum.lean:289）から出発するが asymptotic は皆無。~500-800 行 or honest `sorry + @residual(wall:nyquist-2w-dof)`。
5. **`IsBandlimited` 述語 + W-scaling 橋（Phase 1/3）** — 自明な述語 + dilation 補題数十行。壁なし。
6. **Parseval 電力橋（Phase 3）** — `Lp.norm_fourier_eq`（Plancherel）+ WhittakerShannon で per-sample ↔ 連続電力。~50-150 行。壁なし。

---

## Mathlib 壁の列挙（`@residual` 対象）

| slug | 命題 | loogle 証拠 | shared sorry lemma 推奨 |
|---|---|---|---|
| **`wall:nyquist-2w-dof`**（register 既存、audit-tags.md:77） | 時間帯域 DOF-per-second カウント: `#{n | 1/2 < prolateEigenvalues T W n} ≈ ⌊2WT⌋ + O(log WT)`（Landau-Pollak-Slepian 固有値集中） | `"prolate"` → `unknown identifier 'prolate'`（Found 0）; `"Slepian"` → Found 0; `"spheroidal"` → Found 0; `rg -i "weyl.law\|eigenvalue.count\|asymptotic.*eigenvalue"` → prime counting のみ（無関係）。2026-07-14 確認 | **既存 register slug に集約推奨**。Phase 2（`prolate_eigenvalue_count`）が SoT、Phase 4（converse）は transitive 継承、Phase 5-min（`contAwgn_eq_shannonHartley` body）も同 slug。Phase 3 achievability の edge-effect が guard-interval で閉じなければ下位カウント側で同 slug 一部共有 |

**壁でない（= plumbing / 大規模だが genuine 建設可能、`@residual` 不要）**:
- Hilbert-Schmidt 不在 → compactness は代替ルート（有限ランク近似 / Arzelà-Ascoli）で genuine 建設可能。Mathlib 壁でなく self-build コスト。
- Kolmogorov 拡張不在 → 雑音測度 route α のみブロック。route β/γ で回避可能（`Measure.infinitePi` / `Measure.pi`）。Mathlib 壁でなく route 選択。
- 無限次元固有値列不在 → Mathlib 有限次元のみだが、既存スペクトル定理（Spectrum.lean:443/463）の上に genuine 建設可能。大規模 self-build（Mathlib 貢献余地）。

**峻別まとめ（loogle Found 0 = necessary but not sufficient を遵守）**: genuine gap（真に Mathlib 不在で self-build しても textbook 難度）= **LPS asymptotic count のみ**。それ以外（作用素構成・コンパクト性・固有値列・雑音測度・帯域制限述語・capacity def）は既存資産への配線 + 大規模だが機械的な建設 = plumbing 相当（壁でない）。

---

## 撤退ラインへの距離

親計画の各 Phase 撤退ライン照合:

- **Phase 1 撤退ライン**（雑音測度が `IsGaussianProcess` 不足で詰まる → proposed `wall:cont-awgn-noise-measure`）: **発動しない見込み**。`IsGaussianProcess` は述語で測度を作らないが、雑音測度は `Measure.infinitePi (gaussianReal)`（route β）/ `Measure.pi (gaussianReal)`（route γ）で genuine 構成可能（Kolmogorov 拡張不要）。route α のみブロックされるが、それは選ばなければよい。**proposed wall は promote 不要**。
- **Phase 2 撤退ライン**（`prolate_eigenvalue_count` を `sorry + @residual(wall:nyquist-2w-dof)`、作用素の自己共役・コンパクト性も詰まれば同 slug 集約）: **触れる（設計通り）**。ただし在庫の追加所見: コンパクト性は HS 不在ゆえ計画想定の「HS 経由」が使えず、代替ルートで genuine 建設（壁でなく self-build 増）。**新規撤退ライン提案**: Phase 2 の作用素構成 + 固有値列（壁でない大規模建設）が想定超過で詰まった場合も、個別補題を `sorry + @residual(wall:nyquist-2w-dof)` に集約（compound 化しない、hypothesis bundling 禁止）。retreat exit = sorry + @residual、hypothesis bundling なし。
- **Phase 3 撤退ライン**（sinc-tail edge-effect が guard-interval で閉じない → 下位カウント側で `wall:nyquist-2w-dof` 一部共有）: **在庫では未確定**（feasibility unknown、実装で早期判定）。標本化定理は whole-real-line 全単射なので `[0,T]` 制限のエネルギー漏れが `limsup (T→∞)` で洗えるかは解析的判断で、在庫段階では GO/NO-GO 不能。**最も危険な未確認点**（下記要約）。
- **Phase 5-min 撤退ライン**（`contAwgn_eq_shannonHartley` body = 単一 honest wall-sorry、load-bearing predicate 除去後の honest tier-2 着地点）: **これが mainline の設計上の着地点**。在庫的に GO（経路上の全 API が既存 or in-project 定義可能）。

**mainline（Phase 1 → 5-min）判定: inventory 的に GO。** 経路上に Mathlib 壁 0、唯一の壁 `nyquist-2w-dof` は Phase 5-min の sorry 背後に隔離され、honest tier-2 の着地そのもの。

---

## Phase 1 着手 skeleton（`InformationTheory/Shannon/ShannonHartleyOperational.lean` 出だし案、~25 行）

```lean
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.LiminfLimsup
import InformationTheory.Shannon.ShannonHartley
import InformationTheory.Shannon.WhittakerShannon
import InformationTheory.Shannon.AWGN.Achievability  -- awgn_achievability
import InformationTheory.Shannon.AWGN.Converse        -- awgn_converse

namespace InformationTheory.Shannon.ShannonHartley

open MeasureTheory ProbabilityTheory Filter
open scoped Topology FourierTransform

/-- 帯域制限述語: 𝓕 f の台が [-W, W]。規約は WhittakerShannon の正規化 [-1/2,1/2] へ dilation で橋渡し。 -/
def IsBandlimited (f : ℝ → ℂ) (W : ℝ) : Prop := ∀ ξ : ℝ, W < |ξ| → 𝓕 f ξ = 0

/-- 連続時間 AWGN code: encoder は [0,T] essentially time-limited な帯域制限信号（C1: サンプルベクトルでない）。 -/
structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  encoder : Fin M → (ℝ → ℂ)
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W
  encoder_power : ∀ m, (∫ t in Set.Icc (0 : ℝ) T, ‖encoder m t‖ ^ 2) ≤ T * P
  -- decoder / errorProb は Phase 1 で雑音測度（route γ: Measure.pi (gaussianReal)）と共に決定

/-- operational capacity（毎秒レート、C2 primitive、2W を含まない）。M(T) の定義は Phase 1 で確定。 -/
noncomputable def contAwgnOperationalCapacity (W N₀ P : ℝ) : ℝ :=
  Filter.limsup (fun T : ℝ => Real.log (contAwgnMaxMessages T W N₀ P) / T) atTop  -- contAwgnMaxMessages: Phase 1 def

/-- mainline 着地（Phase 5-min）。body は Phase 3/4 完成まで honest wall-sorry。 -/
theorem contAwgn_eq_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  sorry -- @residual(wall:nyquist-2w-dof)

end InformationTheory.Shannon.ShannonHartley
```

（`contAwgnMaxMessages` / 雑音測度 / decoder / errorProb は Phase 1 で確定。上記は非循環設計 C1-C4 を満たす骨格の出発点。）

---

## M-fix inventory — faithful band-limit predicate + Paley-Wiener continuous representative (Phase 1-fix, 2026-07-15)

> 親計画: [`shannon-hartley-operational-moonshot-plan.md`](shannon-hartley-operational-moonshot-plan.md)（Phase 1-fix 節）。
> 対象: `IsBandlimited`（junk-0 defect）+ `ContAwgnCode.encoder`（a.e.-class / pointwise gap defect）の 2 根の def 修正。両 defect は独立 honesty audit で machine 確認済（`@audit:defect` stamps, ShannonHartleyOperational.lean L86/L181）。
> 検証日: 2026-07-15（loogle index `.lake/build/loogle.index`、Mathlib `.lake/packages/mathlib`）。全 loogle query は Found N 付きで下記に転記（negatives auditable）。

### 一行サマリ

**Q1（L² スペクトル台の `IsBandlimited` 述語）は既存 API で clean に定義可能 → GO。Q2（Paley-Wiener 連続代表 + sup bound `|f(t)| ≤ √(2W)·‖f‖₂`）は Mathlib 完全不在（Paley-Wiener / bandlimited / exponentialType すべて Found 0）だが、下請け部品（`Lp.fourierTransform` L¹→有界連続 op-norm≤1、`mono_exponent_of_measure_support_ne_top`、`integral_mul_le_Lp_mul_Lq_of_nonneg`、`Lp.norm_fourier_eq` Plancherel）は全て存在 → self-build ~200-350 行、うち genuine gap は「L²-FT ↔ pointwise L¹ `𝓕` 一致 bridge（L¹∩L²）」~150-250 行。** M-fix の def 再設計そのものは GO。sup bound は「statement を真にする load-bearing な数学的中身」なので honest sorry か encoder field 化のどちらか（下記 Unification verdict）。

---

### VERDICT — Q1（spectral-support `IsBandlimited` on raw `ℝ→ℂ`）: **GO**

既存 API で clean に書ける。推奨述語（`f : ℝ → ℂ`、L² spectral support ⊆ `[-W,W]`）:

```lean
open MeasureTheory
/-- `f` の L² Fourier 変換の台が `[-W,W]` に含まれる（junk-0 でない真の帯域制限）。 -/
def IsBandlimited (f : ℝ → ℂ) (W : ℝ) : Prop :=
  ∃ hf : MemLp f 2 volume,
    (𝓕 (hf.toLp f) : Lp ℂ 2 volume)
      =ᵐ[volume.restrict {ξ : ℝ | W < |ξ|}] 0
```

- `hf.toLp f : Lp ℂ 2 volume`（`MemLp.toLp`、LpSpace/Basic.lean:106）で raw 関数 → Lp 元。
- `𝓕`（= FourierTransform typeclass 記法）は `Lp.instFourierTransform`（LpSpace.lean:57、`fourierTransformₗᵢ ℝ ℂ` を fourier に）経由で `Lp ℂ 2 volume → Lp ℂ 2 volume` に解決。`E = ℝ`（`InnerProductSpace ℝ ℝ` + `FiniteDimensional ℝ ℝ` + `BorelSpace ℝ` 充足）, `F = ℂ`（`InnerProductSpace ℂ ℂ` + `CompleteSpace ℂ` 充足）, 測度は **volume 固定**（def に埋込、変更不可）。
- 「Lp 元が `{|ξ|>W}` 上 a.e. 0」は `⇑g =ᵐ[volume.restrict {ξ | W<|ξ|}] 0`（`Lp` の coeFn + `Filter.EventuallyEq`）で表現。**専用 support API 不要**（`Lp.indicator` 系も不要）。
- **依存する既存 lemma**: `MemLp.toLp`（Basic.lean:106）、`Lp.instFourierTransform`（LpSpace.lean:57）、`fourierTransformₗᵢ`（LpSpace.lean:50）。すべて既存、typeclass は `ℝ`/`ℂ` で自動充足。
- **落とし穴（Q1d）**: `IsBandlimited` を **証明**する側（Phase 3 の `synthSignal` = 有限 sinc 和、その pointwise `Real.fourierIntegral` は boxcar）で、explicit な L¹ `𝓕` 計算を L²-support 述語へ繋ぐには「`𝓕_L²(toLp f) =ᵐ Real.fourierIntegral f`（`f ∈ L¹∩L²`）」が要る。**この一致 lemma は Mathlib 不在**（`"toLp_fourier"` → Schwartz 版 4 件のみ、下表）。→ Q2 の bridge と同一の self-build。**述語定義は GO、述語の検証（Phase 3）は bridge self-build 依存**。

### VERDICT — Q2（Paley-Wiener 連続代表 + sup bound）: **NOT IN MATHLIB → self-build（~200-350 行、genuine gap は 1 bridge）**

「帯域制限 L² 関数は連続代表を持ち `|f(t)| ≤ √(2W)·‖f‖₂` を満たす」は Mathlib **不在**（Paley-Wiener 系すべて Found 0）。ただし標準証明の 3 サブステップの下請けは全て存在:

| サブステップ | Mathlib 資産 | 存在? | self-build 見積り |
|---|---|---|---|
| (i) compact-support FT の pointwise 反転 / 連続代表 | `Real.Lp.fourierTransform : Lp E 1 → V →ᵇ E`（op-norm≤1）+ `Integrable.fourierInv_fourier_eq`（L¹ 反転）。**ただし L²-FT↔pointwise L¹`𝓕` 一致 bridge は不在** | 部分（bridge 欠） | **~150-250 行（genuine gap）**。𝓢' 三角測量（両 Lp が `Lp.toTemperedDistribution` で 𝓢' に埋込、L²-FT↔𝓢'-FT = `Lp.fourier_toTemperedDistribution_eq` 既存、L¹-FT↔𝓢'-FT link を建設）で closable。textbook 難度でなく plumbing-heavy |
| (ii) Cauchy-Schwarz `L²→L¹` on `[-W,W]` | `MemLp.mono_exponent_of_measure_support_ne_top`（compact-support L²→L¹）+ `integral_mul_le_Lp_mul_Lq_of_nonneg`（Hölder、p=q=2） | ✅ 存在 | ~40-80 行（plumbing） |
| (iii) Plancherel `‖𝓕f‖₂=‖f‖₂` | `Lp.norm_fourier_eq`（LpSpace.lean:89） | ✅ 存在 | ~5 行 |

- **定数 `√(2W)` verbatim 確認**: `[-W,W]` の Lebesgue 測度 = `2W`。Cauchy-Schwarz `∫_{[-W,W]}1·|g| ≤ (∫_{[-W,W]}1²)^{1/2}(∫|g|²)^{1/2} = (2W)^{1/2}·‖g‖_{L²[-W,W]}`、`g` は `[-W,W]` に台を持つので `‖g‖_{L²[-W,W]}=‖g‖_{L²(ℝ)}=‖𝓕f‖₂`、Plancherel で `=‖f‖₂`。∴ `|f(t)| ≤ √(2W)·‖f‖₂`。**定数正しい**。
- **genuine gap は 1 つ**: (i) の「L²-inverse-FT = pointwise L¹ inverse integral（L¹∩L²）」bridge。これは Q1d の一致 bridge と実質同一物。**Mathlib wall（textbook 難度で不在）ではなく、既存 𝓢' scaffolding への配線 self-build**。よって `@residual` を切るなら `wall:` でなく plumbing 相当。ただし blast が大きく Phase 3 まで届かない場合は honest `sorry + @residual(plan:shannon-hartley-l2fourier-bridge)` が retreat exit。
- **合計 self-build**: ~200-350 行（bridge ~150-250 + Cauchy-Schwarz plumbing ~40-80 + Plancherel ~5 + 連続性配線）。

### VERDICT — Unification（(a) L²-support 述語 + (b) encoder 連続/`MemLp` field を 1 述語に？）

**部分的に 1 つに束ねられるが、sup bound は独立に扱うべき。** 推奨 `ContAwgnCode` field 形:

```lean
structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  encoder : Fin M → (ℝ → ℂ)                              -- ℝ→ℂ（L²-FT が ℂ 値）
  encoder_memLp : ∀ m, MemLp (encoder m) 2 volume         -- L² 所属（toLp の材料、defect#1 の非退化化）
  encoder_continuous : ∀ m, Continuous (encoder m)        -- pointwise 整合（defect#2、sampledSignal の a.e.-class gap を閉じる）
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W  -- L²-spectral-support（上記 Q1 述語）
  encoder_power : ∀ m, (∫ t in Set.Icc (0:ℝ) T, ‖encoder m t‖^2) ≤ T * P
  sampleCount : ℕ
  decoder : (Fin sampleCount → ℝ) → Fin M
  decoder_meas : Measurable decoder
```

- `IsBandlimited` は `MemLp` の存在を `∃` で内包するが、encoder は `toLp` を明示的に何度も使うので `encoder_memLp` を **別 field** に出す方が実用（`∃`-witness の unpack を各所で避ける）。
- `encoder_continuous` は defect#2 の直接修正（連続関数は pointwise 値で確定、`∫ f²` が真の関数を見る）。**ただし連続性だけでは sample を energy で bound できない**（tall-thin spike は連続でも `|f(t)|` 大・`‖f‖₂` 小が可能）。
- **sup bound `|f(t)| ≤ √(2W)‖f‖₂` は field 化 or Paley-Wiener 派生の二択**。これは「message set を有界化して statement を真にする load-bearing な中身」（下記 defect 解析）なので、`encoder_sup_bounded` を field に足すと **regularity precondition か load-bearing bundling かの判定が微妙**。判定: 「全ての帯域制限 L² 関数が満たす性質（= Paley-Wiener の帰結）」を field に置くのは **regularity（測度可能性と同格）で honest**。主定理の core（DOF count `nyquist-2w-dof`）を束ねるわけではない。ただし honest 度は Paley-Wiener 派生（field 不要）が上。**推奨: まず Paley-Wiener sup bound を self-build に挑戦、詰まれば `sorry + @residual` で publish（field 化は最後の手段）**。

### VERDICT — Overall feasibility: **GO-with-honest-sorry**

- **def 再設計（`IsBandlimited` L²-support 化 + encoder に `memLp`/`continuous` field 追加）= GO**（既存 API のみ、Q1 述語 clean、両 defect 根を溶かす）。
- **honest sorry になる sub-lemma = `bandlimited_sup_bound`（Paley-Wiener `|f(t)| ≤ √(2W)‖f‖₂`）とその下請け `l2Fourier_eq_fourierIntegral`（L²-FT ↔ pointwise L¹ `𝓕` on L¹∩L²）**。後者が genuine gap（~150-250 行、Mathlib wall でなく 𝓢' 配線）。
- **重大な非自明所見**: 「`Integrable f` を足せば junk-0 defect は消える」は **UNDER-HYPOTHESIS の罠**。帯域制限 L² 関数は一般に **L¹ でない**（sinc は L² だが L¹ でない、有限 sinc 和も同様）。`Integrable f` を課すと **狙いの信号クラス（essentially time-limited + band-limited、L² だが非 L¹）を除外**してしまう。だから owner の「L¹ `𝓕` を捨てて L²-FT へ」は正しく、L¹ 反転（`Continuous.fourierInv_fourier_eq`、両 `Integrable f` ∧ `Integrable (𝓕 f)` 要求）は対象クラスに直接使えない。

---

### API 在庫テーブル — Q1（spectral-support 述語の材料）

| 概念 | Mathlib API (verbatim signature, brackets kept) | file:line | conclusion (verbatim) | usable-as? |
|---|---|---|---|---|
| L² Fourier 変換（線形等長同型） | `def MeasureTheory.Lp.fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2)`. Context: `variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]` + `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`. 測度 = **volume 固定**（def 内 `toLpCLM ℂ (E := E) F 2 volume`） | `Mathlib/Analysis/Fourier/LpSpace.lean:50` | `(Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2)` | ✅ `E=ℝ, F=ℂ` で `IsBandlimited` の `𝓕`。**注意**: 名前で言及する decl は Mathlib 全体で **これ 1 件のみ**（loogle "Found one declaration"）→ spectral-support / coeFn / L¹一致 の専用 lemma は**皆無**、全て `𝓕` typeclass 記法経由 |
| FourierTransform instance（Lp を `𝓕` の定義域に） | `instance MeasureTheory.Lp.instFourierTransform : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where fourier := fourierTransformₗᵢ E F` | `Mathlib/Analysis/Fourier/LpSpace.lean:57` | — | ✅ `𝓕 (g : Lp ℂ 2 volume) : Lp ℂ 2 volume` を解決 |
| L² 反転 instance | `instance MeasureTheory.Lp.instFourierPair … fourierInv_fourier_eq := (Lp.fourierTransformₗᵢ E F).symm_apply_apply` | `Mathlib/Analysis/Fourier/LpSpace.lean:81` | `𝓕⁻ (𝓕 f) = f`（Lp 元、等長同型ゆえ自明可逆） | ✅ L²-inversion（pointwise でなく Lp 元同値） |
| raw 関数 → Lp 元 | `def MeasureTheory.MemLp.toLp (f : α → E) (h_mem_ℒp : MemLp f p μ) : Lp E p μ`. Context: `variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E]` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:106` | `Lp E p μ` | ✅ `hf.toLp f : Lp ℂ 2 volume`。typeclass 最小（`[NormedAddCommGroup ℂ]` のみ） |
| toLp の coeFn a.e. 一致 | `theorem MeasureTheory.MemLp.coeFn_toLp {f : α → E} (hf : MemLp f p μ) : hf.toLp f =ᵐ[μ] f` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:111` | `hf.toLp f =ᵐ[μ] f` | ✅ Lp 元 ↔ raw 関数の a.e. 橋 |
| Plancherel（ノルム保存） | `theorem MeasureTheory.Lp.norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖` | `Mathlib/Analysis/Fourier/LpSpace.lean:89` | `‖𝓕 f‖ = ‖f‖` | ✅ Q2 sup bound の (iii)、電力橋 |
| Plancherel（内積保存） | `theorem MeasureTheory.Lp.inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` | `Mathlib/Analysis/Fourier/LpSpace.lean:93` | `⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` | ✅ 固有関数系 Parseval |
| Schwartz 一致（**唯一の一致 lemma**） | `theorem SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2` | `Mathlib/Analysis/Fourier/LpSpace.lean:99` | `𝓕 (f.toLp 2) = (𝓕 f).toLp 2` | 🟡 **f が Schwartz 必須**。sinc/synthSignal は Schwartz でない → Phase 3 に直接使えない。一般 L¹∩L² 一致は不在 |
| L²-FT ↔ 𝓢'-FT 一致 | `theorem MeasureTheory.Lp.fourier_toTemperedDistribution_eq (f : Lp (α := E) F 2) : 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)` | `Mathlib/Analysis/Fourier/LpSpace.lean:126` | `𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)` | ✅ bridge self-build の L² 側 scaffold |
| Lp → 𝓢' 埋込（任意 p≥1） | `def MeasureTheory.Lp.toTemperedDistribution` + `theorem Lp.toTemperedDistribution_apply (f : Lp F p μ) [Fact (1 ≤ p)] …` | `Mathlib/Analysis/Distribution/TemperedDistribution.lean:169` | `∫ f·φ`（= 埋込の pairing） | ✅ **L¹ と L² 双方が 𝓢' に埋込 → bridge self-build の三角測量基盤** |

### API 在庫テーブル — Q2（Paley-Wiener sup bound の下請け）

| 概念 | Mathlib API (verbatim, brackets kept) | file:line | conclusion (verbatim) | usable-as? |
|---|---|---|---|---|
| L¹ FT = 有界連続関数（op-norm≤1） | `def Real.Lp.fourierTransformCLM : Lp (α := V) E 1 →L[ℂ] V →ᵇ E`（`LinearMap.mkContinuous … 1 …`）. Context: `variable {V W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]` + `V` finite-dim real IPS | `Mathlib/Analysis/Fourier/FourierTransform.lean:572` | `Lp (α := V) E 1 →L[ℂ] V →ᵇ E` | ✅ 「compact-support L²(⊆L¹) の逆FT は有界連続、sup≤L¹ノルム」の (i) 部品 |
| L¹ FT の pointwise 一致 | `theorem Real.Lp.fourierTransform_apply (f : Lp (α := V) E 1) (x : V) : Lp.fourierTransform f x = 𝓕 (f : V → E) x` | `Mathlib/Analysis/Fourier/FourierTransform.lean:559` | `Lp.fourierTransform f x = 𝓕 (f : V → E) x` | ✅ L¹-FT ↔ `Real.fourierIntegral` pointwise |
| L¹ FT of toLp | `theorem Real.fourierTransform_toLp {f : V → E} (hf : MemLp f 1) : (Lp.fourierTransform hf.toLp : V → E) = 𝓕 f` | `Mathlib/Analysis/Fourier/FourierTransform.lean:563` | `(Lp.fourierTransform hf.toLp : V → E) = 𝓕 f` | ✅ raw L¹ 関数の FT = pointwise `𝓕` |
| L¹ FT の連続性（VectorFourier） | `theorem VectorFourier.fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (hf : Integrable f μ) : Continuous (fourierIntegral e μ L f)` | `Mathlib/Analysis/Fourier/FourierTransform.lean:163` | `Continuous (fourierIntegral e μ L f)` | ✅ WhittakerShannon が既用（L221-224）。`Real.fourierIntegral_continuous` は不在、これ経由 |
| L¹ 反転（continuity point） | `theorem MeasureTheory.Integrable.fourierInv_fourier_eq (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V} (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v`. Context: `variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]` | `Mathlib/Analysis/Fourier/Inversion.lean:165` | `𝓕⁻ (𝓕 f) v = f v` | 🟡 **両 `Integrable f` ∧ `Integrable (𝓕 f)` 要求 = L¹ のみ**。帯域制限 L² f は一般に非 L¹ → 対象クラスに直接不可（UNDER-HYP 罠の根拠） |
| L¹ 反転（全点、連続版） | `theorem Continuous.fourierInv_fourier_eq (h : Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f` | `Mathlib/Analysis/Fourier/Inversion.lean:177` | `𝓕⁻ (𝓕 f) = f` | 🟡 同上（L¹ 限定） |
| compact-support L²→L¹ | `lemma MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top {p q : ℝ≥0∞} {f : α → ε'} (hfq : MemLp f q μ) {s : Set α} (hf : ∀ x, x ∉ s → f x = 0) (hs : μ s ≠ ∞) (hpq : p ≤ q) : MemLp f p μ`. Context: `variable {α ε' : Type*} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε'] [ESeminormedAddMonoid ε']` | `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:146` | `MemLp f p μ` | ✅ `𝓕f`（台⊆`[-W,W]`）が L¹。Cauchy-Schwarz (ii) の入口 |
| 有限測度 L²→L¹ | `theorem MeasureTheory.MemLp.mono_exponent {p q : ℝ≥0∞} [IsFiniteMeasure μ] (hfq : MemLp f q μ) (hpq : p ≤ q) : MemLp f p μ` | `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean:116` | `MemLp f p μ` | ✅ 制限測度版（`volume.restrict [-W,W]` は finite） |
| Hölder（Cauchy-Schwarz p=q=2） | `theorem MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) : ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1181` | `∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1/p) * (∫ a, g a ^ q ∂μ) ^ (1/q)` | ✅ `1·|g|` に適用で (ii)。`ENNReal.lintegral_mul_le_Lp_mul_Lq`（MeanInequalities.lean）が lintegral 版 backup |
| in-project 連続代表 / sup bound | — | — | — | ❌ **不在**。WhittakerShannon は `whittaker_shannon_bandlimited`（L221）で `Continuous f ∧ Integrable f ∧ Integrable (𝓕 f)` を **仮定**（連続代表を構成しない）。NormalizedSinc も sup bound 資産なし（`sincN_le_one` は sinc 自身の bound、Paley-Wiener でない） |

---

### 重要 preconditions box（事故が起きやすい前提）

- **`Lp.fourierTransformₗᵢ`（LpSpace.lean:50）**: 測度は **volume に固定**（def 内で明示、time-out 回避のため）。`E=ℝ`（`[MeasurableSpace ℝ] [BorelSpace ℝ] [InnerProductSpace ℝ ℝ] [FiniteDimensional ℝ ℝ]` 全て自動）, `F=ℂ`（`[InnerProductSpace ℂ ℂ] [CompleteSpace ℂ]` 自動）。**別測度（`volume.restrict` 等）では `𝓕` typeclass が発火しない** → spectral support は「`𝓕`（全 volume 上）の Lp 元を `restrict` 測度で a.e.0」の形で書く（`𝓕` 自体は volume 上）。
- **名前で言及される `fourierTransformₗᵢ` decl は 1 件のみ**: spectral-support / pointwise coeFn / L¹一致 の専用 lemma は**存在しない**。`𝓕` typeclass 記法 + `norm_fourier_eq` / `inner_fourier_eq` / `fourier_toTemperedDistribution_eq` だけが道具。「`𝓕 g` の pointwise 値」を取り出す lemma を探すのは徒労 → **Lp 元同値 / a.e. 等式で押す**。
- **Fourier 反転は L¹ 限定**（`Integrable.fourierInv_fourier_eq`、Inversion.lean:165）: `Integrable f` ∧ `Integrable (𝓕 f)` 両方要求。**帯域制限 L² 関数は一般に非 L¹** なので、対象信号に直接使うと空回り。L²-inversion（`instFourierPair`、Lp 元同値）を使い、pointwise 化は `Real.Lp.fourierTransform`（有界連続、compact-support 側）で行う。
- **`MemLp.mono_exponent_of_measure_support_ne_top`（CompareExp.lean:146）**: `hs : μ s ≠ ∞`（台が有限測度）必須。`{ξ | ξ ∈ [-W,W]}` は `μ = volume` で `2W < ∞` OK。**注意**: `p ≤ q` の向き（L^q → L^p、`q=2, p=1`）。
- **`integral_mul_le_Lp_mul_Lq_of_nonneg`（Bochner/Basic.lean:1181）**: `hpq : p.HolderConjugate q`（`1/p+1/q=1`）。Cauchy-Schwarz は `p=q=2`。非負性 `0 ≤ᵐ f, 0 ≤ᵐ g` 要求（`f=1`, `g=|𝓕f|` で充足）。
- **`Integrable f` を encoder field に足すな**: junk-0 は消えるが対象信号クラス（非 L¹ の band-limited）を除外する UNDER-HYP。L² membership（`MemLp _ 2`）を使うこと。

---

### 自作が必要な要素（優先度順）

1. **`l2Fourier_eq_fourierIntegral`（L²-FT ↔ pointwise L¹ `𝓕` on L¹∩L²）【genuine gap / bridge / ~150-250 行】** — `f ∈ L¹∩L²` に対し `⇑(𝓕 (hf₂.toLp f)) =ᵐ[volume] Real.fourierIntegral f`（`hf₂ : MemLp f 2`）。**推奨実装**: 𝓢' 三角測量。両 `toLp`（L¹/L²）が同一 a.e. 関数から `Lp.toTemperedDistribution` で同じ 𝓢' 元へ（`toTemperedDistribution_apply` = `∫ f·φ` は p 非依存）→ L²-FT↔𝓢'-FT（`fourier_toTemperedDistribution_eq` 既存）+ L¹-FT↔𝓢'-FT（`Real.Lp.fourierTransform` を 𝓢' に埋込む link を建設）→ 一致。**Mathlib wall でなく既存 scaffolding 配線**。詰まれば `sorry + @residual(plan:shannon-hartley-l2fourier-bridge)`。
2. **`bandlimited_sup_bound`（Paley-Wiener `|f(t)| ≤ √(2W)·‖f‖₂`）【~60-120 行、(1) 依存】** — 帯域制限 L² `f` の連続代表に対する sup bound。**推奨**: (1) の bridge で `𝓕f` を pointwise 化 → `mono_exponent_of_measure_support_ne_top` で L¹ → `Real.Lp.fourierTransform`（sup≤L¹ノルム）で連続代表化 → `integral_mul_le_Lp_mul_Lq_of_nonneg`（Cauchy-Schwarz）+ `Lp.norm_fourier_eq`（Plancherel）で `√(2W)·‖f‖₂`。**部品は全存在、(1) の bridge のみ gap**。
3. **`IsBandlimited` 述語（L²-support）【~10-20 行】** — Q1 verdict の述語。既存 API のみ、壁なし。
4. **`ContAwgnCode` 再設計（`encoder : Fin M → (ℝ→ℂ)` + `encoder_memLp` / `encoder_continuous` field 追加）【~20-40 行 + downstream ripple】** — defect#2 修正。`errorProbAt` / `sampledSignal` は `encoder m` が連続なので pointwise well-defined、`encoder_power` の `∫‖f‖²` が真の関数を見る。ripple: `sampledSignal` の型（`ℝ→ℝ` → `ℝ→ℂ` の実部 or `Complex.abs`）調整。
5. **連続代表の一意性 / sampledSignal 整合【~30-60 行】** — `encoder_continuous` から「a.e.-class の代表が pointwise 値で確定」。`MemLp.coeFn_toLp` + 連続関数の a.e.一致 → 全点一致（`Continuous.ae_eq_iff` 系）。

---

### Mathlib 壁の列挙（`@residual` 対象）

| slug 候補 | 命題 | loogle 証拠（Found N、query 転記） | 壁 or plumbing |
|---|---|---|---|
| （新）`plan:shannon-hartley-l2fourier-bridge` | L²-FT ↔ pointwise L¹ `Real.fourierIntegral` 一致（L¹∩L²） | `"toLp_fourier"` → Found 4（全 Schwartz 版のみ）; `"fourierIntegral_eq_fourier"` → Found 0; `"coeFn_fourier"` → Found 1（`coeFn_fourierLp`、AddCircle 版、無関係） | **plumbing（wall でない）**。既存 𝓢' scaffolding（`Lp.toTemperedDistribution` + `fourier_toTemperedDistribution_eq`）への配線 self-build。textbook 難度でない → `wall:` でなく `plan:` |
| — | Paley-Wiener 定理（任意形） | `"PaleyWiener"` → Found 0; `"Paley"` → Found 0; `"bandlimited"` → Found 0; `"BandLimited"` → Found 0; `"exponentialType"` → Found 0 | **Mathlib 完全不在**だが下請け部品（(i)(ii)(iii)）全存在 → self-build（(1) bridge のみ gap）。単独 `@residual` 不要、`bandlimited_sup_bound` を (1) 依存で建設 or `sorry + @residual(plan:…-bridge)` |
| `wall:nyquist-2w-dof`（既存 register） | 時間帯域 DOF-per-second カウント | （Phase 0 inventory で確認済、本 M-fix と独立） | genuine wall（本 M-fix の scope 外、主定理 body の別 residual） |

**shared sorry lemma 推奨**: Q1d の一致 bridge（Phase 3 検証）と Q2 の連続代表 bridge (i) は **同一物**（`l2Fourier_eq_fourierIntegral`）。**両者を 1 本の shared lemma に集約推奨**（audit-tags.md「Shared Mathlib walls」）。散逸させない。

**loogle Found 0 確認（necessary but not sufficient 遵守、二段検索済）**: Paley-Wiener 系は name-search 0 に加え、conclusion-shape の代替（`Real.Lp.fourierTransform` 有界連続 + inversion）を探索し「単独定理は不在だが部品充足」を確認。→ genuine gap は L²↔L¹ 一致 bridge **1 本のみ**、それも 𝓢' 配線で closable な plumbing。

---

### 撤退ラインへの距離

親計画の Phase 1-fix 撤退ライン照合:

- **defect 修正そのもの（`IsBandlimited` L²化 + encoder field 追加）: 発動しない**。既存 API（`fourierTransformₗᵢ` / `MemLp.toLp` / `Lp.norm_fourier_eq`）で GO。両 defect 根を溶かす。
- **Paley-Wiener sup bound（statement を真にする load-bearing な中身）: 触れる**。Mathlib 完全不在だが self-build 可能（(1) bridge のみ gap、~200-350 行）。**新規撤退ライン提案**: (1) の L²↔L¹ 一致 bridge が 𝓢' 配線で想定超過して詰まった場合、`bandlimited_sup_bound` を `sorry + @residual(plan:shannon-hartley-l2fourier-bridge)` で honest 化して encoder field は足さない（hypothesis bundling 禁止）。retreat exit = sorry + @residual、hypothesis bundling なし。sup bound を field 化する degenerate fallback は「全 band-limited L² が満たす regularity」の範囲でのみ許容（core `nyquist-2w-dof` を束ねない）。
- **主定理 body（`contAwgn_eq_shannonHartley`）: M-fix 後も `sorry + @residual(wall:nyquist-2w-dof)` に着地**（defect 解消で「FALSE-as-framed」→「wall-blocked honest tier-2」に復帰）。M-fix の目的は `@audit:defect(false-statement)` を外して honest wall-sorry に戻すこと。

**M-fix 判定: GO-with-honest-sorry。** def 再設計は既存 API のみ（Q1 GO）。唯一の self-build gap = L²↔L¹ FT 一致 bridge（plumbing、~150-250 行、詰まれば `plan:` residual）。sup bound の load-bearing 性が最大の注意点（連続性 field だけでは message set を有界化できない）。

---

### M-fix 着手 skeleton（`ShannonHartleyOperational.lean` 差分案、~28 行）

```lean
import Mathlib.Analysis.Fourier.LpSpace          -- fourierTransformₗᵢ, norm_fourier_eq
import Mathlib.MeasureTheory.Function.LpSpace.Basic  -- MemLp.toLp
-- （既存 import は維持）

namespace InformationTheory.Shannon.ShannonHartley
open MeasureTheory
open scoped FourierTransform

/-- 帯域制限（真）: L² Fourier 変換の台が `[-W,W]`。junk-0 でない。 -/
def IsBandlimited (f : ℝ → ℂ) (W : ℝ) : Prop :=
  ∃ hf : MemLp f 2 volume,
    (𝓕 (hf.toLp f) : Lp ℂ 2 volume) =ᵐ[volume.restrict {ξ : ℝ | W < |ξ|}] 0

/-- 帯域制限 L² 関数の Paley-Wiener sup bound（連続代表、self-build）。 -/
theorem bandlimited_sup_bound (f : ℝ → ℂ) (W : ℝ) (hW : 0 < W)
    (hf : MemLp f 2 volume) (hbl : IsBandlimited f W) (hcont : Continuous f) (t : ℝ) :
    ‖f t‖ ≤ Real.sqrt (2 * W) * ‖hf.toLp f‖ := by
  sorry -- @residual(plan:shannon-hartley-l2fourier-bridge) — L²-FT↔pointwise 𝓕 一致 + Cauchy-Schwarz + Plancherel

structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  encoder : Fin M → (ℝ → ℂ)
  encoder_memLp : ∀ m, MemLp (encoder m) 2 volume
  encoder_continuous : ∀ m, Continuous (encoder m)
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W
  encoder_power : ∀ m, (∫ t in Set.Icc (0 : ℝ) T, ‖encoder m t‖ ^ 2) ≤ T * P
  sampleCount : ℕ
  decoder : (Fin sampleCount → ℝ) → Fin M
  decoder_meas : Measurable decoder

end InformationTheory.Shannon.ShannonHartley
```

（`sampledSignal` は `encoder m : ℝ→ℂ` の連続代表を pointwise 読む形に、`errorProbAt` は実部 or `‖·‖` で実サンプル化。主定理 body は `@residual(wall:nyquist-2w-dof)` のまま。M-fix 完了で `@audit:defect(false-statement)` / `@audit:defect(degenerate)` を除去し honest tier-2 に復帰。）
