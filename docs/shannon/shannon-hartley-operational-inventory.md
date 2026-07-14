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
