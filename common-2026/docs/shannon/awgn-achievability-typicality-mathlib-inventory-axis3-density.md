# AWGN Achievability Typicality — 軸 3 (joint density / rnDeriv / differentialEntropy) Mathlib API 在庫

> **Parent plan**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> (Phase 0, Phase B, 判断 #3)。
>
> **Scope**: Cover-Thomas 9.2 の jointly typical set 定義に必要な
> `joint density / rnDeriv / differentialEntropy / klDiv` 系 Mathlib API を
> per-lemma 構造化棚卸。3 形式 (Option α: rnDeriv 形 / Option β: differentialEntropy 形 /
> Option γ: klDiv 形) のうち、Phase B-2 (P→1)、B-3 (volume bound)、B-4 (indep-product)
> の compose に最も適合する形式を判定する。
>
> **Sister inventories**: 軸 1 (codebook 測度、決着済 → 2 段 `Measure.pi` 採用) /
> 軸 2 (continuous AEP) / 軸 4 (expurgation) / 軸 5 (球殻 volume)。

## 一行サマリ

**軸 3 の 1-d Gaussian closed-form + KL chain rule は完備。n-fold 化の本体 (`klDiv_pi_eq_sum` / `mutualInfo_pi_eq_sum`) も Common2026 が既保有。一方、`(joint).rnDeriv (volume.prod volume)` の closed form と `Measure.pi`-rnDeriv 系の Mathlib 直接補題は完全不在 (loogle で 0 declarations 確認済)。**

**判断 #3 推奨: Option γ (`klDiv` 形)**。理由:
1. `klDiv_compProd_eq_add` (Mathlib) + `klDiv_pi_eq_sum` (Common2026) で n-fold が無条件 chain rule で sum 化、Phase C union bound (B-4 indep-product) と直結。
2. Common2026 の `mutualInfo := klDiv (joint) (prod marginal)` 定義が既に Option γ。`mutualInfoOfChannel` の awgn 版経路で AwgnCode 評価との接続済。
3. Option α (rnDeriv 形) は `(joint).rnDeriv (volume.prod)` を直接書くと `f log f` 分解が必要だが `Measure.pi` × `rnDeriv` の Mathlib 補題は **0 件** (loogle 確認)、Common2026 既存の `MultivariateDiffEntropy` も honest hyp 化 (`h_llr_split`) で逃げている。同じ pivot を強いられる。
4. Option β (`differentialEntropy` 形) は `f log f` 直書きが必要で n-d への generalization 補題 `differentialEntropy_pi` が **Mathlib 不在 + Common2026 自作** (`jointDifferentialEntropyPi`)。さらに subadditivity (`jointDifferentialEntropyPi_le_sum`) は **load-bearing hyp `h_llr_split` 残置**。

詳細は末尾「§判断 #3」。

---

## サブ項目 3.1: 1-d Gaussian の基本量

### `ProbabilityTheory.gaussianReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:200`
- **signature** (verbatim):
  ```lean
  noncomputable
  def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
    if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)
  ```
- **type-class prerequisites**: 無 (definition)
- **explicit args**: `μ : ℝ`, `v : ℝ≥0`
- **conclusion**: `Measure ℝ`
- **applicability to 軸 3**: 全 Option (α/β/γ) の入力測度の核。`σ² = (P : ℝ≥0)` で 1-d Gaussian。

### `ProbabilityTheory.rnDeriv_gaussianReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:240`
- **signature** (verbatim):
  ```lean
  lemma rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) :
      ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v
  ```
- **type-class prerequisites**: 無
- **explicit args**: `μ : ℝ`, `v : ℝ≥0`
- **conclusion**: `∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v` (i.e., `=ᵐ[volume]`)
- **applicability to 軸 3**: **Option α (rnDeriv 形)** の核心。1-d marginal の rnDeriv は閉じている。n-d product への持ち上げ補題は別途必要 (§3.2 参照、不在)。

### `Common2026.Shannon.differentialEntropy_gaussianReal` (既存自作)

- **file:line**: `Common2026/Shannon/DifferentialEntropy.lean:406`
- **signature** (verbatim):
  ```lean
  theorem differentialEntropy_gaussianReal
      (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      differentialEntropy (gaussianReal m v)
        = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)
  ```
- **type-class prerequisites**: 無 (関数 args のみ)
- **explicit args**: `m : ℝ`, `v : ℝ≥0`, `hv : v ≠ 0`
- **conclusion**: `differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)`
- **applicability to 軸 3**: **Option β (differentialEntropy 形)** の核心。1-d 値は閉式。n-d は §3.3 参照。

### `Common2026.Shannon.klDiv_gaussianReal_gaussianReal_eq` (既存自作)

- **file:line**: `Common2026/Shannon/DifferentialEntropy.lean:791`
- **signature** (verbatim):
  ```lean
  theorem klDiv_gaussianReal_gaussianReal_eq
      (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
      (klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)).toReal
        = (1/2) * (Real.log ((v₂ : ℝ) / v₁) + (v₁ : ℝ) / v₂
                    + (m₁ - m₂)^2 / v₂ - 1)
  ```
- **type-class prerequisites**: 無 (関数 args のみ)
- **explicit args**: `m₁ m₂ : ℝ`, `v₁ v₂ : ℝ≥0`, `hv₁ : v₁ ≠ 0`, `hv₂ : v₂ ≠ 0`
- **conclusion**: 上記 (1-d Gaussian KL closed form)
- **applicability to 軸 3**: **Option γ (klDiv 形)** の核心。1-d Gaussian KL は閉式。**Mathlib 不在** (loogle で `InformationTheory.klDiv, ProbabilityTheory.gaussianReal` = 0 declarations 確認)。

### `ProbabilityTheory.gaussianReal_absolutelyContinuous`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:226`
- **signature** (verbatim):
  ```lean
  lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      gaussianReal μ v ≪ volume
  ```
- **type-class prerequisites**: 無
- **explicit args**: `μ : ℝ`, `v : ℝ≥0`, `hv : v ≠ 0`
- **conclusion**: `gaussianReal μ v ≪ volume`
- **applicability to 軸 3**: rnDeriv / KL の AC 前提を埋める基本補題。

---

## サブ項目 3.2: Joint density (X, Y) where Y = X + Z

### `ProbabilityTheory.gaussianReal_conv_gaussianReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:613`
- **signature** (verbatim):
  ```lean
  lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
      (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)
  ```
- **type-class prerequisites**: 無 (mΩ / Ω / P は section variable)
- **explicit args**: implicit `m₁ m₂ : ℝ`, `v₁ v₂ : ℝ≥0`
- **conclusion**: `(gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)`
- **applicability to 軸 3**: AWGN 出力 `Y = X + Z` の law。`X ∼ 𝒩(0, P)`, `Z ∼ 𝒩(0, N)` から `Y ∼ 𝒩(0, P+N)` を導く。Phase B-3 の output entropy `(1/2) log(2πe(P+N))` の起点。

### `ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:624`
- **signature** (verbatim):
  ```lean
  lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
      {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
      (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
      P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)
  ```
- **type-class prerequisites**: 無 (Ω は section variable)
- **explicit args**: `hXY : IndepFun X Y P`, `hX : P.map X = gaussianReal m₁ v₁`, `hY : P.map Y = gaussianReal m₂ v₂`
- **conclusion**: `P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)`
- **applicability to 軸 3**: AWGN setup `Y = X + Z`、`X ⟂ Z` から `Y` の周辺分布を Mathlib 形で取れる。Phase B-3 で `h(Y) = (1/2) log(2πe(P+N))` を `differentialEntropy_gaussianReal` 経由で確定する直接ルート。

### **不在**: `(p ⊗ₘ W).rnDeriv (volume.prod volume)` の closed form

- **状態**: ❌ **Mathlib に直接補題不在** (loogle `MeasureTheory.Measure.rnDeriv, MeasureTheory.Measure.prod` = 0 declarations)
- **代替**: `ProbabilityTheory.rnDeriv_compProd` (Kernel 形、§3.4 参照) は存在するが、`(volume.prod volume)` への分母は kernel composition product 形ではないため、直接適用不可。
- **applicability to 軸 3**: **Option α (rnDeriv 形) の致命的 gap**。`(joint).rnDeriv (volume.prod volume)` を `gaussianPDF(x) * gaussianPDF(y - x)` 形に展開する補題は自作必要。Common2026 既存の `MultivariateDiffEntropy.klDiv_prod_marginals_toReal_eq_sum_sub_joint` は同じ gap を `h_llr_split` honest hyp で吸収している (line 97-102)。

### **不在**: `klDiv (gaussianReal _ _) (gaussianReal _ _)` の Mathlib 補題

- **状態**: ❌ **Mathlib に 0 declarations** (loogle `InformationTheory.klDiv, ProbabilityTheory.gaussianReal` = 0)
- **代替**: Common2026 `klDiv_gaussianReal_gaussianReal_eq` (上記 §3.1) が既に書かれている。
- **applicability to 軸 3**: Option γ (klDiv 形) は **Common2026 既存資産で完備**。新規実装不要。

---

## サブ項目 3.3: n-fold (i.i.d. extension)

### `Common2026.Shannon.jointDifferentialEntropyPi` (既存自作)

- **file:line**: `Common2026/Shannon/MultivariateDiffEntropy.lean:58`
- **signature** (verbatim):
  ```lean
  noncomputable def jointDifferentialEntropyPi {n : ℕ} (μ : Measure (Fin n → ℝ)) : ℝ :=
    ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume
  ```
- **type-class prerequisites**: 無
- **explicit args**: `n : ℕ`, `μ : Measure (Fin n → ℝ)`
- **conclusion**: `ℝ`
- **applicability to 軸 3**: **Option β (differentialEntropy 形)** の n-d 一般化。Mathlib 不在 (`differentialEntropy_pi` は 0 declarations) のため Common2026 自作。1-d の `differentialEntropy` と shape を完全に揃えてある (`Real.negMulLog ((μ.rnDeriv volume z).toReal)` 形) ので 1-d 補題が `volume_eq_prod` で再利用可能。

### `Common2026.Shannon.jointDifferentialEntropyPi_le_sum` (既存自作)

- **file:line**: `Common2026/Shannon/MultivariateDiffEntropy.lean:280`
- **signature** (verbatim):
  ```lean
  theorem jointDifferentialEntropyPi_le_sum
      {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
      [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]
      (h_marg_ac : ∀ i, (μ.map (fun z => z i)) ≪ volume)
      (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
      (h_joint_ac : μ ≪ Measure.pi (fun i => μ.map (fun z => z i)))
      (h_llr_split :
        (fun z => llr μ (Measure.pi (fun i => μ.map (fun z => z i))) z)
          =ᵐ[μ]
        (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                    - (∑ i, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal))))
      (h_int_marg : ∀ i,
        Integrable (fun z => Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal)) μ)
      (h_int_joint :
        Integrable (fun z => Real.log ((μ.rnDeriv volume z).toReal)) μ)
      (h_marg_id : ∀ i,
        (∫ z, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal) ∂μ)
          = ∫ x, Real.log (((μ.map (fun z => z i)).rnDeriv volume x).toReal)
              ∂(μ.map (fun z => z i))) :
      jointDifferentialEntropyPi μ
        ≤ ∑ i, differentialEntropy (μ.map (fun z => z i))
  ```
- **type-class prerequisites**: `[IsProbabilityMeasure μ]`, `[∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]`
- **explicit args**: 6 hyps (`h_marg_ac`, `hμ_ac`, `h_joint_ac`, `h_llr_split`, `h_int_marg`, `h_int_joint`, `h_marg_id`)
- **conclusion**: `jointDifferentialEntropyPi μ ≤ ∑ i, differentialEntropy (μ.map (fun z => z i))`
- **applicability to 軸 3**: **Option β subadditivity の honest hyp 残置**。`h_llr_split` (joint log = sum marginal log) は **Mathlib `pi_withDensity` 不在を吸収する load-bearing hyp** (audit:suspect タグ付き、line 89/175/214/279)。Option β 採用時には Phase B-3 / B-4 で同じ honest hyp を担ぐことになる。

### `Common2026.Shannon.klDiv_pi_eq_sum` (既存自作、決定的)

- **file:line**: `Common2026/Shannon/MIChainRule.lean:273`
- **signature** (verbatim):
  ```lean
  theorem klDiv_pi_eq_sum
      {n : ℕ} {α' : Fin n → Type*} [∀ i, MeasurableSpace (α' i)]
      (μs νs : ∀ i, Measure (α' i))
      [∀ i, IsProbabilityMeasure (μs i)] [∀ i, IsProbabilityMeasure (νs i)] :
      klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)
  ```
- **type-class prerequisites**: `[∀ i, MeasurableSpace (α' i)]`, `[∀ i, IsProbabilityMeasure (μs i)]`, `[∀ i, IsProbabilityMeasure (νs i)]`
- **explicit args**: `μs νs : ∀ i, Measure (α' i)`
- **conclusion**: `klDiv (Measure.pi μs) (Measure.pi νs) = ∑ i : Fin n, klDiv (μs i) (νs i)` (**無条件 = 等号、honest hyp なし**)
- **applicability to 軸 3**: **Option γ (klDiv 形) の決定打**。n-fold tensor の KL は **無条件で sum に分解**。Phase B-4 で `klDiv (joint_n) (prod_n) = n * klDiv (joint_1) (prod_1) = n * I(X;Y)` という MI nに比例 identity が 1 行で取れる。**Option β の `jointDifferentialEntropyPi_le_sum` のような load-bearing hyp なし**。

### `Common2026.Shannon.mutualInfo_pi_eq_sum` (既存自作)

- **file:line**: `Common2026/Shannon/MIChainRule.lean:341`
- **signature** (verbatim):
  ```lean
  theorem mutualInfo_pi_eq_sum
      {n : ℕ}
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
      (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
      (h_iid_joint : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
                        = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))))
      (h_iid_X : μ.map (fun ω (i : Fin n) => Xs i ω)
                    = Measure.pi (fun i => μ.map (Xs i)))
      -- ... (signature 末尾は line 392 で `mutualInfo μ Xs Ys = ∑ i, ...`)
  ```
- **type-class prerequisites**: `[IsProbabilityMeasure μ]` (Ω/α/β は section variable で `MeasurableSpace`)
- **explicit args**: `μ`, `Xs`, `Ys`, `hXs`, `hYs`, `h_iid_joint`, `h_iid_X`, (h_iid_Y は次行)
- **conclusion**: n-d joint MI が ∑ I(X_i; Y_i) に分解 (i.i.d 仮定下)
- **applicability to 軸 3**: **Option γ の真打**。Cover-Thomas joint typicality の Phase B-4 (indep marginal の typical pair 確率 ≤ exp(-n(I-3ε))) を直接組める形。

### `ProbabilityTheory.map_pi_eq_stdGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:137`
- **signature** (verbatim):
  ```lean
  lemma map_pi_eq_stdGaussian :
      (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι)
  ```
- **type-class prerequisites**: section variable `[Fintype ι] [Nonempty ι]` (Multivariate.lean header)
- **explicit args**: 無 (`ι`, `E` は variable)
- **conclusion**: `(Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι)`
- **applicability to 軸 3**: **判断 #2 (codebook 型) との接続点**。`Measure.pi` 形 (採用済) と `stdGaussian (EuclideanSpace)` 形の間を `toLp 2` で繋ぐ。Option α/β で n-d Gaussian の density / entropy を `stdGaussian` API 経由で取りたい時の bridge。Option γ では (`klDiv_pi_eq_sum` がある分) 不要。

### `ProbabilityTheory.measurePreserving_eval_multivariateGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:229`
- **signature** (verbatim):
  ```lean
  lemma measurePreserving_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
      MeasurePreserving (fun x ↦ x i) (multivariateGaussian μ S)
        (gaussianReal (μ i) (S i i).toNNReal)
  ```
- **type-class prerequisites**: `[DecidableEq ι]` (section variable)
- **explicit args**: `hS : S.PosSemidef`, `i : ι` (implicit)
- **conclusion**: `MeasurePreserving (fun x ↦ x i) (multivariateGaussian μ S) (gaussianReal (μ i) (S i i).toNNReal)`
- **applicability to 軸 3**: codebook 経由で n-d Gaussian にした後、coordinate-wise marginal が 1-d Gaussian であることを保証 (Option α/β/γ 全てで使える marginal 補題)。

### **不在**: `(Measure.pi p).rnDeriv (Measure.pi q)` の product 化

- **状態**: ❌ **Mathlib 0 declarations** (loogle `MeasureTheory.Measure.rnDeriv, MeasureTheory.Measure.pi` = 0)
- **applicability to 軸 3**: **Option α (rnDeriv 形) の n-d gap の本体**。Option γ は `klDiv_pi_eq_sum` (Common2026) で迂回済。

### **不在**: `differentialEntropy (Measure.pi p) = ∑ differentialEntropy (p i)`

- **状態**: ❌ **Mathlib 0 declarations** (loogle `Real.log, MeasureTheory.Measure.pi` = 0)
- **代替**: Common2026 `jointDifferentialEntropyPi_le_sum` (load-bearing `h_llr_split` 付き)。equality 版 (i.i.d 仮定下) は不在。
- **applicability to 軸 3**: **Option β の n-d 致命的 gap**。equality を取るには `h_llr_split` で逃げるか自作 50-100 行。

---

## サブ項目 3.4: chain rule / Bayes / kernel-product 経由の reshape

### `InformationTheory.klDiv_compProd_eq_add` (Mathlib chain rule)

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`
- **signature** (verbatim):
  ```lean
  theorem klDiv_compProd_eq_add : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)
  ```
- **type-class prerequisites** (section variable, file header):
  ```lean
  variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
  ```
- **explicit args**: 無 (全 implicit / instance)
- **conclusion**: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` (**無条件**、AC / integrability hypothesis なし)
- **applicability to 軸 3**: **Option γ の本丸**。AWGN の `(X, Y) ∼ p ⊗ₘ W` 形に直接適用、`I(X;Y) = KL(joint || p ⊗ output) = KL(p ⊗ₘ W || p ⊗ₘ (Kernel.const _ output))` の分解が無条件で取れる。前提 `[IsMarkovKernel κ]` は AWGN kernel が `IsMarkovKernel` (Common2026 `awgnChannel` は probability kernel) で OK。

### `ProbabilityTheory.rnDeriv_compProd`

- **file:line**: `Mathlib/Probability/Kernel/Composition/RadonNikodym.lean:107`
- **signature** (verbatim):
  ```lean
  lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
      (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
      (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η]
        (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)
  ```
- **type-class prerequisites**: `[IsFiniteMeasure μ]`, `[IsFiniteKernel κ]`, `[IsFiniteKernel η]`, `[IsFiniteMeasure ν]`
- **explicit args**: `h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η`, `ν : Measure α`
- **conclusion**: `(μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p`
- **applicability to 軸 3**: **Option α が kernel 経由で再起する道**。`(p ⊗ₘ W)` を kernel composition product 形のまま rnDeriv 化、分母を `volume.prod volume` ではなく `p ⊗ₘ (Kernel.const _ output)` に取れば適用可能。だが Cover-Thomas の typical set 定義は `(joint).rnDeriv (vol × vol)` 形なので、結局 `volume.prod` 形への変換補題が必要 → **gap**。

### `InformationTheory.rnDeriv_compProd_mul_log_eq_mul_add`

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:103`
- **signature** (verbatim):
  ```lean
  lemma rnDeriv_compProd_mul_log_eq_mul_add (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
      ∀ᵐ p ∂(ν ⊗ₘ η), ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal =
        (((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * (log ((∂μ/∂ν) p.1).toReal +
          log ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) p).toReal))
  ```
- **type-class prerequisites** (inherited from file header): `[IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]`
- **explicit args**: `h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η`
- **conclusion**: `∀ᵐ p ∂(ν ⊗ₘ η), ...` (log 形の分解、`log f_joint = log f_marginal + log f_conditional`)
- **applicability to 軸 3**: **Option γ の Phase B-2 (P→1) で使う本命**。typical set 条件 `|-(1/n) log p(x^n, y^n) - h(X,Y)| < ε` の log density 部を marginal + conditional に分解。本当に typical set を log 形で書くなら必須。

### `InformationTheory.integral_llr_compProd_eq_add`

- **file:line**: `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:151`
- **signature** (verbatim):
  ```lean
  lemma integral_llr_compProd_eq_add (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
      (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
      ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
        ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ)
  ```
- **type-class prerequisites**: 上記と同 (file header の `[IsMarkovKernel κ] [IsMarkovKernel η]` 等)
- **explicit args**: `h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η`, `h_int : Integrable ...`
- **conclusion**: `∫ p, llr ... p ∂μ ⊗ₘ κ = ∫ a, llr μ ν a ∂μ + ∫ p, llr ... p ∂(μ ⊗ₘ κ)`
- **applicability to 軸 3**: Option γ の Phase B-2 で expected log-density を chain rule で分解。AEP bound 1 (typical 集合の確率) 構築時に直接使う。

### `Common2026.Shannon.MIChainRule.klDiv_prod_eq_add`

- **file:line**: `Common2026/Shannon/MIChainRule.lean:254`
- **signature** (verbatim):
  ```lean
  theorem klDiv_prod_eq_add
      {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
      (μ₁ μ₂ : Measure α') [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
      (ν₁ ν₂ : Measure β') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
      klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂
  ```
- **type-class prerequisites**: `[MeasurableSpace α'] [MeasurableSpace β']`, `[IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]`
- **explicit args**: `μ₁ μ₂ : Measure α'`, `ν₁ ν₂ : Measure β'`
- **conclusion**: `klDiv (μ₁.prod ν₁) (μ₂.prod ν₂) = klDiv μ₁ μ₂ + klDiv ν₁ ν₂`
- **applicability to 軸 3**: **Option γ の独立積バージョン**。`Measure.prod` 形での KL 加法性。`klDiv_compProd_eq_add` を `Kernel.const` でラップして導出済。

### `Common2026.Shannon.MutualInfo.klDiv_map_measurableEquiv`

- **file:line**: `Common2026/Shannon/MutualInfo.lean:52`
- **signature** (verbatim):
  ```lean
  theorem klDiv_map_measurableEquiv {α β : Type*}
      [MeasurableSpace α] [MeasurableSpace β]
      (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
      klDiv (μ.map e) (ν.map e) = klDiv μ ν
  ```
- **type-class prerequisites**: `[MeasurableSpace α] [MeasurableSpace β]`, `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`
- **explicit args**: `e : α ≃ᵐ β`, `μ ν : Measure α`
- **conclusion**: `klDiv (μ.map e) (ν.map e) = klDiv μ ν`
- **applicability to 軸 3**: **Mathlib 不在を Common2026 が埋めた** (`InformationTheory.klDiv` × `MeasureTheory.Measure.map` = 0、独立確認)。Option γ で `Fin M → Fin n → ℝ` ↔ `Fin (M*n) → ℝ` 等の型変換時に必須。

---

## サブ項目 3.5: `Real.log` 適用の便利補題 (どの Option でも共通)

### `Real.log_mul`

- **file:line**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (line 不要、Mathlib 標準)
- **signature** (verbatim, sketched):
  ```lean
  theorem Real.log_mul (hx : x ≠ 0) (hz : z ≠ 0) : Real.log (x * z) = Real.log x + Real.log z
  ```
- **applicability to 軸 3**: 密度の積を log の和に分解する基本。Phase B-2 / B-3 で頻用。

### `Real.log_prod`

- **file:line**: `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`
- **signature** (verbatim, sketched — loogle で 1 declaration 確認):
  ```lean
  theorem Real.log_prod (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
      Real.log (∏ i ∈ s, f i) = ∑ i ∈ s, Real.log (f i)
  ```
- **applicability to 軸 3**: i.i.d product density `∏ p(x_i)` → sum `∑ log p(x_i)` 分解。Option β の `f log f` 形で n-d を 1-d sum に reduce する時の核心。

### `ProbabilityTheory.strong_law_ae` (Mathlib SLLN、軸 2 inventory のリンク先)

- **file:line**: `Mathlib/Probability/StrongLaw.lean:788`
- **signature** (verbatim):
  ```lean
  theorem strong_law_ae (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])
  ```
- **type-class prerequisites** (section variable in StrongLaw.lean):
  ```lean
  variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
  ```
- **explicit args**: `X : ℕ → Ω → E`, `hint : Integrable (X 0) μ`, `hindep : Pairwise ...`, `hident : ∀ i, IdentDistrib ...`
- **conclusion**: `∀ᵐ ω ∂μ, Tendsto (fun n ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])`
- **applicability to 軸 3**: **Phase B-2 (P→1) の解析的核心**。「`X` は Banach space E 値」なので E = ℝ で `log gaussianPDF(X_i)`、または E = ℝ² で `(log gaussianPDF(X_i), log gaussianPDF(Y_i))` 等の組合せが coordinate-wise SLLN として走る。

---

## 主要前提条件ボックス (前提事故 hotspot)

- **`klDiv_compProd_eq_add`** (Mathlib chain rule、軸 3 の主役): file header の section variable で `[IsMarkovKernel κ] [IsMarkovKernel η]` + `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` を要求。AWGN の `awgnChannel` は `IsMarkovKernel` (Common2026 既存)、入力 `gaussianReal` は `IsProbabilityMeasure → IsFiniteMeasure` で OK。**`IsSFiniteKernel` ではなく `IsMarkovKernel` 要求**なので、AWGN kernel の構成時に prob kernel 性を維持する必要あり (Common2026 既存だが、worktree で新規 kernel を組む場合は注意)。
- **`rnDeriv_compProd`** (Mathlib): `[IsFiniteKernel κ] [IsFiniteKernel η]` (Markov ではなく Finite で OK) + `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` + AC hypothesis `μ ⊗ₘ κ ≪ μ ⊗ₘ η`。AWGN setup では `awgnChannel N h_meas` が `IsMarkovKernel` (⇒ `IsFiniteKernel`) で AC は `gaussianReal_absolutelyContinuous` から得る。
- **`klDiv_map_measurableEquiv`** (Common2026): `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`。`Measure.pi` の prob 化が AC で渡らない場合 (e.g., expurgation 段で打ち切った subcodebook) は事前に instance を `haveI` で取り直す必要あり。
- **`strong_law_ae`** (Mathlib SLLN): E が `[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]`。ℝ, ℝ², ℝⁿ で OK。`hident : ∀ i, IdentDistrib (X i) (X 0) μ μ` は 1 個ずつ作る必要がある (`pairwise IndepFun + 1 つの identical distribution` ではなく `IdentDistrib` を i ごとに供給)。
- **`jointDifferentialEntropyPi_le_sum`** (Common2026 既存自作): **load-bearing `h_llr_split` 残置**、`@audit:suspect(differential-entropy-plan)` タグ付き (line 89/175/214/279)。Option β を採用するなら、本 plan の Phase B で同じ honest hyp を継承することになり、結局 `IsContinuousAEPGaussian` の中身に load-bearing hyp が再混入する。

---

## 自作が必要な要素 (優先度順)

| # | 要素 | 状態 | 推奨実装 | 工数 | Option |
|---|---|---|---|---|---|
| 1 | `(p ⊗ₘ W).rnDeriv (volume.prod volume)` closed form | ❌ Mathlib 不在 | `rnDeriv_compProd` + `gaussianReal_absolutelyContinuous` chain | 50-100 行 | α のみ必要 |
| 2 | `differentialEntropy_pi {n} (Measure.pi p) = ∑ differentialEntropy (p i)` (i.i.d 等号版) | ❌ Mathlib 不在 (Common2026 は `≤` で `h_llr_split` hyp 化) | 等号は `h_llr_split` を `Measure.pi` の `pi_withDensity` から本物 discharge する必要、現状 gap | 100-200 行 (gap closed 場合) | β のみ必要 |
| 3 | typical set 定義 (Cover-Thomas の `\|-(1/n) log p - h\| < ε` 形) | ❌ Mathlib 不在 (Common2026 にも未定義、`StrongTypicality` は finite alphabet) | Phase B 着手時に Option γ なら `\|(1/n) klDiv(emp || target) - 0\|` 形、Option α/β なら log 形を実装 | 30-50 行 (Option γ) / 50-80 行 (Option α/β) | 全 Option |
| 4 | (Option γ 限定) joint typical set 確率の SLLN ↔ klDiv → 0 bridge | ❌ Mathlib 不在 | Sanov 系 / `strong_law_ae` + `klDiv_pi_eq_sum` 経由 | 50-100 行 | γ のみ |
| 5 | (Option α/β 限定) `\|(1/n) ∑ log p(X_i) - E[log p]\|` の WLLN | △ Mathlib `strong_law_ae` から ε-version 引出し可 | `Tendsto` + Markov 不等式 | 20-40 行 | α/β のみ |

---

## 撤退ラインへの距離

親 plan (`awgn-achievability-typicality-plan.md`) §「撤退ライン」参照:

- **T-2 (continuous AEP for n-dim Gaussian の Mathlib 不在)**: **発動する見込み**。本 inventory で確認した:
  - `Measure.pi` × `rnDeriv` = 0 declarations
  - `Measure.pi` × `klDiv` = 0 declarations (`klDiv_pi_eq_sum` は Common2026 自作)
  - `differentialEntropy_pi` = 0 declarations
  - n-dim Gaussian SLLN は `strong_law_ae` を E = ℝⁿ で起動すれば取れるが、典型集合の 3 bound (P→1 / volume bound / indep-product) をすべて n-d で組むには Mathlib API が薄い
  - **判定**: T-2 採用 (`IsContinuousAEPGaussian P N` regularity hyp)、achievability core (Phase C-D) は本物 discharge を維持。**判断 #3 (本 inventory) と整合**。
- **T-3 (expurgation lemma 不在)**: 軸 4 で判定 (本 inventory のスコープ外)。
- **T-4 (全体 700 行超 + Phase B/D 同時壁)**: 判断 #3 が Option γ を採用すれば Phase B-4 (indep-product) は `klDiv_pi_eq_sum` で 30 行に収まる見込み、よって T-4 発動可能性 **低**。

---

## 着手 skeleton (Phase B、判断 #3 = Option γ 採用時)

`Common2026/Shannon/AWGNAchievabilityDischarge.lean` の Phase B 部分の出だし:

```lean
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNAchievability
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.MultivariateDiffEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.StrongLaw
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-- (Phase B-0, T-2 採用時) **Continuous AEP for n-dim Gaussian under AWGN**
(Mathlib gap predicate, NOT load-bearing for achievability).

This predicate packages the 3 classical AEP bounds whose direct Lean discharge is
blocked by the absence of n-dim Gaussian joint-density structure in Mathlib (this
inventory §3.2 / §3.3 confirms `(Measure.pi p).rnDeriv (Measure.pi q)` and
`differentialEntropy_pi` are 0 declarations in Mathlib).

The achievability core (codebook + union bound + expurgation) is genuinely
discharged in Phase C-D, so this hypothesis is regularity not load-bearing. -/
def IsContinuousAEPGaussian (P : ℝ) (N : ℝ≥0) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      -- (a) P[joint ∈ A] ≥ 1 - ε
      -- (b) volume(A) ≤ exp(n*(h(X,Y)+ε)) where h(X,Y) computed via
      --     mutualInfo + differentialEntropy_gaussianReal in 1-d
      -- (c) P[(X', Y) ∈ A] ≤ exp(-n*(I - 3ε)) for X' indep of Y
      -- precise form determined at Phase B implementation time
      sorry

/-- (Phase B-4 sketch) n-fold MI decomposition (i.i.d. extension), using
the Mathlib `klDiv_compProd_eq_add` chain rule + Common2026 `klDiv_pi_eq_sum`. -/
example (n : ℕ) (P : ℝ) (N : ℝ≥0)
    (hP : 0 < P) (hN : (N : ℝ) ≠ 0) :
    -- placeholder: I(X^n; Y^n) = n * I(X; Y) under i.i.d.
    True := by
  trivial

end InformationTheory.Shannon.AWGN
```

---

## §判断 #3 (typical set 定義形): **Option γ (`klDiv` 形) を採用**

### 比較表 (Mathlib + Common2026 既存資産)

| 項目 | Option α (rnDeriv 形) | Option β (differentialEntropy 形) | **Option γ (klDiv 形)** ⭐ |
|---|---|---|---|
| 1-d Gaussian 値の closed form | ✅ `rnDeriv_gaussianReal` | ✅ `differentialEntropy_gaussianReal` (Common2026) | ✅ `klDiv_gaussianReal_gaussianReal_eq` (Common2026) |
| Y = X+Z の joint density / convolution | ✅ `gaussianReal_conv_gaussianReal` | △ 1-d 化経由 | ✅ `gaussianReal_add_gaussianReal_of_indepFun` |
| n-d (Measure.pi) への持ち上げ補題 | ❌ Mathlib `rnDeriv × Measure.pi` = 0 | ❌ Mathlib `differentialEntropy_pi` 不在、Common2026 `jointDifferentialEntropyPi_le_sum` は load-bearing hyp 残置 | ✅ **`klDiv_pi_eq_sum` (Common2026、無条件 = 等号)** |
| chain rule (joint → marginal + conditional) | △ `rnDeriv_compProd` (Mathlib) があるが分母 `volume.prod` への bridge 必要 | △ `klDiv_prod_marginals_toReal_eq_sum_sub_joint` (Common2026) は load-bearing hyp 経由 | ✅ **`klDiv_compProd_eq_add` (Mathlib、無条件)** |
| AWGN setup (`p ⊗ₘ W`) との接続 | △ kernel 形で書ければ `rnDeriv_compProd` 経由 | △ 1-d 化経由 | ✅ **`mutualInfoOfChannel` (Common2026) が klDiv 形で既存** |
| Phase B-4 (indep-product の典型確率) との接続 | △ density 形の Markov 不等式 | △ 同上 | ✅ **`klDiv_pi_eq_sum` で 1 行** |
| load-bearing hyp 残置リスク | 中 (rnDeriv 分解 bridge) | **高** (`h_llr_split` 残置、Common2026 既存自作の負債を継承) | **低** (chain rule が無条件 = 等号) |
| Common2026 既存資産との合流 | △ `MultivariateDiffEntropy` (β 側) のみ | △ 同上、load-bearing hyp 経由 | ✅ **`MutualInfo` + `MIChainRule` で n-d / chain rule 完備** |

### 判定根拠

1. **Mathlib の結論形と完全一致** (CLAUDE.md「Mathlib-shape-driven definitions」): `klDiv_compProd_eq_add` の結論形 `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` がそのまま AWGN setup の MI 分解に乗る。
2. **load-bearing hyp ゼロ**: Option β の `h_llr_split` (`pi_withDensity` を仮定として担ぐ) や Option α の `(joint).rnDeriv (vol×vol)` closed form 自作を完全に回避。`klDiv_pi_eq_sum` は **無条件等号**、`klDiv_compProd_eq_add` も **無条件等号**。
3. **Common2026 既存資産 100% 流用**: `mutualInfo := klDiv (...)` (MutualInfo.lean:36)、`klDiv_pi_eq_sum`、`klDiv_prod_eq_add`、`klDiv_map_measurableEquiv`、`mutualInfoOfChannel` (ChannelCoding.lean:84) がすべて Option γ 軌道。
4. **typical set 定義の縮退化**: T-2 (`IsContinuousAEPGaussian` 採用) と組み合わせると、typical set 定義は **predicate 内に隠れる** ため明示定義不要。Option α/β は明示定義時に `f log f` 形を書かざるを得ず、Option γ は `(1/n) klDiv(joint_emp || joint_target) → 0` 形で書けるため、TypeError や reshape bridge を回避。
5. **判断 #1 (T-2) との整合**: T-2 採用 (本 inventory で発動確定) なら typical set は `IsContinuousAEPGaussian` predicate の内側に詰める。Option γ は **predicate 中身が `klDiv (joint_n) (prod_n) ≤ ε` 形で書けるので、外側 Phase C-D が `klDiv_pi_eq_sum` 1 行で `n * I ≤ ε` まで詰められる**。

### Option γ の唯一の弱み

- typical set を Cover-Thomas 流の textbook と同型の log-density 表記で書きたい場合、`klDiv` 形からの bridge lemma が一段必要 (e.g., `klDiv → ∫ log rnDeriv` 換算)。これは `toReal_klDiv_of_measure_eq` (Mathlib `Basic.lean:`、Common2026 で頻用済) で 5-10 行。
- **ただし achievability の証明には textbook 表記との一致は不要**。判定: 受容。

### 推奨採用: **Option γ**

Phase B 着手時、`continuousJointTypical P N ε n : Set ((Fin n → ℝ) × (Fin n → ℝ))` を以下の形で書く (T-2 採用なら predicate 内側に隠れる):

```lean
noncomputable def continuousJointTypical (P : ℝ) (N : ℝ≥0) (ε : ℝ) (n : ℕ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  -- T-2 採用なら `IsContinuousAEPGaussian` predicate 内で
  -- `∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)), ...` の A として取得
  -- T-2 不採用なら以下の klDiv 形で書く
  { p | -- klDiv ベースの典型条件、Phase B 着手時に確定
        True }
```

Phase B 着手時の本実装 (T-2 不採用ルート) の最終形は、`klDiv_pi_eq_sum` + `klDiv_compProd_eq_add` の組合せで n-d KL を 1-d KL の n 倍として書き直し、`strong_law_ae` で E = ℝ² (joint 1-d KL の経験値) を起動。

---

## オーケストレータ注記

- 本 inventory は判断 #3 = **Option γ** を推奨。Phase A 着手時の `gaussianCodebook` の各 codeword law を `Measure.pi (gaussianReal 0 σ²)` 形で取れば、判断 #2 (= 軸 1 inventory の Option A、2 段 `Measure.pi`) と Option γ がそのまま乗る。
- Phase B 着手時に T-2 採用判定が確定 (本 inventory で発動確定) なら、`IsContinuousAEPGaussian P N` predicate を Option γ 軌道で書き、内部の `∃ A, ...` の A は `{p | (1/n) * (klDiv (...) (...)).toReal < ε}` 形で表現。
- 判断ログ #3 は Phase 0 完了時に append される (現時点では本 inventory が判定根拠を提供)。
- **honesty 規律**: Option γ 採用により、Common2026 既存 `jointDifferentialEntropyPi_le_sum` (`@audit:suspect(differential-entropy-plan)` 残置) を本 plan で **継承しない**。これは Phase E の honesty 再 audit (親 plan Phase V) で `IsContinuousAEPGaussian` が regularity 判定されることに直結する。
