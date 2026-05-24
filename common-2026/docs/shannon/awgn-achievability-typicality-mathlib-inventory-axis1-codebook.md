# AWGN Achievability Typicality — 軸 1 (codebook 測度) Mathlib API 在庫

> **Parent plan**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> (Phase 0, Phase A, 判断 #2)。
>
> **Scope**: Cover-Thomas 9.2 の random Gaussian codebook を
> `Measure (Fin M → Fin n → ℝ)` 上の確率測度として構成するための Mathlib API を
> per-lemma 構造化棚卸。
>
> **Sister inventories (parallel)**: 軸 2 (continuous AEP) / 軸 3 (union bound) /
> 軸 4 (expurgation) / 軸 5 (球殻 volume) はそれぞれ別 file。本 file は軸 1 のみ。

## 一行サマリ

**軸 1 (codebook 測度) の必要 API はすべて Mathlib 既存**。2 段 `Measure.pi` で
`Fin M → Fin n → ℝ` 上の確率測度として直接組める。`IsProbabilityMeasure` /
`SigmaFinite` / `IsFiniteMeasure` instance は自動推論可能、各 codeword の law と
codewords 間の `IndepFun` も `Measure.pi_pi` / `iIndepFun_pi` /
`measurePreserving_eval` で1〜2 行で取れる。

**判断 #2 推奨: Option A (2 段 `Measure.pi`)** を採用。Option B (`EuclideanSpace`
flatten) は軸 2 (continuous AEP) の Mathlib 在庫が 1-d SLLN coordinate-wise 軌道で
来た場合のみ後退案として保留。詳細は末尾「§判断 #2」。

---

## サブ項目 1: `Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)` の型クラス

### `ProbabilityTheory.gaussianReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:200`
- **signature**:
  ```lean
  noncomputable
  def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
    if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)
  ```
- **type-class prerequisites**: 無 (definition)
- **explicit args**: `μ : ℝ`, `v : ℝ≥0`
- **conclusion**: `Measure ℝ`
- **applicability to 軸 1**: codeword 各成分の law。`σ²` は `ℝ≥0` で表現 (`P-δ` を
  `(P-δ).toNNReal` で。`hP : 0 < P` から `P-δ > 0` 保証時のみ意味あり。`v=0` 退化は
  `dirac` に落ちる、Cover-Thomas では `v=0` は使わないので OK)。

### `ProbabilityTheory.instIsProbabilityMeasureGaussianReal`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean:209`
- **signature**:
  ```lean
  instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
      IsProbabilityMeasure (gaussianReal μ v) where
    measure_univ := by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]
  ```
- **type-class prerequisites**: 無
- **explicit args**: `μ : ℝ`, `v : ℝ≥0`
- **conclusion**: `IsProbabilityMeasure (gaussianReal μ v)`
- **applicability to 軸 1**: 各成分が prob measure であることの自動推論起点。
  これにより `Measure.pi` 側の prob instance が起動する。

### `MeasureTheory.Measure.pi.instIsProbabilityMeasure`

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:313`
- **signature**:
  ```lean
  instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :
      IsProbabilityMeasure (Measure.pi μ) :=
    ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩
  ```
- **type-class prerequisites**: `[∀ i, IsProbabilityMeasure (μ i)]`
  (省略されている前提として、ambient `[Fintype ι] [∀ i, MeasurableSpace (α i)]`
  が `Measure.pi` 定義時の `variable` から継承)
- **explicit args**: 無 (`μ` は `variable` から)
- **conclusion**: `IsProbabilityMeasure (Measure.pi μ)`
- **applicability to 軸 1**: `Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)` が
  自動で `IsProbabilityMeasure`。`Fin n` は `Fintype`、`ℝ` は
  `MeasurableSpace` (Borel)、`gaussianReal` は `IsProbabilityMeasure` ですべて
  自動推論。

### `MeasureTheory.Measure.pi.instIsFiniteMeasure`

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:305`
- **signature**:
  ```lean
  instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :
      IsFiniteMeasure (Measure.pi μ) :=
    ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ ↦ measure_lt_top (μ i) _)⟩
  ```
- **type-class prerequisites**: `[∀ i, IsFiniteMeasure (μ i)]`
- **explicit args**: 無
- **conclusion**: `IsFiniteMeasure (Measure.pi μ)`
- **applicability to 軸 1**: `IsProbabilityMeasure → IsFiniteMeasure` は Mathlib 標準。
  `IsProbabilityMeasure` instance があれば不要 (自動派生)。

### `MeasureTheory.Measure.pi.sigmaFinite`

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:336`
- **signature**:
  ```lean
  instance pi.sigmaFinite : SigmaFinite (Measure.pi μ) :=
    (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite
  ```
- **type-class prerequisites**: 親 `variable [∀ i, SigmaFinite (μ i)]` (Pi.lean:327)
- **explicit args**: 無
- **conclusion**: `SigmaFinite (Measure.pi μ)`
- **applicability to 軸 1**: `Measure.pi_pi` などの計算ベース。`IsFiniteMeasure → SigmaFinite`
  自動派生で起動する。

### 判定 (サブ項目 1)

**既存**。1 段の `Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)` は
`Fintype (Fin n)` + `MeasurableSpace ℝ` (Borel) + `IsProbabilityMeasure (gaussianReal 0 σ²)`
だけで `IsProbabilityMeasure / IsFiniteMeasure / SigmaFinite` がすべて自動推論。

---

## サブ項目 2: 2 段 `Measure.pi` の型クラス (Fin M × Fin n → ℝ)

「内側 `Measure.pi (fun _ : Fin n => gaussianReal 0 σ²) : Measure (Fin n → ℝ)`」を
さらに `Measure.pi (fun _ : Fin M => νₙ) : Measure (Fin M → Fin n → ℝ)` で外側を組む。

### 上記 `pi.instIsProbabilityMeasure` の 2 回適用

- 外側適用の前提: `[∀ _ : Fin M, IsProbabilityMeasure νₙ]`
  → νₙ は内側 `Measure.pi`、サブ項目 1 で自動推論済み
- 外側 ambient: `[Fintype (Fin M)]` (自明) +
  `[MeasurableSpace (Fin n → ℝ)]` (Pi instance、Mathlib 自動)
- 結果: `IsProbabilityMeasure (Measure.pi (fun _ : Fin M => νₙ))` 自動

### Caveat: `MeasurableSpace` インスタンスの自動推論

- `MeasurableSpace.pi : MeasurableSpace (∀ i, α i)` は Mathlib 既存
  (`Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`)。
- ambient `[∀ i, MeasurableSpace (α i)]` から自動。
- 2 段ネストで `Measurable (fun c : Fin M → Fin n → ℝ => c m i) ↔ ` の chain は
  `measurable_pi_apply` + 関数合成で自動 (`fun_prop` で通る)。

### 判定 (サブ項目 2)

**既存**。`Measure.pi` の instance は型クラス推論が再帰的に動くので、追加 lemma
不要で `Measure (Fin M → Fin n → ℝ)` 上の確率測度として直接構成可能。
**判断 #2 で Option A (2 段 `Measure.pi`) を採用する根拠の中核。**

---

## サブ項目 3: EuclideanSpace flatten ルート (Option B、代替案)

### `ProbabilityTheory.stdGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:66`
- **signature**:
  ```lean
  noncomputable
  def stdGaussian : Measure E :=
    (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
      (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)
  ```
- **type-class prerequisites** (定義の `variable` blockから):
  `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E]`
- **explicit args**: 無 (`E` は `variable`)
- **conclusion**: `Measure E`
- **applicability to 軸 1**: Option B では `E := EuclideanSpace ℝ (Fin (M*n))` を
  取って `stdGaussian E : Measure (EuclideanSpace ℝ (Fin (M*n)))` を codebook
  測度として採用。**ただし型は `EuclideanSpace ℝ _` で `Fin M → Fin n → ℝ` ではない**
  ため、`AwgnCode.encoder : Fin M → (Fin n → ℝ)` と整合させるには
  `EuclideanSpace ℝ (Fin (M*n)) ≃ᵐ (Fin M → Fin n → ℝ)` の measure-preserving 同型
  (`Finprod` + `EuclideanSpace.measurableEquiv` 等) が別途必要。

### `ProbabilityTheory.isProbabilityMeasure_stdGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:72`
- **signature**:
  ```lean
  instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  ```
- **type-class prerequisites**: 上記 `stdGaussian` の変数ブロックに加えて `[BorelSpace E]`
  (Multivariate.lean:70 で追加)
- **explicit args**: 無
- **conclusion**: `IsProbabilityMeasure (stdGaussian E)`
- **applicability to 軸 1**: Option B での prob 性。`[BorelSpace E]` が追加で要る点に
  注意。

### `ProbabilityTheory.map_pi_eq_stdGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:137`
- **signature**:
  ```lean
  lemma map_pi_eq_stdGaussian :
      (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι) := by
  ```
- **type-class prerequisites**: 親 section `variable {ι : Type*} [Fintype ι]` +
  上記 `stdGaussian` 変数ブロック (`E := EuclideanSpace ℝ ι` の場合)
- **explicit args**: 無
- **conclusion**:
  `(Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι)`
- **applicability to 軸 1**: **これが Option A と Option B の橋**。`σ² = 1` の場合の
  flatten。`σ² ≠ 1` の場合は `gaussianReal_map_const_mul` で scale して合わせる必要
  (1 段増える)。

### `ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:146`
- **signature**:
  ```lean
  lemma stdGaussian_eq_map_pi_orthonormalBasis (b : OrthonormalBasis ι ℝ E) :
      stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (fun x ↦ ∑ i, x i • b i) := by
  ```
- **type-class prerequisites**: 上記 `stdGaussian` の `[NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]`
  + `[Fintype ι]` (section から)
- **explicit args**: `b : OrthonormalBasis ι ℝ E`
- **conclusion**:
  `stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (fun x ↦ ∑ i, x i • b i)`
- **applicability to 軸 1**: `stdGaussian` の定義が basis-independent であることの確認。
  Option B 採用時に「`stdGaussian (EuclideanSpace ℝ (Fin (M*n)))` ≅ `Measure.pi`」
  を rewrite で行き来できる。

### `ProbabilityTheory.multivariateGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:168`
- **signature**:
  ```lean
  noncomputable
  def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
      Measure (EuclideanSpace ℝ ι) :=
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
  ```
- **type-class prerequisites**: 親 section `variable [DecidableEq ι]` (Multivariate.lean:161)
  + `[Fintype ι]` (section の上で導入)
- **explicit args**: `μ : EuclideanSpace ℝ ι`, `S : Matrix ι ι ℝ`
- **conclusion**: `Measure (EuclideanSpace ℝ ι)`
- **applicability to 軸 1**: Option B で variance `σ²` を扱う最も自然な道。
  `S = σ² • 1` (diagonal) を渡せば iid Gaussian。**ただし `Matrix.PosSemidef` の
  処理が `CFC.sqrt` 経由で型クラス的に重い** (`isGaussian_multivariateGaussian`
  proof は `fun_prop` で済んでいるが、`AwgnCode` 側と接続する際は `Matrix` 表現と
  scalar `σ²` の変換コストあり)。Option A の方がはるかに軽量。

### 判定 (サブ項目 3)

**既存** (Option B 自体は構築可能)。ただし:
1. 型が `EuclideanSpace ℝ (Fin (M*n))` で、`AwgnCode.encoder : Fin M → (Fin n → ℝ)`
   との measurable equivalence が別途必要。
2. `σ² ≠ 1` の場合は `multivariateGaussian 0 (σ² • 1)` 経由で重い`CFC.sqrt` を
   触る必要。
3. 軸 1 単独では Option A の方が遥かに軽量。**Option B は軸 2 の continuous AEP
   が `stdGaussian (EuclideanSpace ℝ _)` の形でしか Mathlib 在庫が引っ張れない
   場合に限り採用候補**。軸 2 inventory の結果を待つ。

---

## サブ項目 4: IndepFun across codewords

### `ProbabilityTheory.iIndepFun_pi`

- **file:line**: `Mathlib/Probability/Independence/Basic.lean:784`
- **signature**:
  ```lean
  lemma iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
      iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  ```
- **type-class prerequisites** (Basic.lean:778-780 の `variable` から):
  ```
  {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : (i : ι) → Ω i → 𝓧 i}
  ```
- **explicit args**: `mX : ∀ i, AEMeasurable (X i) (μ i)`
- **conclusion**: `iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)`
- **applicability to 軸 1**: **これが「codewords は indep」の核**。
  外側 `Measure.pi (fun _ : Fin M => νₙ)` に対して `X i = id : (Fin n → ℝ) → (Fin n → ℝ)`、
  `Ω i = 𝓧 i = (Fin n → ℝ)`、`μ i = νₙ` で適用すれば
  `iIndepFun (fun i ω => ω i) (Measure.pi (fun _ => νₙ))` が得られる。これは
  「外側 codebook 測度の下で各 m に対する codeword 射影 (fun c => c m) が mutually
  indep」を意味する。`νₙ = Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)` が
  `IsProbabilityMeasure` であることはサブ項目 1 から自動。

### `ProbabilityTheory.iIndepFun.indepFun`

- **file:line**: `Mathlib/Probability/Independence/Basic.lean:447`
- **signature**:
  ```lean
  theorem iIndepFun.indepFun {β : ι → Type*}
      {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : iIndepFun f μ) {i j : ι}
      (hij : i ≠ j) :
      f i ⟂ᵢ[μ] f j :=
    Kernel.iIndepFun.indepFun hf_Indep hij
  ```
- **type-class prerequisites**: ambient `{Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}` (file の中で `variable` から)、explicit な instance なし
- **explicit args**: `hf_Indep : iIndepFun f μ`, `hij : i ≠ j` (implicit `{i j : ι}`)
- **conclusion**: `f i ⟂ᵢ[μ] f j`
- **applicability to 軸 1**: `iIndepFun_pi` で得た mutual indep から pairwise
  `IndepFun (fun c => c m) (fun c => c m') (gaussianCodebook M n σ²)` を 1 行で抽出。
  これが plan §「`gaussianCodebook_indepFun_codewords`」の結論形そのもの。

### `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`

- **file:line**: `Mathlib/Probability/Independence/Basic.lean:706`
- **signature**:
  ```lean
  theorem iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] {β : ι → Type*}
      {m : ∀ i, MeasurableSpace (β i)} {f : Π i, Ω → β i} [IsProbabilityMeasure μ]
      (hf : ∀ i, AEMeasurable (f i) μ) :
      iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i)) := by
  ```
- **type-class prerequisites**: `[Fintype ι]`, `[IsProbabilityMeasure μ]` (explicit
  bracket); ambient `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`
- **explicit args**: `hf : ∀ i, AEMeasurable (f i) μ`
- **conclusion**: `iIndepFun f μ ↔ μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i))`
- **applicability to 軸 1**: バックアップ。`iIndepFun_pi` の前段の characterization。
  直接使うのは `iIndepFun_pi` の方だが、もし `iIndepFun_pi` の signature が我々の
  使い方に合わない (e.g., `X i = id` で `(fun i ω => id (ω i)) = (fun i ω => ω i)`
  が解消されない) 場合のフォールバック。

### `ProbabilityTheory.iIndepFun.hasLaw_pi`

- **file:line**: `Mathlib/Probability/HasLaw.lean:199`
- **signature**:
  ```lean
  lemma iIndepFun.hasLaw_pi {ι : Type*} [Fintype ι] {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)}
      {μ : (i : ι) → Measure (𝓧 i)} {X : (i : ι) → Ω → 𝓧 i} (hX : ∀ i, HasLaw (X i) (μ i) P)
      (h : iIndepFun X P) :
      HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P where
  ```
- **type-class prerequisites**: `[Fintype ι]`; ambient `{Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}`
- **explicit args**: `hX : ∀ i, HasLaw (X i) (μ i) P`, `h : iIndepFun X P`
- **conclusion**: `HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P`
- **applicability to 軸 1**: 補助。我々は逆方向 (`Measure.pi` → IndepFun) を使う
  ので、こちらは Phase A で「`HasLaw` 形に再パッケージしたい」場合のみ参照。

### 判定 (サブ項目 4)

**既存**。`iIndepFun_pi` + `iIndepFun.indepFun` で「異なる codeword は IndepFun」が
2 行で取れる。plan の `gaussianCodebook_indepFun_codewords` 結論形と直結。

---

## サブ項目 5: Measure.map along projection

### `MeasureTheory.measurePreserving_eval`

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:407`
- **signature**:
  ```lean
  omit [∀ i, SigmaFinite (μ i)] in
  lemma _root_.MeasureTheory.measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
      MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
    refine ⟨measurable_pi_apply i, ?_⟩
    classical
    rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
    exact fun _ _ ↦ measure_univ
  ```
- **type-class prerequisites**: 親 namespace の `variable {ι : Type*} [Fintype ι]
  {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))`
  (Pi.lean の `Measure` namespace 内) + explicit `[∀ i, IsProbabilityMeasure (μ i)]`
- **explicit args**: `i : ι`
- **conclusion**: `MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i)`
- **applicability to 軸 1**: **「codeword m の marginal = νₙ」の核**。
  `MeasurePreserving` には `.map_eq : (Measure.pi μ).map (Function.eval i) = μ i`
  が含まれる。これに `i := m` (codeword index) を代入すると
  `(Measure.pi (fun _ : Fin M => νₙ)).map (Function.eval m) = νₙ`。
  そして `Function.eval m = (· m)` なので plan §「`gaussianCodebook_codeword_law`」の
  結論形 `(gaussianCodebook M n σ²).map (· m) = Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)`
  と直結。

### `MeasureTheory.Measure.pi_map_eval`

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:379`
- **signature**:
  ```lean
  lemma pi_map_eval [DecidableEq ι] (i : ι) :
       (Measure.pi μ).map (Function.eval i) = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i) := by
  ```
- **type-class prerequisites**: 親 namespace `[Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i))` + explicit `[DecidableEq ι]` + 親 `variable [∀ i, SigmaFinite (μ i)]`
  (Pi.lean:327)
- **explicit args**: `i : ι`
- **conclusion**:
  `(Measure.pi μ).map (Function.eval i) = (∏ j ∈ Finset.univ.erase i, μ j Set.univ) • (μ i)`
- **applicability to 軸 1**: より一般 (非 prob measure でも成立) だが scalar
  `∏ μ j univ` が残る。Prob measure では `1` に簡約され `measurePreserving_eval` の
  形になる。我々はサブ項目 1 で `IsProbabilityMeasure` を確立済みなので
  `measurePreserving_eval` を直接使う方が clean。

### `MeasureTheory.Measure.pi_pi`

- **file:line**: `Mathlib/MeasureTheory/Constructions/Pi.lean:293`
- **signature**:
  ```lean
  @[simp]
  theorem pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) :
      Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
    haveI : Encodable ι := Fintype.toEncodable ι
    rw [← pi'_eq_pi, pi'_pi]
  ```
- **type-class prerequisites**: 親 `[Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i))` + explicit `[∀ i, SigmaFinite (μ i)]`
- **explicit args**: `s : (i : ι) → Set (α i)`
- **conclusion**: `Measure.pi μ (pi univ s) = ∏ i, μ i (s i)`
- **applicability to 軸 1**: 確率計算の基底。Phase A 以降で `Measure.pi` 上の積分や
  測度値計算で逐次起動。

### 判定 (サブ項目 5)

**既存**。`measurePreserving_eval` で「codeword m の marginal が νₙ」が 1 行。

---

## サブ項目 6: marginal が i.i.d. Gaussian

これは合成: サブ項目 5 (`measurePreserving_eval` で外側 marginal = νₙ) +
サブ項目 1 (`νₙ = Measure.pi (fun _ : Fin n => gaussianReal 0 σ²)` 自体が iid
Gaussian の law) の組み合わせ。新規 Mathlib lemma は不要。

### Phase A での組み立て (pseudo-Lean)

```lean
noncomputable def gaussianCodebook (M n : ℕ) (σ² : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σ²))

instance (M n : ℕ) (σ² : ℝ≥0) : IsProbabilityMeasure (gaussianCodebook M n σ²) := by
  unfold gaussianCodebook
  infer_instance   -- Measure.pi.instIsProbabilityMeasure 2 回 + instIsProbabilityMeasureGaussianReal

theorem gaussianCodebook_codeword_law (M n : ℕ) (σ² : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σ²).map (· m) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 σ²) := by
  unfold gaussianCodebook
  exact (measurePreserving_eval (μ := fun _ : Fin M => _) m).map_eq

theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σ² : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c : Fin M → Fin n → ℝ => c m)
             (fun c : Fin M → Fin n → ℝ => c m')
             (gaussianCodebook M n σ²) := by
  unfold gaussianCodebook
  have h_iIndep :=
    iIndepFun_pi (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σ²))
      (X := fun _ : Fin M => (id : (Fin n → ℝ) → (Fin n → ℝ)))
      (fun _ => aemeasurable_id)
  -- h_iIndep : iIndepFun (fun i ω => id (ω i)) (Measure.pi ...)
  -- 函数等式: (fun i ω => id (ω i)) = (fun i c => c i)
  exact h_iIndep.indepFun hmm'
```

### 判定 (サブ項目 6)

**既存** (サブ項目 1 + 5 の組み合わせ、新規 lemma 不要)。

---

## 5 軸サブ項目の判定まとめ

| サブ項目 | 内容 | 判定 | 中心 Mathlib API |
|---|---|---|---|
| 1 | `Measure.pi (fun _ => gaussianReal 0 σ²)` の型クラス | **既存** | `pi.instIsProbabilityMeasure` + `instIsProbabilityMeasureGaussianReal` |
| 2 | 2 段 `Measure.pi` で `Fin M → Fin n → ℝ` 上 prob 測度 | **既存** | サブ項目 1 を再帰的に適用、追加 lemma なし |
| 3 | `EuclideanSpace` flatten (Option B) | **既存** (重い) | `stdGaussian` / `map_pi_eq_stdGaussian` / `multivariateGaussian` |
| 4 | codewords IndepFun | **既存** | `iIndepFun_pi` + `iIndepFun.indepFun` |
| 5 | projection marginal | **既存** | `measurePreserving_eval` |
| 6 | marginal が iid Gaussian | **既存** (1 + 5 合成) | `measurePreserving_eval` + サブ項目 1 |

**結論**: 軸 1 の必要 API はすべて Mathlib に揃っている。Phase A は新規 Mathlib
寄与なしで完了可能。Phase A の plumbing は plan 見積 80-150 行で十分妥当。

---

## 判断 #2 (codebook 測度 type)

### 推奨: Option A (2 段 `Measure.pi`)

```lean
noncomputable def gaussianCodebook (M n : ℕ) (σ² : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σ²))
```

### 採用根拠

1. **型整合**: `Fin M → Fin n → ℝ` は `AwgnCode.encoder : Fin M → (Fin n → ℝ)`
   (`Common2026/Shannon/AWGN.lean:97-103`) と直接 defeq。Phase D の `awgn_extract_AwgnCode`
   で encoder 抽出が `id`-cast で済む。
2. **型クラス無料**: サブ項目 1-2 で全 instance が `infer_instance` で起動。
   追加の `[BorelSpace _]` 等は不要。
3. **IndepFun API 直結**: `iIndepFun_pi` (Basic.lean:784) が 2 段の **外側** に
   `X i = id` で直接 fire。codewords indep が 2-3 行で取れる。
4. **marginal API 直結**: `measurePreserving_eval` (Pi.lean:407) が `(· m)` の
   marginal を 1 行で νₙ に等しいと示せる。

### Option B (`stdGaussian (EuclideanSpace ℝ (Fin (M*n)))`) を採らない理由

1. **型不整合**: `EuclideanSpace ℝ (Fin (M*n))` ≠ `Fin M → Fin n → ℝ`。
   measurable equivalence (`Fin M × Fin n ≃ᵐ Fin (M*n)`, `EuclideanSpace ≃ᵐ Pi ℝ`) を
   経由する 2 段 transport が必要、Phase A で +30-50 行の overhead。
2. **`σ² ≠ 1` の重さ**: `stdGaussian` は variance = 1 固定。`σ² ≠ 1` には
   `multivariateGaussian 0 (σ² • 1)` 経由で `CFC.sqrt` を触る必要。
   `Matrix.PosSemidef` chain は `infer_instance` で通るが、symbolic
   manipulation が重く Phase A 終わらせる気が失せる。
3. **必要な追加型クラス**: `[BorelSpace (EuclideanSpace ℝ _)]` (自動だが
   chain 中に表面化する)、`[FiniteDimensional ℝ _]`、`[DecidableEq (Fin (M*n))]`
   など、Option A では一切要らない `instance` が並ぶ。

### Option B 保留条件 (軸 2 待ち)

軸 2 (continuous AEP) inventory で **「n-dim Gaussian SLLN が `stdGaussian E` 入力でしか
Mathlib に在庫しない」** ことが判明した場合のみ、Option B 採用を再検討。1-d SLLN を
coordinate-wise に起動できる場合 (`measurePreserving_eval` + 1-d
`MeasureTheory.LLN` の組み合わせ) は Option A 継続。

---

## 危険な発見

- **`iIndepFun_pi` の `[∀ i, IsProbabilityMeasure (μ i)]` ambient prerequisite**
  (Basic.lean:779) はファイルレベル `variable` から継承で signature には現れない
  が、適用時に絶対必要。サブ項目 1 で νₙ が prob measure であることを自動推論で
  確保しているので Phase A では問題ないが、もし途中で νₙ を「IsFiniteMeasure に
  落とした非正規化版」に書き換えた瞬間に `iIndepFun_pi` が unify しなくなる。
  Phase A の definition は `gaussianReal 0 σ²` (= prob measure) のままで触らないこと。

- **`measurePreserving_eval` には `[∀ i, IsProbabilityMeasure (μ i)]` が明示的に
  要る** (Pi.lean:407)。`pi_map_eval` (一般版、Pi.lean:379) は scalar
  `∏ μ j univ` が残るので、prob measure で消える形を使うこと。
  Phase A で書く `gaussianCodebook_codeword_law` の 1 行 proof は
  `measurePreserving_eval` 一択。

- **`Measure.pi` の `MeasurableSpace` instance は内側の `MeasurableSpace.pi` を
  介して自動で起動するが、2 段ネストでは項を露わにすると `MeasurableSpace
  (Fin M → Fin n → ℝ)` と `Pi.measurableSpace` の defeq に頼ることになる**。
  `unfold gaussianCodebook` 後の状態で `measurePreserving_eval` を当てる際、
  内側 `Fin n → ℝ` 上の `MeasurableSpace` が `Pi.measurableSpace` 経由で
  期待形になっているかを Phase A 着手時に LSP で 1 回確認すること。

---

## 着手 skeleton (Phase A の最初の Write 候補)

> 本 skeleton は **Phase A の出発点提案**。実装 agent は本ファイルを参照しつつ
> 別ファイル `Common2026/Shannon/AWGNAchievabilityDischarge.lean` に Write する
> (本 inventory file は read-only)。

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNAchievability

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ProbabilityTheory

/-- Random Gaussian codebook: M codewords, each n i.i.d. ~ 𝒩(0, σ²).
    Concrete type `Fin M → Fin n → ℝ` matches `AwgnCode.encoder`. -/
noncomputable def gaussianCodebook (M n : ℕ) (σ² : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σ²))

instance (M n : ℕ) (σ² : ℝ≥0) : IsProbabilityMeasure (gaussianCodebook M n σ²) := by
  unfold gaussianCodebook; infer_instance

theorem gaussianCodebook_codeword_law (M n : ℕ) (σ² : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σ²).map (· m) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 σ²) := by
  sorry  -- one-liner via measurePreserving_eval

theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σ² : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c : Fin M → Fin n → ℝ => c m)
             (fun c : Fin M → Fin n → ℝ => c m')
             (gaussianCodebook M n σ²) := by
  sorry  -- iIndepFun_pi + iIndepFun.indepFun

end InformationTheory.Shannon.AWGN
```

---

## 撤退ラインへの距離

- **T-1 (`Measure.pi` 型クラス壁)** の **発動なし**。サブ項目 1-2 で型クラス
  チェーンが全自動で起動することを確認済み。T-1 は Phase A 開始時の予防的
  ライン (plan §撤退ライン) だったが、本 inventory の結果により**当面破棄候補**。
- ただし「実装中に Lean のクラス推論が unfold ヒューリスティクスで詰まる」可能性は
  残るので、T-1 自体は plan に残置のまま、本 inventory が「在庫面では破棄可」を
  追加判定したと位置づける。
- 軸 2-5 inventory は本 file の判定とは独立。**特に軸 2 で n-dim Gaussian AEP が
  Mathlib 不在と確定すれば T-2 採用** (achievability core は本物 discharge、AEP
  bound 3 つを `IsContinuousAEPGaussian` regularity hyp に packing) → これは
  軸 2 inventory の責務。
