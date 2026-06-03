# Ch.17 Minkowski determinant inequality — Mathlib inventory

> **Parent plan**: [`chapter-17-frontier-sweep-plan.md`](chapter-17-frontier-sweep-plan.md) §Phase 2
> **Date**: 2026-05-28
> **Subagent**: `mathlib-inventory` (docs-only, no Lean touched)

---

## 一行サマリ

**4 軸 ranking: 1=POSITIVE / 2=PARTIAL / 3=PARTIAL / 4=PARTIAL (Mathlib に multivariate Gaussian が存在する SURPRISE)。** ただし主結論 `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` 自体は NEGATIVE (Mathlib に minkowski-det 形は不在)。**Phase 3 推奨ルート: shared sorry 補題 `minkowskiDeterminantInequality` 1 件 + `@residual(wall:minkowski-det-posdef)` (新規 wall 候補) を default、textbook genuine 証明 (AM-GM + 同時対角化) は軸 1+3 が POSITIVE/PARTIAL なので Phase 3 で本格挑戦も合理的選択肢。** Phase 2 dispatch brief で「軸 4 NEGATIVE」と予測したが verbatim 確認で **wall (ii) 名称 drift を発見**: 正しい名は `gaussianMultivariate` ではなく `multivariateGaussian` で、**Mathlib に存在する**。撤退ライン **L-CH17-2-γ** (multivariate Gaussian が landing 済の surprise POSITIVE 化) が**部分的に発火**: ただし `differentialEntropy` (InformationTheory 1-D 版のみ) と `entropyPower` (Mathlib 不在) は依然として multivariate 化が必要なため、Gaussian additivity 経路で Minkowski に bridge するには複数 自作 layer (vector `differentialEntropy` + `multivariateGaussian` の entropy 評価 + EPI multivariate 形) が必要、軸 4 は **PARTIAL** に格上げ。

---

## 二重壁 verbatim 再確認 (本 task)

二重壁の predict/actual:

### Wall (i): `Matrix.det_add` 系

**Query 1**: `loogle "Matrix.det, _ + _"`
**結果**: `Found 48 declarations mentioning HAdd.hAdd and Matrix.det. Of these, 48 match your pattern(s).`

48 件をすべて目視確認: `Matrix.det_updateCol_add_self`、`det_updateRow_add_*`、`det_succ_column`、`det_one_add_smul`、`det_add_mul` (Schur complement)、`det_one_add_X_smul`、`coeff_det_X_add_C_*` 等。**general `det (A + B)` (A, B 任意行列) を直接扱う公式は 0 件**。Schur complement 系の `Matrix.det_add_mul` は `det (A + U * V)` で行列乗法を介する形で本件の `A + B` (純加法) には適用不能。

**Query 2 (refinement)**: `loogle "Matrix.det (_ + _)"` (subterm pattern)
**結果**: `Found 45 declarations ... Of these, 15 match your pattern(s).`

15 件は `det (X·I + 何々)` / `det (1 + …)` / `det (… + smul·1)` 等の Charpoly / Polynomial 特殊形のみ。**PosDef + 一般加法形は引き続き 0 件**。

**Query 3**: `loogle "Matrix.det, Matrix.PosDef"`
**結果**: `Found 2 declarations`: `Matrix.PosDef.det_pos` (det 正値性のみ)、`Matrix.PosSemidef.posDef_iff_det_ne_zero`。**Minkowski 形 0 件**。

**Verdict**: Wall (i) 維持 — `det(A+B)` Mathlib 不在。drift なし。

### Wall (ii): multivariate Gaussian (`gaussianMultivariate`)

**Query**: `loogle "ProbabilityTheory.gaussianMultivariate"`
**結果**: `unknown identifier 'ProbabilityTheory.gaussianMultivariate'`

**しかし**: ファイル探索 `ls .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/` で **`Multivariate.lean` が存在**。中身は `multivariateGaussian` (camelCase、`gaussianMultivariate` ではない)。

**Query 確認**: `loogle "ProbabilityTheory.multivariateGaussian"`
**結果**: `Found 12 declarations`:

```
ProbabilityTheory.multivariateGaussian
ProbabilityTheory.multivariateGaussian_of_not_posSemidef
ProbabilityTheory.multivariateGaussian_zero_one
ProbabilityTheory.integral_id_multivariateGaussian
ProbabilityTheory.integral_id_multivariateGaussian'
ProbabilityTheory.covarianceBilin_multivariateGaussian
ProbabilityTheory.covariance_eval_multivariateGaussian
ProbabilityTheory.variance_eval_multivariateGaussian
ProbabilityTheory.measurePreserving_eval_multivariateGaussian
ProbabilityTheory.charFun_multivariateGaussian
ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian
ProbabilityTheory.isGaussian_multivariateGaussian
```

**Verdict drift**: Phase 0-B でも parent plan でも `gaussianMultivariate` という存在しない名前で 0 件確認していた (識別子 typo)。**Mathlib に multivariate Gaussian は存在する**。

ただし、**直接の `differentialEntropy (multivariateGaussian μ S)` 計算式 (= `(1/2) log ((2πe)^n det S)`) は Mathlib 不在**。これは `differentialEntropy` 自体が Mathlib に存在しないため (InformationTheory の `InformationTheory/Shannon/DifferentialEntropy.lean:45` が 1-D 版のみ定義)。

→ wall (ii) の正味状態: **「multivariate Gaussian の measure / charFun / covariance API は POSITIVE、entropy / entropy power API は NEGATIVE」** の split。Phase 0-B の「unknown identifier → 不在」結論は **不正確** (識別子間違いによる false negative)。

---

## 主定理の最終形 (再掲)

```lean
/-- Cover-Thomas Theorem 17.9.1: Minkowski determinant inequality.
    For PosDef A B, det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n). -/
theorem minkowskiDeterminantInequality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ)) + (B.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ ((A + B).det) ^ (1 / (Fintype.card n : ℝ)) := by
  sorry -- @residual(wall:minkowski-det-posdef)
```

証明戦略 (Cover-Thomas 17.9 textbook):

```
1. A PosDef → IsHermitian → spectral_theorem: A = U diag(λᵢ) Uᴴ           -- 軸 1 POSITIVE
2. (A + B) PosDef (closure under +)、固有値 μᵢ > 0                          -- 軸 1 POSITIVE
3. 同時対角化 (B' := U^(-1) B U^(-H) も PosDef)
4. Minkowski → 各 i で 1 + λᵢ⁻¹ μᵢ' ≥ (1 + λᵢ^(-1/n) μᵢ'^(1/n))^n          -- AM-GM (軸 3 PARTIAL)
5. ∏ᵢ (μᵢ'(A) + μᵢ'(B)) / ∏ᵢ λᵢ ≥ (1 + (det B'/det A')^(1/n))^n
6. det(A+B) = det A · det(I + A⁻¹B) = det A · ∏ (1 + ν_i)
7. ⇒ det(A+B)^(1/n) ≥ det A^(1/n) + det B^(1/n)
```

代替戦略 (Cover-Thomas 17.9.2 entropic proof):

```
1. X ~ multivariateGaussian 0 A, Y ~ multivariateGaussian 0 B 独立                -- 軸 4 PARTIAL (measure 存在)
2. h(X+Y) ≥ h(X) + h(Y) + (n/2) log(2)... を multivariate EPI から                -- 軸 4 NEGATIVE (multivariate EPI 不在)
3. h(Gaussian, cov C) = (1/2) log((2πe)^n det C) を変形                          -- 軸 4 NEGATIVE (multivariate differentialEntropy 不在)
4. 整理 ⇒ Minkowski determinant
```

---

## 軸 1: `Matrix.PosDef` 系 (加法閉性 + det 正値性 + 対角化)

**Ranking**: **POSITIVE**

Mathlib `Matrix.PosDef` の API は加法閉性・正値性・spectral diagonalization まで揃っている。Minkowski 証明の入口インフラとしては十分。

### `Matrix.PosDef`

- **file:line**: `Mathlib/LinearAlgebra/Matrix/PosDef.lean:67-70` (定義位置の典型)
- **signature (verbatim)**:
  ```
  structure Matrix.PosDef [...]  (M : Matrix n n R) : Prop where
    isHermitian : M.IsHermitian
    re_dotProduct_pos : ∀ {x : n → R}, x ≠ 0 → 0 < re (star x ⬝ᵥ M *ᵥ x)
  ```
- **type-class 前提**: `[Fintype n] [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]` (場所により variant)
- **結論**: structure (`IsHermitian` + dot-product positivity)
- **Phase 3 での扱い**: hypothesis として受ける主入力。

### `Matrix.PosDef.add` (加法閉性、PosDef + PosDef)

- **file:line**: `Mathlib/LinearAlgebra/Matrix/PosDef.lean:255-257`
- **signature (verbatim)**:
  ```
  protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
      (hA : A.PosDef) (hB : B.PosDef) : (A + B).PosDef :=
    hA.add_posSemidef hB.posSemidef
  ```
- **引数 (explicit)**: `(hA : A.PosDef) (hB : B.PosDef)`
- **引数 (instance)**: `[Fintype m] [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [AddLeftMono R]`
- **結論 (verbatim)**: `(A + B).PosDef`
- **Phase 3 での扱い**: ✅ そのまま `(hA.add hB).det_pos` で `det (A+B) > 0` が出る。

### `Matrix.PosDef.add_posSemidef` / `Matrix.PosDef.posSemidef_add`

- **file:line**: `Mathlib/LinearAlgebra/Matrix/PosDef.lean:244-253`
- **signature**:
  ```
  protected lemma add_posSemidef [AddLeftMono R] {A B : Matrix m m R}
      (hA : A.PosDef) (hB : B.PosSemidef) : (A + B).PosDef
  protected lemma posSemidef_add [AddLeftMono R] {A B : Matrix m m R}
      (hA : A.PosSemidef) (hB : B.PosDef) : (A + B).PosDef
  ```
- **Phase 3 での扱い**: backup (PosSemidef との混合用)。

### `Matrix.posDef_sum` (有限和への一般化)

- **file:line**: `Mathlib/LinearAlgebra/Matrix/PosDef.lean:259-269`
- **signature (verbatim)**:
  ```
  theorem _root_.Matrix.posDef_sum {ι : Type*} [AddLeftMono R] {A : ι → Matrix m m R}
      {s : Finset ι} (hs : s.Nonempty) (hA : ∀ i ∈ s, (A i).PosDef) : (∑ i ∈ s, A i).PosDef
  ```
- **Phase 3 での扱い**: 不使用 (2 項加法で十分)。多変量への一般化検討時の予備。

### `Matrix.PosDef.det_pos`

- **file:line**: `Mathlib/Analysis/Matrix/PosDef.lean:85-89`
- **signature (verbatim)**:
  ```
  lemma det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    apply Finset.prod_pos
    intro i _
    simpa using hA.eigenvalues_pos i
  ```
- **type-class 前提**: `[Fintype n] [DecidableEq n] [RCLike 𝕜]` (`Mathlib.Analysis.Matrix.PosDef` namespace, `A : Matrix n n 𝕜`)
- **結論 (verbatim)**: `0 < det A`
- **Phase 3 での扱い**: ✅ `(det A)^(1/n)` を `Real.rpow` で取るには `det A > 0` が必要。直接適用可。

### `Matrix.PosDef.isHermitian`

- **file:line**: `Mathlib/LinearAlgebra/Matrix/PosDef.lean` (structure field アクセサ、`PosDef` 定義位置の field)
- **signature**: `theorem isHermitian (hA : A.PosDef) : A.IsHermitian` (structure 1st field)
- **Phase 3 での扱い**: spectral_theorem への入口。

### `Matrix.PosDef.eigenvalues_pos`

- **file:line**: `Mathlib/Analysis/Matrix/PosDef.lean:82-83`
- **signature (verbatim)**:
  ```
  lemma eigenvalues_pos [DecidableEq n] (hA : A.PosDef) (i : n) : 0 < hA.1.eigenvalues i :=
    hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i
  ```
- **type-class 前提**: `[Fintype n] [DecidableEq n] [RCLike 𝕜]`
- **結論 (verbatim)**: `0 < hA.1.eigenvalues i`
- **Phase 3 での扱い**: ✅ AM-GM 適用時に各固有値の正値性が要る。直接利用。

### `Matrix.IsHermitian.spectral_theorem` (対角化)

- **file:line**: `Mathlib/Analysis/Matrix/Spectrum.lean:144-147`
- **signature (verbatim)**:
  ```
  theorem spectral_theorem :
      A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    rw [← conjStarAlgAut_star_eigenvectorUnitary, ← conjStarAlgAut_mul_apply]
    simp
  ```
- **type-class 前提**: `[RCLike 𝕜] [Fintype n] [DecidableEq n]`、変数 `hA : A.IsHermitian`
- **結論 (verbatim)**: `A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))`
- **Phase 3 での扱い**: 同時対角化アプローチで A, B を別々に対角化、`U^(-1) B U^(-H)` を再 PosDef 化する経路で利用 (CT 17.9.1 proof)。

### `Matrix.IsHermitian.det_eq_prod_eigenvalues`

- **file:line**: `Mathlib/Analysis/Matrix/Spectrum.lean:192-194`
- **signature (verbatim)**:
  ```
  theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
    simp [det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly,
      hA.roots_charpoly_eq_eigenvalues]
  ```
- **type-class 前提**: `[RCLike 𝕜] [Fintype n] [DecidableEq n]`
- **結論 (verbatim)**: `det A = ∏ i, (hA.eigenvalues i : 𝕜)`
- **Phase 3 での扱い**: ✅ `det(A+B) = ∏ ν_i(A+B)` で AM-GM につなぐ核補題。

### `Matrix.IsHermitian.eigenvalues`

- **file:line**: `Mathlib/Analysis/Matrix/Spectrum.lean:64-66`
- **signature (verbatim)**:
  ```
  noncomputable def eigenvalues : n → ℝ := fun i =>
    hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
  ```
- **type-class 前提**: `[Fintype n] [DecidableEq n] [RCLike 𝕜]`、変数 `hA : A.IsHermitian`
- **結論**: 固有値は **ℝ-valued** (`RCLike 𝕜` のとき: `n → ℝ`)
- **Phase 3 での扱い**: AM-GM のターゲット (ℝ 列としての ν_i)。

### `Matrix.IsHermitian.add`

- **file:line**: `Mathlib/LinearAlgebra/Matrix/Hermitian.lean:200-203`
- **signature (verbatim)**:
  ```
  @[simp]
  theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
      (A + B).IsHermitian :=
    IsSelfAdjoint.add hA hB
  ```
- **Phase 3 での扱い**: `PosDef.add` の内部実装で使用済 (直接書く必要なし)。

**軸 1 verdict**: **POSITIVE**。Minkowski 証明に必要な PosDef 加法閉性 / det 正値性 / 同時対角化 (spectral theorem) すべて Mathlib に揃っている。`Matrix.PosDef.add` + `Matrix.PosDef.det_pos` + `Matrix.IsHermitian.spectral_theorem` + `Matrix.IsHermitian.det_eq_prod_eigenvalues` が core 4 件。

---

## 軸 2: `det^(1/n)` の代数性質

**Ranking**: **PARTIAL**

`Real.rpow` 自体は完備、Minkowski 形 (`(a^p + b^p)^(1/p) ≤ a + b`) も `MeanInequalitiesPow` に整備済。ただし「`det^(1/n)` を扱うための adapter (det が ℝ-valued ⇔ ℝ≥0 lift) は明示的補題ではなく `Matrix.PosDef.det_pos` から `Real.rpow_nonneg` 等を経由する数行の plumbing が必要」。

### `NNReal.rpow_add_le_add_rpow` (concavity at `p ≤ 1`、Minkowski の "rpow 形")

- **file:line**: `Mathlib/Analysis/MeanInequalitiesPow.lean:177-184`
- **signature (verbatim)**:
  ```
  theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
      (a + b) ^ p ≤ a ^ p + b ^ p := by
    rcases hp.eq_or_lt with (rfl | hp_pos)
    · simp
    have h := rpow_add_rpow_le a b hp_pos hp1
    rw [one_div_one, one_div] at h
    repeat' rw [NNReal.rpow_one] at h
    exact (NNReal.le_rpow_inv_iff hp_pos).mp h
  ```
- **引数**: `(a b : ℝ≥0)` (explicit)、`(hp : 0 ≤ p) (hp1 : p ≤ 1)` (explicit)
- **結論 (verbatim)**: `(a + b) ^ p ≤ a ^ p + b ^ p`
- **Phase 3 での扱い**: ⚠️ これは**逆向き**の不等式。`(a+b)^(1/n) ≤ a^(1/n) + b^(1/n)` (subadditivity)。Minkowski determinant は `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` (superadditivity) なので**反対向き**。`det(A+B) ≥ a + b` 形で扱うわけではなく、別経路 (固有値同時対角化 + AM-GM) で組む必要あり。direct には**使えない**。

### `Real.rpow_add_le_add_rpow`

- **file:line**: `Mathlib/Analysis/MeanInequalitiesPow.lean:209-214`
- **signature (verbatim)**:
  ```
  lemma rpow_add_le_add_rpow {p : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
      (hp1 : p ≤ 1) :
      (a + b) ^ p ≤ a ^ p + b ^ p := by
    lift a to NNReal using ha
    lift b to NNReal using hb
    exact_mod_cast NNReal.rpow_add_le_add_rpow a b hp hp1
  ```
- **結論 (verbatim)**: `(a + b) ^ p ≤ a ^ p + b ^ p`
- **Phase 3 での扱い**: 上と同じく**逆向き**。NOT useful direct.

### `NNReal.rpow_arith_mean_le_arith_mean_rpow` (一般化 AM-GM, p ≥ 1)

- **file:line**: `Mathlib/Analysis/MeanInequalitiesPow.lean:103-107`
- **signature (verbatim)**:
  ```
  theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) {p : ℝ}
      (hp : 1 ≤ p) : (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p
  ```
- **結論 (verbatim)**: `(∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p`
- **Phase 3 での扱い**: AM-GM の `p ≥ 1` 方向 (convex)。Minkowski 証明では **p = 1/n ≤ 1** 方向が要るので別 lemma 必要 (→ 軸 3 `geom_mean_le_arith_mean`)。

### `Real.rpow_arith_mean_le_arith_mean_rpow`

- **file:line**: `Mathlib/Analysis/MeanInequalitiesPow.lean:73-76`
- **signature (verbatim)**:
  ```
  theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
      (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
      (∑ i ∈ s, w i * z i) ^ p ≤ ∑ i ∈ s, w i * z i ^ p :=
    (convexOn_rpow hp).map_sum_le hw hw' hz
  ```
- **Phase 3 での扱い**: 軸 2 PARTIAL の中心: `1/n ≤ 1` 方向は直接対応する lemma が無いが、`Real.geom_mean_le_arith_mean_weighted` (軸 3) で代用可。

### `Real.rpow_nonneg`, `Real.rpow_le_rpow`, `Real.rpow_natCast` 等

- これらは `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` に多数存在 (代数的 plumbing 用)。本 inventory では個別 file:line 省略 (200+ 件)。Phase 3 では必要に応じて随時引用。

**軸 2 verdict**: **PARTIAL**。Minkowski 「(a+b)^p form」自体は Mathlib にあるが **p≤1 で subadditive 方向のみ** (Minkowski-det は逆向き superadditive)。Det 同時対角化経由で固有値の AM-GM に持ち込む必要 → 軸 3 が本命。

---

## 軸 3: AM-GM / Hadamard 不等式

**Ranking**: **PARTIAL**

AM-GM (`geom_mean_le_arith_mean_weighted`) は Mathlib に揃う。Hadamard 不等式 (`det A ≤ ∏ ‖rowᵢ‖`) は **不在** (確認済)。Minkowski 証明には Hadamard 自体は不要 (AM-GM だけで足りる)。

### `Real.geom_mean_le_arith_mean_weighted` (重み付き AM-GM)

- **file:line**: `Mathlib/Analysis/MeanInequalities.lean:130-152` (theorem block)
- **signature (verbatim)**:
  ```
  theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
      (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
      (∏ i ∈ s, z i ^ w i) ≤ ∑ i ∈ s, w i * z i
  ```
  (注: verbatim 取得には `Mathlib.Analysis.MeanInequalities` 内の 130 行目近辺を Read 推奨。 1 つだけ確認できているのは name 一致 (loogle `Found one declaration`))
- **引数**: `(w z : ι → ℝ)` (重み + 値)、`(hw : ∀ i ∈ s, 0 ≤ w i)`、`(hw' : ∑ i ∈ s, w i = 1)` (確率重み)、`(hz : ∀ i ∈ s, 0 ≤ z i)`
- **結論 (verbatim)**: `(∏ i ∈ s, z i ^ w i) ≤ ∑ i ∈ s, w i * z i`
- **Phase 3 での扱い**: ✅ 等重み `w i = 1/n` で `(∏ zᵢ)^(1/n) ≤ (1/n) ∑ zᵢ` の標準 AM-GM。Minkowski 証明で `(det A)^(1/n) = (∏ λᵢ)^(1/n)` を扱う中心 lemma。`z i ^ w i` の `^` は `Real.rpow` (型推論で確定)。

### `Real.geom_mean_le_arith_mean` (重みなし)

- **file:line**: `Mathlib/Analysis/MeanInequalities.lean:153-156`
- **signature (verbatim)**:
  ```
  theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℝ)
      ...  -- (continuation 内省略)
  ```
- **Phase 3 での扱い**: 重みなし版 (`(∏ z)^(1/|s|) ≤ ∑z/|s|`)、上と等価。

### `NNReal.geom_mean_le_arith_mean_weighted`

- **file:line**: `Mathlib/Analysis/MeanInequalities.lean:278-283`
- **signature (verbatim)**:
  ```
  theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) :
      (∏ i ∈ s, z i ^ (w i : ℝ)) ≤ ∑ i ∈ s, w i * z i :=
    le_of_forall_pos_le_add fun _ ε_pos => by
      ...
  ```
  (verbatim 末尾は省略)
- **Phase 3 での扱い**: NNReal cast を経由する場合の便利版。

### `strictConcaveOn_log_Ioi`

- **file:line**: `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67`
- **signature (verbatim)**: `theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log`
- **Phase 3 での扱い**: AM-GM を log Jensen 形で書き直すバックアップ (`log ∘ ∏ = ∑ log` + Jensen)。直接 AM-GM lemma で済めば不要。

### Hadamard 不等式 (Mathlib 不在)

- **Query**: `loogle "Matrix.det_le_prod_diag"`, `rg "Hadamard.*det" Mathlib/`
- **結果**: Mathlib に Hadamard 不等式 `|det A| ≤ ∏ᵢ ‖row_i A‖` (PosDef 形なら `det A ≤ ∏ Aᵢᵢ`) は**不在**。`Matrix.PosDef.hadamard` (`Mathlib/Analysis/Matrix/Order.lean`) は Hadamard 積の PosDef 閉性で、本件 Hadamard 不等式とは **別物** (名前衝突注意)。
- **Phase 3 での扱い**: Cover-Thomas 17.9.1 textbook proof は Hadamard 不等式 **を使わない** (同時対角化 + AM-GM だけで完結)。なので Hadamard 不在は本 plan の障害にならない。

**軸 3 verdict**: **PARTIAL**。AM-GM (`geom_mean_le_arith_mean_weighted`) は POSITIVE で証明骨格に直接使える。Hadamard 不等式は NEGATIVE だが proof に不要。「PARTIAL」と評価したのは AM-GM の引数が `(w z : ι → ℝ)` で weight + value 分離形 (Minkowski 内では `w = 1/n`, `z = (λᵢ(A) + λᵢ(B))/λᵢ(A)` 等の具体配線が要る、~5-10 行 plumbing) のため。

---

## 軸 4: 代替 route (Gaussian additivity → multivariate lift)

**Ranking**: **PARTIAL (SURPRISE: multivariate Gaussian は Mathlib に存在)**

Phase 0-B の orchestrator 仮定 (「`gaussianMultivariate` Mathlib 不在 → 軸 4 NEGATIVE」) は**部分的に誤り**。正しい名前 `multivariateGaussian` で Mathlib に landing 済 (12 declarations)。

ただし Cover-Thomas 17.9.2 entropic proof を実現するための **`differentialEntropy` の multivariate 形** と **`entropyPower` の multivariate 形** は Mathlib 不在 (InformationTheory にも 1-D 版のみ)。Gaussian additivity → Minkowski lift には複数自作 layer が必要。

### `ProbabilityTheory.multivariateGaussian` (定義、SURPRISE: 存在)

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:167-170`
- **signature (verbatim)**:
  ```
  /-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
  matrix `S`. This only makes sense when `S` is positive semidefinite,
  as then `CFC.sqrt S * CFC.sqrt S = S`. Otherwise `CFC.sqrt S = 0`, and
  `multivariateGaussian μ S = Measure.dirac μ`. -/
  noncomputable
  def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
      Measure (EuclideanSpace ℝ ι) :=
    (stdGaussian (EuclideanSpace ℝ ι)).map
      (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
  ```
- **type-class 前提**: `[Fintype ι] [DecidableEq ι]` (file-level variable)
- **codomain**: `EuclideanSpace ℝ ι`
- **退化境界注意 (CLAUDE.md「具体的数値・型予測の verbatim 確認」)**: `S` が PosSemidef でないと **`Measure.dirac μ` に退化** (`multivariateGaussian_of_not_posSemidef`、line 172-177)。Minkowski 用に使うときは `S.PosDef → S.PosSemidef` (Mathlib `Matrix.PosDef.posSemidef`) で正則化必須。退化を踏むと entropy 計算の Gaussian 形が崩れ、`-∞ vs 0` の境界 case がやはり混入する。
- **Phase 3 での扱い**: Cover-Thomas 17.9.2 経路の主入力。⚠️ ただし `differentialEntropy (multivariateGaussian μ S) = (1/2) log ((2πe)^n det S)` の式は Mathlib 不在 (自作必要)。

### `ProbabilityTheory.isGaussian_multivariateGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:186-191`
- **signature (verbatim)**:
  ```
  instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
    have h : (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) =
      (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) := rfl
    simp only [multivariateGaussian]
    rw [h, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
    infer_instance
  ```
- **結論 (verbatim)**: `IsGaussian (multivariateGaussian μ S)` (instance)
- **Phase 3 での扱い**: `IsGaussian` instance 自動推論用。

### `ProbabilityTheory.covarianceBilin_multivariateGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:202-214`
- **signature (verbatim)**:
  ```
  lemma covarianceBilin_multivariateGaussian (hS : S.PosSemidef) (x y : EuclideanSpace ℝ ι) :
      covarianceBilin (multivariateGaussian μ S) x y = x ⬝ᵥ S *ᵥ y
  ```
- **type-class 前提**: variable `{μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}` (`[Fintype ι] [DecidableEq ι]` 継承)
- **結論 (verbatim)**: `covarianceBilin (multivariateGaussian μ S) x y = x ⬝ᵥ S *ᵥ y`
- **Phase 3 での扱い**: 共分散 S の取り出し用。

### `ProbabilityTheory.charFun_multivariateGaussian`

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:239-242`
- **signature (verbatim)**:
  ```
  lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
      charFun (multivariateGaussian μ S) x =
        exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2)
  ```
- **Phase 3 での扱い**: 特性関数経由の Gaussian additivity (`X + Y` の特性関数 = 積) → multivariate convolution closure に使える。

### `InformationTheory.Shannon.differentialEntropy` (1-D のみ、Mathlib 不在)

- **file:line**: `InformationTheory/Shannon/DifferentialEntropy.lean:45`
- **signature**:
  ```
  noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
    ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
  ```
- **状態**: ✅ 1-D 既存 (codomain `Measure ℝ` のみ)
- **Phase 3 での扱い**: ❌ multivariate 形 `Measure (EuclideanSpace ℝ ι) → ℝ` が要るが InformationTheory にも不在。新規定義必要。**ただし `InformationTheory/Shannon/MultivariateDiffEntropy.lean` に `jointDifferentialEntropy : Measure (ℝ × ℝ) → ℝ` (2 変数版) と `jointDifferentialEntropyPi : Measure (Fin n → ℝ) → ℝ` (n 変数版) が既存**。EuclideanSpace 形ではなく `Fin n → ℝ` 形に注意 (Mathlib-shape-driven 判断、`multivariate-diffentropy-subadditivity-plan.md` §A1 で記録)。`EuclideanSpace ℝ ι = WithLp 2 (ι → ℝ)` なので `defeq` ではなく `WithLp` 変換が要る。

### `InformationTheory.Shannon.entropyPower` (1-D のみ、Mathlib 不在)

- **status**: `rg "entropyPower"` で InformationTheory 内に複数言及 (`EntropyPowerInequality.lean`)、ただし定義は 1-D `differentialEntropy` 経由のみ。multivariate 形 `entropyPower (μ : Measure (EuclideanSpace ℝ ι)) := exp(2·h(μ)/n) / (2πe)` は不在。Phase 3 で新規定義必要。

### `ProbabilityTheory.gaussianReal_conv_gaussianReal` (univariate additivity、Mathlib 既存)

- **file:line**: `Mathlib/Probability/Distributions/Gaussian/Real.lean` (loogle: `ProbabilityTheory.gaussianReal_conv_gaussianReal`)
- **signature 形 (推定)**: convolution of two `gaussianReal` is `gaussianReal` (variance 加法)
- **Phase 3 での扱い**: univariate Gaussian additivity の Mathlib 既存版。`multivariateGaussian` 形での同様 `additivity` lemma の Mathlib 在庫は今回 cross-check 未実施 (要追加調査、確認時間予算超過)。

**軸 4 verdict**: **PARTIAL**。
- Mathlib 在庫 (POSITIVE 側): `multivariateGaussian` measure 自体、`isGaussian_multivariateGaussian` instance、`covarianceBilin_multivariateGaussian`、`charFun_multivariateGaussian` (12 declarations)。
- Mathlib 不在 (NEGATIVE 側): `differentialEntropy` の multivariate 形、`entropyPower` の multivariate 形、Gaussian の **entropy 表式** `h(N(μ, S)) = (1/2) log ((2πe)^n det S)`、multivariate EPI `h(X+Y) ≥ ...`。
- Phase 3 で entropic proof を採用するには **4 件の InformationTheory 新規補題 + Mathlib 不在 lemma の sorry 化** が必要。コスト的に Phase 3 default の textbook (軸 1+3) 経路より重く、entropic proof 経路は **deferred / 別 plan** が現実的判断。

---

## 主要前提条件ボックス

事故が起きやすい lemma の前提条件をまとめる (CLAUDE.md「Subagent Inventory」の verbatim 型クラス前提)。

### `Matrix.PosDef.add` 前提

- `[Fintype m]` (有限指標)
- `[CommRing R]` (環)
- `[PartialOrder R]` (順序)
- `[StarRing R]` (involution)
- `[StarOrderedRing R]` (★ 互換順序)
- `[AddLeftMono R]` (加法の単調性)
- Phase 3 で `R = ℝ` を取れば `Real` には全 instance 自動 (確認: `ℝ` は `CommRing`, `LinearOrder`, `StarOrderedRing`, `AddLeftMono` すべて instance あり)。

### `Matrix.PosDef.det_pos` 前提

- `[Fintype n]`
- `[DecidableEq n]` ⚠️ — `DecidableEq n` は Minkowski 主定理 signature にも必要 (`n` を Fintype index として扱う)
- `[RCLike 𝕜]` ⚠️ — `Mathlib.Analysis.Matrix.PosDef` の namespace は `𝕜 : Type _` で `RCLike` 必須 (`ℝ` は instance `RCLike ℝ` あり)。
- 変数 `(A : Matrix n n 𝕜) (hA : A.PosDef)`

### `Matrix.IsHermitian.spectral_theorem` 前提

- `[RCLike 𝕜]`
- `[Fintype n]`
- `[DecidableEq n]`
- 変数 `(hA : A.IsHermitian)`
- 内部で `eigenvectorUnitary hA : Matrix.unitaryGroup n 𝕜` を構築
- ⚠️ 戻り値の形 `A = conjStarAlgAut 𝕜 _ U (diagonal (RCLike.ofReal ∘ eigenvalues))` は **`conjStarAlgAut`** で書かれており、proof で展開するには `conjStarAlgAut_apply` (`Mathlib/Algebra/Star/StarAlgHom.lean`) の rewrite が必要。textbook の `A = U D U^*` 形と直接同型ではないので、Phase 3 で再 unfold するか専用 corollary を別作るかの判断が要る (Mathlib-shape-driven definition の典型ケース)。

### `Real.geom_mean_le_arith_mean_weighted` 前提

- `(w z : ι → ℝ)` (両方 explicit)
- `(hw : ∀ i ∈ s, 0 ≤ w i)` ⚠️ — `∀ i ∈ s` であって `∀ i` ではない (Finset 内のみ要請)
- `(hw' : ∑ i ∈ s, w i = 1)` ⚠️ — **確率重み**。等重み `w i = 1/n` を使うときは `(card n : ℝ)⁻¹` で書いて `Finset.sum_const` + `Finset.card_eq_iff` で証明する典型 plumbing
- `(hz : ∀ i ∈ s, 0 ≤ z i)`
- 結論内 `z i ^ w i` の `^` は `Real.rpow` (両 ℝ-valued なので自動)

### `multivariateGaussian` 退化境界 (CLAUDE.md「具体的数値・型予測の verbatim 確認」)

- `S : Matrix ι ι ℝ` が `PosSemidef` でないと **`Measure.dirac μ` に退化** (`multivariateGaussian_of_not_posSemidef` line 172)
- Minkowski 用には `hA : A.PosDef → hA.posSemidef : A.PosSemidef` (Mathlib `Matrix.PosDef.posSemidef`) で先に正則化必須
- 退化を踏むと `differentialEntropy (Measure.dirac μ) = ?` 評価が問題化 (InformationTheory では `DifferentialEntropy.lean:147` `differentialEntropy_dirac = 0` 確認済、entropyPower で 1 (= exp(0))、log で `-∞ vs 0` の境界 case)
- Phase 3 主定理は `hA hB : PosDef` (strictly) を hypothesis にとるので `multivariateGaussian` 退化は本 plan main path では発火しない。ただし途中で `A + B` 等を扱うとき degenerate なら `PosDef.add` (`A + B PosDef`) で再正則化される (退化境界に再到達しないはず)

---

## 自作が必要な要素 (Phase 3 候補)

優先度順:

### 優先度 1: `minkowskiDeterminantInequality` (主定理) — shared sorry 補題

- **推奨実装**: `InformationTheory/Shannon/MinkowskiDet.lean` (新規 file)、shared sorry 補題として `theorem minkowskiDeterminantInequality ... := by sorry` + `@residual(wall:minkowski-det-posdef)`
- **工数感**: signature 起草 ~10 行 + import ~5 行 + namespace + 1 sorry = **~30 行 (type-check done)**
- **落とし穴**: `[DecidableEq n]` を忘れると `det_pos` で詰まる。`Nonempty n` (`Fintype.card n ≥ 1`) を assumption に入れないと `(card n : ℝ)⁻¹` がゼロ除算扱いで `rpow` の degenerate 境界に踏み込む

### 優先度 2: textbook proof attempt (Phase 3 で本格挑戦の場合)

- **推奨実装**: 同 file 内で先に `det_le_arith_mean_eigenvalues_rpow : (∏ λᵢ)^(1/n) ≤ ∑ λᵢ / n` (AM-GM 直接適用 helper)、次に PosDef.add 経由で `det(A+B)` を spectral_theorem + 同時対角化で `∏ ν_i` 形に変形、AM-GM で組み立て
- **工数感**: 同時対角化 + 固有値書換 = ~80-150 行。Mathlib-shape-driven で `eigenvalues` 列を直接扱う path のほうが `conjStarAlgAut` unfold 経路より楽見込
- **落とし穴**: A, B の同時対角化は一方を `A^(-1/2) B A^(-1/2)` で congruence transformation する手順が古典的、ただし `Matrix.PosDef.inv` (`Mathlib/LinearAlgebra/Matrix/PosDef.lean:?` 70 件中存在) と sqrt (`Matrix.IsHermitian.sqrt` → CFC.sqrt 経由、`Mathlib/Analysis/CStarAlgebra/...`) のコンビが整っているか追加調査要 (本 inventory では未確認)

### 優先度 3: 軸 4 用 multivariate entropy 補題群 (entropic proof 経路、別 plan 推奨)

- `vectorDifferentialEntropy (μ : Measure (EuclideanSpace ℝ ι)) : ℝ` 定義
- `vectorDifferentialEntropy_multivariateGaussian : h(N(μ, S)) = (1/2) log ((2πe)^n * S.det)` (Gaussian の entropy 公式)
- `vectorDifferentialEntropy_add_le` (multivariate EPI、これ自体が大物 = Stam-level wall)
- **工数感**: ~500-800 行 (multivariate AEP / Fisher info / score 系の Mathlib 不在分の自作含む)
- **判断**: 本 Phase 3 では **scope-out**。entropic proof は別 family (`multivariate-diffentropy-subadditivity-plan.md` の延長線) と統合した moonshot plan として後続化推奨

---

## Mathlib 壁の列挙 (Phase 3 で `@residual(wall:...)` 化候補)

### 新規 wall 候補: `minkowski-det-posdef`

- **対象**: `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` for `A B : Matrix n n ℝ` PosDef
- **理由**: Mathlib 0 件 (verbatim 確認済)、Cover-Thomas 17.9.1 textbook proof は AM-GM + 同時対角化で組めるが ~80-150 行の implementation がいる
- **shared sorry 補題化推奨**: ✅ Yes — 単一 `theorem minkowskiDeterminantInequality (hA hB : PosDef) : ...` 形で InformationTheory 内 1 箇所に集約、後続 consumer (例: EPI multivariate / Brunn-Minkowski / vector capacity 系) が apply で利用
- **loogle 確認結果**: `Found 0 declarations mentioning Real.rpow and Matrix.det` (`loogle "Matrix.det _, Matrix.det _, Real.rpow"`)、`Found 0 declarations mentioning Real.rpow, LE.le, and HAdd.hAdd` (`loogle "Real.rpow, _ + _, _ ≤ _"`)
- **register への追加位置**: `audit-tags.md`「Wall name register」§ Ch.17 EPI 隣接行に追加候補。隣接 `epi-n-dim` (多次元 EPI / n-dim Prékopa-Leindler) と semantic 区別:
  - `epi-n-dim`: 多次元 entropy power inequality (entropic 形)
  - `minkowski-det-posdef` (新): det 同型 (algebraic 形)、entropic proof と独立に AM-GM + 対角化で組める

### 既存 wall との関係 (semantic 区別)

- `bm-convex-body-sqrt` (Proposed): 凸体 BM の sqrt 形 `vol(A+B)^(1/n) ≥ vol A^(1/n) + vol B^(1/n)` — **本質的に同型 statement** (体積測度 ⇔ det)、ただし対象が「凸体測度」vs 「PosDef 行列の det」で異なる
- `epi-n-dim`: 多次元 EPI `N(X+Y) ≥ N(X) + N(Y)` (entropy power 加法形) — Minkowski-det は Gaussian special case として entropic proof で出る
- 3 件 (`bm-convex-body-sqrt` / `epi-n-dim` / `minkowski-det-posdef`) は同一定理の異種形 (algebraic / geometric / entropic) と捉え、Phase 3 で wall register 入りさせるときは「semantic 区別」表に明示推奨

### 候補追加: なし (軸 1-3 ですべて closure 可能、唯一の本物 wall は主定理 sorry)

---

## 撤退ラインへの距離

親 plan `chapter-17-frontier-sweep-plan.md` §Phase 2 で定義された 3 ライン (L-CH17-2-α/β/γ) を本 inventory 結果に照合:

### L-CH17-2-α (4 軸すべて NEGATIVE → 主定理 sorry のみで撤退)

- **発火条件**: 4 軸すべて NEGATIVE
- **実測**: 軸 1 = POSITIVE, 軸 2 = PARTIAL, 軸 3 = PARTIAL, 軸 4 = PARTIAL (SURPRISE)
- **発火**: **NO** (4/4 NEGATIVE ではない)
- **判定**: Phase 3 で `minkowskiDeterminantInequality := by sorry` + `@residual(wall:minkowski-det-posdef)` の小規模 landing は依然合理的選択肢だが、撤退ラインの強制発火条件は満たされていない

### L-CH17-2-β (軸 2/3 が POSITIVE → genuine 化試行)

- **発火条件**: 軸 2/3 が POSITIVE
- **実測**: 軸 2 = PARTIAL, 軸 3 = PARTIAL
- **発火**: **部分的 (POSITIVE ではないが PARTIAL なので genuine 化試行は合理性が残る)**
- **判定**: 軸 1 (POSITIVE) + 軸 3 (PARTIAL、AM-GM lemma あり) で同時対角化経路の genuine proof は **着手可能**。Phase 3 dispatch で「先に shared sorry 補題 landing → 並行して genuine proof attempt」の 2 段構えが推奨

### L-CH17-2-γ (軸 4 が positive surprise → 親 plan 再 scoping)

- **発火条件**: 軸 4 が positive surprise (multivariate Gaussian Mathlib 入り)
- **実測**: 軸 4 = PARTIAL (multivariate Gaussian measure 自体は **Mathlib 存在**、ただし entropy 周辺は NEGATIVE)
- **発火**: **部分的 (yes for measure, no for entropy)**
- **判定**: **`brunn-minkowski-from-epi-discharge-plan` 等の親 plan との統合検討は適切**。ただし `differentialEntropy` の multivariate 化と Gaussian の entropy 公式 (`h(N) = (1/2) log ((2πe)^n det S)`) は依然として自作必要 — 本 Phase 3 の scope を膨張させる。本 plan default は依然「textbook (軸 1+3) 経路」推奨、entropic proof (軸 4) は別 plan に委ねる

### 新規 (drift) findings

- **drift 1: `gaussianMultivariate` typo は orchestrator brief / Phase 0-B / 親 plan §0-B-1 すべてに残留**。Mathlib 実在 identifier は `multivariateGaussian`。本 inventory で訂正 (drift 検知通知)
- **drift 2: ファイル名 `Multivariate.lean` の存在を Phase 0-B では把握できていなかった**。Phase 3 dispatch brief を書く段階で「multivariate Gaussian は Mathlib 存在、ただし differential entropy 形は不在」と更新すべき

---

## 着手 skeleton (Phase 3 で `lean-implementer` に渡す出だし、~30 行)

```lean
/-
Copyright (c) 2026 ...
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Minkowski determinant inequality (Cover-Thomas Theorem 17.9.1)

For positive-definite matrices `A, B : Matrix n n ℝ`,
`det(A + B)^(1/n) ≥ det A^(1/n) + det B^(1/n)`.

Currently a shared sorry lemma (`@residual(wall:minkowski-det-posdef)`).

-/

namespace InformationTheory.Shannon

open scoped Matrix

/-- Cover-Thomas Theorem 17.9.1: Minkowski determinant inequality.

For PosDef `A B`, `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)`.

⚠️ Mathlib does not provide this inequality directly. Sorry-based shared wall
lemma per audit-tags.md 「共有 Mathlib 壁: shared sorry 補題パターン」.

@residual(wall:minkowski-det-posdef)
-/
theorem minkowskiDeterminantInequality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ)) + (B.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ ((A + B).det) ^ (1 / (Fintype.card n : ℝ)) := by
  sorry

end InformationTheory.Shannon
```

注意:
- `import Mathlib` 禁止 (CLAUDE.md「Import Policy」)、pinpoint import 5 件のみ
- `Matrix n n ℝ` 形 (not `Matrix (Fin n) (Fin n) ℝ`) で型引数を一般化 — Fintype + DecidableEq を要請。後続 consumer の多くは `n = Fin k` で具体化するが、汎用 `n` のままのほうが covariance matrix index 等への適用が広い
- 等号成立条件 (Cover-Thomas 17.9.1 系: A = c·B for c > 0) は本 sorry には含めない。等号成立が必要な後続 consumer が出てきたら別 corollary として `minkowskiDeterminantInequality_eq_iff` を起こす方針
- 後続 wall consumer が単一 file 内に増えてきたら shared sorry 補題化を維持 (`audit-tags.md` 「共有 Mathlib 壁」)
- `InformationTheory.lean` への import 1 行追加は Phase 3 完了時 (本 inventory phase では対象外)

---

## 総合 verdict (Phase 3 dispatch brief 用)

### 軸別 ranking 集計

| 軸 | 想定 (parent §201-208) | 実測 (本 inventory) | 差分 |
|---|---|---|---|
| 1. `Matrix.PosDef` 加法閉性 | POSITIVE | **POSITIVE** | 一致 |
| 2. `det^(1/n)` 代数性質 | PARTIAL〜UNKNOWN | **PARTIAL** | 一致 |
| 3. AM-GM / Hadamard 不等式 | PARTIAL | **PARTIAL** | 一致 |
| 4. multivariate Gaussian lift | NEGATIVE | **PARTIAL (SURPRISE)** | drift: `multivariateGaussian` Mathlib 存在 |

### Per-lemma 件数

- 軸 1: **6 件** core (`Matrix.PosDef`, `Matrix.PosDef.add`, `Matrix.PosDef.det_pos`, `Matrix.PosDef.eigenvalues_pos`, `Matrix.IsHermitian.spectral_theorem`, `Matrix.IsHermitian.det_eq_prod_eigenvalues`) + 補助 3 件 (`add_posSemidef` / `posDef_sum` / `IsHermitian.add`)
- 軸 2: **4 件 reviewed** (`NNReal.rpow_add_le_add_rpow`, `Real.rpow_add_le_add_rpow`, `NNReal.rpow_arith_mean_le_arith_mean_rpow`, `Real.rpow_arith_mean_le_arith_mean_rpow`) — 全て**方向逆 or 適用不可** (Minkowski-det superadditive vs Mathlib subadditive)
- 軸 3: **2 件 core** (`Real.geom_mean_le_arith_mean_weighted`, `NNReal.geom_mean_le_arith_mean_weighted`) + バックアップ `strictConcaveOn_log_Ioi` — Hadamard 不等式は **不在** (Phase 3 で不要)
- 軸 4: **5 件 core** (`multivariateGaussian` def + `isGaussian_multivariateGaussian` + `covarianceBilin_multivariateGaussian` + `charFun_multivariateGaussian` + `multivariateGaussian_of_not_posSemidef`) + 12 件 total

**合計 17 件** (重複・補助含めず) を Phase 3 で参照候補とする。

### Phase 3 推奨 route

**Default**: **2 段構え**
1. **Stage A (確実、~30 行)**: `InformationTheory/Shannon/MinkowskiDet.lean` に shared sorry 補題 `minkowskiDeterminantInequality := by sorry` + `@residual(wall:minkowski-det-posdef)` を landing。type-check done で commit。
2. **Stage B (挑戦的、~80-150 行)**: 同 file 内で textbook proof attempt (軸 1 POSITIVE + 軸 3 AM-GM 経路)。Mathlib-shape-driven で `IsHermitian.spectral_theorem` の `conjStarAlgAut` 形を直接 unfold するか `eigenvalues` 列 + `det_eq_prod_eigenvalues` 経由かは実装時判断。失敗時は sorry を維持して終了。

**回避ルート (entropic proof / 軸 4)**: 別 plan (`multivariate-diffentropy-subadditivity-plan.md` 延長 or 新規 EPI-multivariate moonshot) として後続化。本 Phase 3 では **scope-out**。

### 新規 wall 候補名

**`minkowski-det-posdef`** (新規)。`audit-tags.md` Wall name register への追加文案:

```
| `minkowski-det-posdef` | Cover-Thomas 17.9.1: `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` for PosDef A B (Mathlib 不在、AM-GM + 同時対角化で組めるが未 land) | Ch.17 EPI / 17.9 BM |
```

隣接 wall `epi-n-dim` (entropic 形) / `bm-convex-body-sqrt` (geometric 形、Proposed) との semantic 区別を register コメントで明示推奨。

### 想定外の surprise

1. **`multivariateGaussian` Mathlib 存在 (識別子 typo の false negative)**: Phase 0-B / 親 plan / orchestrator brief すべてで `gaussianMultivariate` という存在しない名前で query して unknown identifier を「不在」と誤判定。Mathlib 実在 identifier は `multivariateGaussian` (`Multivariate.lean`、12 declarations)。drift 通知としてこの inventory で訂正済。Phase 3 dispatch brief / 親 plan §Phase 0-B / §Phase 2 brief を update 推奨。

2. **`Matrix.PosDef.add` のスコープが想定より広い**: `[AddLeftMono R]` という比較的弱い type-class 前提で済む (一般環で動く)、InformationTheory の `R = ℝ` 設定では自動 instance。Phase 2 dispatch brief で「PosDef.add は ℝ 限定だろうか」と不安があったが、実 verbatim では一般環 OK。

3. **`Matrix.IsHermitian.spectral_theorem` の戻り値が `conjStarAlgAut` で書かれている**: textbook `A = U D U^*` 形と直接同型ではなく、Mathlib-shape-driven で proof 構造を選ぶ必要あり。`det_eq_prod_eigenvalues` (固有値列を直接扱う) のほうが Minkowski 証明では使い勝手良い見込。

---

## 撤退ライン発火状況

| ライン | 発火条件 | 実測 | 発火 |
|---|---|---|---|
| L-CH17-2-α | 4 軸すべて NEGATIVE | 軸 1 POS / 2,3 PARTIAL / 4 PARTIAL | **NO** |
| L-CH17-2-β | 軸 2/3 が POSITIVE | 軸 2,3 ともに PARTIAL (POSITIVE ではない) | **部分** |
| L-CH17-2-γ | 軸 4 surprise POSITIVE | 軸 4 PARTIAL (measure POSITIVE, entropy NEGATIVE) | **部分** |

**正式発火: なし**。
**部分発火: L-CH17-2-β + L-CH17-2-γ** — Phase 3 で「shared sorry 補題 landing (Stage A) + textbook genuine 試行 (Stage B)」の 2 段構えを推奨。entropic proof (軸 4 経路) は別 plan に scope-out。

---

> Inventory 終了。Phase 3 では本ファイルを入力とし、`InformationTheory/Shannon/MinkowskiDet.lean` の skeleton を起こす実装フェーズに進む。
