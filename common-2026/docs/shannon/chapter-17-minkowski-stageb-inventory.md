# Ch.17 Minkowski determinant inequality — Stage B (simultaneous-diagonalization) Mathlib inventory

> **Parent inventory**: [`chapter-17-minkowski-inventory.md`](chapter-17-minkowski-inventory.md) (4-軸 sweep, 自作が必要な要素 優先度 2 line 533 が「行列 sqrt / `PosDef.inv` 未確認」と flag)
> **Target file**: `Common2026/Shannon/MinkowskiDet.lean` (Stage A landed: `det_rpow_le_arith_mean_eigenvalues` genuine 0-sorry + `minkowskiDeterminantInequality` sorry + `@residual(wall:minkowski-det-posdef)`)
> **Date**: 2026-05-28
> **Subagent**: `mathlib-inventory` (docs-only, no Lean touched)

---

## 一行サマリ

**Stage B (`A^(-1/2)(A+B)A^(-1/2) = I + A^(-1/2) B A^(-1/2)` 簡約) を支える 5 軸はすべて POSITIVE か PARTIAL。`Matrix.PosDef.inv` 存在 (POSITIVE)、行列 sqrt は `CFC.sqrt` 経由で full API + `Matrix.PosSemidef.det_sqrt` も存在 (POSITIVE)、congruence の PosDef 保存は `Matrix.IsUnit.posDef_star_left/right_conjugate_iff` + `conjTranspose_mul_mul_same` で完備 (POSITIVE)、det 簡約は `det_mul` / `det_nonsing_inv` / `det_sqrt` で揃う (PARTIAL — `det_nonsing_inv` が `⁻¹ʳ` 形で adapter 数行要)、`I + S` 経路は `det_eq_prod_eigenvalues` + `trace_eq_sum_eigenvalues` 既存だが `eigenvalues (1+S) = 1 + eigenvalues S` の直接 lemma が不在 (PARTIAL)。** Stream C の「matrix sqrt は deprecated section」観察は **半分正しく半分 misleading**: `Mathlib/Analysis/Matrix/Order.lean` に literally `section sqrtDeprecated` が存在するが、その中の `inv_sqrt` および直後の `det_sqrt` には **`@[deprecated]` attribute が付いておらず live**。deprecated なのは「Matrix 固有の旧 sqrt def を `CFC.sqrt` に置き換えた」歴史的経緯であり、現行ルートの `CFC.sqrt` は full API。**総合 verdict: Stage B の genuine 証明は今 feasible。`wall:minkowski-det-posdef` を維持するのは正しい (主定理形は Mathlib 0 件、458 件の `Matrix.det` 中に Minkowski 形なし) が、その sorry を closure する道は全 5 軸が埋まったので open。Phase 順序を本ファイル末尾に提案。**

---

## 主定理の最終形 (再掲、実コード verbatim)

`Common2026/Shannon/MinkowskiDet.lean:89-94` (verbatim):

```lean
theorem minkowskiDeterminantInequality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ)) + (B.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ ((A + B).det) ^ (1 / (Fintype.card n : ℝ)) := by
  sorry
```

Stage A landed helper (`MinkowskiDet.lean:38-70`, **0 sorry**):

```lean
theorem det_rpow_le_arith_mean_eigenvalues ... (hA : A.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ (1 / (Fintype.card n : ℝ)) * ∑ i, hA.1.eigenvalues i
```

Stage B 証明戦略 (congruence reduction, Cover-Thomas 17.9.1 の standard 行列版):

```
let S := A.sqrt⁻¹ * B * A.sqrt⁻¹            -- A := CFC.sqrt の inverse でサンドイッチ (A^(-1/2) B A^(-1/2))
1. A PosDef → 0 < det A、A.sqrt := CFC.sqrt A は PosSemidef、det (A.sqrt) = sqrt (det A)   -- 軸 2
2. A^(-1/2) := (CFC.sqrt A)⁻¹ も PosDef (PosDef.inv + sqrt の PosDef化)、congruence 保存       -- 軸 1,3
3. S := A^(-1/2) B A^(-1/2) PosDef (B PosDef + 両側 conjugate)                                  -- 軸 3
4. A + B = A.sqrt * (I + S) * A.sqrt                                                            -- algebra
5. det(A+B) = det(A.sqrt)^2 * det(I + S) = det A * det(I + S)                                   -- 軸 4 (det_mul)
6. det(I+S) = ∏ (1 + μᵢ)  (μᵢ = eigenvalues S > 0)                                              -- 軸 5
7. det(A+B)^(1/n) = (det A)^(1/n) * (∏(1+μᵢ))^(1/n)  ≥ (det A)^(1/n) * (1 + (∏μᵢ)^(1/n))        -- AM-GM 各因子 1+μᵢ
   = (det A)^(1/n) + (det A · det S)^(1/n) = (det A)^(1/n) + (det B)^(1/n)                       -- det B = det A · det S
```

> 代替 (trace-based, eigenvalue-shift を避ける): Stage A helper を 2 回 (`det A^(1/n) ≤ (1/n)tr A`, `det B^(1/n) ≤ (1/n)tr B` の **superadditive** 逆向き版が必要) — ただし Stage A helper は **subadditive 方向** なので逆向きが要り Minkowski には direct 接続できない。congruence reduction が本命。

---

## API 在庫テーブル

### 軸 1: `Matrix.PosDef.inv` / `Matrix.PosSemidef.inv` (逆行列の PosDef 保存)

**Ranking: POSITIVE.** `A.PosDef → A⁻¹.PosDef` は存在。loogle `Matrix.PosDef.inv` → `Found one declaration`.

| 概念 | Mathlib API | file:line | 状態 | Stage B での扱い |
|---|---|---|---|---|
| PosDef 逆 | `Matrix.PosDef.inv` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:498` | ✅ POSITIVE | `A^(-1/2)` の PosDef 化に使用 |
| PosSemidef 逆 | `Matrix.PosSemidef.inv` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:334` | ✅ POSITIVE | backup |
| PosDef 逆 ⇔ | `Matrix.posDef_inv_iff` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:505` | ✅ POSITIVE | `A⁻¹.PosDef ↔ A.PosDef` |
| PosDef ⇒ PosSemidef | `Matrix.PosDef.posSemidef` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean` (PosDef structure 直後の accessor) | ✅ POSITIVE | sqrt / Order 補題に PosSemidef 形を渡す bridge |

`Matrix.PosDef.inv` 完全 signature (verbatim, line 498):

```lean
protected theorem inv [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : M⁻¹.PosDef := by
```

- **type-class 前提 (section header, file:line PosDef.lean の `section Field` 内、verbatim)**: `variable {𝕜 : Type*} [RCLike 𝕜]` 系 + `[Fintype n]` (file variable) + 明示 `[DecidableEq n]`。具体的には `K` が the field; `Matrix n n K` で `RCLike K` 相当 (`ℝ` は instance あり)
- **引数**: `[DecidableEq n]` (instance), `{M : Matrix n n K}` (implicit), `(hM : M.PosDef)` (explicit)
- **結論 (verbatim)**: `M⁻¹.PosDef`

`Matrix.PosSemidef.inv` 完全 signature (verbatim, line 334):

```lean
protected lemma inv [DecidableEq n] {M : Matrix n n R'} (hM : M.PosSemidef) : M⁻¹.PosSemidef := by
```

- **type-class 前提**: `R'` は `[Field R'] [StarRing R'] [PartialOrder R'] [StarOrderedRing R']` 系 (`section` の variable)。`[Fintype n]` file-level + 明示 `[DecidableEq n]`
- **結論 (verbatim)**: `M⁻¹.PosSemidef`

`Matrix.posDef_inv_iff` (verbatim, line 505):

```lean
@[simp]
theorem _root_.Matrix.posDef_inv_iff [DecidableEq n] {M : Matrix n n K} :
    M⁻¹.PosDef ↔ M.PosDef :=
```

---

### 軸 2: 行列平方根 (`CFC.sqrt` 経由、`Matrix.PosSemidef.sqrt` は不在)

**Ranking: POSITIVE.** ⚠️ **Matrix 固有の `Matrix.PosSemidef.sqrt` / `Matrix.IsHermitian.sqrt` は識別子として存在しない** (loogle `unknown identifier`)。現行ルートは generic `CFC.sqrt` (C⋆-algebra functional calculus) を `Matrix n n 𝕜` に適用。Matrix 専用の det / inv-sqrt 補題は `Mathlib/Analysis/Matrix/Order.lean` の `Matrix.PosSemidef` namespace に live で存在。

**Deprecation 状況 (最重要、Stream C 観察への verdict)**:

- `Mathlib/Analysis/Matrix/Order.lean:124` に **literally `section sqrtDeprecated`** が存在 → Stream C の「deprecated section 寄り」観察は section 名としては正しい。
- **しかしその中の `Matrix.PosSemidef.inv_sqrt` (line 130) には `@[deprecated]` attribute が付いていない**。`rg deprecated Order.lean` の唯一の `@[deprecated]` ヒットは line 340/342 の `PosDef.matrixNormedAddCommGroup` / `PosDef.matrixInnerProductSpace` (norm / inner-product、**sqrt とは無関係**)。
- `Matrix.PosSemidef.det_sqrt` (line 152) は `section sqrtDeprecated` の **外** (section は line 134 で閉じる)、`@[deprecated]` なし、live。
- ファイル冒頭 docstring (line 20): *"This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`."* → 設計意図は「Matrix 固有 sqrt を廃して `CFC.sqrt` に一本化」。
- **結論: matrix sqrt は deprecated でも不在でもない。** 旧 `Matrix.PosSemidef.sqrt` def が `CFC.sqrt` に置換され、その移行の名残として section 名に "Deprecated" が残っているだけ。**現行ルート `CFC.sqrt A` (A : Matrix n n 𝕜) は full API + Matrix 固有 `det_sqrt` / `inv_sqrt` も live。**

| 概念 | Mathlib API | file:line | 状態 | Stage B での扱い |
|---|---|---|---|---|
| 行列 sqrt (generic) | `CFC.sqrt` | `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:236` | ✅ POSITIVE | `A.sqrt := CFC.sqrt A` (`Matrix n n ℝ` に適用) |
| `sqrt a * sqrt a = a` | `CFC.sqrt_mul_sqrt_self` | `…/Rpow/Basic.lean:265` | ✅ POSITIVE | `A.sqrt * A.sqrt = A` |
| `(sqrt a)^2 = a` | `CFC.sq_sqrt` | `…/Rpow/Basic.lean:648` | ✅ POSITIVE | step 4 の `A = A.sqrt^2` |
| `sqrt (a*a) = a` | `CFC.sqrt_mul_self` | `…/Rpow/Basic.lean:276` | ✅ POSITIVE | backup |
| `0 ≤ sqrt a` | `CFC.sqrt_nonneg` | `…/Rpow/Basic.lean:239` | ✅ POSITIVE | `(CFC.sqrt A).PosSemidef` への bridge (下記注意) |
| `det (sqrt A) = sqrt (det A)` | `Matrix.PosSemidef.det_sqrt` | `Mathlib/Analysis/Matrix/Order.lean:152` | ✅ POSITIVE | step 5 の `det(A.sqrt)^2 = det A` |
| `(sqrt A)⁻¹ = sqrt A⁻¹` | `Matrix.PosSemidef.inv_sqrt` | `Mathlib/Analysis/Matrix/Order.lean:130` | ✅ POSITIVE | `A^(-1/2)` の整理 |
| 0 ≤ M ⇔ PosSemidef | `Matrix.nonneg_iff_posSemidef` | `Mathlib/Analysis/Matrix/Order.lean:59` | ✅ POSITIVE | `CFC.sqrt_nonneg → (CFC.sqrt A).PosSemidef` の bridge (scoped `MatrixOrder`) |

`CFC.sqrt` 完全 signature (verbatim, Rpow/Basic.lean:236):

```lean
noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a
```

- **type-class 前提 (section `NonUnital` の variable, line 81, verbatim)**: `variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]`。`sqrt_mul_sqrt_self` 等の equation lemma は加えて `[IsSemitopologicalRing A] [T2Space A]` (line 255) + `0 ≤ a` 仮説 (`cfc_tac` autoparam)。Matrix 適用時は `Matrix n n 𝕜` の C⋆-algebra instance (`MatrixOrder` scoped) が要る
- ⚠️ **`CFC.sqrt` は `A` 上の generic 元を返す**。`(CFC.sqrt A).PosSemidef` (Matrix 述語) を得るには `CFC.sqrt_nonneg A : 0 ≤ CFC.sqrt A` + `Matrix.nonneg_iff_posSemidef.mp` を経由する 1-2 行 plumbing が要る (直接の `(CFC.sqrt A).PosSemidef` lemma は **不在** — loogle `Matrix.PosSemidef (CFC.sqrt _)` → 0 match)

`CFC.sqrt_mul_sqrt_self` (verbatim, Rpow/Basic.lean:265):

```lean
lemma sqrt_mul_sqrt_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
```
- **結論 (verbatim)**: `sqrt a * sqrt a = a`
- **autoparam**: `(ha : 0 ≤ a := by cfc_tac)` ⚠️ — Matrix では `cfc_tac` が `0 ≤ A` を自動で解けない可能性、明示 `(ha := hA.posSemidef.nonneg)` が要ることがある

`CFC.sq_sqrt` (verbatim, Rpow/Basic.lean:648):

```lean
lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
```
- **結論 (verbatim)**: `(sqrt a) ^ 2 = a`

`Matrix.PosSemidef.det_sqrt` (verbatim, Order.lean:152):

```lean
theorem det_sqrt [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (CFC.sqrt A).det = RCLike.sqrt A.det := by
```
- **type-class 前提 (file variable line 38 + 90/120)**: `variable {𝕜 n : Type*} [RCLike 𝕜]` + `[Fintype n]` + 明示 `[DecidableEq n]`。`open scoped MatrixOrder` 前提 (line 118)
- **引数**: `[DecidableEq n]` (instance), `{A : Matrix n n 𝕜}` (implicit), `(hA : A.PosSemidef)` (explicit)
- **結論 (verbatim)**: `(CFC.sqrt A).det = RCLike.sqrt A.det` ⚠️ RHS は `RCLike.sqrt` (NOT `Real.sqrt`)、`𝕜 = ℝ` のとき `RCLike.sqrt_of_nonneg` で `Real.sqrt` に落とす

`Matrix.PosSemidef.inv_sqrt` (verbatim, Order.lean:130, **`section sqrtDeprecated` 内だが `@[deprecated]` なし**):

```lean
lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
```
- **type-class 前提 (section local, Order.lean:126, verbatim)**: `variable [DecidableEq n] {A : Matrix n n 𝕜} (hA : PosSemidef A)` + `include hA`
- **結論 (verbatim)**: `(CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹`
- ⚠️ section 名 `sqrtDeprecated` に惑わされない — 上記「Deprecation 状況」参照、live

---

### 軸 3: congruence の PosDef 保存 (`PᴴAP` / `PAPᴴ` PosDef)

**Ranking: POSITIVE.** `section conjugate` (`PosDef.lean:513`) に iff 形 + 片方向 lemma が完備。

| 概念 | Mathlib API | file:line | 状態 | Stage B での扱い |
|---|---|---|---|---|
| `PᴴAP` PosDef ⇔ (U 可逆) | `Matrix.IsUnit.posDef_star_left_conjugate_iff` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:522` | ✅ POSITIVE | `S = A^(-1/2) B A^(-1/2)` の PosDef 化 |
| `UAUᴴ` PosDef ⇔ (U 可逆) | `Matrix.IsUnit.posDef_star_right_conjugate_iff` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:536` | ✅ POSITIVE | 反対向き congruence |
| `BᴴAB` PosDef (片方向) | `Matrix.PosDef.conjTranspose_mul_mul_same` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:444` | ✅ POSITIVE | injective B から PosDef |
| `BABᴴ` PosDef (片方向) | `Matrix.PosDef.mul_mul_conjTranspose_same` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:451` | ✅ POSITIVE | injective vecMul から PosDef |
| `BᴴAB` PosSemidef (任意 B) | `Matrix.PosSemidef.conjTranspose_mul_mul_same` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:312` | ✅ POSITIVE | semidef 形 backup |
| `BABᴴ` PosSemidef (任意 B) | `Matrix.PosSemidef.mul_mul_conjTranspose_same` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:320` | ✅ POSITIVE | semidef 形 backup |

`Matrix.IsUnit.posDef_star_left_conjugate_iff` 完全 signature (verbatim, PosDef.lean:522):

```lean
theorem _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff (hU : IsUnit U) :
    PosDef (star U * x * U) ↔ x.PosDef := by
```
- **type-class 前提 (`section conjugate` variable line 514, verbatim)**: `variable [DecidableEq n] {x U : Matrix n n R}`、`R` は `[CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]` 系 (file-level、docstring "works on any ⋆-ring with a partial order") + `[Fintype n]`
- **引数**: `(hU : IsUnit U)` (explicit)。`{x U : Matrix n n R}` (implicit)
- **結論 (verbatim)**: `PosDef (star U * x * U) ↔ x.PosDef` ⚠️ `star U` (= `Uᴴ` for matrices via `star_eq_conjTranspose`)

`Matrix.IsUnit.posDef_star_right_conjugate_iff` (verbatim, PosDef.lean:536):

```lean
theorem _root_.Matrix.IsUnit.posDef_star_right_conjugate_iff (hU : IsUnit U) :
    PosDef (U * x * star U) ↔ x.PosDef := by
```
- **結論 (verbatim)**: `PosDef (U * x * star U) ↔ x.PosDef`

`Matrix.PosDef.conjTranspose_mul_mul_same` (verbatim, PosDef.lean:444):

```lean
lemma conjTranspose_mul_mul_same {A : Matrix n n R} {B : Matrix n m R} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) :
    (Bᴴ * A * B).PosDef := by
```
- **type-class 前提 (PosDef section, file variable + `omit`/`variable` local)**: `[Fintype n]` `[Finite m]` (line 311 の `omit [Fintype m] in variable [Finite m] in` パターンが先行宣言) + `R` の ⋆-ring 順序系
- **引数**: `{A : Matrix n n R}` `{B : Matrix n m R}` (implicit), `(hA : A.PosDef)`, `(hB : Function.Injective B.mulVec)` (explicit)
- **結論 (verbatim)**: `(Bᴴ * A * B).PosDef` ⚠️ injectivity `Function.Injective B.mulVec` が要る — 可逆 B なら `mulVec_injective_of_isUnit hU` (PosDef.lean:524 で実使用) から供給

`Matrix.PosDef.mul_mul_conjTranspose_same` (verbatim, PosDef.lean:451):

```lean
lemma mul_mul_conjTranspose_same {A : Matrix n n R} {B : Matrix m n R} (hA : A.PosDef)
    (hB : Function.Injective B.vecMul) :
    (B * A * Bᴴ).PosDef := by
```
- **結論 (verbatim)**: `(B * A * Bᴴ).PosDef`

`Matrix.PosSemidef.conjTranspose_mul_mul_same` (verbatim, PosDef.lean:312):

```lean
lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
```
- **結論 (verbatim)**: `PosSemidef (Bᴴ * A * B)` ⚠️ semidef 版は injectivity 不要 (任意 B)

---

### 軸 4: congruence の det (`det(PAQ) = det P det A det Q`, `det A⁻¹`, `det sqrt`)

**Ranking: PARTIAL.** `det_mul` は完璧、`det_sqrt` も既存 (軸 2)。唯一の引っかかり: `Matrix.det_nonsing_inv` が **`Ring.inverse` (`⁻¹ʳ`)** で書かれており field 上の `(det A)⁻¹` への変換に 1-2 行 adapter が要る (`det A ≠ 0` 既知なので容易)。

| 概念 | Mathlib API | file:line | 状態 | Stage B での扱い |
|---|---|---|---|---|
| `det(M*N) = det M * det N` | `Matrix.det_mul` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:137` | ✅ POSITIVE | step 5 `det(A+B)` 分解 |
| `det M⁻¹ = (det M)⁻¹ʳ` | `Matrix.det_nonsing_inv` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:412` | ⚠️ PARTIAL (`⁻¹ʳ` 形) | `A^(-1/2)` の det 整理 |
| `det A⁻¹ * det A = 1` | `Matrix.det_nonsing_inv_mul_det` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:408` | ✅ POSITIVE | field inverse への adapter として直接的 |
| `det(sqrt A) = sqrt(det A)` | `Matrix.PosSemidef.det_sqrt` | `Mathlib/Analysis/Matrix/Order.lean:152` | ✅ POSITIVE | step 5 (軸 2 再掲) |
| `(a*b)^p = a^p * b^p` (rpow) | `Real.mul_rpow` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (loogle: `Found one declaration`) | ✅ POSITIVE | step 7 `(det A · det(I+S))^(1/n)` 分解 |

`Matrix.det_mul` 完全 signature (verbatim, Determinant/Basic.lean:137):

```lean
@[simp]
theorem det_mul (M N : Matrix n n R) : det (M * N) = det M * det N :=
```
- **type-class 前提 (file variable line 49-50, verbatim)**: `variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]` + `variable {R : Type v} [CommRing R]`
- **引数**: `(M N : Matrix n n R)` (両方 explicit)
- **結論 (verbatim)**: `det (M * N) = det M * det N`

`Matrix.det_nonsing_inv` 完全 signature (verbatim, NonsingularInverse.lean:412):

```lean
@[simp]
theorem det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ := by
```
- **結論 (verbatim)**: `A⁻¹.det = A.det⁻¹ʳ` ⚠️ `⁻¹ʳ` = `Ring.inverse`。`det A ≠ 0` (= `IsUnit (det A)`、PosDef なら `hA.det_pos.ne'`) のとき `Ring.inverse_eq_inv` で field `(det A)⁻¹` に落ちる
- **adapter**: `Matrix.det_nonsing_inv_mul_det (h : IsUnit A.det) : A⁻¹.det * A.det = 1` (line 408) を使えば `⁻¹ʳ` を経由せず field 計算可能

---

### 軸 5: `I + S` 簡約経路 (eigenvalue `1 + μᵢ` → `det_eq_prod_eigenvalues`)

**Ranking: PARTIAL.** `det = ∏ eigenvalues` (`det_eq_prod_eigenvalues`、親 inventory 軸 1 で確認済) と `trace = ∑ eigenvalues` は既存だが、**`eigenvalues (1 + S) = fun i => 1 + eigenvalues S i` の直接 lemma が Mathlib 不在**。`det(I+S) = ∏(1+μᵢ)` を組むには (a) `1 + S` が PosDef ⇒ Hermitian ⇒ `det_eq_prod_eigenvalues` を適用 + (b) `1 + S` の固有値が `1 + (S の固有値)` であることを spectral mapping で示す ~10-20 行の bridge が要る。または (b') AM-GM を `det(I+S)` に直接適用せず、`S` の固有値 μᵢ に対して `(∏(1+μᵢ))^(1/n) ≥ 1 + (∏μᵢ)^(1/n)` を AM-GM 系で組む。

| 概念 | Mathlib API | file:line | 状態 | Stage B での扱い |
|---|---|---|---|---|
| `det A = ∏ eigenvalues` | `Matrix.IsHermitian.det_eq_prod_eigenvalues` | `Mathlib/Analysis/Matrix/Spectrum.lean:192` | ✅ POSITIVE | `det(I+S)` を固有値積に |
| `trace A = ∑ eigenvalues` | `Matrix.IsHermitian.trace_eq_sum_eigenvalues` | `Mathlib/Analysis/Matrix/Spectrum.lean:240` | ✅ POSITIVE | trace-based 代替経路用 |
| spectral theorem | `Matrix.IsHermitian.spectral_theorem` | `Mathlib/Analysis/Matrix/Spectrum.lean:144` | ✅ POSITIVE | eigenvalue shift の根拠 |
| `eigenvalues (1+S) = 1 + eigenvalues S` | — | — | ❌ NEGATIVE | **自作 bridge ~10-20 行 (spectral mapping)** |
| `det(1+S)` 一般式 | `det_one_add_*` 系 (Schur/Charpoly) | `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`, `.../Charpoly/Coeff.lean` | ⚠️ 特殊形のみ | 一般 `det(1+S)` には direct 不適 (Schur は `1 + UV` 形) |

`Matrix.IsHermitian.trace_eq_sum_eigenvalues` 完全 signature (verbatim, Spectrum.lean:240):

```lean
theorem trace_eq_sum_eigenvalues [DecidableEq n] (hA : A.IsHermitian) :
    A.trace = ∑ i, (hA.eigenvalues i : 𝕜) := by
```
- **type-class 前提 (file variable, Spectrum.lean)**: `[RCLike 𝕜] [Fintype n]` + 明示 `[DecidableEq n]`、変数 `(hA : A.IsHermitian)`
- **結論 (verbatim)**: `A.trace = ∑ i, (hA.eigenvalues i : 𝕜)`

`Matrix.IsHermitian.det_eq_prod_eigenvalues` (親 inventory line 213 で取得済、verbatim):

```lean
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
```
- **結論 (verbatim)**: `det A = ∏ i, (hA.eigenvalues i : 𝕜)`

---

## 主要前提条件ボックス (事故の起きやすい lemma の前提逐語)

### `CFC.sqrt` / `CFC.sqrt_mul_sqrt_self` / `CFC.sq_sqrt` (軸 2)

- `[PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]` (def の section), equation lemma は加えて `[IsSemitopologicalRing A] [T2Space A]`
- ⚠️ **`(ha : 0 ≤ a := by cfc_tac)` autoparam**: `A = Matrix n n ℝ` では `cfc_tac` が `0 ≤ A` を自動解決できないことが多い。明示 `(ha := hA.posSemidef.nonneg)` 渡しを想定
- ⚠️ Matrix を C⋆-algebra として扱うには `open scoped MatrixOrder` (scoped instance、`Order.lean:118`) が必須。これを忘れると `0 ≤ A` も `CFC.sqrt` も型が合わない
- ⚠️ **`CFC.sqrt A` の戻り値は generic 元** → `.PosSemidef` / `.det` 述語を得るのに `CFC.sqrt_nonneg` + `Matrix.nonneg_iff_posSemidef` の bridge が要る (直接 lemma 不在)

### `Matrix.PosSemidef.det_sqrt` (軸 2)

- `[RCLike 𝕜] [Fintype n] [DecidableEq n]`、`open scoped MatrixOrder`
- ⚠️ 結論 RHS は `RCLike.sqrt A.det` (NOT `Real.sqrt`)。`𝕜 = ℝ` でも自動で `Real.sqrt` にならない — `RCLike.sqrt_of_nonneg hA.det_nonneg` (det_sqrt 内部で使用、line 154) で変換

### `Matrix.IsUnit.posDef_star_left_conjugate_iff` (軸 3)

- `[DecidableEq n] [Fintype n]`、`R` は `[CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]` 系 (`ℝ` 全 instance あり)
- ⚠️ 結論は `star U * x * U` (`star U` = `Uᴴ`)。`A^(-1/2) B A^(-1/2)` を当てはめるとき `U = A^(-1/2)` は **Hermitian** なので `star U = U` (`hU.isHermitian` で `star U = U`) → 両 conjugate iff が片方で済む。明示の `star_eq_conjTranspose` rewrite 想定

### `Matrix.PosDef.conjTranspose_mul_mul_same` (軸 3)

- `(hB : Function.Injective B.mulVec)` ⚠️ — **injectivity 仮説**。`A^(-1/2)` が可逆 (PosDef → isUnit) なら `Matrix.mulVec_injective_of_isUnit hU` で供給。iff 版 (`posDef_star_left_conjugate_iff`) を使えば injectivity を直接書かず `IsUnit` だけで済む (より楽)

### `Matrix.det_nonsing_inv` (軸 4)

- ⚠️ 結論 `A⁻¹.det = A.det⁻¹ʳ` の `⁻¹ʳ` は `Ring.inverse`、field `⁻¹` ではない。`IsUnit (det A)` (PosDef なら `(hA.det_pos).ne'` から) のとき `Ring.inverse_eq_inv'` 等で field inverse に。または `det_nonsing_inv_mul_det` で `⁻¹ʳ` を経由せず計算

### eigenvalue shift (軸 5、NEGATIVE)

- ⚠️ **`eigenvalues (1 + S) = 1 + eigenvalues S` は Mathlib 不在**。`(1+S).IsHermitian` (`PosDef.add` 経由) + spectral mapping で自作。または `det(I+S)` を `∏(1+μᵢ)` に直さず、`S` の固有値で AM-GM を直接組む経路を選ぶ

---

## 自作が必要な要素 (優先度順、Stage B 内訳)

### 優先度 1: `(CFC.sqrt A).PosSemidef` / `.PosDef` bridge (~3-5 行)

- **内容**: `CFC.sqrt_nonneg A : 0 ≤ CFC.sqrt A` + `Matrix.nonneg_iff_posSemidef.mp` → `(CFC.sqrt A).PosSemidef`。さらに A PosDef のとき `(CFC.sqrt A)` も PosDef (det ≠ 0 経由 `PosSemidef.posDef_iff_det_ne_zero`、`Order.lean:199`)
- **工数感**: helper lemma 1 本 ~5 行
- **落とし穴**: `open scoped MatrixOrder` を忘れると `0 ≤ M` の型が合わない。直接の `(CFC.sqrt A).PosSemidef` lemma が不在なのが唯一の摩擦

### 優先度 2: eigenvalue-shift bridge `det(I + S) = ∏(1 + eigenvalues S i)` (~10-20 行)

- **内容**: `(1 + S).IsHermitian` から `det_eq_prod_eigenvalues` 適用 + `eigenvalues (1+S) i = 1 + eigenvalues S i` の spectral mapping。または `S` の固有値で AM-GM `(∏(1+μᵢ))^(1/n) ≥ 1 + (∏μᵢ)^(1/n)` を直接
- **工数感**: ~10-20 行 (spectral mapping が重め)。最も技術的な摩擦点
- **落とし穴**: `1 = (1 : Matrix n n ℝ)` の固有値が全部 1 であることの確認、`diagonal` 形での eigenvalue 計算

### 優先度 3: 全体 congruence reduction + AM-GM 組み立て (~50-80 行)

- **内容**: `A + B = A.sqrt * (I + S) * A.sqrt` の algebra (`CFC.sq_sqrt` / `sqrt_mul_sqrt_self`) → `det_mul` で `det A · det(I+S)` → 各因子 `1 + μᵢ` への AM-GM (`Real.geom_mean_le_arith_mean_weighted`、親 inventory 軸 3) → `det B = det A · det S` で締め
- **工数感**: ~50-80 行
- **落とし穴**: rpow の `(det A · det(I+S))^(1/n) = (det A)^(1/n) · (det(I+S))^(1/n)` 分解に `Real.mul_rpow` (両 nonneg 要)、`det A > 0` / `det(I+S) > 0` の供給

**Stage B 総工数感**: ~70-110 行 (優先度 1+2+3)。Stage A helper (`det_rpow_le_arith_mean_eigenvalues`、0 sorry) が AM-GM 部分の prototype として再利用可能。

---

## Mathlib 壁の列挙 (`@residual(wall:...)` 維持判定)

### `wall:minkowski-det-posdef` — 維持が正しい (主定理形は Mathlib 0 件)

- **対象**: `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` for PosDef `A B`
- **loogle 確認結果**:
  - `loogle "Real.rpow, _ + _, _ ≤ _, Matrix.det"` → **`Found 0 declarations mentioning Real.rpow, LE.le, HAdd.hAdd, and Matrix.det`**
  - `loogle "Matrix.det, Matrix.det, Matrix.det"` → 458 件の `Matrix.det` 系を列挙、**Minkowski 形 (3-det superadditive rpow) は 0 件**
- **判定**: 主定理は Mathlib に literally 不在。`@residual(wall:minkowski-det-posdef)` の wall classification は **正しい**。ただし **「big (選択) wall」ではなく「組める wall」**: 全 5 軸の構成材料 (PosDef.inv / CFC.sqrt / congruence iff / det_mul / det_eq_prod_eigenvalues) は揃っているので、~70-110 行で genuine 化が可能。`docs/audit/audit-tags.md`「Mathlib 壁の 4 分類」上は **hard (textbook-effort) であって blocked ではない**
- **shared sorry 補題への集約**: ✅ 既に `Common2026/Shannon/MinkowskiDet.lean` の単一 `minkowskiDeterminantInequality` に集約済 (新規散在なし)。Stage B で genuine 化すれば `@residual` 解消 → `proof done`

### 真に Mathlib 不在の sub-component (Stage B 内部で自作、wall ではなく plumbing)

- `(CFC.sqrt A).PosSemidef` の直接 lemma (loogle `Matrix.PosSemidef (CFC.sqrt _)` → 0 match) — bridge ~5 行で closure 可能、wall ではない
- `eigenvalues (1 + S) = 1 + eigenvalues S` (loogle で直接 lemma 不在) — spectral mapping ~10-20 行で closure 可能、wall ではない

**いずれも独立 wall に昇格させる必要なし** (Stage B 本体の sorry に内包)。

---

## 撤退ラインへの距離

親 plan の Stage B 撤退ライン (`chapter-17-minkowski-inventory.md` の Phase 3 推奨 route §「Stage B (挑戦的)」、L-CH17-2-β 部分発火状態) に照合:

- **Stage B 撤退口**: 「textbook proof attempt 失敗時は sorry を維持して終了」(親 inventory line 677)
- **本 inventory による更新**: Stage B の 5 軸はすべて POSITIVE / PARTIAL で、NEGATIVE な sub-component (`(CFC.sqrt A).PosSemidef` 直接 lemma / eigenvalue shift) も plumbing で closure 可能と判明。**撤退ライン発動: NO** (genuine 化の道が全軸で open)
- **新規縮退案 (Stage B が session 内で完走できない場合)**: signature を現状 (`minkowskiDeterminantInequality := by sorry` + `@residual(wall:minkowski-det-posdef)`) のまま維持。これは既存撤退口そのもので、新規ライン不要。仮説束化 (`*Hypothesis` predicate に congruence reduction の核を bundle) は **禁止** — Stage B が詰まったら sorry を残すだけ
- **危険な発見**: Stage B 自体には撤退ライン発動リスクなし。ただし **`CFC.sqrt` の `cfc_tac` autoparam が Matrix で自動解決できず明示 `0 ≤ A` 供給が常時要る** + **`MatrixOrder` scoped instance を `open scoped` し忘れると全 sqrt 補題が型不一致** の 2 点が実装初手で詰まりやすい (撤退ラインではなく実装 friction)

---

## 着手 skeleton (Stage B helper を `MinkowskiDet.lean` に追加する出だし、~30 行)

> 既存 `MinkowskiDet.lean` の import (`Mathlib.LinearAlgebra.Matrix.PosDef` / `Mathlib.Analysis.Matrix.PosDef` / `Mathlib.Analysis.Matrix.Spectrum` / `Mathlib.Analysis.MeanInequalities` / `Mathlib.Analysis.SpecialFunctions.Pow.Real`) に加えて、Stage B では以下を追加 import:

```lean
-- 既存 import に追加 (CFC.sqrt + Matrix order/sqrt 補題用)
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace Common2026.Shannon

open scoped Matrix MatrixOrder   -- ⚠️ MatrixOrder scoped instance 必須 (CFC.sqrt / 0 ≤ M 用)
open Finset

/-- For PosDef `A`, the CFC square root `CFC.sqrt A` is again positive definite.
Bridges `CFC.sqrt_nonneg` + `Matrix.nonneg_iff_posSemidef` + det-nonzero. -/
theorem posDef_cfcSqrt {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  sorry  -- 優先度 1 bridge (~5 行)

/-- The congruence reduction core: `det (A + B) = det A * det (1 + S)` where
`S := (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹` is PosDef. -/
theorem det_add_eq_det_mul_det_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A + B).det = A.det * (1 + (CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).det := by
  sorry  -- 優先度 3 (det_mul + sq_sqrt + algebra)

-- 既存 `minkowskiDeterminantInequality := by sorry` (line 89) を上記 2 helper +
-- 優先度 2 eigenvalue-shift + Stage A `det_rpow_le_arith_mean_eigenvalues` で fill

end Common2026.Shannon
```

注意:
- `import Mathlib` 禁止、pinpoint import 2 件追加 (`Analysis.Matrix.Order` + `…Rpow.Basic`)
- `open scoped MatrixOrder` を namespace 内で必ず開く (CFC.sqrt / `0 ≤ M` の型)
- `posDef_cfcSqrt` の RHS `(CFC.sqrt A).PosDef` を欲しい形で先に作っておくと、`det_sqrt` / `inv_sqrt` / congruence iff へ渡すときの bridge が 1 本で済む (Mathlib-shape-driven)
- Stage B 完走できなければ各 helper の sorry に `@residual(wall:minkowski-det-posdef)` を継承付与、main 定理は現状維持

---

## 総合 verdict (Stage B feasibility)

### 5 軸 ranking 集計

| 軸 | 内容 | ranking | core 件数 |
|---|---|---|---|
| 1. `Matrix.PosDef.inv` | A⁻¹ PosDef 保存 | **POSITIVE** | 4 (`PosDef.inv`, `PosSemidef.inv`, `posDef_inv_iff`, `PosDef.posSemidef`) |
| 2. 行列 sqrt (`CFC.sqrt`) | sqrt + det_sqrt + inv_sqrt | **POSITIVE** (`Matrix.*.sqrt` 名は不在、`CFC.sqrt` 経由) | 7 |
| 3. congruence PosDef 保存 | `PᴴAP` / `PAPᴴ` PosDef | **POSITIVE** | 6 |
| 4. congruence det | `det_mul` / `det⁻¹` / `det_sqrt` | **PARTIAL** (`det_nonsing_inv` が `⁻¹ʳ` 形、adapter 数行) | 5 |
| 5. `I + S` 簡約 | eigenvalue `1+μᵢ` → `det_eq_prod` | **PARTIAL** (eigenvalue shift lemma 不在、自作 ~10-20 行) | 3 + 自作 1 |

### matrix sqrt deprecation 状況 (Stream C 観察への最終 verdict)

**「deprecated section に寄っている」は section 名 (`section sqrtDeprecated`、`Order.lean:124`) としては literally 正しいが、ミスリーディング。** その section 内の `inv_sqrt` および section 外の `det_sqrt` に **`@[deprecated]` attribute は付いていない (live)**。`Order.lean` の `@[deprecated]` ヒットは norm/inner-product alias 2 件 (sqrt とは無関係) のみ。「Matrix 固有の旧 `sqrt` def を `CFC.sqrt` に一本化した」歴史的経緯の名残であり、**現行 `CFC.sqrt` ルートは full API。matrix sqrt は使える。**

### feasibility 判定

**Stage B genuine 証明は今 feasible。** 5 軸の構成材料はすべて Mathlib に揃っており、NEGATIVE な 2 点 (`(CFC.sqrt A).PosSemidef` 直接 lemma / eigenvalue shift) も独立 wall ではなく plumbing (~5 + ~10-20 行) で closure 可能。`wall:minkowski-det-posdef` は主定理形が Mathlib 0 件である事実 (verbatim 確認済) に基づき **維持が正しい** が、その分類は **blocked ではなく hard (textbook-effort)** — Stage B で sorry を genuine に置換する道は open。

### Stage B Phase 順序提案

1. **Phase B-1 (~5 行)**: `posDef_cfcSqrt : A.PosDef → (CFC.sqrt A).PosDef` helper (優先度 1 bridge)。`CFC.sqrt_nonneg` + `nonneg_iff_posSemidef` + det-nonzero。
2. **Phase B-2 (~50-80 行)**: `det_add_eq_det_mul_det_one_add : det(A+B) = det A · det(I + S)` congruence reduction (優先度 3、`det_mul` / `sq_sqrt` / `det_sqrt` / congruence iff)。`S := (CFC.sqrt A)⁻¹ B (CFC.sqrt A)⁻¹` PosDef も同時に確立。
3. **Phase B-3 (~10-20 行)**: eigenvalue-shift `det(I+S) = ∏(1 + eigenvalues S i)` (優先度 2、spectral mapping) または `S` の固有値で AM-GM 直接。
4. **Phase B-4 (~10-20 行)**: 最終組み立て。`det(A+B)^(1/n) = (det A · det(I+S))^(1/n)` を `Real.mul_rpow` 分解 → 各因子 `1+μᵢ` に AM-GM (`Real.geom_mean_le_arith_mean_weighted`、Stage A helper 再利用) → `det B = det A · det S` で `(det A)^(1/n) + (det B)^(1/n)` に締め。`minkowskiDeterminantInequality` の sorry を fill。

各 Phase で詰まったら sorry + `@residual(wall:minkowski-det-posdef)` 継承で抜く (撤退口は既存形のまま、仮説束化禁止)。

---

> Stage B inventory 終了。次フェーズは `Common2026/Shannon/MinkowskiDet.lean` の `minkowskiDeterminantInequality` sorry を上記 Phase B-1〜B-4 で genuine 化する `lean-implementer` dispatch。
