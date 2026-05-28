/-
Copyright (c) 2026 Common2026 contributors. All rights reserved.
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

⚠️ Mathlib does not provide this inequality directly (verbatim-confirmed in
`docs/shannon/chapter-17-minkowski-inventory.md`). Sorry-based shared wall
lemma per `docs/audit/audit-tags.md` 「共有 Mathlib 壁: shared sorry 補題パターン」.

-/

namespace Common2026.Shannon

open scoped Matrix
open Finset

/-- **AM-GM for the determinant of a positive-definite matrix.**

For a positive-definite `A : Matrix n n ℝ`, the `n`-th root of the determinant is
bounded above by the arithmetic mean of its eigenvalues:
`(det A)^(1/n) ≤ (1/n) ∑ᵢ λᵢ(A)`.

This is the genuine building block for the Minkowski determinant inequality
(Cover-Thomas 17.9.1): it is the `p = 1/n ≤ 1` direction of weighted AM-GM applied
to the eigenvalues, using `det A = ∏ᵢ λᵢ(A)`. Fully proved (no `sorry`). -/
theorem det_rpow_le_arith_mean_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ (1 / (Fintype.card n : ℝ)) * ∑ i, hA.1.eigenvalues i := by
  set N : ℝ := (Fintype.card n : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  have hNne : N ≠ 0 := ne_of_gt hNpos
  -- nonnegativity of eigenvalues
  have hz : ∀ i ∈ (univ : Finset n), 0 ≤ hA.1.eigenvalues i := by
    intro i _; exact (hA.eigenvalues_pos i).le
  -- equal weights `1/N` sum to 1
  have hw : ∀ i ∈ (univ : Finset n), (0 : ℝ) ≤ (1 / N) := by
    intro i _; positivity
  have hw' : ∑ _i : n, (1 / N) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, mul_one_div, div_self hNne]
  -- weighted AM-GM: ∏ λᵢ^(1/N) ≤ ∑ (1/N) λᵢ
  have hAMGM := Real.geom_mean_le_arith_mean_weighted (s := univ)
    (fun _ => (1 / N)) (fun i => hA.1.eigenvalues i) hw hw' hz
  -- rewrite the geometric-mean side: ∏ λᵢ^(1/N) = (∏ λᵢ)^(1/N) = (det A)^(1/N)
  have hdet : A.det = ∏ i, hA.1.eigenvalues i := by
    have h := hA.isHermitian.det_eq_prod_eigenvalues
    simpa using h
  have hprod_eq : ∏ i, (hA.1.eigenvalues i) ^ (1 / N)
      = (A.det) ^ (1 / N) := by
    rw [hdet, Real.finsetProd_rpow univ _ (fun i _ => (hz i (mem_univ i))) (1 / N)]
  -- rewrite the arithmetic-mean side: ∑ (1/N) λᵢ = (1/N) ∑ λᵢ
  have harith_eq : ∑ i, (1 / N) * hA.1.eigenvalues i
      = (1 / N) * ∑ i, hA.1.eigenvalues i := by
    rw [Finset.mul_sum]
  rw [hprod_eq, harith_eq] at hAMGM
  simpa [hN] using hAMGM

/-- Cover-Thomas Theorem 17.9.1: Minkowski determinant inequality.

For PosDef `A B`, `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)`.

⚠️ Mathlib does not provide this inequality directly. Sorry-based shared wall
lemma per audit-tags.md 「共有 Mathlib 壁: shared sorry 補題パターン」.

The genuine AM-GM half is already available as
`det_rpow_le_arith_mean_eigenvalues` (no `sorry`). The remaining wall is the
congruence/simultaneous-diagonalization step: reduce to `A' + B' = I` via the
matrix square root `(A+B)^(-1/2)` (Mathlib `CFC.sqrt`, deprecated section), then
combine the two AM-GM bounds through `tr(A') + tr(B') = tr I = n`. The matrix
sqrt + congruence-`det` + PosDef-preservation chain is the unverified part flagged
in `docs/shannon/chapter-17-minkowski-inventory.md` (自作が必要な要素 優先度 2).

@residual(wall:minkowski-det-posdef)
-/
theorem minkowskiDeterminantInequality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ)) + (B.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ ((A + B).det) ^ (1 / (Fintype.card n : ℝ)) := by
  sorry

end Common2026.Shannon
