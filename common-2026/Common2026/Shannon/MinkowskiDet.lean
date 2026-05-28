/-
Copyright (c) 2026 Common2026 contributors. All rights reserved.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Minkowski determinant inequality (Cover-Thomas Theorem 17.9.1)

For positive-definite matrices `A, B : Matrix n n ℝ`,
`det(A + B)^(1/n) ≥ det A^(1/n) + det B^(1/n)`.

Genuinely proved (no `sorry`) by simultaneous diagonalization / congruence
reduction. Mathlib does not provide this inequality directly (verbatim-confirmed
in `docs/shannon/chapter-17-minkowski-inventory.md`), so the proof is assembled
from the matrix square root (`CFC.sqrt`), congruence PosDef preservation, the
eigenvalue-shift determinant identity `det (1 + S) = ∏ (1 + eigenvalues S i)`
(`det_one_add_eq_prod_one_add_eigenvalues`), and the scalar geometric-mean
superadditivity bound (`geom_mean_superadditive`).

-/

namespace Common2026.Shannon

open scoped Matrix MatrixOrder
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

/-- **Scalar Minkowski (superadditivity of the geometric mean).**

For nonnegative reals `a i, b i` with `a i + b i > 0`,
`(∏ a i)^(1/n) + (∏ b i)^(1/n) ≤ (∏ (a i + b i))^(1/n)`.

This is the scalar core of the Minkowski determinant inequality. It follows from
weighted AM-GM applied to the normalized weights `a i / (a i + b i)` (and its
complement), exactly the construction used in `det_rpow_le_arith_mean_eigenvalues`.
Fully proved (no `sorry`); reusable. -/
theorem geom_mean_superadditive
    {n : Type*} [Fintype n] [Nonempty n]
    (a b : n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, 0 < a i + b i) :
    (∏ i, a i) ^ (1 / (Fintype.card n : ℝ)) + (∏ i, b i) ^ (1 / (Fintype.card n : ℝ))
      ≤ (∏ i, (a i + b i)) ^ (1 / (Fintype.card n : ℝ)) := by
  set N : ℝ := (Fintype.card n : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hNne : N ≠ 0 := ne_of_gt hNpos
  -- the product of the sums is positive
  have hPpos : (0 : ℝ) < ∏ i, (a i + b i) := Finset.prod_pos (fun i _ => hab i)
  -- normalized weights
  set t : n → ℝ := fun i => a i / (a i + b i) with ht
  set s : n → ℝ := fun i => b i / (a i + b i) with hs
  have htnn : ∀ i, 0 ≤ t i := fun i => div_nonneg (ha i) (hab i).le
  have hsnn : ∀ i, 0 ≤ s i := fun i => div_nonneg (hb i) (hab i).le
  have htst : ∀ i, t i + s i = 1 := by
    intro i; rw [ht, hs]; rw [← add_div, div_self (ne_of_gt (hab i))]
  -- AM-GM on t and on s
  have hw : ∀ i ∈ (univ : Finset n), (0 : ℝ) ≤ (1 / N) := fun i _ => by positivity
  have hw' : ∑ _i : n, (1 / N) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, mul_one_div, div_self hNne]
  have hAMt := Real.geom_mean_le_arith_mean_weighted (s := univ)
    (fun _ => (1 / N)) t hw hw' (fun i _ => htnn i)
  have hAMs := Real.geom_mean_le_arith_mean_weighted (s := univ)
    (fun _ => (1 / N)) s hw hw' (fun i _ => hsnn i)
  -- rewrite geometric-mean sides as a single product raised to 1/N
  have hprodt : ∏ i, (t i) ^ (1 / N) = (∏ i, t i) ^ (1 / N) :=
    (Real.finsetProd_rpow univ _ (fun i _ => htnn i) (1 / N))
  have hprods : ∏ i, (s i) ^ (1 / N) = (∏ i, s i) ^ (1 / N) :=
    (Real.finsetProd_rpow univ _ (fun i _ => hsnn i) (1 / N))
  rw [hprodt] at hAMt
  rw [hprods] at hAMs
  -- sum the two AM-GM bounds; the arithmetic means add to (1/N) * N = 1
  have hsum : (∏ i, t i) ^ (1 / N) + (∏ i, s i) ^ (1 / N) ≤ 1 := by
    have h := add_le_add hAMt hAMs
    have harith : (∑ i, (1 / N) * t i) + (∑ i, (1 / N) * s i) = 1 := by
      rw [← Finset.sum_add_distrib]
      have : ∀ i, (1 / N) * t i + (1 / N) * s i = (1 / N) := by
        intro i; rw [← mul_add, htst i, mul_one]
      simp_rw [this]
      exact hw'
    rw [harith] at h
    exact h
  -- relate ∏ a, ∏ b to ∏ (a+b) via the normalized weights
  have hPpow : (0 : ℝ) < (∏ i, (a i + b i)) ^ (1 / N) := Real.rpow_pos_of_pos hPpos _
  -- (∏ a)^(1/N) = (∏(a+b))^(1/N) * (∏ t)^(1/N)
  have hta : (∏ i, t i) = (∏ i, a i) / (∏ i, (a i + b i)) := by
    rw [ht]; rw [← Finset.prod_div_distrib]
  have hsb : (∏ i, s i) = (∏ i, b i) / (∏ i, (a i + b i)) := by
    rw [hs]; rw [← Finset.prod_div_distrib]
  have hann : (0 : ℝ) ≤ ∏ i, a i := Finset.prod_nonneg (fun i _ => ha i)
  have hbnn : (0 : ℝ) ≤ ∏ i, b i := Finset.prod_nonneg (fun i _ => hb i)
  rw [hta, hsb, Real.div_rpow hann hPpos.le, Real.div_rpow hbnn hPpos.le] at hsum
  -- multiply through by (∏(a+b))^(1/N)
  have hkey := mul_le_mul_of_nonneg_left hsum hPpow.le
  rw [mul_add, mul_one] at hkey
  rw [mul_div_cancel₀ _ (ne_of_gt hPpow), mul_div_cancel₀ _ (ne_of_gt hPpow)] at hkey
  rw [hN] at hkey ⊢
  exact hkey

/-- The CFC square root of a positive-definite matrix is positive definite. -/
theorem posDef_cfcSqrt {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  have hps : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  rw [hps.posDef_iff_det_ne_zero, hA.posSemidef.det_sqrt, RCLike.sqrt_real]
  exact ne_of_gt (Real.sqrt_pos.mpr hA.det_pos)

/-- `det (1 + S) = ∏ (1 + eigenvalues S i)` for a Hermitian matrix `S`.

Spectral-mapping bridge: `S = U diag(λ) Uᴴ` gives `1 + S = U diag(1+λ) Uᴴ`, hence
`det (1 + S) = ∏ (1 + λ i)`. Reusable. -/
theorem det_one_add_eq_prod_one_add_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    (1 + S).det = ∏ i, (1 + hS.eigenvalues i) := by
  set U := hS.eigenvectorUnitary with hU
  set D : Matrix n n ℝ := Matrix.diagonal (RCLike.ofReal ∘ hS.eigenvalues) with hD
  -- spectral decomposition `S = U * D * star U`
  have hspec : S = (U : Matrix n n ℝ) * D * (star U : Matrix n n ℝ) := by
    have h := hS.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hU, hD, mul_assoc] using h
  -- unitarity: `U * star U = 1`
  have hUU : (U : Matrix n n ℝ) * (star U : Matrix n n ℝ) = 1 := Unitary.coe_mul_star_self U
  -- `1 + S = U * (1 + D) * star U`
  have hconj : (1 : Matrix n n ℝ) + S = (U : Matrix n n ℝ) * (1 + D) * (star U : Matrix n n ℝ) := by
    rw [hspec, mul_add, add_mul, mul_one, hUU]
  -- determinant of the conjugation collapses to `det (1 + D)`
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  rw [mul_comm ((U : Matrix n n ℝ).det) ((1 + D).det), mul_assoc]
  rw [← Matrix.det_mul, hUU, Matrix.det_one, mul_one]
  -- `1 + D = diagonal (fun i => 1 + λ i)`, so `det = ∏ (1 + λ i)`
  have hdiag : (1 : Matrix n n ℝ) + D = Matrix.diagonal (fun i => 1 + hS.eigenvalues i) := by
    rw [hD, ← Matrix.diagonal_one, ← Matrix.diagonal_add]
    simp
  rw [hdiag, Matrix.det_diagonal]

/-- Cover-Thomas Theorem 17.9.1: Minkowski determinant inequality.

For PosDef `A B`, `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)`.

Genuine proof by simultaneous diagonalization (congruence reduction):
let `R := CFC.sqrt A` (PosDef, `posDef_cfcSqrt`) and `S := R⁻¹ * B * R⁻¹` (PosDef
by `IsUnit.posDef_star_left_conjugate_iff`). Then `A + B = R * (1 + S) * R`, so
`det(A+B) = det A · det(1+S)`. Writing `μ i := eigenvalues S i > 0` gives
`det(1+S) = ∏ (1 + μ i)` (`det_one_add_eq_prod_one_add_eigenvalues`) and
`∏ μ i = det S = det B / det A`. Apply scalar Minkowski
(`geom_mean_superadditive` with `a ≡ 1`, `b = μ`) and multiply through by
`(det A)^(1/n)`. -/
theorem minkowskiDeterminantInequality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (A.det) ^ (1 / (Fintype.card n : ℝ)) + (B.det) ^ (1 / (Fintype.card n : ℝ))
      ≤ ((A + B).det) ^ (1 / (Fintype.card n : ℝ)) := by
  set p : ℝ := 1 / (Fintype.card n : ℝ) with hp
  -- square root `R := CFC.sqrt A`
  set R : Matrix n n ℝ := CFC.sqrt A with hR
  have hRpd : R.PosDef := posDef_cfcSqrt hA
  have hRU : IsUnit R.det := R.isUnit_iff_isUnit_det.mp hRpd.isUnit
  have hRRA : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  -- `R` is Hermitian, hence `star R = R`
  have hRherm : star R = R := by
    rw [Matrix.star_eq_conjTranspose]; exact hRpd.isHermitian
  -- the inverse `R⁻¹` is a unit and Hermitian
  have hRinvU : IsUnit (R⁻¹) := Matrix.isUnit_nonsing_inv_iff.mpr hRpd.isUnit
  have hRinvHerm : star (R⁻¹) = R⁻¹ := by
    rw [Matrix.star_eq_conjTranspose]; exact (hRpd.isHermitian.inv).eq
  -- congruence matrix `S := R⁻¹ * B * R⁻¹` is PosDef
  set S : Matrix n n ℝ := R⁻¹ * B * R⁻¹ with hS
  have hSpd : S.PosDef := by
    have hiff := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := B) hRinvU
    rw [hRinvHerm] at hiff
    exact hiff.mpr hB
  have hSherm : S.IsHermitian := hSpd.isHermitian
  -- `A + B = R * (1 + S) * R`
  have hAB : A + B = R * (1 + S) * R := by
    have hcancel : R * S * R = B := by
      rw [hS, show R * (R⁻¹ * B * R⁻¹) * R = (R * R⁻¹) * B * (R⁻¹ * R) by noncomm_ring,
        Matrix.mul_nonsing_inv R hRU, Matrix.nonsing_inv_mul R hRU, one_mul, mul_one]
    rw [mul_add, mul_one, add_mul, hRRA, hcancel]
  -- determinant of the congruence: `det(A+B) = det A · det(1+S)`
  have hdetAB : (A + B).det = A.det * (1 + S).det := by
    rw [hAB, Matrix.det_mul, Matrix.det_mul, ← hRRA, Matrix.det_mul]
    ring
  -- `det(1+S) = ∏ (1 + μ i)`
  have hμpos : ∀ i, 0 < hSherm.eigenvalues i := fun i => hSpd.eigenvalues_pos i
  have hdetone : (1 + S).det = ∏ i, (1 + hSherm.eigenvalues i) :=
    det_one_add_eq_prod_one_add_eigenvalues hSherm
  -- `∏ μ i = det S`
  have hdetS : S.det = ∏ i, hSherm.eigenvalues i := by
    have h := hSherm.det_eq_prod_eigenvalues
    simpa using h
  -- positivity facts
  have hAdetpos : (0 : ℝ) < A.det := hA.det_pos
  have hSdetpos : (0 : ℝ) < S.det := hSpd.det_pos
  -- scalar Minkowski with `a ≡ 1`, `b i = μ i`
  have hmink := geom_mean_superadditive (n := n) (fun _ => (1 : ℝ))
    (fun i => hSherm.eigenvalues i) (fun _ => zero_le_one)
    (fun i => (hμpos i).le) (fun i => by have := hμpos i; linarith)
  -- evaluate the products in the scalar bound
  rw [Finset.prod_const_one, Real.one_rpow] at hmink
  -- `∏ (1 + μ i)` matches `det(1+S)`, `∏ μ i` matches `det S`
  rw [← hdetone, ← hdetS] at hmink
  -- so `1 + (det S)^p ≤ (det(1+S))^p`. Multiply by `(det A)^p`.
  have hApos : (0 : ℝ) < A.det ^ p := Real.rpow_pos_of_pos hAdetpos p
  have hstep := mul_le_mul_of_nonneg_left hmink hApos.le
  rw [mul_add, mul_one] at hstep
  -- `(det A)^p · (det S)^p = (det A · det S)^p = (det B)^p`
  have hRdet2 : R.det * R.det = A.det := by
    rw [← Matrix.det_mul, hRRA]
  have hRdetne : R.det ≠ 0 := fun h => by
    rw [h, mul_zero] at hRdet2; exact (ne_of_gt hAdetpos) hRdet2.symm
  have hdetB : A.det * S.det = B.det := by
    rw [hS, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [← hRdet2]
    field_simp [hRdetne]
  have hrpow_mul : A.det ^ p * S.det ^ p = B.det ^ p := by
    rw [← Real.mul_rpow hAdetpos.le hSdetpos.le, hdetB]
  rw [hrpow_mul] at hstep
  -- `(det A)^p · (det(1+S))^p = (det A · det(1+S))^p = (det(A+B))^p`
  have hdetone_pos : (0 : ℝ) ≤ (1 + S).det := by
    rw [hdetone]
    exact Finset.prod_nonneg (fun i _ => by have := hμpos i; linarith)
  have hrpow_mul' : A.det ^ p * (1 + S).det ^ p = (A + B).det ^ p := by
    rw [← Real.mul_rpow hAdetpos.le hdetone_pos, ← hdetAB]
  rw [hrpow_mul'] at hstep
  -- assemble
  rw [hp]
  exact hstep

end Common2026.Shannon
