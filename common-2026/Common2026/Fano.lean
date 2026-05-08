import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators

/-!
# Fano's inequality: a mathlib-current core formalization

Mathlib currently provides `Real.binEntropy` and `Real.qaryEntropy`.  The theorem
`Real.qaryEntropy` is exactly the textbook Fano right-hand side

  `binEntropy Pe + Pe * log (q - 1)`.

This file packages that identity as Fano's inequality, plus a monotone inverse
corollary on the standard range `Pe ≤ 1 - 1 / q`.

For finite joint probability mass functions we also define the usual finite
entropy quantities and provide a ready-to-use wrapper: once the information-
theoretic core estimate

  `H(X | Y) ≤ Real.qaryEntropy |X| Pe`

has been proved for your model, the theorem below rewrites it to the standard
Fano bound.
-/

open scoped BigOperators

namespace InformationTheory

noncomputable section

/-- The textbook right-hand side in Fano's inequality, measured in nats. -/
def fanoBoundRHS (q : ℕ) (Pe : ℝ) : ℝ :=
  Real.binEntropy Pe + Pe * Real.log ((((q : ℤ) - 1 : ℤ) : ℝ))

/-- `Real.qaryEntropy` is the Fano right-hand side. -/
theorem qaryEntropy_eq_fanoBoundRHS (q : ℕ) (Pe : ℝ) :
    Real.qaryEntropy q Pe = fanoBoundRHS q Pe := by
  simp [fanoBoundRHS, Real.qaryEntropy, add_comm]

/-- The reverse rewrite, sometimes more convenient for `rw`. -/
theorem fanoBoundRHS_eq_qaryEntropy (q : ℕ) (Pe : ℝ) :
    fanoBoundRHS q Pe = Real.qaryEntropy q Pe :=
  (qaryEntropy_eq_fanoBoundRHS q Pe).symm

/-- Fano's inequality, in its reusable `q`-ary form.

The hypothesis is the information-theoretic estimate
`Hxy ≤ qaryEntropy q Pe`; the conclusion is the usual textbook display
`Hxy ≤ h(Pe) + Pe log(q - 1)`.
-/
theorem fano_inequality_of_le_qaryEntropy
    {q : ℕ} {Pe Hxy : ℝ}
    (h : Hxy ≤ Real.qaryEntropy q Pe) :
    Hxy ≤ fanoBoundRHS q Pe := by
  simpa [qaryEntropy_eq_fanoBoundRHS] using h

/-- Fano's right-hand side for a finite alphabet. -/
def fanoBoundRHSOfAlphabet (X : Type*) [Fintype X] (Pe : ℝ) : ℝ :=
  fanoBoundRHS (Fintype.card X) Pe

/-- Fano's inequality for a finite alphabet, packaged with `Fintype.card`. -/
theorem fano_inequality_of_alphabet
    {X : Type*} [Fintype X] {Pe Hxy : ℝ}
    (h : Hxy ≤ Real.qaryEntropy (Fintype.card X) Pe) :
    Hxy ≤ fanoBoundRHSOfAlphabet X Pe := by
  simpa [fanoBoundRHSOfAlphabet] using
    (fano_inequality_of_le_qaryEntropy
      (q := Fintype.card X) (Pe := Pe) (Hxy := Hxy) h)

/-- Strict inverse form of the Fano bound on the increasing branch of
`qaryEntropy`.

If a candidate lower bound `a` already has `qaryEntropy q a < Hxy`, and Fano gives
`Hxy ≤ qaryEntropy q Pe`, then `a < Pe`, provided both `a` and `Pe` lie in the
standard monotonicity interval `[0, 1 - 1/q]`.
-/
theorem fano_error_lower_bound_of_lt_qaryEntropy
    {q : ℕ} (hq : 2 ≤ q) {a Pe Hxy : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (q : ℝ))
    (hPe0 : 0 ≤ Pe) (hPe1 : Pe ≤ 1 - 1 / (q : ℝ))
    (hFano : Hxy ≤ Real.qaryEntropy q Pe)
    (haH : Real.qaryEntropy q a < Hxy) :
    a < Pe := by
  have hlt : Real.qaryEntropy q a < Real.qaryEntropy q Pe :=
    lt_of_lt_of_le haH hFano
  have hmono := Real.qaryEntropy_strictMonoOn (q := q) hq
  have ha_mem : a ∈ Set.Icc (0 : ℝ) (1 - 1 / (q : ℝ)) := ⟨ha0, ha1⟩
  have hPe_mem : Pe ∈ Set.Icc (0 : ℝ) (1 - 1 / (q : ℝ)) := ⟨hPe0, hPe1⟩
  by_contra hnot
  have hPe_le_a : Pe ≤ a := le_of_not_gt hnot
  rcases hPe_le_a.eq_or_lt with hEq | hPe_lt_a
  · subst a
    exact (lt_irrefl (Real.qaryEntropy q Pe) hlt)
  · have hlt' : Real.qaryEntropy q Pe < Real.qaryEntropy q a :=
      hmono hPe_mem ha_mem hPe_lt_a
    exact (not_lt_of_ge hlt.le) hlt'

/-- Same inverse form, but stated with the textbook Fano right-hand side. -/
theorem fano_error_lower_bound_of_lt_fanoBoundRHS
    {q : ℕ} (hq : 2 ≤ q) {a Pe Hxy : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (q : ℝ))
    (hPe0 : 0 ≤ Pe) (hPe1 : Pe ≤ 1 - 1 / (q : ℝ))
    (hFano : Hxy ≤ fanoBoundRHS q Pe)
    (haH : fanoBoundRHS q a < Hxy) :
    a < Pe := by
  refine fano_error_lower_bound_of_lt_qaryEntropy
    (q := q) (Hxy := Hxy) hq ha0 ha1 hPe0 hPe1 ?_ ?_
  · rwa [qaryEntropy_eq_fanoBoundRHS]
  · rwa [qaryEntropy_eq_fanoBoundRHS]

/-- Alphabet-indexed inverse form of Fano's inequality. -/
theorem fano_error_lower_bound_of_alphabet
    {X : Type*} [Fintype X]
    (hcard : 2 ≤ Fintype.card X) {a Pe Hxy : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hPe0 : 0 ≤ Pe) (hPe1 : Pe ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hFano : Hxy ≤ fanoBoundRHSOfAlphabet X Pe)
    (haH : fanoBoundRHSOfAlphabet X a < Hxy) :
    a < Pe := by
  exact fano_error_lower_bound_of_lt_fanoBoundRHS
    (q := Fintype.card X) hcard ha0 ha1 hPe0 hPe1
    (by simpa [fanoBoundRHSOfAlphabet] using hFano)
    (by simpa [fanoBoundRHSOfAlphabet] using haH)

/-! ## Finite PMF interface -/

/-- A finite joint probability mass function on `X × Y`, stored as real masses. -/
structure FiniteJointPMF (X Y : Type*) [Fintype X] [Fintype Y] where
  mass : X → Y → ℝ
  mass_nonneg : ∀ x y, 0 ≤ mass x y
  sum_mass : (∑ x, ∑ y, mass x y) = 1

namespace FiniteJointPMF

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Marginal mass of `Y = y`. -/
def marginalY (P : FiniteJointPMF X Y) (y : Y) : ℝ :=
  ∑ x, P.mass x y

/-- Joint Shannon entropy `H(X,Y)` in nats. -/
def jointEntropy (P : FiniteJointPMF X Y) : ℝ :=
  ∑ x, ∑ y, (P.mass x y).negMulLog

/-- Marginal Shannon entropy `H(Y)` in nats. -/
def yEntropy (P : FiniteJointPMF X Y) : ℝ :=
  ∑ y, (P.marginalY y).negMulLog

/-- Conditional entropy `H(X | Y) = H(X,Y) - H(Y)` in nats. -/
def condEntropy (P : FiniteJointPMF X Y) : ℝ :=
  P.jointEntropy - P.yEntropy

/-- Error probability of a Markov-form joint PMF on `(X, Xh)` where the
second coordinate plays the role of the estimator `Xh`. The error event is
`{(x, xh) : x ≠ xh}`. -/
def errorProb [DecidableEq X] (P : FiniteJointPMF X X) : ℝ :=
  ∑ x, ∑ xh, if x = xh then 0 else P.mass x xh

/-- Finite-PMF Fano wrapper, Markov form on `(X, Xh)`.

After proving the model-specific core estimate
`P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb`, this theorem
returns the standard Fano inequality.
-/
theorem fano_inequality_of_core [DecidableEq X]
    (P : FiniteJointPMF X X)
    (hcore :
      P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X P.errorProb := by
  simpa [fanoBoundRHSOfAlphabet] using
    (fano_inequality_of_le_qaryEntropy
      (q := Fintype.card X) (Pe := P.errorProb) (Hxy := P.condEntropy) hcore)

/-- Finite-PMF inverse Fano wrapper on the increasing branch, Markov form. -/
theorem error_lower_bound_of_core [DecidableEq X]
    (P : FiniteJointPMF X X)
    (hcard : 2 ≤ Fintype.card X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hPe0 : 0 ≤ P.errorProb)
    (hPe1 : P.errorProb ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hcore :
      P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb)
    (haH : Real.qaryEntropy (Fintype.card X) a < P.condEntropy) :
    a < P.errorProb := by
  exact fano_error_lower_bound_of_lt_qaryEntropy
    (q := Fintype.card X) hcard ha0 ha1 hPe0 hPe1 hcore haH

end FiniteJointPMF

end

end InformationTheory
