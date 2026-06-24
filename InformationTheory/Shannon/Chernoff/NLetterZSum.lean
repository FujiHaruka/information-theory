import InformationTheory.Shannon.Chernoff.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# n-letter Chernoff `Z`-sum factorization

The `n`-th power of the single-letter Chernoff partition function `chernoffZSum P₁ P₂ lam`
factorizes as a sum over `Fin n → α` of per-coordinate tilt factors:

`(chernoffZSum P₁ P₂ lam) ^ n = ∑ x : Fin n → α, ∏ i, (P₁ (x i))^(1-lam) · (P₂ (x i))^lam`.

This is the pmf-level (`Fintype`) analogue of the finite `Measure.pi` tilt factorization
`MeasurePiTiltedFactorization.pi_tilted_sum_eq_pi_tilted`, and serves as the normalization for
the `n`-letter change of measure.
-/

namespace InformationTheory.Shannon.Chernoff

set_option linter.unusedSectionVars false

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

end InformationTheory.Shannon.Chernoff
