import InformationTheory.Shannon.Chernoff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# n-letter Chernoff `Z`-sum factorization (Ch.11 converse building block)

The Cramér side already has a finite `Measure.pi` tilt factorization
(`MeasurePiTiltedFactorization.pi_tilted_sum_eq_pi_tilted`); this file is the
**Chernoff (pmf-level, `Fintype`) analogue**. It records that the `n`-th power of
the single-letter Chernoff partition function `chernoffZSum P₁ P₂ lam`
factorizes as a sum over `Fin n → α` of per-coordinate tilt factors:

`(chernoffZSum P₁ P₂ lam) ^ n = ∑ x : Fin n → α, ∏ i, (P₁ (x i))^(1-lam) · (P₂ (x i))^lam`.

This is the normalization building block for the `n`-letter change-of-measure
needed to discharge `IsChernoffNLetterRN` (`ChernoffPerTiltSanov.lean`) and
`IsBayesErrorPerTiltLowerBound` (`ChernoffPerTiltDischarge.lean`). The converse
proper still has a remaining CLT-boundary piece and is handled separately.
-/

namespace InformationTheory.Shannon.Chernoff

set_option linter.unusedSectionVars false

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

end InformationTheory.Shannon.Chernoff
