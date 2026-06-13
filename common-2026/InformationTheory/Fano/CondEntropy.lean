import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators

/-!
# 3-variable joint and conditional entropy: chain rule + deterministic collapse

We work directly with raw mass functions `μ : X → E → Y → ℝ` rather than committing to a
structured PMF type, because every chain rule becomes a `ring` identity at this level.

The two non-trivial outputs are:

* the algebraic chain rules `H(X, E | Y) = H(E | Y) + H(X | E, Y)` and
  `H(X, E | Y) = H(X | Y) + H(E | X, Y)`;
* `H(E | X, Y) = 0` whenever `E` is a deterministic function of `(X, Y)`.

Together with `entropyOfFn_le_log_supportCard` and `binEntropy_jensen_finset`, these
assemble the Fano core inequality.

## Implementation notes

This file's mass-function entropy/condEntropy are the form used by the `Fano.Core`
development. The measure-theoretic developments (`Fano.Measure`, `Shannon.Bridge.entropy`,
`InformationTheory.MeasureFano.condEntropy`) use a parallel formalism; the two do not
depend on each other.
-/

namespace InformationTheory
namespace Joint3

open scoped BigOperators
open Finset

noncomputable section

variable {X E Y : Type*} [Fintype X] [Fintype E] [Fintype Y]

/-! ### Marginals and joint entropies -/

/-- Marginal mass on `Y`, summing out both `X` and `E`. -/
def marginalY (μ : X → E → Y → ℝ) (y : Y) : ℝ :=
  ∑ x, ∑ e, μ x e y

/-- Marginal mass on `(E, Y)`, summing out `X`. -/
def marginalEY (μ : X → E → Y → ℝ) (e : E) (y : Y) : ℝ :=
  ∑ x, μ x e y

/-- Marginal mass on `(X, Y)`, summing out `E`. -/
def marginalXY (μ : X → E → Y → ℝ) (x : X) (y : Y) : ℝ :=
  ∑ e, μ x e y

/-- Joint entropy `H(X, E, Y)`. -/
def jointEntropy (μ : X → E → Y → ℝ) : ℝ :=
  ∑ x, ∑ e, ∑ y, (μ x e y).negMulLog

/-- Marginal entropy `H(Y)`. -/
def yEntropy (μ : X → E → Y → ℝ) : ℝ :=
  ∑ y, (marginalY μ y).negMulLog

/-- Marginal entropy `H(E, Y)`. -/
def eyEntropy (μ : X → E → Y → ℝ) : ℝ :=
  ∑ e, ∑ y, (marginalEY μ e y).negMulLog

/-- Marginal entropy `H(X, Y)`. -/
def xyEntropy (μ : X → E → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, (marginalXY μ x y).negMulLog

/-! ### Marginal nonnegativity and Bool decomposition -/

omit [Fintype E] [Fintype Y] in
/-- Each `(E, Y)` marginal is non-negative when the joint mass is. -/
lemma marginalEY_nonneg (μ : X → E → Y → ℝ) (h_nn : ∀ x e y, 0 ≤ μ x e y)
    (e : E) (y : Y) : 0 ≤ marginalEY μ e y :=
  Finset.sum_nonneg (fun x _ => h_nn x e y)

omit [Fintype Y] in
/-- The `Y` marginal is non-negative when the joint mass is. -/
lemma marginalY_nonneg (μ : X → E → Y → ℝ) (h_nn : ∀ x e y, 0 ≤ μ x e y)
    (y : Y) : 0 ≤ marginalY μ y :=
  Finset.sum_nonneg
    (fun x _ => Finset.sum_nonneg (fun e _ => h_nn x e y))

/-- For a binary `E = Bool`, the `Y` marginal splits as the sum of the
two `(E, Y)` marginals. -/
lemma marginalY_eq_marginalEY_true_add_false {X Y : Type*}
    [Fintype X] (μ : X → Bool → Y → ℝ) (y : Y) :
    marginalY μ y = marginalEY μ true y + marginalEY μ false y := by
  unfold marginalY marginalEY
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Fintype.sum_bool _

/-! ### Conditional entropies (defined as entropy differences) -/

/-- `H(X, E | Y) = H(X, E, Y) - H(Y)`. -/
def condXE_Y (μ : X → E → Y → ℝ) : ℝ := jointEntropy μ - yEntropy μ

/-- `H(E | Y) = H(E, Y) - H(Y)`. -/
def condE_Y (μ : X → E → Y → ℝ) : ℝ := eyEntropy μ - yEntropy μ

/-- `H(X | E, Y) = H(X, E, Y) - H(E, Y)`. -/
def condX_EY (μ : X → E → Y → ℝ) : ℝ := jointEntropy μ - eyEntropy μ

/-- `H(X | Y) = H(X, Y) - H(Y)`. -/
def condX_Y (μ : X → E → Y → ℝ) : ℝ := xyEntropy μ - yEntropy μ

/-- `H(E | X, Y) = H(X, E, Y) - H(X, Y)`. -/
def condE_XY (μ : X → E → Y → ℝ) : ℝ := jointEntropy μ - xyEntropy μ

/-! ### Chain rules -/

/-- Chain rule with `E` first: `H(X, E | Y) = H(E | Y) + H(X | E, Y)`. -/
theorem chain_rule_E_first (μ : X → E → Y → ℝ) :
    condXE_Y μ = condE_Y μ + condX_EY μ := by
  simp only [condXE_Y, condE_Y, condX_EY]; ring

/-- Chain rule with `X` first: `H(X, E | Y) = H(X | Y) + H(E | X, Y)`. -/
theorem chain_rule_X_first (μ : X → E → Y → ℝ) :
    condXE_Y μ = condX_Y μ + condE_XY μ := by
  simp only [condXE_Y, condX_Y, condE_XY]; ring

/-! ### Deterministic E ⇒ H(E | X, Y) = 0 -/

/-- If `E` is a deterministic function of `(X, Y)` — formalized by saying
that `μ` is concentrated on `e = f x y` and equals `marginalXY μ x y`
there — then the conditional entropy `H(E | X, Y)` vanishes. -/
theorem condE_XY_zero_of_deterministic [DecidableEq E]
    (μ : X → E → Y → ℝ) (f : X → Y → E)
    (hdet : ∀ x e y, μ x e y = if e = f x y then marginalXY μ x y else 0) :
    condE_XY μ = 0 := by
  -- For each (x, y), the inner sum over e collapses to the marginal term.
  have hfix : ∀ x y, (∑ e, (μ x e y).negMulLog) = (marginalXY μ x y).negMulLog := by
    intro x y
    rw [Finset.sum_eq_single (f x y)]
    · rw [hdet x (f x y) y]
      simp
    · intro e _ he
      rw [hdet x e y, if_neg he]
      exact Real.negMulLog_zero
    · intro h
      exact (h (Finset.mem_univ _)).elim
  -- Collapse the joint entropy sum to the (X, Y) marginal entropy.
  have hjoint_eq_xy : jointEntropy μ = xyEntropy μ := by
    unfold jointEntropy xyEntropy
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    exact hfix x y
  unfold condE_XY
  linarith

end

end Joint3
end InformationTheory
