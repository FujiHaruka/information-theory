import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InformationTheory.Meta.EntryPoint

/-!
# Log-optimal portfolios (Cover–Thomas Chapter 16)

For a market on a finite outcome space `α` with true law `p : α → ℝ` and price
relatives `X : α → (Fin m → ℝ)` (the factor by which stock `i` multiplies wealth in
outcome `a`), a portfolio `b : Fin m → ℝ` on the simplex distributes wealth across the
`m` stocks. Its **wealth relative** in outcome `a` is `S_b(a) = ∑ i, b i · X a i`, and
its **growth (doubling) rate** is `W(b) = ∑ a, p a · log (S_b(a))`.

This is the non-diagonal generalization of the horse-race doubling rate
`InformationTheory.Shannon.Gambling.doublingRate` (recovered by the diagonal choice
`X a i = o i · [a = i]`).

## Main definitions

* `wealthRelative` — the wealth relative `S_b(a) = ∑ i, b i · X a i`.
* `growthRate` — the growth rate `W(b) = ∑ a, p a · log (S_b(a))`.

## Main statements

* `competitive_optimality` — Theorem 16.3.1: for a Kuhn–Tucker portfolio `bs`, every
  portfolio `b` satisfies `E[S_b / S_bs] ≤ 1`.
* `growthRate_concaveOn` — Theorem 16.2.2: the growth rate is concave on the simplex.
* `logOptimal_of_kuhnTucker` — Theorem 16.2.1 (reverse): the Kuhn–Tucker condition
  implies log-optimality.
* `kuhnTucker_of_logOptimal` — Theorem 16.2.1 (forward): log-optimality implies the
  Kuhn–Tucker condition.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Chapter 16.
-/

namespace InformationTheory.Shannon.Portfolio

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α] {m : ℕ}

/-- Wealth relative `S_b(a) = ∑ i, b i · X a i` of portfolio `b` under price relatives `X`. -/
noncomputable def wealthRelative (X : α → Fin m → ℝ) (b : Fin m → ℝ) (a : α) : ℝ :=
  ∑ i, b i * X a i

/-- Growth (doubling) rate `W(b) = ∑ a, p a · log (S_b(a))` of portfolio `b`. -/
noncomputable def growthRate (p : α → ℝ) (X : α → Fin m → ℝ) (b : Fin m → ℝ) : ℝ :=
  ∑ a, p a * Real.log (wealthRelative X b a)

/-- Theorem 16.3.1 (Cover–Thomas): competitive optimality of a Kuhn–Tucker portfolio
`bs`. If `bs` satisfies the Kuhn–Tucker condition `∀ i, ∑ a, p a · X a i / S_bs(a) ≤ 1`,
then every portfolio `b` on the simplex has expected wealth ratio at most one,
`∑ a, p a · (S_b(a) / S_bs(a)) ≤ 1`. -/
@[entry_point]
theorem competitive_optimality (p : α → ℝ) (X : α → Fin m → ℝ) (bs b : Fin m → ℝ)
    (hb : b ∈ stdSimplex ℝ (Fin m))
    (hKT : ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1) :
    (∑ a, p a * (wealthRelative X b a / wealthRelative X bs a)) ≤ 1 := by
  -- Expand each outcome term as a sum over stocks, swap the order of summation, and
  -- factor out `b i` to expose the Kuhn–Tucker quantity `∑ a, p a · X a i / S_bs(a)`.
  have per_a : ∀ a, p a * (wealthRelative X b a / wealthRelative X bs a)
      = ∑ i, b i * (p a * X a i / wealthRelative X bs a) := by
    intro a
    unfold wealthRelative
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  calc (∑ a, p a * (wealthRelative X b a / wealthRelative X bs a))
      = ∑ a, ∑ i, b i * (p a * X a i / wealthRelative X bs a) :=
        Finset.sum_congr rfl (fun a _ ↦ per_a a)
    _ = ∑ i, ∑ a, b i * (p a * X a i / wealthRelative X bs a) := Finset.sum_comm
    _ = ∑ i, b i * (∑ a, p a * X a i / wealthRelative X bs a) :=
        Finset.sum_congr rfl (fun i _ ↦ (Finset.mul_sum _ _ _).symm)
    _ ≤ ∑ i, b i * 1 :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hKT i) (hb.1 i))
    _ = 1 := by simp only [mul_one]; exact hb.2

/-- Theorem 16.2.2 (Cover–Thomas): the growth rate is concave in the portfolio.
@residual(plan:portfolio-concavity) -/
@[entry_point]
theorem growthRate_concaveOn (p : α → ℝ) (X : α → Fin m → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X b a) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (growthRate p X) := by
  sorry

/-- Theorem 16.2.1 (Cover–Thomas), reverse direction: a portfolio `bs` satisfying the
Kuhn–Tucker condition is log-optimal (maximizes the growth rate on the simplex).
@residual(plan:portfolio-reverse-kt) -/
@[entry_point]
theorem logOptimal_of_kuhnTucker (p : α → ℝ) (X : α → Fin m → ℝ) (bs : Fin m → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ a, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X b a)
    (hKT : ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1) :
    IsMaxOn (growthRate p X) (stdSimplex ℝ (Fin m)) bs := by
  sorry

/-- Theorem 16.2.1 (Cover–Thomas), forward direction: a log-optimal portfolio `bs`
satisfies the Kuhn–Tucker condition `∀ i, ∑ a, p a · X a i / S_bs(a) ≤ 1`.
@residual(plan:portfolio-forward-kt) -/
@[entry_point]
theorem kuhnTucker_of_logOptimal (p : α → ℝ) (X : α → Fin m → ℝ) (bs : Fin m → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ a, 0 < wealthRelative X bs a) (hXnn : ∀ a i, 0 ≤ X a i)
    (hmax : IsMaxOn (growthRate p X) (stdSimplex ℝ (Fin m)) bs) :
    ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1 := by
  sorry

end InformationTheory.Shannon.Portfolio
