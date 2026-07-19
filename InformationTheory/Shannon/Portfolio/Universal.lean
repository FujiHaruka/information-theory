import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import InformationTheory.Meta.EntryPoint

/-!
# Cover's universal portfolio (Cover–Thomas Section 16.7)

For a market on `Fin (d + 1)` stocks with a fixed data stream of price relatives
`xs : ℕ → Fin (d + 1) → ℝ`, the wealth of a constant-rebalanced portfolio `b` on the
simplex after `n` periods is `constWealth xs b n = ∏ i < n, (b · xs i)`. Cover's
*universal portfolio* averages the constant-rebalanced wealth uniformly over the
simplex, giving `universalWealth xs n = (∫ b, constWealth xs b n) / vol`. The main
result (Theorem 16.7.1) is that this achieves the same exponential growth rate as the
best constant-rebalanced portfolio chosen in hindsight: the per-period regret
`(1 / n) · (log S*_n − log Ŝ_n)` tends to `0`.

The simplex is parametrized by its `d` free coordinates: the corner simplex
`cornerSimplex d = {y | 0 ≤ y ∧ ∑ y ≤ 1}` carries the ambient Lebesgue measure of
`Fin d → ℝ`, and `simplexLift` sends `y` to the full portfolio with last coordinate
`1 − ∑ y`. This makes the uniform measure on the simplex an honest, computable object
(the intrinsic `(d)`-dimensional measure on the affine hyperplane `∑ b = 1` has no
Mathlib API, whereas the corner parametrization only needs `volume` on `Fin d → ℝ`).

## Main definitions

* `cornerSimplex` — the `d`-dimensional corner simplex in `Fin d → ℝ`.
* `simplexLift` — lifts free coordinates `y` to a portfolio on `Fin (d + 1)`.
* `constWealth` — wealth `∏ i < n, (b · xs i)` of a constant-rebalanced portfolio.
* `universalWealth` — Cover's universal wealth, the uniform average over the simplex.
* `bestConstantWealth` — the best constant-rebalanced wealth in hindsight, `S*_n`.
* `universalRegret` — the per-period regret `(log S*_n − log Ŝ_n) / n`.

## Main statements

* `universal_portfolio_regret_tendsto_zero` — Theorem 16.7.1: the per-period regret of
  the universal portfolio tends to `0`.

## Implementation notes

The regret theorem is derived (proof-done reduction) from three analytic facts about
the universal wealth — positivity, the average bound `Ŝ_n ≤ S*_n`, and Cover's shrink
bound `S*_n ≤ e · (n + 1) ^ d · Ŝ_n` — each of which is a genuine (but Mathlib-wall-free)
measure-theoretic development left as `sorry` for a successor session. The shrink bound
uses `MeasureTheory.Measure.addHaar_image_homothety`: the homothety
`b ↦ (1 − λ) b* + λ b` scales simplex volume by `λ ^ d`, and on its image the wealth
stays within a factor `(1 − λ) ^ n ≥ e⁻¹` of the optimum.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Section 16.7.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter Real
open scoped BigOperators Topology

variable {d : ℕ}

/-- The corner simplex `{y : Fin d → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}`, the domain
of the `d` free coordinates of a portfolio on `Fin (d + 1)` stocks. It carries the
ambient Lebesgue measure of `Fin d → ℝ`. -/
def cornerSimplex (d : ℕ) : Set (Fin d → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

/-- Lift the free coordinates `y : Fin d → ℝ` to a full portfolio on `Fin (d + 1)`
stocks by appending the last coordinate `1 − ∑ i, y i`. -/
noncomputable def simplexLift (y : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc y (1 - ∑ i, y i)

/-- Wealth `∏ i < n, (b · xs i)` of the constant-rebalanced portfolio `b` after `n`
periods with price relatives `xs`. -/
noncomputable def constWealth
    (xs : ℕ → Fin (d + 1) → ℝ) (b : Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∑ j, b j * xs i j

/-- Cover's universal wealth `Ŝ_n`: the uniform average of the constant-rebalanced
wealth over the simplex, computed via the corner parametrization. -/
noncomputable def universalWealth (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  (∫ y in cornerSimplex d, constWealth xs (simplexLift y) n) / (volume (cornerSimplex d)).toReal

/-- The best constant-rebalanced wealth in hindsight `S*_n = ⨆ b, constWealth xs b n`,
the supremum over the simplex. -/
noncomputable def bestConstantWealth (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  ⨆ b : stdSimplex ℝ (Fin (d + 1)), constWealth xs (b : Fin (d + 1) → ℝ) n

/-- The per-period regret `(log S*_n − log Ŝ_n) / n` of the universal portfolio. -/
noncomputable def universalRegret (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  (Real.log (bestConstantWealth xs n) - Real.log (universalWealth xs n)) / (n : ℝ)

/-- Positivity of the universal wealth: with strictly positive price relatives every
constant-rebalanced wealth is positive, and the uniform average over the
positive-measure corner simplex stays positive.

@residual(plan:portfolio-operational-plan) -/
theorem universalWealth_pos
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) (n : ℕ) :
    0 < universalWealth xs n := by
  sorry

/-- The universal wealth never exceeds the best constant-rebalanced wealth: `Ŝ_n` is a
uniform average of values `constWealth xs (simplexLift y) n ≤ S*_n`.

@residual(plan:portfolio-operational-plan) -/
theorem universalWealth_le_bestConstantWealth
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) (n : ℕ) :
    universalWealth xs n ≤ bestConstantWealth xs n := by
  sorry

/-- Cover's shrink bound: the best constant-rebalanced wealth exceeds the universal
wealth by at most a factor `e · (n + 1) ^ d`. The homothety
`b ↦ (1 − 1/(n+1)) b* + (1/(n+1)) b` scales simplex volume by `(n + 1)⁻ᵈ`
(`MeasureTheory.Measure.addHaar_image_homothety`) and keeps the wealth within
`(1 − 1/(n+1)) ^ n ≥ e⁻¹` of the optimum.

@residual(plan:portfolio-operational-plan) -/
theorem bestConstantWealth_le_mul_universalWealth
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) (n : ℕ) :
    bestConstantWealth xs n ≤ Real.exp 1 * ((n : ℝ) + 1) ^ d * universalWealth xs n := by
  sorry

/-- Theorem 16.7.1 (Cover–Thomas): the per-period regret of the universal portfolio
relative to the best constant-rebalanced portfolio chosen in hindsight tends to `0`. -/
@[entry_point]
theorem universal_portfolio_regret_tendsto_zero
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) :
    Tendsto (fun n ↦ universalRegret xs n) atTop (𝓝 0) := by
  -- The three analytic facts about the universal wealth.
  have hU_pos : ∀ n, 0 < universalWealth xs n := fun n ↦ universalWealth_pos xs hpos n
  have hUS : ∀ n, universalWealth xs n ≤ bestConstantWealth xs n :=
    fun n ↦ universalWealth_le_bestConstantWealth xs hpos n
  have hshrink : ∀ n, bestConstantWealth xs n
      ≤ Real.exp 1 * ((n : ℝ) + 1) ^ d * universalWealth xs n :=
    fun n ↦ bestConstantWealth_le_mul_universalWealth xs hpos n
  have hS_pos : ∀ n, 0 < bestConstantWealth xs n := fun n ↦ lt_of_lt_of_le (hU_pos n) (hUS n)
  -- Lower bound: the regret is nonnegative because `Ŝ_n ≤ S*_n`.
  have hlow : ∀ n, 0 ≤ universalRegret xs n := by
    intro n
    refine div_nonneg ?_ (Nat.cast_nonneg n)
    have := Real.log_le_log (hU_pos n) (hUS n)
    linarith
  -- Upper bound: the regret is at most `(1 + d · log (n + 1)) / n` (for `n ≥ 1`).
  have hup : ∀ n, 1 ≤ n →
      universalRegret xs n ≤ (1 + (d : ℝ) * Real.log ((n : ℝ) + 1)) / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpospow : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
    have hlogS : Real.log (bestConstantWealth xs n)
        ≤ 1 + (d : ℝ) * Real.log ((n : ℝ) + 1) + Real.log (universalWealth xs n) := by
      have h1 := Real.log_le_log (hS_pos n) (hshrink n)
      rw [Real.log_mul (by positivity) (hU_pos n).ne',
          Real.log_mul (Real.exp_pos 1).ne' hpospow.ne',
          Real.log_exp, Real.log_pow] at h1
      linarith
    have hnum : Real.log (bestConstantWealth xs n) - Real.log (universalWealth xs n)
        ≤ 1 + (d : ℝ) * Real.log ((n : ℝ) + 1) := by linarith
    exact (div_le_div_iff_of_pos_right hnpos).mpr hnum
  -- The upper bounding sequence tends to `0`.
  have hg_lim : Tendsto (fun n : ℕ ↦ (1 + (d : ℝ) * Real.log ((n : ℝ) + 1)) / (n : ℝ))
      atTop (𝓝 0) := by
    have h1n : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hlogx : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hn1 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlog2 : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
        atTop (𝓝 0) := hlogx.comp hn1
    have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add h1n
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hlogn : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
      have hprod := hlog2.mul hratio
      rw [zero_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hsum := h1n.add (hlogn.const_mul (d : ℝ))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  -- Squeeze the regret between `0` and the vanishing upper bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg_lim
    (Eventually.of_forall hlow) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn using hup n hn

end InformationTheory.Shannon.Portfolio
