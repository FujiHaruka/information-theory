import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Portfolio.Basic
import InformationTheory.Shannon.Gambling.SideInformation

/-!
# Log-optimal portfolios with side information (Cover–Thomas §16.4)

An investor allocating wealth across `m` stocks with price relatives
`X : α → (Fin m → ℝ)` observes side information `Y` on a finite alphabet `γ`. The joint
law is presented in factored form `(pY, pXgivenY)`. Using a portfolio `bcond y` that may
depend on the observed side information gives the conditional growth rate
`W(bcond | Y) = ∑ y, pY y · W(pXgivenY y, X, bcond y)`. The increment of the growth rate
obtained from `Y` over the marginal log-optimal growth is bounded above by the mutual
information `I(X; Y)`.

This is the non-diagonal mirror of the horse-race theorem
`InformationTheory.Shannon.Gambling.sideInfo_doublingRate_increment_eq_mutualInfo`. In the
diagonal (horse-race) case Kelly betting is proportional and the increment equals
`I(X; Y)`; for a general market the log-optimal portfolio is not proportional, the per-term
log cancellation of the gambling proof fails, and the identity weakens to the inequality
`ΔW ≤ I(X; Y)` obtained from Gibbs' inequality and competitive optimality of the marginal
log-optimal portfolio.

## Main definitions

* `condGrowthRate` — the conditional growth rate
  `W(bcond | Y) = ∑ y, pY y · W(pXgivenY y, X, bcond y)`.

## Main statements

* `sideInfo_growthRate_increment_le_mutualInfo` — Theorem 16.4.1: the increment of the
  growth rate due to side information `Y` is at most the mutual information `I(X; Y)`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Section 16.4.
-/

namespace InformationTheory.Shannon.Portfolio

open Real
open scoped BigOperators
open InformationTheory.Shannon.Gambling
  (sideMarginalX sideInfoMutualInfo sideInfoJointEntropy_eq_chain sideInfo_logOdds_cancel
   sideMarginalX_mem_stdSimplex)

variable {α : Type*} [Fintype α] {γ : Type*} [Fintype γ] {m : ℕ}

/-- The conditional (side-information) growth rate of a portfolio `bcond` that may depend on
the observed side information `y`:
`W(bcond | Y) = ∑ y, pY y · W(pXgivenY y, X, bcond y)`. -/
noncomputable def condGrowthRate
    (X : α → Fin m → ℝ) (bcond : γ → Fin m → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : ℝ :=
  ∑ y, pY y * growthRate (pXgivenY y) X (bcond y)

-- Per-term Gibbs inequality `a − b·c/d ≤ a·(log a − log b − log c + log d)`. When `a = 0`
-- both sides are non-positive/zero; when `a > 0` the log terms collapse to `log (a·d/(b·c))`
-- and the bound is `Real.one_sub_inv_le_log_of_pos`.
lemma gibbs_core (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (ha : 0 ≤ a)
    (hpos : 0 < a → 0 < b ∧ 0 < c ∧ 0 < d) :
    a - b * c / d ≤ a * (Real.log a - Real.log b - Real.log c + Real.log d) := by
  rcases ha.eq_or_lt with ha0 | ha0
  · -- a = 0: LHS = −b·c/d ≤ 0 = RHS.
    rw [← ha0, zero_mul, zero_sub]
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg hb hc) hd)
  · -- 0 < a, hence b, c, d > 0.
    obtain ⟨hb0, hc0, hd0⟩ := hpos ha0
    have hlog : Real.log a - Real.log b - Real.log c + Real.log d
        = Real.log (a * d / (b * c)) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul ha0.ne' hd0.ne',
        Real.log_mul hb0.ne' hc0.ne']
      ring
    rw [hlog]
    have hu : 0 < a * d / (b * c) := by positivity
    have hgibbs : 1 - (a * d / (b * c))⁻¹ ≤ Real.log (a * d / (b * c)) :=
      Real.one_sub_inv_le_log_of_pos hu
    have hval : a * (1 - (a * d / (b * c))⁻¹) = a - b * c / d := by
      field_simp
    rw [← hval]
    exact mul_le_mul_of_nonneg_left hgibbs ha0.le

-- The mutual information in the symmetric entropy form equals the conditional KL divergence
-- `∑ y, pY y · ∑ x, pXgivenY y x · (log pXgivenY y x − log pX x)`, via the chain-rule bridge
-- and the marginalization identity `sideInfo_logOdds_cancel`.
lemma sideInfoMutualInfo_eq_condKL (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α) :
    sideInfoMutualInfo pY pXgivenY
      = ∑ y, pY y * ∑ x, pXgivenY y x *
          (Real.log (pXgivenY y x) - Real.log (sideMarginalX pY pXgivenY x)) := by
  have hcancel : (∑ y, pY y * ∑ x, pXgivenY y x * Real.log (sideMarginalX pY pXgivenY x))
      = ∑ x, sideMarginalX pY pXgivenY x * Real.log (sideMarginalX pY pXgivenY x) :=
    sideInfo_logOdds_cancel (sideMarginalX pY pXgivenY) pY pXgivenY
  have e_marg : (∑ x, Real.negMulLog (sideMarginalX pY pXgivenY x))
      = -∑ x, sideMarginalX pY pXgivenY x * Real.log (sideMarginalX pY pXgivenY x) := by
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  have e_cond : (∑ y, pY y * ∑ x, Real.negMulLog (pXgivenY y x))
      = -∑ y, pY y * ∑ x, pXgivenY y x * Real.log (pXgivenY y x) := by
    simp only [Real.negMulLog, neg_mul, mul_neg, Finset.sum_neg_distrib]
  have hRHS : (∑ y, pY y * ∑ x, pXgivenY y x *
        (Real.log (pXgivenY y x) - Real.log (sideMarginalX pY pXgivenY x)))
      = (∑ y, pY y * ∑ x, pXgivenY y x * Real.log (pXgivenY y x))
        - ∑ x, sideMarginalX pY pXgivenY x * Real.log (sideMarginalX pY pXgivenY x) := by
    rw [← hcancel, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg (pY y * ·) (Finset.sum_congr rfl (fun x _ ↦ ?_))
    rw [mul_sub]
  unfold sideInfoMutualInfo
  rw [sideInfoJointEntropy_eq_chain pY pXgivenY hcond, hRHS, e_marg, e_cond]
  ring

-- The growth-rate increment expressed as a conditional log-ratio sum.
lemma increment_eq (X : α → Fin m → ℝ) (bs : Fin m → ℝ) (bcond : γ → Fin m → ℝ)
    (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) :
    condGrowthRate X bcond pY pXgivenY - growthRate (sideMarginalX pY pXgivenY) X bs
      = ∑ y, pY y * ∑ x, pXgivenY y x *
          (Real.log (wealthRelative X (bcond y) x) - Real.log (wealthRelative X bs x)) := by
  unfold condGrowthRate growthRate
  rw [← sideInfo_logOdds_cancel (fun x ↦ wealthRelative X bs x) pY pXgivenY,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ ↦ ?_)
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg (pY y * ·) (Finset.sum_congr rfl (fun x _ ↦ ?_))
  rw [← mul_sub]

/-- Theorem 16.4.1 (Cover–Thomas, portfolio with side information): the increment of the
growth rate obtained from the side information `Y` is bounded above by the mutual
information `I(X; Y)`. Here `bs` is a marginal log-optimal (Kuhn–Tucker) portfolio and
`bcond y` an arbitrary portfolio on the simplex for each observed `y`, so
`W(bcond | Y) − W*(X) ≤ I(X; Y)`.

Unlike the horse-race mirror `sideInfo_doublingRate_increment_eq_mutualInfo` (an equality),
the non-proportional log-optimal portfolio yields only an inequality.

@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`).
`hbs`/`hbcond` are simplex-membership regularity (portfolio validity); without them the
statement is false as framed (an off-simplex `bcond` gives `ΔW = log 100 > 0 = I` under
`X ⊥ Y`). `hpos` is log-domain positivity and `hKT` the Kuhn–Tucker characterization of the
marginal log-optimal baseline `bs`, consumed via the proven `competitive_optimality` — none
is the conclusion. The `ΔW ≤ I` bound is genuinely derived from per-outcome Gibbs plus
competitive optimality; the dropped `hKTcond` (optimality of `bcond`) is not needed for the
upper bound. No load-bearing hypothesis. -/
@[entry_point]
theorem sideInfo_growthRate_increment_le_mutualInfo
    (X : α → Fin m → ℝ) (bs : Fin m → ℝ) (bcond : γ → Fin m → ℝ)
    (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ) (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ c ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X c a)
    (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hbcond : ∀ y, bcond y ∈ stdSimplex ℝ (Fin m))
    (hKT : ∀ i, (∑ a, sideMarginalX pY pXgivenY a * X a i / wealthRelative X bs a) ≤ 1) :
    condGrowthRate X bcond pY pXgivenY - growthRate (sideMarginalX pY pXgivenY) X bs
      ≤ sideInfoMutualInfo pY pXgivenY := by
  rw [← sub_nonneg, sideInfoMutualInfo_eq_condKL pY pXgivenY hcond,
    increment_eq X bs bcond pY pXgivenY]
  -- Combine the conditional-KL and increment sums into a single conditional log-ratio sum.
  have hE : (∑ y, pY y * ∑ x, pXgivenY y x *
        (Real.log (pXgivenY y x) - Real.log (sideMarginalX pY pXgivenY x)))
      - (∑ y, pY y * ∑ x, pXgivenY y x *
        (Real.log (wealthRelative X (bcond y) x) - Real.log (wealthRelative X bs x)))
      = ∑ y, pY y * ∑ x, pXgivenY y x *
          (Real.log (pXgivenY y x) - Real.log (sideMarginalX pY pXgivenY x)
            - Real.log (wealthRelative X (bcond y) x) + Real.log (wealthRelative X bs x)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    exact congrArg (pY y * ·) (Finset.sum_congr rfl (fun x _ ↦ by ring))
  rw [hE]
  refine Finset.sum_nonneg (fun y _ ↦ ?_)
  rcases (hpY.1 y).eq_or_lt with hy0 | hy0
  · rw [← hy0]; simp
  refine mul_nonneg (hpY.1 y) ?_
  -- Competitive optimality of the marginal Kuhn–Tucker portfolio `bs` against `bcond y`.
  have hcomp := competitive_optimality (sideMarginalX pY pXgivenY) X bs (bcond y) (hbcond y) hKT
  -- Per-outcome Gibbs lower bound.
  have hstep : (∑ x, (pXgivenY y x - sideMarginalX pY pXgivenY x *
        wealthRelative X (bcond y) x / wealthRelative X bs x))
      ≤ ∑ x, pXgivenY y x * (Real.log (pXgivenY y x) - Real.log (sideMarginalX pY pXgivenY x)
          - Real.log (wealthRelative X (bcond y) x) + Real.log (wealthRelative X bs x)) := by
    refine Finset.sum_le_sum (fun x _ ↦ ?_)
    refine gibbs_core (pXgivenY y x) (sideMarginalX pY pXgivenY x)
      (wealthRelative X (bcond y) x) (wealthRelative X bs x)
      ((sideMarginalX_mem_stdSimplex hpY hcond).1 x)
      (hpos x (bcond y) (hbcond y)).le (hpos x bs hbs).le ((hcond y).1 x) (fun hax ↦ ?_)
    refine ⟨?_, hpos x (bcond y) (hbcond y), hpos x bs hbs⟩
    exact lt_of_lt_of_le (mul_pos hy0 hax)
      (Finset.single_le_sum (fun y' _ ↦ mul_nonneg (hpY.1 y') ((hcond y').1 x)) (Finset.mem_univ y))
  -- The Gibbs lower-bound sum is non-negative: `∑ pXgivenY = 1` and competitive optimality.
  have hlow : (0:ℝ) ≤ ∑ x, (pXgivenY y x - sideMarginalX pY pXgivenY x *
        wealthRelative X (bcond y) x / wealthRelative X bs x) := by
    rw [Finset.sum_sub_distrib, (hcond y).2]
    have hle : (∑ x, sideMarginalX pY pXgivenY x *
        wealthRelative X (bcond y) x / wealthRelative X bs x) ≤ 1 := by
      simp only [mul_div_assoc]; exact hcomp
    linarith
  linarith [hstep, hlow]

end InformationTheory.Shannon.Portfolio
