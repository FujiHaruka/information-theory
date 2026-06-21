import InformationTheory.Shannon.Hoeffding.Tradeoff
import InformationTheory.Shannon.Chernoff.Basic
import InformationTheory.Meta.EntryPoint
import Mathlib.Order.Filter.IsBounded

/-!
# Hoeffding tradeoff — rate boundedness

This file publishes the boundedness lemmas for the fixed-`alpha` Type-II rate
sequence `-(1/n) log (steinTypeII_at_level_pmf P₁ P₂ n alpha)`. They are
unconditional facts about the rate sequence, and
`hoeffding_rate_isBoundedUnder_le` is consumed by
`hoeffding_tradeoff_achievability_at_boundary`
(`HoeffdingMinimizerExistence.lean`).

The fixed-`alpha` rate converges to `D(P₁‖P₂)`, not to the Hoeffding tradeoff
curve `E₂(alpha)`; the genuine statement of the tradeoff is
`hoeffding_tradeoff_exp` at the exponential level
(`HoeffdingTradeoffExp.lean`).

## What this file publishes

* `hoeffding_rate_isBoundedUnder_ge`: the rate sequence
  `-(1/n) log steinTypeII_at_level_pmf` is bounded below (by `0`) along `atTop`,
  derived from `steinTypeII_at_level_pmf_le_one` + `Real.log_nonpos`.

* `hoeffding_rate_isBoundedUnder_le`: the rate sequence is bounded above by
  `M := -log p₂_min + |log(1 - alpha)|` along `atTop`, derived from a lower
  bound `steinTypeII ≥ (1 - alpha) · p₂_min^n` obtained by Type I constraint +
  minimum P₂ atom (under `alpha < 1`, which avoids the `log 0` corner case).

The `pmf` form `α → ℝ` is kept throughout.
-/

namespace InformationTheory.Shannon.HoeffdingSandwich

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## `IsBoundedUnder (· ≥ ·)`: rate bounded below -/

omit [DecidableEq α] in
/-- The rate sequence
`-(1/n) log (steinTypeII_at_level_pmf P₁ P₂ n alpha)` is bounded below by `0`
along `atTop`.

Derivation:
* `steinTypeII_at_level_pmf ≤ 1` (`HoeffdingTradeoff.steinTypeII_at_level_pmf_le_one`),
* if the infimum is `> 0`, `log ≤ 0`, and `-(1/n) ≤ 0` for `n ≥ 1`, so
  `-(1/n) * log ≥ 0`.
* if the infimum is `0`, `Real.log 0 = 0`, so the rate is `0`.

In both cases `rate n ≥ 0`. -/
@[entry_point]
lemma hoeffding_rate_isBoundedUnder_ge
    (P₁ P₂ : α → ℝ) (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hP₂_nn : ∀ a, 0 ≤ P₂ a) {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) :
    Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) := by
  classical
  -- ∀ᶠ n ≥ 1, rate n ≥ 0.
  refine Filter.isBoundedUnder_of_eventually_ge (a := (0 : ℝ)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  -- steinTypeII ≤ 1, steinTypeII ≥ 0 (we have nonneg). Split on whether it is 0 or positive.
  have h_le_one : steinTypeII_at_level_pmf P₁ P₂ n alpha ≤ 1 :=
    steinTypeII_at_level_pmf_le_one P₁ P₂ hP₁_sum hP₂_sum hP₂_nn n alpha h_alpha_nn
  have h_nn : 0 ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha :=
    steinTypeII_at_level_pmf_nonneg P₁ P₂ hP₁_sum hP₂_sum hP₂_nn n alpha h_alpha_nn
  have h_log_le : Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha) ≤ 0 := by
    rcases eq_or_lt_of_le h_nn with h_zero | h_pos
    · -- steinTypeII = 0 ⇒ log 0 = 0.
      rw [← h_zero, Real.log_zero]
    · -- 0 < steinTypeII ≤ 1 ⇒ log ≤ 0.
      exact Real.log_nonpos h_pos.le h_le_one
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
  have h_neg_inv_nonpos : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  -- (-(1/n)) * log: product of nonpos and nonpos is nonneg.
  exact mul_nonneg_iff.mpr (Or.inr ⟨h_neg_inv_nonpos, h_log_le⟩)

/-! ## `IsBoundedUnder (· ≤ ·)`: rate bounded above -/

omit [DecidableEq α] in
/-- Lower bound on `steinTypeII_at_level_pmf` when `alpha < 1`
under full support `P₁, P₂ > 0`.

Strategy: pick the smallest `P₂` atom `a₀`. For any test `s` with Type I ≤ alpha,
i.e. `∑_{x∈s} ∏ P₁(x_i) ≥ 1 - alpha`, we bound below by the
**worst single x term**: each term `∏ P₂(x_i) ≥ p₂_min^n`. Combined with
`|s| ≥ (1 - alpha) / (P₁_max)^n`, the Type II is at least
`(1 - alpha) · (p₂_min / P₁_max)^n`. We further drop the `(/P₁_max)^n` factor
by using `p₁_max ≤ 1` (pmf entries ≤ 1 in a probability simplex), giving
the looser but cleaner bound

  `Type II ≥ (1 - alpha) · p₂_min^n`.

*Note*: we actually use the tighter argument
`∑_{x∈s} ∏ P₂(x_i) ≥ (∑_{x∈s} ∏ P₁(x_i)) · (p₂_min / p₁_max)^n`,
but it is simpler to bound each `∏ P₂(x_i)` by `p₂_min^n` directly and then
`|s| · p₂_min^n ≥ p₂_min^n` (since `|s| ≥ 1`, which we obtain from
`1 - alpha > 0`). This gives `steinTypeII ≥ p₂_min^n`. -/
lemma steinTypeII_at_level_pmf_ge_pow_pmin
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (_h_alpha_lt : alpha < 1)
    (n : ℕ) {a₀ : α} (ha₀ : ∀ a, P₂ a₀ ≤ P₂ a) :
    (1 - alpha) * (P₂ a₀) ^ n ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha := by
  classical
  -- ∀ β ∈ steinBetaSet_pmf, β ≥ (1 - alpha) · (P₂ a₀)^n.
  unfold steinTypeII_at_level_pmf
  refine le_csInf ?_ ?_
  · exact ⟨1, one_mem_steinBetaSet_pmf P₁ P₂ hP₁_sum hP₂_sum n alpha h_alpha_nn⟩
  · rintro β ⟨s, h_type1, rfl⟩
    -- h_type1 : 1 - ∑_{x∈s} ∏ P₁(x_i) ≤ alpha, i.e. ∑_{x∈s} ∏ P₁(x_i) ≥ 1 - alpha.
    have h_p1_sum_ge : (1 : ℝ) - alpha ≤ ∑ x ∈ s, ∏ i, P₁ (x i) := by linarith
    -- Pointwise: ∏ P₁(x_i) ≤ 1 (since each P₁(x_i) ≤ 1).
    have h_p1_le_one : ∀ x : Fin n → α, ∏ i, P₁ (x i) ≤ 1 := by
      intro x
      -- Each P₁(x_i) ≤ 1 (since ∑ a, P₁ a = 1 and entries ≥ 0).
      refine Finset.prod_le_one ?_ ?_
      · intro i _
        exact (hP₁_pos (x i)).le
      · intro i _
        -- P₁(x_i) ≤ ∑ a, P₁ a = 1.
        have h_single : P₁ (x i) ≤ ∑ a, P₁ a :=
          Finset.single_le_sum (f := P₁) (fun a _ => (hP₁_pos a).le) (Finset.mem_univ _)
        rw [hP₁_sum] at h_single
        exact h_single
    -- So ∑_{x∈s} ∏ P₁ ≤ |s| · 1 = |s|.
    have h_s_card_ge : (1 : ℝ) - alpha ≤ s.card := by
      have h_sum_le : ∑ x ∈ s, ∏ i, P₁ (x i) ≤ ∑ _x ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => h_p1_le_one x)
      rw [Finset.sum_const, Nat.smul_one_eq_cast] at h_sum_le
      linarith
    -- Now: ∑_{x∈s} ∏ P₂(x_i) ≥ ∑_{x∈s} (P₂ a₀)^n = |s| · (P₂ a₀)^n ≥ (1-alpha) · (P₂ a₀)^n.
    have h_p2_pow_le : ∀ x : Fin n → α, (P₂ a₀) ^ n ≤ ∏ i, P₂ (x i) := by
      intro x
      calc (P₂ a₀) ^ n
          = ∏ _i : Fin n, P₂ a₀ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i : Fin n, P₂ (x i) := by
            refine Finset.prod_le_prod (fun i _ => (hP₂_pos a₀).le) (fun i _ => ?_)
            exact ha₀ (x i)
    have h_sum_p2_ge : ∑ x ∈ s, (P₂ a₀) ^ n ≤ ∑ x ∈ s, ∏ i, P₂ (x i) :=
      Finset.sum_le_sum (fun x _ => h_p2_pow_le x)
    -- ∑_{x∈s} (P₂ a₀)^n = |s| · (P₂ a₀)^n.
    rw [Finset.sum_const] at h_sum_p2_ge
    -- s.card • (P₂ a₀)^n = (s.card : ℝ) · (P₂ a₀)^n. Use nsmul_eq_mul.
    simp only [nsmul_eq_mul] at h_sum_p2_ge
    have h_pow_nn : (0 : ℝ) ≤ (P₂ a₀) ^ n := pow_nonneg (hP₂_pos a₀).le _
    have h_mul_le :
        (1 - alpha) * (P₂ a₀) ^ n ≤ (s.card : ℝ) * (P₂ a₀) ^ n :=
      mul_le_mul_of_nonneg_right h_s_card_ge h_pow_nn
    linarith

omit [DecidableEq α] in
/-- The rate sequence is bounded above along `atTop`
under full support + `alpha < 1`. The uniform upper bound is
`M := -log p₂_min - log(1 - alpha) / n`, which is bounded by
`-log p₂_min + |log(1 - alpha)|` for `n ≥ 1`. -/
lemma hoeffding_rate_isBoundedUnder_le
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1) :
    Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ =>
        -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) := by
  classical
  -- Extract p_min := min over a of P₂ a > 0.
  obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image (s := (Finset.univ : Finset α))
    (f := P₂) ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
  set p_min : ℝ := P₂ a₀ with hpmin_def
  have hpmin_pos : 0 < p_min := hP₂_pos a₀
  -- One-α > 0.
  have h_one_minus_alpha_pos : 0 < 1 - alpha := by linarith
  -- M := -log p_min + |log (1 - alpha)|.
  refine Filter.isBoundedUnder_of_eventually_le
    (a := -Real.log p_min + |Real.log (1 - alpha)|) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R
  have hn_one_le : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- Lower bound on steinTypeII via the preceding lemma (same a₀ as outer).
  have h_lower :
      (1 - alpha) * p_min ^ n ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha :=
    steinTypeII_at_level_pmf_ge_pow_pmin P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
      h_alpha_nn h_alpha_lt n (a₀ := a₀) (fun a => ha₀ a (Finset.mem_univ _))
  have h_lb_pos : 0 < (1 - alpha) * p_min ^ n :=
    mul_pos h_one_minus_alpha_pos (pow_pos hpmin_pos n)
  have h_stein_pos : 0 < steinTypeII_at_level_pmf P₁ P₂ n alpha :=
    lt_of_lt_of_le h_lb_pos h_lower
  -- log monotone: log steinTypeII ≥ log((1-alpha) · p_min^n).
  have h_log_ge :
      Real.log ((1 - alpha) * p_min ^ n)
        ≤ Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha) :=
    Real.log_le_log h_lb_pos h_lower
  -- Expand: log((1-alpha) · p_min^n) = log(1-alpha) + n · log p_min.
  have h_log_expand :
      Real.log ((1 - alpha) * p_min ^ n)
        = Real.log (1 - alpha) + (n : ℝ) * Real.log p_min := by
    rw [Real.log_mul h_one_minus_alpha_pos.ne' (pow_pos hpmin_pos n).ne']
    rw [Real.log_pow]
  rw [h_log_expand] at h_log_ge
  -- Multiply by -(1/n) ≤ 0; flips inequality.
  have h_neg_inv_nonpos : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_mul :
      -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha)
        ≤ -((1 : ℝ) / n) * (Real.log (1 - alpha) + (n : ℝ) * Real.log p_min) :=
    mul_le_mul_of_nonpos_left h_log_ge h_neg_inv_nonpos
  -- Simplify RHS: -(1/n) * (log(1-α) + n · log p_min) = -log(1-α)/n - log p_min.
  have h_simp :
      -((1 : ℝ) / n) * (Real.log (1 - alpha) + (n : ℝ) * Real.log p_min)
        = -Real.log (1 - alpha) / n - Real.log p_min := by
    field_simp
    ring
  rw [h_simp] at h_mul
  -- Bound: -log(1-α)/n ≤ |log(1-α)|.
  have h_abs_bound : -Real.log (1 - alpha) / n ≤ |Real.log (1 - alpha)| := by
    -- |x/n| ≤ |x| since 1/n ≤ 1 for n ≥ 1.
    have h_div_abs : |-Real.log (1 - alpha) / n| ≤ |Real.log (1 - alpha)| := by
      rw [abs_div, abs_neg, Nat.abs_cast]
      have h_inv_le : (1 / (n : ℝ)) ≤ 1 := by
        rw [div_le_one hn_R]
        exact hn_one_le
      have h_div_eq : |Real.log (1 - alpha)| / n = |Real.log (1 - alpha)| * (1 / n) := by
        ring
      rw [h_div_eq]
      have h_abs_nn : (0 : ℝ) ≤ |Real.log (1 - alpha)| := abs_nonneg _
      have := mul_le_mul_of_nonneg_left h_inv_le h_abs_nn
      linarith [this]
    exact (le_abs_self _).trans h_div_abs
  -- Conclude: rate ≤ -log(1-α)/n - log p_min ≤ |log(1-α)| + (-log p_min).
  -- Then -log p_min + |log(1-α)| ≥ rate.
  linarith

end InformationTheory.Shannon.HoeffdingSandwich
