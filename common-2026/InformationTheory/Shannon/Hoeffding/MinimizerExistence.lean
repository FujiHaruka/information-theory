import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Hoeffding.Tradeoff
import InformationTheory.Shannon.Hoeffding.Sandwich
import InformationTheory.Shannon.Hoeffding.BoundaryMinimizer
import InformationTheory.Shannon.Hoeffding.InteriorMinimizer
import InformationTheory.Shannon.Hoeffding.Tilt
import InformationTheory.Shannon.Hoeffding.MinimizerAttainment
import InformationTheory.Shannon.Chernoff.Basic
import InformationTheory.Shannon.CsiszarProjection
import InformationTheory.Shannon.Sanov.LDPEquality
import InformationTheory.Shannon.StrongStein
import InformationTheory.Shannon.KLDivContinuous
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Hoeffding tradeoff — sandwich discharge

This file publishes the constructive full-support minimizer of `klDivPmf · P₂`
on the constraint set and the boundary achievability inequality.

## Approach — constructive 3-case minimizer

`exists_hoeffding_minimizer_full_support` supplies an explicit full-support
minimizer `Qstar` of `klDivPmf · P₂` on the constraint set, branching on `alpha`:

* `alpha = 0`   : `Qstar = P₁`            (singleton constraint set)
* `0 < alpha ≤ klDivPmf P₂ P₁` : `Qstar = hoeffdingTilt P₁ P₂ lam`  (IVT tilt)
* `klDivPmf P₂ P₁ ≤ alpha`     : `Qstar = P₂`            (boundary collapse)

All three cases are constructive, so `Qstar` full support is constructive — the
abstract log-singularity gradient argument is avoided.
-/

namespace InformationTheory.Shannon.HoeffdingMinimizerExistence

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingTilt
open InformationTheory.Shannon.HoeffdingMinimizerAttainment
open InformationTheory.Shannon.HoeffdingBoundaryMinimizer
open scoped BigOperators Topology ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Constructive full-support minimizer (3-case) -/

omit [DecidableEq α] in
/-- **Constructive 3-case minimizer**: an explicit full-support `Qstar` realising
`hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂`, with `Qstar ∈ K`. -/
lemma exists_hoeffding_minimizer_full_support
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ ∧ (∀ a, 0 < Qstar a) := by
  classical
  rcases eq_or_lt_of_le h_alpha_nn with h_alpha0 | h_alpha_pos
  · -- case (a) alpha = 0: Qstar = P₁, K = {P₁}, E2 = 0 = klDivPmf P₁ P₁.
    subst h_alpha0
    refine ⟨P₁, ?_, ?_, hP₁_pos⟩
    · -- P₁ ∈ K (klDivPmf P₁ P₁ = 0 ≤ 0).
      refine ⟨⟨fun a => (hP₁_pos a).le, hP₁_sum⟩, ?_⟩
      rw [klDivPmf_self_eq_zero P₁ hP₁_pos]
    · -- hoeffdingE2 P₁ P₂ 0 = klDivPmf P₁ P₂: K = {P₁} forces the infimum.
      have h_singleton : hoeffdingConstraintSet P₁ (0 : ℝ) = {P₁} :=
        hoeffdingConstraintSet_eq_singleton_at_alpha_zero P₁ hP₁_pos hP₁_sum
      -- hoeffdingE2 = sInf over image = klDivPmf P₁ P₂.
      unfold hoeffdingE2
      have h_set_eq : {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ (0 : ℝ)}
          = hoeffdingConstraintSet P₁ (0 : ℝ) := rfl
      rw [h_set_eq, h_singleton]
      rw [Set.image_singleton, csInf_singleton]
  · -- 0 < alpha: branch on interior vs boundary.
    rcases le_or_gt alpha (klDivPmf P₂ P₁) with h_alpha_le | h_alpha_gt
    · -- case (b) interior 0 < alpha ≤ klDivPmf P₂ P₁: Qstar = tilt.
      obtain ⟨lam, _hlam_Ioc, h_lag⟩ :=
        exists_isHoeffdingLagrangeHyp_interior P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
          h_alpha_pos h_alpha_le
      exact ⟨hoeffdingTilt P₁ P₂ lam, h_lag.mem, h_lag.realises,
        hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam⟩
    · -- case (c) boundary klDivPmf P₂ P₁ < alpha: Qstar = P₂.
      obtain ⟨Qstar, hQs_mem, hQs_min, hQs_full⟩ :=
        hoeffdingE2_minimizer_at_boundary_alpha_ge_kl P₁ P₂ hP₁_pos hP₂_pos
          hP₁_sum hP₂_sum h_alpha_nn h_alpha_gt.le
      exact ⟨Qstar, hQs_mem, hQs_min, hQs_full.pos⟩

/-! ## Achievability `E2 ≤ liminf rate` on the boundary regime

The achievability inequality `hoeffdingE2 P₁ P₂ alpha ≤ liminf rate` holds
**unconditionally on the boundary regime** `klDivPmf P₂ P₁ ≤ alpha`, where
`hoeffdingE2 = 0` (`hoeffdingE2_eq_zero_at_alpha_ge_kl`) and the inequality reduces
to `0 ≤ liminf rate`, i.e. the rate is non-negative (`steinTypeII ≤ 1 ⇒ log ≤ 0`).
Outside the boundary it is *not* generally true — see the analysis below (it fails
at `alpha = 0`, where `E₂(0) = D(P₁‖P₂) > 0 = liminf rate`). -/

omit [DecidableEq α] in
/-- **achievability at the boundary** (`klDivPmf P₂ P₁ ≤ alpha`, fully
unconditional): there `hoeffdingE2 = 0 ≤ liminf rate`, since the rate is
non-negative. -/
@[entry_point]
theorem hoeffding_tradeoff_achievability_at_boundary
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1)
    (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha) :
    hoeffdingE2 P₁ P₂ alpha ≤
      Filter.liminf (fun n : ℕ =>
        -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha)) atTop := by
  classical
  -- E2 = 0 on the boundary.
  rw [hoeffdingE2_eq_zero_at_alpha_ge_kl P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
    h_alpha_nn h_alpha_ge]
  -- 0 ≤ liminf rate, via rate ≥ 0 eventually + the upper boundedness coboundedness.
  refine Filter.le_liminf_of_le ?_ ?_
  · -- IsCoboundedUnder (· ≥ ·): follows from boundedness above.
    exact (HoeffdingSandwich.hoeffding_rate_isBoundedUnder_le P₁ P₂ hP₁_pos hP₂_pos
      hP₁_sum hP₂_sum h_alpha_nn h_alpha_lt).isCoboundedUnder_ge
  · -- rate n ≥ 0 eventually.
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h_le_one : steinTypeII_at_level_pmf P₁ P₂ n alpha ≤ 1 :=
      steinTypeII_at_level_pmf_le_one P₁ P₂ hP₁_sum hP₂_sum (fun a => (hP₂_pos a).le) n alpha
        h_alpha_nn
    have h_nn : 0 ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha :=
      steinTypeII_at_level_pmf_nonneg P₁ P₂ hP₁_sum hP₂_sum (fun a => (hP₂_pos a).le) n alpha
        h_alpha_nn
    have h_log_le : Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha) ≤ 0 := by
      rcases eq_or_lt_of_le h_nn with h_zero | h_pos
      · rw [← h_zero, Real.log_zero]
      · exact Real.log_nonpos h_pos.le h_le_one
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_neg_inv_nonpos : -((1 : ℝ) / n) ≤ 0 := by
      have : (0 : ℝ) ≤ 1 / n := by positivity
      linarith
    exact mul_nonneg_iff.mpr (Or.inr ⟨h_neg_inv_nonpos, h_log_le⟩)

/-! ## The fixed-`alpha` rate does not target the Hoeffding tradeoff curve

A fixed-`alpha` `Tendsto rate → hoeffdingE2 P₁ P₂ alpha` does **not** hold:
`steinTypeII_at_level_pmf` bakes in a *constant* Type-I level `alpha`, whereas
the Hoeffding tradeoff curve `E₂(alpha)` is the limit only in the
**exponential-level** regime `alpha_n = exp(-n r)`. The fixed-`alpha` rate
`-(1/n) log steinTypeII_at_level_pmf` converges to `D(P₁‖P₂)`, *not* `E₂(alpha)`.
Two concrete contradictions:

* **`alpha = 0`**: with full-support `P₁`, the only Type-I-exact-`0` test is
  `s = univ` (every other `Finset` has `∑ ∏ P₁ < 1`), so
  `steinTypeII_at_level_pmf P₁ P₂ n 0 = 1` and `rate n ≡ 0`. But
  `hoeffdingE2 P₁ P₂ 0 = klDivPmf P₁ P₂ = D(P₁‖P₂) > 0` in general. So
  `rate → 0 ≠ E₂(0)`.

* **`0 < alpha < 1`**: `steinTypeII_at_level_pmf P₁ P₂ n alpha`
  coincides with `steinOptimalBeta (pmfToMeasure P₁) (pmfToMeasure P₂) n alpha`
  (the pmf and measure β-sets agree on the finite alphabet), so by Stein's lemma
  `rate n → D(P₁‖P₂) = E₂(0) > E₂(alpha)`.

Consequences for the two variational inequalities:

* **achievability** `hoeffdingE2 alpha ≤ liminf rate`: holds whenever
  `E₂(alpha) ≤ liminf rate`. On the **boundary** `klDivPmf P₂ P₁ ≤ alpha` we have
  `E₂(alpha) = 0 ≤ liminf rate` unconditionally
  (`hoeffding_tradeoff_achievability_at_boundary` above). At `alpha = 0` it is
  *false* (`E₂(0) = D > 0 = liminf rate`).
* **converse** `limsup rate ≤ hoeffdingE2 alpha`: would require
  `limsup rate ≤ E₂(alpha)`, contradicted at every `alpha` by the limits above.

The genuine statement of the tradeoff is the exponential-level
`hoeffding_tradeoff_exp` (`HoeffdingTradeoffExp.lean`). This file's two
declarations — the constructive minimizer `exists_hoeffding_minimizer_full_support`
(consumed by `HoeffdingTradeoffExp.lean`) and the boundary achievability
`hoeffding_tradeoff_achievability_at_boundary` — are both genuine. -/

end InformationTheory.Shannon.HoeffdingMinimizerExistence
