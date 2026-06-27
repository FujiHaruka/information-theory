import InformationTheory.Fano.BinaryJensen -- mul_negMulLog_div
import InformationTheory.Fano.DPI          -- log_sum_inequality_negMulLog
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.WynerZiv.ObjectiveConvexity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Field

/-!
# Wyner–Ziv conditional-entropy-difference convexity

This file discharges the irreducible Lemma-15.9 core
`WynerZivCondEntDiffConvex` (`WynerZiv/ObjectiveConvexity.lean:212`)
*unconditionally* (only `P_XY ≥ 0`, supplied at rate level by
`P_XY ∈ stdSimplex`).

The core asserts convexity of `H(m_YU) − H(m_XU) = I(X;U|Y)` along convex
combinations of factorisable joints.  The proof routes the whole content
through the per-atom `log_sum_inequality_negMulLog` (`Fano/DPI.lean:44`):

* Step A — affine translation: the marginals of `a•q₁ + b•q₂` are the
  convex combinations of the marginals (`wzMarginalXU_smul_add`,
  `wzMarginalYU_smul_add`).
* Step B — per-`u` block convexity (`wzCondEntDiff_block_convex`): for a
  fixed `u`, the block difference is convex.  The two mixture components
  play the role of the log-sum "fiber".
* Step C/D — `∑_u` aggregation and identification with `wzJointEntYU/XU`
  (`wzCondEntDiff_blockSum_eq_jointEntDiff`), then assembly into the main
  theorem `wynerZivCondEntDiffConvex_holds`, finally re-publishing the
  unconditional rate wrapper.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

variable {α β : Type*}
variable [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-! ## Step A — affine translation of the marginals -/

/-- `wzMarginalXU` is affine in `q`: marginal of the mix = mix of marginals. -/
@[entry_point]
lemma wzMarginalXU_smul_add (a b : ℝ) (q₁ q₂ : α × β × U → ℝ) :
    wzMarginalXU U (a • q₁ + b • q₂)
      = a • wzMarginalXU U q₁ + b • wzMarginalXU U q₂ := by
  funext p
  simp only [wzMarginalXU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- `wzMarginalYU` is affine in `q`. -/
lemma wzMarginalYU_smul_add (a b : ℝ) (q₁ q₂ : α × β × U → ℝ) :
    wzMarginalYU U (a • q₁ + b • q₂)
      = a • wzMarginalYU U q₁ + b • wzMarginalYU U q₂ := by
  funext p
  simp only [wzMarginalYU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ## Step B — per-`u` block convexity (the core) -/

/-- Refinement / coarsening inequality (the DPI core).  For two
non-negative joint slices `r₁, r₂ : α × β → ℝ` and weights `a, b ≥ 0` with
`a + b = 1`, writing the mixture `m = a • r₁ + b • r₂`, the convexity of the
`Y`-marginal-vs-joint entropy gap holds:
`∑_y [neg(∑_x m(x,y)) − a·neg(∑_x r₁(x,y)) − b·neg(∑_x r₂(x,y))]`
  `≤ ∑_y ∑_x [neg(m(x,y)) − a·neg(r₁(x,y)) − b·neg(r₂(x,y))]`.

This is the data-processing inequality for the Jensen–Shannon gap under the
coarsening `(x,y) ↦ y`, proved per `y` by `log_sum_inequality_negMulLog`
with the two mixture components as the log-sum "fiber". -/
lemma negMulLog_marginal_gap_le_joint_gap
    (r₁ r₂ : α × β → ℝ)
    (hr₁ : ∀ p, 0 ≤ r₁ p) (hr₂ : ∀ p, 0 ≤ r₂ p)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (∑ y, (Real.negMulLog (∑ x, (a * r₁ (x, y) + b * r₂ (x, y)))
            - a * Real.negMulLog (∑ x, r₁ (x, y))
            - b * Real.negMulLog (∑ x, r₂ (x, y))))
      ≤ ∑ y, ∑ x, (Real.negMulLog (a * r₁ (x, y) + b * r₂ (x, y))
            - a * Real.negMulLog (r₁ (x, y))
            - b * Real.negMulLog (r₂ (x, y))) := by
  refine Finset.sum_le_sum (fun y _ ↦ ?_)
  -- Per `y`, set `m(x) = a r₁(x,y) + b r₂(x,y)`; the inequality is
  -- `a·(R1) + b·(R2)` of the log-sum inequality (denominator `m`), negated.
  set m : α → ℝ := fun x ↦ a * r₁ (x, y) + b * r₂ (x, y) with hm_def
  have hm_nn : ∀ x, 0 ≤ m x := fun x ↦
    add_nonneg (mul_nonneg ha (hr₁ (x, y))) (mul_nonneg hb (hr₂ (x, y)))
  -- The summed `r₁`/`r₂`/`m` over `x`.
  set S₁ : ℝ := ∑ x, r₁ (x, y) with hS₁
  set S₂ : ℝ := ∑ x, r₂ (x, y) with hS₂
  set Sm : ℝ := ∑ x, m x with hSm
  -- A log-sum application with denominator `m`, valid when the weight `w` is
  -- positive (so `w·r ≤ m` supplies absolute continuity).
  have key_R : ∀ (r : α → ℝ), (∀ x, 0 ≤ r x) → ∀ (w : ℝ), 0 < w →
      (∀ x, w * r x ≤ m x) →
      (∑ x, (Real.negMulLog (r x) + r x * Real.log (m x)))
        ≤ Real.negMulLog (∑ x, r x)
            + (∑ x, r x) * Real.log (∑ x, m x) := by
    intro r hr w hw hwle
    refine log_sum_inequality_negMulLog Finset.univ r (fun x ↦ m x)
      (fun x _ ↦ hr x) (fun x _ ↦ hm_nn x) (fun x _ hmx ↦ ?_)
    have hwr0 : w * r x ≤ 0 := by have := hwle x; rwa [hmx] at this
    have hwr_nn : 0 ≤ w * r x := mul_nonneg hw.le (hr x)
    have : w * r x = 0 := le_antisymm hwr0 hwr_nn
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hw)
  -- Pointwise: `a·r₁·log m + b·r₂·log m = m·log m`, and `m·log m = -neg m`.
  have hmix_log : ∀ x,
      a * (r₁ (x, y) * Real.log (m x)) + b * (r₂ (x, y) * Real.log (m x))
        = - Real.negMulLog (m x) := by
    intro x
    have : a * (r₁ (x, y) * Real.log (m x)) + b * (r₂ (x, y) * Real.log (m x))
            = m x * Real.log (m x) := by rw [hm_def]; ring
    rw [this]; unfold Real.negMulLog; ring
  -- Build `a·R1 + b·R2` for whichever weights are positive (and `0` for the
  -- zero weight), then negate to obtain the per-`y` goal.
  -- LHS-after-combine: ∑_x [a·neg(r₁) + b·neg(r₂) - neg(m)].
  -- RHS-after-combine: a·neg(S₁) + b·neg(S₂) - neg(Sm).
  have hcombine :
      (∑ x, (a * Real.negMulLog (r₁ (x, y)) + b * Real.negMulLog (r₂ (x, y))
              - Real.negMulLog (m x)))
        ≤ a * Real.negMulLog S₁ + b * Real.negMulLog S₂ - Real.negMulLog Sm := by
    -- `Sm = a·S₁ + b·S₂` and `Sm·log Sm = -neg Sm`, mirroring `hmix_log`.
    have hSm_eq : Sm = a * S₁ + b * S₂ := by
      rw [hSm, hS₁, hS₂, hm_def, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    have hSm_log : a * (S₁ * Real.log Sm) + b * (S₂ * Real.log Sm)
                    = - Real.negMulLog Sm := by
      have : a * (S₁ * Real.log Sm) + b * (S₂ * Real.log Sm)
              = Sm * Real.log Sm := by rw [hSm_eq]; ring
      rw [this]; unfold Real.negMulLog; ring
    -- Assemble from the (possibly zero-weighted) log-sum bounds.
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- a = 0, so b = 1, m = r₂.
      have ha0' : a = 0 := ha0.symm
      have hb1 : b = 1 := by linarith
      have hmr : ∀ x, m x = r₂ (x, y) := fun x ↦ by rw [hm_def]; simp [ha0', hb1]
      have hSmS₂ : Sm = S₂ := by
        rw [hSm, hS₂]; exact Finset.sum_congr rfl (fun x _ ↦ hmr x)
      rw [ha0', hb1, hSmS₂]
      apply le_of_eq
      refine (Finset.sum_eq_zero (fun x _ ↦ ?_)).trans ?_
      · rw [hmr x]; ring
      · ring
    · rcases eq_or_lt_of_le hb with hb0 | hbpos
      · -- b = 0, a = 1, m = r₁.
        have hb0' : b = 0 := hb0.symm
        have ha1 : a = 1 := by linarith
        have hmr : ∀ x, m x = r₁ (x, y) := fun x ↦ by rw [hm_def]; simp [hb0', ha1]
        have hSmS₁ : Sm = S₁ := by
          rw [hSm, hS₁]; exact Finset.sum_congr rfl (fun x _ ↦ hmr x)
        rw [ha1, hb0', hSmS₁]
        apply le_of_eq
        refine (Finset.sum_eq_zero (fun x _ ↦ ?_)).trans ?_
        · rw [hmr x]; ring
        · ring
      · -- a, b > 0: combine the two log-sum bounds linearly.
        have hR1 := key_R (fun x ↦ r₁ (x, y)) (fun x ↦ hr₁ (x, y)) a hapos
          (fun x ↦ by rw [hm_def]; nlinarith [mul_nonneg hb (hr₂ (x, y))])
        have hR2 := key_R (fun x ↦ r₂ (x, y)) (fun x ↦ hr₂ (x, y)) b hbpos
          (fun x ↦ by rw [hm_def]; nlinarith [mul_nonneg ha (hr₁ (x, y))])
        -- a·hR1 + b·hR2.
        have hsum := add_le_add (mul_le_mul_of_nonneg_left hR1 ha)
          (mul_le_mul_of_nonneg_left hR2 hb)
        -- Rewrite LHS of hsum into ∑_x [a·neg r₁ + b·neg r₂ - neg m].
        have hLHS :
            a * (∑ x, (Real.negMulLog (r₁ (x, y)) + r₁ (x, y) * Real.log (m x)))
              + b * (∑ x, (Real.negMulLog (r₂ (x, y)) + r₂ (x, y) * Real.log (m x)))
            = ∑ x, (a * Real.negMulLog (r₁ (x, y)) + b * Real.negMulLog (r₂ (x, y))
                    - Real.negMulLog (m x)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun x _ ↦ ?_)
          have := hmix_log x
          nlinarith [this]
        -- Rewrite RHS of hsum into a·neg S₁ + b·neg S₂ - neg Sm.
        have hRHS :
            a * (Real.negMulLog (∑ x, r₁ (x, y))
                  + (∑ x, r₁ (x, y)) * Real.log (∑ x, m x))
              + b * (Real.negMulLog (∑ x, r₂ (x, y))
                  + (∑ x, r₂ (x, y)) * Real.log (∑ x, m x))
            = a * Real.negMulLog S₁ + b * Real.negMulLog S₂ - Real.negMulLog Sm := by
          rw [← hS₁, ← hS₂, ← hSm]
          have := hSm_log
          nlinarith [this]
        rw [hLHS, hRHS] at hsum
        exact hsum
  -- Negate `hcombine` into the per-`y` goal.
  have hgoal := neg_le_neg hcombine
  -- Rewrite both sides of the negated inequality into the goal shape.
  have hL : -(a * Real.negMulLog S₁ + b * Real.negMulLog S₂ - Real.negMulLog Sm)
      = Real.negMulLog (∑ x, (a * r₁ (x, y) + b * r₂ (x, y)))
        - a * Real.negMulLog (∑ x, r₁ (x, y))
        - b * Real.negMulLog (∑ x, r₂ (x, y)) := by
    rw [hS₁, hS₂, hSm, hm_def]; ring
  have hR : -(∑ x, (a * Real.negMulLog (r₁ (x, y)) + b * Real.negMulLog (r₂ (x, y))
              - Real.negMulLog (m x)))
      = ∑ x, (Real.negMulLog (a * r₁ (x, y) + b * r₂ (x, y))
              - a * Real.negMulLog (r₁ (x, y))
              - b * Real.negMulLog (r₂ (x, y))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [hm_def]; ring
  rw [hL, hR] at hgoal
  exact hgoal


/-- Per-`u` block convexity.  For factorisable `q₁, q₂` and weights
`a, b ≥ 0` with `a + b = 1`, the conditional-entropy-difference block at a
fixed `u`,
`(∑_y negMulLog m_YU(y,u)) − (∑_x negMulLog m_XU(x,u))`, is convex. -/
lemma wzCondEntDiff_block_convex
    (P_XY : α × β → ℝ) (h_pmf_nn : ∀ p, 0 ≤ P_XY p)
    {q₁ q₂ : α × β × U → ℝ}
    (hq₁ : IsWynerZivFactorizable U P_XY q₁)
    (hq₂ : IsWynerZivFactorizable U P_XY q₂)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (u : U) :
    ((∑ y, Real.negMulLog (wzMarginalYU U (a • q₁ + b • q₂) (y, u)))
        - ∑ x, Real.negMulLog (wzMarginalXU U (a • q₁ + b • q₂) (x, u)))
      ≤ a * ((∑ y, Real.negMulLog (wzMarginalYU U q₁ (y, u)))
              - ∑ x, Real.negMulLog (wzMarginalXU U q₁ (x, u)))
        + b * ((∑ y, Real.negMulLog (wzMarginalYU U q₂ (y, u)))
              - ∑ x, Real.negMulLog (wzMarginalXU U q₂ (x, u))) := by
  obtain ⟨κ₁, hκ₁nn, _hκ₁sum, hκ₁eq⟩ := hq₁
  obtain ⟨κ₂, hκ₂nn, _hκ₂sum, hκ₂eq⟩ := hq₂
  -- Pointwise nonnegativity of the joint slices.
  have hq₁nn : ∀ p, 0 ≤ q₁ p := fun ⟨x, y, u'⟩ ↦ by
    rw [hκ₁eq x y u']; exact mul_nonneg (hκ₁nn x u') (h_pmf_nn (x, y))
  have hq₂nn : ∀ p, 0 ≤ q₂ p := fun ⟨x, y, u'⟩ ↦ by
    rw [hκ₂eq x y u']; exact mul_nonneg (hκ₂nn x u') (h_pmf_nn (x, y))
  -- Slices `r_i (x, y) = q_i (x, y, u)`.
  set r₁ : α × β → ℝ := fun p ↦ q₁ (p.1, p.2, u) with hr₁_def
  set r₂ : α × β → ℝ := fun p ↦ q₂ (p.1, p.2, u) with hr₂_def
  have hr₁nn : ∀ p, 0 ≤ r₁ p := fun p ↦ hq₁nn _
  have hr₂nn : ∀ p, 0 ≤ r₂ p := fun p ↦ hq₂nn _
  -- Marginal identifications.
  have hYU_mix : ∀ y, wzMarginalYU U (a • q₁ + b • q₂) (y, u)
      = ∑ x, (a * r₁ (x, y) + b * r₂ (x, y)) := by
    intro y
    rw [wzMarginalYU_smul_add]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wzMarginalYU,
      hr₁_def, hr₂_def]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hYU₁ : ∀ y, wzMarginalYU U q₁ (y, u) = ∑ x, r₁ (x, y) := fun y ↦ rfl
  have hYU₂ : ∀ y, wzMarginalYU U q₂ (y, u) = ∑ x, r₂ (x, y) := fun y ↦ rfl
  -- The refinement (DPI) inequality: (I)_u ≤ joint-gap.
  have hrefine := negMulLog_marginal_gap_le_joint_gap r₁ r₂ hr₁nn hr₂nn a b ha hb hab
  -- Part 1 (factorisation): joint-gap (per x, summed over y) = XU-block-gap.
  -- For each x: ∑_y [neg(m(x,y)) - a·neg r₁ - b·neg r₂]
  --   = neg(m_XU(x,u)) - a·neg(q₁_XU(x,u)) - b·neg(q₂_XU(x,u)).
  have hpart1 : ∀ x,
      (∑ y, (Real.negMulLog (a * r₁ (x, y) + b * r₂ (x, y))
              - a * Real.negMulLog (r₁ (x, y))
              - b * Real.negMulLog (r₂ (x, y))))
        = Real.negMulLog (wzMarginalXU U (a • q₁ + b • q₂) (x, u))
            - a * Real.negMulLog (wzMarginalXU U q₁ (x, u))
            - b * Real.negMulLog (wzMarginalXU U q₂ (x, u)) := by
    intro x
    -- Kernel weights at this `x`, `u`, and the source marginal `P_X(x)`.
    set c₁ := κ₁ x u with hc₁
    set c₂ := κ₂ x u with hc₂
    set PX : ℝ := ∑ y, P_XY (x, y) with hPX
    -- The common scalar Jensen gap of `negMulLog` at the kernel weights.
    set γ : ℝ := Real.negMulLog (a * c₁ + b * c₂)
                  - a * Real.negMulLog c₁ - b * Real.negMulLog c₂ with hγ
    -- Slice values factor through `P_XY`.
    have hr₁fac : ∀ y, r₁ (x, y) = c₁ * P_XY (x, y) := fun y ↦ by
      rw [hr₁_def]; exact hκ₁eq x y u
    have hr₂fac : ∀ y, r₂ (x, y) = c₂ * P_XY (x, y) := fun y ↦ by
      rw [hr₂_def]; exact hκ₂eq x y u
    -- Each summand factors as `P_XY(x,y) · γ` via `negMulLog_mul`.
    have hsummand : ∀ y,
        (Real.negMulLog (a * r₁ (x, y) + b * r₂ (x, y))
            - a * Real.negMulLog (r₁ (x, y)) - b * Real.negMulLog (r₂ (x, y)))
          = P_XY (x, y) * γ := by
      intro y
      rw [hr₁fac y, hr₂fac y]
      have hmix : a * (c₁ * P_XY (x, y)) + b * (c₂ * P_XY (x, y))
                    = (a * c₁ + b * c₂) * P_XY (x, y) := by ring
      rw [hmix, Real.negMulLog_mul, Real.negMulLog_mul, Real.negMulLog_mul, hγ]
      ring
    -- LHS: ∑_y P_XY(x,y) · γ = P_X(x) · γ.
    rw [Finset.sum_congr rfl (fun y _ ↦ hsummand y), ← Finset.sum_mul, ← hPX]
    -- RHS: each XU marginal factors as kernel · P_X(x); reduce via negMulLog_mul.
    have hmXU : wzMarginalXU U (a • q₁ + b • q₂) (x, u) = (a * c₁ + b * c₂) * PX := by
      simp only [wzMarginalXU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hPX, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ ↦ ?_)
      rw [hκ₁eq x y u, hκ₂eq x y u]; ring
    have hq₁XU : wzMarginalXU U q₁ (x, u) = c₁ * PX := by
      simp only [wzMarginalXU]
      rw [hPX, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ ↦ hκ₁eq x y u)
    have hq₂XU : wzMarginalXU U q₂ (x, u) = c₂ * PX := by
      simp only [wzMarginalXU]
      rw [hPX, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ ↦ hκ₂eq x y u)
    rw [hmXU, hq₁XU, hq₂XU, Real.negMulLog_mul, Real.negMulLog_mul,
      Real.negMulLog_mul, hγ]
    ring
  -- XU side of the block goal, rewritten via Part 1.
  have hjointgap_eq :
      (∑ y, ∑ x, (Real.negMulLog (a * r₁ (x, y) + b * r₂ (x, y))
              - a * Real.negMulLog (r₁ (x, y))
              - b * Real.negMulLog (r₂ (x, y))))
        = (∑ x, Real.negMulLog (wzMarginalXU U (a • q₁ + b • q₂) (x, u)))
            - a * ∑ x, Real.negMulLog (wzMarginalXU U q₁ (x, u))
            - b * ∑ x, Real.negMulLog (wzMarginalXU U q₂ (x, u)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x _ ↦ hpart1 x)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.mul_sum]
  -- The refinement LHS `(I)_u`, expanded into the goal's YU terms.
  have hI_eq :
      (∑ y, (Real.negMulLog (∑ x, (a * r₁ (x, y) + b * r₂ (x, y)))
              - a * Real.negMulLog (∑ x, r₁ (x, y))
              - b * Real.negMulLog (∑ x, r₂ (x, y))))
        = (∑ y, Real.negMulLog (wzMarginalYU U (a • q₁ + b • q₂) (y, u)))
            - a * (∑ y, Real.negMulLog (wzMarginalYU U q₁ (y, u)))
            - b * (∑ y, Real.negMulLog (wzMarginalYU U q₂ (y, u))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.mul_sum]
    refine congrArg₂ (· - ·) (congrArg₂ (· - ·) ?_ ?_) ?_
    · exact Finset.sum_congr rfl (fun y _ ↦ by rw [hYU_mix y])
    · exact Finset.sum_congr rfl (fun y _ ↦ by rw [hYU₁ y])
    · exact Finset.sum_congr rfl (fun y _ ↦ by rw [hYU₂ y])
  -- Combine: (I)_u ≤ jointgap = XU-block-combo, then linarith.
  rw [hI_eq, hjointgap_eq] at hrefine
  linarith [hrefine]

/-! ## Step C/D — `∑_u` aggregation + identification with joint blocks -/

/-- The `∑_u` of the per-`u` block differences equals
`wzJointEntYU − wzJointEntXU`. -/
lemma wzCondEntDiff_blockSum_eq_jointEntDiff (q : α × β × U → ℝ) :
    (∑ u, ((∑ y, Real.negMulLog (wzMarginalYU U q (y, u)))
            - ∑ x, Real.negMulLog (wzMarginalXU U q (x, u))))
      = wzJointEntYU U q - wzJointEntXU U q := by
  rw [Finset.sum_sub_distrib]
  unfold wzJointEntYU wzJointEntXU
  rw [Fintype.sum_prod_type (f := fun p : β × U ↦ Real.negMulLog (wzMarginalYU U q p)),
      Fintype.sum_prod_type (f := fun p : α × U ↦ Real.negMulLog (wzMarginalXU U q p))]
  rw [Finset.sum_comm
        (f := fun u y ↦ Real.negMulLog (wzMarginalYU U q (y, u))),
      Finset.sum_comm
        (f := fun u x ↦ Real.negMulLog (wzMarginalXU U q (x, u)))]

/-! ## Main theorem — unconditional discharge of the core -/

/-- Lemma-15.9 core, discharged.  `WynerZivCondEntDiffConvex` holds for
every non-negative `P_XY`. -/
@[entry_point]
theorem wynerZivCondEntDiffConvex_holds
    (P_XY : α × β → ℝ) (h_pmf_nn : ∀ p, 0 ≤ P_XY p) :
    WynerZivCondEntDiffConvex U P_XY := by
  intro q₁ q₂ hq₁ hq₂ a b ha hb hab
  -- Rewrite the three joint-entropy differences into `∑_u` block form.
  rw [← wzCondEntDiff_blockSum_eq_jointEntDiff U (a • q₁ + b • q₂),
      ← wzCondEntDiff_blockSum_eq_jointEntDiff U q₁,
      ← wzCondEntDiff_blockSum_eq_jointEntDiff U q₂]
  -- Distribute the `a •`, `b •` and the sum over `u` on the RHS.
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- Aggregate the per-`u` block convexity.
  refine Finset.sum_le_sum (fun u _ ↦ ?_)
  exact wzCondEntDiff_block_convex U P_XY h_pmf_nn hq₁ hq₂ a b ha hb hab u

/-! ## Unconditional rate-level convexity wrapper -/

/-- Convexity of the factorizable rate function in `D`, with the
objective-convexity hypothesis fully discharged. -/
@[entry_point]
theorem wynerZivRateFactorizable_convex_in_D_unconditional
    {γ : Type*}
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (f : U × β → γ)
    {D₁ D₂ : ℝ}
    {q₁ q₂ : α × β × U → ℝ}
    (h_feasible₁ : (q₁, f) ∈ WynerZivFactorizableConstraint U P_XY d D₁)
    (h_feasible₂ : (q₂, f) ∈ WynerZivFactorizableConstraint U P_XY d D₂)
    (h_attain₁ : wynerZivRateFactorizable U P_XY d D₁
                  = wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
    (h_attain₂ : wynerZivRateFactorizable U P_XY d D₂
                  = wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    wynerZivRateFactorizable U P_XY d (a * D₁ + b * D₂)
      ≤ a * wynerZivRateFactorizable U P_XY d D₁
        + b * wynerZivRateFactorizable U P_XY d D₂ := by
  classical
  exact wynerZivRateFactorizable_convex_in_D_of_condEntDiff U h_pmf d f
    (wynerZivCondEntDiffConvex_holds U P_XY h_pmf.1)
    h_feasible₁ h_feasible₂ h_attain₁ h_attain₂ ha hb hab

end InformationTheory.Shannon
