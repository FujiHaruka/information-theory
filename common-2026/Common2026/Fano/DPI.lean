import Common2026.Fano
import Common2026.Fano.BinaryJensen
import Common2026.Fano.Core
import Common2026.Meta.EntryPoint
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Data processing inequality (deterministic post-processing)

For a finite joint PMF `P : FiniteJointPMF X Y` and a deterministic
"decoder" `f : Y → X`, the pushforward `P.pushforward f : FiniteJointPMF X X`
has conditional entropy at least as large as the original:

  `P.condEntropy ≤ (P.pushforward f).condEntropy`,  i.e.  `H(X | Y) ≤ H(X | f(Y))`.

This is the deterministic-post-processing case of the data processing
inequality. The proof goes through the log-sum inequality (Jensen on
`Real.negMulLog`) applied per fiber `f⁻¹{xh}`.

The Phase 0 form `decode : Y → X` of Fano's inequality is recovered
downstream by combining DPI with the Phase 1 Markov-form `fano_inequality`.
-/

namespace InformationTheory

open scoped BigOperators
open Finset

noncomputable section

/-! ## Log-sum inequality (negMulLog form) -/

/-- Log-sum inequality, negMulLog form. For finite `ι`, nonneg `a, b : ι → ℝ`
with the absolute-continuity condition `b i = 0 → a i = 0`,

  `∑ (negMulLog (a i) + a i * log (b i))
      ≤ negMulLog (∑ a i) + (∑ a i) * log (∑ b i)`.

This is Jensen's inequality on the concave function `negMulLog`, applied
with weights `b i / ∑ b j` and points `a i / b i`, then translated via
`mul_negMulLog_div`. -/
lemma log_sum_inequality_negMulLog {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (h_ac : ∀ i ∈ s, b i = 0 → a i = 0) :
    ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i))
      ≤ Real.negMulLog (∑ i ∈ s, a i)
          + (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, b i) := by
  set B := ∑ i ∈ s, b i with hB_def
  set A := ∑ i ∈ s, a i with hA_def
  by_cases hB : B = 0
  · -- All b i = 0, hence all a i = 0; both sides are 0.
    have hb_all : ∀ i ∈ s, b i = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hb j hj)).mp hB i hi
    have ha_all : ∀ i ∈ s, a i = 0 := fun i hi => h_ac i hi (hb_all i hi)
    have hA0 : A = 0 := Finset.sum_eq_zero (fun i hi => ha_all i hi)
    have hLHS_zero :
        ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [ha_all i hi, hb_all i hi, Real.negMulLog_zero, Real.log_zero,
        zero_mul, add_zero]
    rw [hLHS_zero, hA0, hB, Real.negMulLog_zero, Real.log_zero, zero_mul,
      add_zero]
  · -- B > 0 case.
    have hB_nn : 0 ≤ B := Finset.sum_nonneg (fun i hi => hb i hi)
    have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB)
    set s' := s.filter (fun i => b i ≠ 0) with hs'_def
    have hs'_subset : s' ⊆ s := Finset.filter_subset _ _
    have hb_pos_on_s' : ∀ i ∈ s', 0 < b i := fun i hi => by
      have hin : i ∈ s := hs'_subset hi
      have hne : b i ≠ 0 := (Finset.mem_filter.mp hi).2
      exact lt_of_le_of_ne (hb i hin) (Ne.symm hne)
    have hbi_zero_outside : ∀ i ∈ s, i ∉ s' → b i = 0 := fun i hi hni => by
      by_contra hbi_ne
      exact hni (Finset.mem_filter.mpr ⟨hi, hbi_ne⟩)
    have ha_zero_outside : ∀ i ∈ s, i ∉ s' → a i = 0 := fun i hi hni =>
      h_ac i hi (hbi_zero_outside i hi hni)
    -- ∑ over s collapses to ∑ over s' for both a and b.
    have hsum_a_s' : (∑ i ∈ s', a i) = A := by
      rw [hA_def]
      exact (Finset.sum_subset hs'_subset (fun i hi hni =>
        ha_zero_outside i hi hni))
    have hsum_b_s' : (∑ i ∈ s', b i) = B := by
      rw [hB_def]
      exact (Finset.sum_subset hs'_subset (fun i hi hni =>
        hbi_zero_outside i hi hni))
    -- Jensen with weights w i = b i / B, points p i = a i / b i (on s').
    have hw_nn : ∀ i ∈ s', 0 ≤ b i / B :=
      fun i hi => div_nonneg (hb_pos_on_s' i hi).le hB_pos.le
    have hw_sum : ∑ i ∈ s', b i / B = 1 := by
      rw [← Finset.sum_div, hsum_b_s', div_self hB]
    have hp_nn : ∀ i ∈ s', 0 ≤ a i / b i :=
      fun i hi => div_nonneg (ha i (hs'_subset hi)) (hb_pos_on_s' i hi).le
    have hjensen :
        ∑ i ∈ s', (b i / B) • Real.negMulLog (a i / b i)
          ≤ Real.negMulLog (∑ i ∈ s', (b i / B) • (a i / b i)) :=
      Real.concaveOn_negMulLog.le_map_sum hw_nn hw_sum (fun i hi => hp_nn i hi)
    -- Simplify Jensen's two sides.
    have hjensen_lhs :
        ∑ i ∈ s', (b i / B) • Real.negMulLog (a i / b i)
          = (1 / B) * ∑ i ∈ s', b i * Real.negMulLog (a i / b i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_eq_mul]
      ring
    have h_inner_sum : (∑ i ∈ s', (b i / B) • (a i / b i)) = A / B := by
      have hpw : ∀ i ∈ s', (b i / B) • (a i / b i) = a i / B := by
        intro i hi
        have hbi_ne : b i ≠ 0 := (Finset.mem_filter.mp hi).2
        rw [smul_eq_mul]
        field_simp
      rw [Finset.sum_congr rfl hpw, ← Finset.sum_div, hsum_a_s']
    rw [hjensen_lhs, h_inner_sum] at hjensen
    -- Multiply Jensen by B (positive scaling) to clear (1/B).
    have h_step1 :
        ∑ i ∈ s', b i * Real.negMulLog (a i / b i) ≤ B * Real.negMulLog (A / B) := by
      have hmul : B * ((1 / B) * ∑ i ∈ s', b i * Real.negMulLog (a i / b i))
                    ≤ B * Real.negMulLog (A / B) :=
        mul_le_mul_of_nonneg_left hjensen hB_pos.le
      have hB1 : B * (1 / B) = 1 := by field_simp
      have heq : B * ((1 / B) * ∑ i ∈ s', b i * Real.negMulLog (a i / b i))
          = ∑ i ∈ s', b i * Real.negMulLog (a i / b i) := by
        rw [← mul_assoc, hB1, one_mul]
      linarith
    -- Translate per-term via mul_negMulLog_div.
    have h_translated_LHS :
        ∑ i ∈ s', b i * Real.negMulLog (a i / b i)
          = ∑ i ∈ s', (Real.negMulLog (a i) + a i * Real.log (b i)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hbi_ne : b i ≠ 0 := (Finset.mem_filter.mp hi).2
      rw [mul_negMulLog_div (b i) (a i) hbi_ne]
    have h_translated_RHS :
        B * Real.negMulLog (A / B) = Real.negMulLog A + A * Real.log B :=
      mul_negMulLog_div B A hB
    -- Extend the LHS sum from s' to s (terms with b i = 0 contribute 0).
    have h_LHS_extend :
        ∑ i ∈ s', (Real.negMulLog (a i) + a i * Real.log (b i))
          = ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i)) := by
      apply Finset.sum_subset hs'_subset
      intro i hi hni
      rw [ha_zero_outside i hi hni, hbi_zero_outside i hi hni,
        Real.negMulLog_zero, Real.log_zero, zero_mul, add_zero]
    calc ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i))
        = ∑ i ∈ s', (Real.negMulLog (a i) + a i * Real.log (b i)) :=
          h_LHS_extend.symm
      _ = ∑ i ∈ s', b i * Real.negMulLog (a i / b i) := h_translated_LHS.symm
      _ ≤ B * Real.negMulLog (A / B) := h_step1
      _ = Real.negMulLog A + A * Real.log B := h_translated_RHS

/-! ## Pushforward of a finite joint PMF -/

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

namespace FiniteJointPMF

/-- Pushforward of a finite joint PMF under a deterministic function `f : Y → Xh`.
The new joint PMF on `(X, Xh)` has mass given by summing over the fiber `f⁻¹{xh}`. -/
def pushforward (P : FiniteJointPMF X Y) (f : Y → X) : FiniteJointPMF X X where
  mass x xh := ∑ y ∈ Finset.univ.filter (fun y => f y = xh), P.mass x y
  mass_nonneg x xh := Finset.sum_nonneg (fun y _ => P.mass_nonneg x y)
  sum_mass := by
    -- ∑ x, ∑ xh, ∑ y in fiber, P.mass x y = ∑ x, ∑ y, P.mass x y = 1
    have hkey : ∀ x, (∑ xh, ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
                        P.mass x y) = ∑ y, P.mass x y := by
      intro x
      exact Finset.sum_fiberwise Finset.univ f (P.mass x)
    rw [Finset.sum_congr rfl (fun x _ => hkey x)]
    exact P.sum_mass

/-- Marginal of the pushforward: `(P.pushforward f).marginalY xh = ∑_{y : f y = xh} P.marginalY y`. -/
lemma pushforward_marginalY (P : FiniteJointPMF X Y) (f : Y → X) (xh : X) :
    (P.pushforward f).marginalY xh
      = ∑ y ∈ Finset.univ.filter (fun y => f y = xh), P.marginalY y := by
  unfold marginalY pushforward
  rw [Finset.sum_comm]

/-! ## DPI: H(X | Y) ≤ H(X | f(Y)) -/

/-- Data processing inequality (deterministic post-processing form):
the conditional entropy of `X` given `Y` does not exceed the conditional
entropy of `X` given `f(Y)`. -/
@[entry_point]
theorem condEntropy_le_pushforward_condEntropy
    (P : FiniteJointPMF X Y) (f : Y → X) :
    P.condEntropy ≤ (P.pushforward f).condEntropy := by
  set Q := P.pushforward f with hQ_def
  -- Marginal of P (summing the source X) is nonneg.
  have h_marg_nn : ∀ y, 0 ≤ P.marginalY y := fun y =>
    Finset.sum_nonneg (fun x _ => P.mass_nonneg x y)
  -- Absolute continuity: P.marginalY y = 0 ⟹ P.mass x y = 0.
  have h_ac_pt : ∀ x y, P.marginalY y = 0 → P.mass x y = 0 := fun x y hb =>
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun x'' _ => P.mass_nonneg x'' y)).mp hb x (Finset.mem_univ _)
  -- Convenience: identification of pushforward.mass with the fiber sum.
  have hQmass : ∀ x xh : X,
      Q.mass x xh = ∑ y ∈ Finset.univ.filter (fun y => f y = xh), P.mass x y :=
    fun _ _ => rfl
  have hQmarg : ∀ xh : X,
      Q.marginalY xh = ∑ y ∈ Finset.univ.filter (fun y => f y = xh), P.marginalY y :=
    fun xh => P.pushforward_marginalY f xh
  -- Per-xh inequality: aggregate of log-sum across fibers.
  have h_per_xh : ∀ xh : X,
      ((∑ x : X, ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
            Real.negMulLog (P.mass x y))
        - ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
            Real.negMulLog (P.marginalY y))
      ≤ ((∑ x : X, Real.negMulLog (Q.mass x xh))
        - Real.negMulLog (Q.marginalY xh)) := by
    intro xh
    set F := Finset.univ.filter (fun y : Y => f y = xh) with hF_def
    -- Per-x log-sum on fiber.
    have h_per_x : ∀ x : X,
        ∑ y ∈ F, (Real.negMulLog (P.mass x y) + P.mass x y * Real.log (P.marginalY y))
        ≤ Real.negMulLog (∑ y ∈ F, P.mass x y)
          + (∑ y ∈ F, P.mass x y) * Real.log (∑ y ∈ F, P.marginalY y) := fun x =>
      log_sum_inequality_negMulLog F (fun y => P.mass x y) (fun y => P.marginalY y)
        (fun y _ => P.mass_nonneg x y)
        (fun y _ => h_marg_nn y)
        (fun y _ hb => h_ac_pt x y hb)
    -- Sum over x.
    have h_sum_x :
        (∑ x : X, ∑ y ∈ F,
            (Real.negMulLog (P.mass x y) + P.mass x y * Real.log (P.marginalY y)))
          ≤ ∑ x : X, (Real.negMulLog (∑ y ∈ F, P.mass x y)
              + (∑ y ∈ F, P.mass x y) * Real.log (∑ y ∈ F, P.marginalY y)) :=
      Finset.sum_le_sum (fun x _ => h_per_x x)
    -- Identification: P.marginalY y * log(P.marginalY y) = -negMulLog(P.marginalY y).
    have hneg_marg : ∀ y, P.marginalY y * Real.log (P.marginalY y)
                          = -Real.negMulLog (P.marginalY y) := fun y => by
      unfold Real.negMulLog; ring
    -- Cross-sum: ∑ x, P.mass x y = P.marginalY y.
    have hcross : ∀ y, (∑ x : X, P.mass x y) = P.marginalY y := fun y => rfl
    -- Simplify LHS.
    have hLHS :
        (∑ x : X, ∑ y ∈ F,
            (Real.negMulLog (P.mass x y) + P.mass x y * Real.log (P.marginalY y)))
          = (∑ x : X, ∑ y ∈ F, Real.negMulLog (P.mass x y))
            - ∑ y ∈ F, Real.negMulLog (P.marginalY y) := by
      have hsplit_inner : ∀ x : X,
          (∑ y ∈ F, (Real.negMulLog (P.mass x y) + P.mass x y * Real.log (P.marginalY y)))
            = (∑ y ∈ F, Real.negMulLog (P.mass x y))
              + ∑ y ∈ F, P.mass x y * Real.log (P.marginalY y) :=
        fun _ => Finset.sum_add_distrib
      rw [Finset.sum_congr rfl (fun x _ => hsplit_inner x), Finset.sum_add_distrib]
      have hswap :
          (∑ x : X, ∑ y ∈ F, P.mass x y * Real.log (P.marginalY y))
            = ∑ y ∈ F, P.marginalY y * Real.log (P.marginalY y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.sum_mul, hcross y]
      rw [hswap, Finset.sum_congr rfl (fun y _ => hneg_marg y),
        Finset.sum_neg_distrib]
      ring
    -- Simplify RHS.
    have hRHS :
        (∑ x : X, (Real.negMulLog (∑ y ∈ F, P.mass x y)
              + (∑ y ∈ F, P.mass x y) * Real.log (∑ y ∈ F, P.marginalY y)))
          = (∑ x : X, Real.negMulLog (Q.mass x xh))
            - Real.negMulLog (Q.marginalY xh) := by
      have h_neg_to_negMul : Q.marginalY xh * Real.log (Q.marginalY xh)
                              = -Real.negMulLog (Q.marginalY xh) := by
        unfold Real.negMulLog; ring
      have hQmass' : ∀ x : X, (∑ y ∈ F, P.mass x y) = Q.mass x xh := fun x =>
        (hQmass x xh).symm
      have hQmarg' : (∑ y ∈ F, P.marginalY y) = Q.marginalY xh :=
        (hQmarg xh).symm
      have hQmarg_via_x : (∑ x : X, Q.mass x xh) = Q.marginalY xh := rfl
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_congr rfl (fun x _ => congrArg Real.negMulLog (hQmass' x)),
        Finset.sum_congr rfl (fun x _ => hQmass' x), hQmarg_via_x, hQmarg',
        h_neg_to_negMul]
      ring
    rw [hLHS, hRHS] at h_sum_x
    exact h_sum_x
  -- Sum h_per_xh over xh and reduce to condEntropy comparison.
  have h_sum_xh : (∑ xh : X,
        ((∑ x : X, ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
              Real.negMulLog (P.mass x y))
          - ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
              Real.negMulLog (P.marginalY y)))
      ≤ ∑ xh : X,
        ((∑ x : X, Real.negMulLog (Q.mass x xh)) - Real.negMulLog (Q.marginalY xh)) :=
    Finset.sum_le_sum (s := (Finset.univ : Finset X))
      (fun xh _ => h_per_xh xh)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h_sum_xh
  -- LHS: ∑ xh, ∑ x, ∑ y in F xh = ∑ x, ∑ y, ... (sum_comm + sum_fiberwise).
  rw [show (∑ xh : X, ∑ x : X, ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
              Real.negMulLog (P.mass x y))
        = ∑ x : X, ∑ y, Real.negMulLog (P.mass x y) by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact Finset.sum_fiberwise Finset.univ f (fun y => Real.negMulLog (P.mass x y))] at h_sum_xh
  rw [show (∑ xh : X, ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
              Real.negMulLog (P.marginalY y))
        = ∑ y, Real.negMulLog (P.marginalY y) from
    Finset.sum_fiberwise Finset.univ f (fun y => Real.negMulLog (P.marginalY y))]
    at h_sum_xh
  -- RHS: ∑ xh, ∑ x, negMulLog(Q.mass x xh) = ∑ x, ∑ xh, ... = Q.jointEntropy.
  rw [show (∑ xh : X, ∑ x : X, Real.negMulLog (Q.mass x xh))
        = ∑ x : X, ∑ xh : X, Real.negMulLog (Q.mass x xh) from Finset.sum_comm]
    at h_sum_xh
  -- Now h_sum_xh has the right shape to match P.condEntropy ≤ Q.condEntropy.
  show P.jointEntropy - P.yEntropy ≤ Q.jointEntropy - Q.yEntropy
  unfold jointEntropy yEntropy
  exact h_sum_xh

/-! ## Compatibility of Markov-form errorProb with the Phase 0 decode form -/

/-- The Markov-form error probability of a pushforward agrees with the
Phase 0 (decoder) error probability. -/
lemma pushforward_errorProb (P : FiniteJointPMF X Y) (f : Y → X) :
    (P.pushforward f).errorProb
      = ∑ x, ∑ y, if x = f y then 0 else P.mass x y := by
  unfold errorProb pushforward
  simp only
  -- LHS = ∑ x, ∑ xh, if x = xh then 0 else ∑ y in fiber, P.mass x y
  -- RHS = ∑ x, ∑ y, if x = f y then 0 else P.mass x y
  refine Finset.sum_congr rfl (fun x _ => ?_)
  -- For each x: ∑ xh, (if x = xh then 0 else ∑ y in fiber, P.mass x y)
  --           = ∑ xh, ∑ y in fiber, (if x = xh then 0 else P.mass x y)
  --           = ∑ xh, ∑ y in fiber, (if x = f y then 0 else P.mass x y)  [in fiber, xh = f y]
  --           = ∑ y, (if x = f y then 0 else P.mass x y)                 [sum_fiberwise]
  have hstep1 : ∀ xh, (if x = xh then (0 : ℝ)
                        else ∑ y ∈ Finset.univ.filter (fun y => f y = xh), P.mass x y)
      = ∑ y ∈ Finset.univ.filter (fun y => f y = xh),
          (if x = f y then (0 : ℝ) else P.mass x y) := by
    intro xh
    by_cases hx : x = xh
    · subst hx
      rw [if_pos rfl]
      symm
      apply Finset.sum_eq_zero
      intro y hy
      have hy' : f y = x := (Finset.mem_filter.mp hy).2
      simp [hy']
    · rw [if_neg hx]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hy' : f y = xh := (Finset.mem_filter.mp hy).2
      have hne : ¬ x = f y := by rw [hy']; exact hx
      rw [if_neg hne]
  rw [Finset.sum_congr rfl (fun xh _ => hstep1 xh)]
  exact Finset.sum_fiberwise Finset.univ f (fun y => if x = f y then 0 else P.mass x y)

/-! ## Phase 0 form recovered from Markov Fano + DPI -/

/-- Phase 0 form of Fano's inequality: for a deterministic decoder
`decode : Y → X`, the Phase 0 conditional-entropy estimate

  `H(X | Y) ≤ binEntropy Pe + Pe * log (|X| - 1)`

with `Pe = ∑ {(x, y) : x ≠ decode y}, P.mass x y`. Derived from the
Markov-form Fano (`fano_inequality` on the pushforward) and the data
processing inequality (`condEntropy_le_pushforward_condEntropy`). -/
@[entry_point]
theorem fano_inequality_decode
    (P : FiniteJointPMF X Y) (decode : Y → X)
    (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X (P.pushforward decode).errorProb := by
  have hDPI := P.condEntropy_le_pushforward_condEntropy decode
  have hFano := (P.pushforward decode).fano_inequality hcard
  linarith

/-- Phase 0 form of Fano's inequality, with the error probability written
in the Phase 0 explicit double-sum form `∑ x, ∑ y, if x = decode y then 0 else P.mass x y`. -/
@[entry_point]
theorem fano_inequality_decode'
    (P : FiniteJointPMF X Y) (decode : Y → X)
    (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X
      (∑ x, ∑ y, if x = decode y then 0 else P.mass x y) := by
  rw [← P.pushforward_errorProb decode]
  exact P.fano_inequality_decode decode hcard

/-- Phase 0 form of the strict inverse Fano bound (`error_lower_bound`)
recovered for a deterministic decoder via DPI. -/
@[entry_point]
theorem error_lower_bound_decode
    (P : FiniteJointPMF X Y) (decode : Y → X)
    (hcard : 2 ≤ Fintype.card X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hPe1 : (P.pushforward decode).errorProb ≤ 1 - 1 / (Fintype.card X : ℝ))
    (haH : Real.qaryEntropy (Fintype.card X) a < P.condEntropy) :
    a < (P.pushforward decode).errorProb := by
  have hDPI := P.condEntropy_le_pushforward_condEntropy decode
  exact (P.pushforward decode).error_lower_bound hcard ha0 ha1 hPe1
    (lt_of_lt_of_le haH hDPI)

end FiniteJointPMF

end

end InformationTheory
