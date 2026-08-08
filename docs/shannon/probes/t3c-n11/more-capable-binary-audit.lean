/-
PROBE — not an in-project asset.  Written by the N11 independent adversarial audit
(`docs/shannon/bc-t3c-n11-audit.md`) to put its own suspicions in front of the compiler
instead of leaving them in prose.

Target of the audit: `InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean`
  * `log_two_mul_binEntropy_binConv_sub_binEntropy_le`  (:379)
  * `binEntropy_binConv_sub_binEntropy_le`              (:392)

What is machine-checked below:

(a) `#print axioms` for both entry points, re-derived by the auditor rather than quoted
    from the implementation report.
(b) Both statements instantiated at concrete numbers — the hypotheses are satisfiable, so
    neither theorem is vacuous.
(c) The inequality is TIGHT: at `x = 2⁻¹` the two sides are equal for every `p`
    (`n11_tight_at_two_inv`).  This is what pins the erasure probability implicit in the
    statement to `h₂(p)` exactly: a statement about any other erasure probability would
    have strict slack there.
(d) The left-hand side is strictly positive on a nonempty region
    (`n11_lhs_pos_of_le_two_inv`), so the conclusion is not of the trivial shape
    "nonnegative ≥ nonpositive".
(e) The hypotheses `0 < p` and `p < 1/2` can be dropped: the statement holds on the whole
    of `p ∈ [0, 1]` (`n11_widen_gt_two_inv`, `n11_widen_two_inv`, `n11_widen_zero`,
    `n11_widen_one`).  The audit's verifier additionally records that the statement FAILS
    for `p` outside `[0,1]`, so `[0,1]` is the honest domain.
(f) The line the implementation report says it did not write: the ticket's candidate form,
    which carries the extra hypothesis `0 ≤ e`, follows from the theorem that was loaded
    (`n11_ticket_candidate_form`).
(g) The two entry points are consistent in both directions: the half-space theorem at the
    boundary erasure probability gives the main theorem back (`n11_main_from_halfspace`).

⚠ SCOPE.  Everything below is about one real-variable inequality.  Nothing here says
anything about rate regions, about the [probc] instance, or about any broadcast channel:
no channel, no region and no support function occurs in this file.
-/
import InformationTheory.Shannon.BroadcastChannel.MoreCapableBinary

open InformationTheory.Shannon.BroadcastChannel

namespace N11AuditProbe

/-! ### (a) axioms -/

#print axioms log_two_mul_binEntropy_binConv_sub_binEntropy_le
#print axioms binEntropy_binConv_sub_binEntropy_le

/-! ### (b) the hypotheses are satisfiable -/

example :
    Real.log 2 * (Real.binEntropy ((3 / 10 : ℝ) * (1 - 1 / 10) + (1 - 3 / 10) * (1 / 10))
        - Real.binEntropy (1 / 10))
      ≤ (Real.log 2 - Real.binEntropy (1 / 10)) * Real.binEntropy (3 / 10 : ℝ) :=
  log_two_mul_binEntropy_binConv_sub_binEntropy_le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example :
    Real.binEntropy ((3 / 10 : ℝ) * (1 - 1 / 10) + (1 - 3 / 10) * (1 / 10))
        - Real.binEntropy (1 / 10)
      ≤ (1 - 0) * Real.binEntropy (3 / 10 : ℝ) :=
  binEntropy_binConv_sub_binEntropy_le (by norm_num) (by norm_num)
    (by simpa using Real.binEntropy_nonneg (by norm_num) (by norm_num)) (by norm_num) (by norm_num)

/-! ### (c) the inequality is tight at `x = 2⁻¹`, which pins the erasure probability -/

theorem n11_tight_at_two_inv (p : ℝ) :
    Real.log 2 * (Real.binEntropy ((2⁻¹ : ℝ) * (1 - p) + (1 - 2⁻¹) * p) - Real.binEntropy p)
      = (Real.log 2 - Real.binEntropy p) * Real.binEntropy (2⁻¹ : ℝ) := by
  have h : (2⁻¹ : ℝ) * (1 - p) + (1 - 2⁻¹) * p = 2⁻¹ := by ring
  rw [h, Real.binEntropy_two_inv]
  ring

/-! ### (d) the left-hand side is strictly positive somewhere -/

theorem n11_lhs_pos_of_le_two_inv {p x : ℝ} (hp₀ : 0 < p) (hp₁ : p < 2⁻¹)
    (hx₀ : 0 < x) (hx₁ : x ≤ 2⁻¹) :
    0 < Real.log 2 * (Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p) := by
  have hlt : p < x * (1 - p) + (1 - x) * p := by nlinarith
  have hmem₁ : p ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨hp₀.le, hp₁.le⟩
  have hmem₂ : x * (1 - p) + (1 - x) * p ∈ Set.Icc (0 : ℝ) 2⁻¹ := ⟨by nlinarith, by nlinarith⟩
  have hmono := Real.binEntropy_strictMonoOn hmem₁ hmem₂ hlt
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := sub_pos.mpr hmono
  positivity

/-! ### (e) the domain of `p` widens to the whole of `[0,1]` -/

theorem n11_widen_gt_two_inv {p x : ℝ} (hp₀ : 2⁻¹ < p) (hp₁ : p < 1)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.log 2 * (Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p)
      ≤ (Real.log 2 - Real.binEntropy p) * Real.binEntropy x := by
  have h := log_two_mul_binEntropy_binConv_sub_binEntropy_le (p := 1 - p) (x := x)
    (by linarith) (by linarith) hx₀ hx₁
  rw [Real.binEntropy_one_sub] at h
  have hc : x * (1 - (1 - p)) + (1 - x) * (1 - p) = 1 - (x * (1 - p) + (1 - x) * p) := by ring
  rw [hc, Real.binEntropy_one_sub] at h
  exact h

theorem n11_widen_two_inv (x : ℝ) :
    Real.log 2 * (Real.binEntropy (x * (1 - 2⁻¹) + (1 - x) * 2⁻¹) - Real.binEntropy (2⁻¹ : ℝ))
      ≤ (Real.log 2 - Real.binEntropy (2⁻¹ : ℝ)) * Real.binEntropy x := by
  have hc : x * (1 - (2⁻¹ : ℝ)) + (1 - x) * 2⁻¹ = 2⁻¹ := by ring
  rw [hc, Real.binEntropy_two_inv]
  simp

theorem n11_widen_zero (x : ℝ) :
    Real.log 2 * (Real.binEntropy (x * (1 - 0) + (1 - x) * 0) - Real.binEntropy (0 : ℝ))
      ≤ (Real.log 2 - Real.binEntropy (0 : ℝ)) * Real.binEntropy x := by
  have hc : x * (1 - (0 : ℝ)) + (1 - x) * 0 = x := by ring
  rw [hc, Real.binEntropy_zero]
  simp

theorem n11_widen_one (x : ℝ) :
    Real.log 2 * (Real.binEntropy (x * (1 - 1) + (1 - x) * 1) - Real.binEntropy (1 : ℝ))
      ≤ (Real.log 2 - Real.binEntropy (1 : ℝ)) * Real.binEntropy x := by
  have hc : x * (1 - (1 : ℝ)) + (1 - x) * 1 = 1 - x := by ring
  rw [hc, Real.binEntropy_one_sub, Real.binEntropy_one]
  simp

/-! ### (f) the ticket's candidate form (the one line the report says it did not write) -/

theorem n11_ticket_candidate_form {p x e : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1 / 2)
    (he₀ : 0 ≤ e) (he : e * Real.log 2 ≤ Real.binEntropy p) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p
      ≤ (1 - e) * Real.binEntropy x :=
  binEntropy_binConv_sub_binEntropy_le hp₀ hp₁ he hx₀ hx₁

/-! ### (g) the main theorem comes back out of the half-space one -/

theorem n11_main_from_halfspace {p x : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1 / 2)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.log 2 * (Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p)
      ≤ (Real.log 2 - Real.binEntropy p) * Real.binEntropy x := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he : (Real.binEntropy p / Real.log 2) * Real.log 2 ≤ Real.binEntropy p := by
    rw [div_mul_cancel₀ _ (ne_of_gt hlog)]
  have h := binEntropy_binConv_sub_binEntropy_le (e := Real.binEntropy p / Real.log 2)
    hp₀ hp₁ he hx₀ hx₁
  have hmul := mul_le_mul_of_nonneg_left h hlog.le
  have hrw : Real.log 2 * ((1 - Real.binEntropy p / Real.log 2) * Real.binEntropy x)
      = (Real.log 2 - Real.binEntropy p) * Real.binEntropy x := by
    field_simp
  linarith [hmul, hrw.le, hrw.ge]

end N11AuditProbe
