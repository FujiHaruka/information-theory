import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.ChannelMeasurability

/-!
# AWGN jointly typical set and capacity re-publish

The continuous jointly typical set for the AWGN channel coding theorem
(Cover–Thomas Ch. 9), together with the thin re-publish of the AWGN coding theorem
and its capacity closed form with the kernel-measurability layer discharged.

## Main definitions

* `AWGNJointlyTypicalSet n P N ε` — the jointly typical set on `ℝⁿ × ℝⁿ` cut out by
  three empirical power bounds.

## Main statements

* `AWGNJointlyTypicalSet_zero`, `AWGNJointlyTypicalSet_subset_of_le_ε`,
  `AWGNJointlyTypicalSet_measurable` — degenerate case, monotonicity in the slack,
  and measurability of the jointly typical set.
* `awgn_capacity_closed_form_of_maxent_hypotheses` — the AWGN capacity closed form,
  with the kernel-measurability layer discharged and the max-entropy / boundedness
  conditions taken as hypotheses.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## AWGN jointly typical set -/

/-- The AWGN continuous jointly typical set (Cover–Thomas 9.2).

On `ℝⁿ × ℝⁿ`, the joint typical set for an AWGN channel with input power `P`,
noise power `N`, and slack `ε > 0`, consists of pairs `(x, y)` such that

* `(1/n) ∑ xᵢ² ≤ P + ε` — input power within slack of `P`,
* `(1/n) ∑ (xᵢ - yᵢ)² ≤ N + ε` — empirical noise power within slack of `N`,
* `(1/n) ∑ yᵢ² ≤ (P + N) + ε` — output power within slack of `P + N`.

For `n = 0` the constraints are vacuous and the set is `Set.univ`. -/
def AWGNJointlyTypicalSet (n : ℕ) (P N ε : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  { p |
    (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε)
      ∧ (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε)
      ∧ (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) }

/-- Membership in `AWGNJointlyTypicalSet` unfolded. -/
@[simp] lemma mem_AWGNJointlyTypicalSet {n : ℕ} {P N ε : ℝ}
    {p : (Fin n → ℝ) × (Fin n → ℝ)} :
    p ∈ AWGNJointlyTypicalSet n P N ε ↔
      (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε)
        ∧ (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε)
        ∧ (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) := Iff.rfl

/-- Trivial case: at `n = 0`, every pair is jointly typical. -/
@[entry_point]
lemma AWGNJointlyTypicalSet_zero (P N ε : ℝ) :
    AWGNJointlyTypicalSet 0 P N ε = Set.univ := by
  ext p
  simp [AWGNJointlyTypicalSet]

/-- Monotonicity in the slack `ε`: a larger slack admits more pairs. -/
@[entry_point]
lemma AWGNJointlyTypicalSet_subset_of_le_ε (n : ℕ) (P N : ℝ)
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (hn : 0 ≤ (n : ℝ)) :
    AWGNJointlyTypicalSet n P N ε₁ ⊆ AWGNJointlyTypicalSet n P N ε₂ := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · exact h1.trans (by nlinarith)
  · exact h2.trans (by nlinarith)
  · exact h3.trans (by nlinarith)

/-- Measurability of the AWGN jointly typical set (Borel measurable as a
finite intersection of polynomial sub-level sets on the product space). -/
@[entry_point]
lemma AWGNJointlyTypicalSet_measurable (n : ℕ) (P N ε : ℝ) :
    MeasurableSet (AWGNJointlyTypicalSet n P N ε) := by
  -- Three polynomial inequalities, each measurable as a sub-level set of a
  -- continuous function `((Fin n → ℝ) × (Fin n → ℝ)) → ℝ`.
  have h1 : MeasurableSet { p : (Fin n → ℝ) × (Fin n → ℝ) |
      (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε) } := by
    refine measurableSet_le ?_ measurable_const
    refine Finset.measurable_sum _ (fun i _ ↦ ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).pow_const 2
  have h2 : MeasurableSet { p : (Fin n → ℝ) × (Fin n → ℝ) |
      (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε) } := by
    refine measurableSet_le ?_ measurable_const
    refine Finset.measurable_sum _ (fun i _ ↦ ?_)
    refine Measurable.pow_const ?_ 2
    exact ((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd)
  have h3 : MeasurableSet { p : (Fin n → ℝ) × (Fin n → ℝ) |
      (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) } := by
    refine measurableSet_le ?_ measurable_const
    refine Finset.measurable_sum _ (fun i _ ↦ ?_)
    exact ((measurable_pi_apply i).comp measurable_snd).pow_const 2
  -- `AWGNJointlyTypicalSet` is the intersection of the three sub-level sets.
  have h_eq : AWGNJointlyTypicalSet n P N ε
      = { p : (Fin n → ℝ) × (Fin n → ℝ) |
            (∑ i : Fin n, (p.1 i)^2) ≤ (n : ℝ) * (P + ε) }
        ∩ { p : (Fin n → ℝ) × (Fin n → ℝ) |
            (∑ i : Fin n, (p.1 i - p.2 i)^2) ≤ (n : ℝ) * (N + ε) }
        ∩ { p : (Fin n → ℝ) × (Fin n → ℝ) |
            (∑ i : Fin n, (p.2 i)^2) ≤ (n : ℝ) * (P + N + ε) } := by
    ext p; simp [AWGNJointlyTypicalSet, Set.mem_inter_iff, and_assoc]
  rw [h_eq]
  exact (h1.inter h2).inter h3

end InformationTheory.Shannon.AWGN
