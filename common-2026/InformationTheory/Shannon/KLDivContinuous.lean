import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Sanov.LDP
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Monoid

/-!
# KL divergence in vector form and its continuity

`klDivSumForm_ofVec p q := ∑ a, p a * (log (p a) - log (q a))` and its continuity in `p`
under the Pi topology on `α → ℝ` (finite `α`).

## Main definitions

* `klDivSumForm_ofVec` — KL divergence taking `α → ℝ` inputs.

## Main statements

* `klDivSumForm_ofVec_continuous` — continuous in `p` when `q a > 0` for all `a`.
* `klDivIndex_eq_ofVec` — `klDivIndex c n Q = klDivSumForm_ofVec (c/n) (Q.real ∘ singleton)`.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- KL divergence in finite-alphabet vector form taking `α → ℝ` inputs:
`klDivSumForm_ofVec p q := ∑ a, p a * (log (p a) - log (q a))`.

This variant is designed for continuity arguments in the Pi topology on `α → ℝ`,
complementing the `Measure α`-based `klDiv`. -/
noncomputable def klDivSumForm_ofVec (p q : α → ℝ) : ℝ :=
  ∑ a : α, p a * (Real.log (p a) - Real.log (q a))

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `p ↦ klDivSumForm_ofVec p q` is continuous when `q a > 0` for all `a`. -/
@[entry_point]
theorem klDivSumForm_ofVec_continuous
    (q : α → ℝ) (_hq_pos : ∀ a, 0 < q a) :
    Continuous (fun p : α → ℝ ↦ klDivSumForm_ofVec p q) := by
  -- Rewrite each summand `p a * (log (p a) - log (q a))` as
  --   `-(Real.negMulLog (p a)) - Real.log (q a) * p a`
  -- and use `Real.continuous_negMulLog` (extends `x * log x` continuously through 0).
  show Continuous fun p : α → ℝ ↦ ∑ a : α, p a * (Real.log (p a) - Real.log (q a))
  have hrewrite : ∀ (p : α → ℝ) (a : α),
      p a * (Real.log (p a) - Real.log (q a))
        = -(Real.negMulLog (p a)) - Real.log (q a) * p a := by
    intro p a
    rw [Real.negMulLog_eq_neg]
    ring
  simp_rw [hrewrite]
  refine continuous_finsetSum (Finset.univ : Finset α) (fun a _ ↦ ?_)
  have h_eval : Continuous (fun p : α → ℝ ↦ p a) := continuous_apply a
  have h_negMulLog : Continuous (fun p : α → ℝ ↦ Real.negMulLog (p a)) :=
    Real.continuous_negMulLog.comp h_eval
  exact h_negMulLog.neg.sub (h_eval.const_mul (Real.log (q a)))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma klDivIndex_eq_ofVec (c : α → ℕ) (n : ℕ) (Q : Measure α) :
    klDivIndex c n Q
      = klDivSumForm_ofVec (fun a ↦ (c a : ℝ) / n) (fun a ↦ Q.real {a}) := rfl

end InformationTheory.Shannon
