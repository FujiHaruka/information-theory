import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Finiteness

/-!
# Mixing two measures at a clamped weight

A probability measure is smoothed toward a second one by taking their convex combination.
Clamping the weight to `[0, 1]` makes the combination a probability measure for every real
weight, so the instance is available before any side condition on the weight is discharged, and
the mixture may be formed and reasoned about for an unconstrained parameter.  On a singleton the
mixture is the convex combination of the two masses, so it is positive as soon as the weight is
and the second measure charges that point, and it depends continuously on the weight.

## Main definitions

* `mixWeight ε` — the weight `ε` clamped to `[0, 1]`.
* `mixLaw p μ₀ ε` — the convex combination of `p` and `μ₀` at the clamped weight `ε`.

## Main statements

* `mixLaw_real_apply` — the singleton mass of the mixture is the convex combination of the two
  singleton masses.

## Implementation notes

The module sits at the bottom of the import DAG — it depends only on Mathlib — so any file
forming such a mixture can import it without pulling in information-theoretic material.
-/

namespace InformationTheory

open MeasureTheory

/-! ## The clamped weight -/

/-- The weight `ε` clamped to `[0, 1]`, so that a convex combination taken at it is a
probability measure for every real `ε` while the weight agrees with `ε` on `[0, 1]`. -/
noncomputable def mixWeight (ε : ℝ) : ℝ := min 1 (max 0 ε)

lemma mixWeight_nonneg (ε : ℝ) : 0 ≤ mixWeight ε :=
  le_min zero_le_one (le_max_left 0 ε)

lemma mixWeight_le_one (ε : ℝ) : mixWeight ε ≤ 1 := min_le_left _ _

lemma mixWeight_zero : mixWeight 0 = 0 := by simp [mixWeight]

lemma mixWeight_pos {ε : ℝ} (hε : 0 < ε) : 0 < mixWeight ε :=
  lt_min zero_lt_one (lt_of_lt_of_le hε (le_max_right 0 ε))

lemma mixWeight_continuous : Continuous mixWeight :=
  continuous_const.min (continuous_const.max continuous_id)

/-! ## The mixture -/

variable {X : Type*} [MeasurableSpace X]

/-- The convex combination `mixLaw p μ₀ ε = (1 - mixWeight ε) • p + mixWeight ε • μ₀` of two
measures at the clamped weight `ε`.  For `0 < ε` and a `μ₀` charging every point, so does the
mixture; at `ε = 0` it is `p`. -/
noncomputable def mixLaw (p μ₀ : Measure X) (ε : ℝ) : Measure X :=
  ENNReal.ofReal (1 - mixWeight ε) • p + ENNReal.ofReal (mixWeight ε) • μ₀

instance mixLaw.instIsProbabilityMeasure (p μ₀ : Measure X) [IsProbabilityMeasure p]
    [IsProbabilityMeasure μ₀] (ε : ℝ) : IsProbabilityMeasure (mixLaw p μ₀ ε) := by
  refine ⟨?_⟩
  unfold mixLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [mixWeight_le_one ε]) (mixWeight_nonneg ε),
    show (1 - mixWeight ε) + mixWeight ε = 1 by ring, ENNReal.ofReal_one]

lemma mixLaw_zero (p μ₀ : Measure X) : mixLaw p μ₀ 0 = p := by
  unfold mixLaw
  rw [mixWeight_zero]
  simp

lemma mixLaw_real_apply (p μ₀ : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure μ₀]
    (ε : ℝ) (a : X) :
    (mixLaw p μ₀ ε).real {a}
      = (1 - mixWeight ε) * p.real {a} + mixWeight ε * μ₀.real {a} := by
  unfold mixLaw
  rw [measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [mixWeight_le_one ε]),
    ENNReal.toReal_ofReal (mixWeight_nonneg ε)]
  rfl

lemma mixLaw_real_pos (p μ₀ : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure μ₀]
    (hμ₀ : ∀ a : X, 0 < μ₀.real {a}) {ε : ℝ} (hε : 0 < ε) (a : X) :
    0 < (mixLaw p μ₀ ε).real {a} := by
  rw [mixLaw_real_apply]
  have h1 : 0 ≤ (1 - mixWeight ε) * p.real {a} :=
    mul_nonneg (by linarith [mixWeight_le_one ε]) measureReal_nonneg
  have h2 : 0 < mixWeight ε * μ₀.real {a} := mul_pos (mixWeight_pos hε) (hμ₀ a)
  linarith

lemma mixLaw_real_continuous (p μ₀ : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure μ₀]
    (a : X) : Continuous fun ε : ℝ ↦ (mixLaw p μ₀ ε).real {a} := by
  have hrw : (fun ε : ℝ ↦ (mixLaw p μ₀ ε).real {a})
      = fun ε : ℝ ↦ (1 - mixWeight ε) * p.real {a} + mixWeight ε * μ₀.real {a} := by
    funext ε; exact mixLaw_real_apply p μ₀ ε a
  rw [hrw]
  exact ((continuous_const.sub mixWeight_continuous).mul continuous_const).add
    (mixWeight_continuous.mul continuous_const)

end InformationTheory
