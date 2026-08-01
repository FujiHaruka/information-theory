import InformationTheory.Shannon.Bridge
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The two-point law and the cost of a small mixing weight

Mixing two laws with weight `lam` is carried by a law on `Bool` that records which of the two was
drawn.  Clamping the weight at `1` makes that law a probability measure for every weight, so the
instance is available before any side condition is discharged, which is what lets the mixture be
formed and its information slots be stated at all.

A variable that records the branch of such a mixture carries the binary entropy of the weight, and
that is the price paid for mixing.  Since the binary entropy vanishes at `0` together with the
weight itself, the price can be pushed below any positive slack, simultaneously with a linear cost
in the weight.

## Main definitions

* `boolLaw lam` — the two-point law giving `true` the clamped weight `lam ⊓ 1`.

## Main statements

* `lintegral_boolLaw` — an integral against the two-point law is the weighted sum of its two
  values.
* `entropy_eq_binEntropy_of_map_boolLaw` — a variable distributed as the two-point law has the
  binary entropy of the weight.
* `exists_perturb_weight` — a positive weight below `1` whose linear cost and binary entropy stay
  under any positive slack, for two nonnegative coefficients at once.
-/

namespace InformationTheory.Shannon

open MeasureTheory
open scoped ENNReal

/-! ## The two-point law -/

/-- The two-point law with weight `lam`, clamped so that it is a probability measure for every
weight.  The clamp is what makes `IsProbabilityMeasure` an instance rather than a lemma with a
side condition, and the conditional mutual information of a mixture along this law needs that
instance in order to be stated at all. -/
noncomputable def boolLaw (lam : ℝ≥0∞) : Measure Bool :=
  (lam ⊓ 1) • Measure.dirac true + (1 - lam) • Measure.dirac false

instance boolLaw_isProbabilityMeasure (lam : ℝ≥0∞) : IsProbabilityMeasure (boolLaw lam) := by
  constructor
  simp only [boolLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rcases le_total lam 1 with h | h
  · rw [inf_of_le_left h]
    exact add_tsub_cancel_of_le h
  · rw [inf_of_le_right h, tsub_eq_zero_of_le h, add_zero]

lemma lintegral_boolLaw (lam : ℝ≥0∞) (F : Bool → ℝ≥0∞) :
    ∫⁻ t, F t ∂(boolLaw lam) = (lam ⊓ 1) * F true + (1 - lam) * F false := by
  rw [boolLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, smul_eq_mul, smul_eq_mul]

/-! ## The entropy of the two-point law -/

lemma boolLaw_real_true {lam : ℝ≥0∞} (hlam : lam ≤ 1) :
    (boolLaw lam).real {true} = lam.toReal := by
  rw [Measure.real, boolLaw]
  simp [inf_of_le_left hlam]

lemma boolLaw_real_false {lam : ℝ≥0∞} (hlam : lam ≤ 1) :
    (boolLaw lam).real {false} = 1 - lam.toReal := by
  rw [Measure.real, boolLaw]
  simp [ENNReal.toReal_sub_of_le hlam ENNReal.one_ne_top]

lemma entropy_eq_binEntropy_of_map_boolLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → Bool) {lam : ℝ≥0∞} (hlam : lam ≤ 1) (h : μ.map T = boolLaw lam) :
    entropy μ T = Real.binEntropy lam.toReal := by
  rw [entropy, h, Fintype.sum_bool, boolLaw_real_true hlam, boolLaw_real_false hlam,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-! ## Choosing the mixing weight -/

lemma exists_perturb_weight {A B δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε * A + Real.binEntropy ε < δ ∧ ε * B + Real.binEntropy ε < δ := by
  have hcont : Continuous (fun ε : ℝ ↦ ε * (A + B) + Real.binEntropy ε) :=
    (continuous_id.mul continuous_const).add Real.binEntropy_continuous
  have htend : Filter.Tendsto (fun ε : ℝ ↦ ε * (A + B) + Real.binEntropy ε) (nhds 0) (nhds 0) := by
    have h0 : (0 : ℝ) * (A + B) + Real.binEntropy 0 = 0 := by simp
    simpa [h0] using hcont.tendsto 0
  have hev₁ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε * (A + B) + Real.binEntropy ε < δ :=
    (htend.eventually (gt_mem_nhds hδ)).filter_mono nhdsWithin_le_nhds
  have hev₂ : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT one_pos
  obtain ⟨ε, hlt, hmem⟩ := (hev₁.and hev₂).exists
  have hb : 0 ≤ Real.binEntropy ε := Real.binEntropy_nonneg hmem.1.le hmem.2.le
  refine ⟨ε, hmem.1, hmem.2, ?_, ?_⟩
  · nlinarith [mul_nonneg hmem.1.le hB]
  · nlinarith [mul_nonneg hmem.1.le hA]

end InformationTheory.Shannon
