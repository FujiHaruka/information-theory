import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.ChainRule
import InformationTheory.Shannon.SMB.McMillanBreiman
import InformationTheory.Probability.TwoSidedExtension
import InformationTheory.Shannon.SMB.AlgoetCover.KMarkovApproximation
import InformationTheory.Shannon.SMB.AlgoetCover.Limsup
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## D.6 — Boundedness (hoisted before D.5 because the liminf transfer uses
`blockLogAvg_bddAbove_ae` to establish μZ-a.s. upper boundedness of `blockLogAvgZ`). -/

omit [DecidableEq α] in
/-- A.s. boundedness above for `blockLogAvg`.

A.s., `blockLogAvg ≤ negLogQk(k=0)/n + 2·log n / n` (from
`blockLogAvg_le_negLogQk_plus_error`), and the RHS converges a.s. to
`conditionalEntropyTail μ p 0` (finite), hence the RHS is eventually bounded
above and so is `blockLogAvg`. -/
@[entry_point]
theorem blockLogAvg_bddAbove_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvg μ p.toStationaryProcess n ω) := by
  -- log n / n → 0.
  have h_log_div : Filter.Tendsto (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have h_real : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h_comp := h_real.comp tendsto_natCast_atTop_atTop
      refine h_comp.congr (fun n => ?_)
      simp
    have h_mul := h_log.const_mul (2 : ℝ)
    simp only [mul_zero] at h_mul
    refine h_mul.congr (fun n => ?_)
    rw [mul_div_assoc]
  filter_upwards [blockLogAvg_le_negLogQk_plus_error μ p.toStationaryProcess 0,
                  negLogQk_div_tendsto_condEntropyTail μ p 0] with ω h_bound h_neg
  have h_rhs : Filter.Tendsto
      (fun n : ℕ => negLogQk μ p.toStationaryProcess 0 n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess 0)) := by
    have := h_neg.add h_log_div
    simpa using this
  have h_rhs_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => negLogQk μ p.toStationaryProcess 0 n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ)) := h_rhs.isBoundedUnder_le
  exact h_rhs_bdd.mono_le h_bound

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- A.s. boundedness below for `blockLogAvg`. -/
@[entry_point]
theorem blockLogAvg_bddBelow_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => blockLogAvg μ p.toStationaryProcess n ω) := by
  -- `blockLogAvg μ p n ω ≥ 0` for every `n` and every `ω`.
  refine Filter.Eventually.of_forall (fun ω => ?_)
  refine Filter.isBoundedUnder_of_eventually_ge (a := 0)
    (Filter.Eventually.of_forall (fun n => ?_))
  have hPn : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
  have h_le_one : (μ.map (p.blockRV n)).real {p.blockRV n ω} ≤ 1 :=
    measureReal_le_one
  have h_nn : 0 ≤ (μ.map (p.blockRV n)).real {p.blockRV n ω} := measureReal_nonneg
  have h_log_nonpos : Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) ≤ 0 :=
    Real.log_nonpos h_nn h_le_one
  have h_inv_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have h_neg_inv_nonpos : -(1 / (n : ℝ)) ≤ 0 := neg_nonpos_of_nonneg h_inv_nn
  unfold blockLogAvg
  exact mul_nonneg_of_nonpos_of_nonpos h_neg_inv_nonpos h_log_nonpos

end InformationTheory.Shannon
