import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.ChainRule
import InformationTheory.Shannon.SMB.McMillanBreiman
import InformationTheory.Probability.TwoSidedExtension
import InformationTheory.Shannon.SMB.AlgoetCover.KMarkovApproximation
import InformationTheory.Shannon.SMB.AlgoetCover.MarkovLikelihoodRatio
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

/-! ## D.4 — limsup direction -/

omit [DecidableEq α] in
/-- Logarithmic form of `MRatioUp_le_sq_eventually`: pointwise `blockLogAvg`
upper bound by the `k`-Markov approximation plus a `2 log n / n` error. -/
theorem blockLogAvg_le_negLogQk_plus_error
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg μ p n ω ≤ negLogQk μ p k n ω / n + 2 * Real.log n / n := by
  filter_upwards [MRatioUp_le_sq_eventually μ p k] with ω hω
  -- From eventual n ≥ 1 and the ENNReal bound, take log on the real side.
  filter_upwards [hω, Filter.eventually_ge_atTop 1] with n h_MR hn
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_n_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  -- ENNReal.ofReal (exp X) ≤ ENNReal.ofReal (n^2) ⇒ exp X ≤ n^2.
  have h_exp_nn : (0 : ℝ) ≤ Real.exp ((n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω) :=
    (Real.exp_pos _).le
  have h_real_le : Real.exp ((n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω)
      ≤ (n : ℝ) ^ 2 := by
    have : ENNReal.ofReal (Real.exp ((n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω))
        ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := h_MR
    exact (ENNReal.ofReal_le_ofReal_iff h_n_sq_pos.le).mp this
  -- log monotone: X ≤ log (n^2) = 2 log n.
  have h_log : (n : ℝ) * blockLogAvg μ p n ω - negLogQk μ p k n ω
      ≤ 2 * Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) h_real_le
    rw [Real.log_exp] at h
    have h_log_sq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [show ((n : ℝ) ^ 2) = (n : ℝ) * (n : ℝ) from sq (n : ℝ),
        Real.log_mul h_n_pos.ne' h_n_pos.ne']
      ring
    rw [h_log_sq] at h
    exact h
  -- Divide by n > 0.
  have h_div : blockLogAvg μ p n ω - negLogQk μ p k n ω / (n : ℝ) ≤
      2 * Real.log (n : ℝ) / (n : ℝ) := by
    have h := div_le_div_of_nonneg_right h_log h_n_pos.le
    rw [sub_div, mul_div_cancel_left₀ _ h_n_pos.ne'] at h
    exact h
  linarith

omit [DecidableEq α] in
/-- Taking `limsup` in `blockLogAvg_le_negLogQk_plus_error` and using
Birkhoff for the `k`-Markov approximation gives the per-`k` limsup bound. -/
@[entry_point]
theorem limsup_blockLogAvg_le_condEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n ↦ blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ conditionalEntropyTail μ p.toStationaryProcess k := by
  filter_upwards [blockLogAvg_le_negLogQk_plus_error μ p.toStationaryProcess k,
                  negLogQk_div_tendsto_condEntropyTail μ p k] with ω h_bound h_neg
  -- RHS tendsto: negLogQk / n + 2 log n / n → H_k + 0 = H_k.
  have h_log_div : Filter.Tendsto (fun n : ℕ ↦ 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    -- log n / n → 0 then multiply by 2.
    have h_log : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have h_real : Filter.Tendsto (fun x : ℝ ↦ Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h_comp := h_real.comp tendsto_natCast_atTop_atTop
      refine h_comp.congr (fun n ↦ ?_)
      simp
    have h_mul := h_log.const_mul (2 : ℝ)
    simp only [mul_zero] at h_mul
    refine h_mul.congr (fun n ↦ ?_)
    rw [mul_div_assoc]
  have h_rhs : Filter.Tendsto
      (fun n : ℕ ↦ negLogQk μ p.toStationaryProcess k n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k)) := by
    have := h_neg.add h_log_div
    simpa using this
  -- Use limsup_le_of_le with the eventual bound + tendsto.
  -- We need IsCoboundedUnder for blockLogAvg.
  -- Strategy: limsup ≤ limsup of bound = lim of bound = H_k.
  have h_limsup_bound : Filter.limsup
      (fun n ↦ blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
      ≤ Filter.limsup (fun n : ℕ ↦ negLogQk μ p.toStationaryProcess k n ω / (n : ℝ)
        + 2 * Real.log (n : ℝ) / (n : ℝ)) Filter.atTop := by
    refine Filter.limsup_le_limsup h_bound ?_ ?_
    · -- IsCoboundedUnder (· ≤ ·) of blockLogAvg: from boundedness below by 0.
      refine (Filter.isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall (fun n ↦ ?_))).isCoboundedUnder_le
      -- Reuse the same nonneg proof from blockLogAvg_bddBelow_ae body.
      have hPn : IsProbabilityMeasure (μ.map (p.toStationaryProcess.blockRV n)) :=
        Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
      have h_le_one : (μ.map (p.toStationaryProcess.blockRV n)).real
          {p.toStationaryProcess.blockRV n ω} ≤ 1 := measureReal_le_one
      have h_nn : 0 ≤ (μ.map (p.toStationaryProcess.blockRV n)).real
          {p.toStationaryProcess.blockRV n ω} := measureReal_nonneg
      have h_log_nonpos : Real.log ((μ.map (p.toStationaryProcess.blockRV n)).real
          {p.toStationaryProcess.blockRV n ω}) ≤ 0 := Real.log_nonpos h_nn h_le_one
      have h_inv_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      have h_neg_inv_nonpos : -(1 / (n : ℝ)) ≤ 0 := neg_nonpos_of_nonneg h_inv_nn
      unfold blockLogAvg
      exact mul_nonneg_of_nonpos_of_nonpos h_neg_inv_nonpos h_log_nonpos
    · exact h_rhs.isBoundedUnder_le
  exact h_limsup_bound.trans h_rhs.limsup_eq.le

omit [DecidableEq α] in
/-- Letting `k → ∞` in the per-`k` bound and using
`entropyRate_eq_lim_condEntropy` discharges the `limsup` hypothesis of
`shannon_mcmillan_breiman_of_sandwich`. -/
@[entry_point]
theorem algoet_cover_limsup_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n ↦ blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess := by
  classical
  -- Per-k bound (a.s.): limsup ≤ H_k.
  have h_all : ∀ᵐ ω ∂μ, ∀ k : ℕ,
      Filter.limsup (fun n ↦ blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ conditionalEntropyTail μ p.toStationaryProcess k := by
    rw [ae_all_iff]
    intro k
    exact limsup_blockLogAvg_le_condEntropyTail μ p k
  filter_upwards [h_all] with ω hω
  -- `H_k → entropyRate` as k → ∞.
  have h_tail := entropyRate_eq_lim_condEntropy μ p.toStationaryProcess
  exact ge_of_tendsto' h_tail hω

end InformationTheory.Shannon
