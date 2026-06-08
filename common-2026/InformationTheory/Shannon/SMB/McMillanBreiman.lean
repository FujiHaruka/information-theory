import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.Bridge
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Shannon-McMillan-Breiman theorem (sandwich form — E-8' weakened MVP)

Cover–Thomas Theorem 16.8.1: for a stationary ergodic process with finite
alphabet `α`, the per-symbol negative log-likelihood

  `-(1/n) log P(X_0, …, X_{n-1})`

converges almost surely to the entropy rate `H`. This file packages the
**sandwich form** of the conclusion: assuming `liminf ≥ H` and `limsup ≤ H`
almost surely (the two halves of the Cover–Thomas 16.8 bound which Birkhoff
supplies), we deduce a.s. convergence via `tendsto_of_le_liminf_of_limsup_le`.

The hypothesis-free capstone `shannon_mcmillan_breiman` lives in
`InformationTheory.Shannon.SMBAlgoetCover`: it discharges the two sandwich
inequalities and a.s. boundedness unconditionally via the Algoet–Cover bounds
(`algoet_cover_liminf_bound` / `algoet_cover_limsup_bound`), which rest on the
Birkhoff ergodic theorem (`BirkhoffErgodic`), the two-sided projective-limit
construction (`Probability.TwoSidedExtension`), and backward-martingale
convergence.

We also publish the **expected-value level** statement, which does **not**
need Birkhoff.

## Main definitions

* `blockLogAvg μ p n ω` — `-(1/n) * log P_n({block_n ω})`, the per-block
  empirical entropy estimator for the observed sample.

## Main results

* `shannon_mcmillan_breiman_of_sandwich` — sandwich version: from the two
  Cover–Thomas inequalities (`liminf ≥ H`, `limsup ≤ H`) plus a.s.
  boundedness, derive `Tendsto blockLogAvg n → H` a.s.
* `expected_blockLogAvg_eq` — `𝔼[blockLogAvg μ p n] = blockEntropy μ p n / n`.
* `tendsto_expected_blockLogAvg` — the expected-value SMB:
  `𝔼[blockLogAvg μ p n] → entropyRate μ p` as `n → ∞`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Per-block negative log-likelihood average for the observed sample.

`blockLogAvg μ p n ω := -(1/n) * log P_n({block_n ω})` where
`P_n = μ.map (blockRV n)`. Cover–Thomas 16.8 calls this `-(1/n) log p(X^n)`.

For `n = 0` the value is `0` (multiplication by `1/0 = 0`); only `n > 0`
behavior is informative. -/
noncomputable def blockLogAvg
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω => -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})

omit [DecidableEq α] [Nonempty α] in
/-- Measurability of `blockLogAvg μ p n`. -/
@[entry_point]
lemma measurable_blockLogAvg
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (blockLogAvg μ p n) := by
  -- The function factors as `ω ↦ blockRV n ω` (measurable) composed with
  -- the finite-alphabet function `x ↦ -(1/n) * log (P_n.real {x})` (measurable
  -- because the codomain is discrete).
  have h_block : Measurable (p.blockRV n) := p.measurable_blockRV n
  have h_disc : Measurable (fun x : Fin n → α =>
      -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {x})) := by
    exact measurable_of_finite _
  exact h_disc.comp h_block

/-! ## Sandwich form (Cover–Thomas 16.8.1) -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Shannon–McMillan–Breiman, sandwich form**.

If the per-symbol log-likelihood average `blockLogAvg μ p n` satisfies the
two Cover–Thomas 16.8 bounds (liminf ≥ entropy rate, limsup ≤ entropy rate)
and is a.s. bounded, then it converges to the entropy rate a.s.

This is the "Phase D" wrapper: once Birkhoff (Phase C) supplies the two
sandwich inequalities a.s., the conclusion follows immediately from
`tendsto_of_le_liminf_of_limsup_le`. -/
@[entry_point]
theorem shannon_mcmillan_breiman_of_sandwich
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_liminf : ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop)
    (h_limsup : ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess)
    (h_bdd_above : ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n => blockLogAvg μ p.toStationaryProcess n ω))
    (h_bdd_below : ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n => blockLogAvg μ p.toStationaryProcess n ω)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  filter_upwards [h_liminf, h_limsup, h_bdd_above, h_bdd_below]
    with ω hli hls hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hli hls hba hbb

/-! ## Expected-value level (no Birkhoff needed) -/

omit [DecidableEq α] [Nonempty α] in
/-- The expected per-symbol negative log-likelihood equals `blockEntropy / n`.

This is the discrete-alphabet analogue of `integral_logLikelihood_zero` in
`AEP.lean`: push forward via `blockRV n`, collapse the integral over a
finite alphabet to a sum, and recognize the resulting sum as the entropy
times `-(1/n)`. -/
@[entry_point]
theorem expected_blockLogAvg_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, blockLogAvg μ p n ω ∂μ = blockEntropy μ p n / n := by
  classical
  have hB : Measurable (p.blockRV n) := p.measurable_blockRV n
  have hPn : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
    Measure.isProbabilityMeasure_map hB.aemeasurable
  -- Step 1: push forward via `blockRV n`.
  set f : (Fin n → α) → ℝ :=
    fun x => -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {x}) with hf_def
  have hf_meas : Measurable f := measurable_of_finite _
  have h_push : ∫ ω, blockLogAvg μ p n ω ∂μ
      = ∫ x, f x ∂(μ.map (p.blockRV n)) := by
    rw [integral_map hB.aemeasurable hf_meas.aestronglyMeasurable]
    rfl
  rw [h_push]
  -- Step 2: collapse to a finite sum.
  rw [integral_fintype (μ := μ.map (p.blockRV n)) Integrable.of_finite]
  -- Step 3: factor `-(1/n)` out and recognize the inner sum as
  -- `∑ x, negMulLog ((μ.map blockRV n).real {x}) = blockEntropy μ p n`.
  unfold blockEntropy entropy
  -- Goal: `∑ x, (μ.map blockRV n).real {x} • f x = (∑ x, negMulLog (...)) / n`.
  -- Rewrite each smul as `-(1/n) * (negMulLog of measure)`, factor out, divide.
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h_sum_eq : (∑ x : Fin n → α,
        (μ.map (p.blockRV n)).real {x} • f x)
      = (1 / (n : ℝ)) *
          ∑ x : Fin n → α,
            Real.negMulLog ((μ.map (p.blockRV n)).real {x}) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show (μ.map (p.blockRV n)).real {x} • f x
        = (1 / (n : ℝ)) * Real.negMulLog ((μ.map (p.blockRV n)).real {x})
    rw [hf_def, Real.negMulLog, smul_eq_mul]
    -- `p * (-(1/n) * log p) = (1/n) * (-p * log p)`.
    ring
  rw [h_sum_eq, one_div, ← div_eq_inv_mul]

end InformationTheory.Shannon
