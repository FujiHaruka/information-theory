import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityAEP
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.MultivariateDiffEntropy
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Per-codeword power constraint

The per-codeword power-constraint expurgation bound for the AWGN channel: each
individual codeword drawn from the Gaussian product law violates the power budget
on a codebook set of vanishing mass. This is the WLLN/Markov fact consumed by the
Cover–Thomas expurgation argument.

## Main statements

* `awgnPowerConstraintPerCodeword_holds` — the per-codeword power constraint.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Per-codeword power constraint -/

/-- Per-codeword power-constraint expurgation bound.

For a codebook drawn from the 2-stage Gaussian product law at codeword variance
`P_cb`, and a power target `P_target` with strict slack `P_cb < P_target`, each
*individual* codeword `m` violates the power budget `∑ᵢ (c m i)² > n · P_target`
on a codebook set of mass `≤ ε` (for all `n` past a threshold `N₀`).

This is the per-codeword marginal form: unlike the false `∀ m`-form (mass of
the all-codewords-OK set `≥ 1 − ε`, which decays like `q^M ≈ exp(−exp(n(R−ψ)))`),
the per-codeword marginal mass is `M`-independent (the `m`-th coordinate marginal
of `Measure.pi (fun _ : Fin M => νₙ)` is `νₙ`), so no exponential rate / capacity
rate bound is needed. It is exactly the WLLN/Markov fact the Cover–Thomas
expurgation argument consumes.

Proof: the `m`-th coordinate marginal is `νₙ = Measure.pi (fun _ : Fin n =>
gaussianReal 0 P_cb.toNNReal)` (`measurePreserving_eval`), reducing the codebook
mass to the single-codeword chi-square upper-tail mass. Apply the abstract
Chebyshev engine `pi_empirical_mean_concentration` with statistic `φ x = x²`,
`μ[φ] = (P_cb.toNNReal : ℝ)` (centred Gaussian second moment = variance), and the
deviation level `δ = P_target − (P_cb.toNNReal : ℝ) > 0`: the violating set
`{x | n·P_target < ∑ᵢ xᵢ²}` is contained in the deviation set
`{x | δ ≤ |(∑ᵢ φ(xᵢ))/n − μ[φ]|}`, whose mass is `≤ variance(φ)/(n·δ²)`; choosing
`N₀ > variance(φ)/(ε·δ²)` gives `≤ ε`. `MemLp φ 2` holds because the Gaussian has a
finite 4th moment (`memLp_id_gaussianReal 4`, polynomial — no log). -/
theorem awgnPowerConstraintPerCodeword_holds
    (P_cb P_target : ℝ) (hP_slack : (P_cb.toNNReal : ℝ) < P_target) (N : ℝ≥0) :
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (_hM_pos : 0 < M),
        ∀ m : Fin M,
          (Measure.pi
              (fun _ : Fin M ↦ Measure.pi (fun _ : Fin n ↦ gaussianReal 0 P_cb.toNNReal)))
            {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
          ≤ ENNReal.ofReal ε := by
  classical
  -- Abbreviations: codeword law `μ`, statistic `φ = x²`, mean `μ[φ] = variance = P_cb`.
  set v : ℝ≥0 := P_cb.toNNReal with hv_def
  set μ : Measure ℝ := gaussianReal 0 v with hμ_def
  set φ : ℝ → ℝ := fun x ↦ x ^ 2 with hφ_def
  -- `φ ∈ MemLp 2` via finite 4th moment of the Gaussian.
  have hφ_mem : MemLp φ 2 μ := by
    have hmeas : AEStronglyMeasurable φ μ := by
      rw [hφ_def]; exact (measurable_id.pow_const 2).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    -- `Integrable (fun x => (x²)²) = Integrable (fun x => x⁴)`, from `MemLp id 4`.
    have hmem4 : MemLp (id : ℝ → ℝ) 4 μ := by
      rw [hμ_def]; exact memLp_id_gaussianReal' 4 (by simp)
    have hint4 : Integrable (fun x : ℝ ↦ ‖(id : ℝ → ℝ) x‖ ^ 4) μ :=
      hmem4.integrable_norm_pow (by norm_num)
    refine hint4.congr ?_
    filter_upwards with x
    rw [hφ_def]
    simp only [id_eq, Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity)]
    ring
  -- `μ[φ] = (v : ℝ)` (centred Gaussian second moment = variance).
  have hμφ : μ[φ] = (v : ℝ) := by
    have hmem_id : MemLp (id : ℝ → ℝ) 2 μ := by
      rw [hμ_def]; exact memLp_id_gaussianReal' 2 (by simp)
    have hvar : variance (id : ℝ → ℝ) μ = (v : ℝ) := by
      rw [hμ_def]; exact variance_id_gaussianReal
    have hsub := variance_eq_sub hmem_id
    have hmean : μ[(id : ℝ → ℝ)] = 0 := by
      rw [hμ_def]; simp [integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)]
    rw [hvar, hmean] at hsub
    -- `hsub : (v : ℝ) = μ[id ^ 2] - 0 ^ 2`.
    have hid2 : (μ[(id : ℝ → ℝ) ^ 2]) = μ[φ] := by
      congr 1
    rw [hid2] at hsub
    simpa using hsub.symm
  -- The strict deviation level.
  set δ : ℝ := P_target - (v : ℝ) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hP_slack]
  intro ε hε
  -- Choose `N₀` so that `variance φ μ / (N₀ · δ²) ≤ ε`, mirroring the engine's own
  -- existence construction.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (variance φ μ / (ε * δ ^ 2))
  refine ⟨N₀ + 1, fun n hn M _hM_pos m ↦ ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N₀) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  -- The `m`-th coordinate marginal of the codebook law is `νₙ = Measure.pi μ`.
  have hmarg :
      (Measure.pi (fun _ : Fin M ↦ Measure.pi (fun _ : Fin n ↦ μ)))
          {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
        = (Measure.pi (fun _ : Fin n ↦ μ))
            {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
    have hmp :
        MeasurePreserving (Function.eval m)
          (Measure.pi (fun _ : Fin M ↦ Measure.pi (fun _ : Fin n ↦ μ)))
          (Measure.pi (fun _ : Fin n ↦ μ)) :=
      measurePreserving_eval (fun _ : Fin M ↦ Measure.pi (fun _ : Fin n ↦ μ)) m
    have hmeasSet :
        MeasurableSet {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
      apply measurableSet_lt measurable_const
      exact Finset.measurable_sum _ (fun i _ ↦ (measurable_pi_apply i).pow_const 2)
    have hpre :
        {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
          = (Function.eval m) ⁻¹' {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
      rfl
    rw [hpre, hmp.measure_preimage hmeasSet.nullMeasurableSet]
  rw [hmarg]
  -- The violating set is contained in the level-`δ` deviation set.
  have hsubset :
      {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2}
        ⊆ {x : Fin n → ℝ | δ ≤ |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    -- `∑ᵢ φ(xᵢ) = ∑ᵢ xᵢ²` since `φ = (·)²`.
    have hsumφ : (∑ i, φ (x i)) = ∑ i, (x i) ^ 2 := by simp [hφ_def]
    rw [hsumφ, hμφ]
    -- From `n·P_target < ∑ xᵢ²` and `n > 0`: `δ < (∑ xᵢ²)/n − v`.
    have hkey : δ < (∑ i, (x i) ^ 2) / (n : ℝ) - (v : ℝ) := by
      have hdiv : P_target < (∑ i, (x i) ^ 2) / (n : ℝ) := by
        rw [lt_div_iff₀ hnR]; linarith [hx]
      show P_target - (v : ℝ) < (∑ i, (x i) ^ 2) / (n : ℝ) - (v : ℝ)
      linarith
    exact le_of_lt (lt_of_lt_of_le hkey (le_abs_self _))
  -- Mass of the violating set ≤ mass of the deviation set ≤ variance/(n·δ²) ≤ ε.
  have hdev := pi_empirical_mean_concentration μ hφ_mem hδ_pos hn0
  have hviol_le := measure_mono (μ := Measure.pi (fun _ : Fin n ↦ μ)) hsubset
  refine le_trans (le_trans hviol_le hdev) ?_
  -- `variance φ μ / (n · δ²) ≤ ε`.
  apply ENNReal.ofReal_le_ofReal
  have hVarnn : (0 : ℝ) ≤ variance φ μ := variance_nonneg φ μ
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hεδ : (0 : ℝ) < ε * δ ^ 2 := by positivity
  -- `variance / (ε·δ²) < N₀ ≤ n`.
  have hNn : variance φ μ / (ε * δ ^ 2) < (n : ℝ) := by
    calc variance φ μ / (ε * δ ^ 2) < (N₀ : ℝ) := hN₀
      _ ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_succ N₀) hn
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hεδ] at hNn
  nlinarith [hNn, hVarnn, hδ2, hnR]

end InformationTheory.Shannon.AWGN
