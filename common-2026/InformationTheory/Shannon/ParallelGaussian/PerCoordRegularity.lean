import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.Basic
import InformationTheory.Shannon.ParallelGaussian.PerCoord
import InformationTheory.Shannon.ParallelGaussian.Converse
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.MIBridge
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.ChannelCoding.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Parallel Gaussian capacity: regularity bundle and hypothesis-minimal headline

Assembles the regularity bundle `IsParallelGaussianPerCoordRegularity` (3 fields:
`bddAbove` / `achiever_mi` / `max_ent`) from named lemmas, and re-publishes the capacity
formula in hypothesis-minimal form.

## Main statements

* `isParallelGaussianPerCoordRegularity_of_pieces` — assembles the regularity bundle from
  its three constituent fields.
* `parallel_gaussian_capacity_formula_minimal` — the capacity formula with the regularity
  bundle assembled internally, so its only inputs are the KKT condition `h_kkt` and the
  power-positivity / measurability preconditions.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open InformationTheory.Shannon.AWGN
open scoped ENNReal NNReal BigOperators Topology

/-! ## Regularity bundle constructor -/

/-- Assemble the regularity bundle `IsParallelGaussianPerCoordRegularity` from its three
constituent fields. -/
@[entry_point]
theorem isParallelGaussianPerCoordRegularity_of_pieces {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (Q : Fin n → ℝ≥0) :
    IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q := by
  refine
    { bddAbove := ?_
      achiever_mi := ?_
      max_ent := ?_ }
  · -- `bddAbove` field
    exact parallel_bddAbove_miImage P hP N hN h_meas h_parallel_meas
  · -- `achiever_mi` field
    exact parallelGaussianCapacity_achiever_mi Q N (fun i ↦ NNReal.coe_ne_zero.mp (hN i))
      h_meas h_parallel_meas
  · -- `max_ent` field
    intro p hp
    haveI : IsProbabilityMeasure p := hp.1
    exact parallel_per_input_mi_le_sum P hP N hN h_meas h_parallel_meas p hp

/-! ## Hypothesis-minimal headline -/

/-- **Parallel Gaussian channel capacity** (water-filling), hypothesis-minimal form. The
parallel Gaussian capacity equals the water-filling sum at the KKT water level `ν`. The
regularity bundle is assembled internally, so the only inputs are the KKT condition `h_kkt`
and the preconditions `hP` / `hN` / `h_meas` / `h_parallel_meas`. -/
@[entry_point]
theorem parallel_gaussian_capacity_formula_minimal {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
  -- assemble the regularity bundle, then invoke `parallel_gaussian_capacity_formula`
  set Q : Fin (n + 1) → ℝ≥0 := fun i ↦ (waterFillingPower ν N i).toNNReal with hQ_def
  have h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q :=
    isParallelGaussianPerCoordRegularity_of_pieces P hP.le N hN h_meas h_parallel_meas Q
  exact parallel_gaussian_capacity_formula P hP N hN h_meas h_parallel_meas
    ν h_kkt h_reg

end InformationTheory.Shannon.ParallelGaussian
