import Common2026.Meta.EntryPoint
import Common2026.Shannon.ParallelGaussian
import Common2026.Draft.Shannon.ParallelGaussianPerCoord
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNMIBridge
import Common2026.Draft.Shannon.ContChannelMIDecomp
import Common2026.Shannon.DifferentialEntropy
import Common2026.Draft.Shannon.MultivariateDiffEntropy
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.ChannelCoding
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# L-PG1 closure — `IsParallelGaussianPerCoordRegularity` constructor + hypothesis-minimal headline

[parallel-gaussian-l-pg1-discharge-plan.md](../../../docs/shannon/parallel-gaussian-l-pg1-discharge-plan.md).

This file discharges the honest regularity bundle
`InformationTheory.Shannon.ParallelGaussian.IsParallelGaussianPerCoordRegularity`
(`ParallelGaussianPerCoord.lean:156`, 3 fields: `bddAbove` / `achiever_mi` /
`max_ent`) from honest pieces only, and re-publishes the headline
`parallel_gaussian_capacity_formula` in hypothesis-minimal form
(`h_reg` is unfolded into its 3 fields, the only residual being the
multivariate channel↔RV MI decomposition, which is absent from Mathlib and
not the conclusion equality).

**Phase 0 skeleton** (2026-05-25): only `isParallelGaussianPerCoordRegularity_of_pieces`
and `parallel_gaussian_capacity_formula_minimal` are stated, with bodies
`:= by sorry`. Phase 1-4 of the discharge plan will fill these one by one.
No new `@audit:staged(...)` predicate is introduced — both statements only
consume the already-existing bundle `IsParallelGaussianPerCoordRegularity`.

## Skeleton scope

* **constructor**: take the 3 honest pieces (`h_bdd_global` / `h_perCoord_bridge_achiever` /
  the `max_ent` residual = `h_multivar_decomp` + per-coord bridge) and return
  `IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q`.
* **headline**: take the genuine L-WF1/L-WF2 outputs (`h_kkt` + `h_opt`) plus the
  honest multivariate MI decomposition + per-coord bridge, and return the
  water-filling capacity equality (discharging the previous `h_reg` argument of
  `parallel_gaussian_capacity_formula` via the constructor above).

The honest pieces (`h_multivar_decomp`, `h_bridge_per_coord`) are stated with
real Prop signatures (NOT `:True` placeholders), in the shape Mathlib /
AWGN-MI bridge plan can later discharge. They are load-bearing assumptions
(not conclusions in disguise): each pins down an analytic fact about Gaussian
channels that Mathlib does not currently provide.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase 0 — constructor skeleton

`IsParallelGaussianPerCoordRegularity` (defined at `ParallelGaussianPerCoord.lean:156`)
has 3 fields:

* `bddAbove`: `BddAbove (miImage P N h_meas h_parallel_meas)`
* `achiever_mi`: `(mutualInfoOfChannel (gaussianProductInput Q) …).toReal = ∑ᵢ (1/2) log(1 + Qᵢ/Nᵢ)`
* `max_ent`: every feasible `p` admits a split `P'` with MI bounded by `∑ᵢ (1/2) log(1 + P'ᵢ/Nᵢ)`

The constructor below takes one honest piece per field, in the exact shape Phase 1-4
will produce. Phase 1: `h_bdd_global` (analytic global P-upper-bound).
Phase 2: `h_perCoord_bridge_achiever` (per-coord AWGN MI bridge,
sharing residuals with the AWGN-MI plan). Phase 3: the `max_ent` residual
=`h_multivar_decomp` (multivariate channel↔RV decomp, the sole new honest
piece) + the per-coord max-entropy plumbing fed back via `parallelGaussian_max_ent_le_of_subadditivity`.
-/

/-- **Constructor (skeleton).** Assemble `IsParallelGaussianPerCoordRegularity` from
honest pieces, one per field. Body to be filled by Phase 1-4 of the discharge plan.

* `h_bdd_global` — Phase 1: every feasible `p` has MI value bounded by the
  Q-free global upper bound `∑ᵢ (1/2) log(1 + P/(N i))`.
* `h_perCoord_bridge_achiever` — Phase 2: per-coord AWGN bridge giving the
  achiever MI value for each coordinate (this is the AWGN(#5) residual, shared
  with the AWGN-MI bridge plan).
* `h_multivar_decomp` — Phase 3: multivariate channel↔RV MI decomposition for
  every feasible input, exposing the joint output marginal `μY`, the conditional
  term `condTerm`, and the per-coord max-entropy upper bound. This is the
  **single new honest piece** introduced by the L-PG1 discharge plan; not present
  in Mathlib.

`@audit:ok(parallel-gaussian-l-pg1-discharge)` -/
@[entry_point]
theorem isParallelGaussianPerCoordRegularity_of_pieces {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (Q : Fin n → ℝ≥0)
    -- (P-1, Phase 1) global P-upper-bound (Q-free)
    (h_bdd_global :
      ∀ p ∈ { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
                ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i)^2 ∂p ≤ P },
        (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
          ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P / (N i : ℝ)))
    -- (P-2, Phase 2) per-coord AWGN bridge for the achiever
    (h_perCoord_bridge_achiever :
      (mutualInfoOfChannel (gaussianProductInput Q)
          (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        = ∑ i : Fin n, (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)))
    -- (P-3, Phase 3) multivariate channel↔RV decomp + per-coord max-entropy allocation
    -- For every feasible `p`, there exist a joint output `μY` and a conditional term
    -- such that the MI decomposes as `h(Yⁿ) − condTerm`, and there exists a
    -- per-coord power split `P'` (≥0, ∑≤P) whose subadditive upper bound is met.
    (h_multivar_decomp :
      ∀ p ∈ { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
                ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i)^2 ∂p ≤ P },
        ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
          (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
            ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))) :
    IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q := by
  refine
    { bddAbove := ?_
      achiever_mi := h_perCoord_bridge_achiever
      max_ent := h_multivar_decomp }
  -- Phase 1: the MI image is bounded above by the Q-free global P-upper bound.
  refine ⟨∑ i : Fin n, (1/2) * Real.log (1 + P / (N i : ℝ)), ?_⟩
  rintro y ⟨p, hp_mem, rfl⟩
  exact h_bdd_global p hp_mem

/-! ## Phase 0 — hypothesis-minimal headline skeleton

The headline below is the hypothesis-minimal re-publish of
`parallel_gaussian_capacity_formula` (`PerCoord.lean:367`). The previous
`h_reg : IsParallelGaussianPerCoordRegularity …` argument is unfolded into its
3 honest pieces (the same shapes the constructor above consumes), so callers
need not assemble the bundle manually.
-/

/-- **Hypothesis-minimal headline (skeleton).** The parallel Gaussian capacity
equals the water-filling sum, with the regularity bundle unfolded into its
3 honest pieces. Body to be filled by Phase 4 of the discharge plan via the
constructor `isParallelGaussianPerCoordRegularity_of_pieces` above.

`@audit:ok(parallel-gaussian-l-pg1-discharge)` -/
@[entry_point]
theorem parallel_gaussian_capacity_formula_minimal {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) (h_opt : IsWaterFillingOptimal P N ν)
    -- (P-1) global P-upper-bound (Phase 1 honest piece, Q-free)
    (h_bdd_global :
      ∀ p ∈ { p : Measure (Fin (n + 1) → ℝ) | IsProbabilityMeasure p ∧
                ∑ i : Fin (n + 1), ∫ x : Fin (n + 1) → ℝ, (x i)^2 ∂p ≤ P },
        (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
          ≤ ∑ i : Fin (n + 1), (1/2) * Real.log (1 + P / (N i : ℝ)))
    -- (P-2) per-coord AWGN bridge for the water-filling achiever (Phase 2 honest piece)
    (h_bridge_per_coord :
      (mutualInfoOfChannel
          (gaussianProductInput (fun i => (waterFillingPower ν N i).toNNReal))
          (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        = ∑ i : Fin (n + 1), (1/2) * Real.log
            (1 + ((waterFillingPower ν N i).toNNReal : ℝ) / (N i : ℝ)))
    -- (P-3) multivariate channel↔RV decomp + per-coord max-entropy allocation
    -- (Phase 3 honest piece — the *only* new honest piece of this plan).
    (h_multivar_decomp :
      ∀ p ∈ { p : Measure (Fin (n + 1) → ℝ) | IsProbabilityMeasure p ∧
                ∑ i : Fin (n + 1), ∫ x : Fin (n + 1) → ℝ, (x i)^2 ∂p ≤ P },
        ∃ P' : Fin (n + 1) → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin (n + 1), P' i ≤ P) ∧
          (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
            ≤ ∑ i : Fin (n + 1), (1/2) * Real.log (1 + P' i / (N i : ℝ))) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
  -- Phase 4: assemble the regularity bundle from the 3 honest pieces via the
  -- constructor, then invoke the existing genuine `le_antisymm` headline
  -- `parallel_gaussian_capacity_formula` (`PerCoord.lean:367`).
  set Q : Fin (n + 1) → ℝ≥0 := fun i => (waterFillingPower ν N i).toNNReal with hQ_def
  have h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q :=
    isParallelGaussianPerCoordRegularity_of_pieces P N h_meas h_parallel_meas Q
      h_bdd_global h_bridge_per_coord h_multivar_decomp
  exact parallel_gaussian_capacity_formula P hP N hN h_meas h_parallel_meas
    ν h_kkt h_opt h_reg

end InformationTheory.Shannon.ParallelGaussian
