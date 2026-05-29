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

This file assembles the regularity bundle
`InformationTheory.Shannon.ParallelGaussian.IsParallelGaussianPerCoordRegularity`
(`ParallelGaussianPerCoord.lean:186`, 3 fields: `bddAbove` / `achiever_mi` /
`max_ent`) and re-publishes the headline `parallel_gaussian_capacity_formula` in
hypothesis-minimal form.

**Honest restructure** (2026-05-29,
[parallel-gaussian-headline-honest-restructure-plan.md](../../../docs/shannon/parallel-gaussian-headline-honest-restructure-plan.md)):
the previous versions reduced their conclusions wholesale to load-bearing open
hypotheses (`h_bdd_global` / `h_multivar_decomp`) carrying the converse analytic
core — flagged tier 5 by independent honesty audit. Those hypotheses are now
dropped and replaced by `sorry` + `@residual(wall:multivariate-mi)` at the genuine
walls:

* `achiever_mi` field — **genuine** (product-input MI additivity
  `parallelGaussianCapacity_achiever_mi` fed the per-coordinate AWGN closed form
  `h_perCoordMI`, a regularity-shaped precondition).
* `bddAbove` / `max_ent` fields — `sorry` + `@residual(wall:multivariate-mi)`. The
  global MI upper bound and per-coord max-entropy converse split on *correlated*
  feasible inputs are the converse side of the multivariate MI additivity wall, not
  closed by the achiever's product-input closure (see plan M0).

The headline `parallel_gaussian_capacity_formula_minimal` keeps the genuine
water-filling optimality inputs (`h_kkt` / `h_opt`) and `h_perCoordMI`, genuinely
assembles `h_reg` via the constructor, and invokes the genuine `le_antisymm`
sup-sandwich; its only residual is the transitive `wall:multivariate-mi` from the
constructor (tracked by the type-checker, not re-stated here).

Status: type-check done (tier 2), NOT proof done (2 `sorry` at
`wall:multivariate-mi`).
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open InformationTheory.Shannon.AWGN
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

/-- **Constructor (honest restructure, 2026-05-29).** Assemble
`IsParallelGaussianPerCoordRegularity` from genuine pieces only. The two
load-bearing converse hypotheses of the previous version (`h_bdd_global` /
`h_multivar_decomp`, which carried the CORE analytic content of the `bddAbove`
and `max_ent` fields rather than regularity preconditions) are dropped; those
fields are now `sorry` + `@residual(wall:multivariate-mi)`.

* `achiever_mi` field — **genuine**, built from
  `parallelGaussianCapacity_achiever_mi` (the genuine structural per-channel
  decomposition: product-input MI additivity on `gaussianProductInput Q`) fed the
  per-coordinate AWGN closed form `h_perCoordMI`. `h_perCoordMI` is a per-channel
  regularity-shaped fact (single-channel AWGN value, `p`-independent), NOT the
  conclusion equality; it is supplied as a precondition.
* `bddAbove` field — `sorry` + `@residual(wall:multivariate-mi)`. The global MI
  upper bound on the *correlated* feasible inputs is the converse side of the
  multivariate MI additivity wall (not closed by the achiever's product-input
  closure).
* `max_ent` field — `sorry` + `@residual(wall:multivariate-mi)`. The per-coord
  max-entropy converse split on *correlated* feasible inputs. The output-entropy
  subadditivity step (`jointDifferentialEntropyPi_le_sum`) is genuine, but the
  channel↔RV decomposition and per-coord max-entropy values it needs are the same
  correlated-input wall content, absent from Mathlib.

This is type-check done (tier 2), NOT proof done: 2 `sorry` remain at the
`wall:multivariate-mi`. The achiever side is genuine. -/
@[entry_point]
theorem isParallelGaussianPerCoordRegularity_of_pieces {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (Q : Fin n → ℝ≥0)
    -- per-COORDINATE AWGN closed form for the product-input achiever
    -- (regularity-shaped: single-channel AWGN value, `p`-independent, not the
    -- conclusion equality). Supplied as a precondition; feeds the genuine
    -- structural reduction `parallelGaussianCapacity_achiever_mi`.
    (h_perCoordMI : ∀ i,
      (mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))).toReal
        = (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ))) :
    IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q := by
  refine
    { bddAbove := ?_
      achiever_mi := ?_
      max_ent := ?_ }
  · -- `bddAbove` field: global MI upper bound on correlated feasible inputs.
    -- @residual(wall:multivariate-mi)
    sorry
  · -- `achiever_mi` field: GENUINE. Product-input MI additivity (structural
    -- reduction) fed the per-coordinate AWGN closed form.
    exact parallelGaussianCapacity_achiever_mi Q N (fun i => NNReal.coe_ne_zero.mp (hN i))
      h_meas h_parallel_meas h_perCoordMI
  · -- `max_ent` field: per-coord max-entropy converse split on correlated inputs.
    -- @residual(wall:multivariate-mi)
    sorry

/-! ## Phase 0 — hypothesis-minimal headline skeleton

The headline below is the hypothesis-minimal re-publish of
`parallel_gaussian_capacity_formula` (`PerCoord.lean:367`). The previous
`h_reg : IsParallelGaussianPerCoordRegularity …` argument is unfolded into its
3 honest pieces (the same shapes the constructor above consumes), so callers
need not assemble the bundle manually.
-/

/-- **Hypothesis-minimal headline (honest restructure, 2026-05-29).** The parallel
Gaussian capacity equals the water-filling sum. The two load-bearing converse
hypotheses of the previous version (`h_bdd_global` / `h_multivar_decomp`, which
carried the converse analytic content) are dropped; the residual is now a
**transitive** `wall:multivariate-mi` `sorry` inherited from the constructor
`isParallelGaussianPerCoordRegularity_of_pieces` (its `bddAbove` / `max_ent`
fields), tracked by Lean's type-checker — no `@residual` is re-stated here per the
audit-tags convention (dependent `sorry` is managed at its source).

Genuine inputs retained: `h_kkt` / `h_opt` (water-filling optimality, L-WF1/L-WF2,
genuine — discharged by IVT/concavity, not the conclusion), `h_perCoordMI`
(per-coordinate AWGN closed form, regularity-shaped), and the regularity
preconditions `hP` / `hN` / `h_meas` / `h_parallel_meas`. The body genuinely
assembles `h_reg` via the constructor and invokes the genuine `le_antisymm`
sup-sandwich `parallel_gaussian_capacity_formula`.

This is type-check done (tier 2), NOT proof done: the only residual is the
transitive `wall:multivariate-mi` from the constructor. -/
@[entry_point]
theorem parallel_gaussian_capacity_formula_minimal {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) (h_opt : IsWaterFillingOptimal P N ν)
    -- per-COORDINATE AWGN closed form for the water-filling achiever
    -- (regularity-shaped: single-channel AWGN value, `p`-independent, not the
    -- conclusion equality). Feeds the genuine structural reduction inside the
    -- constructor's `achiever_mi` field.
    (h_perCoordMI : ∀ i,
      (mutualInfoOfChannel (gaussianReal 0 ((waterFillingPower ν N i).toNNReal))
          (awgnChannel (N i) (h_meas i))).toReal
        = (1/2) * Real.log
            (1 + ((waterFillingPower ν N i).toNNReal : ℝ) / (N i : ℝ))) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
  -- Assemble the regularity bundle from the genuine achiever piece via the
  -- constructor (whose `bddAbove` / `max_ent` carry the transitive
  -- `wall:multivariate-mi` residual), then invoke the genuine `le_antisymm`
  -- headline `parallel_gaussian_capacity_formula`.
  set Q : Fin (n + 1) → ℝ≥0 := fun i => (waterFillingPower ν N i).toNNReal with hQ_def
  have h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q :=
    isParallelGaussianPerCoordRegularity_of_pieces P N hN h_meas h_parallel_meas Q
      h_perCoordMI
  exact parallel_gaussian_capacity_formula P hP N hN h_meas h_parallel_meas
    ν h_kkt h_opt h_reg

end InformationTheory.Shannon.ParallelGaussian
