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
core — flagged tier 5 by independent honesty audit. Those hypotheses were dropped.

**Converse closure progress** (2026-05-29,
[parallel-gaussian-converse-closure-plan.md](../../../docs/shannon/parallel-gaussian-converse-closure-plan.md)):
all three constructor fields are now **structurally genuine** — every field reduces
to a named lemma, no load-bearing hypothesis survives in the constructor body:

* `achiever_mi` field — **fully genuine** (0 sorry / 0 @residual; product-input MI
  additivity `parallelGaussianCapacity_achiever_mi`, discharging the per-coordinate
  AWGN closed form in-body).
* `bddAbove` field — **genuine reduction** to `parallel_bddAbove_miImage`
  (`ParallelGaussianConverse.lean`): the constant `p`-independent water-filling sum
  caps every feasible MI value, via `log` monotonicity on the Phase 3 split.
* `max_ent` field — **genuine reduction** to `parallel_per_input_mi_le_sum`
  (`ParallelGaussianConverse.lean`).

Both converse reductions inherit a single transitive
`@residual(plan:parallel-gaussian-converse-closure-plan)` `sorry` located in
`parallel_per_input_mi_le_sum` (Phase 3 per-coord max-entropy split); the Phase 2
channel↔RV decomposition lift (`parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub`)
is **genuine, sorryAx-free**. The wall was reclassified from `wall:multivariate-mi`
to `plan:…-closure-plan` per the inventory's self-buildable verdict.

The headline `parallel_gaussian_capacity_formula_minimal` keeps the genuine
water-filling optimality inputs (`h_kkt` / `h_opt`), assembles `h_reg` via the
constructor, and invokes the genuine `le_antisymm` sup-sandwich; its only residual
is the transitive Phase 3 `sorry` (tracked by the type-checker, not re-stated here).

Status: type-check done (tier 2). This file is `0 sorry`; the sole transitive
residual lives in `ParallelGaussianConverse.parallel_per_input_mi_le_sum`.
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

/-- **Constructor (converse closure, 2026-05-29).** Assemble
`IsParallelGaussianPerCoordRegularity` from genuine pieces only — every field
reduces to a named lemma, no load-bearing hypothesis survives in the body.

* `achiever_mi` field — **fully genuine** (0 sorry / 0 @residual). Built from
  `parallelGaussianCapacity_achiever_mi` (the genuine structural per-channel
  decomposition: product-input MI additivity on `gaussianProductInput Q`,
  sorryAx-free), which discharges the per-coordinate AWGN closed form in-body
  via `awgn_perCoord_mi_closed_form`.
* `bddAbove` field — **genuine reduction** to `parallel_bddAbove_miImage`
  (`ParallelGaussianConverse.lean`): the constant `p`-independent water-filling sum
  `∑ᵢ (1/2)log(1+P/Nᵢ)` caps every feasible MI value (each `P'ᵢ ≤ P` + `log`
  monotonicity on the Phase 3 split).
* `max_ent` field — **genuine reduction** to `parallel_per_input_mi_le_sum`
  (`ParallelGaussianConverse.lean`).

Both converse fields are now fully genuine: the formerly transitive
`plan:parallel-gaussian-converse-5-closure` `sorry` inside
`parallel_per_input_mi_le_sum` (joint log-density integrability #5) was closed
2026-05-29 (multivariate mixture-density lift, `@audit:ok`), so both
`parallel_bddAbove_miImage` and `parallel_per_input_mi_le_sum` are sorryAx-free.

This file is `0 sorry`. Both the converse side **and** L-WF2 (water-filling
optimality) are now fully genuine: L-WF2 is derived internally from `h_kkt` via the
genuine, sorryAx-free, independently-audited (`@audit:ok`) `KKT.isWaterFillingOptimal_of_kkt`
(2026-06-13 closure) rather than carried as a load-bearing `h_opt` hypothesis. So
`parallel_gaussian_capacity_formula_minimal` is **proof done** —
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free), with the
genuine `h_kkt` (L-WF1, IVT-dischargeable) as its only remaining precondition. -/
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
  · -- `bddAbove` field: GENUINE reduction to the Phase 3 converse split
    -- (`parallel_bddAbove_miImage`, `ParallelGaussianConverse.lean`), now
    -- fully sorryAx-free after #5 (joint log-density integrability) closure.
    exact parallel_bddAbove_miImage P hP N hN h_meas h_parallel_meas
  · -- `achiever_mi` field: GENUINE. Product-input MI additivity (structural
    -- reduction) discharges the per-coordinate AWGN closed form in-body.
    exact parallelGaussianCapacity_achiever_mi Q N (fun i => NNReal.coe_ne_zero.mp (hN i))
      h_meas h_parallel_meas
  · -- `max_ent` field: GENUINE reduction to the Phase 3 converse split
    -- (`parallel_per_input_mi_le_sum`, `ParallelGaussianConverse.lean`), now
    -- fully sorryAx-free after #5 (joint log-density integrability) closure.
    intro p hp
    haveI : IsProbabilityMeasure p := hp.1
    exact parallel_per_input_mi_le_sum P hP N hN h_meas h_parallel_meas p hp

/-! ## Phase 0 — hypothesis-minimal headline skeleton

The headline below is the hypothesis-minimal re-publish of
`parallel_gaussian_capacity_formula` (`PerCoord.lean:367`). The previous
`h_reg : IsParallelGaussianPerCoordRegularity …` argument is unfolded into its
3 honest pieces (the same shapes the constructor above consumes), so callers
need not assemble the bundle manually.
-/

/-- **Hypothesis-minimal headline (honest restructure).** The parallel Gaussian
capacity equals the water-filling sum.

History of dropped load-bearing hypotheses:
* `h_bdd_global` / `h_multivar_decomp` (converse analytic content): dropped; the
  formerly transitive `plan:parallel-gaussian-converse-...` `sorry` from
  `parallel_per_input_mi_le_sum` (joint log-density integrability #5) was **closed**
  2026-05-29, so the converse side is fully sorryAx-free.
* `h_perCoordMI` (tier-5, flagged by the 2026-05-29 honesty audit): dropped; the
  constructor discharges the per-coord AWGN closed form in-body via
  `awgn_perCoord_mi_closed_form` (hypothesis-free, sorryAx-free).
* `h_opt` (L-WF2 water-filling optimality): dropped 2026-06-13; previously a
  load-bearing hypothesis (the optimization core), it is now derived internally from
  `h_kkt` via the genuine, sorryAx-free, independently-audited (`@audit:ok`)
  `KKT.isWaterFillingOptimal_of_kkt`.

Genuine input retained: `h_kkt` (L-WF1, water level uses the budget — a genuine
precondition pinning `ν`, IVT-dischargeable via `exists_waterFillingKKT_of_pos`),
plus the regularity preconditions `hP` / `hN` / `h_meas` / `h_parallel_meas`. The
body assembles `h_reg` via the constructor and invokes the genuine `le_antisymm`
sup-sandwich `parallel_gaussian_capacity_formula`.

This is **proof done**: `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free). The only remaining input is the genuine `h_kkt` precondition (L-WF1,
itself IVT-dischargeable); achiever, converse, per-coord closed form, and L-WF2
optimality are all genuine. -/
@[entry_point]
theorem parallel_gaussian_capacity_formula_minimal {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
  -- Assemble the regularity bundle from the genuine achiever piece via the
  -- constructor (`bddAbove` / `max_ent`, both genuine — #5 closed), then invoke the
  -- genuine `le_antisymm` headline `parallel_gaussian_capacity_formula` (which derives
  -- L-WF2 optimality internally from `h_kkt`).
  set Q : Fin (n + 1) → ℝ≥0 := fun i => (waterFillingPower ν N i).toNNReal with hQ_def
  have h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q :=
    isParallelGaussianPerCoordRegularity_of_pieces P hP.le N hN h_meas h_parallel_meas Q
  exact parallel_gaussian_capacity_formula P hP N hN h_meas h_parallel_meas
    ν h_kkt h_reg

end InformationTheory.Shannon.ParallelGaussian
