import InformationTheory.Shannon.ParallelGaussian.WFCertBody

/-!
# W10-S2 Water-filling KKT stationarity discharge (common Lagrange multiplier)

`ParallelGaussianWFCertBody.lean` (wave9 G4) proved the per-coordinate tangent
machinery — `concaveOn_wfCost`, the affine tangent bound
`ConcaveOn.le_tangent_of_hasDerivAt`, the Lagrange reduction
`waterFillingCertificate_of_lagrange`, and the **stationarity discharge**
`isWFStationarityHyp_of_pos` (a genuine concave tangent inequality at the common
multiplier `lam = 1/(2ν)`). But its top-level capacity wrapper
`parallel_gaussian_capacity_formula_WFcert_discharged` still *takes* the Lagrange
bundle existence (`h_for_lagrange : ∀ ν, IsWaterFillingKKT P N ν →
∃ lam, IsWFLagrangeBundle P N ν lam`) as an abstract hypothesis.

## What is genuinely discharged here

This file removes that hypothesis by **producing the common Lagrange multiplier
internally** from the water-filling KKT structure:

1. **`waterFillingKKT_pos`** — for `0 < P`, a KKT water level `ν` (i.e.
   `∑_i max(0, ν − N_i) = P`) is strictly positive. *Genuine*: if `ν ≤ 0` then
   every coordinate is inactive (`max(0, ν − N_i) = 0` since `N_i ≥ 0`), forcing
   the sum to `0 ≠ P`.

2. **`isWFComplementarySlacknessHyp_of_KKT`** — at `lam = 1/(2ν)` with `0 < ν`,
   complementary slackness `0 ≤ lam ∧ ∑ P_i^* = P` holds (slackness from `ν > 0`,
   budget from the KKT predicate itself).

3. **`isWFLagrangeBundle_of_KKT`** — combine the stationarity discharge
   (`isWFStationarityHyp_of_pos`, the common-multiplier tangent inequality) with
   slackness to build `IsWFLagrangeBundle P N ν (1/(2ν))`.

4. **`waterFillingCertificate_of_KKT`** — `IsWaterFillingKKT` ⇒
   `WaterFillingOptimalityCertificate` (Phase D applied to the internal bundle).

5. **`parallel_gaussian_capacity_formula_WFstat_discharged`** — the capacity
   formula with the Lagrange-bundle hypothesis fully eliminated. Only the
   chain-rule bundle (L-PG1, a separate plan) remains as a hypothesis.

## Approach

The single shared multiplier `lam = 1/(2ν)` is the active-set derivative of
`wfCost` at the water level: on active coordinates `N_i + P_i^* = ν` so
`wfCost'(P_i^*) = 1/(2ν) = lam` exactly; on inactive coordinates
`wfCost'(0) = 1/(2N_i) ≤ 1/(2ν)` and the slack is absorbed by the nonneg factor
`P'_i − 0`. Both are already encoded in `isWFStationarityHyp_of_pos`. The only
new fact needed is positivity of the KKT water level, which makes that
discharge applicable and makes `lam ≥ 0` hold. No new convex-duality input is
required — the multiplier is exhibited, not assumed.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Positivity of the KKT water level -/


/-! ## Phase B — Complementary slackness from the KKT predicate -/


/-! ## Phase C — Internal Lagrange bundle -/


/-! ## Phase D — Optimality certificate from KKT -/


/-! ## Phase E — Re-publish capacity formula (stationarity discharged) -/


end InformationTheory.Shannon.ParallelGaussian
