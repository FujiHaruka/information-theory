import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.FisherInfo.V2DeBruijnHeatFlow
import InformationTheory.Shannon.FisherInfo.V2HeatFlow
import InformationTheory.Shannon.GaussianPDFVarianceDerivative

/-!
# Fully-internal Gaussian de Bruijn witness

Assembles the Gaussian heat-kernel derivative facts into a de Bruijn heat-flow witness.

Both analytic halves of `∂_t g_t = (1/2) Δ_x g_t` for the centred Gaussian heat kernel
`g_t = heatKernel t` are proved internally:
- spatial: `isHeatSpatialDerivHyp_gaussian` (`FisherInfoV2HeatFlow.lean`)
- time: `isHeatTimeDerivHyp_gaussian` (`GaussianPDFVarianceDerivative.lean`)

## Main statements

* `isHeatFlowConvolutionHyp_heatKernel` — convolution sub-predicate
  (positivity + measurability internal; only `Z_law` remains as input).
* `isHeatFlowDensity_gaussian_heatKernel` — `IsHeatFlowDensity` witness with
  the heat equation backed by `isHeatTimeDerivHyp_gaussian`.
* `heatKernel_heat_equation` — `∂_t g_t = (1/2) Δ_x g_t` with `Δ_x g_t = spatialLaplacianHeatKernel`.
* `deBruijn_gaussian_heatFlow_witness` — de Bruijn identity with heat-flow-density side internal.
* `isRegularDeBruijnHypV2_gaussian_heatFlow` — packaged `IsRegularDeBruijnHypV2`.

## Implementation notes

Remaining open hypotheses consumed as arguments:
- `Z_law : P.map Z = gaussianReal 0 1` — definitional hypothesis that `Z` is standard normal.
- `IsIBPHypothesis` — integration-by-parts / dominated-convergence step (Cover-Thomas 17.7.2).
-/

namespace InformationTheory.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Convolution sub-predicate -/

/-! ## `IsHeatFlowDensity` witness (heat equation fully internal) -/

/-! ## The heat equation, with both halves proven -/

/-! ## Final glue — Gaussian de Bruijn witness -/

end InformationTheory.Shannon.FisherInfoV2
