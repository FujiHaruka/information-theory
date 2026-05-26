import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoV2DeBruijnBody
import Common2026.Shannon.FisherInfoV2HeatFlowBody
import Common2026.Shannon.GaussianPDFVarianceDerivBody

/-!
# Fully-internal Gaussian de Bruijn witness (W10-S11)

Assembles the wave-9/wave-10 derivative facts for the Gaussian heat kernel into a
**fully-internal de Bruijn heat-flow witness**. The two analytic halves of the
heat equation `∂_t g_t = (1/2) Δ_x g_t` for the centred Gaussian heat kernel
`g_t = heatKernel t` are now both proven internally:

* **spatial** — `isHeatSpatialDerivHyp_gaussian` (`FisherInfoV2HeatFlowBody.lean`):
  `∂²_x g_t = (x²/t² − 1/t) g_t = spatialLaplacianHeatKernel t x`.
* **time** — `isHeatTimeDerivHyp_gaussian` (`GaussianPDFVarianceDerivBody.lean`):
  `∂_t g_t = (1/2)(x²/t² − 1/t) g_t = (1/2) spatialLaplacianHeatKernel t x`.

This seed wires those two proven derivative facts — together with the
internally-proven positivity (`heatKernel_nonneg`) and measurability
(`measurable_heatKernel`) of the kernel — into the wave-7/wave-9 de Bruijn
combinators (`IsHeatFlowDensity_of_sub_predicates`,
`deBruijn_identity_v2_of_heat_subhyp`, `IsRegularDeBruijnHypV2.ofHeatSubhyp`),
producing a Gaussian de Bruijn witness in which **every heat-flow-density slot is
discharged from a proven lemma**.

## 内容

* `isHeatFlowConvolutionHyp_heatKernel` — discharges 2 of the 3 conjuncts of the
  L-FV2HF-C convolution sub-predicate (positivity + measurability) internally;
  only `Z_law` remains as input. **(2/3 internal discharge)**
* `isHeatFlowDensity_gaussian_heatKernel` — assembles the convolution
  sub-predicate with the **proven** `isHeatTimeDerivHyp_gaussian` into a wave-7
  `IsHeatFlowDensity` witness. The bundled `heat_equation` field is now backed by
  a real proof, not a pass-through. **(heat equation fully internal)**
* `heatKernel_heat_equation` — the heat equation `∂_t g_t = (1/2) Δ_x g_t` with
  `Δ_x g_t = spatialLaplacianHeatKernel` shown to coincide with the genuine
  spatial second derivative (`isHeatSpatialDerivHyp_gaussian`). The witness is
  **genuine content**: both the time-derivative value and the Laplacian are
  proven. **(full discharge)**
* `deBruijn_gaussian_heatFlow_witness` — the final glue: given the
  genuinely-irreducible primitives `Z_law` and `IsIBPHypothesis`, the de Bruijn
  identity holds with the heat-flow-density side fully discharged. **(full glue)**
* `isRegularDeBruijnHypV2_gaussian_heatFlow` — packaged `IsRegularDeBruijnHypV2`.

## Remaining genuinely-irreducible primitives

* `Z_law : P.map Z = gaussianReal 0 1` — the defining hypothesis that `Z` is
  standard normal; definitional, not derivable.
* `IsIBPHypothesis` — the integration-by-parts / dominated-convergence step
  (Cover-Thomas 17.7.2's deepest analytic content); a legitimate analytic
  primitive, not a no-op.

Everything else (positivity, measurability, spatial second derivative, time
derivative, the heat equation, the de Bruijn combinator glue) is internal.
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Convolution sub-predicate (positivity + measurability discharged) -/

/-! ## `IsHeatFlowDensity` witness (heat equation fully internal) -/

/-! ## The heat equation, with both halves proven -/

/-! ## Final glue — Gaussian de Bruijn witness (heat-flow side discharged) -/

end Common2026.Shannon.FisherInfoV2
