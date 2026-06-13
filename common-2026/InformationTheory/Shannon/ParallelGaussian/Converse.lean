import InformationTheory.Shannon.ParallelGaussian.Converse.Core
import InformationTheory.Shannon.ParallelGaussian.Converse.Regularity
import InformationTheory.Shannon.ParallelGaussian.Converse.MixtureDensity

/-!
# Parallel Gaussian converse (correlated input)

The converse pieces feeding the `bddAbove` and `max_ent` fields of the regularity bundle
`IsParallelGaussianPerCoordRegularity`, lifting the single-coordinate AWGN converse to the
`Fin n → ℝ` parallel channel.

The supporting development lives in the `Converse.*` submodules:

* `Converse.Core` — the channel↔RV mutual-information decomposition lift
  (`parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub`) and the product-measure
  absolute-continuity / entropy helpers.
* `Converse.Regularity` — the correlated-output regularity preconditions (absolute
  continuity, marginal-as-convolution, log-density integrabilities).
* `Converse.MixtureDensity` — the joint mixture output density, the per-input max-entropy
  split `parallel_per_input_mi_le_sum`, and the boundedness reduction
  `parallel_bddAbove_miImage`.

## Implementation notes

The per-input bound `parallel_per_input_mi_le_sum` requires `0 ≤ P`: the constraint set is
non-empty for `P < 0` (it contains the Dirac at 0, since `ENNReal.ofReal P = 0`), yet
`∑ P'ᵢ ≤ P < 0` with `P'ᵢ ≥ 0` is unsatisfiable, so the statement would be false there. The
constraint is threaded from the headline `parallel_gaussian_capacity_formula_minimal`.
-/
