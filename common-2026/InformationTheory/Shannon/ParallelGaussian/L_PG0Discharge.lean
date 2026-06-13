import InformationTheory.Shannon.ParallelGaussian.Basic

/-!
# Parallel Gaussian kernel measurability

Discharge of the parallel kernel measurability predicate
`IsParallelGaussianKernelMeasurable N`, i.e. measurability of
`x : Fin n → ℝ ↦ Measure.pi (fun i => gaussianReal (x i) (N i))`.

## Implementation notes

Writing each coordinate `gaussianReal (x i) (N i) = (gaussianReal 0 (N i)).map (x i + ·)`
and applying `Measure.pi_map_pi` rewrites the parameter-dependent product measure as the
pushforward of a *fixed* product Gaussian, whose map measurability follows by the same
Giry-monad argument as the single-coordinate AWGN kernel.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

end InformationTheory.Shannon.ParallelGaussian
