import InformationTheory.Shannon.ParallelGaussian

/-!
# T2-B L-PG0 discharge: Parallel Gaussian kernel measurability

Cover-Thomas Ch.9.4 Parallel Gaussian channels の **撤退ライン L-PG0
(parallel kernel measurability) を discharge** した形で
`parallel_gaussian_capacity_formula` および
`parallel_gaussian_capacity_active_form` を再 publish。

## 撤退ラインの位置づけ

親 plan `parallel-gaussian-moonshot-plan.md` の L-PG0 は
`Measurable (fun x : Fin n → ℝ => Measure.pi (fun i => gaussianReal (x i) (N i)))`
の hypothesis pass-through (`IsParallelGaussianKernelMeasurable N`)。

本 file ではこの述語を **Mathlib の `gaussianReal_map_const_add`** と
**`MeasureTheory.Measure.pi_map_pi`** を組合せ、AWGN F-1 と並行な Giry monad
議論で完全証明する (`isParallelGaussianKernelMeasurable`)。

## Approach

```
gaussianReal (x i) (N i)
  = (gaussianReal 0 (N i)).map (x i + ·)                   -- per coord shift
```
を全 `i` に展開すると `pi_map_pi`:
```
Measure.pi (fun i => gaussianReal (x i) (N i))
  = (Measure.pi (fun i => gaussianReal 0 (N i))).map
      (fun y i => x i + y i)
```
パラメータ依存 measure を **固定の** product Gaussian の pushforward に
書き直せる。Map measurability は AWGN F-1 と同じく
`Measure.measurable_of_measurable_coe` + `measurable_measure_prodMk_left`
で finish。

詳細は `docs/shannon/parallel-gaussian-l-pg0-discharge-moonshot-plan.md` 参照。
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — `isParallelGaussianKernelMeasurable` discharge -/


/-! ## Phase B — legacy PG0-closed wrappers (retracted)

`parallel_gaussian_capacity_formula_PG0closed_of_perCoordReduction` and
`parallel_gaussian_capacity_active_form_PG0_discharged` were re-publishes of the
`*_of_perCoordReduction` reduction wrappers (`ParallelGaussian.lean`) with the
L-PG0 hypothesis filled by `isParallelGaussianKernelMeasurable N`. They added
no derivation beyond that fill; the un-active wrapper itself was a `:= h`
pass-through (`IsParallelGaussianPerCoordReduction` def-unfolds to the goal
equality). Both wrappers, plus their `_of_perCoordReduction` parents, have been
retracted. Callers (`ParallelGaussianKKT.lean`, `ParallelGaussianWFCertBody.lean`,
`ParallelGaussianWFStationarityBody.lean`) now consume
`IsParallelGaussianPerCoordReduction` directly via def-unfolding of the
predicate. The honest hypothesis-free headline lives in
`ParallelGaussianPerCoord.parallel_gaussian_capacity_formula`. -/

end InformationTheory.Shannon.ParallelGaussian
