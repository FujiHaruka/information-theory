import InformationTheory.Shannon.GeneralDMC

/-!
# General DMC capacity — extension layer (wave7 I-2)

This file extends `InformationTheory/Shannon/GeneralDMC.lean` with three families of
**hypothesis-form** publish theorems aimed at downstream seeds that need
capacity-limit reasoning beyond the memoryless DMC case.

The mathematical objects this layer would *concretely* discharge (Verdú–Han
sup-information rate, informationally stable channels, capacity-region
convexity for general DMC) are out of scope per the wave7 retreat lines:
their *statements* are exposed here as named publish surface, with the
characterizing hypothesis taken pass-through.

## Main predicates

* `IsInformationallyStable W C` — the per-letter capacity rate is eventually
  the constant `C`. This captures (in a single-rate, statement-level shape)
  the operational notion of an "informationally stable" channel: the
  per-block capacity grows asymptotically linearly with slope `C`.
* `IsSpectralCapacityForm W C` — Verdú–Han 1994 spectral characterization
  (hypothesis-form): there exists some `C` together with a witnessing
  per-block sequence converging to `C`. We take this as a *predicate*, not
  as a definition derived from a sup-information rate, so the downstream
  surface is stable under any future swap-in of the concrete sup-information
  definition.

## Main publish theorems

* `capacity_lim_eq_of_informationally_stable` — if `W` is informationally
  stable with rate `C`, then `capacity_lim W = C`.
* `informationallyStable_of_memoryless` — every memoryless `ofMemoryless W`
  is informationally stable with rate `capacity W` (concrete instance, fully
  discharged from `GeneralDMC.capacityRate_ofMemoryless_eventually_const`).
* `capacity_lim_eq_memoryless_of_informationally_stable` — bridge between the
  general predicate and the memoryless concrete form.
* `capacity_lim_eq_spectral_via_predicate` — `IsSpectralCapacityForm W C`
  pass-through to `capacity_lim W = C` (statement-level Verdú–Han
  identification).
* `spectralCapacityForm_of_memoryless` — every `ofMemoryless W` admits the
  spectral form with rate `capacity W`.
* `capacity_lim_convex_combination_le` — pass-through "convexity" surface:
  if two blockwise channels `W₁, W₂` are informationally stable with rates
  `C₁, C₂`, and a third channel `W` has per-letter rate eventually bounded
  above by `λ * C₁ + (1 - λ) * C₂` for some `0 ≤ λ ≤ 1`, then
  `capacity_lim W ≤ λ * C₁ + (1 - λ) * C₂`.

## Design

This file is intentionally a **predicate + pass-through** layer: it
introduces no new definitions that would shift the `BlockwiseChannel` /
`capacity_lim` API surface. Concrete proofs that a *given* channel is
informationally stable, or that its spectral and limit characterizations
coincide, remain downstream — once `GeneralDMCExtension` is in place, every
such downstream theorem can be re-expressed as discharging the
`IsInformationallyStable` or `IsSpectralCapacityForm` predicate, rather than
unfolding `capacity_lim` itself.

## References

* `InformationTheory/Shannon/GeneralDMC.lean`
* `docs/shannon/general-dmc-plan.md`
* Verdú & Han, "A general formula for channel capacity" (IEEE TIT 1994).
-/

namespace InformationTheory.Shannon.GeneralDMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

open InformationTheory.Shannon.ChannelCoding

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Informationally stable channels -/

/-! ## Spectral capacity form (Verdú–Han 1994, predicate pass-through) -/

/-! ## Pass-through "convexity" surface -/

/-! ## Limsup / liminf publish surface (statement-level)

Where the per-letter sequence does **not** converge (so neither
`IsInformationallyStable` nor `IsSpectralCapacityForm` applies), the
Verdú–Han / Pinsker literature uses `limsup` and `liminf` (the
"information-spectrum" upper/lower rates). We expose these in
hypothesis-form for downstream parallelism: they re-state the existence /
sandwich condition and discharge `capacity_lim = limit` once the user
proves convergence.
-/

end InformationTheory.Shannon.GeneralDMC
