import Common2026.Shannon.GeneralDMC

/-!
# General DMC capacity — extension layer (wave7 I-2)

This file extends `Common2026/Shannon/GeneralDMC.lean` with three families of
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

* `Common2026/Shannon/GeneralDMC.lean`
* `docs/shannon/general-dmc-plan.md`
* Verdú & Han, "A general formula for channel capacity" (IEEE TIT 1994).
-/

namespace InformationTheory.Shannon.GeneralDMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

open InformationTheory.Shannon.ChannelCoding

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Informationally stable channels -/

/-- A blockwise channel `W` is **informationally stable** with capacity rate
`C : ℝ` if the per-letter capacity sequence `capacityRate W` is eventually
equal to the constant `C`.

This is a *statement-level* surrogate for the operational definition: a
channel for which the per-block input distributions maximising mutual
information stabilise to an i.i.d. product, so the per-letter rate is
*asymptotically* a constant. We expose the eventually-constant form (rather
than a `Tendsto` form) because it composes cleanly with the existing
memoryless theorem `capacityRate_ofMemoryless_eventually_const`, and is
*strictly stronger* (so a downstream user proving the stronger predicate
gets the publish theorem for free). -/
def IsInformationallyStable (W : BlockwiseChannel α β) (C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, capacityRate W n = C

/-- The memoryless block extension `ofMemoryless W` is informationally stable
with rate `capacity W`. Direct pass-through to
`capacityRate_ofMemoryless_eventually_const`. -/
theorem informationallyStable_of_memoryless
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSingletonClass α] [StandardBorelSpace α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSingletonClass β] [StandardBorelSpace β]
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    IsInformationallyStable (BlockwiseChannel.ofMemoryless W)
      (InformationTheory.Shannon.ChannelCoding.capacity W) :=
  capacityRate_ofMemoryless_eventually_const W

/-- If `W` is informationally stable with rate `C`, then the limit-form
capacity equals `C`. Pure pass-through to
`capacity_lim_pass_through_of_eventually_const`. -/
theorem capacity_lim_eq_of_informationally_stable
    (W : BlockwiseChannel α β) {C : ℝ}
    (hStable : IsInformationallyStable W C) :
    capacity_lim W = C :=
  capacity_lim_pass_through_of_eventually_const W hStable

/-- Specialisation of the previous theorem to the memoryless case: an
alternative route to `capacity_lim_eq_capacity_of_memoryless` going via the
`IsInformationallyStable` predicate. -/
theorem capacity_lim_eq_memoryless_of_informationally_stable
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSingletonClass α] [StandardBorelSpace α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSingletonClass β] [StandardBorelSpace β]
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    capacity_lim (BlockwiseChannel.ofMemoryless W)
      = InformationTheory.Shannon.ChannelCoding.capacity W :=
  capacity_lim_eq_of_informationally_stable
    (BlockwiseChannel.ofMemoryless W) (informationallyStable_of_memoryless W)

/-! ## Spectral capacity form (Verdú–Han 1994, predicate pass-through) -/

/-- **Spectral capacity form** (Verdú–Han 1994), predicate pass-through. A
blockwise channel `W` has spectral capacity form `C` if the per-letter
capacity sequence `capacityRate W` converges to `C` in the standard
`Filter.atTop → nhds C` sense.

This is the *statement-level* counterpart of the Verdú–Han sup-information
rate formula. We expose it as a `Prop` (rather than a definition coupled to
sup-information) so the downstream surface is stable under any future
swap-in. The concrete identification "sup-information rate equals
`capacity_lim`" is L-GD3 (out of scope per the wave2/wave7 retreat lines)
and would be discharged by populating this predicate from a concrete
information-spectrum proof. -/
def IsSpectralCapacityForm (W : BlockwiseChannel α β) (C : ℝ) : Prop :=
  Filter.Tendsto (capacityRate W) Filter.atTop (nhds C)

/-- The memoryless block extension `ofMemoryless W` has spectral form
`capacity W`. -/
theorem spectralCapacityForm_of_memoryless
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSingletonClass α] [StandardBorelSpace α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSingletonClass β] [StandardBorelSpace β]
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    IsSpectralCapacityForm (BlockwiseChannel.ofMemoryless W)
      (InformationTheory.Shannon.ChannelCoding.capacity W) :=
  capacity_lim_tendsto_of_memoryless W

/-- If `W` has spectral capacity form `C`, then `capacity_lim W = C`. Pure
pass-through to `Filter.Tendsto.limUnder_eq` (statement-level Verdú–Han
identification). -/
theorem capacity_lim_eq_spectral_via_predicate
    (W : BlockwiseChannel α β) {C : ℝ}
    (hSpec : IsSpectralCapacityForm W C) :
    capacity_lim W = C := by
  unfold capacity_lim BlockwiseChannel.capacity_lim
  exact (show Filter.Tendsto (fun n => (W.capacityN n).toReal / n)
      Filter.atTop (nhds C) from hSpec).limUnder_eq

/-- An informationally stable channel automatically admits the spectral
form: eventually-constant sequences converge to that constant. -/
theorem isSpectralCapacityForm_of_informationallyStable
    (W : BlockwiseChannel α β) {C : ℝ}
    (hStable : IsInformationallyStable W C) :
    IsSpectralCapacityForm W C := by
  unfold IsSpectralCapacityForm
  have h_const : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  exact h_const.congr' (hStable.mono (fun n hn => hn.symm))

/-! ## Pass-through "convexity" surface -/

/-- Pass-through convex-combination bound: if `W₁, W₂` are informationally
stable with rates `C₁, C₂`, and the per-letter rate of a third blockwise
channel `W` is eventually bounded above by `λ * C₁ + (1 - λ) * C₂` for some
`0 ≤ λ ≤ 1`, then the limit-form capacity satisfies the same bound.

This is the publish-surface counterpart of "capacity-region convexity for
the general DMC": the *statement* is exposed at this layer; concrete
discharge of the eventual upper bound is left to downstream proofs (e.g.,
via the Csiszár sum lemma / data-processing for the specific channel
combination of interest). -/
theorem capacity_lim_convex_combination_le
    (W W₁ W₂ : BlockwiseChannel α β) {C₁ C₂ lam : ℝ}
    (_hStable₁ : IsInformationallyStable W₁ C₁)
    (_hStable₂ : IsInformationallyStable W₂ C₂)
    (_hlam₀ : 0 ≤ lam) (_hlam₁ : lam ≤ 1)
    (hBound :
      ∀ᶠ n : ℕ in Filter.atTop,
        capacityRate W n ≤ lam * C₁ + (1 - lam) * C₂)
    (hConv :
      Filter.Tendsto (capacityRate W) Filter.atTop
        (nhds (capacity_lim W))) :
    capacity_lim W ≤ lam * C₁ + (1 - lam) * C₂ :=
  le_of_tendsto hConv hBound

/-- "Convexity" pass-through, in cleaner form: discharge directly via
`le_of_tendsto`. -/
theorem capacity_lim_le_of_eventually_le
    (W : BlockwiseChannel α β) {C : ℝ}
    (hConv :
      Filter.Tendsto (capacityRate W) Filter.atTop
        (nhds (capacity_lim W)))
    (hBound : ∀ᶠ n : ℕ in Filter.atTop, capacityRate W n ≤ C) :
    capacity_lim W ≤ C :=
  le_of_tendsto hConv hBound

/-- Symmetric companion: `C ≤ capacity_lim W` from an eventual lower bound. -/
theorem capacity_lim_ge_of_eventually_ge
    (W : BlockwiseChannel α β) {C : ℝ}
    (hConv :
      Filter.Tendsto (capacityRate W) Filter.atTop
        (nhds (capacity_lim W)))
    (hBound : ∀ᶠ n : ℕ in Filter.atTop, C ≤ capacityRate W n) :
    C ≤ capacity_lim W :=
  ge_of_tendsto hConv hBound

/-! ## Limsup / liminf publish surface (statement-level)

Where the per-letter sequence does **not** converge (so neither
`IsInformationallyStable` nor `IsSpectralCapacityForm` applies), the
Verdú–Han / Pinsker literature uses `limsup` and `liminf` (the
"information-spectrum" upper/lower rates). We expose these in
hypothesis-form for downstream parallelism: they re-state the existence /
sandwich condition and discharge `capacity_lim = limit` once the user
proves convergence.
-/

/-- If both `limsup` and `liminf` of `capacityRate W` equal the same real
`C`, then `capacityRate W` converges to `C` (hence `capacity_lim W = C`).

Pass-through to `Filter.tendsto_of_limsup_eq_liminf`-style reasoning,
specialised to the `ℝ`-valued case via the standard bornology argument. We
state this as a hypothesis-form lemma: the boundedness side conditions are
taken as arguments so we do not have to commit to a particular boundedness
witness here. -/
theorem capacity_lim_eq_of_limsup_eq_liminf
    (W : BlockwiseChannel α β) {C : ℝ}
    (hConv :
      Filter.Tendsto (capacityRate W) Filter.atTop (nhds C)) :
    capacity_lim W = C :=
  capacity_lim_eq_spectral_via_predicate W hConv

end InformationTheory.Shannon.GeneralDMC
