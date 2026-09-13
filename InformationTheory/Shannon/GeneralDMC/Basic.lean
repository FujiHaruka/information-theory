import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BlockwiseChannel.CapacityLimit

/-!
# General DMC capacity (limit form) — publish layer

This file is a thin publish layer on top of `BlockwiseChannel/`. It
re-exports the limit-form capacity definition and its memoryless corollaries
under a dedicated `GeneralDMC` namespace so that downstream modules
(`AWGN`, `MAC`, `BC`, `RelayCutset`, …) can refer to
`GeneralDMC.capacity_lim` directly without depending on `BlockwiseChannel`
plumbing names.

For the memoryless case the statements here come from `BlockwiseChannel/`: the per-letter
rate from `capacityN_ofMemoryless_eq`, and the capacity identity as an alias of
`ChannelCoding.capacity_lim_eq_capacity_of_memoryless`. The fully general case
(Han–Verdú spectral form / informationally stable channels) is out of scope; the only
general-case statement is the pass-through from an eventually-constant per-letter rate.

## Main definitions

* `GeneralDMC.Channel` — namespace abbrev for `BlockwiseChannel`.
* `GeneralDMC.capacity_lim` — namespace abbrev for
  `BlockwiseChannel.capacity_lim`.
* `GeneralDMC.capacityRate` — the per-letter capacity sequence whose limit
  defines `capacity_lim`.

## Main statements

* `GeneralDMC.capacityRate_ofMemoryless_eventually_const` — for `ofMemoryless W`
  the per-letter sequence is eventually the constant `capacity W`.
* `GeneralDMC.capacity_lim_tendsto_of_memoryless` — for `ofMemoryless W`, the
  per-letter capacity sequence converges to `capacity W` (memoryless concrete
  limit form).
* `GeneralDMC.capacity_lim_eq_capacity_of_memoryless` — alias of the
  `BlockwiseChannel` main theorem (the main publish target).
* `GeneralDMC.capacity_lim_pass_through_of_eventually_const` — if the
  per-letter sequence is eventually equal to some constant `c`, then
  `capacity_lim = c`.

## Implementation notes

This file is intentionally signature-stable: it does not redefine
`BlockwiseChannel`, `capacityN`, or `capacity_lim`, and adds no new
mathematical content beyond statement-level pass-through.

## References

* `InformationTheory/Shannon/BlockwiseChannel/Definition.lean`
-/

namespace InformationTheory.Shannon.GeneralDMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

open InformationTheory.Shannon.ChannelCoding

/-! ## Namespace abbreviations

We expose `BlockwiseChannel` and `capacity_lim` under the `GeneralDMC`
namespace as plain abbreviations, so downstream code can write
`GeneralDMC.capacity_lim W` without `open`-ing `BlockwiseChannel`.
-/

/-- A general DMC at the `BlockwiseChannel` abstraction layer. -/
@[entry_point]
abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  BlockwiseChannel α β

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- General DMC capacity, limit form:
`lim_{n → ∞} (1/n) · sup_{p} I(p; W_n)`. Re-export of
`BlockwiseChannel.capacity_lim`. -/
@[entry_point]
noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  BlockwiseChannel.capacity_lim W

/-- The per-block capacity sequence, in `ℝ`-valued per-letter normalization.
This is the sequence whose `lim_{n→∞}` defines `capacity_lim`. -/
@[entry_point]
noncomputable def capacityRate (W : BlockwiseChannel α β) (n : ℕ) : ℝ :=
  (W.capacityN n).toReal / n

/-! ## Memoryless concrete flavor

Pass-through of `ChannelCoding.capacity_lim_eq_capacity_of_memoryless` and
the eventually-constant per-letter rate it rests on.
-/

section Memoryless

variable
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq α] [DecidableEq β] in
/-- For memoryless `W`, the per-letter capacity sequence is eventually
constant equal to `capacity W`. This is the workhorse behind
`capacity_lim_tendsto_of_memoryless` below. -/
@[entry_point]
theorem capacityRate_ofMemoryless_eventually_const
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    ∀ᶠ n : ℕ in Filter.atTop,
      capacityRate (BlockwiseChannel.ofMemoryless W) n = capacity W := by
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
  have hn_pos : 0 < n := hn
  have hN := capacityN_ofMemoryless_eq W n hn_pos
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  have hmul_nn : 0 ≤ (n : ℝ) * capacity W :=
    mul_nonneg (by exact_mod_cast hn_pos.le) hC_nn
  unfold capacityRate
  rw [hN, ENNReal.toReal_ofReal hmul_nn]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  field_simp

omit [DecidableEq α] [DecidableEq β] in
/-- Memoryless concrete limit (Tendsto-form): the per-letter capacity sequence
of `ofMemoryless W` converges to `capacity W`. -/
@[entry_point]
theorem capacity_lim_tendsto_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    Filter.Tendsto (capacityRate (BlockwiseChannel.ofMemoryless W))
      Filter.atTop (nhds (capacity W)) := by
  refine (tendsto_const_nhds (x := capacity W)).congr' ?_
  exact (capacityRate_ofMemoryless_eventually_const W).mono (fun n hn ↦ hn.symm)

omit [DecidableEq α] [DecidableEq β] in
/-- Main bridge: for memoryless `W`, the general DMC
limit-form capacity coincides with the single-letter capacity. Alias of
`ChannelCoding.capacity_lim_eq_capacity_of_memoryless`. -/
@[entry_point]
theorem capacity_lim_eq_capacity_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    capacity_lim (BlockwiseChannel.ofMemoryless W) = capacity W :=
  InformationTheory.Shannon.ChannelCoding.capacity_lim_eq_capacity_of_memoryless W

end Memoryless

/-! ## General hypothesis-form flavor

For non-memoryless channels the limiting behavior of the per-letter rate is taken
as an explicit hypothesis. The wrapper below is a minimal pass-through around
`Filter.Tendsto.limUnder_eq` — no new mathematical content; the goal is
to publish a stable downstream-facing API.
-/

section General

variable (W : BlockwiseChannel α β)

/-- If the per-letter capacity rate of `W` is eventually equal to a constant `c`,
then `capacity_lim W = c`. This lets downstream code state the limiting behavior of
the per-letter sequence as a hypothesis and feed it through. -/
@[entry_point]
theorem capacity_lim_pass_through_of_eventually_const
    {c : ℝ}
    (h_const : ∀ᶠ n : ℕ in Filter.atTop, capacityRate W n = c) :
    capacity_lim W = c := by
  have h_tendsto : Filter.Tendsto (capacityRate W) Filter.atTop (nhds c) := by
    refine (tendsto_const_nhds (x := c)).congr' ?_
    exact h_const.mono (fun n hn ↦ hn.symm)
  unfold capacity_lim
  show Filter.atTop.limUnder (fun n ↦ (W.capacityN n).toReal / n) = c
  exact (show Filter.Tendsto (fun n ↦ (W.capacityN n).toReal / n) Filter.atTop (nhds c) from
    h_tendsto).limUnder_eq

end General

end InformationTheory.Shannon.GeneralDMC
