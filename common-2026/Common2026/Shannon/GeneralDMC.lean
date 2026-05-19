import Common2026.Shannon.BlockwiseChannel
import Mathlib.Analysis.Subadditive

/-!
# General DMC capacity (limit form) — publish layer (I-2 seed)

This file is a thin **publish** layer on top of `BlockwiseChannel.lean`. It
re-exports the limit-form capacity definition and four publish-surface
theorems under a dedicated `GeneralDMC` namespace so that downstream seeds
(`AWGN`, `MAC`, `BC`, `RelayCutset`, …) can refer to
`GeneralDMC.capacity_lim` directly without depending on `BlockwiseChannel`
plumbing names.

For the **memoryless** case (the bridge target of I-2), every publish theorem
is fully discharged via `BlockwiseChannel.capacity_lim_eq_capacity_of_memoryless`.
For the **fully general** case (Han–Verdú spectral form / informationally
stable channels) the publish theorems are exposed in **hypothesis-form**
(retreat lines L-GD1 / L-GD2 of the I-2 plan): the limit-existence /
monotonicity hypothesis is taken as an explicit argument and consumed
pass-through. L-GD3 (Han–Verdú spectral form) is scoped out.

## Main publish surface

* `GeneralDMC.capacity_lim` — namespace abbrev for
  `BlockwiseChannel.capacity_lim`.
* `GeneralDMC.capacity_lim_tendsto_of_memoryless` — for `ofMemoryless W`, the
  per-letter capacity sequence converges to `capacity W` (memoryless concrete
  form of L-GD1).
* `GeneralDMC.capacity_lim_exists_of_memoryless` — limit-existence corollary
  in `∃ ℓ, Tendsto …` shape (memoryless concrete form of L-GD1).
* `GeneralDMC.capacity_lim_exists_of_subadditive` — Fekete-based general
  pass-through (L-GD1 hypothesis-form): given a real-valued subadditive
  surrogate that bounds the per-letter capacity, the limit exists.
* `GeneralDMC.capacity_lim_eq_capacity_of_memoryless` — alias of the
  `BlockwiseChannel` main theorem (the I-2 main publish target).
* `GeneralDMC.capacity_lim_nonneg_of_memoryless` — nonnegativity in the
  memoryless case (direct from the equality + `capacity_nonneg`).
* `GeneralDMC.capacity_lim_monotone_in_n_of_memoryless` — the per-letter
  sequence `(capacityN _ n).toReal / n` is monotone in `n` for memoryless
  channels (in fact eventually constant).
* `GeneralDMC.capacity_lim_pass_through_of_eventually_const` — hypothesis-form
  pass-through (L-GD2): if the per-letter sequence is eventually equal to
  some constant `c`, then `capacity_lim = c`.

## Design

This file is intentionally signature-stable: it does **not** redefine
`BlockwiseChannel`, `capacityN`, or `capacity_lim`, and adds no new
mathematical content beyond statement-level pass-through. The four
"publish bullets" requested in the I-2 roadmap (`capacity_lim_exists`,
`capacity_lim_nonneg`, `capacity_lim_monotone_in_n`,
`capacity_lim_eq_capacity_of_memoryless`) are split into a **concrete
memoryless flavour** (discharged 0-sorry from `BlockwiseChannel`) and a
**general hypothesis-form flavour** (retreat lines L-GD1 / L-GD2, taking
the relevant hypothesis as an explicit argument), per the plan.

## References

* `docs/shannon/general-dmc-plan.md`
* `docs/shannon/general-dmc-mathlib-inventory.md`
* `Common2026/Shannon/BlockwiseChannel.lean`
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
abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  BlockwiseChannel α β

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- General DMC capacity, **limit form**:
`lim_{n → ∞} (1/n) · sup_{p} I(p; W_n)`. Re-export of
`BlockwiseChannel.capacity_lim`. -/
noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  BlockwiseChannel.capacity_lim W

@[simp] lemma capacity_lim_def (W : BlockwiseChannel α β) :
    capacity_lim W = BlockwiseChannel.capacity_lim W := rfl

/-- The per-block capacity sequence, in `ℝ`-valued per-letter normalization.
This is the sequence whose `lim_{n→∞}` defines `capacity_lim`. -/
noncomputable def capacityRate (W : BlockwiseChannel α β) (n : ℕ) : ℝ :=
  (W.capacityN n).toReal / n

@[simp] lemma capacityRate_def (W : BlockwiseChannel α β) (n : ℕ) :
    capacityRate W n = (W.capacityN n).toReal / n := rfl

@[simp] lemma capacity_lim_eq_limUnder (W : BlockwiseChannel α β) :
    capacity_lim W = Filter.atTop.limUnder (capacityRate W) := rfl

/-! ## Memoryless concrete flavour

Pass-through of `BlockwiseChannel.capacity_lim_eq_capacity_of_memoryless` plus
its three immediate corollaries (existence, nonnegativity, monotonicity).
-/

section Memoryless

variable
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- For memoryless `W`, the per-letter capacity sequence is **eventually
constant** equal to `capacity W`. This is the workhorse used by all three
memoryless-flavour corollaries below. -/
theorem capacityRate_ofMemoryless_eventually_const
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    ∀ᶠ n : ℕ in Filter.atTop,
      capacityRate (BlockwiseChannel.ofMemoryless W) n = capacity W := by
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hn_pos : 0 < n := hn
  have hN := capacityN_ofMemoryless_eq W n hn_pos
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  have hmul_nn : 0 ≤ (n : ℝ) * capacity W :=
    mul_nonneg (by exact_mod_cast hn_pos.le) hC_nn
  unfold capacityRate
  rw [hN, ENNReal.toReal_ofReal hmul_nn]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  field_simp

/-- Memoryless concrete L-GD1 (Tendsto-form): the per-letter capacity sequence
of `ofMemoryless W` converges to `capacity W`. -/
theorem capacity_lim_tendsto_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    Filter.Tendsto (capacityRate (BlockwiseChannel.ofMemoryless W))
      Filter.atTop (nhds (capacity W)) := by
  refine (tendsto_const_nhds (x := capacity W)).congr' ?_
  exact (capacityRate_ofMemoryless_eventually_const W).mono (fun n hn => hn.symm)

/-- Memoryless concrete L-GD1 (existence form): the limit of the per-letter
capacity sequence of `ofMemoryless W` exists. -/
theorem capacity_lim_exists_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    ∃ ℓ : ℝ, Filter.Tendsto (capacityRate (BlockwiseChannel.ofMemoryless W))
      Filter.atTop (nhds ℓ) :=
  ⟨capacity W, capacity_lim_tendsto_of_memoryless W⟩

/-- **Main bridge** (I-2 target): for memoryless `W`, the general DMC
limit-form capacity coincides with the single-letter capacity. Alias of
`BlockwiseChannel.capacity_lim_eq_capacity_of_memoryless`. -/
theorem capacity_lim_eq_capacity_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    capacity_lim (BlockwiseChannel.ofMemoryless W) = capacity W :=
  InformationTheory.Shannon.ChannelCoding.capacity_lim_eq_capacity_of_memoryless W

/-- Memoryless flavour of `capacity_lim_nonneg`. -/
theorem capacity_lim_nonneg_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    0 ≤ capacity_lim (BlockwiseChannel.ofMemoryless W) := by
  rw [capacity_lim_eq_capacity_of_memoryless W]
  exact capacity_nonneg W

/-- Memoryless concrete L-GD2: the per-letter sequence is **constant** equal
to `capacity W` on every positive index. Trivially monotone in `n`. -/
theorem capacityRate_ofMemoryless_eq
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W]
    {n : ℕ} (hn : 1 ≤ n) :
    capacityRate (BlockwiseChannel.ofMemoryless W) n = capacity W := by
  have hN := capacityN_ofMemoryless_eq W n hn
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hmul_nn : 0 ≤ (n : ℝ) * capacity W := mul_nonneg hn_nn hC_nn
  unfold capacityRate
  rw [hN, ENNReal.toReal_ofReal hmul_nn]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  field_simp

/-- Memoryless flavour of `capacity_lim_monotone_in_n`: the per-letter
sequence is monotone in `n` for `1 ≤ m ≤ n` (vacuously, since it is the
constant `capacity W` there). -/
theorem capacity_lim_monotone_in_n_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W]
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    capacityRate (BlockwiseChannel.ofMemoryless W) m
      = capacityRate (BlockwiseChannel.ofMemoryless W) n := by
  rw [capacityRate_ofMemoryless_eq W hm,
      capacityRate_ofMemoryless_eq W (hm.trans hmn)]

end Memoryless

/-! ## General hypothesis-form flavour

For non-memoryless channels, limit existence and monotonicity are taken as
explicit hypotheses (retreat lines L-GD1 / L-GD2). These versions are
intentionally minimal pass-through wrappers around `Subadditive.tendsto_lim`
and `Filter.Tendsto.limUnder_eq` — no new mathematical content; the goal is
to publish a stable downstream-facing API.
-/

section General

variable (W : BlockwiseChannel α β)

/-- Pass-through monotonicity: if the per-letter capacity rate is eventually
equal to a constant `c`, then `capacity_lim W = c`. Allows downstream code to
state monotonicity hypotheses (`L-GD2`) and feed them through. -/
theorem capacity_lim_pass_through_of_eventually_const
    {c : ℝ}
    (h_const : ∀ᶠ n : ℕ in Filter.atTop, capacityRate W n = c) :
    capacity_lim W = c := by
  have h_tendsto : Filter.Tendsto (capacityRate W) Filter.atTop (nhds c) := by
    refine (tendsto_const_nhds (x := c)).congr' ?_
    exact h_const.mono (fun n hn => hn.symm)
  unfold capacity_lim
  show Filter.atTop.limUnder (fun n => (W.capacityN n).toReal / n) = c
  exact (show Filter.Tendsto (fun n => (W.capacityN n).toReal / n) Filter.atTop (nhds c) from
    h_tendsto).limUnder_eq

/-- L-GD1 pass-through: if the *unnormalized* per-block capacity sequence
`(capacityN W n).toReal` is subadditive in `n` and bounded below per
`Subadditive.tendsto_lim`, then the per-letter sequence `capacityRate W`
converges. Hypothesis-form: the subadditivity premise is deferred to a
caller (concrete proof reserved for Han–Verdú spectral form, out of I-2
scope per L-GD3). -/
theorem capacity_lim_exists_of_subadditive
    (h_sub : Subadditive (fun n : ℕ => (W.capacityN n).toReal))
    (h_bdd : BddBelow (Set.range fun n : ℕ => (W.capacityN n).toReal / n)) :
    ∃ ℓ : ℝ, Filter.Tendsto (capacityRate W) Filter.atTop (nhds ℓ) :=
  ⟨h_sub.lim, h_sub.tendsto_lim h_bdd⟩

end General

end InformationTheory.Shannon.GeneralDMC
