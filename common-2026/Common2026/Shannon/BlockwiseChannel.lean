import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.ChannelCodingShannonTheorem
import Common2026.Shannon.MIChainRule
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Blockwise channel + capacity limit form (I-2 seed)

A `BlockwiseChannel α β` is a sequence of kernels
`W_n : Kernel (Fin n → α) (Fin n → β)` (one per block length). The **general**
DMC capacity is the asymptotic per-letter capacity

  capacity_lim W := lim_{n → ∞} (1/n) · sup_{p^n} I(X^n; Y^n)

For memoryless DMC (`ofMemoryless W`, with all `W_n := ⊗_n W`), this reduces
to the single-letter formula `capacity W` via Fekete's lemma applied to the
(here linear in `n`) sequence `capacityN W n`.

## Main definitions

* `BlockwiseChannel α β := (n : ℕ) → Kernel (Fin n → α) (Fin n → β)`
* `Channel.toBlock W n`  — inductive product kernel `W^{⊗n}`.
* `BlockwiseChannel.ofMemoryless W := fun n => W.toBlock n` — memoryless extension.
* `BlockwiseChannel.capacityN W n : ℝ≥0∞` — per-block capacity (`sSup` MI over
  probability inputs).
* `BlockwiseChannel.capacity_lim W : ℝ` — asymptotic per-letter capacity.

## Main results

* `capacityN_ofMemoryless_eq` — Phase 4-α: `(ofMemoryless W).capacityN n` matches
  `n · capacity W` (per-`n` equality, via `mutualInfo_iid_eq_nsmul`).
* `capacity_lim_eq_capacity_of_memoryless` — Phase 4-β: limit form matches the
  single-letter capacity.

Design judgements (see `docs/shannon/general-dmc-plan.md`):

* `BlockwiseChannel` is the **function form** `(n : ℕ) → Kernel _ _`. No marginal
  consistency axiom; sufficient for memoryless extension + AWGN/MAC/BC seeds.
* `Channel.toBlock` is built inductively via `MeasurableEquiv.piFinSuccAbove`
  (Mathlib has no `Kernel.pi` for finite product of kernels).
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## `BlockwiseChannel` definition -/

variable {α β : Type*}

/-- A **blockwise channel** is a sequence of kernels, one per block length `n`. -/
def BlockwiseChannel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  (n : ℕ) → Kernel (Fin n → α) (Fin n → β)

variable [MeasurableSpace α] [MeasurableSpace β]

/-! ## `Channel.toBlock W` : the i.i.d. block extension of `W`

Built inductively via `MeasurableEquiv.piFinSuccAbove 0`:

* `Channel.toBlock W 0 = Kernel.const _ (Measure.dirac default)`
  (degenerate — the only function `Fin 0 → β` is the trivial one).
* `Channel.toBlock W (n+1)` is obtained by:
  - Splitting `Fin (n+1) → α ≃ᵐ α × (Fin n → α)` via `piFinSuccAbove 0`.
  - Forming the parallel kernel `W ×ₖ (Channel.toBlock W n)` (after `comap`).
  - Mapping back to `Fin (n+1) → β` via the same equiv on the codomain.
-/

/-- Inductive `Kernel.pi` for the constant-family case (memoryless extension). -/
noncomputable def Channel.toBlock (W : Channel α β) : (n : ℕ) → Kernel (Fin n → α) (Fin n → β)
  | 0 => Kernel.const _ (Measure.dirac default)
  | n + 1 =>
    -- `e : (Fin (n+1) → γ) ≃ᵐ γ × (Fin n → γ)` for γ = α (via `piFinSuccAbove 0`).
    let eα : (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
    let eβ : (Fin (n + 1) → β) ≃ᵐ β × (Fin n → β) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => β) 0
    -- precompose `W ×ₖ toBlock W n` with `eα`, then push forward by `eβ.symm`.
    (((W.comap (Prod.fst : α × (Fin n → α) → α) measurable_fst) ×ₖ
      ((Channel.toBlock W n).comap (Prod.snd : α × (Fin n → α) → Fin n → α)
        measurable_snd)).comap eα eα.measurable).map eβ.symm

/-- `Channel.toBlock W n` is a Markov kernel when `W` is. -/
instance Channel.toBlock.instIsMarkovKernel (W : Channel α β) [IsMarkovKernel W] :
    ∀ n : ℕ, IsMarkovKernel (Channel.toBlock W n)
  | 0 => by
      unfold Channel.toBlock
      infer_instance
  | n + 1 => by
      unfold Channel.toBlock
      have _ : IsMarkovKernel (Channel.toBlock W n) := Channel.toBlock.instIsMarkovKernel W n
      exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

/-! ## `BlockwiseChannel.ofMemoryless` -/

/-- Memoryless block extension: `ofMemoryless W n := W.toBlock n`. -/
noncomputable def BlockwiseChannel.ofMemoryless
    (W : Channel α β) [IsMarkovKernel W] : BlockwiseChannel α β :=
  fun n => W.toBlock n

instance BlockwiseChannel.ofMemoryless.instIsMarkovKernel
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsMarkovKernel ((BlockwiseChannel.ofMemoryless W) n) :=
  Channel.toBlock.instIsMarkovKernel W n

/-! ## `capacityN` and `capacity_lim` -/

/-- Per-block capacity: `sup_{p : prob measure on (Fin n → α)} I(p; W_n)`.
Type is `ℝ≥0∞` to match `mutualInfoOfChannel`. -/
noncomputable def BlockwiseChannel.capacityN
    (W : BlockwiseChannel α β) (n : ℕ) : ℝ≥0∞ :=
  sSup ((fun p : Measure (Fin n → α) => mutualInfoOfChannel p (W n)) ''
        { p : Measure (Fin n → α) | IsProbabilityMeasure p })

theorem BlockwiseChannel.capacityN_nonneg (W : BlockwiseChannel α β) (n : ℕ) :
    0 ≤ W.capacityN n := bot_le

/-- The asymptotic per-letter capacity:
`capacity_lim W := lim_{n → ∞} (capacityN W n).toReal / n`.

When the limit does not exist this returns Mathlib's junk value `0`. The
memoryless specialization (`capacity_lim_eq_capacity_of_memoryless`) provides
the only existence guarantee in this file; general subadditivity (Fekete) is
out of scope for the I-2 seed. -/
noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)

/-! ## Phase 4-α — `capacityN_ofMemoryless_eq` (per-`n` equality)

When `W_n = W^{⊗n}` is the memoryless extension of a single-letter Markov kernel,
the block capacity is `n · capacity W`. The `≥` direction is achieved by the
i.i.d. input `p^n` where `p` is the single-letter capacity-achieving distribution
(`mutualInfo_iid_eq_nsmul`). The `≤` direction follows from
`mutualInfo_le_sum_per_letter_of_memoryless_strong`. -/

/-- Phase 4-α: per-`n` block-capacity equality for memoryless `W`. -/
theorem capacityN_ofMemoryless_eq
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) (_hn : 0 < n) :
    (BlockwiseChannel.ofMemoryless W).capacityN n
      = ENNReal.ofReal ((n : ℝ) * capacity W) := by
  sorry

/-! ## Phase 4-β — `capacity_lim_eq_capacity_of_memoryless` -/

/-- Phase 4-β: limit form matches the single-letter `capacity W` in the
memoryless case. Direct from Phase 4-α (the sequence is eventually the constant
`capacity W`). -/
theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (W : Channel α β) [IsMarkovKernel W] :
    (BlockwiseChannel.ofMemoryless W).capacity_lim = capacity W := by
  -- For `n ≥ 1`, Phase 4-α gives `(capacityN (ofMemoryless W) n).toReal = n * capacity W`,
  -- so `(capacityN _).toReal / n = capacity W`. The sequence is eventually constant.
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  -- Build the eventual-equality witness.
  have h_eq_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ) = capacity W := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn_pos : 0 < n := hn
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hN := capacityN_ofMemoryless_eq W n hn_pos
    rw [hN]
    -- ENNReal.ofReal (n * capacity W).toReal = n * capacity W since `n * capacity W ≥ 0`.
    have hmul_nn : 0 ≤ (n : ℝ) * capacity W := mul_nonneg (by exact_mod_cast hn_pos.le) hC_nn
    rw [ENNReal.toReal_ofReal hmul_nn]
    field_simp
  -- The constant sequence tends to its constant.
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ => ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ))
        Filter.atTop (nhds (capacity W)) := by
    refine (tendsto_const_nhds (x := capacity W)).congr' ?_
    exact h_eq_eventually.mono (fun n hn => hn.symm)
  -- Apply `limUnder_eq`.
  unfold BlockwiseChannel.capacity_lim
  exact h_tendsto.limUnder_eq

end InformationTheory.Shannon.ChannelCoding
