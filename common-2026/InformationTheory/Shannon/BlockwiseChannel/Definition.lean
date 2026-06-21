import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondEntropyMemoryless
import Mathlib.Analysis.Subadditive
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Blockwise channel + capacity definitions

A `BlockwiseChannel α β` is a sequence of kernels
`W_n : Kernel (Fin n → α) (Fin n → β)` (one per block length). This file holds the
core definitions: the blockwise channel type, the i.i.d. block extension
`Channel.toBlock`, the memoryless extension `ofMemoryless`, and the per-block /
asymptotic capacity quantities `capacityN` / `capacity_lim`.

## Main definitions

* `BlockwiseChannel α β := (n : ℕ) → Kernel (Fin n → α) (Fin n → β)`
* `Channel.toBlock W n` — direct `Measure.pi` product kernel `W^{⊗n}`.
* `BlockwiseChannel.ofMemoryless W := fun n => W.toBlock n` — memoryless extension.
* `BlockwiseChannel.capacityN W n : ℝ≥0∞` — per-block capacity (`sSup` MI over
  probability inputs).
* `BlockwiseChannel.capacity_lim W : ℝ` — asymptotic per-letter capacity.

Design notes:

* `BlockwiseChannel` is the **function form** `(n : ℕ) → Kernel _ _`. No marginal
  consistency axiom; sufficient for the memoryless extension.
* `Channel.toBlock` is defined directly via `Measure.pi`: this makes
  the `compProd ↔ pi` bridge (`toBlock_compProd_pi_factor`, in
  `BlockwiseChannel.MemorylessCapacity`) almost definitional via
  `measurePreserving_arrowProdEquivProdArrow`, instead of an inductive
  `MeasurableEquiv.piFinSuccAbove` construction whose bridge would require
  substantial self-written plumbing.
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

Defined directly as `Kernel.mk (fun x => Measure.pi (fun i => W (x i)))` with
explicit measurability proof. This makes the `compProd ↔ pi` bridge below
definitionally tractable via `measurePreserving_arrowProdEquivProdArrow`. -/

/-- The block kernel `W^{⊗n}` of `W`, defined as `Measure.pi` of per-coordinate
applications of `W`. Requires `[IsMarkovKernel W]` so each fibre measure is a
probability measure (used in the measurability proof via the π-system route). -/
noncomputable def Channel.toBlock (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    Kernel (Fin n → α) (Fin n → β) where
  toFun x := Measure.pi (fun i : Fin n => W (x i))
  measurable' := by
    -- `Measure.pi (fun i => W (x i))` is a probability measure for each `x`, so use
    -- `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` on the cylinder
    -- π-system `pi univ '' pi univ {MeasurableSet}` generating `MeasurableSpace.pi`.
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi Set.univ '' Set.pi Set.univ
        (fun i : Fin n => { s : Set β | MeasurableSet s }))
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff] at ht
    -- On `Set.univ.pi t`, `Measure.pi (...) = ∏ i, W (x i) (t i)` by `pi_pi`.
    have h_eval : ∀ x : Fin n → α,
        Measure.pi (fun i : Fin n => W (x i)) (Set.univ.pi t)
          = ∏ i : Fin n, (W (x i)) (t i) := by
      intro x; rw [Measure.pi_pi]
    simp_rw [h_eval]
    refine Finset.measurable_prod _ ?_
    intro i _
    exact (Kernel.measurable_coe W (ht i)).comp (measurable_pi_apply i)

/-- `Channel.toBlock W n` is a Markov kernel when `W` is. -/
instance Channel.toBlock.instIsMarkovKernel (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsMarkovKernel (Channel.toBlock W n) where
  isProbabilityMeasure x := by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n => W (x i)))
    infer_instance

@[simp] lemma Channel.toBlock_apply (W : Channel α β) [IsMarkovKernel W] (n : ℕ)
    (x : Fin n → α) :
    (Channel.toBlock W n) x = Measure.pi (fun i : Fin n => W (x i)) := rfl

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
@[entry_point]
noncomputable def BlockwiseChannel.capacityN
    (W : BlockwiseChannel α β) (n : ℕ) : ℝ≥0∞ :=
  sSup ((fun p : Measure (Fin n → α) => mutualInfoOfChannel p (W n)) ''
        { p : Measure (Fin n → α) | IsProbabilityMeasure p })

@[entry_point]
theorem BlockwiseChannel.capacityN_nonneg (W : BlockwiseChannel α β) (n : ℕ) :
    0 ≤ W.capacityN n := bot_le

/-- The asymptotic per-letter capacity:
`capacity_lim W := lim_{n → ∞} (capacityN W n).toReal / n`. -/
@[entry_point]
noncomputable def BlockwiseChannel.capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => (W.capacityN n).toReal / n)

end InformationTheory.Shannon.ChannelCoding
