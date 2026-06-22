import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BlockwiseChannel.MemorylessCapacity

/-!
# Blockwise channel capacity: the asymptotic limit form

For memoryless DMC, the asymptotic per-letter capacity
`capacity_lim W := lim_{n → ∞} (1/n) · sup_{p^n} I(X^n; Y^n)` matches the
single-letter `capacity W`. This follows directly from the per-`n` equality
`capacityN_ofMemoryless_eq` (the sequence is eventually the constant
`capacity W`).

## Main results

* `capacity_lim_eq_capacity_of_memoryless` — the limit form matches the
  single-letter capacity.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## `capacity_lim_eq_capacity_of_memoryless` -/

/-- Limit form matches the single-letter `capacity W` in the memoryless case.
Direct from the per-`n` equality (the sequence is eventually the constant
`capacity W`). -/
@[entry_point]
theorem capacity_lim_eq_capacity_of_memoryless
    {α β : Type*}
    [Fintype α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
    [Fintype β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
    (W : Channel α β) [IsMarkovKernel W] :
    (BlockwiseChannel.ofMemoryless W).capacity_lim = capacity W := by
  classical
  have hC_nn : 0 ≤ capacity W := capacity_nonneg W
  have h_eq_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ) = capacity W := by
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩
    have hn_pos : 0 < n := hn
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hN := capacityN_ofMemoryless_eq W n hn_pos
    rw [hN]
    have hmul_nn : 0 ≤ (n : ℝ) * capacity W := mul_nonneg (by exact_mod_cast hn_pos.le) hC_nn
    rw [ENNReal.toReal_ofReal hmul_nn]
    field_simp
  have h_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ ((BlockwiseChannel.ofMemoryless W).capacityN n).toReal / (n : ℝ))
        Filter.atTop (nhds (capacity W)) := by
    refine (tendsto_const_nhds (x := capacity W)).congr' ?_
    exact h_eq_eventually.mono (fun n hn ↦ hn.symm)
  unfold BlockwiseChannel.capacity_lim
  exact h_tendsto.limUnder_eq


end InformationTheory.Shannon.ChannelCoding
