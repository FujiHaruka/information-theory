import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Counting
import InformationTheory.Shannon.StrongTypicality
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.Order.Basic

/-!
# Kolmogorov complexity converges to the entropy rate

For an i.i.d. source `Xs` on a finite alphabet, the expected conditional
Kolmogorov complexity of a length-`n` block, normalized by `n`, converges to the
entropy `H(X)` re-based to bits:

`(1 / n) · E[C(X^n ∣ n)] → H(X) / log 2`.

The `/ log 2` re-bases the natural-log entropy `entropy` (`Bridge.lean`, base `e`)
to the bit-length complexity `condComplexity` (base `2`).

The proof is a squeeze between an upper and a lower half. The upper half encodes
a typical block by its index inside the typical set (bits `≈ n(H+ε)`) on top of
the conditional literal bound; the lower half combines the counting bound
`#{x ∣ C(x ∣ n) < k} < 2^k` with the strong-typicality size lower bound. Both
halves are currently left as honest `sorry`s; this file establishes the flagship
statement and the plumbing lemmas the two halves consume.

## Main results

* `kolmogorov_entropy_rate` — the flagship convergence (via the two halves).
* `encodeBlock` / `encodeBlock_injective` — injective encoding of a block as `ℕ`.
* `integrable_condComplexity_jointRV` — the block-complexity integrand is integrable.
-/

namespace InformationTheory.Kolmogorov

open InformationTheory.Shannon
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

attribute [local instance] Fintype.toEncodable

section Block
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Injective encoding of a length-`m` block `Fin m → α` into a natural number,
using the `Encodable` structure a finite type carries. -/
noncomputable def encodeBlock (m : ℕ) (x : Fin m → α) : ℕ := Encodable.encode x

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem encodeBlock_injective (m : ℕ) : Function.Injective (encodeBlock (α := α) m) :=
  fun _ _ h ↦ Encodable.encode_injective h

end Block

/-! ### Base-conversion bridges (bit length `2^k` ↔ natural-log `exp`) -/

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem two_pow_eq_exp (k : ℕ) : ((2 : ℝ) ^ k) = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem exp_le_two_pow_iff (t : ℝ) (k : ℕ) :
    Real.exp t ≤ (2 : ℝ) ^ k ↔ t ≤ (k : ℝ) * Real.log 2 := by
  rw [two_pow_eq_exp, Real.exp_le_exp]

/-! ### The entropy-rate theorem -/

section Rate
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Xs : ℕ → Ω → α)

omit [DecidableEq α] [Nonempty α] in
/-- The block-complexity integrand takes finitely many values (the block space is
finite), so it is a bounded measurable function and hence integrable. -/
theorem integrable_condComplexity_jointRV (hXs : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Integrable (fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)) μ := by
  classical
  -- The block space `Fin n → α` is finite, so any function out of it is measurable.
  have hmeas_g : Measurable (fun b : Fin n → α ↦ (condComplexity (encodeBlock n b) n : ℝ)) :=
    measurable_of_finite _
  have hmeas : Measurable
      (fun ω ↦ (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ)) :=
    hmeas_g.comp (measurable_jointRV Xs hXs n)
  -- Bounded by the (finite) supremum over the finite block space.
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((Finset.univ.sup (fun b : Fin n → α ↦ condComplexity (encodeBlock n b) n) : ℕ) : ℝ) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast Finset.le_sup (f := fun b : Fin n → α ↦ condComplexity (encodeBlock n b) n)
    (Finset.mem_univ (jointRV Xs n ω))

/-- Upper half: eventually the normalized expected complexity is within `ε` above
`H / log 2`. -/
theorem kolmogorov_entropy_rate_upper
    (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (1 / (n : ℝ)) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ
        ≤ entropy μ (Xs 0) / Real.log 2 + ε := by
  sorry -- @residual(plan:kolmogorov-p4-upper)

/-- Lower half: eventually the normalized expected complexity is within `ε` below
`H / log 2`. -/
theorem kolmogorov_entropy_rate_lower
    (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      entropy μ (Xs 0) / Real.log 2 - ε
        ≤ (1 / (n : ℝ)) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ := by
  sorry -- @residual(plan:kolmogorov-p4-lower)

/-- Kolmogorov complexity converges to the entropy rate: for an i.i.d. source, the
normalized expected conditional complexity of a length-`n` block tends to the
bit-rebased entropy `H(X) / log 2` (CT 2nd ed. Thm 14.3.1). -/
@[entry_point]
theorem kolmogorov_entropy_rate
    (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i ↦ Xs i) μ)
    (hindep_pair : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a}) :
    Filter.Tendsto
      (fun n : ℕ ↦ (1 / (n : ℝ)) *
        ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ)
      Filter.atTop (nhds (entropy μ (Xs 0) / Real.log 2)) := by
  -- Squeeze between the two halves.
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [kolmogorov_entropy_rate_lower μ Xs hXs hindep_full hindep_pair hident hpos
      ((entropy μ (Xs 0) / Real.log 2 - b) / 2) (by linarith)] with n hn
    linarith
  · filter_upwards [kolmogorov_entropy_rate_upper μ Xs hXs hindep_full hindep_pair hident hpos
      ((b - entropy μ (Xs 0) / Real.log 2) / 2) (by linarith)] with n hn
    linarith

end Rate

end InformationTheory.Kolmogorov
