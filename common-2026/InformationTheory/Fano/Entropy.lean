import InformationTheory.Meta.EntryPoint
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.BigOperators

/-!
# Single-variable Shannon entropy

Non-negativity on `[0, 1]` masses, the support-restricted maximum-entropy bound (Jensen on
`Real.negMulLog`), the universe-wide specialization, and the Dirac-collapse identity.

## Implementation notes

`entropyOfFn` is the mass-function form (a sum over `α → ℝ`) used by the `Fano.Core`
development. The measure-theoretic developments (`Shannon.Bridge.entropy`,
`InformationTheory.MeasureFano.condEntropy`) use a parallel formalism; the two do not
depend on each other.
-/

namespace InformationTheory

open scoped BigOperators
open Finset

noncomputable section

/-- Shannon entropy (in nats) of a real-valued mass function on a finite type. -/
def entropyOfFn {α : Type*} [Fintype α] (μ : α → ℝ) : ℝ :=
  ∑ a, (μ a).negMulLog

/-- Shannon entropy is non-negative whenever each mass lies in `[0, 1]`. -/
@[entry_point]
lemma entropyOfFn_nonneg {α : Type*} [Fintype α]
    (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (h1 : ∀ a, μ a ≤ 1) :
    0 ≤ entropyOfFn μ :=
  Finset.sum_nonneg (fun a _ ↦ Real.negMulLog_nonneg (h0 a) (h1 a))

/-- Maximum-entropy bound, restricted to a Finset containing the support: a
probability mass function whose support is contained in `S` has Shannon
entropy at most `log S.card`. -/
lemma entropyOfFn_le_log_supportCard {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = 1)
    {S : Finset α} (hsupp : ∀ a ∉ S, μ a = 0) :
    entropyOfFn μ ≤ Real.log S.card := by
  -- Restrict the sum to `S` using the support hypothesis.
  have hsum_S : (∑ a ∈ S, μ a) = 1 := by
    refine (Finset.sum_subset S.subset_univ ?_).trans hsum
    intro a _ ha
    exact hsupp a ha
  have hS_nonempty : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hsum_S
    exact zero_ne_one hsum_S
  set n : ℕ := S.card with hn_def
  have hn_pos : 0 < n := Finset.card_pos.mpr hS_nonempty
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  -- The entropy sum collapses to `S` since `negMulLog 0 = 0`.
  have hH_eq : entropyOfFn μ = ∑ a ∈ S, (μ a).negMulLog := by
    unfold entropyOfFn
    refine (Finset.sum_subset S.subset_univ ?_).symm
    intro a _ ha
    rw [hsupp a ha, Real.negMulLog_zero]
  -- Jensen on `S` with uniform weights `1/n`.
  have hJensen :
      (∑ a ∈ S, (1 / (n : ℝ)) • (μ a).negMulLog)
        ≤ Real.negMulLog (∑ a ∈ S, (1 / (n : ℝ)) • μ a) := by
    refine Real.concaveOn_negMulLog.le_map_sum
      (t := S) (w := fun _ ↦ 1 / (n : ℝ)) (p := μ)
      (fun i _ ↦ by positivity) ?_ (fun i _ ↦ hμ i)
    rw [Finset.sum_const, nsmul_eq_mul, ← hn_def, mul_one_div, div_self hn_ne]
  have hlhs :
      (∑ a ∈ S, (1 / (n : ℝ)) • (μ a).negMulLog)
        = (1 / (n : ℝ)) * (∑ a ∈ S, (μ a).negMulLog) := by
    simp [smul_eq_mul, Finset.mul_sum]
  have hrhs_inner : (∑ a ∈ S, (1 / (n : ℝ)) • μ a) = 1 / (n : ℝ) := by
    simp [smul_eq_mul, ← Finset.mul_sum, hsum_S]
  have hneg : Real.negMulLog (1 / (n : ℝ)) = (1 / (n : ℝ)) * Real.log n := by
    have h1ne : (1 : ℝ) ≠ 0 := one_ne_zero
    rw [Real.negMulLog, Real.log_div h1ne hn_ne, Real.log_one, zero_sub, neg_mul,
      mul_neg, neg_neg]
  rw [hlhs, hrhs_inner, hneg] at hJensen
  rw [hH_eq]
  have hinv_pos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  exact le_of_mul_le_mul_left hJensen hinv_pos

/-- The maximum-entropy bound: a probability mass function on a finite type
of cardinality `n` has Shannon entropy at most `log n`. -/
@[entry_point]
lemma entropyOfFn_le_log_card {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = 1) :
    entropyOfFn μ ≤ Real.log (Fintype.card α) := by
  have h := entropyOfFn_le_log_supportCard (S := (Finset.univ : Finset α))
    μ hμ hsum (fun a ha ↦ (ha (Finset.mem_univ a)).elim)
  rwa [Finset.card_univ] at h

/-- A Dirac mass at `a₀` has zero Shannon entropy. -/
@[entry_point]
lemma entropyOfFn_eq_zero_of_isDirac {α : Type*} [Fintype α] [DecidableEq α]
    (μ : α → ℝ) (a₀ : α) (h : ∀ a, μ a = if a = a₀ then 1 else 0) :
    entropyOfFn μ = 0 := by
  unfold entropyOfFn
  apply Finset.sum_eq_zero
  intro a _
  rw [h a]
  by_cases ha : a = a₀
  · simp [ha]
  · simp [ha]

end

end InformationTheory
