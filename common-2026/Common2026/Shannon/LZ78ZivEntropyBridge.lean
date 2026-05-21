import Common2026.Shannon.ShannonMcMillanBreiman
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-!
# LZ78 Ziv-inequality entropy bridge — foundational lemmas (T4-A)

This file hosts the foundational, mutually-independent lemmas of the LZ78
Ziv-inequality entropy bridge (Cover–Thomas §13.5), built on top of the
already-genuine SMB layer (`blockLogAvg`, `ShannonMcMillanBreiman.lean`).

## Main results

* `log_sum_inequality` — the (finite) **log-sum inequality**
  `(∑ aᵢ)·log((∑aᵢ)/(∑bᵢ)) ≤ ∑ aᵢ·log(aᵢ/bᵢ)`, derived from convexity of
  `x ↦ x·log x` (`Real.convexOn_mul_log`) via finite Jensen
  (`ConvexOn.map_sum_le`).
* `blockLogAvg_eq_neg_log_blockProb` — the trivial restatement
  `n · blockLogAvg μ p n ω = -log Pₙ{block ω}` for `0 < n`, the form the Ziv
  chain consumes.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Log-sum inequality** (finite form).

For nonnegative `aᵢ` and strictly positive `bᵢ` over a finite index set `s`,
`(∑ aᵢ)·log((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ·log(aᵢ/bᵢ)`.

Proved from convexity of `x ↦ x·log x` (`Real.convexOn_mul_log`) via finite
Jensen (`ConvexOn.map_sum_le`) with weights `bᵢ/(∑ b)` and points `aᵢ/bᵢ`. -/
theorem log_sum_inequality
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  -- `B := ∑ b > 0`, weights `w i = b i / B`, points `p i = a i / b i`.
  set B : ℝ := ∑ i ∈ s, b i with hB_def
  have hB_pos : 0 < B := Finset.sum_pos hb hs
  have hB_ne : B ≠ 0 := hB_pos.ne'
  set A : ℝ := ∑ i ∈ s, a i with hA_def
  -- Jensen for `x ↦ x * log x` on `Set.Ici 0`.
  have h₀ : ∀ i ∈ s, 0 ≤ b i / B := fun i hi =>
    div_nonneg (hb i hi).le hB_pos.le
  have h₁ : ∑ i ∈ s, b i / B = 1 := by
    rw [← Finset.sum_div, ← hB_def, div_self hB_ne]
  have hmem : ∀ i ∈ s, a i / b i ∈ Set.Ici (0 : ℝ) := fun i hi => by
    simp only [Set.mem_Ici]; exact div_nonneg (ha i hi) (hb i hi).le
  have hJensen :=
    Real.convexOn_mul_log.map_sum_le (t := s)
      (w := fun i => b i / B) (p := fun i => a i / b i) h₀ h₁ hmem
  -- Simplify the two `smul`-sums on `ℝ`.
  have hpt : ∀ i ∈ s, (b i / B) • (a i / b i) = a i / B := fun i hi => by
    have hbi : b i ≠ 0 := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  have hlhs_arg : (∑ i ∈ s, (b i / B) • (a i / b i)) = A / B := by
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, ← hA_def]
  have hrhs : (∑ i ∈ s, (b i / B) • ((a i / b i) * Real.log (a i / b i)))
      = ∑ i ∈ s, (a i / B) * Real.log (a i / b i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hbi : b i ≠ 0 := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  rw [hlhs_arg, hrhs] at hJensen
  -- `hJensen : (A/B) * log (A/B) ≤ ∑ (a i / B) * log (a i / b i)`.
  -- Multiply both sides by `B > 0`.
  have hkey := mul_le_mul_of_nonneg_right hJensen hB_pos.le
  calc A * Real.log (A / B)
      = (A / B) * Real.log (A / B) * B := by field_simp
    _ ≤ (∑ i ∈ s, (a i / B) * Real.log (a i / b i)) * B := hkey
    _ = ∑ i ∈ s, a i * Real.log (a i / b i) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        field_simp

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Restatement of `blockLogAvg` as a negative log block-probability.**

For `0 < n`, `n · blockLogAvg μ p n ω = -log Pₙ{block ω}` where
`Pₙ = μ.map (blockRV n)`. Trivial unfolding of the `blockLogAvg` definition;
this is the form the per-path Ziv inequality consumes. -/
theorem blockLogAvg_eq_neg_log_blockProb
    (μ : Measure Ω) (p : StationaryProcess μ α) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    (n : ℝ) * blockLogAvg μ p n ω
      = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold blockLogAvg
  field_simp

end InformationTheory.Shannon
