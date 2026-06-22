import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite-Finset Jensen for `Real.binEntropy`, plus algebraic helpers

M3 lemma: Jensen inequality on `Real.binEntropy` over a finite Finset
(`binEntropy_jensen_finset`).

Plus two pure-ℝ algebraic identities used to recast a 2-branch sum of
`negMulLog` as a `binEntropy` term, which feeds the M5 step
`H(E | Y) ≤ binEntropy Pe`.
-/

namespace InformationTheory

open scoped BigOperators
open Finset

noncomputable section

/-- Finite-Finset Jensen specialization for `Real.binEntropy`.

If the weights `w` form a probability distribution on a finite type `ι` and
each `p i` lies in the interval `[0, 1]`, then the average of the binary
entropies is bounded by the binary entropy of the average. -/
lemma binEntropy_jensen_finset {ι : Type*} [Fintype ι]
    (w p : ι → ℝ)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hp_mem : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, w i * Real.binEntropy (p i) ≤ Real.binEntropy (∑ i, w i * p i) := by
  have hConc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) Real.binEntropy :=
    Real.strictConcave_binEntropy.concaveOn
  have h := hConc.le_map_sum
    (t := (Finset.univ : Finset ι))
    (w := w) (p := p)
    (fun i _ ↦ hw_nn i) hw_sum (fun i _ ↦ hp_mem i)
  simpa [smul_eq_mul] using h

/-- Algebraic identity used to relate sums of `negMulLog` to `binEntropy`:
`m * negMulLog (x / m) = negMulLog x + x * log m` whenever `m ≠ 0`. -/
lemma mul_negMulLog_div (m x : ℝ) (hm : m ≠ 0) :
    m * Real.negMulLog (x / m) = Real.negMulLog x + x * Real.log m := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold Real.negMulLog
    rw [Real.log_div hx hm]
    field_simp
    ring

/-- Two-branch `binEntropy` collapse:

`negMulLog p + negMulLog q - negMulLog (p + q)
   = (p + q) * binEntropy (p / (p + q))`

for `p, q ≥ 0`.  The boundary case `p + q = 0` is handled via the
convention `negMulLog 0 = 0` and `0/0 = 0` (so `binEntropy (0/0) = 0`). -/
lemma negMulLog_pair_sub_negMulLog_sum_eq_binEntropy (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p.negMulLog + q.negMulLog - (p + q).negMulLog
      = (p + q) * Real.binEntropy (p / (p + q)) := by
  by_cases hm0 : p + q = 0
  · have hp0 : p = 0 := le_antisymm (by linarith) hp
    have hq0 : q = 0 := le_antisymm (by linarith) hq
    simp [hp0, hq0]
  · have hone_sub : 1 - p / (p + q) = q / (p + q) := by
      field_simp
      ring
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hone_sub, mul_add,
        mul_negMulLog_div (p + q) p hm0, mul_negMulLog_div (p + q) q hm0]
    unfold Real.negMulLog
    ring

end

end InformationTheory
