import Mathlib.Analysis.SpecialFunctions.Log.Base
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.PrefixMachine

/-!
# The universal probability of a natural number

Cover–Thomas (2nd ed.) Theorem 14.6.1. The universal probability `universalProb x`
is the total weight `∑ 2^{-|p|}` of the self-delimiting programs `p` that output
`x`. Since the shortest such program has length `prefixComplexity x`, its single
term already gives the lower bound `2^{-K(x)} ≤ P_U(x)`, while the Kraft bound on
the self-delimiting machine gives `P_U(x) ≤ 1` on every finite subsum.

Together the two bounds place `P_U(x)` in the interval `(0, 1]`, so its real
logarithm is well defined and `-log₂ P_U(x) ≤ K(x)` — one half of Levin's coding
theorem.

## Main results

* `universalProb_ge_two_pow_neg_prefixComplexity` — the lower bound
  `2^{-K(x)} ≤ P_U(x)`.
* `universalProb_le_one` — the Kraft bound `P_U(x) ≤ 1`.
* `neg_logb_universalProb_le_prefixComplexity` — the logarithmic form
  `-log₂ P_U(x) ≤ K(x)`.
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

/-- The universal probability dominates the weight of a shortest program:
`2^{-K(x)} ≤ P_U(x)`.
@audit:ok -/
@[entry_point]
theorem universalProb_ge_two_pow_neg_prefixComplexity (x : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ prefixComplexity x ≤ universalProb x := by
  obtain ⟨p, hlen, hmem⟩ := prefixComplexity_spec x
  rw [universalProb, ← hlen]
  exact ENNReal.le_tsum (f := fun q : { q : List Bool // x ∈ prefixUniversalEval q } ↦
    (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length) ⟨p, hmem⟩

private theorem inv_two_pow_eq_ofReal (n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- The universal probability is a subprobability: `P_U(x) ≤ 1`, because every
finite subsum is a Kraft sum of valid self-delimiting programs.
@audit:ok -/
theorem universalProb_le_one (x : ℕ) : universalProb x ≤ 1 := by
  classical
  rw [universalProb, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  have hinj : Set.InjOn
      (Subtype.val : { p : List Bool // x ∈ prefixUniversalEval p } → List Bool) ↑s :=
    fun a _ b _ hab ↦ Subtype.ext hab
  have hdom : ∀ q ∈ s.image (Subtype.val :
      { p : List Bool // x ∈ prefixUniversalEval p } → List Bool),
      (prefixUniversalEval q).Dom := by
    intro q hq
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hq
    exact Part.dom_iff_mem.mpr ⟨x, r.2⟩
  calc ∑ p ∈ s, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length
      = ∑ q ∈ s.image Subtype.val, (2 : ℝ≥0∞)⁻¹ ^ q.length :=
        (Finset.sum_image (f := fun q : List Bool ↦ (2 : ℝ≥0∞)⁻¹ ^ q.length) hinj).symm
    _ = ∑ q ∈ s.image Subtype.val, ENNReal.ofReal ((1 / 2 : ℝ) ^ q.length) :=
        Finset.sum_congr rfl fun q _ ↦ inv_two_pow_eq_ofReal q.length
    _ = ENNReal.ofReal (∑ q ∈ s.image Subtype.val, (1 / 2 : ℝ) ^ q.length) :=
        (ENNReal.ofReal_sum_of_nonneg fun q _ ↦ by positivity).symm
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr (prefixUniversalEval_kraft _ hdom)

/-- The logarithmic form of the lower bound: `-log₂ P_U(x) ≤ K(x)`, one half of
Levin's coding theorem. The bound is not the degenerate `logb 2 0 = 0` reading:
`universalProb_ge_two_pow_neg_prefixComplexity` and `universalProb_le_one` pin
`P_U(x)` to `(0, 1]`.
@audit:ok -/
theorem neg_logb_universalProb_le_prefixComplexity (x : ℕ) :
    -Real.logb 2 (universalProb x).toReal ≤ (prefixComplexity x : ℝ) := by
  have hne : universalProb x ≠ ⊤ := ((universalProb_le_one x).trans_lt ENNReal.one_lt_top).ne
  have hlow : ((2 : ℝ)⁻¹) ^ prefixComplexity x ≤ (universalProb x).toReal := by
    simpa [ENNReal.toReal_pow] using
      ENNReal.toReal_mono hne (universalProb_ge_two_pow_neg_prefixComplexity x)
  have hpos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ prefixComplexity x := by positivity
  have hmono := Real.logb_le_logb_of_le (b := 2) one_lt_two hpos hlow
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one one_lt_two] at hmono
  linarith

end InformationTheory.Kolmogorov
