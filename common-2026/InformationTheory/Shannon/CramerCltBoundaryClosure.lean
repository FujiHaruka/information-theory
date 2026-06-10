import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Cramér / Chernoff CLT-boundary closure — Phase 1 gateway atom

Gateway atom for the `cramer-chernoff-clt-closure-moonshot-plan`: the Gaussian median
lemma `gaussianReal_Ici_eq_half`. The centred Gaussian `𝒩(0, v)` (for `v ≠ 0`) is
symmetric about the origin, so its mass on the half-line `{x | 0 ≤ x}` is exactly `1/2`.

Proof route (symmetry-by-map, plan §Approach / inventory §3): the map `x ↦ -x` sends
`{x | 0 ≤ x}` to `{x | x ≤ 0}` and fixes `gaussianReal 0 v` (`gaussianReal_map_neg` with
`μ = 0`, where `-0 = 0`), so the two half-lines carry equal mass. Their union is `univ`
(mass `1`) and their intersection is the singleton `{0}` (mass `0` by `noAtoms`), so
`measure_union_add_inter` gives `2 · (half-line) = 1`.
-/

namespace InformationTheory.Shannon.CramerCltBoundary

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The centred Gaussian `𝒩(0, v)` (with `v ≠ 0`) assigns mass exactly `1/2` to the
half-line `{x | 0 ≤ x}`. Symmetry-by-map: `x ↦ -x` swaps the two closed half-lines and
fixes `gaussianReal 0 v`. -/
theorem gaussianReal_Ici_eq_half {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | (0 : ℝ) ≤ x} = 1 / 2 := by
  set μ : Measure ℝ := gaussianReal 0 v with hμ
  -- The half-line `{x | 0 ≤ x}` as `Set.Ici 0`.
  have hIci : {x : ℝ | (0 : ℝ) ≤ x} = Set.Ici (0 : ℝ) := by
    ext x; simp [Set.mem_Ici]
  -- Step 1: symmetry-by-map gives equal mass on the two half-lines.
  have hsymm : μ (Set.Ici (0 : ℝ)) = μ (Set.Iic (0 : ℝ)) := by
    -- `x ↦ -x` fixes `gaussianReal 0 v` (`gaussianReal_map_neg`, `-0 = 0`).
    have hmap : μ.map (fun x : ℝ ↦ -x) = μ := by
      rw [hμ, gaussianReal_map_neg, neg_zero]
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Ici (0 : ℝ) = Set.Iic (0 : ℝ) := by
      ext x; simp [Set.mem_Iic]
    calc μ (Set.Ici (0 : ℝ))
        = (μ.map (fun x : ℝ ↦ -x)) (Set.Ici (0 : ℝ)) := by rw [hmap]
      _ = μ ((fun x : ℝ ↦ -x) ⁻¹' Set.Ici (0 : ℝ)) :=
          Measure.map_apply (by fun_prop) measurableSet_Ici
      _ = μ (Set.Iic (0 : ℝ)) := by rw [hpre]
  -- Step 2: union = univ, intersection = {0}.
  have hunion : Set.Ici (0 : ℝ) ∪ Set.Iic (0 : ℝ) = Set.univ := by
    rw [Set.union_comm]; exact Set.Iic_union_Ici
  have hinter : Set.Ici (0 : ℝ) ∩ Set.Iic (0 : ℝ) = {(0 : ℝ)} := by
    rw [Set.Ici_inter_Iic, Set.Icc_self]
  have hsingleton : μ ({(0 : ℝ)} : Set ℝ) = 0 := by
    haveI : NoAtoms μ := noAtoms_gaussianReal hv
    exact measure_singleton 0
  -- Step 3: `measure_union_add_inter` ⇒ `2 * μ(Ici 0) = 1`, ENNReal arithmetic.
  have htwo : 2 * μ (Set.Ici (0 : ℝ)) = 1 := by
    have hadd := measure_union_add_inter (μ := μ) (Set.Ici (0 : ℝ))
      (t := Set.Iic (0 : ℝ)) measurableSet_Iic
    rw [hunion, hinter, hsingleton, add_zero, ← hsymm, measure_univ] at hadd
    rw [two_mul, ← hadd]
  have hhalf : μ (Set.Ici (0 : ℝ)) = 1 / 2 := by
    rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), mul_comm, ← htwo, mul_comm]
  rw [hIci]; exact hhalf

end InformationTheory.Shannon.CramerCltBoundary
