import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Cramér / Chernoff CLT-boundary closure — foundations (Phase 1-2)

Two foundational pieces for closing the boundary case `a = tilted mean` of
`IsTiltedWindowEventuallyLarge` (left open by the interior LLN-squeeze
`tiltedWindow_eventually_large_of_cgfDeriv_interior`).  Both are downstream
ingredients for the CLT-based boundary discharge.

* `gaussianReal_Ici_eq_half` — **Gaussian median**: a centered Gaussian with
  non-degenerate variance puts mass `1/2` on the closed half-line `{x | 0 ≤ x}`.
  Mathlib-absent; proved via `gaussianReal_map_neg` symmetry + `noAtoms`.
* `tendsto_measure_Ici_of_tendsto_gaussian` — **portmanteau half-line bridge**:
  if a sequence of probability measures on `ℝ` converges weakly to a
  non-degenerate centered Gaussian, then the half-line masses converge to `1/2`.
  Assembled from `tendsto_measure_of_null_frontier_of_tendsto'` + `frontier_Ici`
  + `noAtoms_gaussianReal` + `gaussianReal_Ici_eq_half`.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal NNReal

/-- **Gaussian median**: a centered Gaussian with non-degenerate variance puts
mass `1/2` on the closed half-line `{x | 0 ≤ x}`.  Mathlib-absent; proved via
`gaussianReal_map_neg` symmetry + `noAtoms_gaussianReal`. -/
theorem gaussianReal_Ici_eq_half {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | (0 : ℝ) ≤ x} = 1 / 2 := by
  set μ : Measure ℝ := gaussianReal 0 v with hμ
  set A : Set ℝ := {x : ℝ | (0 : ℝ) ≤ x} with hA
  set B : Set ℝ := {x : ℝ | x ≤ (0 : ℝ)} with hB
  have hAmeas : MeasurableSet A := measurableSet_Ici
  have hBmeas : MeasurableSet B := measurableSet_Iic
  -- Symmetry: the half-line masses agree, via `x ↦ -x`.
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' A = B := by
    ext x; simp only [hA, hB, Set.mem_preimage, Set.mem_setOf_eq, neg_nonneg]
  have hsym : μ A = μ B := by
    have hmap : μ.map (fun x : ℝ ↦ -x) = μ := by
      rw [hμ, gaussianReal_map_neg]; simp
    calc
      μ A = μ.map (fun x : ℝ ↦ -x) A := by rw [hmap]
      _ = μ ((fun x : ℝ ↦ -x) ⁻¹' A) := by
            rw [Measure.map_apply measurable_neg hAmeas]
      _ = μ B := by rw [hpre]
  -- Union covers everything, intersection is the null point `{0}`.
  have hunion : A ∪ B = Set.univ := by
    ext x
    simp only [hA, hB, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total 0 x
  have hinter : A ∩ B = {(0 : ℝ)} := by
    ext x
    simp only [hA, hB, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx0, hx1⟩; exact le_antisymm hx1 hx0
    · rintro rfl; exact ⟨le_refl _, le_refl _⟩
  haveI : NoAtoms μ := noAtoms_gaussianReal hv
  have hinter0 : μ (A ∩ B) = 0 := by rw [hinter]; exact measure_singleton _
  have huniv : μ (A ∪ B) = 1 := by rw [hunion, measure_univ]
  -- `μ(A∪B) + μ(A∩B) = μ A + μ B`, i.e. `2 * μ A = 1`.
  have htwo : 2 * μ A = 1 := by
    have hkey := measure_union_add_inter (μ := μ) A hBmeas
    rw [huniv, hinter0, add_zero, ← hsym] at hkey
    rw [two_mul]
    exact hkey.symm
  -- Solve `2 * μ A = 1` for `μ A = 1 / 2` in `ℝ≥0∞`.
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  exact htwo

/-- **Portmanteau half-line bridge** (Gaussian limit): if `μs n` converges weakly
to a non-degenerate centered Gaussian, the closed half-line masses converge to
`1/2` (the Gaussian median). -/
theorem tendsto_measure_Ici_of_tendsto_gaussian {v : ℝ≥0} (hv : v ≠ 0)
    {μs : ℕ → ProbabilityMeasure ℝ}
    (h_lim : Tendsto μs atTop
      (𝓝 (⟨gaussianReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ))) :
    Tendsto (fun n ↦ (μs n : Measure ℝ) {x : ℝ | (0 : ℝ) ≤ x}) atTop (𝓝 (1 / 2)) := by
  set μ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 v, inferInstance⟩ with hμ
  set E : Set ℝ := {x : ℝ | (0 : ℝ) ≤ x} with hE
  have hEIci : E = Set.Ici (0 : ℝ) := rfl
  -- The frontier of the closed half-line is the null point `{0}`.
  haveI : NoAtoms (gaussianReal (0 : ℝ) v) := noAtoms_gaussianReal hv
  have E_nullbdry : (μ : Measure ℝ) (frontier E) = 0 := by
    rw [hμ, ProbabilityMeasure.coe_mk, hEIci, frontier_Ici]
    exact measure_singleton _
  -- Portmanteau half-line convergence.
  have hport :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h_lim E_nullbdry
  -- Rewrite the limit value to the Gaussian median `1/2`.
  have hlimval : (μ : Measure ℝ) E = 1 / 2 := by
    rw [hμ, ProbabilityMeasure.coe_mk, hE]
    exact gaussianReal_Ici_eq_half hv
  rwa [hlimval] at hport

end InformationTheory.Shannon.Cramer.Discharge
