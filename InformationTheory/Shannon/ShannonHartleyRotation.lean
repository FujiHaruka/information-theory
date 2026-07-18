import InformationTheory.Shannon.ShannonHartleyConverse
import InformationTheory.Shannon.ShannonHartleyConverseCount
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Shannon–Hartley converse — S1: isotropic-Gaussian rotation invariance

The measure-theoretic crux of the Shannon–Hartley converse rotation (leg 27, C2). An isotropic
Gaussian on `Fin k → ℝ` with per-coordinate mean `v i` and common variance `N` is invariant under
an orthogonal transformation, up to rotating the mean:

`(Measure.pi (fun i => gaussianReal (v i) N)).map (O.mulVec)`
` = Measure.pi (fun i => gaussianReal ((O v) i) N)`

for `O ∈ Matrix.orthogonalGroup (Fin k) ℝ`. This will be consumed by the downstream `errorProbAt`
rotation, which rotates a code's `testFn` family by the real orthogonal eigenvector matrix of the
band-Gram operator.

## Approach

The proof goes through characteristic functions on `EuclideanSpace ℝ (Fin k)`. By
`charFun_eq_pi_iff`, the product-measure equality reduces to the pointwise identity of
characteristic functions. Pushing the map through `charFun` (change of variables) plus the
orthogonal-matrix adjoint identities (`x ⬝ᵥ (O *ᵥ y) = (Oᵀ *ᵥ x) ⬝ᵥ y` and `O * Oᵀ = 1`) turns
the left-hand product into the right-hand one after expanding `charFun_gaussianReal` and combining
the exponentials.
-/

namespace InformationTheory.Shannon.ShannonHartley

open MeasureTheory ProbabilityTheory Matrix Complex WithLp
open scoped NNReal RealInnerProductSpace

/-- Isotropic Gaussian rotation invariance (S1): the law of `v + Z` with `Z ~ N(0, N·I)` on
`Fin k → ℝ`, pushed forward by an orthogonal matrix `O`, equals the law of `(O v) + Z`.  Concretely,
the pushforward of `Measure.pi (fun i => gaussianReal (v i) N)` under `O.mulVec` is
`Measure.pi (fun i => gaussianReal ((O.mulVec v) i) N)`. -/
theorem measurePi_gaussianReal_map_orthogonal {k : ℕ} (N : ℝ≥0) (v : Fin k → ℝ)
    (O : Matrix (Fin k) (Fin k) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin k) ℝ) :
    (Measure.pi (fun i => gaussianReal (v i) N)).map (fun y => O.mulVec y)
      = Measure.pi (fun i => gaussianReal ((O.mulVec v) i) N) := by
  have hmeas : Measurable (fun y : Fin k → ℝ => O.mulVec y) := by fun_prop
  have hmeasToLp : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) := by
    fun_prop
  haveI : IsProbabilityMeasure
      ((Measure.pi (fun i => gaussianReal (v i) N)).map (fun y => O.mulVec y)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  -- adjoint identity for `mulVec`/`dotProduct`
  have hadj : ∀ (M : Matrix (Fin k) (Fin k) ℝ) (a b : Fin k → ℝ),
      (M *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Mᵀ *ᵥ b) := by
    intro M a b
    rw [dotProduct_comm (M *ᵥ a) b, dotProduct_mulVec, mulVec_transpose,
      dotProduct_comm (b ᵥ* M) a]
  refine (charFun_eq_pi_iff (μ := fun i => gaussianReal ((O.mulVec v) i) N)).mp ?_
  intro t
  set t' : Fin k → ℝ := fun i => t i with ht'
  -- LHS reduction: change of variables + inner-product adjoint, then `charFun_pi`
  have hLHS : charFun ((((Measure.pi (fun i => gaussianReal (v i) N)).map
        (fun y => O.mulVec y))).map (WithLp.toLp 2)) t
      = ∏ i, charFun (gaussianReal (v i) N) ((Oᵀ *ᵥ t') i) := by
    rw [Measure.map_map hmeasToLp hmeas]
    have hinner : charFun ((Measure.pi (fun i => gaussianReal (v i) N)).map
          (WithLp.toLp 2 ∘ fun y => O.mulVec y)) t
        = charFun ((Measure.pi (fun i => gaussianReal (v i) N)).map (WithLp.toLp 2))
            (WithLp.toLp 2 (Oᵀ *ᵥ t')) := by
      rw [charFun_apply, charFun_apply,
        integral_map (by fun_prop) (by fun_prop),
        integral_map (by fun_prop) (by fun_prop)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Function.comp_apply]
      have hIP : (inner ℝ (WithLp.toLp 2 (O *ᵥ x)) t : ℝ)
          = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (Oᵀ *ᵥ t')) := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
        simpa [dotProduct, mul_comm] using hadj O x t'
      rw [hIP]
    rw [hinner, charFun_pi]
  rw [hLHS]
  -- product identity via `charFun_gaussianReal`
  have hmean : (Oᵀ *ᵥ t') ⬝ᵥ v = t' ⬝ᵥ (O *ᵥ v) := by
    rw [hadj Oᵀ t' v, transpose_transpose]
  have hnorm : (Oᵀ *ᵥ t') ⬝ᵥ (Oᵀ *ᵥ t') = t' ⬝ᵥ t' := by
    rw [hadj Oᵀ t' (Oᵀ *ᵥ t'), transpose_transpose, mulVec_mulVec,
      (mem_orthogonalGroup_iff (Fin k) ℝ).mp hO, one_mulVec]
  simp only [charFun_gaussianReal]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  congr 1
  have key : ∀ (w m : Fin k → ℝ),
      ∑ i, ((w i : ℂ) * (m i) * I - (N : ℂ) * (w i) ^ 2 / 2)
        = (↑(w ⬝ᵥ m) : ℂ) * I - (N : ℂ) * ↑(w ⬝ᵥ w) / 2 := by
    intro w m
    simp only [dotProduct, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [key (Oᵀ *ᵥ t') v, key t' (O *ᵥ v), hmean, hnorm]

end InformationTheory.Shannon.ShannonHartley
