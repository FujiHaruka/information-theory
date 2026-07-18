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

/-- The rotated code: rotate a `ContAwgnCode`'s orthonormal test-function family by an orthogonal
matrix `O` and post-compose the decoder with `Oᵀ = O⁻¹`. The encoder (hence the transmitted
signals and the power budget) is untouched; only the receiver's coordinate frame turns. Because
`O` is orthogonal, the rotated test functions stay orthonormal and supported in the window, so this
is again a valid `ContAwgnCode`, and (by `ContAwgnCode.rotate_averageError`) it has exactly the same
error probability. This is the coordinate change that diagonalizes the band-Gram operator in the
Shannon–Hartley converse. -/
noncomputable def ContAwgnCode.rotate {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (O : Matrix (Fin c.k) (Fin c.k) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin c.k) ℝ) : ContAwgnCode T W P M where
  encoder := c.encoder
  encoder_memLp := c.encoder_memLp
  encoder_bandlimited := c.encoder_bandlimited
  encoder_power := c.encoder_power
  k := c.k
  testFn := fun i t => ∑ j, O i j * c.testFn j t
  testFn_memLp := fun i =>
    memLp_finsetSum Finset.univ (fun j _ => (c.testFn_memLp j).const_mul (O i j))
  testFn_support := by
    intro i
    rw [Function.support_subset_iff]
    intro t ht
    by_contra htI
    apply ht
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have htfn : c.testFn j t = 0 := by
      by_contra hne
      exact htI (c.testFn_support j (Function.mem_support.mpr hne))
    rw [htfn, mul_zero]
  testFn_orthonormal := by
    intro i j
    have hInt : ∀ a b, Integrable
        (fun t => (O i a * c.testFn a t) * (O j b * c.testFn b t)) volume :=
      fun a b => ((c.testFn_memLp a).const_mul (O i a)).integrable_mul
        ((c.testFn_memLp b).const_mul (O j b))
    calc (∫ t, (∑ a, O i a * c.testFn a t) * (∑ b, O j b * c.testFn b t))
        = ∫ t, ∑ a, ∑ b, (O i a * c.testFn a t) * (O j b * c.testFn b t) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
          change (∑ a, O i a * c.testFn a t) * (∑ b, O j b * c.testFn b t)
              = ∑ a, ∑ b, (O i a * c.testFn a t) * (O j b * c.testFn b t)
          rw [Finset.sum_mul_sum]
      _ = ∑ a, ∑ b, ∫ t, (O i a * c.testFn a t) * (O j b * c.testFn b t) := by
          rw [integral_finsetSum Finset.univ
            (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hInt a b))]
          exact Finset.sum_congr rfl
            (fun a _ => integral_finsetSum Finset.univ (fun b _ => hInt a b))
      _ = ∑ a, ∑ b, O i a * O j b * (if a = b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          rw [show (fun t => (O i a * c.testFn a t) * (O j b * c.testFn b t))
                = (fun t => (O i a * O j b) * (c.testFn a t * c.testFn b t)) from by
              funext t; ring]
          rw [integral_const_mul, c.testFn_orthonormal a b]
      _ = ∑ a, O i a * O j a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq Finset.univ a (fun b => O i a * O j b)]
          simp
      _ = if i = j then 1 else 0 := by
          have hmul : ∑ a, O i a * O j a = (O * Oᵀ) i j := by
            rw [Matrix.mul_apply]
            exact Finset.sum_congr rfl (fun a _ => by rw [Matrix.transpose_apply])
          rw [hmul, (mem_orthogonalGroup_iff (Fin c.k) ℝ).mp hO, Matrix.one_apply]
  decoder := fun y => c.decoder (Oᵀ *ᵥ y)
  decoder_meas := c.decoder_meas.comp (by fun_prop)

/-- Rotating the test functions rotates the observation vector by the same matrix:
`(c.rotate O hO).observation m = O.mulVec (c.observation m)`. -/
lemma ContAwgnCode.rotate_observation {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (O : Matrix (Fin c.k) (Fin c.k) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin c.k) ℝ) (m : Fin M) :
    (c.rotate O hO).observation m = O.mulVec (c.observation m) := by
  funext i
  have hInt : ∀ j, Integrable (fun t => c.encoder m t * c.testFn j t) volume :=
    fun j => (c.encoder_memLp m).integrable_mul (c.testFn_memLp j)
  change (∫ t, c.encoder m t * (∑ j, O i j * c.testFn j t)) = (O *ᵥ c.observation m) i
  calc (∫ t, c.encoder m t * (∑ j, O i j * c.testFn j t))
      = ∫ t, ∑ j, O i j * (c.encoder m t * c.testFn j t) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        change c.encoder m t * (∑ j, O i j * c.testFn j t)
            = ∑ j, O i j * (c.encoder m t * c.testFn j t)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = ∑ j, ∫ t, O i j * (c.encoder m t * c.testFn j t) :=
        integral_finsetSum Finset.univ (fun j _ => (hInt j).const_mul (O i j))
    _ = ∑ j, O i j * c.observation m j := by
        exact Finset.sum_congr rfl (fun j _ => by
          rw [integral_const_mul]; rfl)
    _ = (O *ᵥ c.observation m) i := rfl

/-- Rotating the code by an orthogonal matrix leaves the average error probability unchanged: the
isotropic AWGN law is rotation-invariant (S1), and the decoder is pre-composed with the inverse
rotation, so the error set transports back exactly. -/
lemma ContAwgnCode.rotate_averageError {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (O : Matrix (Fin c.k) (Fin c.k) ℝ)
    (hO : O ∈ Matrix.orthogonalGroup (Fin c.k) ℝ) (N₀ : ℝ) :
    (c.rotate O hO).averageError N₀ = c.averageError N₀ := by
  have hEP : ∀ m, (c.rotate O hO).errorProbAt N₀ m = c.errorProbAt N₀ m := by
    intro m
    have hobs := c.rotate_observation O hO m
    have hmeasO : Measurable (fun y : Fin c.k → ℝ => O *ᵥ y) := by fun_prop
    have hcomp : Measurable (fun y : Fin c.k → ℝ => c.decoder (Oᵀ *ᵥ y)) :=
      c.decoder_meas.comp (by fun_prop)
    have hS_rot : MeasurableSet {y : Fin c.k → ℝ | c.decoder (Oᵀ *ᵥ y) ≠ m} :=
      hcomp (t := {x : Fin M | x ≠ m}) MeasurableSet.of_discrete
    have hpre : (fun y : Fin c.k → ℝ => O *ᵥ y) ⁻¹' {y | c.decoder (Oᵀ *ᵥ y) ≠ m}
        = {z | c.decoder z ≠ m} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [mulVec_mulVec, (mem_orthogonalGroup_iff' (Fin c.k) ℝ).mp hO, one_mulVec]
    change Measure.pi (fun i : Fin c.k =>
          gaussianReal ((c.rotate O hO).observation m i) (N₀ / 2).toNNReal)
          {y : Fin c.k → ℝ | c.decoder (Oᵀ *ᵥ y) ≠ m}
        = Measure.pi (fun i : Fin c.k => gaussianReal (c.observation m i) (N₀ / 2).toNNReal)
          {y : Fin c.k → ℝ | c.decoder y ≠ m}
    rw [hobs,
      (measurePi_gaussianReal_map_orthogonal (N₀ / 2).toNNReal (c.observation m) O hO).symm,
      Measure.map_apply hmeasO hS_rot, hpre]
  rw [ContAwgnCode.averageError, ContAwgnCode.averageError]
  simp only [hEP]

end InformationTheory.Shannon.ShannonHartley
