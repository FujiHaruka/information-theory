import InformationTheory.Shannon.ShannonHartleyConverse
import InformationTheory.Shannon.ShannonHartleyConverseCount
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

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

open MeasureTheory ProbabilityTheory Matrix Complex WithLp TimeBandLimiting
open scoped NNReal RealInnerProductSpace ComplexConjugate

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

/-!
## S2 — real orthogonal eigenbasis of the band-Gram + count bridge

For a real, orthonormal, `[0,T]`-supported test family `φ : Fin k → ℝ → ℝ`, the band-limited Gram
`Gᵢⱼ = ⟪P_W (φᵢ)ℂ, P_W (φⱼ)ℂ⟫_ℂ` has *real* entries (the lifted functions are self-conjugate, so
each entry equals its own complex conjugate). Hence the complex-Hermitian band-Gram is the
`ℝ → ℂ`-image of a genuine real symmetric matrix `bandGramRealMatrix`, which the real spectral
theorem diagonalizes by an orthogonal matrix. This exposes, for the S3 rotation:

* `bandGramRealMatrix` / `bandGramRealEigenvalues` (`μ`) / `bandGramRealUnitary` (`O`);
* `bandGramRealUnitary_mem_orthogonalGroup` (`↑O ∈ orthogonalGroup`, feeds `ContAwgnCode.rotate`);
* `bandGramRealMatrix_diagonalize` (`Oᵀ Gᵣ O = diagonal μ`);
* `bandGramReal_high_count_le` (`#{c < μⱼ} ≤ prolateCount T W c`, the count bound of the converse).
-/

/-- A `ℂ`-valued `Lp` function that is the complex lift of a real test function is self-conjugate:
`star (testFnLift φ hmem i) = testFnLift φ hmem i`. -/
private lemma testFnLift_star {k : ℕ} (φ : Fin k → ℝ → ℝ) (hmem : ∀ i, MemLp (φ i) 2 volume)
    (i : Fin k) : star (testFnLift φ hmem i) = testFnLift φ hmem i := by
  refine Lp.ext ?_
  have hcoe : (testFnLift φ hmem i : ℝ → ℂ) =ᵐ[volume] fun t => ((φ i t : ℝ) : ℂ) :=
    MemLp.coeFn_toLp _
  filter_upwards [Lp.coeFn_star (testFnLift φ hmem i), hcoe] with t h1 h2
  rw [h1, Pi.star_apply, h2, Complex.star_def, Complex.conj_ofReal]

/-- For two self-conjugate `L²` functions, the inner product is symmetric (both integrands are real
a.e.): `⟪b, a⟫ = ⟪a, b⟫`. -/
private lemma inner_symm_of_star_fixed {a b : E} (ha : star a = a) (hb : star b = b) :
    (inner ℂ b a : ℂ) = inner ℂ a b := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have hae_a : (a : ℝ → ℂ) =ᵐ[volume] star (a : ℝ → ℂ) := by
    have h := Lp.coeFn_star a; rw [ha] at h; exact h
  have hae_b : (b : ℝ → ℂ) =ᵐ[volume] star (b : ℝ → ℂ) := by
    have h := Lp.coeFn_star b; rw [hb] at h; exact h
  filter_upwards [hae_a, hae_b] with t hta htb
  rw [Pi.star_apply] at hta htb
  rw [RCLike.inner_apply, RCLike.inner_apply, starRingEnd_apply, starRingEnd_apply,
    ← hta, ← htb, mul_comm]

/-- The real symmetric band-Gram matrix `Gᵣ ᵢⱼ = Re ⟪P_W (φᵢ)ℂ, P_W (φⱼ)ℂ⟫_ℂ` of a real test
family `φ`. Its complex lift is the band-limited Gram of `testFnLift φ hmem`, and its real
eigen-decomposition diagonalizes the band-Gram for the Shannon–Hartley converse rotation. -/
noncomputable def bandGramRealMatrix (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j =>
    (Matrix.gram ℂ (fun i => (bandLimitSubspace W).starProjection (testFnLift φ hmem i)) i j).re

/-- **B1 (gateway atom).** The band-limited Gram of the complex lift of a real test family has real
entries: it is the `ℝ → ℂ`-image of `bandGramRealMatrix`. -/
theorem bandGram_eq_map_real (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) :
    Matrix.gram ℂ (fun i => (bandLimitSubspace W).starProjection (testFnLift φ hmem i))
      = (bandGramRealMatrix W φ hmem).map (algebraMap ℝ ℂ) := by
  have hvstar : ∀ l, star ((bandLimitSubspace W).starProjection (testFnLift φ hmem l))
      = (bandLimitSubspace W).starProjection (testFnLift φ hmem l) := fun l => by
    rw [← bandLimitProj_star, testFnLift_star]
  ext i j
  simp only [Matrix.map_apply, bandGramRealMatrix, Complex.coe_algebraMap]
  refine (Complex.conj_eq_iff_re.mp ?_).symm
  rw [Matrix.gram_apply]
  calc (starRingEnd ℂ) (inner ℂ
        ((bandLimitSubspace W).starProjection (testFnLift φ hmem i))
        ((bandLimitSubspace W).starProjection (testFnLift φ hmem j)))
      = inner ℂ ((bandLimitSubspace W).starProjection (testFnLift φ hmem j))
          ((bandLimitSubspace W).starProjection (testFnLift φ hmem i)) :=
        inner_conj_symm _ _
    _ = inner ℂ ((bandLimitSubspace W).starProjection (testFnLift φ hmem i))
          ((bandLimitSubspace W).starProjection (testFnLift φ hmem j)) :=
        inner_symm_of_star_fixed (hvstar i) (hvstar j)

/-- `bandGramRealMatrix` is real-symmetric (Hermitian). -/
theorem bandGramRealMatrix_isHermitian (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) : (bandGramRealMatrix W φ hmem).IsHermitian := by
  have hvstar : ∀ l, star ((bandLimitSubspace W).starProjection (testFnLift φ hmem l))
      = (bandLimitSubspace W).starProjection (testFnLift φ hmem l) := fun l => by
    rw [← bandLimitProj_star, testFnLift_star]
  ext i j
  simp only [Matrix.conjTranspose_apply, bandGramRealMatrix, Matrix.gram_apply, star_trivial]
  rw [inner_symm_of_star_fixed (hvstar i) (hvstar j)]

/-- The eigenvalues `μ` of the real band-Gram (= per-coordinate channel gains for the converse). -/
noncomputable def bandGramRealEigenvalues (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) : Fin k → ℝ :=
  (bandGramRealMatrix_isHermitian W φ hmem).eigenvalues

/-- The orthogonal eigenvector matrix `O` diagonalizing the real band-Gram. -/
noncomputable def bandGramRealUnitary (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) : Matrix.unitaryGroup (Fin k) ℝ :=
  (bandGramRealMatrix_isHermitian W φ hmem).eigenvectorUnitary

/-- `↑O ∈ orthogonalGroup`, the hypothesis consumed by `ContAwgnCode.rotate`. -/
lemma bandGramRealUnitary_mem_orthogonalGroup (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) :
    (↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ)
      ∈ Matrix.orthogonalGroup (Fin k) ℝ :=
  (bandGramRealUnitary W φ hmem).2

/-- `↑Oᵀ ∈ orthogonalGroup` (the orthogonal group is closed under transpose). -/
lemma bandGramRealUnitary_transpose_mem_orthogonalGroup (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) :
    (↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ)ᵀ
      ∈ Matrix.orthogonalGroup (Fin k) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (Fin k) ℝ, Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff' (Fin k) ℝ).mp
    (bandGramRealUnitary_mem_orthogonalGroup W φ hmem)

/-- **Real spectral diagonalization.** `Oᵀ Gᵣ O = diagonal μ`, the frame S3 rotates the code by. -/
theorem bandGramRealMatrix_diagonalize (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) :
    (↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ)ᵀ
        * bandGramRealMatrix W φ hmem * (↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ)
      = Matrix.diagonal (bandGramRealEigenvalues W φ hmem) := by
  have h := (bandGramRealMatrix_isHermitian W φ hmem).conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] at h
  simpa only [bandGramRealUnitary, bandGramRealEigenvalues] using h

/-- The characteristic polynomial `∏ (X - C aᵢ)` has roots exactly the multiset `{aᵢ}`. -/
private lemma roots_prod_X_sub_C_fun {k : ℕ} (a : Fin k → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (a i))).roots = Multiset.map a Finset.univ.val := by
  rw [Polynomial.roots_prod]
  · simp [Polynomial.roots_X_sub_C]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- **Count bridge (converse head-count).** The number of real band-Gram eigenvalues exceeding `c`
is at most `prolateCount T W c`. The real-eigenvalue façade of
`gram_high_eigen_finrank_le_prolateCount_real`, obtained by matching the real spectrum against the
complex band-Gram spectrum at the characteristic-polynomial level. -/
theorem bandGramReal_high_count_le (T W : ℝ) {c : ℝ} (hc : 0 < c) {k : ℕ}
    (φ : Fin k → ℝ → ℝ) (hmem : ∀ i, MemLp (φ i) 2 volume)
    (h_on : ∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1 : ℝ) else 0)
    (h_supp : ∀ i, Function.support (φ i) ⊆ Set.Icc 0 T) :
    (Finset.univ.filter (fun j => c < bandGramRealEigenvalues W φ hmem j)).card
      ≤ prolateCount T W c := by
  classical
  set v : Fin k → E := fun i => (bandLimitSubspace W).starProjection (testFnLift φ hmem i) with hv_def
  have hC : (Matrix.gram ℂ v).IsHermitian := Matrix.isHermitian_gram ℂ v
  have hR := bandGramRealMatrix_isHermitian W φ hmem
  have hmap : Matrix.gram ℂ v = (bandGramRealMatrix W φ hmem).map (algebraMap ℝ ℂ) :=
    bandGram_eq_map_real W φ hmem
  -- Match the complex and real characteristic polynomials at the factored level.
  have hcharC : (Matrix.gram ℂ v).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C ((hC.eigenvalues i : ℂ))) := hC.charpoly_eq
  have hcharR : (Matrix.gram ℂ v).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C ((hR.eigenvalues i : ℂ))) := by
    rw [hmap, Matrix.charpoly_map, hR.charpoly_eq, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Complex.coe_algebraMap,
      RCLike.ofReal_real_eq_id, id_eq]
  have hprod : (∏ i, (Polynomial.X - Polynomial.C ((hC.eigenvalues i : ℂ))))
      = ∏ i, (Polynomial.X - Polynomial.C ((hR.eigenvalues i : ℂ))) := hcharC.symm.trans hcharR
  -- Hence the eigenvalue multisets coincide over ℂ, then over ℝ by injectivity of `ofReal`.
  have hroots : Multiset.map (fun i => (hC.eigenvalues i : ℂ)) Finset.univ.val
      = Multiset.map (fun i => (hR.eigenvalues i : ℂ)) Finset.univ.val := by
    rw [← roots_prod_X_sub_C_fun (fun i => (hC.eigenvalues i : ℂ)),
      ← roots_prod_X_sub_C_fun (fun i => (hR.eigenvalues i : ℂ)), hprod]
  have hcancel : Multiset.map hC.eigenvalues Finset.univ.val
      = Multiset.map hR.eigenvalues Finset.univ.val := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [Multiset.map_map, Multiset.map_map]
    exact hroots
  -- The high-eigenvalue counts are equal since they are `countP` over equal multisets.
  have hbridge : ∀ (f : Fin k → ℝ),
      (Finset.univ.filter (fun i => c < f i)).card
        = Multiset.countP (fun x => c < x) (Multiset.map f Finset.univ.val) := by
    intro f
    rw [Multiset.countP_map, ← Finset.filter_val]
    rfl
  have hfinal : (Finset.univ.filter (fun j => c < hR.eigenvalues j)).card
      = (Finset.univ.filter (fun j => c < hC.eigenvalues j)).card := by
    rw [hbridge hR.eigenvalues, hbridge hC.eigenvalues, hcancel]
  calc (Finset.univ.filter (fun j => c < bandGramRealEigenvalues W φ hmem j)).card
      = (Finset.univ.filter (fun j => c < hC.eigenvalues j)).card := hfinal
    _ = (Finset.univ.filter
          (fun j => c < bandGramEigenvalues W (testFnLift φ hmem) j)).card := rfl
    _ ≤ prolateCount T W c :=
        gram_high_eigen_finrank_le_prolateCount_real T W hc φ hmem h_on h_supp

/-!
## S3 — second-moment identity for the rotated converse code

For an arbitrary code `c`, rotating by `Oᵀ` (`O` = the band-Gram eigenvector matrix) makes the rotated
observation's per-coordinate second moment factor as `νᵢ · Qᵢ`, where `νᵢ = bandGramRealEigenvalues`
and `Qᵢ` is a per-mode input power with `∑Qᵢ ≤ T·P`. The three public deliverables consumed by the
downstream ellipsoid/water-filling leg are:

* `bandGramRealEigenvalues_nonneg` — the band-Gram is PSD, so `νᵢ ≥ 0`;
* `bandGramRealEigenvalues_le_one` — `νᵢ ≤ 1` (projection contracts the orthonormal raw frame);
* `contAwgn_rotated_secondMoment` — `∫ (x i)² ∂(rotated signal law) = νᵢ · Qᵢ`, `∑Qᵢ ≤ T·P`, `Qᵢ ≥ 0`.
-/

/-- The `i`-th eigenvector-image `gᵢ = ∑ⱼ Oⱼᵢ • P_W ψⱼ ∈ E` (column `i` of the band-Gram eigenvector
matrix `O`, applied to the projected lifts `P_W ψⱼ`). Its `E`-inner products realize the band-Gram
eigenvalues (`inner_bandGramColumn`), so `‖gᵢ‖² = νᵢ` and rotating the observation by `Oᵀ` produces
`⟨gᵢ, Fₘ⟩` per coordinate. -/
private noncomputable def bandGramColumn (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) (i : Fin k) : E :=
  ∑ j, ((↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ) j i : ℂ) •
    (bandLimitSubspace W).starProjection (testFnLift φ hmem j)

/-- The complex lift of an orthonormal (in the `∫ φᵢ φⱼ = δᵢⱼ` sense) real family is orthonormal in
`E`. -/
private lemma testFnLift_orthonormal {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume)
    (h_on : ∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1 : ℝ) else 0) :
    Orthonormal ℂ (testFnLift φ hmem) := by
  have hcoe : ∀ l, (testFnLift φ hmem l : ℝ → ℂ) =ᵐ[volume] fun t => ((φ l t : ℝ) : ℂ) :=
    fun l => MemLp.coeFn_toLp _
  rw [orthonormal_iff_ite]
  intro i j
  have hinner : (inner ℂ (testFnLift φ hmem i) (testFnLift φ hmem j) : ℂ)
      = ((∫ t, φ i t * φ j t : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hcoe i, hcoe j] with t hti htj
    rw [RCLike.inner_apply, hti, htj, Complex.conj_ofReal]
    push_cast; ring
  rw [hinner, h_on i j]
  split_ifs <;> simp

/-- **S3b.** The eigenvector images are `E`-orthogonal, with squared norm the band-Gram eigenvalue:
`⟨gᵢ, gᵢ'⟩ = δᵢᵢ' · νᵢ`. -/
private lemma inner_bandGramColumn (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) (i i' : Fin k) :
    (inner ℂ (bandGramColumn W φ hmem i) (bandGramColumn W φ hmem i') : ℂ)
      = if i = i' then (bandGramRealEigenvalues W φ hmem i : ℂ) else 0 := by
  unfold bandGramColumn
  set O := (↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ) with hO
  -- inner product of two projected raw lifts is the real band-Gram entry
  have hvinner : ∀ j l, (inner ℂ ((bandLimitSubspace W).starProjection (testFnLift φ hmem j))
        ((bandLimitSubspace W).starProjection (testFnLift φ hmem l)) : ℂ)
      = (bandGramRealMatrix W φ hmem j l : ℂ) := by
    intro j l
    have hmap := congrFun (congrFun (bandGram_eq_map_real W φ hmem) j) l
    rw [Matrix.gram_apply] at hmap
    rw [hmap, Matrix.map_apply, Complex.coe_algebraMap]
  -- expand the sesquilinear form into a double sum
  have hexp : (inner ℂ (∑ j, (O j i : ℂ) •
          (bandLimitSubspace W).starProjection (testFnLift φ hmem j))
        (∑ l, (O l i' : ℂ) •
          (bandLimitSubspace W).starProjection (testFnLift φ hmem l)) : ℂ)
      = ∑ j, ∑ l, (O j i : ℂ) * (O l i' : ℂ) * (bandGramRealMatrix W φ hmem j l : ℂ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [inner_smul_right, hvinner j l, Complex.conj_ofReal]
    ring
  rw [hexp]
  -- the real double sum is the diagonalized entry
  have hd := bandGramRealMatrix_diagonalize W φ hmem
  rw [← hO] at hd
  have hmat : (Oᵀ * bandGramRealMatrix W φ hmem * O) i i'
      = ∑ j, ∑ l, O j i * O l i' * bandGramRealMatrix W φ hmem j l := by
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))
  have hreal : (∑ j, ∑ l, O j i * O l i' * bandGramRealMatrix W φ hmem j l)
      = if i = i' then bandGramRealEigenvalues W φ hmem i else 0 := by
    rw [← hmat, hd, Matrix.diagonal_apply]
  have hcast : (∑ j, ∑ l, (O j i : ℂ) * (O l i' : ℂ) * (bandGramRealMatrix W φ hmem j l : ℂ))
      = ((∑ j, ∑ l, O j i * O l i' * bandGramRealMatrix W φ hmem j l : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, hreal]
  split_ifs <;> simp

/-- `‖gᵢ‖² = νᵢ`. -/
private lemma norm_sq_bandGramColumn (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) (i : Fin k) :
    ‖bandGramColumn W φ hmem i‖ ^ 2 = bandGramRealEigenvalues W φ hmem i := by
  have h := inner_bandGramColumn W φ hmem i i
  rw [if_pos rfl] at h
  have hself := inner_self_eq_norm_sq (𝕜 := ℂ) (bandGramColumn W φ hmem i)
  rw [h] at hself
  simpa using hself.symm

/-- **Deliverable 1.** The band-Gram is PSD, so its eigenvalues are nonnegative. -/
theorem bandGramRealEigenvalues_nonneg (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) :
    ∀ i, 0 ≤ bandGramRealEigenvalues W φ hmem i := by
  intro i
  rw [← norm_sq_bandGramColumn W φ hmem i]
  positivity

/-- `gᵢ = P_W (∑ⱼ Oⱼᵢ • ψⱼ)`: the eigenvector image is the projection of the corresponding raw-frame
combination. -/
private lemma bandGramColumn_eq_starProjection (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume) (i : Fin k) :
    bandGramColumn W φ hmem i
      = (bandLimitSubspace W).starProjection
          (∑ j, ((↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ) j i : ℂ) •
            testFnLift φ hmem j) := by
  unfold bandGramColumn
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul]

/-- The raw-frame combination indexed by a column of the orthogonal `O` has unit `E`-norm (the raw
lift is orthonormal and `O` is orthogonal). -/
private lemma norm_sq_testFnLift_combo (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume)
    (h_on : ∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1 : ℝ) else 0) (i : Fin k) :
    ‖∑ j, ((↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ) j i : ℂ) •
        testFnLift φ hmem j‖ ^ 2 = 1 := by
  have ho := testFnLift_orthonormal φ hmem h_on
  set O := (↑(bandGramRealUnitary W φ hmem) : Matrix (Fin k) (Fin k) ℝ) with hO
  -- inner product collapses to `∑ⱼ (Oⱼᵢ)²` by orthonormality
  have hinner : (inner ℂ (∑ j, (O j i : ℂ) • testFnLift φ hmem j)
        (∑ l, (O l i : ℂ) • testFnLift φ hmem l) : ℂ) = ((∑ j, O j i * O j i : ℝ) : ℂ) := by
    rw [sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_smul_left, inner_sum]
    simp_rw [inner_smul_right, orthonormal_iff_ite.mp ho, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j (fun l => (O l i : ℂ)), if_pos (Finset.mem_univ j),
      Complex.conj_ofReal]
    push_cast; ring
  -- `∑ⱼ (Oⱼᵢ)² = 1` since `O` is orthogonal (`Oᵀ O = 1`)
  have hOO : Oᵀ * O = 1 :=
    (mem_orthogonalGroup_iff' (Fin k) ℝ).mp
      (by rw [hO]; exact bandGramRealUnitary_mem_orthogonalGroup W φ hmem)
  have horth : (∑ j, O j i * O j i) = 1 := by
    have hcol := congrFun (congrFun hOO i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hcol
    simp_rw [Matrix.transpose_apply] at hcol
    exact hcol
  have hself := inner_self_eq_norm_sq (𝕜 := ℂ)
    (∑ j, (O j i : ℂ) • testFnLift φ hmem j)
  rw [hinner, horth] at hself
  simpa using hself.symm

/-- **Deliverable 2.** The band-Gram eigenvalues are at most `1` (the projection `P_W` contracts the
orthonormal raw frame). -/
theorem bandGramRealEigenvalues_le_one (W : ℝ) {k : ℕ} (φ : Fin k → ℝ → ℝ)
    (hmem : ∀ i, MemLp (φ i) 2 volume)
    (h_on : ∀ i j, (∫ t, φ i t * φ j t) = if i = j then (1 : ℝ) else 0) :
    ∀ i, bandGramRealEigenvalues W φ hmem i ≤ 1 := by
  intro i
  rw [← norm_sq_bandGramColumn W φ hmem i, bandGramColumn_eq_starProjection W φ hmem i]
  refine le_trans ?_ (le_of_eq (norm_sq_testFnLift_combo W φ hmem h_on i))
  gcongr
  exact (bandLimitSubspace W).norm_starProjection_apply_le _

/-- The complex lift of a band-limited encoder lies in `bandLimitSubspace W`. -/
private lemma testFnLift_encoder_mem_bandLimitSubspace {W : ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hbl : IsBandlimited f W) :
    ((hf.ofReal (K := ℂ)).toLp (fun t => ((f t : ℝ) : ℂ))) ∈ bandLimitSubspace W := by
  obtain ⟨hf', hvanish⟩ := hbl
  have heq : (hf.ofReal (K := ℂ)).toLp (fun t => ((f t : ℝ) : ℂ))
      = hf'.toLp (fun t : ℝ => ((f t : ℝ) : ℂ)) := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (hf.ofReal (K := ℂ)), MemLp.coeFn_toLp hf'] with t h1 h2
    exact h1.trans h2.symm
  rw [heq, bandLimitSubspace, Submodule.mem_comap]
  exact hvanish

/-- The observation `∫ (encoder m)·(testFn j)` equals `Re ⟨ψⱼ, Fₘ⟩` (real integrand, so no imaginary
part). -/
private lemma observation_eq_inner_re {T W P : ℝ} {M : ℕ} (c : ContAwgnCode T W P M)
    (m : Fin M) (j : Fin c.k) :
    c.observation m j
      = (inner ℂ (testFnLift c.testFn c.testFn_memLp j)
          (testFnLift c.encoder c.encoder_memLp m)).re := by
  have hcoeψ : (testFnLift c.testFn c.testFn_memLp j : ℝ → ℂ)
      =ᵐ[volume] fun t => ((c.testFn j t : ℝ) : ℂ) := MemLp.coeFn_toLp _
  have hcoeF : (testFnLift c.encoder c.encoder_memLp m : ℝ → ℂ)
      =ᵐ[volume] fun t => ((c.encoder m t : ℝ) : ℂ) := MemLp.coeFn_toLp _
  have hinner : (inner ℂ (testFnLift c.testFn c.testFn_memLp j)
        (testFnLift c.encoder c.encoder_memLp m) : ℂ)
      = ((∫ t, c.encoder m t * c.testFn j t : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hcoeψ, hcoeF] with t htψ htF
    rw [RCLike.inner_apply, htψ, htF, Complex.conj_ofReal]
    push_cast; ring
  rw [ContAwgnCode.observation, hinner, Complex.ofReal_re]

/-- `⟨P_W ψⱼ, Fₘ⟩ = ⟨ψⱼ, Fₘ⟩` when `Fₘ` is band-limited (self-adjoint projection + `P_W Fₘ = Fₘ`). -/
private lemma inner_starProjection_testFn_encoder {T W P : ℝ} {M : ℕ} (c : ContAwgnCode T W P M)
    (m : Fin M) (j : Fin c.k) :
    (inner ℂ ((bandLimitSubspace W).starProjection (testFnLift c.testFn c.testFn_memLp j))
        (testFnLift c.encoder c.encoder_memLp m) : ℂ)
      = inner ℂ (testFnLift c.testFn c.testFn_memLp j)
          (testFnLift c.encoder c.encoder_memLp m) := by
  have hFmem : testFnLift c.encoder c.encoder_memLp m ∈ bandLimitSubspace W :=
    testFnLift_encoder_mem_bandLimitSubspace (c.encoder_memLp m) (c.encoder_bandlimited m)
  have hPF : (bandLimitSubspace W).starProjection (testFnLift c.encoder c.encoder_memLp m)
      = testFnLift c.encoder c.encoder_memLp m := Submodule.starProjection_eq_self_iff.mpr hFmem
  rw [Submodule.inner_starProjection_left_eq_right, hPF]

/-- **S3a.** The rotated observation is `Re ⟨gᵢ, Fₘ⟩` per coordinate. -/
private lemma rotate_observation_eq_inner_re {T W P : ℝ} {M : ℕ} (c : ContAwgnCode T W P M)
    (m : Fin M) (i : Fin c.k) :
    (c.rotate (↑(bandGramRealUnitary W c.testFn c.testFn_memLp) :
          Matrix (Fin c.k) (Fin c.k) ℝ)ᵀ
        (bandGramRealUnitary_transpose_mem_orthogonalGroup W c.testFn c.testFn_memLp)).observation m i
      = (inner ℂ (bandGramColumn W c.testFn c.testFn_memLp i)
          (testFnLift c.encoder c.encoder_memLp m)).re := by
  set O := (↑(bandGramRealUnitary W c.testFn c.testFn_memLp) :
    Matrix (Fin c.k) (Fin c.k) ℝ) with hO
  rw [c.rotate_observation Oᵀ
    (bandGramRealUnitary_transpose_mem_orthogonalGroup W c.testFn c.testFn_memLp) m]
  have hg : (inner ℂ (bandGramColumn W c.testFn c.testFn_memLp i)
        (testFnLift c.encoder c.encoder_memLp m) : ℂ).re
      = ∑ j, O j i * c.observation m j := by
    unfold bandGramColumn
    rw [sum_inner, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul,
      inner_starProjection_testFn_encoder, ← observation_eq_inner_re]
  rw [hg]
  rfl

/-- `‖Fₘ‖² = ∫ (encoder m)²` (real lift). -/
private lemma norm_sq_testFnLift_encoder {T W P : ℝ} {M : ℕ} (c : ContAwgnCode T W P M) (m : Fin M) :
    ‖testFnLift c.encoder c.encoder_memLp m‖ ^ 2 = ∫ t, (c.encoder m t) ^ 2 := by
  have hcoeF : (testFnLift c.encoder c.encoder_memLp m : ℝ → ℂ)
      =ᵐ[volume] fun t => ((c.encoder m t : ℝ) : ℂ) := MemLp.coeFn_toLp _
  have hinner : (inner ℂ (testFnLift c.encoder c.encoder_memLp m)
        (testFnLift c.encoder c.encoder_memLp m) : ℂ) = ((∫ t, (c.encoder m t) ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hcoeF] with t htF
    rw [RCLike.inner_apply, htF, Complex.conj_ofReal]
    push_cast; ring
  have hself := inner_self_eq_norm_sq (𝕜 := ℂ) (testFnLift c.encoder c.encoder_memLp m)
  rw [hinner] at hself
  simpa using hself.symm

/-- The signal law's per-coordinate second moment is the empirical average of squared observations. -/
private lemma signalLaw_integral_coord_sq {T W P : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) (N₀ : ℝ) (i : Fin c.k) :
    (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c N₀))
      = (M : ℝ)⁻¹ * ∑ m : Fin M, (c.observation m i) ^ 2 := by
  have hint : ∀ m : Fin M,
      Integrable (fun x : Fin c.k → ℝ => (x i) ^ 2) (Measure.dirac (c.observation m)) :=
    fun m => integrable_dirac (by finiteness)
  rw [contAwgnSignalLaw_eq_mixture c N₀, integral_smul_measure,
    integral_finsetSum_measure (fun m _ => hint m)]
  simp_rw [integral_dirac]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- **Deliverable 3.** For an arbitrary code `c`, rotating by `Oᵀ` (the transpose of the band-Gram
eigenvector matrix) factors the rotated observation's per-coordinate second moment as `νᵢ · Qᵢ`,
where `νᵢ = bandGramRealEigenvalues` and the per-mode powers `Qᵢ ≥ 0` satisfy `∑Qᵢ ≤ T·P`. This is
the ellipsoid data the water-filling converse consumes. -/
theorem contAwgn_rotated_secondMoment {T W P N₀ : ℝ} {M : ℕ} [NeZero M]
    (c : ContAwgnCode T W P M) :
    ∃ Q : Fin c.k → ℝ, (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i ≤ T * P) ∧
      ∀ i, (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw
          (c.rotate (↑(bandGramRealUnitary W c.testFn c.testFn_memLp) :
              Matrix (Fin c.k) (Fin c.k) ℝ)ᵀ
            (bandGramRealUnitary_transpose_mem_orthogonalGroup W c.testFn c.testFn_memLp)) N₀))
        = bandGramRealEigenvalues W c.testFn c.testFn_memLp i * Q i := by
  classical
  set c' := c.rotate (↑(bandGramRealUnitary W c.testFn c.testFn_memLp) :
      Matrix (Fin c.k) (Fin c.k) ℝ)ᵀ
    (bandGramRealUnitary_transpose_mem_orthogonalGroup W c.testFn c.testFn_memLp) with hc'
  set ν : Fin c.k → ℝ := bandGramRealEigenvalues W c.testFn c.testFn_memLp with hν
  set g : Fin c.k → E := bandGramColumn W c.testFn c.testFn_memLp with hg
  set F : Fin M → E := testFnLift c.encoder c.encoder_memLp with hF
  -- shared facts
  have hνnonneg : ∀ i, 0 ≤ ν i := bandGramRealEigenvalues_nonneg W c.testFn c.testFn_memLp
  have hnormg : ∀ i, ‖g i‖ ^ 2 = ν i := fun i => norm_sq_bandGramColumn W c.testFn c.testFn_memLp i
  have hinnerg : ∀ i i', (inner ℂ (g i) (g i') : ℂ) = if i = i' then (ν i : ℂ) else 0 :=
    fun i i' => inner_bandGramColumn W c.testFn c.testFn_memLp i i'
  have hFbound : ∀ m, ‖F m‖ ^ 2 ≤ T * P :=
    fun m => (norm_sq_testFnLift_encoder c m).trans_le (c.encoder_power m)
  have hRe : ∀ z : ℂ, z.re ^ 2 ≤ ‖z‖ ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  have hAval : ∀ i, (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀))
      = (M : ℝ)⁻¹ * ∑ m : Fin M, (inner ℂ (g i) (F m) : ℂ).re ^ 2 := by
    intro i
    rw [signalLaw_integral_coord_sq c' N₀ i]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hro : c'.observation m i = (inner ℂ (g i) (F m) : ℂ).re :=
      rotate_observation_eq_inner_re c m i
    rw [hro]
  -- per-message Bessel bound
  have hbessel_m : ∀ m : Fin M,
      ∑ i, (if ν i = 0 then (0 : ℝ) else (inner ℂ (g i) (F m) : ℂ).re ^ 2 / ν i) ≤ ‖F m‖ ^ 2 := by
    intro m
    set e' : {i : Fin c.k // ν i ≠ 0} → E :=
      fun j => ((Real.sqrt (ν j.1))⁻¹ : ℂ) • g j.1 with he'
    have he'_on : Orthonormal ℂ e' := by
      rw [orthonormal_iff_ite]
      intro j j'
      simp only [he', inner_smul_left, inner_smul_right, hinnerg j.1 j'.1, map_inv₀,
        Complex.conj_ofReal]
      by_cases hjj : j = j'
      · subst hjj
        have hνpos : 0 < ν j.1 := (hνnonneg j.1).lt_of_ne (Ne.symm j.2)
        rw [if_pos rfl, if_pos rfl]
        have hid : (Real.sqrt (ν j.1))⁻¹ * (Real.sqrt (ν j.1))⁻¹ * ν j.1 = 1 := by
          rw [← mul_inv, Real.mul_self_sqrt hνpos.le, inv_mul_cancel₀ j.2]
        rw [show ((Real.sqrt (ν j.1))⁻¹ : ℂ) * (((Real.sqrt (ν j.1))⁻¹ : ℂ) * (ν j.1 : ℂ))
            = (((Real.sqrt (ν j.1))⁻¹ * (Real.sqrt (ν j.1))⁻¹ * ν j.1 : ℝ) : ℂ) by push_cast; ring,
          hid, Complex.ofReal_one]
      · rw [if_neg (fun h => hjj (Subtype.ext h)), if_neg hjj]; simp
    have hnorm_e : ∀ j : {i : Fin c.k // ν i ≠ 0},
        ‖(inner ℂ (e' j) (F m) : ℂ)‖ ^ 2 = ‖(inner ℂ (g j.1) (F m) : ℂ)‖ ^ 2 / ν j.1 := by
      intro j
      have hνpos : 0 < ν j.1 := (hνnonneg j.1).lt_of_ne (Ne.symm j.2)
      rw [he', inner_smul_left, norm_mul, mul_pow, RCLike.norm_conj, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hνpos.le]
      ring
    have hperj : ∀ j : {i : Fin c.k // ν i ≠ 0},
        (inner ℂ (g j.1) (F m) : ℂ).re ^ 2 / ν j.1 ≤ ‖(inner ℂ (e' j) (F m) : ℂ)‖ ^ 2 := by
      intro j
      have hνpos : 0 < ν j.1 := (hνnonneg j.1).lt_of_ne (Ne.symm j.2)
      rw [hnorm_e j, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hRe _) (inv_nonneg.mpr hνpos.le)
    have hsub : ∑ j : {i : Fin c.k // ν i ≠ 0}, (inner ℂ (g j.1) (F m) : ℂ).re ^ 2 / ν j.1
        = ∑ i, (if ν i = 0 then (0 : ℝ) else (inner ℂ (g i) (F m) : ℂ).re ^ 2 / ν i) := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun i => ν i ≠ 0)) (fun x => by simp)
        (fun i => (inner ℂ (g i) (F m) : ℂ).re ^ 2 / ν i), Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hνi : ν i = 0
      · rw [if_neg (not_not.mpr hνi), if_pos hνi]
      · rw [if_pos hνi, if_neg hνi]
    rw [← hsub]
    calc ∑ j : {i : Fin c.k // ν i ≠ 0}, (inner ℂ (g j.1) (F m) : ℂ).re ^ 2 / ν j.1
        ≤ ∑ j : {i : Fin c.k // ν i ≠ 0}, ‖(inner ℂ (e' j) (F m) : ℂ)‖ ^ 2 :=
          Finset.sum_le_sum (fun j _ => hperj j)
      _ ≤ ‖F m‖ ^ 2 := he'_on.sum_inner_products_le (x := F m) (s := Finset.univ)
  -- the ellipsoid witness
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMinv : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
  have hQval : ∀ i, (if ν i = 0 then (0 : ℝ)
        else (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀)) / ν i)
      = ∑ m : Fin M,
          (M : ℝ)⁻¹ * (if ν i = 0 then (0 : ℝ) else (inner ℂ (g i) (F m) : ℂ).re ^ 2 / ν i) := by
    intro i
    by_cases hνi : ν i = 0
    · simp [hνi]
    · simp_rw [if_neg hνi]
      rw [hAval i, ← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc]
  refine ⟨fun i => if ν i = 0 then 0 else (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀)) / ν i,
    ?_, ?_, ?_⟩
  · -- nonnegativity
    intro i
    change (0 : ℝ) ≤ if ν i = 0 then 0 else (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀)) / ν i
    split_ifs with hνi
    · exact le_refl 0
    · exact div_nonneg (integral_nonneg (fun x => sq_nonneg _)) (hνnonneg i)
  · -- power budget
    change ∑ i, (if ν i = 0 then (0 : ℝ)
        else (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀)) / ν i) ≤ T * P
    calc ∑ i, (if ν i = 0 then (0 : ℝ)
          else (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀)) / ν i)
        = (M : ℝ)⁻¹ * ∑ m : Fin M, ∑ i,
            (if ν i = 0 then (0 : ℝ) else (inner ℂ (g i) (F m) : ℂ).re ^ 2 / ν i) := by
          rw [Finset.sum_congr rfl (fun i _ => hQval i)]
          simp_rw [← Finset.mul_sum]
          rw [Finset.sum_comm]
      _ ≤ (M : ℝ)⁻¹ * ∑ m : Fin M, ‖F m‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => hbessel_m m)) hMinv
      _ ≤ (M : ℝ)⁻¹ * ∑ m : Fin M, (T * P) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => hFbound m)) hMinv
      _ = T * P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ hM, one_mul]
  · -- second-moment factorization
    intro i
    change (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀))
        = ν i * if ν i = 0 then 0 else (∫ x, (x i) ^ 2 ∂(contAwgnSignalLaw c' N₀)) / ν i
    by_cases hνi : ν i = 0
    · rw [if_pos hνi, mul_zero, hAval i]
      have hgi0 : g i = 0 := by
        have hn : ‖g i‖ = 0 := by
          have := hnormg i; rw [hνi] at this; nlinarith [norm_nonneg (g i)]
        exact norm_eq_zero.mp hn
      simp [hgi0]
    · rw [if_neg hνi, ← mul_div_assoc, mul_div_cancel_left₀ _ hνi]

/-- **C2 (per-code ellipsoid converse).** Rotating a `ContAwgnCode` by the real orthogonal
eigenvector matrix of the band-Gram operator turns the operational parallel-Gaussian converse
into the diagonal (eigenbasis) form: the log message count is bounded by the per-eigenvalue
parallel-Gaussian sum with gains `νᵢ = bandGramRealEigenvalues …` folded into an ellipsoid power
budget `∑ᵢ Qᵢ ≤ T·P`. Mechanically assembles the per-coordinate converse
`contAwgn_operational_converse_percoord` applied to the rotated code with the rotation
second-moment factorization `contAwgn_rotated_secondMoment`. -/
theorem contAwgn_converse_ellipsoid {T W P N₀ : ℝ} {M : ℕ}
    (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hM : 2 ≤ M)
    (c : ContAwgnCode T W P M) (Pe : ℝ) (hPe : Pe = (c.averageError N₀).toReal) :
    ∃ Q : Fin c.k → ℝ, (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i ≤ T * P)
      ∧ Real.log M ≤ (∑ i : Fin c.k, (1/2) * Real.log
            (1 + bandGramRealEigenvalues W c.testFn c.testFn_memLp i * Q i / (N₀ / 2)))
          + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hNpos : (0 : ℝ) < N₀ / 2 := by positivity
  -- Rotate the code by the (transpose of the) real orthogonal eigenvector matrix of the band-Gram.
  set c' := c.rotate (↑(bandGramRealUnitary W c.testFn c.testFn_memLp) :
      Matrix (Fin c.k) (Fin c.k) ℝ)ᵀ
    (bandGramRealUnitary_transpose_mem_orthogonalGroup W c.testFn c.testFn_memLp) with hc'
  set ν : Fin c.k → ℝ := bandGramRealEigenvalues W c.testFn c.testFn_memLp with hν
  -- The rotation leaves the average error probability unchanged.
  have hPe' : Pe = (c'.averageError N₀).toReal := by
    rw [hc', ContAwgnCode.rotate_averageError]; exact hPe
  -- Per-coordinate operational parallel-Gaussian converse for the rotated code.
  obtain ⟨P', hP'nn, hP'percoord, hP'log⟩ :=
    contAwgn_operational_converse_percoord hN₀ hP hM c' Pe hPe'
  -- Rotation second-moment factorization: the ellipsoid witness `Q` with `∫ (xᵢ)² = νᵢ · Qᵢ`.
  obtain ⟨Q, hQnn, hQsum, hQid⟩ := contAwgn_rotated_secondMoment c
  refine ⟨Q, hQnn, hQsum, ?_⟩
  -- Per-coordinate: `P'ᵢ ≤ νᵢ · Qᵢ`, hence a per-coordinate log bound.
  have hP'le : ∀ i, P' i ≤ ν i * Q i := fun i => (hP'percoord i).trans (hQid i).le
  have hlog_le : ∀ i, (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
      ≤ (1 / 2) * Real.log (1 + ν i * Q i / (N₀ / 2)) := by
    intro i
    have hdiv : P' i / (N₀ / 2) ≤ ν i * Q i / (N₀ / 2) :=
      (div_le_div_iff_of_pos_right hNpos).mpr (hP'le i)
    have harg : 1 + P' i / (N₀ / 2) ≤ 1 + ν i * Q i / (N₀ / 2) := by linarith
    have hposarg : (0 : ℝ) < 1 + P' i / (N₀ / 2) := by
      have : 0 ≤ P' i / (N₀ / 2) := div_nonneg (hP'nn i) hNpos.le
      linarith
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hposarg harg) (by norm_num)
  -- Restate the rotated-code log bound over `Fin c.k` (defeq to `Fin c'.k`) and chain.
  have hP'log' : Real.log M ≤ (∑ i : Fin c.k, (1 / 2) * Real.log (1 + P' i / (N₀ / 2)))
      + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := hP'log
  have hsum : (∑ i : Fin c.k, (1 / 2) * Real.log (1 + P' i / (N₀ / 2)))
      ≤ ∑ i : Fin c.k, (1 / 2) * Real.log (1 + ν i * Q i / (N₀ / 2)) :=
    Finset.sum_le_sum (fun i _ => hlog_le i)
  linarith

end InformationTheory.Shannon.ShannonHartley
