import InformationTheory.Shannon.TimeBandLimiting
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Count domination for the Shannon–Hartley converse (C2 core)

For an arbitrary code's orthonormal, time-limited test family `φ : Fin k → E` (with `E =
L²(ℝ;ℂ)`), the number of *band-limited Gram* eigenvalues exceeding `c` is at most
`prolateCount T W c`. This is the bridge that dominates an arbitrary code's Gram spectrum by the
operator spectrum of `A = timeBandLimitingOp T W`; it feeds the C4 head-count.

The band-limited Gram matrix is `Gᵢⱼ = ⟪P_W φᵢ, P_W φⱼ⟫`, whose eigenvalues are counted by
`bandGramEigenvalues`. The proof realizes the high-eigenvalue eigenspace inside `E` (via the
eigenvector images `gramEig`), where the operator-side Bessel domination
`frame_form_le_op_form` supplies the Rayleigh bound feeding
`finrank_le_prolateCount_of_form_gt` (the abstract min-max half of Cauchy interlacing).

It is genuinely non-circular: it does not assume codewords = prolate basis.
-/

namespace InformationTheory.Shannon

open scoped ComplexConjugate
open TimeBandLimiting Matrix

/-- The eigenvalues of the band-limited Gram matrix `Gᵢⱼ = ⟪P_W φᵢ, P_W φⱼ⟫` of a test family
`φ : Fin k → E`. These are the per-coordinate channel gains consumed by the water-filling converse. -/
noncomputable def bandGramEigenvalues (W : ℝ) {k : ℕ} (φ : Fin k → E) : Fin k → ℝ :=
  (Matrix.isHermitian_gram ℂ fun i => (bandLimitSubspace W).starProjection (φ i)).eigenvalues

/-- The image in `E` of the `i`-th eigenvector of the Gram matrix of `v`, i.e. the vector
`eᵢ = ∑ₗ (wᵢ)ₗ • vₗ` where `wᵢ` is the `i`-th orthonormal eigenvector of `gram ℂ v`. These vectors
are pairwise `E`-orthogonal with `‖eᵢ‖² = νᵢ`, realizing the Gram eigenspaces inside `E`. -/
private noncomputable def gramEig {k : ℕ} (v : Fin k → E) (i : Fin k) : E :=
  ∑ l, (⇑((Matrix.isHermitian_gram ℂ v).eigenvectorBasis i)) l • v l

/-- `⟪eᵢ, eᵢ'⟫ = δᵢᵢ' · νᵢ`: the eigenvector images are `E`-orthogonal with squared norm the
eigenvalue. -/
private lemma inner_gramEig_gramEig {k : ℕ} (v : Fin k → E) (i i' : Fin k) :
    inner ℂ (gramEig v i) (gramEig v i')
      = if i = i' then ((Matrix.isHermitian_gram ℂ v).eigenvalues i : ℂ) else 0 := by
  classical
  set hG := Matrix.isHermitian_gram ℂ v with hGdef
  have hstar : star (⇑(hG.eigenvectorBasis i)) ⬝ᵥ ⇑(hG.eigenvectorBasis i')
      = inner ℂ (hG.eigenvectorBasis i) (hG.eigenvectorBasis i') := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  rw [gramEig, gramEig, ← Matrix.star_dotProduct_gram_mulVec v,
    hG.mulVec_eigenvectorBasis i', dotProduct_smul, hstar,
    orthonormal_iff_ite.mp hG.eigenvectorBasis.orthonormal i i']
  split_ifs with h
  · subst h; simp
  · simp

/-- `⟪eᵢ, vₗ⟫ = νᵢ · conj (wᵢ)ₗ`: the frame coefficient of an eigenvector image against a raw
Gram-frame vector. -/
private lemma inner_gramEig_v {k : ℕ} (v : Fin k → E) (i l : Fin k) :
    inner ℂ (gramEig v i) (v l)
      = ((Matrix.isHermitian_gram ℂ v).eigenvalues i : ℂ)
          * conj ((⇑((Matrix.isHermitian_gram ℂ v).eigenvectorBasis i)) l) := by
  classical
  set hG := Matrix.isHermitian_gram ℂ v with hGdef
  have hmv := congrFun (hG.mulVec_eigenvectorBasis i) l
  have key : inner ℂ (v l) (gramEig v i)
      = (hG.eigenvalues i : ℂ) * (⇑(hG.eigenvectorBasis i)) l := by
    rw [gramEig, inner_sum]
    have hsum : (∑ m, inner ℂ (v l) ((⇑(hG.eigenvectorBasis i)) m • v m))
        = ((Matrix.gram ℂ v) *ᵥ ⇑(hG.eigenvectorBasis i)) l := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [inner_smul_right, Matrix.gram_apply, mul_comm]
    rw [hsum, hmv, Pi.smul_apply]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [← inner_conj_symm (gramEig v i) (v l), key, map_mul, Complex.conj_ofReal]

/-- Each eigenvector image lies in any submodule containing the raw frame `v`. -/
private lemma gramEig_mem {k : ℕ} (v : Fin k → E) (S : Submodule ℂ E) (hv : ∀ l, v l ∈ S)
    (i : Fin k) : gramEig v i ∈ S :=
  Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hv l)

/-- **Count domination (converse min-max).** The number of band-limited Gram eigenvalues of an
orthonormal, time-limited test family `φ` that exceed `c` is at most `prolateCount T W c`. Dominates
the arbitrary code's Gram spectrum by the operator spectrum of `A = timeBandLimitingOp T W`. -/
theorem gram_high_eigen_finrank_le_prolateCount (T W : ℝ) {c : ℝ} (hc : 0 < c)
    {k : ℕ} (φ : Fin k → E) (h_on : Orthonormal ℂ φ)
    (h_tl : ∀ i, φ i ∈ timeLimitSubspace T) :
    (Finset.univ.filter (fun j => c < bandGramEigenvalues W φ j)).card ≤ prolateCount T W c := by
  classical
  set v : Fin k → E := fun i => (bandLimitSubspace W).starProjection (φ i) with hvdef
  set hG := Matrix.isHermitian_gram ℂ v with hGdef
  rw [show bandGramEigenvalues W φ = hG.eigenvalues from rfl]
  set ν := hG.eigenvalues with hνdef
  -- The band-limited frame lies in `bandLimitSubspace W`, and so do the eigenvector images.
  have hv_band : ∀ l, v l ∈ bandLimitSubspace W := fun l => Submodule.starProjection_apply_mem _ _
  have he_band : ∀ i, gramEig v i ∈ bandLimitSubspace W := fun i =>
    gramEig_mem v (bandLimitSubspace W) hv_band i
  -- Subtype-level orthogonality of the eigenvector images.
  have he'_inner : ∀ j j' : {j : Fin k // c < ν j},
      inner ℂ (gramEig v j.1) (gramEig v j'.1) = if j = j' then (ν j.1 : ℂ) else 0 := by
    intro j j'
    rw [inner_gramEig_gramEig v j.1 j'.1]
    by_cases h : j = j'
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]
  -- The realized high-eigenvalue subspace `S ⊆ E`.
  set e' : {j : Fin k // c < ν j} → E := fun j => gramEig v j.1 with he'def
  set S := Submodule.span ℂ (Set.range e') with hSdef
  -- The eigenvector images over the high indices are orthogonal and nonzero, hence independent.
  have hlin : LinearIndependent ℂ e' := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun j hj0 => ?_) (fun j j' hjj' => ?_)
    · have h1 : inner ℂ (e' j) (e' j) = (ν j.1 : ℂ) := by
        rw [he'def, he'_inner j j, if_pos rfl]
      rw [hj0, inner_zero_left] at h1
      have hν0 : ν j.1 = 0 := by exact_mod_cast h1.symm
      exact absurd (hν0 ▸ j.2) (not_lt.mpr hc.le)
    · rw [he'def]; exact he'_inner j j' |>.trans (if_neg hjj')
  have hcard : Module.finrank ℂ S = Fintype.card {j : Fin k // c < ν j} :=
    finrank_span_eq_card hlin
  -- The A-Rayleigh quotient exceeds `c` on `S`; feeds the abstract count bound C1.
  have hS : ∀ g ∈ S, g ≠ 0 → c * ‖g‖ ^ 2 < (inner ℂ (timeBandLimitingOp T W g) g).re := by
    intro g hg hg_ne
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
    -- `g` is band-limited (a combination of band-limited eigenvector images).
    have hg_band : g ∈ bandLimitSubspace W := by
      rw [← ha]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (he_band j.1)
    -- Frame coefficients against `φ` and against the projected frame `v` agree on band-limited `g`.
    have hPg : (bandLimitSubspace W).starProjection g = g :=
      Submodule.starProjection_eq_self_iff.mpr hg_band
    have hgv : ∀ i, inner ℂ g (φ i) = inner ℂ g (v i) := by
      intro i
      change inner ℂ g (φ i) = inner ℂ g ((bandLimitSubspace W).starProjection (φ i))
      conv_lhs => rw [← hPg]
      exact Submodule.inner_starProjection_left_eq_right _ _ _
    -- Bilinear form of `A`'s frame on the orthogonal eigenimages.
    have hbil : ∀ b : {j : Fin k // c < ν j} → ℂ, inner ℂ (∑ j, b j • e' j) g
        = ∑ j, (starRingEnd ℂ (b j)) * (a j * (ν j.1 : ℂ)) := by
      intro b
      rw [← ha, sum_inner]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [inner_smul_left, inner_sum]
      congr 1
      simp_rw [he'def, inner_smul_right, he'_inner j]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    -- `‖g‖² = ∑ⱼ ‖aⱼ‖² νⱼ`.
    have hnorm : ‖g‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 * ν j.1 := by
      have hgg : inner ℂ g g = ((∑ j, ‖a j‖ ^ 2 * ν j.1 : ℝ) : ℂ) := by
        nth_rewrite 1 [← ha]
        rw [hbil a, Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hcj : (starRingEnd ℂ) (a j) * a j = ((‖a j‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.conj_mul]; norm_cast
        rw [show (starRingEnd ℂ) (a j) * (a j * (ν j.1 : ℂ))
            = ((starRingEnd ℂ) (a j) * a j) * (ν j.1 : ℂ) by ring, hcj, ← Complex.ofReal_mul]
      have hre := congrArg Complex.re hgg
      rw [Complex.ofReal_re] at hre
      rw [← hre]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) g).symm
    -- `∑ᵢ ‖⟪g,vᵢ⟫‖² = ∑ⱼ ‖aⱼ‖² νⱼ²`.
    have hframe : ∑ i, ‖inner ℂ g (v i)‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 * (ν j.1) ^ 2 := by
      -- Frame coefficient of `g` against `vᵢ`, expanded along the eigenimages.
      have hgvi : ∀ i, inner ℂ g (v i)
          = ∑ j, (starRingEnd ℂ (a j))
              * ((ν j.1 : ℂ) * (starRingEnd ℂ) ((⇑(hG.eigenvectorBasis j.1)) i)) := by
        intro i
        rw [← ha, sum_inner]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [inner_smul_left]
        congr 1
        exact inner_gramEig_v v j.1 i
      -- Orthonormality of the eigenvectors, in dotProduct form.
      have hw_orth : ∀ j j' : {j : Fin k // c < ν j},
          (∑ i, (starRingEnd ℂ) ((⇑(hG.eigenvectorBasis j.1)) i) * (⇑(hG.eigenvectorBasis j'.1)) i)
            = if j.1 = j'.1 then (1 : ℂ) else 0 := by
        intro j j'
        have hconv : (∑ i, (starRingEnd ℂ) ((⇑(hG.eigenvectorBasis j.1)) i)
              * (⇑(hG.eigenvectorBasis j'.1)) i)
            = inner ℂ (hG.eigenvectorBasis j.1) (hG.eigenvectorBasis j'.1) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct]
          simp only [dotProduct, Pi.star_apply, RCLike.star_def]
          exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        rw [hconv]
        exact orthonormal_iff_ite.mp hG.eigenvectorBasis.orthonormal j.1 j'.1
      -- The complex bilinear identity `∑ᵢ ⟪g,vᵢ⟫ · conj⟪g,vᵢ⟫ = ↑(∑ⱼ ‖aⱼ‖² νⱼ²)`.
      have hcomplex : (∑ i, inner ℂ g (v i) * (starRingEnd ℂ) (inner ℂ g (v i)))
          = ((∑ j, ‖a j‖ ^ 2 * (ν j.1) ^ 2 : ℝ) : ℂ) := by
        have hexpand : ∀ i, inner ℂ g (v i) * (starRingEnd ℂ) (inner ℂ g (v i))
            = ∑ j, ∑ j', (starRingEnd ℂ (a j) * a j' * (ν j.1 : ℂ) * (ν j'.1 : ℂ))
                * ((starRingEnd ℂ) ((⇑(hG.eigenvectorBasis j.1)) i)
                    * (⇑(hG.eigenvectorBasis j'.1)) i) := by
          intro i
          rw [hgvi i, map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
          rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_conj]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hexpand i), Finset.sum_comm]
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        -- inner sum over `i` collapses via `hw_orth`, then over `j'` via the Kronecker delta.
        simp_rw [← Finset.mul_sum, hw_orth, Subtype.coe_inj, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ j
          (fun j' => starRingEnd ℂ (a j) * a j' * (ν j.1 : ℂ) * (ν j'.1 : ℂ))]
        rw [if_pos (Finset.mem_univ _)]
        have hcj : (starRingEnd ℂ) (a j) * a j = ((‖a j‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.conj_mul]; norm_cast
        rw [show starRingEnd ℂ (a j) * a j * (ν j.1 : ℂ) * (ν j.1 : ℂ)
            = ((starRingEnd ℂ) (a j) * a j) * ((ν j.1 : ℂ) * (ν j.1 : ℂ)) by ring, hcj]
        push_cast
        ring
      -- Each squared norm is a `z · conj z`, so the real frame sum casts to the complex one.
      have hsum_eq : ((∑ i, ‖inner ℂ g (v i)‖ ^ 2 : ℝ) : ℂ)
          = ∑ i, inner ℂ g (v i) * (starRingEnd ℂ) (inner ℂ g (v i)) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [RCLike.mul_conj]
        norm_cast
      exact_mod_cast hsum_eq.trans hcomplex
    -- `∃ j, aⱼ ≠ 0` (else `g = 0`).
    have hexists : ∃ j : {j : Fin k // c < ν j}, a j ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_ne_iff] at hall
      exact hg_ne (by rw [← ha]; simp [hall])
    -- Strict comparison `c ∑ⱼ‖aⱼ‖²νⱼ < ∑ⱼ‖aⱼ‖²νⱼ²`.
    have hlt : c * (∑ j, ‖a j‖ ^ 2 * ν j.1) < ∑ j, ‖a j‖ ^ 2 * (ν j.1) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_lt_sum (fun j _ => ?_) ?_
      · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖a j‖) (hc.trans j.2).le)
          (sub_nonneg.mpr j.2.le)]
      · obtain ⟨j0, hj0⟩ := hexists
        refine ⟨j0, Finset.mem_univ _, ?_⟩
        have hpos : (0 : ℝ) < ‖a j0‖ ^ 2 := by positivity
        nlinarith [mul_pos (mul_pos hpos (hc.trans j0.2)) (sub_pos.mpr j0.2)]
    -- Assemble: `c‖g‖² < ∑ⱼ‖aⱼ‖²νⱼ² = ∑ᵢ‖⟪g,vᵢ⟫‖² = ∑ᵢ‖⟪g,φᵢ⟫‖² ≤ Re⟪Ag,g⟫`.
    calc c * ‖g‖ ^ 2 = c * (∑ j, ‖a j‖ ^ 2 * ν j.1) := by rw [hnorm]
      _ < ∑ j, ‖a j‖ ^ 2 * (ν j.1) ^ 2 := hlt
      _ = ∑ i, ‖inner ℂ g (v i)‖ ^ 2 := hframe.symm
      _ = ∑ i, ‖inner ℂ g (φ i)‖ ^ 2 := Finset.sum_congr rfl (fun i _ => by rw [hgv i])
      _ ≤ (inner ℂ (timeBandLimitingOp T W g) g).re :=
          frame_form_le_op_form T W φ h_on h_tl g hg_band
  -- The count is `finrank S`, bounded by C1.
  calc (Finset.univ.filter (fun j => c < ν j)).card
      = Fintype.card {j : Fin k // c < ν j} := (Fintype.card_subtype _).symm
    _ = Module.finrank ℂ S := hcard.symm
    _ ≤ prolateCount T W c := finrank_le_prolateCount_of_form_gt T W hc S hS

end InformationTheory.Shannon
