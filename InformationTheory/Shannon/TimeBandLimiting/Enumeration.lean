import InformationTheory.Shannon.TimeBandLimiting.Operator

/-!
# Time-and-band-limiting operator — the decreasing eigenvalue enumeration

Leg C / C'. The eigenvalues of `A` in decreasing order (`prolateEigenvalues`), rebuilt from the
structural compact self-adjoint spectral theorem since Mathlib's ordered sequence is
`FiniteDimensional`-gated; its antitonicity, `[0,1]` range, and decay to `0`; the non-vacuity
witness `timeBandLimitingOp_ne_zero` making the leading eigenvalue strictly positive; and the
matching parameter-boundary degeneracy of the enumeration.
-/

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory
open scoped ENNReal symmDiff FourierTransform

/-! ### Leg C — the decreasing prolate eigenvalue enumeration -/

section Enumeration

/-- `A = timeBandLimitingOp T W` as a bare `Module.End`, the shape Mathlib's eigenvalue API uses. -/
noncomputable abbrev prolateEnd (T W : ℝ) : Module.End ℂ E := timeBandLimitingOp T W

theorem timeBandLimitingOp_isSymmetric (T W : ℝ) : (prolateEnd T W).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (timeBandLimitingOp_isSelfAdjoint T W)

theorem exists_unit_eigenvector {T W μ : ℝ} (hμ : (prolateEnd T W).HasEigenvalue (μ : ℂ)) :
    ∃ v : E, ‖v‖ = 1 ∧ timeBandLimitingOp T W v = (μ : ℂ) • v := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv_mem
  have hv' : timeBandLimitingOp T W v = (μ : ℂ) • v := hv_mem
  refine ⟨(‖v‖ : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv_ne)
  · rw [map_smul, hv', smul_comm]

theorem inner_eq_zero_of_eigenvalue_ne {T W : ℝ} {μ ν : ℝ} (hμν : μ ≠ ν) {v w : E}
    (hv : timeBandLimitingOp T W v = (μ : ℂ) • v)
    (hw : timeBandLimitingOp T W w = (ν : ℂ) • w) :
    inner ℂ v w = (0 : ℂ) := by
  have hsym := timeBandLimitingOp_isSymmetric T W v w
  have hL : inner ℂ (timeBandLimitingOp T W v) w = (μ : ℂ) * inner ℂ v w := by
    rw [hv, inner_smul_left, Complex.conj_ofReal]
  have hR : inner ℂ v (timeBandLimitingOp T W w) = (ν : ℂ) * inner ℂ v w := by
    rw [hw, inner_smul_right]
  have key : ((μ : ℂ) - (ν : ℂ)) * inner ℂ v w = 0 := by
    have : (μ : ℂ) * inner ℂ v w = (ν : ℂ) * inner ℂ v w := by
      rw [← hL, ← hR]; exact hsym
    linear_combination this
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h) hμν
  · exact h

theorem eigenvalue_le_one {T W μ : ℝ} (hμ : (prolateEnd T W).HasEigenvalue (μ : ℂ)) : μ ≤ 1 := by
  obtain ⟨v, hv_norm, hv⟩ := exists_unit_eigenvector hμ
  have h1 : ‖timeBandLimitingOp T W v‖ ≤ 1 := by
    calc ‖timeBandLimitingOp T W v‖ ≤ ‖timeBandLimitingOp T W‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 :=
          mul_le_mul (timeBandLimitingOp_norm_le_one T W) hv_norm.le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [hv, norm_smul, hv_norm, mul_one, Complex.norm_real] at h1
  exact (abs_le.mp h1).2

/-- The set of eigenvalues of `A = timeBandLimitingOp T W` lying strictly above `c`.
@audit:ok -/
def prolateEigenvalueSet (T W c : ℝ) : Set ℝ :=
  {μ : ℝ | c < μ ∧ (prolateEnd T W).HasEigenvalue (μ : ℂ)}

/-- **Atom 1.** For a positive threshold `c`, the compact operator `A` has only finitely many
eigenvalues above `c`: an infinite family would give an orthonormal sequence of eigenvectors whose
images stay `c`-separated, contradicting compactness.
@audit:ok -/
theorem prolateEigenvalueSet_finite (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    (prolateEigenvalueSet T W c).Finite := by
  by_contra hfin
  have hinf : (prolateEigenvalueSet T W c).Infinite := hfin
  -- An injective stream of distinct eigenvalues above `c`.
  let f := hinf.natEmbedding
  set μ : ℕ → ℝ := fun n => ((f n : ℝ)) with hμdef
  have hμ_inj : Function.Injective μ := Subtype.val_injective.comp f.injective
  have hμ_gt : ∀ n, c < μ n := fun n => (f n).2.1
  have hμ_eig : ∀ n, (prolateEnd T W).HasEigenvalue ((μ n : ℝ) : ℂ) := fun n => (f n).2.2
  -- Unit eigenvectors for each of them.
  choose e he_norm he_eig using fun n => exists_unit_eigenvector (hμ_eig n)
  -- Their images are pairwise `c`-separated.
  have hsep : ∀ i j : ℕ, i ≠ j →
      c < ‖timeBandLimitingOp T W (e i) - timeBandLimitingOp T W (e j)‖ := by
    intro i j hij
    have horth : inner ℂ (e i) (e j) = (0 : ℂ) :=
      inner_eq_zero_of_eigenvalue_ne (hμ_inj.ne hij) (he_eig i) (he_eig j)
    have hinner : inner ℂ (e i) (timeBandLimitingOp T W (e i) - timeBandLimitingOp T W (e j))
        = ((μ i : ℝ) : ℂ) := by
      rw [inner_sub_right, he_eig i, he_eig j, inner_smul_right, inner_smul_right, horth,
        inner_self_eq_norm_sq_to_K, he_norm i]
      push_cast
      ring
    have hCS := norm_inner_le_norm (𝕜 := ℂ) (e i)
      (timeBandLimitingOp T W (e i) - timeBandLimitingOp T W (e j))
    rw [hinner, he_norm i, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hc.trans (hμ_gt i))] at hCS
    exact lt_of_lt_of_le (hμ_gt i) hCS
  -- But `A` maps the unit ball into a compact set, forcing a convergent (hence Cauchy) subsequence.
  have hK : IsCompact (closure ((timeBandLimitingOp T W : E →ₗ[ℂ] E) '' Metric.closedBall 0 1)) :=
    (timeBandLimitingOp_isCompact T W).isCompact_closure_image_closedBall 1
  have hmem : ∀ n, timeBandLimitingOp T W (e n) ∈
      closure ((timeBandLimitingOp T W : E →ₗ[ℂ] E) '' Metric.closedBall 0 1) := by
    intro n
    refine subset_closure ⟨e n, ?_, rfl⟩
    simp [Metric.mem_closedBall, dist_zero_right, he_norm n]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq c hc
  have hne : φ N ≠ φ (N + 1) := (hφ (Nat.lt_succ_self N)).ne
  have := hN N le_rfl (N + 1) (Nat.le_succ N)
  rw [Function.comp_apply, Function.comp_apply, dist_eq_norm] at this
  exact absurd this (not_lt.mpr (hsep _ _ hne).le)

/-- The span of all eigenspaces of `A` whose eigenvalue exceeds `c`.
@audit:ok -/
noncomputable def prolateEigenspaceSup (T W c : ℝ) : Submodule ℂ E :=
  ⨆ μ ∈ prolateEigenvalueSet T W c, Module.End.eigenspace (prolateEnd T W) (μ : ℂ)

theorem prolateEigenspaceSup_finiteDimensional (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    FiniteDimensional ℂ (prolateEigenspaceSup T W c) := by
  haveI : Finite ↥(prolateEigenvalueSet T W c) := (prolateEigenvalueSet_finite T W hc).to_subtype
  haveI : ∀ μ : ↥(prolateEigenvalueSet T W c),
      FiniteDimensional ℂ (Module.End.eigenspace (prolateEnd T W) (((μ : ℝ)) : ℂ)) := by
    intro μ
    exact ContinuousLinearMap.finite_dimensional_eigenspace (timeBandLimitingOp_isCompact T W) _
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (hc.trans μ.2.1)))
  rw [prolateEigenspaceSup, iSup_subtype']
  infer_instance

/-- The eigenvalue counting function of `A`: the number of eigenvalues exceeding `c`, counted with
multiplicity.

Only meaningful for `0 < c`, where `prolateEigenspaceSup_finiteDimensional` makes the `finrank` a
genuine dimension. For `c ≤ 0` it is a junk value: `prolateEigenspaceSup_finiteDimensional` no
longer applies, and on an infinite-dimensional span `finrank` reports `0`. This is why
`prolateEigenvalues` below takes the infimum over `0 < c` rather than `0 ≤ c` — the latter would
risk letting a junk `0` into the constraint set and collapsing the whole enumeration to `≡ 0`.
The span's infinite-dimensionality at `c ≤ 0` is expected but *not* established in-tree (at `c = 0`
it is exactly the open infinite-rank obligation noted on `prolateEigenvalues`); nothing depends on
it, since every use site below is guarded by `0 < c` — audited site-by-site, no proof consumes the
junk value.
@audit:ok -/
noncomputable def prolateCount (T W c : ℝ) : ℕ := Module.finrank ℂ (prolateEigenspaceSup T W c)

theorem prolateEigenvalueSet_subset (T W : ℝ) {c c' : ℝ} (h : c ≤ c') :
    prolateEigenvalueSet T W c' ⊆ prolateEigenvalueSet T W c :=
  fun _ hμ => ⟨lt_of_le_of_lt h hμ.1, hμ.2⟩

theorem prolateEigenspaceSup_mono (T W : ℝ) {c c' : ℝ} (h : c ≤ c') :
    prolateEigenspaceSup T W c' ≤ prolateEigenspaceSup T W c :=
  biSup_mono (prolateEigenvalueSet_subset T W h)

theorem prolateCount_antitone (T W : ℝ) {c c' : ℝ} (hc : 0 < c) (h : c ≤ c') :
    prolateCount T W c' ≤ prolateCount T W c := by
  haveI := prolateEigenspaceSup_finiteDimensional T W hc
  exact Submodule.finrank_mono (prolateEigenspaceSup_mono T W h)

theorem prolateEigenvalueSet_one_eq_empty (T W : ℝ) : prolateEigenvalueSet T W 1 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun μ hμ => ?_
  exact absurd (eigenvalue_le_one hμ.2) (not_le.mpr hμ.1)

theorem prolateCount_one_eq_zero (T W : ℝ) : prolateCount T W 1 = 0 := by
  have : prolateEigenspaceSup T W 1 = ⊥ := by
    rw [prolateEigenspaceSup, prolateEigenvalueSet_one_eq_empty]
    simp
  rw [prolateCount, this]
  simp

/-- The decreasing enumeration of the eigenvalues of the time-and-band limiting operator
`A = P_W ∘ Q_T ∘ P_W`, listed with multiplicity and padded with `0`.

Defined as the generalized inverse of the counting function `prolateCount`: `λ n` is the least
threshold `c > 0` above which `A` has at most `n` eigenvalues.

Scope: the unconditional headlines below (`_nonneg`, `_le_one`, `_antitone`, `_tendsto_zero`) are
shape statements — each is satisfied by the constant-zero sequence, so none of them carries spectral
content on its own. That is not a defect of the definition: for `W ≤ 0` and for `T ≤ 0` the operator
genuinely collapses and the enumeration really is `≡ 0` (`prolateEigenvalues_eq_zero_of_band_nonpos`
/ `prolateEigenvalues_eq_zero_of_time_nonpos`), so a nondegeneracy input is needed to say more.
`prolateEigenvalues_zero_pos` supplies it, ruling out the zero sequence for `0 < T`, `0 < W`; those
two collapse lemmas are exactly what make its hypotheses tight.

Still open (a strictly larger obligation, not attempted here): `λ n ≠ 0` for *all* `n`, which needs
`A` to have infinite rank. Neither that nor the above is the `wall:nyquist-2w-dof` eigenvalue-
concentration wall.
@audit:ok -/
noncomputable def prolateEigenvalues (T W : ℝ) (n : ℕ) : ℝ :=
  sInf {c : ℝ | 0 < c ∧ prolateCount T W c ≤ n}

theorem prolateEigenvalues_setOf_nonempty (T W : ℝ) (n : ℕ) :
    {c : ℝ | 0 < c ∧ prolateCount T W c ≤ n}.Nonempty :=
  ⟨1, one_pos, (prolateCount_one_eq_zero T W).le.trans (Nat.zero_le n)⟩

theorem prolateEigenvalues_setOf_bddBelow (T W : ℝ) (n : ℕ) :
    BddBelow {c : ℝ | 0 < c ∧ prolateCount T W c ≤ n} :=
  ⟨0, fun _ hc => hc.1.le⟩

theorem prolateEigenvalues_nonneg (T W : ℝ) (n : ℕ) : 0 ≤ prolateEigenvalues T W n :=
  le_csInf (prolateEigenvalues_setOf_nonempty T W n) fun _ hc => hc.1.le

theorem prolateEigenvalues_le_of_count_le (T W : ℝ) {c : ℝ} (hc : 0 < c) {n : ℕ}
    (h : prolateCount T W c ≤ n) : prolateEigenvalues T W n ≤ c :=
  csInf_le (prolateEigenvalues_setOf_bddBelow T W n) ⟨hc, h⟩

theorem prolateEigenvalues_le_one (T W : ℝ) (n : ℕ) : prolateEigenvalues T W n ≤ 1 :=
  prolateEigenvalues_le_of_count_le T W one_pos
    ((prolateCount_one_eq_zero T W).le.trans (Nat.zero_le n))

theorem prolateEigenvalues_antitone (T W : ℝ) : Antitone (prolateEigenvalues T W) := by
  intro m n hmn
  refine csInf_le_csInf (prolateEigenvalues_setOf_bddBelow T W n)
    (prolateEigenvalues_setOf_nonempty T W m) ?_
  exact fun c hc => ⟨hc.1, hc.2.trans hmn⟩

theorem prolateEigenvalues_tendsto_zero (T W : ℝ) :
    Filter.Tendsto (prolateEigenvalues T W) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨prolateCount T W (ε / 2), fun n hn => ?_⟩
  have h1 : prolateEigenvalues T W n ≤ ε / 2 :=
    prolateEigenvalues_le_of_count_le T W (by linarith) hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (prolateEigenvalues_nonneg T W n)]
  linarith

/-- Every nonzero entry of the enumeration really is an eigenvalue of `A`. If it were not, the
finitely many eigenvalues above `c/2` would leave a gap around it, making the counting function
constant across `c` — contradicting that the count jumps there by definition of the infimum.

The hypothesis is a non-degeneracy precondition, not the proof's core (granting it hands you
nothing about eigenvalues; the gap argument below does the work). It is retained for content rather
than necessity: at an entry with `λ n = 0` the conclusion would assert only that `0` is an
eigenvalue of `A`, which is no spectral information, so the hypothesis-free form would pin strictly
less. At `n = 0` it is discharged in-tree by `prolateEigenvalues_zero_hasEigenvalue` for `0 < T`,
`0 < W`.
@audit:ok -/
theorem prolateEigenvalues_hasEigenvalue (T W : ℝ) (n : ℕ) (h : prolateEigenvalues T W n ≠ 0) :
    (prolateEnd T W).HasEigenvalue ((prolateEigenvalues T W n : ℝ) : ℂ) := by
  set c := prolateEigenvalues T W n with hc_def
  have hc_eq : c = sInf {x : ℝ | 0 < x ∧ prolateCount T W x ≤ n} := hc_def
  have hc : 0 < c := lt_of_le_of_ne (prolateEigenvalues_nonneg T W n) (Ne.symm h)
  by_contra hnot
  have hFfin := prolateEigenvalueSet_finite T W (half_pos hc)
  have hcF : c ∉ prolateEigenvalueSet T W (c / 2) := fun hmem => hnot hmem.2
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hFfin.isClosed.isOpen_compl c hcF
  have hδ : 0 < min ε₀ (c / 2) := lt_min hε₀ (half_pos hc)
  have hδ_le : min ε₀ (c / 2) ≤ c / 2 := min_le_right _ _
  set ε := min ε₀ (c / 2) / 2 with hε_def
  have hεpos : 0 < ε := half_pos hδ
  have hε_le : ε ≤ c / 4 := by rw [hε_def]; linarith
  -- No eigenvalue lies within `ε` of `c`, so the eigenvalue sets either side agree.
  have hgap : prolateEigenvalueSet T W (c - ε) = prolateEigenvalueSet T W (c + ε) := by
    refine Set.Subset.antisymm (fun μ hμ => ⟨?_, hμ.2⟩)
      (prolateEigenvalueSet_subset T W (by linarith))
    by_contra hle
    push Not at hle
    have hμ_gt : c - ε < μ := hμ.1
    have hmemF : μ ∈ prolateEigenvalueSet T W (c / 2) := ⟨by linarith, hμ.2⟩
    have hin : μ ∈ Metric.ball c ε₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have : min ε₀ (c / 2) ≤ ε₀ := min_le_left _ _
        rw [hε_def] at hμ_gt; linarith
      · have : min ε₀ (c / 2) ≤ ε₀ := min_le_left _ _
        rw [hε_def] at hle; linarith
    exact (hball hin) hmemF
  have hcount_eq : prolateCount T W (c - ε) = prolateCount T W (c + ε) := by
    rw [prolateCount, prolateCount, prolateEigenspaceSup, prolateEigenspaceSup, hgap]
  -- The count is `≤ n` just above `c` ...
  obtain ⟨u, hu_mem, hu_lt⟩ :=
    Real.lt_sInf_add_pos (prolateEigenvalues_setOf_nonempty T W n) hεpos
  rw [← hc_eq] at hu_lt
  have h1 : prolateCount T W (c + ε) ≤ n :=
    le_trans (prolateCount_antitone T W hu_mem.1 hu_lt.le) hu_mem.2
  -- ... but `> n` just below it, since `c` is the infimum.
  have h2 : ¬ prolateCount T W (c - ε) ≤ n := by
    intro hle
    have hle' : c ≤ c - ε :=
      hc_eq ▸ csInf_le (prolateEigenvalues_setOf_bddBelow T W n) ⟨by linarith, hle⟩
    linarith
  exact h2 (hcount_eq ▸ h1)

end Enumeration

section NonVacuity

/-- The indicator of the time window `[0,T]`, as an element of `L²(ℝ;ℂ)`. It is the witness that
makes the eigenvalue enumeration non-vacuous: it lies in the time-limited subspace, and its
spectrum is continuous with value `T` at the origin, hence survives the band cutoff.
@audit:ok -/
noncomputable def timeBox (T : ℝ) : E :=
  indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := T))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (1 : ℂ)

theorem timeBox_coeFn (T : ℝ) :
    (timeBox T : ℝ → ℂ) =ᵐ[volume] (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem timeBox_mem_timeLimitSubspace (T : ℝ) : timeBox T ∈ timeLimitSubspace T := by
  show (timeBox T : ℝ → ℂ) =ᵐ[volume.restrict {t : ℝ | t < 0 ∨ T < t}] 0
  filter_upwards [ae_restrict_of_ae (timeBox_coeFn T), self_mem_ae_restrict
    (measurableSet_lt measurable_id measurable_const |>.union
      (measurableSet_lt measurable_const measurable_id))] with t ht htS
  simp only [Pi.zero_apply]
  rw [ht, Set.indicator_of_notMem]
  rintro ⟨h0, hT⟩
  rcases htS with h | h
  · exact absurd h0 (not_le.mpr h)
  · exact absurd hT (not_le.mpr h)

theorem indicatorIcc_memLp_one (T : ℝ) :
    MemLp ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) 1 volume :=
  memLp_indicator_const 1 measurableSet_Icc (1 : ℂ)
    (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

theorem fourierIntegral_indicatorIcc_continuous (T : ℝ) :
    Continuous (𝓕 ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)))) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (memLp_one_iff_integrable.mp (indicatorIcc_memLp_one T))

theorem fourierIntegral_indicatorIcc_zero {T : ℝ} (hT : 0 < T) :
    𝓕 ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) 0 = (T : ℂ) := by
  rw [Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  simp [hT.le]

theorem fourier_timeBox_ae_eq (T : ℝ) :
    ((Lp.fourierTransformₗᵢ ℝ ℂ (timeBox T) : E) : ℝ → ℂ)
      =ᵐ[volume] 𝓕 ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) := by
  have hmem2 : MemLp ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 measurableSet_Icc (1 : ℂ)
      (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hbridge := ShannonHartley.l2Fourier_eq_fourierIntegral
    ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) (indicatorIcc_memLp_one T) hmem2
  have hLp : hmem2.toLp ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) = timeBox T := by
    rw [← Lp.toLp_coeFn (timeBox T) (Lp.memLp _)]
    exact (MemLp.toLp_eq_toLp_iff hmem2 (Lp.memLp _)).mpr (timeBox_coeFn T).symm
  rw [hLp] at hbridge
  exact hbridge

theorem bandLimitProj_timeBox_ne_zero {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    (bandLimitSubspace W).starProjection (timeBox T) ≠ 0 := by
  intro hzero
  set F := 𝓕 ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ))) with hF_def
  -- The band cutoff of the box spectrum vanishes a.e.
  have hae : ∀ᵐ ξ ∂(volume : Measure ℝ),
      (Set.Icc (-W) W).indicator (fun _ => (1 : ℂ)) ξ * F ξ = 0 := by
    have h1 := fourier_bandLimitProj_apply_ae W (timeBox T)
    rw [hzero] at h1
    have h0 : ((Lp.fourierTransformₗᵢ ℝ ℂ (0 : E) : E) : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [map_zero]; exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [h1, h0, fourier_timeBox_ae_eq T] with ξ h1ξ h0ξ hbξ
    have := h1ξ.symm.trans h0ξ
    simpa [Pi.mul_apply, hbξ] using this
  -- But the spectrum is continuous and nonzero at the origin, which sits inside the band.
  set U := (F ⁻¹' {0}ᶜ) ∩ Set.Ioo (-W) W with hU_def
  have hUopen : IsOpen U :=
    ((isOpen_compl_singleton).preimage (fourierIntegral_indicatorIcc_continuous T)).inter
      isOpen_Ioo
  have hUmem : (0 : ℝ) ∈ U := by
    refine ⟨?_, ⟨by linarith, hW⟩⟩
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [hF_def, fourierIntegral_indicatorIcc_zero hT]
    exact_mod_cast hT.ne'
  have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨0, hUmem⟩
  -- `U` lies in the null set where the cutoff spectrum is nonzero.
  have hUnull : volume U = 0 := by
    rw [MeasureTheory.ae_iff] at hae
    refine measure_mono_null (fun ξ hξ => ?_) hae
    have hband : ξ ∈ Set.Icc (-W) W := Set.Ioo_subset_Icc_self hξ.2
    simp only [Set.mem_setOf_eq, Set.indicator_of_mem hband, one_mul]
    exact hξ.1
  exact absurd hUnull hUpos.ne'

/-- The time-and-band limiting operator is nonzero whenever both the window and the band are
nondegenerate. This is the non-vacuity input for the eigenvalue enumeration.

Both hypotheses are tight, and on structurally distinct grounds: at `T = 0` the window collapses
(`timeLimitSubspace_eq_bot_of_nonpos`, so `Q = 0`) and at `W = 0` the band collapses
(`bandLimitSubspace_eq_bot_of_nonpos`, so `P = 0`); either forces `A = 0`
(`timeBandLimitingOp_eq_zero_of_time_nonpos` / `timeBandLimitingOp_eq_zero_of_band_nonpos`). So
neither can be relaxed to `≤`.
@audit:ok -/
theorem timeBandLimitingOp_ne_zero {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    timeBandLimitingOp T W ≠ 0 := by
  intro hA
  have hQg : (timeLimitSubspace T).starProjection (timeBox T) = timeBox T :=
    Submodule.starProjection_eq_self_iff.mpr (timeBox_mem_timeLimitSubspace T)
  have hApp : (bandLimitSubspace W).starProjection ((timeLimitSubspace T).starProjection
      ((bandLimitSubspace W).starProjection (timeBox T))) = 0 := by
    have h : timeBandLimitingOp T W (timeBox T) = 0 := by rw [hA]; simp
    exact h
  -- `⟪A g, g⟫ = ‖Q (P g)‖²`, so `A = 0` kills `Q (P g)`.
  have h3 : (timeLimitSubspace T).starProjection
      ((bandLimitSubspace W).starProjection (timeBox T)) = 0 := by
    refine inner_self_eq_zero (𝕜 := ℂ).mp ?_
    rw [Submodule.inner_starProjection_left_eq_right (timeLimitSubspace T),
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _),
      Submodule.inner_starProjection_left_eq_right (bandLimitSubspace W), hApp,
      inner_zero_right]
  -- `‖P g‖² = ⟪Q g, P g⟫ = ⟪g, Q (P g)⟫ = 0`, since `g` is already time-limited.
  have h4 : (bandLimitSubspace W).starProjection (timeBox T) = 0 := by
    have key : (inner ℂ (timeBox T)
        ((bandLimitSubspace W).starProjection (timeBox T)) : ℂ) = 0 := by
      have h := Submodule.inner_starProjection_left_eq_right (𝕜 := ℂ) (timeLimitSubspace T)
        (timeBox T) ((bandLimitSubspace W).starProjection (timeBox T))
      rw [hQg] at h
      rw [h, h3, inner_zero_right]
    refine inner_self_eq_zero (𝕜 := ℂ).mp ?_
    rw [Submodule.inner_starProjection_left_eq_right (bandLimitSubspace W),
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
    exact key
  exact bandLimitProj_timeBox_ne_zero hT hW h4

theorem exists_pos_hasEigenvalue {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    ∃ μ : ℝ, 0 < μ ∧ (prolateEnd T W).HasEigenvalue (μ : ℂ) := by
  have hA : timeBandLimitingOp T W ≠ 0 := timeBandLimitingOp_ne_zero hT hW
  have hiff := ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
    (timeBandLimitingOp_isCompact T W) (timeBandLimitingOp_isSymmetric T W)
  have hnot : ¬ (∀ μ : ℂ, Module.End.HasEigenvalue (prolateEnd T W) μ → μ = 0) :=
    fun h => hA (hiff.mp h)
  push Not at hnot
  obtain ⟨μ, hμ, hμ0⟩ := hnot
  have hconj := (timeBandLimitingOp_isSymmetric T W).conj_eigenvalue_eq_self hμ
  have him : μ.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by simp [him])
  have hμ' : (prolateEnd T W).HasEigenvalue ((μ.re : ℝ) : ℂ) := hre ▸ hμ
  refine ⟨μ.re, ?_, hμ'⟩
  have hnn : 0 ≤ μ.re := by
    apply eigenvalue_nonneg_of_nonneg (𝕜 := ℂ) (T := (prolateEnd T W)) hμ'
    intro x
    have h := (timeBandLimitingOp_isPositive T W).inner_nonneg_right x
    have := (Complex.le_def.mp h).1
    simpa using this
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exact absurd (by rw [← hre, ← h]; simp) hμ0

/-- The eigenvalue enumeration of the time-and-band limiting operator is non-vacuous: its leading
entry is strictly positive whenever the window and the band are nondegenerate. This is what rules
out the constant-zero sequence, which satisfies every shape headline on `prolateEigenvalues`.
It bounds only the *leading* entry; `λ n ≠ 0` for all `n` is a strictly larger, open obligation.
@audit:ok -/
theorem prolateEigenvalues_zero_pos {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    0 < prolateEigenvalues T W 0 := by
  obtain ⟨μ, hμpos, hμ⟩ := exists_pos_hasEigenvalue hT hW
  have hlb : ∀ c ∈ {c : ℝ | 0 < c ∧ prolateCount T W c ≤ 0}, μ ≤ c := by
    rintro c ⟨hc, hcount⟩
    by_contra hlt
    push Not at hlt
    haveI := prolateEigenspaceSup_finiteDimensional T W hc
    have hmem : μ ∈ prolateEigenvalueSet T W c := ⟨hlt, hμ⟩
    have hle : Module.End.eigenspace (prolateEnd T W) ((μ : ℝ) : ℂ)
        ≤ prolateEigenspaceSup T W c := by
      rw [prolateEigenspaceSup]
      exact le_biSup (fun μ : ℝ => Module.End.eigenspace (prolateEnd T W) ((μ : ℝ) : ℂ)) hmem
    have hbot : prolateEigenspaceSup T W c = ⊥ :=
      Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hcount)
    exact hμ (le_bot_iff.mp (hbot ▸ hle))
  exact lt_of_lt_of_le hμpos
    (le_csInf (prolateEigenvalues_setOf_nonempty T W 0) hlb)

/-- The leading entry of the enumeration is a genuine eigenvalue of `A`, discharging the
non-degeneracy hypothesis of `prolateEigenvalues_hasEigenvalue` at `n = 0`. The discharge is not
vacuous: the entry is strictly positive, so this exhibits a positive eigenvalue rather than the
uninformative `0`.
@audit:ok -/
theorem prolateEigenvalues_zero_hasEigenvalue {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    (prolateEnd T W).HasEigenvalue ((prolateEigenvalues T W 0 : ℝ) : ℂ) :=
  prolateEigenvalues_hasEigenvalue T W 0 (prolateEigenvalues_zero_pos hT hW).ne'

end NonVacuity

/-! ### Degeneracy — the tightness half of the non-vacuity hypotheses

The operator- and eigenvalue-level consequences of the subspace collapse established above (see the
narrative anchor at `zeroOnLp_eq_bot_of_ae_mem`). Killing either projection kills `A`, and an `A`
that is `0` has no positive eigenvalue, so the enumeration is identically `0`. Together with
`prolateEigenvalues_zero_pos` this pins both of its hypotheses as tight: the conclusion
`0 < prolateEigenvalues T W 0` genuinely fails at `T = 0` and at `W = 0`.
-/

section Degeneracy

theorem timeBandLimitingOp_eq_zero_of_band_nonpos (T : ℝ) {W : ℝ} (hW : W ≤ 0) :
    timeBandLimitingOp T W = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hzf : (bandLimitSubspace W).starProjection f = 0 :=
    (Submodule.eq_bot_iff _).mp (bandLimitSubspace_eq_bot_of_nonpos hW) _ (Submodule.coe_mem _)
  simp only [timeBandLimitingOp, ContinuousLinearMap.comp_apply, hzf, map_zero, zero_apply]

theorem timeBandLimitingOp_eq_zero_of_time_nonpos {T : ℝ} (hT : T ≤ 0) (W : ℝ) :
    timeBandLimitingOp T W = 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hzf : (timeLimitSubspace T).starProjection ((bandLimitSubspace W).starProjection f) = 0 :=
    (Submodule.eq_bot_iff _).mp (timeLimitSubspace_eq_bot_of_nonpos hT) _ (Submodule.coe_mem _)
  simp only [timeBandLimitingOp, ContinuousLinearMap.comp_apply, hzf, map_zero, zero_apply]

theorem prolateEigenvalues_eq_zero_of_op_eq_zero {T W : ℝ} (hA : timeBandLimitingOp T W = 0)
    (n : ℕ) : prolateEigenvalues T W n = 0 := by
  -- A zero operator has no eigenvalue above a positive threshold, so every count vanishes.
  have hset : ∀ c : ℝ, 0 < c → prolateEigenvalueSet T W c = ∅ := by
    intro c hc
    refine Set.eq_empty_iff_forall_notMem.mpr fun μ hμ => ?_
    obtain ⟨v, hv_mem, hv_ne⟩ := hμ.2.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hv_mem
    have hv0 : (μ : ℂ) • v = 0 := by
      rw [← hv_mem]
      simp [prolateEnd, hA]
    have : (μ : ℂ) = 0 := by
      rcases smul_eq_zero.mp hv0 with h | h
      · exact h
      · exact absurd h hv_ne
    have hμ0 : μ = 0 := by exact_mod_cast this
    exact absurd hμ.1 (by simp [hμ0, hc.le])
  have hcount : ∀ c : ℝ, 0 < c → prolateCount T W c = 0 := by
    intro c hc
    have hbot : prolateEigenspaceSup T W c = ⊥ := by
      rw [prolateEigenspaceSup, hset c hc]
      simp
    rw [prolateCount, hbot]
    simp
  refine le_antisymm ?_ (prolateEigenvalues_nonneg T W n)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := prolateEigenvalues_le_of_count_le T W hε ((hcount ε hε).le.trans (Nat.zero_le n))
  linarith

/-- At a degenerate band the eigenvalue enumeration collapses to `0`, so the `0 < W` hypothesis of
`prolateEigenvalues_zero_pos` cannot be relaxed to `0 ≤ W`.
@audit:ok -/
theorem prolateEigenvalues_eq_zero_of_band_nonpos (T : ℝ) {W : ℝ} (hW : W ≤ 0) (n : ℕ) :
    prolateEigenvalues T W n = 0 :=
  prolateEigenvalues_eq_zero_of_op_eq_zero (timeBandLimitingOp_eq_zero_of_band_nonpos T hW) n

/-- At a degenerate window the eigenvalue enumeration collapses to `0`, so the `0 < T` hypothesis of
`prolateEigenvalues_zero_pos` cannot be relaxed to `0 ≤ T`.
@audit:ok -/
theorem prolateEigenvalues_eq_zero_of_time_nonpos {T : ℝ} (hT : T ≤ 0) (W : ℝ) (n : ℕ) :
    prolateEigenvalues T W n = 0 :=
  prolateEigenvalues_eq_zero_of_op_eq_zero (timeBandLimitingOp_eq_zero_of_time_nonpos hT W) n

end Degeneracy

/-!
### The `2WT` trace bound (Leg E)

The crude `2WT` trace bound — the part of the degrees-of-freedom story that Bessel reaches on its
own. (The Landau–Pollak–Slepian *concentration* is a strictly stronger statement and is not proved
here; see `prolateCount_mul_le`.) The band-limiting projection
is an integral operator against the reproducing kernel `k_t = 2W sincN(2W(t − ·))`
(`bandLimitProj_apply_ae`), so `(P_W f)(t) = ⟪k_t, f⟫`. Two facts about that kernel drive everything
here: its `L²`-norm is the constant `‖k_t‖² = 2W` (Plancherel against the spectral boxcar, which is
already in-tree), and the quadratic form of `A` reads `⟪A f, f⟫ = ∫_[0,T] |⟪k_t, f⟫|² dt`.

Bessel's inequality applied pointwise in `t` then caps the trace of `A` along any finite orthonormal
family by `∫_[0,T] ‖k_t‖² dt = 2WT`, and Markov's inequality converts that into the eigenvalue
counting bound `c · #{λ > c} ≤ 2WT`.
-/

end InformationTheory.Shannon.TimeBandLimiting
