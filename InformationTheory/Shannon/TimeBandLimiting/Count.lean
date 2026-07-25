import InformationTheory.Shannon.TimeBandLimiting.SecondMoment

/-!
# Time-and-band-limiting operator — the two-sided eigenvalue count and achievability

The two-sided eigenvalue count concentration `#{λ > c} = 2WT ± D/·` with
`D = 2 + log(1 + 2WT)` and the threshold `c` free, assembled through a Hilbert basis adapted to
`E = V ⊕ Vᗮ`, and the Shannon–Hartley achievability consequence.
-/

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory
open scoped ENNReal symmDiff FourierTransform


section EigenvalueCount

/-- The polarized form behind `A = P_W Q_T P_W` being positive: `⟪A x, y⟫ = ⟪Q_T P_W x, Q_T P_W y⟫`.

`A = C* C` for `C = Q_T ∘ P_W`, so the sesquilinear form of `A` *is* the inner product pulled back
along `C`. This is the diagonal identity inside `norm_timeBandLimitingOp_sq_le_inner`, polarized;
it is what makes Cauchy-Schwarz available for the form of `A` without a positive square root.
@audit:ok -/
theorem inner_timeBandLimitingOp_eq_inner_timeLimit_bandLimit (T W : ℝ) (x y : E) :
    inner ℂ (timeBandLimitingOp T W x) y
      = inner ℂ ((timeLimitSubspace T).starProjection ((bandLimitSubspace W).starProjection x))
          ((timeLimitSubspace T).starProjection ((bandLimitSubspace W).starProjection y)) := by
  have hsymP : ((bandLimitSubspace W).starProjection : E →ₗ[ℂ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_starProjection (bandLimitSubspace W))
  have hsymQ : ((timeLimitSubspace T).starProjection : E →ₗ[ℂ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_starProjection (timeLimitSubspace T))
  set g : E := (bandLimitSubspace W).starProjection x with hg
  set u : E := (timeLimitSubspace T).starProjection g with hu
  have hidem : (timeLimitSubspace T).starProjection u = u := by
    rw [hu]
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have hA : timeBandLimitingOp T W x = (bandLimitSubspace W).starProjection u := by
    rw [hu, hg]
    simp only [timeBandLimitingOp, ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h1 := hsymP u y
  have h2 := hsymQ u ((bandLimitSubspace W).starProjection y)
  simp only [ContinuousLinearMap.coe_coe] at h1 h2
  rw [hidem] at h2
  rw [hA, h1, h2]

/-- Cauchy-Schwarz for the positive form of `A`: `|⟪A x, y⟫|² ≤ ⟪A x, x⟫ ⟪A y, y⟫`.

Mathlib has Cauchy-Schwarz for an inner product (`norm_inner_le_norm`) but not for the semi-inner
product of a general positive operator, which would need a positive square root. Here the square
root is unnecessary: `A` is *concretely* `C* C`, so its form is an honest inner product pulled back
along `C` and Mathlib's Cauchy-Schwarz applies verbatim.
@audit:ok -/
theorem norm_inner_timeBandLimitingOp_sq_le (T W : ℝ) (x y : E) :
    ‖inner ℂ (timeBandLimitingOp T W x) y‖ ^ 2
      ≤ (inner ℂ (timeBandLimitingOp T W x) x).re
          * (inner ℂ (timeBandLimitingOp T W y) y).re := by
  set cx : E := (timeLimitSubspace T).starProjection ((bandLimitSubspace W).starProjection x)
    with hcx
  set cy : E := (timeLimitSubspace T).starProjection ((bandLimitSubspace W).starProjection y)
    with hcy
  have hxy : inner ℂ (timeBandLimitingOp T W x) y = inner ℂ cx cy :=
    inner_timeBandLimitingOp_eq_inner_timeLimit_bandLimit T W x y
  have hself : ∀ z : E, (inner ℂ z z).re = ‖z‖ ^ 2 := by
    intro z
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hxx : (inner ℂ (timeBandLimitingOp T W x) x).re = ‖cx‖ ^ 2 := by
    rw [inner_timeBandLimitingOp_eq_inner_timeLimit_bandLimit T W x x, ← hcx, hself]
  have hyy : (inner ℂ (timeBandLimitingOp T W y) y).re = ‖cy‖ ^ 2 := by
    rw [inner_timeBandLimitingOp_eq_inner_timeLimit_bandLimit T W y y, ← hcy, hself]
  rw [hxy, hxx, hyy]
  have h := norm_inner_le_norm (𝕜 := ℂ) cx cy
  nlinarith [norm_nonneg (inner ℂ cx cy : ℂ), norm_nonneg cx, norm_nonneg cy,
    mul_nonneg (norm_nonneg cx) (norm_nonneg cy)]

/-- The operator inequality `A² ≤ c·A` on `Vᗮ`, in basis-free form: for `v` orthogonal to every
eigenspace above `c`, `‖A v‖² ≤ c ⟪A v, v⟫`.

This sharpens `norm_timeBandLimitingOp_sq_le_inner` (`A² ≤ A`, valid everywhere) by the spectral
gap, and it is what turns the second-moment deficit on `Vᗮ` into a bound on the `Vᗮ` trace in
`le_prolateCount`.

The proof needs no positive square root and no restricted operator. Cauchy-Schwarz for the form of
`A` (`norm_inner_timeBandLimitingOp_sq_le`), tested at `x = v` and `y = A v`, gives
`‖A v‖⁴ ≤ ⟪A v, v⟫ ⟪A(A v), A v⟫`; since `Vᗮ` is `A`-invariant, `A v` is again in `Vᗮ`, so the
spectral gap `inner_timeBandLimitingOp_le_of_mem_orthogonal` caps the second factor by `c ‖A v‖²`,
and dividing by `‖A v‖²` finishes.

Audited 2026-07-17 (independent). `hc : 0 < c` and `hv` are regularity/scoping, not load-bearing:
the operator inequality is *derived* from Cauchy-Schwarz + the gap lemma, not assumed. sorryAx-free.
@audit:ok -/
theorem norm_timeBandLimitingOp_sq_le_of_mem_orthogonal (T W c : ℝ) (hc : 0 < c)
    {v : E} (hv : v ∈ (prolateEigenspaceSup T W c)ᗮ) :
    ‖timeBandLimitingOp T W v‖ ^ 2 ≤ c * (inner ℂ (timeBandLimitingOp T W v) v).re := by
  set w : E := timeBandLimitingOp T W v with hw
  have hwv : w ∈ (prolateEigenspaceSup T W c)ᗮ :=
    prolateEigenspaceSup_orthogonal_invariant T W c v hv
  -- Cauchy-Schwarz for the positive form of `A`, tested against `w = A v`.
  have hCS := norm_inner_timeBandLimitingOp_sq_le T W v w
  have hself : ‖inner ℂ (timeBandLimitingOp T W v) w‖ = ‖w‖ ^ 2 := by
    rw [← hw, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  -- The spectral gap caps the `w`-Rayleigh quotient by `c`.
  have hgap : (inner ℂ (timeBandLimitingOp T W w) w).re ≤ c * ‖w‖ ^ 2 :=
    inner_timeBandLimitingOp_le_of_mem_orthogonal T W c hc hwv
  rw [hself] at hCS
  have hnn : 0 ≤ (inner ℂ (timeBandLimitingOp T W v) v).re :=
    (timeBandLimitingOp_isPositive T W).re_inner_nonneg_left v
  have hkey : ‖w‖ ^ 2 * ‖w‖ ^ 2
      ≤ (inner ℂ (timeBandLimitingOp T W v) v).re * (c * ‖w‖ ^ 2) := by
    calc ‖w‖ ^ 2 * ‖w‖ ^ 2 = (‖w‖ ^ 2) ^ 2 := by ring
      _ ≤ (inner ℂ (timeBandLimitingOp T W v) v).re
            * (inner ℂ (timeBandLimitingOp T W w) w).re := hCS
      _ ≤ (inner ℂ (timeBandLimitingOp T W v) v).re * (c * ‖w‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hgap hnn
  rcases eq_or_lt_of_le (sq_nonneg ‖w‖) with hzero | hpos
  · rw [← hzero]
    positivity
  · exact le_of_mul_le_mul_right (by linarith : ‖w‖ ^ 2 * ‖w‖ ^ 2
      ≤ (c * (inner ℂ (timeBandLimitingOp T W v) v).re) * ‖w‖ ^ 2) hpos

/-- An orthonormal eigenbasis of the finite-dimensional `V = prolateEigenspaceSup T W c`, indexed by
`Fin (prolateCount T W c)`, with every eigenvalue exceeding `c`, spanning `V` back in `E`.

This is the finite-dimensional spectral theorem applied to `A|_V`; it needs no complete eigenbasis
of `A` on `E`. Previously this construction was inlined in the body of `prolateCount_mul_le` and
exported nowhere, so it could not be reused; it is extracted here.

The index type is `Fin (prolateCount T W c)` *definitionally* (`prolateCount` is the `finrank` of
`V`), which is why no separate multiplicity bridge is needed to match the count.

Audited 2026-07-17 (independent). The definitional claim is machine-confirmed, not prose: the body's
`have hn : Module.finrank ℂ (prolateEigenspaceSup T W c) = d := rfl` type-checks, and
`prolateCount T W c := Module.finrank ℂ (prolateEigenspaceSup T W c)` verbatim. sorryAx-free.
@audit:ok -/
theorem exists_orthonormal_eigenbasis_prolateEigenspaceSup (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ (e : Fin (prolateCount T W c) → E) (ν : Fin (prolateCount T W c) → ℝ),
      Orthonormal ℂ e ∧
      (∀ i, timeBandLimitingOp T W (e i) = ((ν i : ℂ)) • e i) ∧
      (∀ i, c < ν i) ∧
      Submodule.span ℂ (Set.range e) = prolateEigenspaceSup T W c := by
  classical
  haveI := prolateEigenspaceSup_finiteDimensional T W hc
  have hinv := prolateEigenspaceSup_invariant T W c
  have hsymV : ((timeBandLimitingOp T W : E →ₗ[ℂ] E).restrict hinv).IsSymmetric :=
    (timeBandLimitingOp_isSymmetric T W).restrict_invariant hinv
  set d : ℕ := prolateCount T W c with hd
  have hn : Module.finrank ℂ (prolateEigenspaceSup T W c) = d := rfl
  set b := hsymV.eigenvectorBasis hn with hb
  set ν := hsymV.eigenvalues hn with hνdef
  set e : Fin d → E := fun i => ((b i : prolateEigenspaceSup T W c) : E) with he_def
  have he : Orthonormal ℂ e :=
    b.orthonormal.comp_linearIsometry (prolateEigenspaceSup T W c).subtypeₗᵢ
  have heig : ∀ i, timeBandLimitingOp T W (e i) = ((ν i : ℝ) : ℂ) • e i := by
    intro i
    have h := hsymV.apply_eigenvectorBasis hn i
    have h' := congrArg (Subtype.val (p := fun x : E => x ∈ prolateEigenspaceSup T W c)) h
    simp only [LinearMap.coe_restrict_apply, Submodule.coe_smul,
      ContinuousLinearMap.coe_coe] at h'
    exact h'
  have hνgt : ∀ i, c < ν i := by
    intro i
    by_contra hcon
    rw [not_lt] at hcon
    have hperp : prolateEigenspaceSup T W c ≤ (ℂ ∙ (e i))ᗮ := by
      conv_lhs => rw [prolateEigenspaceSup]
      refine iSup₂_le fun μ hμ => ?_
      intro w hw
      rw [Module.End.mem_eigenspace_iff] at hw
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ?_
      have hne : ν i ≠ μ := fun h => absurd hμ.1 (not_lt.mpr (h ▸ hcon))
      exact inner_eq_zero_of_eigenvalue_ne hne (heig i) hw
    have hzero : inner ℂ (e i) (e i) = (0 : ℂ) :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hperp (b i).2)
    have hz : e i = 0 := inner_self_eq_zero.mp hzero
    have h1 : ‖e i‖ = 1 := he.1 i
    rw [hz, norm_zero] at h1
    exact absurd h1 (by norm_num)
  refine ⟨e, fun i => ν i, he, heig, hνgt, ?_⟩
  -- The eigenbasis of `V` spans `V` back in the ambient space.
  have hrange : Set.range e
      = (Submodule.subtype (prolateEigenspaceSup T W c)) '' (Set.range b) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, Submodule.span_image, ← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- A Hilbert basis of `E` adapted to `E = V ⊕ Vᗮ`: its `V` half is an eigenbasis of `A` with every
eigenvalue exceeding `c`, and its `Vᗮ` half lies in `Vᗮ`.

The trace identities `tsum_inner_timeBandLimitingOp_eq` and
`tsum_inner_sub_norm_sq_timeBandLimitingOp_le` hold along an *arbitrary* Hilbert basis; feeding them
this one is what splits `tr A` and `tr A − tr A²` along the spectral cliff at `c`.

The `Vᗮ` half is an arbitrary Hilbert basis of `Vᗮ` (`exists_hilbertBasis`, i.e. Zorn) and is *not*
an eigenbasis: no complete eigenbasis of `A` is constructed anywhere. Completeness of the glued
family comes from `V` being spanned by the finite eigenbasis and `Vᗮ` by its own Hilbert basis, so
a vector orthogonal to all of them lies in `Vᗮ` with vanishing `Vᗮ`-coordinates, hence is zero.

Audited 2026-07-17 (independent). The "no complete eigenbasis of `A` on `E`" claim is machine-confirmed
by a constant-graph walk (validated against a positive control): this decl's closure does **not**
contain `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, the infinite-dimensional
totality lemma. It *does* contain `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot`
and `IsCompactOperator` — both via the finite-dimensional spectral theorem for `A|_V` and
`prolateEigenspaceSup_finiteDimensional`, i.e. about `V`, not about a complete eigenbasis on `E`.
sorryAx-free.
@audit:ok -/
theorem exists_hilbertBasis_prolateSplit (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ (κ : Type) (b : HilbertBasis (Fin (prolateCount T W c) ⊕ κ) ℂ E)
      (ν : Fin (prolateCount T W c) → ℝ),
      (∀ i, timeBandLimitingOp T W (b (Sum.inl i)) = ((ν i : ℂ)) • b (Sum.inl i)) ∧
      (∀ i, c < ν i) ∧
      (∀ j, b (Sum.inr j) ∈ (prolateEigenspaceSup T W c)ᗮ) := by
  classical
  obtain ⟨e, ν, he, heig, hνgt, hspan⟩ := exists_orthonormal_eigenbasis_prolateEigenspaceSup T W hc
  have hmemV : ∀ i, e i ∈ prolateEigenspaceSup T W c := by
    intro i
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨w, f, -⟩ := exists_hilbertBasis ℂ ↥(prolateEigenspaceSup T W c)ᗮ
  set g : w → E := fun j => ((f j : ↥(prolateEigenspaceSup T W c)ᗮ) : E) with hg
  have hgmem : ∀ j, g j ∈ (prolateEigenspaceSup T W c)ᗮ := fun j => (f j).2
  set v : Fin (prolateCount T W c) ⊕ w → E := Sum.elim e g with hvdef
  have hcross : ∀ i j, inner ℂ (e i) (g j) = (0 : ℂ) := fun i j =>
    Submodule.inner_right_of_mem_orthogonal (hmemV i) (hgmem j)
  have hcross' : ∀ i j, inner ℂ (g j) (e i) = (0 : ℂ) := fun i j =>
    Submodule.inner_left_of_mem_orthogonal (hmemV i) (hgmem j)
  have hv : Orthonormal ℂ v := by
    constructor
    · rintro (i | j)
      · exact he.1 i
      · exact f.orthonormal.1 j
    · rintro (i | j) (i' | j') hne
      · exact he.2 (fun h => hne (by rw [h]))
      · exact hcross i j'
      · exact hcross' i' j
      · exact f.orthonormal.2 (fun h => hne (by rw [h]))
  have hrange : Set.range v = Set.range e ∪ Set.range g := Set.Sum.elim_range e g
  have hspanv : Submodule.span ℂ (Set.range v)
      = prolateEigenspaceSup T W c ⊔ Submodule.span ℂ (Set.range g) := by
    rw [hrange, Submodule.span_union, hspan]
  have hbot : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [hspanv] at hx
    have hxV : x ∈ (prolateEigenspaceSup T W c)ᗮ :=
      Submodule.orthogonal_le le_sup_left hx
    have hxS : x ∈ (Submodule.span ℂ (Set.range g))ᗮ :=
      Submodule.orthogonal_le le_sup_right hx
    have hcoord : ∀ j : w, f.repr ⟨x, hxV⟩ j = 0 := by
      intro j
      rw [HilbertBasis.repr_apply_apply]
      have hcoe : inner ℂ (f j) (⟨x, hxV⟩ : ↥(prolateEigenspaceSup T W c)ᗮ)
          = inner ℂ (g j) x := rfl
      rw [hcoe]
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self j)) hxS
    have hz : (⟨x, hxV⟩ : ↥(prolateEigenspaceSup T W c)ᗮ) = 0 := by
      have : f.repr ⟨x, hxV⟩ = 0 := by
        ext j
        simpa using hcoord j
      simpa using congrArg f.repr.symm this
    simpa [Submodule.mem_bot] using congrArg (Subtype.val) hz
  refine ⟨w, HilbertBasis.mkOfOrthogonalEqBot hv hbot, ν, ?_, hνgt, ?_⟩
  · intro i
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact heig i
  · intro j
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact hgmem j

-- The inner-product/`star` bridge on `E = Lp ℂ 2 volume`. Mathlib equips `Lp` with only a bare
-- `Star` (no `StarAddMonoid`), so the interaction of complex conjugation with the L² inner product
-- is supplied by hand from `Lp.coeFn_star` and `integral_conj`.
theorem inner_star_star (x y : E) :
    (inner ℂ (star x) (star y) : ℂ) = starRingEnd ℂ (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star x, Lp.coeFn_star y] with t hx hy
  rw [hx, hy, Pi.star_apply, Pi.star_apply]
  simp only [RCLike.inner_apply, map_mul, RCLike.star_def, RCLike.conj_conj]

theorem real_inner_eq_re_complex (x y : E) :
    (inner ℝ x y : ℝ) = RCLike.re (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner x y)]
  apply integral_congr_ae
  filter_upwards with t
  rw [real_inner_eq_re_inner]

theorem inner_complex_eq_real_of_star_fixed (x y : E) (hx : star x = x) (hy : star y = y) :
    (inner ℂ x y : ℂ) = ((inner ℝ x y : ℝ) : ℂ) := by
  have hreal : starRingEnd ℂ (inner ℂ x y) = (inner ℂ x y : ℂ) := by
    conv_rhs => rw [← hx, ← hy]
    rw [inner_star_star]
  have hre : (inner ℂ x y : ℂ) = ((RCLike.re (inner ℂ x y) : ℝ) : ℂ) :=
    (RCLike.conj_eq_iff_re.mp hreal).symm
  rw [hre, ← real_inner_eq_re_complex]

theorem star_sub_Lp (f g : E) : star (f - g) = star f - star g := by
  have := map_sub (starₗE) f g
  simpa [starₗE] using this

/-- The real form of `V = prolateEigenspaceSup T W c`: its star-fixed elements, viewed as an
`ℝ`-subspace of `E`. Since `V` is conjugation-invariant (`star_mem_prolateEigenspaceSup`), it is the
complexification of this real form, and a real orthonormal basis of the real form is a
`ℂ`-orthonormal basis of `V` whose members are star-fixed (a.e. real-valued). -/
def realForm (T W c : ℝ) : Submodule ℝ E where
  carrier := {x | x ∈ prolateEigenspaceSup T W c ∧ star x = x}
  add_mem' {x y} hx hy := by
    refine ⟨add_mem hx.1 hy.1, ?_⟩
    rw [star_add_Lp, hx.2, hy.2]
  zero_mem' := ⟨zero_mem _, star_zero_Lp⟩
  smul_mem' r x hx := by
    refine ⟨Submodule.smul_mem _ _ hx.1, ?_⟩
    show star ((r : ℂ) • x) = (r : ℂ) • x
    rw [star_smul_Lp, hx.2, Complex.conj_ofReal]

/-- The canonical `ℝ`-linear injection of the real form into `↥V`, used to transport
finite-dimensionality of `V` over `ℝ` to its real form. -/
def realFormToV (T W c : ℝ) : realForm T W c →ₗ[ℝ] ↥(prolateEigenspaceSup T W c) where
  toFun x := ⟨(x : E), x.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realForm_finiteDimensional (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    FiniteDimensional ℝ (realForm T W c) := by
  haveI := prolateEigenspaceSup_finiteDimensional T W hc
  haveI : FiniteDimensional ℝ (prolateEigenspaceSup T W c) :=
    Module.Finite.trans ℂ (prolateEigenspaceSup T W c)
  refine FiniteDimensional.of_injective (realFormToV T W c) ?_
  intro a b hab
  have hE : (a : E) = (b : E) := congrArg (fun z : ↥(prolateEigenspaceSup T W c) => (z : E)) hab
  exact Subtype.coe_injective hE

/-- A star-fixed (a.e. real-valued) `ℂ`-orthonormal basis of `V = prolateEigenspaceSup T W c`.

`V` is finite-dimensional (`prolateEigenspaceSup_finiteDimensional`) and closed under complex
conjugation (`star_mem_prolateEigenspaceSup`), so it is the complexification of its real form
`V_ℝ = {v ∈ V | star v = v}` (`realForm`). A standard real orthonormal basis of `V_ℝ`
(`stdOrthonormalBasis`) is `ℂ`-orthonormal — its inner products are real for star-fixed vectors
(`inner_complex_eq_real_of_star_fixed`) — and `ℂ`-spans `V`: every `v ∈ V` decomposes as
`(v + star v)/2 + I·(I/2)·(star v − v)`, two star-fixed summands. Counting shows the basis has
`finrank ℂ V = prolateCount T W c` members, so it reindexes onto `Fin (prolateCount T W c)`. This is
the `ℂ/ℝ` bridge the achievability path needs: it lets the prolate eigenfunctions be chosen
real-valued.

This exports star-fixed elements of `E = Lp ℂ 2 volume` (whose a.e. representative is real-valued);
turning them into the `ℝ → ℝ` matched-filter test functions the `ContAwgnCode` consumer wants
(with `[0,T]` support / band-limit) is a further step, not established here. Also note `u` is an
orthonormal basis of `V` (a *sum* of eigenspaces over `{μ > c}`), not per se an `A`-eigenbasis:
its members span `V` but need not be single-eigenvalue eigenfunctions, so a downstream `ψᵢ/√μᵢ`
normalization requires first refining `u` into an eigenbasis — the same real-form bridge applied
eigenspace-by-eigenspace — which this theorem does not perform.

Audited 2026-07-18 (independent). `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
sorryAx-free, validated against the positive control `tsum_prolateEigenvalues_eq` (which does
show `sorryAx`) after refreshing the module olean. Signature is a plain existence: `hc : 0 < c`
is a regularity precondition (it makes `V` finite-dimensional via
`prolateEigenspaceSup_finiteDimensional`, otherwise `prolateCount` is a junk `0`), with no
`:= h` circularity, no `:True` slot, no load-bearing hypothesis. Body proves all three conjuncts
(`ℂ`-orthonormal, star-fixed, span `= V`); the count is *derived* (`finrank_span_eq_card` on the
`ℂ`-independent star-fixed family, `= prolateCount`), and the `prolateCount = 0` case is the
honest empty family with span `⊥ = V`, not a degenerate trick. No overclaim on
`ℝ → ℝ` / `[0,T]`-support.
@audit:ok -/
theorem exists_real_orthonormalBasis_prolateEigenspaceSup (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ u : Fin (prolateCount T W c) → E,
      Orthonormal ℂ u ∧ (∀ i, star (u i) = u i) ∧
      Submodule.span ℂ (Set.range u) = prolateEigenspaceSup T W c := by
  classical
  haveI := realForm_finiteDimensional T W hc
  set m := Module.finrank ℝ (realForm T W c) with hm
  set b := stdOrthonormalBasis ℝ (realForm T W c) with hb
  set w : Fin m → E := fun i => ((b i : realForm T W c) : E) with hw
  have hw_star : ∀ i, star (w i) = w i := fun i => (b i).2.2
  have hw_memV : ∀ i, w i ∈ prolateEigenspaceSup T W c := fun i => (b i).2.1
  have hrange : Set.range w = (realForm T W c).subtype '' (Set.range b) := by
    rw [← Set.range_comp]; rfl
  have hspanR : Submodule.span ℝ (Set.range w) = realForm T W c := by
    rw [hrange, Submodule.span_image, ← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  -- The real basis is `ℂ`-orthonormal: inner products of star-fixed vectors are real.
  have horth : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    have hb2 := b.orthonormal
    rw [orthonormal_iff_ite] at hb2
    have h1 : (inner ℝ (w i) (w j) : ℝ) = if i = j then (1 : ℝ) else 0 := by
      have := hb2 i j
      rwa [Submodule.coe_inner] at this
    rw [inner_complex_eq_real_of_star_fixed (w i) (w j) (hw_star i) (hw_star j), h1]
    split <;> simp
  -- The real basis `ℂ`-spans `V` via the star-fixed decomposition of each member.
  have hspanC : Submodule.span ℂ (Set.range w) = prolateEigenspaceSup T W c := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hw_memV i
    · intro v hv
      have hmem_span : ∀ x ∈ realForm T W c, x ∈ Submodule.span ℂ (Set.range w) := by
        intro x hx
        exact Submodule.span_le_restrictScalars ℝ ℂ (Set.range w) (hspanR.ge hx)
      have hsv : star v ∈ prolateEigenspaceSup T W c := star_mem_prolateEigenspaceSup hv
      have hconj_half : starRingEnd ℂ ((1 : ℂ) / 2) = 1 / 2 := by
        rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
      have hconj_I : starRingEnd ℂ (Complex.I / 2) = -(Complex.I / 2) := by
        rw [map_div₀, Complex.conj_I, show starRingEnd ℂ 2 = 2 from map_ofNat _ 2, neg_div]
      have hp_mem : ((1 : ℂ) / 2) • (v + star v) ∈ realForm T W c := by
        refine ⟨Submodule.smul_mem _ _ (add_mem hv hsv), ?_⟩
        rw [star_smul_Lp, star_add_Lp, star_star, hconj_half, add_comm]
      have hq_mem : (Complex.I / 2) • (star v - v) ∈ realForm T W c := by
        refine ⟨Submodule.smul_mem _ _ (sub_mem hsv hv), ?_⟩
        rw [star_smul_Lp, star_sub_Lp, star_star, hconj_I, neg_smul, ← smul_neg, neg_sub]
      have hvpq : v = ((1 : ℂ) / 2) • (v + star v)
          + Complex.I • ((Complex.I / 2) • (star v - v)) := by
        rw [smul_smul, show Complex.I * (Complex.I / 2) = ((-1) / 2 : ℂ) by
          rw [← mul_div_assoc, Complex.I_mul_I]]
        module
      rw [hvpq]
      exact add_mem (hmem_span _ hp_mem)
        (Submodule.smul_mem _ _ (hmem_span _ hq_mem))
  -- Being a `ℂ`-basis of `V`, the family has `finrank ℂ V = prolateCount` members.
  have hcard : m = prolateCount T W c := by
    have hli : LinearIndependent ℂ w := horth.linearIndependent
    have hfr := finrank_span_eq_card hli
    rw [hspanC] at hfr
    rw [prolateCount, hfr, Fintype.card_fin]
  refine ⟨fun i => w (Fin.cast hcard.symm i), ?_, ?_, ?_⟩
  · exact horth.comp _ (Fin.cast_injective _)
  · exact fun i => hw_star _
  · have hsurj : Function.Surjective (Fin.cast hcard.symm) :=
      fun y => ⟨Fin.cast hcard y, Fin.ext rfl⟩
    have hru : Set.range (fun i => w (Fin.cast hcard.symm i)) = Set.range w :=
      hsurj.range_comp w
    rw [hru, hspanC]

/-- Upper half of the eigenvalue count concentration: with `D := 2 + log(1 + 2WT)`, the number
of eigenvalues of `A` exceeding `c` is at most `2WT + D/c`, for every free threshold `0 < c`.

Together with `le_prolateCount` this is the Landau-Pollak-Slepian concentration
`#{λ > c} = 2WT ± O(log WT)`. The threshold `c` is a free variable, not fixed at `1/2`: the
downstream converse needs `c → 0` and the achievability needs `c → 1`, so a fixed `c` closes
neither.

*Not the Markov bound.* `prolateCount_mul_le` gives `#{λ > c} ≤ 2WT/c`, which overcounts by `1/c`
with no vanishing relative error. This bound has relative error `→ 0` as `WT → ∞` for fixed `c`,
which is what the exact constant in Shannon-Hartley needs. (Neither dominates pointwise: for small
`WT` the Markov bound is numerically tighter. The content here is the asymptotic shape.)

Mechanism: on `V` the adapted basis of `exists_hilbertBasis_prolateSplit` is an eigenbasis, so the
exact trace `tr A = 2WT` caps `∑_V λᵢ` (the rest of the trace being nonnegative) and the
second-moment bound `tr A − tr A² ≤ D` caps `∑_V λᵢ(1 − λᵢ)` (the deficit being nonnegative
termwise, by `A² ≤ A`). Since `λᵢ > c`, `∑_V (1 − λᵢ) ≤ (1/c) ∑_V λᵢ(1 − λᵢ) ≤ D/c`, and
`n − ∑_V λᵢ ≤ D/c` gives the claim. No eigenbasis of `A` on `E` is used; the spectral gap on `Vᗮ`
is not used either (machine-checked: this half's constant closure contains neither
`inner_timeBandLimitingOp_le_of_mem_orthogonal` nor
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`).

Degenerate boundaries: at `T = 0` both sides collapse to `0 ≤ D/c`; at `c ≥ 1` the count is `0`
(`prolateCount_one_eq_zero` and antitonicity) and the bound is slack. Neither refutes it.

Audited 2026-07-17 (independent). All four hypotheses are regularity on scalars; nothing of the
form "`A` has a complete eigenbasis" / "`S² ≤ cS`" / "an adapted basis exists" is assumed — each is
*derived* (`exists_hilbertBasis_prolateSplit`, `norm_timeBandLimitingOp_sq_le_of_mem_orthogonal`).
sorryAx-free. The "not Markov" claim was re-adjudicated against the consumer docstrings rather than
the plan: the consumers' figure of merit is the DOF density `n(T)/T` as `T → ∞`, where Markov gives
`2W/c` (wrong constant, diverging as `c → 0`) and this bound gives exactly `2W` for every fixed
`c > 0`. The pointwise incomparability at small `WT` is real but is not the figure of merit.
The closure claim above was re-run with a probe validated against a positive control.
@audit:ok -/
theorem prolateCount_le (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) {c : ℝ} (hc : 0 < c) :
    (prolateCount T W c : ℝ) ≤ 2 * W * T + (2 + Real.log (1 + 2 * W * T)) / c := by
  classical
  obtain ⟨κ, b, ν, heig, hνgt, -⟩ := exists_hilbertBasis_prolateSplit T W hc
  set D : ℝ := 2 + Real.log (1 + 2 * W * T) with hD
  set a : Fin (prolateCount T W c) ⊕ κ → ℝ :=
    fun x => (inner ℂ (timeBandLimitingOp T W (b x)) (b x)).re with ha
  have hnn : ∀ x, 0 ≤ a x := fun x => inner_timeBandLimitingOp_self_nonneg T W hW.le (b x)
  have hs1 : Summable a := summable_inner_timeBandLimitingOp_self T W hT hW b.orthonormal
  have hs2 : Summable (fun x => ‖timeBandLimitingOp T W (b x)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun x => by positivity)
      (fun x => norm_timeBandLimitingOp_sq_le_inner T W (b x)) hs1
  -- On the `V` half the basis is an eigenbasis, so `a (inl i) = νᵢ` and `‖A bᵢ‖ = νᵢ`.
  have hbnorm : ∀ i, ‖b (Sum.inl i)‖ = 1 := fun i => b.orthonormal.1 _
  have hval : ∀ i, a (Sum.inl i) = ν i := by
    intro i
    rw [ha]
    simp only
    rw [heig i, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, hbnorm i]
    simp
  have hAnorm : ∀ i, ‖timeBandLimitingOp T W (b (Sum.inl i))‖ = ν i := by
    intro i
    rw [heig i, norm_smul, Complex.norm_real, Real.norm_eq_abs, hbnorm i, mul_one,
      abs_of_pos (lt_trans hc (hνgt i))]
  have hν1 : ∀ i, ν i ≤ 1 := by
    intro i
    rw [← hAnorm i]
    calc ‖timeBandLimitingOp T W (b (Sum.inl i))‖
        ≤ ‖timeBandLimitingOp T W‖ * ‖b (Sum.inl i)‖ :=
          (timeBandLimitingOp T W).le_opNorm _
      _ = ‖timeBandLimitingOp T W‖ := by rw [hbnorm i, mul_one]
      _ ≤ 1 := timeBandLimitingOp_norm_le_one T W
  -- The `V` part of the trace is capped by the exact trace `2WT`.
  have himg : (Finset.univ.image (Sum.inl : Fin (prolateCount T W c) → _)).sum a
      = ∑ i, ν i := by
    rw [Finset.sum_image (by intro x _ y _ h; exact Sum.inl.inj h)]
    exact Finset.sum_congr rfl fun i _ => hval i
  have hsum_le : ∑ i, ν i ≤ 2 * W * T := by
    rw [← himg, ← tsum_inner_timeBandLimitingOp_eq T W hT hW b]
    exact hs1.sum_le_tsum _ (fun x _ => hnn x)
  -- The `V` part of the second-moment deficit is capped by `D`.
  have hdefnn : ∀ x, 0 ≤ a x - ‖timeBandLimitingOp T W (b x)‖ ^ 2 :=
    fun x => sub_nonneg.mpr (norm_timeBandLimitingOp_sq_le_inner T W (b x))
  have himg2 : (Finset.univ.image (Sum.inl : Fin (prolateCount T W c) → _)).sum
      (fun x => a x - ‖timeBandLimitingOp T W (b x)‖ ^ 2) = ∑ i, (ν i - (ν i) ^ 2) := by
    rw [Finset.sum_image (by intro x _ y _ h; exact Sum.inl.inj h)]
    exact Finset.sum_congr rfl fun i _ => by rw [hval i, hAnorm i]
  have hdef_le : ∑ i, (ν i - (ν i) ^ 2) ≤ D := by
    rw [← himg2]
    exact le_trans ((hs1.sub hs2).sum_le_tsum _ (fun x _ => hdefnn x))
      (tsum_inner_sub_norm_sq_timeBandLimitingOp_le T W hT hW b)
  -- `λ > c` turns the deficit into a bound on `n − ∑ λ`.
  have hkey : c * ((prolateCount T W c : ℝ) - ∑ i, ν i) ≤ D := by
    have hterm : ∀ i ∈ Finset.univ, c * (1 - ν i) ≤ ν i - (ν i) ^ 2 := by
      intro i _
      nlinarith [hνgt i, hν1 i]
    have := le_trans (Finset.sum_le_sum hterm) hdef_le
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at this
    simpa using this
  have h1 : (prolateCount T W c : ℝ) - ∑ i, ν i ≤ D / c :=
    (le_div_iff₀ hc).mpr (by linarith [hkey])
  linarith [h1, hsum_le]

/-- Lower half of the eigenvalue count concentration: with `D := 2 + log(1 + 2WT)`, the number
of eigenvalues of `A` exceeding `c` is at least `2WT − D/(1 − c)`, for every free `0 < c < 1`.

The companion of `prolateCount_le`. This is the half no trace bound alone can reach: `tr A = 2WT`
is a coarse scalar and does not by itself forbid a flat spectrum with every `λ ≤ c` and count `0`.
What rules that out is the second moment.

Mechanism: split the exact trace along the adapted basis of `exists_hilbertBasis_prolateSplit`,
`2WT = ∑_V λᵢ + ∑_{Vᗮ} aⱼ`. Each `λᵢ ≤ 1` (contraction), so `∑_V λᵢ ≤ n`. On `Vᗮ` the sharpened
operator inequality `A² ≤ cA` (`norm_timeBandLimitingOp_sq_le_of_mem_orthogonal`) makes each
deficit `aⱼ − ‖A bⱼ‖² ≥ (1 − c) aⱼ`, and the second-moment bound `tr A − tr A² ≤ D` caps the sum of
deficits, so `∑_{Vᗮ} aⱼ ≤ D/(1 − c)`.

`hc1 : c < 1` is a genuine precondition, not padding: at `c = 1` Lean's `x/0 = 0` convention would
read the claim as `2WT ≤ #{λ > 1} = 0` (`prolateCount_one_eq_zero`), which is false for `WT > 0`.
As `c ↑ 1` the bound degrades to `−∞`, consistently. At `T = 0` it reads `−D/(1−c) ≤ 0`, true.
The bound has content rather than holding vacuously: at `c = 1/2` it bites once `2WT ≳ 8`.

Audited 2026-07-17 (independent). sorryAx-free; hypotheses are regularity only. Two claims above
were machine-checked rather than accepted: (a) `hc1` is genuinely load-bearing as a *precondition* —
the `c = 1` instance of this conclusion was **proved false** at `T = W = 1` (via
`prolateCount_one_eq_zero` + `x/0 = 0`), so dropping `hc1` would make the statement false, not merely
weaker; (b) the `2WT ≳ 8` crossover is accurate (numerically, the bound turns positive at
`2WT ≈ 8.5`). Markov (`prolateCount_mul_le`) cannot substitute here at any `c`: it is an upper bound
only and supplies no lower half at all. Density `n(T)/T → 2W` for every fixed `c < 1`, which is what
the achievability consumer's iterated limit (`T → ∞`, then `c → 1`) needs.
@audit:ok -/
theorem le_prolateCount (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    2 * W * T - (2 + Real.log (1 + 2 * W * T)) / (1 - c) ≤ (prolateCount T W c : ℝ) := by
  classical
  obtain ⟨κ, b, ν, heig, hνgt, hperp⟩ := exists_hilbertBasis_prolateSplit T W hc
  set D : ℝ := 2 + Real.log (1 + 2 * W * T) with hD
  set a : Fin (prolateCount T W c) ⊕ κ → ℝ :=
    fun x => (inner ℂ (timeBandLimitingOp T W (b x)) (b x)).re with ha
  have hnn : ∀ x, 0 ≤ a x := fun x => inner_timeBandLimitingOp_self_nonneg T W hW.le (b x)
  have hs1 : Summable a := summable_inner_timeBandLimitingOp_self T W hT hW b.orthonormal
  have hs2 : Summable (fun x => ‖timeBandLimitingOp T W (b x)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun x => by positivity)
      (fun x => norm_timeBandLimitingOp_sq_le_inner T W (b x)) hs1
  have hbnorm : ∀ i, ‖b (Sum.inl i)‖ = 1 := fun i => b.orthonormal.1 _
  have hval : ∀ i, a (Sum.inl i) = ν i := by
    intro i
    rw [ha]
    simp only
    rw [heig i, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, hbnorm i]
    simp
  have hν1 : ∀ i, ν i ≤ 1 := by
    intro i
    have hAn : ‖timeBandLimitingOp T W (b (Sum.inl i))‖ = ν i := by
      rw [heig i, norm_smul, Complex.norm_real, Real.norm_eq_abs, hbnorm i, mul_one,
        abs_of_pos (lt_trans hc (hνgt i))]
    rw [← hAn]
    calc ‖timeBandLimitingOp T W (b (Sum.inl i))‖
        ≤ ‖timeBandLimitingOp T W‖ * ‖b (Sum.inl i)‖ :=
          (timeBandLimitingOp T W).le_opNorm _
      _ = ‖timeBandLimitingOp T W‖ := by rw [hbnorm i, mul_one]
      _ ≤ 1 := timeBandLimitingOp_norm_le_one T W
  -- Split the exact trace `2WT` along `E = V ⊕ Vᗮ`.
  have hsr : Summable (fun j : κ => a (Sum.inr j)) :=
    hs1.comp_injective Sum.inr_injective
  have hsplit : ∑' i, ν i + ∑' j : κ, a (Sum.inr j) = 2 * W * T := by
    rw [← tsum_inner_timeBandLimitingOp_eq T W hT hW b,
      Summable.tsum_sum (f := a) Summable.of_finite hsr]
    exact congrArg (· + ∑' j : κ, a (Sum.inr j)) (tsum_congr fun i => (hval i).symm)
  have hVle : ∑' i, ν i ≤ (prolateCount T W c : ℝ) := by
    rw [tsum_fintype]
    calc ∑ i, ν i ≤ ∑ _i : Fin (prolateCount T W c), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hν1 i
      _ = (prolateCount T W c : ℝ) := by simp
  -- The `Vᗮ` part of the second-moment deficit is capped by `D`.
  have hdefnn : ∀ x, 0 ≤ a x - ‖timeBandLimitingOp T W (b x)‖ ^ 2 :=
    fun x => sub_nonneg.mpr (norm_timeBandLimitingOp_sq_le_inner T W (b x))
  have hsdr : Summable (fun j : κ => a (Sum.inr j)
      - ‖timeBandLimitingOp T W (b (Sum.inr j))‖ ^ 2) :=
    (hs1.sub hs2).comp_injective Sum.inr_injective
  have hdef_le : ∑' j : κ, (a (Sum.inr j)
      - ‖timeBandLimitingOp T W (b (Sum.inr j))‖ ^ 2) ≤ D := by
    have hfull := tsum_inner_sub_norm_sq_timeBandLimitingOp_le T W hT hW b
    rw [Summable.tsum_sum
      (f := fun x => a x - ‖timeBandLimitingOp T W (b x)‖ ^ 2) Summable.of_finite hsdr] at hfull
    have hinl : 0 ≤ ∑' i, (a (Sum.inl i)
        - ‖timeBandLimitingOp T W (b (Sum.inl i))‖ ^ 2) := by
      rw [tsum_fintype]
      exact Finset.sum_nonneg fun i _ => hdefnn (Sum.inl i)
    linarith
  -- `A² ≤ cA` on `Vᗮ` turns the deficit into a bound on the `Vᗮ` trace.
  have hgap : ∀ j : κ, (1 - c) * a (Sum.inr j)
      ≤ a (Sum.inr j) - ‖timeBandLimitingOp T W (b (Sum.inr j))‖ ^ 2 := by
    intro j
    have := norm_timeBandLimitingOp_sq_le_of_mem_orthogonal T W c hc (hperp j)
    have hle : ‖timeBandLimitingOp T W (b (Sum.inr j))‖ ^ 2 ≤ c * a (Sum.inr j) := this
    linarith
  have hperp_le : ∑' j : κ, a (Sum.inr j) ≤ D / (1 - c) := by
    have h1c : (0 : ℝ) < 1 - c := by linarith
    have hmul : (1 - c) * ∑' j : κ, a (Sum.inr j) ≤ D := by
      rw [← tsum_mul_left]
      exact le_trans ((hsr.mul_left (1 - c)).tsum_le_tsum hgap hsdr) hdef_le
    rw [le_div_iff₀ h1c]
    linarith
  linarith [hsplit, hVle, hperp_le]

end EigenvalueCount

section Achievability

/-!
### Operator-level bricks for the achievability pre-equalizer (route ii)

The continuous-time AWGN achievability receiver sees a band-limited codeword `v ∈ V =
`prolateEigenspaceSup T W c`` through the time-limiting filter `Q_T`. The core operator fact is the
*time-window energy concentration*: on `V` the time-limited energy `‖Q_T v‖²` retains at least the
fraction `c` of the total energy `‖v‖²`. These three bricks package that into the exact shapes the
pre-equalizer consumes: the concentration inequality itself, the injectivity of `Q_T|_V` it implies,
and the Gram lower bound `G ≥ c·I` on a `V`-ONB used to bound the pre-equalizer gain `G⁻¹ ≤ (1/c)I`.

Sizing memo for the next leg (A2 `testFn` construction): the dominant cost of the `testFn`
construction is the `Lp`-class → pointwise `ℝ → ℝ` representative lift (route-independent); the
`testFn` themselves are the `[0,T]`-supported real ONB of `Q_T(V)`.
-/

/-- Members of `V = prolateEigenspaceSup T W c` are band-limited: `V ≤ bandLimitSubspace W`.

An eigenvector for eigenvalue `μ > c > 0` satisfies `A v = μ v`; since `A = P_W ∘ Q_T ∘ P_W` has
range inside `bandLimitSubspace W`, so does `μ v`, and `μ ≠ 0` gives `v ∈ bandLimitSubspace W`. The
span of these eigenspaces stays inside the closed subspace `bandLimitSubspace W`. -/
theorem prolateEigenspaceSup_le_bandLimitSubspace (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    prolateEigenspaceSup T W c ≤ bandLimitSubspace W := by
  rw [prolateEigenspaceSup]
  refine iSup₂_le fun μ hμ => ?_
  intro w hw
  rw [Module.End.mem_eigenspace_iff] at hw
  have hw' : timeBandLimitingOp T W w = (μ : ℂ) • w := hw
  have hAmem : timeBandLimitingOp T W w ∈ bandLimitSubspace W := by
    simp only [timeBandLimitingOp, ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_apply_mem _ _
  rw [hw'] at hAmem
  have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc.trans hμ.1).ne'
  have := Submodule.smul_mem (bandLimitSubspace W) (μ : ℂ)⁻¹ hAmem
  rwa [smul_smul, inv_mul_cancel₀ hμ0, one_smul] at this

/-- Time-window energy concentration: for `v ∈ V = prolateEigenspaceSup T W c` and `0 < c`, the
time-limited energy retains at least the fraction `c` of the total energy:
`c ‖v‖² ≤ ‖Q_T v‖²`, where `Q_T = (timeLimitSubspace T).starProjection`.

This is the prolate-spheroidal concentration statement the achievability receiver relies on. It comes
straight from `le_inner_timeBandLimitingOp_of_mem` (the Rayleigh lower bound `c‖v‖² ≤ ⟪A v, v⟫`) once
the polarization identity `inner_timeBandLimitingOp_eq_inner_timeLimit_bandLimit` collapses
`⟪A v, v⟫` to `‖Q_T P_W v‖²` and `prolateEigenspaceSup_le_bandLimitSubspace` removes `P_W` on `V`. -/
theorem le_norm_timeLimitProj_sq_of_mem (T W c : ℝ) (hc : 0 < c) {v : E}
    (hv : v ∈ prolateEigenspaceSup T W c) :
    c * ‖v‖ ^ 2 ≤ ‖(timeLimitSubspace T).starProjection v‖ ^ 2 := by
  have hPv : (bandLimitSubspace W).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr
      (prolateEigenspaceSup_le_bandLimitSubspace T W hc hv)
  have hself : ∀ z : E, (inner ℂ z z).re = ‖z‖ ^ 2 := fun z => by
    rw [inner_self_eq_norm_sq_to_K]; simp [← Complex.ofReal_pow]
  have h1 := le_inner_timeBandLimitingOp_of_mem T W c hc hv
  have h2 : inner ℂ (timeBandLimitingOp T W v) v
      = inner ℂ ((timeLimitSubspace T).starProjection v)
          ((timeLimitSubspace T).starProjection v) := by
    calc inner ℂ (timeBandLimitingOp T W v) v
        = inner ℂ ((timeLimitSubspace T).starProjection
              ((bandLimitSubspace W).starProjection v))
            ((timeLimitSubspace T).starProjection
              ((bandLimitSubspace W).starProjection v)) :=
          inner_timeBandLimitingOp_eq_inner_timeLimit_bandLimit T W v v
      _ = inner ℂ ((timeLimitSubspace T).starProjection v)
            ((timeLimitSubspace T).starProjection v) := by rw [hPv]
  rw [h2, hself] at h1
  exact h1

/-- The time-limiting projection `Q_T` is injective on `V`: for `0 < c`, a `V`-member annihilated
by `Q_T` is zero. Immediate corollary of the energy concentration: `Q_T v = 0` forces
`c ‖v‖² ≤ 0`, and `c > 0` gives `v = 0`. -/
theorem eq_zero_of_timeLimitProj_eq_zero (T W c : ℝ) (hc : 0 < c) {v : E}
    (hv : v ∈ prolateEigenspaceSup T W c)
    (hQ : (timeLimitSubspace T).starProjection v = 0) :
    v = 0 := by
  have h := le_norm_timeLimitProj_sq_of_mem T W c hc hv
  rw [hQ, norm_zero] at h
  have hz : ‖v‖ ^ 2 ≤ 0 := by nlinarith [hc, sq_nonneg ‖v‖]
  have hnorm0 : ‖v‖ = 0 := le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v)
  exact norm_eq_zero.mp hnorm0

/-- The Gram lower bound `G ≥ c·I` on an orthonormal basis of `V`: for a `ℂ`-orthonormal family `u`
inside
`V = prolateEigenspaceSup T W c` and real coefficients `b`, the quadratic form of `A` on the
combination `x = ∑ᵢ bᵢ • uᵢ` dominates `c ∑ᵢ bᵢ²`:
`c ∑ᵢ bᵢ² ≤ Re⟪A x, x⟫`.

This is the operator matrix lower bound the pre-equalizer uses to get `G⁻¹ ≤ (1/c)I`. No per-vector
eigenvalue `μᵢ` is used (`u` is only assumed orthonormal, not an eigenbasis): `x ∈ V` because `V` is
a submodule, `‖x‖² = ∑ᵢ bᵢ²` because `u` is orthonormal, and `le_inner_timeBandLimitingOp_of_mem`
supplies `c ‖x‖² ≤ Re⟪A x, x⟫` on `V`. -/
theorem le_re_inner_timeBandLimitingOp_sum_smul (T W c : ℝ) (hc : 0 < c)
    {u : Fin (prolateCount T W c) → E} (hu : Orthonormal ℂ u)
    (hmem : ∀ i, u i ∈ prolateEigenspaceSup T W c) (b : Fin (prolateCount T W c) → ℝ) :
    c * ∑ i, b i ^ 2
      ≤ (inner ℂ (timeBandLimitingOp T W (∑ i, (b i : ℂ) • u i))
          (∑ i, (b i : ℂ) • u i)).re := by
  set x : E := ∑ i, (b i : ℂ) • u i with hx
  have hxV : x ∈ prolateEigenspaceSup T W c := by
    rw [hx]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hmem i))
  have h1 := le_inner_timeBandLimitingOp_of_mem T W c hc hxV
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [← Complex.ofReal_pow]
  have hip : inner ℂ x x = ((∑ i, b i ^ 2 : ℝ) : ℂ) := by
    rw [hx, hu.inner_sum (fun i => (b i : ℂ)) (fun i => (b i : ℂ)) Finset.univ,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.conj_ofReal]
    push_cast
    ring
  have hnorm : ‖x‖ ^ 2 = ∑ i, b i ^ 2 := by
    rw [← hself, hip, Complex.ofReal_re]
  rw [hnorm] at h1
  exact h1

/-- Pointwise `ℝ → ℝ` lift of an `Lp` class supported in the window. A star-fixed `L²(ℝ;ℂ)`
element that is a.e.-supported in `[0,T]` — the shape `Q_T ψ` takes for a star-fixed `ψ ∈ V` — has
a genuine pointwise real representative supported in `[0,T]`: a function `f : ℝ → ℝ` with `f` in
`L²`, `Function.support f ⊆ [0,T]` *pointwise*, and `(f : ℝ → ℂ)` a.e. equal to the given class.

This is what the `ContAwgnCode.testFn` construction costs: it
converts an a.e. equivalence class into the honest pointwise `ℝ → ℝ` function the structure field
`testFn` demands, pinning both the pointwise support (`testFn_support`) and the real-valuedness. Once
the a.e. identity `(f : ℝ → ℂ) =ᵐ u` is in hand, every integral/inner-product fact about the family
(orthonormality, energy) transfers from the `Lp` inner product for free, so a single lift lemma
sizes the whole conversion. The representative is `𝟙_[0,T] · Re(u)`; the indicator pins the support
pointwise while staying in the same class because `u` already vanishes a.e. off `[0,T]`, and `Re`
recovers a real representative because `u` is star-fixed (a.e. real). -/
theorem exists_pointwise_repr_of_mem_timeLimit_star_fixed (T : ℝ) {u : E}
    (hmem : u ∈ timeLimitSubspace T) (hstar : star u = u) :
    ∃ f : ℝ → ℝ, MemLp f 2 volume ∧ Function.support f ⊆ Set.Icc 0 T ∧
      (fun t => ((f t : ℝ) : ℂ)) =ᵐ[volume] (u : ℝ → ℂ) := by
  classical
  -- `u` is a.e. real-valued (star-fixed): `star u = u` forces `u t = conj (u t)` a.e.
  have hconj : (u : ℝ → ℂ) =ᵐ[volume] fun t => starRingEnd ℂ ((u : ℝ → ℂ) t) := by
    have h1 : (⇑(star u) : ℝ → ℂ) =ᵐ[volume] fun t => starRingEnd ℂ ((u : ℝ → ℂ) t) := by
      filter_upwards [Lp.coeFn_star u] with t ht
      rw [ht]; rfl
    rwa [hstar] at h1
  have hre : ∀ᵐ t ∂volume, (((u : ℝ → ℂ) t).re : ℂ) = (u : ℝ → ℂ) t := by
    filter_upwards [hconj] with t ht
    exact Complex.conj_eq_iff_re.mp ht.symm
  -- `u` is a.e. zero off `[0,T]` (it lies in the time-limited subspace).
  have hset : MeasurableSet {t : ℝ | t < 0 ∨ T < t} := by
    have hsplit : {t : ℝ | t < 0 ∨ T < t} = Set.Iio 0 ∪ Set.Ioi T := by
      ext t; simp [Set.mem_Iio, Set.mem_Ioi]
    rw [hsplit]; exact measurableSet_Iio.union measurableSet_Ioi
  have hoff : ∀ᵐ t ∂volume, t ∈ {t : ℝ | t < 0 ∨ T < t} → (u : ℝ → ℂ) t = 0 := by
    rw [← ae_restrict_iff' hset]
    have hz : (⇑u : ℝ → ℂ) =ᵐ[volume.restrict {t : ℝ | t < 0 ∨ T < t}] 0 := hmem
    filter_upwards [hz] with t ht using by simpa using ht
  refine ⟨(Set.Icc (0 : ℝ) T).indicator (fun s => ((u : ℝ → ℂ) s).re), ?_, ?_, ?_⟩
  · -- `MemLp`: the real part is `L²` (norm-1 Lipschitz image of `u`), and indicators preserve it.
    exact MemLp.indicator measurableSet_Icc (Lp.memLp u).re
  · -- Pointwise support: an indicator vanishes off its set.
    intro x hx
    by_contra hxS
    exact hx (Set.indicator_of_notMem hxS _)
  · -- The a.e. identity `(f : ℝ → ℂ) =ᵐ u`, split by membership in `[0,T]`.
    filter_upwards [hre, hoff] with t ht htoff
    by_cases hmem_t : t ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hmem_t]; exact ht
    · rw [Set.indicator_of_notMem hmem_t, Complex.ofReal_zero]
      have htc : t < 0 ∨ T < t := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem_t; exact hmem_t
      exact (htoff htc).symm

/-- Pointwise `ℝ → ℝ` lift of an `Lp` class, without a support constraint. A star-fixed `L²(ℝ;ℂ)`
element has a genuine pointwise real representative: a function `f : ℝ → ℝ` in `L²` with
`(f : ℝ → ℂ)` a.e. equal to the given class. This is the support-free sibling of
`exists_pointwise_repr_of_mem_timeLimit_star_fixed`, needed for the band-limited encoder family whose
members are not `[0,T]`-supported. The representative is `Re ∘ u`: it is `L²` because `Re` is a norm-1
Lipschitz image, and it recovers a representative of `u` because star-fixedness (`star u = u`) makes
`u` a.e. real. -/
theorem exists_pointwise_repr_of_star_fixed {u : E} (hstar : star u = u) :
    ∃ f : ℝ → ℝ, MemLp f 2 volume ∧
      (fun t => ((f t : ℝ) : ℂ)) =ᵐ[volume] (u : ℝ → ℂ) := by
  -- `u` is a.e. real-valued (star-fixed): `star u = u` forces `u t = conj (u t)` a.e.
  have hconj : (u : ℝ → ℂ) =ᵐ[volume] fun t => starRingEnd ℂ ((u : ℝ → ℂ) t) := by
    have h1 : (⇑(star u) : ℝ → ℂ) =ᵐ[volume] fun t => starRingEnd ℂ ((u : ℝ → ℂ) t) := by
      filter_upwards [Lp.coeFn_star u] with t ht
      rw [ht]; rfl
    rwa [hstar] at h1
  have hre : ∀ᵐ t ∂volume, (((u : ℝ → ℂ) t).re : ℂ) = (u : ℝ → ℂ) t := by
    filter_upwards [hconj] with t ht
    exact Complex.conj_eq_iff_re.mp ht.symm
  refine ⟨fun s => ((u : ℝ → ℂ) s).re, (Lp.memLp u).re, ?_⟩
  filter_upwards [hre] with t ht using ht

/-- Band-limitedness transports from the frequency-support subspace to a pointwise real
representative. If `v ∈ bandLimitSubspace W` and `f : ℝ → ℝ` complexifies to an a.e.-representative
of `v`, then `IsBandlimited f W`. This is the bridge that lets the operator-theoretic
`bandLimitSubspace` feed the `L²`-Fourier-support predicate `IsBandlimited` used by the
`ContAwgnCode` band-limit constraint. -/
theorem isBandlimited_of_bandLimitSubspace_ae {W : ℝ} {v : E} (hv : v ∈ bandLimitSubspace W)
    {f : ℝ → ℝ} (hf : (fun t => ((f t : ℝ) : ℂ)) =ᵐ[volume] (v : ℝ → ℂ)) :
    ShannonHartley.IsBandlimited f W := by
  -- The complexified real representative is `L²` (a.e. equal to the `Lp` element `v`).
  have hf' : MemLp (fun t : ℝ => ((f t : ℝ) : ℂ)) 2 volume := MemLp.ae_eq hf.symm (Lp.memLp v)
  -- Its canonical `Lp` representative is `v` itself.
  have heq : hf'.toLp (fun t : ℝ => ((f t : ℝ) : ℂ)) = v :=
    (MemLp.toLp_congr hf' (Lp.memLp v) hf).trans (Lp.toLp_coeFn v (Lp.memLp v))
  rw [bandLimitSubspace, Submodule.mem_comap] at hv
  refine ⟨hf', ?_⟩
  rw [heq]
  -- The goal is the a.e. vanishing of `𝓕 v` off the band; membership in `zeroOnLp` is defeq to it.
  show (𝓕 v : E) ∈ zeroOnLp {ξ : ℝ | W < |ξ|}
  exact hv

/-- The real band-limited orthonormal encoder family for `V = prolateEigenspaceSup T W c`. Bundles
the star-fixed `ℂ`-orthonormal basis `u` of `V` (needed to feed the operator lower bounds
`le_norm_timeLimitProj_sq_of_mem` / `le_re_inner_timeBandLimitingOp_sum_smul`, which are stated on
`V`) together with concrete real representatives `h i : ℝ → ℝ` of each `u i`, their `L²`-membership,
the a.e. link `(h i : ℂ) =ᵐ u i`, band-limitedness `IsBandlimited (h i) W`, and the real
orthonormality `∫ h i · h j = δ_{ij}`. This is the encoder-side family the achievability receiver
constructs signals from. -/
theorem exists_real_bandlimited_onb (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ (u : Fin (prolateCount T W c) → E) (h : Fin (prolateCount T W c) → (ℝ → ℝ)),
      Orthonormal ℂ u ∧ (∀ i, star (u i) = u i) ∧
      Submodule.span ℂ (Set.range u) = prolateEigenspaceSup T W c ∧
      (∀ i, MemLp (h i) 2 volume) ∧
      (∀ i, (fun t => ((h i t : ℝ) : ℂ)) =ᵐ[volume] (u i : ℝ → ℂ)) ∧
      (∀ i, ShannonHartley.IsBandlimited (h i) W) ∧
      (∀ i j, (∫ t, h i t * h j t) = if i = j then (1 : ℝ) else 0) := by
  classical
  obtain ⟨u, hu_on, hu_star, hu_span⟩ := exists_real_orthonormalBasis_prolateEigenspaceSup T W hc
  -- Skolemize the per-`i` real representatives.
  choose h hmem hae using fun i => exists_pointwise_repr_of_star_fixed (hu_star i)
  -- Each `u i` lies in `V`, hence in `bandLimitSubspace W`.
  have hmemV : ∀ i, u i ∈ prolateEigenspaceSup T W c := by
    intro i
    rw [← hu_span]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hbl : ∀ i, ShannonHartley.IsBandlimited (h i) W := fun i =>
    isBandlimited_of_bandLimitSubspace_ae
      (prolateEigenspaceSup_le_bandLimitSubspace T W hc (hmemV i)) (hae i)
  refine ⟨u, h, hu_on, hu_star, hu_span, hmem, hae, hbl, ?_⟩
  -- Real orthonormality: transport `∫ h i · h j` to `Re ⟪u i, u j⟫_ℂ`.
  intro i j
  have hinner : (inner ℂ (u i) (u j) : ℂ) = ((∫ t, h i t * h j t : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hae i, hae j] with t hti htj
    have hti' : (u i : ℝ → ℂ) t = ((h i t : ℝ) : ℂ) := hti.symm
    have htj' : (u j : ℝ → ℂ) t = ((h j t : ℝ) : ℂ) := htj.symm
    rw [RCLike.inner_apply, hti', htj', Complex.conj_ofReal]
    push_cast
    ring
  have hval : (∫ t, h i t * h j t) = (inner ℂ (u i) (u j) : ℂ).re := by
    rw [hinner, Complex.ofReal_re]
  rw [hval, (orthonormal_iff_ite.mp hu_on) i j]
  split_ifs <;> simp

end Achievability
end InformationTheory.Shannon.TimeBandLimiting
