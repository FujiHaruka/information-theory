import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import InformationTheory.Shannon.NormalizedSinc
import InformationTheory.Shannon.ShannonHartleyAchievability

/-!
# The time-and-band-limiting operator on `L²(ℝ;ℂ)`

Cover–Thomas Ch. 9.6 (Shannon–Hartley), Phase 2 spectral leg A. This file builds the
self-adjoint positive contraction

    `A = P_W ∘ Q_T ∘ P_W`

on the complex Hilbert space `E = L²(ℝ;ℂ)`, where `Q_T` is the orthogonal projection onto the
time-limited subspace (functions a.e.-supported in `[0,T]`) and `P_W` the projection onto the
band-limited subspace (functions whose L²-Fourier transform is a.e.-supported in `[-W,W]`). Both
projections are `Submodule.starProjection`s onto genuinely closed subspaces, so `A`'s
self-adjointness and positivity are one-line consequences of the projection API.

## Main statements

* `timeLimitSubspace` / `bandLimitSubspace` — the two closed subspaces.
* `timeBandLimitingOp` — the operator `A = P_W ∘ Q_T ∘ P_W`.
* `timeBandLimitingOp_isSelfAdjoint` — `A` is self-adjoint.
* `timeBandLimitingOp_isPositive` — `A` is a positive operator.
* `timeBandLimitingOp_norm_le_one` — `‖A‖ ≤ 1` (contraction).

Leg B adds compactness `timeBandLimitingOp_isCompact`, reducing it — via `A = P_W ∘ C` with
`C = Q_T ∘ P_W` — to compactness of the sinc integral operator `C`, whose Hilbert–Schmidt kernel is
`sincConvKernel t s = 𝟙_[0,T](t) · 2W · sincN(2W(t−s))`.

Leg C adds the decreasing eigenvalue enumeration. Mathlib's ordered `ℕ → ℝ` eigenvalue sequence is
`FiniteDimensional`-gated, so it is rebuilt here from the structural compact self-adjoint spectral
theorem: `prolateEigenvalueSet_finite` (only finitely many eigenvalues exceed any `c > 0`) makes the
counting function `prolateCount` honest, and `prolateEigenvalues` is its generalized inverse.

* `prolateEigenvalueSet_finite` — finitely many eigenvalues above any positive threshold.
* `prolateEigenvalues` — the eigenvalues of `A` in decreasing order, listed with multiplicity.
* `prolateEigenvalues_antitone` / `_nonneg` / `_le_one` — the enumeration decreases within `[0,1]`.
* `prolateEigenvalues_hasEigenvalue` — every nonzero entry is a genuine eigenvalue of `A`.
* `prolateEigenvalues_tendsto_zero` — the enumeration tends to `0`.

The Landau–Pollak–Slepian concentration count (`prolate_eigenvalue_count`, `≈ 2WT` eigenvalues near
`1`) lives in a later leg.
-/

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory
open scoped ENNReal symmDiff FourierTransform

/-- The `L²(ℝ;ℂ)` Hilbert space the operator acts on. -/
abbrev E : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- The closed subspace of `L²(ℝ;ℂ)` functions that vanish almost everywhere on a set `S`. It is a
closed submodule: closedness comes from the fact that `L²` convergence has an almost-everywhere
convergent subsequence, and an a.e.-limit of functions vanishing a.e. on `S` again vanishes a.e.
on `S`. -/
def zeroOnLp (S : Set ℝ) : Submodule ℂ E where
  carrier := {f : E | (⇑f : ℝ → ℂ) =ᵐ[volume.restrict S] 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add f g), hf, hg] with x hx h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [hx, Pi.add_apply, h1, h2, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    exact ae_restrict_of_ae (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ))
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq] at hf ⊢
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c f), hf] with x hx h1
    simp only [Pi.zero_apply] at h1 ⊢
    rw [hx, Pi.smul_apply, h1, smul_zero]

theorem zeroOnLp_isClosed (S : Set ℝ) : IsClosed (zeroOnLp S : Set E) := by
  apply IsSeqClosed.isClosed
  intro f g hf hf_lim
  -- `hf n : ⇑(f n) =ᵐ[volume.restrict S] 0`, `hf_lim : Tendsto f atTop (𝓝 g)` in `L²`.
  have hmeas : TendstoInMeasure volume (fun n => (f n : E)) Filter.atTop g :=
    tendstoInMeasure_of_tendsto_Lp hf_lim
  obtain ⟨ns, _, hae⟩ := hmeas.exists_seq_tendsto_ae
  -- Membership of `g`: it vanishes a.e. on `S`.
  change (⇑g : ℝ → ℂ) =ᵐ[volume.restrict S] 0
  have hae' : ∀ᵐ x ∂(volume.restrict S),
      Filter.Tendsto (fun i => (f (ns i) : ℝ → ℂ) x) Filter.atTop (nhds ((g : ℝ → ℂ) x)) :=
    ae_restrict_of_ae hae
  have hz : ∀ᵐ x ∂(volume.restrict S), ∀ i, (f (ns i) : ℝ → ℂ) x = 0 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hf (ns i)] with x hx using by simpa using hx
  filter_upwards [hae', hz] with x hx hxz
  have hconst : Filter.Tendsto (fun i => (f (ns i) : ℝ → ℂ) x) Filter.atTop (nhds 0) := by
    simp only [hxz]
    exact tendsto_const_nhds
  simpa using tendsto_nhds_unique hx hconst

instance instCompleteSpaceZeroOnLp (S : Set ℝ) : CompleteSpace (zeroOnLp S) :=
  (zeroOnLp_isClosed S).completeSpace_coe

/-- Time-limited subspace: `L²` functions a.e.-supported in `[0,T]` (i.e. vanishing a.e. outside
`[0,T]`). Closed. -/
def timeLimitSubspace (T : ℝ) : Submodule ℂ E :=
  zeroOnLp {t : ℝ | t < 0 ∨ T < t}

instance instCompleteSpaceTimeLimit (T : ℝ) : CompleteSpace (timeLimitSubspace T) :=
  instCompleteSpaceZeroOnLp _

/-- Band-limited subspace: `L²` functions whose L²-Fourier transform is a.e.-supported in `[-W,W]`
(i.e. vanishes a.e. on `{ξ | W < |ξ|}`). Closed, as the preimage of the closed subspace
`zeroOnLp {ξ | W < |ξ|}` under the continuous Plancherel isometry. -/
noncomputable def bandLimitSubspace (W : ℝ) : Submodule ℂ E :=
  (zeroOnLp {ξ : ℝ | W < |ξ|}).comap
    (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap

theorem bandLimitSubspace_isClosed (W : ℝ) : IsClosed (bandLimitSubspace W : Set E) := by
  rw [bandLimitSubspace, Submodule.comap_coe]
  exact (zeroOnLp_isClosed _).preimage (Lp.fourierTransformₗᵢ ℝ ℂ).continuous

instance instCompleteSpaceBandLimit (W : ℝ) : CompleteSpace (bandLimitSubspace W) :=
  (bandLimitSubspace_isClosed W).completeSpace_coe

/-- The time-and-band limiting operator `A = P_W ∘ Q_T ∘ P_W`. -/
noncomputable def timeBandLimitingOp (T W : ℝ) : E →L[ℂ] E :=
  (bandLimitSubspace W).starProjection ∘L
    (timeLimitSubspace T).starProjection ∘L (bandLimitSubspace W).starProjection

/-- The time-and-band limiting operator is self-adjoint. -/
theorem timeBandLimitingOp_isSelfAdjoint (T W : ℝ) :
    IsSelfAdjoint (timeBandLimitingOp T W) :=
  (isSelfAdjoint_starProjection (timeLimitSubspace T)).conj_starProjection (bandLimitSubspace W)

/-- The time-and-band limiting operator is a positive operator. -/
theorem timeBandLimitingOp_isPositive (T W : ℝ) :
    (timeBandLimitingOp T W).IsPositive := by
  have hQ : (timeLimitSubspace T).starProjection.IsPositive :=
    ContinuousLinearMap.IsPositive.of_isStarProjection isStarProjection_starProjection
  have h := hQ.conj_adjoint (bandLimitSubspace W).starProjection
  rwa [(isSelfAdjoint_starProjection (bandLimitSubspace W)).adjoint_eq] at h

/-- The time-and-band limiting operator is a contraction: `‖A‖ ≤ 1`. -/
theorem timeBandLimitingOp_norm_le_one (T W : ℝ) :
    ‖timeBandLimitingOp T W‖ ≤ 1 := by
  have hP : ‖(bandLimitSubspace W).starProjection‖ ≤ 1 :=
    Submodule.starProjection_norm_le (bandLimitSubspace W)
  have hQ : ‖(timeLimitSubspace T).starProjection‖ ≤ 1 :=
    Submodule.starProjection_norm_le (timeLimitSubspace T)
  have hQP : ‖(timeLimitSubspace T).starProjection ∘L (bandLimitSubspace W).starProjection‖
      ≤ ‖(timeLimitSubspace T).starProjection‖ * ‖(bandLimitSubspace W).starProjection‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc ‖timeBandLimitingOp T W‖
      ≤ ‖(bandLimitSubspace W).starProjection‖ *
          ‖(timeLimitSubspace T).starProjection ∘L (bandLimitSubspace W).starProjection‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
        gcongr
        exact hQP.trans (by gcongr)
    _ = 1 := by norm_num

/-!
## Compactness (Leg B)

Compactness of `A = P_W ∘ Q_T ∘ P_W` is reduced to compactness of the *sinc integral operator*
`C = Q_T ∘ P_W`. Since `A = P_W ∘ C` (the definition, reassociated) and `P_W` is bounded,
`A` is compact as soon as `C` is (`IsCompactOperator.clm_comp`). The operator `C` is
Hilbert–Schmidt: its integral kernel

    `sincConvKernel T W t s = 𝟙_[0,T](t) · 2W · sincN(2W(t − s))`

lies in `L²(ℝ × ℝ)` (the `t`-indicator confines the mass to `[0,T]`, and Plancherel of the ideal
low-pass gives `∫_ℝ (2W sincN(2W u))² du = 2W`, so `‖k‖₂² = 2WT < ∞`), and an `L²` kernel yields a
compact operator because the kernels with compact operator form a closed submodule containing the
rectangle indicators, which generate `L²(ℝ × ℝ)`. The genuinely analytic content lives in four
leaves:

* `timeLimitProj_apply_ae` — `Q_T` acts as multiplication by `𝟙_[0,T]` (proven, as the instance
  `S = [0,T]ᶜ` of `zeroOnLp_starProjection_apply_ae`);
* `bandLimitProj_apply_ae` — `P_W` acts as convolution with `2W sincN(2W·)` (the
  abstract-projection ↔ concrete-sinc bridge, proven). Its abstract half is
  `fourier_bandLimitProj_apply_ae`, which identifies `P_W` as the Fourier multiplier by `𝟙_[-W,W]`
  via `starProjection_comap_linearIsometryEquiv` (the `comap` form of Mathlib's
  `LinearIsometry.map_starProjection`); the concrete evaluation of `𝓕⁻¹` then goes through the
  `L¹ ∩ L²` Fourier agreement bridge `ShannonHartley.l2FourierInv_eq_fourierIntegralInv`, applied to
  the spectral cutoff `bandLimitSpec W f = 𝟙_[-W,W]·𝓕f` (integrable because the band is bounded);
* `sincConvKernel_memLp` — the kernel is `L²` on `ℝ × ℝ` (proven);
* `l2KernelOperator_isCompact` — a generic `L²`-kernel operator is compact (proven; the reusable
  Hilbert–Schmidt build, `l2KernelOp` and friends).

The remaining declarations (`timeBandLimitingComp_apply_ae`,
`timeBandLimitingComp_isCompact`, `timeBandLimitingOp_isCompact`) are genuine reductions that
compose the four leaves, so the headline `timeBandLimitingOp_isCompact` is unconditional.

Note the sign asymmetry: the kernel representation needs `0 ≤ W` (`sincN` is even, so a negative `W`
flips the sign of the kernel while `P_W` collapses to `0`), but the compactness headlines hold for
every real `W`, the degenerate band being handled separately via `bandLimitSubspace_eq_bot_of_neg`.
-/

/-- The Hilbert–Schmidt kernel of the sinc integral operator `C = Q_T ∘ P_W`:
`𝟙_[0,T](t) · 2W · sincN(2W(t − s))`. The `t`-indicator encodes the time-limiting `Q_T`; the
`2W sincN(2W·)` factor is the ideal low-pass whose Fourier transform is `𝟙_[-W,W]`, i.e. the
convolution kernel of the band-limiting `P_W`. -/
noncomputable def sincConvKernel (T W : ℝ) (t s : ℝ) : ℂ :=
  (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) t *
    ((2 * W * NormalizedSinc.sincN (2 * W * (t - s)) : ℝ) : ℂ)

/-- The sinc integral operator `C = Q_T ∘ P_W` (band-limit, then time-limit). `A = P_W ∘ C`. -/
noncomputable def timeBandLimitingComp (T W : ℝ) : E →L[ℂ] E :=
  (timeLimitSubspace T).starProjection ∘L (bandLimitSubspace W).starProjection

theorem timeBandLimitingOp_eq_bandProj_comp (T W : ℝ) :
    timeBandLimitingOp T W =
      (bandLimitSubspace W).starProjection ∘L timeBandLimitingComp T W := rfl

/-- The orthogonal projection onto `zeroOnLp S` acts, a.e., as multiplication by the indicator of
`Sᶜ`. Proven via the uniqueness of the orthogonal projection: the candidate `𝟙_{Sᶜ}·g` lies in the
subspace, and the residual `𝟙_S·g` is orthogonal to it. Both Leaf 1 (`S = [0,T]ᶜ`, the time-limiting
`Q_T`) and Leaf 2's frequency-side multiplier (`S = {|ξ| > W}`, giving `𝟙_[-W,W]·𝓕f`) are instances,
so the projection-uniqueness argument is written once here.
@audit:ok -/
theorem zeroOnLp_starProjection_apply_ae {S : Set ℝ} (hS : MeasurableSet S) (g : E) :
    ((zeroOnLp S).starProjection g : ℝ → ℂ) =ᵐ[volume]
      Sᶜ.indicator (fun _ => (1 : ℂ)) * (g : ℝ → ℂ) := by
  -- Candidate projection `P = 𝟙_{Sᶜ} · g` as an `Lp` element.
  have hmem : MemLp (Sᶜ.indicator (g : ℝ → ℂ)) 2 volume := (Lp.memLp g).indicator hS.compl
  set P : E := hmem.toLp _ with hP
  have hP_ae : (P : ℝ → ℂ) =ᵐ[volume] Sᶜ.indicator (g : ℝ → ℂ) := hmem.coeFn_toLp
  have hind : Sᶜ.indicator (fun _ => (1 : ℂ)) * (g : ℝ → ℂ) = Sᶜ.indicator (g : ℝ → ℂ) := by
    funext x
    by_cases hx : x ∈ Sᶜ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hind]
  suffices hproj : (zeroOnLp S).starProjection g = P by rw [hproj]; exact hP_ae
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · -- `P ∈ zeroOnLp S`: `⇑P =ᵐ 0` on `S`.
    show (P : ℝ → ℂ) =ᵐ[volume.restrict S] 0
    refine (ae_restrict_iff' hS).mpr ?_
    filter_upwards [hP_ae] with x hx hxS
    rw [Pi.zero_apply, hx, Set.indicator_of_notMem (by simpa using hxS)]
  · -- Orthogonality: `⟪g - P, w⟫ = 0` for every `w` in the subspace.
    intro w hw
    have hw' : (w : ℝ → ℂ) =ᵐ[volume.restrict S] 0 := hw
    have hwS : ∀ᵐ x ∂volume, x ∈ S → (w : ℝ → ℂ) x = (0 : ℝ → ℂ) x :=
      (ae_restrict_iff' hS).mp hw'
    rw [MeasureTheory.L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_sub g P, hP_ae, hwS] with x hsub hpx hwx
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ S
    · have hwx0 : (w : ℝ → ℂ) x = 0 := by simpa using hwx hx
      rw [hwx0, inner_zero_right]
    · have hgP : (g - P : E) x = 0 := by
        rw [hsub]; simp only [Pi.sub_apply]
        rw [hpx, Set.indicator_of_mem (by simpa using hx), sub_self]
      rw [hgP, inner_zero_left]

/-- **Leaf 1** (`Q_T` = multiplication by `𝟙_[0,T]`). The orthogonal projection onto the
time-limited subspace acts, a.e., as multiplication by the indicator of `[0,T]`. The instance
`S = [0,T]ᶜ` of `zeroOnLp_starProjection_apply_ae`.
@audit:ok -/
theorem timeLimitProj_apply_ae (T : ℝ) (g : E) :
    ((timeLimitSubspace T).starProjection g : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) * (g : ℝ → ℂ) := by
  have hScompl : {t : ℝ | t < 0 ∨ T < t} = (Set.Icc (0 : ℝ) T)ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
    constructor
    · rintro (h | h)
      · intro h0; exact absurd h0 (not_le.mpr h)
      · intro _; exact h
    · intro h
      rcases lt_or_ge x 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h h0)
  have hSmeas : MeasurableSet {t : ℝ | t < 0 ∨ T < t} := by
    rw [hScompl]; exact measurableSet_Icc.compl
  have h := zeroOnLp_starProjection_apply_ae (S := {t : ℝ | t < 0 ∨ T < t}) hSmeas g
  have hc : ({t : ℝ | t < 0 ∨ T < t})ᶜ = Set.Icc (0 : ℝ) T := by rw [hScompl, compl_compl]
  rw [hc] at h
  exact h

/-- Conjugating an orthogonal projection by a surjective linear isometry: the projection onto a
`comap`ped subspace is the projection onto the subspace, conjugated. Mathlib has the `map` form
(`LinearIsometry.map_starProjection`); this is the `comap` form, which is what a Fourier-multiplier
subspace such as `bandLimitSubspace` is literally defined by.
@audit:ok -/
theorem starProjection_comap_linearIsometryEquiv {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    (L : X ≃ₗᵢ[𝕜] Y) (U : Submodule 𝕜 Y) [U.HasOrthogonalProjection]
    [(U.comap (L.toLinearEquiv : X →ₗ[𝕜] Y)).HasOrthogonalProjection] (x : X) :
    (U.comap (L.toLinearEquiv : X →ₗ[𝕜] Y)).starProjection x
      = L.symm (U.starProjection (L x)) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · -- `L.symm (P_U (L x)) ∈ U.comap L`, since `L (L.symm y) = y ∈ U`.
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
    exact Submodule.coe_mem _
  · -- Orthogonality transports through `L`, which preserves inner products.
    intro w hw
    have hLw : L w ∈ U := hw
    have hinner := L.inner_map_map (x - L.symm (U.starProjection (L x))) w
    rw [← hinner, map_sub, LinearIsometryEquiv.apply_symm_apply]
    exact Submodule.starProjection_inner_eq_zero (L x) (L w) hLw

instance instHasOrthogonalProjectionBandLimitComap (W : ℝ) :
    (Submodule.comap ((Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap : E →ₗ[ℂ] E)
      (zeroOnLp {ξ : ℝ | W < |ξ|})).HasOrthogonalProjection :=
  inferInstanceAs (bandLimitSubspace W).HasOrthogonalProjection

/-- The band-limiting projection is the Fourier multiplier by `𝟙_[-W,W]`: conjugate the projection
onto `zeroOnLp {ξ | W < |ξ|}` by the Plancherel isometry. Immediate from
`starProjection_comap_linearIsometryEquiv` and the definition of `bandLimitSubspace`.
@audit:ok -/
theorem bandLimitProj_eq_fourier_conj (W : ℝ) (f : E) :
    (bandLimitSubspace W).starProjection f
      = (Lp.fourierTransformₗᵢ ℝ ℂ).symm
          ((zeroOnLp {ξ : ℝ | W < |ξ|}).starProjection (Lp.fourierTransformₗᵢ ℝ ℂ f)) :=
  starProjection_comap_linearIsometryEquiv (Lp.fourierTransformₗᵢ ℝ ℂ) _ f

theorem compl_setOf_lt_abs (W : ℝ) : {ξ : ℝ | W < |ξ|}ᶜ = Set.Icc (-W) W := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Set.mem_Icc]
  exact abs_le

theorem measurableSet_setOf_lt_abs (W : ℝ) : MeasurableSet {ξ : ℝ | W < |ξ|} :=
  measurableSet_lt measurable_const measurable_norm

/-- **The band-limiting projection is the Fourier multiplier by `𝟙_[-W,W]`.** Combining the
conjugation identity `bandLimitProj_eq_fourier_conj` with the projection-uniqueness computation
`zeroOnLp_starProjection_apply_ae` on the frequency side. This is the "half" of Leaf 2 that lives
entirely inside the abstract projection API; the remaining half is the identification of the
multiplier's action with sinc convolution, which needs the Fourier transform to be evaluated
concretely. Note this half needs no sign condition on `W`: for `W < 0` the interval `[-W,W]` is
empty and both sides vanish, so the sign asymmetry of Leaf 2 is localized entirely in the passage
from the multiplier `𝟙_[-W,W]` to the kernel `2W sincN(2W·)`.
@audit:ok -/
theorem fourier_bandLimitProj_apply_ae (W : ℝ) (f : E) :
    ((Lp.fourierTransformₗᵢ ℝ ℂ ((bandLimitSubspace W).starProjection f) : E) : ℝ → ℂ)
      =ᵐ[volume] (Set.Icc (-W) W).indicator (fun _ => (1 : ℂ)) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ f : E) : ℝ → ℂ) := by
  rw [bandLimitProj_eq_fourier_conj, LinearIsometryEquiv.apply_symm_apply]
  have h := zeroOnLp_starProjection_apply_ae (measurableSet_setOf_lt_abs W)
    (Lp.fourierTransformₗᵢ ℝ ℂ f)
  rwa [compl_setOf_lt_abs] at h

/-- For a negative band limit the band-limited subspace degenerates: `{ξ | W < |ξ|}` is everything,
so only the zero function has an a.e.-vanishing Fourier transform. This is a true degeneracy of the
band (`[-W,W] = ∅` for `W < 0`), not an artifact of the definition, and it is what lets the
compactness headlines keep their unrestricted `(T W : ℝ)` signatures.
@audit:ok -/
theorem bandLimitSubspace_eq_bot_of_neg {W : ℝ} (hW : W < 0) : bandLimitSubspace W = ⊥ := by
  have huniv : {ξ : ℝ | W < |ξ|} = Set.univ :=
    Set.eq_univ_of_forall fun ξ => lt_of_lt_of_le hW (abs_nonneg ξ)
  have hzero : zeroOnLp {ξ : ℝ | W < |ξ|} = ⊥ := by
    refine Submodule.eq_bot_iff _ |>.mpr fun g hg => ?_
    have hg' : (g : ℝ → ℂ) =ᵐ[volume.restrict {ξ : ℝ | W < |ξ|}] 0 := hg
    rw [huniv, Measure.restrict_univ] at hg'
    exact (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr hg'
  rw [bandLimitSubspace, hzero, Submodule.comap_bot, LinearMap.ker_eq_bot]
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.injective


/-- The frequency-side content of the band-limiting projection: the spectral cutoff
`𝟙_[-W,W] · 𝓕f`. By `fourier_bandLimitProj_apply_ae` this is a.e. the Fourier transform of
`P_W f`; being an `L²` function cut down to a bounded interval it is moreover integrable, which
is what lets the `L¹ ∩ L²` Fourier bridge evaluate `P_W f` pointwise. -/
noncomputable def bandLimitSpec (W : ℝ) (f : E) : ℝ → ℂ :=
  (Set.Icc (-W) W).indicator (fun _ => (1 : ℂ)) *
    ((Lp.fourierTransformₗᵢ ℝ ℂ f : E) : ℝ → ℂ)

theorem bandLimitSpec_eq_indicator (W : ℝ) (f : E) :
    bandLimitSpec W f
      = (Set.Icc (-W) W).indicator ((Lp.fourierTransformₗᵢ ℝ ℂ f : E) : ℝ → ℂ) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-W) W <;>
    simp [bandLimitSpec, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

theorem bandLimitSpec_memLp_two (W : ℝ) (f : E) : MemLp (bandLimitSpec W f) 2 volume := by
  rw [bandLimitSpec_eq_indicator]
  exact (Lp.memLp _).indicator measurableSet_Icc

theorem bandLimitSpec_memLp_one (W : ℝ) (f : E) : MemLp (bandLimitSpec W f) 1 volume := by
  rw [memLp_one_iff_integrable, bandLimitSpec]
  have hvol : volume (Set.Icc (-W) W) ≠ ∞ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  exact MemLp.integrable_mul
    (memLp_indicator_const 2 measurableSet_Icc (1 : ℂ) (Or.inr hvol)) (Lp.memLp _)

theorem bandLimitProj_coeFn_ae_eq_fourierInv (W : ℝ) (f : E) :
    ((bandLimitSubspace W).starProjection f : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ (bandLimitSpec W f) := by
  set G : E := Lp.fourierTransformₗᵢ ℝ ℂ ((bandLimitSubspace W).starProjection f) with hGdef
  have hG : (G : ℝ → ℂ) =ᵐ[volume] bandLimitSpec W f := fourier_bandLimitProj_apply_ae W f
  have hGeq : G = (bandLimitSpec_memLp_two W f).toLp (bandLimitSpec W f) := by
    have h := MemLp.toLp_congr (Lp.memLp G) (bandLimitSpec_memLp_two W f) hG
    rwa [Lp.toLp_coeFn] at h
  have hproj : (bandLimitSubspace W).starProjection f = (Lp.fourierTransformₗᵢ ℝ ℂ).symm G := by
    rw [hGdef, LinearIsometryEquiv.symm_apply_apply]
  rw [hproj, hGeq]
  exact ShannonHartley.l2FourierInv_eq_fourierIntegralInv (bandLimitSpec W f)
    (bandLimitSpec_memLp_one W f) (bandLimitSpec_memLp_two W f)

theorem inner_two_mul_specBoxcar_apply (W t ξ : ℝ) (hW : 0 < W) (z : ℂ) :
    inner ℂ ((2 * (W : ℂ)) * ShannonHartley.specBoxcar t (1 / (2 * W)) ξ) z
      = Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I) *
          ((Set.Icc (-W) W).indicator (fun _ => (1 : ℂ)) ξ * z) := by
  have hW' : (W : ℝ) ≠ 0 := ne_of_gt hW
  have hhalf : 1 / (2 * (1 / (2 * W))) = W := by field_simp
  rw [ShannonHartley.specBoxcar, hhalf]
  by_cases hξ : ξ ∈ Set.Icc (-W) W
  · have hWC : (W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hW'
    have hbox : (2 * (W : ℂ)) *
        ((Set.Icc (-W) W).indicator
          (fun ζ : ℝ => (((1 / (2 * W) : ℝ)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * t * ζ) : ℝ) * Complex.I)) ξ)
        = Complex.exp ((-(2 * Real.pi * t * ξ) : ℝ) * Complex.I) := by
      rw [Set.indicator_of_mem hξ, ← mul_assoc]
      have h : (((1 / (2 * W) : ℝ)) : ℂ) = 1 / (2 * (W : ℂ)) := by push_cast; ring
      rw [h]
      field_simp
    have hexp : ((-(2 * Real.pi * t * ξ) : ℝ) : ℂ) * (-Complex.I)
        = ((2 * Real.pi * (ξ * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hbox, Set.indicator_of_mem hξ, RCLike.inner_apply, ← Complex.exp_conj,
      map_mul, Complex.conj_I, Complex.conj_ofReal, hexp]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, mul_zero, inner_zero_left,
      zero_mul, mul_zero]

theorem fourierInv_bandLimitSpec_eq (W : ℝ) (hW : 0 < W) (f : E) (t : ℝ) :
    𝓕⁻ (bandLimitSpec W f) t
      = ∫ s, ((2 * W * NormalizedSinc.sincN (2 * W * (t - s)) : ℝ) : ℂ) *
          (f : ℝ → ℂ) s ∂volume := by
  have hΔ : (0:ℝ) < 1 / (2 * W) := by positivity
  -- `S` = the shifted/dilated sinc, `B = 𝓕 S` = the spectral boxcar at `t`.
  set S : E := (ShannonHartley.shiftSinc_memLp t (1 / (2 * W)) hΔ).toLp
    (fun s => (NormalizedSinc.sincN ((s - t) / (1 / (2 * W))) : ℂ)) with hSdef
  set B : E := (ShannonHartley.specBoxcar_memLp t (1 / (2 * W)) hΔ 2).toLp
    (ShannonHartley.specBoxcar t (1 / (2 * W))) with hBdef
  have hFS : Lp.fourierTransformₗᵢ ℝ ℂ S = B :=
    ShannonHartley.fourier_shiftSinc_toLp t (1 / (2 * W)) hΔ
  -- Step A: the inverse transform at `t` is the pairing of `𝓕 f` against `2W · B`.
  have hA : 𝓕⁻ (bandLimitSpec W f) t
      = inner ℂ ((2 * W : ℂ) • B) (Lp.fourierTransformₗᵢ ℝ ℂ f) := by
    rw [MeasureTheory.L2.inner_def, Real.fourierInv_eq']
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (2 * W : ℂ) B,
      (ShannonHartley.specBoxcar_memLp t (1 / (2 * W)) hΔ 2).coeFn_toLp] with ξ hsmul hB
    rw [hsmul, Pi.smul_apply, hB]
    simp only [smul_eq_mul]
    rw [inner_two_mul_specBoxcar_apply W t ξ hW, bandLimitSpec, Pi.mul_apply]
    congr 2
    simp [RCLike.inner_apply]
    ring
  -- Step B: Plancherel moves the pairing to the time side, where `S` is an explicit sinc.
  have hB' : inner ℂ ((2 * W : ℂ) • B) (Lp.fourierTransformₗᵢ ℝ ℂ f)
      = (2 * W : ℂ) * inner ℂ S f := by
    rw [← hFS, inner_smul_left, (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map]
    congr 1
    rw [map_mul, Complex.conj_ofReal, map_ofNat]
  rw [hA, hB', MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(ShannonHartley.shiftSinc_memLp t (1 / (2 * W)) hΔ).coeFn_toLp] with s hs
  rw [hSdef]
  rw [hs, RCLike.inner_apply, Complex.conj_ofReal]
  -- `(s - t)/Δ = 2W(s - t)`, and `sincN` is even.
  rw [show (s - t) / (1 / (2 * W)) = -(2 * W * (t - s)) by field_simp; ring,
    NormalizedSinc.sincN_neg]
  push_cast
  ring

/-- **Leaf 2** (`P_W` = convolution with `2W sincN(2W·)`). The orthogonal projection onto the
band-limited subspace acts, a.e., as convolution with the ideal low-pass `2W sincN(2W·)` (whose
Fourier transform is `𝟙_[-W,W]`). This is the abstract `starProjection`-of-a-`comap`-under-`𝓕` ↔
concrete sinc-convolution identity, and it is what turns the operator `C = Q_T ∘ P_W` into an
integral operator with the Hilbert–Schmidt kernel `sincConvKernel`.

The sign precondition `0 ≤ W` is necessary, not cosmetic: `sincN` is even, so for `W < 0` the stated
kernel `2W sincN(2W·)` is *minus* the ideal low-pass at `|W|`, while the left-hand side collapses to
`0` (`bandLimitSubspace_eq_bot_of_neg`). Concretely at `W = -1`, `f = 𝟙_[0,1]`, `t = 1/2` the
right-hand side is `-∫_(-1)^(1) sincN ≈ -1.179 ≠ 0`, so the unrestricted statement is false; `0 ≤ W`
is a precondition on the parameter, not a hypothesis carrying the proof.

The proof factors through the spectral cutoff `bandLimitSpec W f = 𝟙_[-W,W]·𝓕f`: the abstract half
`fourier_bandLimitProj_apply_ae` identifies `𝓕(P_W f)` with it, and since it is supported in a
bounded interval it lies in `L¹ ∩ L²`, so the Fourier bridge
`ShannonHartley.l2FourierInv_eq_fourierIntegralInv` evaluates `P_W f = 𝓕⁻¹(bandLimitSpec W f)`
pointwise as an honest integral (`bandLimitProj_coeFn_ae_eq_fourierInv`). That integral is then
identified with the sinc convolution by Plancherel against the spectral boxcar, whose inverse
transform is already known to be a shifted sinc (`ShannonHartley.fourier_shiftSinc_toLp`).
The degenerate `W = 0` band is a null set, where both sides vanish.
@audit:ok -/
theorem bandLimitProj_apply_ae (W : ℝ) (hW : 0 ≤ W) (f : E) :
    ((bandLimitSubspace W).starProjection f : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ s, ((2 * W * NormalizedSinc.sincN (2 * W * (t - s)) : ℝ) : ℂ) *
        (f : ℝ → ℂ) s ∂volume := by
  rcases eq_or_lt_of_le hW with hW0 | hWpos
  · -- `W = 0`: the band `[-0,0] = {0}` is a null set, so both sides vanish.
    subst hW0
    have hnull : volume (Set.Icc (-(0:ℝ)) 0) = 0 := by simp
    have hspec : bandLimitSpec 0 f =ᵐ[volume] 0 := by
      rw [bandLimitSpec_eq_indicator]
      filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
      rw [Set.indicator_of_notMem hx]
      rfl
    have hzero : ∀ t : ℝ, 𝓕⁻ (bandLimitSpec 0 f) t = 0 := by
      intro t
      rw [Real.fourierInv_eq']
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hspec] with v hv
      rw [hv, Pi.zero_apply, smul_zero]
    filter_upwards [bandLimitProj_coeFn_ae_eq_fourierInv 0 f] with t ht
    rw [ht, hzero t]
    simp
  · filter_upwards [bandLimitProj_coeFn_ae_eq_fourierInv W f] with t ht
    rw [ht, fourierInv_bandLimitSpec_eq W hWpos f t]

/-- The normalized sinc is square-integrable on `ℝ`. The reusable crux for the kernel-`L²` bound:
its Lebesgue `L²`-membership follows from the elementary majorant `sincN(x)² ≤ 2/(1 + x²)`
(`|sincN| ≤ 1` near `0`, `sincN(x)² = sin²(πx)/(πx)² ≤ 1/(πx)²` away from it) against the
integrable `2/(1 + x²)`. Mathlib's `Real.integrable_sinc` is finite-measure-only, so the Lebesgue
`L²` fact is built here.
@audit:ok -/
theorem sincN_memLp_two :
    MemLp (fun x : ℝ => (NormalizedSinc.sincN x : ℂ)) 2 volume := by
  have hcont : Continuous (fun x : ℝ => (NormalizedSinc.sincN x : ℂ)) :=
    Complex.continuous_ofReal.comp NormalizedSinc.continuous_sincN
  -- Pointwise majorant `sincN x ^ 2 ≤ 2 / (1 + x ^ 2)`.
  have hpt : ∀ x : ℝ, NormalizedSinc.sincN x ^ 2 ≤ 2 / (1 + x ^ 2) := by
    intro x
    have hden : (0 : ℝ) < 1 + x ^ 2 := by positivity
    rcases le_total (x ^ 2) 1 with hx1 | hx1
    · have hs1 : NormalizedSinc.sincN x ^ 2 ≤ 1 := by
        nlinarith [NormalizedSinc.neg_one_le_sincN x, NormalizedSinc.sincN_le_one x]
      rw [le_div_iff₀ hden]; nlinarith [hs1, hx1]
    · have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
      have hπx : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx0
      have hpx2 : (0 : ℝ) < (Real.pi * x) ^ 2 := by rw [sq]; exact mul_self_pos.mpr hπx
      have hsc : NormalizedSinc.sincN x = Real.sin (Real.pi * x) / (Real.pi * x) :=
        NormalizedSinc.sincN_of_ne_zero x hx0
      have hsin2 : Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin (Real.pi * x), Real.sin_le_one (Real.pi * x)]
      have hsq : NormalizedSinc.sincN x ^ 2 ≤ 1 / (Real.pi * x) ^ 2 := by
        rw [hsc, div_pow]; gcongr
      have hπ2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
      refine hsq.trans ?_
      rw [le_div_iff₀ hden, div_mul_eq_mul_div, one_mul, div_le_iff₀ hpx2]
      nlinarith [hπ2, hx1, sq_nonneg x]
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hg : Integrable (fun x : ℝ => 2 / (1 + x ^ 2)) volume := by
    simp_rw [div_eq_mul_inv]
    exact integrable_inv_one_add_sq.const_mul 2
  refine hg.mono' ((continuous_norm.comp hcont).pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  have hnn : (0 : ℝ) ≤ ‖(NormalizedSinc.sincN x : ℂ)‖ ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg hnn, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact hpt x

/-- **Leaf 3** (the kernel is `L²`). `sincConvKernel` is square-integrable on `ℝ × ℝ`: the
`t`-indicator confines the mass to `[0,T]` and the inner mass `∫_ℝ (2W sincN(2W(t−s)))² ds` is a
finite constant `C` (independent of `t`, by translation invariance of Lebesgue measure), so
`‖k‖₂² ≤ C · vol[0,T] < ∞`. The finite `L²` mass of the ideal low-pass `2W sincN(2W·)` is obtained by
rescaling the 1-D crux `sincN ∈ L²` (`sincN_memLp_two`) through `integrable_comp_mul_left_iff`, and
the 2-D lift is a Tonelli (`lintegral_prod_le`) + `lintegral_sub_left_eq_self` computation.
Hypothesis-free in `T` and `W`: the degenerate `T < 0` (empty `[0,T]`, zero mass) and `2W = 0`
(zero kernel) cases are both genuinely covered.
@audit:ok -/
theorem sincConvKernel_memLp (T W : ℝ) :
    MemLp (fun p : ℝ × ℝ => sincConvKernel T W p.1 p.2) 2 (volume.prod volume) := by
  -- The ideal low-pass factor `2W sincN(2W·)`, as a one-variable function.
  set g : ℝ → ℂ := fun u => ((2 * W * NormalizedSinc.sincN (2 * W * u) : ℝ) : ℂ) with hg_def
  have hg_cont : Continuous g := by
    rw [hg_def]; exact Complex.continuous_ofReal.comp (by fun_prop)
  have hg_aesm : AEStronglyMeasurable g volume := hg_cont.aestronglyMeasurable
  -- `sincN` is square-integrable (the 1-D crux, `sincN_memLp_two`).
  have hsincN_sq_int : Integrable (fun x : ℝ => NormalizedSinc.sincN x ^ 2) volume := by
    have h := (memLp_two_iff_integrable_sq_norm
      (Complex.continuous_ofReal.comp NormalizedSinc.continuous_sincN).aestronglyMeasurable).mp
      sincN_memLp_two
    refine h.congr ?_
    filter_upwards with x
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- `g ∈ L²(ℝ)`: rescale `sincN ∈ L²` by the sample rate `2W` (Plancherel of the ideal low-pass).
  have hg_memLp : MemLp g 2 volume := by
    rcases eq_or_ne (2 * W) 0 with h2W | h2W
    · have hz : g = (fun _ => (0 : ℂ)) := by
        funext u; simp only [hg_def]; rw [h2W]; simp
      rw [hz]; exact MemLp.zero'
    · rw [memLp_two_iff_integrable_sq_norm hg_aesm]
      have hφ : Integrable (fun x : ℝ => (2 * W * NormalizedSinc.sincN x) ^ 2) volume := by
        have hpow : (fun x : ℝ => (2 * W * NormalizedSinc.sincN x) ^ 2)
            = (fun x : ℝ => (2 * W) ^ 2 * NormalizedSinc.sincN x ^ 2) := by
          funext x; rw [mul_pow]
        rw [hpow]; exact hsincN_sq_int.const_mul _
      have hcomp :=
        (integrable_comp_mul_left_iff
          (fun x : ℝ => (2 * W * NormalizedSinc.sincN x) ^ 2) h2W).mpr hφ
      refine hcomp.congr ?_
      filter_upwards with u
      simp only [hg_def, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- The finite inner `L²` mass `C = ∫⁻ ‖g s‖ₑ² ds`.
  have hC_lt : (∫⁻ s, ‖g s‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume) < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hg_memLp.2
  set C : ℝ≥0∞ := ∫⁻ s, ‖g s‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume with hC_def
  -- The product kernel is a.e.-strongly-measurable.
  have hk_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => sincConvKernel T W p.1 p.2)
      (volume.prod volume) := by
    simp only [sincConvKernel]
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((measurable_const.indicator measurableSet_Icc).comp
        measurable_fst).aestronglyMeasurable
    · exact (Complex.continuous_ofReal.comp (by fun_prop :
        Continuous (fun p : ℝ × ℝ =>
          2 * W * NormalizedSinc.sincN (2 * W * (p.1 - p.2))))).aestronglyMeasurable
  refine ⟨hk_meas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  -- Per-`t` inner integral: `∫⁻ s, ‖k t s‖ₑ² ds = 𝟙_[0,T](t) · C`.
  have hinner : ∀ t : ℝ,
      (∫⁻ s, ‖sincConvKernel T W t s‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume)
        = (Set.Icc (0 : ℝ) T).indicator (fun _ => C) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem ht]
      have hval : ∀ s, ‖sincConvKernel T W t s‖ₑ ^ (2 : ℝ≥0∞).toReal
          = ‖g (t - s)‖ₑ ^ (2 : ℝ≥0∞).toReal := by
        intro s
        have hks : sincConvKernel T W t s = g (t - s) := by
          simp only [sincConvKernel, Set.indicator_of_mem ht, one_mul, hg_def]
        rw [hks]
      rw [lintegral_congr hval, hC_def]
      exact lintegral_sub_left_eq_self (fun u => ‖g u‖ₑ ^ (2 : ℝ≥0∞).toReal) t
    · rw [Set.indicator_of_notMem ht]
      have hval : ∀ s, ‖sincConvKernel T W t s‖ₑ ^ (2 : ℝ≥0∞).toReal = 0 := by
        intro s
        have hks : sincConvKernel T W t s = 0 := by
          simp only [sincConvKernel, Set.indicator_of_notMem ht, zero_mul]
        rw [hks, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      rw [lintegral_congr hval, lintegral_zero]
  -- Bound the double integral by `C · vol[0,T] < ∞`.
  calc (∫⁻ p : ℝ × ℝ, ‖sincConvKernel T W p.1 p.2‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(volume.prod volume))
      ≤ ∫⁻ t, ∫⁻ s, ‖sincConvKernel T W t s‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume ∂volume :=
        lintegral_prod_le _
    _ = ∫⁻ t, (Set.Icc (0 : ℝ) T).indicator (fun _ => C) t ∂volume := lintegral_congr hinner
    _ = ∫⁻ _ in Set.Icc (0 : ℝ) T, C ∂volume := lintegral_indicator measurableSet_Icc _
    _ = C * volume (Set.Icc (0 : ℝ) T) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top hC_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-!
### The Hilbert–Schmidt machinery (Leaf 4)

Mathlib has no Hilbert–Schmidt / Schatten API, so the "`L²` kernel ⟹ compact operator" implication
is built here from scratch. The construction is deliberately reusable: `l2KernelOp` is the
*continuous linear* map sending a kernel `κ ∈ L²(ℝ × ℝ)` to the integral operator it induces on
`L²(ℝ)`, with the Hilbert–Schmidt bound `‖l2KernelOp κ‖ ≤ ‖κ‖` built into its construction.

Compactness then follows from a soft argument: `{κ | IsCompactOperator (l2KernelOp κ)}` is a
*closed submodule* of `L²(ℝ × ℝ)` (closed because `l2KernelOp` is continuous and the compact
operators are closed in the operator norm), it contains every rectangle indicator `𝟙_{A×B}` (those
induce rank-one operators), and rectangles generate the product σ-algebra — so a π-λ induction plus
`Lp.induction` push membership to the whole space.
-/

/-- The `L²(ℝ × ℝ; ℂ)` space of Hilbert–Schmidt kernels. -/
abbrev L2Kernel : Type := Lp ℂ 2 ((volume : Measure ℝ).prod (volume : Measure ℝ))

/-- The integral operator attached to a kernel, at the level of raw functions:
`f ↦ (t ↦ ∫ k(t,s) f(s) ds)`. -/
noncomputable def l2KernelApply (κ : L2Kernel) (f : E) : ℝ → ℂ :=
  fun t => ∫ s, (κ : ℝ × ℝ → ℂ) (t, s) * (f : ℝ → ℂ) s ∂volume

theorem l2Kernel_slice_memLp (κ : L2Kernel) :
    ∀ᵐ t ∂(volume : Measure ℝ), MemLp (fun s => (κ : ℝ × ℝ → ℂ) (t, s)) 2 volume := by
  have hsm : AEStronglyMeasurable (κ : ℝ × ℝ → ℂ) (volume.prod volume) := (Lp.memLp κ).1
  have hae := hsm.prodMk_left (ν := (volume : Measure ℝ))
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ‖(κ : ℝ × ℝ → ℂ) p‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (volume.prod volume) := hsm.enorm.pow_const _
  have htop : (∫⁻ p, ‖(κ : ℝ × ℝ → ℂ) p‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(volume.prod volume)) < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).mp
      (Lp.eLpNorm_lt_top κ)
  rw [lintegral_prod _ hmeas] at htop
  have hfin : ∀ᵐ t ∂(volume : Measure ℝ),
      (∫⁻ s, ‖(κ : ℝ × ℝ → ℂ) (t, s)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume) < ∞ :=
    ae_lt_top' hmeas.lintegral_prod_right' htop.ne
  filter_upwards [hae, hfin] with t ht htfin
  exact ⟨ht, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).mpr htfin⟩

theorem l2Kernel_integrable (κ : L2Kernel) (f : E) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      Integrable (fun s => (κ : ℝ × ℝ → ℂ) (t, s) * (f : ℝ → ℂ) s) volume := by
  filter_upwards [l2Kernel_slice_memLp κ] with t ht
  exact ht.integrable_mul (Lp.memLp f)

theorem l2KernelApply_aestronglyMeasurable (κ : L2Kernel) (f : E) :
    AEStronglyMeasurable (l2KernelApply κ f) volume := by
  have h : AEStronglyMeasurable (fun p : ℝ × ℝ => (κ : ℝ × ℝ → ℂ) p * (f : ℝ → ℂ) p.2)
      (volume.prod volume) :=
    (Lp.memLp κ).1.mul
      ((Lp.memLp f).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  exact h.integral_prod_right'

theorem l2KernelApply_eLpNorm_le (κ : L2Kernel) (f : E) :
    eLpNorm (l2KernelApply κ f) 2 volume
      ≤ eLpNorm (κ : ℝ × ℝ → ℂ) 2 (volume.prod volume) * eLpNorm (f : ℝ → ℂ) 2 volume := by
  set D : ℝ≥0∞ := ∫⁻ s, ‖(f : ℝ → ℂ) s‖ₑ ^ (2 : ℝ) ∂volume with hD
  set A : ℝ → ℝ≥0∞ := fun t => ∫⁻ s, ‖(κ : ℝ × ℝ → ℂ) (t, s)‖ₑ ^ (2 : ℝ) ∂volume with hA
  have hfm : AEMeasurable (fun s => ‖(f : ℝ → ℂ) s‖ₑ) volume := (Lp.memLp f).1.enorm
  have hκm : AEMeasurable (fun p : ℝ × ℝ => ‖(κ : ℝ × ℝ → ℂ) p‖ₑ ^ (2 : ℝ))
      (volume.prod volume) := (Lp.memLp κ).1.enorm.pow_const _
  -- Cauchy–Schwarz on each slice: `‖∫ k(t,s) f(s) ds‖ ≤ ‖k(t,·)‖₂ · ‖f‖₂`.
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ),
      ‖l2KernelApply κ f t‖ₑ ^ (2 : ℝ) ≤ A t * D := by
    filter_upwards [(Lp.memLp κ).1.prodMk_left (ν := (volume : Measure ℝ))] with t ht
    have hcs : ‖l2KernelApply κ f t‖ₑ ≤ A t ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) := by
      calc ‖l2KernelApply κ f t‖ₑ
          ≤ ∫⁻ s, ‖(κ : ℝ × ℝ → ℂ) (t, s) * (f : ℝ → ℂ) s‖ₑ ∂volume :=
            enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ s, ((fun u => ‖(κ : ℝ × ℝ → ℂ) (t, u)‖ₑ) * fun u => ‖(f : ℝ → ℂ) u‖ₑ) s ∂volume := by
            simp [enorm_mul]
        _ ≤ A t ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) :=
            ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two ht.enorm hfm
    calc ‖l2KernelApply κ f t‖ₑ ^ (2 : ℝ)
        ≤ (A t ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          exact ENNReal.rpow_le_rpow hcs (by norm_num)
      _ = A t * D := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul]
          norm_num
  -- Tonelli in the outer variable.
  have hswap : (∫⁻ t, A t ∂volume)
      = ∫⁻ p, ‖(κ : ℝ × ℝ → ℂ) p‖ₑ ^ (2 : ℝ) ∂(volume.prod volume) := (lintegral_prod _ hκm).symm
  have hLHS : eLpNorm (l2KernelApply κ f) 2 volume
      = (∫⁻ t, ‖l2KernelApply κ f t‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]; norm_num
  have hK : eLpNorm (κ : ℝ × ℝ → ℂ) 2 (volume.prod volume)
      = (∫⁻ p, ‖(κ : ℝ × ℝ → ℂ) p‖ₑ ^ (2 : ℝ) ∂(volume.prod volume)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]; norm_num
  have hF : eLpNorm (f : ℝ → ℂ) 2 volume = D ^ (1 / 2 : ℝ) := by
    rw [hD, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]; norm_num
  rw [hLHS, hK, hF, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), ← hswap,
    ← lintegral_mul_const'' _ (by
      exact (hκm.lintegral_prod_right' : AEMeasurable A volume))]
  exact ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (by norm_num)

theorem l2KernelApply_memLp (κ : L2Kernel) (f : E) : MemLp (l2KernelApply κ f) 2 volume :=
  ⟨l2KernelApply_aestronglyMeasurable κ f,
    lt_of_le_of_lt (l2KernelApply_eLpNorm_le κ f)
      (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top κ) (Lp.eLpNorm_lt_top f))⟩

/-- The integral operator of a kernel, as a linear map on `L²(ℝ;ℂ)`. -/
noncomputable def l2KernelLin (κ : L2Kernel) : E →ₗ[ℂ] E where
  toFun f := (l2KernelApply_memLp κ f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(l2KernelApply_memLp κ (f + g)).coeFn_toLp,
      Lp.coeFn_add ((l2KernelApply_memLp κ f).toLp (l2KernelApply κ f))
        ((l2KernelApply_memLp κ g).toLp (l2KernelApply κ g)),
      (l2KernelApply_memLp κ f).coeFn_toLp, (l2KernelApply_memLp κ g).coeFn_toLp,
      l2Kernel_integrable κ f, l2Kernel_integrable κ g] with t h1 h2 h3 h4 hi1 hi2
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp only [l2KernelApply]
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with s hs
    rw [hs, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(l2KernelApply_memLp κ (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((l2KernelApply_memLp κ f).toLp (l2KernelApply κ f)),
      (l2KernelApply_memLp κ f).coeFn_toLp] with t h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
    simp only [l2KernelApply]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with s hs
    rw [hs, Pi.smul_apply, smul_eq_mul]
    ring

theorem l2KernelLin_coeFn (κ : L2Kernel) (f : E) :
    ((l2KernelLin κ f : E) : ℝ → ℂ) =ᵐ[volume] l2KernelApply κ f :=
  (l2KernelApply_memLp κ f).coeFn_toLp

/-- The kernel-to-operator map, as a bilinear map. -/
noncomputable def l2KernelBilin : L2Kernel →ₗ[ℂ] (E →ₗ[ℂ] E) where
  toFun := l2KernelLin
  map_add' κ κ' := by
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.add_apply]
    refine Lp.ext ?_
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂(volume : Measure ℝ),
        ((κ + κ' : L2Kernel) : ℝ × ℝ → ℂ) (t, s)
          = (κ : ℝ × ℝ → ℂ) (t, s) + (κ' : ℝ × ℝ → ℂ) (t, s) := by
      have h0 : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
          ((κ + κ' : L2Kernel) : ℝ × ℝ → ℂ) p = (κ : ℝ × ℝ → ℂ) p + (κ' : ℝ × ℝ → ℂ) p := by
        filter_upwards [Lp.coeFn_add κ κ'] with p hp using by simpa using hp
      exact Measure.ae_ae_of_ae_prod h0
    filter_upwards [l2KernelLin_coeFn (κ + κ') f,
      Lp.coeFn_add (l2KernelLin κ f) (l2KernelLin κ' f),
      l2KernelLin_coeFn κ f, l2KernelLin_coeFn κ' f,
      l2Kernel_integrable κ f, l2Kernel_integrable κ' f, hae] with t h1 h2 h3 h4 hi1 hi2 hs
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp only [l2KernelApply]
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [hs] with s hsv
    rw [hsv, add_mul]
  map_smul' c κ := by
    refine LinearMap.ext fun f => ?_
    rw [RingHom.id_apply, LinearMap.smul_apply]
    refine Lp.ext ?_
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂(volume : Measure ℝ),
        ((c • κ : L2Kernel) : ℝ × ℝ → ℂ) (t, s) = c * (κ : ℝ × ℝ → ℂ) (t, s) := by
      have h0 : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
          ((c • κ : L2Kernel) : ℝ × ℝ → ℂ) p = c * (κ : ℝ × ℝ → ℂ) p := by
        filter_upwards [Lp.coeFn_smul c κ] with p hp using by simpa using hp
      exact Measure.ae_ae_of_ae_prod h0
    filter_upwards [l2KernelLin_coeFn (c • κ) f, Lp.coeFn_smul c (l2KernelLin κ f),
      l2KernelLin_coeFn κ f, hae] with t h1 h2 h3 hs
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
    simp only [l2KernelApply]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hs] with s hsv
    rw [hsv]
    ring

/-- The kernel-to-operator map `κ ↦ (f ↦ ∫ κ(·,s) f(s) ds)`, as a continuous linear map. Its
continuity is exactly the Hilbert–Schmidt bound `‖l2KernelOp κ‖ ≤ ‖κ‖`.
@audit:ok -/
noncomputable def l2KernelOp : L2Kernel →L[ℂ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous₂ l2KernelBilin 1 (by
    intro κ f
    rw [one_mul]
    calc ‖l2KernelBilin κ f‖
        = (eLpNorm (l2KernelApply κ f) 2 volume).toReal :=
          Lp.norm_toLp _ (l2KernelApply_memLp κ f)
      _ ≤ (eLpNorm (κ : ℝ × ℝ → ℂ) 2 (volume.prod volume)
            * eLpNorm (f : ℝ → ℂ) 2 volume).toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top κ) (Lp.eLpNorm_lt_top f)).ne
            (l2KernelApply_eLpNorm_le κ f)
      _ = ‖κ‖ * ‖f‖ := by rw [ENNReal.toReal_mul, Lp.norm_def, Lp.norm_def])

theorem l2KernelOp_apply_ae (κ : L2Kernel) (f : E) :
    (l2KernelOp κ f : ℝ → ℂ) =ᵐ[volume] l2KernelApply κ f :=
  l2KernelLin_coeFn κ f

/-- A rectangle kernel `c · 𝟙_{A×B}` induces a rank-one operator, hence a compact one. The
degenerate branch (`vol A * vol B = 0`, which by `0 * ∞ = 0` in `ℝ≥0∞` also covers a null side
paired with an infinite one) is not an escape: `Measure.prod_prod` makes the rectangle genuinely
product-null, so the kernel is the zero element of `L²(ℝ × ℝ)` and the induced operator really is
`0`.
@audit:ok -/
theorem l2KernelOp_indicator_prod_isCompact {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : (volume.prod volume) (A ×ˢ B) ≠ ∞) (c : ℂ) :
    IsCompactOperator (l2KernelOp (indicatorConstLp 2 (hA.prod hB) hAB c)) := by
  rcases eq_or_ne ((volume : Measure ℝ) A * volume B) 0 with h0 | hne0
  · -- Degenerate rectangle: the kernel is the zero element of `L²(ℝ × ℝ)`.
    have hzero : (indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) = 0 := by
      refine Lp.ext (indicatorConstLp_coeFn.trans ?_)
      refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℂ 2 _).symm
      exact indicator_meas_zero (by rw [Measure.prod_prod]; exact h0)
    rw [hzero, map_zero]
    exact isCompactOperator_zero
  · have hABm : (volume : Measure ℝ) A * volume B ≠ ∞ := by rw [← Measure.prod_prod]; exact hAB
    have hA0 : (volume : Measure ℝ) A ≠ 0 := fun h => hne0 (by rw [h, zero_mul])
    have hB0 : (volume : Measure ℝ) B ≠ 0 := fun h => hne0 (by rw [h, mul_zero])
    have hAf : (volume : Measure ℝ) A ≠ ∞ := fun h => hABm (by rw [h, ENNReal.top_mul hB0])
    have hBf : (volume : Measure ℝ) B ≠ ∞ := fun h => hABm (by rw [h, ENNReal.mul_top hA0])
    set gA : E := indicatorConstLp 2 hA hAf (1 : ℂ) with hgA_def
    set gB : E := indicatorConstLp 2 hB hBf (1 : ℂ) with hgB_def
    set φ : E →L[ℂ] ℂ := c • (innerSL ℂ gB) with hφ_def
    set ψ : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight gA with hψ_def
    have hEq : l2KernelOp (indicatorConstLp 2 (hA.prod hB) hAB c) = ψ ∘L φ := by
      refine ContinuousLinearMap.ext fun f => Lp.ext ?_
      -- The functional: `⟪𝟙_B, f⟫ = ∫_B f`.
      have hinner : (innerSL ℂ gB) f
          = ∫ s, B.indicator (fun _ => (1 : ℂ)) s * (f : ℝ → ℂ) s ∂volume := by
        simp only [coe_innerSL_apply]
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [(indicatorConstLp_coeFn : (gB : ℝ → ℂ) =ᵐ[volume] _)] with s hs
        rw [hs, RCLike.inner_apply']
        by_cases hsB : s ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hsB]
      -- The a.e. shape of the kernel.
      have hker : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂(volume : Measure ℝ),
          ((indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) : ℝ × ℝ → ℂ) (t, s)
            = (A ×ˢ B).indicator (fun _ => c) (t, s) :=
        Measure.ae_ae_of_ae_prod indicatorConstLp_coeFn
      filter_upwards [l2KernelOp_apply_ae (indicatorConstLp 2 (hA.prod hB) hAB c) f,
        Lp.coeFn_smul (φ f) gA, (indicatorConstLp_coeFn : (gA : ℝ → ℂ) =ᵐ[volume] _), hker]
        with t h1 h2 h3 hs
      rw [h1]
      show (∫ s, ((indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) : ℝ × ℝ → ℂ) (t, s)
        * (f : ℝ → ℂ) s ∂volume) = _
      rw [ContinuousLinearMap.comp_apply, hψ_def, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply]
      rw [h2, Pi.smul_apply, h3, smul_eq_mul, hφ_def, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul, hinner]
      have hrw : (∫ s, ((indicatorConstLp 2 (hA.prod hB) hAB c : L2Kernel) : ℝ × ℝ → ℂ) (t, s)
          * (f : ℝ → ℂ) s ∂volume)
          = ∫ s, (A ×ˢ B).indicator (fun _ => c) (t, s) * (f : ℝ → ℂ) s ∂volume :=
        integral_congr_ae (by filter_upwards [hs] with s hsv using by rw [hsv])
      rw [hrw]
      by_cases htA : t ∈ A
      · rw [Set.indicator_of_mem htA, mul_one, ← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        by_cases hsB : s ∈ B <;>
          simp [Set.mem_prod, htA, hsB, Set.indicator_of_mem, Set.indicator_of_notMem]
      · rw [Set.indicator_of_notMem htA, mul_zero]
        have hz : ∀ s : ℝ, (A ×ˢ B).indicator (fun _ => c) (t, s) * (f : ℝ → ℂ) s = 0 := by
          intro s; simp [Set.mem_prod, htA, Set.indicator_of_notMem]
        simp [hz]
    rw [hEq]
    exact (isCompactOperator_of_locallyCompactSpace_dom φ).clm_comp ψ

/-!
#### Reduction of a general `L²` kernel to rectangle indicators

Three small generic `indicatorConstLp` facts, then the exhausting squares `[-R,R]²`.
-/

theorem indicatorConstLp_congr_set {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (h : s = t) (c : ℂ) :
    indicatorConstLp (μ := μ) 2 hs hμs c = indicatorConstLp 2 ht hμt c := by
  subst h; rfl

theorem indicatorConstLp_of_measure_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (h0 : μ s = 0) (c : ℂ) :
    indicatorConstLp (μ := μ) 2 hs hμs c = 0 := by
  rw [← norm_eq_zero, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Measure.real, h0]

theorem indicatorConstLp_eq_smul_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℂ) :
    indicatorConstLp (μ := μ) 2 hs hμs c = c • indicatorConstLp 2 hs hμs (1 : ℂ) := by
  refine Lp.ext ?_
  filter_upwards [(indicatorConstLp_coeFn : ⇑(indicatorConstLp (μ := μ) 2 hs hμs c) =ᵐ[μ] _),
    Lp.coeFn_smul c (indicatorConstLp (μ := μ) 2 hs hμs (1 : ℂ)),
    (indicatorConstLp_coeFn : ⇑(indicatorConstLp (μ := μ) 2 hs hμs (1 : ℂ)) =ᵐ[μ] _)]
    with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- The exhausting family of squares `[-R,R] × [-R,R]` in `ℝ × ℝ`. Each is a rectangle of finite
measure, and they increase to the whole plane; intersecting with them reduces the kernel density
argument to sets of finite measure. -/
def kernelBox (R : ℕ) : Set (ℝ × ℝ) := Set.Icc (-(R : ℝ)) R ×ˢ Set.Icc (-(R : ℝ)) R

theorem kernelBox_measurableSet (R : ℕ) : MeasurableSet (kernelBox R) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem kernelBox_ne_top (R : ℕ) : (volume.prod volume) (kernelBox R) ≠ ∞ := by
  rw [kernelBox, Measure.prod_prod, Real.volume_Icc]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne

theorem kernelBox_inter_ne_top (u : Set (ℝ × ℝ)) (R : ℕ) :
    (volume.prod volume) (u ∩ kernelBox R) ≠ ∞ :=
  ne_top_of_le_ne_top (kernelBox_ne_top R) (measure_mono Set.inter_subset_right)

theorem kernelBox_mono : Monotone kernelBox := by
  intro R R' hRR' p hp
  have h : (R : ℝ) ≤ R' := Nat.cast_le.mpr hRR'
  obtain ⟨h1, h2⟩ := hp
  exact ⟨Set.Icc_subset_Icc (by linarith) h h1, Set.Icc_subset_Icc (by linarith) h h2⟩

theorem iUnion_kernelBox : (⋃ R : ℕ, kernelBox R) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => Set.mem_iUnion.mpr ?_
  obtain ⟨R, hR⟩ := exists_nat_ge (max |p.1| |p.2|)
  have h1 := abs_le.mp ((le_max_left |p.1| |p.2|).trans hR)
  have h2 := abs_le.mp ((le_max_right |p.1| |p.2|).trans hR)
  exact ⟨R, ⟨h1.1, h1.2⟩, ⟨h2.1, h2.2⟩⟩

theorem l2KernelOp_isCompact (κ : L2Kernel) : IsCompactOperator (l2KernelOp κ) := by
  classical
  -- `V` = the kernels whose operator is compact: a closed submodule of `L²(ℝ × ℝ)`.
  set V : Submodule ℂ L2Kernel :=
    Submodule.comap (l2KernelOp : L2Kernel →L[ℂ] (E →L[ℂ] E)).toLinearMap
      (compactOperator (RingHom.id ℂ) E E) with hV_def
  have hVmem : ∀ ν : L2Kernel, ν ∈ V ↔ IsCompactOperator (l2KernelOp ν) := fun _ => Iff.rfl
  have hVclosed : IsClosed (V : Set L2Kernel) := by
    have hpre : (V : Set L2Kernel)
        = (l2KernelOp : L2Kernel → (E →L[ℂ] E)) ⁻¹' {f : E →L[ℂ] E | IsCompactOperator f} := rfl
    rw [hpre]
    exact isClosed_setOf_isCompactOperator.preimage l2KernelOp.continuous
  -- Step 1: rectangles.
  have hrect : ∀ (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (h : (volume.prod volume) (A ×ˢ B) ≠ ∞),
      indicatorConstLp 2 (hA.prod hB) h (1 : ℂ) ∈ V := fun A B hA hB h =>
    (hVmem _).mpr (l2KernelOp_indicator_prod_isCompact hA hB h 1)
  have hboxV : ∀ R : ℕ,
      indicatorConstLp 2 (kernelBox_measurableSet R) (kernelBox_ne_top R) (1 : ℂ) ∈ V := fun R =>
    hrect _ _ measurableSet_Icc measurableSet_Icc (kernelBox_ne_top R)
  -- Step 2: every measurable set, cut down to a box (π-λ induction over rectangles).
  have key : ∀ (u : Set (ℝ × ℝ)) (hu : MeasurableSet u), ∀ R : ℕ,
      indicatorConstLp 2 (hu.inter (kernelBox_measurableSet R)) (kernelBox_inter_ne_top u R)
        (1 : ℂ) ∈ V := by
    refine MeasurableSpace.induction_on_inter
      (C := fun u hu => ∀ R : ℕ, indicatorConstLp 2 (hu.inter (kernelBox_measurableSet R))
        (kernelBox_inter_ne_top u R) (1 : ℂ) ∈ V)
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
    · -- `∅`
      intro R
      rw [indicatorConstLp_of_measure_zero _ _ (by simp) 1]
      exact V.zero_mem
    · -- rectangles
      rintro t ⟨A, hA, B, hB, rfl⟩ R
      have hA' : MeasurableSet A := hA
      have hB' : MeasurableSet B := hB
      have hseteq : (A ×ˢ B) ∩ kernelBox R
          = (A ∩ Set.Icc (-(R : ℝ)) R) ×ˢ (B ∩ Set.Icc (-(R : ℝ)) R) := Set.prod_inter_prod
      have hfin2 : (volume.prod volume)
          ((A ∩ Set.Icc (-(R : ℝ)) R) ×ˢ (B ∩ Set.Icc (-(R : ℝ)) R)) ≠ ∞ := by
        rw [← hseteq]; exact kernelBox_inter_ne_top _ R
      rw [indicatorConstLp_congr_set _ _
        ((hA'.inter measurableSet_Icc).prod (hB'.inter measurableSet_Icc)) hfin2 hseteq 1]
      exact hrect _ _ (hA'.inter measurableSet_Icc) (hB'.inter measurableSet_Icc) hfin2
    · -- complements
      intro t htm ih R
      have hdisj : Disjoint (tᶜ ∩ kernelBox R) (t ∩ kernelBox R) := by
        refine Set.disjoint_left.mpr fun x hx hx' => ?_
        exact hx.1 hx'.1
      have hsum : indicatorConstLp 2 (kernelBox_measurableSet R) (kernelBox_ne_top R) (1 : ℂ)
          = indicatorConstLp 2 (htm.compl.inter (kernelBox_measurableSet R))
              (kernelBox_inter_ne_top _ R) (1 : ℂ)
            + indicatorConstLp 2 (htm.inter (kernelBox_measurableSet R))
              (kernelBox_inter_ne_top t R) (1 : ℂ) := by
        rw [← indicatorConstLp_disjoint_union (p := 2)
          (htm.compl.inter (kernelBox_measurableSet R)) (htm.inter (kernelBox_measurableSet R))
          (kernelBox_inter_ne_top _ R) (kernelBox_inter_ne_top t R) hdisj (1 : ℂ)]
        refine indicatorConstLp_congr_set _ _ _ _ ?_ 1
        ext x
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      have := V.sub_mem (hboxV R) (ih R)
      rwa [hsum, add_sub_cancel_right] at this
    · -- countable disjoint unions
      intro f hfd hfm ih R
      set Es : ℕ → Set (ℝ × ℝ) := fun i => f i ∩ kernelBox R with hEs
      have hEsm : ∀ i, MeasurableSet (Es i) := fun i =>
        (hfm i).inter (kernelBox_measurableSet R)
      have hEsfin : ∀ i, (volume.prod volume) (Es i) ≠ ∞ := fun i => kernelBox_inter_ne_top _ R
      have hEsd : Pairwise (fun i j => Disjoint (Es i) (Es j)) := fun i j hij =>
        ((hfd hij).mono Set.inter_subset_left Set.inter_subset_left)
      -- Partial unions are finite sums of rectangle-supported pieces.
      have hUm : ∀ n : ℕ, MeasurableSet (⋃ i ∈ Finset.range n, Es i) := fun n =>
        Finset.measurableSet_biUnion _ fun i _ => hEsm i
      have hUfin : ∀ n : ℕ, (volume.prod volume) (⋃ i ∈ Finset.range n, Es i) ≠ ∞ := by
        intro n
        refine ne_top_of_le_ne_top (kernelBox_ne_top R) (measure_mono ?_)
        exact Set.iUnion₂_subset fun i _ => Set.inter_subset_right
      have hpartial : ∀ n : ℕ, indicatorConstLp 2 (hUm n) (hUfin n) (1 : ℂ)
          = ∑ i ∈ Finset.range n, indicatorConstLp 2 (hEsm i) (hEsfin i) (1 : ℂ) := by
        intro n
        induction n with
        | zero =>
          simp only [Finset.range_zero, Finset.sum_empty]
          exact indicatorConstLp_of_measure_zero _ _ (by simp) 1
        | succ n ih2 =>
          have hdisj : Disjoint (Es n) (⋃ i ∈ Finset.range n, Es i) := by
            refine Set.disjoint_iUnion₂_right.mpr fun i hi => ?_
            exact hEsd (by simpa using (Finset.mem_range.mp hi).ne')
          have hsplit : indicatorConstLp 2 (hUm (n + 1)) (hUfin (n + 1)) (1 : ℂ)
              = indicatorConstLp 2 (hEsm n) (hEsfin n) (1 : ℂ)
                + indicatorConstLp 2 (hUm n) (hUfin n) (1 : ℂ) := by
            rw [← indicatorConstLp_disjoint_union (p := 2) (hEsm n) (hUm n) (hEsfin n) (hUfin n)
              hdisj (1 : ℂ)]
            refine indicatorConstLp_congr_set _ _ _ _ ?_ 1
            rw [Finset.range_add_one, Finset.set_biUnion_insert]
          rw [hsplit, Finset.sum_range_succ, ih2, add_comm]
      have hUV : ∀ n : ℕ, indicatorConstLp 2 (hUm n) (hUfin n) (1 : ℂ) ∈ V := by
        intro n
        rw [hpartial n]
        exact V.sum_mem fun i _ => ih i R
      -- The partial unions converge in `L²` to the full union.
      have hUnionm : MeasurableSet ((⋃ i, f i) ∩ kernelBox R) :=
        (MeasurableSet.iUnion hfm).inter (kernelBox_measurableSet R)
      have hset : (⋃ i, f i) ∩ kernelBox R = ⋃ i, Es i := by
        rw [hEs, Set.iUnion_inter]
      have htend : Filter.Tendsto
          (fun n => (volume.prod volume) ((⋃ i ∈ Finset.range n, Es i) ∆ (⋃ i, Es i)))
          Filter.atTop (nhds 0) := by
        haveI : IsFiniteMeasure ((volume.prod volume).restrict (kernelBox R)) := by
          refine ⟨?_⟩
          rw [Measure.restrict_apply_univ]
          exact lt_top_iff_ne_top.mpr (kernelBox_ne_top R)
        have hbase := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
          (μ := (volume.prod volume).restrict (kernelBox R))
          (fun i => (hEsm i).nullMeasurableSet) (fun i j hij => hEsd hij)
        have hsymm : ∀ n : ℕ, ((⋃ i ∈ Finset.range n, Es i) ∆ (⋃ i, Es i)) = ⋃ i ≥ n, Es i := by
          intro n
          ext x
          simp only [Set.mem_symmDiff, Set.mem_iUnion, Finset.mem_range, exists_prop, ge_iff_le]
          constructor
          · rintro (⟨⟨i, hi, hxi⟩, hx⟩ | ⟨⟨i, hxi⟩, hx⟩)
            · exact absurd ⟨i, hxi⟩ hx
            · refine ⟨i, ?_, hxi⟩
              by_contra hcon
              exact hx ⟨i, not_le.mp hcon, hxi⟩
          · rintro ⟨i, hin, hxi⟩
            refine Or.inr ⟨⟨i, hxi⟩, ?_⟩
            rintro ⟨j, hj, hxj⟩
            exact Set.disjoint_left.mp (hEsd (by omega : i ≠ j)) hxi hxj
        have hcap : ∀ n : ℕ, (⋃ i ≥ n, Es i) ∩ kernelBox R = ⋃ i ≥ n, Es i := fun n =>
          Set.inter_eq_left.mpr (Set.iUnion₂_subset fun i _ => Set.inter_subset_right)
        refine hbase.congr fun n => ?_
        rw [Function.comp_apply, Measure.restrict_apply' (kernelBox_measurableSet R), hcap n,
          hsymm n]
      have hlim : Filter.Tendsto
          (fun n => indicatorConstLp (μ := (volume : Measure ℝ).prod volume) 2 (hUm n) (hUfin n)
            (1 : ℂ))
          Filter.atTop
          (nhds (indicatorConstLp 2 hUnionm (kernelBox_inter_ne_top _ R) (1 : ℂ))) := by
        refine tendsto_indicatorConstLp_set (by norm_num) ?_
        simpa only [hset] using htend
      exact hVclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hUV)
  -- Step 3: exhaust the boxes, then run `Lp.induction`.
  have hind : ∀ (c : ℂ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
      (hμs : (volume.prod volume) s ≠ ∞), indicatorConstLp 2 hs hμs c ∈ V := by
    intro c s hs hμs
    rw [indicatorConstLp_eq_smul_one]
    refine V.smul_mem c ?_
    have hanti : Antitone fun R : ℕ => s \ kernelBox R := fun R R' hRR' =>
      Set.sdiff_subset_sdiff_right (kernelBox_mono hRR')
    have hzero : (⋂ R : ℕ, s \ kernelBox R) = ∅ := by
      rw [← Set.sdiff_iUnion, iUnion_kernelBox, Set.sdiff_univ]
    have htend : Filter.Tendsto (fun R : ℕ => (volume.prod volume) (s \ kernelBox R))
        Filter.atTop (nhds 0) := by
      have := tendsto_measure_iInter_atTop (μ := (volume : Measure ℝ).prod volume)
        (fun R : ℕ => (hs.diff (kernelBox_measurableSet R)).nullMeasurableSet) hanti
        ⟨0, ne_top_of_le_ne_top hμs (measure_mono Set.sdiff_subset)⟩
      rwa [hzero, measure_empty] at this
    have hlim : Filter.Tendsto
        (fun R : ℕ => indicatorConstLp (μ := (volume : Measure ℝ).prod volume) 2
          (hs.inter (kernelBox_measurableSet R)) (kernelBox_inter_ne_top s R) (1 : ℂ))
        Filter.atTop (nhds (indicatorConstLp 2 hs hμs (1 : ℂ))) := by
      refine tendsto_indicatorConstLp_set (by norm_num) ?_
      refine htend.congr fun R => ?_
      congr 1
      ext x
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    exact hVclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall fun R => key s hs R)
  refine (hVmem κ).mp ?_
  induction κ using Lp.induction (p := 2) (by norm_num) with
  | indicatorConst c hs hμs =>
      rw [Lp.simpleFunc.coe_indicatorConst]
      exact hind c hs hμs.ne
  | add hf hg _ hfV hgV => exact V.add_mem hfV hgV
  | isClosed => exact hVclosed

/-- **Leaf 4** (generic `L²`-kernel ⟹ compact operator). An integral operator on `L²(ℝ;ℂ)` whose
kernel is `L²` on `ℝ × ℝ` is a compact operator; it is realized a.e. as `f ↦ ∫ k(·,s) f(s) ds`.
Built via the reusable `l2KernelOp` Hilbert–Schmidt machinery above (Mathlib has no Hilbert–Schmidt
API). Stated existentially so the operator object is genuinely constructed together with its
compactness rather than assumed; the a.e.-representation clause pins `Op` uniquely (an `Lp` element
is an a.e. class), so the existential is not weakened by it.
@audit:ok -/
theorem l2KernelOperator_isCompact {k : ℝ → ℝ → ℂ}
    (hk : MemLp (fun p : ℝ × ℝ => k p.1 p.2) 2 (volume.prod volume)) :
    ∃ Op : E →L[ℂ] E, (∀ f : E, (Op f : ℝ → ℂ) =ᵐ[volume]
        fun t => ∫ s, k t s * (f : ℝ → ℂ) s ∂volume) ∧ IsCompactOperator Op := by
  refine ⟨l2KernelOp (hk.toLp _), fun f => ?_, l2KernelOp_isCompact _⟩
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂(volume : Measure ℝ),
      ((hk.toLp _ : L2Kernel) : ℝ × ℝ → ℂ) (t, s) = k t s :=
    Measure.ae_ae_of_ae_prod hk.coeFn_toLp
  filter_upwards [l2KernelOp_apply_ae (hk.toLp _) f, hae] with t h1 h2
  rw [h1]
  simp only [l2KernelApply]
  exact integral_congr_ae (by filter_upwards [h2] with s hs using by rw [hs])

/-- The sinc integral operator `C = Q_T ∘ P_W` acts a.e. as the integral operator of
`sincConvKernel`. Genuine composition of Leaf 1 and Leaf 2. The `0 ≤ W` hypothesis is inherited
from Leaf 2 as a parameter precondition and is discharged by the caller's case split.
@audit:ok -/
theorem timeBandLimitingComp_apply_ae (T W : ℝ) (hW : 0 ≤ W) (f : E) :
    (timeBandLimitingComp T W f : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ s, sincConvKernel T W t s * (f : ℝ → ℂ) s ∂volume := by
  have h1 : (timeBandLimitingComp T W f : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) *
        ((bandLimitSubspace W).starProjection f : ℝ → ℂ) := by
    simpa only [timeBandLimitingComp, ContinuousLinearMap.comp_apply] using
      timeLimitProj_apply_ae T ((bandLimitSubspace W).starProjection f)
  filter_upwards [h1, bandLimitProj_apply_ae W hW f] with t ht1 ht2
  rw [ht1]
  simp only [Pi.mul_apply]
  rw [ht2, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [sincConvKernel]
  ring

/-- The sinc integral operator `C = Q_T ∘ P_W` is compact. Genuine reduction: the operator built by
`l2KernelOperator_isCompact` for `sincConvKernel` coincides with `C` (both have the same a.e.
representative, hence are equal in `Lp`). No sign restriction on `W`: for `W < 0` the kernel
representation is unavailable (and false), but there `P_W = 0`, so `C = 0` is compact outright.
@audit:ok -/
theorem timeBandLimitingComp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingComp T W) := by
  rcases lt_or_ge W 0 with hW | hW
  · -- Degenerate band: `bandLimitSubspace W = ⊥`, so `C = Q_T ∘ 0 = 0`.
    have hzero : timeBandLimitingComp T W = 0 := by
      refine ContinuousLinearMap.ext fun f => ?_
      have hmem : (bandLimitSubspace W).starProjection f ∈ bandLimitSubspace W :=
        Submodule.coe_mem _
      have hzf : (bandLimitSubspace W).starProjection f = 0 :=
        (Submodule.eq_bot_iff _).mp (bandLimitSubspace_eq_bot_of_neg hW) _ hmem
      simp only [timeBandLimitingComp, ContinuousLinearMap.comp_apply, hzf, map_zero,
        zero_apply]
    rw [hzero]
    exact isCompactOperator_zero
  · obtain ⟨Op, hOp_ae, hOp_cpt⟩ := l2KernelOperator_isCompact (sincConvKernel_memLp T W)
    have hEq : Op = timeBandLimitingComp T W := by
      refine ContinuousLinearMap.ext (fun f => MeasureTheory.Lp.ext ?_)
      exact (hOp_ae f).trans (timeBandLimitingComp_apply_ae T W hW f).symm
    rwa [hEq] at hOp_cpt

/-- **The time-and-band limiting operator is compact.** `A = P_W ∘ C` with `C = Q_T ∘ P_W` compact
(the sinc integral operator) and `P_W` bounded, so `A` is compact by `clm_comp`.

Unconditional: the signature carries no hypothesis on `T` or `W`, and both degenerate parameter
ranges are discharged by real proofs rather than assumed away — `W < 0` via
`bandLimitSubspace_eq_bot_of_neg` (`P_W = 0`, so `C = 0`), `T < 0` via the empty `[0,T]`
(`Q_T = 0`), and `W = 0` inside Leaf 2 as a genuine null-band case.
@audit:ok -/
theorem timeBandLimitingOp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingOp T W) := by
  rw [timeBandLimitingOp_eq_bandProj_comp]
  exact (timeBandLimitingComp_isCompact T W).clm_comp (bandLimitSubspace W).starProjection

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
genuine dimension. For `c ≤ 0` it is a junk value: at `0 < T`, `0 < W` the span is then
infinite-dimensional and `finrank` reports `0` (this is why `prolateEigenvalues` below takes the
infimum over `0 < c` rather than `0 ≤ c` — the latter would let the junk `0` into the constraint set
and collapse the whole enumeration to `≡ 0`). Every use site below is guarded by `0 < c`; audited
site-by-site, no proof consumes the junk value.
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

Scope (audit, 2026-07-17): the enumeration is **not yet known to be nonzero**. Nothing in this file
or its dependencies establishes `prolateEigenvalues T W 0 ≠ 0` for `0 < T`, `0 < W`, so the
unconditional headlines below (`_nonneg`, `_le_one`, `_antitone`, `_tendsto_zero`) are all satisfied
by the constant-zero sequence and carry no spectral content on their own; they are the shape
statements, not the eigenvalue asymptotics. This is not a degenerate definition: at `W < 0` and at
`T < 0` the operator genuinely collapses and the enumeration really is `≡ 0`, so a positivity input
is needed to say more. The missing input is exactly one atom, `timeBandLimitingOp T W ≠ 0` for
`0 < T`, `0 < W`; from it, Mathlib's `ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero`
(fed by `timeBandLimitingOp_isCompact` / `_isSymmetric` / `_isPositive`) yields a positive
eigenvalue and hence `0 < prolateEigenvalues T W 0`. Note that atom bounds only the *first* entry:
`λ n ≠ 0` for all `n` additionally needs `A` to have infinite rank. Neither is the
`wall:nyquist-2w-dof` eigenvalue-concentration wall.
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
nothing about eigenvalues; the gap argument below does the work). It is, however, **not currently
dischargeable in-tree** — see the scope note on `prolateEigenvalues` — so this theorem has no
consumer yet.
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

end InformationTheory.Shannon.TimeBandLimiting
