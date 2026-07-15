import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

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

The compactness, eigenvalue enumeration and the Landau–Pollak–Slepian concentration count live in
later legs (`timeBandLimitingOp_isCompact`, `prolateEigenvalues`, `prolate_eigenvalue_count`).
-/

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory

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

end InformationTheory.Shannon.TimeBandLimiting
