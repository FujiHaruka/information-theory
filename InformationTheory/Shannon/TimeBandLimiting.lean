import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import InformationTheory.Shannon.NormalizedSinc

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
`sincConvKernel t s = 𝟙_[0,T](t) · 2W · sincN(2W(t−s))`. The eigenvalue enumeration and the
Landau–Pollak–Slepian concentration count live in later legs (`prolateEigenvalues`,
`prolate_eigenvalue_count`).
-/

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory
open scoped ENNReal

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
compact operator by the finite-rank simple-function approximation. The genuinely analytic content
therefore lives in four leaves, all `@residual(plan:shannon-hartley-operational-moonshot-plan)`:

* `timeLimitProj_apply_ae` — `Q_T` acts as multiplication by `𝟙_[0,T]`;
* `bandLimitProj_apply_ae` — `P_W` acts as convolution with `2W sincN(2W·)` (**the make-or-break
  abstract-projection ↔ concrete-sinc bridge**);
* `sincConvKernel_memLp` — the kernel is `L²` on `ℝ × ℝ`;
* `l2KernelOperator_isCompact` — a generic `L²`-kernel operator is compact (the finite-rank build).

The remaining declarations (`timeBandLimitingComp_apply_ae`,
`timeBandLimitingComp_isCompact`, `timeBandLimitingOp_isCompact`) are genuine reductions that
compose the four leaves and are proven `sorry`-free.
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

/-- **Leaf 1** (`Q_T` = multiplication by `𝟙_[0,T]`). The orthogonal projection onto the
time-limited subspace acts, a.e., as multiplication by the indicator of `[0,T]`. Proven via the
uniqueness of the orthogonal projection: the candidate `𝟙_[0,T]·g` lies in the subspace, and the
residual `𝟙_[0,T]ᶜ·g` is orthogonal to it. -/
theorem timeLimitProj_apply_ae (T : ℝ) (g : E) :
    ((timeLimitSubspace T).starProjection g : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) * (g : ℝ → ℂ) := by
  set S : Set ℝ := {t : ℝ | t < 0 ∨ T < t} with hS
  have hScompl : S = (Set.Icc (0 : ℝ) T)ᶜ := by
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
    constructor
    · rintro (h | h)
      · intro h0; exact absurd h0 (not_le.mpr h)
      · intro _; exact h
    · intro h
      rcases lt_or_ge x 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h h0)
  have hSmeas : MeasurableSet S := by rw [hScompl]; exact measurableSet_Icc.compl
  -- Candidate projection `P = 𝟙_[0,T] · g` as an `Lp` element.
  have hmem : MemLp ((Set.Icc (0 : ℝ) T).indicator (g : ℝ → ℂ)) 2 volume :=
    (Lp.memLp g).indicator measurableSet_Icc
  set P : E := hmem.toLp _ with hP
  have hP_ae : (P : ℝ → ℂ) =ᵐ[volume] (Set.Icc (0 : ℝ) T).indicator (g : ℝ → ℂ) := hmem.coeFn_toLp
  have hind : (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) * (g : ℝ → ℂ)
      = (Set.Icc (0 : ℝ) T).indicator (g : ℝ → ℂ) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) T <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hind]
  suffices hproj : (timeLimitSubspace T).starProjection g = P by rw [hproj]; exact hP_ae
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · -- `P ∈ timeLimitSubspace T`: `⇑P =ᵐ 0` on `S = [0,T]ᶜ`.
    show (P : ℝ → ℂ) =ᵐ[volume.restrict S] 0
    refine (ae_restrict_iff' hSmeas).mpr ?_
    filter_upwards [hP_ae] with x hx hxS
    rw [Pi.zero_apply, hx, Set.indicator_of_notMem]
    rw [hScompl] at hxS; exact hxS
  · -- Orthogonality: `⟪g - P, w⟫ = 0` for every `w` in the subspace.
    intro w hw
    have hw' : (w : ℝ → ℂ) =ᵐ[volume.restrict S] 0 := hw
    have hwS : ∀ᵐ x ∂volume, x ∈ S → (w : ℝ → ℂ) x = (0 : ℝ → ℂ) x :=
      (ae_restrict_iff' hSmeas).mp hw'
    rw [MeasureTheory.L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_sub g P, hP_ae, hwS] with x hsub hpx hwx
    simp only [Pi.zero_apply]
    by_cases hx : x ∈ Set.Icc (0 : ℝ) T
    · have hgP : (g - P : E) x = 0 := by
        rw [hsub]; simp only [Pi.sub_apply]; rw [hpx, Set.indicator_of_mem hx, sub_self]
      rw [hgP, inner_zero_left]
    · have hxS : x ∈ S := by rw [hScompl]; exact hx
      have hwx0 : (w : ℝ → ℂ) x = 0 := by simpa using hwx hxS
      rw [hwx0, inner_zero_right]

/-- **Leaf 2 — the make-or-break bridge** (`P_W` = convolution with `2W sincN(2W·)`). The
orthogonal projection onto the band-limited subspace acts, a.e., as convolution with the ideal
low-pass `2W sincN(2W·)` (whose Fourier transform is `𝟙_[-W,W]`). This is the abstract
`starProjection`-of-a-`comap`-under-`𝓕` ↔ concrete sinc-convolution identity.
@residual(plan:shannon-hartley-operational-moonshot-plan) -/
theorem bandLimitProj_apply_ae (W : ℝ) (f : E) :
    ((bandLimitSubspace W).starProjection f : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ s, ((2 * W * NormalizedSinc.sincN (2 * W * (t - s)) : ℝ) : ℂ) *
        (f : ℝ → ℂ) s ∂volume := by
  sorry -- @residual(plan:shannon-hartley-operational-moonshot-plan)

/-- The normalized sinc is square-integrable on `ℝ`. The reusable crux for the kernel-`L²` bound:
its Lebesgue `L²`-membership follows from the elementary majorant `sincN(x)² ≤ 2/(1 + x²)`
(`|sincN| ≤ 1` near `0`, `sincN(x)² = sin²(πx)/(πx)² ≤ 1/(πx)²` away from it) against the
integrable `2/(1 + x²)`. Mathlib's `Real.integrable_sinc` is finite-measure-only, so the Lebesgue
`L²` fact is built here. -/
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
the 2-D lift is a Tonelli (`lintegral_prod_le`) + `lintegral_sub_left_eq_self` computation. -/
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

/-- **Leaf 4** (generic `L²`-kernel ⟹ compact operator). An integral operator on `L²(ℝ;ℂ)` whose
kernel is `L²` on `ℝ × ℝ` is a compact operator; it is realized a.e. as `f ↦ ∫ k(·,s) f(s) ds`.
Built via finite-rank simple-function approximation of the kernel (Mathlib has no Hilbert–Schmidt
API, so this is the reusable self-build). Stated existentially so the operator object is genuinely
constructed together with its compactness rather than assumed.
@residual(plan:shannon-hartley-operational-moonshot-plan) -/
theorem l2KernelOperator_isCompact {k : ℝ → ℝ → ℂ}
    (hk : MemLp (fun p : ℝ × ℝ => k p.1 p.2) 2 (volume.prod volume)) :
    ∃ Op : E →L[ℂ] E, (∀ f : E, (Op f : ℝ → ℂ) =ᵐ[volume]
        fun t => ∫ s, k t s * (f : ℝ → ℂ) s ∂volume) ∧ IsCompactOperator Op := by
  sorry -- @residual(plan:shannon-hartley-operational-moonshot-plan)

/-- The sinc integral operator `C = Q_T ∘ P_W` acts a.e. as the integral operator of
`sincConvKernel`. Genuine composition of Leaf 1 and Leaf 2. -/
theorem timeBandLimitingComp_apply_ae (T W : ℝ) (f : E) :
    (timeBandLimitingComp T W f : ℝ → ℂ) =ᵐ[volume]
      fun t => ∫ s, sincConvKernel T W t s * (f : ℝ → ℂ) s ∂volume := by
  have h1 : (timeBandLimitingComp T W f : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℂ)) *
        ((bandLimitSubspace W).starProjection f : ℝ → ℂ) := by
    simpa only [timeBandLimitingComp, ContinuousLinearMap.comp_apply] using
      timeLimitProj_apply_ae T ((bandLimitSubspace W).starProjection f)
  filter_upwards [h1, bandLimitProj_apply_ae W f] with t ht1 ht2
  rw [ht1]
  simp only [Pi.mul_apply]
  rw [ht2, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [sincConvKernel]
  ring

/-- The sinc integral operator `C = Q_T ∘ P_W` is compact. Genuine reduction: the operator built by
`l2KernelOperator_isCompact` for `sincConvKernel` coincides with `C` (both have the same a.e.
representative, hence are equal in `Lp`). -/
theorem timeBandLimitingComp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingComp T W) := by
  obtain ⟨Op, hOp_ae, hOp_cpt⟩ := l2KernelOperator_isCompact (sincConvKernel_memLp T W)
  have hEq : Op = timeBandLimitingComp T W := by
    refine ContinuousLinearMap.ext (fun f => MeasureTheory.Lp.ext ?_)
    exact (hOp_ae f).trans (timeBandLimitingComp_apply_ae T W f).symm
  rwa [hEq] at hOp_cpt

/-- **The time-and-band limiting operator is compact.** `A = P_W ∘ C` with `C = Q_T ∘ P_W` compact
(the sinc integral operator) and `P_W` bounded, so `A` is compact by `clm_comp`. -/
theorem timeBandLimitingOp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingOp T W) := by
  rw [timeBandLimitingOp_eq_bandProj_comp]
  exact (timeBandLimitingComp_isCompact T W).clm_comp (bandLimitSubspace W).starProjection

end InformationTheory.Shannon.TimeBandLimiting
