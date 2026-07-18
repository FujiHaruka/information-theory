import InformationTheory.Shannon.TimeBandLimiting.Enumeration

/-!
# Time-and-band-limiting operator — the trace bound and spectral gap

Leg E / R1. The reproducing kernel `k_t = 2W sincN(2W(t − ·))` of the band-limited subspace, the
reproducing property `(P_W f)(t) = ⟪k_t, f⟫`, the Bessel trace bound `∑ᵢ ⟪A eᵢ, eᵢ⟫ ≤ 2WT` with
its Markov consequence `c · #{λ > c} ≤ 2WT`, and the spectral gap below `c`: `A` restricted to the
orthogonal complement of the high eigenspaces has norm `≤ c`, together with the eigenbasis trace
transport.
-/

namespace InformationTheory.Shannon.TimeBandLimiting

open MeasureTheory
open scoped ENNReal symmDiff FourierTransform

section TraceBound

/-- The reproducing kernel of the band-limited subspace at time `t`: the ideal low-pass
`2W sincN(2W(t − ·))`, whose Fourier transform is the spectral boxcar `𝟙_[-W,W] e^{-2πi t ·}`. It
is the integral kernel of `P_W`, so pairing against it evaluates a band-limited function at `t`.

The `2W` factor is not a free constant: `bandLimitProj_apply_ae` pins it against the Fourier
definition of `bandLimitSubspace`, so a wrong gain fails to compile rather than rescaling the
bound below.
@audit:ok -/
noncomputable def bandKernel (W t : ℝ) : ℝ → ℂ :=
  fun s => ((2 * W * NormalizedSinc.sincN (2 * W * (t - s)) : ℝ) : ℂ)

/-- The kernel is a constant multiple of the shifted, dilated sinc `sincN((· − t)/Δ)` at
`Δ = 1/(2W)`, whose `L²` membership is `ShannonHartley.shiftSinc_memLp`.
@audit:ok -/
theorem bandKernel_eq_smul_shiftSinc {W : ℝ} (hW : 0 < W) (t : ℝ) :
    bandKernel W t
      = fun s => (2 * W : ℂ) *
          ((NormalizedSinc.sincN ((s - t) / (1 / (2 * W))) : ℝ) : ℂ) := by
  funext s
  simp only [bandKernel]
  rw [show (s - t) / (1 / (2 * W)) = -(2 * W * (t - s)) by field_simp; ring,
    NormalizedSinc.sincN_neg]
  push_cast
  ring

theorem bandKernel_memLp (W t : ℝ) : MemLp (bandKernel W t) 2 volume := by
  -- The positive-band case; the other two reduce to it.
  have key : ∀ V : ℝ, 0 < V → ∀ u : ℝ, MemLp (bandKernel V u) 2 volume := by
    intro V hV u
    have hΔ : (0 : ℝ) < 1 / (2 * V) := by positivity
    rw [bandKernel_eq_smul_shiftSinc hV u]
    exact (ShannonHartley.shiftSinc_memLp u (1 / (2 * V)) hΔ).const_mul (2 * V : ℂ)
  rcases lt_trichotomy W 0 with hW | hW | hW
  · -- `W < 0`: `sincN` is even, so the kernel is minus the ideal low-pass at `-W > 0`.
    have heq : bandKernel W t = -bandKernel (-W) t := by
      funext s
      simp only [bandKernel, Pi.neg_apply]
      rw [show 2 * -W * (t - s) = -(2 * W * (t - s)) by ring, NormalizedSinc.sincN_neg]
      push_cast
      ring
    rw [heq]
    exact (key (-W) (by linarith) t).neg
  · subst hW
    have hz : bandKernel 0 t = fun _ => (0 : ℂ) := by funext s; simp [bandKernel]
    rw [hz]
    exact MemLp.zero'
  · exact key W hW t

/-- The reproducing kernel at time `t`, as an element of `L²(ℝ;ℂ)`.
@audit:ok -/
noncomputable def bandKernelLp (W t : ℝ) : E := (bandKernel_memLp W t).toLp (bandKernel W t)

theorem bandKernelLp_norm_sq (W t : ℝ) (hW : 0 < W) : ‖bandKernelLp W t‖ ^ 2 = 2 * W := by
  have hΔ : (0 : ℝ) < 1 / (2 * W) := by positivity
  set S : E := (ShannonHartley.shiftSinc_memLp t (1 / (2 * W)) hΔ).toLp
    (fun s => (NormalizedSinc.sincN ((s - t) / (1 / (2 * W))) : ℂ)) with hSdef
  set B : E := (ShannonHartley.specBoxcar_memLp t (1 / (2 * W)) hΔ 2).toLp
    (ShannonHartley.specBoxcar t (1 / (2 * W))) with hBdef
  -- Plancherel on the band: `‖B‖² = Δ = 1/(2W)`, the boxcar's own energy.
  have hBnorm : ‖B‖ ^ 2 = 1 / (2 * W) := by
    have h := ShannonHartley.inner_specBoxcar_toLp t t (1 / (2 * W)) hΔ
    rw [sub_self, zero_div, NormalizedSinc.sincN_zero, ← hBdef,
      inner_self_eq_norm_sq_to_K] at h
    have h' : (((‖B‖ ^ 2 : ℝ)) : ℂ) = (((1 / (2 * W) : ℝ)) : ℂ) := by
      push_cast at h ⊢
      linear_combination h
    exact_mod_cast h'
  -- The Fourier isometry carries `S` to `B`.
  have hFS : Lp.fourierTransformₗᵢ ℝ ℂ S = B :=
    ShannonHartley.fourier_shiftSinc_toLp t (1 / (2 * W)) hΔ
  have hSnorm : ‖S‖ = ‖B‖ := by
    rw [← hFS]
    exact ((Lp.fourierTransformₗᵢ ℝ ℂ).norm_map S).symm
  -- The kernel is `2W · S`.
  have hfun : bandKernel W t
      = (2 * W : ℂ) • (fun s : ℝ => ((NormalizedSinc.sincN ((s - t) / (1 / (2 * W))) : ℝ) : ℂ)) := by
    rw [bandKernel_eq_smul_shiftSinc hW t]
    rfl
  have hk : bandKernelLp W t = (2 * W : ℂ) • S := by
    rw [bandKernelLp, hSdef,
      ← MemLp.toLp_const_smul (2 * W : ℂ) (ShannonHartley.shiftSinc_memLp t (1 / (2 * W)) hΔ)]
    exact MemLp.toLp_congr _ _ (by rw [hfun])
  have hn : ‖(2 * W : ℂ)‖ = 2 * W := by
    rw [show (2 * W : ℂ) = ((2 * W : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hk, norm_smul, mul_pow, hSnorm, hBnorm, hn]
  field_simp

theorem inner_bandKernelLp (W t : ℝ) (f : E) :
    inner ℂ (bandKernelLp W t) f = ∫ s, bandKernel W t s * (f : ℝ → ℂ) s ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  simp only [bandKernelLp]
  filter_upwards [(bandKernel_memLp W t).coeFn_toLp] with s hs
  rw [hs, RCLike.inner_apply]
  simp only [bandKernel, Complex.conj_ofReal]
  ring

/-- The reproducing property of the band-limited subspace: `(P_W f)(t) = ⟪k_t, f⟫` for a.e. `t`,
with `k_t = bandKernelLp W t` the ideal low-pass centered at `t`. This is
`bandLimitProj_apply_ae` read as an `L²` pairing; the kernel is real-valued, so the conjugation in
the (conjugate-linear-in-the-first-slot) inner product is invisible.
@audit:ok -/
theorem bandLimitProj_apply_eq_inner (W : ℝ) (hW : 0 ≤ W) (f : E) :
    ((bandLimitSubspace W).starProjection f : ℝ → ℂ) =ᵐ[volume]
      fun t => inner ℂ (bandKernelLp W t) f := by
  filter_upwards [bandLimitProj_apply_ae W hW f] with t ht
  rw [ht, inner_bandKernelLp]
  simp only [bandKernel]

/-- The quadratic form of `A` is the energy of `P_W f` observed through the window `[0,T]`:
`⟪A f, f⟫ = ∫_[0,T] |⟪k_t, f⟫|² dt`. Self-adjointness of `P_W` moves one copy across the pairing,
and `timeLimitProj_apply_ae` turns `Q_T` into multiplication by `𝟙_[0,T]`.
@audit:ok -/
theorem inner_timeBandLimitingOp_self_eq (T W : ℝ) (hW : 0 ≤ W) (f : E) :
    (inner ℂ (timeBandLimitingOp T W f) f).re
      = ∫ t in Set.Icc (0 : ℝ) T, ‖inner ℂ (bandKernelLp W t) f‖ ^ 2 := by
  set g : E := (bandLimitSubspace W).starProjection f with hgdef
  -- Step 1: `P_W` is self-adjoint, so it moves to the right slot.
  have hsym : ((bandLimitSubspace W).starProjection : E →ₗ[ℂ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_starProjection (bandLimitSubspace W))
  have hstep1 : inner ℂ (timeBandLimitingOp T W f) f
      = inner ℂ ((timeLimitSubspace T).starProjection g) g :=
    hsym ((timeLimitSubspace T).starProjection g) f
  -- Step 2: `Q_T` is multiplication by `𝟙_[0,T]`, so the pairing is the windowed energy.
  have hstep2 : inner ℂ ((timeLimitSubspace T).starProjection g) g
      = (((∫ t in Set.Icc (0 : ℝ) T, ‖(g : ℝ → ℂ) t‖ ^ 2) : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    have hcongr : (∫ t, (inner ℂ (((timeLimitSubspace T).starProjection g : ℝ → ℂ) t)
          ((g : ℝ → ℂ) t) : ℂ))
        = ∫ t, (Set.Icc (0 : ℝ) T).indicator
            (fun t => (((‖(g : ℝ → ℂ) t‖ ^ 2) : ℝ) : ℂ)) t := by
      refine integral_congr_ae ?_
      filter_upwards [timeLimitProj_apply_ae T g] with t ht
      rw [ht, Pi.mul_apply]
      by_cases htm : t ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem htm, Set.indicator_of_mem htm, one_mul,
          inner_self_eq_norm_sq_to_K]
        norm_cast
      · rw [Set.indicator_of_notMem htm, Set.indicator_of_notMem htm, zero_mul,
          inner_zero_left]
    rw [hcongr, integral_indicator measurableSet_Icc, integral_complex_ofReal]
  -- Step 3: the windowed energy is the kernel pairing, by the reproducing property.
  have hstep3 : (∫ t in Set.Icc (0 : ℝ) T, ‖(g : ℝ → ℂ) t‖ ^ 2)
      = ∫ t in Set.Icc (0 : ℝ) T, ‖inner ℂ (bandKernelLp W t) f‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (bandLimitProj_apply_eq_inner W hW f)] with t ht
    rw [hgdef, ht]
  rw [hstep1, hstep2, Complex.ofReal_re, hstep3]

theorem integrableOn_inner_bandKernelLp_sq (T W : ℝ) (hW : 0 ≤ W) (f : E) :
    IntegrableOn (fun t => ‖inner ℂ (bandKernelLp W t) f‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
  have hint : Integrable
      (fun t => ‖((bandLimitSubspace W).starProjection f : ℝ → ℂ) t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  refine (hint.integrableOn (s := Set.Icc (0 : ℝ) T)).congr ?_
  filter_upwards [ae_restrict_of_ae (bandLimitProj_apply_eq_inner W hW f)] with t ht
  rw [ht]

/-- **Leg E gateway atom.** The trace of the time-and-band limiting operator along any finite
orthonormal family is at most `2WT`.

The quadratic form `⟪A eᵢ, eᵢ⟫ = ∫_[0,T] |⟪k_t, eᵢ⟫|² dt` (`inner_timeBandLimitingOp_self_eq`) turns
the trace into an integral of a *finite* sum, so the sum and the integral commute without any
Fubini; Bessel's inequality then caps the integrand by the constant `‖k_t‖² = 2W`
(`bandKernelLp_norm_sq`), and the window `[0,T]` supplies the factor `T`. No trace-class or Schatten
theory is involved — only a finite orthonormal family — so Mathlib's lack of Schatten API does not
block this bound.

Scope (audited 2026-07-17): this is the *trace* bound, not the Landau–Pollak–Slepian
degrees-of-freedom count. It is the same Bessel argument that already closes
`contAwgnMaxMessages_bddAbove` wall-free, and like that bound it yields the crude constant only.
It does **not** bear on `wall:nyquist-2w-dof`, whose content is the eigenvalue *concentration*
(`≈2WT` eigenvalues near `1`, the rest near `0`); Bessel is one-directional and cannot reach it.
@audit:ok -/
theorem sum_inner_timeBandLimitingOp_le (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W)
    {d : ℕ} {e : Fin d → E} (he : Orthonormal ℂ e) :
    ∑ i, (inner ℂ (timeBandLimitingOp T W (e i)) (e i)).re ≤ 2 * W * T := by
  classical
  have hint : ∀ i : Fin d,
      IntegrableOn (fun t => ‖inner ℂ (bandKernelLp W t) (e i)‖ ^ 2)
        (Set.Icc (0 : ℝ) T) volume :=
    fun i => integrableOn_inner_bandKernelLp_sq T W hW.le (e i)
  -- The trace is the integral of the Bessel sum: a finite sum, so it commutes with `∫`.
  have hsum : ∑ i, (inner ℂ (timeBandLimitingOp T W (e i)) (e i)).re
      = ∫ t in Set.Icc (0 : ℝ) T, ∑ i, ‖inner ℂ (bandKernelLp W t) (e i)‖ ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => inner_timeBandLimitingOp_self_eq T W hW.le (e i)
  rw [hsum]
  -- Bessel's inequality, pointwise in `t`, against the constant kernel norm `‖k_t‖² = 2W`.
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∑ i, ‖inner ℂ (bandKernelLp W t) (e i)‖ ^ 2) ≤ 2 * W := by
    intro t _
    have hb := he.sum_inner_products_le (x := bandKernelLp W t) (s := Finset.univ)
    rw [bandKernelLp_norm_sq W t hW] at hb
    refine le_trans (le_of_eq ?_) hb
    exact Finset.sum_congr rfl fun i _ => by rw [← norm_inner_symm]
  have hconst : IntegrableOn (fun _ : ℝ => 2 * W) (Set.Icc (0 : ℝ) T) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  calc (∫ t in Set.Icc (0 : ℝ) T, ∑ i, ‖inner ℂ (bandKernelLp W t) (e i)‖ ^ 2)
      ≤ ∫ _t in Set.Icc (0 : ℝ) T, 2 * W :=
        setIntegral_mono_on (integrable_finsetSum _ (fun i _ => hint i)) hconst
          measurableSet_Icc hle
    _ = 2 * W * T := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hT, sub_zero, smul_eq_mul]
        ring

/-- An orthonormal family in a separable inner-product space is countable.

Distinct members sit at distance `√2`, so the open balls of radius `1/2` around them are pairwise
disjoint, and a separable space admits only countably many pairwise-disjoint nonempty open sets
(`Pairwise.countable_of_isOpen_disjoint`). Mathlib has no such lemma (loogle `Orthonormal, Countable`
= `Found 0`, 2026-07-17), so it is built here; it is what lets `tsum_inner_timeBandLimitingOp_eq`
*derive* the countability its Tonelli step needs instead of assuming it.
@audit:ok -/
theorem orthonormal_countable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] {ι : Type*} {v : ι → H} (hv : Orthonormal ℂ v) :
    Countable ι := by
  -- Distinct members sit at distance `√2`, so the balls of radius `1/2` around them are disjoint.
  have hdist : ∀ i j, i ≠ j → ‖v i - v j‖ ^ 2 = 2 := by
    intro i j hij
    have h : (inner ℂ (v i) (-v j) : ℂ) = 0 := by rw [inner_neg_right, hv.2 hij, neg_zero]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v i) (-v j) h
    rw [← sub_eq_add_neg, norm_neg, hv.1 i, hv.1 j] at hp
    rw [sq]; rw [hp]; norm_num
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1 / 2)) ?_
    (fun _ => Metric.isOpen_ball) (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  simp only [Function.onFun]
  refine Metric.ball_disjoint_ball ?_
  have h2 : ‖v i - v j‖ ^ 2 = 2 := hdist i j hij
  have hnn : (0 : ℝ) ≤ ‖v i - v j‖ := norm_nonneg _
  rw [dist_eq_norm]
  nlinarith

theorem hasSum_norm_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ E) (k : E) :
    HasSum (fun i => ‖inner ℂ k (b i)‖ ^ 2) (‖k‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner k k
  have hval : (inner ℂ k k : ℂ) = ((‖k‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hterm : ∀ i, (inner ℂ k (b i) : ℂ) * (inner ℂ (b i) k : ℂ)
      = ((‖inner ℂ k (b i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm (b i) k, RCLike.mul_conj (K := ℂ)]
    norm_cast
  rw [funext hterm, hval] at h
  exact Complex.hasSum_ofReal.mp h

theorem hasSum_norm_inner_bandKernelLp_sq {ι : Type*} (b : HilbertBasis ι ℂ E) (W t : ℝ) :
    HasSum (fun i => ‖inner ℂ (bandKernelLp W t) (b i)‖ ^ 2) (‖bandKernelLp W t‖ ^ 2) :=
  hasSum_norm_inner_sq b (bandKernelLp W t)

/-- **Leg E-trace.** The trace of the time-and-band limiting operator along *any* complete
orthonormal basis is exactly `2WT`.

This upgrades the Bessel *inequality* `sum_inner_timeBandLimitingOp_le` to a Parseval *equality*.
The quadratic form `⟪A bᵢ, bᵢ⟫ = ∫_[0,T] |⟪k_t, bᵢ⟫|² dt` (`inner_timeBandLimitingOp_self_eq`) makes
the trace a sum of integrals of nonnegative terms, so Tonelli (`lintegral_tsum`, over `ℝ≥0∞`)
exchanges `∑'` and `∫` with no joint-integrability side condition; completeness of the basis then
replaces Bessel by Parseval (`hasSum_norm_inner_bandKernelLp_sq`), pinning the integrand to exactly
`‖k_t‖² = 2W` (`bandKernelLp_norm_sq`), and the window `[0,T]` supplies the factor `T`.

No spectral theorem and no trace-class theory are used: Mathlib's lack of Schatten/Hilbert–Schmidt
API (real, and confirmed) does not block this identity. Countability of the index — the Tonelli
step's only structural need — is *derived* from separability of `L²(ℝ;ℂ)` via
`orthonormal_countable`, not assumed. `exists_hilbertBasis_tsum_inner_timeBandLimitingOp_eq`
witnesses in-tree that such a basis exists, so the statement is not vacuous.

Scope (the question that matters, asked before reporting): this is an *exact first moment*
`∑ λₙ = 2WT`, which is **not** what `wall:nyquist-2w-dof` names. The wall's content is the
Landau–Pollak–Slepian *concentration* `#{n | λₙ > c} = 2WT + O(log WT)`, and the first moment does
not reach it in either direction. Upward it feeds only Markov (`prolateCount_mul_le`), which uses
just the `≤` half and overcounts by `1/c`; the exactness buys nothing there. Downward it is
strictly insufficient: a spectrum with `∑ λₙ = 2WT` and every `λₙ ≤ c` has `#{λₙ > c} = 0`, so no
lower bound on the count follows from the first moment alone. Splitting the sum gives
`#{λₙ > c} ≥ 2WT − ∑_{λₙ ≤ c} λₙ`, whose tail term is controlled only by the *second* moment
`∑ λₙ(1 − λₙ) = tr A − tr A²`. That second moment — not this identity — remains the blocker.
@audit:ok -/
theorem tsum_inner_timeBandLimitingOp_eq (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W)
    {ι : Type*} (b : HilbertBasis ι ℂ E) :
    ∑' i, (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re = 2 * W * T := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  haveI : Countable ι := orthonormal_countable b.orthonormal
  set a : ι → ℝ := fun i => (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re with hadef
  have hint : ∀ i : ι,
      IntegrableOn (fun t => ‖inner ℂ (bandKernelLp W t) (b i)‖ ^ 2) (Set.Icc (0 : ℝ) T) volume :=
    fun i => integrableOn_inner_bandKernelLp_sq T W hW.le (b i)
  have ha : ∀ i, a i = ∫ t in Set.Icc (0 : ℝ) T, ‖inner ℂ (bandKernelLp W t) (b i)‖ ^ 2 :=
    fun i => inner_timeBandLimitingOp_self_eq T W hW.le (b i)
  have hnn : ∀ i, 0 ≤ a i := by
    intro i
    rw [ha i]
    exact setIntegral_nonneg measurableSet_Icc fun t _ => by positivity
  -- Each trace entry as a lower Lebesgue integral, so the swap below needs no integrability side
  -- condition.
  have hlint : ∀ i, ENNReal.ofReal (a i)
      = ∫⁻ t in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (‖inner ℂ (bandKernelLp W t) (b i)‖ ^ 2) := by
    intro i
    rw [ha i]
    exact ofReal_integral_eq_lintegral_ofReal (hint i) (ae_of_all _ fun t => by positivity)
  have hmeas : ∀ i, AEMeasurable
      (fun t => ENNReal.ofReal (‖inner ℂ (bandKernelLp W t) (b i)‖ ^ 2))
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun i => ENNReal.measurable_ofReal.comp_aemeasurable (hint i).1.aemeasurable
  have hTW : (0 : ℝ) ≤ 2 * W * T := mul_nonneg (by linarith) hT
  -- Tonelli (every term is `≥ 0`) plus Parseval, pointwise in `t`.
  have hkey : ∑' i, ENNReal.ofReal (a i) = ENNReal.ofReal (2 * W * T) := by
    rw [tsum_congr hlint, ← lintegral_tsum hmeas]
    have hpt : ∀ t : ℝ, (∑' i, ENNReal.ofReal (‖inner ℂ (bandKernelLp W t) (b i)‖ ^ 2))
        = ENNReal.ofReal (2 * W) := by
      intro t
      have hs := hasSum_norm_inner_bandKernelLp_sq b W t
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs.summable, hs.tsum_eq,
        bandKernelLp_norm_sq W t hW]
    rw [lintegral_congr hpt, setLIntegral_const, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul (by linarith)]
  -- Transfer the identity back to `ℝ`.
  have h := ENNReal.tsum_toReal_eq (f := fun i => ENNReal.ofReal (a i))
    fun i => ENNReal.ofReal_ne_top
  rw [hkey, ENNReal.toReal_ofReal hTW,
    tsum_congr fun i => ENNReal.toReal_ofReal (hnn i)] at h
  exact h.symm

/-- Non-vacuity of `tsum_inner_timeBandLimitingOp_eq`, machine-checked rather than asserted: a
Hilbert basis of `L²(ℝ;ℂ)` exists (`exists_hilbertBasis`), so the trace identity is a statement
about a real object and not an empty quantification over an uninhabited hypothesis.
@audit:ok -/
theorem exists_hilbertBasis_tsum_inner_timeBandLimitingOp_eq (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E),
      ∑' i, (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re = 2 * W * T := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  exact ⟨w, b, tsum_inner_timeBandLimitingOp_eq T W hT hW b⟩

theorem star_mem_eigenspace {T W : ℝ} {μ : ℝ} {v : E}
    (hv : v ∈ Module.End.eigenspace (prolateEnd T W) (μ : ℂ)) :
    star v ∈ Module.End.eigenspace (prolateEnd T W) (μ : ℂ) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : (prolateEnd T W) (star v) = star ((prolateEnd T W) v) :=
    timeBandLimitingOp_star_comm T W v
  rw [h1, hv, star_smul_Lp, Complex.conj_ofReal]

/-- Complex conjugation preserves the span of the high eigenspaces. The operator `A` commutes with
`star` (`timeBandLimitingOp_star_comm`) and its eigenvalues are real, so each eigenspace above `c` is
`star`-invariant; the span inherits it. This is the `ℂ/ℝ` bridge that lets the achievability path
choose real-valued prolate eigenfunctions — it proves the *span is star-invariant*, not that any
individual eigenfunction is real (the latter is the downstream real-basis extraction, not claimed
here). Independently audited 2026-07-17: sorryAx-free, the `hv` hypothesis is the antecedent of a
closure property (not load-bearing), and the prose does not overclaim.
@audit:ok -/
theorem star_mem_prolateEigenspaceSup {T W c : ℝ} {v : E}
    (hv : v ∈ prolateEigenspaceSup T W c) :
    star v ∈ prolateEigenspaceSup T W c := by
  rw [prolateEigenspaceSup, iSup_subtype'] at hv ⊢
  induction hv using Submodule.iSup_induction' with
  | mem i x hx => exact Submodule.mem_iSup_of_mem i (star_mem_eigenspace hx)
  | zero => rw [star_zero_Lp]; exact zero_mem _
  | add x y _ _ ihx ihy => rw [star_add_Lp]; exact add_mem ihx ihy

theorem prolateEigenspaceSup_invariant (T W c : ℝ) :
    ∀ v ∈ prolateEigenspaceSup T W c,
      (timeBandLimitingOp T W : E →ₗ[ℂ] E) v ∈ prolateEigenspaceSup T W c := by
  intro v hv
  have hle : prolateEigenspaceSup T W c
      ≤ Submodule.comap (timeBandLimitingOp T W : E →ₗ[ℂ] E) (prolateEigenspaceSup T W c) := by
    conv_lhs => rw [prolateEigenspaceSup]
    refine iSup₂_le fun μ hμ => ?_
    intro w hw
    have hwV : w ∈ prolateEigenspaceSup T W c :=
      Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ hw)
    rw [Module.End.mem_eigenspace_iff] at hw
    refine Submodule.mem_comap.mpr ?_
    rw [show (timeBandLimitingOp T W : E →ₗ[ℂ] E) w = (μ : ℂ) • w from hw]
    exact Submodule.smul_mem _ _ hwV
  exact hle hv

/-! ### Leg R1 — the spectral gap below `c` -/

theorem prolateEigenspaceSup_orthogonal_invariant (T W c : ℝ) :
    ∀ v ∈ (prolateEigenspaceSup T W c)ᗮ,
      (timeBandLimitingOp T W : E →ₗ[ℂ] E) v ∈ (prolateEigenspaceSup T W c)ᗮ :=
  LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule
    (timeBandLimitingOp_isSymmetric T W) (prolateEigenspaceSup_invariant T W c)

/-- `A` restricted to the orthogonal complement of the span of the eigenspaces above `c`.

Audited 2026-07-17 (independent). Checked for degenerate-definition abuse rather than assumed
genuine: this is the honest restriction of `A`, not a disguised `0`. The machine says so — the
`rfl` step in `inner_timeBandLimitingOp_le_of_mem_orthogonal` proves
`(prolateRestrict T W c ⟨v, hv⟩ : E) = timeBandLimitingOp T W v` definitionally, which no zero map
could satisfy for a nonzero `A` (`timeBandLimitingOp_ne_zero`).
@audit:ok -/
noncomputable def prolateRestrict (T W c : ℝ) :
    (prolateEigenspaceSup T W c)ᗮ →L[ℂ] (prolateEigenspaceSup T W c)ᗮ :=
  (timeBandLimitingOp T W).restrict (prolateEigenspaceSup_orthogonal_invariant T W c)

theorem prolateRestrict_hasEigenvalue_le (T W : ℝ) {c : ℝ} {μ : ℂ}
    (hμ : Module.End.HasEigenvalue
      ((prolateRestrict T W c : _ →L[ℂ] _) : Module.End ℂ ↥(prolateEigenspaceSup T W c)ᗮ) μ) :
    ‖μ‖ ≤ c := by
  obtain ⟨w, hw_mem, hw_ne⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hw_mem
  -- Transfer the eigenvector equation from `Vᗮ` to the ambient space.
  have hwE : timeBandLimitingOp T W (w : E) = μ • (w : E) := by
    have h := congrArg (Subtype.val (p := fun x : E => x ∈ (prolateEigenspaceSup T W c)ᗮ)) hw_mem
    simpa [prolateRestrict] using h
  have hwE_ne : (w : E) ≠ 0 := by simpa using hw_ne
  have hμA : (prolateEnd T W).HasEigenvalue μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hwE, hwE_ne⟩
  -- Symmetry makes `μ` real.
  have hconj := (timeBandLimitingOp_isSymmetric T W).conj_eigenvalue_eq_self hμA
  have him : μ.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by simp [him])
  have hμ' : (prolateEnd T W).HasEigenvalue ((μ.re : ℝ) : ℂ) := hre ▸ hμA
  -- Positivity makes it nonnegative.
  have hnn : 0 ≤ μ.re := by
    apply eigenvalue_nonneg_of_nonneg (𝕜 := ℂ) (T := (prolateEnd T W)) hμ'
    intro x
    have h := (timeBandLimitingOp_isPositive T W).inner_nonneg_right x
    have := (Complex.le_def.mp h).1
    simpa using this
  -- An eigenvalue above `c` would put its eigenvector in `V ⊓ Vᗮ = ⊥`.
  have hle : μ.re ≤ c := by
    by_contra hcon
    push Not at hcon
    have hmem : μ.re ∈ prolateEigenvalueSet T W c := ⟨hcon, hμ'⟩
    have hsub : Module.End.eigenspace (prolateEnd T W) ((μ.re : ℝ) : ℂ)
        ≤ prolateEigenspaceSup T W c := by
      rw [prolateEigenspaceSup]
      exact le_biSup (fun ν : ℝ => Module.End.eigenspace (prolateEnd T W) ((ν : ℝ) : ℂ)) hmem
    have hwV : (w : E) ∈ prolateEigenspaceSup T W c :=
      hsub (Module.End.mem_eigenspace_iff.mpr (by rw [hre]; exact hwE))
    have hzero : inner ℂ (w : E) (w : E) = (0 : ℂ) :=
      (Submodule.mem_orthogonal _ _).mp w.2 _ hwV
    exact hwE_ne (inner_self_eq_zero.mp hzero)
  rw [← hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- The restriction of `A` to `Vᗮ` is a contraction by `c`: `‖S‖ ≤ c`.

Audited 2026-07-17 (independent). `hc : 0 < c` is regularity, not load-bearing: it is consumed only
to place the spectral point `0` below the bound and to invert `ENNReal.ofReal`, never to supply
spectral content. The route was machine-confirmed by walking the transitive constant graph rather
than read off the prose — `ContinuousLinearMap.spectralRadius_eq_nnnorm` (Rayleigh) and
`IsCompactOperator.hasEigenvalue_iff_mem_spectrum` are both genuinely consumed, and
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` is *not*.
@audit:ok -/
theorem prolateRestrict_norm_le (T W : ℝ) {c : ℝ} (hc : 0 < c) :
    ‖prolateRestrict T W c‖ ≤ c := by
  have hsa : IsSelfAdjoint (prolateRestrict T W c) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      ((timeBandLimitingOp_isSymmetric T W).restrict_invariant
        (prolateEigenspaceSup_orthogonal_invariant T W c))
  have hcpt : IsCompactOperator (prolateRestrict T W c) :=
    (timeBandLimitingOp_isCompact T W).restrict'
      (prolateEigenspaceSup_orthogonal_invariant T W c)
  -- For a compact operator every nonzero spectral point is an eigenvalue, hence `≤ c`.
  have hspec : ∀ z ∈ spectrum ℂ (prolateRestrict T W c), ‖z‖ ≤ c := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simpa using hc.le
    · exact prolateRestrict_hasEigenvalue_le T W
        ((hcpt.hasEigenvalue_iff_mem_spectrum hz0).mpr hz)
  -- Self-adjointness turns the spectral radius into the norm.
  have hrad := (prolateRestrict T W c).spectralRadius_eq_nnnorm hsa
  have hle : (‖prolateRestrict T W c‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [← hrad, spectralRadius]
    refine iSup₂_le fun z hz => ?_
    rw [← enorm_eq_nnnorm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hspec z hz)
  rw [← enorm_eq_nnnorm, ← ofReal_norm] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hc.le).mp hle

/-- **The spectral gap below `c`.** On the orthogonal complement of the span of every eigenspace
of `A` with eigenvalue exceeding `c`, the Rayleigh quotient of `A` is at most `c`.

This is the qualitative half of the eigenvalue count: together with the exact trace
`tsum_inner_timeBandLimitingOp_eq` (`tr A = 2WT`) and the second-moment bound
`tsum_inner_sub_norm_sq_timeBandLimitingOp_le` (`tr A − tr A² = O(log WT)`), it is what lets a
Chebyshev split localize the spectrum around the cliff at `c`.

The proof needs no eigenbasis. `prolateEigenspaceSup_invariant` and symmetry make `Vᗮ` invariant,
so `A` restricts to a compact self-adjoint operator `S` there; every eigenvalue of `S` is an
eigenvalue of `A` lying in `[0, c]` (above `c` its eigenvector would land in `V ⊓ Vᗮ = ⊥`), and for
a compact self-adjoint operator the norm *is* the spectral radius, so `‖S‖ ≤ c`. Cauchy-Schwarz
then gives the Rayleigh bound. In particular this route does *not* construct a complete orthonormal
eigenbasis of `A` — the obligation still open at `tsum_prolateEigenvalues_eq`.

Unconditional in `T` and `W`: compactness, symmetry and positivity of `A` all hold for every
parameter value, so no window or band nondegeneracy is assumed. Only `0 < c` is needed, and only to
place the point `0` of the spectrum below the bound.

Audited 2026-07-17 (independent), on the two questions this family keeps failing: is a hypothesis
doing the work, and is this the planned object or a weaker relative?

*No hypothesis carries the core.* The bundle is `hc : 0 < c` (positivity of a free threshold) and
`hv : v ∈ Vᗮ` (membership in a submodule defined outright, not asserted). Granting both hands over
no spectral fact: the substance — that compactness collapses the spectrum onto eigenvalues, and
self-adjointness turns the spectral radius back into the norm — is all discharged in the body. The
specific risk was an input amounting to *"A has a complete eigenbasis"* or *"the spectrum below `c`
is discrete"*; no such hypothesis is present, and the transitive constant graph confirms
mechanically that `orthogonalComplement_iSup_eigenspaces_eq_bot`, `HilbertBasis.mkOfOrthogonalEqBot`
and `finite_dimensional_eigenspace` are all consumed *zero* times. The docstring's claim to need no
eigenbasis is therefore machine-backed, not asserted.

*It is the planned object, `c` free.* The statement is character-for-character the plan's target,
less `hT : 0 ≤ T` and `hW : 0 < W`, which are dropped as unused — strictly stronger, nothing added.

*Sufficiency, re-derived.* Symmetry forces every eigenvalue real (`conj_eigenvalue_eq_self`), so
spanning only the *real* eigenvalues above `c` leaves no complex eigenvalue hiding in `Vᗮ` — the
gap this shape could plausibly have had, and it is closed. Two structurally different degenerate
boundaries were checked live rather than one: at `T ≤ 0` the operator collapses (`A = 0`, `V = ⊥`,
`Vᗮ = ⊤`) and the claim reads `0 ≤ c‖v‖²`, true; at `c ≥ 1` we again get `V = ⊥`
(`prolateEigenvalueSet_one_eq_empty`) and the claim reduces to `‖A‖ ≤ 1`, true. Neither refutes it.
The invariant the hypotheses pin — `v ⊥ every eigenspace above c` — is exactly the granularity the
conclusion needs, not coarser: it is what forces `spectrum (A|Vᗮ) ⊆ [0, c]`.

*Not vacuous where it matters.* For `0 < c`, `V` is finite-dimensional
(`prolateEigenspaceSup_finiteDimensional`) while `E = L²(ℝ;ℂ)` is not, so `Vᗮ ≠ ⊥` and the bound
speaks about real vectors. Unlike its siblings in this file the non-vacuity is argued, not
machine-checked by an in-tree witness lemma; nothing downstream currently depends on that witness.

*Scope — read the name with care.* This closes the plan's decisive atom, **not** leg R1 as planned.
R1 is *eigenbasis + multiplicity bridge*, and this route deliberately bypasses it: the eigenbasis
obligation stands untouched at `tsum_prolateEigenvalues_eq`. What this does deliver is the `Vᗮ`
half of the Chebyshev split (R2). The gate's premise — "the atom consumes `Spectrum.lean:443`, so
its passing certifies the count leg" — is false, so its passing certifies nothing about the
eigenbasis machinery either way.
@audit:ok -/
theorem inner_timeBandLimitingOp_le_of_mem_orthogonal
    (T W c : ℝ) (hc : 0 < c)
    {v : E} (hv : v ∈ (prolateEigenspaceSup T W c)ᗮ) :
    (inner ℂ (timeBandLimitingOp T W v) v).re ≤ c * ‖v‖ ^ 2 := by
  have hAv : ‖timeBandLimitingOp T W v‖ ≤ c * ‖v‖ := by
    have h1 := (prolateRestrict T W c).le_opNorm (⟨v, hv⟩ : ↥(prolateEigenspaceSup T W c)ᗮ)
    have h2 : ‖prolateRestrict T W c‖ * ‖(⟨v, hv⟩ : ↥(prolateEigenspaceSup T W c)ᗮ)‖ ≤ c * ‖v‖ :=
      mul_le_mul_of_nonneg_right (prolateRestrict_norm_le T W hc) (norm_nonneg _)
    calc ‖timeBandLimitingOp T W v‖
        = ‖prolateRestrict T W c (⟨v, hv⟩ : ↥(prolateEigenspaceSup T W c)ᗮ)‖ := rfl
      _ ≤ ‖prolateRestrict T W c‖ * ‖(⟨v, hv⟩ : ↥(prolateEigenspaceSup T W c)ᗮ)‖ := h1
      _ ≤ c * ‖v‖ := h2
  calc (inner ℂ (timeBandLimitingOp T W v) v).re
      ≤ ‖inner ℂ (timeBandLimitingOp T W v) v‖ := Complex.re_le_norm _
    _ ≤ ‖timeBandLimitingOp T W v‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ (c * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hAv (norm_nonneg _)
    _ = c * ‖v‖ ^ 2 := by ring

/-- V-side operator lower bound: on the span `V = prolateEigenspaceSup T W c` of the eigenspaces
above `c`, the Rayleigh quotient of `A` is at least `c`. This is the matched pair to
`inner_timeBandLimitingOp_le_of_mem_orthogonal`, which caps it by `c` on `Vᗮ`.

`V` is finite-dimensional and `A`-invariant, so the finite-dimensional spectral theorem supplies an
orthonormal eigenbasis `b` of `V` with every eigenvalue exceeding `c`. Expanding `v` along `b`,
`⟪A v, v⟫ = ∑ᵢ νᵢ ‖⟪bᵢ, v⟫‖² ≥ c ∑ᵢ ‖⟪bᵢ, v⟫‖² = c ‖v‖²` by Parseval, since every `νᵢ > c`.

Audited 2026-07-18 (independent): sorryAx-free (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`, validated against the positive control `tsum_prolateEigenvalues_eq` which does show
`sorryAx`). Both hypotheses are preconditions, not core: `hc : 0 < c` gives finite-dimensionality of
`V` (so the spectral theorem applies) and `hv : v ∈ V` scopes the claim; neither is `:= h` circular,
a `:True` slot, or a load-bearing bundle. The body proves the stated bound `c‖v‖² ≤ Re⟪Av,v⟫`, not a
weaker `0`-bound: the `hνgt` block earns `νᵢ > c` from the orthogonality argument (an eigenvector for
an eigenvalue `≤ c` would be `⊥` to every eigenspace above `c`, hence to `V ∋ bᵢ`, hence zero,
contradicting unit norm), then Parseval closes it. Not vacuous where it bites (V non-trivial below the
top eigenvalue via `exists_unit_eigenvector`); at the boundaries it degenerates to `0 ≤ c‖v‖²`, true.
@audit:ok -/
theorem le_inner_timeBandLimitingOp_of_mem (T W c : ℝ) (hc : 0 < c) {v : E}
    (hv : v ∈ prolateEigenspaceSup T W c) :
    c * ‖v‖ ^ 2 ≤ (inner ℂ (timeBandLimitingOp T W v) v).re := by
  classical
  haveI := prolateEigenspaceSup_finiteDimensional T W hc
  have hinv := prolateEigenspaceSup_invariant T W c
  have hsymV : ((timeBandLimitingOp T W : E →ₗ[ℂ] E).restrict hinv).IsSymmetric :=
    (timeBandLimitingOp_isSymmetric T W).restrict_invariant hinv
  set S : ↥(prolateEigenspaceSup T W c) →ₗ[ℂ] ↥(prolateEigenspaceSup T W c) :=
    (timeBandLimitingOp T W : E →ₗ[ℂ] E).restrict hinv with hSdef
  set d : ℕ := prolateCount T W c with hd
  have hn : Module.finrank ℂ (prolateEigenspaceSup T W c) = d := rfl
  set b := hsymV.eigenvectorBasis hn with hb
  set ν := hsymV.eigenvalues hn with hνdef
  set e : Fin d → E := fun i => ((b i : prolateEigenspaceSup T W c) : E) with he_def
  have he : Orthonormal ℂ e :=
    b.orthonormal.comp_linearIsometry (prolateEigenspaceSup T W c).subtypeₗᵢ
  have heig : ∀ i, timeBandLimitingOp T W (e i) = ((ν i : ℝ) : ℂ) • e i := fun i =>
    congrArg (Subtype.val (p := fun x : E => x ∈ prolateEigenspaceSup T W c))
      (hsymV.apply_eigenvectorBasis hn i)
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
  set w : ↥(prolateEigenspaceSup T W c) := ⟨v, hv⟩ with hw
  have hSb : ∀ i, S (b i) = (ν i : ℂ) • b i := fun i => hsymV.apply_eigenvectorBasis hn i
  -- Expand the Rayleigh quotient of `A|_V` along the eigenbasis.
  have hcoeff : inner ℂ (S w) w
      = ((∑ i, ν i * ‖(inner ℂ (b i) w : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← OrthonormalBasis.sum_inner_mul_inner b (S w) w, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : inner ℂ (S w) (b i) = (ν i : ℂ) * (starRingEnd ℂ) (inner ℂ (b i) w) := by
      rw [hsymV w (b i), hSb i, inner_smul_right w (b i) (ν i : ℂ), ← inner_conj_symm w (b i)]
    rw [h1, mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_mul]
  have hval : (inner ℂ (timeBandLimitingOp T W v) v).re
      = ∑ i, ν i * ‖(inner ℂ (b i) w : ℂ)‖ ^ 2 := by
    have hcoe : (S w : E) = timeBandLimitingOp T W v := by
      rw [hSdef, hw]; rfl
    have htrans : inner ℂ (timeBandLimitingOp T W v) v = inner ℂ (S w) w := by
      rw [Submodule.coe_inner, hcoe, hw]
    rw [htrans, hcoeff, Complex.ofReal_re]
  have hnorm : ‖v‖ ^ 2 = ∑ i, ‖(inner ℂ (b i) w : ℂ)‖ ^ 2 := by
    rw [show ‖v‖ = ‖w‖ from rfl, ← OrthonormalBasis.sum_sq_norm_inner_right b w]
  rw [hval, hnorm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_right (hνgt i).le (by positivity)

/-- **Count domination (converse min-max upper bound).** Any subspace `S` on which the Rayleigh
quotient of `A = timeBandLimitingOp T W` strictly exceeds `c` has dimension at most
`prolateCount T W c`: the number of "high-gain" directions is capped by the number of prolate
eigenvalues above `c`. Finite-dimensional min-max half of Cauchy interlacing; converse companion
to the achievability count.

Audited 2026-07-18 (independent): sorryAx-free (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`; its crux `inner_timeBandLimitingOp_le_of_mem_orthogonal` re-verified sorryAx-free too).
The hypothesis `hS` is a genuine min-max precondition — it constrains only the Rayleigh-quotient
form `c‖x‖² < Re⟪Ax,x⟫` on `S` and names no count/eigenvalue/prolate object, so it does not bundle
the conclusion `finrank S ≤ prolateCount`. The body does real work: the strict form on `S` collides
with the `≤ c` bound on `Vᗮ` (crux) to force `S ∩ Vᗮ = {0}`, whence orthogonal projection injects
`S ↪ V` and `finrank S ≤ finrank V = prolateCount`. Not vacuous (a genuine `≤` on `finrank S`, not
`0 ≤ _` or `finrank ⊥`).
@audit:ok -/
theorem finrank_le_prolateCount_of_form_gt (T W : ℝ) {c : ℝ} (hc : 0 < c)
    (S : Submodule ℂ E)
    (hS : ∀ x ∈ S, x ≠ 0 → c * ‖x‖ ^ 2 < (inner ℂ (timeBandLimitingOp T W x) x).re) :
    Module.finrank ℂ S ≤ prolateCount T W c := by
  haveI := prolateEigenspaceSup_finiteDimensional T W hc
  set V := prolateEigenspaceSup T W c with hV
  -- On `S ∩ Vᗮ` the two Rayleigh bounds `> c` and `≤ c` collide, so it is `{0}`.
  have hzero : ∀ x ∈ S, x ∈ Vᗮ → x = 0 := fun x hxS hxV => by
    by_contra hx0
    exact absurd (inner_timeBandLimitingOp_le_of_mem_orthogonal T W c hc hxV)
      (not_le.mpr (hS x hxS hx0))
  -- The orthogonal projection `E → V`, restricted to `S`, has trivial kernel, hence injects `S ↪ V`.
  set f : ↥S →ₗ[ℂ] ↥V := (V.orthogonalProjectionOnto : E →L[ℂ] ↥V).toLinearMap ∘ₗ S.subtype with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxS⟩ hfx
    have hxV : x ∈ Vᗮ := Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hfx
    exact Subtype.ext (hzero x hxS hxV)
  calc Module.finrank ℂ S ≤ Module.finrank ℂ V :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = prolateCount T W c := rfl

-- **Operator-side Bessel domination.** For a band-limited `g` and an orthonormal family `φ` of
-- time-limited vectors, the Bessel sum `∑ᵢ ‖⟪g, φᵢ⟫‖²` is dominated by the operator quadratic form
-- `Re⟪A g, g⟫`. Since `P_W g = g` and `Q_T φᵢ = φᵢ`, the frame coefficient `⟪g, φᵢ⟫ = ⟪φᵢ, Q_T g⟫`,
-- so Bessel against `Q_T g` caps the sum by `‖Q_T g‖² = Re⟪A g, g⟫`. This feeds
-- `finrank_le_prolateCount_of_form_gt`: an arbitrary code's Gram spectrum is dominated by the
-- operator spectrum. Pure complex `E`-space, no real↔E bridge.
lemma frame_form_le_op_form (T W : ℝ) {k : ℕ} (φ : Fin k → E)
    (h_on : Orthonormal ℂ φ) (h_tl : ∀ i, φ i ∈ timeLimitSubspace T)
    (g : E) (hg : g ∈ bandLimitSubspace W) :
    ∑ i, ‖inner ℂ g (φ i)‖ ^ 2 ≤ (inner ℂ (timeBandLimitingOp T W g) g).re := by
  classical
  have hQfix : ∀ i, (timeLimitSubspace T).starProjection (φ i) = φ i := fun i =>
    Submodule.starProjection_eq_self_iff.mpr (h_tl i)
  have hPg : (bandLimitSubspace W).starProjection g = g :=
    Submodule.starProjection_eq_self_iff.mpr hg
  have hQidem : (timeLimitSubspace T).starProjection ((timeLimitSubspace T).starProjection g)
      = (timeLimitSubspace T).starProjection g :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  -- `A g = P_W (Q_T g)` since `P_W g = g`.
  have hAg : timeBandLimitingOp T W g
      = (bandLimitSubspace W).starProjection ((timeLimitSubspace T).starProjection g) := by
    simp only [timeBandLimitingOp, ContinuousLinearMap.comp_apply, hPg]
  -- The operator quadratic form is the squared norm of `Q_T g`.
  have hinner : inner ℂ (timeBandLimitingOp T W g) g
      = inner ℂ ((timeLimitSubspace T).starProjection g)
          ((timeLimitSubspace T).starProjection g) := by
    rw [hAg, Submodule.inner_starProjection_left_eq_right, hPg]
    conv_lhs => rw [← hQidem]
    rw [Submodule.inner_starProjection_left_eq_right]
  have hform : (inner ℂ (timeBandLimitingOp T W g) g).re
      = ‖(timeLimitSubspace T).starProjection g‖ ^ 2 := by
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  -- Each frame coefficient is a coefficient against `Q_T g`.
  have hLHS : ∀ i, ‖inner ℂ g (φ i)‖ ^ 2
      = ‖inner ℂ (φ i) ((timeLimitSubspace T).starProjection g)‖ ^ 2 := by
    intro i
    have hi : inner ℂ (φ i) g
        = inner ℂ (φ i) ((timeLimitSubspace T).starProjection g) := by
      conv_lhs => rw [← hQfix i]
      rw [Submodule.inner_starProjection_left_eq_right]
    rw [norm_inner_symm g (φ i), hi]
  rw [hform]
  calc ∑ i, ‖inner ℂ g (φ i)‖ ^ 2
      = ∑ i, ‖inner ℂ (φ i) ((timeLimitSubspace T).starProjection g)‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => hLHS i)
    _ ≤ ‖(timeLimitSubspace T).starProjection g‖ ^ 2 :=
        h_on.sum_inner_products_le (x := (timeLimitSubspace T).starProjection g)
          (s := Finset.univ)

/-- Markov bound on the eigenvalue counting function: at most `2WT/c` eigenvalues of the
time-and-band limiting operator exceed `c`.

The span `prolateEigenspaceSup T W c` of the eigenspaces above `c` is `A`-invariant and
finite-dimensional, so the finite-dimensional spectral theorem supplies an orthonormal eigenbasis of
it; every one of its eigenvalues exceeds `c` (an eigenvector for an eigenvalue `≤ c` would be
orthogonal to every eigenspace above `c`, hence to the span containing it, hence zero). Feeding that
basis to `sum_inner_timeBandLimitingOp_le` gives `c · #{λ > c} ≤ ∑ λᵢ ≤ 2WT`.

Scope (audited 2026-07-17): read as a count this says `#{λ > c} ≤ 2WT/c`, which *overcounts* by the
factor `1/c` and has no vanishing relative error. It is therefore weaker than the sharp upper half
`#{λ > c} ≤ 2WT + O(log WT)`, and weaker still than the two-sided concentration that
`wall:nyquist-2w-dof` names. Neither wall consumer is unblocked by it:
`contAwgn_ge_shannonHartley` needs the *lower* half, and `contAwgn_eq_shannonHartley`, being an
equality, needs both halves sharply.

Non-vacuity is machine-checked rather than assumed: for `0 < T`, `0 < W`,
`exists_pos_hasEigenvalue` yields an eigenvalue `μ > 0`, so `prolateCount T W (μ/2) ≥ 1` and the
bound bites (`μ/2 ≤ 2WT`) instead of holding by `0 ≤ 2WT`.
@audit:ok
@audit:retract-candidate(superseded by `prolateCount_le` for the family's purpose; 0 consumers as of
2026-07-17, machine-checked via `scripts/dep_consumers.sh`. Caveat for the owner making the call:
this is *asymptotic* supersession, not pointwise — `2WT/c` is strictly tighter than
`2WT + (2+log(1+2WT))/c` for small `WT` (e.g. `2WT ≤ 8` at `c = 1/2`), so the two are incomparable
as bounds. What makes it retractable is that the family's figure of merit is the `T → ∞` density,
where this bound gives `2W/c` and `prolateCount_le` gives `2W`.) -/
theorem prolateCount_mul_le (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) {c : ℝ} (hc : 0 < c) :
    c * (prolateCount T W c : ℝ) ≤ 2 * W * T := by
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
  -- Each basis vector is an eigenvector of `A` in the ambient space.
  have heig : ∀ i, timeBandLimitingOp T W (e i) = ((ν i : ℝ) : ℂ) • e i := by
    intro i
    have h := hsymV.apply_eigenvectorBasis hn i
    have h' := congrArg (Subtype.val (p := fun x : E => x ∈ prolateEigenspaceSup T W c)) h
    simp only [LinearMap.coe_restrict_apply, Submodule.coe_smul,
      ContinuousLinearMap.coe_coe] at h'
    exact h'
  -- Every eigenvalue of the restriction exceeds `c`.
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
  -- The trace along that basis is the eigenvalue sum, and the atom caps it by `2WT`.
  have hval : ∀ i, (inner ℂ (timeBandLimitingOp T W (e i)) (e i)).re = ν i := by
    intro i
    rw [heig i, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, he.1 i]
    simp
  have hsum := sum_inner_timeBandLimitingOp_le T W hT hW he
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hval i)] at hsum
  have hlow : c * (d : ℝ) ≤ ∑ i, ν i := by
    calc c * (d : ℝ) = ∑ _i : Fin d, c := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i, ν i := Finset.sum_le_sum fun i _ => (hνgt i).le
  linarith

/-! ### The complete eigen-Hilbert basis and the trace transport -/

/-- Every eigenspace of the compact operator `A = timeBandLimitingOp T W` is complete: it is the
kernel of the continuous map `A − μ•1`, hence closed in the complete space `E`. Uniform in `μ`
(both the finite-dimensional eigenspaces for `μ ≠ 0` and the possibly infinite-dimensional kernel),
which is what lets the per-eigenspace Hilbert bases be chosen without a dimension case split. -/
instance prolate_eigenspace_completeSpace (T W : ℝ) (μ : ℂ) :
    CompleteSpace (Module.End.eigenspace (prolateEnd T W) μ) := by
  haveI hclosed : IsClosed (Module.End.eigenspace (prolateEnd T W) μ : Set E) := by
    have hset : (Module.End.eigenspace (prolateEnd T W) μ : Set E)
        = {x : E | (timeBandLimitingOp T W - μ • ContinuousLinearMap.id ℂ E) x = 0} := by
      ext x
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Set.mem_setOf_eq,
        sub_apply, smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
      rfl
    rw [hset]
    exact isClosed_eq (ContinuousLinearMap.continuous _) continuous_const
  infer_instance

/-- **P1 — the complete eigen-Hilbert basis (gateway).** `A = timeBandLimitingOp T W` is compact and
self-adjoint, so its eigenspaces are total (`orthogonalComplement_iSup_eigenspaces_eq_bot`).
Collating a Hilbert basis of each eigenspace (`exists_hilbertBasis`, uniform in `μ`) over
`Σ μ : ℂ, …` and gluing by `mkOfOrthogonalEqBot` yields a complete orthonormal eigenbasis of `E`,
with real nonnegative eigenvalues, whose vectors with eigenvalue above `c` span the high eigenspace
`prolateEigenspaceSup T W c`.

Independent honesty audit 2026-07-18 (`7a08b9c2`): no hypotheses; the whole construction is in the
body. All three conjuncts are genuinely proven — the eigen-relation and nonnegativity pointwise, and
the span identity by a real two-sided `le_antisymm` (not `:True`). The third conjunct is non-vacuous:
were `{i | c < lam i}` empty for all `c > 0`, nonnegativity would force `lam ≡ 0`, contradicting P2's
`∑ lam = 2WT ≠ 0` for `0 < W`, `0 < T`. sorryAx-free (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`).
@audit:ok -/
theorem exists_eigen_hilbertBasis (T W : ℝ) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ E) (lam : ι → ℝ),
      (∀ i, timeBandLimitingOp T W (b i) = (lam i : ℂ) • b i) ∧
      (∀ i, 0 ≤ lam i) ∧
      (∀ c : ℝ, 0 < c →
        prolateEigenspaceSup T W c = Submodule.span ℂ (b '' {i | c < lam i})) := by
  classical
  -- The eigenspaces of `A` form an orthogonal family.
  have hof : OrthogonalFamily ℂ (fun μ : ℂ => Module.End.eigenspace (prolateEnd T W) μ)
      (fun μ => (Module.End.eigenspace (prolateEnd T W) μ).subtypeₗᵢ) :=
    (timeBandLimitingOp_isSymmetric T W).orthogonalFamily_eigenspaces
  -- A Hilbert basis of each eigenspace, uniform in `μ` (completeness from the instance above).
  choose w bμ hbμ using
    fun μ : ℂ => exists_hilbertBasis ℂ (Module.End.eigenspace (prolateEnd T W) μ)
  -- Collate them into one orthonormal family over `Σ μ, (per-eigenspace index)`.
  have hv0 := hof.orthonormal_sigma_orthonormal fun μ => (bμ μ).orthonormal
  set v : (Σ μ : ℂ, ↥(w μ)) → E :=
    fun a => (Module.End.eigenspace (prolateEnd T W) a.1).subtypeₗᵢ (bμ a.1 a.2) with hvdef
  have hv : Orthonormal ℂ v := hv0
  -- Totality: a vector orthogonal to every collated basis vector is orthogonal to every eigenspace,
  -- hence zero by the compact self-adjoint spectral theorem.
  have htot : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    have hspec : (⨆ μ : ℂ, Module.End.eigenspace (prolateEnd T W) μ)ᗮ = ⊥ :=
      ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
        (timeBandLimitingOp_isCompact T W) (timeBandLimitingOp_isSymmetric T W)
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hperp : ∀ μ : ℂ, x ∈ (Module.End.eigenspace (prolateEnd T W) μ)ᗮ := by
      intro μ
      rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
      have hz : ∀ k : ↥(w μ),
          inner ℂ ((bμ μ k : ↥(Module.End.eigenspace (prolateEnd T W) μ)) : E) x = (0 : ℂ) :=
        fun k => (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨⟨μ, k⟩, rfl⟩)
      have hsum := (bμ μ).hasSum_orthogonalProjectionOnto x
      simp only [hz, zero_smul] at hsum
      exact hsum.unique hasSum_zero
    have hxsup : x ∈ (⨆ μ : ℂ, Module.End.eigenspace (prolateEnd T W) μ)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.iSup_induction' with
      | mem μ y hy => exact (Submodule.mem_orthogonal _ _).mp (hperp μ) y hy
      | zero => simp
      | add y z _ _ ihy ihz => rw [inner_add_left, ihy, ihz, add_zero]
    rw [hspec] at hxsup
    simpa using hxsup
  -- Glue into a Hilbert basis of `E`.
  set b := HilbertBasis.mkOfOrthogonalEqBot hv htot with hb
  have hbv : ⇑b = v := HilbertBasis.coe_mkOfOrthogonalEqBot hv htot
  -- Each glued vector lies in the eigenspace indexed by its first coordinate.
  have hmem : ∀ i, b i ∈ Module.End.eigenspace (prolateEnd T W) i.1 := by
    intro i
    rw [congrFun hbv i]
    exact SetLike.coe_mem (bμ i.1 i.2)
  have heigC : ∀ i, timeBandLimitingOp T W (b i) = i.1 • b i := fun i =>
    Module.End.mem_eigenspace_iff.mp (hmem i)
  -- Each glued vector is a unit vector, so its eigenvalue is real and nonnegative.
  have hreal : ∀ i : (Σ μ : ℂ, ↥(w μ)), (i.1 : ℂ) = ((i.1.re : ℝ) : ℂ) ∧ 0 ≤ i.1.re := by
    intro i
    have hne : b i ≠ 0 := by
      intro h
      have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [h, norm_zero] at h1
      exact one_ne_zero h1.symm
    have hev : (prolateEnd T W).HasEigenvalue i.1 :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (heigC i), hne⟩
    have hconj := (timeBandLimitingOp_isSymmetric T W).conj_eigenvalue_eq_self hev
    have him : i.1.im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hre : (i.1 : ℂ) = ((i.1.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    refine ⟨hre, ?_⟩
    have hev' : (prolateEnd T W).HasEigenvalue ((i.1.re : ℝ) : ℂ) := hre ▸ hev
    apply eigenvalue_nonneg_of_nonneg (𝕜 := ℂ) (T := (prolateEnd T W)) hev'
    intro x
    have h := (timeBandLimitingOp_isPositive T W).inner_nonneg_right x
    have := (Complex.le_def.mp h).1
    simpa using this
  -- Every glued vector is a genuine eigenvector, so it spans a genuine eigenvalue's eigenspace.
  have hev : ∀ i : (Σ μ : ℂ, ↥(w μ)), (prolateEnd T W).HasEigenvalue i.1 := by
    intro i
    have hne : b i ≠ 0 := by
      intro h
      have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [h, norm_zero] at h1
      exact one_ne_zero h1.symm
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (heigC i), hne⟩
  -- Each nonzero eigenspace is finite-dimensional, so the coerced per-eigenspace basis spans it.
  have hspanμ : ∀ μ : ℂ, μ ≠ 0 →
      Submodule.span ℂ (Set.range (fun k : ↥(w μ) =>
        ((bμ μ k : ↥(Module.End.eigenspace (prolateEnd T W) μ)) : E)))
        = Module.End.eigenspace (prolateEnd T W) μ := by
    intro μ hμ0
    haveI : FiniteDimensional ℂ ↥(Module.End.eigenspace (prolateEnd T W) μ) :=
      ContinuousLinearMap.finite_dimensional_eigenspace (timeBandLimitingOp_isCompact T W) μ hμ0
    have hcl := (Submodule.span ℂ (Set.range (bμ μ))).closed_of_finiteDimensional
    have h1 : Submodule.span ℂ (Set.range (bμ μ)) = ⊤ := by
      rw [← hcl.submodule_topologicalClosure_eq, (bμ μ).dense_span]
    have hrange : Set.range (fun k : ↥(w μ) =>
        ((bμ μ k : ↥(Module.End.eigenspace (prolateEnd T W) μ)) : E))
        = (Module.End.eigenspace (prolateEnd T W) μ).subtype '' Set.range (bμ μ) := by
      rw [← Set.range_comp]; rfl
    rw [hrange, Submodule.span_image, h1, Submodule.map_top, Submodule.range_subtype]
  refine ⟨_, b, fun a => a.1.re, ?_, fun i => (hreal i).2, ?_⟩
  · intro i
    rw [heigC i]
    congr 1
    exact (hreal i).1
  · intro c hc
    apply le_antisymm
    · -- `prolateEigenspaceSup T W c ≤ span of the high eigenbasis vectors`
      rw [prolateEigenspaceSup]
      refine iSup₂_le fun ν hν => ?_
      have hν0 : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hc.trans hν.1))
      rw [← hspanμ (ν : ℂ) hν0]
      apply Submodule.span_mono
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨(ν : ℂ), k⟩, ?_, congrFun hbv ⟨(ν : ℂ), k⟩⟩
      show c < ((ν : ℂ)).re
      rw [Complex.ofReal_re]
      exact hν.1
    · -- `span of the high eigenbasis vectors ≤ prolateEigenspaceSup T W c`
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [prolateEigenspaceSup]
      have hi' : c < i.1.re := hi
      have hmemν : (i.1.re : ℝ) ∈ prolateEigenvalueSet T W c :=
        ⟨hi', (hreal i).1 ▸ hev i⟩
      refine Submodule.mem_iSup_of_mem (i.1.re) (Submodule.mem_iSup_of_mem hmemν ?_)
      have hbe := hmem i
      rwa [(hreal i).1] at hbe

/-- **P2 — trace transport.** The eigenvalue sum along the complete eigenbasis equals `2WT`, by
feeding the eigenbasis to `tsum_inner_timeBandLimitingOp_eq` and simplifying each Rayleigh quotient
`⟪A bᵢ, bᵢ⟫.re` to its eigenvalue `lam i`. -/
theorem tsum_eigen_eq_two_mul (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W)
    {ι : Type} (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (heig : ∀ i, timeBandLimitingOp T W (b i) = (lam i : ℂ) • b i) :
    ∑' i, lam i = 2 * W * T := by
  have hval : ∀ i, (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re = lam i := by
    intro i
    rw [heig i, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K,
      b.orthonormal.1 i]
    simp
  calc ∑' i, lam i
      = ∑' i, (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re :=
        tsum_congr fun i => (hval i).symm
    _ = 2 * W * T := tsum_inner_timeBandLimitingOp_eq T W hT hW b

/-- **P3a-fin.** For `t > 0`, only finitely many eigenbasis vectors have eigenvalue above `t`: they
are orthonormal (hence linearly independent) and lie in the finite-dimensional high eigenspace
`prolateEigenspaceSup T W t`. -/
theorem setOf_lt_lam_finite (T W : ℝ) {ι : Type} (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (hspan : ∀ c : ℝ, 0 < c →
      prolateEigenspaceSup T W c = Submodule.span ℂ (b '' {i | c < lam i}))
    {t : ℝ} (ht : 0 < t) : {i | t < lam i}.Finite := by
  haveI : FiniteDimensional ℂ (prolateEigenspaceSup T W t) :=
    prolateEigenspaceSup_finiteDimensional T W ht
  have hmem : ∀ i : ↥{i | t < lam i}, b ↑i ∈ prolateEigenspaceSup T W t := by
    intro i
    rw [hspan t ht]
    exact Submodule.subset_span ⟨↑i, i.2, rfl⟩
  have hli : LinearIndependent ℂ
      (fun i : ↥{i | t < lam i} => (⟨b ↑i, hmem i⟩ : ↥(prolateEigenspaceSup T W t))) := by
    apply LinearIndependent.of_comp (prolateEigenspaceSup T W t).subtype
    exact (b.orthonormal.comp _ Subtype.val_injective).linearIndependent
  exact Set.finite_coe_iff.mp hli.finite

/-- **P3a.** The super-level count of the eigenbasis eigenvalues equals `prolateCount`: the vectors
with eigenvalue above `t` form an orthonormal basis of `prolateEigenspaceSup T W t`, so their number
is its `finrank`. -/
theorem ncard_setOf_lt_lam (T W : ℝ) {ι : Type} (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (hspan : ∀ c : ℝ, 0 < c →
      prolateEigenspaceSup T W c = Submodule.span ℂ (b '' {i | c < lam i}))
    {t : ℝ} (ht : 0 < t) : {i | t < lam i}.ncard = prolateCount T W t := by
  haveI : Fintype ↥{i | t < lam i} := (setOf_lt_lam_finite T W b lam hspan ht).fintype
  have hli : LinearIndependent ℂ (fun i : ↥{i | t < lam i} => b ↑i) :=
    (b.orthonormal.comp _ Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun i : ↥{i | t < lam i} => b ↑i) = b '' {i | t < lam i} :=
    (Set.image_eq_range b {i | t < lam i}).symm
  simp only [prolateCount]
  rw [hspan t ht, ← hrange, finrank_span_eq_card hli, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]

/-- **P3b.** For `t > 0`, the decreasing enumeration exceeds `t` exactly on an initial segment
`{0, …, prolateCount T W t − 1}`. This is the generalized-inverse duality
`t < prolateEigenvalues T W n ↔ n < prolateCount T W t`, packaged as a set identity. The `←`
direction uses the finiteness of the eigenvalue set above `t` to produce a spectral gap just above
`t`, so the counting function is locally constant there and the infimum defining
`prolateEigenvalues` clears `t` strictly. -/
theorem setOf_lt_prolateEigenvalues_eq_Iio (T W : ℝ) {t : ℝ} (ht : 0 < t) :
    {n | t < prolateEigenvalues T W n} = Set.Iio (prolateCount T W t) := by
  have hiff : ∀ n, t < prolateEigenvalues T W n ↔ n < prolateCount T W t := by
    intro n
    constructor
    · -- `t < λₙ → n < count`: else `count ≤ n` puts `λₙ ≤ t`.
      intro hlt
      by_contra hle
      push Not at hle
      exact absurd (prolateEigenvalues_le_of_count_le T W ht hle) (not_le.mpr hlt)
    · -- `n < count → t < λₙ`: a spectral gap just above `t` clears the infimum strictly.
      intro hn
      have hFfin : (prolateEigenvalueSet T W t).Finite := prolateEigenvalueSet_finite T W ht
      have hFne : (prolateEigenvalueSet T W t).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have hbot : prolateEigenspaceSup T W t = ⊥ := by
          rw [prolateEigenspaceSup, hemp]; simp
        have : prolateCount T W t = 0 := by rw [prolateCount, hbot]; simp
        omega
      -- The least eigenvalue above `t` is `> t` and bounds `prolateEigenvalues n` from below.
      have hmem : sInf (prolateEigenvalueSet T W t) ∈ prolateEigenvalueSet T W t :=
        hFne.csInf_mem hFfin
      have hbdd : BddBelow (prolateEigenvalueSet T W t) := ⟨t, fun x hx => hx.1.le⟩
      have hlb : ∀ c ∈ {c : ℝ | 0 < c ∧ prolateCount T W c ≤ n},
          sInf (prolateEigenvalueSet T W t) ≤ c := by
        rintro c ⟨hc0, hcn⟩
        by_contra hlt
        push Not at hlt
        rcases le_or_gt c t with hct | htc
        · exact absurd (le_trans (prolateCount_antitone T W hc0 hct) hcn) (by omega)
        · have hseteq : prolateEigenvalueSet T W c = prolateEigenvalueSet T W t := by
            refine Set.Subset.antisymm (prolateEigenvalueSet_subset T W htc.le) fun ev hev => ?_
            exact ⟨lt_of_lt_of_le hlt (csInf_le hbdd hev), hev.2⟩
          have : prolateCount T W c = prolateCount T W t := by
            rw [prolateCount, prolateCount, prolateEigenspaceSup, prolateEigenspaceSup, hseteq]
          omega
      have hle : sInf (prolateEigenvalueSet T W t) ≤ prolateEigenvalues T W n :=
        le_csInf (prolateEigenvalues_setOf_nonempty T W n) hlb
      exact lt_of_lt_of_le hmem.1 hle
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_Iio]
  exact hiff n

/-- **P3 — multiplicity bridge.** The eigenvalue sum along the eigenbasis equals the sum over the
decreasing enumeration `prolateEigenvalues`, since both nonnegative families share the super-level
counts `#{· > c} = prolateCount T W c` (the eigenbasis vectors above `c` span
`prolateEigenspaceSup T W c`, whose `finrank` *is* `prolateCount` — `ncard_setOf_lt_lam`; the
enumeration exceeds `c` on the initial segment `{0, …, prolateCount T W c − 1}` —
`setOf_lt_prolateEigenvalues_eq_Iio`), transported through the layer-cake identity
`lintegral_eq_lintegral_meas_lt`: both `ℝ≥0∞` sums equal `∫⁻ t ∈ Ioi 0, prolateCount T W t`.
Summability of both families (`summable_of_sum_le` from the Bessel bound, then `ENNReal.summable_toReal`)
converts the `ℝ≥0∞` equality back to `ℝ`.

Independent honesty audit 2026-07-18 (`7a08b9c2`): `heig`/`hnn`/`hspan` are structural preconditions
describing an abstract eigenbasis, not the conclusion in disguise — the multiplicity core (layer-cake
`lintegral_eq_lintegral_meas_lt`, Bessel summability, the `Measure.count` distribution functions) is
carried by the body. They are discharged by feeding `exists_eigen_hilbertBasis`'s output at the
headline `tsum_prolateEigenvalues_eq`, which therefore assumes none of them (no load-bearing bundle).
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
@audit:ok -/
theorem tsum_eigen_eq_tsum_prolateEigenvalues (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W)
    {ι : Type} (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (heig : ∀ i, timeBandLimitingOp T W (b i) = (lam i : ℂ) • b i)
    (hnn : ∀ i, 0 ≤ lam i)
    (hspan : ∀ c : ℝ, 0 < c →
      prolateEigenspaceSup T W c = Submodule.span ℂ (b '' {i | c < lam i})) :
    ∑' i, lam i = ∑' n, prolateEigenvalues T W n := by
  classical
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  -- Each Rayleigh quotient along the eigenbasis is its eigenvalue.
  have hval : ∀ i, (inner ℂ (timeBandLimitingOp T W (b i)) (b i)).re = lam i := by
    intro i
    rw [heig i, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K,
      b.orthonormal.1 i]
    simp
  -- Summability of `lam` from the Bessel bound `∑ lam ≤ 2WT` on every finite subfamily.
  have hsummL : Summable lam := by
    refine summable_of_sum_le (fun i => hnn i) (c := 2 * W * T) fun u => ?_
    have e : ↥u ≃ Fin u.card := Fintype.equivFinOfCardEq (Fintype.card_coe u)
    have hinj : Function.Injective (fun k : Fin u.card => ((e.symm k : ↥u) : ι)) :=
      Subtype.val_injective.comp e.symm.injective
    have hbes := sum_inner_timeBandLimitingOp_le T W hT hW (b.orthonormal.comp _ hinj)
    simp only [Function.comp_apply] at hbes
    have heq : (∑ k, (inner ℂ (timeBandLimitingOp T W (b ((e.symm k : ↥u) : ι)))
        (b ((e.symm k : ↥u) : ι))).re) = ∑ k : Fin u.card, lam ((e.symm k : ↥u) : ι) :=
      Finset.sum_congr rfl fun k _ => hval ((e.symm k : ↥u) : ι)
    rw [heq] at hbes
    calc ∑ i ∈ u, lam i = ∑ i : ↥u, lam ↑i := (Finset.sum_coe_sort u lam).symm
      _ = ∑ k : Fin u.card, lam ((e.symm k : ↥u) : ι) :=
          (Equiv.sum_comp e.symm (fun i : ↥u => lam ↑i)).symm
      _ ≤ 2 * W * T := hbes
  -- Both distribution functions equal `prolateCount T W t` for `t > 0`.
  have hLcount : ∀ t : ℝ, 0 < t →
      Measure.count {i | t < lam i} = (prolateCount T W t : ℝ≥0∞) := by
    intro t ht
    have hfin := setOf_lt_lam_finite T W b lam hspan ht
    rw [Measure.count_apply_finite {i | t < lam i} hfin,
      ← Set.ncard_eq_toFinset_card {i | t < lam i} hfin, ncard_setOf_lt_lam T W b lam hspan ht]
  have hRcount : ∀ t : ℝ, 0 < t →
      Measure.count {n | t < prolateEigenvalues T W n} = (prolateCount T W t : ℝ≥0∞) := by
    intro t ht
    rw [setOf_lt_prolateEigenvalues_eq_Iio T W ht, ← Finset.coe_range,
      Measure.count_apply_finset, Finset.card_range]
  -- Layer cake: both `ℝ≥0∞` sums equal `∫⁻ t ∈ Ioi 0, prolateCount T W t`.
  have hLint : (∑' i, ENNReal.ofReal (lam i))
      = ∫⁻ t in Set.Ioi (0 : ℝ), (prolateCount T W t : ℝ≥0∞) := by
    rw [← lintegral_count' (f := fun i => ENNReal.ofReal (lam i)) measurable_from_top,
      lintegral_eq_lintegral_meas_lt Measure.count (ae_of_all _ fun i => hnn i)
        measurable_from_top.aemeasurable]
    exact setLIntegral_congr_fun measurableSet_Ioi fun t ht => hLcount t ht
  have hRint : (∑' n, ENNReal.ofReal (prolateEigenvalues T W n))
      = ∫⁻ t in Set.Ioi (0 : ℝ), (prolateCount T W t : ℝ≥0∞) := by
    rw [← lintegral_count (fun n => ENNReal.ofReal (prolateEigenvalues T W n)),
      lintegral_eq_lintegral_meas_lt Measure.count
        (ae_of_all _ fun n => prolateEigenvalues_nonneg T W n)
        (measurable_of_countable _).aemeasurable]
    exact setLIntegral_congr_fun measurableSet_Ioi fun t ht => hRcount t ht
  have hkey : (∑' i, ENNReal.ofReal (lam i))
      = ∑' n, ENNReal.ofReal (prolateEigenvalues T W n) := by rw [hLint, hRint]
  -- Transfer the identity back to `ℝ`.
  have hLfin : (∑' i, ENNReal.ofReal (lam i)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsummL]; exact ENNReal.ofReal_ne_top
  have hsummR : Summable (prolateEigenvalues T W) := by
    have hne : (∑' n, ENNReal.ofReal (prolateEigenvalues T W n)) ≠ ⊤ := hkey ▸ hLfin
    refine (ENNReal.summable_toReal hne).congr fun n => ?_
    rw [ENNReal.toReal_ofReal (prolateEigenvalues_nonneg T W n)]
  have hfinal : ENNReal.ofReal (∑' i, lam i)
      = ENNReal.ofReal (∑' n, prolateEigenvalues T W n) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsummL,
      ENNReal.ofReal_tsum_of_nonneg (fun n => prolateEigenvalues_nonneg T W n) hsummR, hkey]
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hnn)
    (tsum_nonneg fun n => prolateEigenvalues_nonneg T W n)).mp hfinal

/-- The trace identity `tsum_inner_timeBandLimitingOp_eq`, transported onto the decreasing
eigenvalue enumeration: `∑ₙ λₙ = 2WT` (the exact first spectral moment of `A = timeBandLimitingOp`).

Proof-done, sorryAx-free, and independent of the `wall:nyquist-2w-dof` concentration. It composes
three pieces, each proved from assets already in Mathlib / this file:

1. **P1 (`exists_eigen_hilbertBasis`)** — a complete orthonormal *eigen*basis of `A`. The compact
   self-adjoint spectral theorem (`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`:
   the eigenspaces are total) glues per-eigenspace Hilbert bases (`exists_hilbertBasis`, uniform in
   `μ`) into one orthonormal family via `HilbertBasis.mkOfOrthogonalEqBot`, with real nonnegative
   eigenvalues whose above-`c` vectors span `prolateEigenspaceSup T W c`.
2. **P2 (`tsum_eigen_eq_two_mul`)** — feeding that eigenbasis to the trace identity gives `∑ λ = 2WT`.
3. **P3 (`tsum_eigen_eq_tsum_prolateEigenvalues`)** — the multiplicity bridge to `prolateEigenvalues`,
   the generalized inverse `sInf {c > 0 | prolateCount T W c ≤ n}` of the counting function: both
   nonnegative families share the super-level counts `prolateCount T W t`, so a layer-cake identity
   equates their sums.

None of this is the Landau-Pollak-Slepian asymptotics in `WT`; it is `c`-by-`c` structure for a
compact positive operator. This exact first moment is off the Shannon-Hartley converse path (a bonus:
the converse lands via count domination `bandGramReal_high_count_le`, not this identity).

Independent honesty audit 2026-07-18 (`7a08b9c2`): unconditional — the body `obtain`s the eigenbasis
data `heig`/`hnn`/`hspan` from the hypothesis-free `exists_eigen_hilbertBasis`, so it discharges (does
not assume) the P2/P3 preconditions. The only hypotheses `hT : 0 ≤ T`, `hW : 0 < W` are domain
regularity (matching the already-audited `tsum_inner_timeBandLimitingOp_eq`), fixing the nonnegative
value `2WT`. No load-bearing hypothesis, no circularity. sorryAx-free (`#print axioms` = `[propext,
Classical.choice, Quot.sound]`).
@audit:ok -/
theorem tsum_prolateEigenvalues_eq (T W : ℝ) (hT : 0 ≤ T) (hW : 0 < W) :
    ∑' n, prolateEigenvalues T W n = 2 * W * T := by
  obtain ⟨ι, b, lam, heig, hnn, hspan⟩ := exists_eigen_hilbertBasis T W
  have h2 := tsum_eigen_eq_two_mul T W hT hW b lam heig
  have h3 := tsum_eigen_eq_tsum_prolateEigenvalues T W hT hW b lam heig hnn hspan
  rw [← h3, h2]

end TraceBound

end InformationTheory.Shannon.TimeBandLimiting
