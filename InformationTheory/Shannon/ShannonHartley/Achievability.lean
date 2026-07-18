import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import InformationTheory.Shannon.ShannonHartley.Operational
import InformationTheory.Shannon.NormalizedSinc
import InformationTheory.Shannon.WhittakerShannon
import InformationTheory.Shannon.AWGN.Achievability
import InformationTheory.Shannon.AWGN.ChannelMeasurability
import InformationTheory.Shannon.AWGN.Converse
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley: achievability (Cover-Thomas Ch. 9.6, Phase 3)

The `≥` half of the operational Shannon-Hartley sandwich,

    `bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P`

(`contAwgn_ge_shannonHartley`), together with the boundedness obligation
`contAwgnMaxMessages_bddAbove` that the operational `sSup` needs in order not to collapse to
junk-`0`.

The two have different characters, and the split is the point. Boundedness is *wall-independent*:
Bessel's inequality against the orthonormal `ContAwgnCode.testFn` caps the observed energy by
`T·P` uniformly in the observation count, which is enough for `BddAbove` but only enough for the
crude rate `P/N₀`. Achievability at the *exact* constant is not wall-independent: it needs the
`≈ 2WT` degrees-of-freedom count (the `nyquist-2w-dof` wall, Leg E), because the test family must
recover near-unit gain on `≈ 2WT` dimensions. See the two declarations for detail.

## The synthesis bridge

`synthSignal T n a` reconstructs a band-limited signal interpolating the sample values
`a : Fin n → ℝ` at the grid `t_i = i·(T/n)`; it is how the band-limited codewords of a
`ContAwgnCode` get built from a discrete `awgn_achievability` codebook. Its three properties power
the reduction:

* **(ii) interpolation exactness** — `synthSignal T n a (j·(T/n)) = a j`
  (`synthSignal_sample`).
* **(i) band-limitedness** — `IsBandlimited (synthSignal T n a) W` when `n ≤ 2WT`
  (`synthSignal_bandlimited`): each shifted `sincN(·/Δ)` has spectrum supported in
  `[-1/(2Δ), 1/(2Δ)] = [-n/(2T), n/(2T)] ⊆ [-W, W]`.
* **(iii) Parseval energy** — `∫ t, (synthSignal T n a t)² = (T/n)·∑ᵢ (a i)²`
  (`synthSignal_energy`), an equality on the *whole line*, which is exactly the shape
  `ContAwgnCode.encoder_power` asks for: with `a = √(n/T)·c` it reads `∑ᵢ cᵢ² ≤ T·P`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1 (achievability).
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology FourierTransform ComplexInnerProductSpace
open InformationTheory.Shannon.NormalizedSinc

/-! ## §A — Sinc synthesis -/

/-- Sinc synthesis at grid spacing `Δ = T/n`: the band-limited signal interpolating the
sample values `a : Fin n → ℝ` at the nodes `t_i = i·(T/n)`. This is the *synthesis*
direction (build a band-limited function from finitely many samples), dual to the
*analysis* direction of `whittaker_shannon_bandlimited`. -/
noncomputable def synthSignal (T : ℝ) (n : ℕ) (a : Fin n → ℝ) : ℝ → ℝ :=
  fun t => ∑ i : Fin n,
    a i * sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ)))

/-- `sincN` of a difference of natural-number casts is the Kronecker delta. -/
theorem sincN_natCast_sub (p q : ℕ) :
    sincN ((p : ℝ) - (q : ℝ)) = if p = q then (1 : ℝ) else 0 := by
  rw [show ((p : ℝ) - (q : ℝ)) = ((((p : ℤ) - (q : ℤ)) : ℤ) : ℝ) by push_cast; ring,
    sincN_int_eq_kronecker]
  simp [sub_eq_zero]

/-! ## §B — (ii) interpolation exactness -/

/-- **(ii)** At a sample node `t = j·(T/n)`, the synthesis recovers the sample value exactly:
all sinc cross-terms vanish (`sincN` at nonzero integers is `0`). -/
theorem synthSignal_sample (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n)
    (j : Fin n) :
    synthSignal T n a (((j : ℕ) : ℝ) * (T / (n : ℝ))) = a j := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hΔ : (T / (n : ℝ)) ≠ 0 := by positivity
  unfold synthSignal
  -- rewrite each summand to `if i = j then a i else 0`
  have hterm : ∀ i : Fin n,
      a i * sincN ((((j : ℕ) : ℝ) * (T / (n : ℝ)) - ((i : ℕ) : ℝ) * (T / (n : ℝ)))
          / (T / (n : ℝ)))
        = if i = j then a i else 0 := by
    intro i
    have harg : (((j : ℕ) : ℝ) * (T / (n : ℝ)) - ((i : ℕ) : ℝ) * (T / (n : ℝ)))
        / (T / (n : ℝ)) = ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      rw [sub_div, mul_div_assoc, mul_div_assoc, div_self hΔ, mul_one, mul_one]
    rw [harg, sincN_natCast_sub]
    by_cases h : i = j
    · rw [h]; simp
    · have hji : ¬ ((j : ℕ) = (i : ℕ)) := by
        intro hc; exact h (Fin.ext hc.symm)
      rw [if_neg hji, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j a]
  simp

/-! ## §B2 — Sinc/boxcar L²-Fourier atom

The workhorse of the whole reduction. A single shifted, dilated normalized sinc
`t ↦ sincN((t - c)/Δ)` is the inverse Fourier transform of the spectral boxcar
`Δ · e^{-2πi c ξ} · 𝟙_{[-1/(2Δ), 1/(2Δ)]}`. Because the boxcar is compactly supported
(hence `L¹ ∩ L²`), the inverse Fourier-agreement bridge
`l2FourierInv_eq_fourierIntegralInv` transfers this pointwise identity to the abstract
`L²`-Fourier isometry, giving both the `L²` membership of the sinc and the explicit
`L²`-Fourier transform. Everything else (band-limitedness, energy) is finite linearity. -/

/-- The spectral boxcar `Δ · e^{-2πi c ξ}` supported on `[-1/(2Δ), 1/(2Δ)]`. This is the
`L²`-Fourier transform of the shifted, dilated normalized sinc `t ↦ sincN((t - c)/Δ)`. -/
noncomputable def specBoxcar (c Δ : ℝ) : ℝ → ℂ :=
  (Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))).indicator
    fun ξ => (Δ : ℂ) * Complex.exp ((-(2 * Real.pi * c * ξ) : ℝ) * Complex.I)

/-- Dilated boxcar integral: rescaling the fundamental-interval identity
`integral_exp_boxcar_eq_sincN` to the band `[-1/(2Δ), 1/(2Δ)]`. -/
theorem exp_dilate_interval_integral (Δ u : ℝ) (hΔ : 0 < Δ) :
    (∫ ξ in (-(1 / (2 * Δ)))..(1 / (2 * Δ)),
        Complex.exp ((2 * Real.pi * u * ξ : ℝ) * Complex.I))
      = (Δ⁻¹ : ℂ) * (sincN (u / Δ) : ℂ) := by
  have hΔ' : Δ ≠ 0 := ne_of_gt hΔ
  have hrw : (fun ξ : ℝ => Complex.exp ((2 * Real.pi * u * ξ : ℝ) * Complex.I))
      = fun ξ : ℝ =>
          (fun y : ℝ => Complex.exp ((2 * Real.pi * (u / Δ) * y : ℝ) * Complex.I)) (Δ * ξ) := by
    funext ξ
    have harg : (2 * Real.pi * u * ξ : ℝ) = 2 * Real.pi * (u / Δ) * (Δ * ξ) := by
      field_simp
    rw [harg]
  rw [show (∫ ξ in (-(1 / (2 * Δ)))..(1 / (2 * Δ)),
        Complex.exp ((2 * Real.pi * u * ξ : ℝ) * Complex.I))
        = ∫ ξ in (-(1 / (2 * Δ)))..(1 / (2 * Δ)),
            (fun y : ℝ => Complex.exp ((2 * Real.pi * (u / Δ) * y : ℝ) * Complex.I)) (Δ * ξ) from by
      rw [hrw]]
  rw [intervalIntegral.integral_comp_mul_left
      (f := fun y : ℝ => Complex.exp ((2 * Real.pi * (u / Δ) * y : ℝ) * Complex.I)) hΔ',
    show Δ * (-(1 / (2 * Δ))) = -(1 / 2) by field_simp,
    show Δ * (1 / (2 * Δ)) = 1 / 2 by field_simp,
    WhittakerShannon.integral_exp_boxcar_eq_sincN (u / Δ), Complex.real_smul, Complex.ofReal_inv]

/-- The spectral boxcar lies in every `Lᵖ`: it is bounded by `Δ` on a compact set. -/
theorem specBoxcar_memLp (c Δ : ℝ) (hΔ : 0 < Δ) (p : ℝ≥0∞) :
    MemLp (specBoxcar c Δ) p volume := by
  have hcont : Continuous
      fun ξ : ℝ => (Δ : ℂ) * Complex.exp ((-(2 * Real.pi * c * ξ) : ℝ) * Complex.I) := by
    fun_prop
  have haesm : AEStronglyMeasurable (specBoxcar c Δ) volume :=
    hcont.aestronglyMeasurable.indicator measurableSet_Icc
  have hvol : volume (Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))) ≠ ∞ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine MemLp.mono' (memLp_indicator_const p measurableSet_Icc (Δ : ℝ) (Or.inr hvol)) haesm ?_
  refine ae_of_all _ (fun ξ => ?_)
  rw [specBoxcar]
  by_cases hξ : ξ ∈ Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_pos hΔ)
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, norm_zero]

/-- Pointwise inverse Fourier transform of the spectral boxcar is the shifted, dilated sinc. -/
theorem fourierInv_specBoxcar (c Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) :
    𝓕⁻ (specBoxcar c Δ) t = (sincN ((t - c) / Δ) : ℂ) := by
  have hb : (0 : ℝ) ≤ 1 / (2 * Δ) := by positivity
  have hΔC : (Δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hΔ
  rw [Real.fourierInv_eq']
  simp only [Real.inner_apply]
  have hfun : (fun ξ : ℝ => Complex.exp ((↑(2 * Real.pi * (ξ * t)) : ℂ) * Complex.I) •
        specBoxcar c Δ ξ)
      = (Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))).indicator
          (fun ξ => (Δ : ℂ) * Complex.exp ((2 * Real.pi * (t - c) * ξ : ℝ) * Complex.I)) := by
    funext ξ
    by_cases hξ : ξ ∈ Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))
    · have hexp : Complex.exp ((2 * Real.pi * (t - c) * ξ : ℝ) * Complex.I)
          = Complex.exp ((2 * Real.pi * (ξ * t) : ℝ) * Complex.I)
            * Complex.exp ((-(2 * Real.pi * c * ξ) : ℝ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [specBoxcar, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, smul_eq_mul, hexp]
      ring
    · rw [specBoxcar, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, smul_zero]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(1 / (2 * Δ)) ≤ 1 / (2 * Δ)),
    intervalIntegral.integral_const_mul, exp_dilate_interval_integral Δ (t - c) hΔ,
    ← mul_assoc, mul_inv_cancel₀ hΔC, one_mul]

/-- The complexified shifted, dilated sinc lies in `L²` (it is the inverse transform of an
`L¹ ∩ L²` boxcar). -/
theorem shiftSinc_memLp (c Δ : ℝ) (hΔ : 0 < Δ) :
    MemLp (fun t => (sincN ((t - c) / Δ) : ℂ)) 2 volume := by
  have hS1 := specBoxcar_memLp c Δ hΔ 1
  have hS2 := specBoxcar_memLp c Δ hΔ 2
  have hbridge := l2FourierInv_eq_fourierIntegralInv (specBoxcar c Δ) hS1 hS2
  have hpt : 𝓕⁻ (specBoxcar c Δ) = fun t => (sincN ((t - c) / Δ) : ℂ) := by
    funext t; exact fourierInv_specBoxcar c Δ hΔ t
  rw [hpt] at hbridge
  exact (memLp_congr_ae hbridge).mp (Lp.memLp _)

/-- The abstract `L²`-Fourier transform of the sinc's canonical `Lp` representative is the
boxcar's canonical `Lp` representative. -/
theorem fourier_shiftSinc_toLp (c Δ : ℝ) (hΔ : 0 < Δ) :
    (𝓕 ((shiftSinc_memLp c Δ hΔ).toLp (fun t => (sincN ((t - c) / Δ) : ℂ))) : Lp ℂ 2 volume)
      = (specBoxcar_memLp c Δ hΔ 2).toLp (specBoxcar c Δ) := by
  have hS1 := specBoxcar_memLp c Δ hΔ 1
  have hbridge := l2FourierInv_eq_fourierIntegralInv (specBoxcar c Δ) hS1
    (specBoxcar_memLp c Δ hΔ 2)
  have hpt : 𝓕⁻ (specBoxcar c Δ) = fun t => (sincN ((t - c) / Δ) : ℂ) := by
    funext t; exact fourierInv_specBoxcar c Δ hΔ t
  rw [hpt] at hbridge
  have hGeq : (shiftSinc_memLp c Δ hΔ).toLp (fun t => (sincN ((t - c) / Δ) : ℂ))
      = 𝓕⁻ ((specBoxcar_memLp c Δ hΔ 2).toLp (specBoxcar c Δ)) := by
    rw [← Lp.toLp_coeFn (𝓕⁻ ((specBoxcar_memLp c Δ hΔ 2).toLp (specBoxcar c Δ))) (Lp.memLp _)]
    exact MemLp.toLp_congr (shiftSinc_memLp c Δ hΔ) (Lp.memLp _) hbridge.symm
  rw [hGeq]
  simp

/-- Boxcar orthogonality (Plancherel on the band): the `L²` inner product of two spectral
boxcars collapses to `Δ · sincN((c - c')/Δ)`. -/
theorem inner_specBoxcar_toLp (c c' Δ : ℝ) (hΔ : 0 < Δ) :
    (⟪(specBoxcar_memLp c Δ hΔ 2).toLp (specBoxcar c Δ),
        (specBoxcar_memLp c' Δ hΔ 2).toLp (specBoxcar c' Δ)⟫ : ℂ)
      = (Δ : ℂ) * (sincN ((c - c') / Δ) : ℂ) := by
  have hb : (0 : ℝ) ≤ 1 / (2 * Δ) := by positivity
  have hΔC : (Δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hΔ
  have hu := MemLp.coeFn_toLp (specBoxcar_memLp c Δ hΔ 2)
  have hv := MemLp.coeFn_toLp (specBoxcar_memLp c' Δ hΔ 2)
  have hfun : (fun ξ : ℝ => (⟪((specBoxcar_memLp c Δ hΔ 2).toLp (specBoxcar c Δ)) ξ,
        ((specBoxcar_memLp c' Δ hΔ 2).toLp (specBoxcar c' Δ)) ξ⟫ : ℂ))
      =ᵐ[volume] fun ξ => (Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))).indicator
        (fun ξ => (Δ : ℂ) ^ 2 * Complex.exp ((2 * Real.pi * (c - c') * ξ : ℝ) * Complex.I)) ξ := by
    filter_upwards [hu, hv] with ξ hξu hξv
    rw [hξu, hξv]
    by_cases hmem : ξ ∈ Set.Icc (-(1 / (2 * Δ))) (1 / (2 * Δ))
    · rw [specBoxcar, specBoxcar, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        Set.indicator_of_mem hmem, RCLike.inner_apply']
      have hexp : Complex.exp ((2 * Real.pi * (c - c') * ξ : ℝ) * Complex.I)
          = (starRingEnd ℂ) (Complex.exp ((-(2 * Real.pi * c * ξ) : ℝ) * Complex.I))
            * Complex.exp ((-(2 * Real.pi * c' * ξ) : ℝ) * Complex.I) := by
        rw [← Complex.exp_conj, ← Complex.exp_add]
        congr 1
        rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast; ring
      rw [hexp, map_mul, Complex.conj_ofReal]
      ring
    · rw [specBoxcar, specBoxcar, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem hmem, inner_zero_left]
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hfun,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(1 / (2 * Δ)) ≤ 1 / (2 * Δ)),
    intervalIntegral.integral_const_mul, exp_dilate_interval_integral Δ (c - c') hΔ, pow_two]
  rw [show (Δ : ℂ) * (Δ : ℂ) * ((Δ : ℂ)⁻¹ * (sincN ((c - c') / Δ) : ℂ))
        = (Δ : ℂ) * ((Δ : ℂ) * (Δ : ℂ)⁻¹) * (sincN ((c - c') / Δ) : ℂ) by ring,
    mul_inv_cancel₀ hΔC, mul_one]

/-- The complexified synthesis lies in `L²` (a finite sum of `L²` shifted sincs). -/
theorem synthSignal_complex_memLp (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n) :
    MemLp (fun t => (synthSignal T n a t : ℂ)) 2 volume := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hΔ : (0 : ℝ) < T / (n : ℝ) := by positivity
  have hrw : (fun t => (synthSignal T n a t : ℂ))
      = fun t => ∑ i : Fin n, (a i : ℂ) *
          (sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ) := by
    funext t
    simp only [synthSignal, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hrw]
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).const_mul (a i : ℂ))

/-- The synthesis's canonical `Lp` representative decomposes as the finite `Lp` combination
`∑ᵢ aᵢ • (shifted sinc)ᵢ`. -/
theorem synthSignal_toLp_eq_sum (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n)
    (hΔ : 0 < T / (n : ℝ)) :
    (synthSignal_complex_memLp T n a hT hn).toLp (fun t => (synthSignal T n a t : ℂ))
      = ∑ i : Fin n, (a i : ℂ) •
          (shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).toLp
            (fun t => (sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ)) := by
  refine Lp.ext ?_
  have hRHS : (⇑(∑ i : Fin n, (a i : ℂ) •
        (shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).toLp
          (fun t => (sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ))) : ℝ → ℂ)
      =ᵐ[volume] fun t => (synthSignal T n a t : ℂ) := by
    refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
    have hterm : ∀ i : Fin n, ∀ᵐ x ∂volume,
        (((a i : ℂ) • (shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).toLp
            (fun t => (sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ))) x)
          = (a i : ℂ) * (sincN ((x - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ) := by
      intro i
      filter_upwards [Lp.coeFn_smul (a i : ℂ)
          ((shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).toLp
            (fun t => (sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ))),
        MemLp.coeFn_toLp (shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ)]
        with x hx1 hx2
      rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]
    filter_upwards [ae_all_iff.mpr hterm] with x hx
    rw [Finset.sum_congr rfl (fun i _ => hx i)]
    simp only [synthSignal, Complex.ofReal_sum, Complex.ofReal_mul]
  exact (MemLp.coeFn_toLp _).trans hRHS.symm

/-! ## §C — (i) band-limitedness -/

/-- **(i)** The synthesis is band-limited to `[-W, W]` provided the sample count satisfies the
Nyquist bound `n ≤ 2WT`: each shifted `sincN(·/Δ)` (spacing `Δ = T/n`) has spectrum supported
in `[-1/(2Δ), 1/(2Δ)] = [-n/(2T), n/(2T)]`, and `n/(2T) ≤ W`.

@audit:ok -/
theorem synthSignal_bandlimited (T W : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) (hnW : (n : ℝ) ≤ 2 * W * T) :
    IsBandlimited (synthSignal T n a) W := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hΔ : (0 : ℝ) < T / (n : ℝ) := by positivity
  have hbW : 1 / (2 * (T / (n : ℝ))) ≤ W := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (T / (n : ℝ))),
      show W * (2 * (T / (n : ℝ))) = (2 * W * T) / (n : ℝ) by ring, le_div_iff₀ hnR, one_mul]
    exact hnW
  have hSmeas : MeasurableSet {ξ : ℝ | W < |ξ|} :=
    measurableSet_lt measurable_const measurable_id.abs
  refine ⟨synthSignal_complex_memLp T n a hT hn, ?_⟩
  have hFT : (𝓕 ((synthSignal_complex_memLp T n a hT hn).toLp
        (fun t => (synthSignal T n a t : ℂ))) : Lp ℂ 2 volume)
      = ∑ i : Fin n, (a i : ℂ) •
          (specBoxcar_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ 2).toLp
            (specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ))) := by
    rw [synthSignal_toLp_eq_sum T n a hT hn hΔ, FourierTransform.fourier_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [FourierTransform.fourier_smul,
      fourier_shiftSinc_toLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ]
  rw [hFT]
  have hcoe : (⇑(∑ i : Fin n, (a i : ℂ) •
        (specBoxcar_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ 2).toLp
          (specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)))) : ℝ → ℂ)
      =ᵐ[volume] fun ξ => ∑ i : Fin n, (a i : ℂ) *
        specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) ξ := by
    refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
    have hterm : ∀ i : Fin n, ∀ᵐ x ∂volume,
        (((a i : ℂ) • (specBoxcar_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ 2).toLp
            (specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)))) x)
          = (a i : ℂ) * specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) x := by
      intro i
      filter_upwards [Lp.coeFn_smul (a i : ℂ)
          ((specBoxcar_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ 2).toLp
            (specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)))),
        MemLp.coeFn_toLp (specBoxcar_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ 2)]
        with x hx1 hx2
      rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]
    filter_upwards [ae_all_iff.mpr hterm] with x hx
    exact Finset.sum_congr rfl (fun i _ => hx i)
  have hcoe' : (⇑(∑ i : Fin n, (a i : ℂ) •
        (specBoxcar_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ 2).toLp
          (specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)))) : ℝ → ℂ)
      =ᵐ[volume.restrict {ξ : ℝ | W < |ξ|}] fun ξ => ∑ i : Fin n, (a i : ℂ) *
        specBoxcar (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) ξ := ae_restrict_of_ae hcoe
  refine hcoe'.trans ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hSmeas]
  refine ae_of_all _ (fun ξ hξ => ?_)
  have hnotmem : ξ ∉ Set.Icc (-(1 / (2 * (T / (n : ℝ))))) (1 / (2 * (T / (n : ℝ)))) := by
    rw [Set.mem_Icc, ← abs_le, not_le]
    exact lt_of_le_of_lt hbW hξ
  simp only [Pi.zero_apply]
  exact Finset.sum_eq_zero (fun i _ => by
    rw [specBoxcar, Set.indicator_of_notMem hnotmem, mul_zero])

/-! ## §D — (iii) Parseval energy -/

/-- The squared synthesis is integrable on the whole line (it lies in `L²`).

@audit:ok -/
theorem synthSignal_sq_integrable (T : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    Integrable (fun t => (synthSignal T n a t) ^ 2) := by
  have hint : Integrable (fun t => ‖(synthSignal T n a t : ℂ)‖ ^ 2) :=
    (synthSignal_complex_memLp T n a hT hn).integrable_norm_pow (p := 2) (by norm_num)
  refine hint.congr ?_
  filter_upwards with t
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **(iii)** Parseval / sinc self-reproducing energy identity: the whole-line energy of the
synthesis equals `Δ · ∑ᵢ (a i)²` with `Δ = T/n`. Follows from the sinc orthogonality
`∫ sincN((t-iΔ)/Δ)·sincN((t-jΔ)/Δ) dt = Δ·δᵢⱼ`.

@audit:ok -/
theorem synthSignal_energy (T : ℝ) (n : ℕ) (a : Fin n → ℝ) (hT : 0 < T) (hn : 0 < n) :
    (∫ t, (synthSignal T n a t) ^ 2) = (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hΔ : (0 : ℝ) < T / (n : ℝ) := by positivity
  have hstep1 : (⟪(synthSignal_complex_memLp T n a hT hn).toLp (fun t => (synthSignal T n a t : ℂ)),
        (synthSignal_complex_memLp T n a hT hn).toLp (fun t => (synthSignal T n a t : ℂ))⟫ : ℂ)
      = ((∫ t, (synthSignal T n a t) ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    have hae : (fun ξ => (⟪((synthSignal_complex_memLp T n a hT hn).toLp
          (fun t => (synthSignal T n a t : ℂ))) ξ,
        ((synthSignal_complex_memLp T n a hT hn).toLp
          (fun t => (synthSignal T n a t : ℂ))) ξ⟫ : ℂ))
        =ᵐ[volume] fun ξ => ((synthSignal T n a ξ ^ 2 : ℝ) : ℂ) := by
      filter_upwards [MemLp.coeFn_toLp (synthSignal_complex_memLp T n a hT hn)] with ξ hξ
      rw [hξ, RCLike.inner_apply', Complex.conj_ofReal]
      push_cast; ring
    rw [integral_congr_ae hae, integral_complex_ofReal]
  have hstep2 : (⟪(synthSignal_complex_memLp T n a hT hn).toLp (fun t => (synthSignal T n a t : ℂ)),
        (synthSignal_complex_memLp T n a hT hn).toLp (fun t => (synthSignal T n a t : ℂ))⟫ : ℂ)
      = ((T / (n : ℝ) * ∑ i : Fin n, (a i) ^ 2 : ℝ) : ℂ) := by
    have hinner : ∀ i j : Fin n,
        (⟪(shiftSinc_memLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).toLp
            (fun t => (sincN ((t - ((i : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ)),
          (shiftSinc_memLp (((j : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ).toLp
            (fun t => (sincN ((t - ((j : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))) : ℂ))⟫ : ℂ)
          = (T / (n : ℝ) : ℂ) * (if i = j then 1 else 0) := by
      intro i j
      rw [← Lp.inner_fourier_eq,
        fourier_shiftSinc_toLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ,
        fourier_shiftSinc_toLp (((j : ℕ) : ℝ) * (T / (n : ℝ))) (T / (n : ℝ)) hΔ,
        inner_specBoxcar_toLp (((i : ℕ) : ℝ) * (T / (n : ℝ))) (((j : ℕ) : ℝ) * (T / (n : ℝ)))
          (T / (n : ℝ)) hΔ,
        show (((i : ℕ) : ℝ) * (T / (n : ℝ)) - ((j : ℕ) : ℝ) * (T / (n : ℝ))) / (T / (n : ℝ))
            = ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) by
          rw [sub_div, mul_div_assoc, mul_div_assoc, div_self (ne_of_gt hΔ), mul_one, mul_one],
        sincN_natCast_sub]
      by_cases h : i = j
      · simp [h]
      · have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => h (Fin.ext hc)
        simp [hne, h]
    rw [synthSignal_toLp_eq_sum T n a hT hn hΔ]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal, hinner]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  exact_mod_cast hstep1.symm.trans hstep2

/-! ## §E — boundedness of the message set -/

/-- Bessel's inequality against the orthonormal test family: the total observed energy of any
codeword is capped by its whole-line `L²` energy, hence by the power budget `T·P` — uniformly in
the observation count `k`, with no bandwidth or spacing input. -/
private theorem contAwgn_sum_observation_sq_le {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (m : Fin M) :
    ∑ i : Fin c.k, (c.observation m i) ^ 2 ≤ T * P := by
  classical
  -- The codeword and the test family, as elements of `L²(ℝ)`.
  set f : Lp ℝ 2 volume := (c.encoder_memLp m).toLp (c.encoder m) with hf_def
  set φ : Fin c.k → Lp ℝ 2 volume := fun i => (c.testFn_memLp i).toLp (c.testFn i) with hφ_def
  -- `⟪φ i, g⟫ = ∫ t, g t * testFn i t` for any `g` given a.e. representatives.
  have hinner : ∀ (i : Fin c.k) (g : Lp ℝ 2 volume),
      (inner ℝ (φ i) g : ℝ) = ∫ t, g t * c.testFn i t := by
    intro i g
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (c.testFn_memLp i)] with t ht
    simp only [hφ_def, ht, RCLike.inner_apply, conj_trivial]
  -- The test family is orthonormal in `L²` — this is exactly `testFn_orthonormal`.
  have hortho : Orthonormal ℝ φ := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner i (φ j)]
    have : (∫ t, (φ j : ℝ → ℝ) t * c.testFn i t) = ∫ t, c.testFn j t * c.testFn i t := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (c.testFn_memLp j)] with t ht
      simp only [hφ_def, ht]
    rw [this, c.testFn_orthonormal j i]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  -- Bessel's inequality, uniform in `k`.
  have hbessel := hortho.sum_inner_products_le (x := f) (s := Finset.univ)
  -- `⟪φ i, f⟫ = observation m i`.
  have hobs : ∀ i : Fin c.k, (inner ℝ (φ i) f : ℝ) = c.observation m i := by
    intro i
    rw [hinner i f]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (c.encoder_memLp m)] with t ht
    simp only [hf_def, ht]
  -- `‖f‖² = ∫ t, (encoder m t)²`, which `encoder_power` caps by `T·P`.
  have hnorm : ‖f‖ ^ 2 = ∫ t, (c.encoder m t) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (c.encoder_memLp m)] with t ht
    simp only [hf_def, ht, RCLike.inner_apply, conj_trivial, sq]
  calc ∑ i : Fin c.k, (c.observation m i) ^ 2
      = ∑ i : Fin c.k, ‖(inner ℝ (φ i) f : ℝ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hobs i, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖f‖ ^ 2 := hbessel
    _ = ∫ t, (c.encoder m t) ^ 2 := hnorm
    _ ≤ T * P := c.encoder_power m

/-- The discrete `AwgnCode` induced by reading a `ContAwgnCode` through its matched filters: the
codewords are the observation vectors and the decoder is unchanged. The per-observation power
budget `(T·P + 1)/k` is chosen strictly positive (the `+1` covers the degenerate `P = 0`), which
`awgn_converse` requires. -/
private noncomputable def contAwgnToAwgnCode {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (hk : 0 < c.k) :
    AWGN.AwgnCode M c.k ((T * P + 1) / (c.k : ℝ)) where
  encoder m i := c.observation m i
  decoder := c.decoder
  decoder_meas := c.decoder_meas
  power_constraint := by
    intro m
    have hkR : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hk
    rw [mul_div_cancel₀ _ (ne_of_gt hkR)]
    linarith [contAwgn_sum_observation_sq_le c m]

/-- The continuous-time error probability *is* the discrete one for the induced code: both are the
same `Measure.pi` of per-observation Gaussians over the same decoding-error event. -/
private theorem contAwgn_errorProbAt_eq {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (hk : 0 < c.k) (N₀ : ℝ) (m : Fin M) :
    c.errorProbAt N₀ m
      = (contAwgnToAwgnCode c hk).toCode.errorProbAt
          (AWGN.awgnChannel (N₀ / 2).toNNReal (AWGN.isAwgnChannelMeasurable _)) m := by
  rfl

/-- Each pointwise error probability is finite (it is a probability). -/
private theorem contAwgn_errorProbAt_ne_top {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) (m : Fin M) :
    c.errorProbAt N₀ m ≠ ⊤ := by
  unfold ContAwgnCode.errorProbAt
  exact measure_ne_top _ _

/-- The average error in the shape `awgn_converse` wants: a real average of real error
probabilities. -/
private theorem contAwgn_averageError_toReal {T W P : ℝ} {M : ℕ} (hM : 0 < M)
    (c : ContAwgnCode T W P M) (N₀ : ℝ) :
    (c.averageError N₀).toReal
      = (1 / M : ℝ) * ∑ m : Fin M, (c.errorProbAt N₀ m).toReal := by
  unfold ContAwgnCode.averageError
  rw [if_neg hM.ne']
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sum (fun m _ => contAwgn_errorProbAt_ne_top c N₀ m)]
  simp [one_div]

/-- The crude wall-free rate bound, for codes with at least one observation: `log M` is capped by
`(T·P + 1)/N₀` plus the Fano terms, **uniformly in the observation count `k`**. This is where
Bessel meets `awgn_converse`, and where `ln(1+x) ≤ x` discards the `k`-dependence. -/
theorem contAwgn_log_le_of_pos_k {T W N₀ P ε : ℝ} {M : ℕ}
    (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hT : 0 < T) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hM : 2 ≤ M) (c : ContAwgnCode T W P M) (hk : 0 < c.k)
    (hce : (c.averageError N₀).toReal ≤ ε) :
    Real.log M ≤ ((T * P + 1) / N₀ + Real.log 2) / (1 - ε) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hkR : (0 : ℝ) < (c.k : ℝ) := by exact_mod_cast hk
  have hTP : 0 ≤ T * P := mul_nonneg hT.le hP
  -- The noise variance of the discretized channel is `N₀/2`.
  set N : ℝ≥0 := (N₀ / 2).toNNReal with hN_def
  have hNR : (N : ℝ) = N₀ / 2 := Real.coe_toNNReal _ (by linarith)
  have hN : (N : ℝ) ≠ 0 := by rw [hNR]; linarith
  set h_meas := AWGN.isAwgnChannelMeasurable N with hmeas_def
  -- The induced discrete code and its (strictly positive) per-observation power budget.
  set P' : ℝ := (T * P + 1) / (c.k : ℝ) with hP'_def
  have hP'pos : 0 < P' := div_pos (by linarith) hkR
  set dc := contAwgnToAwgnCode c hk with hdc_def
  -- The continuous average error *is* the discrete one.
  set Pe : ℝ := (c.averageError N₀).toReal with hPe_def
  have hPe : Pe = (1 / M : ℝ) *
      ∑ m : Fin M, (dc.toCode.errorProbAt (AWGN.awgnChannel N h_meas) m).toReal := by
    rw [hPe_def, contAwgn_averageError_toReal hM0 c N₀]
    exact congrArg _ (Finset.sum_congr rfl fun m _ => by
      rw [contAwgn_errorProbAt_eq c hk N₀ m])
  -- The discrete converse.
  have hconv := AWGN.awgn_converse P' hP'pos N hN h_meas hM hk dc Pe hPe
  -- `ln(1+x) ≤ x` kills the `k`-dependence: the whole observation bank is worth `≤ (T·P+1)/N₀`.
  have hlog : (c.k : ℝ) * ((1 / 2) * Real.log (1 + P' / (N : ℝ))) ≤ (T * P + 1) / N₀ := by
    have hx : 0 < 1 + P' / (N : ℝ) := by
      have : 0 < P' / (N : ℝ) := div_pos hP'pos (by rw [hNR]; linarith)
      linarith
    have h1 : Real.log (1 + P' / (N : ℝ)) ≤ P' / (N : ℝ) := by
      have := Real.log_le_sub_one_of_pos hx; linarith
    have h2 : (c.k : ℝ) * ((1 / 2) * Real.log (1 + P' / (N : ℝ)))
        ≤ (c.k : ℝ) * ((1 / 2) * (P' / (N : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hkR.le
      linarith
    refine h2.trans (le_of_eq ?_)
    rw [hP'_def, hNR]
    field_simp
  -- Fano terms: `binEntropy ≤ log 2`, and `Pe·log(M-1) ≤ ε·log M`.
  have hPe0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPeε : Pe ≤ ε := hce
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM1 : 0 ≤ Real.log ((M : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hlogle : Real.log ((M : ℝ) - 1) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hfano : Pe * Real.log ((M : ℝ) - 1) ≤ ε * Real.log (M : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hPeε hlogM1)
      (mul_le_mul_of_nonneg_left hlogle hε0.le)
  have hbin : Real.binEntropy Pe ≤ Real.log 2 := Real.binEntropy_le_log_two
  -- Rearrange: `(1-ε)·log M ≤ (T·P+1)/N₀ + log 2`.
  have hkey : (1 - ε) * Real.log (M : ℝ) ≤ (T * P + 1) / N₀ + Real.log 2 := by nlinarith [hconv]
  rw [le_div_iff₀ (by linarith)]
  linarith [hkey]

/-- With no observations at all the receiver learns nothing: every message is decoded to the same
one, so the average error is exactly `(M-1)/M`. -/
theorem contAwgn_averageError_of_k_eq_zero {T W P : ℝ} {M : ℕ} (hM : 0 < M)
    (c : ContAwgnCode T W P M) (hk : c.k = 0) (N₀ : ℝ) :
    (c.averageError N₀).toReal = ((M : ℝ) - 1) / M := by
  classical
  haveI : IsEmpty (Fin c.k) := by rw [hk]; infer_instance
  -- With no observations the sample space is a single point.
  set x₀ : Fin c.k → ℝ := isEmptyElim with hx₀
  set m₀ : Fin M := c.decoder x₀ with hm₀
  -- Every error probability is `0` at `m₀` and `1` elsewhere.
  have herr : ∀ m : Fin M,
      (c.errorProbAt N₀ m).toReal = 1 - (if m₀ = m then (1 : ℝ) else 0) := by
    intro m
    have hmeas : MeasurableSet {y : Fin c.k → ℝ | c.decoder y ≠ m} :=
      (c.decoder_meas (measurableSet_singleton m)).compl
    unfold ContAwgnCode.errorProbAt
    rw [Measure.pi_of_empty _ x₀, Measure.dirac_apply' _ hmeas]
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hm₀, Pi.one_apply]
    by_cases h : c.decoder x₀ = m <;> simp [h]
  rw [contAwgn_averageError_toReal hM c N₀]
  simp_rw [herr]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq _ m₀ (fun _ => (1 : ℝ))]
  simp [Finset.card_univ, div_eq_inv_mul]

/-- The message-count set is bounded above — the `BddAbove` obligation needed to lower-bound
`contAwgnMaxMessages` via `le_csSup`.

This is wall-independent: it closes by Bessel's inequality alone, without the `≈ 2WT`
degrees-of-freedom count. The test family `testFn` is orthonormal, so for every codeword

    `∑ᵢ (observation m i)² = ∑ᵢ ⟨encoder m, testFn i⟩² ≤ ‖encoder m‖₂² ≤ T·P`,

uniformly in the observation count `k` — no spacing, rate or bandwidth hypothesis enters, and the
whole-line `encoder_power` supplies the right-hand side directly. That energy bound feeds
`awgn_converse` on the induced discrete code `contAwgnToAwgnCode` (per-observation power
`P' = (T·P + 1)/k`, whose `power_constraint` holds by construction; the `+1` keeps it strictly
positive when `P = 0`), and `log(1+x) ≤ x` collapses the `k`-dependence:

    `(k/2)·log(1 + 2(T·P+1)/(k·N₀)) ≤ (T·P+1)/N₀`.

Rearranging the Fano terms against `ε < 1` gives `log M ≤ ((T·P+1)/N₀ + log 2)/(1-ε)`, a bound
free of `k`, so the message set is capped. Two degenerate branches sit outside that argument and
are handled separately: `M < 2` (below the converse's range) and `k = 0`, where the receiver
observes nothing, every message decodes to the same one, the average error is exactly `(M-1)/M`,
and `ε < 1` alone caps `M ≤ 1/(1-ε)`.

That the bandwidth constraint is *unused* here is the point rather than an oversight: `hW` is the
only hypothesis the proof never touches, and it is retained solely to keep the signature uniform
with the rest of the sandwich (`W` itself still appears, via `ContAwgnCode T W P M`). The proof in
fact reads neither `encoder_bandlimited` nor `testFn_support`: orthonormality of `testFn` plus the
whole-line `encoder_power` are the only structure fields the bound needs.

This bound is deliberately crude, and its crudeness is load-bearing evidence rather than a
shortcoming: it caps the rate at `P/N₀`, which `ln(1+x) ≤ x` makes strictly larger than
`bandlimitedAwgnCapacity W N₀ P`. Boundedness is free; the exact constant is not, and it is the
part that still needs the prolate eigenvalue count (see `contAwgn_eq_shannonHartley`).

Hypotheses are regularity-only (not load-bearing).

@audit:ok -/
theorem contAwgnMaxMessages_bddAbove (T W N₀ P ε : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hε0 : 0 < ε) (hε1 : ε < 1) :
    BddAbove { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε } := by
  have hε : 0 < 1 - ε := by linarith
  -- The two crude caps: the Bessel/converse one, and the observation-free one.
  set B : ℝ := ((T * P + 1) / N₀ + Real.log 2) / (1 - ε) with hB
  set C : ℝ := 1 / (1 - ε) with hC
  refine ⟨max ⌈Real.exp B⌉₊ ⌈C⌉₊, ?_⟩
  rintro M ⟨c, hce⟩
  rcases lt_or_ge M 2 with hM | hM
  · -- `M ≤ 1` is below `C = 1/(1-ε) > 1`.
    have h1 : (1 : ℝ) ≤ C := by rw [hC, le_div_iff₀ hε]; linarith
    have : (1 : ℕ) ≤ ⌈C⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    omega
  · have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
    have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    rcases Nat.eq_zero_or_pos c.k with hk | hk
    · -- No observations: the receiver guesses, so `(M-1)/M ≤ ε` pins `M ≤ 1/(1-ε)`.
      rw [contAwgn_averageError_of_k_eq_zero hM0 c hk N₀] at hce
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ))] at hce
      have hMC : (M : ℝ) ≤ C := by rw [hC, le_div_iff₀ hε]; nlinarith
      have : M ≤ ⌈C⌉₊ := by exact_mod_cast hMC.trans (Nat.le_ceil C)
      omega
    · -- Bessel + `awgn_converse`: `log M ≤ B`, uniformly in the observation count.
      have hlog := contAwgn_log_le_of_pos_k hN₀ hP hT hε0 hε1 hM c hk hce
      rw [← hB, Real.log_le_iff_le_exp (by linarith)] at hlog
      have : M ≤ ⌈Real.exp B⌉₊ := by exact_mod_cast hlog.trans (Nat.le_ceil _)
      omega

end InformationTheory.Shannon.ShannonHartley
