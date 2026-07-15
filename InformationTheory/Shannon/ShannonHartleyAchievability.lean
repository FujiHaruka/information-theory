import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import InformationTheory.Shannon.ShannonHartleyOperational
import InformationTheory.Shannon.NormalizedSinc
import InformationTheory.Shannon.WhittakerShannon
import InformationTheory.Shannon.AWGN.Achievability
import InformationTheory.Shannon.AWGN.Converse
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley: achievability (Cover-Thomas Ch. 9.6, Phase 3)

The `≥` half of the operational Shannon-Hartley sandwich,

    `bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P`

(`contAwgn_ge_shannonHartley`). This direction is *wall-independent*: a discrete
per-sample AWGN codebook (`awgn_achievability`) is lifted to a continuous band-limited
signal by **sinc synthesis** at the true sampler spacing `Δ = T/n` (with `n = ⌊2WT⌋`).

## The synthesis bridge

`synthSignal T n a` reconstructs a band-limited signal interpolating the sample values
`a : Fin n → ℝ` at the grid `t_i = i·(T/n)`. Its three properties power the reduction:

* **(ii) interpolation exactness** — `synthSignal T n a (j·(T/n)) = a j`
  (`synthSignal_sample`), whence `sampledSignal (synthSignal …) = c` after the
  `√(T/n)·√(n/T)` cancellation.
* **(i) band-limitedness** — `IsBandlimited (synthSignal T n a) W` when `n ≤ 2WT`
  (`synthSignal_bandlimited`): each shifted `sincN(·/Δ)` has spectrum supported in
  `[-1/(2Δ), 1/(2Δ)] = [-n/(2T), n/(2T)] ⊆ [-W, W]`.
* **(iii) Parseval energy** — `∫ t, (synthSignal T n a t)² = (T/n)·∑ᵢ (a i)²`
  (`synthSignal_energy`), so with `a = √(n/T)·c` the whole-line energy is `∑ᵢ cᵢ² ≤ T·P`
  and the in-window energy is `≤` that.

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

/-- The `√(T/n)`-normalized samples of the synthesized signal recover `√(T/n)·a`. -/
theorem sampledSignal_synthSignal (T : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    sampledSignal (synthSignal T n a) T n = fun j => Real.sqrt (T / (n : ℝ)) * a j := by
  funext j
  rw [sampledSignal, synthSignal_sample T n a hT hn j]

/-- Choosing `a = √(n/T)·c` makes the synthesized signal's normalized samples equal to the
discrete codeword `c` exactly (the `√(T/n)·√(n/T) = 1` cancellation). -/
theorem sampledSignal_synthSignal_sqrt (T : ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    sampledSignal (synthSignal T n (fun i => Real.sqrt ((n : ℝ) / T) * c i)) T n = c := by
  rw [sampledSignal_synthSignal T n _ hT hn]
  funext j
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.sqrt (T / (n : ℝ)) * Real.sqrt ((n : ℝ) / T) = 1 := by
    rw [← Real.sqrt_mul (by positivity),
      show (T / (n : ℝ)) * ((n : ℝ) / T) = 1 by field_simp]
    exact Real.sqrt_one
  rw [← mul_assoc, h1, one_mul]

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

/-- In-window energy is bounded by the whole-line energy (the integrand is `≥ 0`), giving the
`ContAwgnCode.encoder_power` obligation directly. This reduction is genuine, resting on the
(now genuine) `synthSignal_energy` (iii) and `synthSignal_sq_integrable`.

@audit:ok -/
theorem synthSignal_window_energy_le (T : ℝ) (n : ℕ) (a : Fin n → ℝ)
    (hT : 0 < T) (hn : 0 < n) :
    (∫ t in Set.Icc (0 : ℝ) T, (synthSignal T n a t) ^ 2)
      ≤ (T / (n : ℝ)) * ∑ i : Fin n, (a i) ^ 2 := by
  rw [← synthSignal_energy T n a hT hn]
  exact setIntegral_le_integral (synthSignal_sq_integrable T n a hT hn)
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))

/-! ## §E — boundedness of the message set (wall-gated) -/

/-- The message-count set is bounded above — the `BddAbove` obligation needed to lower-bound
`contAwgnMaxMessages` via `le_csSup`.

Contrary to the original plan, this is **not** a crude/wall-independent converse. Applying
`awgn_converse` to the sampled codeword vector reduces `BddAbove` to a bound on the sampled
energy `E = (T/n)·∑ᵢ (encoder m (i·T/n))²` that is **uniform over the whole code family and over
`sampleCount = n`** (more samples give the decoder strictly more information, so the sup is not
attained at small `n`). The `ContAwgnCode` structure constrains only the **window** energy
`∫₀ᵀ f² ≤ T·P`; `bandlimited_sup_bound` controls point values by the **full-line** `‖f‖₂`, which
is unconstrained (a band-limited `L²` signal can carry arbitrary energy outside `[0,T]` while
keeping the window energy small, and the sinc reproducing-kernel tail leaks it back into the
in-window samples). Tying the in-window sampled energy of a band-limited signal to its window
energy is exactly the time-band concentration (prolate-spheroidal / Landau-Pollak-Slepian)
content — the same `nyquist-2w-dof` wall carried by `contAwgn_eq_shannonHartley` (converse side).
The statement is **true** (the message set is finite because capacity is finite), but even mere
finiteness of the sampled energy requires the concentration theorem; there is no cheaper crude
intermediate (a `≈2WT`-tight count is not needed, yet no weaker bound exists either). Absent from
Mathlib: loogle `Found 0` for `prolate`/`Slepian`.

`@residual(wall:nyquist-2w-dof)` -/
theorem contAwgnMaxMessages_bddAbove (T W N₀ P ε : ℝ)
    (hT : 0 < T) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (hε0 : 0 < ε) (hε1 : ε < 1) :
    BddAbove { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε } := by
  sorry -- @residual(wall:nyquist-2w-dof)

/-! ## §F — assembly (gated on §E's wall-blocked boundedness) -/

/-- **Shannon-Hartley achievability (`≥`)**: the operational capacity is at least the
Shannon-Hartley closed form. Proved by lifting a per-sample `awgn_achievability` codebook
through the synthesis bridge.

The achievability construction itself (per-sample `awgn_achievability` → `synthSignal` bridge →
per-`T` codebook) is wall-free plan-work. But lower-bounding the operational capacity requires
`contAwgnMaxMessages = sSup {M | …} ≥ M₀` via `le_csSup`, which consumes
`contAwgnMaxMessages_bddAbove` (§E) — and the ℕ-`sSup` collapses to junk `0` without that
`BddAbove`. Since §E is `nyquist-2w-dof`-wall-blocked, this direction cannot close until either
the wall is resolved or the capacity definition is refactored to the standard achievable-rate
form (`sup` over rates achievable by code sequences), which decouples achievability from the
converse's boundedness obligation. Hence the residual is wall-gated even though the assembly logic
is not itself a wall. The residual's own content (the assembly) is writeable plan-work; the
`nyquist-2w-dof` obstruction it transitively needs is carried by §E (`contAwgnMaxMessages_bddAbove`),
so this residual is classified `plan:` with the wall recorded as a documented prerequisite rather
than duplicating the wall tag here.

`@residual(plan:shannon-hartley-operational-moonshot-plan)` -/
theorem contAwgn_ge_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := by
  sorry -- @residual(plan:shannon-hartley-operational-moonshot-plan)

end InformationTheory.Shannon.ShannonHartley
