import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.LiminfLimsup
import InformationTheory.Shannon.ShannonHartley
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley operational capacity

Cover-Thomas Ch. 9.6. This file gives a *non-circular, operational* definition of the capacity of
the continuous-time band-limited AWGN channel and states the Shannon-Hartley identity

    `contAwgnOperationalCapacity W N₀ P = W · log(1 + P / (N₀ · W))`

as `contAwgn_eq_shannonHartley`. That theorem is published with a `sorry` body tagged to the
`nyquist-2w-dof` wall: what blocks it is the prolate-spheroidal / Landau-Pollak-Slepian
time-bandwidth degrees-of-freedom count, a genuine Mathlib gap.

`IsBandlimited` uses the *L²-Fourier spectral support* of the complexification (a genuine
band-limit constraint, not junk-`0`). The Paley-Wiener sup bound `bandlimited_sup_bound`
(`|f(t)| ≤ √(2W)·‖f‖₂`) is fully proven (`sorryAx`-free) over the `L²↔L¹` Fourier-agreement
bridges `l2Fourier_eq_fourierIntegral` / `l2FourierInv_eq_fourierIntegralInv`; it caps pointwise
values by the *full-line* `L²` energy `‖f‖₂`.

`ContAwgnCode` models the receiver as a bank of `k` matched filters: `k` orthonormal test
functions supported in `[0, T]`, against which the codeword is correlated
(`ContAwgnCode.observation`) before independent Gaussian noise is added
(`ContAwgnCode.errorProbAt`). This is the Karhunen-Loève discretization, and orthonormality is
what makes the independent per-observation noise law exact. An earlier version of this file read
the codeword pointwise on a grid, which is an isometry only at the Nyquist spacing and hence
assumed what the theorem must prove; the refutation and the def-fix are recorded in
`docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP.

## Main definitions

* `IsBandlimited f W` — the L²-Fourier transform of the complexification of `f : ℝ → ℝ` has
  spectral support in `[-W, W]` (vanishes a.e. on `{ξ | W < |ξ|}`).
* `ContAwgnCode T W P M` — a continuous-time AWGN code: `M` band-limited signals of whole-line
  energy `≤ T·P`, observed through a *free* number `k` of orthonormal test functions supported in
  `[0, T]`, together with a decoder acting on the observation vector.
* `ContAwgnCode.observation` — the noiseless correlation `∫ (encoder m)·(testFn i)`.
* `contAwgnOperationalCapacity W N₀ P` — the per-second operational rate
  `⨅ ε, limsup_T (log M(T, ε)) / T`.

## Main statements

* `contAwgn_eq_shannonHartley` — the operational capacity equals the Shannon-Hartley
  closed form `bandlimitedAwgnCapacity W N₀ P`.

## Implementation notes — the three honesty risks and how the definition fares

The definition aims to make `contAwgn_eq_shannonHartley` *true*, *non-circular*, and
*non-degenerate*.

* **Truth.** Observations are the correlations `⟨encoder m, testFn i⟩` against an orthonormal
  family supported in `[0, T]`, each corrupted by independent noise of variance `N₀/2`. Against an
  orthonormal family, white-noise coefficients are exactly i.i.d., so no spacing or rate condition
  is smuggled into the noise law. For band-limited `f`, `⟨f, φᵢ⟩ = ⟨f, P_W φᵢ⟩`, so the signal
  energy the receiver can see is controlled by the compression of the time-band-limiting operator
  onto `span{φᵢ}`; Bessel caps it by `‖f‖₂² ≤ T·P` uniformly in `k`, and Cauchy interlacing caps
  the per-dimension gains by the prolate eigenvalues. Rate `W·log(1 + P/(N₀·W))` is reached in the
  `T → ∞` limit exactly when `≈ 2WT` of those eigenvalues are near `1`.
* **Non-circularity (C1–C4).** A codeword is a genuine band-limited *function* `ℝ → ℝ`
  (C1), never a length-`⌊2WT⌋` sample vector; `contAwgnMaxMessages` contains no `2W` or
  `⌊2WT⌋` (C2); the observation count `k` is a *free* `ℕ` field, not pinned to `⌊2WT⌋` (C4); the
  factor `2W` is not in any definition and must emerge from the DOF proof (C3) — `testFn` is asked
  only for orthonormality and `[0, T]` support. Consequently `contAwgn_eq_shannonHartley` cannot
  be closed by `rfl`/`unfold`.
* **Non-degeneracy.** The noise genuinely corrupts the signal (variance `N₀/2 > 0` whenever
  `N₀ > 0`). Neither oversampling nor undersampling inflates the signal-to-noise ratio: raising
  `k` adds observations but Bessel holds `∑ᵢ ⟨f, φᵢ⟩² ≤ ‖f‖₂²` uniformly, so extra observations
  split the same energy budget rather than duplicating it, and the whole-line `encoder_power`
  leaves no energy outside the window for the reproducing kernel to reflect back in.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1.
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology FourierTransform SchwartzMap ContDiff RealInnerProductSpace

/-! ## §A — Band-limited signals -/

/-- A real signal `f : ℝ → ℝ` is band-limited to `[-W, W]` if the **L²-Fourier transform** of its
complexification has spectral support in `[-W, W]`, i.e. vanishes almost everywhere on
`{ξ | W < |ξ|}`. The complexification `t ↦ (f t : ℂ)` is needed because the L² Fourier transform
`𝓕 : Lp ℂ 2 volume → Lp ℂ 2 volume` is complex-valued.

This is a *genuine* band-limit constraint: unlike the L¹ `Real.fourierIntegral` (which is `0`
for every non-L¹ signal, hence vacuous — junk-`0` — on the entire target class of essentially
time-limited band-limited L² signals), the L² transform is defined on the whole a.e. class and
its support genuinely separates band-limited functions from broadband ones. -/
def IsBandlimited (f : ℝ → ℝ) (W : ℝ) : Prop :=
  ∃ hf : MemLp (fun t : ℝ => (f t : ℂ)) 2 volume,
    (𝓕 (hf.toLp (fun t : ℝ => (f t : ℂ))) : Lp ℂ 2 volume)
      =ᵐ[volume.restrict {ξ : ℝ | W < |ξ|}] 0

/-- **`L²`-`L¹` Fourier-agreement bridge.** For `f ∈ L¹ ∩ L²`, the coeFn of the `L²`-Fourier
transform of the canonical `Lp` representative of `f` agrees almost everywhere with the classical
`L¹` Fourier integral `𝓕 f` (the pointwise `VectorFourier.fourierIntegral`).

This is the plumbing that connects the abstract `L²`-Fourier isometry `𝓕 : Lp ℂ 2 → Lp ℂ 2` to the
concrete pointwise integral, over the tempered-distribution scaffolding. Both objects define the
same tempered distribution: the `L²`-Fourier side via `Lp.fourier_toTemperedDistribution_eq`, the
`L¹` pointwise side via the Fourier self-adjointness (multiplication formula)
`VectorFourier.integral_fourierIntegral_smul_eq_flip`; equality of tempered distributions on the
locally integrable class forces almost-everywhere equality
(`ae_eq_of_integral_contDiff_smul_eq`).

@audit:ok -/
theorem l2Fourier_eq_fourierIntegral (f : ℝ → ℂ)
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hf1_int : Integrable f volume := memLp_one_iff_integrable.mp hf1
  set G : Lp ℂ 2 volume := 𝓕 (hf2.toLp f) with hG
  have hlocG : LocallyIntegrable (⇑G) volume :=
    (Lp.memLp G).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcont_Ff : Continuous (𝓕 f) := by
    rw [← Real.fourierTransform_toLp hf1]
    exact (Real.Lp.fourierTransform hf1.toLp).continuous
  have hlocFf : LocallyIntegrable (𝓕 f) volume := hcont_Ff.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hlocG hlocFf ?_
  intro g hg_diff hg_supp
  -- Complexified compactly supported smooth test function as a Schwartz map.
  have hφ1 : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_supp.comp_left rfl
  have hφ2 : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg_diff
  set φ : 𝓢(ℝ, ℂ) := hφ1.toSchwartzMap hφ2 with hφdef
  have hφ_coe : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  -- Real smul `g x • z` equals the multiplication `φ x • z` by the complexification of `g`.
  have hsmul : ∀ (x : ℝ) (z : ℂ), g x • z = φ x • z := by
    intro x z
    rw [hφ_coe, Complex.real_smul, smul_eq_mul]
  -- Step A: rewrite the `L²` side over the tempered-distribution scaffolding.
  have hdist : (G : 𝓢'(ℝ, ℂ)) = 𝓕 ((hf2.toLp f : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) := by
    rw [hG]; exact (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f)).symm
  have hA : ∫ x, g x • (⇑G) x ∂volume = ∫ x, (𝓕 φ : 𝓢(ℝ, ℂ)) x • f x ∂volume := by
    calc ∫ x, g x • (⇑G) x ∂volume
        = ∫ x, φ x • (⇑G) x ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hsmul x (G x))
      _ = (G : 𝓢'(ℝ, ℂ)) φ := (Lp.toTemperedDistribution_apply G φ).symm
      _ = 𝓕 ((hf2.toLp f : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) φ := by rw [hdist]
      _ = ((hf2.toLp f : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) (𝓕 φ) := TemperedDistribution.fourier_apply _ _
      _ = ∫ x, (𝓕 φ : 𝓢(ℝ, ℂ)) x • (hf2.toLp f : ℝ → ℂ) x ∂volume := Lp.toTemperedDistribution_apply _ _
      _ = ∫ x, (𝓕 φ : 𝓢(ℝ, ℂ)) x • f x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hf2.coeFn_toLp] with x hx
          rw [hx]
  -- Step B: rewrite the `L¹` side via the Fourier self-adjointness (multiplication formula).
  have hB : ∫ x, g x • (𝓕 f) x ∂volume = ∫ x, (𝓕 φ : 𝓢(ℝ, ℂ)) x • f x ∂volume := by
    have hstep : ∫ x, g x • (𝓕 f) x ∂volume = ∫ x, φ x • (𝓕 f) x ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => hsmul x (𝓕 f x))
    have hFT : ∀ h : ℝ → ℂ, 𝓕 h = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) h :=
      fun _ => rfl
    rw [hstep]
    simp only [SchwartzMap.fourier_coe, hFT]
    simpa using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner φ.integrable hf1_int).symm
  rw [hA, hB]

/-- **`L²`-`L¹` inverse-Fourier-agreement bridge.** The inverse-transform sibling of
`l2Fourier_eq_fourierIntegral`: for `f ∈ L¹ ∩ L²`, the coeFn of the `L²`-inverse-Fourier transform
of the canonical `Lp` representative agrees almost everywhere with the classical `L¹` inverse
Fourier integral `𝓕⁻ f`. Used by `bandlimited_sup_bound` to realize a band-limited signal as the
inverse transform of its (compactly supported, hence `L¹`) spectrum.

@audit:ok -/
theorem l2FourierInv_eq_fourierIntegralInv (f : ℝ → ℂ)
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume) :
    ((𝓕⁻ (hf2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  have hf1_int : Integrable f volume := memLp_one_iff_integrable.mp hf1
  set G : Lp ℂ 2 volume := 𝓕⁻ (hf2.toLp f) with hG
  have hlocG : LocallyIntegrable (⇑G) volume :=
    (Lp.memLp G).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcont_Ff : Continuous (𝓕⁻ f) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := -innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hf1_int
  have hlocFf : LocallyIntegrable (𝓕⁻ f) volume := hcont_Ff.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hlocG hlocFf ?_
  intro g hg_diff hg_supp
  have hφ1 : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_supp.comp_left rfl
  have hφ2 : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg_diff
  set φ : 𝓢(ℝ, ℂ) := hφ1.toSchwartzMap hφ2 with hφdef
  have hφ_coe : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have hsmul : ∀ (x : ℝ) (z : ℂ), g x • z = φ x • z := by
    intro x z
    rw [hφ_coe, Complex.real_smul, smul_eq_mul]
  have hdist : (G : 𝓢'(ℝ, ℂ)) = 𝓕⁻ ((hf2.toLp f : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) := by
    rw [hG]; exact (Lp.fourierInv_toTemperedDistribution_eq (hf2.toLp f)).symm
  have hA : ∫ x, g x • (⇑G) x ∂volume = ∫ x, (𝓕⁻ φ : 𝓢(ℝ, ℂ)) x • f x ∂volume := by
    calc ∫ x, g x • (⇑G) x ∂volume
        = ∫ x, φ x • (⇑G) x ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hsmul x (G x))
      _ = (G : 𝓢'(ℝ, ℂ)) φ := (Lp.toTemperedDistribution_apply G φ).symm
      _ = 𝓕⁻ ((hf2.toLp f : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) φ := by rw [hdist]
      _ = ((hf2.toLp f : Lp ℂ 2 volume) : 𝓢'(ℝ, ℂ)) (𝓕⁻ φ) :=
          TemperedDistribution.fourierInv_apply _ _
      _ = ∫ x, (𝓕⁻ φ : 𝓢(ℝ, ℂ)) x • (hf2.toLp f : ℝ → ℂ) x ∂volume :=
          Lp.toTemperedDistribution_apply _ _
      _ = ∫ x, (𝓕⁻ φ : 𝓢(ℝ, ℂ)) x • f x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hf2.coeFn_toLp] with x hx
          rw [hx]
  have hB : ∫ x, g x • (𝓕⁻ f) x ∂volume = ∫ x, (𝓕⁻ φ : 𝓢(ℝ, ℂ)) x • f x ∂volume := by
    have hstep : ∫ x, g x • (𝓕⁻ f) x ∂volume = ∫ x, φ x • (𝓕⁻ f) x ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => hsmul x (𝓕⁻ f x))
    have hFTinv : ∀ h : ℝ → ℂ, 𝓕⁻ h = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) h :=
      fun _ => rfl
    have hflip : (-innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = -innerₗ ℝ :=
      LinearMap.ext fun a => LinearMap.ext fun b => by
        simp only [LinearMap.flip_apply, LinearMap.neg_apply, innerₗ_apply_apply,
          real_inner_comm b a]
    rw [hstep]
    simp only [SchwartzMap.fourierInv_coe, hFTinv]
    simpa [hflip] using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ ℝ)
        Real.continuous_fourierChar (by fun_prop) φ.integrable hf1_int).symm
  rw [hA, hB]

/-- **Paley-Wiener sup bound**: a continuous band-limited `L²` signal is bounded pointwise by its
`L²` energy, `|f t| ≤ √(2W)·‖f‖₂`. Continuity pins the raw codeword to the canonical
representative, and this bound caps the sample values by the codeword energy — dissolving the
pointwise-vs-a.e. defect that made an `encoder`-only code unbounded.

The proof realizes the signal as the inverse Fourier transform of its (compactly supported, hence
`L¹`) spectrum via `l2FourierInv_eq_fourierIntegralInv`, bounds the pointwise inverse transform by
the `L¹` norm of the spectrum, and closes with Hölder on `[-W, W]` and Plancherel.

@audit:ok -/
theorem bandlimited_sup_bound (f : ℝ → ℝ) (W : ℝ) (hW : 0 < W)
    (hf : MemLp f 2 volume) (hbl : IsBandlimited f W) (hcont : Continuous f) (t : ℝ) :
    |f t| ≤ Real.sqrt (2 * W) * (eLpNorm f 2 volume).toReal := by
  obtain ⟨hfc2, hspec⟩ := hbl
  set fc : ℝ → ℂ := fun t => (f t : ℂ) with hfcdef
  set G : Lp ℂ 2 volume := 𝓕 (hfc2.toLp fc) with hG
  -- The band `S = [-W, W]`; its complement is the essential support of `hspec`.
  set S : Set ℝ := Set.Icc (-W) W with hSdef
  have hS_meas : MeasurableSet S := measurableSet_Icc
  have hSc_meas : MeasurableSet Sᶜ := hS_meas.compl
  have hSc : Sᶜ = {ξ : ℝ | W < |ξ|} := by
    ext x
    simp only [hSdef, Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le, not_le]
  rw [← hSc] at hspec
  have hvolS : volume S = ENNReal.ofReal (2 * W) := by
    rw [hSdef, Real.volume_Icc]; ring_nf
  -- (b) `G` vanishes a.e. off `S`, hence `G ∈ L¹`.
  have hcompl0 : Sᶜ.indicator (⇑G) =ᵐ[volume] 0 :=
    indicator_ae_eq_zero_of_restrict_ae_eq_zero hSc_meas hspec
  have hind_eq : (⇑G) =ᵐ[volume] S.indicator (⇑G) := by
    filter_upwards [hcompl0] with x hx
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
    · rw [Set.indicator_of_notMem hxS]
      have hxSc : x ∈ Sᶜ := hxS
      rw [show (⇑G) x = Sᶜ.indicator (⇑G) x from (Set.indicator_of_mem hxSc _).symm]
      simpa using hx
  have hG1 : MemLp (⇑G) 1 volume := by
    have hind_L1 : MemLp (S.indicator (⇑G)) 1 volume :=
      ((Lp.memLp G).indicator hS_meas).mono_exponent_of_measure_support_ne_top
        (s := S) (fun x hx => Set.indicator_of_notMem hx _)
        (by rw [hvolS]; exact ENNReal.ofReal_ne_top) (by norm_num)
    exact (memLp_congr_ae hind_eq).mpr hind_L1
  have hG1_int : Integrable (⇑G) volume := memLp_one_iff_integrable.mp hG1
  -- (c) `fc =ᵐ 𝓕⁻ ⇑G` via the inverse bridge and the `L²` Fourier pair.
  have hfc_ae : fc =ᵐ[volume] 𝓕⁻ (⇑G) := by
    have hbridge := l2FourierInv_eq_fourierIntegralInv (⇑G) hG1 (Lp.memLp G)
    have hinv : 𝓕⁻ (𝓕 (hfc2.toLp fc)) = hfc2.toLp fc := by simp
    rw [Lp.toLp_coeFn G (Lp.memLp G), hG, hinv] at hbridge
    exact (hfc2.coeFn_toLp.symm).trans hbridge
  -- (d) both sides are continuous, so the a.e. equality is everywhere.
  have hfc_cont : Continuous fc := Complex.continuous_ofReal.comp hcont
  have hFinv_cont : Continuous (𝓕⁻ (⇑G)) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := -innerₗ ℝ)
      Real.continuous_fourierChar (by fun_prop) hG1_int
  have hpt : fc = 𝓕⁻ (⇑G) := (hfc_cont.ae_eq_iff_eq (μ := volume) hFinv_cont).mp hfc_ae
  -- (e) `|f t| = ‖𝓕⁻ ⇑G t‖ ≤ ∫ ‖⇑G‖`.
  have he : |f t| ≤ ∫ ξ, ‖(⇑G) ξ‖ ∂volume := by
    have hfeq : (f t : ℂ) = 𝓕⁻ (⇑G) t := congrFun hpt t
    rw [show |f t| = ‖(f t : ℂ)‖ from by rw [Complex.norm_real, Real.norm_eq_abs],
      hfeq, Real.fourierInv_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [Circle.norm_smul]
  -- (f)+(g) `∫ ‖⇑G‖ ≤ √(2W)·‖f‖₂` by Hölder on `S` and Plancherel.
  have h_int_eq : ∫ ξ, ‖(⇑G) ξ‖ ∂volume = (eLpNorm (⇑G) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hG1_int,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  have hnorm : (eLpNorm (⇑G) 2 volume).toReal = (eLpNorm f 2 volume).toReal := by
    rw [← Lp.norm_def G, hG, Lp.norm_fourier_eq, Lp.norm_def]
    congr 1
    rw [eLpNorm_congr_ae hfc2.coeFn_toLp]
    exact eLpNorm_congr_norm_ae
      (Filter.Eventually.of_forall fun x => by simp only [hfcdef, Complex.norm_real])
  have h_holder :
      eLpNorm (⇑G) 1 volume ≤ eLpNorm (⇑G) 2 volume * ENNReal.ofReal (Real.sqrt (2 * W)) := by
    have e1 : eLpNorm (⇑G) 1 volume = eLpNorm (⇑G) 1 (volume.restrict S) := by
      rw [eLpNorm_congr_ae hind_eq, eLpNorm_indicator_eq_eLpNorm_restrict hS_meas]
    have e2 : eLpNorm (⇑G) 2 volume = eLpNorm (⇑G) 2 (volume.restrict S) := by
      rw [eLpNorm_congr_ae hind_eq, eLpNorm_indicator_eq_eLpNorm_restrict hS_meas]
    rw [e1, e2]
    have hae : AEStronglyMeasurable (⇑G) (volume.restrict S) :=
      (Lp.memLp G).aestronglyMeasurable.restrict
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hae).trans
      (le_of_eq ?_)
    congr 1
    have hb : (0 : ℝ) ≤ 2 * W := by positivity
    rw [Measure.restrict_apply_univ, hvolS,
      show (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) from by norm_num,
      Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hb (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine he.trans ?_
  calc ∫ ξ, ‖(⇑G) ξ‖ ∂volume
      = (eLpNorm (⇑G) 1 volume).toReal := h_int_eq
    _ ≤ (eLpNorm (⇑G) 2 volume * ENNReal.ofReal (Real.sqrt (2 * W))).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top (Lp.memLp G).2.ne ENNReal.ofReal_ne_top) h_holder
    _ = (eLpNorm (⇑G) 2 volume).toReal * Real.sqrt (2 * W) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    _ = Real.sqrt (2 * W) * (eLpNorm f 2 volume).toReal := by rw [hnorm, mul_comm]

/-! ## §B — Continuous-time AWGN code -/

/-- A continuous-time AWGN code over the window `[0, T]` with bandwidth `W`, average power
`P`, and `M` messages.

The encoder maps each message to a genuine band-limited *function* `ℝ → ℝ` (never a fixed
sample vector — this is the non-circularity constraint C1), whose whole-line energy is at most
`T · P`. The receiver does not read the codeword pointwise; it correlates it against `k`
**orthonormal test functions supported in `[0, T]`**, observing the vector
`i ↦ ∫ (encoder m)·(testFn i)` corrupted by independent Gaussian noise
(`ContAwgnCode.observation`, `ContAwgnCode.errorProbAt`). This is the textbook Karhunen-Loève /
matched-filter discretization of the channel: against an orthonormal family the coefficients of
white noise are *exactly* i.i.d. `N(0, N₀/2)`, which is what makes the product law `Measure.pi`
in `errorProbAt` an exact description of the physical channel rather than a surrogate for one.
It replaces a point-sampling observation map that was an isometry only at the Nyquist spacing —
i.e. calibrated at exactly the value the Shannon-Hartley identity has to prove; the refutation is
recorded in `docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP.

The observation count `k` is a *free* `ℕ` field (constraint C4), and no field mentions `2W` or
`⌊2WT⌋` (constraint C3): `testFn` is asked only to be orthonormal and supported in `[0, T]`, and
the `W` in `encoder_bandlimited` is a physical bandwidth, not a dimension count. The `≈ 2WT`
degrees-of-freedom count is therefore not available from this definition. It has to come from the
prolate-spheroidal eigenvalue distribution: a band-limited `f` satisfies `∫ f·φᵢ = ⟪f, P_W φᵢ⟫`,
so the Gram matrix of the test family is a compression of the time-band-limiting operator of
`TimeBandLimiting.lean`, and how many of its eigenvalues sit near `1` is exactly the
Landau-Pollak-Slepian count. -/
structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  /-- The `M` band-limited codewords, one per message. -/
  encoder : Fin M → (ℝ → ℝ)
  /-- Each codeword lies in `L²` (regularity: together with `testFn_memLp` this makes every
  observation integral `∫ (encoder m)·(testFn i)` well-defined, by Cauchy-Schwarz). -/
  encoder_memLp : ∀ m, MemLp (encoder m) 2 volume
  /-- Each codeword is band-limited to `[-W, W]`. -/
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W
  /-- Average-power constraint: the whole-line energy of each codeword is at most `T · P`. The
  budget is over all of `ℝ`, not just the window: a band-limited signal cannot be supported in
  `[0, T]`, and charging it only for the energy it happens to park inside the window leaves the
  rest free to be reflected back in by the reproducing kernel. -/
  encoder_power : ∀ m, (∫ t, (encoder m t) ^ 2) ≤ T * P
  /-- The number of observations (a free `ℕ` parameter; constraint C4). -/
  k : ℕ
  /-- The test functions the receiver correlates the codeword against. -/
  testFn : Fin k → (ℝ → ℝ)
  /-- Each test function lies in `L²` (regularity, paired with `encoder_memLp`). -/
  testFn_memLp : ∀ i, MemLp (testFn i) 2 volume
  /-- Each test function is supported in the window `[0, T]`: the receiver may listen only while
  the codeword is being transmitted. -/
  testFn_support : ∀ i, Function.support (testFn i) ⊆ Set.Icc (0 : ℝ) T
  /-- The test functions are orthonormal. This is the field that makes the coefficients of white
  noise against them exactly i.i.d., hence `ContAwgnCode.errorProbAt`'s product law exact. -/
  testFn_orthonormal : ∀ i j, (∫ t, testFn i t * testFn j t) = if i = j then 1 else 0
  /-- The decoder maps the observation vector back to a message. -/
  decoder : (Fin k → ℝ) → Fin M
  /-- The decoder is measurable (needed on the continuous output alphabet). -/
  decoder_meas : Measurable decoder

/-- The noiseless observation of message `m` along the `i`-th test function: the correlation
`∫ (encoder m)·(testFn i)` of the codeword with the matched filter `testFn i`.

This is the analysis half of the Karhunen-Loève discretization. It depends on `encoder m` only
through its a.e. class, and is finite because `encoder_memLp` and `testFn_memLp` put both factors
in `L²`. Since `testFn i` is supported in `[0, T]`, the integral only sees the codeword during the
transmission window; since `encoder m` is band-limited, `∫ f·φᵢ = ⟪f, P_W φᵢ⟫`, which is what
routes the degrees-of-freedom question to the spectrum of the time-band-limiting operator. -/
noncomputable def ContAwgnCode.observation {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (m : Fin M) (i : Fin c.k) : ℝ :=
  ∫ t, c.encoder m t * c.testFn i t

/-- Point-wise error probability for message `m`: the noisy observation vector
`y = ContAwgnCode.observation m + noise` (per-observation noise variance `N₀/2`, independent
across observations) lands in the decoding-error region `{y | decoder y ≠ m}`.

Modelled directly as `Measure.pi (fun i => gaussianReal (observationᵢ) (N₀/2))`, i.e. the
memoryless per-observation AWGN law — the same law computed by the discrete
`ChannelCoding.Code.errorProbAt` for `awgnChannel (N₀/2)`, but inlined so that no
`IsAwgnChannelMeasurable` kernel-measurability hypothesis is needed inside the definition.

The product law is exact here, not an approximation: the noise coefficients are `⟪ξ, φᵢ⟫` for the
orthonormal family `testFn`, and the coefficients of white noise along an orthonormal family are
i.i.d. `N(0, N₀/2)` for that family alone — no spacing, rate or bandwidth condition enters. This
is what `ContAwgnCode.testFn_orthonormal` buys. -/
noncomputable def ContAwgnCode.errorProbAt {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) (m : Fin M) : ℝ≥0∞ :=
  Measure.pi (fun i : Fin c.k =>
      gaussianReal (c.observation m i) (N₀ / 2).toNNReal)
    {y : Fin c.k → ℝ | c.decoder y ≠ m}

/-- Average error probability under a uniform message: `(1/M) ∑ₘ errorProbAt m`
(`0` for the empty code `M = 0`). -/
noncomputable def ContAwgnCode.averageError {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) : ℝ≥0∞ :=
  if M = 0 then 0 else (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt N₀ m

/-! ## §C — Operational capacity -/

/-- The largest number of messages distinguishable over the window `[0, T]` with average
error probability at most `ε` — an *operational* primitive that contains no `2W` or
`⌊2WT⌋` (constraint C2). -/
noncomputable def contAwgnMaxMessages (T W N₀ P ε : ℝ) : ℕ :=
  sSup { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε }

/-- The per-second rate achievable at error level `ε`: `limsup_T (log M(T, ε)) / T`. -/
noncomputable def contAwgnRate (W N₀ P ε : ℝ) : ℝ :=
  Filter.limsup (fun T : ℝ => Real.log (contAwgnMaxMessages T W N₀ P ε : ℝ) / T) atTop

/-- The **operational capacity** of the continuous-time band-limited AWGN channel:
the per-second rate in the vanishing-error limit, `⨅_{ε ∈ (0,1)} contAwgnRate W N₀ P ε`.
The infimum over `ε` extracts the `ε → 0` capacity; `ε` is restricted to `(0, 1)` because
`ε ≥ 1` is satisfied by every code (average error is `≤ 1`) and would make the message set
unbounded. -/
noncomputable def contAwgnOperationalCapacity (W N₀ P : ℝ) : ℝ :=
  ⨅ ε ∈ Set.Ioo (0 : ℝ) 1, contAwgnRate W N₀ P ε

/-! ## §D — Shannon-Hartley identity -/

/-- The **continuous-time Shannon-Hartley formula**: the operational capacity of the
band-limited AWGN channel equals `W · log(1 + P/(N₀·W))`.

Under the Karhunen-Loève observation map of `ContAwgnCode` this statement is expected true; an
earlier point-sampling model made it false as framed, and the def-fix that repaired it is recorded
in `docs/shannon/shannon-hartley-facts.md` §OBSERVATION-MAP. What remains is the genuine
mathematical obstruction, which no change of definition can remove: the time-bandwidth
degrees-of-freedom count.

Both halves need it. `∫ f·φᵢ = ⟪f, P_W φᵢ⟫` for band-limited `f`, so the Gram matrix of the test
family is a compression of the time-band-limiting operator `timeBandLimitingOp T W`
(`TimeBandLimiting.lean`), and the achievable rate along any `[0, T]`-supported orthonormal family
is governed by that compression's eigenvalues, which Cauchy interlacing caps by the prolate
eigenvalues `prolateEigenvalues T W`. Reaching the closed form in the limit requires `≈ 2WT` of
them to sit near `1` and the rest near `0` — the Landau-Pollak-Slepian concentration, whose
statement is `prolate_eigenvalue_count` (Leg E of
`shannon-hartley-phase2-spectral-plan`). The converse needs the upper half of the count, the
achievability (`contAwgn_ge_shannonHartley`) the lower half.

Note the asymmetry that certifies the def-fix was a repair and not a disguise: the crude bound of
`contAwgnMaxMessages_bddAbove` closes by Bessel alone, wall-free, but caps the rate only at
`P/N₀`, and `ln(1+x) ≤ x` makes that strictly larger than the closed form. Boundedness comes for
free; the exact constant does not.

Hypotheses `hW`/`hN₀`/`hP` are regularity-only (not load-bearing).

`@residual(wall:nyquist-2w-dof)` -/
@[entry_point]
theorem contAwgn_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  -- Blocked on the `≈ 2WT` prolate eigenvalue count (Leg E); see docstring.
  sorry -- @residual(wall:nyquist-2w-dof)

end InformationTheory.Shannon.ShannonHartley
