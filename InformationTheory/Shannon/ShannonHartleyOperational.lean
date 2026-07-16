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

as `contAwgn_eq_shannonHartley`. That theorem is currently false as framed and is published with
a `sorry` body carrying `@audit:defect(false-statement)`; the intended mathematical content (the
prolate-spheroidal / Landau-Pollak-Slepian time-bandwidth degrees-of-freedom count) is a genuine
Mathlib gap, but it is not what blocks the statement today. The definition is non-circular but not
faithful: the observation map is a surrogate for the physical channel rather than a model of it,
and that is the decisive defect.

`IsBandlimited` uses the *L²-Fourier spectral support* of the complexification (a genuine
band-limit constraint, not junk-`0`), and `ContAwgnCode.encoder` carries `encoder_continuous` +
`encoder_memLp` regularity fields that pin each codeword to its canonical continuous `L²`
representative. The Paley-Wiener sup bound `bandlimited_sup_bound` (`|f(t)| ≤ √(2W)·‖f‖₂`) is
fully proven (`sorryAx`-free) over the `L²↔L¹` Fourier-agreement bridges
`l2Fourier_eq_fourierIntegral` / `l2FourierInv_eq_fourierIntegralInv`; it caps the pointwise
samples by the *full-line* `L²` energy `‖f‖₂` (the norm over all of `ℝ`).

There is, however, no tie from `‖f‖₂` to the *window* energy `∫_{[0,T]} f² ≤ T·P`: `ContAwgnCode`
has no essential-time-limitation field, and attributing such a tie to the degrees-of-freedom count
was an error. The window-energy-to-point-value ratio of a band-limited signal is in fact
unbounded, which refutes `contAwgnMaxMessages_bddAbove` and, through the ℕ-`sSup` junk value,
`contAwgn_eq_shannonHartley` as well.

Restoring that tie is not sufficient, and the two theorems part company here. Constraining the
full-line energy repairs `contAwgnMaxMessages_bddAbove`, but the identity stays false, because a
second defect sits in the observation map rather than in the input class: `sampledSignal` is an
isometry only at the Nyquist spacing and `ContAwgnCode.errorProbAt` prices the noise as if the
spacing were always Nyquist, while `sampleCount` is free to be coarser. Time-limiting the codewords
does not repair it either. Details, refutation and counterexample are recorded on those
declarations and on `ContAwgnCode`; the def-fix — an orthonormal-test-function observation map,
with the full-line power constraint as one component — is pending under
`shannon-hartley-phase2-spectral-plan`.

## Main definitions

* `IsBandlimited f W` — the L²-Fourier transform of the complexification of `f : ℝ → ℝ` has
  spectral support in `[-W, W]` (vanishes a.e. on `{ξ | W < |ξ|}`).
* `ContAwgnCode T W P M` — a continuous-time AWGN code: `M` band-limited signals
  (average power `≤ P` over the window `[0, T]`) together with a decoder acting on a *free*
  number `sampleCount` of observations. The window-only power constraint makes this class too
  broad, and the point-sampling observation map is unfaithful on top of that; see the defect note
  on the structure.
* `contAwgnOperationalCapacity W N₀ P` — the per-second operational rate
  `⨅ ε, limsup_T (log M(T, ε)) / T`.

## Main statements

* `contAwgn_eq_shannonHartley` — the operational capacity equals the Shannon-Hartley
  closed form `bandlimitedAwgnCapacity W N₀ P`.

## Implementation notes — the three honesty risks and how the definition fares

The definition aims to make `contAwgn_eq_shannonHartley` *true*, *non-circular*, and
*non-degenerate*. Non-circularity and non-degeneracy hold as described below; truth does not,
which is exactly why the statement carries a defect marker rather than a wall tag.

* **Truth (not attained).** Observations are the `√(T/n)`-normalized samples `sampledSignal`,
  each corrupted by independent Gaussian noise of variance `N₀/2` — the standard Nyquist
  per-sample noise. At the Nyquist rate, and for signals whose energy really lives in `[0, T]`,
  the discrete energy `∑ᵢ (T/n)·f(t_i)²` tracks `∫_{[0,T]} f² ≤ T·P`, giving per-dimension SNR
  `(T·P/(2WT)) / (N₀/2) = P/(N₀·W)` and per-second rate `W·log(1 + P/(N₀·W))`, matching
  `bandlimitedAwgnCapacity`. That correspondence is a Riemann-sum heuristic, not an identity: at
  fixed `n` the discrete energy is *not* pinned by `∫_{[0,T]} f²`. For `n = 1` it is `T·f(0)²`,
  which the window constraint leaves unbounded. Truth therefore fails as framed, and it fails for
  a second reason that no constraint on the codewords can remove: the whole per-dimension SNR
  computation above is valid only at the Nyquist spacing, which the code is free not to use (see
  the defect notes on `ContAwgnCode`, `sampledSignal` and `ContAwgnCode.errorProbAt`).
* **Non-circularity (C1–C4).** A codeword is a genuine band-limited *function* `ℝ → ℝ`
  (C1), never a length-`⌊2WT⌋` sample vector; `contAwgnMaxMessages` contains no `2W` or
  `⌊2WT⌋` (C2); the observation count `sampleCount` is a *free* `ℕ` field, not pinned to
  `⌊2WT⌋` (C4); the factor `2W` is not in any definition and must emerge from the DOF proof
  (C3). Consequently `contAwgn_eq_shannonHartley` cannot be closed by `rfl`/`unfold`.
* **Non-degeneracy (partial).** The noise genuinely corrupts the signal (variance `N₀/2 > 0`
  whenever `N₀ > 0`), and the `√(T/n)` normalization does stop *oversampling* from inflating the
  signal-to-noise ratio. That is the wrong direction to guard, however, and the normalization
  guards only it: the scaling is an isometry solely at the Nyquist spacing, so *under*-sampling
  inflates the signal-to-noise ratio instead, by a factor the free `sampleCount` may choose. Nor
  does the normalization bound the capacity: even at `n = 1` the single in-window sample
  `√T·f(0)` is unconstrained, because an integral bound on `∫_{[0,T]} f²` does not control a point
  value. For band-limited `f` the pointwise bound available is `|f(t)| ≤ √(2W)·‖f‖₂` through the
  *full-line* norm, which `encoder_power` leaves free.

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
sample vector — this is the non-circularity constraint C1), with average power `≤ P` over
`[0, T]`. The decoder acts on a *free* number `sampleCount` of observations (constraint C4: the
observation count is not pinned to `⌊2WT⌋`).

This model carries two independent defects, and the theorems quantifying over it are false as a
result.

The first is in the input class. `encoder_power` constrains only the energy inside the window
`[0, T]`, and no field imposes essential time-limitation or a full-line energy budget. A
band-limited signal may therefore hold arbitrary energy outside `[0, T]` and, through the sinc
reproducing-kernel tail, exhibit an arbitrarily large in-window point value at fixed window
energy — the classical superdirectivity / superoscillation paradox. This is what refutes
`contAwgnMaxMessages_bddAbove`, and constraining the whole-line energy `‖encoder m‖₂` does repair
that theorem.

The second is in the observation map (`sampledSignal` and `ContAwgnCode.errorProbAt`), and it
survives the first repair, so it is what refutes `contAwgn_eq_shannonHartley`. Because
`sampleCount` is free, a code may sample *below* the Nyquist rate; the `√(T/n)` scaling is an
isometry only at the Nyquist spacing, while the per-sample noise variance is held fixed
independently of the spacing. Sub-Nyquist sampling therefore inflates the signal-to-noise ratio,
and a whole-line energy budget does not prevent it. Time-limiting the codewords does not prevent
it either: the counterexample's signal already concentrates essentially all of its energy inside
the window. The repair is to discretize the observation against an orthonormal family supported
in `[0, T]` (the Karhunen-Loève / matched-filter construction), which makes the independent
per-sample noise law exact rather than a surrogate; a whole-line power constraint is one
component of it. It is deliberately not applied here, since it changes the theory's statements.

The defect is not that this structure is false — it is inhabited and internally consistent — but
that it under-constrains the object it models. That is the `cause:signature-drops-constraint`
axis, understood to run through the observation map as well as through `encoder_power`: the
dropped constraint is not only the codeword energy but the fidelity of the sampling model to the
channel it stands for. `degenerate` is the closest available defect kind (the kind dichotomy in
`docs/audit/audit-tags.md` routes a not-FALSE definition here); it is not `false-hypothesis`,
which denotes a predicate with a refutation and vacuously-true consumers — the inverse failure of
this one.

@audit:defect(degenerate) @audit:closed-by-successor(shannon-hartley-phase2-spectral-plan) -/
structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  /-- The `M` band-limited codewords, one per message. -/
  encoder : Fin M → (ℝ → ℝ)
  /-- Each codeword lies in `L²` (regularity: makes the pointwise samples well-defined and
  supplies the energy the Paley-Wiener sup bound caps against). -/
  encoder_memLp : ∀ m, MemLp (encoder m) 2 volume
  /-- Each codeword is continuous (regularity: pins the codeword to its canonical representative,
  so the pointwise `sampledSignal` reads a determinate value rather than an a.e.-class artifact). -/
  encoder_continuous : ∀ m, Continuous (encoder m)
  /-- Each codeword is band-limited to `[-W, W]`. -/
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W
  /-- Average-power constraint: energy over `[0, T]` is at most `T · P`. This window-only
  constraint is one of the two defects recorded above: it leaves the full-line energy
  `‖encoder m‖₂` free, so it does not pin the in-window samples, and that is what refutes
  `contAwgnMaxMessages_bddAbove`. Constraining the full-line energy repairs that theorem but not
  the Shannon-Hartley identity, whose falsity comes from the observation map instead. -/
  encoder_power : ∀ m, (∫ t in Set.Icc (0 : ℝ) T, (encoder m t) ^ 2) ≤ T * P
  /-- The number of observed samples (a free `ℕ` parameter; constraint C4). -/
  sampleCount : ℕ
  /-- The decoder maps the observation vector back to a message. -/
  decoder : (Fin sampleCount → ℝ) → Fin M
  /-- The decoder is measurable (needed on the continuous output alphabet). -/
  decoder_meas : Measurable decoder

/-- The Nyquist-normalized sample vector of `f` over `[0, T]` with `n` samples: the value at
`t_i = i · T / n` scaled by `√(T/n)`. The `√(T/n)` scaling makes the discrete `ℓ²` energy
`∑ᵢ (sampledSignal f T n i)²` a Riemann sum for the continuous energy `∫_{[0,T]} f²`.

This scaling is an isometry on band-limited signals only at the Nyquist spacing `Δ = 1/(2W)`. It
is calibrated at exactly the one parameter value that the Shannon-Hartley identity is supposed to
prove, which makes this definition a surrogate for the physical observation rather than a
faithful model of it, and it is the reason `contAwgn_eq_shannonHartley` is false as framed. The
leak runs opposite to the direction one expects: oversampling (`n → ∞`) does not inflate the
signal-to-noise ratio, but *under*-sampling does. Since `ContAwgnCode.sampleCount` is free, a code
may choose a spacing `Δ` coarser than Nyquist; at such a spacing the reproducing kernels at the
sample points are mutually orthogonal, so a sample vector of given `ℓ²` norm is carried by a
band-limited interpolant of proportionally *smaller* energy, and the energy budget admits sample
vectors inflated by the factor `2WΔ` — against a per-sample noise level that
`ContAwgnCode.errorProbAt` holds fixed. The rate obtained this way exceeds the Shannon-Hartley
value, by an unbounded ratio at low signal-to-noise; the exact statement and its verification live
in `docs/shannon/shannon-hartley-facts.md`.

The discrete and continuous energies also disagree at fixed `n` for a separate reason: for
`n = 1` the discrete energy is `T · f(0)²`, which no bound on `∫_{[0,T]} f²` controls. Reading
this correspondence as an exact isometry is what made `contAwgnMaxMessages_bddAbove` look
provable; it is false. -/
noncomputable def sampledSignal (f : ℝ → ℝ) (T : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => Real.sqrt (T / (n : ℝ)) * f (((i : ℕ) : ℝ) * (T / (n : ℝ)))

/-- Point-wise error probability for message `m`: the noisy observation
`y = sampledSignal (encoder m) + noise` (per-sample noise variance `N₀/2`, independent
across samples) lands in the decoding-error region `{y | decoder y ≠ m}`.

Modelled directly as `Measure.pi (fun i => gaussianReal (sampleᵢ) (N₀/2))`, i.e. the
memoryless per-sample AWGN law — the same law computed by the discrete
`ChannelCoding.Code.errorProbAt` for `awgnChannel (N₀/2)`, but inlined so that no
`IsAwgnChannelMeasurable` kernel-measurability hypothesis is needed inside the definition.

Both the fixed per-sample variance `N₀/2` and the independence across samples are correct only at
the Nyquist spacing. The true covariance of band-limited noise on the sample vector at spacing `Δ`
is `(N₀/2) · Δ · G`, where `G` is the Gram matrix of the reproducing kernels at the sample points;
`G` is diagonal exactly when `2WΔ` is an integer, and the variance it yields then scales with `Δ`
rather than staying fixed. So `Measure.pi` is an exact description of the physical channel only at
`Δ = 1/(2W)`, and holding the variance fixed while `sampleCount` is free is the half of the
observation-map defect that pairs with the `sampledSignal` scaling: together they let a
sub-Nyquist code buy signal energy without paying in noise. Recovering an exact independent
per-sample law requires the orthonormal-test-function repair described on `ContAwgnCode`. -/
noncomputable def ContAwgnCode.errorProbAt {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) (m : Fin M) : ℝ≥0∞ :=
  Measure.pi (fun i : Fin c.sampleCount =>
      gaussianReal (sampledSignal (c.encoder m) T c.sampleCount i) (N₀ / 2).toNNReal)
    {y : Fin c.sampleCount → ℝ | c.decoder y ≠ m}

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

This statement is false as framed for every `P > 0`, so the `sorry` below can never be filled. It
is kept in defect form because the falsity lives in the `ContAwgnCode` model, whose repair is a
separate decision; the intended mathematical content (the time-bandwidth degrees-of-freedom count)
is unaffected and remains the genuine obstruction for the repaired statement.

Two independent mechanisms make it false, and repairing either one alone leaves it false.

The first runs through `contAwgnMaxMessages_bddAbove`, which is itself false: `ContAwgnCode`
constrains only the window energy, and the window-energy-to-point-value ratio of a band-limited
signal is unbounded, so a one-sample scaled-superoscillation code achieves every `M` at every
error level (the refutation and the explicit counterexample are recorded on that declaration).
Falsity then propagates here by the junk-value chain: `¬ BddAbove` gives
`contAwgnMaxMessages = 0` via `Nat.sSup_of_not_bddAbove`, hence `contAwgnRate = 0` via
`Real.log_zero`, hence `contAwgnOperationalCapacity W N₀ P = 0`, while
`bandlimitedAwgnCapacity W N₀ P > 0` whenever `P > 0`.

The second is independent of the power constraint and survives its repair. Constraining the
full-line energy `‖f‖₂ ≤ T·P` does restore `contAwgnMaxMessages_bddAbove`, but it does not restore
this identity: the observation map is itself unfaithful. Since `sampleCount` is free, a code may
sample below the Nyquist rate, where `sampledSignal`'s `√(T/n)` scaling is no longer an isometry
and `ContAwgnCode.errorProbAt`'s fixed per-sample variance is no longer the true noise law; the
resulting capacity strictly exceeds the closed form, by an unbounded ratio at low
signal-to-noise. The mechanism is recorded on those two declarations. So the earlier account —
that the falsity is the absence of a tie between `‖f‖₂` and the window energy `∫_{[0,T]} f² ≤ T·P`,
and that the Paley-Wiener sup bound `bandlimited_sup_bound` (`|f(t)| ≤ √(2W)·‖f‖₂`) would then cap
the samples — identifies a real gap but not the decisive one: restoring that tie does not make
this statement true.

The repair is therefore the observation-map def-fix, replacing point sampling with an orthonormal
family supported in `[0, T]`, with the full-line power constraint as one component. Hypotheses
`hW`/`hN₀`/`hP` are regularity-only (not load-bearing). The def-fix is pending under
`shannon-hartley-phase2-spectral-plan`.

`@residual(defect:false-statement)` `@audit:defect(false-statement)`
`@audit:closed-by-successor(shannon-hartley-phase2-spectral-plan)` -/
@[entry_point]
theorem contAwgn_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  -- FALSE as framed (see docstring): unfillable pending the observation-map def-fix of
  -- `ContAwgnCode` (repairing `encoder_power` alone leaves it false).
  sorry -- @residual(defect:false-statement)

end InformationTheory.Shannon.ShannonHartley
