import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.L2Space
import InformationTheory.Shannon.NormalizedSinc
import InformationTheory.Meta.EntryPoint

/-!
# Whittaker–Shannon sampling theorem (Fourier-series route, Cover–Thomas Ch. 9.6)

This file proves the Whittaker–Shannon (cardinal series) sampling theorem via the
**L² Fourier series on the circle** route, reusing the normalized sinc scaffolding of
`NormalizedSinc.lean`.

The honest core (unconditional) is `whittaker_shannon_hasSum`: for an L² spectrum
`F : Lp ℂ 2 (haarAddCircle (T := 1))`, the reconstructed signal `wsSignal F` is recovered
from its integer samples by the cardinal series
`wsSignal F t = ∑' n, wsSignal F n · sincN (t - n)` (as a `HasSum`).

## Main statements

* `wsExp` — the evaluation kernel `ξ ↦ e^{-2πiξt}` as an L² element of `AddCircle 1`.
* `wsSignal` — the band-limited signal reconstructed from an L² spectrum `F`.
* `inner_wsExp_fourierLp` — the monomial pairing collapses to a normalized sinc.
* `fourierCoeff_eq_wsSignal` — a Fourier coefficient equals a sample value.
* `whittaker_shannon_hasSum` — the cardinal series, per-`t` `HasSum` form (unconditional).
* `whittaker_shannon_bandlimited` — real-line band-limited textbook wrapper (stretch).
-/

open MeasureTheory Real Complex intervalIntegral
open scoped FourierTransform ComplexInnerProductSpace ComplexConjugate

namespace InformationTheory.Shannon.WhittakerShannon

open InformationTheory.Shannon.NormalizedSinc

/-- `Fact (0 < 1)` so `AddCircle 1` carries `haarAddCircle`. -/
instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- The evaluation kernel as a real-line function `s ↦ e^{-2πist}`. -/
noncomputable def wsExpFun (t : ℝ) : ℝ → ℂ :=
  fun s => Complex.exp ((-(2 * π * t * s) : ℝ) * Complex.I)

/-- The evaluation kernel `ξ ↦ e^{-2πiξt}` as an `L²` element of the unit circle. -/
noncomputable def wsExp (t : ℝ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  MemLp.toLp (AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun t)) <| by
    apply MemLp.haarAddCircle
    apply MemLp.memLp_liftIoc
    have hcont : Continuous (wsExpFun t) := by
      unfold wsExpFun; fun_prop
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    refine MemLp.of_bound hcont.aestronglyMeasurable 1 ?_
    filter_upwards with s
    simp only [wsExpFun, Complex.norm_exp_ofReal_mul_I, le_refl]

/-- The reconstructed band-limited signal, `⟪wsExp t, F⟫`. -/
noncomputable def wsSignal (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) : ℂ :=
  ⟪wsExp t, F⟫

/-- The boxcar integral over the unit interval equals the normalized sinc. -/
theorem integral_exp_boxcar_eq_sincN (s : ℝ) :
    (∫ a in (-(1 / 2))..(1 / 2), Complex.exp ((2 * π * s * a : ℝ) * Complex.I))
      = (sincN s : ℂ) := by
  by_cases hs : s = 0
  · subst hs
    simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      intervalIntegral.integral_const, sincN_zero]
    norm_num
  · have hc : (2 * π * s) ≠ 0 := by positivity
    have hrw : (fun a : ℝ => Complex.exp ((2 * π * s * a : ℝ) * Complex.I))
        = fun a : ℝ => (fun y : ℝ => Complex.exp ((y : ℝ) * Complex.I)) ((2 * π * s) * a) := by
      funext a; norm_num
    rw [show (∫ a in (-(1 / 2))..(1 / 2), Complex.exp ((2 * π * s * a : ℝ) * Complex.I))
          = ∫ a in (-(1 / 2))..(1 / 2),
              (fun y : ℝ => Complex.exp ((y : ℝ) * Complex.I)) ((2 * π * s) * a) from by
        rw [hrw]]
    rw [intervalIntegral.integral_comp_mul_left
        (f := fun y : ℝ => Complex.exp ((y : ℝ) * Complex.I)) hc,
      show (2 * π * s) * (-(1 / 2)) = -(π * s) by ring,
      show (2 * π * s) * (1 / 2) = π * s by ring, integral_exp_mul_I_eq_sinc]
    rw [Complex.real_smul, sincN]
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    have hπC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

/-- Step 4 bridge: the monomial pairing is the normalized sinc. -/
theorem inner_wsExp_fourierLp (t : ℝ) (n : ℤ) :
    ⟪wsExp t, (fourierLp (T := 1) 2 n)⟫ = (sincN (t + n) : ℂ) := by
  have hws : ⇑(wsExp t) =ᵐ[AddCircle.haarAddCircle (T := 1)]
      AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun t) := MemLp.coeFn_toLp _
  have hfou : ⇑(fourierLp (T := 1) 2 n) =ᵐ[AddCircle.haarAddCircle (T := 1)] fourier n :=
    coeFn_fourierLp 2 n
  have hcong : (fun ξ : AddCircle (1 : ℝ) => ⟪(wsExp t) ξ, (fourierLp (T := 1) 2 n) ξ⟫)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ =>
        conj (AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun t) ξ) * fourier n ξ := by
    filter_upwards [hws, hfou] with ξ h1 h2
    rw [h1, h2, RCLike.inner_apply']
  rw [← integral_exp_boxcar_eq_sincN (t + n), MeasureTheory.L2.inner_def,
    integral_congr_ae hcong, AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.intervalIntegral_preimage 1 (-(1 / 2)),
    show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun a ha => ?_)
  rw [Set.uIoc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] at ha
  have hmem : a ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := ⟨ha.1, by linarith [ha.2]⟩
  simp only [AddCircle.liftIoc_coe_apply hmem, fourier_coe_apply, wsExpFun]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Step 3 bridge: the Fourier coefficient is the sample value. -/
theorem fourierCoeff_eq_wsSignal (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (n : ℤ) :
    fourierCoeff (⇑F) n = wsSignal F (-n) := by
  have hkey : ∀ ξ : AddCircle (1 : ℝ), (fourier (-n) ξ : ℂ)
      = conj (AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun (-n : ℝ)) ξ) := by
    intro ξ
    set y := AddCircle.equivIoc 1 (-(1 / 2)) ξ with hy
    have hs_mem : (y : ℝ) ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := y.2
    have hξ : (((y : ℝ)) : AddCircle (1 : ℝ)) = ξ := by rw [hy]; exact AddCircle.coe_equivIoc
    rw [← hξ, AddCircle.liftIoc_coe_apply hs_mem, fourier_coe_apply]
    simp only [wsExpFun]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [fourierCoeff, wsSignal, MeasureTheory.L2.inner_def]
  have hws : ⇑(wsExp (-n : ℝ)) =ᵐ[AddCircle.haarAddCircle (T := 1)]
      AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun (-n : ℝ)) := MemLp.coeFn_toLp _
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hws] with ξ h1
  rw [h1, RCLike.inner_apply', smul_eq_mul, hkey ξ]

/-- **Whittaker–Shannon**, per-`t` `HasSum` on an L² spectrum (unconditional core).

@audit:ok — independent honesty audit PASS (2026-07-13). Unconditional: signature is
`(F : Lp ℂ 2 haarAddCircle) (t : ℝ)` with no load-bearing hypothesis and the conclusion is
not assumed among the inputs; `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free). Genuinely captures the sampling theorem (`wsSignal F t = ⟪wsExp t, F⟫` is the
inverse-Fourier reconstruction, `F` ranges over the band-limited spectra). -/
@[entry_point]
theorem whittaker_shannon_hasSum
    (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (t : ℝ) :
    HasSum (fun n : ℤ => wsSignal F n • (sincN (t - n) : ℂ)) (wsSignal F t) := by
  have h1 := hasSum_fourier_series_L2 F
  have h2 := (innerSL ℂ (wsExp t)).hasSum h1
  simp only [map_smul, innerSL_apply_apply, inner_wsExp_fourierLp,
    fourierCoeff_eq_wsSignal] at h2
  refine (Equiv.hasSum_iff (Equiv.neg ℤ)).mp ?_
  change HasSum (fun b : ℤ => wsSignal F ((-b : ℤ) : ℝ) • (sincN (t - ((-b : ℤ) : ℝ)) : ℂ))
    (wsSignal F t)
  simp only [Int.cast_neg, sub_neg_eq_add]
  exact h2

/-- Boxcar form of the reconstruction pairing: for any circle-L² element `G` that agrees a.e.
with the periodization of a real-line function `g`, the pairing `wsSignal G w` is the boxcar
integral of `e^{2πiwξ} · g ξ` over the fundamental interval. -/
private lemma wsSignal_eq_boxcar (G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (g : ℝ → ℂ)
    (hG : ⇑G =ᵐ[AddCircle.haarAddCircle (T := 1)] AddCircle.liftIoc 1 (-(1 / 2)) g) (w : ℝ) :
    wsSignal G w = ∫ ξ in (-(1 / 2))..(1 / 2),
      Complex.exp ((2 * π * w * ξ : ℝ) * Complex.I) * g ξ := by
  have hws : ⇑(wsExp w) =ᵐ[AddCircle.haarAddCircle (T := 1)]
      AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun w) := MemLp.coeFn_toLp _
  have hcong : (fun ξ : AddCircle (1 : ℝ) => ⟪(wsExp w) ξ, G ξ⟫)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ =>
        conj (AddCircle.liftIoc 1 (-(1 / 2)) (wsExpFun w) ξ)
          * AddCircle.liftIoc 1 (-(1 / 2)) g ξ := by
    filter_upwards [hws, hG] with ξ h1 h2
    rw [h1, h2, RCLike.inner_apply']
  rw [wsSignal, MeasureTheory.L2.inner_def, integral_congr_ae hcong,
    AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.intervalIntegral_preimage 1 (-(1 / 2)),
    show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun a ha => ?_)
  rw [Set.uIoc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] at ha
  have hmem : a ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2) + 1) := ⟨ha.1, by linarith [ha.2]⟩
  simp only [AddCircle.liftIoc_coe_apply hmem]
  congr 1
  simp only [wsExpFun]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Boxcar form of a band-limited function: Fourier inversion plus the support hypothesis
recovers `f w` as the same boxcar integral of `e^{2πiwξ} · 𝓕 f ξ`. -/
private lemma fourier_eq_boxcar (f : ℝ → ℂ) (hcont : Continuous f) (hf : Integrable f)
    (hFf : Integrable (𝓕 f))
    (hband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → 𝓕 f ξ = 0) (w : ℝ) :
    f w = ∫ ξ in (-(1 / 2))..(1 / 2),
      Complex.exp ((2 * π * w * ξ : ℝ) * Complex.I) * 𝓕 f ξ := by
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hcont hf hFf
  rw [show f w = 𝓕⁻ (𝓕 f) w from (congrFun hinv w).symm, Real.fourierInv_eq']
  have hzero : ∀ v : ℝ, v ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
      Complex.exp ((↑(2 * π * inner ℝ v w) * Complex.I)) • 𝓕 f v = 0 := by
    intro v hv
    rw [hband v hv, smul_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  refine intervalIntegral.integral_congr (fun ξ _ => ?_)
  simp only [smul_eq_mul, Real.inner_apply]
  rw [show (2 * π * (ξ * w) : ℝ) = 2 * π * w * ξ from by ring]

/-- **Whittaker–Shannon**, real-line band-limited textbook wrapper (statement (i)).

Reduces to `whittaker_shannon_hasSum` by taking `F` to be `𝓕 f` restricted to the fundamental
interval as a circle-L² element; Fourier inversion (`Continuous.fourierInv_fourier_eq`) plus the
band-limited support hypothesis give `wsSignal F w = f w` for every real `w`. -/
@[entry_point]
theorem whittaker_shannon_bandlimited
    (f : ℝ → ℂ) (hcont : Continuous f) (hf : Integrable f) (hFf : Integrable (𝓕 f))
    (hband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → 𝓕 f ξ = 0) (t : ℝ) :
    HasSum (fun n : ℤ => f n • (sincN (t - n) : ℂ)) (f t) := by
  have hcontFf : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
      hcontFf.continuousOn
  have hmemLp : MemLp (𝓕 f) 2 (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    refine MemLp.of_bound hcontFf.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x ⟨le_of_lt hx.1, by linarith [hx.2]⟩
  set F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    (hmemLp.memLp_liftIoc.haarAddCircle).toLp with hFdef
  have hF : ⇑F =ᵐ[AddCircle.haarAddCircle (T := 1)]
      AddCircle.liftIoc 1 (-(1 / 2)) (𝓕 f) := MemLp.coeFn_toLp _
  have key : ∀ w : ℝ, wsSignal F w = f w := by
    intro w
    rw [wsSignal_eq_boxcar F (𝓕 f) hF w, ← fourier_eq_boxcar f hcont hf hFf hband w]
  simpa only [key] using whittaker_shannon_hasSum F t

end InformationTheory.Shannon.WhittakerShannon
