import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import InformationTheory.Shannon.EPI.Vitali.AE
import InformationTheory.Shannon.EPI.Vitali.UnifTight
import InformationTheory.Shannon.EPI.Vitali.UI
import InformationTheory.Shannon.EPI.Conv.DensityAssoc
import InformationTheory.Shannon.EPI.G2.BridgeDensityHelpers
import InformationTheory.Shannon.EPI.G2.ConvEntropyDensity
import InformationTheory.Meta.EntryPoint

/-!
# EPI G2 (α) upper bound — KL lower-semicontinuity via klFun-Fatou

This file supplies the **(α) upper bound** of the EPI G2 general-sandwich result
along a constructive route that **avoids the Donsker–Varadhan dual hard direction**.

The route:
- `klDiv μ γ = ∫⁻ klFun(rnDeriv μ γ) dγ` (`klDiv_eq_lintegral_klFun_of_ac`, the ℝ≥0∞
  integral form, no integrability side-condition),
- `klFun ≥ 0` + `lintegral_liminf_le` (Fatou) gives `klDiv μ γ ≤ liminf klDiv (μ_n) γ`
  from a.e. pointwise convergence of the densities (W1 = `klDiv_le_liminf_of_ae_tendsto`),
- the a.e. density convergence is identified through the withDensity-quotient bridge
  (W2 = `rnDeriv_withDensity_quotient_ae`),
- the cross-term `∫ f_n log g → ∫ pX log g` (W3) and the density-level a.e. subsequence
  (W4) plug in,
- assembly turns the KL liminf bound into the differential-entropy limsup bound (α)
  through `klDiv_toReal_eq_neg_differentialEntropy_sub_cross`
  (`EPIG2BridgeDensityHelpers.lean`, `@audit:ok`).

The two missing facts (KL-LSC, withDensity rnDeriv quotient) are assemblies of existing
Mathlib parts. The final boundedness step of the (α) assembly is supplied by the
pX-only (β) lower bound `negMulLog_convDensity_entropy_ge_density`
(`EPIG2ConvEntropyDensity.lean`).
-/

namespace InformationTheory.EPIG2KLFatou

open MeasureTheory Filter Real ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- **W2 — withDensity rnDeriv quotient identification** (the largest gap, an assembly
of existing parts). For `f ≥ 0`, `g > 0`, both measurable and integrable, the
Radon–Nikodym derivative of `volume.withDensity (ofReal∘f)` w.r.t.
`volume.withDensity (ofReal∘g)` is, `γ`-a.e. (with `γ` the `g`-weighted measure),
the pointwise quotient `ofReal (f x / g x)`.

Route: `Measure.rnDeriv_withDensity` collapses each withDensity rnDeriv to its density
on the `volume` axis, `rnDeriv_withDensity_right` inverts the right withDensity, and the
base is transferred `=ᵐ[volume] ⟹ =ᵐ[γ]` through `volume ≪ γ` (`g > 0`).

`hf_meas`/`hg_meas`/`hf_nn`/`hg_pos`/`hf_int`/`hg_int` are regularity preconditions.
@audit:ok -/
theorem rnDeriv_withDensity_quotient_ae
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 < g x)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv
        (volume.withDensity (fun x => ENNReal.ofReal (g x)))
      =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (g x))]
        fun x => ENNReal.ofReal (f x / g x) := by
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hFdef
  set Gd : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x) with hGdef
  set μf : Measure ℝ := volume.withDensity F with hμf
  set γ : Measure ℝ := volume.withDensity Gd with hγ
  -- Measurability of the two ℝ≥0∞ densities.
  have hF_meas' : Measurable F := hf_meas.ennreal_ofReal
  have hGd_meas' : Measurable Gd := hg_meas.ennreal_ofReal
  -- `Gd > 0` everywhere (since `g > 0`).
  have hGd_pos : ∀ x, Gd x ≠ 0 := fun x => by
    simp only [hGdef]; exact (ENNReal.ofReal_pos.mpr (hg_pos x)).ne'
  have hGd_top : ∀ x, Gd x ≠ ∞ := fun x => by simp only [hGdef]; exact ENNReal.ofReal_ne_top
  -- Finiteness instances (from integrability).
  have : IsFiniteMeasure μf := isFiniteMeasure_withDensity_ofReal hf_int.2
  have : IsFiniteMeasure γ := isFiniteMeasure_withDensity_ofReal hg_int.2
  -- Step 1: invert the right withDensity (a.e. `volume`).
  have h1 : μf.rnDeriv γ =ᵐ[volume] fun x => (Gd x)⁻¹ * μf.rnDeriv volume x :=
    Measure.rnDeriv_withDensity_right μf volume hGd_meas'.aemeasurable
      (ae_of_all _ hGd_pos) (ae_of_all _ hGd_top)
  -- Step 2: collapse the left withDensity rnDeriv to its density (a.e. `volume`).
  have h2 : μf.rnDeriv volume =ᵐ[volume] F :=
    Measure.rnDeriv_withDensity volume hF_meas'
  -- Step 3: combine — a.e. `volume`, `μf.rnDeriv γ x = (Gd x)⁻¹ * F x = ofReal (f x / g x)`.
  have hcomb : μf.rnDeriv γ =ᵐ[volume] fun x => ENNReal.ofReal (f x / g x) := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
    -- `(ofReal (g x))⁻¹ * ofReal (f x) = ofReal (f x / g x)`.
    simp only [hFdef, hGdef]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (hf_nn x), ENNReal.ofReal_inv_of_pos (hg_pos x),
      mul_comm]
  -- Step 4: transfer `=ᵐ[volume] ⟹ =ᵐ[γ]` through `γ ≪ volume` (`withDensity ≪ base`).
  have hγ_ac : γ ≪ volume := withDensity_absolutelyContinuous volume Gd
  exact hγ_ac.ae_eq hcomb

/-- **W1 — KL lower-semicontinuity via klFun-Fatou** (the heart of the route).
If `μ_n.rnDeriv γ → μ.rnDeriv γ` `γ`-a.e. (as reals), then `klDiv μ γ ≤ liminf klDiv (μ_n) γ`.

Route: rewrite both sides with the ℝ≥0∞ integral form
`klDiv_eq_lintegral_klFun_of_ac`, apply Fatou `lintegral_liminf_le` (`klFun ≥ 0`,
lifted by `ENNReal.ofReal`), and discharge the pointwise liminf bound via continuity of
`klFun` composed with the a.e. convergence.

`hμ_ac`/`hμn_ac` (absolute continuity) and `h_ae` (a.e. convergence input) are
preconditions; the conclusion is the genuine LSC inequality (not bundled).
@audit:ok -/
theorem klDiv_le_liminf_of_ae_tendsto
    (γ : Measure ℝ) [IsFiniteMeasure γ]
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ) [IsFiniteMeasure μ] [∀ n, IsFiniteMeasure (μ_n n)]
    (hμ_ac : μ ≪ γ) (hμn_ac : ∀ n, μ_n n ≪ γ)
    (h_ae : ∀ᵐ x ∂γ, Tendsto (fun n => ((μ_n n).rnDeriv γ x).toReal) atTop
              (𝓝 ((μ.rnDeriv γ x).toReal))) :
    klDiv μ γ ≤ Filter.liminf (fun n => klDiv (μ_n n) γ) atTop := by
  classical
  -- Abbreviate the ℝ≥0∞ integrands `F n x := ofReal (klFun ((μ_n n).rnDeriv γ x).toReal)`.
  set F : ℕ → ℝ → ℝ≥0∞ :=
    fun n x => ENNReal.ofReal (klFun ((μ_n n).rnDeriv γ x).toReal) with hF
  set G : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (klFun ((μ.rnDeriv γ x).toReal)) with hG
  -- Rewrite both sides into ℝ≥0∞ integral form.
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hμ_ac]
  have hrhs : (fun n => klDiv (μ_n n) γ)
      = fun n => ∫⁻ x, F n x ∂γ := by
    funext n
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hμn_ac n)]
  rw [hrhs]
  -- Goal: `∫⁻ G ≤ liminf (fun n => ∫⁻ F n)`.
  -- Each `F n` is measurable.
  have hF_meas : ∀ n, Measurable (F n) := by
    intro n
    exact (measurable_klFun.comp ((μ_n n).measurable_rnDeriv γ).ennreal_toReal).ennreal_ofReal
  -- Pointwise: `G x ≤ liminf (fun n => F n x)`, `γ`-a.e.
  have hpt : ∀ᵐ x ∂γ, G x ≤ Filter.liminf (fun n => F n x) atTop := by
    filter_upwards [h_ae] with x hx
    -- `F n x → G x` by continuity of `klFun` and `ENNReal.ofReal`.
    have htend : Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
      have hk : Tendsto (fun n => klFun ((μ_n n).rnDeriv γ x).toReal) atTop
          (𝓝 (klFun ((μ.rnDeriv γ x).toReal))) :=
        (continuous_klFun.tendsto _).comp hx
      exact (ENNReal.continuous_ofReal.tendsto _).comp hk
    -- A convergent sequence's limit is `≤` its liminf (equals it, hence `≤`).
    exact htend.liminf_eq.ge
  -- Fatou: `∫⁻ liminf F ≤ liminf ∫⁻ F`; combine with the pointwise lower bound.
  calc ∫⁻ x, G x ∂γ
      ≤ ∫⁻ x, Filter.liminf (fun n => F n x) atTop ∂γ := lintegral_mono_ae hpt
    _ ≤ Filter.liminf (fun n => ∫⁻ x, F n x ∂γ) atTop := lintegral_liminf_le hF_meas

open InformationTheory.Shannon
open InformationTheory.Shannon.EPIConvDensity

/-- **W4 — density-level a.e. subsequence convergence** (genuine, the negMulLog-free
companion of `EPIVitaliAE.negMulLog_convDensity_tendsto_ae_subseq`). Along any sequence
`u → 0⁺`, the smoothed densities `convDensityAdd pX g_{u n}` converge to `pX`
**a.e. along a subsequence** `n ↦ u (ns n)` (`StrictMono ns`), *before* composing with
any continuous map.

Genuine route, identical to `EPIVitaliAE` but cut before the `negMulLog` composition:
layer-1 L¹ convergence `convDensityAdd_tendsto_L1_zero` (`@audit:ok`, sorryAx-free) →
`tendstoInMeasure_of_tendsto_eLpNorm` (Lp → measure) →
`TendstoInMeasure.exists_seq_tendsto_ae` (measure → a.e. subsequence). No own `sorry`.

All `hpX_*` are regularity preconditions; `hu_lim` is the input filter.
@audit:ok -/
theorem convDensity_tendsto_ae_subseq
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂volume,
      Tendsto (fun i =>
        convDensityAdd pX (gaussianPDFReal 0 ⟨u (ns i), (hu_pos (ns i)).le⟩) x)
        atTop (𝓝 (pX x)) := by
  classical
  set f : ℕ → ℝ → ℝ :=
    fun n => convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) with hf_def
  -- Layer-1 L¹ convergence, reparameterised onto the sequence `u`.
  have hL1 : Tendsto (fun n => eLpNorm (f n - pX) 1 volume) atTop (𝓝 0) := by
    have hcomp :
        Tendsto
          (fun n => eLpNorm
            (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 (u n).toNNReal) - pX) 1 volume)
          atTop (𝓝 0) :=
      (convDensityAdd_tendsto_L1_zero hpX_nn hpX_meas hpX_int hpX_mom).comp hu_lim
    refine hcomp.congr (fun n => ?_)
    have hwit : (u n).toNNReal = (⟨u n, (hu_pos n).le⟩ : ℝ≥0) :=
      NNReal.coe_injective (Real.coe_toNNReal _ (hu_pos n).le)
    rw [hf_def, hwit]
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) volume := fun n =>
    (EPIConvDensity.convDensityAdd_pXpY_measurable pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩)
      hpX_meas (measurable_gaussianPDFReal _ _)).aestronglyMeasurable
  have hpX_aesm : AEStronglyMeasurable pX volume := hpX_meas.aestronglyMeasurable
  have hmeas : TendstoInMeasure volume f atTop pX :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf_meas hpX_aesm hL1
  obtain ⟨ns, hns_mono, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨ns, hns_mono, hns_ae⟩

/-- **log of the Gaussian density** as a quadratic (verbatim from the `gaussianPDFReal`
definition `(√(2πv))⁻¹ · exp(-(x-μ)²/(2v))`). For `v ≠ 0` and `μ = 0`:
`log (gaussianPDFReal 0 v x) = - log (√(2πv)) - x² / (2v)`.
@audit:ok -/
theorem log_gaussianPDFReal_zero {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x)
      = - Real.log (Real.sqrt (2 * π * v)) - x ^ 2 / (2 * v) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    rw [show (0 : ℝ) = ((0 : ℝ≥0) : ℝ) by simp]
    exact_mod_cast pos_iff_ne_zero.mpr hv
  have hprod : (0 : ℝ) < 2 * π * v := by positivity
  have hsqrt_ne : Real.sqrt (2 * π * v) ≠ 0 := (Real.sqrt_pos.mpr hprod).ne'
  rw [gaussianPDFReal]
  rw [Real.log_mul (inv_ne_zero hsqrt_ne) (Real.exp_ne_zero _)]
  rw [Real.log_inv, Real.log_exp]
  ring

/-- **Cross-term closed form** for a smoothed density against a Gaussian log-density.
With `g := gaussianPDFReal 0 σ²` (`σ² ≠ 0`) and `f_t := convDensityAdd pX g_t` (`t > 0`),
the cross integral `∫ f_t · log g` is an *affine* function of `t`:
`∫ x, f_t x · log (g x) = c₀ · 1 − (1/(2σ²)) · (M2(pX) + (∫pX)·t)`,
where `c₀ = − log (√(2πσ²))` and `M2(pX) = ∫ x²·pX`.
@audit:ok -/
theorem cross_term_closed_form {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∫ x, convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x
          * Real.log (gaussianPDFReal 0 σ2 x) ∂volume
      = (- Real.log (Real.sqrt (2 * π * σ2))) * (∫ x, pX x ∂volume)
        - (1 / (2 * σ2)) * ((∫ x, x ^ 2 * pX x ∂volume) + (∫ x, pX x ∂volume) * t) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  set f := convDensityAdd pX g with hf_def
  set c₀ : ℝ := - Real.log (Real.sqrt (2 * π * σ2)) with hc₀
  -- Pointwise: `f x · log (gaussian x) = c₀·f x − (1/(2σ²))·(x²·f x)`.
  have hpt : (fun x => f x * Real.log (gaussianPDFReal 0 σ2 x))
      = fun x => c₀ * f x - (1 / (2 * σ2)) * (x ^ 2 * f x) := by
    funext x
    rw [log_gaussianPDFReal_zero hσ x, hc₀]
    ring
  rw [hpt]
  -- Integrability of the two pieces.
  have hf_int : Integrable f volume :=
    convDensityAdd_pXpY_integrable pX g hpX_int hpX_meas
      (integrable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _)
  have hsq_int : Integrable (fun x => x ^ 2 * f x) volume :=
    convDensityAdd_gaussian_sq_integrable hpX_nn hpX_meas hpX_int hpX_mom ht
  rw [integral_sub (hf_int.const_mul _) (hsq_int.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  -- `∫ f = (∫pX)·(∫g) = (∫pX)·1`, and `∫ x²·f` from the second-moment lemma.
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  rw [convDensityAdd_pXpY_integral_eq pX g hpX_int (integrable_gaussianPDFReal _ _)]
  rw [hg_def, integral_gaussianPDFReal_eq_one 0 hv_ne]
  rw [convDensityAdd_second_moment hpX_nn hpX_meas hpX_int hpX_mom ht]
  ring

/-- **Limit of the marginal cross-term** `∫ pX · log g` in the same expanded form.
With `g := gaussianPDFReal 0 σ²`, `∫ x, pX x · log (g x) = c₀·(∫pX) − (1/(2σ²))·M2(pX)`.
@audit:ok -/
theorem pX_cross_term_expand {pX : ℝ → ℝ}
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) :
    ∫ x, pX x * Real.log (gaussianPDFReal 0 σ2 x) ∂volume
      = (- Real.log (Real.sqrt (2 * π * σ2))) * (∫ x, pX x ∂volume)
        - (1 / (2 * σ2)) * (∫ x, x ^ 2 * pX x ∂volume) := by
  have hpt : (fun x => pX x * Real.log (gaussianPDFReal 0 σ2 x))
      = fun x => (- Real.log (Real.sqrt (2 * π * σ2))) * pX x
          - (1 / (2 * σ2)) * (x ^ 2 * pX x) := by
    funext x; rw [log_gaussianPDFReal_zero hσ x]; ring
  rw [hpt, integral_sub (hpX_int.const_mul _) (hpX_mom.const_mul _),
    integral_const_mul, integral_const_mul]

/-- **W3 — cross-term convergence** `∫ f_n · log g → ∫ pX · log g` as `u_n → 0⁺`.
Combines the affine closed form `cross_term_closed_form` (in `t`) with the marginal
expansion `pX_cross_term_expand`; the difference is `−(1/(2σ²))·(∫pX)·u_n → 0`.
@audit:ok -/
theorem cross_term_tendsto {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ x, convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x
          * Real.log (gaussianPDFReal 0 σ2 x) ∂volume)
      atTop (𝓝 (∫ x, pX x * Real.log (gaussianPDFReal 0 σ2 x) ∂volume)) := by
  set c₀ : ℝ := - Real.log (Real.sqrt (2 * π * σ2)) with hc₀
  set I0 : ℝ := ∫ x, pX x ∂volume with hI0
  set M2 : ℝ := ∫ x, x ^ 2 * pX x ∂volume with hM2
  -- Rewrite each term with the affine closed form.
  have hcf : ∀ n,
      (∫ x, convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x
          * Real.log (gaussianPDFReal 0 σ2 x) ∂volume)
        = c₀ * I0 - (1 / (2 * σ2)) * (M2 + I0 * u n) := by
    intro n
    rw [cross_term_closed_form hpX_nn hpX_meas hpX_int hpX_mom hσ (hu_pos n)]
  -- Rewrite the limit with the marginal expansion.
  rw [pX_cross_term_expand hpX_int hpX_mom hσ]
  -- Tendsto of the affine function.
  simp_rw [hcf]
  have hlim : Tendsto (fun n => c₀ * I0 - (1 / (2 * σ2)) * (M2 + I0 * u n)) atTop
      (𝓝 (c₀ * I0 - (1 / (2 * σ2)) * (M2 + I0 * 0))) := by
    apply Tendsto.sub tendsto_const_nhds
    apply Tendsto.const_mul
    apply Tendsto.const_add
    exact tendsto_const_nhds.mul hu_lim
  have hgoal : c₀ * I0 - (1 / (2 * σ2)) * (M2 + I0 * 0)
      = c₀ * I0 - (1 / (2 * σ2)) * M2 := by ring
  rw [hgoal] at hlim
  exact hlim

/-- **(α) upper bound assembly** — differential-entropy upper semicontinuity of the
smoothed densities at the `t → 0⁺` endpoint, via the klFun-Fatou KL lower-semicontinuity
route (`klDiv_le_liminf_of_ae_tendsto`) and the genuine bridge
`klDiv_toReal_eq_neg_differentialEntropy_sub_cross`.

For a probability density `pX` (nonneg, measurable, integrable, mass `1`, finite second
moment, finite entropy integrand) and a reference Gaussian `g := gaussianPDFReal 0 σ²`
(`σ² ≠ 0`), the smoothed-density entropy `∫ negMulLog (convDensityAdd pX g_{u n})` has
limsup bounded by the limit entropy `∫ negMulLog pX` along any `u → 0⁺`:

`limsup (fun n => ∫ x, negMulLog (convDensityAdd pX g_{u n} x)) atTop ≤ ∫ x, negMulLog (pX x)`.

ROUTE (the pieces all live in this file):
- W1 `klDiv_le_liminf_of_ae_tendsto` gives `klDiv μ γ ≤ liminf klDiv (μ_n) γ` (ℝ≥0∞),
- W2 `rnDeriv_withDensity_quotient_ae` identifies `rnDeriv μ_n γ =ᵐ[γ] ofReal (f_n/g)`,
- W4 `convDensity_tendsto_ae_subseq` supplies `f_n → pX` a.e. (subsequence),
- W3 `cross_term_tendsto` gives the cross-term limit,
- the bridge `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` turns each
  `(klDiv μ_n γ).toReal` into `−h(μ_n) − cross_n`, and `tendsto_of_subseq_tendsto`
  promotes the subsequence bound to the full sequence.

BOUNDEDNESS (the `hKL_limsup` step): the boundedness that the
ℝ≥0∞ → `toReal` transfer of W1 requires is supplied by the **pX-only (β) lower bound**
`negMulLog_convDensity_entropy_ge_density` (`EPIG2ConvEntropyDensity.lean`, `@audit:ok`,
via the `cond-diff-entropy` route): each `h(μ_n) ≥ h(pX)`, so
`KLr n = −h(μ_n) − cross_n ≤ −cross_n − h(pX)`, which converges (W3) and hence bounds
`KLr` above. KL finiteness `klDiv μ_n γ ≠ ∞` (and `klDiv μ γ ≠ ∞`) is the genuine
llr-integrability content, established from the volume-density entropy + cross
integrability via `integrable_toReal_rnDeriv_mul_iff`. Along any subsequence W4 extracts
an a.e.-convergent sub-subsequence; W1 + `ENNReal.liminf_toReal_eq` give
`liminf KLr ≥ (klDiv μ γ).toReal` and the β bound gives `limsup KLr ≤ (klDiv μ γ).toReal`,
so `KLr → (klDiv μ γ).toReal` (squeeze), hence `h_n → −(klDiv μ γ).toReal − crossμ = h(pX)`.
`tendsto_of_subseq_tendsto` promotes this to the full sequence, so `limsup h_n = h(pX)`.

The hypotheses are all regularity preconditions (`pX` density regularity + `σ² ≠ 0` +
`u → 0⁺` positivity); the conclusion is the genuine limsup inequality, not bundled.
@audit:ok -/
@[entry_point]
theorem negMulLog_convDensity_limsup_le {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    Filter.limsup
        (fun n => ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume)
        atTop
      ≤ ∫ x, Real.negMulLog (pX x) ∂volume := by
  classical
  -- Reference Gaussian `g` (density) and `γ` (measure), the smoothed densities `f_n`,
  -- and the corresponding measures `μ_n`, `μ`.
  set g : ℝ → ℝ := gaussianPDFReal 0 σ2 with hg_def
  set γ : Measure ℝ := gaussianReal 0 σ2 with hγ_def
  set f : ℕ → ℝ → ℝ :=
    fun n => convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) with hf_def
  set μn : ℕ → Measure ℝ :=
    fun n => volume.withDensity (fun x => ENNReal.ofReal (f n x)) with hμn_def
  set μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (pX x)) with hμ_def
  -- Positivity of `g` (σ² ≠ 0).
  have hg_pos : ∀ x, 0 < g x := fun x => gaussianPDFReal_pos 0 σ2 x hσ
  have hg_meas : Measurable g := measurable_gaussianPDFReal _ _
  have hg_int : Integrable g volume := integrable_gaussianPDFReal _ _
  -- `γ = volume.withDensity (ofReal ∘ g)` (σ² ≠ 0, so not a Dirac).
  have hγ_wd : γ = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [hγ_def, hg_def, gaussianReal_of_var_ne_zero 0 hσ]
    rfl
  -- Regularity of each `f n`: nonneg, measurable, integrable, mass 1.
  have hf_nn : ∀ n x, 0 ≤ f n x := fun n x =>
    convDensityAdd_pXpY_nonneg pX _ hpX_nn (fun y => gaussianPDFReal_nonneg _ _ y) x
  have hf_meas : ∀ n, Measurable (f n) := fun n =>
    convDensityAdd_pXpY_measurable pX _ hpX_meas (measurable_gaussianPDFReal _ _)
  have hf_int : ∀ n, Integrable (f n) volume := fun n =>
    convDensityAdd_pXpY_integrable pX _ hpX_int hpX_meas
      (integrable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _)
  have hgn_ne : ∀ n, (⟨u n, (hu_pos n).le⟩ : ℝ≥0) ≠ 0 := fun n => by
    intro h; exact (hu_pos n).ne' (congrArg NNReal.toReal h)
  have hf_mass : ∀ n, (∫ x, f n x ∂volume) = 1 := fun n => by
    rw [hf_def, convDensityAdd_pXpY_integral_eq pX _ hpX_int (integrable_gaussianPDFReal _ _),
      integral_gaussianPDFReal_eq_one 0 (hgn_ne n), hpX_mass, mul_one]
  -- Probability-measure instances.
  have hμn_prob : ∀ n, IsProbabilityMeasure (μn n) := fun n => by
    constructor
    rw [hμn_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hf_int n) (ae_of_all _ (hf_nn n)),
      hf_mass n, ENNReal.ofReal_one]
  have hμ_prob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hpX_int (ae_of_all _ hpX_nn),
      hpX_mass, ENNReal.ofReal_one]
  have hγ_prob : IsProbabilityMeasure γ := by
    rw [hγ_def]; infer_instance
  -- Absolute continuity preconditions for the bridge / W1.
  have hμn_v : ∀ n, μn n ≪ volume := fun n => by
    rw [hμn_def]; exact withDensity_absolutelyContinuous _ _
  have hμ_v : μ ≪ volume := by rw [hμ_def]; exact withDensity_absolutelyContinuous _ _
  have hγ_v : γ ≪ volume := by rw [hγ_def]; exact gaussianReal_absolutelyContinuous 0 hσ
  have hv_γ : volume ≪ γ := by rw [hγ_def]; exact gaussianReal_absolutelyContinuous' 0 hσ
  have hμn_γ : ∀ n, μn n ≪ γ := fun n => (hμn_v n).trans hv_γ
  have hμ_γ : μ ≪ γ := hμ_v.trans hv_γ
  -- The volume-density of `γ` equals `g`, a.e.
  have hγ_rnDeriv : γ.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (g x) := by
    rw [hγ_wd]; exact Measure.rnDeriv_withDensity volume hg_meas.ennreal_ofReal
  -- The volume-density of `μn n` equals `f n`, a.e.; same for `μ` / `pX`.
  have hμn_rnDeriv : ∀ n, (μn n).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (f n x) :=
    fun n => by rw [hμn_def]; exact Measure.rnDeriv_withDensity volume (hf_meas n).ennreal_ofReal
  have hμ_rnDeriv : μ.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (pX x) := by
    rw [hμ_def]; exact Measure.rnDeriv_withDensity volume hpX_meas.ennreal_ofReal
  -- Cross-term integrability for each `n` (against `log g`, a quadratic).
  have hcross_int : ∀ n, Integrable
      (fun x => f n x * Real.log (g x)) volume := fun n => by
    have hpt : (fun x => f n x * Real.log (g x))
        = fun x => (- Real.log (Real.sqrt (2 * π * σ2))) * f n x
            - (1 / (2 * σ2)) * (x ^ 2 * f n x) := by
      funext x; rw [hg_def, log_gaussianPDFReal_zero hσ x]; ring
    rw [hpt]
    exact ((hf_int n).const_mul _).sub
      ((convDensityAdd_gaussian_sq_integrable hpX_nn hpX_meas hpX_int hpX_mom (hu_pos n)).const_mul _)
  have hcross_int_μ : Integrable (fun x => pX x * Real.log (g x)) volume := by
    have hpt : (fun x => pX x * Real.log (g x))
        = fun x => (- Real.log (Real.sqrt (2 * π * σ2))) * pX x
            - (1 / (2 * σ2)) * (x ^ 2 * pX x) := by
      funext x; rw [hg_def, log_gaussianPDFReal_zero hσ x]; ring
    rw [hpt]; exact (hpX_int.const_mul _).sub (hpX_mom.const_mul _)
  -- The `log f` integrability for each `n` (= negMulLog integrability, up to sign).
  have hlogp_int : ∀ n, Integrable
      (fun x => f n x * Real.log (f n x)) volume := fun n => by
    have hng := InformationTheory.Shannon.FisherInfoV2.convDensityAdd_negMulLog_integrable
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (hu_pos n)
    have hpt : (fun x => f n x * Real.log (f n x))
        = fun x => - Real.negMulLog (f n x) := by
      funext x; rw [Real.negMulLog_def]; ring
    rw [hpt]; exact hng.neg
  -- The `log p` integrability for `μ = pX`.
  have hlogp_int_μ : Integrable (fun x => pX x * Real.log (pX x)) volume := by
    have hpt : (fun x => pX x * Real.log (pX x)) = fun x => - Real.negMulLog (pX x) := by
      funext x; rw [Real.negMulLog_def]; ring
    rw [hpt]; exact hpX_ent.neg
  -- Cross-term in the bridge's density shape (rnDeriv form), rewritten to `f n · log g`.
  have hcross_density : ∀ n, Integrable
      (fun x => ((μn n).rnDeriv volume x).toReal
        * Real.log ((γ.rnDeriv volume x).toReal)) volume := fun n => by
    apply (hcross_int n).congr
    filter_upwards [hμn_rnDeriv n, hγ_rnDeriv] with x hx hxg
    rw [hx, hxg, ENNReal.toReal_ofReal (hf_nn n x), ENNReal.toReal_ofReal (hg_pos x).le]
  have hlogp_density : ∀ n, Integrable
      (fun x => ((μn n).rnDeriv volume x).toReal
        * Real.log (((μn n).rnDeriv volume x).toReal)) volume := fun n => by
    apply (hlogp_int n).congr
    filter_upwards [hμn_rnDeriv n] with x hx
    rw [hx, ENNReal.toReal_ofReal (hf_nn n x)]
  have hcross_density_μ : Integrable
      (fun x => (μ.rnDeriv volume x).toReal
        * Real.log ((γ.rnDeriv volume x).toReal)) volume := by
    apply hcross_int_μ.congr
    filter_upwards [hμ_rnDeriv, hγ_rnDeriv] with x hx hxg
    rw [hx, hxg, ENNReal.toReal_ofReal (hpX_nn x), ENNReal.toReal_ofReal (hg_pos x).le]
  have hlogp_density_μ : Integrable
      (fun x => (μ.rnDeriv volume x).toReal
        * Real.log ((μ.rnDeriv volume x).toReal)) volume := by
    apply hlogp_int_μ.congr
    filter_upwards [hμ_rnDeriv] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpX_nn x)]
  -- Equal-mass conditions (all probability measures).
  have hmass_n : ∀ n, (μn n) Set.univ = γ Set.univ := fun n => by
    rw [(hμn_prob n).measure_univ, hγ_prob.measure_univ]
  have hmass_μ : μ Set.univ = γ Set.univ := by
    rw [hμ_prob.measure_univ, hγ_prob.measure_univ]
  -- The bridge, instantiated for each `n` and for `μ`.
  have hbridge_n : ∀ n, (klDiv (μn n) γ).toReal
      = - differentialEntropy (μn n)
        - ∫ x, ((μn n).rnDeriv volume x).toReal
            * Real.log ((γ.rnDeriv volume x).toReal) ∂volume := fun n =>
    haveI := hμn_prob n
    klDiv_toReal_eq_neg_differentialEntropy_sub_cross (μn n) γ (hμn_v n) hγ_v (hμn_γ n)
      (hmass_n n) (hlogp_density n) (hcross_density n)
  have hbridge_μ : (klDiv μ γ).toReal
      = - differentialEntropy μ
        - ∫ x, (μ.rnDeriv volume x).toReal
            * Real.log ((γ.rnDeriv volume x).toReal) ∂volume :=
    klDiv_toReal_eq_neg_differentialEntropy_sub_cross μ γ hμ_v hγ_v hμ_γ
      hmass_μ hlogp_density_μ hcross_density_μ
  -- Identify the differential entropies with the negMulLog integrals.
  have hent_n : ∀ n, differentialEntropy (μn n) = ∫ x, Real.negMulLog (f n x) ∂volume := fun n => by
    rw [hμn_def, differentialEntropy_eq_integral_withDensity (hf_meas n).ennreal_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [ENNReal.toReal_ofReal (hf_nn n x)]
  have hent_μ : differentialEntropy μ = ∫ x, Real.negMulLog (pX x) ∂volume := by
    rw [hμ_def, differentialEntropy_eq_integral_withDensity hpX_meas.ennreal_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [ENNReal.toReal_ofReal (hpX_nn x)]
  -- Identify the bridge's cross-term (rnDeriv form) with `∫ f n · log g` and `∫ pX · log g`.
  have hcross_eq_n : ∀ n,
      (∫ x, ((μn n).rnDeriv volume x).toReal * Real.log ((γ.rnDeriv volume x).toReal) ∂volume)
        = ∫ x, f n x * Real.log (g x) ∂volume := fun n =>
    integral_congr_ae (by
      filter_upwards [hμn_rnDeriv n, hγ_rnDeriv] with x hx hxg
      rw [hx, hxg, ENNReal.toReal_ofReal (hf_nn n x), ENNReal.toReal_ofReal (hg_pos x).le])
  have hcross_eq_μ :
      (∫ x, (μ.rnDeriv volume x).toReal * Real.log ((γ.rnDeriv volume x).toReal) ∂volume)
        = ∫ x, pX x * Real.log (g x) ∂volume :=
    integral_congr_ae (by
      filter_upwards [hμ_rnDeriv, hγ_rnDeriv] with x hx hxg
      rw [hx, hxg, ENNReal.toReal_ofReal (hpX_nn x), ENNReal.toReal_ofReal (hg_pos x).le])
  -- Abbreviate the entropy / KL-toReal / cross sequences.
  set h_n : ℕ → ℝ := fun n => ∫ x, Real.negMulLog (f n x) ∂volume with hh_def
  set KLr : ℕ → ℝ := fun n => (klDiv (μn n) γ).toReal with hKLr_def
  set cross_n : ℕ → ℝ := fun n => ∫ x, f n x * Real.log (g x) ∂volume with hcr_def
  set crossμ : ℝ := ∫ x, pX x * Real.log (g x) ∂volume with hcrμ_def
  -- Per-`n` rearrangement: `h_n n = - KLr n - cross_n n`.
  have hhn_eq : ∀ n, h_n n = - KLr n - cross_n n := fun n => by
    have := hbridge_n n
    rw [hent_n n, hcross_eq_n n] at this
    rw [hh_def, hKLr_def, hcr_def]
    linarith [this]
  -- `h(pX) = - KLr_μ - crossμ`.
  have hhμ_eq : (∫ x, Real.negMulLog (pX x) ∂volume) = - (klDiv μ γ).toReal - crossμ := by
    have := hbridge_μ
    rw [hent_μ, hcross_eq_μ] at this
    rw [hcrμ_def]; linarith [this]
  -- W3: cross-term convergence (full sequence) `cross_n → crossμ`.
  have hu_lim' : Tendsto u atTop (𝓝 0) := hu_lim.mono_right nhdsWithin_le_nhds
  have hcross_tendsto : Tendsto cross_n atTop (𝓝 crossμ) := by
    have hw3 := cross_term_tendsto hpX_nn hpX_meas hpX_int hpX_mom hσ u hu_pos hu_lim'
    simpa only [hcr_def, hg_def, hcrμ_def] using hw3
  -- **The toReal-level entropy convergence** (W1 `klDiv_le_liminf_of_ae_tendsto`
  -- transferred to `toReal`, with the boundedness supplied by the genuine (β) lower bound
  -- `negMulLog_convDensity_entropy_ge_density`, plus the W4 subsequence promotion).
  -- `h_n n = - KLr n - cross_n n` (`hhn_eq`, genuine bridge), `KLr n ≥ 0`; the W1 bound
  -- `(klDiv μ γ).toReal ≤ liminf KLr` along the a.e.-convergent W4 subsequence + the W3
  -- limit `cross_n → crossμ` + the β upper bound on `KLr` squeeze `KLr → (klDiv μ γ).toReal`.
  -- KL finiteness for each `μn n` (= the genuine llr-integrability content), so that
  -- the ℝ≥0∞ W1 bound can be transferred to `toReal`.
  have hKL_ne_top : ∀ n, klDiv (μn n) γ ≠ ∞ := fun n => by
    refine InformationTheory.klDiv_ne_top (hμn_γ n) ?_
    -- `llr μn γ =ᵐ[μn] log p_n − log g`, and the latter is `μn`-integrable since
    -- `p_n·(log p_n) − p_n·(log g)` is volume-integrable (genuine entropy + cross terms).
    have hllr_eq : llr (μn n) γ =ᵐ[μn n]
        fun x => Real.log ((μn n).rnDeriv volume x).toReal
          - Real.log ((γ.rnDeriv volume x).toReal) :=
      InformationTheory.Shannon.llr_eq_log_density_sub_log_density (μn n) γ (hμn_v n) hγ_v (hμn_γ n)
    refine (Integrable.congr ?_ hllr_eq.symm)
    -- Pull the integral back to volume via `integrable_toReal_rnDeriv_mul_iff`.
    rw [← MeasureTheory.integrable_toReal_rnDeriv_mul_iff (hμn_v n)
      (f := fun x => Real.log ((μn n).rnDeriv volume x).toReal
        - Real.log ((γ.rnDeriv volume x).toReal))]
    -- Identify the volume-integrand with `p_n·log p_n − p_n·log g`.
    refine ((hlogp_int n).sub (hcross_int n)).congr ?_
    filter_upwards [hμn_rnDeriv n, hγ_rnDeriv] with x hx hxg
    rw [hx, hxg, ENNReal.toReal_ofReal (hf_nn n x), ENNReal.toReal_ofReal (hg_pos x).le]
    exact (mul_sub _ _ _).symm
  have hμ_KL_ne_top : klDiv μ γ ≠ ∞ := by
    refine InformationTheory.klDiv_ne_top hμ_γ ?_
    have hllr_eq : llr μ γ =ᵐ[μ]
        fun x => Real.log (μ.rnDeriv volume x).toReal
          - Real.log ((γ.rnDeriv volume x).toReal) :=
      InformationTheory.Shannon.llr_eq_log_density_sub_log_density μ γ hμ_v hγ_v hμ_γ
    refine (Integrable.congr ?_ hllr_eq.symm)
    rw [← MeasureTheory.integrable_toReal_rnDeriv_mul_iff hμ_v
      (f := fun x => Real.log (μ.rnDeriv volume x).toReal
        - Real.log ((γ.rnDeriv volume x).toReal))]
    refine (hlogp_int_μ.sub hcross_int_μ).congr ?_
    filter_upwards [hμ_rnDeriv, hγ_rnDeriv] with x hx hxg
    rw [hx, hxg, ENNReal.toReal_ofReal (hpX_nn x), ENNReal.toReal_ofReal (hg_pos x).le]
    exact (mul_sub _ _ _).symm
  -- (β) lower bound, supplying the upper boundedness of `KLr` (= each `h_n ≥ h(pX)`).
  have hbeta : ∀ n, (∫ x, Real.negMulLog (pX x) ∂volume) ≤ h_n n := fun n => by
    rw [hh_def]
    exact negMulLog_convDensity_entropy_ge_density hpX_nn hpX_meas hpX_int hpX_mass hpX_mom
      hpX_ent hσ.bot_lt u hu_pos n
  -- Convenient abbreviation for the target real value `L = h(pX) = -KLr_μ - crossμ`.
  set L : ℝ := - (klDiv μ γ).toReal - crossμ with hL_def
  have hL_eq : (∫ x, Real.negMulLog (pX x) ∂volume) = L := hhμ_eq
  -- `cross_n → crossμ`, so the upper β bound `-cross_n - h(pX) → -crossμ - L = (klDiv μ γ).toReal`.
  have hupper_lim : Tendsto (fun n => - cross_n n - L) atTop (𝓝 ((klDiv μ γ).toReal)) := by
    have : Tendsto (fun n => - cross_n n - L) atTop (𝓝 (- crossμ - L)) :=
      (hcross_tendsto.neg).sub_const L
    have heq : - crossμ - L = (klDiv μ γ).toReal := by rw [hL_def]; ring
    rwa [heq] at this
  -- Each `KLr n` is the `toReal` of a genuine real value (β + bridge), bounded above.
  have hKLr_upper : ∀ n, KLr n ≤ - cross_n n - L := fun n => by
    have h1 := hhn_eq n
    have h2 := hbeta n
    rw [hL_eq] at h2
    linarith [h1, h2]
  have hKLr_nn : ∀ n, 0 ≤ KLr n := fun n => ENNReal.toReal_nonneg
  -- **The toReal-level entropy convergence**, via the subsequence-promotion principle:
  -- it suffices that every subsequence has a further subsequence along which `h_n → L`.
  have hKLr_tendsto : Tendsto h_n atTop (𝓝 L) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    -- `u ∘ ns → 0⁺`, so W4 gives an a.e.-convergent sub-subsequence of the densities.
    have huns_lim : Tendsto (fun k => u (ns k)) atTop (𝓝[Set.Ioi 0] 0) := hu_lim.comp hns
    obtain ⟨ms, _hms_mono, hms_ae⟩ :=
      convDensity_tendsto_ae_subseq hpX_nn hpX_meas hpX_int hpX_mom
        (fun k => u (ns k)) (fun k => hu_pos (ns k)) huns_lim
    refine ⟨ms, ?_⟩
    -- Reindex: `idx i := ns (ms i)`.
    set idx : ℕ → ℕ := fun i => ns (ms i) with hidx_def
    -- a.e.-`γ` convergence of the rnDeriv-`γ` densities along `idx`.
    have hae_γ : ∀ᵐ x ∂γ, Tendsto
        (fun i => ((μn (idx i)).rnDeriv γ x).toReal) atTop
          (𝓝 ((μ.rnDeriv γ x).toReal)) := by
      -- a.e.-`volume` density convergence `f (idx i) → pX`, transferred to `γ` (γ ≪ volume).
      have hae_vol : ∀ᵐ x ∂volume, Tendsto
          (fun i => f (idx i) x) atTop (𝓝 (pX x)) := by
        filter_upwards [hms_ae] with x hx
        simpa only [hf_def, hidx_def] using hx
      have hae_vol_γ : ∀ᵐ x ∂γ, Tendsto
          (fun i => f (idx i) x) atTop (𝓝 (pX x)) := hγ_v.ae_le hae_vol
      -- W2 a.e.-`γ` identifications of the rnDeriv-`γ` densities as `f/g` and `pX/g`.
      -- `γ` equals the `g`-withDensity (`hγ_wd`); rewrite the W2 output onto `μn`/`μ`/`γ`.
      have hquot_n : ∀ n, ((μn n).rnDeriv γ) =ᵐ[γ]
          fun x => ENNReal.ofReal (f n x / g x) := fun n => by
        have hraw := rnDeriv_withDensity_quotient_ae (hf_meas n) hg_meas (hf_nn n) hg_pos
          (hf_int n) hg_int
        rw [← hγ_wd] at hraw
        exact hraw
      have hquot_μ : (μ.rnDeriv γ) =ᵐ[γ]
          fun x => ENNReal.ofReal (pX x / g x) := by
        have hraw := rnDeriv_withDensity_quotient_ae hpX_meas hg_meas hpX_nn hg_pos hpX_int hg_int
        rw [← hγ_wd] at hraw
        exact hraw
      -- Combine the a.e. identities with the pointwise quotient convergence.
      have hquot_all : ∀ᵐ x ∂γ,
          (∀ i, ((μn (idx i)).rnDeriv γ x).toReal = f (idx i) x / g x)
          ∧ ((μ.rnDeriv γ x).toReal = pX x / g x) := by
        have hall_n : ∀ᵐ x ∂γ, ∀ i,
            ((μn (idx i)).rnDeriv γ x) = ENNReal.ofReal (f (idx i) x / g x) :=
          ae_all_iff.mpr (fun i => hquot_n (idx i))
        filter_upwards [hall_n, hquot_μ] with x hxn hxμ
        refine ⟨fun i => ?_, ?_⟩
        · rw [hxn i, ENNReal.toReal_ofReal]
          exact div_nonneg (hf_nn (idx i) x) (hg_pos x).le
        · rw [hxμ, ENNReal.toReal_ofReal]
          exact div_nonneg (hpX_nn x) (hg_pos x).le
      filter_upwards [hae_vol_γ, hquot_all] with x hx_conv ⟨hxn, hxμ⟩
      have hconv : Tendsto (fun i => f (idx i) x / g x) atTop (𝓝 (pX x / g x)) :=
        hx_conv.div_const (g x)
      simp only [hxn, hxμ]
      exact hconv
    -- W1: `klDiv μ γ ≤ liminf (klDiv (μn (idx ·)) γ)` (ℝ≥0∞).
    have hw1 : klDiv μ γ ≤ Filter.liminf (fun i => klDiv (μn (idx i)) γ) atTop :=
      klDiv_le_liminf_of_ae_tendsto γ μ (fun i => μn (idx i)) hμ_γ
        (fun i => hμn_γ (idx i)) hae_γ
    -- Transfer the ℝ≥0∞ liminf bound to `toReal`, using upper boundedness of `KLr`.
    -- Uniform upper bound `b` on `klDiv (μn (idx i)) γ` (from the β upper bound + convergence).
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ i, KLr (idx i) ≤ C := by
      -- `-cross_n - L → (klDiv μ γ).toReal`, so `KLr (idx i)` is eventually ≤ that limit + 1.
      have hbdd : BddAbove (Set.range (fun i => - cross_n (idx i) - L)) := by
        have : Tendsto (fun i => - cross_n (idx i) - L) atTop (𝓝 ((klDiv μ γ).toReal)) :=
          hupper_lim.comp (hns.comp _hms_mono.tendsto_atTop)
        exact this.bddAbove_range
      obtain ⟨C, hC⟩ := hbdd
      exact ⟨C, fun i => (hKLr_upper (idx i)).trans (hC (Set.mem_range_self i))⟩
    -- `klDiv (μn (idx i)) γ ≤ ofReal C` (since `KLr = toReal` and the value is `≠ ∞`).
    have hb_bound : ∀ᶠ i in atTop, klDiv (μn (idx i)) γ ≤ ENNReal.ofReal C := by
      refine Filter.Eventually.of_forall fun i => ?_
      rw [← ENNReal.ofReal_toReal (hKL_ne_top (idx i))]
      exact ENNReal.ofReal_le_ofReal (hC i)
    -- `liminf (KLr (idx ·)) = (liminf klDiv ...).toReal ≥ (klDiv μ γ).toReal`.
    have hliminf_toReal :
        Filter.liminf (fun i => KLr (idx i)) atTop
          = (Filter.liminf (fun i => klDiv (μn (idx i)) γ) atTop).toReal := by
      rw [← ENNReal.liminf_toReal_eq (ENNReal.ofReal_ne_top) hb_bound]
    have hliminf_klDiv_ne_top :
        Filter.liminf (fun i => klDiv (μn (idx i)) γ) atTop ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (Filter.liminf_le_of_frequently_le' hb_bound.frequently)
    have hliminf_ge : (klDiv μ γ).toReal ≤ Filter.liminf (fun i => KLr (idx i)) atTop := by
      rw [hliminf_toReal]
      exact (ENNReal.toReal_le_toReal hμ_KL_ne_top hliminf_klDiv_ne_top).mpr hw1
    -- `limsup (KLr (idx ·)) ≤ (klDiv μ γ).toReal` from the β upper bound.
    have hlimsup_le : Filter.limsup (fun i => KLr (idx i)) atTop ≤ (klDiv μ γ).toReal := by
      have htend : Tendsto (fun i => - cross_n (idx i) - L) atTop (𝓝 ((klDiv μ γ).toReal)) :=
        hupper_lim.comp (hns.comp _hms_mono.tendsto_atTop)
      calc Filter.limsup (fun i => KLr (idx i)) atTop
          ≤ Filter.limsup (fun i => - cross_n (idx i) - L) atTop :=
            Filter.limsup_le_limsup
              (Filter.Eventually.of_forall fun i => hKLr_upper (idx i))
              (Filter.isCoboundedUnder_le_of_le atTop (fun i => hKLr_nn (idx i)))
              htend.isBoundedUnder_le
        _ = (klDiv μ γ).toReal := htend.limsup_eq
    -- Squeeze: `KLr (idx ·) → (klDiv μ γ).toReal`.
    have hKLr_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop (fun i => KLr (idx i)) :=
      Filter.isBoundedUnder_of ⟨C, fun i => hC i⟩
    have hKLr_bdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop (fun i => KLr (idx i)) :=
      Filter.isBoundedUnder_of ⟨0, fun i => hKLr_nn (idx i)⟩
    have hKLr_idx_tendsto : Tendsto (fun i => KLr (idx i)) atTop (𝓝 ((klDiv μ γ).toReal)) :=
      tendsto_of_le_liminf_of_limsup_le hliminf_ge hlimsup_le hKLr_bdd_le hKLr_bdd_ge
    -- `cross_n (idx ·) → crossμ` along the subsequence.
    have hcross_idx : Tendsto (fun i => cross_n (idx i)) atTop (𝓝 crossμ) :=
      hcross_tendsto.comp (hns.comp _hms_mono.tendsto_atTop)
    -- `h_n (idx ·) = -KLr (idx ·) - cross_n (idx ·) → -(klDiv μ γ).toReal - crossμ = L`.
    have : Tendsto (fun i => h_n (idx i)) atTop (𝓝 (- (klDiv μ γ).toReal - crossμ)) := by
      have heq : (fun i => h_n (idx i)) = fun i => - KLr (idx i) - cross_n (idx i) := by
        funext i; exact hhn_eq (idx i)
      rw [heq]
      exact (hKLr_idx_tendsto.neg).sub hcross_idx
    rw [hL_def]
    exact this
  -- The limsup of a convergent sequence equals its limit (`≤ L` trivially).
  have hKL_limsup : Filter.limsup h_n atTop ≤ L := le_of_eq hKLr_tendsto.limsup_eq
  -- Assemble: rewrite the goal limsup into `h_n`, apply the toReal bound, and close the
  -- final equation through the genuine bridge `hhμ_eq`.
  calc Filter.limsup (fun n => ∫ x, Real.negMulLog (f n x) ∂volume) atTop
      = Filter.limsup h_n atTop := rfl
    _ ≤ L := hKL_limsup
    _ = ∫ x, Real.negMulLog (pX x) ∂volume := hhμ_eq.symm

end InformationTheory.EPIG2KLFatou
