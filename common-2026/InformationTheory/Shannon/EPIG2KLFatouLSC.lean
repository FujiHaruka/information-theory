import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import InformationTheory.Shannon.EPIVitaliAE
import InformationTheory.Shannon.EPIVitaliUnifTight
import InformationTheory.Shannon.EPIVitaliUI
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.EPIG2BridgeDensityHelpers

/-!
# EPI G2 (α) upper bound — KL lower-semicontinuity via klFun-Fatou

This file supplies the **(α) upper bound** of the EPI G2 general-sandwich moonshot
along a constructive route that **avoids the Donsker–Varadhan dual hard direction**
(the parked `2b` of `epi-g2-general-sandwich-moonshot-plan.md`).

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

Per the inventory `docs/shannon/epi-g2-alpha-klfun-fatou-inventory.md`, the genuine
Mathlib walls along this route are **0**: the missing facts (KL-LSC, withDensity
rnDeriv quotient) are assemblies of existing parts. Any residual is parked under the
inherited `wall:kl-lower-semicontinuous` slug.
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

`hf_meas`/`hg_meas`/`hf_nn`/`hg_pos`/`hf_int`/`hg_int` are regularity preconditions. -/
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
preconditions; the conclusion is the genuine LSC inequality (not bundled). -/
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

All `hpX_*` are regularity preconditions; `hu_lim` is the input filter. -/
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
`log (gaussianPDFReal 0 v x) = - log (√(2πv)) - x² / (2v)`. -/
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
where `c₀ = − log (√(2πσ²))` and `M2(pX) = ∫ x²·pX`. -/
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
With `g := gaussianPDFReal 0 σ²`, `∫ x, pX x · log (g x) = c₀·(∫pX) − (1/(2σ²))·M2(pX)`. -/
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
expansion `pX_cross_term_expand`; the difference is `−(1/(2σ²))·(∫pX)·u_n → 0`. -/
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

ROUTE (genuine pieces all in this file, sorryAx-free):
- W1 `klDiv_le_liminf_of_ae_tendsto` gives `klDiv μ γ ≤ liminf klDiv (μ_n) γ` (ℝ≥0∞),
- W2 `rnDeriv_withDensity_quotient_ae` identifies `rnDeriv μ_n γ =ᵐ[γ] ofReal (f_n/g)`,
- W4 `convDensity_tendsto_ae_subseq` supplies `f_n → pX` a.e. (subsequence),
- W3 `cross_term_tendsto` gives the cross-term limit,
- the bridge `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` turns each
  `(klDiv μ_n γ).toReal` into `−h(μ_n) − cross_n`, and `tendsto_of_subseq_tendsto`
  promotes the subsequence bound to the full sequence.

REMAINING (parked here): the end-to-end assembly threads the bridge's regularity
preconditions (per-measure equal mass / two-way absolute continuity / `log p`–`log q`
integrability) for the smoothed-density family `μ_n` and for `μ = pX`, converts the
ℝ≥0∞ liminf bound to a `toReal` bound via `klDiv μ γ ≠ ∞`, and runs the subsequence
promotion. None of these are Mathlib walls — they are precondition plumbing on top of the
genuine W1–W4 — so the residual is the inherited `wall:kl-lower-semicontinuous` slug
(its surface has shrunk from "DV dual hard direction" to "Fatou assembly plumbing").

The hypotheses are all regularity preconditions (`pX` density regularity + `σ² ≠ 0` +
`u → 0⁺` positivity); the conclusion is the genuine limsup inequality, not bundled.
@residual(wall:kl-lower-semicontinuous) -/
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
  -- **The toReal-level limsup bound on the entropies** (W1 `klDiv_le_liminf_of_ae_tendsto`
  -- transferred to `toReal`, threaded with the boundedness needed to convert the ℝ≥0∞
  -- liminf to a real limsup, plus the W4 subsequence promotion). This is the only
  -- remaining residual: the toReal / subsequence / boundedness plumbing on top of the
  -- genuine W1–W4 bridge. The genuine pieces below it (bridge per-`n`, entropy
  -- identification, cross-term limit, probability-measure framing) are all wired in.
  --
  -- Concretely this is `limsup h_n ≤ - (klDiv μ γ).toReal - crossμ`: from
  -- `h_n n = - KLr n - cross_n n` (`hhn_eq`, genuine bridge), `KLr n ≥ 0`, the W1 bound
  -- `(klDiv μ γ).toReal ≤ liminf KLr` along the a.e.-convergent W4 subsequence, the W3
  -- limit `cross_n → crossμ`, and the boundedness of `h_n` above (= `- KLr n ≤ 0`).
  -- @residual(wall:kl-lower-semicontinuous)
  have hKL_limsup : Filter.limsup h_n atTop ≤ - (klDiv μ γ).toReal - crossμ := by
    sorry
  -- Assemble: rewrite the goal limsup into `h_n`, apply the toReal bound, and close the
  -- final equation through the genuine bridge `hhμ_eq`.
  calc Filter.limsup (fun n => ∫ x, Real.negMulLog (f n x) ∂volume) atTop
      = Filter.limsup h_n atTop := rfl
    _ ≤ - (klDiv μ γ).toReal - crossμ := hKL_limsup
    _ = ∫ x, Real.negMulLog (pX x) ∂volume := hhμ_eq.symm

end InformationTheory.EPIG2KLFatou
