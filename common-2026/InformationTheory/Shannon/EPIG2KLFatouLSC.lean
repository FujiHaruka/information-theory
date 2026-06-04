import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import InformationTheory.Shannon.EPIVitaliAE
import InformationTheory.Shannon.EPIVitaliUnifTight
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

end InformationTheory.EPIG2KLFatou
