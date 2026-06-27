import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EPI.Blachman.GeneralDensity
import InformationTheory.Shannon.EPI.Stam.Inequality

/-!
# Stam's inequality — standalone density-level headline (Cover–Thomas Lemma 17.7.2)

This file assembles the genuine, sorry-free parts already present in the project into a clean,
self-contained statement of **Stam's inequality** at the density level, for the non-vacuous class
of Gaussian-smoothed densities `pX ∗ g_t` (`t > 0`, `pX` any probability density). No new analytic
core is introduced: every ingredient (the convex Fisher bound, the `λ`-optimization, the regularity
and `IsBlachmanConvReady` producers, the convolution Fisher finiteness bound) is an existing
`@audit:ok` asset; this file is the wiring plus the smoothed-density Fisher positivity producer.

## Main statements

* `fisherInfoOfDensity_ne_zero_of_regular` — a regular density has nonzero Fisher information.
* `fisherInfoOfDensity_convDensityAdd_gaussian_pos` — the Fisher information of a Gaussian-smoothed
  density `pX ∗ g_t` is strictly positive and finite (positivity producer, Phase 1).
* `stam_inequality_smoothed_density` — the headline Stam inequality
  `1 / J(fX ∗ fY) ≥ 1 / J(fX) + 1 / J(fY)` for `fX = pX ∗ g_t`, `fY = pY ∗ g_t`.

## References

[CoverThomas2006] Lemma 17.7.2; [Blachman1965].
-/

namespace InformationTheory.Shannon.StamInequality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open InformationTheory.Shannon.FisherInfo
open InformationTheory.Shannon.EPIConvDensity
open InformationTheory.Shannon.EPIConvDensityRegular
open InformationTheory.Shannon.EPIBlachmanDensity
open InformationTheory.Shannon.EPIBlachmanGeneralDensity

/-- A regular density (`IsRegularDensityV2`) has strictly positive Fisher information: if it were
zero, the score `logDeriv f` would vanish a.e., forcing `deriv f = 0` a.e., hence (by the
fundamental theorem of calculus and the integrability of `deriv f`) `f` constant, contradicting the
tail-vanishing and strict positivity of a regular density. -/
theorem fisherInfoOfDensity_ne_zero_of_regular {f : ℝ → ℝ}
    (h_reg : IsRegularDensityV2 f) : fisherInfoOfDensity f ≠ 0 := by
  intro hzero
  have hf_meas : Measurable f := h_reg.diff.continuous.measurable
  have hlogderiv_meas : Measurable (logDeriv f) := by
    unfold logDeriv
    exact (measurable_deriv f).div hf_meas
  have hmeas : Measurable
      (fun x ↦ ENNReal.ofReal ((logDeriv f x) ^ 2) * ENNReal.ofReal (f x)) :=
    ((hlogderiv_meas.pow_const 2).ennreal_ofReal).mul hf_meas.ennreal_ofReal
  rw [fisherInfoOfDensity, lintegral_eq_zero_iff hmeas] at hzero
  -- `deriv f = 0` a.e.
  have hderiv0 : deriv f =ᵐ[volume] 0 := by
    filter_upwards [hzero] with x hx
    have hfx : 0 < f x := h_reg.pos x
    have hofx : ENNReal.ofReal (f x) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hfx
    rcases mul_eq_zero.mp hx with h1 | h2
    · rw [ENNReal.ofReal_eq_zero] at h1
      have hsq : (logDeriv f x) ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
      have hld : logDeriv f x = 0 := by
        exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
      rw [logDeriv_apply] at hld
      rcases div_eq_zero_iff.mp hld with hd | hf0
      · simpa using hd
      · exact absurd hf0 hfx.ne'
    · exact absurd h2 hofx
  -- the interval integral of `deriv f` vanishes
  have hzero_int : ∀ a b : ℝ, ∫ y in a..b, deriv f y = 0 := by
    intro a b
    have h0 : ∫ y in a..b, deriv f y = ∫ _ in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv0] with x hx
      intro _
      simpa using hx
    rw [h0, intervalIntegral.integral_zero]
  -- `f` is constant by the fundamental theorem of calculus
  have hconst : ∀ a b : ℝ, f b = f a := by
    intro a b
    have hftc := intervalIntegral.integral_deriv_eq_sub
      (a := a) (b := b) (f := f) (fun x _ ↦ h_reg.diff x)
      h_reg.integrable_deriv.intervalIntegrable
    rw [hzero_int a b] at hftc
    linarith [hftc]
  -- contradiction: a constant density cannot vanish at `+∞` yet be strictly positive
  have hf_eq : f = fun _ ↦ f 0 := by funext b; exact hconst 0 b
  have htend : Filter.Tendsto (fun _ : ℝ ↦ f 0) Filter.atTop (nhds 0) := by
    rw [← hf_eq]; exact h_reg.tail_top
  have hf0 : (0 : ℝ) = f 0 := tendsto_nhds_unique htend tendsto_const_nhds
  linarith [h_reg.pos 0, hf0]

/-- **Phase 1 positivity producer.** The Fisher information of a Gaussian-smoothed probability
density `pX ∗ g_t` (`t > 0`) is strictly positive (as a real number): finiteness comes from the
convolution Fisher bound `J ≤ 1/t`, and nonzero-ness from regularity. -/
theorem fisherInfoOfDensity_convDensityAdd_gaussian_pos
    (pX : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_norm : ∫ x, pX x ∂volume = 1) :
    0 < (fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))).toReal := by
  have hpX_mass : 0 < ∫ x, pX x ∂volume := by rw [hpX_norm]; norm_num
  have hreg := isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
  have hne_zero :
      fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) ≠ 0 :=
    fisherInfoOfDensity_ne_zero_of_regular hreg
  have hle := gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int hpX_norm ht
  have hlt :
      fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) < ⊤ :=
    lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  exact ENNReal.toReal_pos hne_zero hlt.ne

/-- **Stam's inequality (density-level headline, Cover–Thomas Lemma 17.7.2 / Blachman 1965).**

For probability densities `pX, pY` and a Gaussian heat kernel `g_t` (`t > 0`), the
Gaussian-smoothed densities `fX = pX ∗ g_t`, `fY = pY ∗ g_t` satisfy the inverse (harmonic-mean)
Fisher information inequality

`1 / J(fX ∗ fY) ≥ 1 / J(fX) + 1 / J(fY)`.

The Gaussian-smoothed class is non-vacuous (it contains every heat-flow smoothing of an arbitrary
probability density, not just Gaussian equality cases), so the inequality is not vacuously true.

References: [CoverThomas2006] Lemma 17.7.2; [Blachman1965]. -/
@[entry_point]
theorem stam_inequality_smoothed_density
    (pX pY : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_norm : ∫ x, pX x ∂volume = 1)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY)
    (hpY_int : Integrable pY volume) (hpY_norm : ∫ x, pY x ∂volume = 1) :
    1 / (fisherInfoOfDensity
            (convDensityAdd
              (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
              (convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩)))).toReal
      ≥ 1 / (fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))).toReal
          + 1 / (fisherInfoOfDensity
                  (convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩))).toReal := by
  classical
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg
  set fX : ℝ → ℝ := convDensityAdd pX g with hfX
  set fY : ℝ → ℝ := convDensityAdd pY g with hfY
  -- normalizations give strictly positive masses
  have hpX_mass : 0 < ∫ x, pX x ∂volume := by rw [hpX_norm]; norm_num
  have hpY_mass : 0 < ∫ x, pY x ∂volume := by rw [hpY_norm]; norm_num
  -- regularity of the smoothed densities
  have hregX : IsRegularDensityV2 fX :=
    isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
  have hregY : IsRegularDensityV2 fY :=
    isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
  -- the smoothed densities are normalized
  have hnormX : ∫ x, fX x ∂volume = 1 :=
    integral_convDensityAdd_gaussian_eq_one pX ht hpX_int hpX_norm
  have hnormY : ∫ x, fY x ∂volume = 1 :=
    integral_convDensityAdd_gaussian_eq_one pY ht hpY_int hpY_norm
  -- the Blachman convolution-readiness bundle
  have hready : IsBlachmanConvReady fX fY :=
    isBlachmanConvReady_convDensityAdd_gaussian pX pY ht
      hpX_nn hpX_meas hpX_int hpX_mass hpX_norm
      hpY_nn hpY_meas hpY_int hpY_mass hpY_norm
  -- Fisher positivity of each smoothed density (Phase 1 producer)
  have hJX_pos : 0 < (fisherInfoOfDensity fX).toReal :=
    fisherInfoOfDensity_convDensityAdd_gaussian_pos pX ht hpX_nn hpX_meas hpX_int hpX_norm
  have hJY_pos : 0 < (fisherInfoOfDensity fY).toReal :=
    fisherInfoOfDensity_convDensityAdd_gaussian_pos pY ht hpY_nn hpY_meas hpY_int hpY_norm
  -- Fisher positivity of the convolution `fX ∗ fY`, via the 4-fold interchange
  -- `fX ∗ fY = (pX ∗ pY) ∗ g_{2t}`, reducing to the Phase 1 producer at variance `2t`.
  have hJsum_pos : 0 < (fisherInfoOfDensity (convDensityAdd fX fY)).toReal := by
    have hinter : convDensityAdd fX fY
        = convDensityAdd (convDensityAdd pX pY) (gaussianPDFReal 0 ⟨2 * t, by positivity⟩) := by
      rw [hfX, hfY]
      exact convDensityAdd_convGaussian_interchange pX pY ht
        hpX_nn hpX_meas hpX_int hpY_nn hpY_meas hpY_int
    rw [hinter]
    have hq_nn : ∀ x, 0 ≤ convDensityAdd pX pY x :=
      convDensityAdd_pXpY_nonneg pX pY hpX_nn hpY_nn
    have hq_meas : Measurable (convDensityAdd pX pY) :=
      convDensityAdd_pXpY_measurable pX pY hpX_meas hpY_meas
    have hq_int : Integrable (convDensityAdd pX pY) volume :=
      convDensityAdd_pXpY_integrable pX pY hpX_int hpX_meas hpY_int hpY_meas
    have hq_norm : ∫ x, convDensityAdd pX pY x ∂volume = 1 := by
      rw [convDensityAdd_pXpY_integral_eq pX pY hpX_int hpY_int, hpX_norm, hpY_norm, mul_one]
    exact fisherInfoOfDensity_convDensityAdd_gaussian_pos (convDensityAdd pX pY)
      (by positivity : (0 : ℝ) < 2 * t) hq_nn hq_meas hq_int hq_norm
  -- abbreviate and chain through the convex Fisher bound + λ-optimization + inverse form
  set J_X := (fisherInfoOfDensity fX).toReal with hJXdef
  set J_Y := (fisherInfoOfDensity fY).toReal with hJYdef
  set J_sum := (fisherInfoOfDensity (convDensityAdd fX fY)).toReal with hJsumdef
  have hsum : 0 < J_X + J_Y := by linarith
  have hlam0 : (0 : ℝ) ≤ J_Y / (J_X + J_Y) := by positivity
  have hlam1 : J_Y / (J_X + J_Y) ≤ 1 := by rw [div_le_one hsum]; linarith
  have h_bd := convex_fisher_bound_of_ready fX fY (J_Y / (J_X + J_Y)) hlam0 hlam1
    hregX hregY hnormX hnormY hready
  have h_min := stam_lambda_min hJX_pos hJY_pos
  have h_le : J_sum ≤ J_X * J_Y / (J_X + J_Y) := by linarith [h_bd, h_min]
  exact stam_inverse_form_of_harmonic_mean hJX_pos hJY_pos hJsum_pos h_le

end InformationTheory.Shannon.StamInequality
