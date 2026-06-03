import InformationTheory.Shannon.EPIBlachmanDensity
import InformationTheory.Shannon.EPIConvDensityRegular
import InformationTheory.Shannon.EPIConvDensityNormalization
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.FisherConvBound

/-!
# Non-Gaussian `IsBlachmanConvReady` producer — EPI A-5 precondition (4)

This file supplies a producer for
`IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)` where `pX`/`pY`
are arbitrary probability densities and `g_t = gaussianPDFReal 0 ⟨t, ht.le⟩` is the
heat kernel (`t > 0`). The existing producer
(`isBlachmanConvReady_gaussianPDFReal`) is Gaussian-only; the A-5 chain apex needs the
conv-with-Gaussian (general density) version.

Set `fX := convDensityAdd pX g_t`, `fY := convDensityAdd pY g_t`. Both are
conv-with-Gaussian densities. **All 19 `IsBlachmanConvReady` fields are closed genuinely**
(19/19, no retreat).

* **GENUINE (18 conv-with-Gaussian fields)**: `int_fX/fY`, `bdd_*`, `pos_pZ`,
  `int_X/int_Y`, `cond_int`, `int_W`, `int_Wsq`, `int_inner`, `int_fisherX/int_fisherY`,
  `int_prod1/2/3` — closed from the conv-with-Gaussian regularity assets
  (`isRegularDensityV2_convDensityAdd_gaussian`,
  `convDensityAdd_gaussian_bdd`/`_deriv_bdd`/`_integrable`, `convDensityAdd_pos_of_pos_cont`,
  the Fisher-finiteness bound `gaussianConv_fisher_le_inv_var` via
  `convDensityAdd_fisher_integrand_integrable`, and the shear
  `measurePreserving_prod_sub_swap` for the Tonelli product-measure terms). The key
  reduction is `logDeriv fX · fX = deriv fX` (strict positivity of `fX`), turning the
  linear-score fields into integrable·bounded products and the Fisher fields into
  shifted/sheared copies of `int_fisherX/int_fisherY`.
* **GENUINE (`int_fisherZ`)**: Fisher integrability of the conv-of-conv
  `convDensityAdd fX fY`. The 4-fold interchange bridge
  `convDensityAdd_convGaussian_interchange` (`EPIConvDensityAssoc.lean`) identifies it with
  `convDensityAdd (convDensityAdd pX pY) g_{2t}` (convolution associativity via Mathlib
  `convolution_assoc` + `convDensityAdd_comm` + variance-doubling `g_t ∗ g_t = g_{2t}`),
  which is conv-with-Gaussian (variance `2t`) and closes via
  `convDensityAdd_fisher_integrand_integrable (pX∗pY) … (2t)`. The `pX∗pY` arm needs
  `pX∗pY` to be a normalized probability density (nonneg / measurable / integrable / mass 1),
  supplied by the `convDensityAdd_pXpY_*` helpers in `EPIConvDensityAssoc.lean`.

`hpX_norm : ∫ pX = 1` / `hpY_norm` are added beyond the bare `hpX_mass` of the brief
target signature: they are A-5-suppliable regularity (from `pX_law`'s probability
measure pushforward) and needed by `gaussianConv_fisher_le_inv_var`.
-/

namespace InformationTheory.Shannon.EPIBlachmanGeneralDensity

open MeasureTheory Real ProbabilityTheory
open scoped NNReal
open InformationTheory.Shannon.EPIConvDensity
open InformationTheory.Shannon.EPIBlachmanDensity
open Common2026.Shannon.EPIConvDensityRegular
open Common2026.Shannon.FisherInfoV2

/-- **Fisher integrand integrability for a conv-with-Gaussian density** (public form).

`Integrable ((logDeriv (convDensityAdd pX g_t))² · convDensityAdd pX g_t)` — the
`int_fisherX` shape. Reconstructed from the public Fisher-finiteness bound
`gaussianConv_fisher_le_inv_var` (`J(p_t) ≤ 1/t < ⊤`), exactly mirroring the private
`convDensityAdd_fisher_integrable` body.
@audit:ok — independent honesty audit (2026-06-01): hypotheses are all regularity
(nonneg / Measurable / Integrable / mass `= 1` normalization); the Fisher-integrand
integrability follows genuinely from the existing `@audit:ok` bound
`gaussianConv_fisher_le_inv_var` (`J(p_t) < ⊤`) + `lintegral_ofReal_ne_top_iff_integrable`.
No bundled core (the Fisher inequality is *imported* from a proved lemma, not a hypothesis).
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-confirmed). -/
theorem convDensityAdd_fisher_integrand_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_norm : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) ^ 2
      * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hp_def
  have hp_nn : ∀ x, 0 ≤ p_t x := fun x =>
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  have hg_nn : 0 ≤ᵐ[volume] fun x => (logDeriv p_t x) ^ 2 * p_t x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hp_nn x)
  have hbound : fisherInfoOfDensity p_t ≤ ENNReal.ofReal (1 / t) :=
    gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int hpX_norm ht
  have hfin : fisherInfoOfDensity p_t < ⊤ :=
    lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hmerge :
      fisherInfoOfDensity p_t
        = ∫⁻ x, ENNReal.ofReal ((logDeriv p_t x) ^ 2 * p_t x) ∂volume := by
    unfold fisherInfoOfDensity
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hmerge] at hfin
  have hgt_meas : Measurable (gaussianPDFReal 0 ⟨t, ht.le⟩) :=
    measurable_gaussianPDFReal 0 ⟨t, ht.le⟩
  have hpt_meas : Measurable p_t := by
    have huncurry :
        StronglyMeasurable
          (Function.uncurry fun z x => pX x * gaussianPDFReal 0 ⟨t, ht.le⟩ (z - x)) := by
      apply Measurable.stronglyMeasurable
      apply (hpX_meas.comp measurable_snd).mul
      exact hgt_meas.comp ((measurable_fst).sub measurable_snd)
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [hp_def, convDensityAdd] using h.measurable
  have hderiv_meas : Measurable (deriv p_t) := measurable_deriv p_t
  have hlogderiv_meas : Measurable (logDeriv p_t) := by
    simp only [logDeriv]
    exact hderiv_meas.div hpt_meas
  have hg_aesm :
      AEStronglyMeasurable (fun x => (logDeriv p_t x) ^ 2 * p_t x) volume :=
    ((hlogderiv_meas.pow_const 2).mul hpt_meas).aestronglyMeasurable
  exact (lintegral_ofReal_ne_top_iff_integrable hg_aesm hg_nn).mp hfin.ne

/-- Global boundedness of a conv-with-Gaussian density:
`|convDensityAdd pX g_t z| ≤ (sup g_t) · ∫ pX`.
@audit:ok — independent honesty audit (2026-06-01): constructive bound (`∫pX · Mg`),
regularity hypotheses only, sorryAx-free transitively via the producer. -/
theorem convDensityAdd_gaussian_bdd
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ, ∀ z, |convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) z| ≤ M := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg
  set Mg : ℝ := (Real.sqrt (2 * Real.pi * (⟨t, ht.le⟩ : ℝ≥0)))⁻¹ with hMg
  have hMg_nn : (0:ℝ) ≤ Mg := by rw [hMg]; positivity
  refine ⟨(∫ x, pX x ∂volume) * Mg, fun z => ?_⟩
  -- |∫ pX(x) g(z-x)| ≤ ∫ |pX(x) g(z-x)| ≤ ∫ pX(x)·Mg = (∫pX)·Mg
  have hge : ∀ x, |pX x * g (z - x)| ≤ pX x * Mg := by
    intro x
    rw [abs_mul, abs_of_nonneg (hpX_nn x)]
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_abs_le _ (z - x)) (hpX_nn x)
  have hbound_int : Integrable (fun x => pX x * Mg) volume := hpX_int.mul_const Mg
  calc |convDensityAdd pX g z| = |∫ x, pX x * g (z - x) ∂volume| := rfl
    _ ≤ ∫ x, |pX x * g (z - x)| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ x, pX x * Mg ∂volume := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x => abs_nonneg _
        · exact hbound_int
        · exact Filter.Eventually.of_forall hge
    _ = (∫ x, pX x ∂volume) * Mg := by rw [integral_mul_const]

/-- `convDensityAdd pX g_t` is Lebesgue-integrable (envelope).
@audit:ok — independent honesty audit (2026-06-01): delegates to the proved
`convDensityAdd_envelope_integrable`, regularity hypotheses only, sorryAx-free transitively. -/
theorem convDensityAdd_gaussian_integrable
    (pX : ℝ → ℝ) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) volume := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  exact Common2026.Shannon.FisherInfoV2.convDensityAdd_envelope_integrable
    pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_int hpX_meas
    (ProbabilityTheory.integrable_gaussianPDFReal 0 ⟨t, ht.le⟩)
    (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)

/-- `deriv (convDensityAdd pX g_t)` is globally bounded:
`|deriv (convDensityAdd pX g_t) z| = |convDensityAdd pX (deriv g_t) z| ≤ (sup|deriv g_t|)·∫pX`.
@audit:ok — independent honesty audit (2026-06-01): constructive bound via
`deriv_convDensityAdd_eq` (differentiation-under-integral) + global `deriv g_t` sup,
regularity hypotheses only, sorryAx-free transitively. -/
theorem convDensityAdd_gaussian_deriv_bdd
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ, ∀ z, |deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) z| ≤ M := by
  have hv_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact ht.ne' (congrArg NNReal.toReal h)
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg
  obtain ⟨Mg, hMg⟩ := deriv_gaussianPDFReal_abs_le hv_ne
  -- WLOG Mg ≥ 0
  have hMg_nn : (0:ℝ) ≤ Mg := le_trans (abs_nonneg _) (hMg 0)
  have hderiv_eq : deriv (convDensityAdd pX g) = convDensityAdd pX (deriv g) :=
    deriv_convDensityAdd_eq ht hpX_int
  refine ⟨(∫ x, pX x ∂volume) * Mg, fun z => ?_⟩
  rw [hderiv_eq]
  have hge : ∀ x, |pX x * deriv g (z - x)| ≤ pX x * Mg := by
    intro x
    rw [abs_mul, abs_of_nonneg (hpX_nn x)]
    exact mul_le_mul_of_nonneg_left (hMg (z - x)) (hpX_nn x)
  have hbound_int : Integrable (fun x => pX x * Mg) volume := hpX_int.mul_const Mg
  calc |convDensityAdd pX (deriv g) z| = |∫ x, pX x * deriv g (z - x) ∂volume| := rfl
    _ ≤ ∫ x, |pX x * deriv g (z - x)| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ x, pX x * Mg ∂volume := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x => abs_nonneg _
        · exact hbound_int
        · exact Filter.Eventually.of_forall hge
    _ = (∫ x, pX x ∂volume) * Mg := by rw [integral_mul_const]

/-- **General convolution positivity.** If `fX`, `fY` are continuous, strictly
positive everywhere, and the integrand `x ↦ fX x · fY (z - x)` is integrable, then the
convolution density `convDensityAdd fX fY z` is strictly positive.
@audit:ok — independent honesty audit (2026-06-01): genuine positivity via
`integral_pos_of_integrable_nonneg_nonzero` (continuous nonneg integrand, nonzero at 0);
hypotheses are regularity (Continuous / pointwise positivity / Integrable), sorryAx-free
transitively. -/
theorem convDensityAdd_pos_of_pos_cont (fX fY : ℝ → ℝ)
    (hfX_cont : Continuous fX) (hfY_cont : Continuous fY)
    (hfX_pos : ∀ x, 0 < fX x) (hfY_pos : ∀ x, 0 < fY x)
    (z : ℝ)
    (hint : Integrable (fun x => fX x * fY (z - x)) volume) :
    0 < convDensityAdd fX fY z := by
  have hcont : Continuous (fun x => fX x * fY (z - x)) :=
    hfX_cont.mul (hfY_cont.comp (continuous_const.sub continuous_id))
  have hnn : 0 ≤ (fun x => fX x * fY (z - x)) := fun x =>
    (mul_pos (hfX_pos x) (hfY_pos (z - x))).le
  exact integral_pos_of_integrable_nonneg_nonzero (x := (0:ℝ)) hcont hint hnn
    (by exact (mul_pos (hfX_pos 0) (hfY_pos (z - 0))).ne')

/-- **Non-Gaussian `IsBlachmanConvReady` producer** for EPI A-5 precondition (4).

`fX := convDensityAdd pX g_t`, `fY := convDensityAdd pY g_t`.

@audit:ok — independent honesty audit (2026-06-01): all 11 hypotheses are pure regularity
on the *input* densities `pX`/`pY` (nonneg / Measurable / Integrable / `0 < mass` /
`mass = 1`); none is an inequality / equality / Fisher core. The output is the 19-field
`IsBlachmanConvReady` regularity bundle for the *convolved* densities — genuinely derived,
not a circular `:= h` (the conclusion is about `convDensityAdd pX g_t` / `convDensityAdd pY g_t`,
a distinct proposition from any hypothesis). The 19 fields are built from proved assets
(`isRegularDensityV2_convDensityAdd_gaussian`, `gaussianConv_fisher_le_inv_var`,
`measurePreserving_prod_sub_swap`), not from a load-bearing predicate. `int_fisherZ` closure
is genuine: the 4-fold interchange bridge `convDensityAdd_convGaussian_interchange` identifies
the conv-of-conv with `convDensityAdd (pX∗pY) g_{2t}` (real convolution associativity, traced)
and closes via `convDensityAdd_fisher_integrand_integrable (pX∗pY) … (2t)` — sufficiency
verified, no false framing. The two extra hypotheses `hpX_norm` / `hpY_norm` (`∫ = 1`) are
genuine regularity preconditions required by `gaussianConv_fisher_le_inv_var`'s `mass = 1`
argument (probability-density normalization, A-5-suppliable from `pX_law`), NOT load-bearing.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-confirmed
end-to-end through the full helper chain). -/
theorem isBlachmanConvReady_convDensityAdd_gaussian (pX pY : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    (hpX_mass : 0 < ∫ x, pX x ∂volume) (hpX_norm : (∫ x, pX x ∂volume) = 1)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY) (hpY_int : Integrable pY volume)
    (hpY_mass : 0 < ∫ x, pY x ∂volume) (hpY_norm : (∫ x, pY x ∂volume) = 1) :
    IsBlachmanConvReady
      (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      (convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩)) where
  int_fX := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht
  int_fY := convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht
  bdd_fX := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int ht
  bdd_fX' := convDensityAdd_gaussian_deriv_bdd pX hpX_nn hpX_int ht
  bdd_fY := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
  bdd_fY' := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
  pos_pZ := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    obtain ⟨MfY, hMfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    have hint : Integrable (fun x => fX x * fY (z - x)) volume :=
      (convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht).mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := MfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hMfY (z - x))
    exact convDensityAdd_pos_of_pos_cont fX fY hregX.diff.continuous hregY.diff.continuous
      hregX.pos hregY.pos z hint
  int_X := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pX hpX_nn hpX_int ht
    have hg : Integrable (fun x => fY (z - x)) volume :=
      (convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht).comp_sub_left z
    refine hg.bdd_mul ?_ (c := M) ?_
    · exact (measurable_deriv fX).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x
  int_Y := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
    have hg : Integrable fX volume := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht
    refine hg.mul_bdd ?_ (c := M) ?_
    · exact ((measurable_deriv fY).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM (z - x)
  cond_int := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    obtain ⟨MfY, hMfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hbase : Integrable (fun x => fX x * fY (z - x)) volume :=
      (convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht).mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := MfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hMfY (z - x))
    refine (hbase.div_const (convDensityAdd fX fY z)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [condDensityX]
  int_W := by
    intro lam _ _ z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    -- `logDeriv f · f = deriv f` since `f > 0`.
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    obtain ⟨MfX, hMfX⟩ := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int ht
    obtain ⟨MfY, hMfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    -- term A: deriv fX (= logDeriv fX·fX, integrable) × fY(z-·) (bounded)
    have hA : Integrable (fun x =>
        logDeriv fX x * fX x * fY (z - x)) volume := by
      have hbase : Integrable (fun x => deriv fX x * fY (z - x)) volume := by
        have hg : Integrable (fun x => fY (z - x)) volume :=
          (convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht).comp_sub_left z
        obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pX hpX_nn hpX_int ht
        refine hg.bdd_mul (measurable_deriv fX).aestronglyMeasurable (c := M)
          (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
      refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [← hlogX x]
    -- term B: fX (bounded) × deriv fY(z-·) (= logDeriv fY(z-·)·fY(z-·), integrable shift)
    have hB : Integrable (fun x =>
        fX x * (logDeriv fY (z - x) * fY (z - x))) volume := by
      have hbase : Integrable (fun x => fX x * deriv fY (z - x)) volume := by
        have hg : Integrable fX volume := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht
        obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
        refine hg.mul_bdd
          ((measurable_deriv fY).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
          (c := M) (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM (z - x))
      refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [← hlogY (z - x)]
    have hcomb := ((hA.const_mul lam).add (hB.const_mul (1 - lam))).div_const
      (convDensityAdd fX fY z)
    refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [scoreWeight, condDensityX, Pi.add_apply]
    ring
  int_Wsq := by
    intro lam _ _ z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    obtain ⟨CfX, hCfX⟩ := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int ht
    obtain ⟨CfY, hCfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    obtain ⟨CfY', hCfY'⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
    -- T1: (logDeriv fX x)²·fX x · fY(z-x)  = [int_fisherX] × [bounded fY(z-·)]
    have hT1base : Integrable (fun x => (logDeriv fX x) ^ 2 * fX x) volume :=
      convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm ht
    have hT1 : Integrable (fun x =>
        (logDeriv fX x) ^ 2 * fX x * fY (z - x)) volume :=
      hT1base.mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := CfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hCfY (z - x))
    -- T2 cross: logDeriv fX·fX (= deriv fX, int) × logDeriv fY(z-·)·fY(z-·) (= deriv fY(z-·), bdd)
    have hT2meas : AEStronglyMeasurable
        (fun x => logDeriv fY (z - x) * fY (z - x)) volume := by
      have heq : (fun x => logDeriv fY (z - x) * fY (z - x))
          = (fun x => deriv fY (z - x)) := by funext x; exact hlogY (z - x)
      rw [heq]
      exact ((measurable_deriv fY).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    have hT2 : Integrable (fun x =>
        logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x))) volume := by
      have hbase : Integrable (fun x => deriv fX x * (logDeriv fY (z - x) * fY (z - x))) volume :=
        (hregX.integrable_deriv).mul_bdd hT2meas (c := CfY')
          (Filter.Eventually.of_forall fun x => by
            rw [hlogY (z - x)]; simpa [Real.norm_eq_abs] using hCfY' (z - x))
      refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only []; rw [← hlogX x]
    -- T3: (logDeriv fY(z-·))²·fY(z-·) (int shift) × fX (bdd)
    have hT3pre : Integrable (fun w => (logDeriv fY w) ^ 2 * fY w) volume :=
      convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
    have hT3base : Integrable (fun x => (logDeriv fY (z - x)) ^ 2 * fY (z - x)) volume :=
      hT3pre.comp_sub_left z
    have hT3 : Integrable (fun x =>
        fX x * ((logDeriv fY (z - x)) ^ 2 * fY (z - x))) volume :=
      hT3base.bdd_mul (hregX.diff.continuous.aestronglyMeasurable) (c := CfX)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCfX x)
    have hcomb := ((((hT1.const_mul (lam ^ 2)).add
      (hT2.const_mul (2 * lam * (1 - lam)))).add
      (hT3.const_mul ((1 - lam) ^ 2)))).div_const (convDensityAdd fX fY z)
    refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [scoreWeight, condDensityX, Pi.add_apply]
    ring
  int_inner := by
    intro lam hlam0 hlam1
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    -- product-measure integrabilities (= int_prod1/2/3 integrands), via the shear
    have hP1 : Integrable
        (Function.uncurry fun z x =>
          (logDeriv fX x) ^ 2 * fX x * fY (z - x)) (volume.prod volume) := by
      have hA : Integrable (fun a => (logDeriv fX a) ^ 2 * fX a) volume :=
        convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm ht
      have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).integrable_comp_of_integrable
        (hA.mul_prod (convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht))
      refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Function.uncurry, hfX, hfY]
    have hP2 : Integrable
        (Function.uncurry fun z x =>
          (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x)) (volume.prod volume) := by
      have hB : Integrable (fun b => (logDeriv fY b) ^ 2 * fY b) volume :=
        convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
      have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).integrable_comp_of_integrable
        ((convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht).mul_prod hB)
      refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Function.uncurry, hfX, hfY]; ring
    have hP3 : Integrable
        (Function.uncurry fun z x =>
          logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)))
          (volume.prod volume) := by
      have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).integrable_comp_of_integrable
        ((hregX.integrable_deriv).mul_prod (hregY.integrable_deriv))
      refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Function.uncurry, hfX, hfY]
      rw [← hlogX p.2, ← hlogY (p.1 - p.2)]
    have hI1 := hP1.integral_prod_left
    have hI2 := hP2.integral_prod_left
    have hI3 := hP3.integral_prod_left
    have hcomb := (((hI1.const_mul (lam ^ 2)).add
      (hI3.const_mul (2 * lam * (1 - lam)))).add (hI2.const_mul ((1 - lam) ^ 2)))
    refine hcomb.congr (Filter.Eventually.of_forall fun z => ?_)
    have hpZ : convDensityAdd fX fY z ≠ 0 := by
      have hregZint : Integrable (fun x => fX x * fY (z - x)) volume := by
        obtain ⟨MfY, hMfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
        exact (convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht).mul_bdd
          ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
          (c := MfY) (Filter.Eventually.of_forall fun x => by
            simpa [Real.norm_eq_abs] using hMfY (z - x))
      exact (convDensityAdd_pos_of_pos_cont fX fY hregX.diff.continuous hregY.diff.continuous
        hregX.pos hregY.pos z hregZint).ne'
    set pZ := convDensityAdd fX fY z with hpZdef
    obtain ⟨CfX, hCfX⟩ := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int ht
    obtain ⟨CfY, hCfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    obtain ⟨CfY', hCfY'⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
    -- per-z integrabilities of the three g-terms
    have hg1 : Integrable (fun x =>
        (logDeriv fX x) ^ 2 * fX x * fY (z - x)) volume := by
      have hbase : Integrable (fun x => (logDeriv fX x) ^ 2 * fX x) volume :=
        convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm ht
      exact hbase.mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := CfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hCfY (z - x))
    have hg3 : Integrable (fun x =>
        logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x))) volume := by
      have hmeas : AEStronglyMeasurable (fun x => logDeriv fY (z - x) * fY (z - x)) volume := by
        have heq : (fun x => logDeriv fY (z - x) * fY (z - x))
            = (fun x => deriv fY (z - x)) := by funext x; exact hlogY (z - x)
        rw [heq]
        exact ((measurable_deriv fY).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      have hbase : Integrable (fun x => deriv fX x * (logDeriv fY (z - x) * fY (z - x))) volume :=
        (hregX.integrable_deriv).mul_bdd hmeas (c := CfY')
          (Filter.Eventually.of_forall fun x => by
            rw [hlogY (z - x)]; simpa [Real.norm_eq_abs] using hCfY' (z - x))
      refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only []; rw [← hlogX x]
    have hg2 : Integrable (fun x =>
        (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x)) volume := by
      have hpre : Integrable (fun w => (logDeriv fY w) ^ 2 * fY w) volume :=
        convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
      have hbase : Integrable (fun x => (logDeriv fY (z - x)) ^ 2 * fY (z - x)) volume :=
        hpre.comp_sub_left z
      refine (hbase.bdd_mul (hregX.diff.continuous.aestronglyMeasurable) (c := CfX)
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hCfX x)).congr
        (Filter.Eventually.of_forall fun x => ?_)
      ring
    -- step 1+2: pull pZ inside and cancel condDensityX·pZ = fX·fY(z-·)
    have hstep12 : (∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume) * pZ
        = ∫ x, (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x)) ∂volume := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [condDensityX, ← hpZdef]
      rw [mul_assoc, div_mul_cancel₀ _ hpZ]
    have hexpand : (fun x => (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x)))
        = (fun x => lam ^ 2 * ((logDeriv fX x) ^ 2 * fX x * fY (z - x))
          + 2 * lam * (1 - lam) * (logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)))
          + (1 - lam) ^ 2 * ((logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x))) := by
      funext x; simp only [scoreWeight]; ring
    simp only [Pi.add_apply, Function.uncurry]
    have hsplit : (∫ x, (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x)) ∂volume)
        = lam ^ 2 * (∫ x, (logDeriv fX x) ^ 2 * fX x * fY (z - x) ∂volume)
          + 2 * lam * (1 - lam) * (∫ x, logDeriv fX x * fX x
              * (logDeriv fY (z - x) * fY (z - x)) ∂volume)
          + (1 - lam) ^ 2 * (∫ x, (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x) ∂volume) := by
      rw [hexpand]
      rw [show (fun x => lam ^ 2 * ((logDeriv fX x) ^ 2 * fX x * fY (z - x))
          + 2 * lam * (1 - lam) * (logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)))
          + (1 - lam) ^ 2 * ((logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x)))
          = ((fun x => lam ^ 2 * ((logDeriv fX x) ^ 2 * fX x * fY (z - x)))
              + (fun x => 2 * lam * (1 - lam) * (logDeriv fX x * fX x
                  * (logDeriv fY (z - x) * fY (z - x)))))
            + (fun x => (1 - lam) ^ 2 * ((logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x))) from rfl,
        integral_add' ((hg1.const_mul (lam ^ 2)).add (hg3.const_mul (2 * lam * (1 - lam))))
            (hg2.const_mul ((1 - lam) ^ 2)),
        integral_add' (hg1.const_mul (lam ^ 2)) (hg3.const_mul (2 * lam * (1 - lam))),
        integral_const_mul, integral_const_mul, integral_const_mul]
    rw [hstep12, hsplit]
  int_fisherX :=
    convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm ht
  int_fisherY :=
    convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
  int_fisherZ := by
    -- Fisher integrability of the conv-of-conv `convDensityAdd fX fY`
    -- (`fX = pX∗g_t`, `fY = pY∗g_t`). The 4-fold interchange bridge identifies it with
    -- `convDensityAdd (convDensityAdd pX pY) g_{2t}` (conv-with-Gaussian, variance 2t),
    -- closed by `convDensityAdd_fisher_integrand_integrable (pX∗pY) … (2t)`.
    rw [InformationTheory.Shannon.EPIConvDensity.convDensityAdd_convGaussian_interchange
        pX pY ht hpX_nn hpX_meas hpX_int hpY_nn hpY_meas hpY_int]
    -- `pX∗pY` is a normalized probability density (nonneg / measurable / integrable / mass 1).
    have hPXY_nn : ∀ x, 0 ≤ convDensityAdd pX pY x :=
      fun x => InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_nonneg
        pX pY hpX_nn hpY_nn x
    have hPXY_meas : Measurable (convDensityAdd pX pY) :=
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_measurable
        pX pY hpX_meas hpY_meas
    have hPXY_int : Integrable (convDensityAdd pX pY) volume :=
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integrable
        pX pY hpX_int hpX_meas hpY_int hpY_meas
    have hPXY_norm : (∫ x, convDensityAdd pX pY x ∂volume) = 1 := by
      rw [InformationTheory.Shannon.EPIConvDensity.convDensityAdd_pXpY_integral_eq
        pX pY hpX_int hpY_int, hpX_norm, hpY_norm, mul_one]
    exact convDensityAdd_fisher_integrand_integrable (convDensityAdd pX pY)
      hPXY_nn hPXY_meas hPXY_int hPXY_norm (t := 2 * t) (by positivity)
  int_prod1 := by
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    -- shear `(z,x) ↦ (x, z-x)`: A a = (logDeriv fX a)²·fX a, B b = fY b
    have hA : Integrable (fun a => (logDeriv fX a) ^ 2 * fX a) volume :=
      convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm ht
    have hB : Integrable fY volume := convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable (hA.mul_prod hB)
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]
  int_prod2 := by
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    -- shear `(z,x) ↦ (x, z-x)`: A a = fX a, B b = (logDeriv fY b)²·fY b
    have hA : Integrable fX volume := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int ht
    have hB : Integrable (fun b => (logDeriv fY b) ^ 2 * fY b) volume :=
      convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable (hA.mul_prod hB)
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]; ring
  int_prod3 := by
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX ht hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    -- `logDeriv f · f = deriv f`
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    -- shear `(z,x) ↦ (x, z-x)`: A a = deriv fX a, B b = deriv fY b
    have hA : Integrable (deriv fX) volume := hregX.integrable_deriv
    have hB : Integrable (deriv fY) volume := hregY.integrable_deriv
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable (hA.mul_prod hB)
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]
    rw [← hlogX p.2, ← hlogY (p.1 - p.2)]

end InformationTheory.Shannon.EPIBlachmanGeneralDensity
