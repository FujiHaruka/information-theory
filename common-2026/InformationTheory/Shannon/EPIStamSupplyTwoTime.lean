/-
# Two-time harmonic-Stam supply producer (`h_stam_supply` for the two-time EPI assembler)

Produces the `h_stam_supply` clause demanded by
`EPICase1TwoTime.entropyPower_add_ge_case1_of_regular_twotime`
(`InformationTheory/Shannon/EPICase1TwoTime.lean:1620`): for noises `Z_X Z_Y Z`
(all unit, the sum perturbed by a **separate** unit noise `Z`) and de Bruijn
regularity hyps `h_reg_X`, `h_reg_Y`, `h_reg_sum`, at every pair of matched times
`σ, τ > 0` the three smoothed Fisher informations are positive and the inverse-Stam
inequality `1/J_S ≥ 1/J_X + 1/J_Y` holds, where `J_S` is the single-noise sum heat
flow at `σ + τ`.

## Approach

Mirror the same-time producer `EPIDensityForm.lean:300-414` (which parks the sum
conjuncts because the same-noise sum has variance `𝒩(0,2)`), but with **separate
times** `σ ≠ τ` and a **separate unit noise** `Z` for the sum. The asymmetric
variance-add bridge `EPIConvDensityAssoc.convDensityAdd_convGaussian_interchange_asym`
then closes the conv-pin seam at the genuine sum-time `σ + τ` (no `𝒩(0,2)` reparam).

The structure `IsRegularDeBruijnHypV2` exposes a smooth density witness `density_t`
pointwise-pinned (`density_t_eq`, ∀x not a.e.) to `convDensityAdd pX g_t`. The three
positivities and all `IsStamInequalityHyp` regularity gates are discharged by rewriting
`density_t` to its conv-Gaussian form and reusing the per-time conv-Gaussian producers.

The single genuinely-new piece is the conv-pin gate
`density_sum_{σ+τ} = convDensityAdd density_X_σ density_Y_τ`, reduced via the asym
interchange to the **input-level a.e. identity** `pXY =ᵐ convDensityAdd pX pY`
(independent-sum density = convolution-of-densities), proved from `pX_law`/`pY_law`/
`pXY_law` + `IndepFun.map_add_eq_map_conv_map` + `conv_withDensity_eq_lconvolution`
+ withDensity a.e.-uniqueness. The a.e.→pointwise wash through `convDensityAdd · g`
is honest: the consumed object is the pointwise-pinned smooth `density_t`, the a.e.
seam lives only at the un-smoothed input density.

SoT plan: `docs/shannon/epi-debruijn-pertime-closure-plan.md` (closure of the seam).
-/
import InformationTheory.Shannon.EPICase1TwoTime
import InformationTheory.Shannon.EPIStamStep3Body
import InformationTheory.Shannon.EPIConvDensityRegular
import InformationTheory.Shannon.EPIBlachmanGeneralDensity
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.EPIConvDensityNormalization
import InformationTheory.Shannon.FisherInfoV2DeBruijn

namespace InformationTheory.Shannon.EPIStamSupplyTwoTime

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.FisherInfoV2
open InformationTheory.Shannon.EPIConvDensity
open InformationTheory.Shannon.EPIConvDensityRegular
open InformationTheory.Shannon.EPIBlachmanDensity
open InformationTheory.Shannon.EPIBlachmanGeneralDensity
open scoped ENNReal NNReal Convolution

/-- **Density facts from a `withDensity` law** (probability-density normalization):
if `P.map W = volume.withDensity (ofReal ∘ p)` with `P` a probability measure and `p ≥ 0`
measurable, then `p` is `volume`-integrable with mass `1`. Copy of the `density_facts`
local lemma in `EPIDensityForm.lean:321-340`, lifted to a top-level helper. -/
theorem density_int_mass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : Ω → ℝ) (p : ℝ → ℝ)
    (hW : Measurable W) (hp_nn : ∀ x, 0 ≤ p x) (hp_meas : Measurable p)
    (hp_law : P.map W = volume.withDensity (fun x => ENNReal.ofReal (p x))) :
    Integrable p volume ∧ (∫ x, p x ∂volume) = 1 := by
  have hprob : IsProbabilityMeasure (P.map W) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hW.aemeasurable
  have hlint : (∫⁻ x, ENNReal.ofReal (p x) ∂volume) = 1 := by
    have := hprob.measure_univ
    rw [hp_law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have hp_int : Integrable p volume := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hp_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hp_nn)]
    rw [hlint]; exact ENNReal.one_ne_top
  have hp_mass : (∫ x, p x ∂volume) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hp_nn)
      hp_meas.aestronglyMeasurable, hlint, ENNReal.toReal_one]
  exact ⟨hp_int, hp_mass⟩

/-- **The independent-sum input identity (the seam)**: for `X ⊥ Y` with Lebesgue
densities `pX`, `pY` and `X+Y` with Lebesgue density `pXY` (all from probability-measure
`withDensity` laws), the sum density equals the convolution of the addend densities a.e.:
`pXY =ᵐ[volume] convDensityAdd pX pY`.

Both `pXY` and `convDensityAdd pX pY` are densities of
`P.map (X+Y) = (P.map X) ∗ (P.map Y)` (independence), and `withDensity` densities are
a.e.-unique. This is an a.e. identity at the **un-smoothed input** level; the consumed
`density_t` is pinned pointwise to the *smooth* convolution, so this a.e. seam is honest. -/
theorem indepSum_density_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (pX pY pXY : ℝ → ℝ)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (hpY_law : P.map Y = volume.withDensity (fun x => ENNReal.ofReal (pY x)))
    (hpXY_law : P.map (fun ω => X ω + Y ω)
      = volume.withDensity (fun x => ENNReal.ofReal (pXY x)))
    (hpXY_nn : ∀ x, 0 ≤ pXY x) (hpXY_meas : Measurable pXY)
    (hpX_int : Integrable pX volume) (hpY_int : Integrable pY volume)
    (hpXY_lmass : (∫⁻ x, ENNReal.ofReal (pXY x) ∂volume) ≠ ⊤)
    (hpX_lmass : (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) = 1)
    (hpY_lmass : (∫⁻ x, ENNReal.ofReal (pY x) ∂volume) = 1) :
    pXY =ᵐ[volume] convDensityAdd pX pY := by
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (pX x) with hF
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (pY x) with hG
  have hF_meas : Measurable F := hpX_meas.ennreal_ofReal
  have hG_meas : Measurable G := hpY_meas.ennreal_ofReal
  -- Step 1: `P.map (X+Y) = withDensity F ∗ withDensity G = withDensity (F ⋆ₗ G)`.
  have hmap : P.map (fun ω => X ω + Y ω)
      = volume.withDensity (F ⋆ₗ[volume] G) := by
    rw [show (fun ω => X ω + Y ω) = X + Y from rfl,
      hXY.map_add_eq_map_conv_map hX hY, hpX_law, hpY_law,
      conv_withDensity_eq_lconvolution hF_meas hG_meas]
  -- Step 2: `ofReal∘pXY =ᵐ F ⋆ₗ G` by `withDensity` a.e.-uniqueness.
  have hwd_eq : volume.withDensity (fun x => ENNReal.ofReal (pXY x))
      = volume.withDensity (F ⋆ₗ[volume] G) := by rw [← hpXY_law, hmap]
  have hae1 : (fun x => ENNReal.ofReal (pXY x)) =ᵐ[volume] (F ⋆ₗ[volume] G) :=
    (withDensity_eq_iff hpXY_meas.ennreal_ofReal.aemeasurable
      (MeasureTheory.measurable_lconvolution volume hF_meas hG_meas).aemeasurable
      hpXY_lmass).mp hwd_eq
  -- Step 3: `F ⋆ₗ G =ᵐ ofReal∘(convDensityAdd pX pY)`.
  -- a.e.-z finiteness of the inner `∫⁻ y, F y * G (-y+z)` (Tonelli: total mass `= 1·1`),
  -- then a.e.-z `ofReal_integral_eq_lintegral_ofReal`.
  have hae2 : (F ⋆ₗ[volume] G) =ᵐ[volume]
      fun z => ENNReal.ofReal (convDensityAdd pX pY z) := by
    -- finiteness of the total lconvolution mass (Tonelli: `= (∫⁻F)·(∫⁻G) = 1`).
    have hfin : (∫⁻ z, (F ⋆ₗ[volume] G) z ∂volume) ≠ ⊤ := by
      have heq : (∫⁻ z, (F ⋆ₗ[volume] G) z ∂volume)
          = (∫⁻ y, F y ∂volume) * ∫⁻ w, G w ∂volume := by
        simp only [lconvolution_def]
        -- swap the order of integration (`(y,z) ↦ F y · G(-y+z)` is measurable)
        rw [lintegral_lintegral_swap
          (by exact ((hF_meas.comp measurable_snd).mul
            (hG_meas.comp ((measurable_snd.neg).add measurable_fst))).aemeasurable)]
        -- inner `∫⁻ z, F y · G(-y+z) = F y · ∫⁻ z, G z` (translation invariance)
        have hinner : ∀ y : ℝ, (∫⁻ z, F y * G (-y + z) ∂volume)
            = F y * ∫⁻ w, G w ∂volume := by
          intro y
          have htrans : (∫⁻ z, G (-y + z) ∂volume) = ∫⁻ w, G w ∂volume :=
            (measurePreserving_add_left (volume : Measure ℝ) (-y)).lintegral_comp hG_meas
          calc (∫⁻ z, F y * G (-y + z) ∂volume)
              = F y * ∫⁻ z, G (-y + z) ∂volume :=
                lintegral_const_mul (F y) (hG_meas.comp (measurable_const.add measurable_id'))
            _ = F y * ∫⁻ w, G w ∂volume := by rw [htrans]
        simp only [hinner]
        rw [lintegral_mul_const _ hF_meas]
      rw [heq, hpX_lmass, hpY_lmass]; simp
    have hae_fin : ∀ᵐ z ∂volume, (F ⋆ₗ[volume] G) z < ⊤ :=
      ae_lt_top (MeasureTheory.measurable_lconvolution volume hF_meas hG_meas) hfin
    filter_upwards [hae_fin] with z hz
    -- per finite-`z`: `∫⁻ y, ofReal(pX y)·ofReal(pY(-y+z)) = ofReal(∫ y, pX y·pY(z-y))`
    rw [lconvolution_def] at hz ⊢
    have hofReal_mul : ∀ y : ℝ,
        ENNReal.ofReal (pX y) * ENNReal.ofReal (pY (-y + z))
          = ENNReal.ofReal (pX y * pY (-y + z)) :=
      fun y => (ENNReal.ofReal_mul (hpX_nn y)).symm
    simp only [hF, hG, hofReal_mul] at hz ⊢
    have hsub : ∀ y : ℝ, (-y + z) = z - y := fun y => by ring
    simp only [hsub] at hz ⊢
    -- a.e.-`z` integrability of `fun y => pX y · pY(z-y)` from finiteness `hz`.
    have hmeasf : AEMeasurable (fun y => pX y * pY (z - y)) volume :=
      (hpX_meas.mul (hpY_meas.comp (measurable_const.sub measurable_id))).aemeasurable
    have hint : Integrable (fun y => pX y * pY (z - y)) volume := by
      rw [← lintegral_ofReal_ne_top_iff_integrable hmeasf.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => mul_nonneg (hpX_nn y) (hpY_nn (z - y)))]
      exact hz.ne
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => mul_nonneg (hpX_nn y) (hpY_nn (z - y)))]
    rfl
  -- Step 4: combine + strip `ofReal`.
  have hae3 : (fun x => ENNReal.ofReal (pXY x))
      =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd pX pY z) := hae1.trans hae2
  filter_upwards [hae3] with x hx
  have hpos : (0 : ℝ) ≤ convDensityAdd pX pY x :=
    integral_nonneg fun y => mul_nonneg (hpX_nn y) (hpY_nn (x - y))
  exact (ENNReal.ofReal_eq_ofReal_iff (hpXY_nn x) hpos).mp hx

/-- **Asymmetric `IsBlachmanConvReady` producer** (independent times `σ ≠ τ`):
`IsBlachmanConvReady (convDensityAdd pX g_σ) (convDensityAdd pY g_τ)`. Faithful
generalization of `EPIBlachmanGeneralDensity.isBlachmanConvReady_convDensityAdd_gaussian`
(which hardcodes the same `t` for both arms) — every field's construction uses only the
public **per-arm** conv-Gaussian lemmas (`convDensityAdd_gaussian_integrable` / `_bdd` /
`_deriv_bdd` / `convDensityAdd_fisher_integrand_integrable` / `convDensityAdd_pos_of_pos_cont`
/ `isRegularDensityV2_convDensityAdd_gaussian`), each at its own arm's time, so the same-`t`
restriction was incidental. The only structural change is `int_fisherZ`: the conv-of-conv
`conv(pX∗g_σ)(pY∗g_τ)` is identified with `conv(pX∗pY) g_{σ+τ}` via the **asymmetric**
interchange bridge `convDensityAdd_convGaussian_interchange_asym` (variance `σ+τ`, not `2t`).

All hypotheses are regularity preconditions; the conclusion (19-field integrability /
boundedness / positivity bundle) is genuinely derived. No bundled analytic core. -/
theorem isBlachmanConvReady_convDensityAdd_gaussian_asym (pX pY : ℝ → ℝ) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    (hpX_mass : 0 < ∫ x, pX x ∂volume) (hpX_norm : (∫ x, pX x ∂volume) = 1)
    (hpY_nn : ∀ x, 0 ≤ pY x) (hpY_meas : Measurable pY) (hpY_int : Integrable pY volume)
    (hpY_mass : 0 < ∫ x, pY x ∂volume) (hpY_norm : (∫ x, pY x ∂volume) = 1) :
    IsBlachmanConvReady
      (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      (convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩)) where
  int_fX := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs
  int_fY := convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht
  bdd_fX := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int hs
  bdd_fX' := convDensityAdd_gaussian_deriv_bdd pX hpX_nn hpX_int hs
  bdd_fY := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
  bdd_fY' := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
  pos_pZ := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX hs hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    obtain ⟨MfY, hMfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    have hint : Integrable (fun x => fX x * fY (z - x)) volume :=
      (convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs).mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := MfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hMfY (z - x))
    exact convDensityAdd_pos_of_pos_cont fX fY hregX.diff.continuous hregY.diff.continuous
      hregX.pos hregY.pos z hint
  int_X := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pX hpX_nn hpX_int hs
    have hg : Integrable (fun x => fY (z - x)) volume :=
      (convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht).comp_sub_left z
    refine hg.bdd_mul ?_ (c := M) ?_
    · exact (measurable_deriv fX).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x
  int_Y := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
    have hg : Integrable fX volume := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs
    refine hg.mul_bdd ?_ (c := M) ?_
    · exact ((measurable_deriv fY).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM (z - x)
  cond_int := by
    intro z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    obtain ⟨MfY, hMfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hbase : Integrable (fun x => fX x * fY (z - x)) volume :=
      (convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs).mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := MfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hMfY (z - x))
    refine (hbase.div_const (convDensityAdd fX fY z)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [condDensityX]
  int_W := by
    intro lam _ _ z
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX hs hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    have hA : Integrable (fun x =>
        logDeriv fX x * fX x * fY (z - x)) volume := by
      have hbase : Integrable (fun x => deriv fX x * fY (z - x)) volume := by
        have hg : Integrable (fun x => fY (z - x)) volume :=
          (convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht).comp_sub_left z
        obtain ⟨M, hM⟩ := convDensityAdd_gaussian_deriv_bdd pX hpX_nn hpX_int hs
        refine hg.bdd_mul (measurable_deriv fX).aestronglyMeasurable (c := M)
          (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
      refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [← hlogX x]
    have hB : Integrable (fun x =>
        fX x * (logDeriv fY (z - x) * fY (z - x))) volume := by
      have hbase : Integrable (fun x => fX x * deriv fY (z - x)) volume := by
        have hg : Integrable fX volume := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs
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
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX hs hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    obtain ⟨CfX, hCfX⟩ := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int hs
    obtain ⟨CfY, hCfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    obtain ⟨CfY', hCfY'⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
    have hT1base : Integrable (fun x => (logDeriv fX x) ^ 2 * fX x) volume :=
      convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm hs
    have hT1 : Integrable (fun x =>
        (logDeriv fX x) ^ 2 * fX x * fY (z - x)) volume :=
      hT1base.mul_bdd
        ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (c := CfY) (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hCfY (z - x))
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
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX hs hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    have hP1 : Integrable
        (Function.uncurry fun z x =>
          (logDeriv fX x) ^ 2 * fX x * fY (z - x)) (volume.prod volume) := by
      have hA : Integrable (fun a => (logDeriv fX a) ^ 2 * fX a) volume :=
        convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm hs
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
        ((convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs).mul_prod hB)
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
        exact (convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs).mul_bdd
          ((hregY.diff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
          (c := MfY) (Filter.Eventually.of_forall fun x => by
            simpa [Real.norm_eq_abs] using hMfY (z - x))
      exact (convDensityAdd_pos_of_pos_cont fX fY hregX.diff.continuous hregY.diff.continuous
        hregX.pos hregY.pos z hregZint).ne'
    set pZ := convDensityAdd fX fY z with hpZdef
    obtain ⟨CfX, hCfX⟩ := convDensityAdd_gaussian_bdd pX hpX_nn hpX_int hs
    obtain ⟨CfY, hCfY⟩ := convDensityAdd_gaussian_bdd pY hpY_nn hpY_int ht
    obtain ⟨CfY', hCfY'⟩ := convDensityAdd_gaussian_deriv_bdd pY hpY_nn hpY_int ht
    have hg1 : Integrable (fun x =>
        (logDeriv fX x) ^ 2 * fX x * fY (z - x)) volume := by
      have hbase : Integrable (fun x => (logDeriv fX x) ^ 2 * fX x) volume :=
        convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm hs
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
    convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm hs
  int_fisherY :=
    convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
  int_fisherZ := by
    rw [InformationTheory.Shannon.EPIConvDensity.convDensityAdd_convGaussian_interchange_asym
        pX pY hs ht hpX_nn hpX_meas hpX_int hpY_nn hpY_meas hpY_int]
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
      hPXY_nn hPXY_meas hPXY_int hPXY_norm (t := s + t) (by positivity)
  int_prod1 := by
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hA : Integrable (fun a => (logDeriv fX a) ^ 2 * fX a) volume :=
      convDensityAdd_fisher_integrand_integrable pX hpX_nn hpX_meas hpX_int hpX_norm hs
    have hB : Integrable fY volume := convDensityAdd_gaussian_integrable pY hpY_meas hpY_int ht
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable (hA.mul_prod hB)
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]
  int_prod2 := by
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hA : Integrable fX volume := convDensityAdd_gaussian_integrable pX hpX_meas hpX_int hs
    have hB : Integrable (fun b => (logDeriv fY b) ^ 2 * fY b) volume :=
      convDensityAdd_fisher_integrand_integrable pY hpY_nn hpY_meas hpY_int hpY_norm ht
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable (hA.mul_prod hB)
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]; ring
  int_prod3 := by
    set fX : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) with hfX
    set fY : ℝ → ℝ := convDensityAdd pY (gaussianPDFReal 0 ⟨t, ht.le⟩) with hfY
    have hregX := isRegularDensityV2_convDensityAdd_gaussian pX hs hpX_nn hpX_meas hpX_int hpX_mass
    have hregY := isRegularDensityV2_convDensityAdd_gaussian pY ht hpY_nn hpY_meas hpY_int hpY_mass
    have hlogX : ∀ w, logDeriv fX w * fX w = deriv fX w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos w).ne']
    have hlogY : ∀ w, logDeriv fY w * fY w = deriv fY w := fun w => by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos w).ne']
    have hA : Integrable (deriv fX) volume := hregX.integrable_deriv
    have hB : Integrable (deriv fY) volume := hregY.integrable_deriv
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable (hA.mul_prod hB)
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]
    rw [← hlogX p.2, ← hlogY (p.1 - p.2)]

/-- **Two-time harmonic-Stam supply producer**.

For `X Y Z_X Z_Y Z : Ω → ℝ` (all unit noises, sum perturbed by separate `Z`), independent
appropriately, with Lebesgue densities and finite second moments, and de Bruijn regularity
`h_reg_X`/`h_reg_Y`/`h_reg_sum`, the `h_stam_supply` clause of
`entropyPower_add_ge_case1_of_regular_twotime` holds: at every matched pair `σ, τ > 0`,
the three smoothed Fisher informations are positive and `1/J_S ≥ 1/J_X + 1/J_Y` with
`J_S` the single-noise sum heat flow at `σ + τ`.

Genuine (no residual): the conv-pin seam `indepSum_density_ae`
(`pXY =ᵐ convDensityAdd pX pY`) is proved via
`IndepFun.map_add_eq_map_conv_map` + `conv_withDensity_eq_lconvolution`
+ `withDensity` a.e.-uniqueness + the lconvolution-Bochner a.e. bridge
(Tonelli finiteness + a.e.-`z` `ofReal_integral_eq_lintegral_ofReal`). -/
theorem twoTime_stam_supply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z_X Z_Y Z : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hXZX : IndepFun X Z_X P) (hYZY : IndepFun Y Z_Y P) (hXY : IndepFun X Y P)
    -- joint independence of the two source-noise pairs (supplied by the lift's
    -- `iIndepFun ![X, Y, Z_X, Z_Y]` via `indepFun_prodMk_prodMk`); needed for `A ⊥ B`.
    (hpair_indep : IndepFun (fun ω => (X ω, Z_X ω)) (fun ω => (Y ω, Z_Y ω)) P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hmomX : Integrable (fun ω => (X ω) ^ 2) P)
    (hmomY : Integrable (fun ω => (Y ω) ^ 2) P)
    (h_reg_X : EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_reg_sum : EPIStamDischarge.IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) Z P) :
    ∀ (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ),
      0 < fisherInfoOfDensityReal ((h_reg_X.reg_at σ hσ).density_t) ∧
      0 < fisherInfoOfDensityReal ((h_reg_Y.reg_at τ hτ).density_t) ∧
      0 < fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (σ + τ) (add_pos hσ hτ)).density_t) ∧
      1 / fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (σ + τ) (add_pos hσ hτ)).density_t)
        ≥ 1 / fisherInfoOfDensityReal ((h_reg_X.reg_at σ hσ).density_t)
          + 1 / fisherInfoOfDensityReal ((h_reg_Y.reg_at τ hτ).density_t) := by
  intro σ τ hσ hτ
  have hστ : 0 < σ + τ := add_pos hσ hτ
  -- ===== regular structures at the three matched times =====
  set RX := h_reg_X.reg_at σ hσ with hRX
  set RY := h_reg_Y.reg_at τ hτ with hRY
  set RS := h_reg_sum.reg_at (σ + τ) hστ with hRS
  -- input densities (producers' internal `pX`/`pY`/`pXY`)
  set pX : ℝ → ℝ := RX.pX with hpX_def
  set pY : ℝ → ℝ := RY.pX with hpY_def
  set pXY : ℝ → ℝ := RS.pX with hpXY_def
  -- density_t pins (pointwise) to `convDensityAdd p g_·`
  have hpinX : RX.density_t = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩) := by
    funext x; exact RX.density_t_eq hσ x
  have hpinY : RY.density_t = convDensityAdd pY (gaussianPDFReal 0 ⟨τ, hτ.le⟩) := by
    funext x; exact RY.density_t_eq hτ x
  have hpinS : RS.density_t
      = convDensityAdd pXY (gaussianPDFReal 0 ⟨σ + τ, hστ.le⟩) := by
    funext x; exact RS.density_t_eq hστ x
  -- input-density regularity from the V2 structure fields
  have hpX_nn : ∀ x, 0 ≤ pX x := RX.pX_nn
  have hpX_meas : Measurable pX := RX.pX_meas
  have hpY_nn : ∀ x, 0 ≤ pY x := RY.pX_nn
  have hpY_meas : Measurable pY := RY.pX_meas
  have hpXY_nn : ∀ x, 0 ≤ pXY x := RS.pX_nn
  have hpXY_meas : Measurable pXY := RS.pX_meas
  -- input-density integrability + mass from the `pX_law` (probability-density normalization)
  obtain ⟨hpX_int, hpX_norm⟩ := density_int_mass X pX hX hpX_nn hpX_meas RX.pX_law
  obtain ⟨hpY_int, hpY_norm⟩ := density_int_mass Y pY hY hpY_nn hpY_meas RY.pX_law
  obtain ⟨hpXY_int, hpXY_norm⟩ :=
    density_int_mass (fun ω => X ω + Y ω) pXY (hX.add hY) hpXY_nn hpXY_meas RS.pX_law
  have hpX_mass : (0 : ℝ) < ∫ x, pX x ∂volume := by rw [hpX_norm]; norm_num
  have hpY_mass : (0 : ℝ) < ∫ x, pY x ∂volume := by rw [hpY_norm]; norm_num
  have hpXY_mass : (0 : ℝ) < ∫ x, pXY x ∂volume := by rw [hpXY_norm]; norm_num
  -- ===== (1) three Fisher positivities (genuine, via convDensityAdd_pos producer) =====
  have hposX : 0 < fisherInfoOfDensityReal RX.density_t := by
    rw [hpinX]
    exact EPIConvDensityRegular.fisherInfoOfDensityReal_convDensityAdd_pos
      pX hσ hpX_nn hpX_meas hpX_int hpX_norm
  have hposY : 0 < fisherInfoOfDensityReal RY.density_t := by
    rw [hpinY]
    exact EPIConvDensityRegular.fisherInfoOfDensityReal_convDensityAdd_pos
      pY hτ hpY_nn hpY_meas hpY_int hpY_norm
  have hposS : 0 < fisherInfoOfDensityReal RS.density_t := by
    rw [hpinS]
    exact EPIConvDensityRegular.fisherInfoOfDensityReal_convDensityAdd_pos
      pXY hστ hpXY_nn hpXY_meas hpXY_int hpXY_norm
  refine ⟨hposX, hposY, hposS, ?_⟩
  -- ===== (2) the inverse-Stam inequality `1/J_S ≥ 1/J_X + 1/J_Y` =====
  -- the perturbed addends `A := X + √σ·Z_X`, `B := Y + √τ·Z_Y`
  set A : Ω → ℝ := fun ω => X ω + Real.sqrt σ * Z_X ω with hA_def
  set B : Ω → ℝ := fun ω => Y ω + Real.sqrt τ * Z_Y ω with hB_def
  have hA_meas : Measurable A := by fun_prop
  have hB_meas : Measurable B := by fun_prop
  -- independence `A ⊥ B` (adapt the EPIDensityForm `hStam_indep` block to σ ≠ τ)
  have hAB_indep : IndepFun A B P := by
    have hcombA : Measurable (fun q : ℝ × ℝ => q.1 + Real.sqrt σ * q.2) := by fun_prop
    have hcombB : Measurable (fun q : ℝ × ℝ => q.1 + Real.sqrt τ * q.2) := by fun_prop
    have := hpair_indep.comp hcombA hcombB
    simpa [Function.comp, A, B] using this
  -- genuine Stam hyp via step3
  have hStam : EPIStamDischarge.IsStamInequalityHyp A B P :=
    EPIStamStep3Body.isStamInequalityHyp_via_step3 P A B hA_meas hB_meas hAB_indep
  -- per-time regularity of the three `density_t`s (= conv-Gaussian densities)
  have hregX : IsRegularDensityV2 RX.density_t := by
    rw [hpinX]
    exact EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian
      pX hσ hpX_nn hpX_meas hpX_int hpX_mass
  have hregY : IsRegularDensityV2 RY.density_t := by
    rw [hpinY]
    exact EPIConvDensityRegular.isRegularDensityV2_convDensityAdd_gaussian
      pY hτ hpY_nn hpY_meas hpY_int hpY_mass
  have hnormX : (∫ x, RX.density_t x ∂volume) = 1 := by
    rw [hpinX]
    exact EPIConvDensity.integral_convDensityAdd_gaussian_eq_one pX hσ hpX_int hpX_norm
  have hnormY : (∫ x, RY.density_t x ∂volume) = 1 := by
    rw [hpinY]
    exact EPIConvDensity.integral_convDensityAdd_gaussian_eq_one pY hτ hpY_int hpY_norm
  have hready : EPIBlachmanDensity.IsBlachmanConvReady RX.density_t RY.density_t := by
    rw [hpinX, hpinY]
    exact isBlachmanConvReady_convDensityAdd_gaussian_asym pX pY hσ hτ
      hpX_nn hpX_meas hpX_int hpX_mass hpX_norm
      hpY_nn hpY_meas hpY_int hpY_mass hpY_norm
  -- the conv-pin gate `∀ x, RS.density_t x = convDensityAdd RX.density_t RY.density_t x`
  have hconv : ∀ x, RS.density_t x = convDensityAdd RX.density_t RY.density_t x := by
    -- `∫⁻ ofReal(p) = total mass = 1` from each `withDensity` probability law.
    have lmass : ∀ (W : Ω → ℝ) (p : ℝ → ℝ), Measurable W → (∀ x, 0 ≤ p x) →
        P.map W = volume.withDensity (fun x => ENNReal.ofReal (p x)) →
        (∫⁻ x, ENNReal.ofReal (p x) ∂volume) = 1 := by
      intro W p hW _ hp_law
      have hprob : IsProbabilityMeasure (P.map W) :=
        MeasureTheory.Measure.isProbabilityMeasure_map hW.aemeasurable
      have := hprob.measure_univ
      rw [hp_law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
      exact this
    have hpX_lmass := lmass X pX hX hpX_nn RX.pX_law
    have hpY_lmass := lmass Y pY hY hpY_nn RY.pX_law
    have hpXY_lmass : (∫⁻ x, ENNReal.ofReal (pXY x) ∂volume) ≠ ⊤ := by
      rw [lmass (fun ω => X ω + Y ω) pXY (hX.add hY) hpXY_nn RS.pX_law]; exact ENNReal.one_ne_top
    -- the input identity `pXY =ᵐ convDensityAdd pX pY` (the seam)
    have hseam : pXY =ᵐ[volume] convDensityAdd pX pY :=
      indepSum_density_ae X Y hX hY hXY pX pY pXY hpX_nn hpX_meas hpY_nn hpY_meas
        RX.pX_law RY.pX_law RS.pX_law hpXY_nn hpXY_meas hpX_int hpY_int
        hpXY_lmass hpX_lmass hpY_lmass
    -- the asym 4-fold interchange: RHS = convDensityAdd (convDensityAdd pX pY) g_{σ+τ}
    have hinterchange :
        convDensityAdd (convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))
            (convDensityAdd pY (gaussianPDFReal 0 ⟨τ, hτ.le⟩))
          = convDensityAdd (convDensityAdd pX pY)
              (gaussianPDFReal 0 ⟨σ + τ, by positivity⟩) :=
      EPIConvDensity.convDensityAdd_convGaussian_interchange_asym pX pY hσ hτ
        hpX_nn hpX_meas hpX_int hpY_nn hpY_meas hpY_int
    -- a.e.-invariance of `convDensityAdd · g` under a.e.-modification of the first arg
    have hgconv : ∀ z,
        convDensityAdd pXY (gaussianPDFReal 0 ⟨σ + τ, by positivity⟩) z
          = convDensityAdd (convDensityAdd pX pY)
              (gaussianPDFReal 0 ⟨σ + τ, by positivity⟩) z := by
      intro z
      show (∫ y, pXY y * _ ∂volume) = ∫ y, convDensityAdd pX pY y * _ ∂volume
      refine integral_congr_ae ?_
      filter_upwards [hseam] with y hy
      rw [hy]
    intro x
    rw [hpinS, hpinX, hpinY, hinterchange, hgconv x]
  -- instantiate the Stam hyp at the three `density_t`s; the J-gates close definitionally.
  have hJX : 0 < fisherInfoOfDensityReal RX.density_t := hposX
  have hJY : 0 < fisherInfoOfDensityReal RY.density_t := hposY
  have hJS : 0 < fisherInfoOfDensityReal RS.density_t := hposS
  have hgateX :
      fisherInfoOfDensityReal RX.density_t
        = (fisherInfoOfMeasureV2 (P.map A) RX.density_t).toReal := by
    simp only [fisherInfoOfMeasureV2_def, fisherInfoOfDensityReal]
  have hgateY :
      fisherInfoOfDensityReal RY.density_t
        = (fisherInfoOfMeasureV2 (P.map B) RY.density_t).toReal := by
    simp only [fisherInfoOfMeasureV2_def, fisherInfoOfDensityReal]
  have hgateS :
      fisherInfoOfDensityReal RS.density_t
        = (fisherInfoOfMeasureV2 (P.map (fun ω => A ω + B ω)) RS.density_t).toReal := by
    simp only [fisherInfoOfMeasureV2_def, fisherInfoOfDensityReal]
  exact hStam _ _ _ RX.density_t RY.density_t RS.density_t hJX hJY hJS
    hgateX hgateY hgateS hregX hregY hnormX hnormY hconv hready

end InformationTheory.Shannon.EPIStamSupplyTwoTime
