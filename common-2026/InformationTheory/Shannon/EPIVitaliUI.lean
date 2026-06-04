import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Distributions.Gaussian.Real
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensityAssoc
import InformationTheory.Shannon.EPIConvDensityNormalization
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIVitaliUnifTight
import InformationTheory.Shannon.FisherInfoV2DeBruijnAssembly

/-!
# EPI G2 Vitali witness — UnifIntegrable (UI), standalone genuine attempt

Genuine standalone implementation of the `hui` input for the layer-2 Vitali
machinery (`differentialEntropy_convDensity_integral_tendsto`). The main lemma
`negMulLog_convDensity_unifIntegrable` has the *same signature* as the parked
`EPIG2HeatFlowContinuity.negMulLog_convDensity_unifIntegrable` (`:165`) plus an
added probability-mass normalization precondition `hpX_mass : ∫ pX = 1` (a
regularity precondition supplied by the layer-2 consumer). The orchestrator will
delegate the parked version to this file (removing the EPIG2 copy).

## Strategy (inventory `epi-g2-ui-bridge-inventory.md`, 4 steps)

`f_n := convDensityAdd pX g_{u n} = pX ∗ g_{u n}`.

* **Step 1** (Mathlib in): `unifIntegrable_of` reduces UI to a *uniform* indicator-tail
  estimate `∀ ε>0, ∃ C, ∀ n, eLpNorm ({C ≤ |negMulLog (f_n)|}.indicator (negMulLog∘f_n)) 1 volume ≤ ofReal ε`.
* **Step 2** (probability-measure framing, genuine, option b = `withDensity` direct):
  `μ_n := volume.withDensity (ofReal∘f_n)` is a probability measure (`∫ f_n = 1` via
  `integral_convDensityAdd_gaussian_eq_one`), `≪ volume`, and `rnDeriv = ofReal∘f_n`.
  Hence `differentialEntropy μ_n = ∫ negMulLog f_n`.
* **Step 3** (maxent upper bound, in-tree `@entry_point`):
  `differentialEntropy_le_gaussian_of_variance_le` applied to `μ_n` gives
  `∫ negMulLog f_n ≤ (1/2) log(2πe V_n)` with `V_n = (∫ x² pX) + u n` `n`-uniform.
  Combined with `negMulLog_le_one_sub_self` (positive part) this gives a uniform
  bound `M` on `∫ |negMulLog f_n|`.
* **Step 4** (★ de la Vallée-Poussin bridge core, Mathlib-absent): "`∫|negMulLog f_n|`
  uniformly bounded → `∫⁻_{C≤|negMulLog f_n|}|negMulLog f_n| ≤ ε` uniformly (C large)".
  This is the genuine de la Vallée-Poussin content (superlinear moment) which has no
  Mathlib lemma. **Parked** as `wall:approx-identity-L1`; Steps 1-3 are genuine.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-! ## Genuine framing helpers (Steps 2-3) -/

/-- Measurability of `f_t = convDensityAdd pX g_t`. Genuine. -/
theorem convDensityAdd_gaussian_measurable {pX : ℝ → ℝ} (hpX_meas : Measurable pX)
    {t : ℝ} (ht : 0 < t) :
    Measurable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) :=
  convDensityAdd_pXpY_measurable pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_meas
    (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)

/-- Nonnegativity of `f_t = convDensityAdd pX g_t`. Genuine. -/
theorem convDensityAdd_gaussian_nonneg {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x :=
  convDensityAdd_pXpY_nonneg pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_nn
    (fun y => gaussianPDFReal_nonneg 0 ⟨t, ht.le⟩ y) x

/-- The smoothed-density measure `μ_t := volume.withDensity (ofReal ∘ f_t)` is a
probability measure (Step 2). Genuine via `integral_convDensityAdd_gaussian_eq_one`. -/
theorem convDensityAdd_gaussian_isProbabilityMeasure {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure
      (volume.withDensity (fun x =>
        ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x))) := by
  set f : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hf_def
  have hf_int : Integrable f volume :=
    convDensityAdd_pXpY_integrable pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_int hpX_meas
      (integrable_gaussianPDFReal 0 ⟨t, ht.le⟩) (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)
  have hf_nn : ∀ x, 0 ≤ f x := fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hf_mass : ∫ x, f x ∂volume = 1 :=
    integral_convDensityAdd_gaussian_eq_one pX ht hpX_int hpX_mass
  have hf_meas : Measurable f := convDensityAdd_gaussian_measurable hpX_meas ht
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int (Eventually.of_forall hf_nn)]
  rw [hf_mass]
  simp

/-- The differential entropy of the smoothed-density measure equals the entropy
integral of the density (Step 2). Genuine via `rnDeriv_withDensity`. -/
theorem differentialEntropy_convDensityAdd_gaussian_eq {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    {t : ℝ} (ht : 0 < t) :
    differentialEntropy
        (volume.withDensity (fun x =>
          ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)))
      = ∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) ∂volume := by
  set f : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hf_def
  have hf_meas : Measurable f := convDensityAdd_gaussian_measurable hpX_meas ht
  have hf_nn : ∀ x, 0 ≤ f x := fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hofReal_meas : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf_meas
  have hrn : (volume.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv volume
      =ᵐ[volume] fun x => ENNReal.ofReal (f x) :=
    Measure.rnDeriv_withDensity volume hofReal_meas
  rw [differentialEntropy]
  refine integral_congr_ae ?_
  filter_upwards [hrn] with x hx
  rw [hx, ENNReal.toReal_ofReal (hf_nn x)]

/-- **Second-moment integrability of `f_t` (helper, in-tree absent).**
`x ↦ x² · f_t(x)` is `volume`-integrable. Same Tonelli/measurability plumbing scope as
`convDensityAdd_second_moment` (value version). Parked for the closure plan.

@residual(plan:epi-g2-vitali-closure-plan) -/
theorem convDensityAdd_gaussian_sq_integrable {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  sorry

/-- **First-moment integrability of `f_t` (helper, in-tree absent).**
`x ↦ x · f_t(x)` is `volume`-integrable. Same Tonelli/measurability plumbing scope as
`convDensityAdd_second_moment` (value version). Parked for the closure plan.

@residual(plan:epi-g2-vitali-closure-plan) -/
theorem convDensityAdd_gaussian_id_integrable {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => x * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume := by
  sorry

/-- **Maxent upper bound (Step 3).** The entropy integral `∫ negMulLog f_t` is bounded
above by the Gaussian max-entropy `(1/2) log(2πe·V)` with `V = (∫ x² pX) + t`. Genuine
via `differentialEntropy_le_gaussian_of_variance_le` on `μ_t`. The variance moments are
supplied by `convDensityAdd_second_moment` (value) and the moment-integrability helpers
(parked); the maxent application itself is a genuine reduction. -/
theorem negMulLog_convDensityAdd_gaussian_entropy_upper {pX : ℝ → ℝ}
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t)
    {V : ℝ≥0} (hV : (∫ x, x ^ 2 * pX x ∂volume) + t ≤ (V : ℝ)) (hV0 : V ≠ 0) :
    (∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) ∂volume)
      ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * V) := by
  classical
  -- Establish all facts about the convolution density `f` and the framing measure `μ`
  -- *before* making them opaque, then `clear_value` to stop downstream tactics
  -- (`measure_univ`, `integral_const`, typeclass search) from unfolding `μ`/`f` to the
  -- convolution density (which blows up `isDefEq`). The defining equations
  -- `hf_def`/`hμ_def` remain available as ordinary hypotheses.
  have hf_nn : ∀ x, 0 ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x :=
    fun x => convDensityAdd_gaussian_nonneg hpX_nn ht x
  have hf_meas : Measurable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) :=
    convDensityAdd_gaussian_measurable hpX_meas ht
  have hf_int : Integrable (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) volume :=
    convDensityAdd_pXpY_integrable pX (gaussianPDFReal 0 ⟨t, ht.le⟩) hpX_int hpX_meas
      (integrable_gaussianPDFReal 0 ⟨t, ht.le⟩) (measurable_gaussianPDFReal 0 ⟨t, ht.le⟩)
  have hf_mass : ∫ x, convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume = 1 :=
    integral_convDensityAdd_gaussian_eq_one pX ht hpX_int hpX_mass
  set f : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) with hf_def
  set μ : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (f x)) with hμ_def
  haveI hμ_prob : IsProbabilityMeasure μ := by
    rw [hμ_def, hf_def]
    exact convDensityAdd_gaussian_isProbabilityMeasure hpX_nn hpX_meas hpX_int hpX_mass ht
  have hμ_ac : μ ≪ volume := withDensity_absolutelyContinuous volume _
  have hofReal_lt : ∀ᵐ x ∂volume, ENNReal.ofReal (f x) < ∞ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  clear_value μ f
  -- `∫ g ∂μ = ∫ f · g ∂volume` for any `g`.
  have htransfer : ∀ g : ℝ → ℝ, ∫ x, g x ∂μ = ∫ x, f x * g x ∂volume := by
    intro g
    have hstep : ∫ x, g x ∂μ
        = ∫ x, (ENNReal.ofReal (f x)).toReal • g x ∂volume := by
      rw [hμ_def]
      exact integral_withDensity_eq_integral_toReal_smul
        (ENNReal.measurable_ofReal.comp hf_meas) hofReal_lt g
    rw [hstep]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul]
  -- Moments transferred to `volume`.
  set m : ℝ := ∫ x, x ∂μ with hm_def
  have hsq_int : Integrable (fun x => x ^ 2 * f x) volume := by
    rw [hf_def]; exact convDensityAdd_gaussian_sq_integrable hpX_nn hpX_meas hpX_int hpX_mom ht
  have hid_int : Integrable (fun x => x * f x) volume := by
    rw [hf_def]; exact convDensityAdd_gaussian_id_integrable hpX_nn hpX_meas hpX_int hpX_mom ht
  have hsq_val : ∫ x, x ^ 2 * f x ∂volume = (∫ x, x ^ 2 * pX x ∂volume) + t := by
    have h := convDensityAdd_second_moment hpX_nn hpX_meas hpX_int hpX_mom ht
    rw [hf_def, h, hpX_mass]; ring
  -- `∫ x ∂μ = m` (definition).
  have h_mean : ∫ x, x ∂μ = m := rfl
  -- `∫ x² ∂μ = ∫ x² f`.
  have hsqμ : ∫ x, x ^ 2 ∂μ = (∫ x, x ^ 2 * pX x ∂volume) + t := by
    rw [htransfer (fun x => x ^ 2)]
    simp only [mul_comm (f _)]
    rw [hsq_val]
  -- `∫ x ∂μ = ∫ x f`, integrable transfer for variance expansion.
  have hidμ_eq : ∫ x, x ∂μ = ∫ x, x * f x ∂volume := by
    rw [htransfer (fun x => x)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_); ring
  -- Variance ≤ second moment: `∫ (x-m)² ∂μ = ∫ x² ∂μ - m² ≤ ∫ x² ∂μ`.
  -- Integrability of `x ↦ (x - m)²` wrt `μ`.
  have hvar_int_vol : Integrable (fun x => f x * (x - m) ^ 2) volume := by
    have hexp : ∀ x, f x * (x - m) ^ 2
        = (x ^ 2 * f x) - (2 * m) * (x * f x) + (m ^ 2) * f x := by
      intro x; ring
    rw [integrable_congr (Eventually.of_forall hexp)]
    exact (hsq_int.sub (hid_int.const_mul (2 * m))).add (hf_int.const_mul (m ^ 2))
  have hvar_int : Integrable (fun x => (x - m) ^ 2) μ := by
    have hiff := integrable_withDensity_iff_integrable_smul₀'
      (μ := volume) (f := fun x => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp hf_meas).aemeasurable hofReal_lt (g := fun x => (x - m) ^ 2)
    rw [hμ_def]
    refine hiff.mpr (hvar_int_vol.congr (Eventually.of_forall fun x => ?_))
    simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul]
  -- Variance bound.
  have h_var : ∫ x, (x - m) ^ 2 ∂μ ≤ (V : ℝ) := by
    have hvar_eq : ∫ x, (x - m) ^ 2 ∂μ = (∫ x, x ^ 2 ∂μ) - m ^ 2 := by
      have hxsq_int : Integrable (fun x => x ^ 2) μ := by
        have hiff := integrable_withDensity_iff_integrable_smul₀'
          (μ := volume) (f := fun x => ENNReal.ofReal (f x))
          (ENNReal.measurable_ofReal.comp hf_meas).aemeasurable hofReal_lt (g := fun x => x ^ 2)
        rw [hμ_def]
        refine hiff.mpr ((hsq_int).congr (Eventually.of_forall fun x => ?_))
        simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul, mul_comm]
      have hx_int : Integrable (fun x => x) μ := by
        have hiff := integrable_withDensity_iff_integrable_smul₀'
          (μ := volume) (f := fun x => ENNReal.ofReal (f x))
          (ENNReal.measurable_ofReal.comp hf_meas).aemeasurable hofReal_lt (g := fun x => x)
        rw [hμ_def]
        refine hiff.mpr ((hid_int).congr (Eventually.of_forall fun x => ?_))
        simp only [ENNReal.toReal_ofReal (hf_nn x), smul_eq_mul, mul_comm]
      have hexpand : ∀ x : ℝ, (x - m) ^ 2 = (x ^ 2 - (2 * m) * x) + m ^ 2 := by
        intro x; ring
      calc ∫ x, (x - m) ^ 2 ∂μ
          = ∫ x, (fun x => x ^ 2 - (2 * m) * x) x + (fun _ => m ^ 2) x ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_); simpa using hexpand x
        _ = (∫ x, (x ^ 2 - (2 * m) * x) ∂μ) + ∫ _, m ^ 2 ∂μ :=
            integral_add ((hxsq_int).sub (hx_int.const_mul (2 * m))) (integrable_const _)
        _ = ((∫ x, x ^ 2 ∂μ) - ∫ x, (2 * m) * x ∂μ) + ∫ _, m ^ 2 ∂μ := by
            rw [integral_sub hxsq_int (hx_int.const_mul (2 * m))]
        _ = ((∫ x, x ^ 2 ∂μ) - (2 * m) * (∫ x, x ∂μ)) + m ^ 2 := by
            rw [integral_const_mul, integral_const, probReal_univ]
            simp only [smul_eq_mul, one_mul]
        _ = (∫ x, x ^ 2 ∂μ) - m ^ 2 := by
            rw [← h_mean, ← hm_def]; ring
    rw [hvar_eq, hsqμ]
    have hm_sq_nonneg : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
    linarith [hV]
  -- `h_ent_int`: integrability of the entropy integrand.
  have h_ent_int : Integrable
      (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
    have hrn : (μ.rnDeriv volume) =ᵐ[volume] fun x => ENNReal.ofReal (f x) := by
      rw [hμ_def]; exact Measure.rnDeriv_withDensity volume (ENNReal.measurable_ofReal.comp hf_meas)
    have hbase : Integrable (fun x => Real.negMulLog (f x)) volume := by
      rw [hf_def]
      exact InformationTheory.Shannon.FisherInfoV2.convDensityAdd_negMulLog_integrable
        pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht
    refine hbase.congr ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (hf_nn x)]
  -- Apply maxent.
  have hmaxent := differentialEntropy_le_gaussian_of_variance_le
    (μ := μ) hμ_ac m hV0 h_mean h_var hvar_int h_ent_int
  -- Rewrite `differentialEntropy μ = ∫ negMulLog f`.
  have hent_eq : differentialEntropy μ
      = ∫ x, Real.negMulLog (f x) ∂volume := by
    rw [hμ_def, hf_def]
    exact differentialEntropy_convDensityAdd_gaussian_eq hpX_nn hpX_meas ht
  rw [hent_eq, hf_def] at hmaxent
  rw [hf_def]
  exact hmaxent

/-! ## de la Vallée-Poussin bridge core (Step 4, parked) -/

/-- **de la Vallée-Poussin bridge core (Step 4, ★ Mathlib-absent).**
The uniform indicator-tail input required by `unifIntegrable_of`: for every `ε > 0`,
there is a threshold `C` such that the tail eLpNorm of `negMulLog (f_n)` above `C` is
`≤ ε` uniformly in `n`. The maxent upper bound (Step 3) controls `∫ negMulLog f_n`
uniformly, but the de la Vallée-Poussin step — turning a uniform bound on
`∫ |negMulLog f_n|` into a uniform tail `∫⁻_{C ≤ |negMulLog f_n|} |negMulLog f_n| → 0`
— requires a superlinear-moment argument absent from Mathlib (inventory category B,
loogle: 0 hits for any de la Vallée-Poussin / superlinear-moment → UnifIntegrable
lemma). Parked as the approximate-identity wall.

@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_indicatorTail_uniform
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        ({ x | C ≤ ‖Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)‖₊ }.indicator
          (fun x => Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)))
        1 volume ≤ ENNReal.ofReal ε := by
  sorry

/-! ## Main UI witness (Step 1, genuine reduction to Step 4) -/

/-- **Layer 2 UI witness.** Uniform integrability of the entropy integrands along any
sequence `u : ℕ → ℝ` with `u n > 0` and bounded range. Vitali input `hui`.

Same signature as `EPIG2HeatFlowContinuity.negMulLog_convDensity_unifIntegrable`
(`:165`) plus the probability-mass normalization precondition `hpX_mass : ∫ pX = 1`
(regularity, supplied by the layer-2 consumer). The genuine reduction (`unifIntegrable_of`,
`[IsFiniteMeasure]`-free) delegates the uniform indicator-tail input to the parked de
la Vallée-Poussin bridge core `negMulLog_convDensity_indicatorTail_uniform`
(`wall:approx-identity-L1`). The framing/maxent helpers (Steps 2-3) are genuine.

NOT load-bearing: this body is the genuine Step-1 reduction. Its only own residual is
transitive, through the parked de la Vallée-Poussin bridge core
(`wall:approx-identity-L1`); the framing/maxent helpers (Steps 2-3) are genuine modulo
the parked moment-integrability plumbing (`plan:epi-g2-vitali-closure-plan`). -/
theorem negMulLog_convDensity_unifIntegrable
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) :
    UnifIntegrable
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume := by
  -- Step 1: reduce UnifIntegrable to the uniform indicator-tail estimate via
  -- `unifIntegrable_of` (`[IsFiniteMeasure]`-free, so usable on `volume`).
  refine unifIntegrable_of (le_refl 1) ENNReal.one_ne_top (fun n => ?_) (fun ε hε => ?_)
  · -- AEStronglyMeasurable of `negMulLog ∘ f_n`.
    refine Real.continuous_negMulLog.comp_aestronglyMeasurable ?_
    exact (convDensityAdd_gaussian_measurable hpX_meas (hu_pos n)).aestronglyMeasurable
  · -- The uniform indicator-tail input is the parked de la Vallée-Poussin bridge core.
    exact negMulLog_convDensity_indicatorTail_uniform hpX_nn hpX_meas hpX_int hpX_mass
      hpX_mom u hu_pos hu_bdd hε

end InformationTheory.Shannon
