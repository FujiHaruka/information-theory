import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.FisherInfo.OfDensity

/-!
# Convolution density gateway — `pX` integrable-only + Gaussian-kernel-smooth variant

`convDensityAdd_hasDerivAt_of_integrable_smoothKernel` is the `fX`-integrable-only
variant of `convDensityAdd_hasDerivAt_of_regular`
(`InformationTheory/Shannon/EPI/Conv/Density.lean`). The smoothness regularity on `fX`
is dropped: differentiation is carried entirely by the Gaussian kernel `fY`
(`hregY : IsRegularDensityV2 fY` + bounded `fY` / `deriv fY`). `fX` only needs
`Integrable fX volume`, used for `aestronglyMeasurable` (via
`Integrable.aestronglyMeasurable`) and the bound integrability.

This is the common foundation for the A-5 producer group: an arbitrary input
density `pX` (no smoothness) convolved with the Gaussian heat kernel.

All hypotheses are honest regularity preconditions (integrability / boundedness);
the differentiability conclusion is *derived* via the `@audit:ok` gateway
`convDensityAdd_hasDerivAt`, NOT assumed (no load-bearing bundling).
-/

namespace InformationTheory.Shannon.EPIConvDensityGaussianGateway

open MeasureTheory Real
open InformationTheory.Shannon.EPIConvDensity

/-- **`pX` integrable-only variant of `convDensityAdd_hasDerivAt_of_regular`.**
`fX` smoothness is dropped; the derivative is carried by the Gaussian kernel `fY`.
`fX` enters only through `Integrable fX volume` (ae-measurability + bound
integrability). All hyps are regularity preconditions; the differentiability is
derived via the gateway, not assumed.
@audit:ok -/
theorem convDensityAdd_hasDerivAt_of_integrable_smoothKernel (fX fY : ℝ → ℝ) (z₀ : ℝ)
    (hX_int : Integrable fX volume)
    (hregY : InformationTheory.Shannon.FisherInfo.IsRegularDensityV2 fY)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M)
    (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M) :
    HasDerivAt (InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY)
      (∫ x, InformationTheory.Shannon.EPIConvDensity.convDensityAddDeriv fX fY z₀ x ∂volume)
      z₀ := by
  obtain ⟨MY, hMY⟩ := hY_bdd
  obtain ⟨MY', hMY'⟩ := hY'_bdd
  -- Continuity / measurability facts (only `fY`-side; `fX` uses integrability).
  have hY_cont : Continuous fY := hregY.diff.continuous
  have hY'_meas : Measurable (deriv fY) := measurable_deriv fY
  -- `s := Metric.ball z₀ 1`, a neighborhood of `z₀`.
  set s : Set ℝ := Metric.ball z₀ 1 with hs_def
  -- (1) `hs : s ∈ nhds z₀`.
  have hs : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  -- (2) `hF_meas`.
  have hF_meas : ∀ᶠ z in nhds z₀,
      AEStronglyMeasurable (fun x => fX x * fY (z - x)) volume := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    exact (hX_int.aestronglyMeasurable).mul
      ((hY_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  -- (3) `hF_int : Integrable (fun x => fX x * fY (z₀ - x))`.
  have hF_int : Integrable (fun x => fX x * fY (z₀ - x)) volume := by
    have hYmeas : AEStronglyMeasurable (fun x => fY (z₀ - x)) volume :=
      (hY_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂volume, ‖fY (z₀ - x)‖ ≤ MY :=
      Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact hMY (z₀ - x))
    have := hX_int.bdd_mul hYmeas hbound
    -- `this : Integrable (fun x => fY (z₀ - x) * fX x)`
    simpa only [mul_comm] using this
  -- (4) `hF'_meas`.
  have hF'_meas : AEStronglyMeasurable
      (fun x => convDensityAddDeriv fX fY z₀ x) volume := by
    unfold convDensityAddDeriv
    exact (hX_int.aestronglyMeasurable).mul
      ((hY'_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  -- bound function `bound x := MY' * |fX x|`.
  set bound : ℝ → ℝ := fun x => MY' * |fX x| with hbound_def
  -- (5) `h_bound`.
  have h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s,
      ‖convDensityAddDeriv fX fY z x‖ ≤ bound x := by
    refine Filter.Eventually.of_forall (fun x z _ => ?_)
    unfold convDensityAddDeriv
    rw [Real.norm_eq_abs, abs_mul, hbound_def]
    have : |deriv fY (z - x)| ≤ MY' := hMY' (z - x)
    calc |fX x| * |deriv fY (z - x)|
        ≤ |fX x| * MY' := by
          gcongr
      _ = MY' * |fX x| := mul_comm _ _
  -- (6) `bound_integrable`.
  have bound_integrable : Integrable bound volume := by
    rw [hbound_def]
    exact (hX_int.abs).const_mul MY'
  -- (7) `h_diff`.
  have h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s,
      HasDerivAt (fun z => fX x * fY (z - x))
        (convDensityAddDeriv fX fY z x) z := by
    refine Filter.Eventually.of_forall (fun x z _ => ?_)
    unfold convDensityAddDeriv
    -- inner: `z ↦ z - x` has derivative `1`.
    have hinner : HasDerivAt (fun z : ℝ => z - x) 1 z :=
      (hasDerivAt_id z).sub_const x
    -- `fY` differentiable at `z - x`.
    have hY_at : HasDerivAt fY (deriv fY (z - x)) (z - x) :=
      (hregY.diff (z - x)).hasDerivAt
    -- compose: `z ↦ fY (z - x)` has derivative `deriv fY (z-x) * 1`.
    have hcomp : HasDerivAt (fun z : ℝ => fY (z - x)) (deriv fY (z - x) * 1) z :=
      hY_at.comp z hinner
    rw [mul_one] at hcomp
    -- const_mul by `fX x`.
    have := hcomp.const_mul (fX x)
    -- `this : HasDerivAt (fun z => fX x * fY (z - x)) (fX x * deriv fY (z - x)) z`
    exact this
  exact convDensityAdd_hasDerivAt fX fY z₀ hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff

/-- **Differentiable corollary** of `convDensityAdd_hasDerivAt_of_integrable_smoothKernel`,
for the `diff` field of downstream regular-density witnesses.
@audit:ok -/
theorem convDensityAdd_differentiable_of_integrable_smoothKernel (fX fY : ℝ → ℝ)
    (hX_int : Integrable fX volume)
    (hregY : InformationTheory.Shannon.FisherInfo.IsRegularDensityV2 fY)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M)
    (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M) :
    Differentiable ℝ (InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY) :=
  fun z₀ =>
    (convDensityAdd_hasDerivAt_of_integrable_smoothKernel fX fY z₀ hX_int hregY hY_bdd
      hY'_bdd).differentiableAt

end InformationTheory.Shannon.EPIConvDensityGaussianGateway
