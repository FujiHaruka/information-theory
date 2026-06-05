import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfoV2DeBruijnAssembly
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone

/-!
# EPI G2 — (β) density-only lower bound

This file packages the genuine Ω-level (β) lower bound
`negMulLog_convDensity_entropy_ge` (`EPIG2ConvEntropyMonotone.lean`) into a
**density-only** wrapper: given just a probability density `pX` (plus minimal
regularity), no abstract independent pair is required.

  `∫ negMulLog pX ≤ ∫ negMulLog (pX ∗ g_{u n})`.

The Ω-level theorem requires an independent pair `X ⊥ Z` (with `Z ∼ 𝒩(0, v_Z)`) on
some probability space together with 8 per-`n` regularity/integrability preconditions.
We **instantiate the canonical product space** `Ω := ℝ × ℝ`,
`μ := (volume.withDensity (ofReal ∘ pX)).prod (gaussianReal 0 v_Z)`,
`X := Prod.fst`, `Z := Prod.snd`. Then `X ⊥ Z` (product independence),
`μ.map X = withDensity pX`, `μ.map Z = gaussianReal 0 v_Z`, and the 8 preconditions are
discharged here (or honestly parked).

## Status — type-check done (1 sorry / 1 residual)

Of the 8 per-`n` preconditions of the Ω-level (β) lower bound, **7 are discharged
genuinely** here from the canonical construction:

* per-fibre absolute continuity, `p log p` integrability, fibre-entropy integrability
  (translation invariance: each fibre is a translate `pX(· − √s·z)` of `μ.map X`);
* joint absolute continuity (per-fibre `≪ volume ≪ μ.map W`, the marginal having a
  strictly positive density);
* the **two cross terms** (per-fibre (5) + outer (7)): now genuinely closed via the
  `s`-uniform polynomial majorant `|log p_t| ≤ A + B·x²`
  (`convDensityAdd_logFactor_poly_majorant`, made public in
  `FisherInfoV2DeBruijnAssembly`) integrated against `pX`'s translate moments
  (helpers `hLog` / `hfib_eq` / `hfib_dom_int` in the proof body);
* marginal log-density integrability (`∫ negMulLog p_t < ∞`, the genuine
  `convDensityAdd_negMulLog_integrable`).

The **1 remaining precondition is parked** (`@residual(plan:...)`): the joint llr
integrability `h_int` (= KL finiteness `D(joint ‖ product) < ∞`). This is a separate
compProd / per-fibre chain-rule assembly (`rnDeriv_compProd_eq_kernel_rnDeriv` +
`rnDeriv_mul_rnDeriv` + the `llr` value identity `log((κ_z).rnDeriv (μ.map W)) =ᵐ[κ_z]
log q_z − log p_t`), reducing to the already-discharged fibre/outer integrabilities; it
is NOT blocked by the (former) private majorant. Closure plan:
`docs/shannon/epi-g2-general-sandwich-moonshot-plan.md` Phase 1.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Real

/-- Translation transport for fibre integrability: if `κ z = ν.map (· + c·z)` (with
`ν ≪ volume`), then `Integrable (fun x => Φ ((κ z).rnDeriv volume x).toReal) volume`
holds iff `Integrable (fun x => Φ (ν.rnDeriv volume x).toReal) volume`. -/
private theorem fibre_rnDeriv_integrable_iff
    (ν : Measure ℝ) [SigmaFinite ν] (c : ℝ) (Φ : ℝ → ℝ) :
    Integrable
      (fun x => Φ ((ν.map (fun y : ℝ => y + c)).rnDeriv volume x).toReal) volume
      ↔ Integrable (fun x => Φ ((ν.rnDeriv volume x).toReal)) volume := by
  have hf : MeasurableEmbedding (fun x : ℝ => x + c) := measurableEmbedding_addRight c
  have hvol : (volume : Measure ℝ).map (fun x : ℝ => x + c) = volume :=
    MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) c
  -- rnDeriv transport: `(ν.map f).rnDeriv volume (x+c) =ᵐ[volume] ν.rnDeriv volume x`.
  have h_rn := hf.rnDeriv_map ν (volume : Measure ℝ)
  rw [hvol] at h_rn
  constructor
  · intro h
    -- `H(x) := Φ((ν.map f).rnDeriv volume x).toReal`, integrable; pull back by `f`.
    have h2 : Integrable
        (fun x => Φ (((ν.map (fun y : ℝ => y + c)).rnDeriv volume (x + c)).toReal)) volume := by
      have := (hf.integrable_map_iff
        (g := fun x => Φ (((ν.map (fun y : ℝ => y + c)).rnDeriv volume x).toReal))).mp
        (by rw [hvol]; exact h)
      simpa [Function.comp] using this
    refine h2.congr ?_
    filter_upwards [h_rn] with x hx
    rw [hx]
  · intro h
    have h2 : Integrable
        (fun x => Φ (((ν.map (fun y : ℝ => y + c)).rnDeriv volume (x + c)).toReal)) volume := by
      refine h.congr ?_
      filter_upwards [h_rn] with x hx
      rw [hx]
    have := (hf.integrable_map_iff
      (g := fun x => Φ (((ν.map (fun y : ℝ => y + c)).rnDeriv volume x).toReal))).mpr
      (by simpa [Function.comp] using h2)
    rw [hvol] at this
    exact this

/-- **(β) density form, pX-only.** Convolution with a Gaussian does not decrease the
`negMulLog` entropy integral: `∫ negMulLog pX ≤ ∫ negMulLog (pX ∗ g_{u n})`.

`pX` is a probability density (non-negative, measurable, integrable, mass `1`) with a
finite second moment and integrable entropy integrand. `v_Z` is any fixed positive
variance for the auxiliary Gaussian; it does not appear in the conclusion.

Proved by instantiating the genuine Ω-level (β) lower bound
`negMulLog_convDensity_entropy_ge` on the canonical product space `ℝ × ℝ`. -/
theorem negMulLog_convDensity_entropy_ge_density
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume)
    {v_Z : ℝ≥0} (hv_Z_pos : 0 < v_Z)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (n : ℕ) :
    (∫ x, Real.negMulLog (pX x) ∂volume)
      ≤ ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume := by
  classical
  -- Canonical space `Ω := ℝ × ℝ` with `μ := (withDensity pX).prod (gaussianReal 0 v_Z)`.
  set νX : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (pX x)) with hνX
  set μ : Measure (ℝ × ℝ) := νX.prod (gaussianReal 0 v_Z) with hμ
  set X : ℝ × ℝ → ℝ := Prod.fst with hX_def
  set Z : ℝ × ℝ → ℝ := Prod.snd with hZ_def
  -- `νX` is a probability measure (mass `∫ pX = 1`).
  have hνX_prob : IsProbabilityMeasure νX := by
    constructor
    rw [hνX, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hpX_int (ae_of_all _ hpX_nn),
      hpX_mass, ENNReal.ofReal_one]
  haveI := hνX_prob
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  -- Measurability of the canonical coordinates.
  have hX : Measurable X := measurable_fst
  have hZ : Measurable Z := measurable_snd
  -- Marginal laws.
  have hX_law : μ.map X = νX := by
    rw [hμ, hX_def, Measure.map_fst_prod, measure_univ, one_smul]
  have hZ_law : μ.map Z = gaussianReal 0 v_Z := by
    rw [hμ, hZ_def, Measure.map_snd_prod, measure_univ, one_smul]
  have hpX_law : μ.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)) := by
    rw [hX_law, hνX]
  -- Independence of the canonical coordinates.
  have hXZ : IndepFun X Z μ := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable,
      hX_law, hZ_law]
    have hid : (fun ω => (X ω, Z ω)) = (id : ℝ × ℝ → ℝ × ℝ) := rfl
    rw [hid, Measure.map_id, hμ]
  -- Heat-flow time `s := u n / v_Z` (used only inside the preconditions).
  set s : ℝ := u n / (v_Z : ℝ) with hs_def
  have hv_Z_pos' : (0 : ℝ) < v_Z := hv_Z_pos
  have hs : 0 < s := div_pos (hu_pos n) hv_Z_pos'
  set W : ℝ × ℝ → ℝ := fun ω => X ω + Real.sqrt s * Z ω with hW_def
  -- `μ.map X ≪ volume` (a `withDensity`).
  have hX_ac : (μ.map X) ≪ volume := by
    rw [hpX_law]; exact withDensity_absolutelyContinuous _ _
  -- Fibre identification: `condDistrib W Z μ =ᵐ[μ.map Z] affineShiftKernel (μ.map X) (√s)`,
  -- where `affineShiftKernel ν c z = ν.map (· + c·z)`.  Mirrors the assembly inside
  -- `condDifferentialEntropy_indep_add_eq`.
  have hW_meas : Measurable W := hX.add ((measurable_const).mul hZ)
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hae : condDistrib W Z μ
      =ᵐ[μ.map Z] affineShiftKernel (μ.map X) (Real.sqrt s) := by
    have hZX : IndepFun Z X μ := hXZ.symm
    have hjoint_ZX : μ.map (fun ω => (Z ω, X ω)) = (μ.map Z).prod (μ.map X) :=
      (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hX.aemeasurable).mp hZX
    have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + Real.sqrt s * p.1) := by fun_prop
    have hjoint_ZW : μ.map (fun ω => (Z ω, W ω))
        = (μ.map Z) ⊗ₘ (affineShiftKernel (μ.map X) (Real.sqrt s)) := by
      have hcomp : (fun ω => (Z ω, W ω))
          = (fun p : ℝ × ℝ => (p.1, p.2 + Real.sqrt s * p.1)) ∘ (fun ω => (Z ω, X ω)) := by
        funext ω; simp [hW_def]
      rw [hcomp, ← Measure.map_map hg (hZ.prodMk hX), hjoint_ZX,
        prod_map_affine_eq_compProd]
    exact condDistrib_ae_eq_of_measure_eq_compProd Z hW_meas.aemeasurable hjoint_ZW
  -- Density of `μ.map X` is `pX` a.e.: `(μ.map X).rnDeriv volume x = ofReal (pX x)`.
  have hqX : (μ.map X).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (pX x) := by
    rw [hpX_law]
    exact Measure.rnDeriv_withDensity volume hpX_meas.ennreal_ofReal
  -- `s·v_Z = u n` so the convolution variance witness matches.
  have hsv : s * (v_Z : ℝ) = u n := by
    rw [hs_def, div_mul_cancel₀ _ hv_Z_pos'.ne']
  have hwit : (⟨s * (v_Z : ℝ), by positivity⟩ : ℝ≥0) = (⟨u n, (hu_pos n).le⟩ : ℝ≥0) := by
    apply NNReal.coe_injective; show s * (v_Z : ℝ) = u n; exact hsv
  set p_t : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) with hp_t_def
  -- Density of the marginal `μ.map W`: `(μ.map W).rnDeriv volume x = ofReal (p_t x)`.
  have hqW : (μ.map W).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (p_t x) := by
    have hpath : W = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s := rfl
    have hrn := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
      X Z hX hZ hXZ v_Z hv_Z_pos hZ_law pX hpX_nn hpX_meas hpX_law hs
    rw [hpath]
    filter_upwards [hrn] with x hx
    rw [hx, hp_t_def, hwit]
  -- Non-negativity / measurability of `p_t`.
  have hpX_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  have hp_t_nn : ∀ x, 0 ≤ p_t x := fun x =>
    (InformationTheory.Shannon.FisherInfoV2.convDensityAdd_pos
      pX hpX_nn hpX_int hpX_pos (hu_pos n) x).le
  have hp_t_meas : Measurable p_t := by
    rw [hp_t_def]
    have hg_pdf : Measurable (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) :=
      measurable_gaussianPDFReal 0 _
    have huncurry : StronglyMeasurable
        (Function.uncurry fun z x => pX x * gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩ (z - x)) := by
      apply Measurable.stronglyMeasurable
      apply (hpX_meas.comp measurable_snd).mul
      exact hg_pdf.comp ((measurable_fst).sub measurable_snd)
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [convDensityAdd] using h.measurable
  -- Marginal `μ.map W = withDensity (ofReal p_t)` and `volume ≪ μ.map W` (full support).
  have hW_ac : (μ.map W) ≪ volume := by
    have hW_law : μ.map W = (μ.map X) ∗ gaussianReal 0 ⟨s * (v_Z : ℝ), by positivity⟩ :=
      InformationTheory.Shannon.FisherInfoV2.gaussianConvolution_law_conv
        X Z hX hZ hXZ v_Z hZ_law hs.le
    have hsv_ne : (⟨s * (v_Z : ℝ), by positivity⟩ : ℝ≥0) ≠ 0 := by
      intro h; exact (mul_pos hs hv_Z_pos').ne' (congrArg NNReal.toReal h)
    rw [hW_law]
    exact Measure.conv_absolutelyContinuous
      (gaussianReal_absolutelyContinuous 0 hsv_ne)
  have hW_eq : μ.map W = volume.withDensity (fun x => ENNReal.ofReal (p_t x)) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq (μ.map W) volume hW_ac]
    exact withDensity_congr_ae hqW
  have vol_ac_W : volume ≪ μ.map W := by
    rw [hW_eq]
    refine withDensity_absolutelyContinuous' hp_t_meas.ennreal_ofReal.aemeasurable ?_
    exact ae_of_all _ (fun x => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact (InformationTheory.Shannon.FisherInfoV2.convDensityAdd_pos
        pX hpX_nn hpX_int hpX_pos (hu_pos n) x))
  -- ============ Shared analytic facts for the 3 coupled preconditions ============
  -- (A) `s`-uniform polynomial majorant for `|log p_t|`.  Take the majorant at `t := u n`,
  -- evaluated at the single point `s = u n ∈ Ioo (u n / 2, 2·u n)`:
  -- `‖-log p_t - 1‖ ≤ A + B·x²`, hence `|log p_t x| ≤ (A+1) + B·x²` for a.e. `x`.
  obtain ⟨A, B, hB_nn, hLog0⟩ :=
    InformationTheory.Shannon.FisherInfoV2.convDensityAdd_logFactor_poly_majorant
      pX hpX_nn hpX_meas hpX_int hpX_mass (hu_pos n)
  have hun_mem : u n ∈ Set.Ioo (u n / 2) (2 * u n) :=
    ⟨by linarith [hu_pos n], by linarith [hu_pos n]⟩
  have hLog : ∀ᵐ x ∂volume, |Real.log (p_t x)| ≤ (A + 1) + B * x ^ 2 := by
    filter_upwards [hLog0] with x hx
    have hb := hx (u n) hun_mem
    -- `p_t = convDensityAdd pX g_{u n}` (the majorant's witness at `s = u n`).
    have hpt_eq : convDensityAdd pX
        (gaussianPDFReal 0 ⟨u n, le_of_lt (by have := hun_mem.1; linarith : (0:ℝ) < u n)⟩) x
        = p_t x := by rw [hp_t_def]
    rw [hpt_eq, Real.norm_eq_abs] at hb
    have habs : |Real.log (p_t x)| ≤ |(- Real.log (p_t x) - 1)| + 1 := by
      calc |Real.log (p_t x)| = |(- Real.log (p_t x) - 1) + 1| := by
            rw [show (- Real.log (p_t x) - 1) + 1 = - Real.log (p_t x) by ring, abs_neg]
        _ ≤ |(- Real.log (p_t x) - 1)| + |(1:ℝ)| := abs_add_le _ _
        _ = |(- Real.log (p_t x) - 1)| + 1 := by norm_num
    linarith
  -- (B) fibre density a.e. equals the translate `pX(· − √s·z)`.
  have hfib_eq : ∀ᵐ z ∂(μ.map Z),
      (condDistrib W Z μ z).rnDeriv volume
        =ᵐ[volume] fun x => ENNReal.ofReal (pX (x - Real.sqrt s * z)) := by
    filter_upwards [hae] with z hz
    rw [hz, affineShiftKernel_apply]
    -- `((μ.map X).map (· + c)).rnDeriv volume x =ᵐ (μ.map X).rnDeriv volume (x − c) =ᵐ pX(x−c)`.
    set c : ℝ := Real.sqrt s * z with hc
    have hf : MeasurableEmbedding (fun x : ℝ => x + c) := measurableEmbedding_addRight c
    have hvol : (volume : Measure ℝ).map (fun x : ℝ => x + c) = volume :=
      MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) c
    have h_rn := hf.rnDeriv_map (μ.map X) (volume : Measure ℝ)
    rw [hvol] at h_rn
    -- `h_rn : (fun x => ((μ.map X).map (·+c)).rnDeriv volume (x+c)) =ᵐ[volume] (μ.map X).rnDeriv volume`.
    -- Pull `h_rn` back along the measure-preserving shift `(· − c)`.
    have hshift_qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x - c) volume volume := by
      refine ⟨by fun_prop, ?_⟩
      have : (volume : Measure ℝ).map (fun x : ℝ => x - c) = volume := by
        simpa [sub_eq_add_neg] using
          (MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) (-c))
      rw [this]
    have h_rn'' := hshift_qmp.ae_eq h_rn
    -- `h_rn'' : (fun x => ((μX).map (·+c)).rnDeriv volume ((x−c)+c)) =ᵐ (μX).rnDeriv volume (x−c)`.
    have hqX'' := hshift_qmp.ae_eq hqX
    -- combine: `((μX).map (·+c)).rnDeriv volume y =ᵐ ofReal (pX (y−c))`.
    filter_upwards [h_rn'', hqX''] with y hy hqy
    simp only [Function.comp, sub_add_cancel] at hy hqy
    rw [hy, hqy]
  -- (C) the dominating function `pX(x−c)·((A+1)+B·x²)` is integrable for any shift `c`.
  -- Expand `x² = (x−c)² + 2c·(x−c) + c²`, so the body is an `ℝ`-linear combination of the
  -- translates of `pX`, `y·pX`, `y²·pX` (all `volume`-integrable).
  -- `y·pX y` is integrable: `|y·pX| ≤ pX + y²·pX`.
  have hpX_mom1 : Integrable (fun y => y * pX y) volume := by
    refine Integrable.mono' (hpX_int.add hpX_mom)
      (by fun_prop : AEStronglyMeasurable (fun y => y * pX y) volume) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpX_nn y)]
    -- `|y|·pX ≤ (1+y²)·pX = pX + y²·pX` since `|y| ≤ 1 + y²` and `pX ≥ 0`.
    have hy_le : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
    calc |y| * pX y ≤ (1 + y ^ 2) * pX y := by
          apply mul_le_mul_of_nonneg_right hy_le (hpX_nn y)
      _ = pX y + y ^ 2 * pX y := by ring
  have hfib_dom_int : ∀ c : ℝ, Integrable
      (fun x => pX (x - c) * ((A + 1) + B * x ^ 2)) volume := by
    intro c
    -- translates
    have hT0 : Integrable (fun x => pX (x - c)) volume := hpX_int.comp_sub_right c
    have hT1 : Integrable (fun x => (x - c) * pX (x - c)) volume := hpX_mom1.comp_sub_right c
    have hT2 : Integrable (fun x => (x - c) ^ 2 * pX (x - c)) volume := hpX_mom.comp_sub_right c
    -- assemble: `pX(x−c)·((A+1)+B x²) = (A+1)·pX(x−c) + B·((x−c)²pX + 2c·(x−c)pX + c²·pX)`.
    have hcomb : Integrable
        (fun x => (A + 1) * pX (x - c)
          + B * ((x - c) ^ 2 * pX (x - c) + 2 * c * ((x - c) * pX (x - c))
              + c ^ 2 * pX (x - c))) volume :=
      (hT0.const_mul (A + 1)).add
        (((hT2.add (hT1.const_mul (2 * c))).add (hT0.const_mul (c ^ 2))).const_mul B)
    refine hcomb.congr (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- The 8 per-`n` preconditions of the Ω-level (β) lower bound.
  -- (3) per-fibre absolute continuity: each fibre is a translate of `μ.map X ≪ volume`.
  have hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib W Z μ z ≪ volume := by
    filter_upwards [hae] with z hz
    rw [hz, affineShiftKernel_apply]
    -- `(μ.map X).map (· + c·z) ≪ volume.map (· + c·z) = volume`.
    have hshift : MeasurableEmbedding (fun x : ℝ => x + Real.sqrt s * z) :=
      measurableEmbedding_addRight _
    have hvol : (volume : Measure ℝ).map (fun x : ℝ => x + Real.sqrt s * z) = volume :=
      MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) _
    calc (μ.map X).map (fun x : ℝ => x + Real.sqrt s * z)
        ≪ volume.map (fun x : ℝ => x + Real.sqrt s * z) :=
          (hX_ac).map (by fun_prop)
      _ = volume := hvol
  -- (1) joint absolute continuity: `condDistrib z ≪ volume ≪ μ.map W` (per-fibre),
  -- lifted to the compProd.
  have h_ac : (μ.map Z) ⊗ₘ condDistrib W Z μ
      ≪ (μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W) := by
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards [hκ_v] with z hz
    simpa using hz.trans vol_ac_W
  -- (4) per-fibre `p log p` integrability: transport along the translation, then
  -- identify with `∫ pX log pX = -∫ negMulLog pX` (`hpX_ent`).
  have h_pXlogpX : Integrable
      (fun x => ((μ.map X).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume := by
    refine (hpX_ent.neg).congr ?_
    filter_upwards [hqX] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpX_nn x)]
    simp only [Pi.neg_apply, Real.negMulLog, neg_neg, neg_mul]
  have hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib W Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib W Z μ z).rnDeriv volume x).toReal)) volume := by
    filter_upwards [hae] with z hz
    rw [hz, affineShiftKernel_apply]
    exact (fibre_rnDeriv_integrable_iff (μ.map X) (Real.sqrt s * z)
      (fun t => t * Real.log t)).mpr h_pXlogpX
  -- (5) per-fibre cross-term integrability.  The integrand couples the (translated)
  -- fibre density `p_z(x) = pX(x − √s·z)` with `log p_t(x)` (the marginal log-density).
  -- Identify both factors a.e. (`hfib_eq` / `hqW`), bound by `pX(x−c)·((A+1)+B·x²)`
  -- (`hLog`), then dominate by `hfib_dom_int c` (`Integrable.mono'`).
  have hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib W Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map W).rnDeriv volume x).toReal)) volume := by
    filter_upwards [hfib_eq] with z hz
    set c : ℝ := Real.sqrt s * z with hc
    -- target integrand `=ᵐ[volume] pX(x−c)·log (p_t x)`.
    have htarget_eq : (fun x => ((condDistrib W Z μ z).rnDeriv volume x).toReal
          * Real.log (((μ.map W).rnDeriv volume x).toReal))
        =ᵐ[volume] fun x => pX (x - c) * Real.log (p_t x) := by
      filter_upwards [hz, hqW] with x hx hxW
      rw [hx, hxW, ENNReal.toReal_ofReal (hpX_nn _), ENNReal.toReal_ofReal (hp_t_nn x)]
    refine (Integrable.mono' (hfib_dom_int c) ?_ ?_).congr htarget_eq.symm
    · exact ((hpX_meas.comp (measurable_id.sub_const c)).mul
        (hp_t_meas.log)).aestronglyMeasurable
    · filter_upwards [hLog] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpX_nn _)]
      exact mul_le_mul_of_nonneg_left hx (hpX_nn _)
  -- (6) outer fibre-entropy integrability: each fibre entropy equals the constant
  -- `h(μ.map X)` (translation invariance), so the function is a.e. constant.
  have h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib W Z μ z)) (μ.map Z) := by
    have hconst : (fun z => differentialEntropy (condDistrib W Z μ z))
        =ᵐ[μ.map Z] (fun _ => differentialEntropy (μ.map X)) := by
      filter_upwards [hae] with z hz
      rw [hz, affineShiftKernel_apply]
      exact differentialEntropy_map_add_const hX_ac (Real.sqrt s * z)
    exact (integrable_const _).congr hconst.symm
  -- (7) outer cross-term integrability (the `μ_Z`-average of the (5) cross integrals).
  -- The inner integral a.e.-equals `F(z) = ∫ pX(x−√s·z)·log p_t(x) dx`; bound
  -- `|F(z)| ≤ (A+1) + 2B·M2 + 2B·s·z²` (via `x² ≤ 2(x−c)²+2c²` and the translate
  -- moments), which is integrable over the Gaussian `μ.map Z`.
  have h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib W Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map W).rnDeriv volume x).toReal) ∂volume) (μ.map Z) := by
    set M2 : ℝ := ∫ y, y ^ 2 * pX y ∂volume with hM2
    set Fclean : ℝ → ℝ :=
      fun z => ∫ x, pX (x - Real.sqrt s * z) * Real.log (p_t x) ∂volume with hFclean
    -- the inner integral a.e.-equals `Fclean` (per-`z` integrand identification).
    have hF_eq : (fun z => ∫ x, ((condDistrib W Z μ z).rnDeriv volume x).toReal
          * Real.log (((μ.map W).rnDeriv volume x).toReal) ∂volume)
        =ᵐ[μ.map Z] Fclean := by
      filter_upwards [hfib_eq] with z hz
      refine integral_congr_ae ?_
      filter_upwards [hz, hqW] with x hx hxW
      rw [hx, hxW, ENNReal.toReal_ofReal (hpX_nn _), ENNReal.toReal_ofReal (hp_t_nn x)]
    refine (Integrable.congr ?_ hF_eq.symm)
    -- dominating polynomial `H(z) := (A+1) + 2B·M2 + 2B·s·z²`, integrable over the Gaussian.
    set H : ℝ → ℝ := fun z => (A + 1) + 2 * B * M2 + 2 * B * s * z ^ 2 with hH
    have hsq_int : Integrable (fun z => z ^ 2) (μ.map Z) := by
      rw [hZ_law]
      have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v_Z) := memLp_id_gaussianReal 2
      have := (memLp_two_iff_integrable_sq (μ := gaussianReal 0 v_Z)
        (f := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable).mp hmem
      simpa using this
    have hH_int : Integrable H (μ.map Z) := by
      rw [hH]
      exact (integrable_const _).add ((hsq_int.const_mul (2 * B * s)))
    -- measurability of `Fclean` (integral of a jointly measurable function).
    have hFclean_meas : AEStronglyMeasurable Fclean (μ.map Z) := by
      have hjoint : StronglyMeasurable
          (Function.uncurry fun z x => pX (x - Real.sqrt s * z) * Real.log (p_t x)) := by
        apply Measurable.stronglyMeasurable
        apply Measurable.mul
        · exact hpX_meas.comp (measurable_snd.sub (measurable_const.mul measurable_fst))
        · exact (hp_t_meas.comp measurable_snd).log
      exact (hjoint.integral_prod_right').aestronglyMeasurable
    refine Integrable.mono' hH_int hFclean_meas ?_
    -- `‖Fclean z‖ ≤ H z`.
    filter_upwards with z
    set c : ℝ := Real.sqrt s * z with hc
    have hc2 : c ^ 2 = s * z ^ 2 := by
      rw [hc, mul_pow, Real.sq_sqrt hs.le]
    -- a.e. pointwise bound `‖pX(x−c)·log p_t x‖ ≤ pX(x−c)·((A+1)+B x²)`.
    have hbound_ae : ∀ᵐ x ∂volume,
        ‖pX (x - c) * Real.log (p_t x)‖ ≤ pX (x - c) * ((A + 1) + B * x ^ 2) := by
      filter_upwards [hLog] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpX_nn _)]
      exact mul_le_mul_of_nonneg_left hx (hpX_nn _)
    have hdom : Integrable (fun x => pX (x - c) * ((A + 1) + B * x ^ 2)) volume :=
      hfib_dom_int c
    have hF_le : ‖Fclean z‖ ≤ ∫ x, pX (x - c) * ((A + 1) + B * x ^ 2) ∂volume := by
      rw [hFclean]
      calc ‖∫ x, pX (x - c) * Real.log (p_t x) ∂volume‖
          ≤ ∫ x, ‖pX (x - c) * Real.log (p_t x)‖ ∂volume := norm_integral_le_integral_norm _
        _ ≤ ∫ x, pX (x - c) * ((A + 1) + B * x ^ 2) ∂volume :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
              hdom hbound_ae
    -- bound `∫ pX(x−c)·((A+1)+Bx²) dx ≤ H z` via `x² ≤ 2(x−c)²+2c²` and translate moments.
    have hint_le : ∫ x, pX (x - c) * ((A + 1) + B * x ^ 2) ∂volume ≤ H z := by
      -- upper integrand `U(x) := (A+1)·pX(x−c) + 2B·(x−c)²pX(x−c) + 2Bc²·pX(x−c)`.
      set U : ℝ → ℝ := fun x =>
        (A + 1) * pX (x - c) + 2 * B * ((x - c) ^ 2 * pX (x - c))
          + 2 * B * c ^ 2 * pX (x - c) with hU
      have hT0 : Integrable (fun x => pX (x - c)) volume := hpX_int.comp_sub_right c
      have hT2 : Integrable (fun x => (x - c) ^ 2 * pX (x - c)) volume := hpX_mom.comp_sub_right c
      have hU_int : Integrable U volume :=
        ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B))).add (hT0.const_mul (2 * B * c ^ 2))
      -- `pX(x−c)·((A+1)+Bx²) ≤ U x` (using `x² ≤ 2(x−c)²+2c²` and `pX,B ≥ 0`).
      have hle : ∀ x, pX (x - c) * ((A + 1) + B * x ^ 2) ≤ U x := by
        intro x
        rw [hU]
        have hx2 : x ^ 2 ≤ 2 * (x - c) ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (x - 2 * c)]
        have hBnn : (0:ℝ) ≤ B := hB_nn
        nlinarith [hpX_nn (x - c), mul_le_mul_of_nonneg_left hx2 hBnn,
          mul_nonneg hBnn (sq_nonneg (x - c))]
      calc ∫ x, pX (x - c) * ((A + 1) + B * x ^ 2) ∂volume
          ≤ ∫ x, U x ∂volume :=
            integral_mono hdom hU_int hle
        _ = H z := by
            have hI0 : ∫ x, pX (x - c) ∂volume = 1 := by
              rw [integral_sub_right_eq_self (fun y => pX y) c, hpX_mass]
            have hI2 : ∫ x, (x - c) ^ 2 * pX (x - c) ∂volume = M2 := by
              rw [integral_sub_right_eq_self (fun y => y ^ 2 * pX y) c, ← hM2]
            have hsplit : ∫ x, U x ∂volume
                = (A + 1) * (∫ x, pX (x - c) ∂volume)
                  + 2 * B * (∫ x, (x - c) ^ 2 * pX (x - c) ∂volume)
                  + 2 * B * c ^ 2 * (∫ x, pX (x - c) ∂volume) := by
              show ∫ x, ((A + 1) * pX (x - c) + 2 * B * ((x - c) ^ 2 * pX (x - c))
                  + 2 * B * c ^ 2 * pX (x - c)) ∂volume = _
              rw [integral_add
                  (f := fun x => (A + 1) * pX (x - c) + 2 * B * ((x - c) ^ 2 * pX (x - c)))
                  (g := fun x => 2 * B * c ^ 2 * pX (x - c))
                  ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B)))
                  (hT0.const_mul (2 * B * c ^ 2)),
                integral_add
                  (f := fun x => (A + 1) * pX (x - c))
                  (g := fun x => 2 * B * ((x - c) ^ 2 * pX (x - c)))
                  (hT0.const_mul (A + 1)) (hT2.const_mul (2 * B)),
                integral_const_mul, integral_const_mul, integral_const_mul]
            rw [hsplit, hI0, hI2, hH, hc2]; ring
    exact le_trans hF_le hint_le
  -- (8) marginal log-density integrability: change measure `μ.map W → volume` and use
  -- the genuine marginal entropy integrability `∫ negMulLog p_t < ∞`.
  have h_negMulLog_p_t : Integrable (fun x => Real.negMulLog (p_t x)) volume := by
    rw [hp_t_def]
    exact InformationTheory.Shannon.FisherInfoV2.convDensityAdd_negMulLog_integrable
      pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (hu_pos n)
  have h_logq_int : Integrable
      (fun x => Real.log (((μ.map W).rnDeriv volume x).toReal)) (μ.map W) := by
    rw [← integrable_toReal_rnDeriv_mul_iff hW_ac]
    refine (h_negMulLog_p_t.neg).congr ?_
    filter_upwards [hqW] with x hx
    rw [hx, ENNReal.toReal_ofReal (hp_t_nn x)]
    simp only [Pi.neg_apply, Real.negMulLog, neg_neg, neg_mul]
  -- (2) joint llr integrability (= KL finiteness `D(joint ‖ product) < ∞`).  This is a
  -- separate compProd/chain-rule assembly (NOT the private-majorant blocker that (5)/(7)
  -- needed): the joint `rnDeriv` factorises per-fibre into `(κ_z).rnDeriv (μ.map W)` whose
  -- log a.e.[κ_z] equals `log q_z − log p_t`, and `integrable_compProd_iff` reduces to the
  -- already-discharged fibre/outer integrabilities.  Parked: the per-fibre chain-rule
  -- (`rnDeriv_mul_rnDeriv`) + reciprocal + `llr` value identity is a sizeable assembly.
  -- @residual(plan:epi-g2-general-sandwich-moonshot-plan)
  have h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib W Z μ)
        ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)))
      ((μ.map Z) ⊗ₘ condDistrib W Z μ) := by
    sorry
  -- Instantiate the genuine Ω-level (β) lower bound.
  exact negMulLog_convDensity_entropy_ge X Z μ hX hZ hXZ v_Z hv_Z_pos hZ_law
    hpX_nn hpX_meas hpX_law u hu_pos n
    h_ac h_int hκ_v hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int

end InformationTheory.Shannon
