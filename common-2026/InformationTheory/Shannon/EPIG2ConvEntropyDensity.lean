import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone
import InformationTheory.Meta.EntryPoint

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

## Status — proof done (0 sorry / 0 residual)

All 8 per-`n` preconditions of the Ω-level (β) lower bound are discharged genuinely here
from the canonical construction:

* per-fibre absolute continuity, `p log p` integrability, fibre-entropy integrability
  (translation invariance: each fibre is a translate `pX(· − √s·z)` of `μ.map X`);
* joint absolute continuity (per-fibre `≪ volume ≪ μ.map W`, the marginal having a
  strictly positive density);
* the **two cross terms** (per-fibre (5) + outer (7)): closed via the `s`-uniform
  polynomial majorant `|log p_t| ≤ A + B·x²`
  (`convDensityAdd_logFactor_poly_majorant`, made public in
  `FisherInfoV2DeBruijnAssembly`) integrated against `pX`'s translate moments
  (helpers `hLog` / `hfib_eq` / `hfib_dom_int` in the proof body);
* marginal log-density integrability (`∫ negMulLog p_t < ∞`, the genuine
  `convDensityAdd_negMulLog_integrable`);
* **joint llr integrability** `h_int` (= KL finiteness `D(joint ‖ product) < ∞`): closed
  via `MeasureTheory.Measure.integrable_compProd_iff`.  The slice identity
  `rnDeriv_compProd_eq_kernel_rnDeriv` + `Kernel.rnDeriv_eq_rnDeriv_measure` identify the
  joint `llr` a.e. with the per-fibre `llr (κ_z) (μ.map W)`, which the density split
  `llr_eq_log_density_sub_log_density` rewrites as `log p_z − log p_t`.  The per-fibre
  branch reuses the fibre-entropy + cross-term integrabilities (via
  `integrable_toReal_rnDeriv_mul_iff`); the outer branch dominates
  `∫ ‖log p_z − log p_t‖ ∂κ_z` by `C0 + (A+1) + 2B·M2 + 2B·s·z²` (Gaussian-integrable),
  using `∫ pX·|log pX| < ∞` (from `Integrable f ↔ Integrable ‖f‖` on `hpX_ent`) plus the
  `s`-uniform majorant.

`#print axioms negMulLog_convDensity_entropy_ge_density` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free).  This completes the EPI G2 (β) density-only lower bound.
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
`negMulLog_convDensity_entropy_ge` on the canonical product space `ℝ × ℝ`.

Independent honesty audit 2026-06-05: PASS — non-circular, non-bundled (all 8 Ω-level
preconditions discharged genuinely in the body from the canonical `ℝ × ℝ` construction;
no `*Hypothesis` predicate bundling), `μ = withDensity(pX).prod(gaussian)` is a genuine
probability measure (not vacuous), the cross-term / KL-finiteness preconditions are closed
via the s-uniform polynomial majorant + `integrable_compProd_iff` (non-trivial), `#print
axioms` re-verified sorryAx-free.
@audit:ok -/
@[entry_point]
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
  -- (2) joint llr integrability (= KL finiteness `D(joint ‖ product) < ∞`).  We open
  -- `integrable_compProd_iff` on `J := (μ.map Z) ⊗ₘ condDistrib W Z μ`.  The joint `llr`
  -- a.e.-equals the per-fibre `llr (κ_z) (μ.map W) = log p_z − log p_t`, and both branches
  -- reduce to the already-discharged fibre/outer integrabilities.
  set κ : Kernel ℝ ℝ := condDistrib W Z μ with hκ_def
  -- per-fibre absolute continuity `κ z ≪ μ.map W` (= `κ z ≪ volume ≪ μ.map W`).
  have hκ_acW : ∀ᵐ z ∂(μ.map Z), κ z ≪ μ.map W := by
    filter_upwards [hκ_v] with z hz
    exact hz.trans vol_ac_W
  -- per-fibre `llr (κ z) (μ.map W) =ᵐ[κ z] log p_z − log p_t` (density split).
  have hllr_split : ∀ᵐ z ∂(μ.map Z),
      llr (κ z) (μ.map W) =ᵐ[κ z] fun x =>
        Real.log (((κ z).rnDeriv volume x).toReal)
          - Real.log (((μ.map W).rnDeriv volume x).toReal) := by
    filter_upwards [hκ_v, hκ_acW] with z hz_v hz_acW
    haveI : SigmaFinite (κ z) := by
      haveI : IsProbabilityMeasure (κ z) := by rw [hκ_def]; infer_instance
      infer_instance
    exact llr_eq_log_density_sub_log_density (κ z) (μ.map W) hz_v hW_ac hz_acW
  -- per-fibre `Integrable (llr (κ z) (μ.map W)) (κ z)` from fibre-entropy + cross-term.
  have hfib_llr_int : ∀ᵐ z ∂(μ.map Z), Integrable (llr (κ z) (μ.map W)) (κ z) := by
    filter_upwards [hκ_v, hllr_split, hκ_logp_int, hκ_cross_int] with
      z hz_v hz_split hz_logp hz_cross
    -- `Integrable f (κ z) ↔ Integrable (fun x => (κz).rnDeriv volume · f) volume`.
    refine (integrable_congr hz_split).mpr ?_
    rw [← integrable_toReal_rnDeriv_mul_iff hz_v]
    -- `(κz).rnDeriv volume · (log p_z − log p_t) = (κz·log p_z) − (κz·log p_t)`.
    have hdist : (fun x => ((κ z).rnDeriv volume x).toReal
          * (Real.log (((κ z).rnDeriv volume x).toReal)
            - Real.log (((μ.map W).rnDeriv volume x).toReal)))
        = (fun x => ((κ z).rnDeriv volume x).toReal * Real.log (((κ z).rnDeriv volume x).toReal)
            - ((κ z).rnDeriv volume x).toReal * Real.log (((μ.map W).rnDeriv volume x).toReal)) := by
      funext x; ring
    rw [hdist]
    exact hz_logp.sub hz_cross
  -- `∫ pX·|log pX| < ∞` (the fibre-entropy in absolute value; `Integrable f ↔ Integrable |f|`).
  have hpX_abs_ent : Integrable (fun x => pX x * |Real.log (pX x)|) volume := by
    have h := hpX_ent.norm
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.norm_eq_abs, Real.negMulLog, abs_neg, abs_mul, abs_of_nonneg (hpX_nn x)]
  -- The joint llr value identity, transferred to per-fibre a.e.
  have h_llr_joint_eq : ∀ᵐ z ∂(μ.map Z), (fun y =>
        llr ((μ.map Z) ⊗ₘ κ) ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)) (z, y))
      =ᵐ[κ z] llr (κ z) (μ.map W) := by
    -- slice identity `(μ_Z ⊗ₘ κ).rnDeriv (μ_Z ⊗ₘ const μ_W) (z,y) =ᵐ Kernel.rnDeriv κ (const μ_W) z y`.
    have h_slice := InformationTheory.rnDeriv_compProd_eq_kernel_rnDeriv
      (μ := μ.map Z) (κ := κ) (η := Kernel.const ℝ (μ.map W)) h_ac
    -- transfer to `J`-a.e. (`J ≪ Jc`), then open into per-`z` a.e.
    have h_sliceJ := h_ac.ae_le h_slice
    have h_per : ∀ᵐ z ∂(μ.map Z), ∀ᵐ y ∂(κ z),
        ((μ.map Z) ⊗ₘ κ).rnDeriv ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)) (z, y)
          = Kernel.rnDeriv κ (Kernel.const ℝ (μ.map W)) z y :=
      Measure.ae_ae_of_ae_compProd h_sliceJ
    filter_upwards [h_per, hκ_acW] with z hz hz_acW
    have hkrn := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ)
      (η := Kernel.const ℝ (μ.map W)) (a := z)
    simp only [Kernel.const_apply] at hkrn
    -- transfer `Kernel.rnDeriv = (κ z).rnDeriv (μ.map W)` from `μ.map W`-a.e. to `κ z`-a.e.
    have hkrn' : Kernel.rnDeriv κ (Kernel.const ℝ (μ.map W)) z
        =ᵐ[κ z] fun y => (κ z).rnDeriv (μ.map W) y := hz_acW.ae_le hkrn
    filter_upwards [hz, hkrn'] with y hy hky
    simp only [llr_def]
    rw [hy, hky]
  -- AEStronglyMeasurable of the joint `llr` w.r.t. `J = μ_Z ⊗ₘ κ`.
  have h_meas_llr : AEStronglyMeasurable
      (llr ((μ.map Z) ⊗ₘ κ) ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)))
      ((μ.map Z) ⊗ₘ κ) := by
    simp only [llr_def]
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.log.aestronglyMeasurable
  -- joint llr integrability (= KL finiteness), genuinely closed via `integrable_compProd_iff`.
  have h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ κ)
        ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)))
      ((μ.map Z) ⊗ₘ κ) := by
    rw [MeasureTheory.Measure.integrable_compProd_iff h_meas_llr]
    constructor
    · -- branch (a): per-fibre integrability.
      filter_upwards [h_llr_joint_eq, hfib_llr_int] with z hz_eq hz_int
      exact (integrable_congr hz_eq).mpr hz_int
    · -- branch (b): outer integrability of `z ↦ ∫ ‖llr‖ ∂(κ z)`.
      -- a.e.-rewrite the inner integral via the joint llr identity + density split, then
      -- dominate `∫ ‖log p_z − log p_t‖ ∂κz ≤ C + 2B·s·z²` (gaussian-integrable).
      set Gabs : ℝ → ℝ := fun z => ∫ y, ‖Real.log (((κ z).rnDeriv volume y).toReal)
          - Real.log (((μ.map W).rnDeriv volume y).toReal)‖ ∂(κ z) with hGabs
      have hinner_eq : (fun z => ∫ y, ‖llr ((μ.map Z) ⊗ₘ κ)
            ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)) (z, y)‖ ∂(κ z))
          =ᵐ[μ.map Z] Gabs := by
        filter_upwards [h_llr_joint_eq, hllr_split] with z hz_eq hz_split
        rw [hGabs]
        refine integral_congr_ae ?_
        filter_upwards [hz_eq, hz_split] with y hy hy2
        rw [hy, hy2]
      refine (Integrable.congr ?_ hinner_eq.symm)
      -- clean form of the inner integral via translate `p_z(y) = pX(y − c)`, `c = √s·z`.
      set Fabs : ℝ → ℝ := fun z =>
        ∫ y, pX (y - Real.sqrt s * z)
          * |Real.log (pX (y - Real.sqrt s * z)) - Real.log (p_t y)| ∂volume with hFabs
      have hGF_eq : Gabs =ᵐ[μ.map Z] Fabs := by
        filter_upwards [hκ_v, hfib_eq] with z hz_v hz_fib
        simp only [hGabs, hFabs]
        set c : ℝ := Real.sqrt s * z with hc
        -- `∫ ‖log p_z − log p_t‖ ∂κz = ∫ (κz-density)·‖log p_z − log p_t‖ ∂vol`.
        rw [← integral_toReal_rnDeriv_mul (μ := κ z) (ν := volume) hz_v]
        refine integral_congr_ae ?_
        filter_upwards [hz_fib, hqW] with y hyfib hyW
        rw [hyfib, hyW, ENNReal.toReal_ofReal (hpX_nn _), ENNReal.toReal_ofReal (hp_t_nn y),
          Real.norm_eq_abs]
      refine (Integrable.congr ?_ hGF_eq.symm)
      -- dominate `‖Fabs z‖ ≤ Habs z := (C0 + (A+1)) + 2B·M2 + 2B·s·z²`.
      set M2 : ℝ := ∫ y, y ^ 2 * pX y ∂volume with hM2
      set C0 : ℝ := ∫ y, pX y * |Real.log (pX y)| ∂volume with hC0
      set Habs : ℝ → ℝ := fun z => (C0 + (A + 1)) + 2 * B * M2 + 2 * B * s * z ^ 2 with hHabs
      have hsq_int : Integrable (fun z => z ^ 2) (μ.map Z) := by
        rw [hZ_law]
        have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v_Z) := memLp_id_gaussianReal 2
        have := (memLp_two_iff_integrable_sq (μ := gaussianReal 0 v_Z)
          (f := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable).mp hmem
        simpa using this
      have hHabs_int : Integrable Habs (μ.map Z) := by
        rw [hHabs]
        exact (integrable_const _).add ((hsq_int.const_mul (2 * B * s)))
      have hFabs_meas : AEStronglyMeasurable Fabs (μ.map Z) := by
        have hjoint : StronglyMeasurable (Function.uncurry fun z y =>
            pX (y - Real.sqrt s * z)
              * |Real.log (pX (y - Real.sqrt s * z)) - Real.log (p_t y)|) := by
          apply Measurable.stronglyMeasurable
          apply Measurable.mul
          · exact hpX_meas.comp (measurable_snd.sub (measurable_const.mul measurable_fst))
          · exact (((hpX_meas.comp (measurable_snd.sub (measurable_const.mul measurable_fst))).log).sub
              ((hp_t_meas.comp measurable_snd).log)).abs
        exact (hjoint.integral_prod_right').aestronglyMeasurable
      refine Integrable.mono' hHabs_int hFabs_meas ?_
      filter_upwards with z
      set c : ℝ := Real.sqrt s * z with hc
      have hc2 : c ^ 2 = s * z ^ 2 := by rw [hc, mul_pow, Real.sq_sqrt hs.le]
      -- pointwise `pX(y−c)·|log p_z − log p_t| ≤ pX(y−c)·|log pX(y−c)| + pX(y−c)·((A+1)+B y²)`.
      have hbound_ae : ∀ᵐ y ∂volume,
          pX (y - c) * |Real.log (pX (y - c)) - Real.log (p_t y)|
            ≤ pX (y - c) * |Real.log (pX (y - c))|
              + pX (y - c) * ((A + 1) + B * y ^ 2) := by
        filter_upwards [hLog] with y hy
        have htri : |Real.log (pX (y - c)) - Real.log (p_t y)|
            ≤ |Real.log (pX (y - c))| + |Real.log (p_t y)| := abs_sub _ _
        have hstep : |Real.log (pX (y - c)) - Real.log (p_t y)|
            ≤ |Real.log (pX (y - c))| + ((A + 1) + B * y ^ 2) := le_trans htri (by linarith)
        calc pX (y - c) * |Real.log (pX (y - c)) - Real.log (p_t y)|
            ≤ pX (y - c) * (|Real.log (pX (y - c))| + ((A + 1) + B * y ^ 2)) :=
              mul_le_mul_of_nonneg_left hstep (hpX_nn _)
          _ = pX (y - c) * |Real.log (pX (y - c))| + pX (y - c) * ((A + 1) + B * y ^ 2) := by ring
      -- the two dominating pieces are integrable.
      have hC_int : Integrable (fun y => pX (y - c) * |Real.log (pX (y - c))|) volume :=
        hpX_abs_ent.comp_sub_right c
      have hD_int : Integrable (fun y => pX (y - c) * ((A + 1) + B * y ^ 2)) volume :=
        hfib_dom_int c
      have hsum_int : Integrable (fun y => pX (y - c) * |Real.log (pX (y - c))|
          + pX (y - c) * ((A + 1) + B * y ^ 2)) volume := hC_int.add hD_int
      -- `‖Fabs z‖ ≤ ∫ (dominating sum) ≤ Habs z`.
      have hF_le : ‖Fabs z‖ ≤ ∫ y, (pX (y - c) * |Real.log (pX (y - c))|
          + pX (y - c) * ((A + 1) + B * y ^ 2)) ∂volume := by
        rw [hFabs]
        have hint_nn : 0 ≤ ∫ y, pX (y - c)
            * |Real.log (pX (y - c)) - Real.log (p_t y)| ∂volume :=
          integral_nonneg (fun y => mul_nonneg (hpX_nn _) (abs_nonneg _))
        rw [Real.norm_eq_abs, abs_of_nonneg hint_nn]
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun y => mul_nonneg (hpX_nn _) (abs_nonneg _)))
          hsum_int hbound_ae
      -- evaluate the dominating integral `= C0 + (A+1) + 2B·M2 + 2B·c² = Habs z`.
      have hI_eval : ∫ y, (pX (y - c) * |Real.log (pX (y - c))|
          + pX (y - c) * ((A + 1) + B * y ^ 2)) ∂volume ≤ Habs z := by
        rw [integral_add hC_int hD_int]
        -- first piece `= C0` (translation invariance).
        have hICabs : ∫ y, pX (y - c) * |Real.log (pX (y - c))| ∂volume = C0 := by
          rw [hC0, integral_sub_right_eq_self (fun y => pX y * |Real.log (pX y)|) c]
        -- second piece `≤ (A+1) + 2B·M2 + 2B·c²`.
        set U : ℝ → ℝ := fun y =>
          (A + 1) * pX (y - c) + 2 * B * ((y - c) ^ 2 * pX (y - c))
            + 2 * B * c ^ 2 * pX (y - c) with hU
        have hT0 : Integrable (fun y => pX (y - c)) volume := hpX_int.comp_sub_right c
        have hT2 : Integrable (fun y => (y - c) ^ 2 * pX (y - c)) volume :=
          hpX_mom.comp_sub_right c
        have hU_int : Integrable U volume :=
          ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B))).add (hT0.const_mul (2 * B * c ^ 2))
        have hle : ∀ y, pX (y - c) * ((A + 1) + B * y ^ 2) ≤ U y := by
          intro y; rw [hU]
          have hy2 : y ^ 2 ≤ 2 * (y - c) ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (y - 2 * c)]
          have hBnn : (0:ℝ) ≤ B := hB_nn
          nlinarith [hpX_nn (y - c), mul_le_mul_of_nonneg_left hy2 hBnn,
            mul_nonneg hBnn (sq_nonneg (y - c))]
        have hIDle : ∫ y, pX (y - c) * ((A + 1) + B * y ^ 2) ∂volume ≤ ∫ y, U y ∂volume :=
          integral_mono hD_int hU_int hle
        have hI0 : ∫ y, pX (y - c) ∂volume = 1 := by
          rw [integral_sub_right_eq_self (fun y => pX y) c, hpX_mass]
        have hI2 : ∫ y, (y - c) ^ 2 * pX (y - c) ∂volume = M2 := by
          rw [integral_sub_right_eq_self (fun y => y ^ 2 * pX y) c, ← hM2]
        have hUsplit : ∫ y, U y ∂volume
            = (A + 1) * (∫ y, pX (y - c) ∂volume)
              + 2 * B * (∫ y, (y - c) ^ 2 * pX (y - c) ∂volume)
              + 2 * B * c ^ 2 * (∫ y, pX (y - c) ∂volume) := by
          show ∫ y, ((A + 1) * pX (y - c) + 2 * B * ((y - c) ^ 2 * pX (y - c))
              + 2 * B * c ^ 2 * pX (y - c)) ∂volume = _
          rw [integral_add
              (f := fun y => (A + 1) * pX (y - c) + 2 * B * ((y - c) ^ 2 * pX (y - c)))
              (g := fun y => 2 * B * c ^ 2 * pX (y - c))
              ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B)))
              (hT0.const_mul (2 * B * c ^ 2)),
            integral_add
              (f := fun y => (A + 1) * pX (y - c))
              (g := fun y => 2 * B * ((y - c) ^ 2 * pX (y - c)))
              (hT0.const_mul (A + 1)) (hT2.const_mul (2 * B)),
            integral_const_mul, integral_const_mul, integral_const_mul]
        rw [hICabs, hHabs]
        rw [hUsplit, hI0, hI2] at hIDle
        -- `hIDle : ∫ pX(·−c)·((A+1)+B·²) ≤ (A+1)·1 + 2B·M2 + 2B·c²·1`, and `c² = s·z²`.
        nlinarith [hIDle, hc2]
      exact le_trans hF_le hI_eval
  -- Instantiate the genuine Ω-level (β) lower bound.
  exact negMulLog_convDensity_entropy_ge X Z μ hX hZ hXZ v_Z hv_Z_pos hZ_law
    hpX_nn hpX_meas hpX_law u hu_pos n
    h_ac h_int hκ_v hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int

/-! ## Standalone cross-entropy integrability lemmas (extract of the template above)

The 3 `have` blocks `hκ_cross_int` / `h_cross_int` / `h_int` inside
`negMulLog_convDensity_entropy_ge_density` are extracted into standalone lemmas
parametrized over an arbitrary **fibre density** `q` (with mass `1`, finite second
moment, finite absolute entropy) and a **target convolution log-density**
`g := convDensityAdd pX (gaussianPDFReal 0 v)`.  Unlike the template (where fibre and
target share the same `pX`), these admit *two distinct* densities, so they cover the
EPI case-1 framing where the fibre is the Gaussian `q = gaussianPDFReal 0 v_B` (translated
by `z`) and the target is the input-convolution density `g`.

The polynomial majorant `|log g| ≤ (A+1) + B·x²` (a.e.) comes from
`convDensityAdd_logFactor_poly_majorant pX …`; the fibre `q` supplies the dominating
moments.  All genuine (no `sorry`), reusing the template's domination structure. -/

variable {Ω : Type*}

/-- Second-moment integrability of the centred Gaussian density: `y²·g_v(y)` is
`volume`-integrable.  Via `∫ y²·g_v = ∫ y² ∂(gaussianReal 0 v)` (finite by
`memLp_id_gaussianReal 2`).

Independent honesty audit 2026-06-05: PASS — genuine (no sorry), pure regularity output
(second-moment integrability), `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
@audit:ok -/
theorem integrable_sq_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y => y ^ 2 * gaussianPDFReal 0 v y) volume := by
  -- `Integrable (y²) (gaussianReal 0 v)` from `MemLp id 2`.
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  have hsq : Integrable (fun y => y ^ 2) (gaussianReal 0 v) := by
    have := (memLp_two_iff_integrable_sq (μ := gaussianReal 0 v)
      (f := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable).mp hmem
    simpa using this
  -- `gaussianReal 0 v = withDensity (ofReal (gaussianPDFReal 0 v))`.
  have hgauss : (gaussianReal 0 v)
      = volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 v x)) := by
    rw [gaussianReal_of_var_ne_zero 0 hv, gaussianPDF_def]
  rw [hgauss] at hsq
  rw [integrable_withDensity_iff_integrable_smul₀'
    (measurable_gaussianPDFReal 0 v).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq
  refine hsq.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v y)]
  ring

/-- Per-fibre cross-term integrability: the (shifted) fibre density `q(·−c)` times the
log of the convolution target `g = convDensityAdd pX g_v` is `volume`-integrable.
Dominated by `q(x−c)·((A+1)+B·x²)` via the polynomial majorant of `log g`.

Independent honesty audit 2026-06-05: PASS — genuine (no sorry). Conclusion (an
`Integrable` regularity output) follows from the hypotheses by `Integrable.mono'` against
the genuine majorant `convDensityAdd_logFactor_poly_majorant` (`@audit:ok`); no hypothesis
restates the conclusion or bundles an EPI/entropy claim — `q` is a free density argument
(instantiated at the Gaussian fibre by the consumer), so `hq_mom`/`hq_int` etc. are
preconditions, not load-bearing. `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
@audit:ok -/
theorem convCrossEntropy_perFibre_integrable
    (q pX : ℝ → ℝ) (hq_nn : ∀ x, 0 ≤ q x) (hq_meas : Measurable q)
    (hq_int : Integrable q volume) (hq_mom : Integrable (fun y => y ^ 2 * q y) volume)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {v : ℝ≥0} (hv : 0 < v) (c : ℝ) :
    Integrable (fun x => q (x - c)
      * Real.log (convDensityAdd pX (gaussianPDFReal 0 v) x)) volume := by
  set g : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 v) with hg_def
  -- Polynomial majorant `|log g| ≤ (A+1) + B·x²` a.e., at the single point `s = v`.
  obtain ⟨A, B, hB_nn, hLog0⟩ :=
    InformationTheory.Shannon.FisherInfoV2.convDensityAdd_logFactor_poly_majorant
      pX hpX_nn hpX_meas hpX_int hpX_mass hv
  have hv_mem : (v : ℝ) ∈ Set.Ioo ((v : ℝ) / 2) (2 * v) :=
    ⟨by linarith [(show (0:ℝ) < v from hv)], by linarith [(show (0:ℝ) < v from hv)]⟩
  have hLog : ∀ᵐ x ∂volume, |Real.log (g x)| ≤ (A + 1) + B * x ^ 2 := by
    filter_upwards [hLog0] with x hx
    have hb := hx (v : ℝ) hv_mem
    have hvval : (⟨(v : ℝ), le_of_lt (show (0:ℝ) < v from hv)⟩ : ℝ≥0) = v :=
      NNReal.coe_injective rfl
    have hpt_eq : convDensityAdd pX
        (gaussianPDFReal 0 ⟨(v : ℝ), le_of_lt (show (0:ℝ) < v from hv)⟩) x = g x := by
      rw [hg_def, hvval]
    rw [hpt_eq, Real.norm_eq_abs] at hb
    have habs : |Real.log (g x)| ≤ |(- Real.log (g x) - 1)| + 1 := by
      calc |Real.log (g x)| = |(- Real.log (g x) - 1) + 1| := by
            rw [show (- Real.log (g x) - 1) + 1 = - Real.log (g x) by ring, abs_neg]
        _ ≤ |(- Real.log (g x) - 1)| + |(1:ℝ)| := abs_add_le _ _
        _ = |(- Real.log (g x) - 1)| + 1 := by norm_num
    linarith
  -- Measurability of `g = convDensityAdd pX g_v`.
  have hg_meas : Measurable g := by
    rw [hg_def]
    have hg_pdf : Measurable (gaussianPDFReal 0 v) := measurable_gaussianPDFReal 0 _
    have huncurry : StronglyMeasurable
        (Function.uncurry fun z x => pX x * gaussianPDFReal 0 v (z - x)) := by
      apply Measurable.stronglyMeasurable
      exact (hpX_meas.comp measurable_snd).mul (hg_pdf.comp (measurable_fst.sub measurable_snd))
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [convDensityAdd] using h.measurable
  -- `q·first-moment` is integrable: `|y·q y| ≤ q + y²·q`.
  have hq_mom1 : Integrable (fun y => y * q y) volume := by
    refine Integrable.mono' (hq_int.add hq_mom)
      (by fun_prop : AEStronglyMeasurable (fun y => y * q y) volume) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq_nn y)]
    have hy_le : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
    calc |y| * q y ≤ (1 + y ^ 2) * q y := mul_le_mul_of_nonneg_right hy_le (hq_nn y)
      _ = q y + y ^ 2 * q y := by ring
  -- The dominating function `q(x−c)·((A+1)+B·x²)` is integrable.
  have hdom : Integrable (fun x => q (x - c) * ((A + 1) + B * x ^ 2)) volume := by
    have hT0 : Integrable (fun x => q (x - c)) volume := hq_int.comp_sub_right c
    have hT1 : Integrable (fun x => (x - c) * q (x - c)) volume := hq_mom1.comp_sub_right c
    have hT2 : Integrable (fun x => (x - c) ^ 2 * q (x - c)) volume := hq_mom.comp_sub_right c
    have hcomb : Integrable
        (fun x => (A + 1) * q (x - c)
          + B * ((x - c) ^ 2 * q (x - c) + 2 * c * ((x - c) * q (x - c))
              + c ^ 2 * q (x - c))) volume :=
      (hT0.const_mul (A + 1)).add
        (((hT2.add (hT1.const_mul (2 * c))).add (hT0.const_mul (c ^ 2))).const_mul B)
    refine hcomb.congr (Filter.Eventually.of_forall (fun x => ?_)); ring
  refine Integrable.mono' hdom ?_ ?_
  · exact ((hq_meas.comp (measurable_id.sub_const c)).mul hg_meas.log).aestronglyMeasurable
  · filter_upwards [hLog] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq_nn _)]
    exact mul_le_mul_of_nonneg_left hx (hq_nn _)

/-- `z`-averaged cross-term integrability: averaging the per-fibre cross integral over a
measure `νZ` with finite second moment yields an integrable function of `z`.  The shift
is `c(z) = √s·z`; bounded by `(A+1) + 2B·M2q + 2B·s·z²` (gaussian-style moment control).

Independent honesty audit 2026-06-05: PASS — genuine (no sorry). The `z`-averaged
`Integrable` conclusion follows by `Integrable.mono'` against a degree-2 polynomial
`H(z)`, integrable over `νZ` precisely because `hνZ_sq` (finite second moment) is supplied
as a precondition; all hypotheses are regularity/integrability obligations on the free
density `q` and the convolution target, none encodes the conclusion. `#print axioms` =
`[propext, Classical.choice, Quot.sound]`.
@audit:ok -/
theorem convCrossEntropy_zAvg_integrable
    (q pX : ℝ → ℝ) (hq_nn : ∀ x, 0 ≤ q x) (hq_meas : Measurable q)
    (hq_int : Integrable q volume) (hq_mass : (∫ y, q y ∂volume) = 1)
    (hq_mom : Integrable (fun y => y ^ 2 * q y) volume)
    (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {v : ℝ≥0} (hv : 0 < v) {s : ℝ} (hs : 0 < s)
    (νZ : Measure ℝ) [IsFiniteMeasure νZ] (hνZ_sq : Integrable (fun z => z ^ 2) νZ) :
    Integrable (fun z => ∫ x, q (x - Real.sqrt s * z)
      * Real.log (convDensityAdd pX (gaussianPDFReal 0 v) x) ∂volume) νZ := by
  set g : ℝ → ℝ := convDensityAdd pX (gaussianPDFReal 0 v) with hg_def
  -- Polynomial majorant `|log g| ≤ (A+1) + B·x²` a.e.
  obtain ⟨A, B, hB_nn, hLog0⟩ :=
    InformationTheory.Shannon.FisherInfoV2.convDensityAdd_logFactor_poly_majorant
      pX hpX_nn hpX_meas hpX_int hpX_mass hv
  have hv_mem : (v : ℝ) ∈ Set.Ioo ((v : ℝ) / 2) (2 * v) :=
    ⟨by linarith [(show (0:ℝ) < v from hv)], by linarith [(show (0:ℝ) < v from hv)]⟩
  have hvval : (⟨(v : ℝ), le_of_lt (show (0:ℝ) < v from hv)⟩ : ℝ≥0) = v :=
    NNReal.coe_injective rfl
  have hLog : ∀ᵐ x ∂volume, |Real.log (g x)| ≤ (A + 1) + B * x ^ 2 := by
    filter_upwards [hLog0] with x hx
    have hb := hx (v : ℝ) hv_mem
    have hpt_eq : convDensityAdd pX
        (gaussianPDFReal 0 ⟨(v : ℝ), le_of_lt (show (0:ℝ) < v from hv)⟩) x = g x := by
      rw [hg_def, hvval]
    rw [hpt_eq, Real.norm_eq_abs] at hb
    have habs : |Real.log (g x)| ≤ |(- Real.log (g x) - 1)| + 1 := by
      calc |Real.log (g x)| = |(- Real.log (g x) - 1) + 1| := by
            rw [show (- Real.log (g x) - 1) + 1 = - Real.log (g x) by ring, abs_neg]
        _ ≤ |(- Real.log (g x) - 1)| + |(1:ℝ)| := abs_add_le _ _
        _ = |(- Real.log (g x) - 1)| + 1 := by norm_num
    linarith
  -- Measurability of `g`.
  have hg_meas : Measurable g := by
    rw [hg_def]
    have hg_pdf : Measurable (gaussianPDFReal 0 v) := measurable_gaussianPDFReal 0 _
    have huncurry : StronglyMeasurable
        (Function.uncurry fun z x => pX x * gaussianPDFReal 0 v (z - x)) := by
      apply Measurable.stronglyMeasurable
      exact (hpX_meas.comp measurable_snd).mul (hg_pdf.comp (measurable_fst.sub measurable_snd))
    have h := huncurry.integral_prod_right (ν := volume)
    simpa only [convDensityAdd] using h.measurable
  -- Translate moments of `q`.
  set M2 : ℝ := ∫ y, y ^ 2 * q y ∂volume with hM2
  set Fclean : ℝ → ℝ :=
    fun z => ∫ x, q (x - Real.sqrt s * z) * Real.log (g x) ∂volume with hFclean
  -- dominating polynomial `H(z) := (A+1) + 2B·M2 + 2B·s·z²`, integrable over `νZ`.
  set H : ℝ → ℝ := fun z => (A + 1) + 2 * B * M2 + 2 * B * s * z ^ 2 with hH
  have hH_int : Integrable H νZ := by
    rw [hH]; exact (integrable_const _).add (hνZ_sq.const_mul (2 * B * s))
  -- measurability of `Fclean`.
  have hFclean_meas : AEStronglyMeasurable Fclean νZ := by
    have hjoint : StronglyMeasurable
        (Function.uncurry fun z x => q (x - Real.sqrt s * z) * Real.log (g x)) := by
      apply Measurable.stronglyMeasurable
      apply Measurable.mul
      · exact hq_meas.comp (measurable_snd.sub (measurable_const.mul measurable_fst))
      · exact (hg_meas.comp measurable_snd).log
    exact (hjoint.integral_prod_right').aestronglyMeasurable
  refine Integrable.mono' hH_int hFclean_meas ?_
  -- `‖Fclean z‖ ≤ H z`.
  filter_upwards with z
  set c : ℝ := Real.sqrt s * z with hc
  have hc2 : c ^ 2 = s * z ^ 2 := by rw [hc, mul_pow, Real.sq_sqrt hs.le]
  have hbound_ae : ∀ᵐ x ∂volume,
      ‖q (x - c) * Real.log (g x)‖ ≤ q (x - c) * ((A + 1) + B * x ^ 2) := by
    filter_upwards [hLog] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq_nn _)]
    exact mul_le_mul_of_nonneg_left hx (hq_nn _)
  have hdom : Integrable (fun x => q (x - c) * ((A + 1) + B * x ^ 2)) volume := by
    have hq_mom1 : Integrable (fun y => y * q y) volume := by
      refine Integrable.mono' (hq_int.add hq_mom)
        (by fun_prop : AEStronglyMeasurable (fun y => y * q y) volume) ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq_nn y)]
      have hy_le : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
      calc |y| * q y ≤ (1 + y ^ 2) * q y := mul_le_mul_of_nonneg_right hy_le (hq_nn y)
        _ = q y + y ^ 2 * q y := by ring
    have hT0 : Integrable (fun x => q (x - c)) volume := hq_int.comp_sub_right c
    have hT1 : Integrable (fun x => (x - c) * q (x - c)) volume := hq_mom1.comp_sub_right c
    have hT2 : Integrable (fun x => (x - c) ^ 2 * q (x - c)) volume := hq_mom.comp_sub_right c
    have hcomb : Integrable
        (fun x => (A + 1) * q (x - c)
          + B * ((x - c) ^ 2 * q (x - c) + 2 * c * ((x - c) * q (x - c))
              + c ^ 2 * q (x - c))) volume :=
      (hT0.const_mul (A + 1)).add
        (((hT2.add (hT1.const_mul (2 * c))).add (hT0.const_mul (c ^ 2))).const_mul B)
    refine hcomb.congr (Filter.Eventually.of_forall (fun x => ?_)); ring
  have hF_le : ‖Fclean z‖ ≤ ∫ x, q (x - c) * ((A + 1) + B * x ^ 2) ∂volume := by
    rw [hFclean]
    calc ‖∫ x, q (x - c) * Real.log (g x) ∂volume‖
        ≤ ∫ x, ‖q (x - c) * Real.log (g x)‖ ∂volume := norm_integral_le_integral_norm _
      _ ≤ ∫ x, q (x - c) * ((A + 1) + B * x ^ 2) ∂volume :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
            hdom hbound_ae
  have hint_le : ∫ x, q (x - c) * ((A + 1) + B * x ^ 2) ∂volume ≤ H z := by
    set U : ℝ → ℝ := fun x =>
      (A + 1) * q (x - c) + 2 * B * ((x - c) ^ 2 * q (x - c))
        + 2 * B * c ^ 2 * q (x - c) with hU
    have hT0 : Integrable (fun x => q (x - c)) volume := hq_int.comp_sub_right c
    have hT2 : Integrable (fun x => (x - c) ^ 2 * q (x - c)) volume := hq_mom.comp_sub_right c
    have hU_int : Integrable U volume :=
      ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B))).add (hT0.const_mul (2 * B * c ^ 2))
    have hle : ∀ x, q (x - c) * ((A + 1) + B * x ^ 2) ≤ U x := by
      intro x; rw [hU]
      have hx2 : x ^ 2 ≤ 2 * (x - c) ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (x - 2 * c)]
      have hBnn : (0:ℝ) ≤ B := hB_nn
      nlinarith [hq_nn (x - c), mul_le_mul_of_nonneg_left hx2 hBnn,
        mul_nonneg hBnn (sq_nonneg (x - c))]
    calc ∫ x, q (x - c) * ((A + 1) + B * x ^ 2) ∂volume
        ≤ ∫ x, U x ∂volume := integral_mono hdom hU_int hle
      _ = H z := by
          have hI0 : ∫ x, q (x - c) ∂volume = 1 := by
            rw [integral_sub_right_eq_self (fun y => q y) c, hq_mass]
          have hI2 : ∫ x, (x - c) ^ 2 * q (x - c) ∂volume = M2 := by
            rw [integral_sub_right_eq_self (fun y => y ^ 2 * q y) c, ← hM2]
          have hsplit : ∫ x, U x ∂volume
              = (A + 1) * (∫ x, q (x - c) ∂volume)
                + 2 * B * (∫ x, (x - c) ^ 2 * q (x - c) ∂volume)
                + 2 * B * c ^ 2 * (∫ x, q (x - c) ∂volume) := by
            show ∫ x, ((A + 1) * q (x - c) + 2 * B * ((x - c) ^ 2 * q (x - c))
                + 2 * B * c ^ 2 * q (x - c)) ∂volume = _
            rw [integral_add
                (f := fun x => (A + 1) * q (x - c) + 2 * B * ((x - c) ^ 2 * q (x - c)))
                (g := fun x => 2 * B * c ^ 2 * q (x - c))
                ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B)))
                (hT0.const_mul (2 * B * c ^ 2)),
              integral_add
                (f := fun x => (A + 1) * q (x - c))
                (g := fun x => 2 * B * ((x - c) ^ 2 * q (x - c)))
                (hT0.const_mul (A + 1)) (hT2.const_mul (2 * B)),
              integral_const_mul, integral_const_mul, integral_const_mul]
          rw [hsplit, hI0, hI2, hH, hc2]; ring
  exact le_trans hF_le hint_le

/-- Joint llr (conditional-KL divergence integrand) integrability, extracted from the
template `h_int` block.  Given a probability space `μ` with coordinates `Z W`, a fibre
kernel `κ = condDistrib W Z μ` whose fibres a.e.-equal the (shifted) density `q(·−√s·z)`
and whose marginal `μ.map W` has density `g`, with the polynomial majorant
`|log g| ≤ (A+1)+B·x²`, the joint `llr` of the compProd vs. the product-with-const is
`(μ.map Z) ⊗ₘ κ`-integrable.  All hypotheses are genuine regularity/integrability
obligations (none encodes the EPI conclusion).

Independent honesty audit 2026-06-05: PASS (sufficiency check applied — the 4th honesty
axis beyond non-circular / non-bundled). The conclusion (KL-finiteness `D(joint‖product)
< ∞`, a regularity output) follows from the hypotheses via `integrable_compProd_iff`:
branch (a) reuses `hκ_logp_int + hκ_cross_int` through the density split
`llr_eq_log_density_sub_log_density`; branch (b) dominates the outer `∫‖log p_z − log
p_t‖∂κz` by `C0 + (A+1) + 2B·M2 + 2B·s·z²` (`hq_abs_ent` → `C0`, `hLog` → polynomial,
`hZ_sq` → Gaussian integrability of `z²`). Each hypothesis discharges an actual obligation;
none is a restatement of the conclusion or an EPI inequality. Crucially `q` and `g` are
*decoupled free arguments* — the consumer (EPI case-1) instantiates `q` at the **Gaussian
fibre** `gaussianPDFReal 0 v_B` (since the conditioning variable is the input `Zt` and the
fibre is the translated Gaussian), so `hq_abs_ent` is Gaussian self-entropy (genuinely
finite via `integrable_density_log_density_of_gaussian`), NOT the input-density entropy
`hpX_ent`. This vindicates the implementer's pivot over the inventory's `hpX_ent`
prediction: the `hpX_ent` requirement was an artefact of the `_density` template (where the
fibre is `pX`), not intrinsic — the abstract `q` lets the consumer pick whichever side is
Gaussian. Non-circular (no hypothesis ≡ conclusion), non-bundled (no `*Hypothesis`
predicate), satisfiable (consumer supplies a genuine instance). `#print axioms` = `[propext,
Classical.choice, Quot.sound]`.
@audit:ok -/
theorem convJointLlr_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z W : Ω → ℝ)
    (q g : ℝ → ℝ) (hq_nn : ∀ x, 0 ≤ q x) (hg_nn : ∀ x, 0 ≤ g x)
    (hq_meas : Measurable q) (hg_meas : Measurable g)
    (A B : ℝ) {s : ℝ} (hs : 0 < s)
    (hW_ac : (μ.map W) ≪ volume)
    (vol_ac_W : (volume : Measure ℝ) ≪ μ.map W)
    (hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib W Z μ z ≪ volume)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib W Z μ
        ≪ (μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W))
    (hfib_eq : ∀ᵐ z ∂(μ.map Z),
        (condDistrib W Z μ z).rnDeriv volume
          =ᵐ[volume] fun x => ENNReal.ofReal (q (x - Real.sqrt s * z)))
    (hqW : (μ.map W).rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (g x))
    (hLog : ∀ᵐ x ∂volume, |Real.log (g x)| ≤ (A + 1) + B * x ^ 2) (hB_nn : 0 ≤ B)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
        (fun x => ((condDistrib W Z μ z).rnDeriv volume x).toReal
          * Real.log (((condDistrib W Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
        (fun x => ((condDistrib W Z μ z).rnDeriv volume x).toReal
          * Real.log (((μ.map W).rnDeriv volume x).toReal)) volume)
    (hq_int : Integrable q volume) (hq_mass : (∫ y, q y ∂volume) = 1)
    (hq_mom : Integrable (fun y => y ^ 2 * q y) volume)
    (hq_abs_ent : Integrable (fun x => q x * |Real.log (q x)|) volume)
    (hZ_sq : Integrable (fun z => z ^ 2) (μ.map Z)) :
    Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib W Z μ)
        ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)))
      ((μ.map Z) ⊗ₘ condDistrib W Z μ) := by
  set κ : Kernel ℝ ℝ := condDistrib W Z μ with hκ_def
  -- per-fibre absolute continuity `κ z ≪ μ.map W`.
  have hκ_acW : ∀ᵐ z ∂(μ.map Z), κ z ≪ μ.map W := by
    filter_upwards [hκ_v] with z hz
    exact hz.trans vol_ac_W
  -- per-fibre `llr (κ z) (μ.map W) =ᵐ[κ z] log p_z − log p_t`.
  have hllr_split : ∀ᵐ z ∂(μ.map Z),
      llr (κ z) (μ.map W) =ᵐ[κ z] fun x =>
        Real.log (((κ z).rnDeriv volume x).toReal)
          - Real.log (((μ.map W).rnDeriv volume x).toReal) := by
    filter_upwards [hκ_v, hκ_acW] with z hz_v hz_acW
    haveI : SigmaFinite (κ z) := by
      haveI : IsProbabilityMeasure (κ z) := by rw [hκ_def]; infer_instance
      infer_instance
    exact llr_eq_log_density_sub_log_density (κ z) (μ.map W) hz_v hW_ac hz_acW
  -- per-fibre `Integrable (llr (κ z) (μ.map W)) (κ z)`.
  have hfib_llr_int : ∀ᵐ z ∂(μ.map Z), Integrable (llr (κ z) (μ.map W)) (κ z) := by
    filter_upwards [hκ_v, hllr_split, hκ_logp_int, hκ_cross_int] with
      z hz_v hz_split hz_logp hz_cross
    refine (integrable_congr hz_split).mpr ?_
    rw [← integrable_toReal_rnDeriv_mul_iff hz_v]
    have hdist : (fun x => ((κ z).rnDeriv volume x).toReal
          * (Real.log (((κ z).rnDeriv volume x).toReal)
            - Real.log (((μ.map W).rnDeriv volume x).toReal)))
        = (fun x => ((κ z).rnDeriv volume x).toReal * Real.log (((κ z).rnDeriv volume x).toReal)
            - ((κ z).rnDeriv volume x).toReal * Real.log (((μ.map W).rnDeriv volume x).toReal)) := by
      funext x; ring
    rw [hdist]
    exact hz_logp.sub hz_cross
  -- The joint llr value identity, transferred to per-fibre a.e.
  have h_llr_joint_eq : ∀ᵐ z ∂(μ.map Z), (fun y =>
        llr ((μ.map Z) ⊗ₘ κ) ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)) (z, y))
      =ᵐ[κ z] llr (κ z) (μ.map W) := by
    have h_slice := InformationTheory.rnDeriv_compProd_eq_kernel_rnDeriv
      (μ := μ.map Z) (κ := κ) (η := Kernel.const ℝ (μ.map W)) h_ac
    have h_sliceJ := h_ac.ae_le h_slice
    have h_per : ∀ᵐ z ∂(μ.map Z), ∀ᵐ y ∂(κ z),
        ((μ.map Z) ⊗ₘ κ).rnDeriv ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)) (z, y)
          = Kernel.rnDeriv κ (Kernel.const ℝ (μ.map W)) z y :=
      Measure.ae_ae_of_ae_compProd h_sliceJ
    filter_upwards [h_per, hκ_acW] with z hz hz_acW
    have hkrn := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ)
      (η := Kernel.const ℝ (μ.map W)) (a := z)
    simp only [Kernel.const_apply] at hkrn
    have hkrn' : Kernel.rnDeriv κ (Kernel.const ℝ (μ.map W)) z
        =ᵐ[κ z] fun y => (κ z).rnDeriv (μ.map W) y := hz_acW.ae_le hkrn
    filter_upwards [hz, hkrn'] with y hy hky
    simp only [llr_def]
    rw [hy, hky]
  -- AEStronglyMeasurable of the joint `llr`.
  have h_meas_llr : AEStronglyMeasurable
      (llr ((μ.map Z) ⊗ₘ κ) ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)))
      ((μ.map Z) ⊗ₘ κ) := by
    simp only [llr_def]
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.log.aestronglyMeasurable
  rw [MeasureTheory.Measure.integrable_compProd_iff h_meas_llr]
  refine ⟨?_, ?_⟩
  · -- branch (a): per-fibre integrability.
    filter_upwards [h_llr_joint_eq, hfib_llr_int] with z hz_eq hz_int
    exact (integrable_congr hz_eq).mpr hz_int
  · -- branch (b): outer integrability of `z ↦ ∫ ‖llr‖ ∂(κ z)`.
    set Gabs : ℝ → ℝ := fun z => ∫ y, ‖Real.log (((κ z).rnDeriv volume y).toReal)
        - Real.log (((μ.map W).rnDeriv volume y).toReal)‖ ∂(κ z) with hGabs
    have hinner_eq : (fun z => ∫ y, ‖llr ((μ.map Z) ⊗ₘ κ)
          ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map W)) (z, y)‖ ∂(κ z))
        =ᵐ[μ.map Z] Gabs := by
      filter_upwards [h_llr_joint_eq, hllr_split] with z hz_eq hz_split
      rw [hGabs]
      refine integral_congr_ae ?_
      filter_upwards [hz_eq, hz_split] with y hy hy2
      rw [hy, hy2]
    refine (Integrable.congr ?_ hinner_eq.symm)
    -- clean form of the inner integral via translate `p_z(y) = q(y − c)`, `c = √s·z`.
    set Fabs : ℝ → ℝ := fun z =>
      ∫ y, q (y - Real.sqrt s * z)
        * |Real.log (q (y - Real.sqrt s * z)) - Real.log (g y)| ∂volume with hFabs
    have hGF_eq : Gabs =ᵐ[μ.map Z] Fabs := by
      filter_upwards [hκ_v, hfib_eq] with z hz_v hz_fib
      simp only [hGabs, hFabs]
      set c : ℝ := Real.sqrt s * z with hc
      rw [← integral_toReal_rnDeriv_mul (μ := κ z) (ν := volume) hz_v]
      refine integral_congr_ae ?_
      filter_upwards [hz_fib, hqW] with y hyfib hyW
      rw [hyfib, hyW, ENNReal.toReal_ofReal (hq_nn _), ENNReal.toReal_ofReal (hg_nn y),
        Real.norm_eq_abs]
    refine (Integrable.congr ?_ hGF_eq.symm)
    -- dominate `‖Fabs z‖ ≤ Habs z := (C0 + (A+1)) + 2B·M2 + 2B·s·z²`.
    set M2 : ℝ := ∫ y, y ^ 2 * q y ∂volume with hM2
    set C0 : ℝ := ∫ y, q y * |Real.log (q y)| ∂volume with hC0
    set Habs : ℝ → ℝ := fun z => (C0 + (A + 1)) + 2 * B * M2 + 2 * B * s * z ^ 2 with hHabs
    have hHabs_int : Integrable Habs (μ.map Z) := by
      rw [hHabs]; exact (integrable_const _).add (hZ_sq.const_mul (2 * B * s))
    have hFabs_meas : AEStronglyMeasurable Fabs (μ.map Z) := by
      have hjoint : StronglyMeasurable (Function.uncurry fun z y =>
          q (y - Real.sqrt s * z)
            * |Real.log (q (y - Real.sqrt s * z)) - Real.log (g y)|) := by
        apply Measurable.stronglyMeasurable
        apply Measurable.mul
        · exact hq_meas.comp (measurable_snd.sub (measurable_const.mul measurable_fst))
        · exact (((hq_meas.comp (measurable_snd.sub (measurable_const.mul measurable_fst))).log).sub
            ((hg_meas.comp measurable_snd).log)).abs
      exact (hjoint.integral_prod_right').aestronglyMeasurable
    refine Integrable.mono' hHabs_int hFabs_meas ?_
    filter_upwards with z
    set c : ℝ := Real.sqrt s * z with hc
    have hc2 : c ^ 2 = s * z ^ 2 := by rw [hc, mul_pow, Real.sq_sqrt hs.le]
    have hbound_ae : ∀ᵐ y ∂volume,
        q (y - c) * |Real.log (q (y - c)) - Real.log (g y)|
          ≤ q (y - c) * |Real.log (q (y - c))|
            + q (y - c) * ((A + 1) + B * y ^ 2) := by
      filter_upwards [hLog] with y hy
      have htri : |Real.log (q (y - c)) - Real.log (g y)|
          ≤ |Real.log (q (y - c))| + |Real.log (g y)| := abs_sub _ _
      have hstep : |Real.log (q (y - c)) - Real.log (g y)|
          ≤ |Real.log (q (y - c))| + ((A + 1) + B * y ^ 2) := le_trans htri (by linarith)
      calc q (y - c) * |Real.log (q (y - c)) - Real.log (g y)|
          ≤ q (y - c) * (|Real.log (q (y - c))| + ((A + 1) + B * y ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep (hq_nn _)
        _ = q (y - c) * |Real.log (q (y - c))| + q (y - c) * ((A + 1) + B * y ^ 2) := by ring
    have hC_int : Integrable (fun y => q (y - c) * |Real.log (q (y - c))|) volume :=
      hq_abs_ent.comp_sub_right c
    have hD_int : Integrable (fun y => q (y - c) * ((A + 1) + B * y ^ 2)) volume := by
      have hq_mom1 : Integrable (fun y => y * q y) volume := by
        refine Integrable.mono' (hq_int.add hq_mom)
          (by fun_prop : AEStronglyMeasurable (fun y => y * q y) volume) ?_
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq_nn y)]
        have hy_le : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
        calc |y| * q y ≤ (1 + y ^ 2) * q y := mul_le_mul_of_nonneg_right hy_le (hq_nn y)
          _ = q y + y ^ 2 * q y := by ring
      have hT0 : Integrable (fun x => q (x - c)) volume := hq_int.comp_sub_right c
      have hT1 : Integrable (fun x => (x - c) * q (x - c)) volume := hq_mom1.comp_sub_right c
      have hT2 : Integrable (fun x => (x - c) ^ 2 * q (x - c)) volume := hq_mom.comp_sub_right c
      have hcomb : Integrable
          (fun x => (A + 1) * q (x - c)
            + B * ((x - c) ^ 2 * q (x - c) + 2 * c * ((x - c) * q (x - c))
                + c ^ 2 * q (x - c))) volume :=
        (hT0.const_mul (A + 1)).add
          (((hT2.add (hT1.const_mul (2 * c))).add (hT0.const_mul (c ^ 2))).const_mul B)
      refine hcomb.congr (Filter.Eventually.of_forall (fun x => ?_)); ring
    have hsum_int : Integrable (fun y => q (y - c) * |Real.log (q (y - c))|
        + q (y - c) * ((A + 1) + B * y ^ 2)) volume := hC_int.add hD_int
    have hF_le : ‖Fabs z‖ ≤ ∫ y, (q (y - c) * |Real.log (q (y - c))|
        + q (y - c) * ((A + 1) + B * y ^ 2)) ∂volume := by
      rw [hFabs]
      have hint_nn : 0 ≤ ∫ y, q (y - c)
          * |Real.log (q (y - c)) - Real.log (g y)| ∂volume :=
        integral_nonneg (fun y => mul_nonneg (hq_nn _) (abs_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg hint_nn]
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun y => mul_nonneg (hq_nn _) (abs_nonneg _)))
        hsum_int hbound_ae
    have hI_eval : ∫ y, (q (y - c) * |Real.log (q (y - c))|
        + q (y - c) * ((A + 1) + B * y ^ 2)) ∂volume ≤ Habs z := by
      rw [integral_add hC_int hD_int]
      have hICabs : ∫ y, q (y - c) * |Real.log (q (y - c))| ∂volume = C0 := by
        rw [hC0, integral_sub_right_eq_self (fun y => q y * |Real.log (q y)|) c]
      set U : ℝ → ℝ := fun y =>
        (A + 1) * q (y - c) + 2 * B * ((y - c) ^ 2 * q (y - c))
          + 2 * B * c ^ 2 * q (y - c) with hU
      have hT0 : Integrable (fun y => q (y - c)) volume := hq_int.comp_sub_right c
      have hT2 : Integrable (fun y => (y - c) ^ 2 * q (y - c)) volume :=
        hq_mom.comp_sub_right c
      have hU_int : Integrable U volume :=
        ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B))).add (hT0.const_mul (2 * B * c ^ 2))
      have hle : ∀ y, q (y - c) * ((A + 1) + B * y ^ 2) ≤ U y := by
        intro y; rw [hU]
        have hy2 : y ^ 2 ≤ 2 * (y - c) ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (y - 2 * c)]
        have hBnn : (0:ℝ) ≤ B := hB_nn
        nlinarith [hq_nn (y - c), mul_le_mul_of_nonneg_left hy2 hBnn,
          mul_nonneg hBnn (sq_nonneg (y - c))]
      have hIDle : ∫ y, q (y - c) * ((A + 1) + B * y ^ 2) ∂volume ≤ ∫ y, U y ∂volume :=
        integral_mono hD_int hU_int hle
      have hI0 : ∫ y, q (y - c) ∂volume = 1 := by
        rw [integral_sub_right_eq_self (fun y => q y) c, hq_mass]
      have hI2 : ∫ y, (y - c) ^ 2 * q (y - c) ∂volume = M2 := by
        rw [integral_sub_right_eq_self (fun y => y ^ 2 * q y) c, ← hM2]
      have hUsplit : ∫ y, U y ∂volume
          = (A + 1) * (∫ y, q (y - c) ∂volume)
            + 2 * B * (∫ y, (y - c) ^ 2 * q (y - c) ∂volume)
            + 2 * B * c ^ 2 * (∫ y, q (y - c) ∂volume) := by
        show ∫ y, ((A + 1) * q (y - c) + 2 * B * ((y - c) ^ 2 * q (y - c))
            + 2 * B * c ^ 2 * q (y - c)) ∂volume = _
        rw [integral_add
            (f := fun y => (A + 1) * q (y - c) + 2 * B * ((y - c) ^ 2 * q (y - c)))
            (g := fun y => 2 * B * c ^ 2 * q (y - c))
            ((hT0.const_mul (A + 1)).add (hT2.const_mul (2 * B)))
            (hT0.const_mul (2 * B * c ^ 2)),
          integral_add
            (f := fun y => (A + 1) * q (y - c))
            (g := fun y => 2 * B * ((y - c) ^ 2 * q (y - c)))
            (hT0.const_mul (A + 1)) (hT2.const_mul (2 * B)),
          integral_const_mul, integral_const_mul, integral_const_mul]
      rw [hICabs, hHabs]
      rw [hUsplit, hI0, hI2] at hIDle
      nlinarith [hIDle, hc2]
    exact le_trans hF_le hI_eval

end InformationTheory.Shannon
