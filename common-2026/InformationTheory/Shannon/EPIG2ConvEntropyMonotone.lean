import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime

/-!
# EPI G2 — (β) Convolution does not decrease differential entropy

This file supplies the **lower bound** `h(pX) ≤ h(pX ∗ g_t)` of the EPI G2 general
sandwich (`docs/shannon/epi-g2-general-sandwich-moonshot-plan.md`, Phase 1 (β)):
the differential entropy of a Gaussian-smoothed density `convDensityAdd pX g_t`
(with `g_t = gaussianPDFReal 0 ⟨t,_⟩`) is at least the differential entropy of `pX`.

The mathematical route is the continuous **conditioning-reduces-entropy**
inequality, applied to `W := X + √t·Z` with `Z ⊥ X` a Gaussian:

  `h(X + √t·Z) ≥ h(X + √t·Z | Z) = h(X)`.

* The first `≥` is conditioning-reduces-entropy, `h(W|Z) ≤ h(W)`
  (`condDifferentialEntropy_le`), which is the differential analogue of
  `I(W;Z) = h(W) − h(W|Z) = KL(joint ‖ product) ≥ 0`.
* The equality `h(X + √t·Z | Z) = h(X)` is the independent-sum fibre identification
  (`condDifferentialEntropy_indep_add_eq`): conditioned on `Z = z`, the variable
  `X + √t·Z` is the constant shift `X + √t·z`, whose entropy equals `h(X)` by
  translation invariance (`differentialEntropy_map_add_const`).

`condDistrib` is the regular conditional probability distribution from Mathlib
(`ProbabilityTheory.condDistrib X Z μ` = conditional law of `X` given `Z`), so the
conditional differential entropy is defined Mathlib-shape:

  `condDifferentialEntropy X Z μ := ∫ z, differentialEntropy ((condDistrib X Z μ) z) ∂(μ.map Z)`.

This is a **reusable, EPI-line-wide asset**: continuous conditional differential
entropy + conditioning-reduces-entropy are absent from Mathlib (genuine gap, not a
wall), but the `condDistrib` machinery exists, so a genuine construction is possible.

## Residual status

`condDifferentialEntropy_le` (conditioning reduces entropy) carries
`@residual(wall:cond-diff-entropy)` — its genuine proof requires the differential
mutual-information non-negativity `I(W;Z) = KL(joint ‖ product) ≥ 0`, which is not
yet assembled in-tree at the differential-entropy level.

The `wall:` class here means "Mathlib-absent obstruction requiring an in-tree
construction" (the project's `wall:` register sense, e.g. the now-closed
`fisher-finiteness` / `entropy-finiteness`), NOT "long-term moonshot". The
obstruction is closeable (a genuine construction path is identified in the docstring
of `condDifferentialEntropy_indep_add_eq`); `wall:` is chosen over `plan:` because
this is a shared, EPI-line-wide / textbook-wide reusable asset aggregated here as a
shared sorry lemma, not a single-plan deferral. Independent honesty audit 2026-06-04:
classification confirmed (sorry-based residuals, signatures honest, `IndepFun` a
genuine precondition not a load-bearing bundle).
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Real

/-- **Continuous conditional differential entropy** `h(X | Z)`. Defined directly on
the Mathlib regular conditional distribution `condDistrib X Z μ` (the conditional law
of `X` given `Z`, a `Kernel α ℝ`): the fibre differential entropy
`differentialEntropy ((condDistrib X Z μ) z)` averaged over the law `μ.map Z` of `Z`.

Mathlib-shape: the textbook `∫_z h(X | Z = z) dμ_Z(z)` is realised through the
`condDistrib` disintegration so that `compProd_map_condDistrib` and
`differentialEntropy_map_add_const` are usable verbatim. -/
noncomputable def condDifferentialEntropy
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ] : ℝ :=
  ∫ z, differentialEntropy ((condDistrib X Z μ) z) ∂(μ.map Z)

/-- **Conditioning reduces (differential) entropy**: `h(X | Z) ≤ h(X)`.

The differential analogue of `I(X;Z) = h(X) − h(X|Z) = KL(joint ‖ product) ≥ 0`.
Mathlib has `condDistrib` and `klDiv` (the latter `ℝ≥0∞`-valued, so non-negative by
type), but the bridge `I(X;Z) = h(X) − h(X|Z)` at the differential-entropy level is
not assembled in-tree; this lemma is the genuine gap.

The hypotheses are all preconditions (regularity / absolute continuity), not
load-bearing: `hX_ac : μ.map X ≪ volume` ensures `h(X)` reflects the density, and
measurability is structural.

@residual(wall:cond-diff-entropy) -/
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X) := by
  sorry

/-- **Independent-sum fibre identification**: for `X ⊥ Z`,
`h(X + c·Z | Z) = h(X)`.

Conditioned on `Z = z`, the variable `fun ω => X ω + c · Z ω` is the constant shift
`X + c·z`, whose differential entropy equals `h(X)` by translation invariance
(`differentialEntropy_map_add_const`). Averaging the constant `h(X)` over the
probability law `μ.map Z` reproduces `h(X)`.

The mathematical content is genuine (the shift invariance + averaging-a-constant
are in-tree), but the **fibre identification**
`condDistrib (X + c·Z) Z μ z =ᵐ[μ.map Z] (μ.map X).map (· + c·z)` is the missing
in-tree step. The genuine construction path identified (for a follow-up closure):

1. `indepFun_iff_map_prod_eq_prod_map_map` gives
   `μ.map (fun ω => (Z ω, X ω + c·Z ω)) = ((μ.map Z).prod (μ.map X)).map g`
   with `g (z, x) = (z, x + c·z)` (push the product joint through the affine map).
2. Show `((μ.map Z).prod (μ.map X)).map g = (μ.map Z) ⊗ₘ κ` with the kernel
   `κ z := (μ.map X).map (· + c·z)` (compProd-vs-prod with an affine, conditioning-
   dependent reparametrisation; requires `κ` measurable as a `Kernel ℝ ℝ`).
3. `compProd_map_condDistrib` + `condDistrib_ae_eq_of_measure_eq_compProd` then give
   `condDistrib (X + c·Z) Z μ =ᵐ[μ.map Z] κ`.

Steps 2-3 need the kernel `κ` built with the affine shift measurable in `z` and the
compProd identity; this measure-theoretic plumbing is not yet in-tree.

@residual(wall:cond-diff-entropy) -/
theorem condDifferentialEntropy_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropy (μ.map X) := by
  sorry

set_option linter.unusedVariables false in
/-- **(β) device form** — convolution does not decrease differential entropy,
stated through an underlying independent pair `X ⊥ Z` with `Z` Gaussian.

`h(X) ≤ h(X + √s·Z)` via the chain `h(X) = h(X+√s·Z | Z) ≤ h(X+√s·Z)`
(`condDifferentialEntropy_indep_add_eq` + `condDifferentialEntropy_le`).

All hypotheses are regularity preconditions (the fields of
`IsHeatFlowEndpointRegular`): measurability, independence, the noise law, and the
absolute continuity of `μ.map X`. -/
theorem differentialEntropy_indep_gaussian_add_ge
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℝ) (hs : 0 < s)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume)
    (hW_ac : (μ.map (fun ω => X ω + Real.sqrt s * Z ω)) ≪ volume) :
    differentialEntropy (μ.map X)
      ≤ differentialEntropy (μ.map (fun ω => X ω + Real.sqrt s * Z ω)) := by
  -- `W := X + √s·Z`. Conditioning on `Z` reduces entropy, and the fibre is `h(X)`.
  set W : Ω → ℝ := fun ω => X ω + Real.sqrt s * Z ω with hW
  have hW_meas : Measurable W := hX.add ((measurable_const).mul hZ)
  have h_fibre : condDifferentialEntropy W Z μ = differentialEntropy (μ.map X) :=
    condDifferentialEntropy_indep_add_eq X Z μ (Real.sqrt s) hX hZ hXZ hX_ac
  have h_le : condDifferentialEntropy W Z μ ≤ differentialEntropy (μ.map W) :=
    condDifferentialEntropy_le W Z μ hW_meas hZ hW_ac
  rw [← h_fibre]
  exact h_le

/-- **(β) density form** — the target consumed by the EPI G2 sandwich layer-2.

Convolution with a Gaussian does not decrease the `negMulLog` entropy integral:
`∫ negMulLog pX ≤ ∫ negMulLog (pX ∗ g_{u n})`. Equivalently `h(pX) ≤ h(pX ∗ g_t)`.

The underlying independent pair `X ⊥ Z` (with `Z ∼ 𝒩(0, v_Z)`, `s·v_Z = u n`) is
supplied as regularity preconditions, matching the fields of
`IsHeatFlowEndpointRegular`. `pX` is identified with the density of `μ.map X`. -/
theorem negMulLog_convDensity_entropy_ge
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (v_Z : ℝ≥0) (hv_Z_pos : 0 < v_Z) (hZ_law : μ.map Z = gaussianReal 0 v_Z)
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : μ.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (n : ℕ) :
    (∫ x, Real.negMulLog (pX x) ∂volume)
      ≤ ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume := by
  -- Choose the heat-flow time `s := u n / v_Z`, so `s·v_Z = u n`.
  have hv_Z_pos' : (0 : ℝ) < v_Z := hv_Z_pos
  set s : ℝ := u n / (v_Z : ℝ) with hs_def
  have hs : 0 < s := div_pos (hu_pos n) hv_Z_pos'
  have hsv : s * (v_Z : ℝ) = u n := by
    rw [hs_def, div_mul_cancel₀ _ hv_Z_pos'.ne']
  -- The variance witness `⟨s·v_Z,_⟩ : ℝ≥0` agrees with `⟨u n,_⟩`.
  have hwit : (⟨s * (v_Z : ℝ), by positivity⟩ : ℝ≥0) = (⟨u n, (hu_pos n).le⟩ : ℝ≥0) := by
    apply NNReal.coe_injective; show s * (v_Z : ℝ) = u n; exact hsv
  -- Absolute continuity of `μ.map X` (a `withDensity`).
  have hX_ac : (μ.map X) ≪ volume := by
    rw [hpX_law]; exact withDensity_absolutelyContinuous _ _
  -- Law of the heat-flow path and its absolute continuity.
  set W : Ω → ℝ := fun ω => X ω + Real.sqrt s * Z ω with hW
  have hW_law : μ.map W = (μ.map X) ∗ gaussianReal 0 ⟨s * (v_Z : ℝ), by positivity⟩ :=
    InformationTheory.Shannon.FisherInfoV2.gaussianConvolution_law_conv
      X Z hX hZ hXZ v_Z hZ_law hs.le
  have hsv_ne : (⟨s * (v_Z : ℝ), by positivity⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact (mul_pos hs hv_Z_pos').ne' (congrArg NNReal.toReal h)
  have hW_ac : (μ.map W) ≪ volume := by
    rw [hW_law]
    exact Measure.conv_absolutelyContinuous
      (gaussianReal_absolutelyContinuous 0 hsv_ne)
  -- (β) device form: `h(μ.map X) ≤ h(μ.map W)`.
  have h_dev : differentialEntropy (μ.map X) ≤ differentialEntropy (μ.map W) :=
    differentialEntropy_indep_gaussian_add_ge X Z μ s hs hX hZ hXZ hX_ac hW_ac
  -- Rewrite LHS `h(μ.map X) = ∫ negMulLog pX`.
  have h_lhs : differentialEntropy (μ.map X) = ∫ x, Real.negMulLog (pX x) ∂volume := by
    rw [hpX_law, differentialEntropy_eq_integral_withDensity hpX_meas.ennreal_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hpX_nn x)]
  -- Rewrite RHS `h(μ.map W) = ∫ negMulLog (convDensityAdd pX g_{u n})`.
  have hrn := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
    X Z hX hZ hXZ v_Z hv_Z_pos hZ_law pX hpX_nn hpX_meas hpX_law hs
  have h_rhs : differentialEntropy (μ.map W)
      = ∫ x, Real.negMulLog
          (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x) ∂volume := by
    have hpath_eq : W = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s := rfl
    unfold differentialEntropy
    rw [hpath_eq]
    refine integral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal]
    · rw [hwit]
    · unfold convDensityAdd
      exact integral_nonneg fun y =>
        mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  rw [h_lhs, h_rhs] at h_dev
  exact h_dev

end InformationTheory.Shannon
