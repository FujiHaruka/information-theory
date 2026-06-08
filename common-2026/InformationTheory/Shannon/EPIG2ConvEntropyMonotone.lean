import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Composition.Lemmas
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfo.V2DeBruijnPerTime
import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.EPIG2BridgeDensityHelpers

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

## Status — fully closed (0 sorry / 0 residual, sorryAx-free)

The whole (β) chain is now **genuinely closed**. The former `wall:cond-diff-entropy`
bridge `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` is assembled
from three genuinely-proved components:

* (a) `InformationTheory.klDiv_compProd_const_toReal_integral` (`CondKLIntegral.lean`,
  which fills the Mathlib `ChainRule.lean:74-77` TODO) turns the joint KL `toReal` into
  the `μ_Z`-average of fibrewise KL `∫ z, (klDiv (κ z) μ_X).toReal ∂μ_Z`;
* (b) `klDiv_toReal_eq_neg_differentialEntropy_sub_cross` (`EPIG2BridgeDensityHelpers.lean`)
  expands each fibre into `−h(κ z) − ∫ p_z · log q_X`;
* (c) `integral_condDistrib_density_marginal_eq` (`EPIG2BridgeDensityHelpers.lean`)
  identifies the `μ_Z`-average of the cross term with `∫ q_X · log q_X = −h(μ_X)` (Fubini
  marginal).

Assembling (a)+(b)+(c) gives `RHS = −h(X|Z) − (−h(X)) = h(X) − h(X|Z)`, the bridge.
`condDifferentialEntropy_le` then follows by `ENNReal.toReal_nonneg`. The regularity /
integrability preconditions (joint `≪`, per-fibre `≪`, the `μ_Z`-integrability of the
fibre entropy and the cross term, the marginal log-density integrability) are threaded
through as honest preconditions (absolute continuity / KL finiteness), not load-bearing
bundles; the downstream device form `differentialEntropy_indep_gaussian_add_ge` and
density form `negMulLog_convDensity_entropy_ge` thread them at the heat-flow path
`W := X + √s·Z` with conclusions unchanged.

`condDifferentialEntropy_indep_add_eq` (independent-sum fibre identification) was already
genuinely closed via the affine-shift kernel `affineShiftKernel`. All declarations here
are now sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
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

/-- **Differential mutual information as a Kullback-Leibler divergence**:

  `h(X) − h(X | Z) = KL(joint ‖ product).toReal`,

where `joint := (μ.map Z) ⊗ₘ condDistrib X Z μ` (the law of `(Z, X)`, by
`compProd_map_condDistrib`) and `product := (μ.map Z) ⊗ₘ Kernel.const _ (μ.map X)`
(`= (μ.map Z).prod (μ.map X)`, by `Measure.compProd_const`). This is the
differential-entropy-level statement of `I(X;Z) = h(X) − h(X|Z)`.

**Genuinely closed** (0 sorry / 0 residual, sorryAx-free), assembled from three
genuinely-proved components, with the regularity / integrability hypotheses threaded
as honest preconditions:

* (a) `InformationTheory.klDiv_compProd_const_toReal_integral` (`CondKLIntegral.lean`,
  filling the Mathlib `ChainRule.lean:74-77` TODO) turns the joint KL `toReal` into the
  `μ_Z`-average of the fibrewise KL `∫ z, (klDiv (κ z) μ_X).toReal ∂μ_Z`;
* (b) `klDiv_toReal_eq_neg_differentialEntropy_sub_cross`
  (`EPIG2BridgeDensityHelpers.lean`) expands each fibre into
  `−h(κ z) − ∫ p_z · log q_X`;
* (c) `integral_condDistrib_density_marginal_eq` (`EPIG2BridgeDensityHelpers.lean`)
  identifies `∫_z ∫ p_z log q_X ∂μ_Z = ∫ q_X log q_X = −h(μ_X)` (Fubini marginal).

Assembling: `RHS = −h(X|Z) − (−h(X)) = h(X) − h(X|Z)`. The classical continuous
`I(X;Z) = h(X) − h(X|Z) = D(P_{Z,X} ‖ P_Z ⊗ P_X)` identity, now genuine in-tree.

All added hypotheses are regularity preconditions (absolute continuity, per-fibre
absolute continuity, equal mass via Markov, integrability = KL finiteness), not
load-bearing bundles. The equal-mass condition `κ z univ = μ_X univ` is discharged
internally (both probability measures). `@audit:ok` -/
theorem differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    -- (a) joint absolute continuity + joint llr integrability
    (h_ac : (μ.map Z) ⊗ₘ condDistrib X Z μ ≪ (μ.map Z) ⊗ₘ Kernel.const α (μ.map X))
    (h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib X Z μ) ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X)))
      ((μ.map Z) ⊗ₘ condDistrib X Z μ))
    -- (b) per-fibre regularity (a.e. `z`)
    (hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib X Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume)
    -- outer `μ_Z`-integrability of the two split pieces
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib X Z μ z)) (μ.map Z))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) (μ.map Z))
    -- (c) marginal log-density integrability
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map X).rnDeriv volume x).toReal)) (μ.map X)) :
    differentialEntropy (μ.map X) - condDifferentialEntropy X Z μ
      = (klDiv ((μ.map Z) ⊗ₘ condDistrib X Z μ)
          ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))).toReal := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set μZ := μ.map Z with hμZ
  set κ := condDistrib X Z μ with hκ
  set ν := μ.map X with hν
  -- a.e. fibrewise absolute continuity `κ z ≪ ν`, from the joint absolute continuity.
  have hκν : ∀ᵐ z ∂μZ, κ z ≪ Kernel.const α ν z := by
    have := Measure.absolutelyContinuous_compProd_right_iff.mp h_ac
    simpa using this
  have hκν' : ∀ᵐ z ∂μZ, κ z ≪ ν := by
    filter_upwards [hκν] with z hz; simpa using hz
  -- (a): RHS = `∫ z, (klDiv (κ z) ν).toReal ∂μZ`.
  have hstepA : (klDiv (μZ ⊗ₘ κ) (μZ ⊗ₘ Kernel.const α ν)).toReal
      = ∫ z, (klDiv (κ z) ν).toReal ∂μZ :=
    InformationTheory.klDiv_compProd_const_toReal_integral h_ac h_int
  -- (b): per-fibre, `(klDiv (κ z) ν).toReal = −h(κ z) − cross_z`.
  have hstepB : ∀ᵐ z ∂μZ, (klDiv (κ z) ν).toReal
      = - differentialEntropy (κ z)
        - ∫ x, ((κ z).rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal) ∂volume := by
    filter_upwards [hκ_v, hκν', hκ_logp_int, hκ_cross_int] with z hzv hzν hzlogp hzcross
    have hmass : (κ z) Set.univ = ν Set.univ := by
      rw [measure_univ, measure_univ]
    exact klDiv_toReal_eq_neg_differentialEntropy_sub_cross (κ z) ν hzv hX_ac hzν hmass
      hzlogp hzcross
  -- Average (b) over `μZ` and split the integral.
  have hstepBint : ∫ z, (klDiv (κ z) ν).toReal ∂μZ
      = - condDifferentialEntropy X Z μ
        - ∫ z, (∫ x, ((κ z).rnDeriv volume x).toReal
              * Real.log ((ν.rnDeriv volume x).toReal) ∂volume) ∂μZ := by
    rw [integral_congr_ae hstepB]
    have hsplit : ∫ z, (- differentialEntropy (κ z)
            - ∫ x, ((κ z).rnDeriv volume x).toReal
                * Real.log ((ν.rnDeriv volume x).toReal) ∂volume) ∂μZ
        = (∫ z, - differentialEntropy (κ z) ∂μZ)
          - ∫ z, (∫ x, ((κ z).rnDeriv volume x).toReal
                * Real.log ((ν.rnDeriv volume x).toReal) ∂volume) ∂μZ :=
      integral_sub h_fibreEnt_int.neg h_cross_int
    rw [hsplit, integral_neg]
    rfl
  -- (c): `∫_z cross_z ∂μZ = ∫ x, qX·log qX = −h(ν)`.
  have hstepC : ∫ z, (∫ x, ((κ z).rnDeriv volume x).toReal
              * Real.log ((ν.rnDeriv volume x).toReal) ∂volume) ∂μZ
      = ∫ x, (ν.rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal) ∂volume :=
    integral_condDistrib_density_marginal_eq X Z μ hX hZ hX_ac hκ_v h_logq_int
  -- `h(ν) = −∫ qX·log qX`.
  have hent : differentialEntropy ν
      = - ∫ x, (ν.rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal) ∂volume := by
    unfold differentialEntropy
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.negMulLog_def]; ring
  -- Assemble.
  rw [hstepA, hstepBint, hstepC, hent]
  ring

/-- **Conditioning reduces (differential) entropy**: `h(X | Z) ≤ h(X)`.

The differential analogue of `I(X;Z) = h(X) − h(X|Z) = KL(joint ‖ product) ≥ 0`.
This proof is **genuine** (0 sorry / 0 residual, sorryAx-free): the bridge
`differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` identifies the entropy
difference with `(klDiv joint product).toReal`, whose non-negativity is type-trivial
(`ENNReal.toReal_nonneg`, since `klDiv` is `ℝ≥0∞`-valued), so the
conditioning-reduces-entropy inequality follows by `sub_nonneg`.

The hypotheses are all preconditions (regularity / absolute continuity / integrability =
KL finiteness), not load-bearing: `hX_ac : μ.map X ≪ volume` ensures `h(X)` reflects the
density, measurability is structural, and the bridge's regularity / integrability
preconditions are threaded through unchanged. `@audit:ok` -/
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib X Z μ ≪ (μ.map Z) ⊗ₘ Kernel.const α (μ.map X))
    (h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib X Z μ) ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X)))
      ((μ.map Z) ⊗ₘ condDistrib X Z μ))
    (hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib X Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib X Z μ z)) (μ.map Z))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) (μ.map Z))
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map X).rnDeriv volume x).toReal)) (μ.map X)) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X) := by
  have hbridge := differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv
    X Z μ hX hZ hX_ac h_ac h_int hκ_v hκ_logp_int hκ_cross_int h_fibreEnt_int
    h_cross_int h_logq_int
  have hnn : 0 ≤ differentialEntropy (μ.map X) - condDifferentialEntropy X Z μ := by
    rw [hbridge]; exact ENNReal.toReal_nonneg
  linarith

/-- The z-dependent affine-shift kernel `κ z := νX.map (· + c·z)`, built as a genuine
`Kernel ℝ ℝ`. Construction: push the parametrised pairing `z ↦ νX.map (Prod.mk z)`
(measurable by `Measurable.map_prodMk_left`) through the measurable affine map
`(z, x) ↦ x + c·z`.

@audit:ok -/
noncomputable def affineShiftKernel (νX : Measure ℝ) [SFinite νX] (c : ℝ) : Kernel ℝ ℝ where
  toFun z := νX.map (fun x => x + c * z)
  measurable' := by
    have h1 : Measurable fun z : ℝ => νX.map (Prod.mk z) :=
      Measurable.map_prodMk_left (ν := νX)
    have h2 : Measurable fun p : ℝ × ℝ => p.2 + c * p.1 := by fun_prop
    have heq : (fun z : ℝ => νX.map (fun x => x + c * z))
        = fun z : ℝ => (νX.map (Prod.mk z)).map (fun p : ℝ × ℝ => p.2 + c * p.1) := by
      funext z
      rw [Measure.map_map h2 measurable_prodMk_left]
      rfl
    rw [heq]
    exact (Measure.measurable_map _ h2).comp h1

@[simp]
lemma affineShiftKernel_apply (νX : Measure ℝ) [SFinite νX] (c z : ℝ) :
    affineShiftKernel νX c z = νX.map (fun x => x + c * z) := rfl

instance affineShiftKernel.instIsMarkov (νX : Measure ℝ) [IsProbabilityMeasure νX] (c : ℝ) :
    IsMarkovKernel (affineShiftKernel νX c) := by
  refine ⟨fun z => ?_⟩
  rw [affineShiftKernel_apply]
  have : Measurable fun x : ℝ => x + c * z := by fun_prop
  exact Measure.isProbabilityMeasure_map this.aemeasurable

/-- Plumbing core (buildable, **not** a Mathlib wall): the pushforward of the product
measure `νZ ⊗ νX` through the affine map `g (z, x) = (z, x + c·z)` equals the composition
product of `νZ` with the z-dependent affine-shift kernel `affineShiftKernel νX c`.

@audit:ok -/
theorem prod_map_affine_eq_compProd
    (νZ νX : Measure ℝ) [SFinite νZ] [IsProbabilityMeasure νX] (c : ℝ) :
    (νZ.prod νX).map (fun p : ℝ × ℝ => (p.1, p.2 + c * p.1))
      = νZ ⊗ₘ (affineShiftKernel νX c) := by
  have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + c * p.1) := by fun_prop
  ext s hs
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr fun z => ?_
  rw [affineShiftKernel_apply]
  have hshift : Measurable fun x : ℝ => x + c * z := by fun_prop
  rw [Measure.map_apply hshift (measurable_prodMk_left hs)]
  congr 1

/-- **Independent-sum fibre identification**: for `X ⊥ Z`,
`h(X + c·Z | Z) = h(X)`.

Conditioned on `Z = z`, the variable `fun ω => X ω + c · Z ω` is the constant shift
`X + c·z`, whose differential entropy equals `h(X)` by translation invariance
(`differentialEntropy_map_add_const`). Averaging the constant `h(X)` over the
probability law `μ.map Z` reproduces `h(X)`.

**Genuine (0 sorry / 0 residual)**, sorryAx-free. The fibre identification
`condDistrib (X + c·Z) Z μ =ᵐ[μ.map Z] affineShiftKernel (μ.map X) c` is assembled
in-tree via:

1. `indepFun_iff_map_prod_eq_prod_map_map` gives
   `μ.map (fun ω => (Z ω, X ω)) = (μ.map Z).prod (μ.map X)` (independence).
2. Push the product through the affine map `g (z, x) = (z, x + c·z)` and identify it
   with `(μ.map Z) ⊗ₘ (affineShiftKernel (μ.map X) c)` (`prod_map_affine_eq_compProd`,
   the z-dependent affine-shift kernel built genuinely above).
3. `condDistrib_ae_eq_of_measure_eq_compProd` then gives the fibre identification, and
   `differentialEntropy_map_add_const` discharges each fibre to `h(μ.map X)`.

The hypotheses are all preconditions: `IndepFun X Z μ` is a genuine independence
precondition (not a load-bearing bundle), `hX_ac` is absolute continuity, measurability
is structural.

@audit:ok -/
theorem condDifferentialEntropy_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropy (μ.map X) := by
  set W : Ω → ℝ := fun ω => X ω + c * Z ω with hW_def
  have hW : Measurable W := hX.add ((measurable_const).mul hZ)
  -- Output and conditioning laws are probability measures.
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hsf : SigmaFinite (μ.map X) := inferInstance
  -- Step 1: joint `(Z, X)` is the product law (independence).
  have hZX : IndepFun Z X μ := hXZ.symm
  have hjoint_ZX : μ.map (fun ω => (Z ω, X ω)) = (μ.map Z).prod (μ.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hX.aemeasurable).mp hZX
  -- Step 1': push the product through the affine map `g (z, x) = (z, x + c·z)`.
  have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + c * p.1) := by fun_prop
  have hjoint_ZW : μ.map (fun ω => (Z ω, W ω))
      = (μ.map Z) ⊗ₘ (affineShiftKernel (μ.map X) c) := by
    have hcomp : (fun ω => (Z ω, W ω))
        = (fun p : ℝ × ℝ => (p.1, p.2 + c * p.1)) ∘ (fun ω => (Z ω, X ω)) := by
      funext ω; simp [hW_def]
    rw [hcomp, ← Measure.map_map hg (hZ.prodMk hX), hjoint_ZX,
      prod_map_affine_eq_compProd]
  -- Step 2: uniqueness of the regular conditional distribution.
  have hae : condDistrib W Z μ =ᵐ[μ.map Z] affineShiftKernel (μ.map X) c :=
    condDistrib_ae_eq_of_measure_eq_compProd Z hW.aemeasurable hjoint_ZW
  -- Step 3: rewrite the fibre integral, then apply translation invariance fibrewise.
  unfold condDifferentialEntropy
  rw [integral_congr_ae (g := fun _ => differentialEntropy (μ.map X)) ?_]
  · rw [integral_const, probReal_univ, one_smul]
  · filter_upwards [hae] with z hz
    rw [hz, affineShiftKernel_apply]
    exact differentialEntropy_map_add_const hX_ac (c * z)

set_option linter.unusedVariables false in
/-- **(β) device form** — convolution does not decrease differential entropy,
stated through an underlying independent pair `X ⊥ Z` with `Z` Gaussian.

`h(X) ≤ h(X + √s·Z)` via the chain `h(X) = h(X+√s·Z | Z) ≤ h(X+√s·Z)`
(`condDifferentialEntropy_indep_add_eq` + `condDifferentialEntropy_le`).

All hypotheses are regularity preconditions (the fields of
`IsHeatFlowEndpointRegular`): measurability, independence, the noise law, and the
absolute continuity of `μ.map X`. The bridge regularity / integrability preconditions
(stated at the heat-flow path `W := X + √s·Z`) are threaded through unchanged. **Genuine**
(0 sorry / 0 residual, sorryAx-free): `condDifferentialEntropy_le` is now genuinely
closed. `@audit:ok` -/
theorem differentialEntropy_indep_gaussian_add_ge
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℝ) (hs : 0 < s)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume)
    (hW_ac : (μ.map (fun ω => X ω + Real.sqrt s * Z ω)) ≪ volume)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ
        ≪ (μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map (fun ω => X ω + Real.sqrt s * Z ω)))
    (h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ)
        ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map (fun ω => X ω + Real.sqrt s * Z ω))))
      ((μ.map Z) ⊗ₘ condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ))
    (hκ_v : ∀ᵐ z ∂(μ.map Z),
      condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map (fun ω => X ω + Real.sqrt s * Z ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ z)) (μ.map Z))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Real.sqrt s * Z ω) Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map (fun ω => X ω + Real.sqrt s * Z ω)).rnDeriv volume x).toReal) ∂volume) (μ.map Z))
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map (fun ω => X ω + Real.sqrt s * Z ω)).rnDeriv volume x).toReal))
      (μ.map (fun ω => X ω + Real.sqrt s * Z ω))) :
    differentialEntropy (μ.map X)
      ≤ differentialEntropy (μ.map (fun ω => X ω + Real.sqrt s * Z ω)) := by
  -- `W := X + √s·Z`. Conditioning on `Z` reduces entropy, and the fibre is `h(X)`.
  set W : Ω → ℝ := fun ω => X ω + Real.sqrt s * Z ω with hW
  have hW_meas : Measurable W := hX.add ((measurable_const).mul hZ)
  have h_fibre : condDifferentialEntropy W Z μ = differentialEntropy (μ.map X) :=
    condDifferentialEntropy_indep_add_eq X Z μ (Real.sqrt s) hX hZ hXZ hX_ac
  have h_le : condDifferentialEntropy W Z μ ≤ differentialEntropy (μ.map W) :=
    condDifferentialEntropy_le W Z μ hW_meas hZ hW_ac h_ac h_int hκ_v hκ_logp_int
      hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
  rw [← h_fibre]
  exact h_le

/-- **(β) density form** — the target consumed by the EPI G2 sandwich layer-2.

Convolution with a Gaussian does not decrease the `negMulLog` entropy integral:
`∫ negMulLog pX ≤ ∫ negMulLog (pX ∗ g_{u n})`. Equivalently `h(pX) ≤ h(pX ∗ g_t)`.

The underlying independent pair `X ⊥ Z` (with `Z ∼ 𝒩(0, v_Z)`, `s·v_Z = u n`) is
supplied as regularity preconditions, matching the fields of
`IsHeatFlowEndpointRegular`. `pX` is identified with the density of `μ.map X`.
The bridge regularity / integrability preconditions (stated at the heat-flow path
`W := X + √s·Z` with `s := u n / v_Z`) are threaded through unchanged. **Genuine**
(0 sorry / 0 residual, sorryAx-free): `condDifferentialEntropy_le` is now genuinely
closed. `@audit:ok` -/
theorem negMulLog_convDensity_entropy_ge
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (v_Z : ℝ≥0) (hv_Z_pos : 0 < v_Z) (hZ_law : μ.map Z = gaussianReal 0 v_Z)
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : μ.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (n : ℕ)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ
        ≪ (μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω)))
    (h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ)
        ((μ.map Z) ⊗ₘ Kernel.const ℝ (μ.map (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω))))
      ((μ.map Z) ⊗ₘ condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ))
    (hκ_v : ∀ᵐ z ∂(μ.map Z),
      condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ z)) (μ.map Z))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω) Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω)).rnDeriv volume x).toReal) ∂volume) (μ.map Z))
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω)).rnDeriv volume x).toReal))
      (μ.map (fun ω => X ω + Real.sqrt (u n / (v_Z:ℝ)) * Z ω))) :
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
      h_ac h_int hκ_v hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
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
