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

* `condDifferentialEntropy_indep_add_eq` (independent-sum fibre identification) is
  **genuinely closed** (0 sorry / 0 residual, sorryAx-free): the affine-shift kernel
  `affineShiftKernel` is built in-tree, the compProd identity `prod_map_affine_eq_compProd`
  is proved by `compProd_apply`/`prod_apply`/`map_apply`, and the fibre identification
  follows from `condDistrib_ae_eq_of_measure_eq_compProd` + `differentialEntropy_map_add_const`.
  The in-tree inventory (`epi-g2-cond-diff-entropy-inventory.md`) flagged this lemma as
  *buildable* (mis-classified as a wall); this closure resolves that — it carries no
  `@residual` tag.

* `condDifferentialEntropy_le` (conditioning reduces entropy) is now **genuine modulo
  a single bridge lemma**. The non-negativity step is genuinely proved here: the entropy
  difference `h(X) − h(X|Z)` is identified with `(klDiv joint product).toReal`, which is
  `≥ 0` by `ENNReal.toReal_nonneg` (`klDiv` is `ℝ≥0∞`-valued), so `h(X|Z) ≤ h(X)` follows
  by `sub_nonneg`/`linarith`. The remaining `sorry` is isolated in the bridge lemma
  `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv`, which carries
  `@residual(wall:cond-diff-entropy)`. `condDifferentialEntropy_le` inherits the tag
  transitively (own body sorry-free apart from the bridge call).

  The parked content is the differential-MI = KL identity
  `h(X) − h(X|Z) = (klDiv (μ_Z ⊗ₘ condDistrib X Z μ) (μ_Z ⊗ₘ const (μ.map X))).toReal`.
  The continuous `mutualInfo` concept is absent from Mathlib (loogle `mutualInfo` =
  Found 0, `klDiv ∩ condDistrib` = Found 0, re-confirmed 2026-06-04), and the bridge
  reduces to the **conditional-KL integral form**
  `(klDiv (μ_Z ⊗ₘ κ) (μ_Z ⊗ₘ const μ_X)).toReal = ∫ z, (klDiv (κ z) μ_X).toReal ∂μ_Z` —
  an explicit unaddressed Mathlib TODO (`KullbackLeibler.ChainRule.lean:74-77`). Note the
  in-tree chain rule `klDiv_compProd_eq_add` decomposes the *first* marginal, which is
  `μ_Z` on both sides here, so it collapses to the trivial `0 + KL`; the genuine content
  is exactly the absent integral-form conditional KL plus the per-fibre density expansion
  `(klDiv (κ z) μ_X).toReal = −h(κ z) − ∫ p_z log q_X` and a Fubini marginal identification
  (estimated ~150-300 lines = a separate Phase).

The `wall:` class here means "Mathlib-absent obstruction requiring an in-tree
construction" (the project's `wall:` register sense, e.g. the now-closed
`fisher-finiteness` / `entropy-finiteness`), NOT "long-term moonshot". The obstruction
is closeable; `wall:` is chosen over `plan:` because this is a shared, EPI-line-wide /
textbook-wide reusable asset aggregated here as a shared sorry lemma, not a single-plan
deferral. Independent honesty audit 2026-06-04: classification confirmed (sorry-based
residual, signature honest, `IndepFun` a genuine precondition not a load-bearing bundle).
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

This is the single remaining gap of the conditioning-reduces-entropy route. The
structural reduction `condDifferentialEntropy_le ← klDiv ≥ 0` (type-trivial via
`ENNReal.toReal_nonneg`) is genuine and lives in `condDifferentialEntropy_le`; the
content parked here is the bridge converting `klDiv(joint ‖ product).toReal` into
the differential-entropy difference, which requires the **conditional-KL integral
form** `(klDiv (μ_Z ⊗ₘ κ) (μ_Z ⊗ₘ const μ_X)).toReal = ∫ z, (klDiv (κ z) μ_X).toReal ∂μ_Z`
— explicitly an unaddressed Mathlib TODO (`KullbackLeibler.ChainRule.lean:74-77`,
"Add a version of the chain rule for the integral form of the conditional KL
divergence") — followed by the per-fibre density expansion
`(klDiv (κ z) μ_X).toReal = −h(κ z) − ∫ p_z · log q_X` (needs `κ z ≪ volume` a.e. `z`,
from the disintegration) and a Fubini marginal identification
`∫_z ∫ p_z log q_X ∂μ_Z = ∫ q_X log q_X = −h(X)`. Estimated a separate ~150-300 line
Phase (the `klDiv_compProd_eq_add` chain rule decomposes the *first* marginal, which
here is `μ_Z` on both sides, so it collapses to the trivial `0 + KL`; the genuine
content is exactly the absent conditional-KL integral form).

All hypotheses are preconditions (regularity / absolute continuity), not load-bearing.

@residual(wall:cond-diff-entropy) -/
theorem differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) :
    differentialEntropy (μ.map X) - condDifferentialEntropy X Z μ
      = (klDiv ((μ.map Z) ⊗ₘ condDistrib X Z μ)
          ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))).toReal := by
  sorry

/-- **Conditioning reduces (differential) entropy**: `h(X | Z) ≤ h(X)`.

The differential analogue of `I(X;Z) = h(X) − h(X|Z) = KL(joint ‖ product) ≥ 0`.
This proof is **genuine** modulo the single bridge
`differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv`: once the entropy
difference is identified with `(klDiv joint product).toReal`, non-negativity is
type-trivial (`ENNReal.toReal_nonneg`, since `klDiv` is `ℝ≥0∞`-valued), so the
conditioning-reduces-entropy inequality follows by `sub_nonneg`. The remaining sorry
is inherited transitively from the bridge lemma (hence the `@residual` tag below).

The hypotheses are all preconditions (regularity / absolute continuity), not
load-bearing: `hX_ac : μ.map X ≪ volume` ensures `h(X)` reflects the density, and
measurability is structural.

Independent honesty audit 2026-06-04: `wall:cond-diff-entropy` classification
confirmed (loogle backstop: `mutualInfo` continuous absent, `condDistrib ∩ klDiv`
Found 0; `wall:` over `plan:` justified as a shared, EPI-line-wide reusable asset).
Signature honest: `hX_ac` is a genuine absolute-continuity precondition, not a
load-bearing bundle; conclusion is not vacuous.

@residual(wall:cond-diff-entropy) -/
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X) := by
  have hbridge := differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv
    X Z μ hX hZ hX_ac
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
absolute continuity of `μ.map X`. The own body is sorry-free; the only sorry is
inherited transitively from `condDifferentialEntropy_le` (hence the tag below, not
`@audit:ok`).

@residual(wall:cond-diff-entropy) -/
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
`IsHeatFlowEndpointRegular`. `pX` is identified with the density of `μ.map X`.
The own body is sorry-free; the only sorry is inherited transitively from
`condDifferentialEntropy_le` (hence the tag below, not `@audit:ok`).

@residual(wall:cond-diff-entropy) -/
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
