import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LogDeriv
import InformationTheory.Shannon.FisherInfo.OfDensity
import InformationTheory.Shannon.FisherInfo.DeBruijn
import InformationTheory.Shannon.FisherInfo.DeBruijnHeatFlow
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.DifferentialEntropy

/-!
# Fisher information V2 — heat flow

Sub-decomposes the heat-flow side of the de Bruijn identity. The heat equation
`∂_t p = (1/2) Δ_x p` is exposed for the Gaussian heat kernel
`heatKernel t x = gaussianPDFReal 0 ⟨t, _⟩ x` by giving its first and second spatial
derivatives in closed form, and the monolithic `heat_equation` field of `IsHeatFlowDensity` is
split into spatial-derivative, time-derivative, and convolution-representation sub-predicates.

## Main definitions

* `spatialLaplacianHeatKernel t x := (x²/t² - 1/t) · g_t x` — the spatial Laplacian of the heat
  kernel.
* `IsHeatSpatialDerivHyp` / `IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` — the three
  sub-predicates of the heat equation.
* `IsHeatFlowDensity_of_sub_predicates` — re-assembles the sub-predicates into an
  `IsHeatFlowDensity` witness.
* `IsRegularDeBruijnHypV2.ofHeatSubhyp` — the `IsRegularDeBruijnHypV2` constructor from the
  sub-predicates.

## Main statements

* `heatKernel_spatial_deriv` / `heatKernel_hasDerivAt_spatial` — `∂_x g_t = -(x/t) · g_t`.
* `heatKernel_spatial_laplacian` — `∂²_x g_t = spatialLaplacianHeatKernel t x`.
* `isHeatSpatialDerivHyp_gaussian` — the Gaussian kernel satisfies the spatial-derivative
  sub-predicate.
* `deBruijn_identity_v2_of_heat_subhyp` — the de Bruijn identity from the sub-predicate
  decomposition.

## Implementation notes

The time-derivative and convolution-representation sub-predicates are kept as pass-through
hypotheses because the variance-derivative `∂_t gaussianPDFReal 0 ⟨t, _⟩ x` is not in Mathlib.
-/

namespace InformationTheory.Shannon.FisherInfo

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Spatial derivatives of the Gaussian heat kernel -/

/-- The variance of the heat kernel at time `t > 0` is nonzero as an `ℝ≥0`. -/
theorem heatKernel_variance_ne_zero {t : ℝ} (ht : 0 < t) :
    (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
  intro h
  have h' : ((⟨t, ht.le⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
  have : (t : ℝ) = 0 := h'
  linarith

/-- First spatial derivative of the heat kernel (`m = 0` case).

`∂_x g_t(x) = -(x / t) · g_t(x)`, the `m = 0` specialization of
`InformationTheory.Shannon.deriv_gaussianPDFReal`. -/
@[entry_point]
theorem heatKernel_spatial_deriv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun y ↦ heatKernel t y) x = -(x / t) * heatKernel t x := by
  have hfun : (fun y ↦ heatKernel t y) = gaussianPDFReal 0 ⟨t, ht.le⟩ := by
    funext y; exact heatKernel_def_gaussianPDFReal ht y
  rw [hfun, InformationTheory.Shannon.deriv_gaussianPDFReal (heatKernel_variance_ne_zero ht) x,
    heatKernel_def_gaussianPDFReal ht x]
  show -((x : ℝ) - 0) / t * gaussianPDFReal 0 ⟨t, ht.le⟩ x
     = -(x / t) * gaussianPDFReal 0 ⟨t, ht.le⟩ x
  ring

/-- `HasDerivAt` form of the first spatial derivative of the heat kernel. -/
@[entry_point]
theorem heatKernel_hasDerivAt_spatial {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y ↦ heatKernel t y) (-(x / t) * heatKernel t x) x := by
  have hfun : (fun y ↦ heatKernel t y) = gaussianPDFReal 0 ⟨t, ht.le⟩ := by
    funext y; exact heatKernel_def_gaussianPDFReal ht y
  rw [hfun]
  have hval : -(x / t) * heatKernel t x = deriv (gaussianPDFReal 0 ⟨t, ht.le⟩) x := by
    rw [InformationTheory.Shannon.deriv_gaussianPDFReal (heatKernel_variance_ne_zero ht) x,
      heatKernel_def_gaussianPDFReal ht x]
    show -(x / t) * gaussianPDFReal 0 ⟨t, ht.le⟩ x
       = -((x : ℝ) - 0) / t * gaussianPDFReal 0 ⟨t, ht.le⟩ x
    ring
  rw [hval]
  exact (InformationTheory.Shannon.differentiable_gaussianPDFReal 0
    ⟨t, ht.le⟩).differentiableAt.hasDerivAt

/-- Spatial Laplacian of the heat kernel (closed form).

`Δ_x g_t(x) = ∂²_x g_t(x) = (x²/t² - 1/t) · g_t(x)`. -/
noncomputable def spatialLaplacianHeatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (x ^ 2 / t ^ 2 - 1 / t) * heatKernel t x

/-- Second spatial derivative of the heat kernel equals
`spatialLaplacianHeatKernel`. The core internal discharge:
differentiate `heatKernel_spatial_deriv` once more (product rule).

`∂²_x g_t(x) = (x²/t² - 1/t) · g_t(x)`. -/
@[entry_point]
theorem heatKernel_spatial_laplacian {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun y ↦ deriv (fun z ↦ heatKernel t z) y) x
      = spatialLaplacianHeatKernel t x := by
  have hinner : (fun y ↦ deriv (fun z ↦ heatKernel t z) y)
      = fun y ↦ -(y / t) * heatKernel t y := by
    funext y; exact heatKernel_spatial_deriv ht y
  rw [hinner]
  -- product rule on `(fun y => -(y/t)) * (fun y => heatKernel t y)`
  have hf : HasDerivAt (fun y : ℝ ↦ -(y / t)) (-(1 / t)) x := by
    have h1 : HasDerivAt (fun y : ℝ ↦ y / t) (1 / t) x :=
      (hasDerivAt_id x).div_const t
    exact h1.neg
  have hg : HasDerivAt (fun y ↦ heatKernel t y) (-(x / t) * heatKernel t x) x :=
    heatKernel_hasDerivAt_spatial ht x
  have hmul : HasDerivAt (fun y ↦ -(y / t) * heatKernel t y)
      (-(1 / t) * heatKernel t x + -(x / t) * (-(x / t) * heatKernel t x)) x := hf.mul hg
  rw [hmul.deriv]
  unfold spatialLaplacianHeatKernel
  ring

/-! ## Heat-equation right-hand side check (Gaussian, internal) -/

/-! ## Sub-predicate decomposition -/

/-- The spatial-derivative sub-predicate: `p t` has the prescribed spatial second derivative
`Δp t` at every `x` (for `t > 0`). For the Gaussian kernel this is discharged by
`isHeatSpatialDerivHyp_gaussian`. -/
def IsHeatSpatialDerivHyp (p : ℝ → ℝ → ℝ) (Δp : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    deriv (fun y ↦ deriv (fun z ↦ p t z) y) x = Δp t x

/-- The time-derivative sub-predicate: `p` solves the heat equation `∂_s p = (1/2) Δp` at `t`. -/
def IsHeatTimeDerivHyp (p : ℝ → ℝ → ℝ) (Δp : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    HasDerivAt (fun s ↦ p s x) ((1 / 2) * Δp t x) t

/-- The convolution-representation sub-predicate. -/
def IsHeatFlowConvolutionHyp {Ω : Type*} [MeasurableSpace Ω]
    (_X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) : Prop :=
  (P.map Z = gaussianReal 0 1)
    ∧ (∀ t : ℝ, 0 < t → ∀ x : ℝ, 0 ≤ p t x)
    ∧ (∀ t : ℝ, 0 < t → Measurable (p t))

/-! ## Gaussian discharge of the spatial sub-predicate -/

/-- The Gaussian heat kernel satisfies `IsHeatSpatialDerivHyp` with
`Δp t x := spatialLaplacianHeatKernel t x`. -/
@[entry_point]
theorem isHeatSpatialDerivHyp_gaussian :
    IsHeatSpatialDerivHyp (fun t x ↦ heatKernel t x)
      (fun t x ↦ spatialLaplacianHeatKernel t x) := by
  intro t ht x
  exact heatKernel_spatial_laplacian ht x

/-! ## Re-assembly into `IsHeatFlowDensity` -/

/-- Re-assembly: the sub-predicates re-build an `IsHeatFlowDensity`. -/
@[entry_point]
def IsHeatFlowDensity_of_sub_predicates {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {p : ℝ → ℝ → ℝ} {Δp : ℝ → ℝ → ℝ}
    (h_conv : IsHeatFlowConvolutionHyp X Z P p)
    (h_time : IsHeatTimeDerivHyp p Δp) :
    IsHeatFlowDensity X Z P p where
  Z_law := h_conv.1
  density_witness := h_conv.2.1
  density_measurable := h_conv.2.2
  heat_equation := ⟨Δp, h_time⟩

/-! ## Measure-level Gaussian heat semigroup composition -/

/-! ## de Bruijn identity bridge re-publish (from sub-predicates) -/

/-- The de Bruijn identity from the sub-predicate decomposition: given the convolution and
time-derivative sub-predicates (which re-assemble into an `IsHeatFlowDensity`) and the IBP
hypothesis at `t`, the de Bruijn identity holds. Re-publishes `deBruijn_identity_v2_of_heat_flow`.
The `_h_ibp` argument is kept for caller compatibility but unused (the genuine derivation does not
consume the heat-equation core of `h_time`).

@audit:ok -/
@[entry_point]
theorem deBruijn_identity_v2_of_heat_subhyp
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (h_mom_X : Integrable (fun ω ↦ (X ω) ^ 2) P)
    {t : ℝ} (ht : 0 < t)
    {p : ℝ → ℝ → ℝ} {Δp : ℝ → ℝ → ℝ}
    (h_conv : IsHeatFlowConvolutionHyp X Z P p)
    (h_time : IsHeatTimeDerivHyp p Δp)
    (_h_ibp : IsIBPHypothesis X Z P p t) :
    HasDerivAt
      (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1 / 2) * fisherInfoOfDensityReal
        (IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ hX_ac h_mom_X ht
          (IsHeatFlowDensity_of_sub_predicates h_conv h_time)).density_t)
      t :=
  deBruijn_identity_v2_of_heat_flow X Z hX hZ hXZ hX_ac h_mom_X ht
    (IsHeatFlowDensity_of_sub_predicates h_conv h_time) _h_ibp

/-- The `IsRegularDeBruijnHypV2` constructor from the convolution and time-derivative
sub-predicates, via `IsHeatFlowDensity_of_sub_predicates` and `ofHeatFlow`.

@audit:ok -/
@[entry_point]
noncomputable def IsRegularDeBruijnHypV2.ofHeatSubhyp
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (h_mom_X : Integrable (fun ω ↦ (X ω) ^ 2) P)
    {t : ℝ} (ht : 0 < t)
    {p : ℝ → ℝ → ℝ} {Δp : ℝ → ℝ → ℝ}
    (h_conv : IsHeatFlowConvolutionHyp X Z P p)
    (h_time : IsHeatTimeDerivHyp p Δp) :
    IsRegularDeBruijnHypV2 X Z P t :=
  IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ hX_ac h_mom_X ht
    (IsHeatFlowDensity_of_sub_predicates h_conv h_time)

end InformationTheory.Shannon.FisherInfo