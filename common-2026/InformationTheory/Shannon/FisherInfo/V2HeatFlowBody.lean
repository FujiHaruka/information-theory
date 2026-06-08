import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LogDeriv
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.FisherInfo.V2DeBruijnBody
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.DifferentialEntropy

/-!
# Fisher information V2 — heat-flow body (W9-S5 / L-FV2DB-A sub-decomposition)

Wave-9 follow-up to `FisherInfoV2DeBruijnBody.lean` (wave-7). That file split the
de Bruijn body into two pass-through predicates:

* `IsHeatFlowDensity` — **L-FV2DB-A** (heat-flow): bundles the heat equation
  `∂_t p = (1/2) Δ_x p` as a single existential field, and
* `IsIBPHypothesis` — **L-FV2DB-B** (integration by parts).

This file *sub-decomposes* the L-FV2DB-A heat-flow side. The wave-7
`heat_equation` field bundles the entire PDE as one opaque `∃ Δp, ...`. Here we
expose the analytic structure of that PDE for the **Gaussian heat kernel**
(`heatKernel t x = gaussianPDFReal 0 ⟨t, _⟩ x`) by giving the first and second
spatial derivatives in closed form (both **internally discharged**).

## 内容

* `heatKernel_spatial_deriv` — closed form of `∂_x g_t`: equals `-(x/t)·g_t x`,
  the `m = 0` specialization of `InformationTheory.Shannon.deriv_gaussianPDFReal`.
  **(internal discharge)**
* `heatKernel_hasDerivAt_spatial` — the `HasDerivAt` form, via
  `differentiable_gaussianPDFReal`. **(internal discharge)**
* `spatialLaplacianHeatKernel t x := (x²/t² - 1/t)·g_t x` — closed form of the
  spatial Laplacian `Δ_x g_t = ∂²_x g_t`.
* `heatKernel_spatial_laplacian` — `∂²_x g_t = spatialLaplacianHeatKernel t x`,
  by differentiating `heatKernel_spatial_deriv` once more (product rule).
  **(internal discharge — the core of this seed)**
* `IsHeatSpatialDerivHyp` / `IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` —
  the three sub-predicates that L-FV2DB-A's monolithic `heat_equation` field
  decomposes into. The spatial-derivative sub-predicate is **internally
  discharged** for the Gaussian kernel (`isHeatSpatialDerivHyp_gaussian`); the
  time-derivative and convolution-representation sub-predicates remain
  pass-through (the variance-derivative of `gaussianPDFReal` is not in Mathlib).
* `IsHeatFlowDensity_of_sub_predicates` — re-assembly: the three sub-predicates
  re-build a wave-7 `IsHeatFlowDensity` witness.
* `heatSemigroup_compose_law` — measure-level Gaussian semigroup composition
  `g_{t₁} ⋆ g_{t₂} = g_{t₁+t₂}`. **(internal discharge, measure level)**
* `deBruijn_identity_v2_of_heat_subhyp` — de Bruijn body bridge re-published from
  the sub-predicate decomposition.

## 撤退ライン

* **L-FV2HF-A** (本 file, 採用 + full discharge): the first and second spatial
  derivatives of the Gaussian heat kernel are discharged internally
  (`heatKernel_spatial_deriv`, `heatKernel_spatial_laplacian`,
  `isHeatSpatialDerivHyp_gaussian`). This is the "manual verification 50-80
  lines" item in `fisher-info-moonshot-plan.md` Phase C.
* **L-FV2HF-B** (本 file, pass-through): the time-derivative sub-predicate
  `IsHeatTimeDerivHyp`. The variance-derivative `∂_t gaussianPDFReal 0 ⟨t,_⟩ x`
  is not available in Mathlib, so the time side is bundled as a `HasDerivAt`
  statement-form field.
* **L-FV2HF-C** (本 file, pass-through): the convolution-representation
  sub-predicate `IsHeatFlowConvolutionHyp`. The density-level convolution
  identity is deferred; the measure-level Gaussian semigroup composition is
  discharged in `heatSemigroup_compose_law`.
-/

namespace InformationTheory.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Spatial derivatives of the Gaussian heat kernel (L-FV2HF-A discharge) -/

/-- The variance of the heat kernel at time `t > 0` is nonzero as an `ℝ≥0`. -/
theorem heatKernel_variance_ne_zero {t : ℝ} (ht : 0 < t) :
    (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
  intro h
  have h' : ((⟨t, ht.le⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
  have : (t : ℝ) = 0 := h'
  linarith

/-- **First spatial derivative of the heat kernel** (`m = 0` case).

`∂_x g_t(x) = -(x / t) · g_t(x)`, the `m = 0` specialization of
`InformationTheory.Shannon.deriv_gaussianPDFReal`. -/
@[entry_point]
theorem heatKernel_spatial_deriv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun y => heatKernel t y) x = -(x / t) * heatKernel t x := by
  have hfun : (fun y => heatKernel t y) = gaussianPDFReal 0 ⟨t, ht.le⟩ := by
    funext y; exact heatKernel_def_gaussianPDFReal ht y
  rw [hfun, InformationTheory.Shannon.deriv_gaussianPDFReal (heatKernel_variance_ne_zero ht) x,
    heatKernel_def_gaussianPDFReal ht x]
  show -((x : ℝ) - 0) / t * gaussianPDFReal 0 ⟨t, ht.le⟩ x
     = -(x / t) * gaussianPDFReal 0 ⟨t, ht.le⟩ x
  ring

/-- **`HasDerivAt` form** of the first spatial derivative of the heat kernel. -/
@[entry_point]
theorem heatKernel_hasDerivAt_spatial {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => heatKernel t y) (-(x / t) * heatKernel t x) x := by
  have hfun : (fun y => heatKernel t y) = gaussianPDFReal 0 ⟨t, ht.le⟩ := by
    funext y; exact heatKernel_def_gaussianPDFReal ht y
  rw [hfun]
  have hval : -(x / t) * heatKernel t x = deriv (gaussianPDFReal 0 ⟨t, ht.le⟩) x := by
    rw [InformationTheory.Shannon.deriv_gaussianPDFReal (heatKernel_variance_ne_zero ht) x,
      heatKernel_def_gaussianPDFReal ht x]
    show -(x / t) * gaussianPDFReal 0 ⟨t, ht.le⟩ x
       = -((x : ℝ) - 0) / t * gaussianPDFReal 0 ⟨t, ht.le⟩ x
    ring
  rw [hval]
  exact (InformationTheory.Shannon.differentiable_gaussianPDFReal 0 ⟨t, ht.le⟩).differentiableAt.hasDerivAt

/-- **Spatial Laplacian of the heat kernel** (closed form).

`Δ_x g_t(x) = ∂²_x g_t(x) = (x²/t² - 1/t) · g_t(x)`. -/
noncomputable def spatialLaplacianHeatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (x ^ 2 / t ^ 2 - 1 / t) * heatKernel t x

/-- **Second spatial derivative of the heat kernel** equals
`spatialLaplacianHeatKernel`. The core internal discharge of this seed:
differentiate `heatKernel_spatial_deriv` once more (product rule).

`∂²_x g_t(x) = (x²/t² - 1/t) · g_t(x)`. -/
@[entry_point]
theorem heatKernel_spatial_laplacian {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun y => deriv (fun z => heatKernel t z) y) x
      = spatialLaplacianHeatKernel t x := by
  have hinner : (fun y => deriv (fun z => heatKernel t z) y)
      = fun y => -(y / t) * heatKernel t y := by
    funext y; exact heatKernel_spatial_deriv ht y
  rw [hinner]
  -- product rule on `(fun y => -(y/t)) * (fun y => heatKernel t y)`
  have hf : HasDerivAt (fun y : ℝ => -(y / t)) (-(1 / t)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y / t) (1 / t) x :=
      (hasDerivAt_id x).div_const t
    exact h1.neg
  have hg : HasDerivAt (fun y => heatKernel t y) (-(x / t) * heatKernel t x) x :=
    heatKernel_hasDerivAt_spatial ht x
  have hmul : HasDerivAt (fun y => -(y / t) * heatKernel t y)
      (-(1 / t) * heatKernel t x + -(x / t) * (-(x / t) * heatKernel t x)) x := hf.mul hg
  rw [hmul.deriv]
  unfold spatialLaplacianHeatKernel
  ring

/-! ## Heat-equation right-hand side check (Gaussian, internal) -/

/-! ## Sub-predicate decomposition of L-FV2DB-A -/

/-- **Spatial-derivative sub-predicate** (L-FV2HF-A).

`p t` has the prescribed spatial second derivative `Δp t` at every `x` (for
`t > 0`). For the Gaussian kernel this is **internally discharged** via
`heatKernel_spatial_laplacian` (see `isHeatSpatialDerivHyp_gaussian`). -/
def IsHeatSpatialDerivHyp (p : ℝ → ℝ → ℝ) (Δp : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    deriv (fun y => deriv (fun z => p t z) y) x = Δp t x

/-- **Time-derivative sub-predicate** (L-FV2HF-B, pass-through). -/
def IsHeatTimeDerivHyp (p : ℝ → ℝ → ℝ) (Δp : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    HasDerivAt (fun s => p s x) ((1 / 2) * Δp t x) t

/-- **Convolution-representation sub-predicate** (L-FV2HF-C, pass-through). -/
def IsHeatFlowConvolutionHyp {Ω : Type*} [MeasurableSpace Ω]
    (_X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) : Prop :=
  (P.map Z = gaussianReal 0 1)
    ∧ (∀ t : ℝ, 0 < t → ∀ x : ℝ, 0 ≤ p t x)
    ∧ (∀ t : ℝ, 0 < t → Measurable (p t))

/-! ## Gaussian discharge of the spatial sub-predicate -/

/-- **Gaussian heat kernel satisfies the spatial-derivative sub-predicate.**

With `Δp t x := spatialLaplacianHeatKernel t x`, the heat kernel discharges
`IsHeatSpatialDerivHyp` internally. This is the L-FV2HF-A discharge. -/
@[entry_point]
theorem isHeatSpatialDerivHyp_gaussian :
    IsHeatSpatialDerivHyp (fun t x => heatKernel t x)
      (fun t x => spatialLaplacianHeatKernel t x) := by
  intro t ht x
  exact heatKernel_spatial_laplacian ht x

/-! ## Re-assembly into wave-7 `IsHeatFlowDensity` -/

/-- **Re-assembly**: the sub-predicates re-build a wave-7 `IsHeatFlowDensity`. -/
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

/-! ## de Bruijn body bridge re-publish (from sub-predicates) -/

/-- **de Bruijn identity body discharge from the sub-predicate decomposition.**

Given the convolution + time-derivative sub-predicates (which re-assemble into a
wave-7 `IsHeatFlowDensity`) and the IBP hypothesis at time `t`, the de Bruijn
identity holds. Re-publishes `deBruijn_identity_v2_of_heat_flow` from the finer
decomposition.

**Phase 2.B 段 2 (2026-05-27、`epi-stam-fisher-epi-integrated-sweep-plan`
§Phase 2.B 段 2)**: L3 (`deBruijn_identity_v2_of_heat_flow`) が
honest pass-through (`IsRegularDeBruijnHypV2.ofHeatFlow` constructor +
genuine `deBruijn_identity_v2`、`wall:debruijn-integration` は [CLOSED
2026-06-04]) 化されたため、本 D5 も transitive pass-through に昇格。`h_ibp`
引数は caller compat 維持 (L3 と同様 unused、`_h_ibp` underscore prefix)。

NOTE (2026-06-05 closure): `deBruijn_identity_v2` 自体は genuine (sorryAx-free、
`debruijnIdentityV2_holds_assembled` 経由)、`wall:debruijn-integration` は
[CLOSED 2026-06-04]。`IsRegularDeBruijnHypV2.ofHeatFlow` constructor の 3 field
(`density_t_eq`/`pX_law`/`pX_mom`) は commit 94a3ae8 で全 genuine 化済 (conv-pin
+ `hX_ac`/`h_mom_X` regularity precond)。よって本 lemma は **sorryAx-free** (旧 NOTE
の「transitive sorryAx 依存」は stale)。`h_conv`/`h_time` は `IsHeatFlowDensity` を
再組立するが genuine path (`pPath_eq_convDensityAdd` + atoms) は `h_time` の heat-
equation 核を消費しない (vestigial、本 commit 由来でなく既存の load-bearing pass-
through predicate)。

@audit:ok — independent honesty audit (2026-06-05, fresh auditor, commit 94a3ae8):
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。新規
`hX_ac`/`h_mom_X` は regularity precondition、load-bearing でない。 -/
@[entry_point]
theorem deBruijn_identity_v2_of_heat_subhyp
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    {t : ℝ} (ht : 0 < t)
    {p : ℝ → ℝ → ℝ} {Δp : ℝ → ℝ → ℝ}
    (h_conv : IsHeatFlowConvolutionHyp X Z P p)
    (h_time : IsHeatTimeDerivHyp p Δp)
    (_h_ibp : IsIBPHypothesis X Z P p t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1 / 2) * fisherInfoOfDensityReal
        (IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ hX_ac h_mom_X ht
          (IsHeatFlowDensity_of_sub_predicates h_conv h_time)).density_t)
      t :=
  deBruijn_identity_v2_of_heat_flow X Z hX hZ hXZ hX_ac h_mom_X ht
    (IsHeatFlowDensity_of_sub_predicates h_conv h_time) _h_ibp

/-- **`IsRegularDeBruijnHypV2` constructor from sub-predicates.**

Phase 2.B 段 1 (foundation) で `IsRegularDeBruijnHypV2` が 2-field 化された
ため、本 constructor の旧 `h_ibp` 引数は段 1 で未使用化済。**Phase 2.B 段 2
(2026-05-27)** で formal 引数自体を削除した (constructor body から literal
alias chain が完全消滅、launder pattern 撲滅完了)。consumer 無し
(本 file 内のみ定義、外部 reference は docstring 言及のみ)。

@audit:ok — independent honesty audit (2026-06-05, fresh auditor, commit 94a3ae8):
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。genuine
delegation to `ofHeatFlow` (`@audit:ok`)。新規 `hX_ac`/`h_mom_X` は regularity
precondition。 -/
@[entry_point]
noncomputable def IsRegularDeBruijnHypV2.ofHeatSubhyp
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    {t : ℝ} (ht : 0 < t)
    {p : ℝ → ℝ → ℝ} {Δp : ℝ → ℝ → ℝ}
    (h_conv : IsHeatFlowConvolutionHyp X Z P p)
    (h_time : IsHeatTimeDerivHyp p Δp) :
    IsRegularDeBruijnHypV2 X Z P t :=
  IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ hX_ac h_mom_X ht
    (IsHeatFlowDensity_of_sub_predicates h_conv h_time)

end InformationTheory.Shannon.FisherInfoV2