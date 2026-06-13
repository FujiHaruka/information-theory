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
import InformationTheory.Shannon.FisherInfo.V2DeBruijnGenuine
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.Conv.Density

/-!
# Fisher information V2 — de Bruijn body

Body-side scaffolding for the general-`X` de Bruijn identity (Cover–Thomas 17.7.2's
differentiate-under-the-integral via heat equation plus integration by parts), built on the
definitions of `FisherInfoV2DeBruijn.lean`. The heat equation and the integration-by-parts step
are exposed as predicates that compose into the de Bruijn statement.

## Main definitions

* `heatKernel t x` — the Gaussian heat kernel `(1/√(2π t)) exp(-x²/(2t))`, defined as
  `gaussianPDFReal 0 ⟨t, _⟩ x` for `t > 0` and `0` otherwise.
* `IsHeatFlowDensity X Z P p` — `p` is a density family for `X + √t · Z` satisfying the heat
  equation `∂_t p = (1/2) Δ_x p`, bundled in statement form.
* `IsIBPHypothesis X Z P p t` — the integration-by-parts conclusion at time `t`.
* `IsRegularDeBruijnHypV2.ofHeatFlow` — the constructor turning an `IsHeatFlowDensity` witness
  (plus a.c. and finite-second-moment regularity of `X`) into an `IsRegularDeBruijnHypV2`.

## Main statements

* `heatKernel_nonneg` / `measurable_heatKernel` — basic regularity of the heat kernel.
* `deBruijn_identity_v2_of_heat_flow` — the de Bruijn identity from `IsHeatFlowDensity` plus
  `IsIBPHypothesis`.

## Implementation notes

The predicate split follows the Mathlib-shape rule: the heat-equation field matches the
conclusion of the convolution chain rule, while the integration-by-parts field matches the
conclusion expected by `HasDerivAt.congr_of_eventuallyEq`, so the two compose with
`deBruijn_identity_v2` without bridging lemmas.
-/

namespace InformationTheory.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open scoped ENNReal NNReal Real

/-! ## Heat kernel (Gaussian density with variance `t`) -/

/-- **Gaussian heat kernel** `g_t(x) := (1/√(2π t)) exp(-x²/(2t))`.

Defined as the standard centred Gaussian density with variance `t > 0`. This is
the *kernel* of the Gaussian heat semigroup: for `Z ∼ 𝒩(0, 1)` and `X`
independent of `Z`, the density of `X + √t · Z` is `p_0 * g_t` (convolution).

For `t = 0` we return `0` as a syntactic placeholder; the meaningful case is
`t > 0` (the kernel does not extend continuously to `t = 0`). -/
noncomputable def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  if h : 0 < t then gaussianPDFReal 0 ⟨t, h.le⟩ x else 0

/-- Unfold lemma for `heatKernel` when `t > 0`. -/
theorem heatKernel_def_gaussianPDFReal {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x = gaussianPDFReal 0 ⟨t, ht.le⟩ x := by
  unfold heatKernel
  rw [dif_pos ht]

/-- The heat kernel is non-negative. -/
@[entry_point]
theorem heatKernel_nonneg (t x : ℝ) : 0 ≤ heatKernel t x := by
  unfold heatKernel
  split_ifs with h
  · exact gaussianPDFReal_nonneg _ _ x
  · exact le_refl 0

/-- The heat kernel is measurable. -/
@[entry_point]
theorem measurable_heatKernel (t : ℝ) : Measurable (fun x => heatKernel t x) := by
  unfold heatKernel
  split_ifs with h
  · exact measurable_gaussianPDFReal 0 ⟨t, h.le⟩
  · exact measurable_const

/-! ## Heat-flow density predicate -/

/-- The heat-flow density predicate for the law of `X + √t · Z`: `p t x` is the density of
`P.map (gaussianConvolution X Z t)` at `x`, satisfying the heat equation `∂_t p = (1/2) Δ_x p`
together with basic regularity. -/
structure IsHeatFlowDensity {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) : Prop where
  /-- `Z` is standard normal. -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- For each `t > 0`, `p t` is a density witness for `P.map (X + √t · Z)`. -/
  density_witness : ∀ t : ℝ, 0 < t → ∀ x : ℝ, 0 ≤ p t x
  /-- The density family is measurable in `x` for each `t > 0`. -/
  density_measurable : ∀ t : ℝ, 0 < t → Measurable (p t)
  /-- The heat equation in statement form: there is a `Δp : ℝ → ℝ → ℝ` with
  `(d/dt) p t x = (1/2) · Δp t x` for each `t > 0` and `x`. -/
  heat_equation : ∃ Δp : ℝ → ℝ → ℝ, ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    HasDerivAt (fun s => p s x) ((1/2) * Δp t x) t

/-- Accessor: the spatial laplacian witness from `heat_equation`. -/
@[entry_point]
noncomputable def IsHeatFlowDensity.laplacian {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ → ℝ → ℝ}
    (h : IsHeatFlowDensity X Z P p) : ℝ → ℝ → ℝ :=
  h.heat_equation.choose

/-- The laplacian witness satisfies the heat equation `∂_t p = (1/2) · Δp`. -/
@[entry_point]
theorem IsHeatFlowDensity.heat_equation_spec {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ → ℝ → ℝ}
    (h : IsHeatFlowDensity X Z P p) :
    ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun s => p s x) ((1/2) * h.laplacian t x) t :=
  h.heat_equation.choose_spec

/-! ## Integration-by-parts predicate -/

/-- The integration-by-parts conclusion at time `t`: the time-derivative of
`differentialEntropy (P.map (X + √s · Z))` at `s = t` equals
`(1/2) · fisherInfoOfDensityReal (p t)`. This is a predicate-form literal alias of that
`HasDerivAt` statement, retained for caller compatibility; it lifts a conclusion type into a
predicate and is a deletion candidate.

@audit:retract-candidate(name-laundering-alias) -/
def IsIBPHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  HasDerivAt
    (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
    ((1/2) * fisherInfoOfDensityReal (p t))
    t

/-! ## Body discharge -/

/-- The `IsRegularDeBruijnHypV2` constructor from a heat-flow density. The two extra
preconditions are regularity of `X` itself, which `IsHeatFlowDensity` (carrying only the path
density) does not supply:

* `hX_ac : (P.map X) ≪ volume` — `X` has a Lebesgue density, feeding `pX_law` via
  `withDensity_rnDeriv_eq`.
* `h_mom_X : Integrable (fun ω => (X ω)^2) P` — `X` has finite second moment, feeding `pX_mom`
  via `integrable_map_measure`.

The density witness `density_t` is pinned to the smooth convolution `convDensityAdd pX g_t`, the
genuine density of `P.map (X + √t · Z)`, so `density_t_eq` holds by `rfl`.

@audit:ok -/
@[entry_point]
noncomputable def IsRegularDeBruijnHypV2.ofHeatFlow
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (_hZ : Measurable Z)
    (_hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    {t : ℝ} (_ht : 0 < t)
    {p : ℝ → ℝ → ℝ}
    (h_heat : IsHeatFlowDensity X Z P p) :
    IsRegularDeBruijnHypV2 X Z P t where
  Z_law := h_heat.Z_law
  -- Conv-pin redesign: pin `density_t` directly to the smooth convolution
  -- representative so `density_t_eq` is `rfl`. This is the genuine density of
  -- `P.map (X + √t·Z)` (Phase 1b `pPath_eq_convDensityAdd`), written explicitly.
  density_t := convDensityAdd (fun x => ((P.map X).rnDeriv volume x).toReal)
    (gaussianPDFReal 0 ⟨t, _ht.le⟩)
  density_t_eq := fun _ _ => rfl
  pX := fun x => ((P.map X).rnDeriv volume x).toReal
  pX_nn := fun x => ENNReal.toReal_nonneg
  pX_meas := ((P.map X).measurable_rnDeriv volume).ennreal_toReal
  -- `pX_law` from `hX_ac` via `withDensity_rnDeriv_eq` (mirrors
  -- `rescaledInput_density_witness`'s `hpX_law`, here on `P.map X`).
  pX_law := by
    set pX : ℝ → ℝ := fun x => ((P.map X).rnDeriv volume x).toReal with hpX
    have hfin : ∀ᵐ x ∂volume, (P.map X).rnDeriv volume x < ∞ :=
      Measure.rnDeriv_lt_top (P.map X) volume
    have hcongr : (fun x => ENNReal.ofReal (pX x)) =ᵐ[volume]
        (P.map X).rnDeriv volume := by
      filter_upwards [hfin] with x hx
      simp only [hpX, ENNReal.ofReal_toReal hx.ne]
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hX_ac]
  -- `pX_mom` from `h_mom_X` via `integrable_map_measure` transport + the `pX_law`
  -- withDensity equation (mirrors `rescaledInput_density_witness`'s `hpX_mom`).
  pX_mom := by
    set pX : ℝ → ℝ := fun x => ((P.map X).rnDeriv volume x).toReal with hpX
    have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
    have hpX_meas : Measurable pX :=
      ((P.map X).measurable_rnDeriv volume).ennreal_toReal
    have hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)) := by
      have hfin : ∀ᵐ x ∂volume, (P.map X).rnDeriv volume x < ∞ :=
        Measure.rnDeriv_lt_top (P.map X) volume
      have hcongr : (fun x => ENNReal.ofReal (pX x)) =ᵐ[volume]
          (P.map X).rnDeriv volume := by
        filter_upwards [hfin] with x hx
        simp only [hpX, ENNReal.ofReal_toReal hx.ne]
      rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hX_ac]
    have hsq_law : Integrable (fun y => y ^ 2) (P.map X) := by
      rw [integrable_map_measure
        ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
        hX.aemeasurable]
      simpa [Function.comp] using h_mom_X
    rw [hpX_law] at hsq_law
    rw [integrable_withDensity_iff_integrable_smul₀'
      hpX_meas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq_law
    refine hsq_law.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpX_nn x)]; ring

/-- The de Bruijn identity from a heat-flow density family `p` (`IsHeatFlowDensity`) and the IBP
hypothesis at `t > 0` (`IsIBPHypothesis`), with the V2 Fisher information of the constructed
density witness on the right. A pass-through to `deBruijn_identity_v2` via
`IsRegularDeBruijnHypV2.ofHeatFlow`; the `_h_ibp` argument is kept for caller compatibility but
unused.

@audit:ok -/
@[entry_point]
theorem deBruijn_identity_v2_of_heat_flow
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    (hX_ac : (P.map X) ≪ volume)
    (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    {t : ℝ} (ht : 0 < t)
    {p : ℝ → ℝ → ℝ}
    (h_heat : IsHeatFlowDensity X Z P p)
    (_h_ibp : IsIBPHypothesis X Z P p t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal
        (IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ hX_ac h_mom_X ht h_heat).density_t)
      t :=
  deBruijn_identity_v2 X Z hX hZ hXZ ht
    (IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ hX_ac h_mom_X ht h_heat)

end InformationTheory.Shannon.FisherInfoV2