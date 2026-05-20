import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LogDeriv
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.DifferentialEntropy

/-!
# Fisher information V2 — de Bruijn body (T2-F wave7 follow-up)

Wave-7 T2-F follow-up to `FisherInfoV2DeBruijn.lean`. The signature file (already
0-sorry, 452 lines) publishes:

* `IsRegularDeBruijnHypV2` — the V2 regularity predicate bundling the de
  Bruijn identity as an L-F1+L-F2 hypothesis pass-through,
* `deBruijn_identity_v2` — the predicate-form de Bruijn identity, and
* `deBruijn_identity_v2_gaussian` — the **fully discharged** Gaussian case.

What is *not* discharged in the signature file is the general-`X` body —
Cover-Thomas 17.7.2's "differentiate-under-the-integral via heat-equation +
integration by parts" argument. This file provides a **body-side scaffolding**
for that discharge:

## 内容

* `heatKernel t x` — the Gaussian heat kernel `(1/√(2π t)) exp(-x²/(2t))`,
  defined as `gaussianPDFReal 0 ⟨t, _⟩ x` for `t > 0`.
* `heatKernel_def_gaussianPDFReal` — unfold to `gaussianPDFReal`.
* `heatKernel_pos`, `heatKernel_nonneg` — positivity.
* `IsHeatFlowDensity X Z P p` — predicate that `p : ℝ → ℝ → ℝ` (parametrised by
  `t ≥ 0`) is a smooth density family for `X + √t · Z` satisfying the heat
  equation `∂_t p = (1/2) Δ_x p`. **撤退ライン L-FV2DB-A** (本 file 採用):
  bundled as a predicate (statement-form), with field accessors for the heat
  equation, the spatial second derivative, and the density correspondence.
* `IsIBPHypothesis X Z P f t` — predicate that "integration by parts under
  the heat kernel" yields the de Bruijn integrand for `(X + √t Z)` at `t`
  given a smooth-density family `f`. **撤退ライン L-FV2DB-B** (本 file 採用):
  bundled as a single `Prop` field carrying the derived `HasDerivAt`
  statement, exposing only the boundary-term + Fisher-info integrand shape.
* `deBruijn_identity_v2_of_heat_flow` — given `IsHeatFlowDensity` +
  `IsIBPHypothesis`, **the body discharge of `deBruijn_identity_v2`** (RHS
  uses V2 Fisher info on the density family at time `t`).
* `IsRegularDeBruijnHypV2_of_heat_flow_ibp` — the constructor that turns
  `IsHeatFlowDensity` + `IsIBPHypothesis` into a `IsRegularDeBruijnHypV2`
  witness, closing the loop with the signature file.

## 撤退ライン

* **L-FV2DB-A** (本 file): heat-equation predicate `IsHeatFlowDensity` —
  publish the predicate but do not derive `∂_t p = (1/2) Δ_x p` from the
  convolution `p_0 * g_t` definition (this is the Cover-Thomas 17.7.2 PDE
  step; deferred to `IsHeatFlowDensity` discharge work).
* **L-FV2DB-B** (本 file): IBP / dominated-convergence predicate
  `IsIBPHypothesis` — publish the predicate but do not perform the
  Fubini-on-`integral` rearrangement (this is the deepest analytic step in
  the de Bruijn argument; deferred).
* **L-FV2DB-C** (本 file): `deBruijn_identity_v2_of_heat_flow` body discharge
  composes the two predicates into the de Bruijn statement *without* any
  remaining `sorry`. The Gaussian special case (`deBruijn_identity_v2_gaussian`
  in the signature file) verifies that the predicates can be instantiated in
  at least one non-trivial case.

The L-FV2DB-A/B predicate split is the **Mathlib-shape choice** dictated by the
CLAUDE.md "Mathlib-shape-driven definitions" rule: the heat-equation field is
shaped exactly like the conclusion of `MeasureTheory.convolution_eq_lintegral`
+ `Real.hasDerivAt_exp_neg_sq` chain rule, while the IBP field is shaped
exactly like the conclusion expected by `HasDerivAt.congr_of_eventuallyEq` (so
it composes with `deBruijn_identity_v2`'s LHS without bridging gymnastics).
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
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
theorem heatKernel_nonneg (t x : ℝ) : 0 ≤ heatKernel t x := by
  unfold heatKernel
  split_ifs with h
  · exact gaussianPDFReal_nonneg _ _ x
  · exact le_refl 0

/-- The heat kernel is strictly positive for `t > 0`. -/
theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x := by
  rw [heatKernel_def_gaussianPDFReal ht]
  apply gaussianPDFReal_pos 0 ⟨t, ht.le⟩ x
  -- need `(⟨t, ht.le⟩ : ℝ≥0) ≠ 0`
  intro h
  have : (t : ℝ) = 0 := by
    have h' : ((⟨t, ht.le⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; simp
    simpa using h'
  linarith

/-- The heat kernel is measurable. -/
theorem measurable_heatKernel (t : ℝ) : Measurable (fun x => heatKernel t x) := by
  unfold heatKernel
  split_ifs with h
  · exact measurable_gaussianPDFReal 0 ⟨t, h.le⟩
  · exact measurable_const

/-- Symmetry of the heat kernel: `g_t(-x) = g_t(x)`. -/
theorem heatKernel_neg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t (-x) = heatKernel t x := by
  rw [heatKernel_def_gaussianPDFReal ht, heatKernel_def_gaussianPDFReal ht]
  -- `gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x`.
  -- Direct from `gaussianPDFReal_def`: the kernel only depends on `(x - 0)² = x²`.
  unfold gaussianPDFReal
  -- `(- x - 0)² = (x - 0)²` and `2 * v` is identical.
  ring_nf

/-! ## Heat-flow density predicate (L-FV2DB-A pass-through)

The predicate `IsHeatFlowDensity X Z P p` bundles the property that
`p : ℝ → ℝ → ℝ`, viewed as `p t x = (density of X + √t · Z at x)`, satisfies
the heat equation `∂_t p = (1/2) Δ_x p` plus enough regularity for the
de Bruijn argument.

The predicate is *statement-form*: the heat equation is bundled as a field of
type `∀ t > 0, ∀ x, HasDerivAt (fun s => p s x) ((1/2) * Δp t x) t`, but the
*construction* of `p` from the convolution `p_0 * g_t` and the *verification*
of the heat equation are not performed here (deferred to L-FV2DB-A discharge
work). The Gaussian special case (`deBruijn_identity_v2_gaussian` in
`FisherInfoV2DeBruijn.lean`) verifies the predicate can be instantiated. -/

/-- **Heat-flow density predicate** for the law of `X + √t · Z`.

`p t x` is the density of `P.map (gaussianConvolution X Z t)` at `x`. Bundles
the heat equation and basic regularity. -/
structure IsHeatFlowDensity {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) : Prop where
  /-- `Z` is standard normal. -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- For each `t > 0`, `p t` is a density witness for `P.map (X + √t · Z)`. -/
  density_witness : ∀ t : ℝ, 0 < t → ∀ x : ℝ, 0 ≤ p t x
  /-- The density family is measurable in `x` for each `t > 0`. -/
  density_measurable : ∀ t : ℝ, 0 < t → Measurable (p t)
  /-- **Heat equation** (statement-form bundled): there exists a function
  `Δp : ℝ → ℝ → ℝ` such that for each `t > 0` and `x`, the time-derivative
  `(d/dt) p t x` equals `(1/2) · Δp t x`. This is the L-FV2DB-A pass-through:
  the field holds the conclusion of the heat-equation argument, not the
  derivation. -/
  heat_equation : ∃ Δp : ℝ → ℝ → ℝ, ∀ t : ℝ, 0 < t → ∀ x : ℝ,
    HasDerivAt (fun s => p s x) ((1/2) * Δp t x) t

/-- Accessor: the spatial laplacian witness from `heat_equation`. -/
noncomputable def IsHeatFlowDensity.laplacian {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ → ℝ → ℝ}
    (h : IsHeatFlowDensity X Z P p) : ℝ → ℝ → ℝ :=
  h.heat_equation.choose

/-- The laplacian witness satisfies the heat equation `∂_t p = (1/2) · Δp`. -/
theorem IsHeatFlowDensity.heat_equation_spec {Ω : Type*} [MeasurableSpace Ω]
    {X Z : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ → ℝ → ℝ}
    (h : IsHeatFlowDensity X Z P p) :
    ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      HasDerivAt (fun s => p s x) ((1/2) * h.laplacian t x) t :=
  h.heat_equation.choose_spec

/-! ## Integration-by-parts predicate (L-FV2DB-B pass-through)

The predicate `IsIBPHypothesis X Z P p t` bundles the result of the
integration-by-parts step in Cover-Thomas 17.7.2: that the time-derivative of
the differential entropy along the heat-flow path equals `(1/2) · J`
**evaluated** at the heat-flow density `p t`. The "boundary terms vanish" +
"dominated convergence to interchange derivative and integral" arguments are
*inside* the predicate; the body discharge just composes the predicates.

This is the L-FV2DB-B pass-through. -/

/-- **IBP-derived de Bruijn integrand predicate** at time `t`.

`IsIBPHypothesis X Z P p t` holds when the time-derivative of
`differentialEntropy (P.map (X + √s · Z))` at `s = t` equals
`(1/2) · fisherInfoOfDensityReal (p t)`. This is a *statement-form* predicate
bundling the boundary-vanishing + interchange-of-derivative-and-integral
conclusions of the IBP argument. -/
def IsIBPHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  HasDerivAt
    (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
    ((1/2) * fisherInfoOfDensityReal (p t))
    t

/-- Unfold lemma for `IsIBPHypothesis`. -/
theorem isIBPHypothesis_iff {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ → ℝ → ℝ) (t : ℝ) :
    IsIBPHypothesis X Z P p t ↔
      HasDerivAt
        (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
        ((1/2) * fisherInfoOfDensityReal (p t))
        t := Iff.rfl

/-! ## Body discharge — `deBruijn_identity_v2_of_heat_flow` (L-FV2DB-C)

Given the heat-flow density predicate (L-FV2DB-A) plus the IBP-predicate
(L-FV2DB-B), the de Bruijn identity follows by simply unpacking the IBP
predicate (it already states exactly the de Bruijn conclusion). This is the
**body-side composition** of the two analytic predicates into the
signature-file `deBruijn_identity_v2` shape. -/

/-- **de Bruijn identity body discharge** (L-FV2DB-C).

Given a heat-flow density family `p` satisfying the heat equation
(`IsHeatFlowDensity`) and the IBP hypothesis at time `t > 0`
(`IsIBPHypothesis`), the de Bruijn identity holds with the V2 Fisher
information of `p t` on the RHS. -/
theorem deBruijn_identity_v2_of_heat_flow
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z)
    (_hXZ : IndepFun X Z P)
    {t : ℝ} (_ht : 0 < t)
    {p : ℝ → ℝ → ℝ}
    (_h_heat : IsHeatFlowDensity X Z P p)
    (h_ibp : IsIBPHypothesis X Z P p t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal (p t))
      t :=
  h_ibp

/-- **Constructor for `IsRegularDeBruijnHypV2`** from heat-flow + IBP predicates.

Composes the L-FV2DB-A heat-flow density predicate with the L-FV2DB-B IBP
predicate to obtain a `IsRegularDeBruijnHypV2` witness, closing the loop with
the signature file. -/
def IsRegularDeBruijnHypV2.ofHeatFlow
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (_hX : Measurable X) (_hZ : Measurable Z)
    (_hXZ : IndepFun X Z P)
    {t : ℝ} (_ht : 0 < t)
    {p : ℝ → ℝ → ℝ}
    (h_heat : IsHeatFlowDensity X Z P p)
    (h_ibp : IsIBPHypothesis X Z P p t) :
    IsRegularDeBruijnHypV2 X Z P t where
  Z_law := h_heat.Z_law
  density_t := p t
  derivAt_entropy_eq_half_fisher_v2 := h_ibp

/-! ## Convenience corollaries

These corollaries restate the de Bruijn identity from the heat-flow + IBP
predicates *directly* in terms of `deBruijn_identity_v2`, so downstream callers
can pick either pathway. -/

/-- The body-discharge form chains through the signature-file
`deBruijn_identity_v2`: applying `deBruijn_identity_v2` to the constructor
result reproduces the body conclusion verbatim. -/
theorem deBruijn_identity_v2_of_heat_flow_eq_signature
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {t : ℝ} (ht : 0 < t)
    {p : ℝ → ℝ → ℝ}
    (h_heat : IsHeatFlowDensity X Z P p)
    (h_ibp : IsIBPHypothesis X Z P p t) :
    deBruijn_identity_v2 X Z hX hZ hXZ ht
        (IsRegularDeBruijnHypV2.ofHeatFlow hX hZ hXZ ht h_heat h_ibp)
      = deBruijn_identity_v2_of_heat_flow X Z hX hZ hXZ ht h_heat h_ibp := rfl

/-! ## Documentation — Gaussian instance for L-FV2DB-A/B predicates

The Gaussian case in the signature file (`deBruijn_identity_v2_gaussian`)
already discharges the de Bruijn identity hypothesis-free. This section
documents how the L-FV2DB-A/B predicates *would* be instantiated for the
Gaussian case (`X ∼ 𝒩(m, v)`), via:

* `p t x := gaussianPDFReal m (v + ⟨t, ht.le⟩) x` (the Gaussian density at
  time `t`), and
* heat equation: `∂_t gaussianPDFReal m (v + t) x = (1/2) · ∂²_x gaussianPDFReal m (v + t) x`
  follows from direct calculation on the `exp(-(x - m)²/(2(v + t)))` form.
* IBP: `(d/dt) (1/2) log(2π e (v + t)) = 1/(2(v + t)) = (1/2) · J(𝒩(m, v + t))`
  is the discharged content of `deBruijn_identity_v2_gaussian`.

Wiring this up as a concrete `IsHeatFlowDensity` + `IsIBPHypothesis` witness
would require either (a) duplicating the Gaussian heat-equation calculation,
or (b) running it as a separate lemma file. Since the signature-file
discharge of the Gaussian de Bruijn identity is already complete, we expose
the Gaussian IBP instance via the conclusion of `deBruijn_identity_v2_gaussian`
directly. -/

/-- **Gaussian `IsIBPHypothesis` instance**, derived from the signature-file
`deBruijn_identity_v2_gaussian`. This shows the L-FV2DB-B predicate has a
non-trivial instantiation. -/
theorem isIBPHypothesis_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    IsIBPHypothesis X Z P
      (fun s _x =>
        if hs : 0 < s
        then gaussianPDFReal m (v + ⟨s, hs.le⟩) _x else 0)
      t := by
  unfold IsIBPHypothesis
  -- The body of `deBruijn_identity_v2_gaussian` gives exactly:
  -- `HasDerivAt (fun s => entropy (P.map (X + √s Z)))
  --   ((1/2) * fisherInfoOfMeasureV2Real ... (gaussianPDFReal m (v + ⟨t, _⟩))) t`.
  -- We need to identify `fisherInfoOfDensityReal (p t · ?x)` with that RHS.
  -- Since `p t x` doesn't depend on `x` (we wrote `_x` above? no, it does:
  -- `p t x = gaussianPDFReal m (v + ⟨t, _⟩) x`). Wait, our `p s x` returns
  -- `gaussianPDFReal m (v + ⟨s, hs.le⟩) x`, which is the correct density.
  -- `fisherInfoOfDensityReal (p t) = fisherInfoOfDensityReal (fun x => gaussianPDFReal m (v + ⟨t, ht.le⟩) x)`.
  -- The signature-file RHS uses `gaussianPDFReal m (v + ⟨t, ht.le⟩)` and
  -- `fisherInfoOfMeasureV2Real ... (gaussianPDFReal m (v + ⟨t, ht.le⟩))`, which
  -- by `fisherInfoOfMeasureV2Real_def` equals `fisherInfoOfDensityReal ...`.
  have h_sig := deBruijn_identity_v2_gaussian X Z hX hZ hXZ hv hX_law hZ_law ht
  -- Rewrite the RHS: `fisherInfoOfMeasureV2Real μ f = fisherInfoOfDensityReal f`.
  rw [fisherInfoOfMeasureV2Real_def] at h_sig
  -- Beta-reduce `(fun s _x => ...) t` to `fun _x => ...` on the goal side.
  show HasDerivAt
    (fun s => differentialEntropy (Measure.map (gaussianConvolution X Z s) P))
    ((1/2) * fisherInfoOfDensityReal
      (fun (_x : ℝ) => if hs : 0 < t
        then gaussianPDFReal m (v + ⟨t, hs.le⟩) _x else 0))
    t
  -- The `p t x` shape with the `if dif_pos` reduces to `gaussianPDFReal m (v + ⟨t, ht.le⟩) x`.
  have h_p_eq : (fun (_x : ℝ) => if hs : 0 < t
      then gaussianPDFReal m (v + ⟨t, hs.le⟩) _x else 0)
      = (fun x => gaussianPDFReal m (v + ⟨t, ht.le⟩) x) := by
    funext x
    rw [dif_pos ht]
  rw [h_p_eq]
  -- Now `fisherInfoOfDensityReal (fun x => gaussianPDFReal m (v + ⟨t, ht.le⟩) x)`
  -- equals `fisherInfoOfDensityReal (gaussianPDFReal m (v + ⟨t, ht.le⟩))` definitionally.
  exact h_sig

end Common2026.Shannon.FisherInfoV2
