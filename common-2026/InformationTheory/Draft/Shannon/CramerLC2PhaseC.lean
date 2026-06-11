import InformationTheory.Draft.Shannon.Cramer
import InformationTheory.Shannon.Cramer.LC2Discharge
import InformationTheory.Shannon.Cramer.LC2DischargeExt
import InformationTheory.Shannon.CramerBoundaryUpstream
import InformationTheory.Shannon.CramerCltBoundaryClosure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import InformationTheory.Meta.EntryPoint

/-!
# Cramér L-C2 Phase C partial discharge (T1-C follow-up Phase C)

This file extends `InformationTheory/Shannon/CramerLC2DischargeExt.lean` (Phase A/B
plumbing + tilted LLN) with the **Phase C partial discharge** of the
`h_tilted_lower` hypothesis of `Cramer.cramer_lower`.

## Status

Phase C requires a **Cramér change-of-measure step** that relates the tilted
infinite-product measure
`Measure.infinitePi (fun _ : ℕ => μ₀.tilted (lam * Y ·))` to the tilted-form of
the un-tilted product measure
`(Measure.infinitePi (fun _ : ℕ => μ₀)).tilted (∑ i ∈ Finset.range n, lam * Y ∘ eval i)`
on cylinders of width `n`. Mathlib has no direct compatibility lemma for this
(`Measure.infinitePi_tilted_eq`), and the textbook proof requires a 500+ line
construction of the n-letter Radon–Nikodym derivative.

We therefore **abstract this identification as a hypothesis** via the predicate
`IsMeasureInfinitePiTiltedEq` and publish a *partial* discharge: given the
n-letter RN-deriv compatibility as a hypothesis, the in-probability LLN from
`CramerLC2DischargeExt.tilted_lln_in_probability_real` is converted into the
parent `h_tilted_lower` hypothesis form, and threaded through the existing
`cramer_lower` / `cramer_lower_legendre` / `cramer_tendsto` chain.

## Outline

### Phase C-1 — predicate for the missing Mathlib gap

* `IsMeasureInfinitePiTiltedEq μ₀ Y lam` — the n-letter RN-deriv identification
  that the tilted infinite product is, on cylinders of width `n`, equivalent to
  the cylinder-restricted tilt of the un-tilted product measure with the sum
  exponent `∑ i ∈ Finset.range n, lam · Y (ω i) − n · Λ(lam)`.

### Phase C-2 — (removed)

* `tilted_lower_from_predicate` was **deleted 2026-06-11** (dead-cleanup sweep):
  false-as-stated (no constraint linking `a` to `lam`; refuted at `a = M + 1`,
  empty event) and consumer-0 (the production path runs through `cramer_lower`).

### Phase C-3 — main discharged wrappers

* `cramer_lower_phaseC_partial_discharge` — `cramer_lower` with `h_tilted_lower`
  replaced by `IsMeasureInfinitePiTiltedEq`.
* `cramer_lower_legendre_phaseC_partial_discharge` — Legendre form.
* `cramer_tendsto_phaseC_partial_discharge` — `Tendsto` form.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Phase C-1 — n-letter RN-deriv identification predicate

`IsMeasureInfinitePiTiltedEq` (the n-letter change-of-measure predicate) was
**hoisted** to `InformationTheory/Shannon/CramerBoundaryUpstream.lean` on
2026-06-11 (`cramer-root-wiring-plan` Phase A a1, import-cycle break) and is
re-exported here via that import. References in this file
(`isMeasureInfinitePiTiltedEq_iff`) resolve to the upstream definition. -/

/-! ## Phase C-3 — discharged wrappers -/

/-- **Cramér lower bound, Phase C partial discharge**.

For the canonical i.i.d. product-measure setting `X i ω := Y (ω i)` with
`Y : Ω₀ → ℝ` bounded and measurable, and on the un-tilted infinite product
`μ := Measure.infinitePi (fun _ => μ₀)`, the conclusion is the asymptotic
Cramér lower bound at threshold `a` and tilt `lam`.

The other ambient hypotheses (`iIndepFun`, `IdentDistrib`, bounded family) are
discharged using the Phase A plumbing from `CramerLC2Discharge`. The former gap
(the n-letter Radon–Nikodym derivative identification of the tilted infinite
product / the CLT-boundary window mass) is now **closed**: this theorem is
discharged below by the sorryAx-free headline `cramer_lower_boundary_unconditional`
(see the WIRED note).

DEF-FIX 2026-06-11 (false-statement defect repaired, canonical i.i.d. product
specialization of the general-IID `cramer_lower` in `Cramer.lean`). The
optimal-tilt hypothesis `(h_deriv : deriv (cgf (Y∘·0) (infinitePi μ₀)) lam = a)`
is now part of the signature, so the statement is TRUE-as-stated. Background:
WITHOUT `h_deriv` the per-`lam` bound is false for general `a` (counterexample
`μ₀ = Bernoulli(1/2)`, `Y(0)=0, Y(1)=1`, `lam=0`, `a=0.9`: LHS `= 0` but
`liminf (1/n) log P[S_n ≥ 0.9n] = -D(0.9‖0.5) = -0.368… < 0`); it is tight
precisely at the optimal tilt `a = deriv cgf lam`, where
`lam·a − Λ(lam) = cramerRate a`. The def-fix threads `h_deriv` through
`cramer_lower_legendre_phaseC_partial_discharge`, the `@[entry_point]`
`cramer_tendsto_phaseC_partial_discharge`, and `cramer_lower_phaseC_residual_discharge`
(`InfinitePiTiltedChangeOfMeasure.lean`).

WIRED 2026-06-11 (`cramer-root-wiring-plan` Phase A): the former CLT-boundary
`sorry` is now **discharged** by the sorryAx-free headline
`CramerCltBoundary.cramer_lower_boundary_unconditional` (verbatim-matching
conclusion, internal-point form `a = deriv cgf lam`). The import cycle was broken
by hoisting the change-of-measure machinery to the upstream module
`CramerBoundaryUpstream.lean`, so the headline file is now an upstream supplier
and can be imported here. The headline requires the non-degeneracy precondition
`hVar` (`0 < Var[Y∘eval 0; infinitePi (μ₀.tilted (lam·Y))]`), which is added to
this signature as a regularity precondition (NOT load-bearing core: the window
mass is supplied internally by the CLT inside the headline; `hVar` only excludes
the degenerate constant-RV case where the Gaussian-median / window-mass argument
breaks). `_h_deriv` is activated (`h_deriv`) to pin the optimal tilt. -/
theorem cramer_lower_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_deriv : deriv (cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀))) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
  CramerCltBoundary.cramer_lower_boundary_unconditional
    hY_meas h_bdd a lam hlam h_deriv hVar h_coboundedBelow

/-- **Cramér lower bound (Legendre form), Phase C partial discharge**.

L-MIG-1: `hlam_opt` restored as regularity precondition (audit-2 verdict).
The root `cramer_lower_phaseC_partial_discharge` is now sorryAx-free (discharged
by the CLT-boundary headline), so this wrapper is too.

DEF-FIX 2026-06-11: honest-inheriting. The root
`cramer_lower_phaseC_partial_discharge` now carries the optimal-tilt hypothesis
`(h_deriv : deriv (cgf …) lam = a)` (true-as-stated); this wrapper threads
`h_deriv` through alongside the `hlam_opt` Legendre-attainment hypothesis (the
two are distinct regularity preconditions: `hlam_opt` bridges the conclusion to
`cramerRate`, `h_deriv` pins the optimal tilt).

WIRED 2026-06-11 (`cramer-root-wiring-plan` Phase A a3): the root now also
requires the non-degeneracy precondition `hVar`; it is threaded through here as a
regularity precondition (not load-bearing, see the root docstring). The root is
now sorryAx-free, so this wrapper is too. -/
theorem cramer_lower_legendre_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt :
      lam * a
          - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
              (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
        = cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)
    (h_deriv : deriv (cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀))) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀)) a
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  have h := cramer_lower_phaseC_partial_discharge
    (μ₀ := μ₀) hY_meas h_bdd a lam hlam h_deriv hVar h_coboundedBelow
  rw [← hlam_opt]; exact h

/-- **Cramér's theorem (`Tendsto` form), Phase C partial discharge**.

L-MIG-1: `hlam_opt` restored as regularity precondition (audit-2 verdict).
Sandwich of `cramer_upper_legendre` (constructive) and
`cramer_lower_legendre_phaseC_partial_discharge` (now sorryAx-free via the
CLT-boundary headline through `cramer_lower_phaseC_partial_discharge`).

WIRED 2026-06-11 (`cramer-root-wiring-plan` Phase A): the lower-bound leg now
runs through the sorryAx-free root (discharged by the CLT-boundary headline);
this `@[entry_point]` is therefore now sorryAx-free. The root's non-degeneracy
precondition `hVar` is threaded through here as a regularity precondition. -/
@[entry_point]
theorem cramer_tendsto_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt :
      lam * a
          - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
              (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
        = cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)
    (h_deriv : deriv (cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀))) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_pos : ∀ᶠ n : ℕ in atTop,
      0 < (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})
    (h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    Filter.Tendsto (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop
      (𝓝 (-cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)) := by
  -- Phase A plumbing: infinite-product i.i.d. structure.
  have h_indep : iIndepFun (fun i : ℕ => fun ω : ℕ → Ω₀ => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
    iIndepFun_eval_under_infinitePi (μ₀ := μ₀) hY_meas
  have h_meas : ∀ i, Measurable (fun ω : ℕ → Ω₀ => Y (ω i)) :=
    fun i => hY_meas.comp (measurable_pi_apply i)
  have h_ident : ∀ i, IdentDistrib
      (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) :=
    fun i => identDistrib_eval_under_infinitePi hY_meas i
  have h_bdd_eval : ∃ M, ∀ i ω, |(fun (ω : ℕ → Ω₀) => Y (ω i)) ω| ≤ M := by
    obtain ⟨M, hM⟩ := bounded_eval_family h_bdd
    exact ⟨M, hM⟩
  -- Upper bound (constructive, through Cramer.cramer_upper_legendre).
  have h_upper :
      limsup (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop
        ≤ -cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a :=
    cramer_upper_legendre (μ := Measure.infinitePi (fun _ : ℕ => μ₀))
      h_indep h_meas h_ident h_bdd_eval a lam hlam hlam_opt h_pos h_cobdd
  -- Lower bound (sorryAx-free via cramer_lower_phaseC_partial_discharge).
  have h_lower :
      -cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
          (Measure.infinitePi (fun _ : ℕ => μ₀)) a
        ≤ liminf (fun n : ℕ =>
            (1 / (n : ℝ)) * Real.log
              ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
    cramer_lower_legendre_phaseC_partial_discharge
      (μ₀ := μ₀) hY_meas h_bdd a lam hlam hlam_opt h_deriv hVar h_coboundedBelow
  exact tendsto_of_le_liminf_of_limsup_le h_lower h_upper h_bdd_above h_bdd_below

/-! ## Phase C-4 — sanity corollary: predicate triviality cases

These corollaries are not part of the main discharge but illustrate the
predicate's interface. They are kept minimal and trivial. -/

/-- The predicate is monotone in the un-tilted ambient: if it holds for one
choice of `μ₀`, the consequent inequality is parameterized by `a` and `ε`. The
following helper records the predicate's defining shape `∀ a ε, ... ∃ C ...`
for downstream callers who want to inline the construction. -/
@[entry_point]
lemma isMeasureInfinitePiTiltedEq_iff (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam ↔
      ∀ a ε : ℝ, 0 < ε →
        ∃ C > 0, ∀ᶠ n : ℕ in atTop,
          C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
            ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} :=
  Iff.rfl

end InformationTheory.Shannon.Cramer.Discharge
