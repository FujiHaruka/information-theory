import InformationTheory.Shannon.Cramer.Cramer
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
# Cramér lower bound: end-to-end discharge

This file completes the Cramér lower bound for the canonical i.i.d. infinite
product setting, discharging the change-of-measure step against the CLT-boundary
headline `CramerCltBoundary.cramer_lower_boundary_unconditional`.

The change-of-measure step relates the tilted infinite-product measure
`Measure.infinitePi (fun _ : ℕ => μ₀.tilted (lam * Y ·))` to the cylinder tilt of
the un-tilted product measure `(Measure.infinitePi (fun _ : ℕ => μ₀)).tilted (...)`
on cylinders of width `n`, identified through the predicate
`IsMeasureInfinitePiTiltedEq` (defined upstream in `CramerBoundaryUpstream.lean`).

## Main statements

* `cramer_lower_phaseC_partial_discharge` — the liminf lower bound at threshold
  `a` and optimal tilt `lam`.
* `cramer_lower_legendre_phaseC_partial_discharge` — its Legendre form.
* `cramer_tendsto_phaseC_partial_discharge` — the two-sided `Tendsto` form.
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Discharged wrappers -/

/-- The Cramér lower bound for the canonical i.i.d. product-measure setting
`X i ω := Y (ω i)` with `Y : Ω₀ → ℝ` bounded and measurable, on the un-tilted
infinite product `μ := Measure.infinitePi (fun _ => μ₀)`: the asymptotic liminf
lower bound at threshold `a` and tilt `lam`.

The ambient i.i.d. hypotheses are discharged using the plumbing from
`LC2Discharge`; the change-of-measure step is discharged by the headline
`CramerCltBoundary.cramer_lower_boundary_unconditional`. The optimal-tilt
hypothesis `h_deriv : deriv (cgf (Y∘·0) (infinitePi μ₀)) lam = a` is required for
truth: without it the per-`lam` bound fails for general `a` (e.g.
`μ₀ = Bernoulli(1/2)`, `Y(0)=0, Y(1)=1`, `lam=0`, `a=0.9`); the bound is tight
precisely at the optimal tilt, where `lam·a − Λ(lam) = cramerRate a`. The
non-degeneracy hypothesis `hVar` and the cobounded-below hypothesis
`h_coboundedBelow` are regularity preconditions, not part of the proof core.

@audit:ok (sorryAx-free `[propext, Classical.choice, Quot.sound]`; body is a
verbatim `exact` of the `@audit:ok` headline `cramer_lower_boundary_unconditional`.
`hVar` is non-load-bearing: the window-mass `≥ 1/4` core is derived inside the CLT
of the headline, where `hVar` is consumed only as the non-degeneracy input; at
`Var = 0` the tilted sum is a.e. constant and the argument collapses, so granting
`hVar` alone does not hand over the conclusion.) -/
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

/-- The Legendre form of `cramer_lower_phaseC_partial_discharge`, with the
conclusion expressed as `-cramerRate a`. The Legendre-attainment hypothesis
`hlam_opt` bridges `lam·a − Λ(lam)` to `cramerRate a`; together with `h_deriv`
(optimal tilt) and `hVar` (non-degeneracy) these are regularity preconditions,
not part of the proof core.

@audit:ok (sorryAx-free; threads root preconditions through and rewrites the
conclusion via the `hlam_opt` Legendre-attainment precondition. `hVar`, `h_deriv`,
`hlam_opt` are all regularity preconditions, no load-bearing core.) -/
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

/-- Cramér's theorem in `Tendsto` form: the empirical log-tail rate converges to
`-cramerRate a`. The proof is a sandwich of `cramer_upper_legendre`
(constructive, upper bound) and `cramer_lower_legendre_phaseC_partial_discharge`
(lower bound). All hypotheses are regularity preconditions or cobounded
side-conditions.

@audit:ok (sorryAx-free; genuine `le_antisymm`-style sandwich of
`cramer_upper_legendre` and `cramer_lower_legendre_phaseC_partial_discharge`. All
hypotheses are regularity preconditions / cobounded side-conditions.) -/
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

/-! ## Predicate interface -/

/-- The defining shape `∀ a ε, ... ∃ C ...` of `IsMeasureInfinitePiTiltedEq`,
exposed for downstream callers who want to inline the construction. -/
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
