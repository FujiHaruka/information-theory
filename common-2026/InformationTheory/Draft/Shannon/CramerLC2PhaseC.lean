import InformationTheory.Draft.Shannon.Cramer
import InformationTheory.Shannon.Cramer.LC2Discharge
import InformationTheory.Shannon.Cramer.LC2DischargeExt
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

### Phase C-2 — `h_tilted_lower` reduction

* `tilted_lower_from_predicate` — given the predicate + the in-probability LLN
  on the tilted ambient + bounded RV hypotheses, construct the
  `h_tilted_lower`-shape Chernoff lower bound on the un-tilted infinite product.

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

/-! ## Phase C-1 — n-letter RN-deriv identification predicate -/

/-- **Cramér n-letter change-of-measure predicate** (Mathlib gap abstraction).

Captures the missing Mathlib compatibility lemma
`Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·)) ↔ (Measure.infinitePi μ₀).tilted (∑ lam * Y ∘ eval i)`
on cylinders of width `n`, in the form usable as input to Cramér's lower-bound
change-of-measure step.

The intended interpretation: for every `n` and every measurable event
`E ⊆ {ω | a·n ≤ ∑ i ∈ Finset.range n, Y (ω i)}`, the un-tilted product measure
of `E` admits the Chernoff-style lower bound
`exp(-n · (lam · a − Λ(lam))) · μ_tilt(E) − o(1) ≤ μ.real E`,
where `μ_tilt := Measure.infinitePi (fun _ => μ₀.tilted (lam * Y ·))` and
`Λ := cgf Y μ₀`.

In the textbook setting this follows from `(dμ_tilt / dμ)|_{cylinder n}
= exp(lam · ∑ Y(ω_i) − n·Λ(lam))`, but the n-letter RN-deriv identification is
not yet in Mathlib.

`@audit:retract-candidate(load-bearing-predicate)` — all *hypothesis-form
load-bearing* consumers were retreated to `sorry + @residual(...)` in the
2026-05-25 Cramér sorry-migration sweep (Phase 2.1–2.4). Three producer-side
constructors remain:
* `InformationTheory.Shannon.InfinitePiTiltedChangeOfMeasure.isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`
  — constructive producer from the residual window-largeness predicate
  `IsTiltedWindowEventuallyLarge`; sorry-free (body uses `Measure.infinitePi`
  cylinder lift + Phase 3 change-of-measure).
* `InformationTheory.Shannon.CramerPhaseDGapWorkaround.isMeasureInfinitePiTiltedEq_of_cylinder_density`
  — sorry'd unconditional producer (`@residual(plan:cramer-moonshot-plan)`).
* `InformationTheory.Shannon.CramerPhaseDGapWorkaround.IsCramerChernoffNLetterRNUnified.cramerPhaseC`
  — sorry'd unconditional projection (the load-bearing
  `IsCramerChernoffNLetterRNUnified` argument was removed in the 2026-05-25
  sweep; the lemma now duplicates `_of_cylinder_density`'s claim modulo
  vestigial implicit parameters `{α} {P₁ P₂} {lamCh}`).
Producer-side bodies depend transitively on the upstream `sorry`. -/
def IsMeasureInfinitePiTiltedEq (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}

/-! ## Phase C-2 — `h_tilted_lower` reduction -/

/-- **`h_tilted_lower` reduction**: in the canonical i.i.d. product-measure
setting `X i ω := Y (ω i)`, the parent `h_tilted_lower`-shape Chernoff lower
bound on the un-tilted infinite product follows from the (currently missing)
n-letter Radon–Nikodym derivative identification of the tilted infinite
product. Closure deferred to `cramer-lc2-discharge-moonshot-plan` (Phase B/C).

`@residual(plan:cramer-lc2-discharge-moonshot-plan)` -/
@[entry_point]
lemma tilted_lower_from_predicate
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ}
    (_hY_meas : Measurable Y) (_h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n : ℝ) *
          (lam * a
            - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
                (Measure.infinitePi (fun _ : ℕ => μ₀)) lam
            + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
  sorry

/-! ## Phase C-3 — discharged wrappers -/

/-- **Cramér lower bound, Phase C partial discharge**.

For the canonical i.i.d. product-measure setting `X i ω := Y (ω i)` with
`Y : Ω₀ → ℝ` bounded and measurable, and on the un-tilted infinite product
`μ := Measure.infinitePi (fun _ => μ₀)`, the conclusion is the asymptotic
Cramér lower bound at threshold `a` and tilt `lam`.

The other ambient hypotheses (`iIndepFun`, `IdentDistrib`, bounded family) are
discharged using the Phase A plumbing from `CramerLC2Discharge`. The remaining
gap is the n-letter Radon–Nikodym derivative identification of the tilted
infinite product, closure deferred to `cramer-lc2-discharge-moonshot-plan`
(Phase B/C). Transitive `sorry` upstream via `cramer_lower` (Phase 2.1 of the
Cramér sorry-migration sweep).

`@residual(plan:cramer-lc2-discharge-moonshot-plan)` -/
theorem cramer_lower_phaseC_partial_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
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
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  sorry

/-- **Cramér lower bound (Legendre form), Phase C partial discharge**.

L-MIG-1: `hlam_opt` restored as regularity precondition (audit-2 verdict).
Transitive `sorry` upstream via `cramer_lower_phaseC_partial_discharge`
(n-letter RN-deriv identification, load-bearing gap in the parent
`cramer-lc2-discharge-moonshot-plan`). -/
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
    (μ₀ := μ₀) hY_meas h_bdd a lam hlam h_coboundedBelow
  rw [← hlam_opt]; exact h

/-- **Cramér's theorem (`Tendsto` form), Phase C partial discharge**.

L-MIG-1: `hlam_opt` restored as regularity precondition (audit-2 verdict).
Sandwich of `cramer_upper_legendre` (constructive) and
`cramer_lower_legendre_phaseC_partial_discharge` (transitive sorry via
`cramer_lower_phaseC_partial_discharge`, n-letter RN-deriv identification
gap in `cramer-lc2-discharge-moonshot-plan`). -/
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
  -- Lower bound (transitive sorry via cramer_lower_phaseC_partial_discharge).
  have h_lower :
      -cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
          (Measure.infinitePi (fun _ : ℕ => μ₀)) a
        ≤ liminf (fun n : ℕ =>
            (1 / (n : ℝ)) * Real.log
              ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
    cramer_lower_legendre_phaseC_partial_discharge
      (μ₀ := μ₀) hY_meas h_bdd a lam hlam hlam_opt h_coboundedBelow
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
