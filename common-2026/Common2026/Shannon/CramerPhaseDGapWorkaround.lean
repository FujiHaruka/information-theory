import Common2026.Shannon.CramerLC2PhaseC
import Common2026.Shannon.ChernoffPerTiltDischarge
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Cramér Phase D Mathlib-gap workaround — `cylinderEvent` route (T1-C wave7)

This file extends `Common2026/Shannon/CramerLC2PhaseC.lean` (Phase C
`IsMeasureInfinitePiTiltedEq` partial discharge) by **refining** the n-letter
Radon-Nikodym derivative identification into a *cylinder-event* primitive
predicate, and publishing the corresponding **Phase D** wrappers.

## Context recap (wave6 / wave7 alignment)

`CramerLC2PhaseC.lean` (wave5/wave6) abstracted the missing Mathlib lemma
`Measure.infinitePi_tilted_eq` (the n-letter RN-deriv identification of the
tilted infinite product) as a single asymptotic predicate
`IsMeasureInfinitePiTiltedEq`. In parallel, the Chernoff converse hit the
**structurally identical** Mathlib gap and was abstracted as
`IsBayesErrorPerTiltLowerBound` in `ChernoffPerTiltDischarge.lean`. Both
predicates record an asymptotic exponential lower bound for the un-tilted
product measure of an upper-tail event, the gap being the Mathlib n-letter
RN-deriv construction (~500 lines).

Wave7 publishes the **cylinder-event refinement**: the predicate is rewritten
in terms of `MeasureTheory.cylinder` (the Mathlib cylinder-event primitive),
exposing the *cylinder-of-width-n* structure of the n-letter RN-deriv
identification. This allows downstream callers (a future full Carathéodory
extension) to plug in a cylinder-level density and obtain the predicate, via
the `IsCaratheodoryExtensionHyp` pass-through.

## What this file publishes

### Phase D-1 — cylinder-event refinement of the predicate

* `IsCramerNLetterRNCylinder μ₀ Y lam` — cylinder-event-shaped variant of
  `IsMeasureInfinitePiTiltedEq` exposing the Finset.range n cylinder structure.

### Phase D-2 — Carathéodory extension pass-through

* `IsCaratheodoryExtensionHyp μ₀ Y lam` — pass-through predicate recording the
  Carathéodory extension hypothesis from the cylinder σ-algebra to the full
  infinite-product measure (retreat line: the Carathéodory extension is itself
  a Mathlib gap, abstracted as a hypothesis).

### Phase D-3 — bridge cylinder → predicate

* `isMeasureInfinitePiTiltedEq_of_cylinder_density` — cylinder form +
  Carathéodory pass-through → `IsMeasureInfinitePiTiltedEq` (the Phase C
  predicate).

### Phase D-4 — discharged wrappers

* `cramer_phase_d_via_cylinder` — Phase C `cramer_tendsto_phaseC_partial_-
  discharge` rerouted through the cylinder form: input is the cylinder-level
  predicate + Carathéodory pass-through.

### Phase D-5 — Cramér × Chernoff unification

* `IsCramerChernoffNLetterRNUnified` — single predicate capturing **both**
  Cramér's `IsMeasureInfinitePiTiltedEq` and Chernoff's
  `IsBayesErrorPerTiltLowerBound`. Records the wave7 finding that the two
  Mathlib gaps are structurally one and the same.

## Retreat lines

The full Carathéodory extension construction (cylinder density → infinite-
product measure agreement) is the Mathlib gap we workaround. We abstract it
as `IsCaratheodoryExtensionHyp` pass-through and publish the cylinder-form
predicate as the main deliverable.
-/

namespace InformationTheory.Shannon.Cramer.PhaseDGapWorkaround

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Real Filter
open InformationTheory.Shannon.Cramer.Discharge
open InformationTheory.Shannon.ChernoffPerTiltDischarge
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## Phase D-1 — cylinder-event refinement of the Phase C predicate -/

/-- **Cylinder-event variant** of `IsMeasureInfinitePiTiltedEq`.

Exposes the cylinder-of-width-`n` structure of the n-letter RN-deriv
identification: the upper-tail event
`{ω | a·n ≤ ∑ i ∈ Finset.range n, Y (ω i)}` is in fact a `MeasureTheory.cylinder
(Finset.range n) _` (it only depends on coordinates `0, …, n-1`). The
cylinder form records the exponential lower bound on the un-tilted product
measure restricted to such cylinders.

`@audit:retract-candidate(load-bearing-predicate)` — all *hypothesis-form
load-bearing* consumers were retreated in the 2026-05-25 Cramér sorry-migration
sweep (Phase 2.3). The predicate now only appears as a structure field of
`IsCramerChernoffNLetterRNUnified` (producer-side bundling, retained for the
Chernoff family sweep). -/
def IsCramerNLetterRNCylinder (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      ∀ (S : Set ((i : Finset.range n) → Ω₀)),
        MeasurableSet S →
        cylinder (Finset.range n) S =
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} →
        C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
          ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real (cylinder (Finset.range n) S)

/-! ## Phase D-2 — Carathéodory extension pass-through -/

/-- **Carathéodory extension pass-through** (Mathlib-gap abstraction).

Records the (currently missing) Mathlib lemma: a measurable upper-tail event
`{ω : ℕ → Ω₀ | a·n ≤ ∑ i ∈ Finset.range n, Y (ω i)}` factors through the
cylinder σ-algebra at width `n`, i.e. is presentable as
`cylinder (Finset.range n) S` for some measurable `S`. This is true in
principle (the event depends only on the first `n` coordinates), but Mathlib
does not yet have the corresponding `cylinderClosure` / `cylinderOfDependsOn`
lemma in the form we need. We abstract it as a pass-through.

`@audit:retract-candidate(load-bearing-predicate)` — all *hypothesis-form
load-bearing* consumers were retreated in the 2026-05-25 Cramér sorry-migration
sweep (Phase 2.3). The predicate now only appears as a structure field of
`IsCramerChernoffNLetterRNUnified` (producer-side bundling, retained for the
Chernoff family sweep). -/
def IsCaratheodoryExtensionHyp (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a : ℝ, ∀ n : ℕ,
    ∃ (S : Set ((i : Finset.range n) → Ω₀)), MeasurableSet S ∧
      cylinder (Finset.range n) S =
        {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}

/-! ## Phase D-3 — bridge cylinder → IsMeasureInfinitePiTiltedEq -/

/-- **Cylinder ↦ Phase C predicate bridge** (Mathlib-gap workaround).

The Phase C predicate `IsMeasureInfinitePiTiltedEq` is the cylinder-level
density (the primitive Mathlib gap: cylinder-form n-letter Radon–Nikodym
derivative identification) wrapped together with a Carathéodory extension. The
cylinder + Carathéodory hypotheses are themselves Mathlib gaps, so this bridge
remains a load-bearing residual deferred to `cramer-moonshot-plan` (Phase D).

`@residual(plan:cramer-moonshot-plan)` -/
lemma isMeasureInfinitePiTiltedEq_of_cylinder_density
    (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam := by
  sorry

/-! ## Phase D-4 — discharged wrappers (Phase D = cylinder-form Phase C) -/

/-- **Cramér lower bound, Phase D via cylinder density**.

Routes the Phase C partial discharge through the cylinder-form n-letter RN-deriv
identification + Carathéodory pass-through. Both are Mathlib gaps abstracted as
hypotheses upstream; closure deferred to `cramer-moonshot-plan` (Phase D).
Transitive `sorry` via `cramer_lower_phaseC_partial_discharge` (Phase 2.2 of
the Cramér sorry-migration sweep).

`@residual(plan:cramer-moonshot-plan)` -/
theorem cramer_lower_phase_d_via_cylinder
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

/-- **Cramér tendsto form, Phase D via cylinder density**. The full `Tendsto`
form.

L-MIG-1: `hlam_opt` restored as regularity precondition (audit-2 verdict).
Sandwich of `cramer_upper_legendre` (constructive) and
`cramer_lower_phase_d_via_cylinder` (transitive sorry via
`cramer_lower_phaseC_partial_discharge`, cylinder + Carathéodory Mathlib
gaps deferred to `cramer-moonshot-plan` Phase D). -/
theorem cramer_tendsto_phase_d_via_cylinder
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
  -- Phase A plumbing: infinite-product i.i.d. structure for the upper bound.
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
  -- Lower bound (transitive sorry via cramer_lower_phase_d_via_cylinder, rate
  -- form), Legendre-rewrite using hlam_opt.
  have h_lower_rate :
      -(lam * a
          - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
              (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
        ≤ liminf (fun n : ℕ =>
            (1 / (n : ℝ)) * Real.log
              ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop :=
    cramer_lower_phase_d_via_cylinder
      (μ₀ := μ₀) hY_meas h_bdd a lam hlam h_coboundedBelow
  have h_lower :
      -cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
          (Measure.infinitePi (fun _ : ℕ => μ₀)) a
        ≤ liminf (fun n : ℕ =>
            (1 / (n : ℝ)) * Real.log
              ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
    rw [← hlam_opt]; exact h_lower_rate
  exact tendsto_of_le_liminf_of_limsup_le h_lower h_upper h_bdd_above h_bdd_below

/-! ## Phase D-5 — Cramér × Chernoff unification predicate

Wave7 finding: the Mathlib gaps in `CramerLC2PhaseC.IsMeasureInfinitePiTiltedEq`
and `ChernoffPerTiltDischarge.IsBayesErrorPerTiltLowerBound` are structurally
**one and the same** (both are n-letter RN-deriv identifications of an
infinite-product tilt, abstracted as asymptotic predicates). The following
predicate captures both as a single conjunction, recording the unification. -/

/-- **Cramér × Chernoff unification predicate**. A single predicate carrying
both the Cramér n-letter RN-deriv identification (cylinder form) and a
Chernoff-side per-tilt lower bound for a finite-alphabet pair `P₁ P₂`,
recording the structural identity of the two Mathlib gaps. -/
structure IsCramerChernoffNLetterRNUnified
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ)
    (P₁ P₂ : α → ℝ) (lamCh : ℝ) : Prop where
  /-- The Cramér-side cylinder predicate. -/
  cramer : IsCramerNLetterRNCylinder μ₀ Y lam
  /-- The Carathéodory extension pass-through, paired with the cylinder
  predicate (the Cramér gap is fully primitive at the cylinder level). -/
  cara   : IsCaratheodoryExtensionHyp μ₀ Y lam
  /-- The Chernoff-side per-tilt lower-bound predicate. -/
  chernoff : IsBayesErrorPerTiltLowerBound P₁ P₂ lamCh

/-- **Cramér projection** from the unified predicate. Transitive `sorry` via
`isMeasureInfinitePiTiltedEq_of_cylinder_density`; the unified predicate
bundles cylinder + Carathéodory Mathlib gaps deferred to
`cramer-moonshot-plan` (Phase D).

NOTE (2026-05-25 sorry-migration sweep): the load-bearing
`h : IsCramerChernoffNLetterRNUnified ...` argument was removed from the
signature in Phase 2.3.4. After removal, the implicit parameters
`{α : Type*} [Fintype α] [DecidableEq α] {P₁ P₂ : α → ℝ} {lamCh : ℝ}` are
**vestigial** — they no longer appear in the conclusion `IsMeasureInfinitePiTiltedEq μ₀ Y lam`
and there is no `h.cramer`/`h.cara` extraction in the body. The lemma is now
claim-equivalent to `isMeasureInfinitePiTiltedEq_of_cylinder_density` modulo
the `IsCramerChernoffNLetterRNUnified.` namespace prefix (kept as a structure
projection name, but no longer a true projection). Future cleanup may either
restore the `h` argument (paired with a constructive body using `h.cramer` +
`h.cara`) or fold this declaration into `_of_cylinder_density` directly.

`@residual(plan:cramer-moonshot-plan)` -/
lemma IsCramerChernoffNLetterRNUnified.cramerPhaseC
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ₀ : Measure Ω₀} {Y : Ω₀ → ℝ} {lam : ℝ}
    {P₁ P₂ : α → ℝ} {lamCh : ℝ} :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam := by
  sorry

/-- **Chernoff projection** from the unified predicate. -/
lemma IsCramerChernoffNLetterRNUnified.chernoffPerTilt
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ₀ : Measure Ω₀} {Y : Ω₀ → ℝ} {lam : ℝ}
    {P₁ P₂ : α → ℝ} {lamCh : ℝ}
    (h : IsCramerChernoffNLetterRNUnified μ₀ Y lam P₁ P₂ lamCh) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lamCh :=
  h.chernoff

/-! ## Phase D-6 — defining unfold lemmas -/

/-- **Unfold** for `IsCramerNLetterRNCylinder`. -/
lemma isCramerNLetterRNCylinder_iff
    (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) :
    IsCramerNLetterRNCylinder μ₀ Y lam ↔
      ∀ a ε : ℝ, 0 < ε →
        ∃ C > 0, ∀ᶠ n : ℕ in atTop,
          ∀ (S : Set ((i : Finset.range n) → Ω₀)),
            MeasurableSet S →
            cylinder (Finset.range n) S =
                {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} →
            C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
              ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
                  (cylinder (Finset.range n) S) :=
  Iff.rfl

/-- **Unfold** for `IsCaratheodoryExtensionHyp`. -/
lemma isCaratheodoryExtensionHyp_iff
    (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) :
    IsCaratheodoryExtensionHyp μ₀ Y lam ↔
      ∀ a : ℝ, ∀ n : ℕ,
        ∃ (S : Set ((i : Finset.range n) → Ω₀)), MeasurableSet S ∧
          cylinder (Finset.range n) S =
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} :=
  Iff.rfl

end InformationTheory.Shannon.Cramer.PhaseDGapWorkaround
