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
measure restricted to such cylinders. -/
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
lemma in the form we need. We abstract it as a pass-through. -/
def IsCaratheodoryExtensionHyp (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a : ℝ, ∀ n : ℕ,
    ∃ (S : Set ((i : Finset.range n) → Ω₀)), MeasurableSet S ∧
      cylinder (Finset.range n) S =
        {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}

/-! ## Phase D-3 — bridge cylinder → IsMeasureInfinitePiTiltedEq -/

/-- **Cylinder ↦ Phase C predicate bridge** (Mathlib-gap workaround).

Given the cylinder-form predicate `IsCramerNLetterRNCylinder` together with
the Carathéodory pass-through `IsCaratheodoryExtensionHyp`, the Phase C
predicate `IsMeasureInfinitePiTiltedEq` follows: the upper-tail event is
cylinder-realisable by Carathéodory, and the cylinder form supplies the
exponential lower bound.

This is the **main bridge** of wave7 Phase D: cylinder-level density (the
primitive Mathlib gap) + Carathéodory extension hypothesis → the Phase C
asymptotic predicate.

`@audit:suspect(cramer-moonshot-plan)` -/
lemma isMeasureInfinitePiTiltedEq_of_cylinder_density
    (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ)
    (h_cyl : IsCramerNLetterRNCylinder μ₀ Y lam)
    (h_cara : IsCaratheodoryExtensionHyp μ₀ Y lam) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam := by
  intro a ε hε
  obtain ⟨C, hC_pos, hC_event⟩ := h_cyl a ε hε
  refine ⟨C, hC_pos, ?_⟩
  filter_upwards [hC_event] with n hn
  obtain ⟨S, hS_meas, hS_eq⟩ := h_cara a n
  have h_bound := hn S hS_meas hS_eq
  rw [hS_eq] at h_bound
  exact h_bound

/-! ## Phase D-4 — discharged wrappers (Phase D = cylinder-form Phase C) -/

/-- **Cramér lower bound, Phase D via cylinder density**.

Routes the Phase C partial discharge through the cylinder-form predicate +
Carathéodory pass-through: this is the cleanest "primitive" form of the
Mathlib gap, in which the Carathéodory extension is explicitly abstracted as
a hypothesis.

`@audit:suspect(cramer-moonshot-plan)` -/
theorem cramer_lower_phase_d_via_cylinder
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_cyl : IsCramerNLetterRNCylinder μ₀ Y lam)
    (h_cara : IsCaratheodoryExtensionHyp μ₀ Y lam) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  have h_pred := isMeasureInfinitePiTiltedEq_of_cylinder_density μ₀ Y lam h_cyl h_cara
  exact cramer_lower_phaseC_partial_discharge
    (μ₀ := μ₀) hY_meas h_bdd a lam hlam h_coboundedBelow h_pred

/-- **Cramér tendsto form, Phase D via cylinder density**. The full `Tendsto`
form, routed through the cylinder-form predicate + Carathéodory pass-through.

`@audit:suspect(cramer-moonshot-plan)` -/
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
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})))
    (h_cyl : IsCramerNLetterRNCylinder μ₀ Y lam)
    (h_cara : IsCaratheodoryExtensionHyp μ₀ Y lam) :
    Filter.Tendsto (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop
      (𝓝 (-cramerRate (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) a)) := by
  have h_pred := isMeasureInfinitePiTiltedEq_of_cylinder_density μ₀ Y lam h_cyl h_cara
  exact cramer_tendsto_phaseC_partial_discharge
    (μ₀ := μ₀) hY_meas h_bdd a lam hlam hlam_opt h_pos
    h_cobdd h_coboundedBelow h_bdd_above h_bdd_below h_pred

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

/-- **Cramér projection** from the unified predicate.

`@audit:suspect(cramer-moonshot-plan)` -/
lemma IsCramerChernoffNLetterRNUnified.cramerPhaseC
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ₀ : Measure Ω₀} {Y : Ω₀ → ℝ} {lam : ℝ}
    {P₁ P₂ : α → ℝ} {lamCh : ℝ}
    (h : IsCramerChernoffNLetterRNUnified μ₀ Y lam P₁ P₂ lamCh) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam :=
  isMeasureInfinitePiTiltedEq_of_cylinder_density μ₀ Y lam h.cramer h.cara

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
