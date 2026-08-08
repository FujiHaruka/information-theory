/-
PROBE — not an in-project asset.  Written by the N13 adversarial independent audit.
Nothing here is imported by `InformationTheory/`.

Target: the goal statement of `docs/shannon/probes/t3c-n2/r4-goal-statement-discrete.lean`,
which the N13 novelty gate cites (via ledger row `N2-i`) as evidence that the completion
condition of the parent plan's section 0 can be *stated* with zero effectivity predicates.

The definitions below are restated, not imported, so that the test is independent of the
audited file.  The theorem shows the positive side is satisfied by the procedure that
returns the empty list, for every region family whatsoever: `Metric.hausdorffDist s ∅ = 0`
holds unconditionally in Mathlib, because the Hausdorff edistance to the empty set is `⊤`
and `ENNReal.toReal ⊤ = 0`.
-/
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Denumerable
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Metric

namespace ProbeGoalAudit

abbrev RatBC (a b c : ℕ) : Type := Fin (a * (b * c)) → ℚ

instance (a b c : ℕ) : Primcodable (RatBC a b c) := inferInstance

abbrev RatRegion : Type := List (ℚ × ℚ)

def ratRegionSet (L : RatRegion) : Set (ℝ × ℝ) :=
  {p | ∃ q ∈ L, p = ((q.1 : ℝ), (q.2 : ℝ))}

def GoalPositive (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) : Prop :=
  ∃ f : RatBC a b c × ℚ → RatRegion, Computable f ∧
    ∀ (W : RatBC a b c) (ε : ℚ), 0 < ε →
      hausdorffDist (C W) (ratRegionSet (f (W, ε))) ≤ (ε : ℝ)

def GoalNegative (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) : Prop :=
  ¬ GoalPositive a b c C

/-- The empty list denotes the empty set. -/
theorem ratRegionSet_nil : ratRegionSet [] = (∅ : Set (ℝ × ℝ)) := by
  ext p; simp [ratRegionSet]

/-- The positive side holds for every region family, witnessed by the constant
empty-list procedure.  Hence it states nothing about the region. -/
theorem goalPositive_trivial (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) :
    GoalPositive a b c C := by
  refine ⟨fun _ ↦ [], Computable.const _, fun W ε hε ↦ ?_⟩
  rw [ratRegionSet_nil, hausdorffDist_empty]
  exact_mod_cast hε.le

/-- Consequently the negative side is refutable for every region family: the dichotomy of
the audited probe is decided on one side, before any information theory is supplied. -/
theorem goalNegative_false (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) :
    ¬ GoalNegative a b c C :=
  fun h ↦ h (goalPositive_trivial a b c C)

/-- Calibration: the two-sided `ε`-net form, which is what the parent plan's positive side
asks for.  It still mentions no predicate of computable analysis, so the repair does not by
itself restore a need for the `(β)` layer. -/
def GoalPositiveNet (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) : Prop :=
  ∃ f : RatBC a b c × ℚ → RatRegion, Computable f ∧
    ∀ (W : RatBC a b c) (ε : ℚ), 0 < ε →
      (∀ p ∈ C W, ∃ q ∈ f (W, ε), dist p ((q.1 : ℝ), (q.2 : ℝ)) ≤ (ε : ℝ)) ∧
      (∀ q ∈ f (W, ε), ∃ p ∈ C W, dist ((q.1 : ℝ), (q.2 : ℝ)) p ≤ (ε : ℝ))

/-- The net form is not satisfied by the empty-list procedure whenever the region is
nonempty, so the vacuity above is a defect of the audited formulation, not of the goal. -/
theorem net_kills_empty (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) (W : RatBC a b c)
    (ε : ℚ) (h : (C W).Nonempty) :
    ¬ ((∀ p ∈ C W, ∃ q ∈ ([] : RatRegion), dist p ((q.1 : ℝ), (q.2 : ℝ)) ≤ (ε : ℝ)) ∧
      (∀ q ∈ ([] : RatRegion), ∃ p ∈ C W, dist ((q.1 : ℝ), (q.2 : ℝ)) p ≤ (ε : ℝ))) := by
  rintro ⟨hfwd, -⟩
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq, -⟩ := hfwd p hp
  exact absurd hq (List.not_mem_nil)

end ProbeGoalAudit
