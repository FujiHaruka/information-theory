/-
PROBE — not an in-project asset.  Written by the N2 independent audit (leg N2-audit)
as the machine test of attack axis 1: is the computable-analysis layer (N2 core theorems
1-7) required in order to *state* the completion condition of the parent plan's section 0?

Nothing here is imported by `InformationTheory/`.  Nothing here is proved: the two
`Prop`-valued definitions below are statements, and the probe measures only what stating
them costs.  Stating is not proving.
-/
import Mathlib.Computability.Halting
import Mathlib.Data.Rat.Denumerable
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Metric

namespace ProbeGoal

/-- A broadcast channel given by an explicit rational transition matrix on finite alphabets:
a fully discrete, `Primcodable` description. -/
abbrev RatBC (a b c : ℕ) : Type := Fin (a * (b * c)) → ℚ

instance (a b c : ℕ) : Primcodable (RatBC a b c) := inferInstance

/-- The output of an approximation procedure: a finite list of rational rate pairs. -/
abbrev RatRegion : Type := List (ℚ × ℚ)

/-- What the returned finite list denotes in the plane. -/
def ratRegionSet (L : RatRegion) : Set (ℝ × ℝ) :=
  {p | ∃ q ∈ L, p = ((q.1 : ℝ), (q.2 : ℝ))}

/-- The positive side of the parent plan's section 0: a procedure that, given a channel and
an `ε > 0`, returns in finite time a rational object within `ε` of the capacity region.
`C` is the capacity region, taken here as an arbitrary parameter, since the probe measures
the cost of the statement and not of any particular region.

Every type crossing the computability predicate is discrete and `Primcodable`; no predicate
of computable analysis (effectively open / closed / compact, overtness, uniform `Π01`)
appears. -/
def GoalPositive (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) : Prop :=
  ∃ f : RatBC a b c × ℚ → RatRegion, Computable f ∧
    ∀ (W : RatBC a b c) (ε : ℚ), 0 < ε →
      hausdorffDist (C W) (ratRegionSet (f (W, ε))) ≤ (ε : ℝ)

/-- The negative side of section 0: no such procedure exists. -/
def GoalNegative (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) : Prop :=
  ¬ GoalPositive a b c C

/-- The two sides are exclusive and exhaustive, which is all the probe can prove about
them without a construction on one side or a reduction on the other. -/
theorem goal_dichotomy (a b c : ℕ) (C : RatBC a b c → Set (ℝ × ℝ)) :
    GoalPositive a b c C ↔ ¬ GoalNegative a b c C :=
  (not_not).symm

end ProbeGoal
