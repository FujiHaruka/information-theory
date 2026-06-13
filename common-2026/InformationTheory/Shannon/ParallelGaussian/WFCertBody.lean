import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.KKT
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Concave tangent-line bound (convex-analysis helper)

A standalone convex-analysis lemma: a function concave on a set `S` lies below
its tangent line at any point where it has a derivative,
`f y ≤ f x + f' · (y - x)` for all `x, y ∈ S` with `HasDerivAt f f' x`. It is the
affine-bound restatement of Mathlib's slope inequalities
(`ConcaveOn.slope_le_of_hasDerivAt` / `ConcaveOn.le_slope_of_hasDerivAt`),
obtained by an `x < y` / `x = y` / `y < x` trichotomy.

## Provenance / honest status

This file was originally drafted as **Phase A** of an intended discharge of the
parallel-Gaussian water-filling optimality (`IsWaterFillingOptimal`, the L-WF2
hypothesis carried by `parallel_gaussian_capacity_formula*`). The plan was to
factor the textbook KKT argument into a concave tangent-line bound, a
per-coordinate Lagrange-stationarity discharge, complementary slackness, and a
Lagrange reduction to an optimality certificate.

**Only Phase A (this tangent-line lemma) was ever implemented.** The downstream
phases — `concaveOn_wfCost`, `waterFillingCertificate_of_lagrange`,
`isWFStationarityHyp_of_pos`, `parallel_gaussian_capacity_formula_WFcert_discharged`
and the KKT-internal Lagrange-bundle lemmas — were never written. Consequently
**L-WF2 (`IsWaterFillingOptimal`) remains an open, undischarged hypothesis**: it
is threaded through the capacity-formula headlines as `h_opt`, not proved (see
`Basic.lean` `IsWaterFillingOptimal` def docstring and
`parallel-gaussian-moonshot-plan.md`). The earlier docstring here claimed those
downstream lemmas were "genuinely discharged"; that was false and has been
removed. What survives below is just the general tangent bound.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Concave tangent-line inequality (internal discharge) -/

/-- **Concave tangent-line bound**: a function concave on `S` with a derivative
`f'` at `x` lies below its tangent line at `x`:
`f y ≤ f x + f' · (y - x)` for all `x, y ∈ S`.

This is the affine-bound restatement of Mathlib's slope inequalities
(`ConcaveOn.slope_le_of_hasDerivAt` / `ConcaveOn.le_slope_of_hasDerivAt`),
obtained by an `x = y / x < y / y < x` trichotomy. -/
@[entry_point]
theorem ConcaveOn.le_tangent_of_hasDerivAt {S : Set ℝ} {f : ℝ → ℝ} {x f' : ℝ}
    (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) {y : ℝ} (hy : y ∈ S)
    (hf' : HasDerivAt f f' x) :
    f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · -- x < y : left-endpoint slope bound `slope f x y ≤ f'`.
    have h_slope : slope f x y ≤ f' :=
      hfc.slope_le_of_hasDerivAt hx hy hxy hf'
    rw [slope_def_field] at h_slope
    have hpos : 0 < y - x := by linarith
    -- (f y - f x) / (y - x) ≤ f'  ⇒  f y - f x ≤ f' * (y - x)
    have := (div_le_iff₀ hpos).mp h_slope
    linarith
  · subst hxy; simp
  · -- y < x : right-endpoint slope bound `f' ≤ slope f y x`.
    have h_slope : f' ≤ slope f y x :=
      hfc.le_slope_of_hasDerivAt hy hx hxy hf'
    rw [slope_def_field] at h_slope
    have hpos : 0 < x - y := by linarith
    -- f' ≤ (f x - f y) / (x - y)  ⇒  f' * (x - y) ≤ f x - f y
    have := (le_div_iff₀ hpos).mp h_slope
    nlinarith [this]

/-! ## Phase B — Per-coordinate cost concavity + derivative -/


/-! ## Phase C — KKT sub-predicate bundle -/


/-! ## Phase D — Lagrange reduction (internal discharge) -/


/-! ## Phase E — Stationarity discharge from log-concavity -/


/-! ## Phase F — Re-publish certificate-discharged capacity formula -/


end InformationTheory.Shannon.ParallelGaussian
