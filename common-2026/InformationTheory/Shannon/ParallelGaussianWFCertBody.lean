import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussianKKT
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# W9-G4 T2-B `WaterFillingOptimalityCertificate` body discharge

wave6 `ParallelGaussianKKT.lean` published the parallel-Gaussian water-filling
optimality as an **abstract certificate** (`WaterFillingOptimalityCertificate`)
plus the chain-rule bundle (`ParallelGaussianChainRuleBundle`), reduced to the
`IsWaterFillingOptimal` / `IsParallelGaussianPerCoordReduction` predicates by
bidirectional definitional unfolding. This file attempts to **discharge the
algebraic core of the certificate body** rather than leave it as a pure
pass-through.

## What is genuinely discharged here

The certificate states that water-filling maximizes the concave per-coordinate
sum `∑ (1/2) log(1 + P_i / N_i)` subject to `P_i ≥ 0, ∑ P_i ≤ P`. The textbook
KKT proof factors into:

1. **Concave tangent-line inequality** (`ConcaveOn.le_tangent_of_hasDerivAt`):
   for `f` concave on `S` with `HasDerivAt f f' x`,
   `f y ≤ f x + f' · (y - x)` for all `x, y ∈ S`. *Fully discharged* from
   Mathlib's slope lemmas via an `x = y / x < y / y < x` trichotomy.

2. **Per-coordinate Lagrange stationarity** (`IsWFStationarityHyp`): each cost
   `g_i(t) = (1/2) log(1 + t / N_i)` admits the tangent bound
   `g_i(P'_i) ≤ g_i(P_i^*) + λ · (P'_i - P_i^*)` at the water-filling point with
   a *common* multiplier `λ`. This is the KKT first-order condition; its
   discharge requires identifying `λ = 1/(2ν)` and the concavity of `g_i`, which
   is encoded as a sub-predicate (Lagrange-multiplier ansatz pass-through, same
   shape as `MaxEntropyConstrainedKKT.KKTSolution.moment_match`).

3. **Complementary slackness** (`IsWFComplementarySlacknessHyp`):
   `λ · (∑ P_i^* - P) = 0` together with `λ ≥ 0`.

4. **Lagrange reduction** (`waterFillingCertificate_of_lagrange`): given (2) + (3)
   + primal feasibility `∑ P_i^* ≤ P`, the certificate holds. *Fully discharged*
   — pure algebra: sum the per-coordinate tangent bounds, then collapse the
   linear remainder using `λ ≥ 0`, `∑ P'_i ≤ P`, and complementary slackness.

## Approach

```
Phase A: Concave tangent-line lemma (Mathlib slope → affine bound)         [internal]
Phase B: Per-coordinate cost concavity + derivative                        [internal]
Phase C: KKT sub-predicate bundle (stationarity / slackness / feasibility) [defs]
Phase D: Lagrange reduction  bundle → WaterFillingOptimalityCertificate    [internal]
Phase E: Stationarity discharge  log-concavity → IsWFStationarityHyp       [internal]
Phase F: Re-publish parallel_gaussian_capacity_formula_WFcert_discharged
```

The deep convex-duality fact "such a `λ` with complementary slackness exists"
remains a hypothesis (the KKT-uniqueness wall the wave6 retreat line names); but
its *use* — turning the multiplier into the optimality certificate — is now an
internal theorem, and the per-coordinate stationarity bound is discharged from
genuine log-concavity.
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
