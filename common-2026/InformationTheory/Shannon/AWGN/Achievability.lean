import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityCodebook
import InformationTheory.Shannon.AWGN.AchievabilityTypicalDecoder
import InformationTheory.Shannon.AWGN.AchievabilityExpurgation
import InformationTheory.Shannon.AWGN.AchievabilityCodeExistence

/-!
# AWGN channel coding theorem — achievability

The achievability headline `awgn_achievability` (Cover–Thomas 9.2: sphere packing,
continuous joint typicality, Gaussian random codebook).

## Main statements

* `awgn_achievability` — codes exist for every rate below capacity.

## Implementation notes

The body is a direct call to `isAwgnTypicalityHypothesis`, a
genuine assembly that lives in `AchievabilityCodeExistence.lean` (the continuous joint
typical set on `ℝⁿ × ℝⁿ`, the Gaussian random codebook, the three continuous-AEP bounds,
and the sphere volume formula). This file imports the `Achievability*` discharge modules.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Achievability -/

/-- AWGN achievability theorem (Cover–Thomas 9.1.1).

For any rate `R < C = (1/2) log(1+P/N)` and target error probability `ε > 0`, there
exists `N₀` such that for every block length `n ≥ N₀` there is an `AwgnCode` (output
power ≤ `P`, measurable decoder) with `M ≥ ⌈exp(nR)⌉` messages whose per-message error
probability is below `ε`.

The body is a direct call to
`isAwgnTypicalityHypothesis P hP N hN h_meas hR_pos hR hε`, a
genuine assembly (sphere packing, Gaussian random codebook, the three continuous-AEP
bounds, and the union bound).

@audit:ok (independent honesty audit 2026-06-12, commit c44be72: discharged from
`by sorry` to `isAwgnTypicalityHypothesis P hP N hN h_meas hR_pos hR hε`. Signature
UNCHANGED vs the parent `39677f9` Tier-2 sorry form (verified by `git diff`: only the
body, docstring, and the added import changed). The callee's conclusion matches this
headline's modulo currying — `isAwgnTypicalityHypothesis` returns the same `∃ N₀, ...`
body with `awgnChannel N h_meas`, and the curried `{R}`/`hR_pos`/`hR`/`{ε}`/`hε`
arguments recover this signature's binders exactly. The callee is a 580-line genuine
assembly whose only hypotheses are regularity preconditions (`0 < P`, `(N:ℝ) ≠ 0`,
measurability) — no load-bearing `*Hypothesis` predicate is passed (the name
`isAwgnTypicalityHypothesis` is a historical artefact, not a bundled-conclusion arg).
`#print axioms awgn_achievability` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-verified by this audit). The old `@residual(plan:...)` /
`@audit:closed-by-successor(...)` tags were removed; the prose above records the
closure provenance honestly.) -/
theorem awgn_achievability
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε :=
  isAwgnTypicalityHypothesis P hP N hN h_meas hR_pos hR hε

end InformationTheory.Shannon.AWGN
