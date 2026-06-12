import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityDischarge

/-!
# T2-A Phase B: AWGN channel coding theorem — achievability (discharged)

Cover-Thomas Ch.9.2 (sphere packing / continuous joint typicality / Gaussian
random codebook) の headline `awgn_achievability` を publish。

**2026-06-12 import 反転 wiring で discharge 済**。body は
`AchievabilityDischarge.isAwgnTypicalityHypothesis` (580 行 genuine assembly、
sorryAx-free) の直接呼出し。本 file は `AchievabilityDischarge` を import する向き
(従来とは逆) になった。実体 (continuous joint typical set on `ℝⁿ × ℝⁿ`, Gaussian
random codebook, continuous AEP の 3 bounds, sphere volume formula) は
`AchievabilityDischarge.lean` に存在。旧 Tier 2 sorry
(`@residual(plan:awgn-achievability-typicality-plan)`) は閉鎖済。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Achievability — `awgn_achievability` (discharged, sorryAx-free) -/

/-- **AWGN achievability theorem (Cover-Thomas 9.1.1)**.

For any rate `R < C = (1/2) log(1+P/N)` and target error probability `ε > 0`,
there exists `N₀` such that for every block length `n ≥ N₀`, there is an
`AwgnCode` (output power ≤ `P`, measurable decoder) with `M ≥ ⌈exp(nR)⌉`
messages whose per-message error probability is below `ε`.

**2026-06-12 import 反転 wiring で discharge**. body =
`AchievabilityDischarge.isAwgnTypicalityHypothesis P hP N hN h_meas hR_pos hR hε`
(580 行 genuine assembly、sorryAx-free) の直接呼出し。旧 Tier 2 sorry
(`@residual(plan:awgn-achievability-typicality-plan)`) は閉鎖。

**migration 履歴**: 2026-05-27 に load-bearing predicate
`IsAwgnTypicalityHypothesis` (circular passthrough) を Tier 2 sorry に migrate
し、analytic content (sphere packing / Gaussian random codebook / 3 continuous-AEP
bounds / union bound) を successor plan `awgn-achievability-typicality-plan.md` に
defer していた。successor 側 assembly が完成 (sorryAx-free) した今、import 方向を
反転して本 file が `AchievabilityDischarge` を import する形にし、headline を genuine
assembly の直接呼出しで閉じた。

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
