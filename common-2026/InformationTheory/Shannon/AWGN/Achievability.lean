import InformationTheory.Shannon.AWGN.Basic

/-!
# T2-A Phase B: AWGN channel coding theorem — achievability (Tier 2 sorry form)

Cover-Thomas Ch.9.2 (sphere packing / continuous joint typicality / Gaussian
random codebook) を **Tier 2 (`sorry + @residual`) 形** で publish。

実体 (continuous joint typical set on `ℝⁿ × ℝⁿ`, Gaussian random codebook,
continuous AEP の 3 つの bounds, sphere volume formula) は別 plan
`docs/shannon/awgn-achievability-typicality-plan.md` (Tier 3) に defer。

**2026-05-27 F-1/F-3 peer migration**: previously `IsAwgnTypicalityHypothesis`
load-bearing predicate (circular passthrough) を Tier 5 として保持していたが、
peer F-3 と同時に第一選択 migration (predicate 削除 + body `sorry` +
`@residual(plan:awgn-achievability-typicality-plan)`、Tier 5 → Tier 2)。
analytic body 完成は successor plan に委ね、本 file の signature は genuine
conclusion を直接 statement に。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Achievability — `awgn_achievability` (Tier 2 sorry + @residual) -/

/-- **AWGN achievability theorem (Cover-Thomas 9.1.1)**.

For any rate `R < C = (1/2) log(1+P/N)` and target error probability `ε > 0`,
there exists `N₀` such that for every block length `n ≥ N₀`, there is an
`AwgnCode` (output power ≤ `P`, measurable decoder) with `M ≥ ⌈exp(nR)⌉`
messages whose per-message error probability is below `ε`.

**2026-05-27 F-1/F-3 peer migration**: previously a load-bearing hypothesis
wrapper consuming `h_typicality : IsAwgnTypicalityHypothesis P N h_meas`
(itself a circular passthrough of this very conclusion). The predicate
`IsAwgnTypicalityHypothesis` is now removed and the body is honestly marked
`sorry` with `@residual(plan:awgn-achievability-typicality-plan)`. The
analytic content (sphere packing on `ℝⁿ`, Gaussian random codebook, three
continuous-AEP bounds, union bound on `M` codewords) is the work of
`awgn-achievability-typicality-plan.md`; the genuine 580-line assembly is
already present in `AWGNAchievabilityDischarge.isAwgnTypicalityHypothesis`
(under the now-removed predicate name, return type inline-expanded by this
migration), and discharging the remaining `IsAwgnRandomCodingFeasible`
bundle in that file is what closes this `sorry`.

`@audit:closed-by-successor(awgn-achievability-typicality-plan)` `@residual(plan:awgn-achievability-typicality-plan)` -/
theorem awgn_achievability
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε := by
  sorry

end InformationTheory.Shannon.AWGN
