import Common2026.Shannon.AWGN

/-!
# T2-A Phase C: AWGN channel coding theorem — converse (Tier 2 sorry form)

Cover-Thomas Ch.9.1.2 (converse) を **Tier 2 (`sorry + @residual`) 形** で publish。

Converse 経路は標準的に:
1. Fano: `log M ≤ I(W; Ŵ) + binEntropy(Pe) + Pe·log(M-1)` を `fano_inequality_measure_theoretic`
   (`Common2026/Fano/Measure.lean`) で `X := Fin M`, `Y := (Fin n → ℝ)` 再利用。
2. Data processing: `I(W; Ŵ) ≤ I(X^n; Y^n)` (encoder/decoder の関数性).
3. Chain rule + memoryless: `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)`.
4. Per-letter max-entropy (`differentialEntropy_le_gaussian_of_variance_le`,
   4-hypothesis 形): `I(X_i; Y_i) ≤ (1/2) log(1+P/N)`.
5. 合計: `log M ≤ n·(1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`.

実体 (Fano + chain rule + per-letter max-entropy 連鎖) は別 plan
`docs/shannon/awgn-converse-aux-plan.md` (Tier 3) に defer。

**2026-05-27 F-1/F-3 peer migration**: previously `IsAwgnConverseHypothesis`
load-bearing predicate (circular passthrough) を Tier 5 として保持していたが、
peer F-1 と同時に第一選択 migration (predicate 削除 + body `sorry` +
`@residual(plan:awgn-converse-aux-plan)`、Tier 5 → Tier 2)。analytic body 完成
は successor plan に委ね、本 file の signature は genuine conclusion を直接 statement に。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Converse — `awgn_converse` (Tier 2 sorry + @residual) -/

/-- **AWGN converse theorem (Cover-Thomas 9.1.2)**.

For every code with `M ≥ 2` messages, block length `n`, output power constraint
`P` and average error probability `Pe`, the rate satisfies

`log M ≤ n·(1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`.

**2026-05-27 F-1/F-3 peer migration**: previously a load-bearing hypothesis
wrapper consuming `h_converseBound_lbh : IsAwgnConverseHypothesis P N h_meas`
(itself a circular passthrough of this very conclusion). The predicate
`IsAwgnConverseHypothesis` is now removed and the body is honestly marked
`sorry` with `@residual(plan:awgn-converse-aux-plan)`. The genuine analytic
content (Fano data processing + chain rule + per-letter Gaussian max-entropy
+ integrability) is the work of `awgn-converse-aux-plan.md`.

Load-bearing pieces awaited from the successor plan:
* Fano's inequality (`fano_inequality_measure_theoretic`),
* Data processing for `I(W; Ŵ) ≤ I(X^n; Y^n)`,
* Chain rule `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` for memoryless channel,
* Per-letter max-entropy `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` (Gaussian Y_i bound),
* Per-letter integrability hypotheses for `differentialEntropy_le_gaussian_of_variance_le`.

`@audit:closed-by-successor(awgn-converse-aux-plan)` `@residual(plan:awgn-converse-aux-plan)` -/
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M)
    (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  sorry

end InformationTheory.Shannon.AWGN
