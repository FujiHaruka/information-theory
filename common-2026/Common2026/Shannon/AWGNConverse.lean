import Common2026.Shannon.AWGN

/-!
# T2-A Phase C: AWGN channel coding theorem — converse (F-3 hypothesis form)

Cover-Thomas Ch.9.1.2 (converse) を **撤退ライン F-3 hypothesis pass-through 形**
で publish。

Converse 経路は標準的に:
1. Fano: `log M ≤ I(W; Ŵ) + binEntropy(Pe) + Pe·log(M-1)` を `fano_inequality_measure_theoretic`
   (`Common2026/Fano/Measure.lean`) で `X := Fin M`, `Y := (Fin n → ℝ)` 再利用。
2. Data processing: `I(W; Ŵ) ≤ I(X^n; Y^n)` (encoder/decoder の関数性).
3. Chain rule + memoryless: `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)`.
4. Per-letter max-entropy (`differentialEntropy_le_gaussian_of_variance_le`,
   4-hypothesis 形): `I(X_i; Y_i) ≤ (1/2) log(1+P/N)`.
5. 合計: `log M ≤ n·(1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`.

撤退ライン **F-3 採用前提**: per-letter `differentialEntropy_le_gaussian_of_variance_le`
の `h_ent_int` (Integrable `negMulLog (rnDeriv μ vol)`) は input law `μ_i` 個別 で
discharge できない可能性が高いため、converse 全体の hypothesis `IsAwgnConverseHypothesis`
に集約 (per-letter integrability + chain rule + Fano data processing + MI bridge を
全部まとめて hypothesis pass-through)。

実体 (Fano + chain rule + per-letter max-entropy 連鎖) は別 plan
`docs/shannon/awgn-converse-aux-plan.md` (Tier 3) に defer。

L-S2 / L-C2 / L-F1+L-F2 と同型 pattern。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## F-3 hypothesis predicate -/

/-- **AWGN converse hypothesis** (Cover-Thomas 9.1.2 schema).

For every block length `n`, message count `M ≥ 2`, AWGN code `c : AwgnCode M n P`,
the converse inequality
`log M ≤ n·(1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`
holds, where `Pe` is the average error probability.

This bundles in one predicate:
* Fano's inequality (`fano_inequality_measure_theoretic`),
* Data processing for `I(W; Ŵ) ≤ I(X^n; Y^n)`,
* Chain rule `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` for memoryless channel,
* Per-letter max-entropy `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` (Gaussian Y_i bound),
* Per-letter integrability hypotheses for `differentialEntropy_le_gaussian_of_variance_le`
  (F-3 撤退ライン's main pain point).

Discharging this predicate (for the canonical AWGN code construction) is deferred
to `awgn-converse-aux-plan.md` (Tier 3 plan). -/
def IsAwgnConverseHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P),
    ∀ (Pe : ℝ)
      (_hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
          (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)),
      Real.log M
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
          + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)

/-! ## Converse — `awgn_converse` (F-3 hypothesis pass-through) -/

/-- 🟢ʰ **load-bearing hypothesis — NOT a discharge.**
**AWGN converse theorem (Cover-Thomas 9.1.2), F-3 hypothesis form**.

For every code with `M ≥ 2` messages, block length `n`, output power constraint
`P` and average error probability `Pe`, the rate satisfies

`log M ≤ n·(1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`.

⚠️ The body is `h_converseBound_lbh hM c Pe hPe`, where
`IsAwgnConverseHypothesis` is *defined to be* the universal converse inequality
itself. The load-bearing hypothesis IS the desired conclusion, packaged as a
named predicate so the theorem can be re-published once F-3 is genuinely
discharged.

Load-bearing pieces bundled inside `h_converseBound_lbh`:
* Fano's inequality (`fano_inequality_measure_theoretic`),
* Data processing for `I(W; Ŵ) ≤ I(X^n; Y^n)`,
* Chain rule `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` for memoryless channel,
* Per-letter max-entropy `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` (Gaussian Y_i bound),
* Per-letter integrability hypotheses (F-3 撤退ライン's main pain point).

Discharging this predicate is deferred to `awgn-converse-aux-plan.md` (Tier 3).

`@audit:suspect(awgn-converse-aux-plan)` -/
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_converseBound_lbh : IsAwgnConverseHypothesis P N h_meas)
    {M n : ℕ} (hM : 2 ≤ M)
    (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) :=
  h_converseBound_lbh hM c Pe hPe

end InformationTheory.Shannon.AWGN
