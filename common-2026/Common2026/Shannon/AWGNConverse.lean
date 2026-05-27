import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNConverseDischarge

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

**2026-05-27 F-3 wiring (`awgn-main-converse-wiring`)**: `awgn_converse` body は
`AWGNConverseDischarge.awgn_converse_F3_discharged` への 1 行 `exact` で discharge
済。新引数 3 件 (`h_feasible : IsAwgnConverseFeasible …` / `h_mi_bridge_per_letter`
/ `hn_pos`) を pass-through。file scope では **0 sorry / 0 @residual**、transitive
wall (`@residual(wall:multivariate-mi)`、`AWGNConverseDischarge.lean:406`) のみ
upstream private 経由で間接残置。import 方向は `AWGNConverse → AWGNConverseDischarge`
に flip (循環解消、旧 `AWGNConverseDischarge → AWGNConverse` import を削除)。
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

**2026-05-27 F-3 wiring (`awgn-main-converse-wiring`)**: body is now a
1-line `exact` to `awgn_converse_F3_discharged` (`AWGNConverseDischarge.lean`),
which packages the analytic content (Fano + DPI + chain rule + per-letter
Gaussian max-entropy + sum-form integration) behind the bundle predicate
`IsAwgnConverseFeasible P N h_meas` plus a Real-form per-letter MI bridge
hypothesis `h_mi_bridge_per_letter`. At file scope this declaration is **0
sorry / 0 @residual**; the remaining transitive Mathlib wall
`@residual(wall:multivariate-mi)` lives privately at
`AWGNConverseDischarge.lean:406` (`awgnConverseJoint_pair_mi_ne_top`) and is
not exposed in this signature.

The three new hypotheses pass-through to `_F3_discharged`:
* `h_feasible : IsAwgnConverseFeasible P N h_meas` — bundle of 3 regularity
  sub-bounds (per-letter integrability / continuous MI chain rule / Markov-side
  regularity), see `AWGNConverseDischarge.lean` for sub-predicate definitions.
* `h_mi_bridge_per_letter` — Real-form per-letter MI = `h(Y_i) - h(Z)` bridge,
  awaiting F-2 closure (`awgn-mi-bridge-plan.md`).
* `hn_pos : 0 < n` — block length positivity (vacuous case `n = 0` excluded).

`@audit:closed-by-successor(awgn-converse-aux-plan, wall-multivariate-mi)` -/
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - Common2026.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) :=
  awgn_converse_F3_discharged P hP N hN h_meas h_feasible
    h_mi_bridge_per_letter hM hn_pos c Pe hPe

end InformationTheory.Shannon.AWGN
