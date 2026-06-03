import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN
import InformationTheory.Shannon.AWGNConverseDischarge

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
`AWGNConverseDischarge.awgn_converse_F3_discharged` への delegation で discharge。
import 方向は `AWGNConverse → AWGNConverseDischarge` に flip (循環解消、旧
`AWGNConverseDischarge → AWGNConverse` import を削除)。

**2026-05-28 Phase 3-α sorry-based migration (`awgn-m5-sorry-migration-plan.md`)**:
旧 load-bearing 引数 2 件 (`h_feasible : IsAwgnConverseFeasible …` + per-letter MI
bridge `h_mi_bridge_per_letter`) を `awgn_converse` signature から除去。
`h_feasible` の analytic content は `AwgnWalls.lean` shared sorry 補題に移管済。
残る `h_mi_bridge_per_letter` (per-letter MI = `h(Y_i) - h(Z)` bridge、F-2 closure
待ち、`awgn-mi-bridge-plan.md`) は published signature から落とし、body 内で
`sorry` (`@residual(plan:awgn-mi-bridge-plan)`) で witness を作って delegate。
本 file は signature が genuine conclusion を直接 statement、sorry 1 件 (Tier 2)。
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

**2026-05-28 Phase 3-α sorry-based migration**: published signature は genuine
conclusion (`log M ≤ n·(1/2) log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`) を直接
statement とし、旧 load-bearing 引数 2 件 (`h_feasible` bundle + per-letter MI
bridge `h_mi_bridge_per_letter`) を除去。`h_feasible` の analytic content は
`AwgnWalls.lean` shared sorry 補題 (`awgnPerLetterIntegrability_holds` /
`awgnContinuousMIChainRule_holds` / `awgnConverseMarkov_holds`) に移管済 (本 file は
それらの呼出を `awgn_converse_F3_discharged` 内部で間接利用)。残る per-letter MI
bridge は F-2 closure 待ち (`awgn-mi-bridge-plan.md`) のため、body 内で `sorry`
として witness を生成し `_F3_discharged` に渡す。

This declaration carries 1 honest `sorry` (the F-2 per-letter MI bridge); the
upstream Mathlib wall `wall:multivariate-mi` (`AWGNConverseDischarge.lean`,
`awgnConverseJoint_pair_mi_ne_top`) and the `AwgnWalls.lean` converse walls
remain transitively in their own files.

@residual(plan:awgn-mi-bridge-plan) -/
@[entry_point]
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  -- per-letter MI bridge (`I(X_i; Y_i) = h(Y_i) - h(Z)`) is the F-2 closure
  -- target (`awgn-mi-bridge-plan.md`); supplied here as an honest residual.
  have h_mi_bridge_per_letter :
      ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
        (perLetterMI h_meas c i).toReal
          = Common2026.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - Common2026.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N) := by
    -- @residual(plan:awgn-mi-bridge-plan)
    sorry
  exact awgn_converse_F3_discharged P hP N hN h_meas
    h_mi_bridge_per_letter hM hn_pos c Pe hPe

end InformationTheory.Shannon.AWGN
