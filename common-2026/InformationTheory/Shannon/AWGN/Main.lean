import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.Achievability
import InformationTheory.Shannon.AWGN.Converse

/-!
# T2-A Phase D: AWGN main theorem — `awgn_channel_coding_theorem`

Cover-Thomas Ch.9 (Theorem 9.1.1 + 9.1.2) AWGN noisy channel coding theorem の
統合 publish。Achievability + Converse + closed-form capacity の sandwich を
1 つの signature に集約。

撤退ライン F-4 hypothesis pass-through 1 本 (2026-05-27 F-1/F-3 peer
migration 後、2026-06-12 dead `h_mi_bridge` cleanup 後):
* `h_meas : IsAwgnChannelMeasurable N` — F-4: kernel measurability の外出し

F-2 (MI closed-form bridge) は genuine closure 済 (`awgn-mi-bridge-plan`
closed)。本 achievability chain が取っていた `h_mi_bridge` hypothesis は body
未参照の dead hyp だったため、2026-06-12 cleanup で signature から除去
(achievability の結論は `awgn_achievability` から得られ MI bridge に依存しない)。

F-1 / F-3 は `IsAwgnTypicalityHypothesis` / `IsAwgnConverseHypothesis` predicate
削除に伴い signature から除去。F-1 (achievability) は `awgn_achievability` の
`sorry + @residual(plan:awgn-achievability-typicality-plan)` として独立 publish。
F-3 (converse) は `awgn_converse` body を `awgn_converse_F3_discharged` への
1 行 `exact` wrapper として discharge 済 (2026-05-27 `awgn-main-converse-wiring`
mini-plan)。converse 経路の 3 Mathlib 壁 (mi-bridge / multivariate-mi /
continuous-mi-chain-rule) はすべて false-wall overturn で genuine closure し、
`awgn_converse` は **完全 transitively sorryAx-free**
(`#print axioms InformationTheory.Shannon.AWGN.awgn_converse` で再確認可能)。

それぞれの discharge plan:
* F-4 → `awgn-kernel-measurability-plan.md`
* F-1 (achievability) → `awgn-achievability-typicality-plan.md`
* F-2 (converse 壁) → closed (`awgn-mi-bridge-plan`)
* F-3 (converse) → closed (3 壁すべて genuine、`awgn-converse-aux-plan`)

判断ログ #2 (3 ファイル分離戦略) より、主定理 wrapper は AWGN.lean 末尾ではなく
本 file (`AWGNMain.lean`) に置く: AWGNAchievability + AWGNConverse を import
する必要があり、AWGN.lean に置くと循環依存になるため。判断ログ #2 (再判断) で
記録予定。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Main theorem — `awgn_channel_coding_theorem` -/

/-- **AWGN channel coding theorem (Cover-Thomas 9.1.1 + 9.1.2)**.

For the additive white Gaussian noise channel `Y = X + Z`, `Z ∼ 𝒩(0, N)`, with
output power constraint `E[X²] ≤ P`:

* (Achievability) For any rate `R < C = (1/2) log(1+P/N)` and target ε > 0,
  there exists `N₀` such that for every `n ≥ N₀`, there is an `AwgnCode`
  with `M ≥ ⌈exp(nR)⌉` messages and per-message error probability < ε.

This is the **achievability half** statement, with converse available
separately via `awgn_converse` (now wired to `awgn_converse_F3_discharged`,
2026-05-27 `awgn-main-converse-wiring` mini-plan). The remaining 撤退ライン
hypothesis (`h_meas`) exposes the F-4 撤退ライン structure;
F-1 / F-3 are no longer signaled by predicate hyps (2026-05-27 F-1/F-3
peer migration removed `IsAwgnTypicalityHypothesis` /
`IsAwgnConverseHypothesis`). The F-2 `h_mi_bridge` hypothesis was a dead
pass-through (never used in the body) and was removed in the 2026-06-12 cleanup
(F-2 itself is genuinely closed via `awgn-mi-bridge-plan`).

撤退ライン discharge plans:
* F-4 (`h_meas`) → `awgn-kernel-measurability-plan.md`
* F-1 (achievability body) → `awgn-achievability-typicality-plan.md`
  (`awgn_achievability` body は `sorry` + `@residual(plan:...)`)
* F-2 → genuine closure 済 (`awgn-mi-bridge-plan` closed)。dead だった
  `h_mi_bridge` hyp は 2026-06-12 cleanup で本 chain の signature から除去。
* F-3 (converse body) → `awgn-converse-aux-plan.md` (`awgn_converse` body は
  `awgn_converse_F3_discharged` 経由で discharge 済。converse の 3 Mathlib 壁
  すべて genuine closure 済のため `awgn_converse` は transitively sorryAx-free —
  `awgn-main-converse-wiring` mini-plan で完了)

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgn_channel_coding_theorem
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε :=
  awgn_achievability P hP N hN h_meas hR_pos hR_lt_C hε

/-! ## Closed-form capacity corollary -/

/-- **AWGN capacity closed form** (Cover-Thomas 9.1, restated as a public corollary).

`awgnCapacity P N h_meas = (1/2) log(1 + P/N)`.

The four hypotheses (`h_bridge_gauss`, `h_bdd`, `h_max_ent`) are the F-2 撤退
ライン pass-throughs (Gaussian-input closed form + bounded-above of MI image +
max-entropy upper bound). See `AWGN.awgnCapacity_eq` for the underlying sandwich.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N h_meas)).toReal) ''
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N h_meas = (1/2) * Real.log (1 + P / (N : ℝ)) :=
  awgnCapacity_eq P hP N hN h_meas h_bridge_gauss h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
