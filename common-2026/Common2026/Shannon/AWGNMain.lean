import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNAchievability
import Common2026.Shannon.AWGNConverse

/-!
# T2-A Phase D: AWGN main theorem — `awgn_channel_coding_theorem`

Cover-Thomas Ch.9 (Theorem 9.1.1 + 9.1.2) AWGN noisy channel coding theorem の
統合 publish。Achievability + Converse + closed-form capacity の sandwich を
1 つの signature に集約。

撤退ライン F-1 + F-2 + F-3 + F-4 を全て採用した形 (hypothesis pass-through 4 本):
* `h_meas : IsAwgnChannelMeasurable N` — F-4: kernel measurability の外出し
* `h_typicality : IsAwgnTypicalityHypothesis P N h_meas` — F-1: 連続版 typicality
* `h_mi_bridge` — F-2: MI closed-form bridge
* `h_converse : IsAwgnConverseHypothesis P N h_meas` — F-3: converse + 可積分

それぞれの discharge は別 plan に defer:
* F-4 → `awgn-kernel-measurability-plan.md`
* F-1 → `awgn-achievability-typicality-plan.md`
* F-2 → `awgn-mi-bridge-plan.md`
* F-3 → `awgn-converse-aux-plan.md`

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

This is the **achievability half** statement, with converse hypothesis available
separately via `awgn_converse`. The four撤退ライン hypotheses (`h_meas`,
`h_typicality`, `h_mi_bridge`, `h_converse`) are kept in the signature to
expose the F-1 / F-2 / F-3 / F-4 撤退ライン structure.

撤退ライン discharge plans:
* F-4 (`h_meas`) → `awgn-kernel-measurability-plan.md`
* F-1 (`h_typicality`) → `awgn-achievability-typicality-plan.md`
* F-2 (`h_mi_bridge`) → `awgn-mi-bridge-plan.md`
* F-3 (`h_converse`) → `awgn-converse-aux-plan.md`

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
theorem awgn_channel_coding_theorem
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_typicality : IsAwgnTypicalityHypothesis P N h_meas)
    (h_mi_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
          = Common2026.Shannon.differentialEntropy
              (gaussianReal 0 (P.toNNReal + N))
            - Common2026.Shannon.differentialEntropy (gaussianReal 0 N))
    (h_converse : IsAwgnConverseHypothesis P N h_meas)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε :=
  awgn_achievability P hP N hN h_meas h_typicality hR_pos hR_lt_C hε

/-! ## Closed-form capacity corollary -/

/-- **AWGN capacity closed form** (Cover-Thomas 9.1, restated as a public corollary).

`awgnCapacity P N h_meas = (1/2) log(1 + P/N)`.

The four hypotheses (`h_bridge_gauss`, `h_bdd`, `h_max_ent`) are the F-2 撤退
ライン pass-throughs (Gaussian-input closed form + bounded-above of MI image +
max-entropy upper bound). See `AWGN.awgnCapacity_eq` for the underlying sandwich.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
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
          { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P }))
    (h_max_ent :
        ∀ p ∈ { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P },
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N h_meas = (1/2) * Real.log (1 + P / (N : ℝ)) :=
  awgnCapacity_eq P hP N hN h_meas h_bridge_gauss h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
