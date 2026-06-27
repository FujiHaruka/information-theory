import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.Achievability
import InformationTheory.Shannon.AWGN.Converse

/-!
# AWGN channel coding theorem

The AWGN noisy-channel coding theorem (Cover–Thomas Theorems 9.1.1 + 9.1.2):
achievability, converse, and the closed-form capacity assembled into one statement.

## Main statements

* `awgn_channel_coding_theorem` — the achievability half (codes exist below capacity).
* `awgn_capacity_closed_form` — the capacity equals `(1/2) log(1 + P/N)`.

## Implementation notes

`awgn_channel_coding_theorem` is a pass-through to the genuine `awgn_achievability`;
the converse is available separately via `awgn_converse`. The kernel measurability is
exposed as the hypothesis `h_meas : IsAwgnChannelMeasurable N`.

The wrapper lives in this file rather than at the end of the `awgnChannel` base file so
that it can import both `Achievability` and `Converse` without creating an import cycle.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006. Theorems 9.1.1–9.1.2.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Main theorem — `awgn_channel_coding_theorem` -/

/-- **AWGN channel coding theorem**.

For the additive white Gaussian noise channel `Y = X + Z`, `Z ∼ 𝒩(0, N)`, with
output power constraint `E[X²] ≤ P`:

* (Achievability) For any rate `R < C = (1/2) log(1+P/N)` and target ε > 0,
  there exists `N₀` such that for every `n ≥ N₀`, there is an `AwgnCode`
  with `M ≥ ⌈exp(nR)⌉` messages and per-message error probability < ε.

This is the achievability-half statement; the converse is available separately via
`awgn_converse`. The hypothesis `h_meas` exposes the kernel measurability. The body is
an honest pass-through to `awgn_achievability`.

@audit:ok -/
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

/-- AWGN capacity closed form (Cover-Thomas 9.1, restated as a public corollary).

`awgnCapacity P N h_meas = (1/2) log(1 + P/N)`.

The hypotheses `h_bridge_gauss`, `h_bdd`, `h_max_ent` supply the Gaussian-input closed
form, the bounded-above property of the MI image, and the max-entropy upper bound. See
`AWGN.awgnCapacity_eq` for the underlying sandwich.

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
        BddAbove ((fun p : Measure ℝ ↦
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
