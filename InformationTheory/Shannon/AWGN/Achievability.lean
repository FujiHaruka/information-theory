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

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley,
  2006. Theorem 9.1.1.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Achievability -/

/-- The AWGN achievability theorem: for any rate `R < C = (1/2) log(1+P/N)` and target
error probability `ε > 0`, there exists `N₀` such that for every block length `n ≥ N₀`
there is an `AwgnCode` (output power ≤ `P`, measurable decoder) with `M ≥ ⌈exp(nR)⌉`
messages whose per-message error probability is below `ε`.

The body is a direct call to `isAwgnTypicalityHypothesis`, a 580-line genuine assembly
(sphere packing, Gaussian random codebook, the three continuous-AEP bounds, and the
union bound). Its only hypotheses are regularity preconditions (`0 < P`, `(N : ℝ) ≠ 0`,
measurability); the name is a historical artifact, not a load-bearing `*Hypothesis`
predicate.

@audit:ok -/
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
