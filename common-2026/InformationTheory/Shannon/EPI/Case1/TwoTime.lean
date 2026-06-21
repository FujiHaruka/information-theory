import InformationTheory.Shannon.EPI.Case1.TwoTime.Core
import InformationTheory.Shannon.EPI.Case1.TwoTime.Paths
import InformationTheory.Shannon.EPI.Case1.TwoTime.GapDerivative
import InformationTheory.Shannon.EPI.Case1.TwoTime.MonotonicityAndSaturation
import InformationTheory.Shannon.EPI.Case1.TwoTime.EntropyPowerInequality

/-!
# EPI case-1 sum frontier — two-time object skeleton

The single-time log-ratio object `csiszarLogRatioGap` (`EPIL3Integration.lean`)
perturbs `X` and `Y` at the **same** time `t`, forcing `s = r = t`. Its sum
derivative is the variance-2 quantity `2·J_sum`, which does **not** close from
the harmonic Stam inequality.

The **two-time object** perturbs `X` at time `s` and `Y` at time `r`
**independently**, and follows the FII-matched path `s'(t) = 1/J_X(s)`,
`r'(t) = 1/J_Y(r)`. Along this path the matched-time characterization gives
`N_X(s(t)) = N_X(0)·eᵗ`, `N_Y(r(t)) = N_Y(0)·eᵗ`, so the gap (formulation (b),
entropy-power reparametrization) is

  `R(t) = log N(s(t),r(t)) − log(N_X(0) + N_Y(0)) − t`,

with derivative `R'(t) = J_S·(1/J_X + 1/J_Y) − 1 ≤ 0` from the **existing**
harmonic Stam producer (no new Mathlib wall). The arithmetic core
(`twotime_full`) and the formulation (`e^t` characterization +
inverse-function chain rule) both go through.

This file implements the two-time object. It is
**proof-done** (0 `sorry`, 0 `@residual`): the derivative core
(`twoTimeLogRatioGap_hasDerivAt`), the endpoints, and the Gaussian-saturation
limit (`twoTimeLogRatioGap_tendsto_zero_atTop`) are all genuinely closed.

## Honesty notes

* `twoTimeLogRatioGap` is a plain `def` parametrized by the matched paths
  `s r : ℝ → ℝ` (formulation (b) `e^t` closed form). The paths are **not**
  load-bearing hypotheses: they are constructed (existence delivered by
  `matchedTimePath_exists`, a genuine (sorry-free, `@audit:ok`) lemma whose
  hypotheses are only the regularity preconditions `J_X > 0`, measurability,
  independence).
* The `IsMatchedTimePath` predicate below records the **output** of the path
  construction (matched `e^t` property + `HasDerivAt`). It is genuinely
  produced by `matchedTimePath_exists`; consumers receive it as a *constructed*
  object, not as a bundled core of the EPI conclusion. The EPI inequality
  itself is never encoded in any hypothesis.
-/
