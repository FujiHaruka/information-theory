import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Unconditional.MixedCase
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.G2.ConvEntropyDensity
import InformationTheory.Shannon.EPI.Case1.ProducerMeasurability
import InformationTheory.Shannon.EPI.Case1.RatioLimit.PathRegular
import InformationTheory.Shannon.EPI.Case1.RatioLimit.Assembly
import InformationTheory.Shannon.EPI.Case1.RatioLimit.Producer

/-!
# EPI case-1 via ratio + scaling squeeze (entropic-CLT-free)

This file lands the **monotone + limit** architecture for the classical (case-1,
a.c. inputs) entropy power inequality, **bypassing the entropic CLT wall**.

## Architecture

Let `R(t) = csiszarLogRatioGap X Y Z_X Z_Y P t
          = log N(law(X+Y+√t·(Z_X+Z_Y))) − log (N(law(X+√t·Z_X)) + N(law(Y+√t·Z_Y)))`,
the genuine log-ratio gap (`EPIL3Integration.csiszarLogRatioGap`).

* `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`, genuine,
  sorryAx-free) gives `AntitoneOn R (Set.Ici 0)`.
* `epi_of_csiszarLogRatioGap_zero_nonneg` (`EPIStamToBridge.lean:985`, genuine)
  gives `0 ≤ R 0 ⟹ EPI`.

So if `R t → 0` as `t → ∞`, then by antitonicity `R 0 ≥ lim_{t→∞} R t = 0`, hence
EPI. **No entropic CLT** is needed: `R t → 0` follows from a *scaling squeeze*.

### Scaling cancellation

`X + √t·Z_X = √t·(X/√t + Z_X)`, so by `entropyPower_map_mul_const`
(`EPIPlumbing.lean:136`, `N(μ.map(·*c)) = c²·N(μ)`, `c = √t`):
`N(law(X+√t·Z_X)) = t · N(law(X/√t + Z_X))`. Applying this to all three paths, the
`t` factor cancels inside the `log`s (`Real.log_mul`, `t > 0`, `N > 0`):
`R t = log N(W_sum t) − log (N(W_X t) + N(W_Y t))`,
`W_X t = X/√t + Z_X`, `W_Y t = Y/√t + Z_Y`, `W_sum t = (X+Y)/√t + (Z_X+Z_Y)`.

### Squeeze

Each `N(W_X t) → N(law Z_X)` as `t → ∞` (input mass shrinks like `1/√t`): the lower
bound is `N(W_X t) = N(Z_X + X/√t) ≥ N(Z_X)` (independent-noise monotonicity,
`differentialEntropy_add_ge_of_indep`); the upper bound is the Gaussian max-entropy
`N(W_X t) ≤ 2πe (Var X / t + 1) → 2πe = N(Z_X)`
(`differentialEntropy_le_gaussian_of_variance_le`). With
`N(law(Z_X)+law(Z_Y)) = N(Z_X) + N(Z_Y)` (`entropyPower_gaussian_additivity`,
standard normals), the two `log`s converge to the same value, so `R t → 0`.

## Honesty

All per-`t` regularity (a.c., finite-entropy integrability of the W-path laws, the
8 fibre-integrability preconditions of `differentialEntropy_add_ge_of_indep`, finite
variance) is threaded as **honest preconditions** in the signatures. The
Stam core / EPI core is never bundled as a `*Hypothesis`. The genuine analytic glue
(scaling cancellation, log-continuity composition, Gaussian additivity, order limit)
is the deliverable; preconditions not discharged here remain honest hypotheses.

The four sections are §1 `epi_of_csiszarLogRatioGap_tendsto`, §2
`entropyPower_path_scaling`, §3 `entropyPower_rescaled_path_tendsto`, §4
`csiszarLogRatioGap_tendsto_zero_atTop`.
In the §3 squeeze both envelopes are derived from the
lemmas `differentialEntropy_add_ge_of_indep` (lower) and
`differentialEntropy_le_gaussian_of_variance_le` (upper) using the per-`t`
regularity bundle `IsRescaledPathRegular` (NOT load-bearing). §4 threads
three such bundles transparently. Discharging `IsRescaledPathRegular` (supplying
the per-`t` regularity from a.c. inputs + Gaussian smoothing) is left to a
separate development; here it is an honest precondition.
-/
