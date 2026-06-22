import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InformationTheory.Meta.EntryPoint

/-!
# Bandlimited Channel / Shannon-Hartley formula

Cover-Thomas Ch.9.6. The continuous-time bandlimited AWGN channel with signal
`X(t)` bandlimited to `[-W, W]` Hz and flat noise PSD `N₀ / 2`. Under average
power constraint `E[X(t)²] ≤ P`, the capacity is

    `C = W · log(1 + P / (N₀ · W))`   (nats/second; divide by `log 2` for bits/second).

## Main definitions

* `bandlimitedAwgnCapacity` — `W · log(1 + P/(N₀·W))`.
* `perSampleAwgnCapacity` — Nyquist-reduction per-sample capacity `(1/2) · log(1 + P/(N₀·W))`.
* `IsBandlimitedSamplingHypothesis`, `IsBandlimitedKernel`, `IsTwoWDegreesOfFreedom` —
  open hypothesis predicates for the three Mathlib-wall residuals.

## Main statements

* `shannon_hartley_formula` — `C = W · log(1 + P/(N₀·W))` conditional on the three
  open predicates above.

## Implementation notes

The Nyquist sampling equivalence requires the Whittaker-Shannon sampling
theorem and continuous-time AEP, neither of which is in Mathlib. These are taken as
explicit hypothesis predicates; `shannon_hartley_formula` performs only the residual
algebra `2W · perSample = W · log(1 + P/(N₀·W))`.
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

open scoped Topology

/-! ## §A — Bandlimited capacity definition + closed form. -/

/-- Shannon-Hartley capacity of a bandlimited AWGN channel with bandwidth
`W > 0` (Hz), noise PSD `N₀ > 0` (W/Hz, two-sided convention so the per-Hz
noise power within the band is `N₀`), and average signal power `P ≥ 0`. -/
noncomputable def bandlimitedAwgnCapacity (W N₀ P : ℝ) : ℝ :=
  W * Real.log (1 + P / (N₀ * W))

/-- Per-sample AWGN capacity obtained from the Nyquist-rate reduction.
With one-sided noise PSD `N₀`, per-sample noise variance is `N₀/2` (since the
total in-band noise power `N₀·W` is split across `2W` samples/second), and
per-sample power budget is `P/(2W)`. The per-sample SNR therefore is
`(P/(2W)) / (N₀/2) = P/(N₀·W)`, giving the per-sample capacity
`(1/2) · log(1 + P/(N₀·W))`. -/
noncomputable def perSampleAwgnCapacity (W N₀ P : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + P / (N₀ * W))

/-! ## §B — Bandlimited-channel hypothesis predicates.

The three predicates below are open residuals (Mathlib walls): the first two carry only
positivity, and `IsTwoWDegreesOfFreedom` states the `2W` degrees-of-freedom identity
whose proof requires the Whittaker-Shannon sampling theorem + continuous-time AEP.
They are consumed as explicit hypotheses by `shannon_hartley_formula`. -/

/-- Bandlimited-sampling hypothesis: positivity carrier `0 < W ∧ 0 < N₀ ∧ 0 ≤ P`.

The intended content is the Whittaker-Shannon sampling-equivalence between the
continuous-time bandlimited AWGN channel and a sequence of independent per-sample
AWGN channels at rate `2W`. That equivalence requires Whittaker-Shannon /
Nyquist-Fourier machinery not in Mathlib; this predicate carries only positivity.

`@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` -/
def IsBandlimitedSamplingHypothesis (W N₀ P : ℝ) : Prop :=
  0 < W ∧ 0 < N₀ ∧ 0 ≤ P

/-- Bandlimited-kernel hypothesis: positivity stand-in `0 < W` for continuous-time AWGN noise
kernel measurability.

`@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` -/
def IsBandlimitedKernel (W : ℝ) : Prop := 0 < W

/-- The `2W` degrees-of-freedom per second identity `C = 2W · perSampleAwgnCapacity`.

Requires Whittaker-Shannon sampling theorem + continuous AEP (not in Mathlib);
taken as the caller's hypothesis.

`@audit:retract-candidate(load-bearing-predicate)`
`@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` -/
def IsTwoWDegreesOfFreedom (W N₀ P C : ℝ) : Prop :=
  C = 2 * W * perSampleAwgnCapacity W N₀ P

/-! ## §D — Sampling-rate scale-up: continuous capacity = `2W · per-sample`. -/

/-- The `2W` degrees-of-freedom identity: `2W · perSample = W · log(1 + P/(N₀·W))`, the
Shannon-Hartley formula in closed form (pure algebra after the
`perSampleAwgnCapacity` definition is unfolded). -/
theorem twoW_perSample_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    2 * W * perSampleAwgnCapacity W N₀ P
      = bandlimitedAwgnCapacity W N₀ P := by
  unfold perSampleAwgnCapacity bandlimitedAwgnCapacity
  ring

/-! ## §E — Main theorem: Shannon-Hartley formula (hypothesis pass-through). -/

/-- The Shannon-Hartley formula (Cover-Thomas Theorem 9.6.1):
`C = W · log(1 + P/(N₀·W))` conditional on the three bandlimited-channel hypotheses.

The hypothesis `h_two_w : IsTwoWDegreesOfFreedom W N₀ P C` carries the `2W`
degrees-of-freedom identity `C = 2W · perSampleAwgnCapacity W N₀ P`; this theorem
only performs the residual algebra `2W · perSample = W · log(1 + P/(N₀·W))`.
Closing the `2W` degrees-of-freedom identity requires the Whittaker-Shannon
sampling theorem + continuous AEP (not in Mathlib).

`@audit:retract-candidate(load-bearing-predicate)`
`@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)`
`@residual(plan:whittaker-shannon-partial-moonshot-plan)`
-/
@[entry_point]
theorem shannon_hartley_formula
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (C : ℝ)
    (h_sampling : IsBandlimitedSamplingHypothesis W N₀ P)
    (h_kernel : IsBandlimitedKernel W)
    (h_two_w : IsTwoWDegreesOfFreedom W N₀ P C) :
    C = bandlimitedAwgnCapacity W N₀ P := by
  -- `h_two_w` is the OPEN operational identity `C = 2W · perSample`
  -- (taken as hypothesis; its discharge needs Nyquist-Fourier machinery).
  unfold IsTwoWDegreesOfFreedom at h_two_w
  rw [h_two_w]
  -- Residual algebra: `2W · perSample = W · log(1 + P/(N₀·W))`.
  exact twoW_perSample_eq_shannonHartley W N₀ P hW hN₀ hP

end InformationTheory.Shannon.ShannonHartley
