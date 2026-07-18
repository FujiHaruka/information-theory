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

## Main statements

* `twoW_perSample_eq_shannonHartley` — the algebraic `2W`-reduction
  `2W · perSample = W · log(1 + P/(N₀·W))`.

## Implementation notes

This file provides only the closed-form definitions and the algebraic `2W`-reduction. The
*operational* Shannon-Hartley identity — that this closed form is the operational capacity of
the continuous-time band-limited AWGN channel — lives in
`InformationTheory.Shannon.ShannonHartley.Operational` (`contAwgn_eq_shannonHartley`), which
builds an operational capacity `contAwgnOperationalCapacity` on top of these definitions.

That identity is now proved (`sorryAx`-free) in `ConverseFinal`. An earlier
`ContAwgnCode` model under-constrained the code class — its point-sampling observation map was an
isometry only at the Nyquist spacing, i.e. calibrated at exactly the value the identity has to
prove — so it was repaired to discretize the received signal against an orthonormal family
supported in the window (a Karhunen-Loève / matched-filter map). The prolate-spheroidal /
Landau-Pollak-Slepian time-bandwidth degrees-of-freedom-per-second count then closes the converse
via the count domination `bandGramReal_high_count_le`. See `Operational` for the
operational definitions.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1.
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

end InformationTheory.Shannon.ShannonHartley
