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

The Whittaker-Shannon sampling theorem itself is now PROVED sorryAx-free (Fourier-series
route) in `InformationTheory.Shannon.WhittakerShannon`
(`whittaker_shannon_hasSum` / `whittaker_shannon_bandlimited`), so it is no longer a Mathlib
wall. The residual carried by `IsTwoWDegreesOfFreedom` is a *single* genuine wall: the
time-bandwidth **degrees-of-freedom-per-second** count — a signal band-limited to `[-W, W]`
and essentially time-limited to `[0, T]` carries `≈ 2WT` degrees of freedom (the
prolate-spheroidal / Landau-Pollak-Slepian eigenvalue concentration of the time-and-band
limiting operator). Mathlib does not have this (`@residual(wall:nyquist-2w-dof)`; loogle
`Found 0` on `prolate` / `Bandlimited` / `Slepian` / `whiteNoise`, 2026-07-14). Everything
*around* the count is in-project definable and is NOT a wall: the noise measure (a band-limited
projection of white noise is a finite-variance Gaussian process whose Nyquist samples are iid
Gaussian, via `IsGaussianProcess` or an iid-sample reconstruction pushforward), continuous-time
AEP, and the per-sample operational coding theorem (already owned: `awgn_achievability` /
`awgn_converse`). The sampling theorem does not close the operational identity because
`whittaker_shannon_bandlimited` is a bijection on the *whole* real line (two-sided infinite
samples ↔ band-limited L² signal), whereas operational capacity is a *per-second rate*
`limsup (log M(T)) / T` over a time window `T` — a whole-line bijection supplies no
time-window dimension count. The identity is taken as an explicit hypothesis predicate;
`shannon_hartley_formula` performs only the residual algebra
`2W · perSample = W · log(1 + P/(N₀·W))`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006. Theorem 9.6.1.
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

The three predicates below are open residuals: the first two carry only
positivity, and `IsTwoWDegreesOfFreedom` states the `2W` degrees-of-freedom identity.
The Whittaker-Shannon sampling theorem underlying that identity is now PROVED sorryAx-free
in `InformationTheory.Shannon.WhittakerShannon`, so the only remaining gap is the
time-bandwidth **degrees-of-freedom-per-second** count (prolate-spheroidal /
Landau-Pollak-Slepian eigenvalue concentration, absent from Mathlib —
`@residual(wall:nyquist-2w-dof)`). The surrounding operational ingredients (band-limited
white-noise measure, continuous-time AEP, per-sample coding theorem) are all in-project
definable and are not the wall. They are consumed as explicit
hypotheses by `shannon_hartley_formula`. -/

/-- Bandlimited-sampling hypothesis: positivity carrier `0 < W ∧ 0 < N₀ ∧ 0 ≤ P`.

The intended content is the Whittaker-Shannon sampling-equivalence between the
continuous-time bandlimited AWGN channel and a sequence of independent per-sample
AWGN channels at rate `2W`. The Whittaker-Shannon sampling theorem underlying that
equivalence is now PROVED sorryAx-free (`whittaker_shannon_hasSum` /
`whittaker_shannon_bandlimited`), so there is no residual Mathlib gap here; this
predicate carries only positivity, and the remaining operational gap — shared with the
other two predicates — is the single time-bandwidth degrees-of-freedom-per-second wall
(`@residual(wall:nyquist-2w-dof)`), not the sampling theorem. -/
def IsBandlimitedSamplingHypothesis (W N₀ P : ℝ) : Prop :=
  0 < W ∧ 0 < N₀ ∧ 0 ≤ P

/-- Bandlimited-kernel hypothesis: positivity stand-in `0 < W` for continuous-time AWGN noise
kernel measurability. -/
def IsBandlimitedKernel (W : ℝ) : Prop := 0 < W

/-- The `2W` degrees-of-freedom per second identity `C = 2W · perSampleAwgnCapacity`.

The Whittaker-Shannon sampling theorem underlying the `2W`-DOF count is now PROVED sorryAx-free
(`InformationTheory.Shannon.WhittakerShannon.whittaker_shannon_hasSum` /
`whittaker_shannon_bandlimited`), so the residual here is a *single* genuine wall: the
time-bandwidth **degrees-of-freedom-per-second** count itself — a signal band-limited to
`[-W, W]` and essentially time-limited to `[0, T]` carries `≈ 2WT` degrees of freedom
(prolate-spheroidal / Landau-Pollak-Slepian eigenvalue concentration), which Mathlib does not
have. The surrounding operational data (band-limited white-noise measure = iid Gaussian Nyquist
samples, continuous-time AEP, per-sample coding theorem `awgn_achievability` / `awgn_converse`)
are all in-project definable, so the wall is *only* the per-second DOF count. Caveat for a
future non-circular restructure: the continuous-time code must not be defined by restricting to
a length-`⌊2WT⌋` sample vector — that embeds the Landau-Pollak-Slepian converse DOF bound into
the definition (circular); the factor `2W` has to emerge from the DOF proof. Taken as the
caller's hypothesis.

`@audit:retract-candidate(load-bearing-predicate)` -/
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

/-- The **Shannon-Hartley formula**:
`C = W · log(1 + P/(N₀·W))` conditional on the three bandlimited-channel hypotheses.

The hypothesis `h_two_w : IsTwoWDegreesOfFreedom W N₀ P C` carries the `2W`
degrees-of-freedom identity `C = 2W · perSampleAwgnCapacity W N₀ P`; this theorem
only performs the residual algebra `2W · perSample = W · log(1 + P/(N₀·W))`.
The Whittaker-Shannon sampling theorem underlying the `2W`-DOF count is now PROVED sorryAx-free
(`InformationTheory.Shannon.WhittakerShannon.whittaker_shannon_hasSum` /
`whittaker_shannon_bandlimited`); the only remaining gap in closing the identity is the
time-bandwidth **degrees-of-freedom-per-second** count (prolate-spheroidal /
Landau-Pollak-Slepian eigenvalue concentration, absent from Mathlib). The sampling theorem does
not close it because `whittaker_shannon_bandlimited` is a whole-real-line bijection, whereas
operational capacity is a per-second rate `limsup (log M(T)) / T`; the noise measure,
continuous-time AEP, and per-sample coding theorem around it are all in-project definable.

`@audit:retract-candidate(load-bearing-predicate)`
`@residual(wall:nyquist-2w-dof)`
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
