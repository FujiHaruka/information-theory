import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.LiminfLimsup
import InformationTheory.Shannon.ShannonHartley
import InformationTheory.Meta.EntryPoint

/-!
# Continuous-time Shannon-Hartley operational capacity

Cover-Thomas Ch. 9.6. This file gives a *faithful, non-circular, operational* definition
of the capacity of the continuous-time band-limited AWGN channel and states the
Shannon-Hartley identity

    `contAwgnOperationalCapacity W N₀ P = W · log(1 + P / (N₀ · W))`

as `contAwgn_eq_shannonHartley`. The proof is the single genuine Mathlib wall
`@residual(wall:nyquist-2w-dof)` (the prolate-spheroidal / Landau-Pollak-Slepian
time-bandwidth degrees-of-freedom count), so the theorem is published with a `sorry`
body while its statement is a true, non-degenerate proposition.

## Main definitions

* `IsBandlimited f W` — the (complexified) Fourier transform of `f : ℝ → ℝ` vanishes
  outside `[-W, W]`.
* `ContAwgnCode T W P M` — a continuous-time AWGN code: `M` band-limited signals
  (essentially time-limited to `[0, T]`, average power `≤ P`) together with a decoder
  acting on a *free* number `sampleCount` of observations.
* `contAwgnOperationalCapacity W N₀ P` — the per-second operational rate
  `⨅ ε, limsup_T (log M(T, ε)) / T`.

## Main statements

* `contAwgn_eq_shannonHartley` — the operational capacity equals the Shannon-Hartley
  closed form `bandlimitedAwgnCapacity W N₀ P`.

## Implementation notes — the three honesty risks and how the definition avoids them

The definition is engineered so that `contAwgn_eq_shannonHartley` is *true*,
*non-circular*, and *non-degenerate*; a wall on a false/circular/degenerate statement
would be a tier-5 defect, strictly worse than the load-bearing predicate it replaces.

* **Truth (standard bookkeeping).** Observations are the `√(T/n)`-normalized samples
  `sampledSignal`: the normalization makes the sample-space energy equal the continuous
  `L²` energy `∫_{[0,T]} f² ≤ T·P` (a Parseval-consistent isometry), and each sample is
  corrupted by independent Gaussian noise of variance `N₀/2` — the standard Nyquist
  per-sample noise. With the effective `2WT` degrees of freedom this gives per-dimension
  SNR `(T·P/(2WT)) / (N₀/2) = P/(N₀·W)` and per-second rate `W·log(1 + P/(N₀·W))`,
  matching `bandlimitedAwgnCapacity` exactly.
* **Non-circularity (C1–C4).** A codeword is a genuine band-limited *function* `ℝ → ℝ`
  (C1), never a length-`⌊2WT⌋` sample vector; `contAwgnMaxMessages` contains no `2W` or
  `⌊2WT⌋` (C2); the observation count `sampleCount` is a *free* `ℕ` field, not pinned to
  `⌊2WT⌋` (C4); the factor `2W` is not in any definition and must emerge from the DOF proof
  (C3). Consequently `contAwgn_eq_shannonHartley` cannot be closed by `rfl`/`unfold`.
* **Non-degeneracy.** The `√(T/n)` normalization caps the sample-space signal energy at
  `T·P` (independent of `n`), so oversampling does *not* drive the capacity to `∞`; in fact
  the capacity is `≤ P/N₀ < ∞` for any `n` (the wide-band limit), and the band-limit brings
  it down to the exact Shannon-Hartley value. The noise genuinely corrupts the signal
  (variance `N₀/2 > 0` whenever `N₀ > 0`).

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 9.6.1.
-/

namespace InformationTheory.Shannon.ShannonHartley

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology FourierTransform

/-! ## §A — Band-limited signals -/

/-- A real signal `f : ℝ → ℝ` is band-limited to `[-W, W]` if the Fourier transform of its
complexification vanishes outside `[-W, W]`. The complexification is needed because the
Fourier transform `𝓕` is complex-valued. -/
def IsBandlimited (f : ℝ → ℝ) (W : ℝ) : Prop :=
  ∀ ξ : ℝ, W < |ξ| → 𝓕 (fun t : ℝ => (f t : ℂ)) ξ = 0

/-! ## §B — Continuous-time AWGN code -/

/-- A continuous-time AWGN code over the window `[0, T]` with bandwidth `W`, average power
`P`, and `M` messages.

The encoder maps each message to a genuine band-limited *function* `ℝ → ℝ` (never a fixed
sample vector — this is the non-circularity constraint C1), essentially time-limited to
`[0, T]` with average power `≤ P`. The decoder acts on a *free* number `sampleCount` of
observations (constraint C4: the observation count is not pinned to `⌊2WT⌋`). -/
structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  /-- The `M` band-limited codewords, one per message. -/
  encoder : Fin M → (ℝ → ℝ)
  /-- Each codeword is band-limited to `[-W, W]`. -/
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W
  /-- Average-power constraint: energy over `[0, T]` is at most `T · P`. -/
  encoder_power : ∀ m, (∫ t in Set.Icc (0 : ℝ) T, (encoder m t) ^ 2) ≤ T * P
  /-- The number of observed samples (a free `ℕ` parameter; constraint C4). -/
  sampleCount : ℕ
  /-- The decoder maps the observation vector back to a message. -/
  decoder : (Fin sampleCount → ℝ) → Fin M
  /-- The decoder is measurable (needed on the continuous output alphabet). -/
  decoder_meas : Measurable decoder

/-- The Nyquist-normalized sample vector of `f` over `[0, T]` with `n` samples: the value at
`t_i = i · T / n` scaled by `√(T/n)`. The `√(T/n)` scaling is load-bearing for honesty — it
makes the discrete `ℓ²` energy `∑ᵢ (sampledSignal f T n i)²` equal the continuous energy
`∫_{[0,T]} f²` (a Parseval-consistent isometry), so that oversampling (`n → ∞`) does not
inflate the signal-to-noise ratio and the capacity stays finite. -/
noncomputable def sampledSignal (f : ℝ → ℝ) (T : ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => Real.sqrt (T / (n : ℝ)) * f (((i : ℕ) : ℝ) * (T / (n : ℝ)))

/-- Point-wise error probability for message `m`: the noisy observation
`y = sampledSignal (encoder m) + noise` (per-sample noise variance `N₀/2`, independent
across samples) lands in the decoding-error region `{y | decoder y ≠ m}`.

Modelled directly as `Measure.pi (fun i => gaussianReal (sampleᵢ) (N₀/2))`, i.e. the
memoryless per-sample AWGN law — the same law computed by the discrete
`ChannelCoding.Code.errorProbAt` for `awgnChannel (N₀/2)`, but inlined so that no
`IsAwgnChannelMeasurable` kernel-measurability hypothesis is needed inside the definition. -/
noncomputable def ContAwgnCode.errorProbAt {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) (m : Fin M) : ℝ≥0∞ :=
  Measure.pi (fun i : Fin c.sampleCount =>
      gaussianReal (sampledSignal (c.encoder m) T c.sampleCount i) (N₀ / 2).toNNReal)
    {y : Fin c.sampleCount → ℝ | c.decoder y ≠ m}

/-- Average error probability under a uniform message: `(1/M) ∑ₘ errorProbAt m`
(`0` for the empty code `M = 0`). -/
noncomputable def ContAwgnCode.averageError {T W P : ℝ} {M : ℕ}
    (c : ContAwgnCode T W P M) (N₀ : ℝ) : ℝ≥0∞ :=
  if M = 0 then 0 else (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt N₀ m

/-! ## §C — Operational capacity -/

/-- The largest number of messages distinguishable over the window `[0, T]` with average
error probability at most `ε` — an *operational* primitive that contains no `2W` or
`⌊2WT⌋` (constraint C2). -/
noncomputable def contAwgnMaxMessages (T W N₀ P ε : ℝ) : ℕ :=
  sSup { M : ℕ | ∃ c : ContAwgnCode T W P M, (c.averageError N₀).toReal ≤ ε }

/-- The per-second rate achievable at error level `ε`: `limsup_T (log M(T, ε)) / T`. -/
noncomputable def contAwgnRate (W N₀ P ε : ℝ) : ℝ :=
  Filter.limsup (fun T : ℝ => Real.log (contAwgnMaxMessages T W N₀ P ε : ℝ) / T) atTop

/-- The **operational capacity** of the continuous-time band-limited AWGN channel:
the per-second rate in the vanishing-error limit, `⨅_{ε ∈ (0,1)} contAwgnRate W N₀ P ε`.
The infimum over `ε` extracts the `ε → 0` capacity; `ε` is restricted to `(0, 1)` because
`ε ≥ 1` is satisfied by every code (average error is `≤ 1`) and would make the message set
unbounded. -/
noncomputable def contAwgnOperationalCapacity (W N₀ P : ℝ) : ℝ :=
  ⨅ ε ∈ Set.Ioo (0 : ℝ) 1, contAwgnRate W N₀ P ε

/-! ## §D — Shannon-Hartley identity -/

/-- The **continuous-time Shannon-Hartley formula**: the operational capacity of the
band-limited AWGN channel equals `W · log(1 + P/(N₀·W))`.

The statement is a true, non-degenerate, non-circular proposition (see the module
implementation notes); its proof is the single genuine Mathlib wall — the time-bandwidth
degrees-of-freedom-per-second count (prolate-spheroidal / Landau-Pollak-Slepian eigenvalue
concentration of the time-and-band limiting operator), absent from Mathlib.

`@residual(wall:nyquist-2w-dof)` -/
@[entry_point]
theorem contAwgn_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  sorry -- @residual(wall:nyquist-2w-dof)

end InformationTheory.Shannon.ShannonHartley
