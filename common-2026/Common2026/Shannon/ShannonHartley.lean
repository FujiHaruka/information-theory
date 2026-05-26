import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# T2-C: Bandlimited Channel / Shannon-Hartley formula

Cover-Thomas Ch.9.6. The continuous-time bandlimited additive white Gaussian
noise (AWGN) channel: signal `X(t)` is bandlimited to `[-W, W]` Hz, noise
`N(t)` has flat power-spectral density `N₀ / 2` over the band, and the
receiver observes `Y(t) = X(t) + N(t)`. Under an average power constraint
`E[X(t)²] ≤ P`, the Shannon-Hartley capacity is

    `C = W · log(1 + P / (N₀ · W))`   (bits/second when `log = log₂`).

We work with the natural-log form (nats/sec); the bit/sec form follows by
dividing by `log 2`.

## Approach

The bandlimited channel is reduced to T2-A (discrete-time AWGN) via Nyquist
sampling at rate `2W` samples/second. Per-sample noise variance is
`N₀ · W` and per-sample power budget is `P / (2W)`. T2-A's
`awgn_capacity_closed_form` then yields per-sample capacity
`(1/2) · log(1 + (P/(2W)) / (N₀·W))` nats/sample; multiplied by the sample
rate `2W` this is `W · log(1 + P/(N₀·W))` nats/sec.

The Nyquist sampling / bandlimit / continuous-time channel measurability
side is **deferred** to retreat lines L-SH1 / L-SH2 / L-SH3 as hypothesis
pass-through predicates; the per-sample reduction itself is delegated to
T2-A's `awgn_capacity_closed_form`.

## 撤退ライン

* **L-SH1** (`IsBandlimitedSamplingHypothesis`): the Whittaker-Shannon
  sampling-equivalence between the continuous-time bandlimited channel and
  the discrete-time AWGN channel at rate `2W` is taken as hypothesis.
* **L-SH2** (`IsBandlimitedKernel`): continuous-time bandlimited noise
  kernel measurability is taken as hypothesis.
* **L-SH3** (`IsTwoWDegreesOfFreedom`): the `2W` degrees-of-freedom-per-second
  identity is taken as hypothesis.

Discharging these requires Whittaker-Shannon sampling theorem in Mathlib,
which is not currently available; follow-up plan
`shannon-hartley-sampling-discharge-plan.md` will treat it.

## Statement form

The main theorem `shannon_hartley_formula` consumes the three hypothesis
predicates plus a `per_sample_reduction` hypothesis (which bridges the
continuous-time capacity to the per-sample T2-A AWGN capacity) and yields
the closed form `W · log(1 + P/(N₀·W))`.
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

/-- Per-sample T2-A AWGN capacity obtained from the Nyquist-rate reduction.
With one-sided noise PSD `N₀`, per-sample noise variance is `N₀/2` (since the
total in-band noise power `N₀·W` is split across `2W` samples/second), and
per-sample power budget is `P/(2W)`. The per-sample SNR therefore is
`(P/(2W)) / (N₀/2) = P/(N₀·W)`, giving the per-sample capacity
`(1/2) · log(1 + P/(N₀·W))`. -/
noncomputable def perSampleAwgnCapacity (W N₀ P : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + P / (N₀ * W))

/-! ## §B — L-SH retreat hypothesis predicates.

⚠️ **UNDISCHARGED PLACEHOLDERS.** The three predicates below are *open*
retreat lines, **not** proven facts. `IsBandlimitedSamplingHypothesis` and
`IsBandlimitedKernel` are deliberately weak (`∃ _h, True` / `0 < W`): they
carry only positivity and assert nothing about the actual Whittaker-Shannon
sampling equivalence or noise-kernel measurability. `IsTwoWDegreesOfFreedom`
is the genuine `2W` degrees-of-freedom *identity*, but discharging it (i.e.
proving the continuous-time operational channel capacity really equals
`2W · perSample`) needs the Whittaker-Shannon / Nyquist sampling theorem and
continuous-time AEP, **neither shipped by Mathlib**. They are consumed as
explicit hypotheses by `shannon_hartley_formula`; supplying them via the
positivity-only builders (`mk_*`) does **not** discharge their mathematical
content — it only re-asserts the still-open identity that the caller hands in. -/

/-- L-SH1 (Mathlib-wall residual, weak positivity carrier): the intended
content is the Whittaker-Shannon sampling-equivalence between the
continuous-time bandlimited AWGN channel at bandwidth `W` and a sequence of
independent per-sample T2-A AWGN channels at rate `2W`. The genuine sampling
equivalence needs the Whittaker-Shannon / Nyquist-Fourier machinery, which
is **not in Mathlib**.

**load-bearing hypothesis — NOT a discharge.** The previous body was
`∃ _h : 0 < W ∧ 0 < N₀ ∧ 0 ≤ P, True` (`True`-slot placeholder = degenerate
def). Replaced with the **honest positivity carrier** `0 < W ∧ 0 < N₀ ∧ 0 ≤ P`:
no `True` slot, the predicate is just a positivity bundle, and the docstring
states explicitly that it does NOT establish the sampling equivalence. The
genuine sampling identity is carried separately by `IsTwoWDegreesOfFreedom`
(`C = 2W · perSampleAwgnCapacity W N₀ P`), which is the actual load-bearing
hypothesis consumed by `shannon_hartley_formula`.

`@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` -/
def IsBandlimitedSamplingHypothesis (W N₀ P : ℝ) : Prop :=
  0 < W ∧ 0 < N₀ ∧ 0 ≤ P

/-- L-SH2 (⚠️ undischarged placeholder): continuous-time bandlimited AWGN
noise kernel measurability. This `def` is `0 < W` — a positivity stand-in,
not the genuine measurability statement.

`@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` -/
def IsBandlimitedKernel (W : ℝ) : Prop := 0 < W

/-- L-SH3 (⚠️ open operational identity): the `2W` degrees-of-freedom per
second identity, i.e. the continuous-time operational capacity `C` equals
`2W` times the per-sample T2-A capacity. This is the genuine bridge whose
proof needs the Whittaker-Shannon sampling theorem + continuous AEP (not in
Mathlib); here it is taken as the caller's hypothesis, never discharged.

`@audit:retract-candidate(load-bearing-predicate) @audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` -/
def IsTwoWDegreesOfFreedom (W N₀ P C : ℝ) : Prop :=
  C = 2 * W * perSampleAwgnCapacity W N₀ P

/-! ## §D — Sampling-rate scale-up: continuous capacity = `2W · per-sample`. -/

/-- L-SH3 identity: `2W · perSample = W · log(1 + P/(N₀·W))`, the
Shannon-Hartley formula in closed form (pure algebra after the
`perSampleAwgnCapacity` definition is unfolded). -/
theorem twoW_perSample_eq_shannonHartley
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    2 * W * perSampleAwgnCapacity W N₀ P
      = bandlimitedAwgnCapacity W N₀ P := by
  unfold perSampleAwgnCapacity bandlimitedAwgnCapacity
  ring

/-! ## §E — Main theorem: Shannon-Hartley formula (L-SH1/2/3 pass-through). -/

/-- **Shannon-Hartley formula** (Cover-Thomas Theorem 9.6.1) —
**conditional / hypothesis pass-through, NOT a self-contained proof.**

The intended operational statement is: the capacity of a continuous-time
bandlimited AWGN channel with bandwidth `W > 0`, noise PSD `N₀ > 0`, and
average signal power `P ≥ 0` is

    `C = W · log(1 + P/(N₀·W))`.

⚠️ **The operational content is taken as the explicit hypothesis `h_two_w`,
not proven.** `h_two_w : IsTwoWDegreesOfFreedom W N₀ P C` *is* the open `2W`
degrees-of-freedom identity `C = 2W · perSampleAwgnCapacity W N₀ P` — the
bridge that genuinely requires the Whittaker-Shannon / Nyquist sampling
theorem and continuous-time AEP, **machinery not yet in Mathlib**. Given that
identity, this theorem only performs the residual *algebra*
`2W · perSample = W · log(1 + P/(N₀·W))` (`twoW_perSample_eq_shannonHartley`).

The companion hypotheses `h_sampling` (L-SH1) and `h_kernel` (L-SH2) are weak
positivity placeholders (see §B) and are **not** load-bearing. This theorem is
therefore honest-but-conditional: it does not establish that the genuine
operational capacity of the channel equals the closed form — it transports the
caller's already-assumed `2W·perSample` identity into the `log` closed form. A
self-contained proof remains open pending continuous AEP / Nyquist-Fourier
support in Mathlib.

`@audit:retract-candidate(load-bearing-predicate) @audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan) @residual(plan:whittaker-shannon-partial-moonshot-plan)`
-/
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
  -- Residual algebra: `2W · perSample = W · log(1 + P/(N₀·W))` (genuine).
  exact twoW_perSample_eq_shannonHartley W N₀ P hW hN₀ hP

end InformationTheory.Shannon.ShannonHartley
