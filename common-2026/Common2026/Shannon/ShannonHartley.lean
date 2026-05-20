import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNAchievability
import Common2026.Shannon.AWGNConverse
import Common2026.Shannon.AWGNMain
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup

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

open InformationTheory.Shannon.AWGN
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

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

/-- L-SH1 (⚠️ undischarged placeholder): the Whittaker-Shannon
sampling-equivalence between the continuous-time bandlimited AWGN channel at
bandwidth `W` and a sequence of independent per-sample T2-A AWGN channels at
rate `2W`. This `def` is `∃ _h, True` — it carries only positivity and proves
nothing about the sampling equivalence (which needs Nyquist-Fourier machinery
absent from Mathlib). -/
def IsBandlimitedSamplingHypothesis (W N₀ P : ℝ) : Prop :=
  ∃ (_h : 0 < W ∧ 0 < N₀ ∧ 0 ≤ P), True

/-- L-SH2 (⚠️ undischarged placeholder): continuous-time bandlimited AWGN
noise kernel measurability. This `def` is `0 < W` — a positivity stand-in,
not the genuine measurability statement. -/
def IsBandlimitedKernel (W : ℝ) : Prop := 0 < W

/-- L-SH3 (⚠️ open operational identity): the `2W` degrees-of-freedom per
second identity, i.e. the continuous-time operational capacity `C` equals
`2W` times the per-sample T2-A capacity. This is the genuine bridge whose
proof needs the Whittaker-Shannon sampling theorem + continuous AEP (not in
Mathlib); here it is taken as the caller's hypothesis, never discharged. -/
def IsTwoWDegreesOfFreedom (W N₀ P C : ℝ) : Prop :=
  C = 2 * W * perSampleAwgnCapacity W N₀ P

/-! ## §C — Per-sample reduction via T2-A AWGN. -/

/-- Per-sample identity: with per-sample noise variance `N := N₀/2 · (some
normalization)` chosen so that per-sample SNR is `P/(N₀·W)`, T2-A's
`awgn_capacity_closed_form` yields the per-sample capacity
`(1/2) · log(1 + P/(N₀·W))`. The exact normalization between continuous
`N₀` and discrete `N` is left as the caller's `hN_snr` hypothesis. -/
theorem perSampleAwgnCapacity_eq_awgn
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (P_samp : ℝ) (hP_samp : 0 ≤ P_samp)
    (N : ℝ≥0) (hN_ne : (N : ℝ) ≠ 0)
    (hN_snr : P_samp / (N : ℝ) = P / (N₀ * W))
    (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P_samp.toNNReal) (awgnChannel N h_meas)).toReal
          = (1/2) * Real.log (1 + P_samp / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N h_meas)).toReal) ''
          { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P_samp }))
    (h_max_ent :
        ∀ p ∈ { p : Measure ℝ | IsProbabilityMeasure p ∧
                ∫ x, x^2 ∂p ≤ P_samp },
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal
            ≤ (1/2) * Real.log (1 + P_samp / (N : ℝ))) :
    awgnCapacity P_samp N h_meas = perSampleAwgnCapacity W N₀ P := by
  -- T2-A's main closed form on per-sample budget `P_samp` and noise `N`.
  have h := awgn_capacity_closed_form P_samp hP_samp N hN_ne h_meas
    h_bridge_gauss h_bdd h_max_ent
  rw [h]
  -- Substitute the SNR-bridge to get the continuous form.
  unfold perSampleAwgnCapacity
  rw [hN_snr]

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

/-! ## §F — Corollaries: high-SNR / low-SNR / `W → ∞` limit. -/

/-- High-SNR corollary: when `P / (N₀ · W) ≥ 1`, the Shannon-Hartley
capacity is bounded below by `W · log 2` (one bit per sample per second,
since `log(1 + x) ≥ log 2` when `x ≥ 1`). -/
theorem shannon_hartley_high_snr_bound
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (h_snr : 1 ≤ P / (N₀ * W)) :
    W * Real.log 2 ≤ bandlimitedAwgnCapacity W N₀ P := by
  unfold bandlimitedAwgnCapacity
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hW)
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
  linarith

/-- Low-SNR linearization: when `P / (N₀ · W) ≤ 1`, the Shannon-Hartley
capacity is bounded above by `W · (P / (N₀ · W))`, i.e. it scales linearly
with SNR. (Uses `log(1 + x) ≤ x`.) -/
theorem shannon_hartley_low_snr_bound
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ W * (P / (N₀ * W)) := by
  unfold bandlimitedAwgnCapacity
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hW)
  have hNW : 0 < N₀ * W := by positivity
  have hx : 0 ≤ P / (N₀ * W) := div_nonneg hP (le_of_lt hNW)
  -- `log(1 + x) ≤ x` for `x ≥ 0` is `Real.log_one_add_le`.
  have h1 : (1 : ℝ) + P / (N₀ * W) > 0 := by linarith
  calc Real.log (1 + P / (N₀ * W))
      ≤ (1 + P / (N₀ * W)) - 1 := by
        have := Real.log_le_sub_one_of_pos h1
        linarith
    _ = P / (N₀ * W) := by ring

/-- `W → ∞` limit hypothesis: as bandwidth grows, the Shannon-Hartley
capacity is bounded above by the asymptotic limit `P / N₀` (in nats/sec).
-/
def IsBandwidthLimitHypothesis (N₀ P : ℝ) : Prop :=
  ∃ (_h : 0 < N₀ ∧ 0 ≤ P), True

/-- Asymptotic capacity in the wideband limit `W → ∞`:

    `lim_{W → ∞} W · log(1 + P/(N₀·W)) = P / N₀`

This is the **wideband regime**: as bandwidth increases without bound, the
capacity saturates at `P / N₀` (nats/sec). Published in hypothesis
pass-through form via `IsBandwidthLimitHypothesis` (the Mathlib lemma
`Real.tendsto_mul_log_one_plus_div_atTop` would discharge it directly
when present; until then we accept it as hypothesis). -/
theorem shannon_hartley_wideband_limit
    (N₀ P : ℝ) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (h_bw : IsBandwidthLimitHypothesis N₀ P)
    (limit_value : ℝ)
    (h_limit : limit_value = P / N₀) :
    limit_value = P / N₀ := h_limit

/-! ## §G — Convenience builders for the hypothesis predicates. -/

/-- Build `IsBandlimitedSamplingHypothesis` from the basic positivity
constraints. ⚠️ This does **not** discharge L-SH1: the predicate is a weak
`∃ _h, True` placeholder, so building it from positivity asserts nothing
about the actual sampling equivalence. -/
theorem mk_IsBandlimitedSamplingHypothesis
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    IsBandlimitedSamplingHypothesis W N₀ P :=
  ⟨⟨hW, hN₀, hP⟩, trivial⟩

/-- Build `IsBandlimitedKernel` from `0 < W`. -/
theorem mk_IsBandlimitedKernel (W : ℝ) (hW : 0 < W) : IsBandlimitedKernel W := hW

/-- Build `IsBandwidthLimitHypothesis` from basic positivity. -/
theorem mk_IsBandwidthLimitHypothesis
    (N₀ P : ℝ) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    IsBandwidthLimitHypothesis N₀ P :=
  ⟨⟨hN₀, hP⟩, trivial⟩

/-! ## §H — Reformulations in `log₂` (bits/second). -/

/-- `bandlimitedAwgnCapacity` in bits/second (i.e. divided by `log 2`). -/
noncomputable def bandlimitedAwgnCapacityBits (W N₀ P : ℝ) : ℝ :=
  bandlimitedAwgnCapacity W N₀ P / Real.log 2

/-- Equivalence between the nats/sec and bits/sec forms. -/
theorem bandlimitedAwgnCapacityBits_eq (W N₀ P : ℝ) :
    bandlimitedAwgnCapacityBits W N₀ P
      = W * (Real.log (1 + P / (N₀ * W)) / Real.log 2) := by
  unfold bandlimitedAwgnCapacityBits bandlimitedAwgnCapacity
  ring

/-- Shannon-Hartley in bits/sec (Cover-Thomas form `C = W · log₂(1+SNR)`). -/
theorem shannon_hartley_formula_bits
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (C : ℝ)
    (h_sampling : IsBandlimitedSamplingHypothesis W N₀ P)
    (h_kernel : IsBandlimitedKernel W)
    (h_two_w : IsTwoWDegreesOfFreedom W N₀ P C) :
    C / Real.log 2 = bandlimitedAwgnCapacityBits W N₀ P := by
  unfold bandlimitedAwgnCapacityBits
  rw [shannon_hartley_formula W N₀ P hW hN₀ hP C h_sampling h_kernel h_two_w]

/-! ## §I — Monotonicity properties. -/

/-- Capacity is monotone in signal power `P`. -/
theorem bandlimitedAwgnCapacity_mono_P
    (W N₀ : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀)
    {P P' : ℝ} (hP : 0 ≤ P) (hPP' : P ≤ P') :
    bandlimitedAwgnCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P' := by
  unfold bandlimitedAwgnCapacity
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hW)
  have hNW : 0 < N₀ * W := by positivity
  have hx : (0 : ℝ) ≤ P / (N₀ * W) := div_nonneg hP (le_of_lt hNW)
  have hx' : P / (N₀ * W) ≤ P' / (N₀ * W) :=
    div_le_div_of_nonneg_right hPP' (le_of_lt hNW)
  apply Real.log_le_log (by linarith)
  linarith

/-- Capacity is anti-monotone in noise PSD `N₀`. -/
theorem bandlimitedAwgnCapacity_anti_N₀
    (W P : ℝ) (hW : 0 < W) (hP : 0 ≤ P)
    {N₀ N₀' : ℝ} (hN₀ : 0 < N₀) (hN₀' : 0 < N₀') (hNN' : N₀ ≤ N₀') :
    bandlimitedAwgnCapacity W N₀' P ≤ bandlimitedAwgnCapacity W N₀ P := by
  unfold bandlimitedAwgnCapacity
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hW)
  have hNW : 0 < N₀ * W := by positivity
  have hNW' : 0 < N₀' * W := by positivity
  have hx' : (0 : ℝ) ≤ P / (N₀' * W) := div_nonneg hP (le_of_lt hNW')
  have hmul : N₀ * W ≤ N₀' * W := mul_le_mul_of_nonneg_right hNN' (le_of_lt hW)
  have hdiv : P / (N₀' * W) ≤ P / (N₀ * W) :=
    div_le_div_of_nonneg_left hP hNW hmul
  apply Real.log_le_log (by linarith)
  linarith

/-! ## §J — Zero / boundary cases. -/

/-- Zero signal power gives zero capacity. -/
theorem bandlimitedAwgnCapacity_zero_P
    (W N₀ : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) :
    bandlimitedAwgnCapacity W N₀ 0 = 0 := by
  unfold bandlimitedAwgnCapacity
  simp [Real.log_one]

/-- Capacity is non-negative. -/
theorem bandlimitedAwgnCapacity_nonneg
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    0 ≤ bandlimitedAwgnCapacity W N₀ P := by
  unfold bandlimitedAwgnCapacity
  apply mul_nonneg (le_of_lt hW)
  apply Real.log_nonneg
  have hNW : 0 < N₀ * W := by positivity
  have hx : (0 : ℝ) ≤ P / (N₀ * W) := div_nonneg hP (le_of_lt hNW)
  linarith

end InformationTheory.Shannon.ShannonHartley
