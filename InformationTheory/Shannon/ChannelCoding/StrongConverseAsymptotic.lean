import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.StrongConverse
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.CsiszarProjection
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Channel coding asymptotic strong converse (Wolfowitz)

Builds on the single-shot Verdú-Han lower bound `channelCoding_average_success_le`
(`StrongConverse.lean`) to prove the Wolfowitz strong converse: for a memoryless channel
`W` over finite alphabets, if the rate `log (M n) / n` eventually exceeds `capacity W + δ`,
then the average error probability tends to `1`.

The argument substitutes the i.i.d. reference `Q := q*^n` (with `q*` the capacity-achieving
output) and threshold `n·(C + δ/2)` into the single-shot bound, then drives both the exponential
term and the high-information-density tail term to `0`.

## Main statements

* `klDiv_channel_le_capacity` — the capacity saddle point `D(W(a)‖q*) ≤ capacity W`
  (Phase A, load-bearing; deferred to `capacity-saddle-point`).
* `mutualInfo_segment_hasDerivAt` — the one-sided directional derivative of `I(p_t; W)`
  along the segment towards the Dirac input `δ_a` (the gateway atom for Phase A).
* `channelCoding_highLLR_tendsto_zero` — the average high-LLR tail mass tends to `0`
  (Phase B; non-i.i.d. Chebyshev concentration).
* `channelCoding_strong_converse_asymptotic` — the Wolfowitz strong converse headline.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 7.9.1 (strong converse).
* J. Wolfowitz, *Coding Theorems of Information Theory*, Springer, 1978.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory Filter
open InformationTheory.Shannon.CsiszarProjection
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Capacity saddle point (Phase A, load-bearing self-build): for a capacity-achieving input
`p` with full-support output `q* := outputDistribution (pmfToMeasure p) W`, every input symbol
`a` satisfies `D(W(a)‖q*) ≤ capacity W`. Carved out as a shared lemma for reuse across the
channel-coding converse family.

@residual(plan:capacity-saddle-point) -/
theorem klDiv_channel_le_capacity
    (W : Channel α β) [IsMarkovKernel W]
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (a : α) :
    klDivPmf (fun b ↦ (W a).real {b})
        (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
      ≤ capacity W := by
  sorry

/-- Gateway atom (Phase A): the one-sided (right) directional derivative of
`t ↦ I(p_t; W).toReal` at `t = 0` along the segment `p_t := (1 - t) • p + t • δ_a` towards the
Dirac input at `a`, equal to `D(W(a)‖q*) − I(p; W)` (the envelope/Danskin cancellation: the
moving reference `q_{p_t}` contributes nothing because `∑_b (dq/dt)(b) = 0`).

Stated as a `HasDerivWithinAt` over `Set.Ici 0` (right derivative), NOT a two-sided
`HasDerivAt`. The two-sided form is FALSE for boundary achievers: when `p a = 0`, for `t < 0`
the segment leaves the simplex (`p_t a = t < 0`), `pmfToMeasure` clamps the negative coordinate
via `ENNReal.ofReal` to `0`, giving the non-probability measure `(1 - t) • pmfToMeasure p`, so
`I(p_t; W).toReal` no longer follows the smooth simplex functional and develops a corner at `0`
(left derivative ≠ right derivative). Concrete refutation: `α = β = Bool`, `p = δ_false`,
`a = true`, any channel with `W false` full support and `W true ≠ W false`; the right derivative
is `D(W true‖W false) > 0`, but the left branch is the non-probability functional
`t ↦ (klDiv ((1-t) • J) ((1-t)² • (J)) ).toReal` (here the input-deterministic joint `J` equals
the product measure), whose derivative at `0` does not match. The one-sided form is also exactly
what the downstream first-order optimality argument consumes (cf. `csiszar_first_order_condition`,
which uses the `𝓝[>] 0` slope). See the orchestrator report / plan `capacity-saddle-point` for
the signature correction.

@residual(plan:capacity-saddle-point) -/
theorem mutualInfo_segment_hasDerivAt
    (W : Channel α β) [IsMarkovKernel W]
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (a : α) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        (mutualInfoOfChannel (pmfToMeasure ((1 - t) • p + t • Pi.single a 1)) W).toReal)
      (klDivPmf (fun b ↦ (W a).real {b})
          (fun b ↦ (outputDistribution (pmfToMeasure p) W).real {b})
        - (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (Set.Ici 0) 0 := by
  sorry

/-- Phase B: the average high-LLR tail mass vanishes as the block length grows, using the
non-i.i.d. Chebyshev concentration (`meas_ge_le_variance_div_sq` + `variance_sum_pi`) with the
i.i.d. reference `q*^n` and threshold `n·(capacity W + δ/2)`. Depends on the saddle point
`klDiv_channel_le_capacity` for the uniform per-codeword mean bound.

@residual(plan:capacity-saddle-point) -/
theorem channelCoding_highLLR_tendsto_zero
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ : 0 < δ)
    {p : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (M : ℕ → ℕ) (c : ∀ n, Code (M n) n α β) :
    Tendsto
      (fun n ↦ (1 / (M n : ℝ)) * ∑ m : Fin (M n),
        (Measure.pi (fun i ↦ W ((c n).encoder m i))).real
          (highLLRSet W (c n)
            (Measure.pi (fun _ : Fin n ↦ outputDistribution (pmfToMeasure p) W))
            ((n : ℝ) * (capacity W + δ / 2)) m))
      atTop (𝓝 0) := by
  sorry

/-- **Wolfowitz strong converse (asymptotic)**: for a memoryless channel `W` over finite
alphabets, if the rate `log (M n) / n` eventually exceeds `capacity W + δ` (with `δ > 0`), then
the average error probability tends to `1`.

The capacity-achieving input `p` (existing by `exists_capacity_achiever`) is received explicitly
together with the regularity precondition `hq_pos` (full-support output, so the log-likelihood
ratios are well-defined); both are preconditions, not load-bearing hypotheses.

@residual(plan:capacity-saddle-point) -/
@[entry_point]
theorem channelCoding_strong_converse_asymptotic
    (W : Channel α β) [IsMarkovKernel W]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (c : ∀ n, Code (M n) n α β)
    {δ : ℝ} (hδ : 0 < δ)
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun p : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    (hrate : ∀ᶠ n in atTop, capacity W + δ ≤ Real.log (M n) / n) :
    Tendsto (fun n ↦ ((c n).averageErrorProb W).toReal) atTop (𝓝 1) := by
  sorry

end InformationTheory.Shannon.ChannelCoding
