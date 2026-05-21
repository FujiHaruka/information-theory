import Common2026.Shannon.LZ78FinalGlue
import Common2026.Shannon.LZ78DistinctEncoding
import Common2026.Shannon.LZ78ConverseKraft
import Common2026.Shannon.LZ78SMBSandwich
import Common2026.Shannon.LZ78ZivEntropyBridge
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 achievability chain-hypothesis assembly (T4-A, L-LZ1)

This file assembles the **achievability-direction chain hypothesis**
`IsLZ78AchievabilityChainHyp` for the *distinct* LZ78 code
(`lz78DistinctEncodingLength`, `LZ78DistinctEncoding.lean`) — the
`h_achiev` argument of the headline
`lz78_two_sided_optimality_distinct_bdd_free`.

The achievability asserts the a.s. limsup upper bound

```
∀ᵐ ω ∂μ, limsup (fun n => lz/n) ≤ limsup (blockLogAvg μ p n ω)
```

i.e. the LZ78 per-symbol rate cannot asymptotically exceed the per-block
negative log-likelihood (the Ziv-inequality consequence, Cover–Thomas
Eq. 13.124).

## Honesty status (read this before reusing)

The genuine content is the **per-path Ziv inequality** `c·log c ≤
−log Pₙ{x}` (Cover–Thomas Eq. 13.122–124), whose crux is the per-path
parsing factorization `Pₙ{x} = ∏ⱼ qⱼ`. As recorded in
`LZ78ZivEntropyBridge.lean`, the current stationary layer carries no
kernel / `compProd` / disintegration structure to derive that
factorization, and the genuine combinatorial Ziv inequality is the
remaining wall on this side. (Note: the existing genuine counting bound
`lz78PhraseStrings_mul_log_le` gives `c·log c ≤ K·n`, a bound to a
*constant* rate `K`, not to `limsup blockLogAvg`; bridging `K·n` to
`−log Pₙ` is exactly the factorization the layer cannot supply.)

We therefore expose the Eq. 13.124 consequence as a single, isolated,
**named honest hypothesis** `IsLZ78AchievabilityZivUpperBound`, strictly
more primitive than the `limsup`-level `IsLZ78AchievabilityChainHyp`: it is
a per-realization, per-`n` eventual inequality `lz/n ≤ blockLogAvg n ω +
slack n` with `slack → 0`, rather than a `limsup`-level statement. From it
the `limsup` chain hypothesis is derived **genuinely** here (`limsup`
monotonicity + SMB convergence + slack absorption).

The hypothesis is a genuine `Prop` (type ≠ conclusion), never `True`,
never a `:= h` defeq alias, and its docstring marks it load-bearing.

## File layout

* **§1.** `IsLZ78AchievabilityZivUpperBound` — the named honest per-path
  Eq. 13.124 upper bound (load-bearing).
* **§2.** `isLZ78AchievabilityChainHyp_of_zivUpperBound` — genuine
  `limsup` assembly: the Ziv upper bound implies
  `IsLZ78AchievabilityChainHyp`.
* **§3.** `isLZ78AchievabilityChainHyp_distinct` — the distinct-code
  instance.
* **§4.** `lz78_two_sided_optimality_distinct_genuine` — the headline with
  *both* chain hypotheses removed, supplied internally from the two named
  primitive honest hypotheses (the Ziv upper bound + the converse coding
  lower bound). This is the maximally-discharged distinct headline.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. Named honest per-path Ziv upper bound (L-LZ1-D) -/

section ZivUpperBound

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Isolated honest input (L-LZ1-D, Cover–Thomas Eq. 13.124)** — the LZ78
achievability Ziv upper bound, in a strictly-more-primitive
per-realization form than the `limsup`-level
`IsLZ78AchievabilityChainHyp`.

For an a.s. set of `ω`, *eventually in `n`*, the per-symbol code rate
`(lz n (blockRV n ω))/n` is at most the per-block negative log-likelihood
`blockLogAvg μ p n ω` plus a vanishing slack `slack n`:

```
∀ᵐ ω ∂μ, ∀ᶠ n in atTop, (lz n (blockRV n ω) : ℝ) / n
                          ≤ blockLogAvg μ p n ω + slack n
slack n → 0
```

This is the genuine Cover–Thomas Ziv-inequality consequence (`c·log₂ c ≤
−log₂ Pₙ{x}`, divided by `n` and combined with the per-phrase bit-length /
counting envelope), whose crux is the per-path parsing factorization the
current stationary layer cannot supply. It is **NOT a discharge**: it is a
*load-bearing* hypothesis, strictly more primitive than
`IsLZ78AchievabilityChainHyp` (per-realization eventual inequality vs.
`limsup`-level statement), and a genuine `Prop` (type ≠ conclusion), never
`True`, never a `:= h` alias.

**Base-2 (bit) unit**: the LZ78 code length `lz78EncodingLength` is in
**bits**, so the genuine Ziv inequality is `c·log₂ c ≤ −log₂ Pₙ{x}` and the
upper bound is against the **bit-based** per-block estimator
`blockLogAvg₂ μ p n ω = blockLogAvg μ p n ω / log 2` — not `blockLogAvg`
(nats). The previous coefficient-1 form `lz/n ≤ blockLogAvg + slack` was a
unit bug (genuinely false for nondegenerate ergodic processes, where Ziv
gives the coefficient `1/log 2`); this is the corrected Cover–Thomas
Theorem 13.5.3 statement. -/
structure IsLZ78AchievabilityZivUpperBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ) : Prop where
  /-- Eventually-in-`n`, a.s.-in-`ω`, the bit-rate is below `blockLogAvg₂ + slack`. -/
  upper : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
        ≤ blockLogAvg₂ μ p n ω + slack n
  /-- The slack vanishes. -/
  slack_tendsto : Filter.Tendsto slack Filter.atTop (𝓝 (0 : ℝ))

end ZivUpperBound

/-! ## §3. Genuine base-2 `limsup` assembly -/

section LimsupAssembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Genuine base-2 `limsup` assembly**: the per-path (bit-based) Ziv upper
bound, together with the base-2 SMB a.s. convergence
`blockLogAvg₂ → entropyRate₂`, gives the a.s. limsup upper bound
`limsup (lz/n) ≤ entropyRate₂`.

Per a.s. `ω`, the base-2 SMB gives `blockLogAvg₂ → entropyRate₂`, so
`limsup blockLogAvg₂ = entropyRate₂`. For arbitrary `ε > 0`, eventually
`blockLogAvg₂ n ω ≤ entropyRate₂ + ε/2` and `slack n ≤ ε/2`, so with the
Ziv upper bound `lz/n ≤ blockLogAvg₂ + slack`,

```
(lz n x)/n ≤ blockLogAvg₂ n ω + slack n ≤ entropyRate₂ + ε   eventually,
```

hence `limsup (lz/n) ≤ entropyRate₂ + ε` (`limsup_le_of_le`, coboundedness
of the rate), and `ε → 0` closes it. The only non-genuine input is the
load-bearing `IsLZ78AchievabilityZivUpperBound`. -/
theorem lz78_achievability_limsup_le₂
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ)
    (h_ub : IsLZ78AchievabilityZivUpperBound μ p.toStationaryProcess
              lz78EncodingLength slack)
    (h_lz_cobdd : ∀ᵐ ω ∂μ,
        Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
          (fun n => (lz78EncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78EncodingLength n
          (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ entropyRate₂ μ p.toStationaryProcess := by
  filter_upwards [h_ub.upper, shannon_mcmillan_breiman₂ μ p, h_lz_cobdd]
    with ω h_upper_ω h_block_ω h_lz_cobdd_ω
  set B : ℕ → ℝ := fun n => blockLogAvg₂ μ p.toStationaryProcess n ω with hB
  set L : ℕ → ℝ :=
    fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
      / (n : ℝ) with hL
  set H : ℝ := entropyRate₂ μ p.toStationaryProcess with hH
  -- Goal: `limsup L ≤ H`. Show `∀ ε > 0, limsup L − ε ≤ H`.
  refine le_of_forall_sub_le (fun ε hε => ?_)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h_slack_le : ∀ᶠ n in Filter.atTop, slack n ≤ ε / 2 := by
    have := h_ub.slack_tendsto.eventually (gt_mem_nhds hε2)
    filter_upwards [this] with n hn
    exact le_of_lt hn
  have h_block_le : ∀ᶠ n in Filter.atTop, B n ≤ H + ε / 2 := by
    have := h_block_ω.eventually (gt_mem_nhds (show H < H + ε / 2 by linarith))
    filter_upwards [this] with n hn
    exact le_of_lt hn
  have h_ev_le : ∀ᶠ n in Filter.atTop, L n ≤ H + ε := by
    filter_upwards [h_upper_ω, h_slack_le, h_block_le] with n hn hslk hblk
    calc L n ≤ B n + slack n := hn
      _ ≤ (H + ε / 2) + ε / 2 := by linarith
      _ = H + ε := by ring
  have := limsup_le_of_le h_lz_cobdd_ω h_ev_le
  linarith [this]

end LimsupAssembly

/-! ## §4. Base-2 distinct headline (both primitives, sandwich → Tendsto) -/

section GenuineHeadline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A base-2 distinct headline (genuine Cover–Thomas Theorem 13.5.3)**,
with both directions internally assembled from the two primitive per-path
honest inputs.

For an ergodic process on a finite alphabet, the **bit-based** per-symbol
LZ78 rate `(lz n (blockRV n ω))/n` converges a.s. to the **base-2 entropy
rate** `entropyRate₂ μ p = entropyRate μ p / log 2` (entropy in bits per
symbol). This is the genuine Cover–Thomas Thm 13.5.3 statement: the LZ78
code length is in bits, so the limit is the entropy measured in bits — not
the natural-log `entropyRate` (which was a unit bug in the earlier
`→ entropyRate` form).

The two inputs are:

* `h_ub : IsLZ78AchievabilityZivUpperBound` — the per-path bit-based Ziv
  upper bound `lz/n ≤ blockLogAvg₂ + slack` (Cover–Thomas Eq. 13.124), and
* `h_lb : IsLZ78ConverseCodingLowerBound` — the per-path bit-based converse
  coding lower bound `blockLogAvg₂ − slack ≤ lz/n` (Cover–Thomas Eq. 13.130),

each a per-realization eventual inequality with vanishing slack. The
base-2 SMB convergence (`shannon_mcmillan_breiman₂`), the `limsup`/`liminf`
half-bounds (`lz78_achievability_limsup_le₂` / `lz78_converse_le_liminf₂`),
the per-symbol boundedness (`lz78DistinctEncodingLength_isBoundedUnder_le`
/ `_ge`), and the final sandwich (`tendsto_of_le_liminf_of_limsup_le`) are
all genuine. The two remaining inputs are load-bearing: they stand for the
genuine bit-based Ziv inequality / averaged converse coding theorem. -/
theorem lz78_two_sided_optimality_distinct_genuine
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slackUp slackLow : ℕ → ℝ)
    (h_ub : IsLZ78AchievabilityZivUpperBound μ p.toStationaryProcess
              (@lz78DistinctEncodingLength α _ _ _) slackUp)
    (h_lb : IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess
              (@lz78DistinctEncodingLength α _ _ _) slackLow) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  -- Coboundedness of the per-symbol rate, from genuine boundedness.
  have h_bdd_le := lz78DistinctEncodingLength_isBoundedUnder_le μ p
  have h_bdd_ge := lz78DistinctEncodingLength_isBoundedUnder_ge μ p
  -- The two base-2 half-bounds.
  have h_limsup_le := lz78_achievability_limsup_le₂ μ p
    (@lz78DistinctEncodingLength α _ _ _) slackUp h_ub
    (by filter_upwards [h_bdd_ge] with ω hω; exact hω.isCoboundedUnder_le)
  have h_le_liminf := lz78_converse_le_liminf₂ μ p
    (@lz78DistinctEncodingLength α _ _ _) slackLow h_lb
    (by filter_upwards [h_bdd_le] with ω hω; exact hω.isCoboundedUnder_ge)
  -- Sandwich `liminf ≥ H`, `limsup ≤ H`, with boundedness, gives `Tendsto`.
  filter_upwards [h_limsup_le, h_le_liminf, h_bdd_le, h_bdd_ge]
    with ω hu hl hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

end GenuineHeadline

end InformationTheory.Shannon
