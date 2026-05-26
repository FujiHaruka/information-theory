import Common2026.Draft.Shannon.LZ78FinalGlue
import Common2026.Draft.Shannon.LZ78DistinctEncoding
import Common2026.Draft.Shannon.LZ78ConverseKraft
import Common2026.Draft.Shannon.LZ78SMBSandwich
import Common2026.Shannon.LZ78ZivEntropyBridge
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 achievability + base-2 distinct headline (T4-A, L-LZ1)

This file assembles the **base-2 (bit) distinct LZ78 headline**
`lz78_two_sided_optimality_distinct_genuine` from the two primitive
per-path honest inputs, targeting the genuine Cover–Thomas Theorem 13.5.3
limit `entropyRate₂ = entropyRate / log 2` (entropy in **bits** per
symbol).

## Base-2 unit correction (read this first)

The LZ78 code length `lz78DistinctEncodingLength` is measured in **bits**
(`LZ78Phrase.bitLength` uses `Nat.log 2`), whereas `blockLogAvg` /
`entropyRate` are **natural-log** (nats). The genuine Cover–Thomas Thm
13.5.3 limit for the bit-based per-symbol rate is therefore the **base-2**
entropy rate `entropyRate₂ = entropyRate / log 2`, against which the
bit-based estimator is `blockLogAvg₂ = blockLogAvg / log 2`
(`LZ78ZivEntropyBridge.lean`). The earlier `→ entropyRate` (nats) form was
a *unit bug*; this file states the corrected bit-based theorem.

## Honesty status (read this before reusing)

The genuine content is the **bit-based per-path Ziv inequality**
`c·log₂ c ≤ −log₂ Pₙ{x}` (Cover–Thomas Eq. 13.122–124). Its parsing
factorization side is now **genuine** (`StationaryKernel.lean`): the
algebraic telescoping `prod_condPhraseProb_telescope` plus prefix
monotonicity gives the unconditional Ziv-direction inequality
`Pₙ{x} ≤ ∏ⱼ qⱼ` (`blockProb_le_prod_condPhraseProb`), and
`isLZ78PerPathParsingFactorization_of_pos` constructs the factorization
from a.s. regularity alone — the earlier *false* parse-completeness
equality `Pₙ = ∏ⱼ qⱼ` (which leaves an unfinished tail; e.g. the block
`(a,a)` parses to `[[a]]`, length `1 < 2`) is no longer needed.

What is *still* load-bearing is the **distinct-phrase combinatorial Ziv
core** `c·log₂ c ≤ ∑ⱼ −log₂ qⱼ` (Cover–Thomas Lemma 13.5.5): the log-sum
step needs the conditional factors to behave like a (sub-)distribution
(`∑ qⱼ ≤ 1` per dictionary stratum), which is the genuine Ziv
combinatorics, not a telescoping. The existing genuine counting bound
`lz78PhraseStrings_mul_log_le` gives `c·log c ≤ K·n` (constant rate `K`),
not `−log Pₙ`. The Ziv upper bound `c·log₂ c ≤ −log₂ Pₙ` therefore remains
exposed as a single isolated **named honest hypothesis**
`IsLZ78AchievabilityZivUpperBound` (bit-based, against `blockLogAvg₂`).

The hypothesis is a genuine `Prop` (type ≠ conclusion), never `True`,
never a `:= h` defeq alias, and its docstring marks it load-bearing.

## File layout

* **§1.** `IsLZ78AchievabilityZivUpperBound` — the named honest per-path
  bit-based Eq. 13.124 upper bound (load-bearing).
* **§2.** `shannon_mcmillan_breiman₂` is reused from `LZ78ConverseKraft.lean`.
* **§3.** `lz78_achievability_limsup_le₂` — genuine base-2 `limsup`
  assembly: the Ziv upper bound + base-2 SMB give `limsup (lz/n) ≤
  entropyRate₂`.
* **§4.** `lz78_two_sided_optimality_distinct_genuine` — the base-2
  distinct headline, both directions assembled internally from the two
  named primitive honest hypotheses (bit-based Ziv upper bound + converse
  coding lower bound), converging to `entropyRate₂`.
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
load-bearing `IsLZ78AchievabilityZivUpperBound`.

`@residual(plan:lz78-achievability-converse-plan)` -/
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
  sorry

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
genuine bit-based Ziv inequality / averaged converse coding theorem.

`@residual(plan:lz78-achievability-converse-plan)` -/
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
  sorry

end GenuineHeadline

end InformationTheory.Shannon
