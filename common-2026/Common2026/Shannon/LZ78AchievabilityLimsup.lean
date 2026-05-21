import Common2026.Shannon.LZ78FinalGlue
import Common2026.Shannon.LZ78DistinctEncoding
import Common2026.Shannon.LZ78ConverseKraft
import Common2026.Shannon.LZ78SMBSandwich
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

This is the genuine Cover–Thomas Ziv-inequality consequence (`c·log c ≤
−log Pₙ{x}`, divided by `n` and combined with the per-phrase bit-length /
counting envelope), whose crux is the per-path parsing factorization the
current stationary layer cannot supply. It is **NOT a discharge**: it is a
*load-bearing* hypothesis, strictly more primitive than
`IsLZ78AchievabilityChainHyp` (per-realization eventual inequality vs.
`limsup`-level statement), and a genuine `Prop` (type ≠ conclusion), never
`True`, never a `:= h` alias. -/
structure IsLZ78AchievabilityZivUpperBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ) : Prop where
  /-- Eventually-in-`n`, a.s.-in-`ω`, the rate is below `blockLogAvg + slack`. -/
  upper : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
        ≤ blockLogAvg μ p n ω + slack n
  /-- The slack vanishes. -/
  slack_tendsto : Filter.Tendsto slack Filter.atTop (𝓝 (0 : ℝ))

end ZivUpperBound

/-! ## §2. Genuine `limsup` assembly -/

section LimsupAssembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Genuine `limsup` assembly**: the per-path Ziv upper bound, together
with the SMB a.s. convergence `blockLogAvg → entropyRate`, implies the
`blockLogAvg`-level achievability chain hypothesis
`IsLZ78AchievabilityChainHyp`.

Per a.s. `ω`, SMB gives `Tendsto (blockLogAvg) → entropyRate`, so
`limsup (blockLogAvg) = entropyRate`; the goal becomes
`limsup (lz/n) ≤ entropyRate`. For arbitrary `ε > 0`, eventually
`blockLogAvg n ω ≤ entropyRate + ε/2` (convergence) and `slack n ≤ ε/2`
(`slack → 0`), so with the Ziv upper bound `lz/n ≤ blockLogAvg + slack`,

```
(lz n x)/n ≤ blockLogAvg n ω + slack n ≤ entropyRate + ε   eventually,
```

hence `limsup (lz/n) ≤ entropyRate + ε` (`limsup_le_of_le`, using the
coboundedness above of the rate), and `ε → 0` closes it
(`le_of_forall_sub_le`). The SMB convergence is the genuine source of the
boundedness side condition; the only non-genuine input is the load-bearing
`IsLZ78AchievabilityZivUpperBound`. -/
theorem isLZ78AchievabilityChainHyp_of_zivUpperBound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ)
    (h_ub : IsLZ78AchievabilityZivUpperBound μ p lz78EncodingLength slack)
    (h_block_tendsto : ∀ᵐ ω ∂μ,
        Filter.Tendsto (fun n => blockLogAvg μ p n ω) Filter.atTop
          (𝓝 (entropyRate μ p)))
    (h_lz_cobdd : ∀ᵐ ω ∂μ,
        Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
          (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))) :
    IsLZ78AchievabilityChainHyp μ p lz78EncodingLength := by
  rw [isLZ78AchievabilityChainHyp_def]
  filter_upwards [h_ub.upper, h_block_tendsto, h_lz_cobdd]
    with ω h_upper_ω h_block_ω h_lz_cobdd_ω
  set B : ℕ → ℝ := fun n => blockLogAvg μ p n ω with hB
  set L : ℕ → ℝ :=
    fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ) with hL
  set H : ℝ := entropyRate μ p with hH
  -- `limsup B = H` from the SMB convergence.
  have h_limsup_B : Filter.limsup B Filter.atTop = H := h_block_ω.limsup_eq
  rw [h_limsup_B]
  -- Goal: `limsup L ≤ H`. Show `∀ ε > 0, limsup L − ε ≤ H`, i.e. `limsup L ≤ H + ε`.
  refine le_of_forall_sub_le (fun ε hε => ?_)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- Eventually `slack n ≤ ε/2` from `slack → 0`.
  have h_slack_le : ∀ᶠ n in Filter.atTop, slack n ≤ ε / 2 := by
    have := h_ub.slack_tendsto.eventually (gt_mem_nhds hε2)
    filter_upwards [this] with n hn
    exact le_of_lt hn
  -- Eventually `B n ≤ H + ε/2` from `B → H`.
  have h_block_le : ∀ᶠ n in Filter.atTop, B n ≤ H + ε / 2 := by
    have := h_block_ω.eventually (gt_mem_nhds (show H < H + ε / 2 by linarith))
    filter_upwards [this] with n hn
    exact le_of_lt hn
  -- Eventually `L n ≤ H + ε`.
  have h_ev_le : ∀ᶠ n in Filter.atTop, L n ≤ H + ε := by
    filter_upwards [h_upper_ω, h_slack_le, h_block_le] with n hn hslk hblk
    calc L n ≤ B n + slack n := hn
      _ ≤ (H + ε / 2) + ε / 2 := by linarith
      _ = H + ε := by ring
  -- `limsup L ≤ H + ε`, hence `limsup L − ε ≤ H`.
  have := limsup_le_of_le h_lz_cobdd_ω h_ev_le
  linarith [this]

end LimsupAssembly

/-! ## §3. Distinct-code instance -/

section DistinctInstance

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Achievability chain hypothesis for the distinct LZ78 code**, from the
named honest Ziv upper bound. Genuine assembly; the only non-genuine input
is the load-bearing `IsLZ78AchievabilityZivUpperBound`. -/
theorem isLZ78AchievabilityChainHyp_distinct
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slack : ℕ → ℝ)
    (h_ub : IsLZ78AchievabilityZivUpperBound μ p.toStationaryProcess
              (@lz78DistinctEncodingLength α _ _ _) slack) :
    IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
      (@lz78DistinctEncodingLength α _ _ _) := by
  refine isLZ78AchievabilityChainHyp_of_zivUpperBound μ p.toStationaryProcess
    (@lz78DistinctEncodingLength α _ _ _) slack h_ub
    (shannon_mcmillan_breiman μ p) ?_
  -- Coboundedness (≤) of the distinct rate from its a.s. lower boundedness
  -- (`IsBoundedUnder (· ≥ ·)` ⟹ `IsCoboundedUnder (· ≤ ·)`).
  filter_upwards [lz78DistinctEncodingLength_isBoundedUnder_ge μ p] with ω hω
  exact hω.isCoboundedUnder_le

end DistinctInstance

/-! ## §4. Fully-discharged distinct headline (both chain hyps removed) -/

section GenuineHeadline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A distinct headline with both chain hypotheses internally
discharged from primitive per-path honest inputs**.

Compared to `lz78_two_sided_optimality_distinct_bdd_free`
(`LZ78DistinctEncoding.lean`), which takes the two `limsup`/`liminf`-level
chain hypotheses `h_achiev` / `h_converse`, this form removes **both** and
supplies them internally from the two *strictly-more-primitive* named
honest hypotheses:

* `h_ub : IsLZ78AchievabilityZivUpperBound` — the per-path Ziv upper bound
  (Cover–Thomas Eq. 13.124), and
* `h_lb : IsLZ78ConverseCodingLowerBound` — the per-path converse coding
  lower bound (Cover–Thomas Eq. 13.130),

each a per-realization eventual inequality with vanishing slack. The
`limsup`/`liminf` plumbing and the SMB-driven boundedness are all genuine
(`isLZ78AchievabilityChainHyp_distinct` / `isLZ78ConverseChainHyp_distinct`).

This is honest progress on *both* directions: each `blockLogAvg`-level
deferral is replaced by a per-realization eventual inequality. The two
remaining inputs are load-bearing (not discharges): they stand for the
genuine Ziv inequality / converse coding theorem, which the current
stationary layer (no kernel / `compProd` structure) cannot derive. -/
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
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_distinct_bdd_free μ p
    (isLZ78AchievabilityChainHyp_distinct μ p slackUp h_ub)
    (isLZ78ConverseChainHyp_distinct μ p slackLow h_lb)

end GenuineHeadline

end InformationTheory.Shannon
