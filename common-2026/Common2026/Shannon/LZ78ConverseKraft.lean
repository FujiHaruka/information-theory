import Common2026.Shannon.LZ78ConverseDischarge
import Common2026.Shannon.LZ78DistinctEncoding
import Common2026.Shannon.LZ78FinalGlue
import Common2026.Shannon.LZ78SMBSandwich
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 converse chain-hypothesis assembly (T4-A, L-LZ2)

This file assembles the **converse-direction chain hypothesis**
`IsLZ78ConverseChainHyp` for the *distinct* LZ78 code
(`lz78DistinctEncodingLength`, `LZ78DistinctEncoding.lean`) — the
`h_converse` argument of the headline
`lz78_two_sided_optimality_distinct_bdd_free` (`LZ78DistinctEncoding.lean`).

The converse asserts the a.s. liminf lower bound

```
∀ᵐ ω ∂μ, liminf (blockLogAvg μ p n ω) ≤ liminf (fun n => lz/n)
```

i.e. the LZ78 per-symbol rate cannot asymptotically beat the per-block
negative log-likelihood (Cover–Thomas Eq. 13.130).

## Honesty status (read this before reusing)

The genuine content of the converse is the **Cover–Thomas Eq. 13.130
coding lower bound** `(lz n x)/n ≥ blockLogAvg μ p n ω − o(1)` — that any
prefix-free / uniquely-decodable code cannot beat the negative
log-likelihood *on average*. This is **not** a pointwise fact: per a fixed
realization `x`, an LZ78 codeword can be *shorter* than `−log Pₙ{x}` (that
is exactly the universality of LZ78). It is the expectation-level Kraft /
converse-coding theorem, lifted to an a.s. eventual lower bound; the
existing `ShannonCode.lean` pointwise lemma
`rpow_neg_shannonLength_le_real` is about the *Shannon* code length, and
`lz(x) ≥ shannonLength(x)` fails pointwise, so it does **not** discharge
this. (See the report accompanying this file: the `lz78-residual-discharge`
plan's "pointwise `2^{−lz(x)} ≤ Pₙ{x}` via shannonLength" route in Phase
C3 is mathematically unsound and is **not** used here.)

We therefore expose the Eq. 13.130 lower bound as a single, isolated,
**named honest hypothesis** `IsLZ78ConverseCodingLowerBound`, which is
*strictly more primitive* than the `blockLogAvg`-level
`IsLZ78ConverseChainHyp`: it is a per-realization, per-`n` eventual
inequality `blockLogAvg n ω − slack n ≤ lz/n` with `slack n → 0`, rather
than a `liminf`-level statement. From it the `liminf` chain hypothesis is
derived **genuinely** here (`liminf` monotonicity + slack absorption), and
chained into a converse-discharged distinct headline.

The hypothesis is a genuine `Prop` (type ≠ conclusion), never `True`,
never a `:= h` defeq alias, and its docstring marks it load-bearing.

## File layout

* **§1.** `IsLZ78ConverseCodingLowerBound` — the named honest per-path
  Eq. 13.130 lower bound (load-bearing).
* **§2.** `isLZ78ConverseChainHyp_of_codingLowerBound` — genuine
  `liminf` assembly: the coding lower bound implies `IsLZ78ConverseChainHyp`.
* **§3.** `isLZ78ConverseChainHyp_distinct` — the distinct-code instance.
* **§4.** `lz78_two_sided_optimality_distinct_converse_discharged` — the
  headline with `h_converse` removed (supplied internally from the named
  hypothesis), carrying only `h_achiev` plus the converse coding bound.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. Named honest per-path coding lower bound (L-LZ2-D) -/

section CodingLowerBound

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Isolated honest input (L-LZ2-D, Cover–Thomas Eq. 13.130)** — the LZ78
converse coding lower bound, in a strictly-more-primitive per-realization
form than the `blockLogAvg`-level `IsLZ78ConverseChainHyp`.

For an a.s. set of `ω`, *eventually in `n`*, the per-symbol code rate
`(lz n (blockRV n ω))/n` is at least the per-block negative log-likelihood
`blockLogAvg μ p n ω` minus a vanishing slack `slack n`:

```
∀ᵐ ω ∂μ, ∀ᶠ n in atTop, blockLogAvg μ p n ω − slack n
                          ≤ (lz n (blockRV n ω) : ℝ) / n
slack n → 0
```

This is the genuine Cover–Thomas converse coding theorem (no prefix-free /
uniquely-decodable code beats the negative log-likelihood on average),
lifted to an a.s. eventual lower bound. It is **NOT a discharge**: it is a
*load-bearing* hypothesis — the genuine measure-theoretic Kraft / converse
coding content that the current stationary layer (no kernel / `compProd` /
disintegration structure) cannot derive. It is strictly more primitive than
`IsLZ78ConverseChainHyp` (per-realization eventual inequality vs.
`liminf`-level statement), and is a genuine `Prop` (type ≠ conclusion),
never `True`, never a `:= h` alias.

The pointwise route "`2^{−lz(x)} ≤ Pₙ{x}` via Shannon-code length" is
unsound (LZ78 beats the Shannon code pointwise) and is deliberately not
used; this hypothesis stands for the *averaged* converse coding theorem. -/
structure IsLZ78ConverseCodingLowerBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ) : Prop where
  /-- Eventually-in-`n`, a.s.-in-`ω`, the rate exceeds `blockLogAvg − slack`. -/
  lower : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg μ p n ω - slack n
        ≤ (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
  /-- The slack vanishes. -/
  slack_tendsto : Filter.Tendsto slack Filter.atTop (𝓝 (0 : ℝ))

end CodingLowerBound

/-! ## §2. Genuine `liminf` assembly -/

section LiminfAssembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Genuine `liminf` assembly**: the per-path coding lower bound, together
with the SMB a.s. convergence `blockLogAvg → entropyRate`, implies the
`blockLogAvg`-level converse chain hypothesis `IsLZ78ConverseChainHyp`.

Per a.s. `ω`, SMB gives `Tendsto (blockLogAvg) → entropyRate`, so
`liminf (blockLogAvg) = entropyRate`; the goal becomes
`entropyRate ≤ liminf (lz/n)`. For arbitrary `ε > 0`, eventually
`blockLogAvg n ω ≥ entropyRate − ε/2` (convergence) and `slack n ≤ ε/2`
(`slack → 0`), so with the coding lower bound `blockLogAvg − slack ≤ lz/n`,

```
entropyRate − ε ≤ blockLogAvg n ω − slack n ≤ (lz n x)/n   eventually,
```

hence `entropyRate − ε ≤ liminf (lz/n)` (`le_liminf_of_le`, using the
coboundedness of the rate), and `ε → 0` closes it (`le_of_forall_sub_le`).
The SMB convergence is the genuine source of the boundedness side
condition; the only non-genuine input is the load-bearing
`IsLZ78ConverseCodingLowerBound`. -/
theorem isLZ78ConverseChainHyp_of_codingLowerBound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ)
    (h_lb : IsLZ78ConverseCodingLowerBound μ p lz78EncodingLength slack)
    (h_block_tendsto : ∀ᵐ ω ∂μ,
        Filter.Tendsto (fun n => blockLogAvg μ p n ω) Filter.atTop
          (𝓝 (entropyRate μ p)))
    (h_lz_cobdd : ∀ᵐ ω ∂μ,
        Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
          (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))) :
    IsLZ78ConverseChainHyp μ p lz78EncodingLength := by
  rw [isLZ78ConverseChainHyp_def]
  filter_upwards [h_lb.lower, h_block_tendsto, h_lz_cobdd]
    with ω h_lower_ω h_block_ω h_lz_cobdd_ω
  -- Notation: `B n = blockLogAvg μ p n ω`, `L n = lz/n`, `H = entropyRate`.
  set B : ℕ → ℝ := fun n => blockLogAvg μ p n ω with hB
  set L : ℕ → ℝ :=
    fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ) with hL
  set H : ℝ := entropyRate μ p with hH
  -- `liminf B = H` from the SMB convergence.
  have h_liminf_B : Filter.liminf B Filter.atTop = H := h_block_ω.liminf_eq
  rw [h_liminf_B]
  -- Goal: `H ≤ liminf L`. Show `∀ ε > 0, H − ε ≤ liminf L`.
  refine le_of_forall_sub_le (fun ε hε => ?_)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- Eventually `slack n ≤ ε/2` from `slack → 0`.
  have h_slack_le : ∀ᶠ n in Filter.atTop, slack n ≤ ε / 2 := by
    have := h_lb.slack_tendsto.eventually (gt_mem_nhds hε2)
    filter_upwards [this] with n hn
    exact le_of_lt hn
  -- Eventually `H − ε/2 ≤ B n` from `B → H`.
  have h_block_ge : ∀ᶠ n in Filter.atTop, H - ε / 2 ≤ B n := by
    have := h_block_ω.eventually (lt_mem_nhds (show H - ε / 2 < H by linarith))
    filter_upwards [this] with n hn
    exact le_of_lt hn
  -- Eventually `H − ε ≤ L n`.
  have h_ev_le : ∀ᶠ n in Filter.atTop, H - ε ≤ L n := by
    filter_upwards [h_lower_ω, h_slack_le, h_block_ge] with n hn hslk hblk
    calc H - ε = (H - ε / 2) - ε / 2 := by ring
      _ ≤ B n - slack n := by linarith
      _ ≤ L n := hn
  -- `H − ε ≤ liminf L` (eventual lower bound + coboundedness of `L`).
  exact le_liminf_of_le h_lz_cobdd_ω h_ev_le

end LiminfAssembly

/-! ## §3. Distinct-code instance -/

section DistinctInstance

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Converse chain hypothesis for the distinct LZ78 code**, from the
named honest converse coding lower bound. Genuine assembly; the only
non-genuine input is the load-bearing `IsLZ78ConverseCodingLowerBound`. -/
theorem isLZ78ConverseChainHyp_distinct
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slack : ℕ → ℝ)
    (h_lb : IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess
              (@lz78DistinctEncodingLength α _ _ _) slack) :
    IsLZ78ConverseChainHyp μ p.toStationaryProcess
      (@lz78DistinctEncodingLength α _ _ _) := by
  refine isLZ78ConverseChainHyp_of_codingLowerBound μ p.toStationaryProcess
    (@lz78DistinctEncodingLength α _ _ _) slack h_lb
    (shannon_mcmillan_breiman μ p) ?_
  -- Coboundedness (≥) of the distinct rate from its a.s. upper boundedness
  -- (`IsBoundedUnder (· ≤ ·)` ⟹ `IsCoboundedUnder (· ≥ ·)`).
  filter_upwards [lz78DistinctEncodingLength_isBoundedUnder_le μ p] with ω hω
  exact hω.isCoboundedUnder_ge

end DistinctInstance

/-! ## §4. Converse-discharged distinct headline -/

section ConverseDischargedHeadline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A distinct headline with the converse internally discharged**.

Compared to `lz78_two_sided_optimality_distinct_bdd_free`
(`LZ78DistinctEncoding.lean`), which takes both `h_achiev` and
`h_converse`, this form **removes `h_converse`**: it is supplied
internally from the named honest converse coding lower bound
`IsLZ78ConverseCodingLowerBound` (the genuine `liminf` assembly is
`isLZ78ConverseChainHyp_distinct`). The remaining honest inputs are:

* `h_achiev` (the Ziv-side chain hypothesis, unchanged), and
* `h_lb` (the load-bearing per-path converse coding lower bound,
  *strictly more primitive* than the previous `liminf`-level
  `h_converse`).

This is honest progress on the converse: the `liminf`-level converse
deferral is replaced by a per-realization eventual inequality, and the
`liminf` plumbing is genuine. -/
theorem lz78_two_sided_optimality_distinct_converse_discharged
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slack : ℕ → ℝ)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  (@lz78DistinctEncodingLength α _ _ _))
    (h_lb : IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess
              (@lz78DistinctEncodingLength α _ _ _) slack) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_distinct_bdd_free μ p h_achiev
    (isLZ78ConverseChainHyp_distinct μ p slack h_lb)

end ConverseDischargedHeadline

end InformationTheory.Shannon
