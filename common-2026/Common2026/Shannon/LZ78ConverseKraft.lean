import Common2026.Shannon.LZ78ConverseDischarge
import Common2026.Shannon.LZ78DistinctEncoding
import Common2026.Shannon.LZ78FinalGlue
import Common2026.Shannon.LZ78SMBSandwich
import Common2026.Shannon.LZ78ZivEntropyBridge
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 converse base-2 liminf assembly (T4-A, L-LZ2)

This file assembles the **base-2 (bit) converse liminf lower bound**
`lz78_converse_le_liminf₂` for the *distinct* LZ78 code from the named
per-path honest converse coding lower bound, plus the base-2 SMB
convergence `shannon_mcmillan_breiman₂`. It targets the genuine
Cover–Thomas Theorem 13.5.3 limit `entropyRate₂ = entropyRate / log 2`
(entropy in **bits** per symbol; see the base-2 unit note in
`LZ78AchievabilityLimsup.lean`).

The converse asserts the a.s. liminf lower bound

```
∀ᵐ ω ∂μ, entropyRate₂ μ p ≤ liminf (fun n => lz/n)
```

i.e. the bit-based LZ78 per-symbol rate cannot asymptotically beat the
per-block negative log-likelihood in bits (Cover–Thomas Eq. 13.130).

## Honesty status (read this before reusing)

The genuine content of the converse is the **Cover–Thomas Eq. 13.130
coding lower bound** `(lz n x)/n ≥ blockLogAvg₂ μ p n ω − o(1)` — that any
prefix-free / uniquely-decodable code cannot beat the negative
log-likelihood (in bits) *on average*. This is **not** a pointwise fact:
per a fixed realization `x`, an LZ78 codeword can be *shorter* than
`−log₂ Pₙ{x}` (that is exactly the universality of LZ78). It is the
expectation-level Kraft / converse-coding theorem, lifted to an a.s.
eventual lower bound. The pointwise route "`2^{−lz(x)} ≤ Pₙ{x}` via
Shannon-code length" is mathematically unsound and is **not** used here.

We therefore expose the Eq. 13.130 lower bound as a single, isolated,
**named honest hypothesis** `IsLZ78ConverseCodingLowerBound` (bit-based,
against `blockLogAvg₂`): a per-realization, per-`n` eventual inequality
`blockLogAvg₂ n ω − slack n ≤ lz/n` with `slack n → 0`. From it the base-2
liminf lower bound is derived **genuinely** here (`liminf` monotonicity +
base-2 SMB + slack absorption).

The hypothesis is a genuine `Prop` (type ≠ conclusion), never `True`,
never a `:= h` defeq alias, and its docstring marks it load-bearing.

## File layout

* **§1.** `IsLZ78ConverseCodingLowerBound` — the named honest per-path
  bit-based Eq. 13.130 lower bound (load-bearing).
* **§1b.** `shannon_mcmillan_breiman₂` — base-2 SMB convergence (unit
  conversion of `shannon_mcmillan_breiman`).
* **§2.** `lz78_converse_le_liminf₂` — genuine base-2 `liminf` assembly:
  the coding lower bound + base-2 SMB give `entropyRate₂ ≤ liminf (lz/n)`.
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
used; this hypothesis stands for the *averaged* converse coding theorem.

**Base-2 (bit) unit**: the LZ78 code length is in **bits**, so the converse
coding bound is against the **bit-based** per-block estimator
`blockLogAvg₂ μ p n ω = blockLogAvg μ p n ω / log 2` (the entropy in bits),
matching the corrected Cover–Thomas Theorem 13.5.3 statement. The previous
coefficient-1 form against `blockLogAvg` (nats) was a unit bug. -/
structure IsLZ78ConverseCodingLowerBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ) : Prop where
  /-- Eventually-in-`n`, a.s.-in-`ω`, the bit-rate exceeds `blockLogAvg₂ − slack`. -/
  lower : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg₂ μ p n ω - slack n
        ≤ (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
  /-- The slack vanishes. -/
  slack_tendsto : Filter.Tendsto slack Filter.atTop (𝓝 (0 : ℝ))

end CodingLowerBound

/-! ## §1b. Base-2 SMB convergence -/

section SMB2

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Base-2 SMB convergence**: dividing the genuine SMB a.s. convergence
`blockLogAvg → entropyRate` by the constant `Real.log 2 > 0` gives the
bit-based convergence `blockLogAvg₂ → entropyRate₂`. This is the unit
conversion of `shannon_mcmillan_breiman`, not new content. -/
theorem shannon_mcmillan_breiman₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  filter_upwards [shannon_mcmillan_breiman μ p] with ω hω
  simpa only [blockLogAvg₂, entropyRate₂] using hω.div_const (Real.log 2)

end SMB2

/-! ## §2. Genuine base-2 `liminf` assembly -/

section LiminfAssembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Genuine base-2 `liminf` assembly**: the per-path (bit-based) coding
lower bound, together with the base-2 SMB a.s. convergence
`blockLogAvg₂ → entropyRate₂`, gives the a.s. liminf lower bound
`entropyRate₂ ≤ liminf (lz/n)`.

Per a.s. `ω`, the base-2 SMB gives `blockLogAvg₂ → entropyRate₂`, so
`liminf blockLogAvg₂ = entropyRate₂`. For arbitrary `ε > 0`, eventually
`blockLogAvg₂ n ω ≥ entropyRate₂ − ε/2` and `slack n ≤ ε/2`, so with the
coding lower bound `blockLogAvg₂ − slack ≤ lz/n`,

```
entropyRate₂ − ε ≤ blockLogAvg₂ n ω − slack n ≤ (lz n x)/n   eventually,
```

hence `entropyRate₂ − ε ≤ liminf (lz/n)` (`le_liminf_of_le`, coboundedness
of the rate), and `ε → 0` closes it. The only non-genuine input is the
load-bearing `IsLZ78ConverseCodingLowerBound`.

`@audit:suspect(lz78-moonshot-plan)` -/
theorem lz78_converse_le_liminf₂
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ)
    (h_lb : IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess
              lz78EncodingLength slack)
    (h_lz_cobdd : ∀ᵐ ω ∂μ,
        Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
          (fun n => (lz78EncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      entropyRate₂ μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => (lz78EncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
            Filter.atTop := by
  filter_upwards [h_lb.lower, shannon_mcmillan_breiman₂ μ p, h_lz_cobdd]
    with ω h_lower_ω h_block_ω h_lz_cobdd_ω
  set B : ℕ → ℝ := fun n => blockLogAvg₂ μ p.toStationaryProcess n ω with hB
  set L : ℕ → ℝ :=
    fun n => (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
      / (n : ℝ) with hL
  set H : ℝ := entropyRate₂ μ p.toStationaryProcess with hH
  -- Goal: `H ≤ liminf L`. Show `∀ ε > 0, H − ε ≤ liminf L`.
  refine le_of_forall_sub_le (fun ε hε => ?_)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have h_slack_le : ∀ᶠ n in Filter.atTop, slack n ≤ ε / 2 := by
    have := h_lb.slack_tendsto.eventually (gt_mem_nhds hε2)
    filter_upwards [this] with n hn
    exact le_of_lt hn
  have h_block_ge : ∀ᶠ n in Filter.atTop, H - ε / 2 ≤ B n := by
    have := h_block_ω.eventually (lt_mem_nhds (show H - ε / 2 < H by linarith))
    filter_upwards [this] with n hn
    exact le_of_lt hn
  have h_ev_le : ∀ᶠ n in Filter.atTop, H - ε ≤ L n := by
    filter_upwards [h_lower_ω, h_slack_le, h_block_ge] with n hn hslk hblk
    calc H - ε = (H - ε / 2) - ε / 2 := by ring
      _ ≤ B n - slack n := by linarith
      _ ≤ L n := hn
  exact le_liminf_of_le h_lz_cobdd_ω h_ev_le

end LiminfAssembly

end InformationTheory.Shannon
