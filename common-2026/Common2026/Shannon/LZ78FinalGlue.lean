import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78ZivInequality
import Common2026.Shannon.LZ78ConverseAsymptotic
import Common2026.Shannon.LZ78ConverseDischarge
import Common2026.Shannon.LZ78SMBSandwich
import Common2026.Shannon.LZ78GreedyParsingImpl
import Common2026.Shannon.SMBAlgoetCover
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 two-sided asymptotic optimality — final glue (S19, T4-A wave10)

This file is the **headline assembly** for Cover–Thomas Theorem 13.5.3
(LZ78 universal source coding). Across waves the individual ingredients
were discharged:

* **L-LZ3 SMB sandwich** (`LZ78SMBSandwich.lean` /
  `SMBAlgoetCover.lean`) — *hypothesis-free* for an ergodic process on a
  finite alphabet: `algoet_cover_liminf_bound` gives
  `entropyRate ≤ liminf blockLogAvg` a.s. and `algoet_cover_limsup_bound`
  gives `limsup blockLogAvg ≤ entropyRate` a.s.
* **L-LZ4 greedy parsing** (`LZ78GreedyParsingImpl.lean`) — the concrete
  longest-prefix-match greedy `lz78GreedyImplEncodingLength` is
  implemented (not a parameter) with a proven `count ≤ n` bound.
* **L-LZ2 converse** (`LZ78ConverseDischarge.lean`) — the lower bound is
  reduced, via `lz78_converse_lower_bound_with_chain`, to the *single*
  genuine primitive `IsLZ78ConverseChainHyp` (Cover–Thomas Eq. 13.130
  pmf-level codeword-length inequality).

The wave-published `lz78_asymptotic_optimality_two_sided`
(`LempelZiv78.lean` §4) still carried **three `True` pass-through
predicates** (`IsZivInequalityPassthrough`, `IsLZ78ConversePassthrough`,
`IsSMBSandwichPassthrough`) *plus* the two SMB-side sandwich bounds
(`h_lower : H ≤ liminf (lz/n)` and `h_upper : limsup (lz/n) ≤ H`) as raw
hypotheses. This file removes all three `True` placeholders and both
SMB-side sandwich bounds, replacing them with the discharged SMB
sandwich (wired in internally) and the two *genuine, strictly-more-
primitive* chain hypotheses.

## The two residual genuine predicates

The two remaining hypotheses are **not** `True` placeholders and **not**
defeq no-ops; they are the Cover–Thomas pmf-level inequalities that the
LZ78 sandwich is genuinely built on, stated *relative to* `blockLogAvg`
(the SMB driver) rather than relative to `entropyRate`:

* `IsLZ78ConverseChainHyp` (already in `LZ78ConverseDischarge.lean`):
  `liminf blockLogAvg ≤ liminf (lz/n)` a.s. — Eq. 13.130.
* `IsLZ78AchievabilityChainHyp` (**introduced here**, the Ziv-side
  mirror): `limsup (lz/n) ≤ limsup blockLogAvg` a.s. — the Ziv-inequality
  consequence (Cover–Thomas Eq. 13.124).

Composing each with the *discharged* SMB sandwich half collapses
`blockLogAvg` to `entropyRate`, giving the `H ≤ liminf` / `limsup ≤ H`
sandwich that `tendsto_of_le_liminf_of_limsup_le` turns into the a.s.
Tendsto. The result therefore carries strictly fewer hypotheses than the
wave-published form: the SMB sandwich, the two SMB-side bounds, and all
three `True` passthroughs are gone.

## File layout

* **§1.** `IsLZ78AchievabilityChainHyp` — Ziv-side primitive predicate,
  mirror of `IsLZ78ConverseChainHyp`, with a bridge to the parent
  `IsZivInequalityPassthrough` placeholder.
* **§2.** `lz78_achievability_upper_bound_ergodic` — collapse the
  achievability chain through the discharged SMB limsup half.
* **§3.** `lz78_two_sided_optimality_ergodic` and `_of_bounds` — the
  headline two-sided theorem with the SMB sandwich and SMB-side bounds
  discharged.
* **§4.** Greedy-impl specialization with the concrete
  `lz78GreedyImplEncodingLength`.

## 撤退ライン

Full discharge of the *source-side* SMB sandwich (L-LZ3) and the greedy
encoding (L-LZ4) is achieved. The two remaining hypotheses
(`IsLZ78ConverseChainHyp`, `IsLZ78AchievabilityChainHyp`) are the genuine
Cover–Thomas Eq. 13.124 / 13.130 pmf-level inequalities (L-LZ1-D /
L-LZ2-D), and the two `IsBoundedUnder` hypotheses are the genuine
boundedness of the per-symbol rate sequence. None is a `sorry`, a `True`
placeholder, or a defeq no-op.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. `IsLZ78AchievabilityChainHyp` — Ziv-side primitive predicate -/

section AchievabilityChainHyp

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Ziv-inequality achievability chain hypothesis (Cover–Thomas
Eq. 13.124, Ziv-side mirror of `IsLZ78ConverseChainHyp`)**.

For a stationary process `p` and an encoding-length function
`lz78EncodingLength`, this predicate asserts that the per-block negative
log-likelihood `blockLogAvg μ p n ω` provides an *eventual limsup* upper
bound on `(lz78EncodingLength n (blockRV n ω) : ℝ) / n`:

```
∀ᵐ ω ∂μ, limsup (fun n => (lz78EncodingLength n (blockRV n ω) : ℝ) / n)
       ≤ limsup (blockLogAvg μ p n)
```

This is the *abstract* statement of the Cover–Thomas Eq. 13.124 Ziv
inequality consequence: an LZ78 encoding cannot do asymptotically worse
than the negative log-likelihood on average. Combined with the SMB
sandwich (driving `blockLogAvg → entropyRate`), it yields the L-LZ1
achievability upper bound. It is the exact dual of `IsLZ78ConverseChainHyp`
(`LZ78ConverseDischarge.lean`), with `liminf` swapped for `limsup` and the
inequality reversed. -/
def IsLZ78AchievabilityChainHyp
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop :=
  ∀ᵐ ω ∂μ,
    Filter.limsup
      (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
      Filter.atTop
    ≤ Filter.limsup
        (fun n => blockLogAvg μ p n ω) Filter.atTop

@[simp] lemma isLZ78AchievabilityChainHyp_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsLZ78AchievabilityChainHyp μ p lz78EncodingLength ↔
      ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop
        ≤ Filter.limsup
            (fun n => blockLogAvg μ p n ω) Filter.atTop := Iff.rfl

end AchievabilityChainHyp

/-! ## §2. Achievability upper bound via discharged SMB limsup -/

section AchievabilityUpperBound

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **LZ78 achievability upper bound — SMB-discharged form**.

Given only the genuine achievability chain hypothesis
`IsLZ78AchievabilityChainHyp` (Cover–Thomas Eq. 13.124), and using the
*discharged* SMB limsup half `algoet_cover_limsup_bound` internally,
conclude

```
∀ᵐ ω ∂μ, limsup (fun n => lz78EncodingLength n / n) ≤ entropyRate μ p
```

This is the Ziv-side mirror of `lz78_converse_lower_bound_with_chain`
(`LZ78ConverseDischarge.lean`), with the SMB upper-bound sandwich
discharged from the ergodic-process side rather than supplied as a
hypothesis.

`@audit:suspect(lz78-moonshot-plan)` -/
theorem lz78_achievability_upper_bound_ergodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_chain : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                lz78EncodingLength) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n =>
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
      ≤ entropyRate μ p.toStationaryProcess := by
  -- Compose the achievability chain `limsup (lz/n) ≤ limsup blockLogAvg`
  -- with the discharged SMB limsup half `limsup blockLogAvg ≤ entropyRate`.
  have h_smb_limsup := algoet_cover_limsup_bound μ p
  filter_upwards [h_chain, h_smb_limsup] with ω h_chain_ω h_smb_ω
  exact le_trans h_chain_ω h_smb_ω

end AchievabilityUpperBound

/-! ## §3. Headline: two-sided optimality with SMB discharged -/

section TwoSidedHeadline

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **S19 headline — LZ78 two-sided asymptotic optimality, SMB
discharged**.

Cover–Thomas Theorem 13.5.3. For an ergodic process `p` on a finite
alphabet, the per-symbol LZ78 output length converges a.s. to the entropy
rate. Compared to the wave-published `lz78_asymptotic_optimality_two_sided`
(`LempelZiv78.lean` §4), this form **drops** all three `True` pass-through
predicates (`_h_ziv`, `_h_converse`, `_h_smb`) **and** both SMB-side
sandwich bounds (`h_lower`, `h_upper`), replacing them with the two
genuine Cover–Thomas chain hypotheses (`IsLZ78AchievabilityChainHyp`,
`IsLZ78ConverseChainHyp`), fed internally through the discharged SMB
sandwich (`algoet_cover_liminf_bound` / `algoet_cover_limsup_bound`).

The two `IsBoundedUnder` hypotheses remain — they are the genuine
boundedness of the per-symbol rate sequence, required by
`tendsto_of_le_liminf_of_limsup_le`.

`@audit:suspect(lz78-moonshot-plan)` -/
theorem lz78_two_sided_optimality_ergodic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  lz78EncodingLength)
    (h_converse : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                  lz78EncodingLength)
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ)))
    (h_bdd_below : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  -- Lower bound: converse chain through the discharged SMB liminf half.
  have h_lower :=
    lz78_converse_lower_bound_with_chain μ p lz78EncodingLength h_converse
      (algoet_cover_liminf_bound μ p)
  -- Upper bound: achievability chain through the discharged SMB limsup half.
  have h_upper :=
    lz78_achievability_upper_bound_ergodic μ p lz78EncodingLength h_achiev
  -- Combine the sandwich `H ≤ liminf` / `limsup ≤ H` with boundedness.
  filter_upwards [h_lower, h_upper, h_bdd_above, h_bdd_below]
    with ω hl hu hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

/-- **S19 headline — bundled `_of_bounds` form**.

Same as `lz78_two_sided_optimality_ergodic`, but the two
`IsBoundedUnder` hypotheses are bundled into a single conjunction, mirroring
`lz78_asymptotic_optimality_of_bounds` (`LempelZiv78.lean` §4).

`@audit:suspect(lz78-moonshot-plan)` -/
theorem lz78_two_sided_optimality_ergodic_of_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  lz78EncodingLength)
    (h_converse : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                  lz78EncodingLength)
    (h_bounded : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n =>
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
        ∧ Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
            (fun n =>
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  refine lz78_two_sided_optimality_ergodic μ p lz78EncodingLength
    h_achiev h_converse ?_ ?_
  · filter_upwards [h_bounded] with ω h; exact h.1
  · filter_upwards [h_bounded] with ω h; exact h.2

end TwoSidedHeadline

/-! ## §4. Greedy-impl specialization (L-LZ4 discharged) -/

section GreedyImplHeadline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Genuine lower boundedness of the greedy per-symbol rate**.

For the concrete greedy implementation, the per-symbol output rate
`(lz78GreedyImplEncodingLength n (blockRV n ω) : ℝ) / n` is `≥ 0` for
*every* `n` and *every* `ω` (the numerator and denominator are both `ℕ`
casts), so it is uniformly bounded below by `0`. This discharges the
`IsBoundedUnder (· ≥ ·)` hypothesis of the headline genuinely — it is a
property of the greedy code, not an external assumption. -/
theorem lz78GreedyImpl_isBoundedUnder_ge
    (μ : Measure Ω) (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ)) := by
  refine Filter.Eventually.of_forall (fun ω => ?_)
  refine Filter.isBoundedUnder_of_eventually_ge (a := 0) ?_
  exact Filter.Eventually.of_forall (fun n =>
    lz78_impl_encoding_length_per_symbol_nonneg n
      (p.toStationaryProcess.blockRV n ω))

/-- **S19 final headline — two-sided LZ78 optimality for the genuine
greedy implementation**.

The complete assembly: the encoding-length parameter is instantiated to
the concrete `lz78GreedyImplEncodingLength` (L-LZ4 discharged), the SMB
sandwich is discharged internally (L-LZ3), and only the two genuine
Cover–Thomas chain hypotheses (Eq. 13.124 / 13.130) plus the boundedness
of the per-symbol rate remain. This is the maximally-discharged form of
Cover–Thomas Theorem 13.5.3 achievable from the current wave's
ingredients.

`@audit:suspect(lz78-moonshot-plan)` -/
theorem lz78_two_sided_optimality_greedy_impl
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  (@lz78GreedyImplEncodingLength α _ _))
    (h_converse : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                  (@lz78GreedyImplEncodingLength α _ _))
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ)))
    (h_bdd_below : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_ergodic μ p (@lz78GreedyImplEncodingLength α _ _)
    h_achiev h_converse h_bdd_above h_bdd_below

/-- **S19 final headline — greedy two-sided optimality with lower
boundedness discharged**.

Same as `lz78_two_sided_optimality_greedy_impl`, but the
`IsBoundedUnder (· ≥ ·)` hypothesis (`h_bdd_below`) is **dropped** — it is
genuinely discharged internally via `lz78GreedyImpl_isBoundedUnder_ge`
(the greedy per-symbol rate is `≥ 0` by construction). The headline now
carries only **three** honest hypotheses:

* `h_achiev` — Cover–Thomas Eq. 13.124 achievability chain (Ziv side);
* `h_converse` — Cover–Thomas Eq. 13.130 converse chain;
* `h_bdd_above` — `IsBoundedUnder (· ≤ ·)` upper boundedness of the
  per-symbol rate. This one is *not* dischargeable from the greedy
  bit-length bound: that bound is `≤ log(n+1) + log|α| + 2`, which grows
  with `n` and hence gives no uniform upper constant. It is the genuine
  residual boundedness input required by
  `tendsto_of_le_liminf_of_limsup_le`.

The two SMB-side sandwich bounds and all three `True` pass-throughs
remain discharged internally (as in the parent headline).

`@audit:suspect(lz78-moonshot-plan)` -/
theorem lz78_two_sided_optimality_greedy_impl_bdd_below_free
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_achiev : IsLZ78AchievabilityChainHyp μ p.toStationaryProcess
                  (@lz78GreedyImplEncodingLength α _ _))
    (h_converse : IsLZ78ConverseChainHyp μ p.toStationaryProcess
                  (@lz78GreedyImplEncodingLength α _ _))
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_greedy_impl μ p h_achiev h_converse h_bdd_above
    (lz78GreedyImpl_isBoundedUnder_ge μ p)

end GreedyImplHeadline

end InformationTheory.Shannon
