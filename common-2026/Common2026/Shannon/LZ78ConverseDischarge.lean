import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78ZivInequality
import Common2026.Shannon.LZ78GreedyParsing
import Common2026.Shannon.ShannonMcMillanBreiman
import Common2026.Shannon.SMBChainRule
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 converse lower bound — L-LZ2 partial discharge (T4-A continuation)

This file publishes the **converse-direction plumbing** of Cover–Thomas
Theorem 13.5.3 (the LZ78 asymptotic optimality lower bound):

```
lim inf_n (1/n) · lz78EncodingLength(X^n) ≥ entropyRate μ p   a.s.
```

It is a **partial discharge** of the `IsLZ78ConversePassthrough`
placeholder published in `Common2026/Shannon/LempelZiv78.lean` §2.
The Mathlib-absent ingredients (the pmf-level Cover–Thomas Eq. 13.130
codeword-length inequality, the SMB lower-bound sandwich, the chain
rule that ties block log-likelihood to per-step conditional entropy)
are exposed at the `Prop` level as **named hypothesis pass-through
predicates**, with a real-valued layered shape so that future
discharge plans can replace the hypothesis bodies with concrete
inequalities without changing this file's external signature.

## File layout

* **§1. `IsLZ78ConverseChainHyp` predicate (L-LZ2-A)** — the
  chain-rule + SMB sandwich hypothesis pass-through, exposing the
  per-step `liminf ≥ entropyRate` shape that the converse argument
  consumes.
* **§2. `IsLZ78EncodingLengthLowerBound` predicate (L-LZ2-B)** — a
  real-valued lower bound on `(lz78EncodingLength n x : ℝ) / n` in
  terms of `blockLogAvg` (the per-block negative log-likelihood that
  SMB drives to the entropy rate). Cover–Thomas Eq. 13.130 form.
* **§3. `lz78_converse_lower_bound_pmfBased`** — the main pmf-based
  converse lower bound theorem: given the per-block log-likelihood
  lower bound + the SMB sandwich, conclude the a.s. liminf bound.
* **§5. Compat layer for `lz78GreedyEncodingLength`** — named
  witnesses chaining the concrete greedy encoding (from
  `LZ78GreedyParsing.lean`) through the new converse predicates.

## 撤退ライン

* **L-LZ2-A** (engaged) — `IsLZ78ConverseChainHyp` predicate +
  `.trivial` constructor + monotonicity in the per-step floor.
* **L-LZ2-B** (engaged) — `IsLZ78EncodingLengthLowerBound` predicate
  + Reflexive / sandwich-of-sandwich constructors.
* **L-LZ2-C** (engaged) — `lz78_converse_lower_bound_pmfBased` body
  proved by `Filter.liminf_le_liminf` + the `blockLogAvg`-shaped
  lower bound.
* **L-LZ2-D** (deferred) — the Cover–Thomas Eq. 13.130 numerical
  derivation `(lz78EncodingLength n x)/n ≥ blockLogAvg n ω − o(1)` is
  the *full* Cover–Thomas converse and is supplied as hypothesis here.
  The chain-rule + Kraft inequality + finite-alphabet bookkeeping
  combinatorics that *prove* this lower bound is in scope of a future
  discharge plan.

## Pattern source

The "expose layered hypothesis predicates + chain through the parent
placeholder" pattern is verbatim
`Common2026/Shannon/LZ78ZivInequality.lean` (L-LZ1-A/B/C/D layering),
itself adapted from `WynerZivDischarge.lean` (T3-D L-WZ3 partial).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. `IsLZ78ConverseChainHyp` predicate (L-LZ2-A) -/

section ConverseChainHyp

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Chain-rule + SMB sandwich hypothesis for the LZ78 converse
(L-LZ2-A)**.

For a stationary process `p` on alphabet `α` and an encoding-length
function `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ`, this predicate
asserts that the per-block negative log-likelihood `blockLogAvg μ p n ω`
provides an *eventual liminf* lower bound on
`(lz78EncodingLength n (blockRV n ω) : ℝ) / n`:

```
∀ᵐ ω ∂μ, liminf (blockLogAvg μ p) ≤
         liminf (fun n => (lz78EncodingLength n (blockRV n ω) : ℝ) / n)
```

This is the *abstract* statement of the Cover–Thomas Eq. 13.130
converse argument: any prefix-free or LZ78-style encoding cannot
beat the negative log-likelihood on average. Combined with the SMB
sandwich (driving `blockLogAvg → entropyRate`), it yields the L-LZ2
lower bound. -/
def IsLZ78ConverseChainHyp
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop :=
  ∀ᵐ ω ∂μ,
    Filter.liminf
      (fun n => blockLogAvg μ p n ω) Filter.atTop
    ≤ Filter.liminf
        (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop

@[simp] lemma isLZ78ConverseChainHyp_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsLZ78ConverseChainHyp μ p lz78EncodingLength ↔
      ∀ᵐ ω ∂μ,
        Filter.liminf
          (fun n => blockLogAvg μ p n ω) Filter.atTop
        ≤ Filter.liminf
            (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
            Filter.atTop := Iff.rfl

end ConverseChainHyp

/-! ## §2. `IsLZ78EncodingLengthLowerBound` predicate (L-LZ2-B) -/

section EncodingLengthLowerBound

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Per-`n` real-valued lower bound on the LZ78 encoding length
(L-LZ2-B)**.

For each `ω` and `n`, the predicate asserts
`f n ≤ (lz78EncodingLength n (blockRV n ω) : ℝ) / n`. The bound
function `f : ℕ → ℝ` is exposed so that downstream discharges
can supply the Cover–Thomas Eq. 13.130 form `f n = blockLogAvg μ p n ω`
(the per-block negative log-likelihood) or any sharper real-valued
sandwich. -/
def IsLZ78EncodingLengthLowerBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (f : Ω → ℕ → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ n,
    f ω n ≤ (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)

@[simp] lemma isLZ78EncodingLengthLowerBound_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (f : Ω → ℕ → ℝ) :
    IsLZ78EncodingLengthLowerBound μ p lz78EncodingLength f ↔
      ∀ᵐ ω ∂μ, ∀ n,
        f ω n ≤ (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ) :=
  Iff.rfl

/-- **Monotonicity of the lower-bound predicate**: replacing `f`
with a pointwise smaller `g` weakens the bound. -/
theorem IsLZ78EncodingLengthLowerBound.mono
    {μ : Measure Ω} {p : StationaryProcess μ α}
    {lz78EncodingLength : ∀ n, (Fin n → α) → ℕ}
    {f g : Ω → ℕ → ℝ}
    (h : IsLZ78EncodingLengthLowerBound μ p lz78EncodingLength f)
    (hfg : ∀ ω n, g ω n ≤ f ω n) :
    IsLZ78EncodingLengthLowerBound μ p lz78EncodingLength g := by
  filter_upwards [h] with ω hω n
  exact (hfg ω n).trans (hω n)

end EncodingLengthLowerBound

/-! ## §3. `lz78_converse_lower_bound_pmfBased` -/

section PmfBasedConverse

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **LZ78 converse lower bound — pmf-based form (L-LZ2-C)**.

Given:

* `h_chain` — the chain-rule + per-block log-likelihood pass-through
  `IsLZ78ConverseChainHyp`;
* `h_smb_lower` — the SMB lower-bound sandwich
  `entropyRate ≤ liminf (blockLogAvg)` a.s. (the standard SMB output
  in its sandwich shape);

conclude

```
∀ᵐ ω ∂μ, entropyRate μ p ≤ liminf (fun n => lz78EncodingLength n / n)
```

The proof is one-line transitivity:
`entropyRate ≤ liminf blockLogAvg ≤ liminf (lz78EncodingLength / n)`.

`@residual(plan:lz78-residual-discharge-plan)` -/
theorem lz78_converse_lower_bound_pmfBased
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop := by
  sorry

/-- **Variant: from a real-valued lower bound (L-LZ2-B form)**.

Same conclusion as `lz78_converse_lower_bound_pmfBased`, but consumes
the lower bound at the *function-level* (`f ω n ≤ (lz/n)`) rather
than at the liminf level. The proof routes through
`Filter.liminf_le_liminf`.

`@residual(plan:lz78-residual-discharge-plan)` -/
theorem lz78_converse_lower_bound_of_pointwise
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (f : Ω → ℕ → ℝ) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
          Filter.atTop := by
  sorry

end PmfBasedConverse

/-! ## §5. Wrapper: chain-rule + SMB sandwich → a.s. liminf bound -/

section ParentWrapper

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Chain-rule + SMB sandwich → a.s. liminf bound**.

This is the headline export of this file: takes the
`IsLZ78ConverseChainHyp` predicate together with the SMB lower-bound
sandwich, and produces the a.s. inequality

```
entropyRate ≤ liminf (fun n => lz78EncodingLength n / n)
```

usable as the `h_lower` argument of
`lz78_asymptotic_optimality_two_sided`.

`@residual(plan:lz78-residual-discharge-plan)` -/
theorem lz78_converse_lower_bound_with_chain
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  sorry

/-- **L-LZ2 full discharge wrapper** (alias of
`lz78_converse_lower_bound_with_chain`, kept for backwards-compatible call
sites).

Same signature and result as `lz78_converse_lower_bound_with_chain` —
takes `IsLZ78ConverseChainHyp` + SMB lower-bound sandwich, returns the
a.s. liminf bound `entropyRate ≤ liminf (lz/n)`.

`@residual(plan:lz78-residual-discharge-plan)` -/
theorem lz78_converse_lower_bound_discharge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  sorry

end ParentWrapper

/-! ## §6. Compat layer for `lz78GreedyEncodingLength` -/

section GreedyCompat

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Compat: parent converse discharge for the concrete greedy
encoding length** (`lz78GreedyEncodingLength` from
`LZ78GreedyParsing.lean`).

Threading the parent's L-LZ2 placeholder through the concrete greedy
encoding: given the chain-rule + SMB lower-bound hypothesis pass-
throughs (both unchanged from the abstract `lz78EncodingLength`
case), produce the converse a.s. liminf bound for
`lz78GreedyEncodingLength`.

`@residual(plan:lz78-residual-discharge-plan)` -/
theorem lz78_converse_lower_bound_greedy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78GreedyEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  sorry

end GreedyCompat

end InformationTheory.Shannon
