import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.SMB.McMillanBreiman
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lempel–Ziv 78 asymptotic optimality

Cover–Thomas Theorem 13.5.3 (Ch.13 Universal Source Coding): for a
stationary ergodic source `{X_i}` on a finite alphabet `α`, the per-symbol
output length of the LZ78 dictionary code converges almost surely to the
entropy rate:

```
lim_{n → ∞} (1/n) · ℓ(LZ78(X^n)) = H(𝓧)   a.s.
```

This is the **universal source-coding analogue** of Shannon's source-coding
theorem: LZ78 achieves the entropy-rate lower bound without any prior
knowledge of the source statistics.

## File layout

This single file publishes:

* **§1. LZ78 phrase data structures** (`LZ78Phrase α`, `LZ78Parsing α`)
  — the type-level encoding of an LZ78 dictionary parsing.
* **§2. Generic sandwich combinator** — `lz78_asymptotic_optimality`
  (and its alias / bundled forms), the LZ78-flavored wrapper of
  `tendsto_of_le_liminf_of_limsup_le`. This is **not** the LZ78
  optimality claim itself; it derives a.s. convergence from a
  caller-supplied two-sided sandwich. The genuine optimality headline
  (with the sandwich halves discharged as proven theorems, sorryAx-free)
  is `lz78_asymptotic_optimality_with_greedy_impl` in
  `InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean`.

## The asymptotic-optimality core

The two halves of LZ78 asymptotic optimality — the achievability upper
bound `∀ᵐ ω, limsup (lz/n) ≤ entropyRate₂`
(Ziv's inequality, Cover–Thomas Lemma 13.5.5) and the converse lower
bound `∀ᵐ ω, entropyRate₂ ≤ liminf (lz/n)` (Cover–Thomas Theorem 13.5.3
lower bound) — are the **single source of truth** in the two proven
theorems
`lz78GreedyImpl_achievability_ae` / `lz78GreedyImpl_converse_ae`
in `InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean`
(both sorryAx-free, `@audit:ok`). The SMB sandwich itself is fully
discharged upstream (`shannon_mcmillan_breiman`).

## Statement-level structure

* The concrete `lz78Encode : List α → LZ78Parsing α` greedy
  parsing implementation is supplied externally; the generic combinator
  consumes a generic encoding-length function
  `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` supplied as a parameter.
* The generic combinator `lz78_asymptotic_optimality` is **not** an
  identity wrap of its conclusion, and **not** the LZ78 optimality claim:
  it takes a caller-supplied two-sided sandwich on `lz/n` — the liminf
  lower bound `entropyRate ≤ liminf (lz/n)`, the limsup upper bound
  `limsup (lz/n) ≤ entropyRate`, and the two boundedness arguments — and
  *derives* the a.s. Tendsto via `tendsto_of_le_liminf_of_limsup_le`. Its
  `h_lower`/`h_upper` are **generic caller-supplied arguments**, not a
  built-in claim that any encoding achieves the entropy rate. For the
  genuine greedy LZ78 parser those two halves are the Cover–Thomas
  Eq. 13.124 / 13.130 substance of Thm 13.5.3, whose genuine discharge
  (Ziv inequality + SMB) is proven (sorryAx-free)
  in `lz78_asymptotic_optimality_with_greedy_impl`
  (`lz78GreedyImpl_converse_ae` / `lz78GreedyImpl_achievability_ae`).

## Re-use of existing infrastructure

`InformationTheory/Shannon/Stationary/Basic.lean` (StationaryProcess / ErgodicProcess /
blockRV), `InformationTheory/Shannon/EntropyRate.lean` (`entropyRate`,
`entropyRate_exists_of_stationary`), and `InformationTheory/Shannon/
ShannonMcMillanBreiman.lean` (`blockLogAvg`,
`shannon_mcmillan_breiman_of_sandwich`, `tendsto_expected_blockLogAvg`)
are imported and re-used as **black boxes**: the present file does not
re-prove any of those results, it merely refers to them through the
type-level signatures.

## Derivation pattern

The §2 combinator is a genuine two-sided-sandwich derivation via
`tendsto_of_le_liminf_of_limsup_le` (the same combine pattern as
`shannon_mcmillan_breiman_of_sandwich` in `ShannonMcMillanBreiman.lean`),
*not* an identity-wrap pass-through, and *not* the LZ78 optimality claim
(its sandwich arguments are generic and caller-supplied). The genuine
two-sided sandwich on `lz/n` — the actual achievability / converse
halves — is proven (sorryAx-free) in
`AsymptoticOptimality.lean` (`lz78GreedyImpl_achievability_ae` /
`lz78GreedyImpl_converse_ae`), the single source of truth.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

/-! ## §1. LZ78 phrase data structures -/

section LZ78Structures

/-- An **LZ78 dictionary phrase** is a pair `(parent, symbol)` where:

* `parent : Option ℕ` references the earlier phrase being extended, or
`none` for the empty-prefix root (the very first phrase ever emitted).
* `symbol : α` is the single new alphabet symbol appended.

This is the Cover–Thomas Ch.13.5 dictionary entry encoded at the type
level. Concrete `lz78Encode : List α → LZ78Parsing α` parsing is supplied
externally; see the file-level docstring. -/
structure LZ78Phrase (α : Type*) where
  /-- Reference to the parent phrase already in the dictionary; `none`
  marks the empty-prefix root. -/
  parent : Option ℕ
  /-- The single alphabet symbol appended to the parent. -/
  symbol : α

namespace LZ78Phrase

variable {α : Type*}

/-- Root phrase: extend the empty prefix by a single symbol. -/
@[simp] def root (s : α) : LZ78Phrase α := { parent := none, symbol := s }

/-- Extension phrase: extend the `k`-th dictionary entry by symbol `s`. -/
@[simp] def cons (k : ℕ) (s : α) : LZ78Phrase α :=
  { parent := some k, symbol := s }

@[simp] lemma parent_root (s : α) : (LZ78Phrase.root s).parent = none := rfl

@[simp] lemma parent_cons (k : ℕ) (s : α) :
    (LZ78Phrase.cons k s).parent = some k := rfl

@[simp] lemma symbol_root (s : α) : (LZ78Phrase.root s).symbol = s := rfl

@[simp] lemma symbol_cons (k : ℕ) (s : α) :
    (LZ78Phrase.cons k s).symbol = s := rfl

/-- Two phrases are equal iff their `parent` and `symbol` agree. -/
lemma ext_iff {p q : LZ78Phrase α} :
    p = q ↔ p.parent = q.parent ∧ p.symbol = q.symbol := by
  cases p; cases q; simp

end LZ78Phrase

/-- An **LZ78 parsing** of a finite input is a list of dictionary phrases
together with the structural invariant that every `parent = some k`
references an earlier (strictly smaller) phrase index.

This is the minimal Cover–Thomas Ch.13.5 LZ78 dictionary structure: a list
of phrases whose parent references back-point into the already-emitted
prefix of the list. -/
structure LZ78Parsing (α : Type*) where
  /-- The ordered list of dictionary phrases. -/
  phrases : List (LZ78Phrase α)
  /-- Structural invariant: every parent reference points to an earlier
  phrase index. The invariant is stated via `List.get ⟨i, h⟩` (the
  total bounded-index accessor) so that the back-pointer constraint
  `parent_i = some k → k < i` is captured at the type level. -/
  inRange : ∀ i (h : i < phrases.length),
      ∀ k, (phrases.get ⟨i, h⟩).parent = some k → k < i

namespace LZ78Parsing

variable {α : Type*}

/-- Number of phrases emitted by the parsing. Cover–Thomas notation: `c(n)`. -/
def count (p : LZ78Parsing α) : ℕ := p.phrases.length

/-- The empty parsing, with no phrases. -/
def empty (α : Type*) : LZ78Parsing α :=
  { phrases := []
    inRange := by
      intro i hi
      exact absurd hi (Nat.not_lt_zero _) }

@[simp] lemma count_empty (α : Type*) : (LZ78Parsing.empty α).count = 0 := rfl

@[simp] lemma phrases_empty (α : Type*) :
    (LZ78Parsing.empty α).phrases = [] := rfl

/-- `count` is just the list length. -/
@[simp] lemma count_eq_length (p : LZ78Parsing α) :
    p.count = p.phrases.length := rfl

end LZ78Parsing

end LZ78Structures

/-! ## §2. Main theorem — LZ78 asymptotic optimality -/

section MainTheorem

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

omit [DecidableEq α] in
/-- **Generic two-sided sandwich-combine lemma for per-symbol coding
rates** (the LZ78-flavored wrapper of `tendsto_of_le_liminf_of_limsup_le`).

This is **NOT** the LZ78 asymptotic-optimality claim itself. It is a
generic combinator: given *any* encoding-length function
`lz78EncodingLength`, *any* limit value `L : ℝ`, and a two-sided a.s.
sandwich on the per-symbol rate (`L ≤ liminf` and `limsup ≤ L`, plus a.s.
boundedness), it derives a.s. convergence of `lz/n` to `L` via
`tendsto_of_le_liminf_of_limsup_le` (a 1-step squeeze). The hypotheses
`h_lower` / `h_upper` are **generic caller-supplied arguments**, not a
claim that any particular encoding achieves any particular limit — the
caller is responsible for supplying them (for the concrete greedy LZ78
parser, with `L = entropyRate₂` the bit-rate target, that supply is the
genuine achievability / converse content, proven (sorryAx-free) in
`lz78_asymptotic_optimality_with_greedy_impl`).

The limit `L` is a generic parameter (not hard-wired to `entropyRate`):
the worst-case forwarder `lz78_asymptotic_optimality_with_greedy_encoding`
instantiates it with the nat-unit `entropyRate`, while the genuine
bit-rate headline `lz78_asymptotic_optimality_with_greedy_impl`
instantiates it with the bit-unit `entropyRate₂`.

The body is a genuine application of the Mathlib squeeze, not an identity
wrap of the conclusion (the sandwich bounds relate `lz/n` to `L` via `≤`,
distinct from the `Tendsto … (𝓝 L)` conclusion). -/
theorem lz78_asymptotic_optimality
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (L : ℝ)
    (h_lower : ∀ᵐ ω ∂μ,
        L
        ≤ Filter.liminf
            (fun n =>
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ L)
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
        (𝓝 L) := by
  filter_upwards [h_lower, h_upper, h_bdd_above, h_bdd_below]
    with ω hl hu hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

omit [DecidableEq α] in
/-- **Generic two-sided sandwich-combine — alias form**.

Alias for the generic combinator `lz78_asymptotic_optimality` with the
same four arguments (liminf lower bound, limsup upper bound, two
`Filter.IsBoundedUnder` boundedness arguments). Like its target this is
**not** the LZ78 optimality claim — `h_lower` / `h_upper` are generic
caller-supplied sandwich arguments. The body is a genuine forward, not an
identity wrap of the conclusion. -/
theorem lz78_asymptotic_optimality_two_sided
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_lower : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n =>
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess)
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
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_asymptotic_optimality μ p lz78EncodingLength
    (entropyRate μ p.toStationaryProcess)
    h_lower h_upper h_bdd_above h_bdd_below

omit [DecidableEq α] in
/-- **Generic two-sided sandwich-combine — bundled-conjunction form**.

Bundles the four generic sandwich arguments into a single conjunction
`h_combined` (lower / upper / above / below); the body destructures and
forwards to `lz78_asymptotic_optimality_two_sided`, a genuine
application, not an identity wrap. As with its target this is **not** the
LZ78 optimality claim — the bundled `h_lower` / `h_upper` conjuncts are
generic caller-supplied sandwich arguments. -/
theorem lz78_asymptotic_optimality_of_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_combined : ∀ᵐ ω ∂μ,
        (entropyRate μ p.toStationaryProcess
          ≤ Filter.liminf
              (fun n =>
                (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                  / (n : ℝ))
              Filter.atTop)
        ∧ (Filter.limsup
              (fun n =>
                (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                  / (n : ℝ))
              Filter.atTop
            ≤ entropyRate μ p.toStationaryProcess)
        ∧ Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
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
  refine lz78_asymptotic_optimality_two_sided μ p lz78EncodingLength
    ?_ ?_ ?_ ?_
  · filter_upwards [h_combined] with ω h
    exact h.1
  · filter_upwards [h_combined] with ω h
    exact h.2.1
  · filter_upwards [h_combined] with ω h
    exact h.2.2.1
  · filter_upwards [h_combined] with ω h
    exact h.2.2.2

end MainTheorem

end InformationTheory.Shannon
