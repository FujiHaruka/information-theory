import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.SMB.McMillanBreiman
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lempel–Ziv 78 asymptotic optimality

Cover–Thomas (Universal Source Coding): for a
stationary ergodic source `{X_i}` on a finite alphabet `α`, the per-symbol
output length of the LZ78 dictionary code converges almost surely to the
entropy rate:

```
lim_{n → ∞} (1/n) · ℓ(LZ78(X^n)) = H(𝓧)   a.s.
```

This is the universal source-coding analogue of Shannon's source-coding
theorem: LZ78 achieves the entropy-rate lower bound without any prior
knowledge of the source statistics.

## File layout

This single file publishes:

* §1. LZ78 phrase data structures (`LZ78Phrase α`, `LZ78Parsing α`)
  — the type-level encoding of an LZ78 dictionary parsing.
* §2. Generic sandwich combinator — `lz78_asymptotic_optimality` (and its
  alias / bundled forms), the LZ78-flavored wrapper of
  `tendsto_of_le_liminf_of_limsup_le`.

## Scope of the §2 combinator

`lz78_asymptotic_optimality` is not the LZ78 optimality theorem. It takes a
generic encoding-length function `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ`
(the concrete greedy parse `lz78Encode : List α → LZ78Parsing α` is supplied
externally), a generic limit `L : ℝ`, and a caller-supplied two-sided a.s.
sandwich on the per-symbol rate — the liminf lower bound `L ≤ liminf (lz/n)`,
the limsup upper bound `limsup (lz/n) ≤ L`, and two boundedness arguments —
and derives a.s. convergence of `lz/n` to `L` by
`tendsto_of_le_liminf_of_limsup_le` (the same combine pattern as
`shannon_mcmillan_breiman_of_sandwich`). Its `h_lower` / `h_upper` are
hypotheses on whatever encoding the caller supplies, not a claim that some
encoding achieves the entropy rate.

For the greedy LZ78 parser the two halves carry the substance:
the achievability upper bound `∀ᵐ ω, limsup (lz/n) ≤ entropyRate₂`
(Ziv's inequality, Cover–Thomas) and the converse
lower bound `∀ᵐ ω, entropyRate₂ ≤ liminf (lz/n)`. They are
`lz78Greedy_achievability_ae` (`AsymptoticOptimality/ParentBridgeAchievability.lean`)
and `lz78Greedy_converse_ae` (`AsymptoticOptimality/ParentBridgeConverse.lean`);
the headline instantiating the combinator with them at `L = entropyRate₂` is
`lz78_asymptotic_optimality_with_greedy`.

## Re-use of existing infrastructure

`InformationTheory/Shannon/Stationary/Basic.lean` (`StationaryProcess` /
`ErgodicProcess` / `blockRV`), `InformationTheory/Shannon/EntropyRate.lean`
(`entropyRate`, `entropyRate_exists_of_stationary`) and
`InformationTheory/Shannon/SMB/McMillanBreiman.lean` (`blockLogAvg`,
`shannon_mcmillan_breiman_of_sandwich`) are imported and used as black
boxes; this file re-proves none of them.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

/-! ## §1. LZ78 phrase data structures -/

section LZ78Structures

/-- An LZ78 dictionary phrase is a pair `(parent, symbol)` where:

* `parent : Option ℕ` references the earlier phrase being extended, or
`none` for the empty-prefix root (the very first phrase ever emitted).
* `symbol : α` is the single new alphabet symbol appended.

This is the Cover–Thomas dictionary entry encoded at the type
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

/-- An LZ78 parsing of a finite input is a list of dictionary phrases
together with the structural invariant that every `parent = some k`
references an earlier (strictly smaller) phrase index.

This is the minimal Cover–Thomas LZ78 dictionary structure: a list
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
/-- The generic two-sided sandwich-combine lemma for per-symbol coding
rates (the LZ78-flavored wrapper of `tendsto_of_le_liminf_of_limsup_le`).

This is not the LZ78 asymptotic-optimality claim itself. It is a generic
combinator: given *any* encoding-length function `lz78EncodingLength`, *any*
limit value `L : ℝ`, and a two-sided a.s. sandwich on the per-symbol rate
(`L ≤ liminf` and `limsup ≤ L`, plus a.s. boundedness), it derives a.s.
convergence of `lz/n` to `L` via `tendsto_of_le_liminf_of_limsup_le` (a
1-step squeeze). The hypotheses `h_lower` / `h_upper` are caller-supplied,
not a claim that any particular encoding achieves any particular limit.

The limit `L` is left generic rather than hard-wired to `entropyRate`, so
that the bit-rate headline `lz78_asymptotic_optimality_with_greedy` can
instantiate it with the bit-unit `entropyRate₂`. -/
theorem lz78_asymptotic_optimality
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (L : ℝ)
    (h_lower : ∀ᵐ ω ∂μ,
        L
        ≤ Filter.liminf
            (fun n ↦
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n ↦
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ L)
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n ↦
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ)))
    (h_bdd_below : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n ↦
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n ↦
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 L) := by
  filter_upwards [h_lower, h_upper, h_bdd_above, h_bdd_below]
    with ω hl hu hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

omit [DecidableEq α] in
/-- The generic two-sided sandwich-combine, alias form.

Alias for the generic combinator `lz78_asymptotic_optimality` with the
same four arguments (liminf lower bound, limsup upper bound, two
`Filter.IsBoundedUnder` boundedness arguments), specialized to
`L = entropyRate μ p`. Like its target this is not the LZ78 optimality
claim — `h_lower` / `h_upper` are caller-supplied sandwich arguments. -/
theorem lz78_asymptotic_optimality_two_sided
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_lower : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n ↦
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n ↦
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess)
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n ↦
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ)))
    (h_bdd_below : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n ↦
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n ↦
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_asymptotic_optimality μ p lz78EncodingLength
    (entropyRate μ p.toStationaryProcess)
    h_lower h_upper h_bdd_above h_bdd_below

omit [DecidableEq α] in
/-- The generic two-sided sandwich-combine, bundled-conjunction form.

Bundles the four sandwich arguments into a single conjunction `h_combined`
(lower / upper / above / below); the body destructures and forwards to
`lz78_asymptotic_optimality_two_sided`. As with its target this is not the
LZ78 optimality claim — the bundled lower / upper conjuncts are
caller-supplied sandwich arguments. -/
theorem lz78_asymptotic_optimality_of_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_combined : ∀ᵐ ω ∂μ,
        (entropyRate μ p.toStationaryProcess
          ≤ Filter.liminf
              (fun n ↦
                (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                  / (n : ℝ))
              Filter.atTop)
        ∧ (Filter.limsup
              (fun n ↦
                (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                  / (n : ℝ))
              Filter.atTop
            ≤ entropyRate μ p.toStationaryProcess)
        ∧ Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n ↦
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
        ∧ Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
            (fun n ↦
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n ↦
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
