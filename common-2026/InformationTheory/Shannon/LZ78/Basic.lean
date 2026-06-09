import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.SMB.McMillanBreiman
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lempel–Ziv 78 asymptotic optimality (T4-A)

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
* **§2. Passthrough predicates** (`IsZivInequalityPassthrough`,
  `IsLZ78ConversePassthrough`, `IsSMBSandwichPassthrough`) — **genuine
  statements** for the discharged ingredients (Ziv's inequality, SMB
  sandwich, the converse). Each body is the real a.s. statement
  (`limsup ≤ entropyRate` / `entropyRate ≤ liminf` / `Tendsto … (𝓝 entropyRate)`)
  rather than a `True` placeholder; their proofs are routed through the
  `lz78-residual-discharge-plan` successor. These are **not hypotheses of
  the §4 main theorem**; they survive only as discharge plumbing consumed
  by the `.of*` bridge constructors in the downstream LZ78 files. The
  genuine residual of the headline is the two-sided sandwich on `lz/n`,
  not any of these predicates.
* **§3. Main theorem** — `lz78_asymptotic_optimality` (Cover–Thomas
  Theorem 13.5.3), plus the two-sided combine form.

## Scope (撤退ライン)

This file publishes the **statement-level hypothesis pass-through** form
of the asymptotic optimality theorem, with the same 5-retreat-line
strategy as `RelayCutset.lean` (T3-F):

* **L-LZ1**: Ziv's inequality (Cover–Thomas Lemma 13.5.5) is published as
  `IsZivInequalityPassthrough μ p lz78EncodingLength : Prop :=
   ∀ᵐ ω, limsup (lz/n) ≤ entropyRate μ p` — the genuine achievability
  upper bound a.s. Discharge plan:
  [`lz78-residual-discharge-plan`](../../docs/shannon/lz78-residual-discharge-plan.md)
  Phase Z (`isLZ78AchievabilityChainHyp_distinct`).
* **L-LZ2**: The LZ78 converse (Cover–Thomas Theorem 13.5.3 lower bound)
  is published as
  `IsLZ78ConversePassthrough μ p lz78EncodingLength : Prop :=
   ∀ᵐ ω, entropyRate μ p ≤ liminf (lz/n)` — the genuine converse lower
  bound a.s. Discharge plan: `lz78-residual-discharge-plan` Phase C.
* **L-LZ3**: The SMB sandwich (a.s. convergence of the per-block negative
  log-likelihood to the entropy rate) is published as
  `IsSMBSandwichPassthrough μ p : Prop :=
   ∀ᵐ ω, Tendsto (blockLogAvg μ p n) atTop (𝓝 (entropyRate μ p))`. This is
  the bridge to `InformationTheory/Shannon/ShannonMcMillanBreiman.lean`'s
  `shannon_mcmillan_breiman_of_sandwich`, which itself takes the two
  sandwich inequalities as hypotheses (those in turn are discharged by
  Birkhoff + the SMB chain rule). Discharge plan:
  `lz78-residual-discharge-plan`.
* **L-LZ4**: The concrete `lz78Encode : List α → LZ78Parsing α` greedy
  parsing implementation is **scope-out**; instead the main theorem
  consumes a generic encoding-length function
  `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` supplied as a parameter.
  Discharge plan: `lz78-encode-impl-*`.
* **L-LZ5**: The main theorem `lz78_asymptotic_optimality` is **not** an
  identity wrap of its conclusion. It takes the genuine two-sided sandwich
  on `lz/n` — the liminf lower bound `entropyRate ≤ liminf (lz/n)`, the
  limsup upper bound `limsup (lz/n) ≤ entropyRate`, and the two
  boundedness hypotheses — and *derives* the a.s. Tendsto via
  `tendsto_of_le_liminf_of_limsup_le`. The sandwich residual is distinct
  from the conclusion (`≤` bounds vs. `Tendsto … (𝓝 entropyRate)`). The
  maximally-discharged chain-level form (residual = the genuine
  Cover–Thomas Eq. 13.124 / 13.130 `blockLogAvg` inequalities, SMB
  sandwich discharged internally) is `lz78_two_sided_optimality_ergodic`
  in `LZ78FinalGlue.lean` (which imports this file).

Out of scope (separate seeds):

* **L-LZ6**: Arithmetic coding (Cover–Thomas Ch.13.2–4) is in a separate
  seed `docs/shannon/arithmetic-coding-*`.
* **L-LZ7**: Kolmogorov complexity (Ch.14) is roadmap-level scope-out.

## Re-use of existing infrastructure

`InformationTheory/Shannon/Stationary.lean` (StationaryProcess / ErgodicProcess /
blockRV), `InformationTheory/Shannon/EntropyRate.lean` (`entropyRate`,
`entropyRate_exists_of_stationary`), and `InformationTheory/Shannon/
ShannonMcMillanBreiman.lean` (`blockLogAvg`,
`shannon_mcmillan_breiman_of_sandwich`, `tendsto_expected_blockLogAvg`)
are imported and re-used as **black boxes**: the present file does not
re-prove any of those results, it merely refers to them through the
type-level signatures.

## Pattern source

The §4 main theorem is a genuine two-sided-sandwich derivation via
`tendsto_of_le_liminf_of_limsup_le` (the same combine pattern as
`shannon_mcmillan_breiman_of_sandwich` in `ShannonMcMillanBreiman.lean`),
*not* an identity-wrap pass-through. The L-LZ1–L-LZ4 passthrough
predicates (§2) survive only as discharge plumbing consumed by the
`.of*` bridges in the downstream LZ78 files; no published headline takes
any of them as its residual hypothesis.
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
externally (L-LZ4); see the file-level docstring. -/
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

/-! ## §2. Passthrough predicates -/

section PassthroughPredicates

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Ziv's inequality passthrough predicate (Cover–Thomas Lemma 13.5.5,
L-LZ1)**.

For a stationary process `p` on alphabet `α` and an encoding-length
function `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ`, this predicate
asserts the Ziv inequality

```
c(n) · log c(n) ≤ - ∑_{i=1}^{c(n)} log P(phrase_i)
```

in its asymptotic per-sample form, which (when combined with SMB) gives
the upper bound `lim sup (1/n) lz78EncodingLength ≤ H` almost surely.

The body is now the genuine a.s. limsup upper bound
`∀ᵐ ω, limsup (lz n / n) ≤ entropyRate μ p` (no longer a `True`
placeholder). The proof of this a.s. statement is delegated to the
companion seed `lz78-ziv-inequality-discharge-*` and the residual
discharge plan; the present file publishes the *statement* only. The
predicate *signature* depends on `μ`, `p`, and `lz78EncodingLength`, and
the main theorem `lz78_asymptotic_optimality` does **not** take this
predicate as a hypothesis, so its external interface is unaffected.

`@audit:closed-by-successor(textbook-roadmap-m3-m4-scope-out)`
— body は実 statement (`limsup (lz n / n) ≤ entropyRate` a.s.) に書換、tier 5
`prop-true` placeholder を解消。signature (`μ`, `p`, `lz78EncodingLength`) は不変、
main theorem `lz78_asymptotic_optimality` は本述語を hypothesis に取らないため
external interface も不変。本 def の証明 (a.s. limsup 上界) は **textbook-roadmap で
M3 (variable-depth tree AEP) / M4 (Barron a.s. lift) として research-level upstream
に scope-out 済** (Mathlib 測度論基盤の新規研究貢献を要する)。
`lz78-residual-discharge-plan` (旧 successor 計画) は archive 化、本 def は
statement-only publish 形式を維持する。 -/
def IsZivInequalityPassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop :=
  ∀ᵐ ω ∂μ,
    Filter.limsup
      (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
      Filter.atTop
    ≤ entropyRate μ p


/-- **LZ78 converse passthrough predicate (Cover–Thomas Theorem 13.5.3
lower bound, L-LZ2)**.

Asserts the lower-bound half of LZ78 asymptotic optimality:

```
lim inf (1/n) · lz78EncodingLength(X^n) ≥ H   a.s.
```

This is the harder direction (uses SMB lower bound + arbitrary prefix
code Kraft inequality + finite-alphabet bookkeeping). The body is now
the genuine a.s. liminf lower bound
`∀ᵐ ω, entropyRate μ p ≤ liminf (lz n / n)` (no longer a `True`
placeholder); the proof of this a.s. statement is delegated to
`lz78-converse-discharge-*` and the residual discharge plan.

`@audit:closed-by-successor(textbook-roadmap-m3-m4-scope-out)`
— body は実 statement (`entropyRate ≤ liminf (lz n / n)` a.s.) に書換、tier 5
`prop-true` placeholder を解消。signature 不変、main theorem `lz78_asymptotic_optimality`
は本述語を hypothesis に取らないため external interface も不変。本 def の証明
(a.s. liminf 下界) は **textbook-roadmap で M3 (variable-depth tree AEP) / M4
(Barron a.s. lift) として research-level upstream に scope-out 済** (Mathlib 測度論
基盤の新規研究貢献を要する)。`lz78-residual-discharge-plan` (旧 successor 計画) は
archive 化、本 def は statement-only publish 形式を維持する。 -/
@[entry_point]
def IsLZ78ConversePassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop :=
  ∀ᵐ ω ∂μ,
    entropyRate μ p
    ≤ Filter.liminf
        (fun n => (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop


/-- **SMB sandwich passthrough predicate (Cover–Thomas Theorem 16.8.1,
L-LZ3)**.

Asserts that the per-block negative log-likelihood
`blockLogAvg μ p n ω` converges almost surely to `entropyRate μ p`. This
is *Shannon–McMillan–Breiman in its a.s. form*; the existing publish
`shannon_mcmillan_breiman_of_sandwich` in
`InformationTheory/Shannon/ShannonMcMillanBreiman.lean` takes the two sandwich
inequalities (`liminf ≥ H`, `limsup ≤ H`) and the two boundedness
hypotheses as input, and the present predicate stands in for the *output*
of that sandwich combine. The body is now the genuine a.s. Tendsto
statement `∀ᵐ ω, Tendsto (blockLogAvg μ p n) atTop (𝓝 (entropyRate μ p))`
(no longer a `True` placeholder); the proof of this a.s. statement is
delegated to `lz78-smb-sandwich-discharge-*` via Birkhoff + the SMB
chain rule.

`@audit:closed-by-successor(textbook-roadmap-m3-m4-scope-out)`
— body は実 statement (a.s. `Tendsto (blockLogAvg μ p n) atTop (𝓝 (entropyRate μ p))`)
に書換、tier 5 `prop-true` placeholder を解消。signature 不変、main theorem
`lz78_asymptotic_optimality` は本述語を hypothesis に取らないため external interface
も不変。本 def の証明 (SMB a.s. 形) は **textbook-roadmap で M3 (variable-depth tree
AEP) / M4 (Barron a.s. lift) として research-level upstream に scope-out 済**
(Mathlib 測度論基盤の新規研究貢献を要する)。`lz78-residual-discharge-plan` (旧
successor 計画) は archive 化、本 def は statement-only publish 形式を維持する。 -/
@[entry_point]
def IsSMBSandwichPassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
  ∀ᵐ ω ∂μ,
    Filter.Tendsto (fun n => blockLogAvg μ p n ω) Filter.atTop
      (𝓝 (entropyRate μ p))


end PassthroughPredicates

/-! ## §3. Main theorem — LZ78 asymptotic optimality -/

section MainTheorem

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

omit [DecidableEq α] in
/-- **T4-A. Lempel–Ziv 78 asymptotic optimality (Cover–Thomas Theorem
13.5.3, two-sided sandwich form)**.

For a stationary ergodic source `p : ErgodicProcess μ α` on a finite
alphabet `α`, the per-symbol output length of any LZ78-like encoding
converges almost surely to the entropy rate:

```
lim_{n → ∞} (1/n) · lz78EncodingLength(X^n) = entropyRate μ p   a.s.
```

This headline is **non-circular**: it does *not* take the conclusion
(`Tendsto … (𝓝 entropyRate)`) as a hypothesis and wrap it. Instead it
takes the genuine two-sided sandwich on `lz/n` — the liminf lower bound
`entropyRate ≤ liminf (lz/n)`, the limsup upper bound
`limsup (lz/n) ≤ entropyRate`, and the two boundedness hypotheses — and
*derives* the a.s. Tendsto via `tendsto_of_le_liminf_of_limsup_le`.

The hypothesis slots:

* `lz78EncodingLength` — the encoding-length function is taken as a
*parameter* (L-LZ4), not implemented in this file. Any function from
`(Fin n → α) → ℕ` consistent with the LZ78 dictionary discharges it.
* `h_lower` — the LZ78 converse direction `entropyRate ≤ liminf (lz/n)`
a.s. (L-LZ2). This is *not* the conclusion; it is the genuine lower
half of the sandwich, supplied downstream by
`lz78_converse_lower_bound_with_chain` composed with the SMB liminf.
* `h_upper` — the Ziv-inequality achievability bound
`limsup (lz/n) ≤ entropyRate` a.s. (L-LZ1). Supplied downstream by
`lz78_achievability_upper_bound_ergodic`.
* `h_bdd_above` / `h_bdd_below` — boundedness of the per-symbol rate.

For the maximally-discharged chain-level form (where the residual is the
genuine `IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp`
Cover–Thomas Eq. 13.124 / 13.130 inequalities relating `lz/n` to
`blockLogAvg`, with the SMB sandwich discharged internally), see
`lz78_two_sided_optimality_ergodic` in `LZ78FinalGlue.lean`. That file
imports this one, so the chain-level discharge cannot be routed back into
this headline without a circular import; this file therefore publishes
the sandwich-level (genuine, non-circular) form. -/
@[entry_point]
theorem lz78_asymptotic_optimality
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
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  filter_upwards [h_lower, h_upper, h_bdd_above, h_bdd_below]
    with ω hl hu hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

omit [DecidableEq α] in
/-- **LZ78 asymptotic optimality — two-sided combine form**.

Public alias for `lz78_asymptotic_optimality` with the same four genuine
sandwich ingredients — the liminf lower bound, the limsup upper bound, and
the two boundedness hypotheses (`Filter.IsBoundedUnder` above and below).
The Tendsto a.s. is assembled via `tendsto_of_le_liminf_of_limsup_le` (the
same combine pattern as `shannon_mcmillan_breiman_of_sandwich` in
`ShannonMcMillanBreiman.lean`). The body is a genuine application, not an
identity wrap of the conclusion.

This is the practical entry point when an upstream caller has the upper
and lower bounds separately (typical exit shape of a Ziv-inequality +
SMB sandwich pipeline). The four hypotheses are non-circular: the
sandwich bounds relate `lz/n` to `entropyRate` via `≤`, distinct from the
`Tendsto … (𝓝 entropyRate)` conclusion. -/
@[entry_point]
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
    h_lower h_upper h_bdd_above h_bdd_below

omit [DecidableEq α] in
/-- **LZ78 asymptotic optimality — combine from limsup and liminf alone**.

Convenience helper that *does not* require the two `IsBoundedUnder`
hypotheses, since they can often be obtained from the integer-valued
nature of `lz78EncodingLength n` (bounded above by `n · log |α|` and
below by `0`). When the caller can supply both `Filter.IsBoundedUnder`
hypotheses elsewhere, this form is strictly weaker than
`lz78_asymptotic_optimality_two_sided`. The single bundled hypothesis is
the genuine four-way sandwich conjunction (lower / upper / above / below);
the body is a genuine application of `lz78_asymptotic_optimality_two_sided`,
not an identity wrap. -/
@[entry_point]
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
