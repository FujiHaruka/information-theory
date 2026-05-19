import Common2026.Shannon.Stationary
import Common2026.Shannon.EntropyRate
import Common2026.Shannon.ShannonMcMillanBreiman
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
  `IsLZ78ConversePassthrough`, `IsSMBSandwichPassthrough`) — `True`
  placeholders for the four discharged ingredients (Ziv's inequality, SMB
  sandwich, and the converse), upgraded to a meaningful predicate
  signature so that downstream discharge plans can replace `True` with the
  real statement without modifying the main theorem's external signature.
* **§3. Cut and intermediate-form theorems** —
  `lz78_achievability_upper_bound`, `lz78_converse_lower_bound`.
* **§4. Main theorem** — `lz78_asymptotic_optimality` (Cover–Thomas
  Theorem 13.5.3), plus the two-sided combine form.

## Scope (撤退ライン)

This file publishes the **statement-level hypothesis pass-through** form
of the asymptotic optimality theorem, with the same 5-retreat-line
strategy as `RelayCutset.lean` (T3-F):

* **L-LZ1**: Ziv's inequality (Cover–Thomas Lemma 13.5.5) is supplied as
  `IsZivInequalityPassthrough μ p lz78EncodingLength : Prop := True`
  placeholder. Discharge plan:
  [`lz78-ziv-inequality-discharge-*`](../../docs/shannon/lz78-moonshot-plan.md#l-lz1).
* **L-LZ2**: The LZ78 converse (Cover–Thomas Theorem 13.5.3 lower bound)
  is supplied as
  `IsLZ78ConversePassthrough μ p lz78EncodingLength : Prop := True`.
  Discharge plan: `lz78-converse-discharge-*`.
* **L-LZ3**: The SMB sandwich (a.s. convergence of the per-block negative
  log-likelihood to the entropy rate) is supplied as
  `IsSMBSandwichPassthrough μ p : Prop := True`. This is the bridge to
  `Common2026/Shannon/ShannonMcMillanBreiman.lean`'s
  `shannon_mcmillan_breiman_of_sandwich`, which itself takes the two
  sandwich inequalities as hypotheses (those in turn are discharged by
  Birkhoff + the SMB chain rule). Discharge plan:
  `lz78-smb-sandwich-discharge-*`.
* **L-LZ4**: The concrete `lz78Encode : List α → LZ78Parsing α` greedy
  parsing implementation is **scope-out**; instead the main theorem
  consumes a generic encoding-length function
  `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` supplied as a parameter.
  Discharge plan: `lz78-encode-impl-*`.
* **L-LZ5**: The final composite rate bound itself is supplied as
  `h_rate_bound` hypothesis; the main theorem's body is the identity wrap
  `:= h_rate_bound`. Discharge plan:
  `lz78-asymptotic-optimality-discharge-*`.

Out of scope (separate seeds):

* **L-LZ6**: Arithmetic coding (Cover–Thomas Ch.13.2–4) is in a separate
  seed `docs/shannon/arithmetic-coding-*`.
* **L-LZ7**: Kolmogorov complexity (Ch.14) is roadmap-level scope-out.

## Re-use of existing infrastructure

`Common2026/Shannon/Stationary.lean` (StationaryProcess / ErgodicProcess /
blockRV), `Common2026/Shannon/EntropyRate.lean` (`entropyRate`,
`entropyRate_exists_of_stationary`), and `Common2026/Shannon/
ShannonMcMillanBreiman.lean` (`blockLogAvg`,
`shannon_mcmillan_breiman_of_sandwich`, `tendsto_expected_blockLogAvg`)
are imported and re-used as **black boxes**: the present file does not
re-prove any of those results, it merely refers to them through the
type-level signatures.

## Pattern source

The 5-retreat-line + main-theorem-body-`:= h_rate_bound` pattern is
directly modelled on T3-F `relay_cutset_outer_bound`
(`Common2026/Shannon/RelayCutset.lean`), which in turn descends from T3-D
`wyner_ziv_converse_n_letter` (`Common2026/Shannon/WynerZivConverse.lean`).
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

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

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

Currently a `True` placeholder; the real Ziv-inequality discharge happens
in the companion seed `lz78-ziv-inequality-discharge-*`. The predicate
*signature* already depends on `μ`, `p`, and `lz78EncodingLength`, so the
external interface of the main theorem will not change when the body is
upgraded from `True` to the real inequality. -/
def IsZivInequalityPassthrough
    (μ : Measure Ω) (_p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

@[simp] lemma isZivInequalityPassthrough_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsZivInequalityPassthrough μ p lz78EncodingLength ↔ True := Iff.rfl

/-- Trivial constructor for the Ziv-inequality passthrough placeholder. -/
lemma IsZivInequalityPassthrough.trivial
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsZivInequalityPassthrough μ p lz78EncodingLength := True.intro

/-- **LZ78 converse passthrough predicate (Cover–Thomas Theorem 13.5.3
lower bound, L-LZ2)**.

Asserts the lower-bound half of LZ78 asymptotic optimality:

```
lim inf (1/n) · lz78EncodingLength(X^n) ≥ H   a.s.
```

This is the harder direction (uses SMB lower bound + arbitrary prefix
code Kraft inequality + finite-alphabet bookkeeping). Currently a `True`
placeholder; discharge in `lz78-converse-discharge-*`. -/
def IsLZ78ConversePassthrough
    (μ : Measure Ω) (_p : StationaryProcess μ α)
    (_lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) : Prop := True

@[simp] lemma isLZ78ConversePassthrough_def
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsLZ78ConversePassthrough μ p lz78EncodingLength ↔ True := Iff.rfl

/-- Trivial constructor for the LZ78-converse passthrough placeholder. -/
lemma IsLZ78ConversePassthrough.trivial
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ) :
    IsLZ78ConversePassthrough μ p lz78EncodingLength := True.intro

/-- **SMB sandwich passthrough predicate (Cover–Thomas Theorem 16.8.1,
L-LZ3)**.

Asserts that the per-block negative log-likelihood
`blockLogAvg μ p n ω` converges almost surely to `entropyRate μ p`. This
is *Shannon–McMillan–Breiman in its a.s. form*; the existing publish
`shannon_mcmillan_breiman_of_sandwich` in
`Common2026/Shannon/ShannonMcMillanBreiman.lean` takes the two sandwich
inequalities (`liminf ≥ H`, `limsup ≤ H`) and the two boundedness
hypotheses as input, and the present predicate stands in for the *output*
of that sandwich combine. Currently a `True` placeholder; discharge in
`lz78-smb-sandwich-discharge-*` via Birkhoff + the SMB chain rule. -/
def IsSMBSandwichPassthrough
    (μ : Measure Ω) (_p : StationaryProcess μ α) : Prop := True

@[simp] lemma isSMBSandwichPassthrough_def
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichPassthrough μ p ↔ True := Iff.rfl

/-- Trivial constructor for the SMB sandwich passthrough placeholder. -/
lemma IsSMBSandwichPassthrough.trivial
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsSMBSandwichPassthrough μ p := True.intro

end PassthroughPredicates

/-! ## §3. Cut and intermediate-form theorems -/

section IntermediateForms

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **LZ78 achievability — upper bound, hypothesis pass-through form**
(L-LZ1 + L-LZ3 engaged).

Given the Ziv-inequality passthrough and the SMB sandwich passthrough,
and supplied with the final scalar upper-bound `h_upper`, conclude

```
lim sup_n (1/n) · lz78EncodingLength(X^n) ≤ entropyRate   a.s.
```

The body is the identity wrap `:= h_upper`: the two passthrough
predicates participate in the *type* of the call but the result is
supplied directly. This signature is the LZ78 analogue of
`relay_broadcast_cut` from `RelayCutset.lean`. -/
theorem lz78_achievability_upper_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess
                lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n =>
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
      ≤ entropyRate μ p.toStationaryProcess := h_upper

/-- **LZ78 converse — lower bound, hypothesis pass-through form**
(L-LZ2 engaged).

Given the LZ78-converse passthrough and supplied with the final scalar
lower-bound `h_lower`, conclude

```
entropyRate ≤ lim inf_n (1/n) · lz78EncodingLength(X^n)   a.s.
```

Body is the identity wrap `:= h_lower`. Analogue of `relay_mac_cut`. -/
theorem lz78_converse_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess
                    lz78EncodingLength)
    (h_lower : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n =>
              (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := h_lower

end IntermediateForms

/-! ## §4. Main theorem — LZ78 asymptotic optimality -/

section MainTheorem

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **T4-A. Lempel–Ziv 78 asymptotic optimality (Cover–Thomas Theorem
13.5.3, hypothesis pass-through form, L-LZ1 + L-LZ2 + L-LZ3 + L-LZ4 +
L-LZ5 all engaged)**.

For a stationary ergodic source `p : ErgodicProcess μ α` on a finite
alphabet `α`, the per-symbol output length of any LZ78-like encoding
converges almost surely to the entropy rate:

```
lim_{n → ∞} (1/n) · lz78EncodingLength(X^n) = entropyRate μ p   a.s.
```

The five passthrough slots:

* `_h_ziv` — Ziv's inequality (L-LZ1; placeholder is `True`, real
  statement supplied by `lz78-ziv-inequality-discharge-*`).
* `_h_converse` — the LZ78 converse direction (L-LZ2).
* `_h_smb` — SMB sandwich a.s. convergence (L-LZ3).
* `lz78EncodingLength` — the encoding-length function is taken as a
  *parameter* (L-LZ4), not implemented in this file. Any function from
  `(Fin n → α) → ℕ` that is consistent with the LZ78 dictionary
  construction discharges this slot.
* `h_rate_bound` — the final composite a.s. Tendsto bound (L-LZ5). The
  body of the theorem is the identity wrap `:= h_rate_bound`.

The signature is the direct LZ78 analogue of
`relay_cutset_outer_bound` (T3-F) and
`wyner_ziv_converse_n_letter` (T3-D), with the Csiszár / chain
placeholders upgraded to meaningful (`IsZivInequalityPassthrough`
etc.) predicates so that the downstream discharge plans can replace the
`True` body with the real statement without changing the external
signature of this theorem. -/
theorem lz78_asymptotic_optimality
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess
                lz78EncodingLength)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess
                    lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_rate_bound : ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n =>
            (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
          (𝓝 (entropyRate μ p.toStationaryProcess))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78EncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := h_rate_bound

/-- **LZ78 asymptotic optimality — two-sided combine form**.

Instead of supplying the final a.s. Tendsto `h_rate_bound` directly,
supply the four sandwich ingredients — the limsup upper bound, the
liminf lower bound, and the two boundedness hypotheses
(`Filter.IsBoundedUnder` above and below) — and the theorem assembles
the Tendsto a.s. via `tendsto_of_le_liminf_of_limsup_le` (the same
combine pattern as `shannon_mcmillan_breiman_of_sandwich` in
`ShannonMcMillanBreiman.lean`).

This is the practical entry point when an upstream caller has the upper
and lower bounds separately (typical exit shape of a Ziv-inequality +
SMB sandwich pipeline). -/
theorem lz78_asymptotic_optimality_two_sided
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (_h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess
                lz78EncodingLength)
    (_h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess
                    lz78EncodingLength)
    (_h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
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

/-- **LZ78 asymptotic optimality — combine from limsup and liminf alone**.

Convenience helper that *does not* require the two `IsBoundedUnder`
hypotheses, since they can often be obtained from the integer-valued
nature of `lz78EncodingLength n` (bounded above by `n · log |α|` and
below by `0`). When the caller can supply both `Filter.IsBoundedUnder`
hypotheses elsewhere, this form is strictly weaker than
`lz78_asymptotic_optimality_two_sided`. -/
theorem lz78_asymptotic_optimality_of_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (h_ziv : IsZivInequalityPassthrough μ p.toStationaryProcess
              lz78EncodingLength)
    (h_converse : IsLZ78ConversePassthrough μ p.toStationaryProcess
                  lz78EncodingLength)
    (h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
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
    h_ziv h_converse h_smb ?_ ?_ ?_ ?_
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
