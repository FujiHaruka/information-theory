import Common2026.Shannon.ShannonCode
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Arithmetic Coding / Shannon-Fano-Elias (T4-A)

Cover-Thomas Theorem 13.3.3 (Ch.13.3 Universal Source Coding, Shannon-Fano-Elias
construction). For a finite-alphabet probability distribution `P` on `α`, the
**arithmetic code** assigns each symbol `a : α` a binary codeword whose length
satisfies

```
H(P) ≤ E[L] ≤ H(P) + 2
```

where `H(P)` is the (base-2) entropy and `E[L] = Σ_a P(a) · ℓ(a)` is the expected
codeword length. The construction uses the binary expansion of the **midpoint of
the cumulative-distribution interval** `F̄(a) := F(a) - P(a)/2`, truncated to
`⌈-log₂ P(a)⌉ + 1` bits. Truncation of distinct midpoints to that many bits
keeps the codewords inside disjoint intervals of the unit segment, which yields
the **prefix-free** property.

## File layout

This single file publishes:

* **§1. `ArithmeticCode` structure** — binary codeword assignment `α → List Bool`
  and the length projection `ArithmeticCode.length`.
* **§2. Passthrough predicates** — `IsCumulativeTruncationPassthrough`,
  `IsArithmeticPrefixFreePassthrough`, `IsArithmeticExpectedLengthPassthrough`
  — three `Prop := True` placeholders for the three discharged ingredients
  (L-AC1 / L-AC2 / L-AC3), upgraded to meaningful predicate signatures so that
  downstream discharge plans can replace `True` with the real statement without
  modifying the main theorem's external signature.
* **§3. Main theorem + side theorems** —
  `arithmetic_coding_expected_length_bounds`,
  `arithmetic_coding_prefix_free`, and
  `arithmetic_coding_unique_decodable`.

## Scope (撤退ライン)

This file publishes the **statement-level hypothesis pass-through** form of the
Cover-Thomas Theorem 13.3.3 sandwich, with the same retreat-line strategy as
`LempelZiv78.lean` (T4-A LZ78) and `ShannonHartley.lean` (T2-C):

* **L-AC1**: The cumulative-distribution truncation core (Cover-Thomas 13.3.2
  midpoint binary expansion + interval-disjointness) is supplied as
  `IsCumulativeTruncationPassthrough P l : Prop := True` placeholder.
  Discharge plan: `arithmetic-coding-cumulative-truncation-discharge-*`.
* **L-AC2**: The prefix-free property of the cumulative-truncation codewords
  is supplied as `IsArithmeticPrefixFreePassthrough c : Prop := True`.
  Discharge plan: `arithmetic-coding-prefix-free-discharge-*`.
* **L-AC3**: The Shannon-Fano-Elias expected-length bound `E[L] ≤ H + 2`
  (Cover-Thomas 13.3.3) is supplied as
  `IsArithmeticExpectedLengthPassthrough P l : Prop := True`, and the final
  scalar sandwich `H(P) ≤ E[L] ≤ H(P) + 2` is supplied as `h_bound`
  hypothesis; the main theorem's body is the identity wrap `:= h_bound`.
  Discharge plan: `arithmetic-coding-expected-length-discharge-*` (a linear
  lift of `ShannonCode.expectedLength_shannon_lt_entropyD_add_one`'s `< H + 1`
  bound to the `≤ H + 2` form via `⌈x⌉₊ + 1 < x + 2`).

Out of scope (separate seeds):

* The greedy/streaming arithmetic-encoding algorithm and its decoder (Cover-Thomas
  13.3.4) — `arithmetic-coding-implementation-*` discharge family.
* Block / stream extensions over `α^n` and asymptotic optimality
  (Cover-Thomas 13.3.5) — separate `arithmetic-coding-block-*` seed.
* Lempel-Ziv 78 (Cover-Thomas 13.5) — already published in
  `Common2026/Shannon/LempelZiv78.lean` as an independent seed.

## Re-use of existing infrastructure

`Common2026/Shannon/ShannonCode.lean`'s `entropyD` and `expectedLength`
definitions are imported and re-used as **black boxes**: the present file does
not redefine entropy or expected-length, it simply specializes `entropyD` to
`D = 2` (binary log) for the arithmetic-coding statement. The Shannon-code
sandwich `H_D(P) ≤ E[L_Shannon] < H_D(P) + 1` is the direct ancestor of the
arithmetic-coding sandwich `H(P) ≤ E[L_arith] ≤ H(P) + 2`: the `+1` becomes
`+2` because each codeword length is `⌈-log P(a)⌉ + 1` instead of
`⌈-log P(a)⌉` (the extra bit is the price of the cumulative-distribution
truncation, which buys the prefix-free property without an explicit Kraft
construction).

## Pattern source

The 3-retreat-line + main-theorem-body-`:= h_bound` pattern is directly modelled
on T4-A LZ78 (`Common2026/Shannon/LempelZiv78.lean`, 5 retreat lines) and T2-C
Shannon-Hartley (`Common2026/Shannon/ShannonHartley.lean`, 3 retreat lines), with
the Csiszár / chain placeholders upgraded to meaningful (`IsCumulativeTruncationPassthrough`
etc.) predicates so that the downstream discharge plans can replace the `True`
body with the real statement without changing the external signature of this
theorem.
-/

namespace InformationTheory.Shannon.ArithmeticCoding

open MeasureTheory
open InformationTheory.Shannon.ShannonCode (entropyD expectedLength)

set_option linter.unusedSectionVars false

/-! ## §1. `ArithmeticCode` structure -/

section ArithmeticCodeStructure

/-- An **arithmetic code** on a finite alphabet `α` is a binary codeword
assignment `α → List Bool`. Cover-Thomas Ch.13.3 constructs this as the
binary expansion of the cumulative-distribution midpoint
`F̄(a) := F(a) - P(a)/2`, truncated to `⌈-log₂ P(a)⌉ + 1` bits, but the
present file treats the codeword function as an opaque field — the
cumulative-truncation construction is hypothesized via the L-AC1 / L-AC2
passthrough predicates below. -/
structure ArithmeticCode (α : Type*) where
  /-- The binary codeword assigned to each symbol. -/
  codeword : α → List Bool

namespace ArithmeticCode

variable {α : Type*}

/-- The length of the codeword for symbol `a`. -/
@[simp] def length (c : ArithmeticCode α) (a : α) : ℕ :=
  (c.codeword a).length

/-- Two arithmetic codes are equal iff their codeword functions agree. -/
lemma ext_iff {c₁ c₂ : ArithmeticCode α} :
    c₁ = c₂ ↔ c₁.codeword = c₂.codeword := by
  cases c₁; cases c₂; simp

@[ext] lemma ext {c₁ c₂ : ArithmeticCode α}
    (h : c₁.codeword = c₂.codeword) : c₁ = c₂ :=
  ext_iff.mpr h

end ArithmeticCode

end ArithmeticCodeStructure

/-! ## §2. Passthrough predicates -/

section PassthroughPredicates

variable {α : Type*}

/-- **Cumulative-truncation passthrough predicate (L-AC1)**.

Asserts the Cover-Thomas 13.3.2 core fact: the binary expansion of the
cumulative-distribution midpoint `F̄(a) := F(a) - P(a)/2`, truncated to
`l(a) = ⌈-log₂ P(a)⌉ + 1` bits, produces a binary codeword `c(a) : List Bool`
of length `l(a)` such that distinct codewords land in disjoint half-open
intervals of `[0, 1)` of length `2^(-l(a))`.

Currently a `True` placeholder; the real cumulative-truncation discharge happens
in the companion seed `arithmetic-coding-cumulative-truncation-discharge-*`.
The predicate *signature* already depends on `P` and `l`, so the external
interface of the main theorem will not change when the body is upgraded from
`True` to the real statement. -/
def IsCumulativeTruncationPassthrough
    [MeasurableSpace α] (_P : Measure α) (_l : α → ℕ) : Prop := True

@[simp] lemma isCumulativeTruncationPassthrough_def
    [MeasurableSpace α] (P : Measure α) (l : α → ℕ) :
    IsCumulativeTruncationPassthrough P l ↔ True := Iff.rfl

/-- Trivial constructor for the cumulative-truncation passthrough placeholder. -/
lemma IsCumulativeTruncationPassthrough.trivial
    [MeasurableSpace α] (P : Measure α) (l : α → ℕ) :
    IsCumulativeTruncationPassthrough P l := True.intro

/-- **Arithmetic prefix-free passthrough predicate (L-AC2)**.

Asserts that the arithmetic-code codewords are prefix-free:
`∀ a b, a ≠ b → ¬ c a <+: c b`. By Cover-Thomas 13.3.2, this follows from the
disjoint-interval property of the cumulative-truncation; here it is hypothesized
directly. Currently a `True` placeholder; discharge in
`arithmetic-coding-prefix-free-discharge-*`. -/
def IsArithmeticPrefixFreePassthrough
    (_c : α → List Bool) : Prop := True

@[simp] lemma isArithmeticPrefixFreePassthrough_def
    (c : α → List Bool) :
    IsArithmeticPrefixFreePassthrough c ↔ True := Iff.rfl

/-- Trivial constructor for the arithmetic prefix-free passthrough placeholder. -/
lemma IsArithmeticPrefixFreePassthrough.trivial
    (c : α → List Bool) :
    IsArithmeticPrefixFreePassthrough c := True.intro

/-- **Arithmetic expected-length passthrough predicate (L-AC3)**.

Asserts the Cover-Thomas Theorem 13.3.3 expected-length bound: for an arithmetic
code with lengths `l(a) = ⌈-log₂ P(a)⌉ + 1`,

```
E[L] := Σ_a P(a) · l(a)  ≤  H(P) + 2.
```

This is a linear lift of `ShannonCode.expectedLength_shannon_lt_entropyD_add_one`'s
`E[L_Shannon] < H + 1` bound (with `+1` replaced by `+2` to account for the
extra bit of the cumulative-truncation construction). Currently a `True`
placeholder; discharge in `arithmetic-coding-expected-length-discharge-*`. -/
def IsArithmeticExpectedLengthPassthrough
    [MeasurableSpace α] (_P : Measure α) (_l : α → ℕ) : Prop := True

@[simp] lemma isArithmeticExpectedLengthPassthrough_def
    [MeasurableSpace α] (P : Measure α) (l : α → ℕ) :
    IsArithmeticExpectedLengthPassthrough P l ↔ True := Iff.rfl

/-- Trivial constructor for the arithmetic expected-length passthrough placeholder. -/
lemma IsArithmeticExpectedLengthPassthrough.trivial
    [MeasurableSpace α] (P : Measure α) (l : α → ℕ) :
    IsArithmeticExpectedLengthPassthrough P l := True.intro

end PassthroughPredicates

/-! ## §3. Main theorem and side theorems -/

section MainTheorem

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **T4-A. Arithmetic coding expected-length sandwich
(Cover-Thomas Theorem 13.3.3, hypothesis pass-through form,
L-AC1 + L-AC2 + L-AC3 all engaged)**.

For a finite-alphabet probability measure `P` on `α` and an arithmetic code
`c : ArithmeticCode α`, the expected codeword length is sandwiched between the
binary entropy and entropy-plus-two:

```
H(P)  ≤  E[L]  ≤  H(P) + 2.
```

The three passthrough slots:

* `_h_trunc` — cumulative-distribution truncation (L-AC1; placeholder is `True`,
  real statement supplied by `arithmetic-coding-cumulative-truncation-discharge-*`).
* `_h_pf` — prefix-free property of the codewords (L-AC2).
* `_h_exp` — Shannon-Fano-Elias expected-length bound (L-AC3).
* `h_bound` — the final scalar sandwich (the body is the identity wrap
  `:= h_bound`).

The signature is the direct Ch.13.3 analogue of
`lz78_asymptotic_optimality` (T4-A LZ78) and `shannon_hartley_formula`
(T2-C), with the Csiszár / chain placeholders upgraded to meaningful
(`IsCumulativeTruncationPassthrough` etc.) predicates so that the downstream
discharge plans can replace the `True` body with the real statement without
changing the external signature of this theorem. -/
theorem arithmetic_coding_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P]
    (c : ArithmeticCode α)
    (_h_trunc : IsCumulativeTruncationPassthrough P c.length)
    (_h_pf : IsArithmeticPrefixFreePassthrough c.codeword)
    (_h_exp : IsArithmeticExpectedLengthPassthrough P c.length)
    (h_bound : entropyD 2 P ≤ expectedLength P c.length
                ∧ expectedLength P c.length ≤ entropyD 2 P + 2) :
    entropyD 2 P ≤ expectedLength P c.length ∧
      expectedLength P c.length ≤ entropyD 2 P + 2 := h_bound

/-- **Arithmetic-coding prefix-free property** (L-AC2 engaged).

The cumulative-truncation codewords are prefix-free: for distinct symbols `a, b`,
`c.codeword a` is not a prefix of `c.codeword b`. Body is the identity wrap
`:= h_pf_real`. -/
theorem arithmetic_coding_prefix_free
    (P : Measure α) [IsProbabilityMeasure P]
    (c : ArithmeticCode α)
    (_h_trunc : IsCumulativeTruncationPassthrough P c.length)
    (_h_pf : IsArithmeticPrefixFreePassthrough c.codeword)
    (h_pf_real : ∀ a b : α, a ≠ b → ¬ c.codeword a <+: c.codeword b) :
    ∀ a b : α, a ≠ b → ¬ c.codeword a <+: c.codeword b := h_pf_real

/-- **Arithmetic-coding unique decodability** (a consequence of prefix-freeness;
Cover-Thomas 5.2.2: every prefix code is uniquely decodable). Body is the
identity wrap `:= h_ud`. -/
theorem arithmetic_coding_unique_decodable
    (P : Measure α) [IsProbabilityMeasure P]
    (c : ArithmeticCode α)
    (_h_trunc : IsCumulativeTruncationPassthrough P c.length)
    (_h_pf : IsArithmeticPrefixFreePassthrough c.codeword)
    (h_ud : ∀ (s₁ s₂ : List α),
        (s₁.map c.codeword).flatten = (s₂.map c.codeword).flatten → s₁ = s₂) :
    ∀ (s₁ s₂ : List α),
      (s₁.map c.codeword).flatten = (s₂.map c.codeword).flatten → s₁ = s₂ := h_ud

end MainTheorem

end InformationTheory.Shannon.ArithmeticCoding
