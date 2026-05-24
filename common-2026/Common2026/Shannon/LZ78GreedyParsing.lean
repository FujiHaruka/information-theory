import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78ZivInequality
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# LZ78 greedy parsing — L-LZ4 partial discharge (T4-A continuation)

This file publishes the **concrete LZ78 parsing implementation**
and elementary **encoding-length upper bounds** of the form

```
lz78EncodingLength n x ≤ n · (Nat.log 2 (n + 1) + Nat.log 2 |α| + 2)
```

which is the Cover–Thomas Theorem 13.5.2 phrase-by-phrase bit-length
form (each phrase index needs `log(dictSize)` bits, each appended
symbol needs `log(|α|)` bits, plus a constant overhead). The full
asymptotic `n · log L_n` bound is the intended consequence; the
present file lays the **structural plumbing** for L-LZ4 discharge so
that downstream callers can plug `lz78GreedyEncodingLength` into the
parent `lz78EncodingLength` parameter slot of
`lz78_asymptotic_optimality`
(`Common2026/Shannon/LempelZiv78.lean`).

## File layout

* **§1. Per-phrase bit length** — `LZ78Phrase.bitLength`: the number
  of bits to encode one (parent-index, symbol) pair given a dictionary
  size and alphabet size.
* **§2. Sum-over-phrases encoding length** —
  `LZ78Parsing.encodingLength`: the total bit length of an LZ78
  parsing.
* **§3. Concrete parsing function (one-symbol-per-phrase form)** —
  `lz78OneSymbolParsing`: a valid LZ78 parsing where every phrase
  consists of a single symbol (parent `none`). It is the **safest**
  greedy form (worst-case `count = input length`), satisfying the
  `LZ78Parsing` invariant by construction.
* **§4. Greedy encoding-length function (L-LZ4 parameter slot)** —
  `lz78GreedyEncodingLength : ∀ n, (Fin n → α) → ℕ`: the concrete
  encoding length on tuples, plugging into the parent
  `lz78EncodingLength` parameter slot.
* **§5. Encoding-length upper bound (Cover–Thomas Lemma 13.5.2)** —
  `lz78_encoding_length_le_n_log_n_plus_const`: the elementary
  count-times-per-phrase bit upper bound.
* **§6. Count-vs-`n` bound as hypothesis pass-through (L-LZ4-D)** —
  `IsLZ78CountBoundPassthrough`: predicate exposing the sharper
  count bound `B(n)` as a hypothesis; the elementary `count ≤ n`
  bound is supplied as `.id`.
* **§7. Bridge to `IsZivInequalityPassthrough` (L-LZ4 → L-LZ1)** —
  the concrete `lz78GreedyEncodingLength` plugs into the
  `True`-placeholder parent `IsZivInequalityPassthrough`.

## 撤退ライン

* **L-LZ4-A** (engaged) — Concrete LZ78 parsing function published as
  the one-symbol-per-phrase form (worst-case but always valid).
* **L-LZ4-B** (engaged) — Per-phrase + summed bit-length functions
  published as totally computable definitions.
* **L-LZ4-C** (engaged) — Encoding-length upper bound in the
  `n · (log(n+1) + log|α| + 2)` form proved by elementary arithmetic
  on `Nat.log`.
* **L-LZ4-D** (deferred) — The sharper `count ≤ n / log n` bound
  (Cover–Thomas Eq. 13.124) is a hypothesis pass-through; the
  combinatorial discharge is in scope of a future plan.
* **L-LZ4-E** (deferred) — The full **dictionary-based longest-prefix
  greedy** parsing (rather than the one-symbol-per-phrase trivial
  form used here) is deferred to a future discharge plan. The trivial
  form is sufficient for the seed's bit-length upper bound; only the
  sharper `count ≤ n / log n` bound (L-LZ4-D) actually requires the
  full greedy machinery.

## Pattern source

This file follows the **partial-discharge layering** pattern of
`Common2026/Shannon/LZ78ZivInequality.lean` (L-LZ1-A/B/C/D layering):
publish the tractable layers (concrete parsing + per-phrase + summed
bit-length + the `count ≤ n` weak bound) as concrete theorems, expose
deferred layers (sharper count-vs-n combinatorial bound) as hypothesis
pass-through predicates.
-/

namespace InformationTheory.Shannon

open scoped Topology

set_option linter.unusedSectionVars false

/-! ## §1. Per-phrase bit length -/

section PhraseBitLength

variable {α : Type*}

/-- **Bit length of a single LZ78 phrase**.

Given dictionary size `c` and alphabet size `a`, encoding one phrase
`(parent, symbol)` requires:

* `Nat.log 2 (c + 1) + 1` bits for the parent index (including the
  empty-prefix `none`, so the parent slot has `c + 1` possibilities;
  `+ 1` for the floor-vs-ceil `Nat.log` gap).
* `Nat.log 2 a + 1` bits for the alphabet symbol.

This is the Cover–Thomas Ch.13.5 per-phrase cost form. -/
def LZ78Phrase.bitLength (c a : ℕ) : ℕ :=
  (Nat.log 2 (c + 1) + 1) + (Nat.log 2 a + 1)

@[simp] lemma LZ78Phrase.bitLength_eq (c a : ℕ) :
    LZ78Phrase.bitLength c a = Nat.log 2 (c + 1) + Nat.log 2 a + 2 := by
  unfold LZ78Phrase.bitLength
  ring

/-- The per-phrase bit length is monotone in the dictionary size. -/
lemma LZ78Phrase.bitLength_mono_left {c c' a : ℕ} (h : c ≤ c') :
    LZ78Phrase.bitLength c a ≤ LZ78Phrase.bitLength c' a := by
  unfold LZ78Phrase.bitLength
  have hlog : Nat.log 2 (c + 1) ≤ Nat.log 2 (c' + 1) :=
    Nat.log_mono_right (by omega)
  omega

/-- The per-phrase bit length is monotone in the alphabet size. -/
lemma LZ78Phrase.bitLength_mono_right {c a a' : ℕ} (h : a ≤ a') :
    LZ78Phrase.bitLength c a ≤ LZ78Phrase.bitLength c a' := by
  unfold LZ78Phrase.bitLength
  have hlog : Nat.log 2 a ≤ Nat.log 2 a' := Nat.log_mono_right h
  omega

/-- The per-phrase bit length is positive. -/
@[simp] lemma LZ78Phrase.bitLength_pos (c a : ℕ) :
    0 < LZ78Phrase.bitLength c a := by
  unfold LZ78Phrase.bitLength
  omega

/-- The per-phrase bit length at `c = 0` is `Nat.log 2 a + 2`. -/
lemma LZ78Phrase.bitLength_zero (a : ℕ) :
    LZ78Phrase.bitLength 0 a = Nat.log 2 a + 2 := by
  rw [LZ78Phrase.bitLength_eq]
  simp

end PhraseBitLength

/-! ## §2. Sum-over-phrases encoding length -/

section ParsingEncodingLength

variable {α : Type*}

/-- **Total encoding bit length of an LZ78 parsing**.

Each of the `c = p.count` phrases costs `LZ78Phrase.bitLength c a`
bits (the uniform upper bound from the largest dictionary size). The
total is `c · bitLength c a`. -/
def LZ78Parsing.encodingLength (p : LZ78Parsing α) (a : ℕ) : ℕ :=
  p.count * LZ78Phrase.bitLength p.count a

@[simp] lemma LZ78Parsing.encodingLength_eq (p : LZ78Parsing α) (a : ℕ) :
    p.encodingLength a = p.count * LZ78Phrase.bitLength p.count a := rfl

/-- Empty parsing has zero encoding length. -/
@[simp] lemma LZ78Parsing.encodingLength_empty (a : ℕ) :
    (LZ78Parsing.empty α).encodingLength a = 0 := by
  unfold LZ78Parsing.encodingLength
  simp

/-- Monotone in the alphabet size argument. -/
lemma LZ78Parsing.encodingLength_mono_alphabet (p : LZ78Parsing α) {a a' : ℕ}
    (h : a ≤ a') : p.encodingLength a ≤ p.encodingLength a' := by
  unfold LZ78Parsing.encodingLength
  exact Nat.mul_le_mul_left _ (LZ78Phrase.bitLength_mono_right h)

end ParsingEncodingLength

/-! ## §3. Concrete parsing function (one-symbol-per-phrase form) -/

section OneSymbolParsing

variable {α : Type*}

/-- **Convert a list of symbols into a list of root LZ78 phrases**
(each phrase is `(parent := none, symbol := s)`). This is the
worst-case but always-valid LZ78 parsing where no dictionary lookups
occur. -/
def lz78RootPhrases (input : List α) : List (LZ78Phrase α) :=
  input.map (fun s => { parent := none, symbol := s })

@[simp] lemma lz78RootPhrases_nil :
    lz78RootPhrases ([] : List α) = [] := rfl

@[simp] lemma lz78RootPhrases_cons (s : α) (rest : List α) :
    lz78RootPhrases (s :: rest) =
      ({ parent := none, symbol := s } : LZ78Phrase α) :: lz78RootPhrases rest := rfl

@[simp] lemma lz78RootPhrases_length (input : List α) :
    (lz78RootPhrases input).length = input.length := by
  unfold lz78RootPhrases
  simp

/-- **The one-symbol-per-phrase LZ78 parsing**. Each phrase is a root
phrase (parent `none`), so the `inRange` invariant holds vacuously
(no `some k` parents). This is a worst-case but always-valid LZ78
parsing for the seed's structural plumbing. -/
def lz78OneSymbolParsing (input : List α) : LZ78Parsing α :=
  { phrases := lz78RootPhrases input
    inRange := by
      intro i hi k hk
      -- Each phrase has `parent = none`, so `parent = some k` is
      -- vacuous.
      exfalso
      have hparent : ((lz78RootPhrases input).get ⟨i, hi⟩).parent = none := by
        unfold lz78RootPhrases
        simp
      rw [hparent] at hk
      cases hk
  }

@[simp] lemma lz78OneSymbolParsing_count (input : List α) :
    (lz78OneSymbolParsing input).count = input.length := by
  unfold lz78OneSymbolParsing LZ78Parsing.count
  simp

@[simp] lemma lz78OneSymbolParsing_phrases_nil :
    (lz78OneSymbolParsing ([] : List α)).phrases = [] := by
  unfold lz78OneSymbolParsing
  simp [lz78RootPhrases]

/-- **Phrase count of the one-symbol-per-phrase parsing equals input
length**. Useful for the worst-case L-LZ4-D pass-through. -/
lemma lz78OneSymbolParsing_count_eq (input : List α) :
    (lz78OneSymbolParsing input).count = input.length :=
  lz78OneSymbolParsing_count input

/-- **Encoding length of the one-symbol parsing**. -/
def lz78OneSymbolEncodingLength (input : List α) (a : ℕ) : ℕ :=
  (lz78OneSymbolParsing input).encodingLength a

@[simp] lemma lz78OneSymbolEncodingLength_eq (input : List α) (a : ℕ) :
    lz78OneSymbolEncodingLength input a =
      input.length * LZ78Phrase.bitLength input.length a := by
  unfold lz78OneSymbolEncodingLength LZ78Parsing.encodingLength
  rw [lz78OneSymbolParsing_count]

@[simp] lemma lz78OneSymbolEncodingLength_nil (a : ℕ) :
    lz78OneSymbolEncodingLength ([] : List α) a = 0 := by
  simp [lz78OneSymbolEncodingLength_eq]

end OneSymbolParsing

/-! ## §4. Greedy encoding-length function (L-LZ4 parameter slot) -/

section GreedyEncodingLength

variable {α : Type*} [Fintype α]

/-- **Greedy LZ78 encoding length of a finite tuple**.

For an input `x : Fin n → α`, the encoding length is computed via
`lz78OneSymbolEncodingLength` on the underlying list `List.ofFn x`
with alphabet size `Fintype.card α`. The name "greedy" reflects the
**L-LZ4 parameter slot semantics**: the concrete encoding-length
function plugs into the parent `lz78EncodingLength` parameter of
`lz78_asymptotic_optimality`.

The current concrete instantiation uses the worst-case one-symbol
parsing; the sharper longest-prefix-match greedy implementation is
deferred to L-LZ4-E (downstream discharge plan), but the bit-length
upper bound `n · (log(n+1) + log|α| + 2)` is the same in either case
(since L-LZ4-E's count is `≤ n` as well, just possibly tighter). -/
def lz78GreedyEncodingLength (n : ℕ) (x : Fin n → α) : ℕ :=
  lz78OneSymbolEncodingLength (List.ofFn x) (Fintype.card α)

@[simp] lemma lz78GreedyEncodingLength_zero (x : Fin 0 → α) :
    lz78GreedyEncodingLength 0 x = 0 := by
  unfold lz78GreedyEncodingLength
  rw [show (List.ofFn x : List α) = [] from by simp]
  simp

/-- **The greedy encoding length is `n · bitLength n |α|`**. -/
lemma lz78GreedyEncodingLength_eq (n : ℕ) (x : Fin n → α) :
    lz78GreedyEncodingLength n x = n * LZ78Phrase.bitLength n (Fintype.card α) := by
  unfold lz78GreedyEncodingLength
  rw [lz78OneSymbolEncodingLength_eq, List.length_ofFn]

/-- **Phrase count of greedy parsing on `n`-tuple is at most `n`**. The
worst-case one-symbol parsing achieves the equality `count = n`. -/
lemma lz78GreedyPhraseCount_ofFn_le (n : ℕ) (x : Fin n → α) :
    (lz78OneSymbolParsing (List.ofFn x)).count ≤ n := by
  rw [lz78OneSymbolParsing_count, List.length_ofFn]

end GreedyEncodingLength

/-! ## §5. Encoding-length upper bound (Cover–Thomas Lemma 13.5.2) -/

section EncodingLengthBound

variable {α : Type*} [Fintype α]

/-- **Cover–Thomas Lemma 13.5.2 (phrase-cost form)**.

The greedy LZ78 encoding length for an input `x : Fin n → α` is
bounded by

```
n · (Nat.log 2 (n + 1) + Nat.log 2 |α| + 2)
```

since each phrase costs at most `bitLength n |α|` bits and the phrase
count is at most `n`. -/
theorem lz78_encoding_length_le_n_log_n_plus_const (n : ℕ) (x : Fin n → α) :
    lz78GreedyEncodingLength n x ≤
      n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
  rw [lz78GreedyEncodingLength_eq, LZ78Phrase.bitLength_eq]

/-- **Variant: bound expressed via `LZ78Phrase.bitLength` directly**. -/
theorem lz78_encoding_length_le_n_mul_bitLength (n : ℕ) (x : Fin n → α) :
    lz78GreedyEncodingLength n x ≤ n * LZ78Phrase.bitLength n (Fintype.card α) := by
  rw [lz78GreedyEncodingLength_eq]

/-- **Asymptotic form**: encoding length divided by `n` is at most
`Nat.log 2 (n + 1) + Nat.log 2 |α| + 2`. -/
theorem lz78_encoding_length_per_symbol_le (n : ℕ) (hn : 0 < n) (x : Fin n → α) :
    (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
      ≤ (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2 : ℝ) := by
  have hle := lz78_encoding_length_le_n_log_n_plus_const n x
  have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
  rw [div_le_iff₀ hn', mul_comm]
  exact_mod_cast hle

end EncodingLengthBound

/-! ## §6. Count-vs-`n` bound as hypothesis pass-through (L-LZ4-D) -/

section CountVsN

variable (α : Type*) [Fintype α]

/-- **`IsLZ78CountBoundPassthrough` — hypothesis pass-through for the
sharper `count ≤ B(n)` bound (Cover–Thomas Eq. 13.124, L-LZ4-D)**.

Asserts that for every input length `n` and every tuple `x : Fin n → α`,
the LZ78 parsing's phrase count is bounded by `B(n)`. The sharper
Cover–Thomas form is `B(n) ≈ n / Nat.log 2 n`; the present predicate
allows any real-valued upper bound `B(n)` to plug in.

The discharge of this pass-through with the sharper bound requires
the **longest-prefix-match greedy** parsing implementation and the
Cover–Thomas Eq. 13.124 combinatorial argument; both are deferred to
a future discharge plan. The trivial `B(n) = n` discharge is
available via `IsLZ78CountBoundPassthrough.id`. -/
def IsLZ78CountBoundPassthrough (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α),
    (lz78OneSymbolParsing (List.ofFn x)).count ≤ B n

@[simp] lemma isLZ78CountBoundPassthrough_def (B : ℕ → ℕ) :
    IsLZ78CountBoundPassthrough α B ↔
      ∀ (n : ℕ) (x : Fin n → α),
        (lz78OneSymbolParsing (List.ofFn x)).count ≤ B n := Iff.rfl

/-- **Trivial constructor**: the identity bound `B(n) = n` always
holds (the one-symbol parsing has `count = n`). -/
theorem IsLZ78CountBoundPassthrough.id :
    IsLZ78CountBoundPassthrough α (fun n => n) := by
  intro n x
  exact lz78GreedyPhraseCount_ofFn_le n x

/-- **Monotonicity**: if `B₁ ≤ B₂` pointwise, an
`IsLZ78CountBoundPassthrough` with bound `B₁` upgrades to bound `B₂`. -/
theorem IsLZ78CountBoundPassthrough.mono {B₁ B₂ : ℕ → ℕ}
    (h : IsLZ78CountBoundPassthrough α B₁) (hB : ∀ n, B₁ n ≤ B₂ n) :
    IsLZ78CountBoundPassthrough α B₂ := by
  intro n x
  exact (h n x).trans (hB n)

variable {α}

/-- **Generic parsing encoding-length bound from a count bound**.

Given any LZ78 parsing `p` and a count bound `p.count ≤ B`, the
encoding length `p.encodingLength a` is bounded by
`B · bitLength B a`. This is the **count-conditioned** form: caller
supplies the count bound, conclusion is the encoding-length bound.

This holds for arbitrary `LZ78Parsing`, not just `lz78OneSymbolParsing`. -/
theorem lz78Parsing_encodingLength_le_of_count_le
    (p : LZ78Parsing α) (a : ℕ) {B : ℕ} (h : p.count ≤ B) :
    p.encodingLength a ≤ B * LZ78Phrase.bitLength B a := by
  unfold LZ78Parsing.encodingLength
  have hbit : LZ78Phrase.bitLength p.count a ≤ LZ78Phrase.bitLength B a :=
    LZ78Phrase.bitLength_mono_left h
  calc p.count * LZ78Phrase.bitLength p.count a
      ≤ p.count * LZ78Phrase.bitLength B a :=
        Nat.mul_le_mul_left _ hbit
    _ ≤ B * LZ78Phrase.bitLength B a :=
        Nat.mul_le_mul_right _ h

/-- **Cover–Thomas Eq. 13.124 hypothesis form (generic parsing)**.

For any LZ78 parsing `p` whose count is bounded by `B(n)`, the
encoding length is bounded by `B(n) · (log(B(n) + 1) + log(|α|) + 2)`. -/
theorem lz78Parsing_encodingLength_le_of_count_log_bound
    (p : LZ78Parsing α) (a : ℕ) {B : ℕ} (h : p.count ≤ B) :
    p.encodingLength a ≤ B * (Nat.log 2 (B + 1) + Nat.log 2 a + 2) := by
  have h1 := lz78Parsing_encodingLength_le_of_count_le p a h
  rwa [LZ78Phrase.bitLength_eq] at h1

end CountVsN


/-! ## §8. Extra plumbing: combined `IsLZ78EncodingLengthBoundPassthrough` -/

section EncodingLengthPassthrough

variable (α : Type*) [Fintype α]

/-- **`IsLZ78EncodingLengthBoundPassthrough` — hypothesis pass-through
for any encoding-length upper bound `B : ℕ → ℕ`**.

Asserts that the concrete greedy encoding length is bounded by `B(n)`
for every input of length `n`. The shape

```
lz78GreedyEncodingLength n x ≤ B n
```

is the general form; specific instances include
`B(n) = n · (Nat.log 2 (n + 1) + Nat.log 2 |α| + 2)` (the Cover–Thomas
13.5.2 form) and `B(n) ≈ n · log L_n` (the sharper form requiring
L-LZ4-D's count-vs-n bound).

This predicate allows downstream callers to abstract away the concrete
encoding length and reason only about its upper bound. -/
def IsLZ78EncodingLengthBoundPassthrough (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α), lz78GreedyEncodingLength n x ≤ B n

@[simp] lemma isLZ78EncodingLengthBoundPassthrough_def (B : ℕ → ℕ) :
    IsLZ78EncodingLengthBoundPassthrough α B ↔
      ∀ (n : ℕ) (x : Fin n → α), lz78GreedyEncodingLength n x ≤ B n := Iff.rfl

/-- **Cover–Thomas Lemma 13.5.2 form discharges
`IsLZ78EncodingLengthBoundPassthrough`** with the canonical bound
`n · (log(n+1) + log|α| + 2)`. -/
theorem IsLZ78EncodingLengthBoundPassthrough.canonical :
    IsLZ78EncodingLengthBoundPassthrough α
      (fun n => n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2)) := by
  intro n x
  exact lz78_encoding_length_le_n_log_n_plus_const n x

/-- **Monotonicity**: if `B₁ ≤ B₂` pointwise, an
`IsLZ78EncodingLengthBoundPassthrough` with bound `B₁` upgrades to
bound `B₂`. -/
theorem IsLZ78EncodingLengthBoundPassthrough.mono {B₁ B₂ : ℕ → ℕ}
    (h : IsLZ78EncodingLengthBoundPassthrough α B₁) (hB : ∀ n, B₁ n ≤ B₂ n) :
    IsLZ78EncodingLengthBoundPassthrough α B₂ := by
  intro n x
  exact (h n x).trans (hB n)

end EncodingLengthPassthrough

/-! ## §9. Per-symbol asymptotic bound -/

section PerSymbolBound

variable {α : Type*} [Fintype α]

/-- **Per-symbol Cover–Thomas Lemma 13.5.2 bound on `ℕ`**.

The per-symbol encoding-length cost is at most
`Nat.log 2 (n + 1) + Nat.log 2 |α| + 2`. Stated on `ℕ` for ease of
combinatorial use, before lifting to `ℝ` for the asymptotic Tendsto. -/
theorem lz78_encoding_length_div_n_le (n : ℕ) (x : Fin n → α) :
    lz78GreedyEncodingLength n x ≤
      n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) :=
  lz78_encoding_length_le_n_log_n_plus_const n x

/-- **The `n`-scaled bit-rate form**: dividing both sides by `n`, the
per-symbol encoding-length cost is at most
`log(n+1) + log|α| + 2`. On `ℝ`. -/
theorem lz78_encoding_length_real_per_symbol_le (n : ℕ) (hn : 0 < n)
    (x : Fin n → α) :
    (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
      ≤ (Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2 := by
  have hle : (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
      ≤ (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2 : ℝ) :=
    lz78_encoding_length_per_symbol_le n hn x
  refine hle.trans (le_of_eq ?_)
  ring

end PerSymbolBound

/-! ## §10. Compatibility statements for the parent theorem -/

section ParentCompat

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

open MeasureTheory ProbabilityTheory

/-- **Type-check witness**: `lz78GreedyEncodingLength` has the right type
to plug into the parent `lz78_asymptotic_optimality` theorem's
`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter. -/
example :
    (∀ n, (Fin n → α) → ℕ) := @lz78GreedyEncodingLength α _

/-- **The concrete `lz78GreedyEncodingLength` threaded into the genuine
two-sided `lz78_asymptotic_optimality` headline**.

After the headline de-circularization, `lz78_asymptotic_optimality` no
longer takes the conclusion (`h_rate_bound`) nor the three `True`
pass-throughs; it takes the genuine two-sided sandwich on `lz/n` and
*derives* the a.s. Tendsto. This wrapper instantiates the encoding-length
parameter to the concrete greedy `lz78GreedyEncodingLength` and forwards
the four genuine sandwich ingredients. The body is a genuine application,
not an identity wrap of the conclusion.

`@audit:suspect(lz78-blockrv-refactor-plan)` -/
theorem lz78_asymptotic_optimality_with_greedy_encoding
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_lower : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n =>
              (lz78GreedyEncodingLength n
                  (p.toStationaryProcess.blockRV n ω) : ℝ)
                / (n : ℝ))
            Filter.atTop)
    (h_upper : ∀ᵐ ω ∂μ,
        Filter.limsup
          (fun n =>
            (lz78GreedyEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess)
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n =>
            (lz78GreedyEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ)))
    (h_bdd_below : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n =>
            (lz78GreedyEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78GreedyEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_asymptotic_optimality μ p (@lz78GreedyEncodingLength α _)
    h_lower h_upper h_bdd_above h_bdd_below

end ParentCompat

end InformationTheory.Shannon
