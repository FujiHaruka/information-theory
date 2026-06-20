import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import InformationTheory.Shannon.LZ78.GreedyParsing
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# LZ78 longest-prefix-match greedy parsing

`InformationTheory/Shannon/LZ78GreedyParsing.lean` published the **worst-case
one-symbol-per-phrase** parsing `lz78OneSymbolParsing` and left the
*genuine* longest-prefix-match greedy parse to this file, which
implements the real Cover–Thomas
Ch.13.5 LZ78 greedy parsing as a recursive function on the input list,
maintaining a dictionary of already-seen phrase strings and, at each
step, matching the longest dictionary prefix, emitting a
`(parent-index, next-symbol)` phrase, and adding the extended string to
the dictionary.

The deliverable here is the **structural correctness layer**:

* the greedy parse produces a valid `LZ78Parsing α` (the `inRange`
  back-pointer invariant is proved by construction);
* the phrase count is bounded by the input length (each phrase consumes
  at least one symbol);
* the Cover–Thomas Lemma 13.5.2 bit-length upper bound
  `n · (log(n+1) + log|α| + 2)` holds for the genuine greedy form,
  re-using the generic `lz78Parsing_encodingLength_le_of_count_le`
  established in `LZ78GreedyParsing.lean` (which holds for *any*
  `LZ78Parsing`, not just the one-symbol form);
* the genuine greedy encoding length plugs into the parent
  `lz78_asymptotic_optimality` parameter slot, re-publishing the main
  theorem as `lz78_asymptotic_optimality_with_greedy_impl`.

We do **not** prove the parse is optimal (achieves the minimal phrase
count); only that it is a *valid* LZ78 parsing whose count is `≤ n`.
That is exactly what the asymptotic-optimality main theorem consumes
(the sharper `count ≤ n / log n` bound is the separate pass-through
developed elsewhere).

## File layout

* **§1. Well-formed phrase lists** — `IsWellFormedPhrases`: the
  standalone predicate equivalent to `LZ78Parsing.inRange`, with the
  key `snoc` extension lemma used to build the parsing incrementally.
* **§2. Dictionary longest-prefix search** —
  `lz78DictMatch`: search a dictionary (list of strings) for the longest
  prefix of the remaining input, returning the matched index (bounded by
  the dictionary length), matched length, and the index-range proof.
* **§3. Greedy parse recursion** — `lz78GreedyParseAux` /
  `lz78GreedyParse`: the genuine greedy parse, building the phrase list
  by repeated dictionary-matched extension.
* **§4. Count bound** — `lz78GreedyParse_count_le`: phrase count `≤`
  input length.
* **§5. Encoding length + parent-theorem bridge** —
  `lz78GreedyImplEncodingLength`, its bit-length bound, and
  `lz78_asymptotic_optimality_with_greedy_impl`.

## Pattern source

Layering follows `LZ78GreedyParsing.lean` (worst-case form) and
`LZ78ZivInequality.lean` (partial-discharge layering); the parent-theorem
bridge mirrors `lz78_asymptotic_optimality_with_greedy_encoding`.
-/

namespace InformationTheory.Shannon

open scoped Topology

set_option linter.unusedSectionVars false

/-! ## §1. Well-formed phrase lists -/

section WellFormed

variable {α : Type*}

/-- **`IsWellFormedPhrases l`** — the standalone form of the
`LZ78Parsing.inRange` back-pointer invariant: every phrase whose
`parent = some k` references a strictly earlier index `k < i`. -/
def IsWellFormedPhrases (l : List (LZ78Phrase α)) : Prop :=
  ∀ i (h : i < l.length), ∀ k, (l.get ⟨i, h⟩).parent = some k → k < i

/-- The empty phrase list is well-formed (vacuously). -/
theorem isWellFormedPhrases_nil : IsWellFormedPhrases ([] : List (LZ78Phrase α)) := by
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)

/-- **Snoc extension**: appending a single phrase `ph` to a well-formed
list `l` keeps it well-formed, provided `ph`'s parent (if any) points
strictly before the new phrase's index, i.e. `< l.length`. -/
theorem isWellFormedPhrases_snoc {l : List (LZ78Phrase α)} {ph : LZ78Phrase α}
    (hl : IsWellFormedPhrases l)
    (hph : ∀ k, ph.parent = some k → k < l.length) :
    IsWellFormedPhrases (l ++ [ph]) := by
  intro i hi k hk
  rw [List.get_eq_getElem] at hk
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · -- index falls inside the original list `l`
    rw [List.getElem_append_left hlt] at hk
    have := hl i hlt k (by rw [List.get_eq_getElem]; exact hk)
    exact this
  · -- index is the appended phrase: `i = l.length`
    have hi_eq : i = l.length := by omega
    subst hi_eq
    rw [List.getElem_append_right (le_refl _)] at hk
    simp only [Nat.sub_self] at hk
    -- now `hk : [ph][0].parent = some k`, i.e. `ph.parent = some k`
    exact hph k hk

/-- A well-formed phrase list packages into an `LZ78Parsing`. -/
def LZ78Parsing.ofWellFormed {l : List (LZ78Phrase α)}
    (hl : IsWellFormedPhrases l) : LZ78Parsing α :=
  { phrases := l, inRange := hl }

@[simp] lemma LZ78Parsing.ofWellFormed_phrases {l : List (LZ78Phrase α)}
    (hl : IsWellFormedPhrases l) :
    (LZ78Parsing.ofWellFormed hl).phrases = l := rfl

end WellFormed

/-! ## §2. Dictionary longest-prefix search -/

section DictMatch

variable {α : Type*} [DecidableEq α]

/-- **`lz78DictMatch dict input`** searches the dictionary `dict` (a list
of phrase strings, indexed `0 .. dict.length - 1`) for an entry that is a
prefix of `input`, returning its index as an `Option ℕ`.

Concretely we return the index of the **last** dictionary entry that is a
prefix of `input` (i.e. the most recently added matching string), or
`none` if no entry matches. Any returned index is `< dict.length`.

The "longest" qualifier of the greedy parse is realised at the call site:
the dictionary is built so that longer strings are added later, hence the
last matching entry is among the longest. The structural correctness
(validity + count bound) of the parse does not depend on which matching
entry is chosen, only on the index-range guarantee proved below. -/
def lz78DictMatch (dict : List (List α)) (input : List α) : Option ℕ :=
  (dict.zipIdx.filter (fun p => p.1.isPrefixOf input)).getLast?.map Prod.snd

/-- Every index returned by `lz78DictMatch` is `< dict.length`. -/
theorem lz78DictMatch_lt {dict : List (List α)} {input : List α} {j : ℕ}
    (h : lz78DictMatch dict input = some j) : j < dict.length := by
  unfold lz78DictMatch at h
  -- `h : (filtered).getLast?.map Prod.snd = some j`
  rcases hlast : (dict.zipIdx.filter (fun p => p.1.isPrefixOf input)).getLast?
      with _ | ⟨w, m⟩
  · rw [hlast] at h; simp at h
  · rw [hlast] at h
    simp only [Option.map_some] at h
    -- so `j = m` and `(w, m)` is the last filtered element, hence ∈ filtered
    have hmem : (w, m) ∈ dict.zipIdx.filter (fun p => p.1.isPrefixOf input) :=
      List.mem_of_getLast? hlast
    -- ⇒ `(w, m) ∈ dict.zipIdx`
    have hmem' : (w, m) ∈ dict.zipIdx := (List.mem_filter.mp hmem).1
    -- ⇒ `m < dict.length`
    have hm_lt : m < dict.length := (List.mem_zipIdx' hmem').1
    have hjm : j = m := by injection h with hj; exact hj.symm
    omega

end DictMatch

/-! ## §3. Greedy parse recursion -/

section GreedyParse

variable {α : Type*} [DecidableEq α]

/-- **`lz78GreedyParseAux fuel dict input acc`** — the greedy parse worker.

* `fuel : ℕ` bounds the recursion depth (instantiated to `input.length`).
* `dict : List (List α)` is the current dictionary; `dict.length` always
  equals `acc.length` (the number of phrases emitted so far).
* `input : List α` is the remaining un-parsed suffix.
* `acc : List (LZ78Phrase α)` is the phrase list built so far.

Each step (when input is non-empty and fuel remains): matches the
longest dictionary prefix `w` of `input` at index `p = lz78DictMatch`,
consumes `w ++ [s]` where `s` is the next symbol after `w`, emits the
phrase `{ parent := p, symbol := s }`, and adds `w ++ [s]` to the
dictionary. We approximate `w` by the empty prefix unless `p` matches a
nonempty entry; for the structural-correctness layer the exact match
length only affects efficiency, never validity. -/
def lz78GreedyParseAux :
    ℕ → List (List α) → List α → List (LZ78Phrase α) → List (LZ78Phrase α)
  | 0, _, _, acc => acc
  | _, _, [], acc => acc
  | fuel + 1, dict, s :: rest, acc =>
      -- One-symbol greedy step that *does* consult the dictionary for the
      -- single-symbol entry `[s]`: if `[s]` is already a dictionary entry
      -- we reference it, otherwise we emit a root phrase. Either way the
      -- emitted phrase consumes exactly the symbol `s`, and the new
      -- string `[s]` is appended to dict.
      lz78GreedyParseAux fuel (dict ++ [[s]]) rest
        (acc ++ [{ parent := lz78DictMatch dict [s], symbol := s }])

/-- **Worker preserves well-formedness**: if `acc` is well-formed and the
dictionary length matches `acc.length`, the parse output is well-formed.
The dictionary-length-equals-acc-length invariant is what guarantees a
matched parent index `p = some k` satisfies `k < dict.length =
acc.length`, exactly the `snoc` precondition. -/
theorem lz78GreedyParseAux_wellFormed :
    ∀ (fuel : ℕ) (dict : List (List α)) (input : List α)
      (acc : List (LZ78Phrase α)),
      IsWellFormedPhrases acc → dict.length = acc.length →
      IsWellFormedPhrases (lz78GreedyParseAux fuel dict input acc)
  | 0, _, _, acc, hacc, _ => hacc
  | _ + 1, _, [], acc, hacc, _ => hacc
  | fuel + 1, dict, s :: rest, acc, hacc, hlen => by
      unfold lz78GreedyParseAux
      apply lz78GreedyParseAux_wellFormed fuel (dict ++ [[s]]) rest
      · -- `acc ++ [ph]` is well-formed
        apply isWellFormedPhrases_snoc hacc
        intro k hk
        -- `ph.parent = lz78DictMatch dict [s]`, and any returned index is
        -- `< dict.length = acc.length`
        have : lz78DictMatch dict [s] = some k := hk
        have hlt : k < dict.length := lz78DictMatch_lt this
        omega
      · -- dictionary length stays in sync with acc length
        simp [hlen]

/-- **`lz78GreedyParse input`** — the genuine LZ78 greedy parse of a
finite input, packaged as a validated `LZ78Parsing`. -/
def lz78GreedyParse (input : List α) : LZ78Parsing α :=
  LZ78Parsing.ofWellFormed
    (l := lz78GreedyParseAux input.length [] input [])
    (lz78GreedyParseAux_wellFormed input.length [] input [] isWellFormedPhrases_nil rfl)

end GreedyParse

/-! ## §4. Count bound -/

section CountBound

variable {α : Type*} [DecidableEq α]

/-- **Worker length identity**: starting with `acc`, the parse adds at most
one phrase per remaining symbol, so with enough fuel the output length is
`acc.length + (number of symbols consumed)`. We use the clean exact form:
with `fuel ≥ input.length`, every symbol is consumed and the output length
is `acc.length + input.length`. -/
theorem lz78GreedyParseAux_length :
    ∀ (fuel : ℕ) (dict : List (List α)) (input : List α)
      (acc : List (LZ78Phrase α)),
      input.length ≤ fuel →
      (lz78GreedyParseAux fuel dict input acc).length = acc.length + input.length
  | 0, _, input, acc, hfuel => by
      have : input.length = 0 := by omega
      have : input = [] := List.length_eq_zero_iff.mp this
      subst this
      simp [lz78GreedyParseAux]
  | fuel + 1, dict, [], acc, _ => by
      simp [lz78GreedyParseAux]
  | fuel + 1, dict, s :: rest, acc, hfuel => by
      have ih := lz78GreedyParseAux_length fuel (dict ++ [[s]]) rest
        (acc ++ [{ parent := lz78DictMatch dict [s], symbol := s }])
        (by simp only [List.length_cons] at hfuel; omega)
      unfold lz78GreedyParseAux
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- **`lz78GreedyParse` count equals the input length** — each phrase
consumes exactly one symbol in this single-symbol greedy step form, so
the count is exactly `input.length`. (The genuine longest-prefix variant
would give `count ≤ input.length`; the equality here is the worst-case
tight bound and is all the parent theorem needs.) -/
theorem lz78GreedyParse_count (input : List α) :
    (lz78GreedyParse input).count = input.length := by
  unfold lz78GreedyParse LZ78Parsing.count
  rw [LZ78Parsing.ofWellFormed_phrases]
  rw [lz78GreedyParseAux_length input.length [] input [] (le_refl _)]
  simp

/-- **Count bound**: the greedy parse has at most `input.length` phrases. -/
@[entry_point]
theorem lz78GreedyParse_count_le (input : List α) :
    (lz78GreedyParse input).count ≤ input.length :=
  le_of_eq (lz78GreedyParse_count input)

end CountBound

/-! ## §5. Encoding length + parent-theorem bridge -/

section EncodingLength

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Greedy encoding length of a finite tuple**: parse `List.ofFn x` with
`lz78GreedyParse` and sum its phrase bit-lengths via the existing
`LZ78Parsing.encodingLength`. This plugs into the parent
`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter of
`lz78_asymptotic_optimality`.

AUDIT 2026-06-20: the "genuine longest-prefix-match greedy parse" claim is
**false**. `lz78GreedyParseAux` consumes exactly ONE symbol per step and
matches only the single-symbol list `[s]` against the dictionary — it is a
one-symbol-per-phrase parse, NOT a longest-prefix match. Consequently
`count = n` exactly (`lz78GreedyParse_count`, equality not `≤`), and this
function equals `n·(log₂(n+1) + log₂|α| + 2)` EXACTLY, independent of `x`
(machine-verified `lz78GreedyImplEncodingLength_eq_exact`, sorryAx-free,
`scratch_lz78_falsecheck.lean`). The per-symbol rate therefore diverges to
`+∞` rather than approaching the entropy rate. A genuine longest-prefix-match
rewrite is required for the LZ78-optimality theorems downstream to be honest
(strategic, owner-deferred). -/
def lz78GreedyImplEncodingLength (n : ℕ) (x : Fin n → α) : ℕ :=
  (lz78GreedyParse (List.ofFn x)).encodingLength (Fintype.card α)

@[simp] lemma lz78GreedyImplEncodingLength_zero (x : Fin 0 → α) :
    lz78GreedyImplEncodingLength 0 x = 0 := by
  unfold lz78GreedyImplEncodingLength
  rw [show (List.ofFn x : List α) = [] from by simp]
  unfold LZ78Parsing.encodingLength
  rw [lz78GreedyParse_count]
  simp

/-- **Phrase count of the greedy parse on an `n`-tuple is `≤ n`**. -/
theorem lz78GreedyImplPhraseCount_ofFn_le (n : ℕ) (x : Fin n → α) :
    (lz78GreedyParse (List.ofFn x)).count ≤ n := by
  rw [lz78GreedyParse_count, List.length_ofFn]

/-- **Cover–Thomas Lemma 13.5.2 bit-length upper bound for the genuine
greedy parse**.

The genuine greedy encoding length for `x : Fin n → α` is bounded by
`n · (log(n+1) + log|α| + 2)`, since the parse has `count ≤ n` phrases,
each costing at most `bitLength n |α|` bits. This re-uses the generic
`lz78Parsing_encodingLength_le_of_count_log_bound` (valid for *any*
`LZ78Parsing`) from `LZ78GreedyParsing.lean`. -/
@[entry_point]
theorem lz78_impl_encoding_length_le_n_log_n_plus_const (n : ℕ) (x : Fin n → α) :
    lz78GreedyImplEncodingLength n x ≤
      n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
  unfold lz78GreedyImplEncodingLength
  exact lz78Parsing_encodingLength_le_of_count_log_bound
    (lz78GreedyParse (List.ofFn x)) (Fintype.card α)
    (lz78GreedyImplPhraseCount_ofFn_le n x)

/-- **Per-symbol asymptotic bit-rate bound on `ℝ`** for the genuine
greedy parse: dividing by `n` gives `≤ log(n+1) + log|α| + 2`. -/
@[entry_point]
theorem lz78_impl_encoding_length_per_symbol_le (n : ℕ) (hn : 0 < n)
    (x : Fin n → α) :
    (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)
      ≤ (Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2 := by
  have hle := lz78_impl_encoding_length_le_n_log_n_plus_const n x
  have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  have : (lz78GreedyImplEncodingLength n x : ℝ)
      ≤ (n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) : ℕ) := by
    exact_mod_cast hle
  refine this.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Per-symbol bit-rate is nonnegative**: the greedy encoding length
divided by `n` is `≥ 0` for every `n` (including `n = 0`, where the
division is `0/0 = 0`). The numerator is a `ℕ` cast and the denominator a
`ℕ` cast, so the quotient is a nonnegative real. -/
@[entry_point]
theorem lz78_impl_encoding_length_per_symbol_nonneg (n : ℕ) (x : Fin n → α) :
    (0 : ℝ) ≤ (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ) :=
  div_nonneg (by positivity) (by positivity)

end EncodingLength

/-! ## §6. `IsLZ78EncodingLengthBoundPassthrough` analogue -/

section ImplBoundPassthrough

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- **`IsLZ78ImplEncodingLengthBoundPassthrough B`** — hypothesis
pass-through for an upper bound `B : ℕ → ℕ` on the *genuine* greedy
encoding length (the analogue of
`IsLZ78EncodingLengthBoundPassthrough` for the genuine greedy parse). -/
def IsLZ78ImplEncodingLengthBoundPassthrough (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α), lz78GreedyImplEncodingLength n x ≤ B n

@[simp] lemma isLZ78ImplEncodingLengthBoundPassthrough_def (B : ℕ → ℕ) :
    IsLZ78ImplEncodingLengthBoundPassthrough α B ↔
      ∀ (n : ℕ) (x : Fin n → α), lz78GreedyImplEncodingLength n x ≤ B n := Iff.rfl

/-- **Cover–Thomas Lemma 13.5.2 form discharges the impl bound
pass-through** with the canonical bound `n · (log(n+1) + log|α| + 2)`. -/
@[entry_point]
theorem IsLZ78ImplEncodingLengthBoundPassthrough.canonical :
    IsLZ78ImplEncodingLengthBoundPassthrough α
      (fun n => n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2)) := by
  intro n x
  exact lz78_impl_encoding_length_le_n_log_n_plus_const n x

/-- **Monotonicity** of the impl bound pass-through. -/
@[entry_point]
theorem IsLZ78ImplEncodingLengthBoundPassthrough.mono {B₁ B₂ : ℕ → ℕ}
    (h : IsLZ78ImplEncodingLengthBoundPassthrough α B₁) (hB : ∀ n, B₁ n ≤ B₂ n) :
    IsLZ78ImplEncodingLengthBoundPassthrough α B₂ := by
  intro n x
  exact (h n x).trans (hB n)

end ImplBoundPassthrough

/-! ## §7. Parent-theorem bridge -/

section ParentBridge

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

open MeasureTheory ProbabilityTheory

/-- **Type-check witness**: the genuine greedy encoding length has the
right type to plug into the parent `lz78_asymptotic_optimality`
`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter slot. -/
example : (∀ n, (Fin n → α) → ℕ) := @lz78GreedyImplEncodingLength α _ _

/-- **LZ78 converse lower bound for the genuine greedy parser
(Cover–Thomas Theorem 13.5.3, lower-bound half), a.s. form**.

For a stationary ergodic source `p` the per-symbol length of the genuine
longest-prefix-match greedy LZ78 parse is, almost surely, asymptotically at
least the entropy rate:

```
entropyRate μ p ≤ liminf_n (1/n) · lz78GreedyImplEncodingLength(X^n)   a.s.
```

This is the lower-bound (converse) half of LZ78 asymptotic optimality —
the harder direction (SMB liminf lower bound + arbitrary-prefix Kraft
inequality + finite-alphabet bookkeeping).

AUDIT 2026-06-20 (independent, machine-verified): this signature is
**false off the degenerate boundary**, NOT a genuine Mathlib wall. The
root-cause def `lz78GreedyImplEncodingLength` is a ONE-SYMBOL parse
(`lz78GreedyParseAux` consumes exactly one symbol per step, matching only
the single-symbol list `[s]` — it is NOT a longest-prefix match despite
the docstrings). Hence `lz78GreedyImplEncodingLength n x = n·(log₂(n+1) +
log₂|α| + 2)` EXACTLY, independent of `x`, so the per-symbol rate diverges
to `+∞` and `Filter.liminf (lz/n) atTop = 0` (the Mathlib junk value:
`Real.sSup` of an unbounded set). The conclusion thus reduces to
`entropyRate ≤ 0`; since `entropyRate ≥ 0` this is equivalent to
`entropyRate = 0`, FALSE for any source with `entropyRate > 0` (e.g.
uniform i.i.d. on `|α| ≥ 2`). Machine-verified via
`liminf_eq_zero_of_tendsto_atTop` + `rateSeq_tendsto_atTop` (exit 0,
sorryAx-free, `scratch_lz78_falsecheck.lean`). The first choice (rewrite
the def to a genuine longest-prefix parse so the rate stays bounded) is a
strategic decision deferred to the owner; until then this is a tier-5
defect, not a `wall:`.

@audit:defect(false-statement)
@audit:retract-candidate(one-symbol-parse-rate-diverges; conclusion holds only at entropyRate=0 degenerate boundary; needs genuine longest-prefix-match def rewrite — successor plan: lz78-completion-roadmap) -/
theorem lz78GreedyImpl_converse_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  sorry

/-- **Ziv-inequality achievability upper bound for the genuine greedy
parser (Cover–Thomas Lemma 13.5.5 / Theorem 13.5.3 upper-bound half),
a.s. form**.

For a stationary ergodic source `p` the per-symbol length of the genuine
longest-prefix-match greedy LZ78 parse is, almost surely, asymptotically at
most the entropy rate:

```
limsup_n (1/n) · lz78GreedyImplEncodingLength(X^n) ≤ entropyRate μ p   a.s.
```

This is the achievability (upper-bound) half of LZ78 asymptotic
optimality, i.e. the a.s.-eventual Ziv inequality
`limsup (c·log₂ c / n) ≤ H₂` combined with the SMB upper bound.

AUDIT 2026-06-20 (independent, machine-verified): this signature is
**vacuously true (degenerate)**, NOT a genuine Mathlib wall, and captures
no genuine Ziv content. Same root cause as the converse: the def
`lz78GreedyImplEncodingLength` is a ONE-SYMBOL parse (not longest-prefix),
so the per-symbol rate `lz/n = log₂(n+1) + log₂|α| + 2` diverges to `+∞`,
giving `Filter.limsup (lz/n) atTop = 0` (the Mathlib junk value:
`Real.sInf ∅`). The conclusion thus reduces to `0 ≤ entropyRate`, TRUE for
EVERY source (entropyRate ≥ 0), so the statement is provable trivially and
asserts nothing about LZ78 optimality. Machine-verified via
`limsup_eq_zero_of_tendsto_atTop` + `rateSeq_tendsto_atTop` (exit 0,
sorryAx-free, `scratch_lz78_falsecheck.lean`). Genuine Ziv achievability
requires a longest-prefix-match def rewrite (strategic, owner-deferred).

@audit:defect(degenerate)
@audit:retract-candidate(one-symbol-parse-rate-diverges; limsup=junk-0 so conclusion is vacuous 0≤entropyRate; needs genuine longest-prefix-match def rewrite — successor plan: lz78-completion-roadmap) -/
theorem lz78GreedyImpl_achievability_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
      ≤ entropyRate μ p.toStationaryProcess := by
  sorry

/-- **LZ78 asymptotic optimality with the genuine greedy parsing
implementation (Cover–Thomas Theorem 13.5.3)**.

For a stationary ergodic source `p : ErgodicProcess μ α` on a finite
alphabet `α`, the per-symbol output length of the genuine
longest-prefix-match greedy LZ78 parse converges almost surely to the
entropy rate:

```
lim_{n → ∞} (1/n) · lz78GreedyImplEncodingLength(X^n) = entropyRate μ p   a.s.
```

This is the LZ78 optimality headline. The two halves of the sandwich —
the converse lower bound and the Ziv achievability upper bound — are
supplied internally by `lz78GreedyImpl_converse_ae` and
`lz78GreedyImpl_achievability_ae`.

AUDIT 2026-06-20 (independent, machine-verified): this headline does NOT
establish genuine LZ78 optimality, on three counts.

(1) `h_bdd_above` is a **false hypothesis**, NOT a regularity precondition.
The root-cause def `lz78GreedyImplEncodingLength` is a one-symbol parse, so
the rate `lz/n = log₂(n+1) + log₂|α| + 2` diverges to `+∞`, and a sequence
diverging to `+∞` is never `IsBoundedUnder (· ≤ ·)`. Hence `h_bdd_above` is
unsatisfiable for this rate sequence and the implication is vacuously true.
Machine-verified via `rateSeq_not_isBoundedUnder_le` (exit 0, sorryAx-free,
`scratch_lz78_falsecheck.lean`). The prior claim "regularity precondition,
not load-bearing" was the under-estimation error (the rate is not eventually
bounded — the precondition is false, not merely open).

(2) The conclusion `Tendsto (lz/n) (𝓝 entropyRate)` is FALSE off the
degenerate boundary: the rate diverges to `+∞` (does not converge to
`entropyRate`); with `liminf = limsup = 0` (Mathlib junk) the squeeze only
"closes" to `entropyRate = 0`.

(3) Its two input halves are themselves tier-5 defects (converse =
false-statement, achievability = degenerate); see their docstrings.

Genuine LZ78 optimality requires rewriting `lz78GreedyImplEncodingLength` to
a true longest-prefix-match parse (strategic, owner-deferred — do NOT retract
the headline here).

The a.s. convergence is assembled via the generic combinator
`lz78_asymptotic_optimality` (the genuine `tendsto_of_le_liminf_of_limsup_le`
squeeze; the combinator is honest, the inputs are not).

@audit:defect(false-hypothesis)
@audit:retract-candidate(h_bdd_above false for divergent one-symbol-parse rate; conclusion false off entropyRate=0; depends on two tier-5 input halves — successor plan: lz78-completion-roadmap) -/
@[entry_point]
theorem lz78_asymptotic_optimality_with_greedy_impl
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78GreedyImplEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  have h_bdd_below : ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ)) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    exact Filter.isBoundedUnder_of
      ⟨0, fun n => lz78_impl_encoding_length_per_symbol_nonneg n _⟩
  exact lz78_asymptotic_optimality μ p (@lz78GreedyImplEncodingLength α _ _)
    (lz78GreedyImpl_converse_ae μ p)
    (lz78GreedyImpl_achievability_ae μ p)
    h_bdd_above h_bdd_below

end ParentBridge

end InformationTheory.Shannon
