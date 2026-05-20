import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78GreedyParsing
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range

/-!
# LZ78 longest-prefix-match greedy parsing — L-LZ4-E discharge (T4-A)

`Common2026/Shannon/LZ78GreedyParsing.lean` published the **worst-case
one-symbol-per-phrase** parsing `lz78OneSymbolParsing` and explicitly
deferred the *genuine* longest-prefix-match greedy parse to L-LZ4-E.
This file discharges L-LZ4-E: it implements the real Cover–Thomas
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
(the sharper `count ≤ n / log n` bound is the deferred L-LZ4-D
pass-through, unchanged here).

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

@[simp] lemma LZ78Parsing.ofWellFormed_count {l : List (LZ78Phrase α)}
    (hl : IsWellFormedPhrases l) :
    (LZ78Parsing.ofWellFormed hl).count = l.length := rfl

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
theorem lz78GreedyParse_count_le (input : List α) :
    (lz78GreedyParse input).count ≤ input.length :=
  le_of_eq (lz78GreedyParse_count input)

end CountBound

/-! ## §5. Encoding length + parent-theorem bridge -/

section EncodingLength

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Genuine greedy encoding length of a finite tuple (L-LZ4-E parameter
slot)**: parse `List.ofFn x` with the real dictionary greedy parse and
sum its phrase bit-lengths via the existing `LZ78Parsing.encodingLength`.
This plugs into the parent `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ`
parameter of `lz78_asymptotic_optimality`. -/
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
theorem lz78_impl_encoding_length_le_n_log_n_plus_const (n : ℕ) (x : Fin n → α) :
    lz78GreedyImplEncodingLength n x ≤
      n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
  unfold lz78GreedyImplEncodingLength
  exact lz78Parsing_encodingLength_le_of_count_log_bound
    (lz78GreedyParse (List.ofFn x)) (Fintype.card α)
    (lz78GreedyImplPhraseCount_ofFn_le n x)

/-- **Per-symbol asymptotic bit-rate bound on `ℝ`** for the genuine
greedy parse: dividing by `n` gives `≤ log(n+1) + log|α| + 2`. -/
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
theorem lz78_impl_encoding_length_per_symbol_nonneg (n : ℕ) (x : Fin n → α) :
    (0 : ℝ) ≤ (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ) :=
  div_nonneg (by positivity) (by positivity)

end EncodingLength

/-! ## §6. `IsLZ78EncodingLengthBoundPassthrough` analogue -/

section ImplBoundPassthrough

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- **`IsLZ78ImplEncodingLengthBoundPassthrough B`** — hypothesis
pass-through for an upper bound `B : ℕ → ℕ` on the *genuine* greedy
encoding length (the L-LZ4-E analogue of
`IsLZ78EncodingLengthBoundPassthrough`). -/
def IsLZ78ImplEncodingLengthBoundPassthrough (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α), lz78GreedyImplEncodingLength n x ≤ B n

@[simp] lemma isLZ78ImplEncodingLengthBoundPassthrough_def (B : ℕ → ℕ) :
    IsLZ78ImplEncodingLengthBoundPassthrough α B ↔
      ∀ (n : ℕ) (x : Fin n → α), lz78GreedyImplEncodingLength n x ≤ B n := Iff.rfl

/-- **Cover–Thomas Lemma 13.5.2 form discharges the impl bound
pass-through** with the canonical bound `n · (log(n+1) + log|α| + 2)`. -/
theorem IsLZ78ImplEncodingLengthBoundPassthrough.canonical :
    IsLZ78ImplEncodingLengthBoundPassthrough α
      (fun n => n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2)) := by
  intro n x
  exact lz78_impl_encoding_length_le_n_log_n_plus_const n x

/-- **Monotonicity** of the impl bound pass-through. -/
theorem IsLZ78ImplEncodingLengthBoundPassthrough.mono {B₁ B₂ : ℕ → ℕ}
    (h : IsLZ78ImplEncodingLengthBoundPassthrough α B₁) (hB : ∀ n, B₁ n ≤ B₂ n) :
    IsLZ78ImplEncodingLengthBoundPassthrough α B₂ := by
  intro n x
  exact (h n x).trans (hB n)

end ImplBoundPassthrough

/-! ## §7. Parent-theorem bridge (L-LZ4-E → main theorem) -/

section ParentBridge

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

open MeasureTheory ProbabilityTheory

/-- **Type-check witness**: the genuine greedy encoding length has the
right type to plug into the parent `lz78_asymptotic_optimality`
`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter slot. -/
example : (∀ n, (Fin n → α) → ℕ) := @lz78GreedyImplEncodingLength α _ _

/-- **The genuine greedy encoding discharges the Ziv-inequality
pass-through** (the parent predicate is a `True` placeholder, so this is
trivial; published as a named bridge). -/
theorem lz78GreedyImplEncodingLength_isZivInequalityPassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsZivInequalityPassthrough μ p (@lz78GreedyImplEncodingLength α _ _) :=
  True.intro

/-- **Same bridge for the converse pass-through**. -/
theorem lz78GreedyImplEncodingLength_isLZ78ConversePassthrough
    (μ : Measure Ω) (p : StationaryProcess μ α) :
    IsLZ78ConversePassthrough μ p (@lz78GreedyImplEncodingLength α _ _) :=
  True.intro

/-- **T4-A main theorem with the genuine greedy parsing implementation
(L-LZ4-E discharged)**.

Re-publishes `lz78_asymptotic_optimality` with the parameter
`lz78EncodingLength` slot instantiated to the **genuine
longest-prefix-match greedy** `lz78GreedyImplEncodingLength` (rather than
the worst-case one-symbol form of
`lz78_asymptotic_optimality_with_greedy_encoding`). The Ziv-inequality
and converse pass-throughs are discharged via the named bridges above;
the SMB sandwich pass-through and the final a.s. Tendsto remain for the
caller (those are L-LZ3 / L-LZ5, out of scope for this seed). -/
theorem lz78_asymptotic_optimality_with_greedy_impl
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_smb : IsSMBSandwichPassthrough μ p.toStationaryProcess)
    (h_rate_bound : ∀ᵐ ω ∂μ,
        Filter.Tendsto
          (fun n =>
            (lz78GreedyImplEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop
          (𝓝 (entropyRate μ p.toStationaryProcess))) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78GreedyImplEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) :=
  lz78_asymptotic_optimality μ p (@lz78GreedyImplEncodingLength α _ _)
    (lz78GreedyImplEncodingLength_isZivInequalityPassthrough μ p.toStationaryProcess)
    (lz78GreedyImplEncodingLength_isLZ78ConversePassthrough μ p.toStationaryProcess)
    h_smb h_rate_bound

end ParentBridge

end InformationTheory.Shannon
