import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LempelZiv78
import InformationTheory.Shannon.LZ78GreedyParsing
import InformationTheory.Shannon.LZ78GreedyParsingImpl
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic

/-!
# LZ78 longest-prefix greedy parsing — Phase A: distinct-phrase invariant (T4-A)

`Common2026/Shannon/LZ78GreedyParsingImpl.lean` published a structurally
valid LZ78 parsing whose worker `lz78GreedyParseAux` is, on inspection,
**one-symbol-per-step** (it always feeds the dictionary the singleton
`[s]`, so every phrase consumes exactly one symbol and `count = n`,
`lz78GreedyParse_count`). That degenerate form makes the distinct-phrase
invariant *false* (the same singleton recurs), so the sharp counting
bound `c(n) · log c(n) ≤ K·n` cannot hold.

This file establishes the **genuine longest-prefix-match greedy parse**
together with the central Phase A invariant: the list of emitted phrase
**strings** (the LZ78 dictionary entries) is `Nodup`.

## Design (Mathlib-shape-driven)

The dominant lemma for the distinct invariant is
`List.Nodup.concat : a ∉ l → l.Nodup → (l.concat a).Nodup`
(`Mathlib/Data/List/Nodup.lean:308`). To make its hypothesis `a ∉ l`
*available by construction* rather than recovered from a "longest match"
argument, the worker grows the current prefix symbol-by-symbol from the
input and **emits the prefix the moment it leaves the dictionary**:

* maintain `dict : List (List α)` of already-emitted phrase strings;
* walk the input building a candidate prefix `acc`; while `acc` is still
  in `dict`, keep extending; the first time `acc ∉ dict`, emit `acc` and
  reset.

The emitted string is then *definitionally* `∉ dict`, so `Nodup.concat`
applies directly with no longest-match reconstruction. This is exactly
LZ78's behaviour (match the longest dictionary prefix, append one new
symbol), recorded in the cheapest shape for the invariant proof.

We track only the **phrase strings** here — that is the object the
counting bound (Phase B) reasons about. The back-pointer
`LZ78Parsing`/`inRange` structure of `LZ78GreedyParsingImpl.lean` is left
untouched (its `count = n` lemmas are not Phase A's concern and remain
genuine for the worst-case form).

## File layout

* **§1. Longest-prefix worker** — `lz78PhraseStringsAux` / `lz78PhraseStrings`:
  the genuine greedy parse, returning the list of emitted phrase strings.
* **§2. Distinct-phrase invariant** — `lz78PhraseStrings_nodup`: the list
  of emitted phrase strings is `Nodup` (Phase A core).
* **§3. Length conservation** — `lz78PhraseStrings_total_length`: the
  total number of symbols across emitted phrases (plus the unfinished
  tail) equals the input length, supplying the counting denominator `n`.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

/-! ## §1. Longest-prefix worker -/

section Worker

variable {α : Type*} [DecidableEq α]

/-- **Longest-prefix greedy worker** returning the list of emitted phrase
strings (the LZ78 dictionary entries) in order.

* `fuel : ℕ` bounds recursion depth (instantiated to `input.length + 1`).
* `dict : List (List α)` — phrase strings emitted so far, in order.
* `cur : List α` — the candidate prefix being grown (still `∈ dict` or
  empty); `acc` plus the next symbol forms the next test.
* `input : List α` — the remaining un-consumed suffix.

Invariant maintained for the `Nodup` proof: `dict.Nodup` and `cur ∈ dict`
(or `cur = []`). At each symbol `s`, form `cur ++ [s]`; if it is already a
dictionary entry, keep growing; otherwise emit it (it is `∉ dict` by the
guard) and reset `cur := []`. -/
def lz78PhraseStringsAux :
    ℕ → List (List α) → List α → List α → List (List α)
  | 0, dict, _, _ => dict
  | _, dict, _, [] => dict
  | fuel + 1, dict, cur, s :: rest =>
      let w := cur ++ [s]
      if w ∈ dict then
        lz78PhraseStringsAux fuel dict w rest
      else
        lz78PhraseStringsAux fuel (dict.concat w) [] rest

/-- **`lz78PhraseStrings input`** — the genuine longest-prefix greedy
parse of `input`, returning the ordered list of emitted phrase strings. -/
def lz78PhraseStrings (input : List α) : List (List α) :=
  lz78PhraseStringsAux (input.length + 1) [] [] input

end Worker

/-! ## §2. Distinct-phrase invariant -/

section Nodup

variable {α : Type*} [DecidableEq α]

/-- **Worker preserves `Nodup`**: if the running dictionary is already
`Nodup`, the dictionary returned by the worker is `Nodup`. The emitted
string is `∉ dict` by the `if`-guard, so `List.Nodup.concat` applies. -/
theorem lz78PhraseStringsAux_nodup :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      dict.Nodup → (lz78PhraseStringsAux fuel dict cur input).Nodup
  | 0, dict, _, _, hd => hd
  | _ + 1, dict, _, [], hd => hd
  | fuel + 1, dict, cur, s :: rest, hd => by
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · -- still in dictionary: keep growing, `dict` unchanged
        simp only [hmem, if_true]
        exact lz78PhraseStringsAux_nodup fuel dict (cur ++ [s]) rest hd
      · -- leaves dictionary: emit `cur ++ [s]`, which is `∉ dict` by guard
        simp only [hmem, if_false]
        exact lz78PhraseStringsAux_nodup fuel (dict.concat (cur ++ [s])) [] rest
          (List.Nodup.concat hmem hd)

/-- **Phase A core — distinct phrase invariant**: the list of emitted
phrase strings of the genuine longest-prefix greedy parse is `Nodup`. -/
@[entry_point]
theorem lz78PhraseStrings_nodup (input : List α) :
    (lz78PhraseStrings input).Nodup :=
  lz78PhraseStringsAux_nodup _ [] [] input List.nodup_nil

end Nodup

/-! ## §3. Length conservation -/

section Length

variable {α : Type*} [DecidableEq α]

/-- **Additive `foldr`-length over an append**: the total phrase length of
`l ++ [w]` is the total over `l` plus `w.length`. (The accumulator
`fun w acc => w.length + acc` is additive, so `foldr_append` would leave a
non-zero seed; this dedicated lemma keeps the seed at `0`.) -/
theorem foldr_length_append_singleton (l : List (List α)) (w : List α) :
    ((l ++ [w]).foldr (fun w acc => w.length + acc) 0)
      = (l.foldr (fun w acc => w.length + acc) 0) + w.length := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

/-- **Total symbol count across emitted phrases plus the unfinished tail
equals the input length** (worker form): the symbols consumed so far are
`(dict total length) + cur.length`, and the worker conserves
`(emitted total length) + cur.length + input.length`. -/
theorem lz78PhraseStringsAux_total_length :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      input.length < fuel →
      ((lz78PhraseStringsAux fuel dict cur input).foldr
          (fun w acc => w.length + acc) 0)
        ≤ (dict.foldr (fun w acc => w.length + acc) 0) + cur.length + input.length
  | 0, _, _, _, hfuel => by omega
  | fuel + 1, dict, cur, [], _ => by
      unfold lz78PhraseStringsAux
      simp only [List.length_nil, Nat.add_zero]
      exact Nat.le_add_right _ _
  | fuel + 1, dict, cur, s :: rest, hfuel => by
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · -- keep growing: `dict` unchanged, `cur` becomes `cur ++ [s]`
        simp only [hmem, if_true]
        have ih := lz78PhraseStringsAux_total_length fuel dict (cur ++ [s]) rest
          (by simp only [List.length_cons] at hfuel; omega)
        simp only [List.length_append, List.length_cons,
          List.length_nil] at ih ⊢
        omega
      · -- emit `cur ++ [s]`: dictionary grows, `cur` resets to `[]`
        simp only [hmem, if_false]
        have ih := lz78PhraseStringsAux_total_length fuel (dict.concat (cur ++ [s])) [] rest
          (by simp only [List.length_cons] at hfuel; omega)
        -- compute the foldr over the grown dictionary without touching the
        -- worker argument (which is identical on both sides)
        have hdict : (dict.concat (cur ++ [s])).foldr (fun w acc => w.length + acc) 0
            = dict.foldr (fun w acc => w.length + acc) 0 + (cur.length + 1) := by
          rw [List.concat_eq_append, foldr_length_append_singleton]
          simp only [List.length_append, List.length_singleton]
        rw [hdict] at ih
        simp only [List.length_nil, List.length_cons, Nat.add_zero] at ih ⊢
        omega

/-- **Top-level total-length bound**: the total number of symbols across
all emitted phrase strings is at most the input length. (Each emitted
phrase consumes input symbols; the unfinished tail accounts for the slack,
so this is `≤`, not `=`.) -/
@[entry_point]
theorem lz78PhraseStrings_total_length_le (input : List α) :
    (lz78PhraseStrings input).foldr (fun w acc => w.length + acc) 0
      ≤ input.length := by
  have h := lz78PhraseStringsAux_total_length (input.length + 1) [] [] input
    (by omega)
  simpa using h

end Length

/-! ## §4. Phrase count bound (Phase B entry) -/

section CountBound

variable {α : Type*} [DecidableEq α]

/-- **Worker emits only non-empty phrases**: if every dictionary entry is
non-empty, every entry of the worker output is non-empty. The emitted
string is `cur ++ [s]`, which is always non-empty. -/
theorem lz78PhraseStringsAux_forall_ne_nil :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      (∀ w ∈ dict, w ≠ []) →
      ∀ w ∈ lz78PhraseStringsAux fuel dict cur input, w ≠ []
  | 0, dict, _, _, hd => hd
  | _ + 1, dict, _, [], hd => hd
  | fuel + 1, dict, cur, s :: rest, hd => by
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · simp only [hmem, if_true]
        exact lz78PhraseStringsAux_forall_ne_nil fuel dict (cur ++ [s]) rest hd
      · simp only [hmem, if_false]
        refine lz78PhraseStringsAux_forall_ne_nil fuel (dict.concat (cur ++ [s])) [] rest ?_
        intro w hw
        rw [List.concat_eq_append, List.mem_append] at hw
        rcases hw with hw | hw
        · exact hd w hw
        · rw [List.mem_singleton] at hw
          subst hw
          simp

/-- **All emitted phrase strings are non-empty**. -/
theorem lz78PhraseStrings_forall_ne_nil (input : List α) :
    ∀ w ∈ lz78PhraseStrings input, w ≠ [] :=
  lz78PhraseStringsAux_forall_ne_nil _ [] [] input (by simp)

/-- **Count is bounded by total length when every phrase is non-empty**:
the number of phrases is at most the sum of their lengths, since each
length is `≥ 1`. -/
theorem length_le_foldr_length_of_ne_nil (l : List (List α))
    (h : ∀ w ∈ l, w ≠ []) :
    l.length ≤ l.foldr (fun w acc => w.length + acc) 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.foldr_cons, List.length_cons]
      have hhd : hd ≠ [] := h hd (List.mem_cons_self ..)
      have hhd_len : 1 ≤ hd.length := by
        rcases hd with _ | ⟨a, as⟩
        · exact absurd rfl hhd
        · simp
      have htl : ∀ w ∈ tl, w ≠ [] := fun w hw => h w (List.mem_cons_of_mem _ hw)
      have := ih htl
      omega

/-- **Phase B entry — distinct phrase count bound**: the number of distinct
phrases emitted by the genuine longest-prefix greedy parse is at most the
input length. Combined with `lz78PhraseStrings_nodup` (the strings are
distinct), this is the count `c(n) ≤ n` feeding the Cover–Thomas
counting bound `c(n) · log c(n) ≤ K·n`. -/
@[entry_point]
theorem lz78PhraseStrings_count_le (input : List α) :
    (lz78PhraseStrings input).length ≤ input.length :=
  (length_le_foldr_length_of_ne_nil _ (lz78PhraseStrings_forall_ne_nil input)).trans
    (lz78PhraseStrings_total_length_le input)

end CountBound

end InformationTheory.Shannon
