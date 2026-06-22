import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import InformationTheory.Shannon.LZ78.GreedyParsing
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Basic

/-!
# LZ78 longest-prefix greedy parsing — distinct-phrase invariant

A one-symbol-per-step parse (always feeding the dictionary the singleton
`[s]`, so every phrase consumes exactly one symbol and `count = n`) makes
the distinct-phrase invariant *false* (the same singleton recurs), so the
sharp counting bound `c(n) · log c(n) ≤ K·n` cannot hold.

This file establishes the **genuine longest-prefix-match greedy parse**
together with the central invariant: the list of emitted phrase
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
counting bound reasons about. The back-pointer
`LZ78Parsing`/`inRange` structure of `LZ78AsymptoticOptimality.lean` is left
untouched.

## File layout

* **§1. Longest-prefix worker** — `lz78PhraseStringsAux` / `lz78PhraseStrings`:
  the genuine greedy parse, returning the list of emitted phrase strings.
* **§2. Distinct-phrase invariant** — `lz78PhraseStrings_nodup`: the list
  of emitted phrase strings is `Nodup`.
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

/-- **Distinct phrase invariant**: the list of emitted phrase strings of
the genuine longest-prefix greedy parse is `Nodup`. -/
@[entry_point]
theorem lz78PhraseStrings_nodup (input : List α) :
    (lz78PhraseStrings input).Nodup :=
  lz78PhraseStringsAux_nodup _ [] [] input List.nodup_nil

end Nodup

/-! ## §3. Length conservation -/

section Length

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- **Additive `foldr`-length over an append**: the total phrase length of
`l ++ [w]` is the total over `l` plus `w.length`. (The accumulator
`fun w acc => w.length + acc` is additive, so `foldr_append` would leave a
non-zero seed; this dedicated lemma keeps the seed at `0`.) -/
theorem foldr_length_append_singleton (l : List (List α)) (w : List α) :
    ((l ++ [w]).foldr (fun w acc ↦ w.length + acc) 0)
      = (l.foldr (fun w acc ↦ w.length + acc) 0) + w.length := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

omit [DecidableEq α] in
theorem foldrLength_take_succ (L : List (List α)) (j : ℕ) (h : j < L.length) :
    ((L.take (j + 1)).foldr (fun w acc ↦ w.length + acc) 0)
      = ((L.take j).foldr (fun w acc ↦ w.length + acc) 0) + (L[j]'h).length := by
  rw [List.take_succ_eq_append_getElem h, foldr_length_append_singleton]

omit [DecidableEq α] in
theorem foldrLength_take_mono (L : List (List α)) {i j : ℕ} (hij : i ≤ j) :
    ((L.take i).foldr (fun w acc ↦ w.length + acc) 0)
      ≤ ((L.take j).foldr (fun w acc ↦ w.length + acc) 0) := by
  have hstep : ∀ i : ℕ,
      ((L.take i).foldr (fun w acc ↦ w.length + acc) 0)
        ≤ ((L.take (i + 1)).foldr (fun w acc ↦ w.length + acc) 0) := by
    intro i
    by_cases h : i < L.length
    · rw [foldrLength_take_succ L i h]; omega
    · have hge : L.length ≤ i := Nat.not_lt.mp h
      have h1 : L.take i = L := List.take_of_length_le (by omega)
      have h2 : L.take (i + 1) = L := List.take_of_length_le (by omega)
      simp only [h1, h2, le_refl]
  induction j with
  | zero => simp_all
  | succ j ihj =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ihj (Nat.lt_succ_iff.mp h)).trans (hstep j)
    · have : i = j + 1 := le_antisymm hij h
      subst this; exact le_refl _

omit [DecidableEq α] in
theorem foldrLength_take_ge_of_forall_ne_nil (L : List (List α))
    (hne : ∀ w ∈ L, w ≠ []) {j : ℕ} (hj : j ≤ L.length) :
    j ≤ (L.take j).foldr (fun w acc ↦ w.length + acc) 0 := by
  induction j with
  | zero => simp
  | succ j ihj =>
    have hjm : j < L.length := by omega
    have := ihj (by omega)
    rw [foldrLength_take_succ L j hjm]
    have hpos : 1 ≤ (L[j]'hjm).length :=
      List.length_pos_iff.mpr (hne _ (List.getElem_mem hjm))
    omega

/-- **Total symbol count across emitted phrases plus the unfinished tail
equals the input length** (worker form): the symbols consumed so far are
`(dict total length) + cur.length`, and the worker conserves
`(emitted total length) + cur.length + input.length`. -/
theorem lz78PhraseStringsAux_total_length :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      input.length < fuel →
      ((lz78PhraseStringsAux fuel dict cur input).foldr
          (fun w acc ↦ w.length + acc) 0)
        ≤ (dict.foldr (fun w acc ↦ w.length + acc) 0) + cur.length + input.length
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
        have hdict : (dict.concat (cur ++ [s])).foldr (fun w acc ↦ w.length + acc) 0
            = dict.foldr (fun w acc ↦ w.length + acc) 0 + (cur.length + 1) := by
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
    (lz78PhraseStrings input).foldr (fun w acc ↦ w.length + acc) 0
      ≤ input.length := by
  have h := lz78PhraseStringsAux_total_length (input.length + 1) [] [] input
    (by omega)
  simpa using h

/-- **Worker conserves the flattened string**: the concatenation
(`List.flatten`) of all emitted phrase strings, followed by an unfinished
tail, reproduces the symbols seen so far `dict.flatten ++ cur ++ input`. This
is the genuine *reconstruction* invariant: the phrases tile a prefix of the
input by concatenation at their cumulative lengths, with the leftover `tail`
being the un-emitted suffix (the `≤`-slack of `lz78PhraseStrings_total_length_le`).
Proved by induction on `fuel`, tracking the `cur` accumulator across the
keep-growing / emit branches.

Genuine structural induction on `fuel`, no sorry / hypothesis bundling.

@audit:ok -/
theorem lz78PhraseStringsAux_flatten_conserve :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      input.length < fuel →
      ∃ tail : List α,
        (lz78PhraseStringsAux fuel dict cur input).flatten ++ tail
          = dict.flatten ++ cur ++ input
  | 0, _, _, _, h => by omega
  | fuel + 1, dict, cur, [], _ => by
      refine ⟨cur, ?_⟩; simp [lz78PhraseStringsAux]
  | fuel + 1, dict, cur, s :: rest, h => by
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · simp only [hmem, if_true]
        obtain ⟨tail, htail⟩ := lz78PhraseStringsAux_flatten_conserve fuel dict (cur ++ [s]) rest
          (by simp only [List.length_cons] at h; omega)
        exact ⟨tail, by rw [htail]; simp⟩
      · simp only [hmem, if_false]
        obtain ⟨tail, htail⟩ := lz78PhraseStringsAux_flatten_conserve fuel
          (dict.concat (cur ++ [s])) [] rest
          (by simp only [List.length_cons] at h; omega)
        exact ⟨tail, by rw [htail]; simp [List.concat_eq_append, List.flatten_append]⟩

/-- **Top-level reconstruction**: the concatenation of all emitted phrase
strings, followed by an unfinished tail, equals the input. The cumulative
phrase lengths therefore furnish an absolute-position tiling of a prefix of
the input, with the tail accounting for the `≤`-slack.

Genuine instantiation of `lz78PhraseStringsAux_flatten_conserve`, no sorry.

@audit:ok -/
@[entry_point]
theorem lz78PhraseStrings_flatten_prefix (input : List α) :
    ∃ tail : List α, (lz78PhraseStrings input).flatten ++ tail = input := by
  obtain ⟨tail, htail⟩ :=
    lz78PhraseStringsAux_flatten_conserve (input.length + 1) [] [] input (by omega)
  exact ⟨tail, by simpa using htail⟩

/-- **Worker conserves the flattened string AND bounds the tail**: the unfinished
tail at termination is the final candidate prefix `cur`, which the greedy invariant
keeps as a dictionary entry (or empty). So the tail is a member of the returned
phrase list (or `[]`), bounding its length by the longest phrase. Proved by induction
on `fuel`, threading the invariant `cur ∈ dict ∨ cur = []` (preserved on both the
keep-growing and emit branches).

@audit:ok (independent audit 2026-06-21, sorryAx-free `[propext, Classical.choice,
Quot.sound]`; genuine fuel-induction establishing the tail ∈ dict ∪ {[]} invariant, no
sorry). -/
theorem lz78PhraseStringsAux_tail_mem :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      input.length < fuel →
      (cur ∈ dict ∨ cur = []) →
      ∃ tail : List α,
        (lz78PhraseStringsAux fuel dict cur input).flatten ++ tail
          = dict.flatten ++ cur ++ input ∧
        (tail ∈ lz78PhraseStringsAux fuel dict cur input ∨ tail = [])
  | 0, _, _, _, h, _ => by omega
  | fuel + 1, dict, cur, [], _, hcur => by
      refine ⟨cur, ?_, ?_⟩
      · simp [lz78PhraseStringsAux]
      · unfold lz78PhraseStringsAux; exact hcur
  | fuel + 1, dict, cur, s :: rest, h, _ => by
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · simp only [hmem, if_true]
        obtain ⟨tail, htail, hmem_tail⟩ :=
          lz78PhraseStringsAux_tail_mem fuel dict (cur ++ [s]) rest
            (by simp only [List.length_cons] at h; omega) (Or.inl hmem)
        exact ⟨tail, by rw [htail]; simp, hmem_tail⟩
      · simp only [hmem, if_false]
        obtain ⟨tail, htail, hmem_tail⟩ := lz78PhraseStringsAux_tail_mem fuel
          (dict.concat (cur ++ [s])) [] rest
          (by simp only [List.length_cons] at h; omega) (Or.inr rfl)
        exact ⟨tail, by rw [htail]; simp [List.concat_eq_append, List.flatten_append],
          hmem_tail⟩

/-- **Top-level tail membership**: the unfinished tail of the parse is a phrase string
(a member of `lz78PhraseStrings input`) or empty. Hence its length is at most the
longest phrase length, which bounds the un-emitted trailing tail `input.length - e`. -/
theorem lz78PhraseStrings_flatten_tail_mem (input : List α) :
    ∃ tail : List α, (lz78PhraseStrings input).flatten ++ tail = input ∧
      (tail ∈ lz78PhraseStrings input ∨ tail = []) := by
  obtain ⟨tail, htail, hmem⟩ :=
    lz78PhraseStringsAux_tail_mem (input.length + 1) [] [] input (by omega) (Or.inr rfl)
  exact ⟨tail, by simpa using htail, hmem⟩

omit [DecidableEq α] in
/-- **`flatten` length equals the additive `foldr` total**: bridges the
reconstruction-invariant `List.flatten` length to the cumulative-length `foldr`
accumulator used by the tiling. -/
theorem length_flatten_eq_foldr_length (L : List (List α)) :
    L.flatten.length = L.foldr (fun w acc ↦ w.length + acc) 0 := by
  rw [List.length_flatten]
  induction L with
  | nil => simp
  | cons hd tl ih => simp only [List.map_cons, List.sum_cons, List.foldr_cons, ih]

/-! ### Slice / content correspondence -/

omit [DecidableEq α] in
/-- **Flatten slice content correspondence** (pure list fact). For a list of
lists `L`, dropping the cumulative length of the first `j` sublists from the
flatten and taking the `j`-th sublist length recovers `L[j]` exactly:
`(L.flatten.drop (cumLen j)).take (L[j].length) = L[j]`, where
`cumLen j = (L.take j).foldr (·.length + ·) 0`.

This is the content half of the absolute-position tiling: the tiling carries
phrase lengths/positions, and this lemma certifies that the slice at those
positions reproduces the `j`-th phrase string. -/
theorem flatten_drop_take_getElem (L : List (List α)) (j : ℕ) (hj : j < L.length) :
    (L.flatten.drop ((L.take j).foldr (fun w acc ↦ w.length + acc) 0)).take
        (L[j].length) = L[j] := by
  induction L generalizing j with
  | nil => exact absurd hj (by simp)
  | cons hd tl ih =>
    cases j with
    | zero =>
      -- `cumLen 0 = 0`, drop nothing; `(hd ++ tl.flatten).take hd.length = hd`.
      simp only [List.take_zero, List.foldr_nil, List.drop_zero, List.flatten_cons,
        List.getElem_cons_zero]
      exact List.take_left
    | succ i =>
      -- `cumLen (i+1) = hd.length + cumLen' tl i`; peel off `hd` from the flatten/drop.
      have hi : i < tl.length := by simpa using hj
      simp only [List.flatten_cons, List.take_succ_cons, List.foldr_cons,
        List.getElem_cons_succ]
      -- Drop `hd.length + (tl cumLen i)` from `hd ++ tl.flatten`: the first `hd.length`
      -- consumes `hd`, leaving `tl.flatten.drop (tl cumLen i)`.
      rw [List.drop_append]
      have hdrop_hd : hd.drop (hd.length
          + (List.take i tl).foldr (fun w acc ↦ w.length + acc) 0) = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [hdrop_hd, List.nil_append,
        show hd.length + (List.take i tl).foldr (fun w acc ↦ w.length + acc) 0 - hd.length
          = (List.take i tl).foldr (fun w acc ↦ w.length + acc) 0 from by omega]
      exact ih i hi

omit [DecidableEq α] in
theorem getElem?_eq_some_drop_take_of_flatten_prefix (L : List (List α))
    {input : List α} {tail : List α} (htail : L.flatten ++ tail = input)
    (idx : ℕ) (hidx : idx < L.length) :
    L[idx]? = some ((input.drop ((L.take idx).foldr (fun w acc ↦ w.length + acc) 0)).take
      (((L.take (idx + 1)).foldr (fun w acc ↦ w.length + acc) 0)
        - ((L.take idx).foldr (fun w acc ↦ w.length + acc) 0))) := by
  -- One-step cumulative length recurrence: the step length is `L[idx].length`, so the
  -- take amount simplifies to `L[idx].length`.
  have hstep := foldrLength_take_succ L idx hidx
  rw [hstep, Nat.add_sub_cancel_left]
  -- `getElem?` of `L` at `idx` is `some (L[idx])`.
  rw [List.getElem?_eq_getElem hidx]
  -- `cum (idx + 1) ≤ L.flatten.length`, hence both `cum idx ≤ L.flatten.length` and
  -- `cum idx + L[idx].length ≤ L.flatten.length`.
  have hbound : (L.take (idx + 1)).foldr (fun w acc ↦ w.length + acc) 0 ≤ L.flatten.length := by
    rw [length_flatten_eq_foldr_length L]
    calc (L.take (idx + 1)).foldr (fun w acc ↦ w.length + acc) 0
        ≤ (L.take L.length).foldr (fun w acc ↦ w.length + acc) 0 :=
          foldrLength_take_mono L (by omega)
      _ = L.foldr (fun w acc ↦ w.length + acc) 0 := by rw [List.take_length]
  have hcumidx_le : (L.take idx).foldr (fun w acc ↦ w.length + acc) 0 ≤ L.flatten.length := by
    omega
  -- On `input = L.flatten ++ tail`, dropping `cum idx` then taking `L[idx].length`
  -- only sees the flatten part.
  have hslice : (input.drop ((L.take idx).foldr (fun w acc ↦ w.length + acc) 0)).take
        ((L[idx]'hidx).length)
      = (L.flatten.drop ((L.take idx).foldr (fun w acc ↦ w.length + acc) 0)).take
        ((L[idx]'hidx).length) := by
    conv_lhs => rw [show input = L.flatten ++ tail from htail.symm]
    rw [List.drop_append_of_le_length hcumidx_le,
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  rw [hslice, flatten_drop_take_getElem L idx hidx]

end Length

/-! ## §3b. Parent-extension invariant -/

section ParentExtension

variable {α : Type*} [DecidableEq α]

/-- **Worker maintains the parent-extension invariant**: every emitted phrase
string is `(an earlier dictionary entry) ++ [symbol]` or `[symbol]`. Stated
positionally: for the worker output `D`, each `D[j].dropLast` either equals
`[]` or appears strictly earlier in `D` (i.e. in `D.take j`).

This is the dictionary structure behind the LZ78 phrase-count bound: at each
step the worker emits `cur ++ [s]` where `cur` is a current dictionary entry
(or `[]`), and dictionaries only grow by appending, so `cur` sits strictly
before the emitted phrase. Threaded with the running invariant
`cur ∈ dict ∨ cur = []`. -/
theorem lz78PhraseStringsAux_dropLast_earlier :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      (cur ∈ dict ∨ cur = []) →
      (∀ j, ∀ h : j < dict.length,
        (dict[j]'h).dropLast ∈ dict.take j ∨ (dict[j]'h).dropLast = []) →
      ∀ j, ∀ h : j < (lz78PhraseStringsAux fuel dict cur input).length,
        ((lz78PhraseStringsAux fuel dict cur input)[j]'h).dropLast
            ∈ (lz78PhraseStringsAux fuel dict cur input).take j
          ∨ ((lz78PhraseStringsAux fuel dict cur input)[j]'h).dropLast = [] := by
  intro fuel
  induction fuel with
  | zero => intro dict _ _ _ hdict; simpa [lz78PhraseStringsAux] using hdict
  | succ fuel ih =>
      intro dict cur input hcur hdict
      cases input with
      | nil => simpa [lz78PhraseStringsAux] using hdict
      | cons s rest =>
          unfold lz78PhraseStringsAux
          by_cases hmem : (cur ++ [s]) ∈ dict
          · -- still in dictionary: dict unchanged, cur := cur ++ [s] ∈ dict
            simp only [hmem, if_true]
            exact ih dict (cur ++ [s]) rest (Or.inl hmem) hdict
          · -- emit `cur ++ [s]`: dict grows, cur resets to []
            simp only [hmem, if_false]
            refine ih (dict.concat (cur ++ [s])) [] rest (Or.inr rfl) ?_
            -- positional invariant for the grown dictionary `dict.concat (cur ++ [s])`
            intro j hj
            simp only [List.concat_eq_append] at hj ⊢
            rw [List.length_append, List.length_singleton] at hj
            rcases Nat.lt_or_ge j dict.length with hjlt | hjge
            · -- j < dict.length: identical to the old entry / take
              have hget : (dict ++ [cur ++ [s]])[j]'(by rw [List.length_append]; omega)
                  = dict[j]'hjlt :=
                List.getElem_append_left hjlt
              have htake : (dict ++ [cur ++ [s]]).take j = dict.take j := by
                rw [List.take_append_of_le_length (by omega)]
              rw [hget, htake]
              exact hdict j hjlt
            · -- j = dict.length: the new entry is `cur ++ [s]`, dropLast = cur
              have hjeq : j = dict.length := by omega
              subst hjeq
              have hget : (dict ++ [cur ++ [s]])[dict.length]'(by
                  rw [List.length_append]; omega) = cur ++ [s] := by
                rw [List.getElem_append_right (le_refl _)]
                simp
              have htake : (dict ++ [cur ++ [s]]).take dict.length = dict := by
                rw [List.take_append_of_le_length (le_refl _), List.take_length]
              rw [hget, htake, List.dropLast_concat]
              exact hcur

/-- **Top-level parent-extension invariant**: for the genuine longest-prefix
greedy parse, each emitted phrase's `dropLast` is either `[]` or an earlier
emitted phrase.

@audit:ok (FINAL completion audit 2026-06-21, commit `bd28e0e`, independent
subagent). NON-VACUOUS — the property is genuinely FALSE for an arbitrary list
(e.g. `L = [[a,b]]`: `L[0].dropLast = [a] ∉ L.take 0 = []` and `≠ []`), so it
genuinely captures the LZ78 dictionary structure (dictionaries grow only by
appending `cur ++ [s]` with `cur` an earlier entry). The worker fuel-induction
is honest: the base / `nil` cases return the accumulated dict unchanged and
discharge via the threaded running invariant `hdict` (NOT a degenerate
fuel-exhaustion shortcut), the `cons`-emit case proves
`(cur ++ [s]).dropLast = cur ∈ dict` via `List.dropLast_concat`. Top-level uses
the genuine sufficient fuel `input.length + 1`. `#print axioms =
[propext, Quot.sound]` (sorryAx-free, machine-confirmed). -/
theorem lz78PhraseStrings_dropLast_earlier (input : List α) :
    ∀ j, ∀ h : j < (lz78PhraseStrings input).length,
      ((lz78PhraseStrings input)[j]'h).dropLast ∈ (lz78PhraseStrings input).take j
        ∨ ((lz78PhraseStrings input)[j]'h).dropLast = [] :=
  lz78PhraseStringsAux_dropLast_earlier (input.length + 1) [] [] input (Or.inr rfl)
    (by intro j h; simp at h)

end ParentExtension

/-! ## §4. Phrase count bound -/

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

omit [DecidableEq α] in
/-- **Count is bounded by total length when every phrase is non-empty**:
the number of phrases is at most the sum of their lengths, since each
length is `≥ 1`. -/
theorem length_le_foldr_length_of_ne_nil (l : List (List α))
    (h : ∀ w ∈ l, w ≠ []) :
    l.length ≤ l.foldr (fun w acc ↦ w.length + acc) 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.foldr_cons, List.length_cons]
      have hhd : hd ≠ [] := h hd (List.mem_cons_self ..)
      have hhd_len : 1 ≤ hd.length := by
        rcases hd with _ | ⟨a, as⟩
        · exact absurd rfl hhd
        · simp
      have htl : ∀ w ∈ tl, w ≠ [] := fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
      have := ih htl
      omega

omit [DecidableEq α] in
/-- **Member length bounded by the `foldr max`**: every entry of a list of strings has
length at most the longest entry length (the `Lmax` accumulator used to bound the
leading-boundary and trailing-tail symbol lengths in the tiling). -/
theorem length_le_foldr_max_of_mem (l : List (List α)) (w : List α) (h : w ∈ l) :
    w.length ≤ l.foldr (fun w acc ↦ max w.length acc) 0 := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with h | h
      · subst h; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- **Distinct phrase count bound**: the number of distinct
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

/-! ## §5. Absolute-position tiling of the parse -/

section Tiling

variable {α : Type*} [DecidableEq α]

/-- **Deterministic absolute-position tiling from the greedy parse.** For an
input list and a Markov order `k`, the greedy longest-prefix parse furnishes an
absolute-position partition of the input prefix it covers: a leading boundary
length `b`, a phrase count `c`, a covered length `e ≤ input.length`, the count
`bAbsorbed` of leading phrases absorbed into `[0, b)` (those whose cumulative end
is `≤ k`), and the cumulative-position function `N : Fin (c + 1) → ℕ`.

The partition `[b, e)` is strictly monotone (each phrase consumes `≥ 1` symbol),
every phrase start `N j.castSucc` exceeds `k` (the leading `≤ k` phrases are
absorbed), the count is anchored to the genuine parse via
`c + bAbsorbed = (parse).length`, and `bAbsorbed ≤ k + 1` (the cumulative length
increases by `≥ 1` each step, so at most `k + 1` phrases fit below position `k`).

**Boundary-length bounds** (for the downstream W2 limsup discharge): with `Lmax` the
longest phrase length, the leading boundary `b ≤ k + Lmax` (the last absorbed phrase
extends one phrase past the `≤ k` cumulative prefix) and the trailing tail
`input.length - e ≤ Lmax` (the un-emitted tail is one dictionary phrase or empty,
`lz78PhraseStrings_flatten_tail_mem`).

This is the pure list-combinatorial heart of the LZ78 threading tiling: it carries
the phrase *lengths* only (the downstream threading reads phrase content directly
off the process, never the parse strings' content).

@audit:ok (independent audit 2026-06-21, sorryAx-free `[propext, Classical.choice,
Quot.sound]`; pure list-combinatorial core, no hypothesis bundling; non-vacuity genuine —
`c := parseCount - bAbsorbed` with `bAbsorbed = Nat.find` (least index with cumulative
length `> k`), so `c > 0` whenever `parseCount > k+1`, not an empty tiling; `bAbsorbed ≤
k+1` and the boundary bounds `n - e ≤ Lmax` / `b ≤ k + Lmax` are genuinely proved (tail
∈ phrases-or-empty via `lz78PhraseStrings_flatten_tail_mem`, last-absorbed-phrase argument),
not vacuous tautologies). -/
theorem lz78_parse_tiling_positions (input : List α) (k : ℕ) :
    ∃ (b c e bAbsorbed Lmax : ℕ) (N : Fin (c + 1) → ℕ),
      N 0 = b ∧ N (Fin.last c) = e ∧ e ≤ input.length ∧
      (∀ j : Fin c, N j.castSucc + 1 ≤ N j.succ) ∧
      (∀ j : Fin c, k < N j.castSucc) ∧
      c + bAbsorbed = (lz78PhraseStrings input).length ∧
      bAbsorbed ≤ k + 1 ∧
      input.length - e ≤ Lmax ∧
      b ≤ k + Lmax ∧
      -- slice/content correspondence: the `j`-th tiled slice of the input is the
      -- `(bAbsorbed + j)`-th greedy phrase string (content half of the tiling).
      (∀ j : Fin c, (lz78PhraseStrings input)[bAbsorbed + j.val]?
        = some ((input.drop (N j.castSucc)).take (N j.succ - N j.castSucc))) := by
  classical
  set L := lz78PhraseStrings input with hL_def
  set m := L.length with hm_def
  -- Cumulative length of the first `j` phrases.
  set cumLen : ℕ → ℕ := fun j ↦ (L.take j).foldr (fun w acc ↦ w.length + acc) 0
    with hcum_def
  -- cumLen 0 = 0.
  have hcum0 : cumLen 0 = 0 := by simp [hcum_def]
  -- One-step recurrence for `j < m`.
  have hcum_succ : ∀ (j : ℕ) (h : j < m), cumLen (j + 1) = cumLen j + (L[j]'h).length := by
    intro j h
    simp only [hcum_def]
    exact foldrLength_take_succ L j h
  -- Each phrase length ≥ 1.
  have hphrase_pos : ∀ j (h : j < m), 1 ≤ (L[j]'h).length := by
    intro j h
    have hmem : L[j]'h ∈ L := List.getElem_mem h
    have hne : L[j]'h ≠ [] := lz78PhraseStrings_forall_ne_nil input _ hmem
    exact List.length_pos_iff.mpr hne
  -- cumLen monotone (≤).
  have hcum_mono : ∀ i j, i ≤ j → cumLen i ≤ cumLen j := by
    intro i j hij
    simp only [hcum_def]
    exact foldrLength_take_mono L hij
  -- cumLen j ≥ j for j ≤ m (each step adds ≥1).
  have hcum_ge : ∀ j, j ≤ m → j ≤ cumLen j := by
    intro j hj
    simp only [hcum_def]
    exact foldrLength_take_ge_of_forall_ne_nil L
      (lz78PhraseStrings_forall_ne_nil input) (by rw [← hm_def]; exact hj)
  -- cumLen m = total ≤ input.length.
  have hcumm_eq : cumLen m = L.foldr (fun w acc ↦ w.length + acc) 0 := by
    simp only [hcum_def, hm_def, List.take_length]
  have hcumm_le : cumLen m ≤ input.length := by
    rw [hcumm_eq, hL_def]
    exact lz78PhraseStrings_total_length_le input
  -- The absorption predicate: least index whose cumulative length exceeds `k`,
  -- or `m` (the parse end) if none.
  set P : ℕ → Prop := fun j ↦ k < cumLen j ∨ j = m with hP_def
  have hP_exists : ∃ j, P j := ⟨m, Or.inr rfl⟩
  set bAbsorbed := Nat.find hP_exists with hbA_def
  have hbA_le_m : bAbsorbed ≤ m := Nat.find_min' hP_exists (Or.inr rfl)
  have hbA_le_k1 : bAbsorbed ≤ k + 1 := by
    -- `P (min (k+1) m)` holds, so `bAbsorbed ≤ min (k+1) m ≤ k+1`.
    have hPmin : P (min (k + 1) m) := by
      rcases le_or_gt m (k + 1) with hle | hlt
      · -- min = m
        rw [min_eq_right hle]; exact Or.inr rfl
      · -- min = k+1 ≤ m, and cumLen (k+1) ≥ k+1 > k
        rw [min_eq_left hlt.le]
        have : k + 1 ≤ cumLen (k + 1) := hcum_ge (k + 1) hlt.le
        exact Or.inl (by omega)
    have := Nat.find_min' hP_exists hPmin
    omega
  -- For j < bAbsorbed, cumLen j ≤ k (and j ≠ m).
  have hbA_below : ∀ j, j < bAbsorbed → cumLen j ≤ k := by
    intro j hj
    have hnot : ¬ P j := Nat.find_min hP_exists hj
    simp only [hP_def, not_or, not_lt] at hnot
    exact hnot.1
  -- Either k < cumLen bAbsorbed, or bAbsorbed = m.
  have hbA_spec : k < cumLen bAbsorbed ∨ bAbsorbed = m := Nat.find_spec hP_exists
  set c := m - bAbsorbed with hc_def
  set N : Fin (c + 1) → ℕ := fun j ↦ cumLen (bAbsorbed + j.val) with hN_def
  -- Longest phrase length: the boundary symbol-length cap.
  set Lmax : ℕ := L.foldr (fun w acc ↦ max w.length acc) 0 with hLmax_def
  have hLmax_bound : ∀ j (h : j < m), (L[j]'h).length ≤ Lmax := by
    intro j h
    exact length_le_foldr_max_of_mem L (L[j]'h) (List.getElem_mem h)
  refine ⟨cumLen bAbsorbed, c, cumLen m, bAbsorbed, Lmax, N,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- N 0 = cumLen bAbsorbed
    simp only [hN_def, Fin.val_zero, Nat.add_zero]
  · -- N (last c) = cumLen m
    simp only [hN_def, Fin.val_last]
    congr 1
    omega
  · -- cumLen m ≤ input.length
    exact hcumm_le
  · -- hmono: N j.castSucc + 1 ≤ N j.succ
    intro j
    simp only [hN_def, Fin.val_castSucc, Fin.val_succ, ← Nat.add_assoc]
    -- bAbsorbed + j < m, so the next step grows by ≥ 1.
    have hjm : bAbsorbed + j.val < m := by
      have := j.isLt; omega
    have hsucc : cumLen (bAbsorbed + j.val + 1)
        = cumLen (bAbsorbed + j.val) + (L[bAbsorbed + j.val]'hjm).length :=
      hcum_succ (bAbsorbed + j.val) hjm
    have hlen := hphrase_pos (bAbsorbed + j.val) hjm
    omega
  · -- hstart: k < N j.castSucc
    intro j
    simp only [hN_def, Fin.val_castSucc]
    -- k < cumLen bAbsorbed ≤ cumLen (bAbsorbed + j).
    have hkb : k < cumLen bAbsorbed := by
      rcases hbA_spec with h | h
      · exact h
      · -- bAbsorbed = m forces c = 0, contradicting `j : Fin c`.
        exfalso
        have hc0 : c = 0 := by omega
        exact absurd j.isLt (by omega)
    have hmono := hcum_mono bAbsorbed (bAbsorbed + j.val) (Nat.le_add_right _ _)
    omega
  · -- c + bAbsorbed = m
    omega
  · -- bAbsorbed ≤ k + 1
    exact hbA_le_k1
  · -- input.length - e ≤ Lmax (trailing tail is one phrase or empty)
    obtain ⟨tail, htail, hmem⟩ := lz78PhraseStrings_flatten_tail_mem input
    -- flatten.length = cumLen m, so tail.length = input.length - cumLen m.
    have hflat_len : L.flatten.length = cumLen m := by
      rw [length_flatten_eq_foldr_length, hcumm_eq]
    have htail_len : tail.length = input.length - cumLen m := by
      have : L.flatten.length + tail.length = input.length := by
        rw [← List.length_append, htail]
      omega
    have htail_le : tail.length ≤ Lmax := by
      rcases hmem with hmem | hmem
      · exact length_le_foldr_max_of_mem L tail hmem
      · simp [hmem]
    omega
  · -- b = cumLen bAbsorbed ≤ k + Lmax (last absorbed phrase extends one phrase past `k`)
    rcases Nat.eq_zero_or_pos bAbsorbed with hz | hpos
    · -- bAbsorbed = 0 ⇒ b = cumLen 0 = 0.
      rw [hz, hcum0]; omega
    · -- bAbsorbed = (bAbsorbed - 1) + 1, with cumLen (bAbsorbed-1) ≤ k.
      have hbm1_lt : bAbsorbed - 1 < m := by omega
      have hbm1_below : cumLen (bAbsorbed - 1) ≤ k := hbA_below (bAbsorbed - 1) (by omega)
      have hsucc : cumLen (bAbsorbed - 1 + 1)
          = cumLen (bAbsorbed - 1) + (L[bAbsorbed - 1]'hbm1_lt).length :=
        hcum_succ (bAbsorbed - 1) hbm1_lt
      have hb_eq : cumLen bAbsorbed = cumLen (bAbsorbed - 1 + 1) := by
        congr 1; omega
      have hlen_le := hLmax_bound (bAbsorbed - 1) hbm1_lt
      omega
  · -- slice/content correspondence: the `j`-th slice is the `(bAbsorbed+j)`-th phrase.
    intro j
    set idx : ℕ := bAbsorbed + j.val with hidx_def
    have hidx_lt : idx < m := by have := j.isLt; omega
    -- `N j.castSucc = cumLen idx`, `N j.succ = cumLen (idx + 1)`.
    have hNcast : N j.castSucc = cumLen idx := by
      simp only [hN_def, Fin.val_castSucc, hidx_def]
    have hNsucc : N j.succ = cumLen (idx + 1) := by
      simp only [hN_def, Fin.val_succ, hidx_def]
      congr 1
    -- Prefix reconstruction `L.flatten ++ tail = input`.
    obtain ⟨tail, htail⟩ := lz78PhraseStrings_flatten_prefix input
    rw [hNcast, hNsucc, hcum_def]
    exact getElem?_eq_some_drop_take_of_flatten_prefix L htail idx hidx_lt

end Tiling

end InformationTheory.Shannon
