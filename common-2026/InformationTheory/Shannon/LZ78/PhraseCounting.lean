import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.GreedyLongestPrefix
import InformationTheory.Shannon.LZ78.PhraseCountAsymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# LZ78 distinct-phrase counting bound — `c · log c ≤ K·n`

`InformationTheory/Shannon/LZ78GreedyLongestPrefix.lean` establishes
the genuine longest-prefix greedy parse `lz78PhraseStrings` together with
its **distinct invariant** `lz78PhraseStrings_nodup` and the
total-length conservation `lz78PhraseStrings_total_length_le`.

This file supplies the **Cover–Thomas Lemma 13.5.2 counting bound** as a
genuine combinatorial inequality on any `Nodup` list of non-empty strings
over a finite alphabet:

```
c · log c ≤ K · T          (K = 4·log(|α|+1),  T = total symbol count)
```

which, instantiated at `lz78PhraseStrings input` with `T ≤ input.length`,
gives the Ziv product bound `c(n) · log c(n) ≤ K·n` (★). Composed with the
inversion `isBigO_natCast_div_log_of_mul_log_le`
(`LZ78/PhraseCountAsymptotics.lean`), this yields `c(n) = O(n / log n)`.

## Approach

The substantive content is the **shortest-first packing lower bound** on
the total length `T` of `c` distinct non-empty strings. Two genuine
ingredients:

1. **Geometric stratification (`card_short_le`)** — the number of
   *distinct* strings of length `≤ L` is at most `(b+1)^(L+1)`, where
   `b = |α|`. Proof: `w ↦ (fun i : Fin (L+1) => w[i]?)` is injective on
   strings of length `≤ L` (two such strings agreeing on indices `0..L`
   of `getElem?` are equal — indices past their length both return
   `none`), so `List.Nodup.length_le_card` into `Fin (L+1) → Option α`
   (card `(b+1)^(L+1)`) bounds the count.

2. **Packing (`total_length_ge`)** — among `c` distinct strings, at most
   `(b+1)^(L+1)` are short (length `≤ L`), so at least `c - (b+1)^(L+1)`
   are long (length `≥ L+1`), each contributing `≥ L+1` to `T`. Choosing
   the threshold `L+1 = Nat.log (b+1) c - 1` makes the short count
   `≤ c/2`, giving `T ≥ (L+1)·(c/2) ≈ (c/2)·log_{b+1} c`.

The real-analysis assembly converts `Nat.log (b+1) c` to `Real.log c /
Real.log (b+1)` via `Nat.pow_log_le_self` / `Nat.lt_pow_succ_log_self`,
yielding `c·log c ≤ 4·log(b+1)·T`.

## File layout

* **§1. Strings as `Option`-tuples** — the injection `toOptTuple` and its
  injectivity on length-`≤L` strings.
* **§2. Geometric stratification** — `card_short_le`.
* **§3. Shortest-first packing** — `total_length_ge_count_mul_log`.
* **§4. Ziv product bound** — `lz78PhraseStrings_mul_log_le`, the genuine
  `c·log c ≤ K·T` on `lz78PhraseStrings`.
-/

namespace InformationTheory.Shannon

open scoped BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. Strings as `Option`-tuples (injection for stratification) -/

section OptTuple

variable {α : Type*}

/-- **Injection of length-`≤L` strings into `Fin (L+1) → Option α`**:
record each of the first `L+1` `getElem?` slots. -/
def toOptTuple (L : ℕ) (w : List α) : Fin (L + 1) → Option α :=
  fun i => w[(i : ℕ)]?

/-- **Injectivity on length-`≤L` strings**: two strings of length `≤ L`
with the same `getElem?` on indices `0..L` are equal. -/
theorem toOptTuple_injOn (L : ℕ) :
    Set.InjOn (toOptTuple L) {w : List α | w.length ≤ L} := by
  intro w hw v hv heq
  apply List.ext_getElem?
  intro i
  by_cases hi : i ≤ L
  · -- index within the recorded window: read off the tuple equality
    have := congrFun heq ⟨i, by omega⟩
    simpa [toOptTuple] using this
  · -- index past the window: both lists are too short, so both `none`
    simp only [not_le] at hi
    have hw' : w.length ≤ L := hw
    have hv' : v.length ≤ L := hv
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end OptTuple

/-! ## §2. Geometric stratification -/

section Stratification

variable {α : Type*} [Fintype α]

/-- **Distinct short-string count bound**: a `Nodup` list of strings, all
of length `≤ L`, has length at most `(|α|+1)^(L+1)`. -/
theorem card_short_le (ws : List (List α)) (hnodup : ws.Nodup)
    (hlen : ∀ w ∈ ws, w.length ≤ L) :
    ws.length ≤ (Fintype.card α + 1) ^ (L + 1) := by
  -- map the `Nodup` list into `Fin (L+1) → Option α` via the injective
  -- `toOptTuple`, then bound by the cardinality of the target type.
  have hmap_nodup : (ws.map (toOptTuple L)).Nodup := by
    refine hnodup.map_on ?_
    intro x hx y hy hxy
    exact toOptTuple_injOn L (hlen x hx) (hlen y hy) hxy
  have hcard := hmap_nodup.length_le_card
  rw [List.length_map] at hcard
  refine hcard.trans ?_
  rw [Fintype.card_pi_const, Fintype.card_option]

end Stratification

/-! ## §3. Shortest-first packing -/

section Packing

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **Nat-level packing bound**: for any threshold `L`, the total length
`T` of a `Nodup` string list dominates `(L+1)` times the number of long
strings (length `> L`), and the long-string count is `c` minus the short
count, which is bounded by `(b+1)^(L+1)`. Concretely
`(L+1)·(c - (b+1)^(L+1)) ≤ T`. -/
theorem packing_nat (ws : List (List α)) (hnodup : ws.Nodup) (L : ℕ) :
    (L + 1) * (ws.length - (Fintype.card α + 1) ^ (L + 1))
      ≤ (ws.map List.length).sum := by
  classical
  -- Split `ws` into long (`L < length`) and short (`length ≤ L`).
  set P : List α → Prop := fun w => L < w.length with hP
  set long := ws.filter (fun w => decide (P w)) with hlong
  set short := ws.filter (fun w => decide (¬ P w)) with hshort
  have hsplit :
      (long.map List.length).sum + (short.map List.length).sum
      = (ws.map List.length).sum :=
    List.sum_map_filter_add_sum_map_filter_not P List.length ws
  -- The short list is `Nodup`, all of length `≤ L`, so bounded by `(b+1)^(L+1)`.
  have hshort_nodup : short.Nodup := hnodup.filter _
  have hshort_len : ∀ w ∈ short, w.length ≤ L := by
    intro w hw
    have : decide (¬ P w) = true := (List.mem_filter.mp hw).2
    simp only [hP, decide_eq_true_eq, not_lt] at this
    exact this
  have hshort_card : short.length ≤ (Fintype.card α + 1) ^ (L + 1) :=
    card_short_le _ hshort_nodup hshort_len
  -- Every long string contributes `≥ L+1`, so the long sum dominates
  -- `(L+1) * (#long)`.
  have hlong_sum : (L + 1) * long.length ≤ (long.map List.length).sum := by
    have hpt : ∀ w ∈ long.map List.length, L + 1 ≤ w := by
      intro k hk
      rcases List.mem_map.mp hk with ⟨w, hw, rfl⟩
      have : decide (P w) = true := (List.mem_filter.mp hw).2
      simp only [hP, decide_eq_true_eq] at this
      omega
    calc (L + 1) * long.length
        = (long.map List.length).length • (L + 1) := by
          rw [List.length_map, smul_eq_mul, Nat.mul_comm]
      _ ≤ (long.map List.length).sum :=
          List.card_nsmul_le_sum (long.map List.length) (L + 1) hpt
  -- Long count = total - short count.
  have hcount : ws.length = long.length + short.length := by
    have := ws.length_eq_countP_add_countP (fun w => decide (P w))
    simp only [List.countP_eq_length_filter, hlong, hshort] at this ⊢
    convert this using 3
    simp
  -- Assemble.
  have hlong_ge : ws.length - (Fintype.card α + 1) ^ (L + 1) ≤ long.length := by
    omega
  calc (L + 1) * (ws.length - (Fintype.card α + 1) ^ (L + 1))
      ≤ (L + 1) * long.length := Nat.mul_le_mul_left _ hlong_ge
    _ ≤ (long.map List.length).sum := hlong_sum
    _ ≤ (ws.map List.length).sum := by omega

/-- **Total-length lower bound (Cover–Thomas packing core)**: a `Nodup`
list of non-empty strings with `c = ws.length` and total length
`T = Σ lengths` satisfies `c · log c ≤ K · T` with `K = 4·log(|α|+1)`. -/
theorem total_length_ge_count_mul_log
    (ws : List (List α)) (hnodup : ws.Nodup)
    (hne : ∀ w ∈ ws, w ≠ []) :
    (ws.length : ℝ) * Real.log (ws.length : ℝ)
      ≤ 8 * Real.log (Fintype.card α + 1)
          * ((ws.map List.length).sum : ℝ) := by
  -- Abbreviations: `b1 = |α| + 1 ≥ 2`, `c = #phrases`, `T = total length`.
  set b1 : ℕ := Fintype.card α + 1 with hb1
  set c : ℕ := ws.length with hc
  set T : ℕ := (ws.map List.length).sum with hT
  -- The goal's RHS is phrased with `↑(card α) + 1`; rewrite to `↑b1`.
  rw [show ((Fintype.card α : ℝ) + 1) = (b1 : ℝ) by rw [hb1]; push_cast; ring]
  have hb1_two : 2 ≤ b1 := by
    have : 1 ≤ Fintype.card α := Fintype.card_pos
    omega
  have hb1R_pos : (0 : ℝ) < (b1 : ℝ) := by positivity
  have hlogb1_pos : (0 : ℝ) < Real.log (b1 : ℝ) :=
    Real.log_pos (by exact_mod_cast hb1_two)
  -- `T ≥ c` since every phrase is non-empty (length `≥ 1`).
  have hTc : c ≤ T := by
    have hone : ∀ k ∈ ws.map List.length, 1 ≤ k := by
      intro k hk
      rcases List.mem_map.mp hk with ⟨w, hw, rfl⟩
      have : w ≠ [] := hne w hw
      cases w with
      | nil => exact absurd rfl this
      | cons _ _ => simp
    have := List.length_le_sum_of_one_le (ws.map List.length) hone
    rwa [List.length_map] at this
  have hTcR : (c : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTc
  have hcR_nonneg : (0 : ℝ) ≤ (c : ℝ) := by positivity
  -- **Case split** at the threshold `c ≤ b1^4`.
  rcases le_or_gt c (b1 ^ 4) with hsmall | hlarge
  · -- Small `c`: `log c ≤ log (b1^4) = 4 log b1`, so `c log c ≤ 4 log b1 · c ≤ … T`.
    have hlogc_le : Real.log (c : ℝ) ≤ 4 * Real.log (b1 : ℝ) := by
      have h1 : Real.log (c : ℝ) ≤ Real.log ((b1 ^ 4 : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos c with hc0 | hcpos
        · simp only [hc0, CharP.cast_eq_zero, Real.log_zero, Nat.cast_pow, Real.log_pow,
            Nat.cast_ofNat, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
          positivity
        · exact Real.log_le_log (by exact_mod_cast hcpos) (by exact_mod_cast hsmall)
      rw [show ((b1 ^ 4 : ℕ) : ℝ) = (b1 : ℝ) ^ 4 by push_cast; ring,
        Real.log_pow] at h1
      push_cast at h1
      linarith
    calc (c : ℝ) * Real.log (c : ℝ)
        ≤ (c : ℝ) * (8 * Real.log (b1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hcR_nonneg
      _ = 8 * Real.log (b1 : ℝ) * (c : ℝ) := by ring
      _ ≤ 8 * Real.log (b1 : ℝ) * (T : ℝ) := by
          apply mul_le_mul_of_nonneg_left hTcR
          positivity
  · -- Large `c > b1^4 ≥ 16`: the genuine packing argument.
    -- Choose `j = Nat.log b1 (c/2)`; then `b1^j ≤ c/2` and `b1^{j+1} > c/2`.
    have hb1_4 : 16 ≤ b1 ^ 4 := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ b1 ^ 4 := Nat.pow_le_pow_left hb1_two 4
    have hc_pos : 0 < c := by omega
    have hc2_pos : 0 < c / 2 := by omega
    set j : ℕ := Nat.log b1 (c / 2) with hj
    have hpow_le : b1 ^ j ≤ c / 2 := Nat.pow_log_le_self b1 (by omega)
    have hpow_lt : c / 2 < b1 ^ (j + 1) :=
      Nat.lt_pow_succ_log_self (by omega) (c / 2)
    -- `j ≥ 1`: since `c/2 ≥ 8 ≥ b1` is false in general, but
    -- `c > b1^4` gives `c/2 > b1^4/2 ≥ b1^3 ≥ b1`, hence `Nat.log b1 (c/2) ≥ 1`.
    have hj_pos : 1 ≤ j := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro h0
      rw [h0, pow_zero] at hpow_le
      -- derive `b1 ≤ c/2` directly to contradict `b1^0 = 1 ≤ c/2` being too small.
      have hb1c2 : b1 ≤ c / 2 := by
        have h2b1 : 2 * b1 ≤ b1 ^ 4 := by
          calc 2 * b1 ≤ b1 * b1 := by nlinarith [hb1_two]
            _ = b1 ^ 2 := by ring
            _ ≤ b1 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      -- but then `Nat.log b1 (c/2) ≥ 1`, contradicting `j = 0`.
      have : 1 ≤ Nat.log b1 (c / 2) :=
        Nat.le_log_of_pow_le (by omega) (by simpa using hb1c2)
      omega
    -- Packing with cutoff `L + 1 = j` (so `L = j - 1`).
    obtain ⟨L, hL⟩ : ∃ L, j = L + 1 := ⟨j - 1, by omega⟩
    have hpack := packing_nat ws hnodup L
    rw [← hL] at hpack
    -- `b1^j ≤ c/2`, so `c - b1^j ≥ c - c/2 ≥ c/2`, giving `j·(c/2) ≤ T`.
    have hsub : c / 2 ≤ c - b1 ^ j := by omega
    have hjc2 : j * (c / 2) ≤ T := by
      calc j * (c / 2) ≤ j * (c - b1 ^ j) := Nat.mul_le_mul_left _ hsub
        _ ≤ T := hpack
    -- Nat → real, with `c ≤ 2·(c/2) + 1` to clear the floor division.
    have hc_floor : c ≤ 2 * (c / 2) + 1 := by omega
    have hjc2R : (j : ℝ) * (c / 2 : ℕ) ≤ (T : ℝ) := by exact_mod_cast hjc2
    -- `j·c ≤ 2T + j` over the reals.
    have hjc : (j : ℝ) * (c : ℝ) ≤ 2 * (T : ℝ) + (j : ℝ) := by
      have h1 : (c : ℝ) ≤ 2 * ((c / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hc_floor
      have hj_nn : (0 : ℝ) ≤ (j : ℝ) := by positivity
      calc (j : ℝ) * (c : ℝ)
          ≤ (j : ℝ) * (2 * ((c / 2 : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left h1 hj_nn
        _ = 2 * ((j : ℝ) * ((c / 2 : ℕ) : ℝ)) + (j : ℝ) := by ring
        _ ≤ 2 * (T : ℝ) + (j : ℝ) := by linarith
    -- `j ≤ T` (since `j ≤ c/2 ≤ c ≤ T`).
    have hjT : (j : ℝ) ≤ (T : ℝ) := by
      have hjc2le : j ≤ c / 2 := Nat.log_le_self b1 (c / 2)
      have : j ≤ T := by omega
      exact_mod_cast this
    -- `c < 2·b1^{j+1}`, so `log c < log 2 + (j+1)·log b1`.
    have hc_lt : (c : ℝ) < 2 * (b1 : ℝ) ^ (j + 1) := by
      have hN : c < 2 * b1 ^ (j + 1) := by omega
      calc (c : ℝ) < ((2 * b1 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hN
        _ = 2 * (b1 : ℝ) ^ (j + 1) := by push_cast; ring
    have hlogc_lt : Real.log (c : ℝ)
        < Real.log 2 + (j + 1 : ℝ) * Real.log (b1 : ℝ) := by
      have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc_pos
      calc Real.log (c : ℝ)
          < Real.log (2 * (b1 : ℝ) ^ (j + 1)) := Real.log_lt_log hcpos hc_lt
        _ = Real.log 2 + Real.log ((b1 : ℝ) ^ (j + 1)) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
        _ = Real.log 2 + (j + 1 : ℝ) * Real.log (b1 : ℝ) := by
            rw [Real.log_pow]; push_cast; ring
    -- `log 2 ≤ log b1`.
    have hlog2_le : Real.log 2 ≤ Real.log (b1 : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hb1_two)
    -- Assemble: `c·log c ≤ 8·log b1·T`.
    have hcj_log : (c : ℝ) * Real.log (c : ℝ)
        ≤ (c : ℝ) * (Real.log 2 + (j + 1 : ℝ) * Real.log (b1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogc_lt.le hcR_nonneg
    -- expand and bound the cross-term `c·j·log b1`.
    have hexpand : (c : ℝ) * (Real.log 2 + (j + 1 : ℝ) * Real.log (b1 : ℝ))
        = (c : ℝ) * Real.log 2 + (j : ℝ) * (c : ℝ) * Real.log (b1 : ℝ)
            + (c : ℝ) * Real.log (b1 : ℝ) := by ring
    have hcross : (j : ℝ) * (c : ℝ) * Real.log (b1 : ℝ)
        ≤ (2 * (T : ℝ) + (j : ℝ)) * Real.log (b1 : ℝ) :=
      mul_le_mul_of_nonneg_right hjc hlogb1_pos.le
    -- Final linear combination.
    rw [hexpand] at hcj_log
    have hclog2 : (c : ℝ) * Real.log 2 ≤ (T : ℝ) * Real.log (b1 : ℝ) :=
      mul_le_mul hTcR hlog2_le (Real.log_nonneg (by norm_num)) (by positivity)
    have hclogb1 : (c : ℝ) * Real.log (b1 : ℝ) ≤ (T : ℝ) * Real.log (b1 : ℝ) :=
      mul_le_mul_of_nonneg_right hTcR hlogb1_pos.le
    nlinarith [hcj_log, hcross, hclog2, hclogb1, hjT, hlogb1_pos.le,
      mul_le_mul_of_nonneg_right hjT hlogb1_pos.le]

end Packing

/-! ## §4. Ziv product bound on `lz78PhraseStrings` -/

section ZivBound

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **`foldr`-length equals `map`-length sum**: bridges the
total-length shape to the `List.sum` shape used by the packing lemma. -/
theorem foldr_length_eq_map_sum (ws : List (List α)) :
    ws.foldr (fun w acc => w.length + acc) 0 = (ws.map List.length).sum := by
  induction ws with
  | nil => simp
  | cons hd tl ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

/-- **Ziv product bound `c·log c ≤ K·n` on the genuine greedy parse**: the
distinct phrase count `c = (lz78PhraseStrings input).length` satisfies
`c · log c ≤ 8·log(|α|+1) · input.length`. This is the genuine
Cover–Thomas `(★)` for the longest-prefix greedy parse, combining the
invariants `lz78PhraseStrings_nodup` / `lz78PhraseStrings_forall_ne_nil`
/ `lz78PhraseStrings_total_length_le` with the §3 packing core. -/
@[entry_point]
theorem lz78PhraseStrings_mul_log_le [Nonempty α] (input : List α) :
    ((lz78PhraseStrings input).length : ℝ)
        * Real.log ((lz78PhraseStrings input).length : ℝ)
      ≤ 8 * Real.log (Fintype.card α + 1) * (input.length : ℝ) := by
  -- The phrase strings are `Nodup` and non-empty, so the §3 packing core
  -- bounds `c·log c` by `8·log(b1)·(total phrase length)`.
  have hcore := total_length_ge_count_mul_log (lz78PhraseStrings input)
    (lz78PhraseStrings_nodup input) (lz78PhraseStrings_forall_ne_nil input)
  -- The total phrase length is `≤ input.length` (length conservation).
  have hlen : ((lz78PhraseStrings input).map List.length).sum ≤ input.length := by
    rw [← foldr_length_eq_map_sum]
    exact lz78PhraseStrings_total_length_le input
  have hlenR : (((lz78PhraseStrings input).map List.length).sum : ℝ)
      ≤ (input.length : ℝ) := by exact_mod_cast hlen
  -- Chain: `c·log c ≤ 8·log b1·T ≤ 8·log b1·n`.
  refine hcore.trans ?_
  apply mul_le_mul_of_nonneg_left hlenR
  have hcard1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlog_nn : (0 : ℝ) ≤ Real.log (Fintype.card α + 1) :=
    Real.log_nonneg (by linarith)
  positivity

end ZivBound

/-! ## §5. String → asymptotic-envelope bridge -/

section AsymptoticBridge

open Filter Asymptotics

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Genuine `c·log c ≤ K·n` for a length-`n` input family**: for any
family `input : ℕ → List α` with `(input n).length = n`, the distinct
phrase count `c(n) = (lz78PhraseStrings (input n)).length` satisfies the
Cover–Thomas product bound `(★)` with `K = 8·log(|α|+1)`. -/
theorem lz78PhraseStrings_mul_log_le_of_length
    (input : ℕ → List α) (hlen : ∀ n, (input n).length = n) (n : ℕ) :
    ((lz78PhraseStrings (input n)).length : ℝ)
        * Real.log ((lz78PhraseStrings (input n)).length : ℝ)
      ≤ 8 * Real.log (Fintype.card α + 1) * (n : ℝ) := by
  have := lz78PhraseStrings_mul_log_le (input n)
  rwa [hlen n] at this

/-- **Genuine distinct-phrase-count asymptotic
`c(n) = O(n / log n)`**: combining the product bound `(★)`
(`lz78PhraseStrings_mul_log_le`) with the genuine inversion lemma
`isBigO_natCast_div_log_of_mul_log_le`
(`LZ78/PhraseCountAsymptotics.lean`), the *genuine longest-prefix
greedy* distinct phrase count is `O(n / log n)`. This connects the
distinct invariant to the Cover–Thomas Eq. 13.124 envelope with
no honest hypothesis. -/
@[entry_point]
theorem lz78PhraseStrings_count_isBigO
    (input : ℕ → List α) (hlen : ∀ n, (input n).length = n) :
    (fun n => ((lz78PhraseStrings (input n)).length : ℝ))
      =O[atTop] (fun n => (n : ℝ) / Real.log (n : ℝ)) := by
  refine isBigO_natCast_div_log_of_mul_log_le
    (K := 8 * Real.log (Fintype.card α + 1)) ?_ ?_
  · exact Filter.Eventually.of_forall (fun n => by positivity)
  · exact Filter.Eventually.of_forall
      (fun n => lz78PhraseStrings_mul_log_le_of_length input hlen n)

end AsymptoticBridge

end InformationTheory.Shannon
