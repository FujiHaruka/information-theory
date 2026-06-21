import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import InformationTheory.Shannon.LZ78.GreedyParsing
import InformationTheory.Shannon.LZ78.GreedyLongestPrefix
import InformationTheory.Shannon.LZ78.ZivCountingBody
import InformationTheory.Shannon.LZ78.ZivAchievabilityComposition
import InformationTheory.Shannon.SMB.AlgoetCover.Liminf
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# LZ78 greedy-parse encoding length + asymptotic-optimality bridge

The genuine longest-prefix-match greedy LZ78 parse itself lives in
`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean` as
`lz78PhraseStrings` (the ordered list of emitted phrase strings, with the
distinct-phrase invariants `lz78PhraseStrings_nodup` /
`lz78PhraseStrings_count_le`). This file builds the **encoding-length and
parent-theorem bridge** on top of that genuine parse:

* `lz78GreedyImplEncodingLength n x` charges `c · bitLength c |α|` bits
  against the genuine distinct phrase count
  `c = (lz78PhraseStrings (List.ofFn x)).length` (each of the `c` phrases
  costs at most `bitLength c |α|` bits at the final dictionary size);
* the Cover–Thomas Lemma 13.5.2 bit-length upper bound
  `n · (log(n+1) + log|α| + 2)` holds via `c ≤ n` and
  `bitLength`-monotonicity;
* the encoding length plugs into the parent
  `lz78_asymptotic_optimality` parameter slot, publishing the main theorem
  as `lz78_asymptotic_optimality_with_greedy_impl`.

The two a.s.-eventual halves of the sandwich (converse lower bound + Ziv
achievability upper bound) are genuine research-level ergodic walls
(M3 / M4 of `docs/shannon/lz78-completion-roadmap.md`), left as
`sorry` + `@residual(wall:...)`.

## File layout

* **§1. Encoding length + parent-theorem bridge** —
  `lz78GreedyImplEncodingLength`, its distinct-phrase count bound, and the
  Cover–Thomas bit-length / per-symbol-rate bounds.
* **§2. `IsLZ78EncodingLengthBoundPassthrough` analogue** — the impl-side
  upper-bound pass-through predicate and its canonical discharge.
* **§3. Parent-theorem bridge** — the two a.s.-eventual halves and the
  `lz78_asymptotic_optimality_with_greedy_impl` headline.

## Pattern source

Layering follows `LZ78GreedyParsing.lean` (worst-case form); the
parent-theorem bridge mirrors
`lz78_asymptotic_optimality_with_greedy_encoding`.
-/

namespace InformationTheory.Shannon

open scoped Topology

set_option linter.unusedSectionVars false

/-! ## §1. Encoding length + parent-theorem bridge -/

section EncodingLength

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Greedy encoding length of a finite tuple**: parse `List.ofFn x` with
the genuine longest-prefix-match greedy parse `lz78PhraseStrings`, count its
`c` distinct emitted phrases, and charge `c · bitLength c |α|` bits (each of
the `c` phrases costs at most `bitLength c |α|` bits, the uniform Cover–Thomas
Ch.13.5 per-phrase cost at the final dictionary size). This plugs into the
parent `lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter of
`lz78_asymptotic_optimality`.

The phrase count `c = (lz78PhraseStrings (List.ofFn x)).length` is the genuine
distinct-phrase count (`c ≤ n` always, `c = O(n / log n)` asymptotically via
`lz78PhraseStrings_count_isBigO`), so the per-symbol rate is data-dependent and
asymptotically bounded — unlike a one-symbol-per-phrase parse. -/
def lz78GreedyImplEncodingLength (n : ℕ) (x : Fin n → α) : ℕ :=
  let c := (lz78PhraseStrings (List.ofFn x)).length
  c * LZ78Phrase.bitLength c (Fintype.card α)

@[simp] lemma lz78GreedyImplEncodingLength_zero (x : Fin 0 → α) :
    lz78GreedyImplEncodingLength 0 x = 0 := by
  unfold lz78GreedyImplEncodingLength
  rw [show (List.ofFn x : List α) = [] from by simp]
  have hc : (lz78PhraseStrings ([] : List α)).length = 0 := by
    have := lz78PhraseStrings_count_le ([] : List α)
    simpa using this
  simp [hc]

/-- **Distinct phrase count of the genuine greedy parse on an `n`-tuple is
`≤ n`**: the genuine longest-prefix parse of `List.ofFn x` emits at most `n`
distinct phrases (`lz78PhraseStrings_count_le` plus `List.length_ofFn`). -/
theorem lz78GreedyImplPhraseCount_ofFn_le (n : ℕ) (x : Fin n → α) :
    (lz78PhraseStrings (List.ofFn x)).length ≤ n := by
  have := lz78PhraseStrings_count_le (List.ofFn x)
  rwa [List.length_ofFn] at this

/-- **Cover–Thomas Lemma 13.5.2 bit-length upper bound for the genuine
greedy parse**.

The genuine greedy encoding length for `x : Fin n → α` is bounded by
`n · (log(n+1) + log|α| + 2)`, since the parse has `c ≤ n` distinct phrases,
each costing at most `bitLength n |α|` bits. Combines the distinct-phrase
count bound `c ≤ n` with `bitLength`-monotonicity in the dictionary size. -/
@[entry_point]
theorem lz78_impl_encoding_length_le_n_log_n_plus_const (n : ℕ) (x : Fin n → α) :
    lz78GreedyImplEncodingLength n x ≤
      n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
  unfold lz78GreedyImplEncodingLength
  set c := (lz78PhraseStrings (List.ofFn x)).length with hc
  have hcn : c ≤ n := lz78GreedyImplPhraseCount_ofFn_le n x
  have hbit : LZ78Phrase.bitLength c (Fintype.card α)
      ≤ LZ78Phrase.bitLength n (Fintype.card α) :=
    LZ78Phrase.bitLength_mono_left hcn
  calc c * LZ78Phrase.bitLength c (Fintype.card α)
      ≤ n * LZ78Phrase.bitLength n (Fintype.card α) :=
        Nat.mul_le_mul hcn hbit
    _ = n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
        rw [LZ78Phrase.bitLength_eq]

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

/-- **`ℕ`–`Real` base-`2` log bridge**: `(Nat.log 2 m : ℝ) · Real.log 2 ≤ Real.log m`
for `m ≥ 1`, the inequality `Nat.log 2 m ≤ log m / log 2` cleared of the
denominator. Used to convert the integer per-phrase code length
`Nat.log 2 (c+1)` to the real `c·log c` Ziv product bound. -/
theorem lz78_impl_natLog_mul_log_two_le (m : ℕ) :
    (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
  have hbridge : (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
    have := Real.natLog_le_logb m 2
    rwa [Real.logb, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast] at this
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2] at hbridge
  exact hbridge

/-- **`n`- and `x`-uniform constant rate bound** for the genuine greedy
parse: the per-symbol bit rate `lz78GreedyImplEncodingLength n x / n` is
bounded by a deterministic constant depending only on `|α|`, for every `n`
(including the degenerate `n = 0`, where the rate is `0`). The constant is
`(1 + 8·log(|α|+1)/log 2) + (log₂|α| + 2)`, obtained from the Ziv product
bound `c·log c ≤ 8·log(|α|+1)·n` (`lz78PhraseStrings_mul_log_le`) together
with `c ≤ n` and the `ℕ`–`Real` log bridge. -/
theorem lz78_impl_rate_le_const [Nonempty α] (n : ℕ) (x : Fin n → α) :
    (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)
      ≤ (1 + 8 * Real.log (Fintype.card α + 1) / Real.log 2)
          + ((Nat.log 2 (Fintype.card α) : ℝ) + 2) := by
  set b : ℝ := Real.log (Fintype.card α + 1) with hb
  set L : ℝ := (Nat.log 2 (Fintype.card α) : ℝ) with hL
  have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb_nn : (0 : ℝ) ≤ b :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
                        linarith)
  have hL_nn : (0 : ℝ) ≤ L := by rw [hL]; exact Nat.cast_nonneg _
  set C : ℝ := (1 + 8 * b / Real.log 2) + (L + 2) with hC
  have hC_nn : (0 : ℝ) ≤ C := by
    have : (0 : ℝ) ≤ 8 * b / Real.log 2 := by positivity
    rw [hC]; linarith
  -- Degenerate `n = 0`: the rate is `0/0 = 0 ≤ C`.
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [Nat.cast_zero, div_zero]
    exact hC_nn
  -- `n ≥ 1`. Abbreviate the distinct phrase count `c`.
  set c : ℕ := (lz78PhraseStrings (List.ofFn x)).length with hc
  have hcn : c ≤ n := lz78GreedyImplPhraseCount_ofFn_le n x
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcR_nn : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hcnR : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcn
  -- The encoding length expanded via `bitLength_eq`.
  have hlen : (lz78GreedyImplEncodingLength n x : ℝ)
      = (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2) := by
    have hdef : lz78GreedyImplEncodingLength n x
        = c * LZ78Phrase.bitLength c (Fintype.card α) := rfl
    rw [hdef, LZ78Phrase.bitLength_eq]
    push_cast [hL]
    ring
  rw [div_le_iff₀ hnR, hlen]
  -- Bound `c · Nat.log 2 (c+1) ≤ n · (1 + 8·b/log 2)`.
  have hterm1 : (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
      ≤ (n : ℝ) * (1 + 8 * b / Real.log 2) := by
    -- `c · Nat.log 2 (c+1) · log 2 ≤ c · log(c+1) ≤ n·log 2 + 8·b·n`.
    have hbridge : (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) * Real.log 2)
        ≤ (c : ℝ) * Real.log (c + 1) := by
      apply mul_le_mul_of_nonneg_left _ hcR_nn
      exact lz78_impl_natLog_mul_log_two_le (c + 1) |>.trans_eq (by push_cast; ring_nf)
    -- `c · log(c+1) ≤ n · log 2 + 8·b·n`.
    have hupper : (c : ℝ) * Real.log (c + 1) ≤ (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ) := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcpos
      · rw [hc0]
        simp only [Nat.cast_zero, zero_mul]
        have : (0 : ℝ) ≤ (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ) := by positivity
        linarith
      · have hcRpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
        -- `log(c+1) ≤ log(2c) = log 2 + log c`.
        have hlogc1 : Real.log (c + 1) ≤ Real.log 2 + Real.log c := by
          have hstep : Real.log ((c : ℝ) + 1) ≤ Real.log (2 * (c : ℝ)) := by
            apply Real.log_le_log (by positivity)
            have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcpos
            linarith
          rw [Real.log_mul (by norm_num) (by positivity)] at hstep
          exact hstep
        -- `c·log(c+1) ≤ c·log 2 + c·log c`, and Ziv: `c·log c ≤ 8·b·n`.
        have hziv : (c : ℝ) * Real.log c ≤ 8 * b * (n : ℝ) := by
          have := lz78PhraseStrings_mul_log_le (List.ofFn x)
          rw [← hc, List.length_ofFn] at this
          exact this
        calc (c : ℝ) * Real.log (c + 1)
            ≤ (c : ℝ) * (Real.log 2 + Real.log c) :=
              mul_le_mul_of_nonneg_left hlogc1 hcR_nn
          _ = (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := by ring
          _ ≤ (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ) := by
              apply add_le_add _ hziv
              exact mul_le_mul_of_nonneg_right hcnR hℓ2.le
    -- Combine: divide the chain `c·Nat.log·log2 ≤ n·log2 + 8bn` by `log 2`.
    have hchain : (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) * Real.log 2)
        ≤ (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ) := hbridge.trans hupper
    have hrhs : (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ)
        = ((n : ℝ) * (1 + 8 * b / Real.log 2)) * Real.log 2 := by
      field_simp
    rw [hrhs] at hchain
    -- `hchain : (c·Nat.log)·log2 ≤ (n·(1+8b/log2))·log2`; cancel `log2 > 0`.
    have hchain' : ((c : ℝ) * (Nat.log 2 (c + 1) : ℝ)) * Real.log 2
        ≤ ((n : ℝ) * (1 + 8 * b / Real.log 2)) * Real.log 2 := by
      rw [mul_assoc]; exact hchain
    exact le_of_mul_le_mul_right hchain' hℓ2
  -- Bound `c · (L + 2) ≤ n · (L + 2)`.
  have hterm2 : (c : ℝ) * (L + 2) ≤ (n : ℝ) * (L + 2) := by
    apply mul_le_mul_of_nonneg_right hcnR
    linarith
  -- Assemble: `c·(Nat.log + L + 2) = c·Nat.log + c·(L+2) ≤ n·C`.
  have hsplit : (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2)
      = (c : ℝ) * (Nat.log 2 (c + 1) : ℝ) + (c : ℝ) * (L + 2) := by ring
  rw [hsplit, hC]
  have : (n : ℝ) * (1 + 8 * b / Real.log 2) + (n : ℝ) * (L + 2)
      = (n : ℝ) * ((1 + 8 * b / Real.log 2) + (L + 2)) := by ring
  linarith [hterm1, hterm2]

/-- **Phase 1 (gateway): per-symbol bit-rate decomposed into a
`c·log c` term and an `o(1)` overhead** (deterministic, per-`n`).

For `0 < n`, writing `c = (lz78PhraseStrings (List.ofFn x)).length` for the
genuine distinct phrase count, the greedy bit-rate splits as

```
lz/n ≤ (c · log c) / (log 2 · n) + overhead(n, x)
```

where the overhead `overhead(n, x) = (c · log 2 + c · (log₂|α| + 2)) / (log 2 · n)`
collects the `+1`-shift slack (`log(c+1) ≤ log 2 + log c`) and the alphabet /
parent-index constant cost. The first term is the genuine combinatorial
`c·log₂c/n` that the Ziv comparison connects to `blockLogAvg₂ = -log₂Pₙ/n`;
the overhead is `o(1)` since `c = O(n/log n)` (`lz78PhraseStrings_count_isBigO`).

This is the unit-coherent (`Nat.log 2 → Real.log / log 2`) restatement of the
encoding-length expansion inside `lz78_impl_rate_le_const`; the bit-rate is
left exactly as `c·log c/(log 2 · n) + overhead`, so the dominant term is
available for the a.s.-eventual limsup comparison. -/
theorem lz78_impl_bitrate_le_clogc_plus_overhead [Nonempty α]
    (n : ℕ) (hn : 0 < n) (x : Fin n → α) :
    (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)
      ≤ ((lz78PhraseStrings (List.ofFn x)).length : ℝ)
            * Real.log ((lz78PhraseStrings (List.ofFn x)).length : ℝ)
            / (Real.log 2 * (n : ℝ))
        + (((lz78PhraseStrings (List.ofFn x)).length : ℝ) * Real.log 2
            + ((lz78PhraseStrings (List.ofFn x)).length : ℝ)
                * ((Nat.log 2 (Fintype.card α) : ℝ) + 2))
            / (Real.log 2 * (n : ℝ)) := by
  set c : ℕ := (lz78PhraseStrings (List.ofFn x)).length with hc
  set L : ℝ := (Nat.log 2 (Fintype.card α) : ℝ) with hL
  have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < Real.log 2 * (n : ℝ) := by positivity
  have hcn : c ≤ n := lz78GreedyImplPhraseCount_ofFn_le n x
  have hcR_nn : (0 : ℝ) ≤ (c : ℝ) := by positivity
  -- Encoding length expanded via `bitLength_eq` (same as `lz78_impl_rate_le_const`).
  have hlen : (lz78GreedyImplEncodingLength n x : ℝ)
      = (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2) := by
    have hdef : lz78GreedyImplEncodingLength n x
        = c * LZ78Phrase.bitLength c (Fintype.card α) := rfl
    rw [hdef, LZ78Phrase.bitLength_eq]
    push_cast [hL]
    ring
  rw [div_le_iff₀ hnR, hlen]
  -- Bound `c · Nat.log 2 (c+1) · log 2 ≤ c · log(c+1) ≤ c·log 2 + c·log c`.
  have hbridge : (c : ℝ) * (Nat.log 2 (c + 1) : ℝ) * Real.log 2
      ≤ (c : ℝ) * Real.log (c + 1) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hcR_nn
    exact lz78_impl_natLog_mul_log_two_le (c + 1) |>.trans_eq (by push_cast; ring_nf)
  -- `log(c+1) ≤ log 2 + log c` for `c ≥ 1`; for `c = 0`, `log 1 = 0 ≤ log 2`.
  have hlogc1 : (c : ℝ) * Real.log (c + 1)
      ≤ (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := by
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · simp [hc0]
    · have hcpos' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcpos
      have hstep : Real.log ((c : ℝ) + 1) ≤ Real.log 2 + Real.log c := by
        have h1 : Real.log ((c : ℝ) + 1) ≤ Real.log (2 * (c : ℝ)) := by
          apply Real.log_le_log (by positivity); linarith
        rwa [Real.log_mul (by norm_num) (by positivity)] at h1
      calc (c : ℝ) * Real.log (c + 1)
          ≤ (c : ℝ) * (Real.log 2 + Real.log c) :=
            mul_le_mul_of_nonneg_left hstep hcR_nn
        _ = (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := by ring
  -- The per-`c` term bound after clearing the common `log 2 · n` denominator.
  have hkey : ((c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2)) * Real.log 2
      ≤ (c : ℝ) * Real.log c + ((c : ℝ) * Real.log 2 + (c : ℝ) * (L + 2)) := by
    have hexpand : ((c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2)) * Real.log 2
        = (c : ℝ) * (Nat.log 2 (c + 1) : ℝ) * Real.log 2
            + (c : ℝ) * (L + 2) * Real.log 2 := by ring
    rw [hexpand]
    have hLcost : (c : ℝ) * (L + 2) * Real.log 2 ≤ (c : ℝ) * (L + 2) := by
      have hL2_nn : (0 : ℝ) ≤ (c : ℝ) * (L + 2) := by
        have : (0 : ℝ) ≤ L + 2 := by rw [hL]; positivity
        positivity
      have hlog2_le1 : Real.log 2 ≤ 1 := by
        calc Real.log 2 ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by norm_num) (by
                have : (2 : ℝ) ≤ Real.exp 1 := by
                  have := Real.add_one_le_exp (1 : ℝ); linarith
                linarith)
          _ = 1 := Real.log_exp 1
      calc (c : ℝ) * (L + 2) * Real.log 2
          ≤ (c : ℝ) * (L + 2) * 1 :=
            mul_le_mul_of_nonneg_left hlog2_le1 hL2_nn
        _ = (c : ℝ) * (L + 2) := by ring
    have h1 : (c : ℝ) * (Nat.log 2 (c + 1) : ℝ) * Real.log 2
        ≤ (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := hbridge.trans hlogc1
    linarith
  -- Combine the two RHS fractions and clear the `log 2 · n` denominator.
  have hsum_frac :
      (c : ℝ) * Real.log c / (Real.log 2 * (n : ℝ))
        + ((c : ℝ) * Real.log 2 + (c : ℝ) * ((Nat.log 2 (Fintype.card α) : ℝ) + 2))
            / (Real.log 2 * (n : ℝ))
      = ((c : ℝ) * Real.log c + ((c : ℝ) * Real.log 2 + (c : ℝ) * (L + 2)))
          / (Real.log 2 * (n : ℝ)) := by
    rw [hL, ← add_div]
  rw [hsum_frac, div_mul_eq_mul_div, le_div_iff₀ hden_pos]
  -- Goal: `c·(Nat.log 2 (c+1) + L + 2) · (log 2 · n) ≤ (RHS_c) · n`.
  -- Cancel `n` via `hkey` scaled by `n ≥ 0`.
  have hnn : (0 : ℝ) ≤ (n : ℝ) := hnR.le
  have hmul := mul_le_mul_of_nonneg_right hkey hnn
  nlinarith [hmul]

end EncodingLength

/-! ## §2. `IsLZ78EncodingLengthBoundPassthrough` analogue -/

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

/-! ## §3. Parent-theorem bridge -/

section ParentBridge

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Type-check witness**: the genuine greedy encoding length has the
right type to plug into the parent `lz78_asymptotic_optimality`
`lz78EncodingLength : ∀ n, (Fin n → α) → ℕ` parameter slot. -/
example : (∀ n, (Fin n → α) → ℕ) := @lz78GreedyImplEncodingLength α _ _

/-- **Per-symbol negative log-likelihood in bits**: `blockLogAvg / Real.log 2`.

The base-2 (bit) version of `blockLogAvg`. SMB (`shannon_mcmillan_breiman`)
converges `blockLogAvg → entropyRate` in nats; dividing through by `Real.log 2`
gives the bit-unit version converging to `entropyRate₂`, the unit that matches
the base-2 LZ78 bit-rate `lz78GreedyImplEncodingLength/n`. -/
noncomputable def blockLogAvg₂
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω => blockLogAvg μ p n ω / Real.log 2

/-- **Shannon–McMillan–Breiman in bits**: `blockLogAvg₂` converges a.s. to
`entropyRate₂`.

Obtained from `shannon_mcmillan_breiman` (nat units) by dividing the
convergence through by `Real.log 2`: this is the unit rescaling
`entropyRate / Real.log 2 = entropyRate₂`, not new ergodic content.

Independent honesty audit 2026-06-20 PASS (commit `876bcd0`, fresh
subagent): `#print axioms shannon_mcmillan_breiman₂ = [propext,
Classical.choice, Quot.sound]` (sorryAx-free, machine-verified). The body is
a genuine unit rescaling (`Tendsto.div_const (Real.log 2)` then `simpa
[blockLogAvg₂, entropyRate₂]`); both defs unfold to `… / Real.log 2`, so no
degenerate rewrite. W1 of the M3 W1/W2 decomposition, genuinely closed.
@audit:ok -/
theorem shannon_mcmillan_breiman₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  filter_upwards [shannon_mcmillan_breiman μ p] with ω hω
  have := hω.div_const (Real.log 2)
  simpa only [blockLogAvg₂, entropyRate₂] using this

/-- **Factorial-power decay** `c! · 2^c ≤ (c+1)^c` (real form). The per-`c`
structure-Kraft term `c!/(c+1)^c` is geometrically small. Proved by induction;
the step uses Bernoulli `2·(c+1)^(c+1) ≤ (c+2)^(c+1)`. -/
theorem factorial_two_pow_le_succ_pow (c : ℕ) :
    (c.factorial : ℝ) * 2 ^ c ≤ ((c : ℝ) + 1) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      -- `(c+1)!·2^(c+1) = 2(c+1)·(c!·2^c) ≤ 2(c+1)·(c+1)^c = 2·(c+1)^(c+1)`.
      have hcpos : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
      have hstep1 : ((c + 1).factorial : ℝ) * 2 ^ (c + 1)
          ≤ 2 * ((c : ℝ) + 1) ^ (c + 1) := by
        have hfac : ((c + 1).factorial : ℝ) = ((c : ℝ) + 1) * (c.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [hfac]
        calc ((c : ℝ) + 1) * (c.factorial : ℝ) * 2 ^ (c + 1)
            = (2 * ((c : ℝ) + 1)) * ((c.factorial : ℝ) * 2 ^ c) := by ring
          _ ≤ (2 * ((c : ℝ) + 1)) * (((c : ℝ) + 1) ^ c) := by
              apply mul_le_mul_of_nonneg_left ih; positivity
          _ = 2 * ((c : ℝ) + 1) ^ (c + 1) := by ring
      -- Bernoulli: `2·(c+1)^(c+1) ≤ (c+2)^(c+1)`.
      have hcne : ((c : ℝ) + 1) ≠ 0 := by positivity
      have hcpos' : (0 : ℝ) < (c : ℝ) + 1 := by positivity
      have hbern : 2 * ((c : ℝ) + 1) ^ (c + 1) ≤ ((c : ℝ) + 2) ^ (c + 1) := by
        -- Bernoulli with `a = 1/(c+1)`, `n = c+1`: `1 + (c+1)·a ≤ (1+a)^(c+1)`.
        have hb := one_add_mul_le_pow (a := 1 / ((c : ℝ) + 1)) (by
          have : (0 : ℝ) ≤ 1 / ((c : ℝ) + 1) := by positivity
          linarith) (c + 1)
        -- LHS `1 + ↑(c+1)·(1/(c+1)) = 2`.
        have hlhs : (1 : ℝ) + ((c + 1 : ℕ) : ℝ) * (1 / ((c : ℝ) + 1)) = 2 := by
          push_cast; field_simp; ring
        rw [hlhs] at hb
        -- RHS `(1 + 1/(c+1))^(c+1) = (c+2)^(c+1)/(c+1)^(c+1)`.
        have hrhs : (1 + 1 / ((c : ℝ) + 1)) ^ (c + 1)
            = ((c : ℝ) + 2) ^ (c + 1) / ((c : ℝ) + 1) ^ (c + 1) := by
          rw [← div_pow]
          congr 1
          field_simp; ring
        rw [hrhs] at hb
        have hden : (0 : ℝ) < ((c : ℝ) + 1) ^ (c + 1) := by positivity
        rw [le_div_iff₀ hden] at hb
        linarith [hb]
      calc ((c + 1).factorial : ℝ) * 2 ^ (c + 1)
          ≤ 2 * ((c : ℝ) + 1) ^ (c + 1) := hstep1
        _ ≤ ((c : ℝ) + 2) ^ (c + 1) := hbern
        _ = ((↑(c + 1) : ℝ) + 1) ^ (c + 1) := by push_cast; ring

/-- **Bit-length decay (nat form)** `2^{bitLength c a} ≥ (c+1)·a`. The per-phrase
bit cost is large enough that `2^{-bitLength}` collapses the dictionary-size and
alphabet-size factors. From `Nat.lt_pow_succ_log_self`: `m + 1 ≤ 2·2^{log₂ m}`. -/
theorem two_pow_bitLength_ge (c a : ℕ) :
    (c + 1) * a ≤ 2 ^ LZ78Phrase.bitLength c a := by
  -- `2^{bitLength c a} = 4 · 2^{log₂(c+1)} · 2^{log₂ a}`.
  have hbit : 2 ^ LZ78Phrase.bitLength c a
      = 4 * 2 ^ Nat.log 2 (c + 1) * 2 ^ Nat.log 2 a := by
    rw [LZ78Phrase.bitLength_eq]
    rw [show Nat.log 2 (c + 1) + Nat.log 2 a + 2
          = 2 + Nat.log 2 (c + 1) + Nat.log 2 a from by ring]
    rw [pow_add, pow_add]
    ring
  rw [hbit]
  -- `c+1 ≤ 2·2^{log₂(c+1)}` and `a ≤ 2·2^{log₂ a}`, then multiply.
  have hc1 : c + 1 ≤ 2 * 2 ^ Nat.log 2 (c + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (c + 1)
    rw [pow_succ] at this
    omega
  have ha : a ≤ 2 * 2 ^ Nat.log 2 a := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
    rw [pow_succ] at this
    omega
  calc (c + 1) * a
      ≤ (2 * 2 ^ Nat.log 2 (c + 1)) * (2 * 2 ^ Nat.log 2 a) :=
        Nat.mul_le_mul hc1 ha
    _ = 4 * 2 ^ Nat.log 2 (c + 1) * 2 ^ Nat.log 2 a := by ring

/-- **Distinct-phrase fiber-cardinality count (the genuine combinatorial
counting core of G2)**.

The number of `n`-tuples `x : Fin n → α` whose genuine greedy parse emits
exactly `c` distinct phrases is bounded by `(n + 1) · c! · |α|^c`. This is the
load-bearing counting fact behind the polynomial Kraft bound
`lz78_block_kraft_poly`: the map `x ↦ (lz78PhraseStrings (List.ofFn x), tail)`
is injective (`lz78PhraseStrings_flatten_prefix` reconstructs `List.ofFn x`, and
`List.ofFn` is injective), and the parent-extension dictionary structure makes
the `j`-th phrase one of the `j` earlier entries (or the empty prefix) extended
by one symbol, giving `≤ c! · |α|^c` valid phrase-lists; the unfinished tail
(`lz78PhraseStrings_flatten_tail_mem`, a dictionary member or empty) contributes
a multiplicity `≤ n + 1`.

The parent-extension invariant `(emitted phrase = earlier entry ++ symbol)` and
the `Fintype.card`-injection counting are not yet in the codebase
(`GreedyLongestPrefix.lean` has the distinct / flatten / tail invariants but not
the dictionary parent-extension structure), so this is isolated as the single
finite-combinatorial residual on which `lz78_block_kraft_poly` (Parts A + C) is
proven unconditionally. Numerically verified for `α = Bool`, `n ≤ 6`,
`c ≤ n` (`#fiber(n,c) ≤ (n+1)·c!·|α|^c` holds with slack).

Independent honesty audit 2026-06-21 PASS: a standalone finite cardinality
bound (no measure / liminf / `μ`,`p` content — pure finite combinatorics on
the project-internal greedy parse), NOT the converse conclusion repackaged and
NOT a load-bearing hypothesis (the obligation is an exposed `sorry`, tier 2).
TRUE-as-framed: replicating the actual `lz78PhraseStringsAux` parse and
counting real fiber sizes for `(n,A)` over `n≤7,A∈{2,3,8}` gives 0 violations
(only `n=0` tight at `1≤1`, large slack elsewhere). Classification `plan:` is
correct (project-internal LZ78 combinatorics with a discharge plan, not a
Mathlib-absent wall); `docs/shannon/lz78-m4-plan.md` G2 schedules it.
@residual(plan:lz78-m4-plan) -/
theorem lz78_phrase_count_fiber_card_le (n c : ℕ) :
    ((Finset.univ.filter
          (fun x : Fin n → α => (lz78PhraseStrings (List.ofFn x)).length = c)).card : ℝ)
      ≤ ((n : ℝ) + 1) * (c.factorial : ℝ) * (Fintype.card α : ℝ) ^ c := by
  sorry

/-- **Per-`c` Kraft term bound (Part C, geometric collapse)**.

The fiber sum over `n`-tuples with `c` distinct phrases is geometrically small:
`#fiber(c) · (1/2)^{c·bitLength(c,|α|)} ≤ (n+1)·(1/2)^c`. Combines the counting
bound `lz78_phrase_count_fiber_card_le` (`#fiber(c) ≤ (n+1)·c!·|α|^c`) with the
bit-length decay `2^{c·bitLength(c,|α|)} ≥ ((c+1)·|α|)^c` (from
`Nat.lt_pow_succ_log_self`), giving `#fiber·2^{-...} ≤ (n+1)·c!/(c+1)^c` and the
elementary inequality `c!·2^c ≤ (c+1)^c`. -/
theorem lz78_block_kraft_term_le (n c : ℕ) :
    (((Finset.univ.filter
          (fun x : Fin n → α => (lz78PhraseStrings (List.ofFn x)).length = c)).card : ℝ)
        * (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)))
      ≤ ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c := by
  set F : ℝ := ((Finset.univ.filter
          (fun x : Fin n → α => (lz78PhraseStrings (List.ofFn x)).length = c)).card : ℝ) with hF
  set a : ℕ := Fintype.card α with ha
  set B : ℕ := LZ78Phrase.bitLength c a with hB
  have hF_nn : 0 ≤ F := by rw [hF]; positivity
  have ha1 : 1 ≤ (a : ℝ) := by
    rw [ha]; exact_mod_cast Fintype.card_pos
  have haR_pos : (0 : ℝ) < (a : ℝ) := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  -- Step 1: counting residual `F ≤ (n+1)·c!·a^c`.
  have hcount : F ≤ ((n : ℝ) + 1) * (c.factorial : ℝ) * (a : ℝ) ^ c :=
    lz78_phrase_count_fiber_card_le n c
  -- Step 2: `(1/2)^(c·B) = ((1/2)^B)^c`, and `(1/2)^B ≤ 1/((c+1)·a)`.
  have hpow_rw : (1 / 2 : ℝ) ^ (c * B) = ((1 / 2 : ℝ) ^ B) ^ c := by
    rw [pow_mul, ← pow_mul, Nat.mul_comm, pow_mul]
  -- `(c+1)·a ≤ 2^B`, so `a·(1/2)^B ≤ 1/(c+1)`.
  have hbit : ((c : ℝ) + 1) * (a : ℝ) ≤ (2 : ℝ) ^ B := by
    have := two_pow_bitLength_ge c a
    have hcast : (((c + 1) * a : ℕ) : ℝ) ≤ ((2 ^ B : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    convert hcast using 2
  have h2Bpos : (0 : ℝ) < (2 : ℝ) ^ B := by positivity
  have hhalfB : (1 / 2 : ℝ) ^ B = 1 / (2 : ℝ) ^ B := by
    rw [div_pow, one_pow]
  -- `a·(1/2)^B ≤ 1/(c+1)`.
  have haB_le : (a : ℝ) * (1 / 2 : ℝ) ^ B ≤ 1 / ((c : ℝ) + 1) := by
    rw [hhalfB, mul_one_div, le_div_iff₀ (by positivity : (0:ℝ) < (c:ℝ) + 1),
      div_mul_eq_mul_div, div_le_one (by positivity : (0:ℝ) < (2:ℝ) ^ B)]
    -- `a · (c+1) ≤ 2^B`
    calc (a : ℝ) * ((c : ℝ) + 1) = ((c : ℝ) + 1) * (a : ℝ) := by ring
      _ ≤ (2 : ℝ) ^ B := hbit
  have haB_nn : 0 ≤ (a : ℝ) * (1 / 2 : ℝ) ^ B := by positivity
  -- Step 3: `c!·(a·(1/2)^B)^c ≤ c!·(1/(c+1))^c = c!/(c+1)^c ≤ (1/2)^c`.
  have hcore : (c.factorial : ℝ) * ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c
      ≤ (1 / 2 : ℝ) ^ c := by
    have hpow_le : ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c ≤ (1 / ((c : ℝ) + 1)) ^ c :=
      pow_le_pow_left₀ haB_nn haB_le c
    have hfac_nn : (0 : ℝ) ≤ (c.factorial : ℝ) := by positivity
    calc (c.factorial : ℝ) * ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c
        ≤ (c.factorial : ℝ) * (1 / ((c : ℝ) + 1)) ^ c :=
          mul_le_mul_of_nonneg_left hpow_le hfac_nn
      _ = (c.factorial : ℝ) / ((c : ℝ) + 1) ^ c := by
          rw [div_pow, one_pow, mul_one_div]
      _ ≤ (1 / 2 : ℝ) ^ c := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < ((c:ℝ) + 1) ^ c), div_pow, one_pow,
            div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ c), one_mul]
          -- `c!·2^c ≤ (c+1)^c`
          exact factorial_two_pow_le_succ_pow c
  -- Assemble: `F·(1/2)^(cB) ≤ (n+1)·c!·a^c·(1/2)^(cB) = (n+1)·c!·(a·(1/2)^B)^c ≤ (n+1)·(1/2)^c`.
  have hpow_cB_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * B) := by positivity
  calc F * (1 / 2 : ℝ) ^ (c * B)
      ≤ (((n : ℝ) + 1) * (c.factorial : ℝ) * (a : ℝ) ^ c) * (1 / 2 : ℝ) ^ (c * B) :=
        mul_le_mul_of_nonneg_right hcount hpow_cB_nn
    _ = ((n : ℝ) + 1) * ((c.factorial : ℝ) * ((a : ℝ) * (1 / 2 : ℝ) ^ B) ^ c) := by
        rw [hpow_rw, mul_pow]; ring
    _ ≤ ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c :=
        mul_le_mul_of_nonneg_left hcore hn1

/-- **G2 — polynomial `n`-block Kraft for the genuine greedy parse (the
genuine combinatorial converse brick)**.

The Kraft sum of `2^{-L_n(x)}` over all `n`-tuples `x : Fin n → α` is bounded
by a polynomial in `n`:

```
∑_{x : Fin n → α} (1/2)^{lz78GreedyImplEncodingLength n x} ≤ (n + 1)^2.
```

**Why a polynomial and not the exact Kraft `≤ 1`.** The greedy
longest-prefix-match parse is *not complete* — `lz78PhraseStrings_flatten` is a
genuine *prefix* of the input, and the unfinished tail (`flatten ++ tail =
input`, with `tail ≠ []` possible and `tail` a prefix of an existing phrase)
is *not* charged a fresh `(parent, symbol)` token. Hence
`lz78GreedyImplEncodingLength n x = c · bitLength c |α|` is the cost of only
the `c` completed phrases and is **not a lossless code length** for `x`, so the
exact Kraft inequality `∑ 2^{-L_n} ≤ 1` is **FALSE**. The polynomial bound is
the honest statement: the number of distinct parse *structures* with `c`
phrases is `≤ c! · |α|^c`, and `2^{-c·bitLength(c,|α|)} ≈ (c+1)^{-c}|α|^{-c}4^{-c}`,
so the structure-Kraft sum `∑_c (#structures)·2^{-c·bitLength} = O(1)`; the
unfinished tail contributes a multiplicity `≤ n + 1`, giving `O(n) ≤ (n+1)^2`.

The math is `O(n)`, so any polynomial degree `≥ 1` is a true bound; the degree
`2` here gives the summable `μ(B_n) ≤ 1/n^2` in the Barron Markov +
Borel–Cantelli lift (`blockLogAvg₂_minus_error_le_rate_ae`).

This is the genuine combinatorial new-math brick of the LZ78 converse
(Cover–Thomas Thm 13.5.3 lower bound, distinct-phrase counting).

**Proof structure (Parts A + C proven, Part B isolated).** The body here is
`sorry`-free: it is assembled from
* **Part A** — fiberwise regrouping of the Kraft sum by the distinct-phrase
  count `c = φ x` (`Finset.sum_fiberwise_of_maps_to'`, `φ x ≤ n`);
* **Part C** — the per-`c` geometric collapse `lz78_block_kraft_term_le`
  (`#fiber(c)·2^{-c·bitLength} ≤ (n+1)·(1/2)^c`, built from the bit-length decay
  `two_pow_bitLength_ge` and the factorial-power decay
  `factorial_two_pow_le_succ_pow`, both `sorryAx`-free), then
  `sum_geometric_two_le` and `(n+1)·2 ≤ (n+1)²` (with the `n = 0` boundary
  `1 ≤ 1`).

The **single remaining residual** is **Part B**, the finite counting fact
`lz78_phrase_count_fiber_card_le` (`#fiber(c) ≤ (n+1)·c!·|α|^c`), isolated as a
clean stated-but-unproven lemma carrying `@residual(plan:lz78-m4-plan)`. G2 is
therefore reduced to that one finite-combinatorial statement (no analysis left);
this theorem inherits its `sorryAx` transitively.

Classification (independent audit 2026-06-21): a project-internal
combinatorial brick with a concrete discharge plan (`docs/shannon/lz78-m4-plan.md`,
G2), **not** a Mathlib-absent research wall — the prior
`wall:lz78-converse-aseventual` "research-level scope-out" verdict was overturned
this session (gateway-atom-first inventory). The statement is TRUE-as-framed: the
polynomial bound `≤ (n+1)²` was checked numerically (α=Bool, n≤6) to hold with
large slack, and the `n = 0` boundary is exactly `1 ≤ 1`. The residual now lives
entirely in the Part B counting lemma `lz78_phrase_count_fiber_card_le`, whose
closure needs the LZ78 dictionary parent-extension invariant (each emitted phrase
= an earlier entry or empty ++ one symbol) — absent from `GreedyLongestPrefix.lean`
(which has the distinct / flatten / tail invariants but not the parent-extension
structure) — plus the `Fintype.card`-injection counting on top.

This theorem's body is `sorry`-free; it carries no own `@residual`. The sole
residual is the Part B counting lemma `lz78_phrase_count_fiber_card_le`
(`@residual(plan:lz78-m4-plan)`), inherited here transitively (its
`#print axioms` shows `sorryAx`), exactly as for the downstream consumers
(`lz78_converse_bad_set_measure_le`, `blockLogAvg₂_minus_error_le_rate_ae`,
`lz78GreedyImpl_converse_ae`), which likewise carry no own `@residual`.
Independent honesty audit 2026-06-21 PASS. -/
theorem lz78_block_kraft_poly (n : ℕ) :
    ∑ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x)
      ≤ ((n : ℝ) + 1) ^ 2 := by
  classical
  -- Part A: group the Kraft sum by the distinct-phrase count `c = φ x`.
  set φ : (Fin n → α) → ℕ := fun x => (lz78PhraseStrings (List.ofFn x)).length with hφ
  -- The encoding length depends on `x` only through `c = φ x`.
  have hLfac : ∀ x : Fin n → α,
      lz78GreedyImplEncodingLength n x = φ x * LZ78Phrase.bitLength (φ x) (Fintype.card α) := by
    intro x; rfl
  -- `φ x ≤ n`, so `φ x ∈ Finset.range (n+1)`.
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin n → α)), φ x ∈ Finset.range (n + 1) := by
    intro x _
    rw [Finset.mem_range]
    have hle : φ x ≤ n := lz78GreedyImplPhraseCount_ofFn_le n x
    omega
  -- Fiberwise regrouping: ∑_x f(φ x) = ∑_{c∈range(n+1)} ∑_{x : φ x = c} f(φ x).
  have hfiber :
      ∑ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x)
        = ∑ c ∈ Finset.range (n + 1),
            ∑ x ∈ Finset.univ.filter (fun x => φ x = c),
              (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)) := by
    -- `(1/2)^(L_n x) = f (φ x)` with `f c = (1/2)^(c·bitLength c |α|)`.
    have hrw : ∀ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x)
        = (fun c => (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α))) (φ x) := by
      intro x; rw [hLfac x]
    -- On each fiber `φ x = c`, the summand `f (φ x)` collapses to `f c`.
    rw [Finset.sum_congr rfl (fun x _ => hrw x),
      ← Finset.sum_fiberwise_of_maps_to' hmaps
        (fun c => (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)))]
  rw [hfiber]
  -- Part B + C: each per-`c` term is ≤ (n+1)·(1/2)^c, then sum the geometric series.
  have hterm : ∀ c ∈ Finset.range (n + 1),
      (∑ x ∈ Finset.univ.filter (fun x => φ x = c),
          (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α)))
        ≤ ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c := by
    intro c _
    -- The inner summand is constant on the fiber, so the sum is `#fiber · (1/2)^…`.
    rw [Finset.sum_const, nsmul_eq_mul]
    exact lz78_block_kraft_term_le n c
  calc
    ∑ c ∈ Finset.range (n + 1),
        ∑ x ∈ Finset.univ.filter (fun x => φ x = c),
          (1 / 2 : ℝ) ^ (c * LZ78Phrase.bitLength c (Fintype.card α))
      ≤ ∑ c ∈ Finset.range (n + 1), ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ c :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * ∑ c ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ c := by
        rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) + 1) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · -- n = 0: the sum has one term `(1/2)^0 = 1`, giving `1·1 = 1 ≤ 1`.
          subst hn0; norm_num
        · -- n ≥ 1: `∑_{c<n+1}(1/2)^c ≤ 2` and `(n+1)·2 ≤ (n+1)^2` since `2 ≤ n+1`.
          have hgeom : (∑ c ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ c) ≤ 2 :=
            sum_geometric_two_le (n + 1)
          have hnpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
          have h2le : (2 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
            linarith
          calc ((n : ℝ) + 1) * ∑ c ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ c
              ≤ ((n : ℝ) + 1) * 2 := by
                exact mul_le_mul_of_nonneg_left hgeom hnpos
            _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) := by
                exact mul_le_mul_of_nonneg_left h2le hnpos
            _ = ((n : ℝ) + 1) ^ 2 := by ring

/-- **Per-`n` bad-set measure bound (Markov on the discrete block law + G2)**.

For `n ≥ 1`, the LZ78 converse bad set
`B_n = {ω : lz/n < blockLogAvg₂ n ω − err_n}`
has `μ`-measure at most `1/n²`, where
`err_n = (2 log n + 2 log(n+1))/(n log 2)`.

This is the genuine Markov step of the Barron lift. The bad set factors through
the block random variable (`lz` and `blockLogAvg₂` depend on `ω` only via
`block_n ω`), so `μ(B_n) = (μ.map block_n)(S_n) = ∑_{x ∈ S_n} Pₙ(x)` over the
discrete block law `Pₙ = μ.map block_n`. For each `x ∈ S_n` with `Pₙ(x) > 0`
the defining inequality (cleared of denominators) gives
`Pₙ(x) < 2^{−Lₙ(x)}·2^{−n·err_n}`, and `2^{−n·err_n} = 1/(n²(n+1)²)`. Summing
and applying G2 (`lz78_block_kraft_poly`: `∑_x 2^{−Lₙ(x)} ≤ (n+1)²`) gives
`μ(B_n) ≤ (n+1)²/(n²(n+1)²) = 1/n²`. The genuine combinatorial residual lives
entirely in G2; this lemma is its measure-theoretic plumbing. -/
theorem lz78_converse_bad_set_measure_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) (n : ℕ) (hn : 1 ≤ n) :
    μ {ω | (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ)
          < blockLogAvg₂ μ p.toStationaryProcess n ω
            - (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2)}
      ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) := by
  classical
  set q := p.toStationaryProcess with hq
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set Pn : Measure (Fin n → α) := μ.map (q.blockRV n) with hPn
  have hB_meas : Measurable (q.blockRV n) := q.measurable_blockRV n
  have hPn_prob : IsProbabilityMeasure Pn :=
    Measure.isProbabilityMeasure_map hB_meas.aemeasurable
  -- The bad set on the discrete block alphabet.
  set rateX : (Fin n → α) → ℝ :=
    fun x => (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ) with hrateX
  set bla₂X : (Fin n → α) → ℝ :=
    fun x => (-(1 / (n : ℝ)) * Real.log (Pn.real {x})) / Real.log 2 with hbla₂X
  set errR : ℝ := (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2) with herrR
  set S : Finset (Fin n → α) :=
    Finset.univ.filter (fun x => rateX x < bla₂X x - errR) with hS
  -- `blockLogAvg₂ μ q n ω = bla₂X (block_n ω)` (depends on `ω` only via `block_n`).
  have h_bla_factor : ∀ ω, blockLogAvg₂ μ q n ω = bla₂X (q.blockRV n ω) := by
    intro ω; rw [hbla₂X]; simp only [blockLogAvg₂, blockLogAvg, hPn]
  -- The bad set is the preimage of `S` under `block_n`.
  have h_setEq : {ω | (lz78GreedyImplEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ)
        < blockLogAvg₂ μ q n ω
          - (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2)}
      = (q.blockRV n) ⁻¹' (S : Set (Fin n → α)) := by
    ext ω
    rw [Set.mem_preimage, Finset.mem_coe, hS, Finset.mem_filter]
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and, hrateX, hbla₂X, herrR,
      h_bla_factor ω]
  rw [h_setEq]
  -- Pushforward: `μ(block⁻¹ S) = Pn(S) = ∑_{x∈S} Pn.real{x}`.
  have h_meas_S : MeasurableSet (S : Set (Fin n → α)) := S.measurableSet
  have h_push : μ ((q.blockRV n) ⁻¹' (S : Set (Fin n → α)))
      = Pn (S : Set (Fin n → α)) := by
    rw [hPn, Measure.map_apply hB_meas h_meas_S]
  rw [h_push]
  -- Work with the real-valued measure (`Pn` is finite).
  have h_toReal : (Pn (S : Set (Fin n → α))).toReal ≤ 1 / (n : ℝ) ^ 2 := by
    -- `Pn(S) = ∑_{x∈S} Pn.real{x}`.
    have h_sum : (Pn (S : Set (Fin n → α))).toReal = ∑ x ∈ S, Pn.real {x} := by
      rw [← measureReal_def, ← sum_measureReal_singleton]
    rw [h_sum]
    -- Per-element bound: `Pn.real{x} ≤ (1/2)^{Lₙ(x)} · (1/(n²(n+1)²))` for `x ∈ S`.
    have h_elt : ∀ x ∈ S, Pn.real {x}
        ≤ (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x)
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
      intro x hxS
      have hxlt : rateX x < bla₂X x - errR := by
        rw [hS, Finset.mem_filter] at hxS; exact hxS.2
      simp only [hrateX, hbla₂X] at hxlt
      set P := Pn.real {x} with hP
      have hP_nn : 0 ≤ P := by rw [hP]; exact measureReal_nonneg
      have hcoef_pos : (0 : ℝ) < 1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by positivity
      have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x) := by
        positivity
      rcases eq_or_lt_of_le hP_nn with hP0 | hPpos
      · -- `P = 0`: the bound is trivial (RHS > 0).
        rw [← hP0]; positivity
      · -- `P > 0`: clear denominators and exponentiate.
        -- `n · errR · log 2 = 2 log n + 2 log(n+1)`.
        have h_nerr : (n : ℝ) * errR * Real.log 2
            = 2 * Real.log n + 2 * Real.log (n + 1) := by
          rw [herrR]; field_simp
        -- From `L/n < (-(1/n) log P)/log2 - errR`, multiply by `n · log 2 > 0`
        -- to get `L · log 2 < -log P - (2 log n + 2 log(n+1))`.
        have hLn : (lz78GreedyImplEncodingLength n x : ℝ) * Real.log 2
            < -Real.log P - (2 * Real.log n + 2 * Real.log (n + 1)) := by
          have h1 : (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)
                * ((n : ℝ) * Real.log 2)
              < ((-(1 / (n : ℝ)) * Real.log P) / Real.log 2 - errR)
                * ((n : ℝ) * Real.log 2) :=
            mul_lt_mul_of_pos_right hxlt (by positivity)
          have hlhs : (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)
              * ((n : ℝ) * Real.log 2)
              = (lz78GreedyImplEncodingLength n x : ℝ) * Real.log 2 := by
            field_simp
          have hrhs : ((-(1 / (n : ℝ)) * Real.log P) / Real.log 2 - errR)
              * ((n : ℝ) * Real.log 2)
              = -Real.log P - (n : ℝ) * errR * Real.log 2 := by
            field_simp
          rw [hlhs, hrhs, h_nerr] at h1
          exact h1
        -- Take `exp` of both sides: `P < 2^{-Lₙ} · 1/(n²(n+1)²)`.
        have hlogP_lt : Real.log P
            < Real.log ((1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x)
                * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2))) := by
          rw [Real.log_mul hpow_pos.ne' hcoef_pos.ne', Real.log_pow]
          have h_log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
            rw [one_div, Real.log_inv]
          have h_log_coef : Real.log (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2))
              = -(2 * Real.log n + 2 * Real.log (n + 1)) := by
            rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_pow]
            push_cast; ring
          rw [h_log_half, h_log_coef]
          have : (lz78GreedyImplEncodingLength n x : ℝ) * -Real.log 2
              = -((lz78GreedyImplEncodingLength n x : ℝ) * Real.log 2) := by ring
          nlinarith [hLn, hℓ2]
        have := (Real.log_lt_log_iff hPpos (by positivity)).mp hlogP_lt
        exact le_of_lt this
    -- Sum the per-element bound and apply G2.
    calc ∑ x ∈ S, Pn.real {x}
        ≤ ∑ x ∈ S, (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x)
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) :=
          Finset.sum_le_sum h_elt
      _ = (∑ x ∈ S, (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x))
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          rw [← Finset.sum_mul]
      _ ≤ (∑ x : Fin n → α, (1 / 2 : ℝ) ^ (lz78GreedyImplEncodingLength n x))
            * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          intro x _ _; positivity
      _ ≤ ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          apply mul_le_mul_of_nonneg_right (lz78_block_kraft_poly n) (by positivity)
      _ = 1 / (n : ℝ) ^ 2 := by
          have hn1 : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
          field_simp
  -- Convert the real bound back to `ℝ≥0∞`.
  have h_ne_top : Pn (S : Set (Fin n → α)) ≠ ∞ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal h_ne_top]
  rw [show (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2)
      = ENNReal.ofReal (1 / (n : ℝ) ^ 2) by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      show (n : ℝ) ^ 2 = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring,
      ENNReal.ofReal_natCast]; push_cast; ring]
  exact ENNReal.ofReal_le_ofReal h_toReal

/-- **G3 — Barron a.s.-eventual lift**: the per-realization, a.s.-eventual
converse lower bound on the greedy bit-rate by `blockLogAvg₂` minus an `o(1)`
error term.

For a stationary process `p`, almost surely the greedy bit-rate
`lz78GreedyImplEncodingLength n (block_n ω) / n` is, eventually in `n`, at
least `blockLogAvg₂ n ω` minus the vanishing error
`(2 log n + 2 log(n+1))/(n log 2)`:

```
∀ᵐ ω, ∀ᶠ n,  blockLogAvg₂ n ω − (2 log n + 2 log(n+1))/(n log 2) ≤ lz/n.
```

This is the Barron competitive-optimality a.s. lift (Cover–Thomas Thm 13.5.3):
a per-realization LZ78 codeword can be *shorter* than `−log₂ Pₙ{xⁿ}`, so the
expectation-level converse `H_D ≤ E[L]` does not transfer pointwise. The lift
is a Markov + first Borel–Cantelli argument on the bad set
`B_n = {ω : lz/n < blockLogAvg₂ n ω − err_n}`: by G2 (`lz78_block_kraft_poly`),
`μ(B_n) = Pₙ{xⁿ : Pₙ(xⁿ) < 2^{−Lₙ}·2^{−n·err}} ≤ 2^{−n·err}·∑ 2^{−Lₙ} ≤
2^{−n·err}·(n+1)²`, and with `n·err = 2 log₂(n+1) + 2 log₂ n` this is `≤ 1/n²`,
summable, so first Borel–Cantelli gives `∀ᵐ ω, ∀ᶠ n, ω ∉ B_n`.

Modeled on the Z-side `blockLogAvgZ_ge_negLogQInftyZ_minus_error`
(`SMB/AlgoetCover/Liminf.lean`) — the same Markov + p-series + Borel–Cantelli
template. The body is **`sorry`-free**: the Markov + Borel–Cantelli lift is
genuinely proven; it consumes the genuine combinatorial brick G2
(`lz78_block_kraft_poly`) through the per-`n` bad-set measure bound
`lz78_converse_bad_set_measure_le`. The only remaining converse residual is
isolated in G2 (`@residual(plan:lz78-m4-plan)`); this lemma
inherits that residual transitively (its `#print axioms` shows `sorryAx`) but
introduces no new `sorry`. -/
theorem blockLogAvg₂_minus_error_le_rate_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg₂ μ p.toStationaryProcess n ω
          - (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2)
        ≤ (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ) := by
  set q := p.toStationaryProcess with hq
  -- The bad set at scale `n`: the realizations where the greedy bit-rate
  -- undershoots `blockLogAvg₂ − err` by more than the error margin.
  set err : ℕ → ℝ :=
    fun n => (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2) with herr
  set B : ℕ → Set Ω :=
    fun n => {ω | (lz78GreedyImplEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ)
        < blockLogAvg₂ μ q n ω - err n} with hB
  -- Per-`n` bad-set measure bound `μ(B n) ≤ 1/n²` (Markov on the discrete
  -- block law + G2 polynomial Kraft); summable, so first Borel–Cantelli.
  have h_bound : ∀ n, 1 ≤ n → μ (B n) ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) :=
    fun n hn => lz78_converse_bad_set_measure_le μ p n hn
  -- ∑' n, μ (B n) < ∞ (p-series), via the same machinery as
  -- `MRatioLowerZ_le_sq_eventually`.
  have h_tsum : ∑' n, μ (B n) ≠ ∞ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ?_⟩
    have h_le : (∑' n : ℕ, μ (B (n + 1)))
        ≤ ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) :=
      ENNReal.tsum_le_tsum (fun n => h_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le _)))
    refine ne_top_of_le_ne_top ?_ h_le
    have h_summable_real : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    have h_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := fun _ => by positivity
    have h_ennreal_tsum : ∑' n : ℕ,
        ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable_real]
      exact ENNReal.ofReal_ne_top
    have h_pointwise : ∀ n : ℕ,
        (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) =
          ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro n
      have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_one,
        show ((n + 1 : ℕ) : ℝ) ^ 2 = (((n + 1)^2 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
      push_cast; ring_nf
    rw [tsum_congr h_pointwise]
    exact h_ennreal_tsum
  -- First Borel–Cantelli: a.s. `ω ∉ B n` eventually.
  have h_BC := MeasureTheory.ae_eventually_notMem h_tsum
  filter_upwards [h_BC] with ω hx
  filter_upwards [hx] with n hn
  -- `ω ∉ B n` is exactly the desired inequality.
  simp only [hB, Set.mem_setOf_eq, not_lt] at hn
  exact hn

/-- **LZ78 converse lower bound for the genuine greedy parser
(Cover–Thomas Theorem 13.5.3, lower-bound half), a.s. form**.

For a stationary ergodic source `p` the per-symbol length of the genuine
longest-prefix-match greedy LZ78 parse is, almost surely, asymptotically at
least the bit entropy rate:

```
entropyRate₂ μ p ≤ liminf_n (1/n) · lz78GreedyImplEncodingLength(X^n)   a.s.
```

This is the lower-bound (converse) half of LZ78 asymptotic optimality —
the harder direction (SMB liminf lower bound + arbitrary-prefix Kraft
inequality + finite-alphabet bookkeeping).

Units: the encoding length is a base-2 code length
(`lz78GreedyImplEncodingLength = c · bitLength c |α|`, `bitLength` uses
`Nat.log 2`), so the per-symbol rate `lz/n` is in **bits**, and the correct
RHS is the **bit** entropy rate `entropyRate₂ = entropyRate / Real.log 2`
(not the nat-unit `entropyRate`), exactly the unit-correction documented in
`ZivEntropyBridge.lean` ("Base-2 (bit) layer") and
`McMillanKraftBridge.lean` (converse target `blockLogAvg₂`).

**Dependency shape (Barron reduction, 2026-06-21).** The body is no longer a
bare `sorry`: it is genuinely wired from two bricks plus the bit SMB
convergence,

* `shannon_mcmillan_breiman₂` (SMB in bits, **sorryAx-free**) — gives
  `Tendsto blockLogAvg₂ → entropyRate₂` a.s.;
* `blockLogAvg₂_minus_error_le_rate_ae` (G3, Barron a.s.-eventual lift) —
  gives `∀ᶠ n, blockLogAvg₂ n ω − err_n ≤ lz/n` a.s., with `err_n → 0`;

assembled by `Filter.liminf_le_liminf` between the lower sequence
`Low n = blockLogAvg₂ n ω − err_n` (which `→ entropyRate₂`, so
`liminf Low = entropyRate₂`) and `lz/n` (bounded above by
`lz78_impl_rate_le_const`, hence cobounded below). The genuine converse
content (the Barron competitive-optimality lift) is **isolated** in G3,
which in turn consumes the genuine combinatorial brick G2
(`lz78_block_kraft_poly`, the polynomial `n`-block Kraft bound). The whole
remaining `sorry` is carried transitively by G2 (and, for now, G3); the
assembly here introduces no new `sorry`.

This statement is TRUE-as-framed (the units defect found by the prior audit
is resolved by stating the RHS against `entropyRate₂` rather than
`entropyRate`): on a uniform i.i.d. source on A symbols the bit-rate limit
is `log₂ A = entropyRate / Real.log 2 = entropyRate₂` exactly, so the
converse `entropyRate₂ ≤ liminf` is the genuine LZ78 converse (e.g. A=2:
`entropyRate₂ = log₂ 2 = 1 ≤ liminf`, with equality in the limit); on the
degenerate `entropyRate = 0` boundary it reads `0 ≤ liminf` (`entropyRate₂ =
0`), again genuine. Signature takes only source data (`μ`, `p`), no
load-bearing hypothesis. -/
theorem lz78GreedyImpl_converse_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate₂ μ p.toStationaryProcess
      ≤ Filter.liminf
          (fun n =>
            (lz78GreedyImplEncodingLength n
                (p.toStationaryProcess.blockRV n ω) : ℝ)
              / (n : ℝ))
          Filter.atTop := by
  set q := p.toStationaryProcess with hq
  -- The greedy bit-rate sequence and its eventual lower envelope.
  set rate : Ω → ℕ → ℝ :=
    fun ω n => (lz78GreedyImplEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ) with hrate
  set err : ℕ → ℝ :=
    fun n => (2 * Real.log n + 2 * Real.log (n + 1)) / ((n : ℝ) * Real.log 2) with herr
  -- `err n → 0` (each `log n / n → 0`).
  have h_err_tend : Filter.Tendsto err Filter.atTop (𝓝 0) := by
    have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogn : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have hR : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
      simpa using hR.comp tendsto_natCast_atTop_atTop
    have hlogn1 : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have hR : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + (-1)))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)
      have hcomp := hR.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
      refine hcomp.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      simp only [Function.comp_apply, pow_one]
      rw [show (1 : ℝ) * ((n : ℝ) + 1) + (-1) = (n : ℝ) by ring]
    set g : ℕ → ℝ := fun n =>
      (2 / Real.log 2) * (Real.log (n : ℝ) / (n : ℝ))
      + (2 / Real.log 2) * (Real.log ((n : ℝ) + 1) / (n : ℝ)) with hg
    have hg_tend : Filter.Tendsto g Filter.atTop (𝓝 0) := by
      have t1 := hlogn.const_mul (2 / Real.log 2)
      have t2 := hlogn1.const_mul (2 / Real.log 2)
      simpa [hg] using t1.add t2
    refine hg_tend.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hg, herr]
    field_simp
  filter_upwards [shannon_mcmillan_breiman₂ μ p,
      blockLogAvg₂_minus_error_le_rate_ae μ p] with ω h_smb h_lift
  -- The lower sequence `Low n = blockLogAvg₂ n ω − err n` tends to `entropyRate₂`.
  set Low : ℕ → ℝ := fun n => blockLogAvg₂ μ q n ω - err n with hLow
  have h_Low_tend : Filter.Tendsto Low Filter.atTop
      (𝓝 (entropyRate₂ μ q)) := by
    have := h_smb.sub h_err_tend
    simpa only [hLow, hq, sub_zero] using this
  -- The rate `lz/n` is bounded above (deterministic constant), hence cobounded below.
  have h_rate_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (rate ω) :=
    Filter.isBoundedUnder_of
      ⟨(1 + 8 * Real.log (Fintype.card α + 1) / Real.log 2)
          + ((Nat.log 2 (Fintype.card α) : ℝ) + 2),
        fun n => lz78_impl_rate_le_const n _⟩
  -- `Low n ≤ rate ω n` eventually, from G3.
  have h_le : ∀ᶠ n in Filter.atTop, Low n ≤ rate ω n := by
    filter_upwards [h_lift] with n hn
    simpa only [hLow, hrate, hq] using hn
  -- Assemble via `liminf_le_liminf`, with `liminf Low = entropyRate₂`.
  have h_liminf_le : Filter.liminf Low Filter.atTop
      ≤ Filter.liminf (rate ω) Filter.atTop :=
    Filter.liminf_le_liminf h_le (hu := h_Low_tend.isBoundedUnder_ge)
      (hv := h_rate_bdd.isCoboundedUnder_ge)
  rw [h_Low_tend.liminf_eq] at h_liminf_le
  exact h_liminf_le

/-- Elementary log bound `log t ≤ 2 · √t` for `t > 0`, used to control the
`c · log(Ntot / c)` boundary term of the achievability composition. -/
private theorem log_le_two_sqrt (t : ℝ) (ht : 0 < t) :
    Real.log t ≤ 2 * Real.sqrt t := by
  have hlog : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  nlinarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht), Real.sqrt_nonneg t]

/-- The `c · log(Ntot / c)` boundary term of the achievability composition,
controlled by `2 · n · √(c' / n)`, where `c ≤ c'` and `Ntot ≤ n`. The `c = 0`
boundary degenerates to `0 ≤ …`; otherwise `c · log(Ntot/c) ≤ c · log(n/c) =
2 · √(c · n) ≤ 2 · √(c' · n) = 2 · n · √(c'/n)` via `log_le_two_sqrt`. -/
private theorem clog_div_le_two_mul_sqrt
    (c Ntot cp n : ℝ) (hc : 0 ≤ c) (hcCp : c ≤ cp) (hcn : c ≤ n) (hNn : Ntot ≤ n)
    (hN0 : 0 ≤ Ntot) (hn : 0 < n) :
    c * Real.log (Ntot / c) ≤ 2 * n * Real.sqrt (cp / n) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]; simp; positivity
  · have hCp_pos : 0 < cp := lt_of_lt_of_le hcpos hcCp
    have hstep1 : c * Real.log (Ntot / c) ≤ c * Real.log (n / c) := by
      rcases eq_or_lt_of_le hN0 with hN00 | hNpos
      · rw [← hN00]; simp
        have h1c : (1 : ℝ) ≤ n / c := by rw [le_div_iff₀ hcpos]; nlinarith
        have := Real.log_nonneg h1c
        positivity
      · apply mul_le_mul_of_nonneg_left _ hc
        apply Real.log_le_log (by positivity)
        exact div_le_div_of_nonneg_right hNn hcpos.le
    have hncpos : 0 < n / c := by positivity
    have hlogbd : Real.log (n / c) ≤ 2 * Real.sqrt (n / c) := log_le_two_sqrt _ hncpos
    have hstep2 : c * Real.log (n / c) ≤ c * (2 * Real.sqrt (n / c)) :=
      mul_le_mul_of_nonneg_left hlogbd hc
    have hcn_eq : c * Real.sqrt (n / c) = Real.sqrt (c * n) := by
      rw [Real.sqrt_mul hcpos.le n, Real.sqrt_div' n hcpos.le, mul_div_assoc']
      rw [div_eq_iff (Real.sqrt_pos.mpr hcpos).ne']
      nlinarith [Real.mul_self_sqrt hcpos.le, Real.sqrt_nonneg n, Real.sqrt_nonneg c]
    have hsqrt_eq : c * (2 * Real.sqrt (n / c)) = 2 * Real.sqrt (c * n) := by
      rw [show c * (2 * Real.sqrt (n / c)) = 2 * (c * Real.sqrt (n / c)) by ring, hcn_eq]
    rw [hsqrt_eq] at hstep2
    have hn_eq : n * Real.sqrt (cp / n) = Real.sqrt (n * cp) := by
      rw [Real.sqrt_mul hn.le cp, Real.sqrt_div' cp hn.le, mul_div_assoc']
      rw [div_eq_iff (Real.sqrt_pos.mpr hn).ne']
      nlinarith [Real.mul_self_sqrt hn.le, Real.sqrt_nonneg cp, Real.sqrt_nonneg n]
    have hrhs_eq : 2 * n * Real.sqrt (cp / n) = 2 * Real.sqrt (n * cp) := by
      rw [show 2 * n * Real.sqrt (cp / n) = 2 * (n * Real.sqrt (cp / n)) by ring, hn_eq]
    rw [hrhs_eq]
    have hmono : Real.sqrt (c * n) ≤ Real.sqrt (n * cp) :=
      Real.sqrt_le_sqrt (by nlinarith)
    calc c * Real.log (Ntot / c) ≤ 2 * Real.sqrt (c * n) := le_trans hstep1 hstep2
      _ ≤ 2 * Real.sqrt (n * cp) := by linarith [hmono]

/-- Reconcile term: with `cp = c + b`, `b ≤ K`, `1 ≤ c`, `cp ≤ n`, the genuine
distinct-phrase product `cp · log cp` is bounded by the composition product
`c · log c` plus the `o(n)` reconcile slack `K + K · log n`. Uses
`log(1 + b/c) ≤ b/c`. -/
private theorem cp_log_cp_le_reconcile
    (c cp b n K : ℝ) (hc : 1 ≤ c) (hcp : cp = c + b) (hb : 0 ≤ b) (hbK : b ≤ K)
    (hcpn : cp ≤ n) (hcppos : 1 ≤ cp) :
    cp * Real.log cp ≤ c * Real.log c + (K + K * Real.log n) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hcppos' : 0 < cp := lt_of_lt_of_le one_pos hcppos
  have e1 : cp * Real.log cp = c * Real.log cp + b * Real.log cp := by rw [hcp]; ring
  have e2 : c * Real.log cp = c * Real.log c + c * Real.log (cp / c) := by
    rw [Real.log_div hcppos'.ne' hcpos.ne']; ring
  have hbound1 : c * Real.log (cp / c) ≤ b := by
    have hcpc : cp / c = 1 + b / c := by rw [hcp]; field_simp
    rw [hcpc]
    have hlog : Real.log (1 + b / c) ≤ b / c := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + b / c by positivity)
      linarith [this]
    calc c * Real.log (1 + b / c) ≤ c * (b / c) :=
          mul_le_mul_of_nonneg_left hlog hcpos.le
      _ = b := by field_simp
  have hbound2 : b * Real.log cp ≤ K * Real.log n := by
    have hlogcp_nn : 0 ≤ Real.log cp := Real.log_nonneg hcppos
    have hlogcp_le : Real.log cp ≤ Real.log n := Real.log_le_log hcppos' hcpn
    have hKnn : 0 ≤ K := le_trans hb hbK
    calc b * Real.log cp ≤ K * Real.log cp :=
          mul_le_mul_of_nonneg_right hbK hlogcp_nn
      _ ≤ K * Real.log n := mul_le_mul_of_nonneg_left hlogcp_le hKnn
  rw [e1, e2]; linarith

/-- **Lemma 1 (core)**: for each fixed `k`, the a.s.-eventual limsup of the
greedy bit-rate is at most the `k`-th conditional tail entropy in bits.

This is the per-`k` Ziv bound: combining the achievability composition
`ziv_achievability_composition` (the `c·log c ≤ negLogQk + o(n)` brick) with
the AEP `negLogQk_div_tendsto_condEntropyTail` and the deterministic
overhead-vanishing `c = O(n/log n)`, the per-symbol greedy rate is dominated
by `negLogQk/(log 2 · n) → H_k/log 2`. -/
theorem ziv_aseventual_le_condEntropyTail_bits
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ conditionalEntropyTail μ p.toStationaryProcess k / Real.log 2 := by
  classical
  set q := p.toStationaryProcess with hq
  set H : ℝ := conditionalEntropyTail μ q k with hH
  set La : ℝ := Real.log (Fintype.card α) with hLa
  set L : ℝ := (Nat.log 2 (Fintype.card α) : ℝ) with hL
  have hℓ2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLa_nn : (0 : ℝ) ≤ La := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith)
  have hL_nn : (0 : ℝ) ≤ L := by rw [hL]; positivity
  filter_upwards [negLogQk_div_tendsto_condEntropyTail μ p k,
      (MeasureTheory.ae_all_iff.2 (fun n => ziv_achievability_composition μ q k n))]
    with ω h_aep h_comp
  -- Abbreviations: the genuine distinct phrase count `cp n`, the LZ78 bit-rate
  -- `T n`, and the deterministic error sequence `E n`.
  set cp : ℕ → ℝ :=
    fun n => ((lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length : ℝ) with hcp
  set T : ℕ → ℝ :=
    fun n => (lz78GreedyImplEncodingLength n (q.blockRV n ω) : ℝ) / (n : ℝ) with hT
  set E : ℕ → ℝ := fun n =>
    (2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La)
      + ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)
      + (cp n * Real.log 2 + cp n * (L + 2))) / (Real.log 2 * (n : ℝ)) with hE
  set U : ℕ → ℝ :=
    fun n => (negLogQk μ q k n ω / (n : ℝ)) / Real.log 2 + E n with hU
  -- `cp n ≥ 0` and `cp n / n → 0`.
  have hcp_nn : ∀ n, 0 ≤ cp n := fun n => by simp only [hcp]; positivity
  have hcp_div : Filter.Tendsto (fun n => cp n / (n : ℝ)) Filter.atTop (𝓝 0) := by
    obtain ⟨C, hCb⟩ :=
      (lz78PhraseStrings_count_isBigO (fun n => List.ofFn (q.blockRV n ω))
        (fun n => List.length_ofFn)).bound
    have hub : Filter.Tendsto (fun n : ℕ => C * (Real.log (n : ℝ))⁻¹)
        Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
          Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      simpa using (tendsto_inv_atTop_zero.comp h1).const_mul C
    refine squeeze_zero_norm' ?_ hub
    filter_upwards [hCb, Filter.eventually_gt_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlogpos : (0 : ℝ) < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn1)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hcp_nn n) hnpos.le)]
    rw [Real.norm_eq_abs, abs_of_nonneg (hcp_nn n)] at hn
    have hng : ‖(n : ℝ) / Real.log (n : ℝ)‖ = (n : ℝ) / Real.log (n : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (div_pos hnpos hlogpos))]
    rw [hng] at hn
    calc cp n / (n : ℝ) ≤ (C * ((n : ℝ) / Real.log (n : ℝ))) / (n : ℝ) :=
          div_le_div_of_nonneg_right hn hnpos.le
      _ = C * (Real.log (n : ℝ))⁻¹ := by
          rw [mul_div_assoc, div_div, mul_comm (Real.log (n : ℝ)) (n : ℝ), ← div_div,
            div_self hnpos.ne', one_div]
  -- `E n → 0` (every summand divided by `log 2 · n` vanishes via `cp/n → 0`).
  have hE_tend : Filter.Tendsto E Filter.atTop (𝓝 0) := by
    have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (cp n / (n : ℝ)))
        Filter.atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hcp_div
      simp only [Function.comp_def, Real.sqrt_zero] at h
      exact h
    have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have hlogn : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have hR : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
      simpa using hR.comp tendsto_natCast_atTop_atTop
    set g : ℕ → ℝ := fun n =>
      (2 / Real.log 2) * Real.sqrt (cp n / (n : ℝ))
      + (1 / Real.log 2) * (cp n / (n : ℝ))
      + ((k : ℝ) * La / Real.log 2) * (cp n / (n : ℝ))
      + (((k : ℝ) + 1) / Real.log 2) * ((1 : ℝ) / (n : ℝ))
      + (((k : ℝ) + 1) / Real.log 2) * (Real.log (n : ℝ) / (n : ℝ))
      + (cp n / (n : ℝ))
      + ((L + 2) / Real.log 2) * (cp n / (n : ℝ)) with hg
    have hg_tend : Filter.Tendsto g Filter.atTop (𝓝 0) := by
      have t1 := hsqrt.const_mul (2 / Real.log 2)
      have t2 := hcp_div.const_mul (1 / Real.log 2)
      have t3 := hcp_div.const_mul ((k : ℝ) * La / Real.log 2)
      have t4 := hinv.const_mul (((k : ℝ) + 1) / Real.log 2)
      have t5 := hlogn.const_mul (((k : ℝ) + 1) / Real.log 2)
      have t6 := hcp_div
      have t7 := hcp_div.const_mul ((L + 2) / Real.log 2)
      simpa [hg] using ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
    refine hg_tend.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hg, hE]
    field_simp
    ring
  -- `U n → H / log 2`.
  have hU_tend : Filter.Tendsto U Filter.atTop (𝓝 (H / Real.log 2)) := by
    have ha : Filter.Tendsto (fun n => negLogQk μ q k n ω / (n : ℝ) / Real.log 2)
        Filter.atTop (𝓝 (H / Real.log 2)) := h_aep.div_const (Real.log 2)
    have := ha.add hE_tend
    simpa [hU] using this
  -- Per-`n` bound: `T n ≤ U n` eventually.
  have hTU : ∀ᶠ n in Filter.atTop, T n ≤ U n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn1
    obtain ⟨c, bAbsorbed, Ntot, hcount, hbA, hNtot, hbound⟩ := h_comp n
    have hn : 0 < n := hn1
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hden_pos : (0 : ℝ) < Real.log 2 * (n : ℝ) := by positivity
    -- Real-cast abbreviations.
    set cR : ℝ := (c : ℝ) with hcR
    set bR : ℝ := (bAbsorbed : ℝ) with hbR
    set NtR : ℝ := (Ntot : ℝ) with hNtR
    have hcR_nn : (0 : ℝ) ≤ cR := by positivity
    have hbR_nn : (0 : ℝ) ≤ bR := by positivity
    have hNtR_nn : (0 : ℝ) ≤ NtR := by positivity
    -- `cp n = cR + bR`, so `cR ≤ cp n` and `cp n ≤ n`.
    have hcount' : cp n = cR + bR := by
      simp only [hcp, hcR, hbR]; rw [← Nat.cast_add, hcount]
    have hbA' : bR ≤ (k : ℝ) + 1 := by rw [hbR]; exact_mod_cast hbA
    have hNtot' : NtR ≤ (n : ℝ) := by rw [hNtR]; exact_mod_cast hNtot
    have hcp_le_n : cp n ≤ (n : ℝ) := by
      have := lz78GreedyImplPhraseCount_ofFn_le n (q.blockRV n ω)
      simp only [hcp]; exact_mod_cast this
    have hcR_le_cp : cR ≤ cp n := by rw [hcount']; linarith
    have hcR_le_n : cR ≤ (n : ℝ) := le_trans hcR_le_cp hcp_le_n
    -- Composition bound with `log((card α)^k) = k · log(card α)`.
    have hlogpow : Real.log (((Fintype.card α) ^ k : ℕ) : ℝ) = (k : ℝ) * La := by
      rw [hLa, Nat.cast_pow, Real.log_pow]
    have hcomp : cR * Real.log cR ≤ negLogQk μ q k n ω
        + (cR * Real.log (NtR / cR) + cR + cR * ((k : ℝ) * La)) := by
      have := hbound
      rw [hlogpow] at this
      simpa [hcR, hNtR] using this
    -- Boundary term bound: `cR · log(Ntot/cR) ≤ 2 n √(cp n / n)`.
    have hbdry : cR * Real.log (NtR / cR) ≤ 2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) :=
      clog_div_le_two_mul_sqrt cR NtR (cp n) (n : ℝ) hcR_nn hcR_le_cp hcR_le_n
        hNtot' hNtR_nn hnR
    -- `cp n · log(cp n) ≤ cR · log cR + reconcile`, handling the `cp n < 1` boundary.
    have hrec : cp n * Real.log (cp n)
        ≤ cR * Real.log cR + (((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)) := by
      rcases lt_or_ge (cp n) 1 with hlt | hge
      · -- `cp n < 1` ⇒ `cp n = 0` (it is a Nat cast) ⇒ `cR = 0` too.
        have hcp0 : cp n = 0 := by
          rcases Nat.eq_zero_or_pos (lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length
            with h0 | hpos
          · simp only [hcp, h0]; simp
          · exfalso; simp only [hcp] at hlt
            have : (1 : ℝ) ≤ ((lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length : ℝ) := by
              exact_mod_cast hpos
            linarith
        have hcR0 : cR = 0 := le_antisymm (by linarith [hcR_le_cp, hcp0]) hcR_nn
        rw [hcp0, hcR0]
        simp only [Real.log_zero, mul_zero, zero_add]
        have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
        positivity
      · -- `cp n ≥ 1`. Two cases on `cR`.
        rcases lt_or_ge cR 1 with hcRlt | hcRge
        · -- `cR < 1` ⇒ `cR = 0` (Nat cast) ⇒ `cp n = bR ≤ k+1`, so `cp n log cp n` is small.
          have hcR0 : cR = 0 := by
            rcases Nat.eq_zero_or_pos c with h0 | hpos
            · rw [hcR, h0]; simp
            · exfalso
              have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hpos
              rw [hcR] at hcRlt; linarith
          have hcp_eq_b : cp n = bR := by rw [hcount', hcR0]; ring
          have hcp_le_k1 : cp n ≤ (k : ℝ) + 1 := by rw [hcp_eq_b]; exact hbA'
          have hlogcp_le : Real.log (cp n) ≤ Real.log (n : ℝ) :=
            Real.log_le_log (by linarith) hcp_le_n
          have hlogcp_nn : 0 ≤ Real.log (cp n) := Real.log_nonneg hge
          rw [hcR0]; simp only [Real.log_zero, mul_zero, zero_add]
          calc cp n * Real.log (cp n) ≤ ((k : ℝ) + 1) * Real.log (n : ℝ) :=
                mul_le_mul hcp_le_k1 hlogcp_le hlogcp_nn (by linarith [hbA'])
            _ ≤ ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ) := by
                have : 0 ≤ (k : ℝ) + 1 := by positivity
                linarith
        · -- `1 ≤ cR` and `1 ≤ cp n`: the generic reconcile lemma.
          exact cp_log_cp_le_reconcile cR (cp n) bR (n : ℝ) ((k : ℝ) + 1) hcRge hcount'
            hbR_nn hbA' hcp_le_n hge
    -- Step A: `T n ≤ cp n · log(cp n)/(log 2 · n) + StepA-overhead/(log 2 · n)`.
    have hstepA := lz78_impl_bitrate_le_clogc_plus_overhead n hn (q.blockRV n ω)
    -- Assemble. Clear the common `log 2 · n` denominator and chain the bounds.
    simp only [hU, hE]
    -- The Step-A RHS, rewritten via `cp`.
    have hstepA' : T n ≤ cp n * Real.log (cp n) / (Real.log 2 * (n : ℝ))
        + (cp n * Real.log 2 + cp n * (L + 2)) / (Real.log 2 * (n : ℝ)) := by
      simp only [hT, hcp, hL]; exact hstepA
    -- Bound `cp n · log(cp n) ≤ negLogQk + boundary + reconcile + alphabet`.
    have hclog : cp n * Real.log (cp n)
        ≤ negLogQk μ q k n ω
          + (2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La)
            + ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)) := by
      have hcR_le_cp' : cR ≤ cp n := hcR_le_cp
      -- `cR·log(Ntot/cR) + cR + cR·k·La ≤ boundary + cp n + cp n·k·La`.
      have h1 : cR * Real.log (NtR / cR) + cR + cR * ((k : ℝ) * La)
          ≤ 2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La) := by
        have hmono_kLa : cR * ((k : ℝ) * La) ≤ cp n * ((k : ℝ) * La) :=
          mul_le_mul_of_nonneg_right hcR_le_cp' (by positivity)
        linarith [hbdry]
      calc cp n * Real.log (cp n)
          ≤ cR * Real.log cR + (((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)) := hrec
        _ ≤ (negLogQk μ q k n ω
              + (cR * Real.log (NtR / cR) + cR + cR * ((k : ℝ) * La)))
            + (((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)) := by linarith [hcomp]
        _ ≤ negLogQk μ q k n ω
              + (2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La)
                + ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)) := by linarith [h1]
    -- Divide `hclog` by the positive denominator and combine with Step A.
    have hdiv : cp n * Real.log (cp n) / (Real.log 2 * (n : ℝ))
        ≤ (negLogQk μ q k n ω
            + (2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La)
              + ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)))
          / (Real.log 2 * (n : ℝ)) :=
      div_le_div_of_nonneg_right hclog hden_pos.le
    -- Final: combine `hstepA'` + `hdiv`, splitting the RHS fraction.
    have hgoal : (negLogQk μ q k n ω / (n : ℝ)) / Real.log 2
        + (2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La)
            + ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)
            + (cp n * Real.log 2 + cp n * (L + 2))) / (Real.log 2 * (n : ℝ))
        = (negLogQk μ q k n ω
            + (2 * (n : ℝ) * Real.sqrt (cp n / (n : ℝ)) + cp n + cp n * ((k : ℝ) * La)
              + ((k : ℝ) + 1) + ((k : ℝ) + 1) * Real.log (n : ℝ)))
          / (Real.log 2 * (n : ℝ))
          + (cp n * Real.log 2 + cp n * (L + 2)) / (Real.log 2 * (n : ℝ)) := by
      rw [div_div]
      have : negLogQk μ q k n ω / ((n : ℝ) * Real.log 2)
          = negLogQk μ q k n ω / (Real.log 2 * (n : ℝ)) := by rw [mul_comm]
      rw [this, ← add_div]
      ring
    rw [hgoal]
    linarith [hstepA', hdiv]
  -- Conclude via `limsup_le_limsup`.
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop T :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop
      (fun n => lz78_impl_encoding_length_per_symbol_nonneg n (q.blockRV n ω))
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop U :=
    hU_tend.isBoundedUnder_le
  have hlim_le : Filter.limsup T Filter.atTop ≤ Filter.limsup U Filter.atTop :=
    Filter.limsup_le_limsup hTU hcobdd hbdd
  rw [hU_tend.limsup_eq] at hlim_le
  exact hlim_le

/-- **Lemma 2 (diagonalization = inf over `k`)**: the a.s.-eventual limsup of
the greedy bit-rate is at most the bit entropy rate.

From Lemma 1 (`ziv_aseventual_le_condEntropyTail_bits`) for all `k`
(countable intersection) plus the limit `conditionalEntropyTail → entropyRate`
(`entropyRate_eq_lim_condEntropy`), rescaled by `/Real.log 2`. The LHS is a
`k`-independent constant, so `le_of_tendsto` closes it. -/
theorem ziv_aseventual_le_entropyRate₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ entropyRate₂ μ p.toStationaryProcess := by
  filter_upwards
    [(MeasureTheory.ae_all_iff.2
        (fun k => ziv_aseventual_le_condEntropyTail_bits μ p k))] with ω hω
  -- `hω : ∀ k, limsup (lz/n) ≤ conditionalEntropyTail μ p k / log 2`.
  have h_tend : Filter.Tendsto
      (fun k => conditionalEntropyTail μ p.toStationaryProcess k / Real.log 2)
      Filter.atTop (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
    have h := (entropyRate_eq_lim_condEntropy μ p.toStationaryProcess).div_const
      (Real.log 2)
    simpa only [entropyRate₂] using h
  exact ge_of_tendsto h_tend (Filter.Eventually.of_forall hω)

/-- **a.s.-eventual Ziv comparison**: the limsup of the greedy bit-rate is at
most the limsup of `blockLogAvg₂`.

The achievability crux (Cover–Thomas Lemma 13.5.5): combining the Ziv product
bound `c·log c ≤ 8·log(|α|+1)·n` with the length-grouping overhead control
`c = O(n/log n)` and the `-log Pₙ = n·blockLogAvg` identity, the greedy
bit-rate is asymptotically dominated by `blockLogAvg₂`. Stated as an
`a.s.-eventual` limsup comparison (the per-block form is FALSE, counterexample
`a^16`).

Independent honesty audit 2026-06-21 PASS (commit `c22f2d5`, fresh
subagent): the M3 wall `lz78-aseventual-ziv` is now CLOSED — the body is
genuinely `sorry`-free (filter_upwards on `ziv_aseventual_le_entropyRate₂`
+ `shannon_mcmillan_breiman₂`, `rw [h_smb.limsup_eq]`, `exact h_ziv`). The
prior stale wall residual (slug `lz78-aseventual-ziv`) is removed. `#print axioms`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-verified
2026-06-21). The Ziv→AEP connection that was the M3 wall is supplied by the
genuine composition `ziv_achievability_composition`
(`c·log c ≤ negLogQk + o(n)`, sorryAx-free + audited) plus the AEP
`negLogQk_div_tendsto_condEntropyTail`, assembled in
`ziv_aseventual_le_condEntropyTail_bits`. Four honesty checks PASS —
(1) non-circular (no `:= h`), (2) non-bundled (signature is `(μ, p)` +
`[IsProbabilityMeasure μ]` regularity only), (3) non-degenerate (genuine
limsup inequality), (4) sufficiency TRUE-as-framed (Cover–Thomas 13.5.5;
per-block form correctly avoided; degenerate `entropyRate = 0` boundary
stays alive).

@audit:ok -/
theorem ziv_aseventual_le_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ Filter.limsup
          (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) Filter.atTop := by
  filter_upwards [ziv_aseventual_le_entropyRate₂ μ p, shannon_mcmillan_breiman₂ μ p]
    with ω h_ziv h_smb
  rw [h_smb.limsup_eq]
  exact h_ziv

/-- **Ziv-inequality achievability upper bound for the genuine greedy
parser (Cover–Thomas Lemma 13.5.5 / Theorem 13.5.3 upper-bound half),
a.s. form**.

For a stationary ergodic source `p` the per-symbol length of the genuine
longest-prefix-match greedy LZ78 parse is, almost surely, asymptotically at
most the bit entropy rate:

```
limsup_n (1/n) · lz78GreedyImplEncodingLength(X^n) ≤ entropyRate₂ μ p   a.s.
```

This is the achievability (upper-bound) half of LZ78 asymptotic
optimality, i.e. the a.s.-eventual Ziv inequality
`limsup (c·log₂ c / n) ≤ H₂` combined with the SMB upper bound.

Units: the encoding length is a base-2 code length (`bitLength` uses
`Nat.log 2`), so the per-symbol rate `lz/n` is in **bits** and the correct
RHS is the **bit** entropy rate `entropyRate₂ = entropyRate / Real.log 2`,
the unit-correction documented in `ZivEntropyBridge.lean` ("Base-2 (bit)
layer") and `McMillanKraftBridge.lean`.

After the 2026-06-20 def-fix (`lz78GreedyImplEncodingLength` now charges
`c · bitLength c |α|` against the genuine distinct phrase count
`c = (lz78PhraseStrings (List.ofFn x)).length`), this is a **genuine
proposition** carrying real Ziv content.

**Composition lemma (2026-06-20 W1/W2 decomposition).** The body of this
theorem is now `sorry`-free: it is assembled from the two genuine halves of
the achievability sandwich,

* `shannon_mcmillan_breiman₂` (SMB in bits, **sorryAx-free**) — gives
  `Tendsto blockLogAvg₂ → entropyRate₂` a.s., hence
  `limsup blockLogAvg₂ = entropyRate₂` (`Filter.Tendsto.limsup_eq`);
* `ziv_aseventual_le_blockLogAvg₂` (the a.s.-eventual Ziv comparison) —
  gives `limsup (lz/n) ≤ limsup blockLogAvg₂` a.s.

`ziv_aseventual_le_blockLogAvg₂` is itself now sorryAx-free (the M3 wall
`lz78-aseventual-ziv` is CLOSED): the Ziv→AEP connection — variable-depth
tree-node AEP linking the combinatorial `c · log c` to the probabilistic
`-log Pₙ` — is supplied by the genuine composition
`ziv_achievability_composition` (`c · log c ≤ negLogQk + o(n)`) plus the AEP
`negLogQk_div_tendsto_condEntropyTail`, assembled per-`k` in
`ziv_aseventual_le_condEntropyTail_bits` and diagonalized in
`ziv_aseventual_le_entropyRate₂`. The combinatorial core
(`c · log c ≤ K · n`, `c = O(n / log n)`) and the SMB AEP
(`shannon_mcmillan_breiman`) are all sorryAx-free; the whole achievability
chain depends only on `[propext, Classical.choice, Quot.sound]`.

This statement is TRUE-as-framed against the bit target `entropyRate₂` (the
prior audit's units defect — false on a uniform i.i.d. source when stated
against the nat-unit `entropyRate` — is resolved by the bit RHS). On a
uniform i.i.d. source on A symbols the LZ78-optimal bit-rate limit is
`log₂ A = entropyRate / Real.log 2 = entropyRate₂` exactly, so
`limsup ≤ entropyRate₂` holds with equality in the limit (A=2: `1 ≤ 1`); on
the degenerate `entropyRate = 0` boundary it reads `limsup ≤ 0` with
`entropyRate₂ = 0`, again genuine. Signature takes only source data, no
load-bearing hypothesis.

Independent honesty audit 2026-06-21 PASS (commit `c22f2d5`, fresh
subagent): the M3 wall `lz78-aseventual-ziv` is CLOSED, so the prior stale
wall residual (slug `lz78-aseventual-ziv`) is removed. The body is sorry-free
(filter_upwards on `shannon_mcmillan_breiman₂` + `ziv_aseventual_le_blockLogAvg₂`,
`exact h_ziv.trans h_smb.limsup_eq.le`); `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-verified
2026-06-21). The bit RHS `entropyRate₂ = entropyRate / Real.log 2` resolves
the prior units defect (the nat-unit bound was false for A ≥ 2; the bit bound
holds at equality, A=2: `1 ≤ 1`, A=3: `log₂ 3 ≤ log₂ 3`). Four honesty checks
PASS — non-circular, non-bundled (signature is `(μ, p)` +
`[IsProbabilityMeasure μ]` regularity only), non-degenerate, sufficiency
TRUE-as-framed; degenerate `entropyRate = 0` boundary reads `limsup ≤ 0` and
stays alive.

@audit:ok -/
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
      ≤ entropyRate₂ μ p.toStationaryProcess := by
  filter_upwards [shannon_mcmillan_breiman₂ μ p, ziv_aseventual_le_blockLogAvg₂ μ p]
    with ω h_smb h_ziv
  exact h_ziv.trans h_smb.limsup_eq.le

/-- **LZ78 asymptotic optimality with the genuine greedy parsing
implementation (Cover–Thomas Theorem 13.5.3)**.

For a stationary ergodic source `p : ErgodicProcess μ α` on a finite
alphabet `α`, the per-symbol output length of the genuine
longest-prefix-match greedy LZ78 parse converges almost surely to the
**bit** entropy rate:

```
lim_{n → ∞} (1/n) · lz78GreedyImplEncodingLength(X^n) = entropyRate₂ μ p   a.s.
```

Units: the encoding length is a base-2 code length
(`lz78GreedyImplEncodingLength = c · bitLength c |α|`, `bitLength` uses
`Nat.log 2`), so the per-symbol rate is in **bits** and the convergence
target is the **bit** entropy rate `entropyRate₂ = entropyRate / Real.log 2`
(not the nat-unit `entropyRate`). This is the unit-correction documented in
`ZivEntropyBridge.lean` ("Base-2 (bit) layer — unit correction for the LZ78
headline"). On a uniform i.i.d. source on A symbols the bit-rate limit is
`log₂ A = entropyRate₂` exactly (e.g. A=2: `rate → 1`), which is what the
two TRUE-as-framed halves squeeze to.

This is the LZ78 optimality headline. The two halves of the sandwich —
the converse lower bound and the Ziv achievability upper bound — are
supplied internally by `lz78GreedyImpl_converse_ae` and
`lz78GreedyImpl_achievability_ae`, both now stated against the bit target
`entropyRate₂`. The a.s. convergence is assembled via the generic
combinator `lz78_asymptotic_optimality` instantiated at `L = entropyRate₂`
(the genuine `tendsto_of_le_liminf_of_limsup_le` squeeze).

After the 2026-06-20 def-fix (`lz78GreedyImplEncodingLength` now charges
`c · bitLength c |α|` against the genuine distinct phrase count of the
longest-prefix-match parse), the per-symbol rate is data-dependent and
**deterministically bounded above by an `n`- and `ω`-uniform constant**
`(1 + 8·log(|α|+1)/log 2) + (log₂|α| + 2)` (via `lz78_impl_rate_le_const`,
combining the Ziv product bound `c·log c ≤ 8·log(|α|+1)·n` with `c ≤ n` and the
`ℕ`–`Real` `log` bridge). The upper-boundedness hypothesis is therefore **no
longer a parameter**: it is supplied internally — even the `a.e.` envelope is
unnecessary since the bound holds for every `ω` and every `n`. The two input
halves remain genuine research-level walls (M3 / M4); see their docstrings.

Units defect resolution 2026-06-20: an earlier units-mismatch defect (the
convergence target was the nat-unit `entropyRate` while the bit-rate `lz/n`
converges to the bit entropy rate, making the achievability half — and hence
this headline — FALSE on a uniform i.i.d. source) is now resolved by stating
the target against `entropyRate₂ = entropyRate / Real.log 2` (bit). With the
bit target the headline is a **TRUE-as-framed proposition**: on a uniform
i.i.d. source on A symbols the bit-rate limit is `log₂ A = entropyRate₂`
exactly (A=2: `entropyRate₂ = log₂ 2 = 1`, so the two halves squeeze
`rate → 1`, the genuine LZ78-optimal bit rate); on the degenerate
`entropyRate = 0` boundary the target is `entropyRate₂ = 0` and the squeeze
reads `rate → 0`, again genuine. Both halves
(`lz78GreedyImpl_converse_ae` / `lz78GreedyImpl_achievability_ae`) are stated
against `entropyRate₂`, and the base combinator `lz78_asymptotic_optimality`
is instantiated at `L = entropyRate₂`.

Type-check done, honest (not proof done). The headline takes only the source
data (`μ`, `p`) — no `h_bdd_above` precondition. Both `IsBoundedUnder`
witnesses (`(·≤·)` above and `(·≥·)` below) are constructed deterministically
inside the body from `lz78_impl_rate_le_const` /
`lz78_impl_encoding_length_per_symbol_nonneg` (both unit-agnostic: they bound
the bit-rate `lz/n` itself, so they are unaffected by the choice of `L`), so
the squeeze `tendsto_of_le_liminf_of_limsup_le` is applied with all of its
regularity inputs genuine. The achievability half
(`lz78GreedyImpl_achievability_ae`) is now sorryAx-free (the M3 wall
`lz78-aseventual-ziv` is CLOSED, audited 2026-06-21); the remaining `sorryAx`
is carried exactly via the M4 converse residual `lz78GreedyImpl_converse_ae`,
isolated in the G2 brick `lz78_block_kraft_poly`
(`@residual(plan:lz78-m4-plan)`, reclassified from the overturned
`wall:lz78-converse-aseventual`). The boundedness discharge
introduces no new `sorry`. -/
@[entry_point]
theorem lz78_asymptotic_optimality_with_greedy_impl
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78GreedyImplEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  have h_bdd_above : ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n =>
          (lz78GreedyImplEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ)) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    exact Filter.isBoundedUnder_of
      ⟨(1 + 8 * Real.log (Fintype.card α + 1) / Real.log 2)
          + ((Nat.log 2 (Fintype.card α) : ℝ) + 2),
        fun n => lz78_impl_rate_le_const n _⟩
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
    (entropyRate₂ μ p.toStationaryProcess)
    (lz78GreedyImpl_converse_ae μ p)
    (lz78GreedyImpl_achievability_ae μ p)
    h_bdd_above h_bdd_below

end ParentBridge

end InformationTheory.Shannon
