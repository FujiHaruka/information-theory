import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.Basic
import InformationTheory.Shannon.LZ78.GreedyParsing
import InformationTheory.Shannon.LZ78.GreedyLongestPrefix
import InformationTheory.Shannon.LZ78.PhraseCounting
import InformationTheory.Shannon.LZ78.ZivAchievabilityComposition
import InformationTheory.Shannon.SMB.AlgoetCover.Liminf
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.GroupWithZero

/-! # LZ78 greedy encoding length + Cover-Thomas bit-length bounds (part 1/3) -/

namespace InformationTheory.Shannon

open scoped Topology

set_option linter.unusedSectionVars false

/-! ## §1. Encoding length + parent-theorem bridge -/

section EncodingLength

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The greedy encoding length of a finite tuple: parse `List.ofFn x` with
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
def lz78GreedyEncodingLength (n : ℕ) (x : Fin n → α) : ℕ :=
  let c := (lz78PhraseStrings (List.ofFn x)).length
  c * LZ78Phrase.bitLength c (Fintype.card α)

@[simp] lemma lz78GreedyEncodingLength_zero (x : Fin 0 → α) :
    lz78GreedyEncodingLength 0 x = 0 := by
  unfold lz78GreedyEncodingLength
  rw [show (List.ofFn x : List α) = [] from by simp]
  have hc : (lz78PhraseStrings ([] : List α)).length = 0 := by
    have := lz78PhraseStrings_count_le ([] : List α)
    simpa using this
  simp [hc]

/-- **Distinct phrase count of the genuine greedy parse on an `n`-tuple is
`≤ n`**: the genuine longest-prefix parse of `List.ofFn x` emits at most `n`
distinct phrases (`lz78PhraseStrings_count_le` plus `List.length_ofFn`). -/
theorem lz78GreedyPhraseCount_ofFn_le (n : ℕ) (x : Fin n → α) :
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
theorem lz78_encoding_length_le_n_log_n_plus_const (n : ℕ) (x : Fin n → α) :
    lz78GreedyEncodingLength n x ≤
      n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
  unfold lz78GreedyEncodingLength
  set c := (lz78PhraseStrings (List.ofFn x)).length with hc
  have hcn : c ≤ n := lz78GreedyPhraseCount_ofFn_le n x
  have hbit : LZ78Phrase.bitLength c (Fintype.card α)
      ≤ LZ78Phrase.bitLength n (Fintype.card α) :=
    LZ78Phrase.bitLength_mono_left hcn
  calc c * LZ78Phrase.bitLength c (Fintype.card α)
      ≤ n * LZ78Phrase.bitLength n (Fintype.card α) :=
        Nat.mul_le_mul hcn hbit
    _ = n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) := by
        rw [LZ78Phrase.bitLength_eq]

/-- The per-symbol asymptotic bit-rate bound on `ℝ` for the genuine
greedy parse: dividing by `n` gives `≤ log(n+1) + log|α| + 2`. -/
@[entry_point]
theorem lz78_encoding_length_per_symbol_le (n : ℕ) (hn : 0 < n)
    (x : Fin n → α) :
    (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
      ≤ (Nat.log 2 (n + 1) : ℝ) + (Nat.log 2 (Fintype.card α) : ℝ) + 2 := by
  have hle := lz78_encoding_length_le_n_log_n_plus_const n x
  have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  have : (lz78GreedyEncodingLength n x : ℝ)
      ≤ (n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2) : ℕ) := by
    exact_mod_cast hle
  refine this.trans (le_of_eq ?_)
  push_cast
  ring

/-- The per-symbol bit-rate is nonnegative: the greedy encoding length
divided by `n` is `≥ 0` for every `n` (including `n = 0`, where the
division is `0/0 = 0`). The numerator is a `ℕ` cast and the denominator a
`ℕ` cast, so the quotient is a nonnegative real. -/
@[entry_point]
theorem lz78_encoding_length_per_symbol_nonneg (n : ℕ) (x : Fin n → α) :
    (0 : ℝ) ≤ (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ) :=
  div_nonneg (by positivity) (by positivity)

/-- `(Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m`: the integer base-`2`
logarithm bounded by `Real.log m / Real.log 2` with the denominator cleared.
A real-valued restatement of `Real.natLog_le_logb`. -/
theorem natLog_mul_log_two_le (m : ℕ) :
    (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
  have hbound : (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
    have := Real.natLog_le_logb m 2
    rwa [Real.logb, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast] at this
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2] at hbound
  exact hbound

/-- `(c : ℝ) * Real.log (c + 1) ≤ (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c`:
the per-phrase `+1`-shift slack, from `Real.log (c + 1) ≤ Real.log 2 + Real.log c`
(via `Real.log (c + 1) ≤ Real.log (2 * c)` for `c ≥ 1`; trivial for `c = 0`). -/
theorem mul_log_succ_le (c : ℕ) :
    (c : ℝ) * Real.log (c + 1) ≤ (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := by
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · simp [hc0]
  · have hcR_nn : (0 : ℝ) ≤ (c : ℝ) := by positivity
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcpos
    have hstep : Real.log ((c : ℝ) + 1) ≤ Real.log 2 + Real.log c := by
      have h1 : Real.log ((c : ℝ) + 1) ≤ Real.log (2 * (c : ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
      rwa [Real.log_mul (by norm_num) (by positivity)] at h1
    calc (c : ℝ) * Real.log (c + 1)
        ≤ (c : ℝ) * (Real.log 2 + Real.log c) := mul_le_mul_of_nonneg_left hstep hcR_nn
      _ = (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := by ring

/-- The per-symbol greedy bit rate `lz78GreedyEncodingLength n x / n` is
bounded by a deterministic constant depending only on `|α|`, for every `n`
(including the degenerate `n = 0`, where the rate is `0`). The constant
`(1 + 8 * Real.log (|α| + 1) / Real.log 2) + (Nat.log 2 |α| + 2)` comes from the
Ziv product bound `c * Real.log c ≤ 8 * Real.log (|α| + 1) * n`
(`lz78PhraseStrings_mul_log_le`), `c ≤ n`, and `natLog_mul_log_two_le`. -/
theorem lz78_rate_le_const [Nonempty α] (n : ℕ) (x : Fin n → α) :
    (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
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
  have hcn : c ≤ n := lz78GreedyPhraseCount_ofFn_le n x
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcR_nn : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hcnR : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcn
  -- The encoding length expanded via `bitLength_eq`.
  have hlen : (lz78GreedyEncodingLength n x : ℝ)
      = (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2) := by
    have hdef : lz78GreedyEncodingLength n x
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
      exact natLog_mul_log_two_le (c + 1) |>.trans_eq (by push_cast; ring_nf)
    have hziv : (c : ℝ) * Real.log c ≤ 8 * b * (n : ℝ) := by
      have := lz78PhraseStrings_mul_log_le (List.ofFn x)
      rw [← hc, List.length_ofFn] at this
      exact this
    have hupper : (c : ℝ) * Real.log (c + 1) ≤ (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ) :=
      calc (c : ℝ) * Real.log (c + 1)
          ≤ (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := mul_log_succ_le c
        _ ≤ (n : ℝ) * Real.log 2 + 8 * b * (n : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_right hcnR hℓ2.le) hziv
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

/-- **Per-symbol bit-rate decomposed into a `c·log c` term and an `o(1)`
overhead** (deterministic, per-`n`).

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
encoding-length expansion inside `lz78_rate_le_const`; the bit-rate is
left exactly as `c·log c/(log 2 · n) + overhead`, so the dominant term is
available for the a.s.-eventual limsup comparison. -/
theorem lz78_bitrate_le_clogc_plus_overhead [Nonempty α]
    (n : ℕ) (hn : 0 < n) (x : Fin n → α) :
    (lz78GreedyEncodingLength n x : ℝ) / (n : ℝ)
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
  have hcn : c ≤ n := lz78GreedyPhraseCount_ofFn_le n x
  have hcR_nn : (0 : ℝ) ≤ (c : ℝ) := by positivity
  -- Encoding length expanded via `bitLength_eq` (same as `lz78_rate_le_const`).
  have hlen : (lz78GreedyEncodingLength n x : ℝ)
      = (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ) + L + 2) := by
    have hdef : lz78GreedyEncodingLength n x
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
    exact natLog_mul_log_two_le (c + 1) |>.trans_eq (by push_cast; ring_nf)
  have hlogc1 : (c : ℝ) * Real.log (c + 1)
      ≤ (c : ℝ) * Real.log 2 + (c : ℝ) * Real.log c := mul_log_succ_le c
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

/-! ## §2. `IsLZ78EncodingLengthBoundPassthrough` -/

section EncodingLengthBoundPassthrough

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- `IsLZ78EncodingLengthBoundPassthrough B` — hypothesis
pass-through for an upper bound `B : ℕ → ℕ` on the genuine greedy
encoding length `lz78GreedyEncodingLength`. -/
def IsLZ78EncodingLengthBoundPassthrough (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → α), lz78GreedyEncodingLength n x ≤ B n

@[simp] lemma isLZ78EncodingLengthBoundPassthrough_def (B : ℕ → ℕ) :
    IsLZ78EncodingLengthBoundPassthrough α B ↔
      ∀ (n : ℕ) (x : Fin n → α), lz78GreedyEncodingLength n x ≤ B n := Iff.rfl

/-- **Cover–Thomas Lemma 13.5.2 form discharges the bound
pass-through** with the canonical bound `n · (log(n+1) + log|α| + 2)`. -/
@[entry_point]
theorem IsLZ78EncodingLengthBoundPassthrough.canonical :
    IsLZ78EncodingLengthBoundPassthrough α
      (fun n ↦ n * (Nat.log 2 (n + 1) + Nat.log 2 (Fintype.card α) + 2)) := by
  intro n x
  exact lz78_encoding_length_le_n_log_n_plus_const n x

/-- Monotonicity of the bound pass-through. -/
@[entry_point]
theorem IsLZ78EncodingLengthBoundPassthrough.mono {B₁ B₂ : ℕ → ℕ}
    (h : IsLZ78EncodingLengthBoundPassthrough α B₁) (hB : ∀ n, B₁ n ≤ B₂ n) :
    IsLZ78EncodingLengthBoundPassthrough α B₂ := by
  intro n x
  exact (h n x).trans (hB n)

end EncodingLengthBoundPassthrough

end InformationTheory.Shannon
