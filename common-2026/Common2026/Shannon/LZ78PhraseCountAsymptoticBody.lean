import Common2026.Shannon.LempelZiv78
import Common2026.Shannon.LZ78ZivInequality
import Common2026.Shannon.LZ78ConverseAsymptotic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# LZ78 phrase-count asymptotic envelope — genuine `IsBigO` discharge (S3 wave10)

This file discharges the predicate `IsLZ78PhraseCountAsymptotic p B`
(published in `Common2026/Shannon/LZ78ConverseAsymptotic.lean`) with
**genuine real-analysis content** rather than a hypothesis pass-through.

The target predicate unfolds to
`(fun n => ((p n).count : ℝ)) =O[atTop] (fun n => (n : ℝ) / Real.log n)`,
i.e. the Cover–Thomas Eq. 13.124 statement `c(n) = O(n / log n)`.

## Approach

The substantive ingredient is the **inversion** of the Ziv counting
inequality. Cover–Thomas Lemma 13.5.2 gives, for an LZ78 parsing of a
length-`n` string over a `b`-symbol alphabet, the *primitive* bound

```
c(n) · log c(n) ≤ K · n          (K = log b, large n)        (★)
```

We take `(★)` as the genuine more-primitive hypothesis and prove the
real-analysis lemma

```
(★) + (c n → handled pointwise)  ⟹  c(n) = O(n / log n).
```

The proof is an honest two-case argument at the threshold `√n = n^(1/2)`:

* **Large branch** `c(n) > √n`:  then `log c(n) > ½ log n`, so `(★)`
  gives `c(n) · ½ log n < K n`, hence `c(n) · log n ≤ 2K n`.
* **Small branch** `c(n) ≤ √n`:  then `c(n) · log n ≤ √n · log n`, and
  `log n ≤ 2√n` (`Real.log_natCast_le_rpow_div` with `ε = ½`), so
  `c(n) · log n ≤ √n · 2√n = 2n`.

In both branches `c(n) · log n ≤ C · n` with `C = max (2K) 2`, which —
since `log n > 0` eventually — is exactly `c(n) ≤ C · (n / log n)`, i.e.
the `IsBigO` bound with constant `C`.

## Layering

* **§1** — the threshold algebra helpers (`√n · √n = n`, `log √n`, the
  `log n ≤ 2√n` envelope).
* **§2** — the genuine inversion lemma `isBigO_natCast_div_log_of_mul_log_le`.
* **§3** — `IsZivCountingMulLogBound`, the primitive `(★)` predicate, plus
  the discharge `IsLZ78PhraseCountAsymptotic` from it.
* **§4** — re-published wrappers `lz78_phrase_count_asymptotic_of_mul_log`
  on top of `LZ78ConverseAsymptotic.lean`'s envelope.
-/

namespace InformationTheory.Shannon

open Filter Topology Asymptotics
open scoped BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. Threshold algebra (`√n = n^(1/2)`) -/

section ThresholdAlgebra

/-- `√x · √x = x` for `0 ≤ x`, with `√x := x ^ (1/2 : ℝ)`. -/
theorem rpow_half_mul_self (x : ℝ) (hx : 0 ≤ x) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]
  norm_num

/-- `log (x ^ (1/2)) = (1/2) · log x` for `0 < x`. -/
theorem log_rpow_half (x : ℝ) (hx : 0 < x) :
    Real.log (x ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log x := by
  rw [Real.log_rpow hx]

/-- The square-root envelope of `log`: `log n ≤ 2 · n^(1/2)`. -/
theorem log_natCast_le_two_mul_rpow_half (n : ℕ) :
    Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have h := Real.log_natCast_le_rpow_div n (ε := (1 / 2 : ℝ)) (by norm_num)
  -- `log n ≤ n ^ (1/2) / (1/2) = 2 * n ^ (1/2)`
  calc Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := h
    _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by ring

/-- `0 ≤ n^(1/2)`. -/
theorem rpow_half_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

end ThresholdAlgebra

/-! ## §2. The genuine inversion lemma -/

section Inversion

/-- **Genuine inversion (S3 core)**: from the primitive Cover–Thomas
`c(n) · log c(n) ≤ K · n` bound, the count `c(n)` is `O(n / log n)`.

`f : ℕ → ℝ` is the (nonnegative, real-valued) count sequence. The
hypotheses are all *eventual*: `f n ≥ 0` and the primitive product
bound. The `IsBigO` constant is `max (2K) 2`, so the result holds for
*any* real `K` (the negative-`K` case is vacuously stronger). -/
theorem isBigO_natCast_div_log_of_mul_log_le
    {f : ℕ → ℝ} {K : ℝ}
    (h_nonneg : ∀ᶠ n in atTop, 0 ≤ f n)
    (h_mul_log : ∀ᶠ n in atTop, f n * Real.log (f n) ≤ K * (n : ℝ)) :
    f =O[atTop] (fun n => (n : ℝ) / Real.log (n : ℝ)) := by
  -- Choose the constant `C = max (2K) 2`, valid in both branches.
  refine IsBigO.of_bound (max (2 * K) 2) ?_
  -- `1 < n` eventually gives `log n > 0` and `n > 0`.
  have h_one_lt : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < (n : ℝ) := by
    have : ∀ᶠ n : ℕ in atTop, 2 ≤ n := Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
    filter_upwards [this] with n hn
    exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast hn)
  filter_upwards [h_nonneg, h_mul_log, h_one_lt] with n hf hfl hn1
  -- Real positivity facts.
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn1
  have hdiv_nonneg : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) :=
    div_nonneg hn_pos.le hlogn_pos.le
  -- Norms collapse to the values (everything is nonnegative).
  rw [Real.norm_of_nonneg hf, Real.norm_of_nonneg hdiv_nonneg]
  -- It suffices to prove `f n * log n ≤ C * n` (then divide by `log n > 0`).
  rw [mul_div_assoc']
  rw [le_div_iff₀ hlogn_pos]
  -- Now goal: `f n * log n ≤ max (2K) 2 * n`.
  -- Case split at the threshold `√n = n ^ (1/2)`.
  have hsqrt_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := rpow_half_nonneg n
  rcases le_or_gt (f n) ((n : ℝ) ^ (1 / 2 : ℝ)) with hsmall | hlarge
  · -- **Small branch**: `f n ≤ √n`, so `f n * log n ≤ √n * 2√n = 2n ≤ C n`.
    have hlog_le : Real.log (n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) :=
      log_natCast_le_two_mul_rpow_half n
    have hstep : f n * Real.log (n : ℝ)
        ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (2 * (n : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul hsmall hlog_le hlogn_pos.le hsqrt_nonneg
    have hcollapse : (n : ℝ) ^ (1 / 2 : ℝ) * (2 * (n : ℝ) ^ (1 / 2 : ℝ))
        = 2 * (n : ℝ) := by
      rw [show (n : ℝ) ^ (1 / 2 : ℝ) * (2 * (n : ℝ) ^ (1 / 2 : ℝ))
            = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) by ring,
        rpow_half_mul_self _ hn_pos.le]
    rw [hcollapse] at hstep
    have hCge : (2 : ℝ) ≤ max (2 * K) 2 := le_max_right _ _
    calc f n * Real.log (n : ℝ) ≤ 2 * (n : ℝ) := hstep
      _ ≤ max (2 * K) 2 * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right hCge hn_pos.le
  · -- **Large branch**: `f n > √n`, so `log (f n) > ½ log n`, and the
    -- product bound gives `f n * log n ≤ 2K n ≤ C n`.
    have hfn_pos : (0 : ℝ) < f n := lt_of_le_of_lt hsqrt_nonneg hlarge
    have hsqrt_pos : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    -- `log (f n) > log (√n) = ½ log n` by strict monotonicity of `log`.
    have hlog_lt : Real.log ((n : ℝ) ^ (1 / 2 : ℝ)) < Real.log (f n) :=
      Real.log_lt_log hsqrt_pos hlarge
    have hlog_half : Real.log ((n : ℝ) ^ (1 / 2 : ℝ))
        = (1 / 2 : ℝ) * Real.log (n : ℝ) := log_rpow_half _ hn_pos
    -- Hence `½ log n < log (f n)`, and `f n > 0`, so
    -- `f n * (½ log n) ≤ f n * log (f n) ≤ K n`.
    have hhalf_lt : (1 / 2 : ℝ) * Real.log (n : ℝ) < Real.log (f n) := by
      rw [← hlog_half]; exact hlog_lt
    have hprod : f n * ((1 / 2 : ℝ) * Real.log (n : ℝ)) ≤ K * (n : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hhalf_lt.le hfn_pos.le) hfl
    -- Rearrange to `f n * log n ≤ 2K n`.
    have htwoKn : f n * Real.log (n : ℝ) ≤ (2 * K) * (n : ℝ) := by
      have : (1 / 2 : ℝ) * (f n * Real.log (n : ℝ)) ≤ K * (n : ℝ) := by
        rw [show (1 / 2 : ℝ) * (f n * Real.log (n : ℝ))
              = f n * ((1 / 2 : ℝ) * Real.log (n : ℝ)) by ring]
        exact hprod
      nlinarith [this]
    have hCge : (2 * K) ≤ max (2 * K) 2 := le_max_left _ _
    calc f n * Real.log (n : ℝ) ≤ (2 * K) * (n : ℝ) := htwoKn
      _ ≤ max (2 * K) 2 * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right hCge hn_pos.le

end Inversion

/-! ## §3. The primitive predicate `IsZivCountingMulLogBound` and discharge -/

section MulLogPredicate

variable {α : Type*}

/-- **Primitive Ziv `c·log c` product predicate (S3)**.

For a family of parsings `p : ℕ → LZ78Parsing α` and constant `K : ℝ`,
this asserts the Cover–Thomas Lemma 13.5.2 primitive bound `(★)`:
eventually `c(n) · log c(n) ≤ K · n`. This is *strictly more primitive*
than `IsLZ78PhraseCountAsymptotic` — the latter is derived from it by the
inversion lemma of §2. -/
def IsZivCountingMulLogBound (p : ℕ → LZ78Parsing α) (K : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((p n).count : ℝ) * Real.log ((p n).count : ℝ) ≤ K * (n : ℝ)

/-- **Genuine discharge of `IsLZ78PhraseCountAsymptotic`** from the
primitive `c·log c ≤ Kn` product bound. This is the S3 deliverable: the
asymptotic envelope predicate holds with genuine `IsBigO` content. -/
theorem IsLZ78PhraseCountAsymptotic.of_mul_log_bound
    {p : ℕ → LZ78Parsing α} {K : ℝ} (_hK : 0 ≤ K)
    (h : IsZivCountingMulLogBound p K) :
    IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ) / Real.log (n : ℝ)) := by
  unfold IsLZ78PhraseCountAsymptotic
  refine isBigO_natCast_div_log_of_mul_log_le (K := K) ?_ h
  -- `((p n).count : ℝ) ≥ 0` always.
  exact Filter.Eventually.of_forall (fun n => by exact_mod_cast Nat.zero_le _)

end MulLogPredicate

/-! ## §4. Re-published wrappers -/

section Wrappers

variable {α : Type*}

/-- **Re-published main S3 statement**: the LZ78 phrase-count is
`O(n / log n)` whenever the primitive product bound holds. Mirrors the
shape of `lz78_phrase_count_asymptotic_n_div_log` but with the genuine
`IsBigO` content supplied (no eventual-`≤` hypothesis needed). -/
theorem lz78_phrase_count_asymptotic_of_mul_log
    (p : ℕ → LZ78Parsing α) {K : ℝ} (hK : 0 ≤ K)
    (h : IsZivCountingMulLogBound p K) :
    IsLZ78PhraseCountAsymptotic p (fun n => (n : ℝ) / Real.log (n : ℝ)) :=
  IsLZ78PhraseCountAsymptotic.of_mul_log_bound hK h

/-- **Sandwich upgrade**: combine the genuine upper envelope with the
reflexive lower envelope into a phrase-count sandwich. -/
theorem IsLZ78PhraseCountSandwich.of_mul_log_bound
    (p : ℕ → LZ78Parsing α) {K : ℝ} (hK : 0 ≤ K)
    (h : IsZivCountingMulLogBound p K) :
    IsLZ78PhraseCountSandwich p
      (fun n => ((p n).count : ℝ))
      (fun n => (n : ℝ) / Real.log (n : ℝ)) :=
  IsLZ78PhraseCountSandwich.mk
    (IsLZ78PhraseCountAsymptotic.of_mul_log_bound hK h)
    (isBigO_refl _ _)

end Wrappers

end InformationTheory.Shannon
