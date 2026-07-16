import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InformationTheory.Meta.EntryPoint

/-!
# Whittaker-Shannon sampling (partial, Cover-Thomas Ch.9.6)

Companion to `ShannonHartley.lean`. Mathlib does not ship the Whittaker-Shannon
sampling theorem `f(t) = Σ_{n ∈ ℤ} f(n/(2W)) · sincN(2W·t - n)` for
`f ∈ L²(ℝ)` bandlimited to `[-W, W]`.

This file publishes the subset of the Whittaker-Shannon machinery available in
current Mathlib:

- `sincN x := Real.sinc (π · x)` — normalized sinc whose zeros are at the integers.
- `sincN_int_eq_zero` — the integer-zero identity `sincN (n : ℝ) = 0` for `n ≠ 0`.
- `whittaker_shannon_sample_collapse` — `sincN((2W)·(n₀/(2W)) − n) = δ_{n,n₀}`.

## Main statements

* `sincN_le_one`, `neg_one_le_sincN` — pointwise bounds.
* `continuous_sincN`, `measurable_sincN` — regularity.
* `sincN_int_eq_zero`, `sincN_int_eq_kronecker` — zeros at nonzero integers.
* `whittaker_shannon_sample_collapse` — sample-point collapse (Kronecker delta form).

## Implementation notes

L²-orthogonality of `{sincN(·-n)}_{n ∈ ℤ}` requires the Fourier transform of the
rectangular pulse and Plancherel; Poisson summation requires Schwartz-class results.
Neither is available in Mathlib, so both are out of scope here.
-/

namespace InformationTheory.Shannon.NormalizedSinc

set_option linter.unusedVariables false

open Real
open scoped Topology

/-! ## §B — Normalized sinc and bridge to Mathlib's `Real.sinc`. -/

/-- Normalized sinc, `sin(π · x) / (π · x)` (with value `1` at `0`).

This is the information-theoretic convention whose zeros land at the
non-zero integers (vs Mathlib's `Real.sinc` whose zeros are at non-zero
multiples of `π`). The Whittaker-Shannon series formula
`f(t) = Σ_n f(n/(2W)) · sincN(2W·t - n)` uses this convention. -/
noncomputable def sincN (x : ℝ) : ℝ := Real.sinc (Real.pi * x)

@[simp] theorem sincN_zero : sincN 0 = 1 := by
  unfold sincN; simp

@[entry_point]
theorem sincN_le_one (x : ℝ) : sincN x ≤ 1 := by
  unfold sincN; exact Real.sinc_le_one _

@[entry_point]
theorem neg_one_le_sincN (x : ℝ) : -1 ≤ sincN x := by
  unfold sincN; exact Real.neg_one_le_sinc _

theorem sincN_neg (x : ℝ) : sincN (-x) = sincN x := by
  unfold sincN; rw [mul_neg, Real.sinc_neg]

@[entry_point, fun_prop]
theorem continuous_sincN : Continuous sincN := by
  unfold sincN
  exact Real.continuous_sinc.comp (continuous_const.mul continuous_id)

@[entry_point, fun_prop]
theorem measurable_sincN : Measurable sincN :=
  continuous_sincN.measurable

theorem sincN_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    sincN x = Real.sin (Real.pi * x) / (Real.pi * x) := by
  unfold sincN
  have hπx : Real.pi * x ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero hx
  exact Real.sinc_of_ne_zero hπx

/-! ## §C — Integer-zero identity (sincN Kronecker delta). -/

/-- The normalized sinc vanishes at all non-zero integers.

This is the algebraic reason the Whittaker-Shannon series collapses
to a single term at a sample point: `sincN(n - n₀) = δ_{n,n₀}`. -/
@[entry_point]
theorem sincN_int_eq_zero (n : ℤ) (hn : n ≠ 0) : sincN (n : ℝ) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sincN_of_ne_zero (n : ℝ) hnR]
  -- `sin(π · n) = 0` from `Real.sin_int_mul_pi`.
  rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring,
      Real.sin_int_mul_pi]
  simp

/-- Kronecker-delta form of `sincN` at integers. -/
@[entry_point]
theorem sincN_int_eq_kronecker (n : ℤ) :
    sincN (n : ℝ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]; exact sincN_int_eq_zero n hn

/-! ## §D — Sample-point collapse identity. -/

/-- The sample-point collapse identity: at `t = n₀ / (2W)`, the Whittaker-Shannon
series term `sincN(2W·t - n)` evaluates to `δ_{n,n₀}` (`1` if `n = n₀`,
`0` otherwise).

This is the rigorous form of "only the `n = n₀` term survives" — the
information-theoretic content driving the Whittaker-Shannon series
collapse at sample points. -/
@[entry_point]
theorem whittaker_shannon_sample_collapse
    (W : ℝ) (hW : 0 < W) (n n₀ : ℤ) :
    sincN ((2 * W) * ((n₀ : ℝ) / (2 * W)) - (n : ℝ))
      = if n = n₀ then 1 else 0 := by
  have h2W : (2 * W) ≠ 0 := by positivity
  -- Simplify the argument to `(n₀ - n : ℝ)`.
  have harg : (2 * W) * ((n₀ : ℝ) / (2 * W)) - (n : ℝ) = ((n₀ - n : ℤ) : ℝ) := by
    field_simp
    push_cast
    ring
  rw [harg, sincN_int_eq_kronecker]
  -- `n₀ - n = 0 ↔ n = n₀`.
  by_cases hn : n = n₀
  · simp [hn]
  · have hne : n₀ - n ≠ 0 := by
      intro h
      exact hn (by omega)
    simp [hn, hne]

/-! ## §H — Auxiliary algebraic / measurability corollaries. -/

/-- Composition: `sincN ∘ f` is measurable if `f` is. -/
@[entry_point, fun_prop]
theorem Measurable.sincN {α : Type*} [MeasurableSpace α]
    {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun x ↦ sincN (f x)) :=
  measurable_sincN.comp hf

/-- Composition: `sincN ∘ f` is continuous if `f` is. -/
@[entry_point, fun_prop]
theorem Continuous.sincN {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} (hf : Continuous f) :
    Continuous (fun x ↦ sincN (f x)) :=
  continuous_sincN.comp hf

/-! ## §I — Sample-rate scaling identities. -/

/-- The sample-rate-scaled sinc `sincN (2W·t - n)` is continuous in `t`
for any fixed integer `n` and positive `W`. -/
@[entry_point, fun_prop]
theorem continuous_sincN_sample_term (W : ℝ) (n : ℤ) :
    Continuous (fun t : ℝ ↦ sincN ((2 * W) * t - (n : ℝ))) := by
  fun_prop

end InformationTheory.Shannon.NormalizedSinc
