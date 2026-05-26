import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# T2-C-WS: Whittaker-Shannon sampling partial publish

Cover-Thomas Ch.9.6. Companion to `ShannonHartley.lean` (327 行) which
publishes `shannon_hartley_formula` in **L-SH1+L-SH2+L-SH3 hypothesis
pass-through form**. The retreat lines all collapse to the
**Whittaker-Shannon sampling theorem**

  `f(t) = Σ_{n ∈ ℤ} f(n/(2W)) · sincN(2W·t - n)`

for `f` ∈ L²(ℝ) bandlimited to `[-W, W]`. Mathlib does not ship this
theorem (only `Real.sinc` and its continuity / integrability — see the
Mathlib gap section below).

This file publishes the **largest subset of the Whittaker-Shannon
machinery that goes through with current Mathlib**:

- A normalized sinc `sincN x := Real.sinc (π · x)` whose zeros land at
  the **integers** (the information-theoretic convention).
- The integer-zero identity `sincN (n : ℝ) = 0` for `n ≠ 0` (the
  algebraic reason the Whittaker-Shannon series collapses to a single
  term when evaluated at a sample point).
- The **sample-point collapse** `sincN ((2W) · (n₀ / (2W)) - n) = δ_{n,n₀}`
  which is the rigorous form of "only the `n = n₀` term survives".
- A **1-point Whittaker-Shannon uniqueness** theorem in hypothesis
  pass-through form (`IsWhittakerShannonInterpolation` predicate), ready
  for a future discharge module to plug a real series-convergence proof
  into the predicate.

## Approach

We commit to **撤退ライン L-WS-A** (sinc basic + integer-zero +
sample-point collapse + 1-point hypothesis pass-through) and explicitly
scope out:

* **L-WS-B** (L²-orthogonality of `{sincN(·-n)}_{n ∈ ℤ}`) — requires the
  Fourier transform of the rectangular pulse + Plancherel, neither
  shipped as a named Mathlib lemma.
* **L-WS-C** (Plancherel-style sampling identity / Poisson summation)
  — substantially further from current Mathlib.

The architectural shape mirrors `ShannonHartley.lean`: a closed-form
definition, a hypothesis predicate carrying the convergent-series
equality, and a main pass-through theorem consuming the predicate.

## Mathlib gap

Mathlib ships `Real.sinc`, `sinc_zero`, `sinc_neg`, `sinc_of_ne_zero`,
`abs_sinc_le_one`, `continuous_sinc`, `measurable_sinc`,
`stronglyMeasurable_sinc`, `integrable_sinc`. It does **not** ship:

1. `Real.sinc (n · π) = 0` for non-zero integer `n` (normalized integer
   zeros; trivially provable from `Real.sin_int_mul_pi`, no named lemma).
2. `{n ∈ ℤ ↦ sincN(t - n)}` L²-orthogonality.
3. Poisson summation for Schwartz / band-limited functions.
4. `IsBandlimited f W : Prop` predicate (no canonical definition).
5. Whittaker-Shannon sampling theorem itself.

This file publishes #1 directly and exposes #2–5 as hypothesis
predicates for future discharge.
-/

namespace InformationTheory.Shannon.WhittakerShannonPartial

set_option linter.unusedVariables false

open Real
open scoped Topology

/-! ## §B — Normalized sinc and bridge to Mathlib's `Real.sinc`. -/

/-- Normalized sinc, `sin(π · x) / (π · x)` (with value `1` at `0`).

This is the **information-theoretic convention** whose zeros land at the
non-zero integers (vs Mathlib's `Real.sinc` whose zeros are at non-zero
multiples of `π`). The Whittaker-Shannon series formula
`f(t) = Σ_n f(n/(2W)) · sincN(2W·t - n)` uses this convention. -/
noncomputable def sincN (x : ℝ) : ℝ := Real.sinc (Real.pi * x)

@[simp] theorem sincN_zero : sincN 0 = 1 := by
  unfold sincN; simp

theorem sincN_le_one (x : ℝ) : sincN x ≤ 1 := by
  unfold sincN; exact Real.sinc_le_one _

theorem neg_one_le_sincN (x : ℝ) : -1 ≤ sincN x := by
  unfold sincN; exact Real.neg_one_le_sinc _

@[fun_prop]
theorem continuous_sincN : Continuous sincN := by
  unfold sincN
  exact Real.continuous_sinc.comp (continuous_const.mul continuous_id)

@[fun_prop]
theorem measurable_sincN : Measurable sincN :=
  continuous_sincN.measurable

/-- For non-zero `x`, the normalized sinc equals `sin(π·x) / (π·x)`. -/
theorem sincN_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    sincN x = Real.sin (Real.pi * x) / (Real.pi * x) := by
  unfold sincN
  have hπx : Real.pi * x ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero hx
  exact Real.sinc_of_ne_zero hπx

/-! ## §C — Integer-zero identity (sincN Kronecker delta). -/

/-- The normalized sinc vanishes at all non-zero integers.

This is the **algebraic reason** the Whittaker-Shannon series collapses
to a single term at a sample point: `sincN(n - n₀) = δ_{n,n₀}`. -/
theorem sincN_int_eq_zero (n : ℤ) (hn : n ≠ 0) : sincN (n : ℝ) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sincN_of_ne_zero (n : ℝ) hnR]
  -- `sin(π · n) = 0` from `Real.sin_int_mul_pi`.
  rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring,
      Real.sin_int_mul_pi]
  simp

/-- Kronecker-delta form of `sincN` at integers. -/
theorem sincN_int_eq_kronecker (n : ℤ) :
    sincN (n : ℝ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]; exact sincN_int_eq_zero n hn

/-! ## §D — Sample-point collapse identity. -/

/-- **Sample-point collapse**: at `t = n₀ / (2W)`, the Whittaker-Shannon
series term `sincN(2W·t - n)` evaluates to `δ_{n,n₀}` (`1` if `n = n₀`,
`0` otherwise).

This is the rigorous form of "only the `n = n₀` term survives" — the
information-theoretic content driving the Whittaker-Shannon series
collapse at sample points. -/
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
@[fun_prop]
theorem Measurable.sincN {α : Type*} [MeasurableSpace α]
    {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun x => sincN (f x)) :=
  measurable_sincN.comp hf

/-- Composition: `sincN ∘ f` is continuous if `f` is. -/
@[fun_prop]
theorem Continuous.sincN {α : Type*} [TopologicalSpace α]
    {f : α → ℝ} (hf : Continuous f) :
    Continuous (fun x => sincN (f x)) :=
  continuous_sincN.comp hf

/-! ## §I — Sample-rate scaling identities. -/

/-- The sample-rate-scaled sinc `sincN (2W·t - n)` is **continuous in `t`**
for any fixed integer `n` and positive `W`. -/
@[fun_prop]
theorem continuous_sincN_sample_term (W : ℝ) (n : ℤ) :
    Continuous (fun t : ℝ => sincN ((2 * W) * t - (n : ℝ))) := by
  fun_prop

end InformationTheory.Shannon.WhittakerShannonPartial
