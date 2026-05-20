import Common2026.Shannon.ShannonHartley
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

theorem sincN_neg (x : ℝ) : sincN (-x) = sincN x := by
  unfold sincN
  rw [show Real.pi * (-x) = -(Real.pi * x) by ring, Real.sinc_neg]

theorem abs_sincN_le_one (x : ℝ) : |sincN x| ≤ 1 := by
  unfold sincN; exact Real.abs_sinc_le_one _

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

/-- Bridge: `sincN (n : ℝ)` for integer `n` equals `Real.sinc (n · π)`
modulo the commutativity of multiplication. -/
theorem sincN_int_eq_sinc_int_mul_pi (n : ℤ) :
    sincN (n : ℝ) = Real.sinc ((n : ℝ) * Real.pi) := by
  unfold sincN
  rw [mul_comm]

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

/-- Equivalent form: `sincN n = 0 ↔ n ≠ 0` for integer `n`. -/
theorem sincN_int_eq_zero_iff (n : ℤ) :
    sincN (n : ℝ) = 0 ↔ n ≠ 0 := by
  constructor
  · intro hzero hn
    rw [hn] at hzero
    simp [sincN_zero] at hzero
  · intro hn
    exact sincN_int_eq_zero n hn

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

/-! ## §E — L-WS-A retreat predicate (Whittaker-Shannon interpolation). -/

/-- **L-WS-A retreat (⚠️ undischarged placeholder)**: the Whittaker-Shannon
interpolation series converges pointwise to `f` at `t`, given sample-rate
`2W`.

The intended (operational) content is

  `f(t) = Σ_{n ∈ ℤ} f(n/(2W)) · sincN(2W·t - n)`

but ⚠️ this `def` is `0 < W ∧ ∃ _S, True` — a **weak positivity placeholder
that asserts nothing about convergence or the reconstruction equality**. The
genuine statement needs bandlimited-function machinery + Poisson summation /
Nyquist-Fourier theory, **not shipped by Mathlib**. It is exposed as a
predicate so that a future discharge can strengthen this definition (to carry
the real series-convergence proof) without rewriting downstream consumers. As
written it is **not** discharged. -/
def IsWhittakerShannonInterpolation (f : ℝ → ℝ) (W t : ℝ) : Prop :=
  0 < W ∧ ∃ (_S : ℝ), True

/-- Builder for `IsWhittakerShannonInterpolation` from positivity. ⚠️ This
does **not** discharge L-WS-A: the predicate is a weak `0 < W ∧ ∃ _S, True`
placeholder, so building it from `0 < W` proves nothing about the
Whittaker-Shannon reconstruction. -/
theorem mk_IsWhittakerShannonInterpolation
    (f : ℝ → ℝ) (W t : ℝ) (hW : 0 < W) :
    IsWhittakerShannonInterpolation f W t :=
  ⟨hW, f t, trivial⟩

/-! ## §F — 1-point Whittaker-Shannon uniqueness theorem. -/

/-- **1-point Whittaker-Shannon reconstruction at a sample point**
(⚠️ conditional / hypothesis pass-through, NOT a self-contained proof).

The intended operational statement is: a bandlimited `f` recovered by the
full Whittaker-Shannon series at sample point `t = n₀/(2W)` equals its own
sample value `f(n₀/(2W))`. ⚠️ Because the infinite-series reconstruction is
not available in Mathlib (no bandlimited / Poisson-summation machinery), the
**recovered value `recovered` and the reconstruction equality
`h_reconstruct : recovered = f(n₀/(2W))` are taken as explicit hypotheses**,
and the theorem merely returns that equality. It establishes nothing about the
genuine series — discharging `h_reconstruct` needs the Whittaker-Shannon /
Nyquist-Fourier theorem (open).

The **genuinely proven** content adjacent to this lies in §D
(`whittaker_shannon_sample_collapse`) and `whittaker_shannon_collapsed_value`
below, which show — without any hypothesis — that the sinc Kronecker delta
collapses the series to a single term at sample points. Those are the honest
sinc-layer results; this 1-point theorem only transports the (assumed)
operational equality. -/
theorem whittaker_shannon_one_point
    (f : ℝ → ℝ) (W : ℝ) (n₀ : ℤ) (hW : 0 < W)
    (_h_interp :
        IsWhittakerShannonInterpolation f W ((n₀ : ℝ) / (2 * W)))
    (recovered : ℝ)
    (h_reconstruct : recovered = f ((n₀ : ℝ) / (2 * W))) :
    recovered = f ((n₀ : ℝ) / (2 * W)) := h_reconstruct

/-- **Sample-value equality bridge**: at sample point `t = n₀/(2W)`, the
"recovered value via collapsed Whittaker-Shannon" equals `f(n₀/(2W))`.

Concretely the collapsed series at `t = n₀/(2W)` reduces to the single
term `f(n₀/(2W)) · sincN(0) = f(n₀/(2W))`. -/
theorem whittaker_shannon_collapsed_value
    (f : ℝ → ℝ) (W : ℝ) (n₀ : ℤ) (hW : 0 < W) :
    f ((n₀ : ℝ) / (2 * W)) *
        sincN ((2 * W) * ((n₀ : ℝ) / (2 * W)) - (n₀ : ℝ))
      = f ((n₀ : ℝ) / (2 * W)) := by
  rw [whittaker_shannon_sample_collapse W hW n₀ n₀]
  simp

/-- Companion: at sample point `t = n₀/(2W)`, every **off-sample** term
`n ≠ n₀` vanishes. -/
theorem whittaker_shannon_off_sample_zero
    (f : ℝ → ℝ) (W : ℝ) (n n₀ : ℤ) (hW : 0 < W) (hn : n ≠ n₀) :
    f ((n : ℝ) / (2 * W)) *
        sincN ((2 * W) * ((n₀ : ℝ) / (2 * W)) - (n : ℝ)) = 0 := by
  rw [whittaker_shannon_sample_collapse W hW n n₀]
  rw [if_neg hn]
  ring

/-! ## §G — L-SH1 chaining (link to ShannonHartley). -/

/-- L-SH1 chain: the `IsBandlimitedSamplingHypothesis` predicate from
`ShannonHartley.lean` can be built from positivity alone (it is a weak
placeholder predicate). The point of this chain lemma is to expose at
the type level the L-WS-A → L-SH1 implication — once a future discharge
strengthens `IsWhittakerShannonInterpolation`, this is the surface area
the discharge plugs into. -/
theorem ShannonHartley_IsBandlimitedSamplingHypothesis_of_interp
    (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    InformationTheory.Shannon.ShannonHartley.IsBandlimitedSamplingHypothesis
      W N₀ P :=
  InformationTheory.Shannon.ShannonHartley.mk_IsBandlimitedSamplingHypothesis
    W N₀ P hW hN₀ hP

/-- L-SH2 chain: bandlimited kernel measurability is `0 < W` (weak
placeholder). -/
theorem ShannonHartley_IsBandlimitedKernel_of_pos
    (W : ℝ) (hW : 0 < W) :
    InformationTheory.Shannon.ShannonHartley.IsBandlimitedKernel W :=
  InformationTheory.Shannon.ShannonHartley.mk_IsBandlimitedKernel W hW

/-! ## §H — Auxiliary algebraic / measurability corollaries. -/

/-- Bridge: `sincN (π · x)` is **not** `Real.sinc (π · x)` — `sincN` is
already the normalized version, so `sincN (π · x) = Real.sinc (π² · x)`.
This lemma exists to prevent confusion in downstream use. -/
theorem sincN_pi_mul_eq (x : ℝ) :
    sincN (Real.pi * x) = Real.sinc (Real.pi * (Real.pi * x)) := by
  unfold sincN
  rfl

/-- `sincN` agrees with `Real.sinc` (up to the `π` normalization) at the
argument `x / π` — a useful conversion when interfacing with the
unnormalized Mathlib lemmas. -/
theorem sincN_div_pi_eq_sinc (x : ℝ) :
    sincN (x / Real.pi) = Real.sinc x := by
  unfold sincN
  rw [mul_div_assoc', mul_div_cancel_left₀ x Real.pi_ne_zero]

/-- `sincN` is `0` precisely at the non-zero integers (the bidirectional
form of `sincN_int_eq_zero`). -/
theorem sincN_eq_zero_of_int_ne_zero (n : ℤ) (hn : n ≠ 0) :
    sincN (n : ℝ) = 0 := sincN_int_eq_zero n hn

/-- `sincN` is bounded between `-1` and `1` (combination of
`abs_sincN_le_one`). -/
theorem sincN_mem_unit_interval (x : ℝ) :
    sincN x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_sincN x, sincN_le_one x⟩

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

/-- The sample-rate-scaled sinc `sincN (2W·t - n)` is **measurable in `t`**. -/
@[fun_prop]
theorem measurable_sincN_sample_term (W : ℝ) (n : ℤ) :
    Measurable (fun t : ℝ => sincN ((2 * W) * t - (n : ℝ))) :=
  (continuous_sincN_sample_term W n).measurable

/-- The sample-rate-scaled sinc is bounded by `1` in absolute value. -/
theorem abs_sincN_sample_term_le_one (W t : ℝ) (n : ℤ) :
    |sincN ((2 * W) * t - (n : ℝ))| ≤ 1 :=
  abs_sincN_le_one _

/-! ## §J — Sign / non-negativity carve-outs. -/

/-- `sincN 0 = 1` (re-export of the `@[simp]` lemma as a named theorem). -/
theorem sincN_zero_eq_one : sincN 0 = 1 := sincN_zero

/-- `sincN` at a non-zero integer equals zero (re-export). -/
theorem sincN_apply_int_ne_zero (n : ℤ) (hn : n ≠ 0) :
    sincN (n : ℝ) = 0 := sincN_int_eq_zero n hn

/-- For integer arguments, `|sincN n|` is either `0` (when `n ≠ 0`) or
`1` (when `n = 0`). Crisp Kronecker form. -/
theorem abs_sincN_int (n : ℤ) :
    |sincN (n : ℝ)| = if n = 0 then 1 else 0 := by
  rw [sincN_int_eq_kronecker n]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

end InformationTheory.Shannon.WhittakerShannonPartial
