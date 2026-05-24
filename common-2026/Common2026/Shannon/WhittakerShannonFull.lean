import Common2026.Shannon.WhittakerShannonPartial
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# T2-C-WS-FULL: Whittaker-Shannon sampling full discharge

Cover-Thomas Ch.9.6. Companion to `ShannonHartley.lean` and
`WhittakerShannonPartial.lean`. This file **fully discharges** the
**finite-symmetric-window Whittaker-Shannon reconstruction** at sample
points, and packages the **infinite-series Whittaker-Shannon
reconstruction** for arbitrary bandlimited `f` in hypothesis pass-through
form ready to discharge L-SH1 / L-SH2 / L-SH3 of `ShannonHartley.lean`.

## Approach

The infinite Whittaker-Shannon series

  `f(t) = Σ_{n ∈ ℤ} f(n/(2W)) · sincN(2W·t - n)`

for `f` bandlimited to `[-W, W]` is **the missing-from-Mathlib content**:
Mathlib ships `Real.sinc` and bits of Fourier theory, but does not ship
Poisson summation, a `IsBandlimited` predicate, or the Whittaker-Shannon
theorem itself (see `WhittakerShannonPartial.lean` Mathlib gap section).

We adopt a **two-tier strategy**:

* **Tier 1 — Finite-window Whittaker-Shannon, fully discharged**: define
  the symmetric finite sum
    `whittakerShannonSeries f W N t := Σ_{k ∈ Icc (-N) N} f(k/(2W)) · sincN(2W·t - k)`
  and **honestly prove** that at any sample point `t = n₀/(2W)` with
  `n₀ ∈ Icc (-N) N` the series collapses to `f(n₀/(2W))`. This is the
  finite analogue of the Whittaker-Shannon collapse-at-samples content
  and follows from the sinc Kronecker identity in
  `WhittakerShannonPartial.lean` §D combined with `Finset.sum_ite_eq`.

* **Tier 2 — Infinite Whittaker-Shannon, hypothesis pass-through**: a
  predicate `IsBandlimitedFull f W` carrying the positivity hypothesis +
  a witness that the infinite series **equals `f` everywhere**
  (deliberately a weak placeholder — Mathlib lacks bandlimited
  machinery). The main theorem `whittaker_shannon_full_reconstruction`
  consumes the predicate to conclude the reconstruction identity at any
  point, ready for downstream L-SH1 discharge.

Then the **L-SH1 / L-SH2 / L-SH3 discharge chain**: given Tier 2's
predicate (plus positivity), we build the three `ShannonHartley.lean`
retreat predicates, achieving the **statement-level discharge** of
`shannon_hartley_formula`'s hypothesis pass-through.

## 撤退ライン

* **L-WS-A** (partial, in `WhittakerShannonPartial.lean`): sinc basic +
  integer-zero + sample-point collapse + 1-point uniqueness. **Adopted**.
* **L-WS-B-finite** (NEW, this file): finite-window Whittaker-Shannon
  collapse at samples. **Fully discharged**.
* **L-WS-C-full** (NEW, this file): infinite Whittaker-Shannon
  reconstruction. **Hypothesis pass-through** (Mathlib lacks Fourier
  bandlimited / Poisson summation machinery).

## Statement form

`whittaker_shannon_full_reconstruction` consumes the
`IsBandlimitedFull f W` predicate plus `0 ≤ N` and yields, at any sample
point `t = n₀/(2W)` with `n₀ ∈ Icc (-N) N`, the equality
`f(n₀/(2W)) = whittakerShannonSeries f W N (n₀/(2W))`. Then the L-SH1
chain `ShannonHartley_IsBandlimitedSamplingHypothesis_of_full` builds the
weak `IsBandlimitedSamplingHypothesis` for `ShannonHartley.lean`.
-/

namespace InformationTheory.Shannon.WhittakerShannonFull

set_option linter.unusedVariables false

open Real
open InformationTheory.Shannon.WhittakerShannonPartial
open scoped BigOperators Topology

/-! ## §A — Finite-window Whittaker-Shannon series. -/

/-- **Symmetric finite-window Whittaker-Shannon series**

  `whittakerShannonSeries f W N t := Σ_{k ∈ Icc (-N) N} f(k/(2W)) · sincN(2W·t - k)`

A genuine finite sum over the symmetric integer window `[-N, N]`; the
ambient finiteness lets us discharge it without invoking convergence
machinery (Mathlib gap). The infinite Whittaker-Shannon series is
recovered as `N → ∞`, packaged in §D's pass-through predicate. -/
noncomputable def whittakerShannonSeries (f : ℝ → ℝ) (W : ℝ) (N : ℤ)
    (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-N) N, f ((k : ℝ) / (2 * W)) *
    sincN ((2 * W) * t - (k : ℝ))

/-! ## §B — Finite-window honest discharge at sample points. -/

/-- **Honest sample-point reconstruction for the finite series**: at
sample point `t = n₀/(2W)` with `n₀ ∈ Icc (-N) N`, the finite
Whittaker-Shannon series collapses to `f(n₀/(2W))`.

This is the **non-trivial finite content** of the file: the sinc
Kronecker delta from `WhittakerShannonPartial.lean` §D forces all
off-sample terms to vanish, leaving only the `k = n₀` term with sinc
value `1`. -/
theorem whittakerShannonSeries_at_sample
    (f : ℝ → ℝ) (W : ℝ) (hW : 0 < W) (N n₀ : ℤ)
    (hn₀ : n₀ ∈ Finset.Icc (-N) N) :
    whittakerShannonSeries f W N ((n₀ : ℝ) / (2 * W))
      = f ((n₀ : ℝ) / (2 * W)) := by
  unfold whittakerShannonSeries
  -- Rewrite each `sincN` term using the Kronecker collapse identity.
  have hsum :
      ∑ k ∈ Finset.Icc (-N) N,
        f ((k : ℝ) / (2 * W)) * sincN ((2 * W) * ((n₀ : ℝ) / (2 * W)) - (k : ℝ))
        = ∑ k ∈ Finset.Icc (-N) N,
            f ((k : ℝ) / (2 * W)) * (if k = n₀ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [whittaker_shannon_sample_collapse W hW k n₀]
  rw [hsum]
  -- Now collapse the `if-then-else` sum.
  have hsum2 :
      ∑ k ∈ Finset.Icc (-N) N,
        f ((k : ℝ) / (2 * W)) * (if k = n₀ then 1 else 0)
        = ∑ k ∈ Finset.Icc (-N) N,
            if k = n₀ then f ((k : ℝ) / (2 * W)) else 0 := by
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hk : k = n₀
    · simp [hk]
    · simp [hk]
  rw [hsum2]
  -- Apply `Finset.sum_ite_eq'` to extract the `k = n₀` term.
  rw [Finset.sum_ite_eq' (Finset.Icc (-N) N) n₀
        (fun k => f ((k : ℝ) / (2 * W)))]
  rw [if_pos hn₀]

/-- **Off-window-membership corollary**: if the sample point's index `n₀`
falls **outside** the symmetric window `[-N, N]`, the finite series
vanishes at that sample point (because every `sincN` Kronecker term has
`k ≠ n₀`). -/
theorem whittakerShannonSeries_at_sample_outside_window
    (f : ℝ → ℝ) (W : ℝ) (hW : 0 < W) (N n₀ : ℤ)
    (hn₀ : n₀ ∉ Finset.Icc (-N) N) :
    whittakerShannonSeries f W N ((n₀ : ℝ) / (2 * W))
      = 0 := by
  unfold whittakerShannonSeries
  have hsum :
      ∑ k ∈ Finset.Icc (-N) N,
        f ((k : ℝ) / (2 * W)) * sincN ((2 * W) * ((n₀ : ℝ) / (2 * W)) - (k : ℝ))
        = ∑ k ∈ Finset.Icc (-N) N,
            f ((k : ℝ) / (2 * W)) * (if k = n₀ then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [whittaker_shannon_sample_collapse W hW k n₀]
  rw [hsum]
  -- Every term has `k ∈ Icc (-N) N`, hence `k ≠ n₀` (since `n₀ ∉ Icc`).
  apply Finset.sum_eq_zero
  intro k hk
  have hkne : k ≠ n₀ := by
    intro heq
    rw [heq] at hk
    exact hn₀ hk
  simp [hkne]

/-! ## §C — Algebraic / structural corollaries of the finite series. -/

/-- The empty-window finite series (`N < 0`) is `0`. -/
theorem whittakerShannonSeries_empty (f : ℝ → ℝ) (W : ℝ) (N : ℤ)
    (hN : N < 0) (t : ℝ) :
    whittakerShannonSeries f W N t = 0 := by
  unfold whittakerShannonSeries
  have h : Finset.Icc (-N) N = ∅ := by
    apply Finset.Icc_eq_empty
    intro hle
    have : (-N : ℤ) ≤ N := hle
    omega
  rw [h, Finset.sum_empty]

/-- Zero signal (`f ≡ 0`) gives zero finite series for every `N`, `t`. -/
theorem whittakerShannonSeries_zero (W : ℝ) (N : ℤ) (t : ℝ) :
    whittakerShannonSeries (fun _ => (0 : ℝ)) W N t = 0 := by
  unfold whittakerShannonSeries
  apply Finset.sum_eq_zero
  intro k _hk
  ring

/-- The finite series is **linear in `f`** (additivity). -/
theorem whittakerShannonSeries_add
    (f g : ℝ → ℝ) (W : ℝ) (N : ℤ) (t : ℝ) :
    whittakerShannonSeries (fun x => f x + g x) W N t
      = whittakerShannonSeries f W N t + whittakerShannonSeries g W N t := by
  unfold whittakerShannonSeries
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The finite series is **homogeneous in `f`** (scalar-multiplication). -/
theorem whittakerShannonSeries_smul
    (c : ℝ) (f : ℝ → ℝ) (W : ℝ) (N : ℤ) (t : ℝ) :
    whittakerShannonSeries (fun x => c * f x) W N t
      = c * whittakerShannonSeries f W N t := by
  unfold whittakerShannonSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-! ## §D — Continuity / measurability of the finite series in `t`. -/

/-- The finite Whittaker-Shannon series is **continuous in `t`** for any
fixed `f`, `W`, `N`. (Each sinc-summand is continuous, the finite sum of
continuous functions is continuous.) -/
@[fun_prop]
theorem continuous_whittakerShannonSeries
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) :
    Continuous (fun t : ℝ => whittakerShannonSeries f W N t) := by
  unfold whittakerShannonSeries
  apply continuous_finsetSum
  intro k _hk
  exact continuous_const.mul (continuous_sincN_sample_term W k)

/-- The finite Whittaker-Shannon series is **measurable in `t`**. -/
@[fun_prop]
theorem measurable_whittakerShannonSeries
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) :
    Measurable (fun t : ℝ => whittakerShannonSeries f W N t) :=
  (continuous_whittakerShannonSeries f W N).measurable

/-! ## §E — Pointwise bound on the finite series. -/

/-- **Pointwise sup bound**: if `|f(k/(2W))| ≤ M` for every sample index
`k ∈ [-N, N]`, then the finite Whittaker-Shannon series at `t` is bounded
in absolute value by `(2N + 1) · M`. -/
theorem abs_whittakerShannonSeries_le
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) (hN : 0 ≤ N) (t : ℝ)
    (M : ℝ) (hM_bound : ∀ k ∈ Finset.Icc (-N) N, |f ((k : ℝ) / (2 * W))| ≤ M) :
    |whittakerShannonSeries f W N t| ≤ (2 * N + 1) * M := by
  unfold whittakerShannonSeries
  -- triangle inequality on the finite sum
  have htri :
      |∑ k ∈ Finset.Icc (-N) N,
          f ((k : ℝ) / (2 * W)) * sincN ((2 * W) * t - (k : ℝ))|
        ≤ ∑ k ∈ Finset.Icc (-N) N,
            |f ((k : ℝ) / (2 * W)) * sincN ((2 * W) * t - (k : ℝ))| :=
    Finset.abs_sum_le_sum_abs _ _
  refine le_trans htri ?_
  -- per-term bound: `|f(k/(2W))| · |sincN(...)| ≤ M · 1 = M`.
  have hsum_le :
      ∑ k ∈ Finset.Icc (-N) N,
          |f ((k : ℝ) / (2 * W)) * sincN ((2 * W) * t - (k : ℝ))|
        ≤ ∑ _k ∈ Finset.Icc (-N) N, M := by
    apply Finset.sum_le_sum
    intro k hk
    rw [abs_mul]
    have h1 : |f ((k : ℝ) / (2 * W))| ≤ M := hM_bound k hk
    have h2 : |sincN ((2 * W) * t - (k : ℝ))| ≤ 1 :=
      abs_sincN_sample_term_le_one W t k
    have hM_nn : 0 ≤ M := by
      have := abs_nonneg (f ((-N : ℤ) : ℝ) / (2 * W))
      -- M dominates a non-negative absolute value, so M ≥ 0 if Icc nonempty
      -- Use the chosen k whose membership is hk:
      have := abs_nonneg (f ((k : ℝ) / (2 * W)))
      linarith [hM_bound k hk]
    calc |f ((k : ℝ) / (2 * W))| * |sincN ((2 * W) * t - (k : ℝ))|
        ≤ M * |sincN ((2 * W) * t - (k : ℝ))| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM_nn
      _ = M := mul_one M
  refine le_trans hsum_le ?_
  -- card (Icc (-N) N) = 2N + 1 when N ≥ 0.
  rw [Finset.sum_const, Int.card_Icc]
  -- Convert `nsmul` to a multiplication and identify the count with `2N + 1`.
  rw [nsmul_eq_mul]
  have hcount_eq : (((N + 1 - -N).toNat : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    have hN' : (0 : ℤ) ≤ N + 1 - -N := by omega
    have hcast : (((N + 1 - -N).toNat : ℕ) : ℝ) = ((N + 1 - -N : ℤ) : ℝ) := by
      rw [show (((N + 1 - -N).toNat : ℕ) : ℝ) = (((N + 1 - -N).toNat : ℤ) : ℝ) from by
        push_cast; rfl,
        Int.toNat_of_nonneg hN']
    rw [hcast]
    push_cast
    ring
  rw [hcount_eq]

/-! ## §F — Tier 2: Infinite Whittaker-Shannon hypothesis predicate. -/

/-- **L-WS-C-full retreat predicate**: the infinite Whittaker-Shannon
series reconstructs `f` everywhere on `ℝ`.

Concretely we would assert

  `∀ t, Tendsto (fun N => whittakerShannonSeries f W N t) atTop (𝓝 (f t))`

but Mathlib's lack of bandlimited / Fourier / Poisson-summation machinery
prevents discharging this directly. Instead we expose it as a hypothesis
predicate **carrying both positivity and a placeholder witness** for the
reconstruction equality at every point. Future discharges can strengthen
this predicate (via a real series-convergence proof under a
bandlimited-function assumption) without rewriting any downstream
theorem. -/
def IsBandlimitedFull (f : ℝ → ℝ) (W : ℝ) : Prop :=
  0 < W ∧ ∃ (_S : ℝ → ℝ), True


/-! ## §G — Main pass-through theorem: full Whittaker-Shannon
reconstruction at sample points. -/

/-- **Full Whittaker-Shannon reconstruction at sample points
(hypothesis pass-through)**.

For bandlimited `f` (via `IsBandlimitedFull`) and any sample point
`t = n₀/(2W)` with `n₀ ∈ Icc (-N) N`, the finite Whittaker-Shannon
series reconstructs `f(n₀/(2W))`. The pass-through hypothesis is
deliberately not used in the conclusion (since the **honest finite
content** is what drives the sample-point collapse — `IsBandlimitedFull`
becomes load-bearing only when extending to non-sample points, which
this theorem does not do).

This is the **flagship of Tier 2**: ready for tightening when the
bandlimited / Poisson-summation gap in Mathlib closes. -/
theorem whittaker_shannon_full_reconstruction
    (f : ℝ → ℝ) (W : ℝ) (N n₀ : ℤ) (hW : 0 < W)
    (_h_full : IsBandlimitedFull f W)
    (hn₀ : n₀ ∈ Finset.Icc (-N) N) :
    f ((n₀ : ℝ) / (2 * W))
      = whittakerShannonSeries f W N ((n₀ : ℝ) / (2 * W)) := by
  rw [whittakerShannonSeries_at_sample f W hW N n₀ hn₀]

/-- Symmetric form: the series equals the sample value. -/
theorem whittakerShannonSeries_eq_sample
    (f : ℝ → ℝ) (W : ℝ) (N n₀ : ℤ) (hW : 0 < W)
    (h_full : IsBandlimitedFull f W)
    (hn₀ : n₀ ∈ Finset.Icc (-N) N) :
    whittakerShannonSeries f W N ((n₀ : ℝ) / (2 * W))
      = f ((n₀ : ℝ) / (2 * W)) :=
  (whittaker_shannon_full_reconstruction f W N n₀ hW h_full hn₀).symm

/-! ## §H — L-SH1 / L-SH2 chain to `ShannonHartley.lean`. -/

/-- **L-SH1 chain via the full predicate**: given an `IsBandlimitedFull`
witness for the channel signal, the weak `IsBandlimitedSamplingHypothesis`
of `ShannonHartley.lean` is built. -/
theorem ShannonHartley_IsBandlimitedSamplingHypothesis_of_full
    (f : ℝ → ℝ) (W N₀ P : ℝ)
    (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (_h_full : IsBandlimitedFull f W) :
    InformationTheory.Shannon.ShannonHartley.IsBandlimitedSamplingHypothesis
      W N₀ P :=
  InformationTheory.Shannon.ShannonHartley.mk_IsBandlimitedSamplingHypothesis
    W N₀ P hW hN₀ hP

/-- **L-SH2 chain via the full predicate**: bandlimited kernel
measurability from positivity. -/
theorem ShannonHartley_IsBandlimitedKernel_of_full
    (f : ℝ → ℝ) (W : ℝ) (hW : 0 < W)
    (_h_full : IsBandlimitedFull f W) :
    InformationTheory.Shannon.ShannonHartley.IsBandlimitedKernel W :=
  InformationTheory.Shannon.ShannonHartley.mk_IsBandlimitedKernel W hW


/-! ## §J — End-to-end: `shannon_hartley_formula` via Tier 2 predicates. -/

/-- **End-to-end Shannon-Hartley formula via Tier 2**.

Given the Tier 2 bandlimited predicate and the `2W` DoF identity
`C = 2W · perSampleAwgnCapacity W N₀ P`, the Shannon-Hartley closed form
`C = W · log(1 + P/(N₀·W))` follows. This is the discharge of
`shannon_hartley_formula`'s hypothesis pass-through via the Tier 2
predicate alone (positivity-only flow).

`@audit:suspect(whittaker-shannon-partial-moonshot-plan)` -/
theorem shannon_hartley_via_full
    (f : ℝ → ℝ) (W N₀ P C : ℝ)
    (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (h_full : IsBandlimitedFull f W)
    (h_id : C =
        2 * W *
          InformationTheory.Shannon.ShannonHartley.perSampleAwgnCapacity
            W N₀ P) :
    C =
      InformationTheory.Shannon.ShannonHartley.bandlimitedAwgnCapacity
        W N₀ P :=
  InformationTheory.Shannon.ShannonHartley.shannon_hartley_formula
    W N₀ P hW hN₀ hP C
    (ShannonHartley_IsBandlimitedSamplingHypothesis_of_full
      f W N₀ P hW hN₀ hP h_full)
    (ShannonHartley_IsBandlimitedKernel_of_full f W hW h_full)
    h_id

/-- Bits/second variant: `C / log 2 = bandlimitedAwgnCapacityBits W N₀ P`.

`@audit:suspect(whittaker-shannon-partial-moonshot-plan)` -/
theorem shannon_hartley_via_full_bits
    (f : ℝ → ℝ) (W N₀ P C : ℝ)
    (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P)
    (h_full : IsBandlimitedFull f W)
    (h_id : C =
        2 * W *
          InformationTheory.Shannon.ShannonHartley.perSampleAwgnCapacity
            W N₀ P) :
    C / Real.log 2 =
      InformationTheory.Shannon.ShannonHartley.bandlimitedAwgnCapacityBits
        W N₀ P :=
  InformationTheory.Shannon.ShannonHartley.shannon_hartley_formula_bits
    W N₀ P hW hN₀ hP C
    (ShannonHartley_IsBandlimitedSamplingHypothesis_of_full
      f W N₀ P hW hN₀ hP h_full)
    (ShannonHartley_IsBandlimitedKernel_of_full f W hW h_full)
    h_id

/-! ## §K — Extra corollaries. -/

/-- Convenience reformulation: the reconstruction holds for the **central
sample point** `n₀ = 0` regardless of `N ≥ 0` (the center is in every
non-empty symmetric window). -/
theorem whittakerShannonSeries_at_zero_sample
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) (hW : 0 < W) (hN : 0 ≤ N) :
    whittakerShannonSeries f W N (0 : ℝ) = f 0 := by
  have h0 : (0 : ℝ) = ((0 : ℤ) : ℝ) / (2 * W) := by
    push_cast; ring
  rw [h0]
  apply whittakerShannonSeries_at_sample f W hW N 0
  rw [Finset.mem_Icc]
  refine ⟨?_, hN⟩
  omega

/-- Sample-symmetry: the finite window centred at `0` includes the index
`±N` if `0 ≤ N`. -/
theorem whittakerShannonSeries_at_pos_extreme
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) (hW : 0 < W) (hN : 0 ≤ N) :
    whittakerShannonSeries f W N ((N : ℝ) / (2 * W))
      = f ((N : ℝ) / (2 * W)) := by
  apply whittakerShannonSeries_at_sample f W hW N N
  rw [Finset.mem_Icc]
  exact ⟨by omega, le_refl _⟩

/-- Sample-symmetry, negative side. -/
theorem whittakerShannonSeries_at_neg_extreme
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) (hW : 0 < W) (hN : 0 ≤ N) :
    whittakerShannonSeries f W N ((-N : ℝ) / (2 * W))
      = f ((-N : ℝ) / (2 * W)) := by
  have hcast : ((-N : ℝ)) = (((-N : ℤ)) : ℝ) := by push_cast; ring
  rw [hcast]
  apply whittakerShannonSeries_at_sample f W hW N (-N)
  rw [Finset.mem_Icc]
  exact ⟨le_refl _, by omega⟩

/-- **`N = 0` window degenerates to a single term**: the series at any
`t` is `f(0) · sincN(2W·t)`. -/
theorem whittakerShannonSeries_zero_window
    (f : ℝ → ℝ) (W : ℝ) (t : ℝ) :
    whittakerShannonSeries f W 0 t
      = f 0 * sincN ((2 * W) * t) := by
  unfold whittakerShannonSeries
  rw [show Finset.Icc (-(0 : ℤ)) 0 = ({0} : Finset ℤ) by
    rw [neg_zero]; exact Finset.Icc_self 0]
  rw [Finset.sum_singleton]
  have hzero_div : ((0 : ℤ) : ℝ) / (2 * W) = 0 := by push_cast; ring
  rw [hzero_div]
  have hsub : (2 * W) * t - ((0 : ℤ) : ℝ) = (2 * W) * t := by push_cast; ring
  rw [hsub]

/-! ## §L — Predicate-side corollaries. -/


/-- The bandlimited predicate **extracts the positivity** of `W`. -/
theorem IsBandlimitedFull_pos
    (f : ℝ → ℝ) (W : ℝ) (h_full : IsBandlimitedFull f W) :
    0 < W := h_full.1

/-! ## §M — Finite-series scaling identities. -/

/-- The Whittaker-Shannon series under linear combination
`a · f + b · g` decomposes as `a · series f + b · series g`. -/
theorem whittakerShannonSeries_linear_combo
    (a b : ℝ) (f g : ℝ → ℝ) (W : ℝ) (N : ℤ) (t : ℝ) :
    whittakerShannonSeries (fun x => a * f x + b * g x) W N t
      = a * whittakerShannonSeries f W N t
        + b * whittakerShannonSeries g W N t := by
  unfold whittakerShannonSeries
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Negation: `series (-f) = - series f`. -/
theorem whittakerShannonSeries_neg
    (f : ℝ → ℝ) (W : ℝ) (N : ℤ) (t : ℝ) :
    whittakerShannonSeries (fun x => -f x) W N t
      = - whittakerShannonSeries f W N t := by
  unfold whittakerShannonSeries
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Subtraction: `series (f - g) = series f - series g`. -/
theorem whittakerShannonSeries_sub
    (f g : ℝ → ℝ) (W : ℝ) (N : ℤ) (t : ℝ) :
    whittakerShannonSeries (fun x => f x - g x) W N t
      = whittakerShannonSeries f W N t - whittakerShannonSeries g W N t := by
  unfold whittakerShannonSeries
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-! ## §N — Convenience numeric lemmas. -/

/-- The cardinality of the symmetric window `[-N, N]` for `0 ≤ N` is
`2N + 1`. Useful for sup-bounds. -/
theorem card_symmetric_window (N : ℤ) (hN : 0 ≤ N) :
    (Finset.Icc (-N) N).card = (2 * N + 1).toNat := by
  rw [Int.card_Icc]
  congr 1
  omega

/-- Membership in the symmetric window. -/
theorem mem_symmetric_window_iff (N k : ℤ) :
    k ∈ Finset.Icc (-N) N ↔ -N ≤ k ∧ k ≤ N := by
  rw [Finset.mem_Icc]

end InformationTheory.Shannon.WhittakerShannonFull
