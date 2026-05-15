import Common2026.Shannon.BackwardFiltration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Backward martingale convergence theorem (E-8'' / Birkhoff a.s. — Phase β)

This file states and partially develops the **backward (reverse) martingale
convergence theorem**: if `f : ℕᵒᵈ → Ω → ℝ` is a martingale with respect to
an antitone filtration `ℋ : Filtration ℕᵒᵈ m₀` (i.e. `ℋ` decreases as the
ℕ-index grows), and `f (toDual 0)` is integrable, then `f (toDual n)` converges
almost everywhere as `n → ∞` to a `⨅ n, ℋ (toDual n)`-measurable limit.

## Structure (per `docs/shannon/birkhoff-ergodic-plan.md` Phase β)

* **β.1** — `Martingale (ι := ℕᵒᵈ)` API works out of the box because Mathlib's
  `Martingale` is `Preorder ι`-generic (`Probability/Martingale/Basic.lean:53`).
  We expose two convenience renames (`backwardMartingale_condExp_ae_eq` and
  `BackwardMartingale.integrable`) tailored to the ℕᵒᵈ shape.
* **β.2** — Backward upcrossing inequality. **Sorry-skeleton.** The forward
  upcrossing inequality (`Probability/Martingale/Upcrossing.lean:686+`) is
  `ℕ`-hardcoded and the reverse adaptation requires ~150 lines of intricate
  bookkeeping (`reverseProxy N f n := f (toDual (N - n))`, forward-upcrossing
  finiteness, and re-indexing). Per the plan's retreat line, this lemma ships
  as a statement with `sorry`. Phase γ can build against the statement.
* **β.3** — L¹ contraction `eLpNorm (f n) 1 μ ≤ eLpNorm (f (toDual 0)) 1 μ`.
  Fully proven: backward martingale means `f n = 𝔼[f (toDual 0) | ℋ n]`
  (since `n ≤ toDual 0` in `ℕᵒᵈ`), then `eLpNorm_one_condExp_le_eLpNorm`.
* **β.4** — Main theorem `BackwardMartingale.ae_tendsto`. **Sorry-skeleton.**
  The proof skeleton would be: liminf-equals-limsup from upcrossing finiteness
  plus L¹ boundedness (β.3), then existence of a measurable limit using the
  same construction as `Submartingale.ae_tendsto_limitProcess`. Both ingredients
  depend on β.2 in its full reverse form.

## Retreat line

Per plan §5, the retreat line for β.2 has been adopted: the statements are
recorded with `sorry`, allowing Phase γ to proceed as a hypothesis-form
construction. Phase γ assembly then closes once β is filled (or a Mathlib PR
provides the forward→backward bridge).

## Main definitions / results

* `BackwardMartingale.integrable` — `Integrable (f n) μ` for every `n : ℕᵒᵈ`
  (re-export of `Martingale.integrable`).
* `backwardMartingale_eq_condExp` — `f n =ᵐ[μ] 𝔼[f (toDual 0) | ℋ n]`.
* `BackwardMartingale.eLpNorm_one_le` — L¹ bound (β.3).
* `BackwardMartingale.upcrossings_ae_lt_top` — **statement only / sorry** (β.2).
* `BackwardMartingale.ae_tendsto` — **statement only / sorry** (β.4).
-/

namespace InformationTheory.Shannon

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

section BasicAPI
/-! ### β.1 — `Martingale (ι := ℕᵒᵈ)` convenience wrappers -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- For a backward martingale `f` indexed by `ℕᵒᵈ`, every level is integrable. -/
theorem BackwardMartingale.integrable (hf : Martingale f ℋ μ) (n : ℕᵒᵈ) :
    Integrable (f n) μ :=
  hf.integrable n

/-- Backward martingale defining equation in ℕᵒᵈ form:
`f n =ᵐ[μ] 𝔼[f (toDual 0) | ℋ n]` since in `ℕᵒᵈ` we have `n ≤ toDual 0`. -/
theorem backwardMartingale_eq_condExp (hf : Martingale f ℋ μ) (n : ℕᵒᵈ) :
    f n =ᵐ[μ] μ[f (OrderDual.toDual 0) | ℋ n] := by
  -- In `ℕᵒᵈ`, `n ≤ toDual 0` because `ofDual n ≥ 0` in `ℕ`.
  have hle : n ≤ OrderDual.toDual 0 :=
    (Nat.zero_le (OrderDual.ofDual n) : (0 : ℕ) ≤ OrderDual.ofDual n)
  exact (hf.condExp_ae_eq hle).symm

end BasicAPI

section L1Bound
/-! ### β.3 — Automatic L¹ boundedness -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- L¹ contraction for backward martingales: `‖f n‖₁ ≤ ‖f (toDual 0)‖₁`.

Proof: `f n = 𝔼[f (toDual 0) | ℋ n]` a.e. (β.1), then apply
`eLpNorm_one_condExp_le_eLpNorm`. -/
theorem BackwardMartingale.eLpNorm_one_le
    (hf : Martingale f ℋ μ) (n : ℕᵒᵈ) :
    eLpNorm (f n) 1 μ ≤ eLpNorm (f (OrderDual.toDual 0)) 1 μ := by
  have h_eq : f n =ᵐ[μ] μ[f (OrderDual.toDual 0) | ℋ n] :=
    backwardMartingale_eq_condExp hf n
  calc eLpNorm (f n) 1 μ
      = eLpNorm (μ[f (OrderDual.toDual 0) | ℋ n]) 1 μ :=
        eLpNorm_congr_ae h_eq
    _ ≤ eLpNorm (f (OrderDual.toDual 0)) 1 μ :=
        eLpNorm_one_condExp_le_eLpNorm _

end L1Bound

section Upcrossings
/-! ### β.2 — Backward upcrossing inequality (retreat line / sorry-skeleton) -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- **Backward upcrossing finiteness.** For a backward martingale indexed by
`ℕᵒᵈ` with integrable head, the number of upcrossings of any rational interval
`(a, b)` along the sequence `n ↦ f (toDual n)` is almost surely finite.

This is the reverse-time analogue of
`Submartingale.upcrossings_ae_lt_top`
(`Probability/Martingale/Convergence.lean:184`).

**Status — sorry-skeleton (Phase β retreat line, see file docstring).** The
forward proof relies on Doob's upcrossing inequality
`mul_integral_upcrossingsBefore_le_integral_pos_part`
(`Probability/Martingale/Upcrossing.lean:690`), which is `ℕ`-hardcoded through
its dependence on `upperCrossingTime`, `lowerCrossingTime`, and
`upcrossingStrat` (each `ℕ`-indexed). Reverse-time adaptation requires either
re-deriving these objects for `ℕᵒᵈ` (~150 lines) or constructing a
`reverseProxy N f n := f (toDual (N - n))` and lifting forward results — both
are nontrivial Mathlib-PR-sized tasks. -/
theorem BackwardMartingale.upcrossings_ae_lt_top
    [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ)
    (hf_int : Integrable (f (OrderDual.toDual 0)) μ)
    (a b : ℝ) (_hab : a < b) :
    ∀ᵐ ω ∂μ,
      MeasureTheory.upcrossings a b (fun n : ℕ => f (OrderDual.toDual n)) ω < ∞ := by
  -- Retreat-line statement; see file docstring.
  sorry

end Upcrossings

section MainTheorem
/-! ### β.4 — Main theorem (retreat line / sorry-skeleton) -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- **Backward martingale convergence theorem.** If `f : ℕᵒᵈ → Ω → ℝ` is a
martingale with respect to an antitone filtration `ℋ : Filtration ℕᵒᵈ m₀` and
`f (toDual 0)` is integrable, then `n ↦ f (toDual n) ω` converges almost
everywhere as `n → ∞` to a `⨅ n, ℋ (toDual n)`-measurable limit `g`.

This is the reverse-time analogue of
`MeasureTheory.Submartingale.ae_tendsto_limitProcess`
(`Probability/Martingale/Convergence.lean:209`).

**Status — sorry-skeleton (Phase β retreat line, see file docstring).** The
proof requires Phase β.2 (`upcrossings_ae_lt_top`) plus the
`liminf = limsup` argument and a measurable-limit existence construction
analogous to Mathlib's `tendsto_of_uncrossing_lt_top`. Phase γ
(`BirkhoffErgodic.lean`) uses this statement as a hypothesis. -/
theorem BackwardMartingale.ae_tendsto
    [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ)
    (hf_int : Integrable (f (OrderDual.toDual 0)) μ) :
    ∃ g : Ω → ℝ,
      StronglyMeasurable[⨅ n : ℕ, ℋ (OrderDual.toDual n)] g ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (OrderDual.toDual n) ω)
          atTop (𝓝 (g ω)) := by
  -- Retreat-line statement; see file docstring.
  sorry

end MainTheorem

end InformationTheory.Shannon
