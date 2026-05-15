import Common2026.Shannon.BackwardFiltration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Upcrossing
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
* **β.2** — Backward upcrossing inequality. **Sorry-skeleton.** See the
  retreat-line note attached to `BackwardMartingale.upcrossings_ae_lt_top`.
* **β.3** — L¹ contraction `eLpNorm (f n) 1 μ ≤ eLpNorm (f (toDual 0)) 1 μ`.
  Fully proven: backward martingale means `f n = 𝔼[f (toDual 0) | ℋ n]`
  (since `n ≤ toDual 0` in `ℕᵒᵈ`), then `eLpNorm_one_condExp_le_eLpNorm`.
* **β.4** — Main theorem `BackwardMartingale.ae_tendsto`. **Sorry-skeleton.**
  See the retreat-line note attached to `BackwardMartingale.ae_tendsto`.

## Proxy machinery (Phase β scaffolding)

The proofs of β.2 and β.4 hinge on lifting a finite-window forward proxy to
the global backward sequence. We introduce the proxy infrastructure here:

* `reverseProxy N f k ω := f (toDual (N - k)) ω` — a forward sequence indexed
  by `k : ℕ` whose values along `[0, N]` are the reverse of `f (toDual ·)` on
  `[0, N]`.
* `reverseFiltration N ℋ k := ℋ (toDual (N - k))` — the matching forward
  `Filtration ℕ m₀`. Since `k ↦ N - k` is antitone in `ℕ` and `ℋ` is monotone
  in `ℕᵒᵈ`, the composition is monotone in `ℕ`.
* `reverseProxy_isMartingale` — Mathlib forward `Martingale` for `reverseProxy`
  / `reverseFiltration`, derived from the ℕᵒᵈ martingale equation.

These three definitions / lemma are used in the (still-sorry) attempts to
discharge β.2 / β.4 below; they are general-purpose and would persist in any
future completion or Mathlib-PR-shaped lift.

## Retreat line

Per plan §5, the retreat line for β.2 / β.4 has been adopted: the statements
are recorded with `sorry` and Phase γ proceeds against them as hypotheses.
The single missing ingredient — a **path-reversal inequality** for
`upcrossingsBefore` (no analogue currently exists in Mathlib) — is documented
in the relevant theorem comments.

## Main definitions / results

* `BackwardMartingale.integrable` — `Integrable (f n) μ` for every `n : ℕᵒᵈ`
  (re-export of `Martingale.integrable`).
* `backwardMartingale_eq_condExp` — `f n =ᵐ[μ] 𝔼[f (toDual 0) | ℋ n]`.
* `BackwardMartingale.eLpNorm_one_le` — L¹ bound (β.3).
* `reverseProxy`, `reverseFiltration`, `reverseProxy_isMartingale` —
  forward-proxy machinery for the finite-window forward Doob argument.
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

section ReverseProxy
/-! ### Forward proxy for finite-window Doob arguments

Given a backward martingale `f : ℕᵒᵈ → Ω → ℝ` w.r.t. `ℋ : Filtration ℕᵒᵈ m₀`
and a horizon `N : ℕ`, the *reverse proxy* is the forward `ℕ`-indexed sequence

```
reverseProxy N f k ω := f (toDual (N - k)) ω
```

with matching filtration `reverseFiltration N ℋ k := ℋ (toDual (N - k))`.
Past `k = N` both stabilise (since `N - k = 0` in `ℕ`), so the proxy is a
genuine `Filtration ℕ m₀` and a genuine `Martingale (ι := ℕ)`. This lets us
plug the proxy directly into `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`
and other forward-time Doob estimates. -/

variable (N : ℕ) (f : ℕᵒᵈ → Ω → ℝ) (ℋ : Filtration ℕᵒᵈ m₀)

/-- The forward `ℕ`-indexed proxy sequence
`reverseProxy N f k ω := f (toDual (N - k)) ω`. -/
def reverseProxy : ℕ → Ω → ℝ := fun k ω => f (OrderDual.toDual (N - k)) ω

/-- The forward `ℕ`-indexed proxy filtration
`reverseFiltration N ℋ k := ℋ (toDual (N - k))`.

`Monotone` in `k` because `k ↦ N - k` is antitone on `ℕ` and `ℋ` is monotone
in `ℕᵒᵈ`; the composition `k ↦ ℋ (toDual (N - k))` is therefore monotone. -/
def reverseFiltration : Filtration ℕ m₀ where
  seq k := ℋ (OrderDual.toDual (N - k))
  mono' i j hij := by
    -- For `i ≤ j` in ℕ, `N - j ≤ N - i` in ℕ, hence
    -- `toDual (N - i) ≤ toDual (N - j)` in ℕᵒᵈ, so by `ℋ.mono`:
    have h_sub : N - j ≤ N - i := Nat.sub_le_sub_left hij N
    -- In `ℕᵒᵈ`, `toDual (N - i) ≤ toDual (N - j)` ↔ `N - j ≤ N - i` in `ℕ`.
    have h_dual : OrderDual.toDual (N - i) ≤ OrderDual.toDual (N - j) :=
      OrderDual.toDual_le_toDual.mpr h_sub
    exact ℋ.mono h_dual
  le' k := ℋ.le _

@[simp] lemma reverseProxy_apply (k : ℕ) (ω : Ω) :
    reverseProxy N f k ω = f (OrderDual.toDual (N - k)) ω := rfl

@[simp] lemma reverseFiltration_apply (k : ℕ) :
    reverseFiltration N ℋ k = ℋ (OrderDual.toDual (N - k)) := rfl

variable {N f ℋ}

/-- The reverse proxy is a forward `ℕ`-indexed `Martingale` whenever the
underlying ℕᵒᵈ-indexed sequence is. -/
theorem reverseProxy_isMartingale (hf : Martingale f ℋ μ) :
    Martingale (reverseProxy N f) (reverseFiltration N ℋ) μ := by
  refine ⟨?_, ?_⟩
  · -- StronglyAdapted: each `reverseProxy N f k = f (toDual (N - k))` is
    -- `ℋ (toDual (N - k))`-strongly measurable, which is the proxy filtration.
    intro k
    exact hf.stronglyAdapted (OrderDual.toDual (N - k))
  · -- Martingale equation: for `i ≤ j` in ℕ,
    -- `μ[reverseProxy N f j | reverseFiltration N ℋ i] =ᵐ[μ] reverseProxy N f i`.
    intro i j hij
    -- Translate to ℕᵒᵈ: `toDual (N - i) ≤ toDual (N - j)` in ℕᵒᵈ
    -- because `N - j ≤ N - i` in ℕ (and `toDual` reverses order).
    have h_sub : N - j ≤ N - i := Nat.sub_le_sub_left hij N
    have h_dual : OrderDual.toDual (N - i) ≤ OrderDual.toDual (N - j) :=
      OrderDual.toDual_le_toDual.mpr h_sub
    -- Apply the ℕᵒᵈ-martingale equation at `(toDual (N - i), toDual (N - j))`:
    -- `μ[f (toDual (N - j)) | ℋ (toDual (N - i))] =ᵐ[μ] f (toDual (N - i))`.
    -- Unfolding:
    --   reverseProxy N f j = f (toDual (N - j))
    --   reverseProxy N f i = f (toDual (N - i))
    --   reverseFiltration N ℋ i = ℋ (toDual (N - i))
    -- this is exactly the desired equation.
    exact hf.condExp_ae_eq h_dual

end ReverseProxy

section Upcrossings
/-! ### β.2 — Backward upcrossing inequality (retreat line / sorry-skeleton) -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- **Backward upcrossing finiteness.** For a backward martingale indexed by
`ℕᵒᵈ` with integrable head, the number of upcrossings of any rational interval
`(a, b)` along the sequence `n ↦ f (toDual n)` is almost surely finite.

This is the reverse-time analogue of
`Submartingale.upcrossings_ae_lt_top`
(`Probability/Martingale/Convergence.lean:184`).

**Status — sorry-skeleton (Phase β retreat line, see file docstring).**

The proxy machinery (`reverseProxy`, `reverseFiltration`,
`reverseProxy_isMartingale`) lifts each finite window `[0, N]` of the backward
sequence to a forward Mathlib martingale, so that
`Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`
(`Probability/Martingale/Upcrossing.lean:690`) supplies a uniform-in-`N`
bound on the proxy's `upcrossingsBefore _ _ (proxy N) N`. The single missing
ingredient to translate this back to `upcrossings _ _ (n ↦ f (toDual n))` is a
**path-reversal inequality** of the form

```
upcrossingsBefore a b (n ↦ f (toDual n)) N ω
  ≤ upcrossingsBefore a b (reverseProxy N f) N ω + 1.
```

Mathlib does not currently provide this combinatorial identity, and a hand
derivation would unfold `upperCrossingTime` / `lowerCrossingTime` recursively
(Mathlib `Probability/Martingale/Upcrossing.lean:142, 152`) — a Mathlib-PR-sized
effort outside Phase β's scope. Pending that, β.2 is recorded as a statement
and Phase γ proceeds against it as a hypothesis. -/
theorem BackwardMartingale.upcrossings_ae_lt_top
    [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ)
    (hf_int : Integrable (f (OrderDual.toDual 0)) μ)
    (a b : ℝ) (_hab : a < b) :
    ∀ᵐ ω ∂μ,
      MeasureTheory.upcrossings a b (fun n : ℕ => f (OrderDual.toDual n)) ω < ∞ := by
  -- Retreat-line statement; see comment above.
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
`liminf = limsup` argument (`tendsto_of_uncrossing_lt_top`,
`Probability/Martingale/Convergence.lean:142`) and a measurable-limit existence
construction analogous to Mathlib's `tendsto_of_uncrossing_lt_top` +
`aemeasurable_of_tendsto_metrizable_ae'`
(`MeasureTheory/Constructions/BorelSpace/Metrizable.lean:79`). All ingredients
chain off β.2; see the retreat note there. Phase γ
(`BirkhoffErgodic.lean`) uses this statement as a hypothesis. -/
theorem BackwardMartingale.ae_tendsto
    [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ)
    (hf_int : Integrable (f (OrderDual.toDual 0)) μ) :
    ∃ g : Ω → ℝ,
      StronglyMeasurable[⨅ n : ℕ, ℋ (OrderDual.toDual n)] g ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (OrderDual.toDual n) ω)
          atTop (𝓝 (g ω)) := by
  -- Retreat-line statement; see comment above.
  sorry

end MainTheorem

end InformationTheory.Shannon
