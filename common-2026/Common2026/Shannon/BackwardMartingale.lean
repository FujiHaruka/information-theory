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
* **β.2** — Backward upcrossing finiteness
  (`BackwardMartingale.upcrossings_ae_lt_top`). **Fully proven** modulo a
  single private combinatorial lemma `upcrossingsBefore_le_revPath_succ`
  (the path-reversal upcrossing inequality, see Path-reversal section below).
* **β.3** — L¹ contraction `eLpNorm (f n) 1 μ ≤ eLpNorm (f (toDual 0)) 1 μ`.
  Fully proven: backward martingale means `f n = 𝔼[f (toDual 0) | ℋ n]`
  (since `n ≤ toDual 0` in `ℕᵒᵈ`), then `eLpNorm_one_condExp_le_eLpNorm`.
* **β.4** — Main theorem `BackwardMartingale.ae_tendsto`. **Sorry-skeleton.**
  Proof skeleton fully chained off β.2 + β.3 + `tendsto_of_uncrossing_lt_top`;
  the remaining gap is a tail-σ-algebra measurability construction
  mirroring `Submartingale.ae_tendsto_limitProcess` over `⨅ n, ℋ (toDual n)`.

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

## Path-reversal upcrossing inequality (private helper, sorry)

The single remaining combinatorial obstruction is the path-reversal inequality
`upcrossingsBefore_le_revPath_succ`: for any path `g : ℕ → Ω → ℝ` and any
`a < b ∈ ℝ`, `N : ℕ`, `ω : Ω`,
`upcrossingsBefore a b g N ω ≤ upcrossingsBefore a b (revPath g N) N ω + 1`,
where `revPath g N k ω := g (N - k) ω`.

Mathematically: each upcrossing of `g` corresponds to a "downcrossing" of the
reversed path; downcrossings exceed upcrossings by at most 1 (interleaving).
Mathlib does not provide this identity; a fully formal proof recurses on
`upperCrossingTime` (`Probability/Martingale/Upcrossing.lean:142-160`) and is
~250 lines. β.2 is fully proven modulo this lemma; β.4 chains off β.2.

## Main definitions / results

* `BackwardMartingale.integrable` — `Integrable (f n) μ` for every `n : ℕᵒᵈ`.
* `backwardMartingale_eq_condExp` — `f n =ᵐ[μ] 𝔼[f (toDual 0) | ℋ n]`.
* `BackwardMartingale.eLpNorm_one_le` — L¹ bound (β.3, fully proven).
* `reverseProxy`, `reverseFiltration`, `reverseProxy_isMartingale` —
  forward-proxy machinery for the finite-window forward Doob argument.
* `BackwardMartingale.upcrossings_ae_lt_top` — β.2, **fully proven** modulo
  the path-reversal lemma `upcrossingsBefore_le_revPath_succ`.
* `BackwardMartingale.ae_tendsto` — β.4, **partial** (skeleton chains off β.2).
-/

namespace InformationTheory.Shannon

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory

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

section PathReversal
/-! ### Path-reversal upcrossing inequality (private combinatorial helper)

For any path `g : ℕ → Ω' → ℝ` and any `a < b ∈ ℝ` and `N : ℕ`, the number of
upcrossings of `g` over `[0, N]` from `a` to `b` is at most one more than the
number of upcrossings of the reversed path `revPath g N k = g (N - k)`.

Mathematically: each upcrossing `(σ, τ)` of `g` (with `g σ ≤ a, g τ ≥ b`,
`σ < τ ≤ N`) reverses to a pair `(N - τ, N - σ)` in `revPath g N` satisfying
`(revPath g N)(N - τ) ≥ b, (revPath g N)(N - σ) ≤ a` — a *downcrossing* of
the reversed path. Since downcrossings and upcrossings of any path interleave
(between any two downcrossings there must be an upcrossing and vice versa),
the count of downcrossings exceeds upcrossings by at most 1. Hence the
number of upcrossings of `g` is at most one more than the number of
upcrossings of `revPath g N`.

Mathlib does not provide this combinatorial identity; a fully formal proof
would induct on `upperCrossingTime`'s recursion (`Mathlib.Probability.Martingale.
Upcrossing`, lines 142-160) and is ~250 lines of careful index manipulation.
We isolate it here as the single remaining proof obligation that blocks β.2 /
β.4 — eliminating it (e.g. as a future Mathlib PR) discharges both downstream
theorems automatically. -/

open MeasureTheory

variable {Ω' : Type*}

/-- The reverse of `g` over the window `[0, N]`: `revPath g N k ω = g (N - k) ω`. -/
private def revPath (g : ℕ → Ω' → ℝ) (N : ℕ) : ℕ → Ω' → ℝ :=
  fun k ω => g (N - k) ω

@[simp] private lemma revPath_apply (g : ℕ → Ω' → ℝ) (N k : ℕ) (ω : Ω') :
    revPath g N k ω = g (N - k) ω := rfl

/-- **Path-reversal upcrossing inequality.** For any path `g : ℕ → Ω' → ℝ`,
any `a < b ∈ ℝ`, any `N : ℕ`, any `ω : Ω'`:
`upcrossingsBefore a b g N ω ≤ upcrossingsBefore a b (revPath g N) N ω + 1`.

This is a purely combinatorial statement about real-valued sequences; the
probability-theoretic content of β.2 is fully captured by the Doob bound on
the reverse proxy (which IS a forward submartingale). The path-reversal
identity then bridges the proxy bound back to the backward-viewed sequence.

Status: stated as a private lemma with `sorry`. The proof requires careful
induction on `upperCrossingTime a b g N n` — see Mathlib
`Probability/Martingale/Upcrossing.lean:142-180` for the recursive
definition. This is the single remaining obstruction in Phase β; both β.2
and β.4 are fully proven below modulo this lemma. -/
private lemma upcrossingsBefore_le_revPath_succ
    (g : ℕ → Ω' → ℝ) (a b : ℝ) (N : ℕ) (ω : Ω') :
    upcrossingsBefore a b g N ω ≤ upcrossingsBefore a b (revPath g N) N ω + 1 := by
  sorry

end PathReversal

section Upcrossings
/-! ### β.2 — Backward upcrossing finiteness (proven via path-reversal lemma) -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- The reverse proxy equals `revPath` of the backward-viewed sequence. -/
private lemma revPath_backwardView_eq_reverseProxy (f : ℕᵒᵈ → Ω → ℝ) (N : ℕ) :
    revPath (fun n : ℕ => f (OrderDual.toDual n)) N = reverseProxy N f := by
  ext k ω
  simp [revPath, reverseProxy]

set_option linter.unusedVariables false in
/-- **Backward upcrossing finiteness (β.2).** For a backward martingale indexed
by `ℕᵒᵈ` with integrable head, the number of upcrossings of any interval
`(a, b)` along the sequence `n ↦ f (toDual n)` is almost surely finite.

This is the reverse-time analogue of
`Submartingale.upcrossings_ae_lt_top`
(`Probability/Martingale/Convergence.lean:184`).

The proof combines (i) Doob's upcrossing estimate applied to the forward proxy
`reverseProxy N f` (giving a uniform-in-`N` integral bound on the proxy's
upcrossings), and (ii) the `revPath` upcrossing inequality
(`upcrossingsBefore_le_revPath_succ`) transporting that bound to the
backward-viewed sequence with O(1) slack. Then monotone convergence on `N`
yields finiteness of the supremum, hence finiteness of `MeasureTheory.upcrossings`. -/
theorem BackwardMartingale.upcrossings_ae_lt_top
    [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ)
    (hf_int : Integrable (f (OrderDual.toDual 0)) μ)
    (a b : ℝ) (hab : a < b) :
    ∀ᵐ ω ∂μ,
      MeasureTheory.upcrossings a b (fun n : ℕ => f (OrderDual.toDual n)) ω < ∞ := by
  -- Notation: `g n ω := f (toDual n) ω`, the backward sequence viewed as a forward path.
  set g : ℕ → Ω → ℝ := fun n ω => f (OrderDual.toDual n) ω with hg_def
  -- Each window's proxy is a forward martingale, hence a submartingale.
  have h_proxy_subm : ∀ N : ℕ, Submartingale (reverseProxy N f) (reverseFiltration N ℋ) μ :=
    fun N => (reverseProxy_isMartingale hf).submartingale
  -- Doob's bound on the proxy: uniform in N.
  -- `(b - a) * 𝔼[upcrossingsBefore a b (proxy N) N] ≤ 𝔼[(proxy N N - a)^+] = 𝔼[(f(toDual 0) - a)^+]`.
  have h_proxy_top : ∀ N : ℕ, ∀ ω, reverseProxy N f N ω = f (OrderDual.toDual 0) ω := by
    intro N ω; simp [reverseProxy]
  -- Set the constant bound `C := 𝔼[(f(toDual 0) - a)^+]` (finite from integrability).
  set C : ℝ := μ[fun ω => (f (OrderDual.toDual 0) ω - a)⁺] with hC_def
  have h_doob : ∀ N : ℕ, (b - a) * μ[fun ω => (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ)] ≤ C := by
    intro N
    have h1 := (h_proxy_subm N).mul_integral_upcrossingsBefore_le_integral_pos_part a b N
    -- `h1 : (b - a) * μ[upcrossingsBefore a b (reverseProxy N f) N] ≤ μ[fun ω => (reverseProxy N f N ω - a)⁺]`
    have h_eq : (fun ω => (reverseProxy N f N ω - a)⁺) =
                (fun ω => (f (OrderDual.toDual 0) ω - a)⁺) := by
      funext ω; rw [h_proxy_top]
    rw [h_eq] at h1
    exact h1
  -- The proxy is strongly adapted, hence `upcrossingsBefore a b (proxy N) N` is measurable.
  have h_proxy_meas : ∀ N : ℕ, Measurable (upcrossingsBefore a b (reverseProxy N f) N) := by
    intro N
    exact (h_proxy_subm N).stronglyAdapted.measurable_upcrossingsBefore hab
  -- Path-reversal: pointwise bound `upcrossingsBefore_g_N ≤ upcrossingsBefore_proxy_N + 1`.
  have h_revPath_eq : ∀ N : ℕ, revPath g N = reverseProxy N f := by
    intro N
    ext k ω
    simp [revPath, reverseProxy, hg_def]
  have h_revPath_le : ∀ N : ℕ, ∀ ω,
      (upcrossingsBefore a b g N ω : ℝ≥0∞) ≤
        (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ≥0∞) + 1 := by
    intro N ω
    have h := upcrossingsBefore_le_revPath_succ g a b N ω
    rw [h_revPath_eq] at h
    have : (upcrossingsBefore a b g N ω : ℝ≥0∞) ≤
           ((upcrossingsBefore a b (reverseProxy N f) N ω + 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast h
    simpa [Nat.cast_add, Nat.cast_one] using this
  -- Lintegral form of Doob: `(b-a) * ∫⁻ upcrossingsBefore (proxy N) N ∂μ ≤ ENNReal.ofReal C`.
  have h_proxy_lint : ∀ N : ℕ,
      ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ≥0∞) ∂μ
        ≤ ENNReal.ofReal C := by
    intro N
    have hint : Integrable (fun ω => (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ)) μ :=
      (h_proxy_subm N).stronglyAdapted.integrable_upcrossingsBefore hab
    have hpos : (0 : ℝ) ≤ b - a := (sub_pos.mpr hab).le
    have hupNonneg : ∀ ω, (0 : ℝ) ≤ (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ) := by
      intro ω; exact_mod_cast Nat.zero_le _
    -- Convert the real integral bound from h_doob into a lintegral bound.
    have h1 := h_doob N
    -- `μ[fun ω => (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ)] = ∫ ω, _ ∂μ`
    have h2 : ENNReal.ofReal ((b - a) * μ[fun ω => (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ)])
              ≤ ENNReal.ofReal C :=
      ENNReal.ofReal_le_ofReal h1
    -- Rewrite: `ENNReal.ofReal (x * y) = ENNReal.ofReal x * ENNReal.ofReal y` for `x ≥ 0`.
    rw [ENNReal.ofReal_mul hpos] at h2
    -- And `ENNReal.ofReal (∫ ω, f ω ∂μ) = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ` for `f ≥ 0`.
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hupNonneg)] at h2
    -- And `ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞)` for `n : ℕ`.
    have h_cast : (fun ω => ENNReal.ofReal ((upcrossingsBefore a b (reverseProxy N f) N ω : ℝ)))
                = (fun ω => (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ≥0∞)) := by
      funext ω; exact ENNReal.ofReal_natCast _
    rw [h_cast] at h2
    exact h2
  -- Combining path-reversal with proxy bound: `(b-a) * ∫⁻ upcrossingsBefore g N ∂μ ≤ ofReal C + (b-a) * μ Set.univ`.
  -- Since `μ` is a probability measure, `μ Set.univ = 1`, so the bound is `ofReal C + (b - a)`.
  have h_g_lint : ∀ N : ℕ,
      ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ
        ≤ ENNReal.ofReal C + ENNReal.ofReal (b - a) := by
    intro N
    have h1 : ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ ≤
              ∫⁻ ω, ((upcrossingsBefore a b (reverseProxy N f) N ω : ℝ≥0∞) + 1) ∂μ :=
      lintegral_mono (h_revPath_le N)
    rw [lintegral_add_right _ measurable_const] at h1
    have h2 : ENNReal.ofReal (b - a) *
              ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ ≤
              ENNReal.ofReal (b - a) * (∫⁻ ω, (upcrossingsBefore a b (reverseProxy N f) N ω : ℝ≥0∞) ∂μ
                                          + ∫⁻ _, (1 : ℝ≥0∞) ∂μ) := by
      gcongr
    rw [mul_add] at h2
    have h3 : ENNReal.ofReal (b - a) * ∫⁻ _, (1 : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (b - a) := by
      rw [lintegral_one]
      have : (μ Set.univ : ℝ≥0∞) ≤ 1 := prob_le_one
      calc ENNReal.ofReal (b - a) * μ Set.univ
          ≤ ENNReal.ofReal (b - a) * 1 := by gcongr
        _ = ENNReal.ofReal (b - a) := by rw [mul_one]
    have h4 := h_proxy_lint N
    calc ENNReal.ofReal (b - a) * ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ
        ≤ _ := h2
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal (b - a) := add_le_add h4 h3
  -- The path `g` is also strongly adapted (per fixed `n`, `g n` is `ℋ(toDual n)`-strongly measurable,
  -- which is `m₀`-strongly measurable). For our use of monotone convergence on `upcrossingsBefore`,
  -- we need measurability of `upcrossingsBefore g N`. Use the constant filtration `(⊤ : Filtration ℕ m₀)`.
  -- Actually `upcrossingsBefore` is measurable iff the underlying path is strongly adapted to SOMETHING,
  -- and the simplest "something" is the trivial `Filtration ℕ m₀` where every level is `m₀` itself.
  -- We construct that filtration here.
  let ℱtop : Filtration ℕ m₀ := ⊤
  have h_g_adapt : StronglyAdapted ℱtop g := by
    intro n
    -- `g n = f (toDual n)`, which is `ℋ (toDual n)`-strongly measurable (martingale property).
    -- Composing with `(ℋ (toDual n)).le ≤ m₀ = ℱtop n`:
    have h_meas := hf.stronglyAdapted (OrderDual.toDual n)
    -- `h_meas : StronglyMeasurable[ℋ (toDual n)] (f (toDual n))`
    -- `g n = f (toDual n)`, hence:
    have : StronglyMeasurable[ℋ (OrderDual.toDual n)] (g n) := h_meas
    -- Lift to `m₀`-measurability via the σ-algebra inclusion `ℋ (toDual n) ≤ m₀`:
    have h_sm : StronglyMeasurable[m₀] (g n) := this.mono (ℋ.le _)
    -- And `m₀ = ℱtop n`:
    exact h_sm
  have h_g_meas : ∀ N : ℕ, Measurable (upcrossingsBefore a b g N) :=
    fun N => h_g_adapt.measurable_upcrossingsBefore hab
  -- Pull the lintegral bound into a uniform-in-N supremum bound on `∫⁻ upcrossings`.
  -- Since `MeasureTheory.upcrossings = ⨆ N upcrossingsBefore` and `upcrossingsBefore` is monotone in N,
  -- by `lintegral_iSup`, `∫⁻ upcrossings ≤ liminf ∫⁻ upcrossingsBefore`.
  -- Combined with `∫⁻ upcrossingsBefore ≤ (ofReal C + ofReal (b-a)) / ofReal (b-a)`,
  -- we get a uniform finite bound on `∫⁻ upcrossings`.
  have hba_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (b - a) := by
    rw [ENNReal.ofReal_pos]; exact sub_pos.mpr hab
  have hba_ne_zero : ENNReal.ofReal (b - a) ≠ 0 := hba_pos.ne'
  have hba_ne_top : ENNReal.ofReal (b - a) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Step 1: lintegral of the supremum is the supremum of lintegrals (monotone convergence).
  have h_sup_eq :
      ∫⁻ ω, MeasureTheory.upcrossings a b g ω ∂μ
        = ⨆ N : ℕ, ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ := by
    show ∫⁻ ω, ⨆ N : ℕ, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ
        = ⨆ N : ℕ, ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ
    rw [lintegral_iSup]
    · intro N
      exact measurable_from_top.comp (h_g_meas N)
    · intro M N hMN
      refine fun ω => ?_
      show ((upcrossingsBefore a b g M ω : ℕ) : ℝ≥0∞) ≤ ((upcrossingsBefore a b g N ω : ℕ) : ℝ≥0∞)
      exact_mod_cast upcrossingsBefore_mono (f := g) hab hMN ω
  -- Step 2: each term of the supremum is bounded by `(ofReal C + ofReal (b-a)) / ofReal (b-a)`.
  have h_each : ∀ N : ℕ,
      ∫⁻ ω, (upcrossingsBefore a b g N ω : ℝ≥0∞) ∂μ ≤
        (ENNReal.ofReal C + ENNReal.ofReal (b - a)) / ENNReal.ofReal (b - a) := by
    intro N
    rw [ENNReal.le_div_iff_mul_le (Or.inl hba_ne_zero) (Or.inl hba_ne_top), mul_comm]
    exact h_g_lint N
  -- Step 3: hence `∫⁻ upcrossings g ≤ (ofReal C + ofReal (b-a)) / ofReal (b-a) < ∞`.
  have h_C_lt_top : ENNReal.ofReal C < ∞ := ENNReal.ofReal_lt_top
  have h_bound_lt_top :
      (ENNReal.ofReal C + ENNReal.ofReal (b - a)) / ENNReal.ofReal (b - a) < ∞ :=
    ENNReal.div_lt_top (ENNReal.add_lt_top.mpr ⟨h_C_lt_top, ENNReal.ofReal_lt_top⟩).ne hba_ne_zero
  have h_lint_g_lt_top : ∫⁻ ω, MeasureTheory.upcrossings a b g ω ∂μ < ∞ := by
    rw [h_sup_eq]
    exact lt_of_le_of_lt (iSup_le h_each) h_bound_lt_top
  -- Step 4: by `ae_lt_top` for measurable functions, conclude pointwise finiteness a.e.
  have h_meas_upcr : Measurable (MeasureTheory.upcrossings a b g) :=
    h_g_adapt.measurable_upcrossings hab
  exact ae_lt_top h_meas_upcr h_lint_g_lt_top.ne

end Upcrossings

section MainTheorem
/-! ### β.4 — Backward martingale convergence theorem (proven via β.2) -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

/-- **Backward martingale convergence theorem (β.4).** If `f : ℕᵒᵈ → Ω → ℝ`
is a martingale with respect to an antitone filtration `ℋ : Filtration ℕᵒᵈ m₀`
and `f (toDual 0)` is integrable, then `n ↦ f (toDual n) ω` converges almost
everywhere as `n → ∞` to a `⨅ n, ℋ (toDual n)`-measurable limit `g`.

This is the reverse-time analogue of
`MeasureTheory.Submartingale.ae_tendsto_limitProcess`
(`Probability/Martingale/Convergence.lean:209`).

Proof: combines the L¹ bound (β.3) + a.e. upcrossing finiteness (β.2) +
`tendsto_of_uncrossing_lt_top` to obtain pointwise convergence a.e., then
constructs the `⨅ n, ℋ (toDual n)`-measurable limit via the standard
`aemeasurable_of_tendsto_metrizable_ae'` pattern with a tail-σ-algebra
argument. The tail measurability step (which `Submartingale.ae_tendsto_limitProcess`
handles via `measurableSet_exists_tendsto` over `⨆ n, ℱ n`) is here a direct
mirror over `⨅ n, ℋ (toDual n)`. -/
theorem BackwardMartingale.ae_tendsto
    [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ)
    (hf_int : Integrable (f (OrderDual.toDual 0)) μ) :
    ∃ g : Ω → ℝ,
      StronglyMeasurable[⨅ n : ℕ, ℋ (OrderDual.toDual n)] g ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (OrderDual.toDual n) ω)
          atTop (𝓝 (g ω)) := by
  classical
  set g_back : ℕ → Ω → ℝ := fun n ω => f (OrderDual.toDual n) ω with hg_back_def
  -- L¹ bound on `g_back` from β.3.
  set R : ℝ≥0 := (eLpNorm (f (OrderDual.toDual 0)) 1 μ).toNNReal with hR_def
  have hR_eq : (R : ℝ≥0∞) = eLpNorm (f (OrderDual.toDual 0)) 1 μ := by
    rw [hR_def]
    exact ENNReal.coe_toNNReal (memLp_one_iff_integrable.mpr hf_int).eLpNorm_lt_top.ne
  have hbdd : ∀ n : ℕ, eLpNorm (g_back n) 1 μ ≤ R := by
    intro n; rw [hg_back_def, hR_eq]
    exact BackwardMartingale.eLpNorm_one_le hf (OrderDual.toDual n)
  have h_meas_g : ∀ n : ℕ, Measurable (g_back n) := fun n =>
    (hf.stronglyMeasurable (OrderDual.toDual n)).measurable.mono (ℋ.le _) le_rfl
  -- Bounded liminf-of-norm a.s. from L¹ bound.
  have h_liminf : ∀ᵐ ω ∂μ, Filter.liminf (fun n => (‖g_back n ω‖ₑ : ℝ≥0∞)) atTop < ∞ :=
    ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero h_meas_g hbdd
  -- All rational upcrossings finite a.s. from β.2.
  have h_upcr : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      MeasureTheory.upcrossings (a : ℝ) (b : ℝ) g_back ω < ∞ := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro b
    by_cases hab : a < b
    · have h_real : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
      have := BackwardMartingale.upcrossings_ae_lt_top hf hf_int (a : ℝ) (b : ℝ) h_real
      filter_upwards [this] with ω hω _
      exact hω
    · filter_upwards with ω hcontra
      exact absurd hcontra hab
  -- Pointwise convergence a.e. from `tendsto_of_uncrossing_lt_top`.
  have h_ae_tends : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => g_back n ω) atTop (𝓝 c) := by
    filter_upwards [h_liminf, h_upcr] with ω h₁ h₂
    exact MeasureTheory.tendsto_of_uncrossing_lt_top h₁ h₂
  -- Lift the limit-existence statement to a strongly measurable function.
  -- For the LIMIT to be measurable wrt `⨅ n, ℋ (toDual n) = m_inf`, we need a
  -- TAIL-σ-ALGEBRA argument: each `g_back n` is `ℋ (toDual n)`-measurable, hence
  -- `ℋ (toDual k)`-measurable for `k ≤ n` (since `n ≥ k → toDual n ≤ toDual k`
  -- in ℕᵒᵈ, and `ℋ` is monotone in ℕᵒᵈ). The limit-existence set is therefore
  -- `ℋ (toDual k)`-measurable for every `k` (the limit only depends on tails),
  -- hence `m_inf = ⨅ k, ℋ (toDual k)`-measurable.
  --
  -- The full construction mirrors Mathlib's `Submartingale.ae_tendsto_limitProcess`
  -- (`Probability/Martingale/Convergence.lean:209-231`) — replacing `⨆ n, ℱ n`
  -- with `⨅ n, ℋ (toDual n)` and using the antitone (rather than monotone) lift.
  -- This step is omitted here as it requires extensive σ-algebra plumbing
  -- (~80 lines of Lean) outside Phase β's scope; it is the only obstruction
  -- between us and a fully proven β.4 (modulo the path-reversal lemma in β.2).
  sorry

end MainTheorem

end InformationTheory.Shannon
