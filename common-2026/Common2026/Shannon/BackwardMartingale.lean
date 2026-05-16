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
  (`BackwardMartingale.upcrossings_ae_lt_top`). **Fully proven**, including
  the path-reversal combinatorial lemma `upcrossingsBefore_le_revPath_succ`
  (see Path-reversal section below).
* **β.3** — L¹ contraction `eLpNorm (f n) 1 μ ≤ eLpNorm (f (toDual 0)) 1 μ`.
  Fully proven: backward martingale means `f n = 𝔼[f (toDual 0) | ℋ n]`
  (since `n ≤ toDual 0` in `ℕᵒᵈ`), then `eLpNorm_one_condExp_le_eLpNorm`.
* **β.4** — Main theorem `BackwardMartingale.ae_tendsto`. **Fully proven**,
  chaining off β.2 + β.3 + `tendsto_of_uncrossing_lt_top`, with the
  tail-σ-algebra measurability handled via `Filter.limsup_nat_add` tail
  invariance over `⨅ n, ℋ (toDual n)`.

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

## Path-reversal upcrossing inequality (private helper)

The path-reversal inequality `upcrossingsBefore_le_revPath_succ`: for any path
`g : ℕ → Ω → ℝ` and any `a < b ∈ ℝ`, `N : ℕ`, `ω : Ω`,
`upcrossingsBefore a b g N ω ≤ upcrossingsBefore a b (revPath g N) N ω + 1`,
where `revPath g N k ω := g (N - k) ω`.

Mathematically: each upcrossing of `g` corresponds to a "downcrossing" of the
reversed path; downcrossings exceed upcrossings by at most 1 (interleaving).
The formal proof avoids defining a separate `downcrossingsBefore`; instead it
goes via a witness-chain characterization (`upperCrossingTime_le_of_witness`),
extracts the `n` Mathlib upcrossing witnesses for `g`, reverses indices to
obtain `n - 1` upcrossing witnesses for `revPath g N`, and translates back via
`le_csSup`. The boundary case `τ_0 ≥ 1` is handled by `upperCrossingTime_one_pos`.

## Main definitions / results

* `BackwardMartingale.integrable` — `Integrable (f n) μ` for every `n : ℕᵒᵈ`.
* `backwardMartingale_eq_condExp` — `f n =ᵐ[μ] 𝔼[f (toDual 0) | ℋ n]`.
* `BackwardMartingale.eLpNorm_one_le` — L¹ bound (β.3, fully proven).
* `reverseProxy`, `reverseFiltration`, `reverseProxy_isMartingale` —
  forward-proxy machinery for the finite-window forward Doob argument.
* `BackwardMartingale.upcrossings_ae_lt_top` — β.2, **fully proven**.
* `BackwardMartingale.ae_tendsto` — β.4, **fully proven**.
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

Mathlib does not provide this combinatorial identity. Our proof factors through
two private helpers:

* `upperCrossingTime_le_of_witness` — from `k` strictly-alternating upcrossing
  witnesses `(s_i, t_i)` strictly inside `[0, N)`, conclude
  `upperCrossingTime a b g N k ω ≤ t_{k-1}`. Induction on `k` using the
  recursive form of `upperCrossingTime` and `hittingBtwn_le_of_mem`.
* `upperCrossingTime_one_pos` — when `0 < upcrossings`, the first upper
  crossing time `upperCrossingTime _ _ g N 1 ω ≥ 1`. (If it were `0`, then
  `g 0 ω ≥ b` and also `g 0 ω ≤ a`, contradicting `a < b`.)

Combining them in `upcrossingsBefore_revPath_ge`: extract the `n = k + 1`
Mathlib upcrossing witnesses for `g`, reverse them via `t' i := N -
upperCrossingTime _ _ g N (k - i) ω`, `s' i := N - lowerCrossingTime _ _ g N
(k - i) ω`, apply `upperCrossingTime_le_of_witness` to `revPath g N`, then
conclude via `le_csSup` and `upperCrossingTime_lt_bddAbove`. Total proof
~250 lines including helpers. -/

open MeasureTheory

variable {Ω' : Type*}

/-- The reverse of `g` over the window `[0, N]`: `revPath g N k ω = g (N - k) ω`. -/
private def revPath (g : ℕ → Ω' → ℝ) (N : ℕ) : ℕ → Ω' → ℝ :=
  fun k ω => g (N - k) ω

@[simp] private lemma revPath_apply (g : ℕ → Ω' → ℝ) (N k : ℕ) (ω : Ω') :
    revPath g N k ω = g (N - k) ω := rfl

/-- Witness-extraction (induction step): from `k` upcrossing pairs of `g` strictly
inside `[0, N)`, with the alternating ordering, conclude
`upperCrossingTime a b g N k ω ≤ t_{k-1} < N`, hence `k ≤ upcrossingsBefore a b g N ω`. -/
private lemma upperCrossingTime_le_of_witness {a b : ℝ}
    (g : ℕ → Ω' → ℝ) (N : ℕ) (ω : Ω')
    (s t : ℕ → ℕ) (k : ℕ)
    (hs_lt_t : ∀ i < k, s i < t i)
    (ht_le_s : ∀ i, i + 1 < k → t i ≤ s (i + 1))
    (ht_lt_N : ∀ i < k, t i < N)
    (hgs : ∀ i < k, g (s i) ω ≤ a)
    (hgt : ∀ i < k, b ≤ g (t i) ω) :
    upperCrossingTime a b g N k ω ≤ if k = 0 then 0 else t (k - 1) := by
  induction k with
  | zero => simp [upperCrossingTime_zero]
  | succ k ih =>
    -- Specialize ih to bounds for indices `< k`.
    have hs_lt_t' : ∀ i < k, s i < t i := fun i hi => hs_lt_t i (hi.trans (Nat.lt_succ_self _))
    have ht_le_s' : ∀ i, i + 1 < k → t i ≤ s (i + 1) :=
      fun i hi => ht_le_s i (hi.trans (Nat.lt_succ_self _))
    have ht_lt_N' : ∀ i < k, t i < N := fun i hi => ht_lt_N i (hi.trans (Nat.lt_succ_self _))
    have hgs' : ∀ i < k, g (s i) ω ≤ a := fun i hi => hgs i (hi.trans (Nat.lt_succ_self _))
    have hgt' : ∀ i < k, b ≤ g (t i) ω := fun i hi => hgt i (hi.trans (Nat.lt_succ_self _))
    have ih' := ih hs_lt_t' ht_le_s' ht_lt_N' hgs' hgt'
    -- Goal: `upperCrossingTime a b g N (k+1) ω ≤ t k`
    simp only [Nat.succ_sub_one, if_neg (Nat.succ_ne_zero _)]
    -- The recursion: `upperCrossingTime (k+1) ω = hittingBtwn g (Ici b) lowerAux N ω`
    -- where `lowerAux = lowerCrossingTimeAux a g (upperCrossingTime k ω) N ω
    --              = hittingBtwn g (Iic a) (upperCrossingTime k ω) N ω`.
    rw [upperCrossingTime_succ]
    unfold lowerCrossingTimeAux
    -- We need: `hittingBtwn g (Ici b) (hittingBtwn g (Iic a) (upperCrossingTime k ω) N ω) N ω ≤ t k`
    -- Use `hittingBtwn_le_of_mem` (the outer hit ≤ t k since g (t k) ∈ Ici b and t k is reachable).
    -- First, bound the inner `lowerAux` ≤ s k.
    have h_inner_le_sk : hittingBtwn g (Set.Iic a) (upperCrossingTime a b g N k ω) N ω ≤ s k := by
      -- `upperCrossingTime k ω ≤ (if k = 0 then 0 else t (k-1)) ≤ s k`.
      have h_upper_le : upperCrossingTime a b g N k ω ≤ s k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
        · subst hk0
          simp [upperCrossingTime_zero]
        · have := ih'
          simp only [if_neg hk_pos.ne', Nat.sub_one] at this
          calc upperCrossingTime a b g N k ω
              ≤ t (k - 1) := this
            _ ≤ s k := by
              have : k - 1 + 1 < k + 1 := by omega
              have h := ht_le_s (k - 1) (by omega : k - 1 + 1 < k + 1)
              rwa [Nat.sub_add_cancel hk_pos] at h
      -- `g (s k) ω ∈ Iic a`, `s k ∈ Icc (upperCrossingTime k ω) N`
      have hsk_le_N : s k ≤ N := (hs_lt_t k (Nat.lt_succ_self _)).le.trans
        (ht_lt_N k (Nat.lt_succ_self _)).le
      have hgsk : g (s k) ω ∈ Set.Iic a := hgs k (Nat.lt_succ_self _)
      exact hittingBtwn_le_of_mem h_upper_le hsk_le_N hgsk
    -- Now bound the outer hit by t k.
    have h_outer_le_tk : hittingBtwn g (Set.Ici b)
        (hittingBtwn g (Set.Iic a) (upperCrossingTime a b g N k ω) N ω) N ω ≤ t k := by
      have htk_le_N : t k ≤ N := (ht_lt_N k (Nat.lt_succ_self _)).le
      have hgtk : g (t k) ω ∈ Set.Ici b := hgt k (Nat.lt_succ_self _)
      have h_inner_le_tk : hittingBtwn g (Set.Iic a) (upperCrossingTime a b g N k ω) N ω ≤ t k :=
        h_inner_le_sk.trans (hs_lt_t k (Nat.lt_succ_self _)).le
      exact hittingBtwn_le_of_mem h_inner_le_tk htk_le_N hgtk
    exact h_outer_le_tk

/-- Helper: when `n ≥ 1` upcrossings exist and `hab : a < b`, the first upper crossing time
`upperCrossingTime a b g N 1 ω` is strictly positive. (If it were `0`, then `g 0 ω ≥ b` and
also `g 0 ω ≤ a` from the lower crossing being at `0` too, contradicting `a < b`.) -/
private lemma upperCrossingTime_one_pos {a b : ℝ} (hab : a < b)
    (g : ℕ → Ω' → ℝ) (N : ℕ) (ω : Ω')
    (h_pos : 0 < upcrossingsBefore a b g N ω) :
    0 < upperCrossingTime a b g N 1 ω := by
  -- Suppose `upperCrossingTime a b g N 1 ω = 0`. Then `g 0 ω ∈ Ici b`, i.e., `b ≤ g 0 ω`.
  -- Also `lowerCrossingTime a b g N 0 ω = 0` (the lower crossing chain starts at 0 and
  -- `lowerCrossingTimeAux a g 0 N` ≤ `upperCrossingTime 1` = 0). With `g 0 ω ≤ a`
  -- (since `lowerCrossingTime 0 ≠ N` from `0 < n ≤ upcrossings`), we get `b ≤ g 0 ω ≤ a`, ⊥.
  by_contra h
  push Not at h
  have h_eq : upperCrossingTime a b g N 1 ω = 0 := Nat.le_zero.mp h
  -- The recursive form: `upperCrossingTime 1 ω = hittingBtwn g (Ici b) (lowerCrossingTimeAux a g 0 N) N ω`.
  -- And `lowerCrossingTime a b g N 0 ω = hittingBtwn g (Iic a) 0 N ω`.
  -- Note `lowerCrossingTimeAux a g 0 N ω = lowerCrossingTime a b g N 0 ω`.
  have h_low_eq : lowerCrossingTimeAux a g (upperCrossingTime a b g N 0 ω) N ω
                = lowerCrossingTime a b g N 0 ω := by
    simp [lowerCrossingTimeAux, lowerCrossingTime, upperCrossingTime_zero]
  have h_upper_succ : upperCrossingTime a b g N 1 ω
                    = hittingBtwn g (Set.Ici b) (lowerCrossingTime a b g N 0 ω) N ω := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, upperCrossingTime_succ, h_low_eq]
  rw [h_upper_succ] at h_eq
  -- From `0 < upcrossings`, `lowerCrossingTime 0 < N`.
  have h_low0_lt_N : lowerCrossingTime a b g N 0 ω < N :=
    lowerCrossingTime_lt_of_lt_upcrossingsBefore (zero_lt_iff.mpr (by
      intro hN0
      simp [hN0, upcrossingsBefore_zero] at h_pos)) hab h_pos
  have h_low0_ne_N : lowerCrossingTime a b g N 0 ω ≠ N := h_low0_lt_N.ne
  have h_g_low0 : g (lowerCrossingTime a b g N 0 ω) ω ≤ a := stoppedValue_lowerCrossingTime h_low0_ne_N
  -- From `hittingBtwn g (Ici b) (lowerCrossingTime 0) N ω = 0` and `lowerCrossingTime 0 ≤ 0`
  -- (since the hittingBtwn always has the start as a lower bound), we get `lowerCrossingTime 0 = 0`.
  have h_low0_zero : lowerCrossingTime a b g N 0 ω = 0 := by
    have h_le_start : lowerCrossingTime a b g N 0 ω ≤
        hittingBtwn g (Set.Ici b) (lowerCrossingTime a b g N 0 ω) N ω := by
      apply le_hittingBtwn
      exact h_low0_lt_N.le
    rw [h_eq] at h_le_start
    omega
  -- And `g 0 ω ∈ Ici b`, since `hittingBtwn _ _ _ _ ω = 0 < N` means the value at 0 is in Ici b.
  have h_g0_ge_b : b ≤ g 0 ω := by
    have h_zero_lt_N : (0 : ℕ) < N := by
      have := h_low0_lt_N
      omega
    -- The hit is at `0`, value `g 0 ω`. Since `0 < N`, `0` is in the Icc range, and the hit
    -- means we found `Ici b` there.
    have h_mem : g (hittingBtwn g (Set.Ici b) (lowerCrossingTime a b g N 0 ω) N ω) ω
        ∈ Set.Ici b := by
      apply hittingBtwn_mem_set_of_hittingBtwn_lt
      rw [h_eq]
      exact h_zero_lt_N
    rw [h_eq] at h_mem
    exact h_mem
  rw [h_low0_zero] at h_g_low0
  linarith

/-- Path reversal: from `k+1 ≤ upcrossings g`, extract `k` upcrossing pairs of
`revPath g N`. Combined with `upperCrossingTime_le_of_witness`, this yields
`k ≤ upcrossings (revPath g N) N`, hence the main bound. -/
private lemma upcrossingsBefore_revPath_ge {a b : ℝ} (hab : a < b)
    (g : ℕ → Ω' → ℝ) (N : ℕ) (ω : Ω') (k : ℕ)
    (hk : k + 1 ≤ upcrossingsBefore a b g N ω) :
    k ≤ upcrossingsBefore a b (revPath g N) N ω := by
  -- Notation: with `n := k + 1`, set:
  --   `σ_i := lowerCrossingTime a b g N i ω`  for i = 0, …, k = n - 1
  --   `τ_i := upperCrossingTime a b g N (i + 1) ω`  for i = 0, …, k
  -- These are the n upcrossing time witnesses. We construct k upcrossing witnesses
  -- (s', t') for `revPath g N` via index reversal.
  set n := k + 1 with hn_def
  -- N must be positive (otherwise `upcrossingsBefore` would be 0).
  have hN_pos : 0 < N := by
    by_contra hN
    push Not at hN
    interval_cases N
    simp [upcrossingsBefore_zero] at hk
  -- Each σ_i is < N for i ≤ k (since i < n ≤ upcrossings).
  have h_sig_lt_N : ∀ i ≤ k, lowerCrossingTime a b g N i ω < N := by
    intro i hi
    have : i < upcrossingsBefore a b g N ω := lt_of_le_of_lt hi (Nat.lt_of_succ_le hk)
    exact lowerCrossingTime_lt_of_lt_upcrossingsBefore hN_pos hab this
  -- Each τ_i is < N for i ≤ k (since i + 1 ≤ n ≤ upcrossings).
  have h_tau_lt_N : ∀ i ≤ k, upperCrossingTime a b g N (i + 1) ω < N := by
    intro i hi
    have : i + 1 ≤ upcrossingsBefore a b g N ω := Nat.succ_le_of_lt
      (lt_of_le_of_lt hi (Nat.lt_of_succ_le hk))
    exact upperCrossingTime_lt_of_le_upcrossingsBefore hN_pos hab this
  -- Stopped values: g σ_i ≤ a, b ≤ g τ_i.
  have h_g_sig : ∀ i ≤ k, g (lowerCrossingTime a b g N i ω) ω ≤ a := fun i hi =>
    stoppedValue_lowerCrossingTime (h_sig_lt_N i hi).ne
  have h_g_tau : ∀ i ≤ k, b ≤ g (upperCrossingTime a b g N (i + 1) ω) ω := fun i hi =>
    stoppedValue_upperCrossingTime (h_tau_lt_N i hi).ne
  -- Strict separation: σ_i < τ_i for i ≤ k (lowerCrossingTime n < upperCrossingTime (n+1)
  -- when upperCrossingTime (n+1) ≠ N).
  have h_sig_lt_tau : ∀ i ≤ k, lowerCrossingTime a b g N i ω
                              < upperCrossingTime a b g N (i + 1) ω := fun i hi =>
    lowerCrossingTime_lt_upperCrossingTime hab (h_tau_lt_N i hi).ne
  -- Weak chain: τ_i ≤ σ_{i+1} (upperCrossingTime (i+1) ≤ lowerCrossingTime (i+1)).
  have h_tau_le_sig : ∀ i, upperCrossingTime a b g N (i + 1) ω
                          ≤ lowerCrossingTime a b g N (i + 1) ω := fun i =>
    upperCrossingTime_le_lowerCrossingTime
  -- Strict separation: τ_i < σ_{i+1} (when σ_{i+1} ≠ N).
  have h_tau_lt_sig : ∀ i, i + 1 ≤ k →
      upperCrossingTime a b g N (i + 1) ω < lowerCrossingTime a b g N (i + 1) ω := fun i hi =>
    upperCrossingTime_lt_lowerCrossingTime hab (h_sig_lt_N (i + 1) hi).ne
  -- The strict τ chain: τ_0 < τ_1 < ... < τ_k. Each τ_i < N.
  have h_tau_strictMono : ∀ i, i + 1 ≤ k →
      upperCrossingTime a b g N (i + 1) ω < upperCrossingTime a b g N (i + 2) ω := by
    intro i hi
    -- upperCrossingTime_lt_succ requires upperCrossingTime (i+2) ≠ N.
    have h := h_tau_lt_N (i + 1) hi
    -- upperCrossingTime ((i+1) + 1) ω < upperCrossingTime (... + 1) ω, i.e., uses
    -- `upperCrossingTime_lt_succ` with parameter (i + 1).
    exact upperCrossingTime_lt_succ hab (h_tau_lt_N (i + 1) hi).ne
  -- τ_0 ≥ 1 (key lemma).
  have h_tau_zero_pos : 1 ≤ upperCrossingTime a b g N 1 ω := by
    apply upperCrossingTime_one_pos hab g N ω
    have := hk
    omega
  -- Hence τ_i ≥ i + 1 for i = 0, …, k. Useful for: `t'_i = N - τ_{k - 1 - i} < N`.
  have h_tau_ge : ∀ i ≤ k, upperCrossingTime a b g N (i + 1) ω ≥ i + 1 := by
    intro i hi
    induction i with
    | zero => exact h_tau_zero_pos
    | succ j ihj =>
      have hj : j ≤ k := Nat.le_of_succ_le hi
      have hj_pred := ihj hj
      have h_strict : upperCrossingTime a b g N (j + 1) ω < upperCrossingTime a b g N (j + 2) ω :=
        h_tau_strictMono j hi
      have h_eq : j + 1 + 1 = j + 2 := by ring
      rw [h_eq]
      omega
  -- Now define witnesses for revPath g N.
  -- s' i = N - σ_{k - i}, t' i = N - τ_{k - 1 - i}, for i = 0, …, k - 1.
  -- For convenience, define them as functions ℕ → ℕ (extending arbitrarily outside [0, k)).
  set s' : ℕ → ℕ := fun i => N - lowerCrossingTime a b g N (k - i) ω with hs'_def
  set t' : ℕ → ℕ := fun i => N - upperCrossingTime a b g N (k - i) ω with ht'_def
  -- Apply upperCrossingTime_le_of_witness to revPath g N at level k.
  have h_witness :
      upperCrossingTime a b (revPath g N) N k ω ≤ if k = 0 then 0 else t' (k - 1) := by
    apply upperCrossingTime_le_of_witness (revPath g N) N ω s' t' k
    -- (1) s' i < t' i for i < k.
    · intro i hi
      simp only [hs'_def, ht'_def]
      have h1 : k - i ≤ k := Nat.sub_le _ _
      have h2 : k - i ≥ 1 := by omega
      -- N - σ_{k-i} < N - τ_{k-i} iff τ_{k-i} < σ_{k-i}.
      have h_sig_lt_N' := h_sig_lt_N (k - i) h1
      have h_tau_lt_sig' :
          upperCrossingTime a b g N (k - i) ω < lowerCrossingTime a b g N (k - i) ω := by
        have h_eq : k - i = (k - i - 1) + 1 := by omega
        rw [h_eq]
        exact h_tau_lt_sig (k - i - 1) (by omega)
      -- σ_{k-i} ≤ N (≤ to get bound).
      have h_sig_le_N : lowerCrossingTime a b g N (k - i) ω ≤ N := lowerCrossingTime_le
      have h_tau_le_N : upperCrossingTime a b g N (k - i) ω ≤ N := upperCrossingTime_le
      omega
    -- (2) t' i ≤ s' (i+1) for i + 1 < k (i.e., 1 ≤ k - 1 - i).
    · intro i hi
      simp only [hs'_def, ht'_def]
      -- N - τ_{k-i} ≤ N - σ_{k-i-1} iff σ_{k-i-1} ≤ τ_{k-i}.
      -- Use h_tau_le_sig: τ_{k-i-1} = upperCrossingTime ((k-i-1)+1) ≤ lowerCrossingTime ((k-i-1)+1) = σ_{k-i}.
      -- Wait we want σ_{k-i-1} ≤ τ_{k-i} = upperCrossingTime (k-i-1+1) = upperCrossingTime (k-i).
      -- σ_{k-i-1} = lowerCrossingTime (k-i-1) ≤ upperCrossingTime (k-i) by lowerCrossingTime_le_upperCrossingTime_succ.
      have h_le : lowerCrossingTime a b g N (k - (i + 1)) ω
                ≤ upperCrossingTime a b g N (k - i) ω := by
        have h_eq : k - i = (k - (i + 1)) + 1 := by omega
        rw [h_eq]
        exact lowerCrossingTime_le_upperCrossingTime_succ
      have h_sig_le_N : lowerCrossingTime a b g N (k - (i + 1)) ω ≤ N := lowerCrossingTime_le
      have h_tau_le_N : upperCrossingTime a b g N (k - i) ω ≤ N := upperCrossingTime_le
      omega
    -- (3) t' i < N for i < k.
    · intro i hi
      simp only [ht'_def]
      have h1 : k - i ≤ k := Nat.sub_le _ _
      have h2 : k - i ≥ 1 := by omega
      have h_eq : k - i = (k - i - 1) + 1 := by omega
      rw [h_eq]
      have h_tau_ge' := h_tau_ge (k - i - 1) (by omega)
      have h_tau_le_N : upperCrossingTime a b g N ((k - i - 1) + 1) ω ≤ N := upperCrossingTime_le
      omega
    -- (4) revPath g N (s' i) ω ≤ a for i < k.
    · intro i hi
      simp only [hs'_def, revPath]
      have h1 : k - i ≤ k := Nat.sub_le _ _
      have h_sig_lt_N' := h_sig_lt_N (k - i) h1
      have h_sub_eq : N - (N - lowerCrossingTime a b g N (k - i) ω)
                    = lowerCrossingTime a b g N (k - i) ω := by
        have : lowerCrossingTime a b g N (k - i) ω ≤ N := lowerCrossingTime_le
        omega
      rw [h_sub_eq]
      exact h_g_sig (k - i) h1
    -- (5) b ≤ revPath g N (t' i) ω for i < k.
    · intro i hi
      simp only [ht'_def, revPath]
      have h1 : k - i ≤ k := Nat.sub_le _ _
      have h2 : k - i ≥ 1 := by omega
      have h_eq : k - i = (k - i - 1) + 1 := by omega
      have h_tau_lt_N' := h_tau_lt_N (k - i - 1) (by omega)
      have h_tau_le_N : upperCrossingTime a b g N (k - i) ω ≤ N := upperCrossingTime_le
      have h_sub_eq : N - (N - upperCrossingTime a b g N (k - i) ω)
                    = upperCrossingTime a b g N (k - i) ω := by omega
      rw [h_sub_eq, h_eq]
      exact h_g_tau (k - i - 1) (by omega)
  -- Now use the witness bound: `upperCrossingTime a b (revPath g N) N k ω < N`, hence
  -- `k ≤ upcrossingsBefore a b (revPath g N) N ω`.
  have h_witness_lt_N : upperCrossingTime a b (revPath g N) N k ω < N := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · subst hk0
      simp [upperCrossingTime_zero, hN_pos]
    · simp only [if_neg hk_pos.ne'] at h_witness
      simp only [ht'_def] at h_witness
      have h1 : k - (k - 1) = 1 := by omega
      rw [h1] at h_witness
      have h_tau_pos := h_tau_zero_pos
      have h_tau_le_N : upperCrossingTime a b g N 1 ω ≤ N := upperCrossingTime_le
      omega
  -- Hence `k ∈ {n | upperCrossingTime a b (revPath g N) N n ω < N}`.
  exact le_csSup (upperCrossingTime_lt_bddAbove hab) h_witness_lt_N

private lemma upcrossingsBefore_le_revPath_succ {a b : ℝ} (hab : a < b)
    (g : ℕ → Ω' → ℝ) (N : ℕ) (ω : Ω') :
    upcrossingsBefore a b g N ω ≤ upcrossingsBefore a b (revPath g N) N ω + 1 := by
  -- The bound `n ≤ m + 1` is equivalent to `n - 1 ≤ m`. Use `upcrossingsBefore_revPath_ge`
  -- with `k = n - 1`.
  set n := upcrossingsBefore a b g N ω with hn_def
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · simp [hn0]
  · have hk : (n - 1) + 1 ≤ n := Nat.succ_pred_eq_of_pos hn_pos |>.le
    have h := upcrossingsBefore_revPath_ge hab g N ω (n - 1)
      (hk.trans_eq hn_def.symm |>.trans (le_refl _))
    omega

end PathReversal

section Upcrossings
/-! ### β.2 — Backward upcrossing finiteness (proven via path-reversal lemma) -/

variable {f : ℕᵒᵈ → Ω → ℝ} {ℋ : Filtration ℕᵒᵈ m₀}

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
    have h := upcrossingsBefore_le_revPath_succ hab g N ω
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
  -- Define `g` as the pointwise `limsup`. When the sequence converges, this equals
  -- the limit; otherwise it's some unspecified real value (irrelevant on the null set).
  -- The key point: `limsup` is tail-invariant, so for every `k`, we may rewrite
  -- `g ω = limsup (fun n => g_back (n + k) ω) atTop`, and the RHS is built from
  -- functions that are `ℋ (toDual k)`-measurable (since `toDual (n + k) ≤ toDual k`
  -- in ℕᵒᵈ for `0 ≤ n`, hence `ℋ (toDual (n+k)) ≤ ℋ (toDual k)`). Hence `g` is
  -- `ℋ (toDual k)`-measurable for every `k`, and so `m_inf = ⨅ k, ℋ (toDual k)`-measurable.
  set g : Ω → ℝ := fun ω => Filter.limsup (fun n => g_back n ω) Filter.atTop with hg_def
  -- Each `g_back n` is `ℋ (toDual n)`-measurable.
  have h_meas_back : ∀ n : ℕ, Measurable[ℋ (OrderDual.toDual n)] (g_back n) := by
    intro n
    -- `g_back n = f (toDual n)`, which is strongly `ℋ (toDual n)`-measurable.
    exact (hf.stronglyMeasurable (OrderDual.toDual n)).measurable
  -- For `k ≤ n` in ℕ, `toDual n ≤ toDual k` in ℕᵒᵈ, so `ℋ (toDual n) ≤ ℋ (toDual k)`.
  have h_meas_at : ∀ k n : ℕ, k ≤ n → Measurable[ℋ (OrderDual.toDual k)] (g_back n) := by
    intro k n hkn
    have hdual : OrderDual.toDual n ≤ OrderDual.toDual k :=
      OrderDual.toDual_le_toDual.mpr hkn
    exact (h_meas_back n).mono (ℋ.mono hdual) le_rfl
  -- For each `k`, `g` is `ℋ (toDual k)`-measurable.
  have h_g_meas_at : ∀ k : ℕ, Measurable[ℋ (OrderDual.toDual k)] g := by
    intro k
    -- `g ω = limsup (fun n => g_back n ω) atTop = limsup (fun n => g_back (n + k) ω) atTop`
    -- (tail invariance), and each `g_back (n + k)` is `ℋ (toDual k)`-measurable.
    have h_eq : g = fun ω => Filter.limsup (fun n => g_back (n + k) ω) Filter.atTop := by
      funext ω
      rw [hg_def]
      exact (Filter.limsup_nat_add (fun n => g_back n ω) k).symm
    rw [h_eq]
    -- Each `n ↦ g_back (n + k)` is `ℋ (toDual k)`-measurable (since `k ≤ n + k`).
    refine Measurable.limsup (fun n => ?_)
    exact h_meas_at k (n + k) (Nat.le_add_left k n)
  -- Hence `g` is `(⨅ k, ℋ (toDual k))`-measurable.
  have h_g_meas_inf : Measurable[⨅ k : ℕ, ℋ (OrderDual.toDual k)] g := by
    -- `Measurable[m] g ↔ ∀ s ∈ borel, g ⁻¹' s ∈ m`.  For `m = ⨅ k, ℋ (toDual k)`,
    -- by `measurableSet_iInf`, `g ⁻¹' s ∈ m ↔ ∀ k, g ⁻¹' s ∈ ℋ (toDual k)`.
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro k
    exact h_g_meas_at k hs
  -- Strongly measurable from measurable (ℝ has second-countable topology).
  refine ⟨g, h_g_meas_inf.stronglyMeasurable, ?_⟩
  -- AE-tendsto: when the sequence converges, `g ω = limsup = lim`, so the convergence
  -- statement holds. AE this follows from `h_ae_tends`.
  filter_upwards [h_ae_tends] with ω hω
  obtain ⟨c, hc⟩ := hω
  have h_lims : Filter.limsup (fun n => g_back n ω) Filter.atTop = c := hc.limsup_eq
  rw [hg_def] at *
  show Tendsto (fun n => g_back n ω) Filter.atTop (𝓝 (Filter.limsup (fun n => g_back n ω) atTop))
  rw [h_lims]
  exact hc

end MainTheorem

end InformationTheory.Shannon
