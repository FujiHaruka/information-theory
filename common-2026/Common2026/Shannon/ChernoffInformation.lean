import Common2026.Shannon.Chernoff
import Common2026.InformationTheory.Asymptotic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.Filter.IsBounded

/-!
# Chernoff Information sandwich `Tendsto` (T1-B independent publish)

This file publishes the **sandwich `Tendsto` form** of the Chernoff lemma
(Cover-Thomas Theorem 11.9.1) on top of the existing achievability side in
`Common2026/Shannon/Chernoff.lean`.

## Context

The predecessor file `Common2026/Shannon/Chernoff.lean` (1066 lines, 0 sorry)
publishes:

* `chernoffInfo P₁ P₂` (Cover-Thomas 11.9.1 exponent),
* `bayesErrorMinPmf P₁ P₂ n` (n-IID optimal Bayes error in pmf form),
* `chernoff_lemma_achievability` (rate-side lower bound,
  `liminf -(1/n) log bayesErrorMinPmf ≥ chernoffInfo`).

The converse direction (`limsup -(1/n) log bayesErrorMinPmf ≤ chernoffInfo`)
is deferred to a follow-up plan (`chernoff-converse-moonshot-plan.md`),
following the **L-S2** retreat in the predecessor plan
`chernoff-hoeffding-moonshot-plan.md`.

## What this file publishes

* `chernoff_rate_isBoundedUnder_ge`: the rate sequence
  `-(1/n) log bayesErrorMinPmf` is bounded below by `chernoffInfo` along `atTop`.
  Discharged from `chernoffInfo_nonneg` + `chernoff_rate_ge_chernoffInfo_eventually`.

* `chernoff_lemma_tendsto`: **Cover-Thomas Theorem 11.9.1 sandwich `Tendsto`**,
  in hypothesis pass-through form. Given the (deferred) converse `h_converse`
  and an `IsBoundedUnder (· ≤ ·)` hypothesis `h_bdd_le`, the rate sequence
  converges to `chernoffInfo P₁ P₂`. Mirrors the publish pattern of
  `Common2026/Shannon/HoeffdingTradeoff.lean:hoeffding_tradeoff_with_hypothesis`.

* `chernoff_dotEq_tendsto`: equivalent `DotEq` form
  (`bayesErrorMinPmf ≐ exp(-n · chernoffInfo)`), derived from
  `chernoff_lemma_tendsto` via `dotEq_iff_tendsto_log_div`.

## Retreat lines adopted

* **L-Ch1** (converse hypothesis): `h_converse : limsup rate ≤ chernoffInfo`
  taken as a hypothesis. Discharge plan: `chernoff-converse-moonshot-plan.md`.
* **L-Ch2** (`IsBoundedUnder (· ≤ ·)` hypothesis): taken as a hypothesis.
  Internal discharge would require ~120 line transliteration of the `private`
  `Chernoff.chernoff_rate_le_aux_upper`.
* **L-Ch3** (`IsBoundedUnder (· ≥ ·)`): **internally discharged** here, not
  a hypothesis (see `chernoff_rate_isBoundedUnder_ge`).

## Design notes

* The `pmf` form `α → ℝ` is kept throughout (matching `Chernoff.lean`).
* The `[Nonempty α]` instance is required for `bayesErrorMinPmf_pos`
  (constant Fin n → α vector exists, used to lower-bound the Bayes error sum).
* `tendsto_of_le_liminf_of_limsup_le` from
  `Mathlib.Topology.Order.LiminfLimsup` is the single Mathlib lemma driving
  the sandwich; the four boundedness defaults are supplied explicitly.
-/

namespace InformationTheory.Shannon.ChernoffInformation

set_option linter.unusedSectionVars false

open Real InformationTheory Filter
open InformationTheory.Shannon.Chernoff
open scoped Topology InformationTheory.Asymptotic

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Phase 2 — `IsBoundedUnder (· ≥ ·)` internal discharge -/

/-- **L-Ch3 internal discharge**: the rate sequence
`-(1/n) log bayesErrorMinPmf` is bounded below along `atTop`.

This is the `IsBoundedUnder (· ≥ ·)` half of the boundedness defaults consumed by
`tendsto_of_le_liminf_of_limsup_le`. We derive it from
`Chernoff.chernoff_rate_ge_chernoffInfo_eventually` (which gives
`rate n ≥ chernoffInfo + log 2 / n` eventually) by dropping the positive
`log 2 / n` slack and applying `Filter.isBoundedUnder_of_eventually_ge`. -/
lemma chernoff_rate_isBoundedUnder_ge
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) := by
  -- Use `chernoff_rate_ge_chernoffInfo_eventually` and drop the `+ log 2 / n` slack.
  have h_event :=
    chernoff_rate_ge_chernoffInfo_eventually P₁ P₂ hP₁_pos hP₂_pos
  have h_log2_nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- ∀ᶠ n, chernoffInfo P₁ P₂ ≤ rate n.
  have h_ev : ∀ᶠ n : ℕ in atTop,
      chernoffInfo P₁ P₂
        ≤ -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n) := by
    filter_upwards [h_event, eventually_gt_atTop 0] with n h_ev_n hn
    -- h_ev_n : rate n ≥ chernoffInfo + log 2 / n.
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_div_nn : (0 : ℝ) ≤ Real.log 2 / n := div_nonneg h_log2_nn hn_R.le
    linarith
  exact Filter.isBoundedUnder_of_eventually_ge h_ev

/-! ## Phase 4 — sandwich `Tendsto` wrapper -/

/-- **Cover-Thomas Theorem 11.9.1** (sandwich `Tendsto`, hypothesis pass-through).

Given:
* achievability (existing): `chernoff_lemma_achievability` gives
  `chernoffInfo ≤ liminf (rate n)`,
* converse (hypothesis, L-Ch1): `h_converse : limsup (rate n) ≤ chernoffInfo`,
* `IsBoundedUnder (· ≤ ·)` (hypothesis, L-Ch2): `h_bdd_le`,
* `IsBoundedUnder (· ≥ ·)` (internal discharge, L-Ch3): supplied via
  `chernoff_rate_isBoundedUnder_ge`,

the optimal Bayesian error rate `-(1/n) log bayesErrorMinPmf` converges to
`chernoffInfo P₁ P₂`.

This is the formal **Tendsto** version of Cover-Thomas:
`P_e^{(n)} ≐ exp(-n · C(P₁, P₂))`. Downstream code (e.g. the DotEq corollary
`chernoff_dotEq_tendsto` below) can rely on this Tendsto form right now;
the discharge of `h_converse` is the responsibility of a follow-up plan
(`chernoff-converse-moonshot-plan.md`). -/
theorem chernoff_lemma_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_converse : Filter.limsup
        (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
        atTop ≤ chernoffInfo P₁ P₂)
    (h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))) :
    Tendsto (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂)) :=
  tendsto_of_le_liminf_of_limsup_le
    (chernoff_lemma_achievability P₁ P₂ hP₁_pos hP₂_pos)
    h_converse
    h_bdd_le
    (chernoff_rate_isBoundedUnder_ge P₁ P₂ hP₁_pos hP₂_pos)

/-! ## Phase 5 — `DotEq` corollary -/

/-- **Positivity along `atTop`** for the n-IID Bayes error.

`dotEq_iff_tendsto_log_div` requires `0 < a n ∧ 0 < b n` **for every** `n`,
including `n = 0`. For `bayesErrorMinPmf`, positivity at `n = 0` follows from
the singleton sum `(Fin 0 → α) ≃ {()}` giving `(1/2) * min(1, 1) = 1/2 > 0`.
The existing `Chernoff.bayesErrorMinPmf_pos` lemma covers all `n` including
`n = 0`. We re-package it as a convenience reference. -/
lemma bayesErrorMinPmf_pos_all
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (n : ℕ) :
    0 < bayesErrorMinPmf P₁ P₂ n :=
  bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n

/-- The exponential lower envelope `n ↦ exp(-n · chernoffInfo P₁ P₂)` is
strictly positive for every `n`. (Used as the right-hand sequence in the
`DotEq` corollary.) -/
lemma exp_neg_n_chernoffInfo_pos (P₁ P₂ : α → ℝ) (n : ℕ) :
    0 < Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂) :=
  Real.exp_pos _

/-- The ratio `(1/n) · log (bayesErrorMinPmf / exp(-n · chernoffInfo))`
equals `chernoffInfo - rate n` (where `rate n := -(1/n) log bayesErrorMinPmf`).
(Pointwise reshape; used inside the DotEq corollary proof.)

Derivation:
  `log(b / exp(-n c)) = log b - log(exp(-n c)) = log b - (-n c) = log b + n c`.
  `(1/n) * (log b + n c) = (1/n) * log b + c = - rate n + c = c - rate n`. -/
lemma rate_eq_log_ratio
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) {n : ℕ} (hn : 0 < n) :
    (1 / (n : ℝ)) *
        Real.log (bayesErrorMinPmf P₁ P₂ n /
          Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂))
      = chernoffInfo P₁ P₂
          - (-((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) := by
  have hb_pos : 0 < bayesErrorMinPmf P₁ P₂ n :=
    bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n
  have he_pos : 0 < Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂) := Real.exp_pos _
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_R
  -- log (b / exp(-n c)) = log b - log (exp(-n c)) = log b - (-n c) = log b + n c.
  rw [Real.log_div hb_pos.ne' he_pos.ne']
  rw [Real.log_exp]
  field_simp
  ring

/-- **Cover-Thomas Theorem 11.9.1 in `DotEq` form**: the n-IID Bayesian
error decays at the exponential rate `chernoffInfo P₁ P₂`:

  `bayesErrorMinPmf P₁ P₂ n ≐ exp(-n · chernoffInfo P₁ P₂)`.

Derived from `chernoff_lemma_tendsto` via `dotEq_iff_tendsto_log_div`. -/
theorem chernoff_dotEq_tendsto
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_converse : Filter.limsup
        (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
        atTop ≤ chernoffInfo P₁ P₂)
    (h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))) :
    (fun n : ℕ => bayesErrorMinPmf P₁ P₂ n)
      ≐ (fun n : ℕ => Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂)) := by
  -- Use `dotEq_iff_tendsto_log_div` with positivity from `bayesErrorMinPmf_pos` and `exp_pos`.
  rw [InformationTheory.Asymptotic.dotEq_iff_tendsto_log_div]
  · -- Need: Tendsto (fun n => (1/n) * log (bayesErrorMinPmf / exp(-n c))) atTop (𝓝 0).
    -- Equals Tendsto (fun n => (1/n) * (log b + n c)) atTop (𝓝 0)
    --      = Tendsto (fun n => (1/n) * log b + c) atTop (𝓝 0)
    --      = Tendsto (fun n => rate n shifted) atTop (𝓝 0).
    -- Note rate n = -(1/n) * log b. We want (1/n) * log b + c → 0,
    --   i.e. -rate n + c → 0, i.e. rate n → c.
    have h_tendsto :=
      chernoff_lemma_tendsto P₁ P₂ hP₁_pos hP₂_pos h_converse h_bdd_le
    -- We have rate → chernoffInfo. We need (1/n) * log(b/exp(-n c)) → 0.
    -- (1/n) * log(b/exp(-n c)) = (1/n) * (log b - (-n c)) = (1/n) * log b + c
    --                          = -rate n + c.
    -- Thus the sequence equals (chernoffInfo - rate n), which → 0.
    have h_diff_tendsto :
        Tendsto (fun n : ℕ => chernoffInfo P₁ P₂
            - (-((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))) atTop (𝓝 0) := by
      have h_sub :
          Tendsto (fun n : ℕ => chernoffInfo P₁ P₂
              - (-((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))) atTop
            (𝓝 (chernoffInfo P₁ P₂ - chernoffInfo P₁ P₂)) :=
        (tendsto_const_nhds.sub h_tendsto)
      simpa using h_sub
    -- Show the two sequences are eventually equal.
    have h_eq_event : ∀ᶠ n : ℕ in atTop,
        (1 / (n : ℝ)) *
            Real.log (bayesErrorMinPmf P₁ P₂ n /
              Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂))
          = chernoffInfo P₁ P₂
              - (-((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact rate_eq_log_ratio P₁ P₂ hP₁_pos hP₂_pos hn
    exact h_diff_tendsto.congr' (h_eq_event.mono (fun n h => h.symm))
  · -- Positivity hypothesis: 0 < bayesErrorMinPmf P₁ P₂ n ∧ 0 < exp(-n c) for all n.
    intro n
    refine ⟨bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n, Real.exp_pos _⟩

end InformationTheory.Shannon.ChernoffInformation
