import Common2026.Shannon.Chernoff
import Common2026.Shannon.ChernoffInformation
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.Filter.IsBounded

/-!
# Chernoff converse L-Ch1 (partial) discharge — T1-B follow-up

This file publishes the **partial discharge** of the L-Ch1 hypothesis pulled
out of `Common2026/Shannon/ChernoffInformation.lean`:

```
h_converse : Filter.limsup (fun n : ℕ => -((1 : ℝ) / n) *
    Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop ≤ chernoffInfo P₁ P₂
```

## Context

The predecessor files publish:

* `Common2026/Shannon/Chernoff.lean` (1066 lines, 0 sorry) — `chernoffZSum`,
  `chernoffInfo`, `chernoffInfo_attained`, `bayesErrorMinPmf`,
  `bayesErrorMinPmf_pos`, `bayesErrorMinPmf_le_half_Z_pow`,
  `chernoff_lemma_achievability` (rate-side lower bound).
* `Common2026/Shannon/ChernoffInformation.lean` (241 lines, 0 sorry) —
  `chernoff_rate_isBoundedUnder_ge` (L-Ch3 internal discharge),
  `chernoff_lemma_tendsto` (sandwich `Tendsto` with L-Ch1+L-Ch2 hypotheses).

The L-Ch1 hypothesis (Phase B converse `limsup rate ≤ chernoffInfo`) is the
Cover-Thomas Theorem 11.9.1 upper-rate half, traditionally discharged via
Sanov LDP per-tilt + `pmfToMeasure` bridge. A full discharge of L-Ch1 along
that path is a ~1000-line undertaking (cf. `Common2026/Shannon/CramerLC2-
Discharge.lean` for the analogous Cramér L-C2 situation) and is **deferred**.

## What this file publishes (partial discharge L-CC2)

* `chernoffMediator P₁ P₂ lam` — the **Chernoff mediating pmf**
  `P_λ(a) := P₁(a)^{1-λ} · P₂(a)^λ / Z(λ)` (Cover-Thomas 11.9.7), as a
  Phase A scaffolding object (`α → ℝ`).
* `chernoffMediator_pos`, `chernoffMediator_nonneg`, `chernoffMediator_sum_eq_one`
  — basic properties of the mediating pmf.
* `chernoff_rate_isBoundedUnder_le` — internal discharge of the L-Ch2
  hypothesis (`IsBoundedUnder (· ≤ ·)`) using the `(1/2)·p_min^n` lower-bound
  on `bayesErrorMinPmf` (re-built here since the parent `Chernoff.chernoff_
  rate_le_aux_upper` is `private`).
* `chernoff_converse_from_per_tilt` — **per-tilt wrapper**: given a per-tilt
  Sanov-style lower bound on `bayesErrorMinPmf` (hypothesis form), derive
  `limsup rate ≤ -log Z(λ)`. This is the main reduction shape.
* `chernoff_converse_of_per_tilt_existential` — load-bearing FALSE per-tilt
  hypothesis wrapper (sorry-based migrated). The per-tilt Sanov-style lower
  bound `IsBayesErrorPerTiltLowerBound` is FALSE in general (Cramér
  `Θ(1/√n)` prefactor); successor `ChernoffBandMassDischarge` discharges the
  converse via the `ε`-relaxed route. The previous wrapper repackaged the
  load-bearing FALSE hypothesis; it now states the unconditional headline
  `limsup rate ≤ chernoffInfo P₁ P₂` with a sorry pinning the residual to
  the successor.
* `chernoff_lemma_tendsto_from_per_tilt` — sandwich `Tendsto` wrapper re-
  publishing `chernoff_lemma_tendsto` with hypothesis count reduced 2 → 1
  (only the per-tilt hypothesis remains; both L-Ch1 and L-Ch2 are derived
  from it).

## Retreat lines adopted

* **L-CC2** (per-tilt hypothesis reduced form): the L-Ch1 hypothesis is
  reshaped into a single per-tilt Sanov-style lower bound on
  `bayesErrorMinPmf P₁ P₂ n` at the optimal tilt `λ*`. Full `sanov_ldp_
  equality` discharge of that single remaining hypothesis is **deferred**
  to a follow-up plan.
* **Not adopted L-CC1** (Phase A scaffolding only): we go past Phase A and
  publish the per-tilt wrapper + main
  `chernoff_converse_of_per_tilt_existential` (load-bearing FALSE per-tilt
  hypothesis, sorry-based migrated to successor `ChernoffBandMassDischarge`
  via the `ε`-relaxed route) + sandwich Tendsto wrapper.

## Design notes

* `chernoffMediator` is defined as a plain `α → ℝ` (matching the `pmf` shape
  used throughout `Chernoff.lean`); a `Measure α` lift can be derived later
  via `pmfToMeasure` for actual Sanov LDP launch (follow-up plan scope).
* `chernoff_rate_isBoundedUnder_le` is **independently rebuilt** here rather
  than re-exposed from `Chernoff.lean` because the parent
  `chernoff_rate_le_aux_upper` is `private`. We use the same `(1/2)·p_min^n`
  vector lower bound but inlined without the constant-function vector
  argument.
* The per-tilt hypothesis shape `C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n`
  (eventually for `n ≥ 1`) matches what a Sanov LDP launch at the tilted
  measure would produce after change-of-measure.
-/

namespace InformationTheory.Shannon.ChernoffConverse

set_option linter.unusedSectionVars false

open Real InformationTheory Filter Finset
open InformationTheory.Shannon.Chernoff
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Phase A — `chernoffMediator` tilted pmf -/

/-- **Chernoff mediating pmf** (Cover-Thomas 11.9.7):
`P_λ(a) := P₁(a)^{1-λ} · P₂(a)^λ / Z(λ)`.

Scaffolding object intended as the natural Sanov LDP target measure on which
the converse-side per-tilt analysis lives. -/
noncomputable def chernoffMediator (P₁ P₂ : α → ℝ) (lam : ℝ) (a : α) : ℝ :=
  ((P₁ a) ^ (1 - lam) * (P₂ a) ^ lam) / chernoffZSum P₁ P₂ lam

omit [DecidableEq α] in
/-- `chernoffMediator > 0` under full support. -/
lemma chernoffMediator_pos
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    0 < chernoffMediator P₁ P₂ lam a := by
  unfold chernoffMediator
  exact div_pos
    (chernoffZSum_term_pos P₁ P₂ hP₁_pos hP₂_pos lam a)
    (chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam)

omit [DecidableEq α] in
/-- `chernoffMediator ≥ 0` under full support. -/
lemma chernoffMediator_nonneg
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    0 ≤ chernoffMediator P₁ P₂ lam a :=
  (chernoffMediator_pos P₁ P₂ hP₁_pos hP₂_pos lam a).le

omit [DecidableEq α] in
/-- `∑ a, chernoffMediator P₁ P₂ λ a = 1` (pmf normalisation). -/
lemma chernoffMediator_sum_eq_one
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    ∑ a : α, chernoffMediator P₁ P₂ lam a = 1 := by
  unfold chernoffMediator
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  -- Step 1: pull the constant divisor out of the sum.
  rw [← Finset.sum_div]
  -- Step 2: identify the numerator as `chernoffZSum P₁ P₂ lam` (definitional rfl) and divide.
  show chernoffZSum P₁ P₂ lam / chernoffZSum P₁ P₂ lam = 1
  exact div_self hZ_pos.ne'

/-! ## Phase A pre — `IsBoundedUnder (· ≤ ·)` internal discharge (L-Ch2) -/

/-- **L-Ch2 internal discharge**: the rate sequence
`-(1/n) log bayesErrorMinPmf` is bounded above along `atTop`.

The parent `Chernoff.chernoff_rate_le_aux_upper` is `private`; we rebuild the
same bound here using the constant-vector lower bound
`bayesErrorMinPmf ≥ (1/2)·p_min^n`. -/
lemma chernoff_rate_isBoundedUnder_le
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) := by
  classical
  -- p_min := min_a min(P₁ a, P₂ a) > 0.
  obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image
    (s := (Finset.univ : Finset α)) (f := fun a => min (P₁ a) (P₂ a))
    ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
  set p_min : ℝ := min (P₁ a₀) (P₂ a₀) with hpmin_def
  have hpmin_pos : 0 < p_min := lt_min (hP₁_pos a₀) (hP₂_pos a₀)
  refine ⟨-Real.log p_min + Real.log 2, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn
  -- Lower bound on bayesErrorMinPmf via const a₀ vector.
  have h_pmin_le_P₁ : ∀ a, p_min ≤ P₁ a := by
    intro a
    have := ha₀ a (Finset.mem_univ _)
    exact le_trans this (min_le_left _ _)
  have h_pmin_le_P₂ : ∀ a, p_min ≤ P₂ a := by
    intro a
    have := ha₀ a (Finset.mem_univ _)
    exact le_trans this (min_le_right _ _)
  have h_pmin_pow_le : ∀ x : Fin n → α,
      p_min ^ n ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    intro x
    refine le_min ?_ ?_
    · calc p_min ^ n
          = ∏ _i : Fin n, p_min := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i : Fin n, P₁ (x i) :=
          Finset.prod_le_prod (fun i _ => hpmin_pos.le)
            (fun i _ => h_pmin_le_P₁ (x i))
    · calc p_min ^ n
          = ∏ _i : Fin n, p_min := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i : Fin n, P₂ (x i) :=
          Finset.prod_le_prod (fun i _ => hpmin_pos.le)
            (fun i _ => h_pmin_le_P₂ (x i))
  -- Sum lower bound: take just the const a₀ vector summand.
  have h_term_nn : ∀ x : Fin n → α, 0 ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    intro x
    refine le_min ?_ ?_
    · exact Finset.prod_nonneg (fun i _ => (hP₁_pos (x i)).le)
    · exact Finset.prod_nonneg (fun i _ => (hP₂_pos (x i)).le)
  set x_const : Fin n → α := fun _ => a₀
  have h_sum_ge :
      p_min ^ n
        ≤ ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    calc p_min ^ n
        ≤ min (∏ i, P₁ (x_const i)) (∏ i, P₂ (x_const i)) := h_pmin_pow_le x_const
      _ ≤ ∑ x : Fin n → α, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) :=
          Finset.single_le_sum (s := (Finset.univ : Finset (Fin n → α)))
            (f := fun x => min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)))
            (fun x _ => h_term_nn x) (Finset.mem_univ x_const)
  -- bayesErrorMinPmf ≥ (1/2) p_min^n.
  have h_bayes_ge : (1 / 2 : ℝ) * p_min ^ n ≤ bayesErrorMinPmf P₁ P₂ n := by
    unfold bayesErrorMinPmf
    have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have := mul_le_mul_of_nonneg_left h_sum_ge h_half_nn
    exact this
  have h_bayes_pos : (0 : ℝ) < bayesErrorMinPmf P₁ P₂ n :=
    bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n
  have h_lb_pos : (0 : ℝ) < (1 / 2 : ℝ) * p_min ^ n :=
    mul_pos (by norm_num) (pow_pos hpmin_pos n)
  -- log bayesErrorMinPmf ≥ -log 2 + n · log p_min.
  have h_log_ge :
      Real.log ((1 / 2 : ℝ) * p_min ^ n)
        ≤ Real.log (bayesErrorMinPmf P₁ P₂ n) :=
    Real.log_le_log h_lb_pos h_bayes_ge
  have h_log_expand :
      Real.log ((1 / 2 : ℝ) * p_min ^ n)
        = -Real.log 2 + (n : ℝ) * Real.log p_min := by
    rw [Real.log_mul (by norm_num) (pow_pos hpmin_pos n).ne']
    rw [Real.log_pow]
    congr 1
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [Real.log_inv]
  rw [h_log_expand] at h_log_ge
  -- Multiply by -(1/n) ≤ 0:
  have h_neg_inv : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_mul :
      -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
        ≤ -((1 : ℝ) / n) * (-Real.log 2 + (n : ℝ) * Real.log p_min) :=
    mul_le_mul_of_nonpos_left h_log_ge h_neg_inv
  have h_simp :
      -((1 : ℝ) / n) * (-Real.log 2 + (n : ℝ) * Real.log p_min)
        = Real.log 2 / n - Real.log p_min := by
    field_simp
    ring
  rw [h_simp] at h_mul
  have h_log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log2_div_le : Real.log 2 / n ≤ Real.log 2 := by
    have h_div : Real.log 2 / n = Real.log 2 * (1 / n) := by ring
    rw [h_div]
    have h_inv_le : (1 / (n : ℝ)) ≤ 1 := by
      rw [div_le_one hn_R]
      exact_mod_cast hn
    have := mul_le_mul_of_nonneg_left h_inv_le h_log2_pos.le
    linarith [this]
  linarith

/-! ## Phase B — per-tilt converse wrapper -/

/-- **Per-tilt converse wrapper** (Phase B, unconditional headline):
`limsup rate ≤ -log Z(λ)` for any tilt `λ ∈ ℝ`.

This is the rate-side conclusion of the Cover-Thomas Theorem 11.9 converse
restricted to a single tilt `λ`. Combining with `chernoffInfo_attained` at
the optimum `λ*` (where `chernoffInfo = -log Z(λ*)`) yields the L-Ch1 main
conclusion `limsup rate ≤ chernoffInfo`.

**Sorry-based migration note**: this theorem previously consumed three
load-bearing arguments (`C : ℝ`, `hC_pos : 0 < C`, `h_lb : ∀ᶠ n, C·Z(λ)^n ≤
2·bayesErrorMinPmf`) that destructure the FALSE-in-general predicate
`IsBayesErrorPerTiltLowerBound` (`ChernoffPerTiltDischarge.lean:148`,
`@audit:defect(false-statement)`). The Cramér `Θ(1/√n)` prefactor rules out
a constant `C > 0`; the genuine route lives at the successor
`ChernoffBandMassDischarge` via the `ε`-relaxed bound. Hypotheses dropped
so the declaration states the unconditional `λ`-indexed claim.

@residual(plan:chernoff-converse-sanov-discharge) -/
theorem chernoff_converse_from_per_tilt
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ -Real.log (chernoffZSum P₁ P₂ lam) := by
  sorry

/-! ## Phase C — main theorem `chernoff_converse_of_per_tilt_existential`
    (load-bearing FALSE per-tilt hypothesis, sorry-based migrated) -/

/-- **Cover-Thomas Theorem 11.9.1 converse half** (unconditional headline):

```
limsup rate ≤ chernoffInfo
```

**Sorry-based migration note**: this theorem previously consumed an
existence-bundle `h_per_tilt : ∃ lam ∈ Icc 0 1, chernoffInfo = -log Z(λ) ∧ ∃ C,
0 < C ∧ ∀ᶠ n, C·Z(λ)^n ≤ 2·bayesErrorMinPmf` that bundles (a) an attaining
tilt and (b) the FALSE-in-general Sanov-style per-tilt lower bound
(`IsBayesErrorPerTiltLowerBound`). The per-tilt lower bound carries the
converse core but is FALSE (Cramér `Θ(1/√n)` prefactor rules out a constant
`C > 0`); successor `ChernoffBandMassDischarge` discharges the converse via
the `ε`-relaxed route, not the false constant-`C` predicate.

The hypothesis is dropped here so the declaration states the unconditional
headline. The body merely pinned the FALSE predicate together with
`chernoffInfo_attained`; the genuine combined proof lives at the successor.

@residual(plan:chernoff-converse-sanov-discharge) -/
theorem chernoff_converse_of_per_tilt_existential
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ chernoffInfo P₁ P₂ := by
  sorry

/-! ## Phase D — sandwich `Tendsto` re-publish with per-tilt hypothesis only -/

/-- **Sandwich `Tendsto` wrapper** (Cover-Thomas Theorem 11.9.1, unconditional
headline): `-(1/n) log bayesErrorMinPmf → chernoffInfo P₁ P₂` along `atTop`.

**Sorry-based migration note**: this theorem previously consumed the same
load-bearing FALSE per-tilt existence-bundle as
`chernoff_converse_of_per_tilt_existential`. The hypothesis is dropped so
the declaration states the unconditional headline. The genuine combined
proof lives at the successor `ChernoffBandMassDischarge.chernoff_lemma_tendsto_holds`
via the `ε`-relaxed route.

@residual(plan:chernoff-converse-sanov-discharge) -/
theorem chernoff_lemma_tendsto_from_per_tilt
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Tendsto
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂)) := by
  sorry

end InformationTheory.Shannon.ChernoffConverse
