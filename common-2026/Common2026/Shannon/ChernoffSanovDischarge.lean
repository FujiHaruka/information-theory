import Common2026.Shannon.ChernoffPerTiltSanov
import Common2026.Shannon.ChernoffPerTiltDischarge
import Common2026.Shannon.ChernoffConverse
import Common2026.Shannon.Chernoff
import Common2026.Shannon.ChernoffNLetterZSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chernoff converse — Sanov-style per-tilt discharge (T1-B follow-up)

This file works toward the **genuine, unconditional** discharge of the Chernoff
converse `limsup rate ≤ chernoffInfo` (Cover-Thomas Theorem 11.9.1), the residual
left load-bearing in `ChernoffPerTiltDischarge.lean` /
`ChernoffPerTiltSanov.lean` as the predicate `IsBayesErrorPerTiltLowerBound` /
`IsChernoffNLetterRN`.

## ⚠️ Plan-level finding (honesty alert)

The predicate `IsBayesErrorPerTiltLowerBound P₁ P₂ lam`
(`ChernoffPerTiltDischarge.lean:136`) demands a **constant** `C > 0` with the
**exact** base `Z(λ)`:

```
∃ C > 0, ∀ᶠ n, C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n.
```

This is equivalent to `liminf_n bayesErrorMinPmf / Z(λ)^n > 0`. But the genuine
method-of-types asymptotics of the Bayes error are
`bayesErrorMinPmf ~ poly(n) · Z(λ*)^n` with a **vanishing** sub-exponential
prefactor (a `Θ(1/√n)` local-limit / lattice factor): so
`bayesErrorMinPmf / Z(λ*)^n → 0` and **no constant `C` exists**. The predicate
as stated is therefore *false* in general (verifiable already on a symmetric
2-point alphabet at `λ* = 1/2`, where the Bayes error is a known `Θ(1/√n)·Z^n`).

The predicate is only ever *consumed* as a hypothesis (no code claims to prove
it); it over-states what the converse needs. The converse only needs
`limsup rate ≤ -log Z(λ*)`, which the **`ε`-relaxed** lower bound
`∀ ε>0, ∀ᶠ n, exp(-nε)·Z(λ*)^n ≤ 2·bayesErrorMinPmf` delivers (the vanishing
prefactor is absorbed by `exp(-nε)`). That `ε`-relaxed bound is what the
typical-set + reverse-Hölder argument actually produces.

## What this file genuinely proves (no Mathlib gap, no hypothesis)

* **Step 1 — reverse Hölder per-point on the typical band** (`min_ge_exp_neg_mul
  _rpow_mul_rpow`): for `a, b > 0`, `λ ∈ [0,1]`, and `|log a - log b| ≤ δ`,
  `exp(-δ) · a^{1-λ}·b^λ ≤ min a b`. This is the exact reverse of the
  achievability-side `min_le_rpow_mul_rpow` (`Chernoff.lean:699`), valid on the
  log-ratio band. **Pure real analysis; the plan's designated must-prove core.**
* **Step 1 (block form)** (`bayesErrorBlock_ge_exp_neg_mul_geomMean`): the same
  per-block, for the products `a := ∏ P₁(x_i)`, `b := ∏ P₂(x_i)` on the typical
  band `|∑ (log P₁(x_i) − log P₂(x_i))| ≤ n·ε`.
* `chernoffLogRatioBand` — the typical band as a `Set (Fin n → α)`.
* `bayesErrorMinPmf_ge_half_band_sum` — restricting the (nonnegative) `min`-sum
  to the band, the genuine lower-bound starting point.

## What remains genuinely open (honest load-bearing hypothesis)

The `ε`-relaxed converse needs the band's `Q^n`-mass (`Q = chernoffMediator`) to
tend to `1`, which in turn requires the **first-order optimality** of the
Chernoff exponent at the attaining `λ*`: the `Q`-mean of `log(P₁/P₂)` must be
`0` (interior optimum). `chernoffInfo_attained` (`Chernoff.lean:163`) only gives
an attaining `λ* ∈ [0,1]` via compactness — it carries **no** first-order /
interior information. Building that (convex-analytic optimality + differentiability
of `λ ↦ Z(λ)` + a Q-LLN on the band) is a substantial separate development.

It is exposed below as the **honest, load-bearing** hypothesis
`IsChernoffBandMassToOne` (type ≠ conclusion: it is the band-mass→1 input, the
conclusion is the rate bound) — *not* the circular predicate. See its docstring.

## Relation to the prior `:= h_RN` circularity

`ChernoffPerTiltSanov.chernoff_per_tilt_via_RN` (`:162`) is `:= h_RN` with
`IsChernoffNLetterRN` ≡ `IsBayesErrorPerTiltLowerBound` (name laundering /
circular). This file does **not** reuse that route: it neither produces the
false constant-`C` predicate nor renames it. The genuine pieces (step 1) stand
unconditionally; the residual is named honestly.
-/

namespace InformationTheory.Shannon.ChernoffSanovDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Real InformationTheory Filter Finset
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.ChernoffConverse
open InformationTheory.Shannon.ChernoffPerTiltDischarge
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Step 1 — reverse Hölder per-point on the log-ratio band -/

/-- **Reverse Hölder, per-point, on the log-ratio band.**

For `a, b > 0`, `λ ∈ [0,1]`, and `|log a − log b| ≤ δ`,

```
exp(-δ) · a^{1-λ} · b^λ ≤ min a b.
```

This is the exact reverse of the achievability per-point bound
`Chernoff.min_le_rpow_mul_rpow` (`min a b ≤ a^{1-λ}·b^λ`), valid whenever the
log-ratio is within the band `[-δ, δ]`. Pure real analysis; no Mathlib gap. -/
lemma min_ge_exp_neg_mul_rpow_mul_rpow
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (hband : |Real.log a - Real.log b| ≤ δ) :
    Real.exp (-δ) * (a ^ (1 - lam) * b ^ lam) ≤ min a b := by
  have hδ_nn : 0 ≤ δ := le_trans (abs_nonneg _) hband
  -- Extract the two-sided log-ratio bounds.
  have h_lo : -δ ≤ Real.log a - Real.log b := neg_le_of_abs_le hband
  have h_hi : Real.log a - Real.log b ≤ δ := le_of_abs_le hband
  -- Positivity facts.
  have ha_pow : 0 < a ^ (1 - lam) := Real.rpow_pos_of_pos ha _
  have hb_pow : 0 < b ^ lam := Real.rpow_pos_of_pos hb _
  have hG_pos : 0 < a ^ (1 - lam) * b ^ lam := mul_pos ha_pow hb_pow
  have h_one_sub_nn : 0 ≤ 1 - lam := by linarith
  -- `a = a^{1-lam}·a^lam` and `b = b^{1-lam}·b^lam`.
  have h_a_split : a ^ (1 - lam) * a ^ lam = a := by
    rw [← Real.rpow_add ha]; ring_nf; rw [Real.rpow_one]
  have h_b_split : b ^ (1 - lam) * b ^ lam = b := by
    rw [← Real.rpow_add hb]; ring_nf; rw [Real.rpow_one]
  -- It suffices to bound `exp(-δ)·G ≤ a` and `≤ b`.
  refine le_min ?_ ?_
  · -- `exp(-δ)·a^{1-lam}·b^lam ≤ a`: reduce to `exp(-δ)·b^lam ≤ a^lam`.
    have h_key : Real.exp (-δ) * b ^ lam ≤ a ^ lam := by
      have h_apow_pos : 0 < a ^ lam := Real.rpow_pos_of_pos ha _
      rw [← Real.exp_log h_apow_pos, ← Real.exp_log hb_pow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.log_rpow ha, Real.log_rpow hb]
      -- -δ + lam·log b ≤ lam·log a, i.e. -δ ≤ lam·(log a - log b)
      have hmul : -δ ≤ lam * (Real.log a - Real.log b) := by
        rcases eq_or_lt_of_le hlam_nn with h | h
        · simp [← h, hδ_nn]
        · nlinarith [mul_le_mul_of_nonneg_left h_lo hlam_nn,
            mul_nonneg hlam_nn hδ_nn]
      nlinarith [hmul]
    calc Real.exp (-δ) * (a ^ (1 - lam) * b ^ lam)
        = a ^ (1 - lam) * (Real.exp (-δ) * b ^ lam) := by ring
      _ ≤ a ^ (1 - lam) * a ^ lam := mul_le_mul_of_nonneg_left h_key ha_pow.le
      _ = a := h_a_split
  · -- `exp(-δ)·a^{1-lam}·b^lam ≤ b`: reduce to `exp(-δ)·a^{1-lam} ≤ b^{1-lam}`.
    have h_bp_pos : 0 < b ^ (1 - lam) := Real.rpow_pos_of_pos hb _
    have h_key : Real.exp (-δ) * a ^ (1 - lam) ≤ b ^ (1 - lam) := by
      rw [← Real.exp_log h_bp_pos, ← Real.exp_log ha_pow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.log_rpow hb, Real.log_rpow ha]
      -- -δ + (1-lam)·log a ≤ (1-lam)·log b, i.e. -δ ≤ (1-lam)·(log b - log a)
      have h_lo' : -δ ≤ Real.log b - Real.log a := by linarith [h_hi]
      have hmul : -δ ≤ (1 - lam) * (Real.log b - Real.log a) := by
        rcases eq_or_lt_of_le h_one_sub_nn with h | h
        · simp [← h, hδ_nn]
        · nlinarith [mul_le_mul_of_nonneg_left h_lo' h_one_sub_nn,
            mul_nonneg h_one_sub_nn hδ_nn]
      nlinarith [hmul]
    calc Real.exp (-δ) * (a ^ (1 - lam) * b ^ lam)
        = (Real.exp (-δ) * a ^ (1 - lam)) * b ^ lam := by ring
      _ ≤ b ^ (1 - lam) * b ^ lam := mul_le_mul_of_nonneg_right h_key hb_pow.le
      _ = b := h_b_split

/-! ## Step 1 — block (product) form -/

/-- The **Chernoff log-ratio band**: blocks `x : Fin n → α` whose summed
log-ratio `∑ (log P₁(x_i) − log P₂(x_i))` lies within `[-n·ε, n·ε]`. On this
band the reverse-Hölder per-block bound (with `δ = n·ε`) holds, so each `min`
term is at least `exp(-n·ε)` times the geometric-mean term. -/
noncomputable def chernoffLogRatioBand
    (P₁ P₂ : α → ℝ) (n : ℕ) (ε : ℝ) : Set (Fin n → α) :=
  { x | |∑ i : Fin n, (Real.log (P₁ (x i)) - Real.log (P₂ (x i)))| ≤ (n : ℝ) * ε }

lemma mem_chernoffLogRatioBand_iff
    (P₁ P₂ : α → ℝ) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    x ∈ chernoffLogRatioBand P₁ P₂ n ε ↔
      |∑ i : Fin n, (Real.log (P₁ (x i)) - Real.log (P₂ (x i)))| ≤ (n : ℝ) * ε :=
  Iff.rfl

/-- **Reverse Hölder, per-block, on the band.** For `x` in the band,
`exp(-n·ε) · (∏ P₁(x_i))^{1-λ} · (∏ P₂(x_i))^λ ≤ min (∏ P₁(x_i)) (∏ P₂(x_i))`. -/
lemma bayesErrorBlock_ge_exp_neg_mul_geomMean
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {n : ℕ} {ε : ℝ} {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    {x : Fin n → α} (hx : x ∈ chernoffLogRatioBand P₁ P₂ n ε) :
    Real.exp (-((n : ℝ) * ε)) *
        ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam)
      ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
  have ha : 0 < ∏ i, P₁ (x i) := Finset.prod_pos (fun i _ => hP₁_pos (x i))
  have hb : 0 < ∏ i, P₂ (x i) := Finset.prod_pos (fun i _ => hP₂_pos (x i))
  -- Translate the band condition into a log-ratio bound on the products.
  rw [mem_chernoffLogRatioBand_iff] at hx
  have h_log_prod₁ : Real.log (∏ i, P₁ (x i)) = ∑ i, Real.log (P₁ (x i)) :=
    Real.log_prod (fun i _ => (hP₁_pos (x i)).ne')
  have h_log_prod₂ : Real.log (∏ i, P₂ (x i)) = ∑ i, Real.log (P₂ (x i)) :=
    Real.log_prod (fun i _ => (hP₂_pos (x i)).ne')
  have h_band : |Real.log (∏ i, P₁ (x i)) - Real.log (∏ i, P₂ (x i))| ≤ (n : ℝ) * ε := by
    rw [h_log_prod₁, h_log_prod₂, ← Finset.sum_sub_distrib]
    exact hx
  exact min_ge_exp_neg_mul_rpow_mul_rpow ha hb hlam_nn hlam_le h_band

/-! ## Step 1 + 2 — restrict the Bayes error to the band and normalize -/

/-- The `min`-sum over the band is a lower bound for the full Bayes-error sum
(all `min` terms are nonnegative). -/
lemma bayesErrorMinPmf_ge_half_band_sum
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {n : ℕ} {ε : ℝ} :
    (1 / 2 : ℝ) * ∑ x ∈ (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset,
        min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))
      ≤ bayesErrorMinPmf P₁ P₂ n := by
  unfold bayesErrorMinPmf
  have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  apply mul_le_mul_of_nonneg_left _ h_half_nn
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro x _ _
  exact le_min (Finset.prod_nonneg (fun i _ => (hP₁_pos (x i)).le))
    (Finset.prod_nonneg (fun i _ => (hP₂_pos (x i)).le))

/-! ## Step 3 — honest load-bearing residual: band mass → 1 -/

/-- **Honest load-bearing hypothesis** (NOT a discharge; type ≠ conclusion).

The genuine `ε`-relaxed converse needs the `chernoffMediator`-product mass of the
log-ratio band to be eventually `≥ 1/2`:

```
∀ ε > 0, ∀ᶠ n, (1/2 : ℝ)
  ≤ ∑_{x ∈ band(P₁,P₂,n,ε)} ∏ i, chernoffMediator P₁ P₂ lam (x i).
```

(The `∑ ∏ chernoffMediator` is the `Q^n`-mass of the band in pmf form, bridged
to `Measure.pi` by `chernoffMediatorMeasure_pi_singleton_toReal`.) This holds at
the attaining tilt `λ*` **iff** `λ*` is a first-order-optimal (interior) Chernoff
tilt, i.e. the `Q`-mean of `log(P₁/P₂)` is `0`; then a Q-LLN concentrates the
empirical log-ratio at `0` and the band has mass → 1.

`chernoffInfo_attained` gives an attaining `λ*` by compactness only — it does
**not** supply interior/first-order optimality. Closing this requires
convex-analytic optimality of the Chernoff exponent + differentiability of
`λ ↦ Z(λ)` + a Q-LLN on the band, a substantial separate development. This is
the genuine remaining residual of the Chernoff converse; it is *not* the false
constant-`C` predicate `IsBayesErrorPerTiltLowerBound`. -/
def IsChernoffBandMassToOne (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (1 / 2 : ℝ)
      ≤ ∑ x ∈ (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset,
          ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)

/-! ## Step 2 — per-block normalization: geometric mean = `Z(λ)^n · ∏ mediator` -/

/-- **Per-block normalization** (step 2). The block geometric-mean term equals
`Z(λ)^n` times the `Fin n` product of the Chernoff mediator:

```
(∏ P₁(x_i))^{1-λ}·(∏ P₂(x_i))^λ
  = Z(λ)^n · ∏ i, chernoffMediator P₁ P₂ lam (x i).
```

`chernoffMediator a = (P₁ a^{1-λ}·P₂ a^λ)/Z(λ)`, so `∏ mediator = (geomMean)/Z^n`. -/
lemma geomMean_eq_Z_pow_mul_prod_mediator
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) {n : ℕ} (x : Fin n → α) :
    (∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam
      = (chernoffZSum P₁ P₂ lam) ^ n *
          ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i) := by
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  -- ∏ mediator = (∏ tilt factor) / Z^n.
  have h_med : ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)
      = (∏ i, (P₁ (x i)) ^ (1 - lam) * (P₂ (x i)) ^ lam)
          / (chernoffZSum P₁ P₂ lam) ^ n := by
    unfold ChernoffConverse.chernoffMediator
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_med]
  -- ∏ tilt factor = geomMean (Chernoff.prod_rpow_mul_rpow).
  rw [prod_rpow_mul_rpow P₁ P₂ (fun a => (hP₁_pos a).le) (fun a => (hP₂_pos a).le) x lam]
  -- geomMean = Z^n · (geomMean / Z^n).
  rw [mul_div_cancel₀]
  exact pow_ne_zero n hZ_pos.ne'

/-! ## Step 1+2+3 — the `ε`-relaxed per-tilt lower bound -/

/-- **`ε`-relaxed per-tilt lower bound** (genuine, modulo the honest band-mass
hypothesis): for every `ε > 0`, eventually
`exp(-n·ε) · Z(λ)^n ≤ 4 · bayesErrorMinPmf P₁ P₂ n`. -/
lemma bayesErrorMinPmf_ge_exp_neg_mul_Z_pow
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ 1)
    (h_band : IsChernoffBandMassToOne P₁ P₂ lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n
        ≤ 4 * bayesErrorMinPmf P₁ P₂ n := by
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  filter_upwards [h_band ε hε] with n hmass
  -- Abbreviations.
  set T : Finset (Fin n → α) := (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset with hT
  -- Step 1: each band term `min ≥ exp(-nε)·geomMean`.
  have h_block : ∀ x ∈ T,
      Real.exp (-((n : ℝ) * ε)) *
          ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam)
        ≤ min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    intro x hx
    have hxB : x ∈ chernoffLogRatioBand P₁ P₂ n ε := (Set.Finite.mem_toFinset _).mp hx
    exact bayesErrorBlock_ge_exp_neg_mul_geomMean P₁ P₂ hP₁_pos hP₂_pos
      hlam_nn hlam_le hxB
  -- Sum step 1 over the band, factor out the constant `exp(-nε)`.
  have h_sum_block :
      Real.exp (-((n : ℝ) * ε)) *
          ∑ x ∈ T, ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam)
        ≤ ∑ x ∈ T, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h_block
  -- Step 2: geomMean = Z^n · ∏ mediator, so the band geomMean-sum = Z^n · (band mass).
  have h_geom_sum :
      ∑ x ∈ T, ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam)
        = (chernoffZSum P₁ P₂ lam) ^ n *
            ∑ x ∈ T, ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact geomMean_eq_Z_pow_mul_prod_mediator P₁ P₂ hP₁_pos hP₂_pos lam x
  -- Step 3: band mass ≥ 1/2, so Z^n·(band mass) ≥ (1/2)·Z^n.
  have hZn_nn : (0 : ℝ) ≤ (chernoffZSum P₁ P₂ lam) ^ n := (pow_pos hZ_pos n).le
  have h_mass_ge : (chernoffZSum P₁ P₂ lam) ^ n *
        ∑ x ∈ T, ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)
      ≥ (chernoffZSum P₁ P₂ lam) ^ n * (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hmass hZn_nn
  -- Combine: exp(-nε)·Z^n·(1/2) ≤ ∑_band min ≤ 2·bayesError.
  have h_exp_nn : (0 : ℝ) ≤ Real.exp (-((n : ℝ) * ε)) := (Real.exp_pos _).le
  have h_band_sum_le :
      (1 / 2 : ℝ) * ∑ x ∈ T, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i))
        ≤ bayesErrorMinPmf P₁ P₂ n :=
    bayesErrorMinPmf_ge_half_band_sum P₁ P₂ hP₁_pos hP₂_pos
  -- Chain the inequalities.
  have h_chain :
      Real.exp (-((n : ℝ) * ε)) * ((chernoffZSum P₁ P₂ lam) ^ n * (1 / 2 : ℝ))
        ≤ ∑ x ∈ T, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := by
    calc Real.exp (-((n : ℝ) * ε)) * ((chernoffZSum P₁ P₂ lam) ^ n * (1 / 2 : ℝ))
        ≤ Real.exp (-((n : ℝ) * ε)) *
            ((chernoffZSum P₁ P₂ lam) ^ n *
              ∑ x ∈ T, ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)) :=
          mul_le_mul_of_nonneg_left h_mass_ge h_exp_nn
      _ = Real.exp (-((n : ℝ) * ε)) *
            ∑ x ∈ T, ((∏ i, P₁ (x i)) ^ (1 - lam) * (∏ i, P₂ (x i)) ^ lam) := by
          rw [h_geom_sum]
      _ ≤ ∑ x ∈ T, min (∏ i, P₁ (x i)) (∏ i, P₂ (x i)) := h_sum_block
  -- Finish: exp(-nε)·Z^n ≤ 4·bayesError.
  nlinarith [h_chain, h_band_sum_le, h_exp_nn, hZn_nn]

/-! ## Step 4 — the `ε`-relaxed converse aggregation -/

/-- **`ε`-relaxed per-tilt converse**: if for every `ε > 0` the bound
`exp(-n·ε)·Z(λ)^n ≤ 4·bayesErrorMinPmf` holds eventually, then
`limsup rate ≤ -log Z(λ)`. (The `exp(-n·ε)` factor contributes `+ε` to the rate,
which vanishes as `ε → 0`.) -/
theorem chernoff_converse_from_eps_relaxed
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ)
    (h_eps : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n
          ≤ 4 * bayesErrorMinPmf P₁ P₂ n) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ -Real.log (chernoffZSum P₁ P₂ lam) := by
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  have h_bdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) :=
    InformationTheory.Shannon.ChernoffInformation.chernoff_rate_isBoundedUnder_ge
      P₁ P₂ hP₁_pos hP₂_pos
  have h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) :=
    chernoff_rate_isBoundedUnder_le P₁ P₂ hP₁_pos hP₂_pos
  rw [Filter.limsup_le_iff h_bdd_ge.isCoboundedUnder_le h_bdd_le]
  intro b hb
  set x := -Real.log (chernoffZSum P₁ P₂ lam) with hx_def
  -- Choose `ε := (b - x)/2 > 0`.
  have hbx_pos : 0 < b - x := by linarith
  set ε := (b - x) / 2 with hε_def
  have hε_pos : 0 < ε := by simp only [hε_def]; linarith
  -- `log 4 / n → 0`, so eventually `< ε`.
  have h_log4_div : Tendsto (fun n : ℕ => Real.log 4 / (n : ℝ)) atTop (𝓝 0) := by
    have h_inv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have h_eq : (fun n : ℕ => Real.log 4 / (n : ℝ))
        = (fun n : ℕ => Real.log 4 * ((n : ℝ))⁻¹) := by
      funext n; rw [div_eq_mul_inv]
    rw [h_eq]; simpa using h_inv.const_mul (Real.log 4)
  have h_lt_eps : ∀ᶠ n : ℕ in atTop, Real.log 4 / (n : ℝ) < ε :=
    h_log4_div.eventually_lt_const hε_pos
  filter_upwards [h_eps ε hε_pos, eventually_gt_atTop 0, h_lt_eps]
    with n hn_lb hn_pos hn_lt
  have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- From hn_lb: exp(-nε)·Z^n ≤ 4·bayesError ⇒ bayesError ≥ (1/4)exp(-nε)Z^n.
  have h_bayes_pos : 0 < bayesErrorMinPmf P₁ P₂ n :=
    bayesErrorMinPmf_pos P₁ P₂ hP₁_pos hP₂_pos n
  have h_lb_pos : 0 < Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n :=
    mul_pos (Real.exp_pos _) (pow_pos hZ_pos n)
  -- log bayesError ≥ log( (1/4)·exp(-nε)·Z^n ).
  have h_quarter_le : (1 / 4 : ℝ) *
        (Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n)
      ≤ bayesErrorMinPmf P₁ P₂ n := by linarith [hn_lb]
  have h_quarter_pos : 0 < (1 / 4 : ℝ) *
      (Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n) := by
    positivity
  have h_log_ge :
      Real.log ((1 / 4 : ℝ) *
          (Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n))
        ≤ Real.log (bayesErrorMinPmf P₁ P₂ n) :=
    Real.log_le_log h_quarter_pos h_quarter_le
  -- Expand the log.
  have h_log_expand :
      Real.log ((1 / 4 : ℝ) *
          (Real.exp (-((n : ℝ) * ε)) * (chernoffZSum P₁ P₂ lam) ^ n))
        = -Real.log 4 - (n : ℝ) * ε + (n : ℝ) * Real.log (chernoffZSum P₁ P₂ lam) := by
    rw [Real.log_mul (by norm_num) (mul_pos (Real.exp_pos _) (pow_pos hZ_pos n)).ne',
      Real.log_mul (Real.exp_pos _).ne' (pow_pos hZ_pos n).ne',
      Real.log_exp, Real.log_pow]
    have h4 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    rw [h4]; ring
  rw [h_log_expand] at h_log_ge
  -- Multiply by -(1/n) ≤ 0.
  have h_neg_inv : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_mul :
      -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
        ≤ -((1 : ℝ) / n) *
            (-Real.log 4 - (n : ℝ) * ε
              + (n : ℝ) * Real.log (chernoffZSum P₁ P₂ lam)) :=
    mul_le_mul_of_nonpos_left h_log_ge h_neg_inv
  have h_simp :
      -((1 : ℝ) / n) *
          (-Real.log 4 - (n : ℝ) * ε
            + (n : ℝ) * Real.log (chernoffZSum P₁ P₂ lam))
        = Real.log 4 / n + ε + x := by
    rw [hx_def]; field_simp; ring
  rw [h_simp] at h_mul
  -- rate n ≤ log4/n + ε + x < ε + ε + x = b.
  calc -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)
      ≤ Real.log 4 / n + ε + x := h_mul
    _ < b := by rw [hε_def] at hn_lt ⊢; rw [hx_def]; linarith [hn_lt]

/-! ## Headline — the converse, modulo the honest band-mass hypothesis -/

/-- **Chernoff converse `limsup rate ≤ chernoffInfo`** at the attaining tilt,
given the honest band-mass hypothesis at that tilt.

This replaces the false constant-`C` predicate route: it requires only the
genuine load-bearing `IsChernoffBandMassToOne` (band mass → 1, ≠ the
conclusion). Step 1 (reverse Hölder) is proved unconditionally inside. -/
theorem chernoff_converse_of_bandMass
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_band : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsChernoffBandMassToOne P₁ P₂ lam) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ chernoffInfo P₁ P₂ := by
  obtain ⟨lam, hlam_mem, h_eq, h_mass⟩ := h_band
  rw [h_eq]
  refine chernoff_converse_from_eps_relaxed P₁ P₂ hP₁_pos hP₂_pos lam ?_
  intro ε hε
  exact bayesErrorMinPmf_ge_exp_neg_mul_Z_pow P₁ P₂ hP₁_pos hP₂_pos lam
    hlam_mem.1 hlam_mem.2 h_mass hε

end InformationTheory.Shannon.ChernoffSanovDischarge
