import Common2026.Shannon.ChernoffConverse
import Common2026.Shannon.Chernoff
import Common2026.Shannon.ChernoffInformation
import Common2026.InformationTheory.Asymptotic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.Filter.IsBounded
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Real

/-!
# Chernoff per-tilt Sanov-style hypothesis discharge — T1-B follow-up

This file extends `Common2026/Shannon/ChernoffConverse.lean` (publishing
`chernoff_lemma_tendsto_from_per_tilt` with the per-tilt hypothesis remaining)
by **reducing** the per-tilt hypothesis to a more primitive Mathlib-gap
predicate `IsBayesErrorPerTiltLowerBound P₁ P₂ lam`, in direct analogy to the
Cramér L-C2 Phase C partial discharge (`Common2026/Shannon/CramerLC2PhaseC.lean`).

## Context

Cover-Thomas Theorem 11.9.1 (Chernoff bound, converse direction):

```
limsup_n -(1/n) log bayesErrorMinPmf P₁ P₂ n ≤ chernoffInfo P₁ P₂
```

The achievability side is in `Chernoff.lean` (`chernoff_lemma_achievability`),
and the converse side is reduced in `ChernoffConverse.lean` to a per-tilt
Sanov-style lower bound at the optimal tilt `λ*`:

```
∃ lam ∈ Icc 0 1, chernoffInfo = -log Z(λ) ∧
  ∃ C > 0, ∀ᶠ n, C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n
```

The full discharge of this per-tilt hypothesis goes via **Sanov LDP per-tilt**:
the tilted infinite-product measure on `α^∞` is, on cylinders of width `n`,
absolutely continuous w.r.t. the un-tilted product with Radon-Nikodym
derivative `exp(λ · ∑ Y(x_i) - n · log Z(λ))` (Cover-Thomas 11.9.7–11.9.10).
The cylinder is the typical set of the tilted ambient, on which the tilted
probability tends to 1 as `n → ∞` (a tilted LLN). Combining gives the
required `C · Z(λ)^n` lower bound on `bayesErrorMinPmf`.

The **n-letter RN-derivative identification** for the Chernoff mediating pmf
`chernoffMediator` is a Mathlib-gap construction (~500-line) of exactly the
same shape as the one Cramér L-C2 hit in `CramerLC2PhaseC.lean` (`IsMeasure-
InfinitePiTiltedEq`). This file therefore **abstracts the same gap as a
predicate** and publishes the corresponding partial discharge.

## What this file publishes

### Phase A — Mathlib-gap predicate

* `IsBayesErrorPerTiltLowerBound P₁ P₂ lam` — captures the Sanov LDP per-tilt
  output in the canonical Chernoff form. Direct interpretation:
  `∃ C > 0, ∀ᶠ n in atTop, C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n`.

### Phase B — predicate plumbing

* `isBayesErrorPerTiltLowerBound_iff` — defining unfold of the predicate.

  No "degenerate witness at lam = 0" lemma is published: the per-tilt
  bound is **asymptotic** (the constant `C` must hold for all large `n`
  while `Z(λ)^n` decays as a power), so no shape-trivial witness exists
  outside of the Sanov LDP per-tilt setting.

### Phase C — main discharged wrappers

* `chernoff_converse_from_predicate` — given a `IsBayesErrorPerTilt-
  LowerBound` predicate at a tilt `lam` with `chernoffInfo = -log Z(λ)`,
  derive `limsup rate ≤ chernoffInfo`.
* `chernoff_converse_discharged_from_predicate` — main theorem: given an
  attaining `λ* ∈ Icc 0 1` (from `chernoffInfo_attained`) together with the
  predicate at `λ*`, derive `limsup rate ≤ chernoffInfo`.
* `chernoff_lemma_tendsto_from_predicate` — sandwich `Tendsto` wrapper:
  `Tendsto rate atTop (𝓝 chernoffInfo)` given only the per-tilt predicate at
  the optimum.

### Phase D — corollary identifying the predicate with the per-tilt hypothesis

* `chernoff_per_tilt_predicate_iff_per_tilt_hypothesis` — the predicate at
  `lam` is **definitionally equivalent** to the per-tilt hypothesis used in
  `ChernoffConverse.chernoff_lemma_tendsto_from_per_tilt`.

## Retreat lines adopted

* **L-PT1** (full Sanov LDP per-tilt discharge): the n-letter RN-deriv
  identification and tilted LLN on the cylinder is **abstracted as a
  predicate** (`IsBayesErrorPerTiltLowerBound`). This is the same retreat as
  Cramér L-C2 Phase C in `CramerLC2PhaseC.lean` (`IsMeasureInfinitePiTilted-
  Eq`): the Mathlib gap is identical (n-letter RN-deriv identification of an
  infinite-product tilt). Full discharge is deferred to a follow-up plan that
  builds the n-letter RN-deriv construction (estimated 500-1000 lines).

## Design notes

* The predicate keeps the Chernoff pmf form `α → ℝ` (matching `Chernoff.lean`,
  `ChernoffConverse.lean`). A `Measure α` lift via `pmfToMeasure` is the
  natural conduit to a Sanov-LDP-style discharge but is deferred (cf. above).
* `chernoff_lemma_tendsto_from_predicate` is a thin wrapper around
  `ChernoffConverse.chernoff_lemma_tendsto_from_per_tilt`: the predicate is
  the per-tilt hypothesis in a clean, named, reusable form.
-/

namespace InformationTheory.Shannon.ChernoffPerTiltDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Real InformationTheory Filter Finset
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.ChernoffConverse
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Phase A — Mathlib-gap predicate for Sanov LDP per-tilt output -/

/-- **Sanov-style per-tilt lower bound predicate** (Mathlib-gap abstraction).

Captures the output of the (yet-to-be-formalized) Sanov LDP per-tilt change-of-
measure step for the Chernoff converse at tilt `lam ∈ Icc 0 1`:

```
∃ C > 0, ∀ᶠ n in atTop, C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n
```

This is the canonical Sanov LDP output form for the n-IID Bayes-error sum on
the tilted ambient `chernoffMediator P₁ P₂ λ`. Establishing it requires the
n-letter Radon-Nikodym derivative identification for the Chernoff mediating
pmf `chernoffMediator`, a Mathlib gap (cf. `Common2026/Shannon/CramerLC2-
PhaseC.lean` for the analogous Cramér gap `IsMeasureInfinitePiTiltedEq`). -/
def IsBayesErrorPerTiltLowerBound
    (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n

/-! ## Phase B — predicate plumbing -/

/-- **Unfold lemma** for the per-tilt lower-bound predicate. -/
lemma isBayesErrorPerTiltLowerBound_iff
    (P₁ P₂ : α → ℝ) (lam : ℝ) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam ↔
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n :=
  Iff.rfl

/-! ## Phase C — main discharged wrappers -/

/-- **Per-tilt converse from predicate**: given the Sanov-style per-tilt
lower bound predicate at a single tilt `lam ∈ Icc 0 1`, derive
`limsup rate ≤ -log Z(λ)`.

This is a thin wrapper around `ChernoffConverse.chernoff_converse_from_per_tilt`;
the predicate unfolds to exactly the per-tilt hypothesis required. -/
theorem chernoff_converse_from_predicate
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ)
    (h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ -Real.log (chernoffZSum P₁ P₂ lam) := by
  obtain ⟨C, hC_pos, h_lb⟩ := h_pred
  exact chernoff_converse_from_per_tilt P₁ P₂ hP₁_pos hP₂_pos lam C hC_pos h_lb

/-- **L-Ch1 partial discharge from predicate**: given an attaining tilt `λ*`
(from `chernoffInfo_attained`) together with the Sanov-style per-tilt lower
bound predicate at `λ*`, derive `limsup rate ≤ chernoffInfo P₁ P₂`.

This is a thin re-package of `ChernoffConverse.chernoff_converse_discharged`. -/
theorem chernoff_converse_discharged_from_predicate
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_predicate : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ chernoffInfo P₁ P₂ := by
  -- Unfold the predicate; the structure `∃ C, 0 < C ∧ ∀ᶠ n, ...` then
  -- matches `chernoff_converse_discharged`'s hypothesis shape exactly.
  obtain ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩ := h_predicate
  exact chernoff_converse_discharged P₁ P₂ hP₁_pos hP₂_pos
    ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩

/-- **Sandwich `Tendsto` from predicate** (Cover-Thomas Theorem 11.9.1).

The optimal Bayesian error rate converges to `chernoffInfo P₁ P₂` along
`atTop`, given the Sanov-style per-tilt lower bound predicate at the
attaining tilt `λ*`. Both the L-Ch1 converse and L-Ch2 boundedness
hypotheses of `ChernoffInformation.chernoff_lemma_tendsto` are discharged
internally.

This is the cleanest publish shape of Cover-Thomas Theorem 11.9.1 given the
current Mathlib state: only one explicit hypothesis (the per-tilt predicate
`IsBayesErrorPerTiltLowerBound`, itself the Mathlib-gap abstraction of the
Sanov LDP per-tilt output). -/
theorem chernoff_lemma_tendsto_from_predicate
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_predicate : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :
    Tendsto
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂)) := by
  -- The predicate unfolds to the per-tilt hypothesis of
  -- `chernoff_lemma_tendsto_from_per_tilt` definitionally.
  obtain ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩ := h_predicate
  exact chernoff_lemma_tendsto_from_per_tilt P₁ P₂ hP₁_pos hP₂_pos
    ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩

/-! ## Phase D — predicate ↔ per-tilt hypothesis -/

/-- **Predicate ↔ per-tilt hypothesis**: the `IsBayesErrorPerTiltLowerBound`
predicate is **definitionally equivalent** to the per-tilt hypothesis of
`ChernoffConverse.chernoff_lemma_tendsto_from_per_tilt`. This lemma records
the equivalence explicitly for downstream callers. -/
lemma isBayesErrorPerTiltLowerBound_iff_per_tilt_hypothesis
    (P₁ P₂ : α → ℝ) (lam : ℝ) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam ↔
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n :=
  Iff.rfl

/-! ## Phase E — chernoffInfo_attained variant -/

/-- **Predicate-form of the full per-tilt hypothesis** (combining the
attaining `λ*` with the predicate). This is the cleanest "single-hypothesis"
form for callers: package `chernoffInfo_attained` together with the predicate
into a single existential. -/
def IsChernoffPerTiltDischargeable
    (P₁ P₂ : α → ℝ) : Prop :=
  ∃ lam ∈ Set.Icc (0 : ℝ) 1,
    chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam

/-- **Unfold lemma** for `IsChernoffPerTiltDischargeable`. -/
lemma isChernoffPerTiltDischargeable_iff (P₁ P₂ : α → ℝ) :
    IsChernoffPerTiltDischargeable P₁ P₂ ↔
      ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsBayesErrorPerTiltLowerBound P₁ P₂ lam :=
  Iff.rfl

/-- **Final wrapper**: `Tendsto rate → chernoffInfo` from
`IsChernoffPerTiltDischargeable` — a **single, atomic** hypothesis. -/
theorem chernoff_lemma_tendsto_discharged
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_disch : IsChernoffPerTiltDischargeable P₁ P₂) :
    Tendsto
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂)) :=
  chernoff_lemma_tendsto_from_predicate P₁ P₂ hP₁_pos hP₂_pos h_disch

/-! ## Phase F — `DotEq` form of the discharged Chernoff lemma -/

open scoped InformationTheory.Asymptotic in
/-- **Cover-Thomas Theorem 11.9.1 in `DotEq` form, discharged from the
predicate**: the n-IID Bayesian error decays at the exponential rate
`chernoffInfo P₁ P₂`:

  `bayesErrorMinPmf P₁ P₂ n ≐ exp(-n · chernoffInfo P₁ P₂)`

given only the per-tilt predicate `IsChernoffPerTiltDischargeable P₁ P₂`.

This is derived via `chernoff_dotEq_tendsto` from `ChernoffInformation`,
combined with the two hypotheses it requires
(`h_converse` + `h_bdd_le`) — both of which are discharged here via the
predicate. -/
theorem chernoff_dotEq_tendsto_discharged
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_disch : IsChernoffPerTiltDischargeable P₁ P₂) :
    (fun n : ℕ => bayesErrorMinPmf P₁ P₂ n)
      ≐ (fun n : ℕ => Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂)) := by
  -- Discharge h_converse and h_bdd_le from the predicate.
  have h_converse :=
    chernoff_converse_discharged_from_predicate P₁ P₂ hP₁_pos hP₂_pos h_disch
  have h_bdd_le :=
    chernoff_rate_isBoundedUnder_le P₁ P₂ hP₁_pos hP₂_pos
  exact InformationTheory.Shannon.ChernoffInformation.chernoff_dotEq_tendsto
    P₁ P₂ hP₁_pos hP₂_pos h_converse h_bdd_le

/-! ## Phase G — structural lemmas on the predicate -/

/-- **Monotonicity in `C`** (smaller constants still work). If a witness `C`
makes the predicate hold and `0 < C' ≤ C`, then `C'` also witnesses it. -/
lemma isBayesErrorPerTiltLowerBound_of_le
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ)
    {C C' : ℝ} (hC_pos : 0 < C) (hC'_pos : 0 < C') (hC'_le : C' ≤ C)
    (h_lb : ∀ᶠ n : ℕ in atTop,
        C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam := by
  refine ⟨C', hC'_pos, ?_⟩
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  filter_upwards [h_lb] with n hn
  have hZ_pow_nn : 0 ≤ (chernoffZSum P₁ P₂ lam) ^ n := (pow_pos hZ_pos n).le
  have : C' * (chernoffZSum P₁ P₂ lam) ^ n ≤ C * (chernoffZSum P₁ P₂ lam) ^ n :=
    mul_le_mul_of_nonneg_right hC'_le hZ_pow_nn
  linarith

/-- **Cobounded coboundedness** for the limsup machinery. The rate sequence
`-(1/n) log bayesErrorMinPmf` is co-bounded under `(· ≤ ·)` along `atTop`,
because it is bounded above (`chernoff_rate_isBoundedUnder_le`) hence
trivially cobounded below by any finite constant — and the `IsBoundedUnder
(· ≥ ·)` discharge in `ChernoffInformation.chernoff_rate_isBoundedUnder_ge`
furnishes the `(· ≤ ·)` coboundedness via `.isCoboundedUnder_le`.

This lemma records the conversion explicitly for downstream callers. -/
lemma chernoff_rate_isCoboundedUnder_le
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) :=
  (InformationTheory.Shannon.ChernoffInformation.chernoff_rate_isBoundedUnder_ge
    P₁ P₂ hP₁_pos hP₂_pos).isCoboundedUnder_le

/-- **Cobounded form for `(· ≥ ·)` direction.** Companion to
`chernoff_rate_isCoboundedUnder_le`. -/
lemma chernoff_rate_isCoboundedUnder_ge
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) :=
  (chernoff_rate_isBoundedUnder_le P₁ P₂ hP₁_pos hP₂_pos).isCoboundedUnder_ge

/-! ## Phase H — `chernoffInfo_attained` packaging -/

/-- **Packaging helper**: given the per-tilt predicate at **every**
`lam ∈ Icc 0 1` and the `chernoffInfo_attained` existential, construct an
`IsChernoffPerTiltDischargeable`. This is the "uniform-in-λ" interface to the
discharge: a caller supplying the predicate uniformly in λ can extract the
attaining `λ*` automatically. -/
lemma isChernoffPerTiltDischargeable_of_forall
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_forall : ∀ lam ∈ Set.Icc (0 : ℝ) 1, IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :
    IsChernoffPerTiltDischargeable P₁ P₂ := by
  obtain ⟨lam, hlam_mem, h_eq⟩ :=
    chernoffInfo_attained P₁ P₂ hP₁_pos hP₂_pos
  exact ⟨lam, hlam_mem, h_eq, h_forall lam hlam_mem⟩

/-- **Specialization at the attaining tilt only**: given the predicate at the
specific `λ*` returned by `chernoffInfo_attained`, conclude
`IsChernoffPerTiltDischargeable`. -/
lemma isChernoffPerTiltDischargeable_of_attaining
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_at_some : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :
    IsChernoffPerTiltDischargeable P₁ P₂ :=
  h_at_some

/-! ## Phase I — round-trip lemmas: predicate ↔ per-tilt hypothesis in the
parent ChernoffConverse form -/

/-- **Round-trip from `ChernoffConverse.chernoff_lemma_tendsto_from_per_tilt`
hypothesis form**: given the parent's per-tilt hypothesis form, extract the
`IsChernoffPerTiltDischargeable` form. (Used to switch interface forms.) -/
lemma isChernoffPerTiltDischargeable_of_per_tilt_hypothesis
    (P₁ P₂ : α → ℝ)
    (h_per_tilt : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n) :
    IsChernoffPerTiltDischargeable P₁ P₂ := by
  obtain ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩ := h_per_tilt
  exact ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩

/-- **Round-trip to the parent hypothesis form**: going the other direction. -/
lemma per_tilt_hypothesis_of_isChernoffPerTiltDischargeable
    (P₁ P₂ : α → ℝ)
    (h_disch : IsChernoffPerTiltDischargeable P₁ P₂) :
    ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n := by
  obtain ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩ := h_disch
  exact ⟨lam, hlam_mem, h_eq, C, hC_pos, h_lb⟩

/-! ## Phase J — `chernoffMediator` `Measure α` lift (Sanov LDP launch target) -/

/-- **Chernoff mediator as a `Measure α`** (Sanov LDP launch target).

Lift of `ChernoffConverse.chernoffMediator P₁ P₂ lam : α → ℝ` to the natural
probability measure on `α` (with `[MeasurableSpace α]` and
`[MeasurableSingletonClass α]` instances). The Sanov LDP per-tilt route would
launch its tilted infinite product `Measure.infinitePi (fun _ : ℕ =>
chernoffMediatorMeasure P₁ P₂ lam)` and convert back to the un-tilted product
via the n-letter Radon-Nikodym derivative identification (the Mathlib gap
captured in `IsBayesErrorPerTiltLowerBound`). -/
noncomputable def chernoffMediatorMeasure
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P₁ P₂ : α → ℝ) (lam : ℝ) : MeasureTheory.Measure α :=
  ∑ a : α, ENNReal.ofReal (ChernoffConverse.chernoffMediator P₁ P₂ lam a) •
    MeasureTheory.Measure.dirac a

/-- **Atom evaluation** for the chernoff mediator measure on a singleton. -/
lemma chernoffMediatorMeasure_apply_singleton
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P₁ P₂ : α → ℝ) (lam : ℝ) (a : α) :
    (chernoffMediatorMeasure P₁ P₂ lam) ({a} : Set α)
      = ENNReal.ofReal (ChernoffConverse.chernoffMediator P₁ P₂ lam a) := by
  classical
  unfold chernoffMediatorMeasure
  rw [MeasureTheory.Measure.finsetSum_apply Finset.univ _ {a}]
  rw [Finset.sum_eq_single a]
  · simp [MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.singleton a)]
  · intro b _ hb
    simp [MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.dirac_apply' _ (MeasurableSet.singleton a),
      Set.indicator_of_notMem
        (show b ∉ ({a} : Set α) by simp [Set.mem_singleton_iff]; exact hb)]
  · intro h
    exact (h (Finset.mem_univ a)).elim

/-- **The chernoff mediator measure is a probability measure** under full
support `P₁, P₂ > 0`. -/
lemma chernoffMediatorMeasure_isProbabilityMeasure
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) :
    MeasureTheory.IsProbabilityMeasure (chernoffMediatorMeasure P₁ P₂ lam) := by
  refine ⟨?_⟩
  unfold chernoffMediatorMeasure
  rw [MeasureTheory.Measure.finsetSum_apply Finset.univ _ Set.univ]
  have h_each : ∀ a ∈ (Finset.univ : Finset α),
      (ENNReal.ofReal (ChernoffConverse.chernoffMediator P₁ P₂ lam a) •
          MeasureTheory.Measure.dirac a) (Set.univ : Set α)
        = ENNReal.ofReal (ChernoffConverse.chernoffMediator P₁ P₂ lam a) := by
    intro a _
    simp [MeasureTheory.Measure.smul_apply]
  rw [Finset.sum_congr rfl h_each]
  have hnn : ∀ a, 0 ≤ ChernoffConverse.chernoffMediator P₁ P₂ lam a :=
    ChernoffConverse.chernoffMediator_nonneg P₁ P₂ hP₁_pos hP₂_pos lam
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnn a)]
  rw [ChernoffConverse.chernoffMediator_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam,
      ENNReal.ofReal_one]

/-- **`.real` form of atom evaluation** for chernoff mediator measure. -/
lemma chernoffMediatorMeasure_real_singleton
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (a : α) :
    (chernoffMediatorMeasure P₁ P₂ lam).real ({a} : Set α)
      = ChernoffConverse.chernoffMediator P₁ P₂ lam a := by
  unfold MeasureTheory.Measure.real
  rw [chernoffMediatorMeasure_apply_singleton]
  exact ENNReal.toReal_ofReal
    ((chernoffMediator_nonneg P₁ P₂ hP₁_pos hP₂_pos lam a))

end InformationTheory.Shannon.ChernoffPerTiltDischarge
