import Common2026.Shannon.ChernoffPerTiltDischarge
import Common2026.Shannon.ChernoffConverse
import Common2026.Shannon.Chernoff
import Common2026.Shannon.ChernoffInformation
import Common2026.InformationTheory.Asymptotic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Real

/-!
# Chernoff per-tilt Sanov LDP body discharge — T1-B (wave7)

This file extends `Common2026/Shannon/ChernoffPerTiltDischarge.lean`
(publishing the per-tilt predicate `IsBayesErrorPerTiltLowerBound` with the
`chernoffMediatorMeasure` `Measure α` lift) by **further decomposing** the
Mathlib gap into a *named* n-letter RN-derivative predicate
`IsChernoffNLetterRN`, and publishing the pass-through reduction
`chernoff_per_tilt_via_RN`.

## Context

The Chernoff converse (Cover-Thomas Theorem 11.9.1) is reduced in
`ChernoffPerTiltDischarge.lean` to the predicate
`IsBayesErrorPerTiltLowerBound P₁ P₂ lam`:

```
∃ C > 0, ∀ᶠ n in atTop, C · Z(λ)^n ≤ 2 · bayesErrorMinPmf P₁ P₂ n
```

The textbook proof of this predicate proceeds via **Sanov LDP per-tilt**: the
tilted infinite-product measure on `α^∞` (the Chernoff mediator's product
form) is, on cylinders of width `n`, absolutely continuous w.r.t. the
un-tilted product with Radon-Nikodym derivative
`exp(λ · ∑ Y(x_i) - n · log Z(λ))` (Cover-Thomas 11.9.7-11.9.10).

This is **structurally identical** to the Cramér L-C2 Phase C Mathlib gap
`IsMeasureInfinitePiTiltedEq` (cf. `Common2026/Shannon/CramerLC2PhaseC.lean`):
both are n-letter RN-derivative identifications of an infinite-product tilt.

## What this file publishes

### Phase A — `IsChernoffNLetterRN` predicate (Mathlib gap, named)

* `IsChernoffNLetterRN P₁ P₂ lam` — predicate naming the n-letter
  Radon-Nikodym derivative identification for the Chernoff mediator. Same
  shape as `IsBayesErrorPerTiltLowerBound` but conceptually scoped as the
  *Mathlib gap*: it is the predicate the textbook proof of the Bayes-error
  lower bound would directly yield after the RN-deriv step.

### Phase B — pass-through reduction

* `chernoff_per_tilt_via_RN` — `IsChernoffNLetterRN → IsBayesErrorPerTiltLower-
  Bound`. The current implementation is **definitional**: the RN predicate is
  defined so this conversion is a refl-shape rewrite. Future work that
  refines `IsChernoffNLetterRN` to the *structural* RN-deriv statement (a
  ~500-1000 line Mathlib gap) will discharge `chernoff_per_tilt_via_RN` via
  the Sanov LDP change-of-measure step (cf. `CramerLC2PhaseC` for the
  analogous Cramér structure).

### Phase C — pi-measure plumbing on `chernoffMediatorMeasure`

* `chernoffMediatorMeasure_pi_singleton` — for the `Fin n` finite-product
  measure `Measure.pi (fun _ => chernoffMediatorMeasure P₁ P₂ lam)`, the
  singleton `{x}` evaluates to `∏ i, chernoffMediator P₁ P₂ lam (x i)`.
  This is the Sanov LDP launch lemma's `Q^n({x}) = ∏ Q.real {x_i}` analog
  for the tilted Chernoff product.
* `chernoffMediatorMeasure_pi_isProbability` — the finite-product Chernoff
  mediator measure is a probability measure.

### Phase D — final chained wrappers

* `chernoff_lemma_tendsto_via_RN` — `Tendsto rate → chernoffInfo` from
  `IsChernoffNLetterRN`-form `IsChernoffPerTiltDischargeable`. Drop-in
  alternative to `chernoff_lemma_tendsto_of_per_tilt` (🟢ʰ load-bearing in
  the per-tilt hypothesis) with the RN-deriv predicate as the *named*
  Mathlib gap input.

### Phase E — predicate roundtrip lemmas

* `isChernoffNLetterRN_iff_isBayesErrorPerTiltLowerBound` — the two
  predicates are definitionally equivalent in the current pass-through form;
  this lemma records the equivalence for downstream callers.

## Retreat lines adopted

* **L-PT2** (full Sanov LDP per-tilt RN-deriv discharge): the n-letter RN-
  derivative identification is **renamed as a separate predicate**
  `IsChernoffNLetterRN`, structurally equivalent to
  `IsBayesErrorPerTiltLowerBound` in the current pass-through form. The
  structural refinement (replacing the current Bayes-error-bound body with
  the actual RN-deriv statement on cylinder events) is deferred to a follow-
  up plan ; the current publish exposes the gap as a named predicate so
  callers can declaratively register where the gap lives.

## Design notes

* The pass-through pattern follows `CramerLC2PhaseC.lean` exactly: predicate
  + reduction + chained wrapper. The Cramér side names the gap
  `IsMeasureInfinitePiTiltedEq` and reduces it to the tilted LLN; the
  Chernoff side here names the gap `IsChernoffNLetterRN` and reduces it to
  `IsBayesErrorPerTiltLowerBound` (which downstream feeds the existing
  `chernoff_lemma_tendsto_of_per_tilt` chain).
* The `chernoffMediatorMeasure_pi_*` plumbing is independent of the Sanov
  LDP per-tilt route: it just records standard facts about the finite-product
  Chernoff mediator measure that any future Sanov LDP launch will need.
-/

namespace InformationTheory.Shannon.ChernoffPerTiltSanov

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Real InformationTheory Filter Finset MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.ChernoffConverse
open InformationTheory.Shannon.ChernoffPerTiltDischarge
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Phase A — `IsChernoffNLetterRN` predicate (Mathlib gap, named) -/

/-- **Chernoff n-letter RN-derivative predicate** (Mathlib gap, named).

Captures the n-letter Radon-Nikodym derivative identification for the
Chernoff mediator's infinite-product tilt. In the textbook Sanov LDP per-tilt
proof, this RN-deriv identification is what yields the `C · Z(λ)^n ≤ 2 ·
bayesErrorMinPmf` bound after change-of-measure on a cylinder of width `n`.

The current implementation is **pass-through** to `IsBayesErrorPerTiltLower-
Bound`: the predicate is named as the Mathlib gap, but its body is the
post-change-of-measure form. A future structural refinement (a ~500-1000
line Mathlib gap) would replace the body with the actual RN-deriv
identification on cylinder events; the pass-through conversion `chernoff_per_
tilt_via_RN` would then become non-trivial.

Cf. `CramerLC2PhaseC.IsMeasureInfinitePiTiltedEq` for the structurally
identical Cramér gap. -/
def IsChernoffNLetterRN (P₁ P₂ : α → ℝ) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n

/-- **Unfold lemma** for the n-letter RN-deriv predicate. -/
lemma isChernoffNLetterRN_iff (P₁ P₂ : α → ℝ) (lam : ℝ) :
    IsChernoffNLetterRN P₁ P₂ lam ↔
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop,
          C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n :=
  Iff.rfl

/-! ## Phase B — pass-through reduction -/

/-- **Pass-through reduction**: the n-letter RN-deriv predicate is equivalent
to the per-tilt Bayes-error lower bound.

In the current pass-through publish, the conversion is **definitional**
(both predicates share the same body). A future structural refinement of
`IsChernoffNLetterRN` would discharge this conversion via the Sanov LDP per-
tilt change-of-measure step (cf. `CramerLC2PhaseC.tilted_lower_from_predicate`
for the analogous Cramér reduction). -/
lemma chernoff_per_tilt_via_RN
    (P₁ P₂ : α → ℝ) (lam : ℝ)
    (h_RN : IsChernoffNLetterRN P₁ P₂ lam) :
    IsBayesErrorPerTiltLowerBound P₁ P₂ lam :=
  h_RN

/-- **Reverse pass-through**: `IsBayesErrorPerTiltLowerBound → IsChernoff-
NLetterRN`. The two predicates are structurally identical in the current
publish. -/
lemma isChernoffNLetterRN_of_isBayesErrorPerTiltLowerBound
    (P₁ P₂ : α → ℝ) (lam : ℝ)
    (h_pred : IsBayesErrorPerTiltLowerBound P₁ P₂ lam) :
    IsChernoffNLetterRN P₁ P₂ lam :=
  h_pred

/-- **Equivalence** between the two predicates (current pass-through publish). -/
lemma isChernoffNLetterRN_iff_isBayesErrorPerTiltLowerBound
    (P₁ P₂ : α → ℝ) (lam : ℝ) :
    IsChernoffNLetterRN P₁ P₂ lam ↔ IsBayesErrorPerTiltLowerBound P₁ P₂ lam :=
  Iff.rfl

/-! ## Phase C — `chernoffMediatorMeasure` pi-measure plumbing -/

omit [DecidableEq α] in
/-- **Pi-measure singleton evaluation** for the Chernoff mediator measure on
`Fin n`. For each tuple `x : Fin n → α`,

```
(Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) {x}
  = ∏ i, ENNReal.ofReal (chernoffMediator P₁ P₂ lam (x i)).
```

This is the Chernoff analog of the singleton evaluation `Measure.pi_singleton`
used in the Sanov LDP launch (`SanovLDPEquality.sanov_ldp_equality`'s
`h_singleton_eq`). -/
lemma chernoffMediatorMeasure_pi_singleton
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) {n : ℕ} (x : Fin n → α) :
    (Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) {x}
      = ∏ i : Fin n,
          ENNReal.ofReal (ChernoffConverse.chernoffMediator P₁ P₂ lam (x i)) := by
  classical
  haveI hpi : ∀ i : Fin n, IsProbabilityMeasure
      ((fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam) i) := fun _ =>
    chernoffMediatorMeasure_isProbabilityMeasure P₁ P₂ hP₁_pos hP₂_pos lam
  haveI hsf : ∀ i : Fin n, SigmaFinite
      ((fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam) i) := fun i =>
    haveI := hpi i; inferInstance
  rw [Measure.pi_singleton]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact chernoffMediatorMeasure_apply_singleton P₁ P₂ lam (x i)

omit [DecidableEq α] in
/-- **Pi-measure singleton evaluation in `toReal` form**. -/
lemma chernoffMediatorMeasure_pi_singleton_toReal
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) {n : ℕ} (x : Fin n → α) :
    ((Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) {x}).toReal
      = ∏ i : Fin n, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i) := by
  rw [chernoffMediatorMeasure_pi_singleton P₁ P₂ hP₁_pos hP₂_pos lam x]
  rw [ENNReal.toReal_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact ENNReal.toReal_ofReal
    (ChernoffConverse.chernoffMediator_nonneg P₁ P₂ hP₁_pos hP₂_pos lam (x i))

omit [DecidableEq α] in
/-- **Pi-measure is a probability measure** for the Chernoff mediator product. -/
instance chernoffMediatorMeasure_pi_isProbability
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {P₁ P₂ : α → ℝ} [Nonempty α]
    [Fact (∀ a, 0 < P₁ a)] [Fact (∀ a, 0 < P₂ a)]
    {lam : ℝ} {n : ℕ} :
    IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)) := by
  haveI : ∀ i : Fin n, IsProbabilityMeasure
      ((fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam) i) := fun _ =>
    chernoffMediatorMeasure_isProbabilityMeasure P₁ P₂
      (Fact.out : ∀ a, 0 < P₁ a) (Fact.out : ∀ a, 0 < P₂ a) lam
  infer_instance

/-! ## Phase D — final chained wrappers -/

/-- **Tendsto wrapper via RN-deriv predicate** at a single tilt. Given the
RN-deriv predicate `IsChernoffNLetterRN P₁ P₂ lam` at *some* `lam ∈ Icc 0 1`
attaining `chernoffInfo = -log Z(λ)`, derive
`Tendsto rate → chernoffInfo`. -/
theorem chernoff_lemma_tendsto_via_RN
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_predicate : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsChernoffNLetterRN P₁ P₂ lam) :
    Tendsto
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂)) := by
  obtain ⟨lam, hlam_mem, h_eq, h_RN⟩ := h_predicate
  have h_pred := chernoff_per_tilt_via_RN P₁ P₂ lam h_RN
  exact chernoff_lemma_tendsto_from_predicate P₁ P₂ hP₁_pos hP₂_pos
    ⟨lam, hlam_mem, h_eq, h_pred⟩

/-- **`IsChernoffPerTiltDischargeable` from RN-deriv predicate at the
attaining tilt**. -/
lemma isChernoffPerTiltDischargeable_of_RN
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_predicate : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsChernoffNLetterRN P₁ P₂ lam) :
    IsChernoffPerTiltDischargeable P₁ P₂ := by
  obtain ⟨lam, hlam_mem, h_eq, h_RN⟩ := h_predicate
  exact ⟨lam, hlam_mem, h_eq, chernoff_per_tilt_via_RN P₁ P₂ lam h_RN⟩

/-- **Limsup converse via RN-deriv predicate**: given the RN-deriv predicate
at *every* `lam ∈ Icc 0 1`, derive `limsup rate ≤ chernoffInfo`. -/
theorem chernoff_converse_via_RN_forall
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_forall : ∀ lam ∈ Set.Icc (0 : ℝ) 1, IsChernoffNLetterRN P₁ P₂ lam) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ chernoffInfo P₁ P₂ := by
  obtain ⟨lam, hlam_mem, h_eq⟩ :=
    chernoffInfo_attained P₁ P₂ hP₁_pos hP₂_pos
  have h_RN := h_forall lam hlam_mem
  have h_pred := chernoff_per_tilt_via_RN P₁ P₂ lam h_RN
  exact chernoff_converse_discharged_from_predicate P₁ P₂ hP₁_pos hP₂_pos
    ⟨lam, hlam_mem, h_eq, h_pred⟩

/-- **Tendsto via RN-deriv predicate at every tilt**. -/
theorem chernoff_lemma_tendsto_via_RN_forall
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_forall : ∀ lam ∈ Set.Icc (0 : ℝ) 1, IsChernoffNLetterRN P₁ P₂ lam) :
    Tendsto
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂)) := by
  obtain ⟨lam, hlam_mem, h_eq⟩ :=
    chernoffInfo_attained P₁ P₂ hP₁_pos hP₂_pos
  have h_RN := h_forall lam hlam_mem
  have h_pred := chernoff_per_tilt_via_RN P₁ P₂ lam h_RN
  exact chernoff_lemma_tendsto_from_predicate P₁ P₂ hP₁_pos hP₂_pos
    ⟨lam, hlam_mem, h_eq, h_pred⟩


/-- **Monotonicity in `C`**: smaller positive constants still witness the
predicate. -/
lemma isChernoffNLetterRN_of_le
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ)
    {C C' : ℝ} (hC_pos : 0 < C) (hC'_pos : 0 < C') (hC'_le : C' ≤ C)
    (h_lb : ∀ᶠ n : ℕ in atTop,
        C * (chernoffZSum P₁ P₂ lam) ^ n ≤ 2 * bayesErrorMinPmf P₁ P₂ n) :
    IsChernoffNLetterRN P₁ P₂ lam := by
  refine ⟨C', hC'_pos, ?_⟩
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  filter_upwards [h_lb] with n hn
  have hZ_pow_nn : 0 ≤ (chernoffZSum P₁ P₂ lam) ^ n := (pow_pos hZ_pos n).le
  have : C' * (chernoffZSum P₁ P₂ lam) ^ n ≤ C * (chernoffZSum P₁ P₂ lam) ^ n :=
    mul_le_mul_of_nonneg_right hC'_le hZ_pow_nn
  linarith

/-! ## Phase F — `DotEq` form discharged from RN-deriv predicate -/

open scoped InformationTheory.Asymptotic in
/-- **Cover-Thomas Theorem 11.9.1 in `DotEq` form, discharged from the
RN-deriv predicate**: the n-IID Bayesian error decays at the exponential
rate `chernoffInfo P₁ P₂`:

  `bayesErrorMinPmf P₁ P₂ n ≐ exp(-n · chernoffInfo P₁ P₂)`

given only the n-letter RN-deriv predicate `IsChernoffNLetterRN` at the
attaining tilt `λ*` (with `chernoffInfo = -log Z(λ*)`). -/
theorem chernoff_dotEq_tendsto_via_RN
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (h_predicate : ∃ lam ∈ Set.Icc (0 : ℝ) 1,
        chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) ∧
        IsChernoffNLetterRN P₁ P₂ lam) :
    (fun n : ℕ => bayesErrorMinPmf P₁ P₂ n)
      ≐ (fun n : ℕ => Real.exp (-(n : ℝ) * chernoffInfo P₁ P₂)) := by
  exact chernoff_dotEq_tendsto_of_per_tilt P₁ P₂ hP₁_pos hP₂_pos
    (isChernoffPerTiltDischargeable_of_RN P₁ P₂ hP₁_pos hP₂_pos h_predicate)

end InformationTheory.Shannon.ChernoffPerTiltSanov
