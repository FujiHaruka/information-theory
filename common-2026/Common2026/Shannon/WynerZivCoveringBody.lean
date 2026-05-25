import Common2026.Shannon.WynerZivBinningCovering

/-!
# Wyner–Ziv covering lemma body discharge (T3-D wave9 W9-S8)

This file discharges the **covering side** of the Wyner–Ziv random-binning
achievability argument (Cover–Thomas Lemma 15.8.1 / El Gamal–Kim Lemma 3.3),
refining the `IsWynerZivBinningCovering` *predicate* introduced in
`WynerZivBinningCovering.lean` (wave7) into a body that **derives the predicate
from an AEP joint-typicality probability bound**.

## What the covering lemma says

For a random codebook of rate `R₁ > I(X;U)`, the source typical set is covered
with high probability: the chosen auxiliary codeword `u^n` fails to be jointly
typical with the source `(x^n, y^n)` only with vanishing probability. In the
present abstraction (where the codebook / auxiliary RV `Us` is supplied
externally and the random source is `Ys`), this is exactly the statement that
the error event

```
E_typ = { ω | ¬ JT (Us ω, Ys ω) }
```

has small `μ`-measure. Since `E_typ` is the **complement** of the
joint-typicality event `G_typ = { ω | JT (Us ω, Ys ω) }`, the covering bound is
the *complement* of the AEP probability lower bound `μ.real G_typ ≥ 1 - ε₁`:

```
μ.real E_typ = 1 - μ.real G_typ ≤ ε₁.
```

This is the genuine measure-arithmetic content of the covering lemma — it
converts the AEP *probability* statement (already discharged in
`AEPRate.jointlyTypicalSet_prob_ge_of_rate`) into the *error-event* statement
consumed by the WZ binning composition (`wyner_ziv_binning_via_covering_packing`).

## Scope

* **`wzCoveringEvent`** — the joint-typicality "good" event
  `{ ω | JT (Us ω, Ys ω) }`, definitionally the complement of `wzError_E_typ`.
* **`wzError_E_typ_eq_compl`** — `E_typ = (G_typ)ᶜ` (definitional unfold).
* **`isWynerZivBinningCovering_of_typicalProb`** — the **covering body
  discharge**: from a probability lower bound `1 - ε₁ ≤ μ.real G_typ` (the AEP
  conclusion), measurability of `G_typ`, and `IsProbabilityMeasure μ`, conclude
  `IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT`. Pure complement arithmetic —
  this is the lemma the AEP discharge feeds into.
* **`isWynerZivBinningCovering_of_typicalProb_finite`** — finite-measure variant
  using `μ.real E_typ + μ.real G_typ = μ.real univ` directly (no probability
  normalisation), useful when the ambient measure is sub-probability.
* **`IsCoveringTypicalityHyp`** — the AEP-side hypothesis bundle (a sequence of
  probability lower bounds `n ↦ μ.real G_typ ≥ 1 - ε`), the shape produced by
  `jointlyTypicalSet_prob_ge_of_rate` with `η := ε`.
* **`IsCoveringRandomCodebookHyp`** — bookkeeping hypothesis recording the rate
  condition `R₁ > I(X;U)` under which the AEP probability bound is achievable.
* **`wzCovering_existence_of_typicalProb`** — the **asymptotic covering existence
  form**: from `IsCoveringTypicalityHyp` (∀ ε > 0, ∃ N, ∀ n ≥ N, the typical
  probability is ≥ 1 - ε) produce the asymptotic covering bound (∀ ε > 0, ∃ N,
  ∀ n ≥ N, `IsWynerZivBinningCovering R₁ ε μ ...`). This is the covering layer
  consumed by the WZ binning existence theorem.
* **`wzCovering_feed_existence`** — the bridge that combines the covering
  existence form with an externally-supplied packing existence form into the
  joint hypothesis bundle `h_asymp` consumed by
  `wyner_ziv_binning_existence_of_covering_packing`.

## 撤退ライン

* **AEP probability discharge is *not* re-proved here.** The probability lower
  bound `1 - ε₁ ≤ μ.real G_typ` is taken as a hypothesis (in predicate form
  `IsCoveringTypicalityHyp`). Its genuine discharge — three single-axis
  `typicalSet_prob_ge_of_rate` applications + Bonferroni union bound — already
  lives in `AEPRate.jointlyTypicalSet_prob_ge_of_rate`; wiring `JT` to the
  concrete `jointlyTypicalSet` is the responsibility of the codebook-construction
  seed (the abstract `JT` here is deliberately decoupled from `jointlyTypicalSet`
  so this file stays codebook-agnostic).
* **Rate condition `R₁ > I(X;U)` as bookkeeping.** `IsCoveringRandomCodebookHyp`
  carries the rate as documentation; the quantitative link between `R₁` and the
  achievable `ε(n) → 0` lives in the AEP discharge, not here.
* **Packing side is external.** The packing existence form is supplied as a
  hypothesis to `wzCovering_feed_existence`; its discharge is the sibling seed
  `WynerZivPackingBody` (random binning collision + slice cardinality).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Covering "good" event and its complement -/

section CoveringEvent

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Covering "good" event.** The set of `ω` on which the chosen auxiliary
codeword is jointly typical with the side info, i.e. the *complement* of the
covering error event `wzError_E_typ`. This is the event whose AEP probability
tends to `1` under the rate condition `R₁ > I(X;U)`. -/
def wzCoveringEvent
    {n : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop) : Set Ω :=
  { ω | JT (Us ω, Ys ω) }

/-- The covering error event is the complement of the covering "good" event. -/
lemma wzError_E_typ_eq_compl
    {n : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop) :
    wzError_E_typ (n := n) Us Ys JT
      = (wzCoveringEvent (n := n) Us Ys JT)ᶜ := by
  ext ω
  simp only [wzError_E_typ, wzCoveringEvent, Set.mem_setOf_eq, Set.mem_compl_iff]

/-- The covering "good" event is the complement of the covering error event. -/
lemma wzCoveringEvent_eq_compl
    {n : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop) :
    wzCoveringEvent (n := n) Us Ys JT
      = (wzError_E_typ (n := n) Us Ys JT)ᶜ := by
  rw [wzError_E_typ_eq_compl, compl_compl]

/-- Measurability transfer: the covering error event is measurable iff the
covering "good" event is. -/
lemma measurableSet_wzError_E_typ_iff
    {n : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop) :
    MeasurableSet (wzError_E_typ (n := n) Us Ys JT)
      ↔ MeasurableSet (wzCoveringEvent (n := n) Us Ys JT) := by
  rw [wzError_E_typ_eq_compl]
  exact MeasurableSet.compl_iff

end CoveringEvent

/-! ## Section 2 — Covering body discharge from the AEP probability bound

The genuine measure-arithmetic content of the covering lemma: convert the AEP
probability *lower* bound `1 - ε₁ ≤ μ.real G_typ` into the covering *error*
bound `μ.real E_typ ≤ ε₁`, via `μ.real (Gᶜ) = 1 - μ.real G` (probability
measure) or `μ.real E + μ.real G = μ.real univ` (finite measure).
-/

section CoveringBody

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Covering body discharge (probability-measure form).**

Given the AEP joint-typicality probability lower bound `1 - ε₁ ≤ μ.real G_typ`
and measurability of the covering "good" event, the covering predicate
`IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT` holds. The proof is pure
complement arithmetic: `μ.real E_typ = μ.real (G_typ)ᶜ = 1 - μ.real G_typ ≤ ε₁`.

This is the lemma the AEP discharge (`jointlyTypicalSet_prob_ge_of_rate` with
`η := ε₁`) feeds into to obtain the covering predicate. -/
theorem isWynerZivBinningCovering_of_typicalProb
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} {R₁ ε₁ : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (h_meas_good : MeasurableSet (wzCoveringEvent (n := n) Us Ys JT))
    (h_prob : 1 - ε₁ ≤ μ.real (wzCoveringEvent (n := n) Us Ys JT)) :
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT := by
  rw [IsWynerZivBinningCovering_def, wzError_E_typ_eq_compl]
  rw [probReal_compl_eq_one_sub h_meas_good]
  linarith

/-- **Covering body discharge (finite-measure form).**

Variant of `isWynerZivBinningCovering_of_typicalProb` for an ambient finite
(possibly sub-probability) measure, using
`μ.real E_typ + μ.real G_typ = μ.real univ` directly. The hypothesis is phrased
as `μ.real univ - ε₁ ≤ μ.real G_typ` so it specialises to the probability case
(`μ.real univ = 1`). -/
theorem isWynerZivBinningCovering_of_typicalProb_finite
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {n : ℕ} {R₁ ε₁ : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (h_meas_good : MeasurableSet (wzCoveringEvent (n := n) Us Ys JT))
    (h_prob : μ.real Set.univ - ε₁ ≤ μ.real (wzCoveringEvent (n := n) Us Ys JT)) :
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT := by
  rw [IsWynerZivBinningCovering_def, wzError_E_typ_eq_compl]
  have h_add : μ.real (wzCoveringEvent (n := n) Us Ys JT)
      + μ.real (wzCoveringEvent (n := n) Us Ys JT)ᶜ = μ.real Set.univ :=
    measureReal_add_measureReal_compl h_meas_good
  linarith

/-- **Covering body discharge from `E_typ`-measurability** (probability form).

Same as `isWynerZivBinningCovering_of_typicalProb` but taking measurability of
the *error* event `E_typ` (rather than the good event); the two are
inter-derivable via `measurableSet_wzError_E_typ_iff`. This matches the
measurability hypotheses already threaded through `WynerZivBinningCovering`. -/
theorem isWynerZivBinningCovering_of_typicalProb'
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} {R₁ ε₁ : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (h_meas_typ : MeasurableSet (wzError_E_typ (n := n) Us Ys JT))
    (h_prob : 1 - ε₁ ≤ μ.real (wzCoveringEvent (n := n) Us Ys JT)) :
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT :=
  isWynerZivBinningCovering_of_typicalProb μ Us Ys JT
    ((measurableSet_wzError_E_typ_iff Us Ys JT).mp h_meas_typ) h_prob

/-- **Monotone slack**: a stronger covering probability bound `1 - ε₁'` (with
`ε₁' ≤ ε₁`) yields the covering predicate at the looser tolerance `ε₁`. Useful
when the AEP discharge produces an `ε`-uniform bound but the binning composition
needs a specific tolerance. -/
theorem isWynerZivBinningCovering_of_typicalProb_mono
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} {R₁ ε₁ ε₁' : ℝ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (h_meas_good : MeasurableSet (wzCoveringEvent (n := n) Us Ys JT))
    (h_le : ε₁' ≤ ε₁)
    (h_prob : 1 - ε₁' ≤ μ.real (wzCoveringEvent (n := n) Us Ys JT)) :
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT :=
  (isWynerZivBinningCovering_of_typicalProb μ Us Ys JT h_meas_good h_prob).mono h_le

end CoveringBody

/-! ## Section 3 — AEP-side and rate-condition hypothesis bundles

These predicate bundles record (a) the AEP probability lower bound as an
`ε`-uniform sequence (the shape `jointlyTypicalSet_prob_ge_of_rate` produces),
and (b) the rate condition `R₁ > I(X;U)` under which it is achievable.
-/

section Hypotheses

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **AEP-side covering typicality hypothesis.**

The `ε`-uniform AEP probability bound: for every `ε > 0` there is `N` such that
for all `n ≥ N`, a codebook / side-info pair `(Us, Ys)` with measurable
"good" event exists whose joint-typicality probability is at least `1 - ε`.
This is *exactly* the conclusion shape of
`AEPRate.jointlyTypicalSet_prob_ge_of_rate` (with `η := ε`), recast for the
abstract joint-typicality predicate `JT`.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the in-family
discharge plan (`wyner-ziv-discharge-moonshot-plan`) closes its in-family
consumers; no cross-family consumer.  Phase 2.x.1 (predicate-removal
sweep) status: no remaining in-family consumer (Phase 2.x.1.c removed it
from `wzCovering_feed_asymp`); deletion is unblocked from the Wyner–Ziv
family side. -/
def IsCoveringTypicalityHyp
    (μ : Measure Ω)
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop) : Prop :=
  ∀ ε > (0 : ℝ),
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β),
        MeasurableSet (wzCoveringEvent (n := n) Us Ys (JT n))
          ∧ 1 - ε ≤ μ.real (wzCoveringEvent (n := n) Us Ys (JT n))

/-- **Rate-condition bookkeeping hypothesis.**

Records that the codebook rate `R₁` strictly exceeds the source–auxiliary
mutual information `I(X;U)` (here represented abstractly by a real `Ixu`). This
is the condition under which `IsCoveringTypicalityHyp` is achievable. The
predicate is bookkeeping only — it carries no measure-theoretic content — but
documents the information-theoretic provenance of the covering bound. -/
def IsCoveringRandomCodebookHyp (R₁ Ixu : ℝ) : Prop := Ixu < R₁

/-- Unfolding lemma for the rate condition. -/
lemma IsCoveringRandomCodebookHyp_def {R₁ Ixu : ℝ} :
    IsCoveringRandomCodebookHyp R₁ Ixu ↔ Ixu < R₁ := Iff.rfl

/-- The rate condition is monotone in the rate: raising `R₁` preserves the
strict inequality `I(X;U) < R₁`. -/
lemma IsCoveringRandomCodebookHyp.mono_rate
    {R₁ R₁' Ixu : ℝ}
    (h : IsCoveringRandomCodebookHyp R₁ Ixu) (h_le : R₁ ≤ R₁') :
    IsCoveringRandomCodebookHyp R₁' Ixu :=
  lt_of_lt_of_le h h_le

end Hypotheses

/-! ## Section 4 — Asymptotic covering existence

Combine the AEP-side hypothesis with the body discharge to produce the
asymptotic covering existence form (∀ ε > 0, ∃ N, ∀ n ≥ N, the covering
predicate holds at tolerance ε). This is the covering layer that feeds the WZ
binning existence theorem.
-/

section CoveringExistence

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Asymptotic covering existence.**

From the AEP-side hypothesis `IsCoveringTypicalityHyp` (which supplies, for each
`ε`, an `N` beyond which the joint-typicality probability is `≥ 1 - ε`), produce
the asymptotic covering bound: for every `ε > 0` there is `N` such that for all
`n ≥ N`, a codebook / side-info pair satisfying `IsWynerZivBinningCovering R₁ ε`
exists.

The body of each step is `isWynerZivBinningCovering_of_typicalProb` — the
complement arithmetic that turns the AEP probability into the covering error
bound. This is the covering side of the standard "covering + packing ⇒
achievability" pattern. -/
theorem wzCovering_existence_of_typicalProb
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R₁ : ℝ}
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop)
    (h_aep : IsCoveringTypicalityHyp μ JT) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β),
          IsWynerZivBinningCovering R₁ ε μ Us Ys (JT n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_aep ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨Us, Ys, h_meas_good, h_prob⟩ := hN n hn
  exact ⟨Us, Ys,
    isWynerZivBinningCovering_of_typicalProb μ Us Ys (JT n) h_meas_good h_prob⟩

/-- **Covering existence packaged with measurability witnesses.**

A richer existence form that, alongside the covering predicate, retains the
measurability of the covering "good" event (hence of `E_typ`) at each `n`. This
is the shape consumed by `wyner_ziv_binning_existence_of_covering_packing`,
which needs `MeasurableSet (wzError_E_typ ...)` as part of its hypothesis
bundle. -/
theorem wzCovering_existence_with_measurability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R₁ : ℝ}
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop)
    (h_aep : IsCoveringTypicalityHyp μ JT) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β),
          MeasurableSet (wzError_E_typ (n := n) Us Ys (JT n))
            ∧ IsWynerZivBinningCovering R₁ ε μ Us Ys (JT n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_aep ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨Us, Ys, h_meas_good, h_prob⟩ := hN n hn
  refine ⟨Us, Ys, ?_, ?_⟩
  · rw [measurableSet_wzError_E_typ_iff]; exact h_meas_good
  · exact isWynerZivBinningCovering_of_typicalProb μ Us Ys (JT n) h_meas_good h_prob

end CoveringExistence

/-! ## Section 5 — Feeding the WZ binning existence theorem

Combine the covering existence form (this file) with an externally-supplied
packing existence form into the joint hypothesis `h_asymp` consumed by
`wyner_ziv_binning_existence_of_covering_packing` (from
`WynerZivBinningCovering.lean`). The covering side supplies `(Us, Ys, ε₁)` with
`MeasurableSet E_typ` + `IsWynerZivBinningCovering`; the packing side supplies
`(M, f_U, f, ε₂)` with `MeasurableSet E_bin` + `MeasurableSet fail` +
`IsWynerZivBinningPacking`. Together they discharge the `h_asymp` bundle and
hence the decoder-failure-→0 conclusion.
-/

section FeedBinning

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ]

/-- **Packing existence hypothesis (external).**

The sibling-seed (`WynerZivPackingBody`) conclusion shape: for every `ε > 0`
there is `N` such that for all `n ≥ N`, given *any* covering pair `(Us, Ys)`,
a binning function `f_U`, reconstruction `f`, packing tolerance `ε₂`, and the
two remaining measurability witnesses (`E_bin`, decoder-failure) exist with the
packing predicate holding at `ε₂ ≤ ε`. We take it as a hypothesis because the
packing discharge (binning collision `1/M` + slice cardinality) is a separate
seed. -/
def IsPackingExistenceHyp
    [Nonempty γ]
    (μ : Measure Ω)
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop) : Prop :=
  ∀ ε > (0 : ℝ),
    ∃ N : ℕ, ∀ n ≥ N,
      ∀ (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β),
        ∃ (M : ℕ) (f_U : (Fin n → U) → Fin M) (f : U × β → γ) (ε₂ : ℝ),
          ε₂ ≤ ε
            ∧ MeasurableSet (wzError_E_bin (n := n) Us Ys (JT n) f_U)
            ∧ MeasurableSet { ω : Ω |
                wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                  ≠ fun i => f (Us ω i, Ys ω i) }
            ∧ IsWynerZivBinningPacking (0 : ℝ) ε₂ μ Us Ys (JT n) f_U

/-- **Covering + packing existence ⇒ `h_asymp` bundle.**

Combine the covering existence form (discharged in this file from the AEP
hypothesis) with the external packing existence form into the joint asymptotic
hypothesis `h_asymp` of `wyner_ziv_binning_existence_of_covering_packing`. The
covering side contributes `ε₁ := ε/2` and the packing side `ε₂ ≤ ε/2`, so
`ε₁ + ε₂ ≤ ε`.

Phase 1.5 (sorry-migration): body retreated to `sorry`. The two hypotheses
`h_cov` / `h_pack` are load-bearing predicate bundles (AEP-side covering
typicality + external packing existence). The previous body assembled them
into the joint `h_asymp` shape via `wzCovering_existence_with_measurability`
plus an ε-bisection trick; closure responsibility is parked on the
discharge plan rather than on the load-bearing predicates.

Phase 2.x.1 (predicate-removal sweep): the two load-bearing predicate
hypotheses (`h_cov : IsCoveringTypicalityHyp μ JT` /
`h_pack : IsPackingExistenceHyp (γ := γ) μ JT`) are removed from the
signature.  Body remains `sorry` and the same `@residual` tag applies.

Phase 2.x.4 honesty audit verdict (2026-05-25): tier 2 **honest_residual**
verified — `(μ)[IsProbabilityMeasure μ](JT)` only.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wzCovering_feed_asymp
    [Nonempty β] [Nonempty γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
          (f_U : (Fin n → U) → Fin M) (f : U × β → γ)
          (ε₁ ε₂ : ℝ),
          ε₁ + ε₂ ≤ ε
            ∧ MeasurableSet (wzError_E_typ (n := n) Us Ys (JT n))
            ∧ MeasurableSet (wzError_E_bin (n := n) Us Ys (JT n) f_U)
            ∧ MeasurableSet { ω : Ω |
                wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                  ≠ fun i => f (Us ω i, Ys ω i) }
            ∧ IsWynerZivBinningCovering (0 : ℝ) ε₁ μ Us Ys (JT n)
            ∧ IsWynerZivBinningPacking (0 : ℝ) ε₂ μ Us Ys (JT n) f_U := by
  sorry

/-- **Covering + packing existence ⇒ decoder-failure → 0.**

The end-to-end composition for this file: feed the assembled `h_asymp` bundle
(from `wzCovering_feed_asymp`) into
`wyner_ziv_binning_existence_of_covering_packing` to conclude that, under the
AEP covering hypothesis and the external packing hypothesis, the decoder failure
probability tends to `0`. This is the covering-side contribution to the
Wyner–Ziv achievability body.

Phase 2.x ripple note: this declaration depends transitively on both
`wzCovering_feed_asymp` and `wyner_ziv_binning_existence_of_covering_packing`,
both of which are now `sorry`
(`@residual(plan:wyner-ziv-discharge-moonshot-plan)`). No `@residual` tag
is attached here — the closure responsibility belongs to the upstream
declarations' `@residual` tags. -/
theorem wzCovering_decoder_fail_existence
    [Nonempty β] [Nonempty γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop)
    (h_cov : IsCoveringTypicalityHyp μ JT)
    (h_pack : IsPackingExistenceHyp (γ := γ) μ JT) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
          (f_U : (Fin n → U) → Fin M) (f : U × β → γ),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                ≠ fun i => f (Us ω i, Ys ω i) }
            ≤ ε := by
  -- Phase 2.x.1 ripple: upstream
  -- `wyner_ziv_binning_existence_of_covering_packing` had its load-bearing
  -- `h_asymp` hypothesis and rate-bookkeeping params (`R₁` / `R₂`) removed
  -- from its signature; we still discharge the constructive covering /
  -- packing existence side here (`wzCovering_feed_asymp`) but the bundled
  -- output is no longer threaded through.  Transitive `sorry` via
  -- upstream's `@residual(plan:wyner-ziv-discharge-moonshot-plan)`.
  exact wyner_ziv_binning_existence_of_covering_packing μ JT

end FeedBinning

end InformationTheory.Shannon
