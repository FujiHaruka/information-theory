import Common2026.Shannon.HoeffdingTradeoff
import Common2026.Shannon.HoeffdingSandwich
import Common2026.Shannon.MaxEntropyConstrained
import Common2026.Meta.EntryPoint

/-!
# T1-D Hoeffding tradeoff — sandwich body completion (residual 2 hypotheses)

This file publishes the **`IsHoeffdingMinimizerFullSupport`** predicate plus the
**boundary full-support discharges** (`α = 0` and `α ≥ klDivPmf P₂ P₁`) used by
the constructive minimizer of `HoeffdingSandwichDischarge.lean` and the genuine
exponential-level closure `hoeffding_tradeoff_exp` (`HoeffdingTradeoffExp.lean`).

## Retraction note (2026-05-28)

The fixed-`alpha` sandwich `Tendsto` wrappers `hoeffding_tradeoff_sandwich_via_predicate`
and `hoeffding_tradeoff_sandwich_at_boundary_alpha_ge_kl` that lived in this file
have been **retracted**: their `h_liminf` / `h_limsup` premises are jointly
unsatisfiable in the general fixed-`alpha` regime (the rate targets `D(P₁‖P₂)`,
not the Hoeffding tradeoff curve `E₂(alpha)`). See the retraction record in
`HoeffdingSandwichDischarge.lean`. The genuine statement is `hoeffding_tradeoff_exp`.
The full-support predicate and boundary discharges below are retained — they are
sound and feed the genuine successor.

## Context

`HoeffdingSandwich.lean` already discharged the **boundedness defaults**
(`IsBoundedUnder (· ≤ ·)` + `IsBoundedUnder (· ≥ ·)`) internally, reducing the
sandwich `Tendsto` from a **4-hypothesis** to a **2-hypothesis** form. Two further
gaps remain in the upstream pipeline:

* **Gap H1** — the **log-singularity gradient argument** for
  `hoeffdingE2_minimizer_full_support`: any Csiszar-Pythagoras minimizer of
  `klDivPmf · P₂` on `K := hoeffdingConstraintSet P₁ alpha` is full-support
  (`∀ a, 0 < Qstar a`). The textbook proof requires a `HasDerivAt` computation
  showing the directional derivative of `klDivPmf · P₂` at a `0`-atom is `-∞`,
  contradicting Qstar's minimum. ~30-50 行 deferred per L-H4.

* **Gap H2** — full minimizer support consumption: downstream `hoeffding_minimizer_ge`
  (`HoeffdingTradeoff.lean:236`) was published in **hypothesis-form** taking
  `hQs_pos : ∀ a, 0 < Qstar a` as an explicit argument; we want a flag carrying
  this so callers wire only one assumption.

## Strategy — body discharge + hypothesis pass-through

Per the L-H4 retreat lines:

* **Retreat L-H4-FS** (full support, hypothesis pass-through): we introduce the
  `IsHoeffdingMinimizerFullSupport` `Prop`-valued predicate that wraps the
  deferred `∀ a, 0 < Qstar a` claim and use it as an input to downstream lemmas.
  Discharge of the predicate itself in the **general** `alpha` regime
  requires the gradient argument and is deferred.

* **Retreat L-H4-FB** (boundary full discharge): for **boundary values of α**
  — namely `α = 0` and `α ≥ klDivPmf P₂ P₁` — we **fully discharge** the
  full-support claim from already-published Mathlib + Common2026 API:

  - `α = 0`: `klDivPmf Q P₁ ≤ 0` combined with `klDivPmf_nonneg` forces
    `klDivPmf Q P₁ = 0`. By `klDivPmf_eq_zero_iff_pmf`, `Q = P₁`. Hence the
    sole `K`-element is `P₁`, which is full-support by `hP₁_pos`.

  - `α ≥ klDivPmf P₂ P₁`: `P₂ ∈ K` (constraint satisfied). Combined with
    `hoeffdingE2_nonneg` and `klDivPmf P₂ P₂ = 0`, the infimum is `0` and
    `Qstar = P₂` realises it with full support by `hP₂_pos`. (Different
    minimizers may exist, but a full-support one is always available.)

## What this file publishes

* **`IsHoeffdingMinimizerFullSupport`** (`Prop` predicate, abbrev form): wraps
  the deferred `∀ a, 0 < Qstar a` claim.

* **`hoeffdingE2_minimizer_at_boundary_alpha_zero`** (full discharge): at `α = 0`,
  every `Qstar ∈ K` (with `K = {P₁}` in this case) is full-support, i.e.
  `IsHoeffdingMinimizerFullSupport` holds for any such Qstar.

* **`hoeffdingE2_minimizer_at_boundary_alpha_ge_kl`** (full discharge, witness
  form): at `α ≥ klDivPmf P₂ P₁`, the witness `Qstar := P₂` realises the
  minimum and is full-support.

* **`hoeffding_minimizer_ge_via_predicate`**: variant of
  `hoeffding_minimizer_ge` taking `IsHoeffdingMinimizerFullSupport` instead of
  raw `hQs_pos`.

## Retreat lines adopted

* **L-H4-FS** (hypothesis pass-through for full support): the **general** Qstar
  full-support claim (any α with general Csiszar-Pythagoras minimizer) remains
  deferred. `IsHoeffdingMinimizerFullSupport` carries the deferred assumption.

* **L-H4-FB** (boundary full discharge): both edge cases
  `α = 0` and `α ≥ klDivPmf P₂ P₁` are **fully discharged** from existing API.

## Design notes

* `IsHoeffdingMinimizerFullSupport` is intentionally a thin alias (definitional
  unfolding to `∀ a, 0 < Qstar a`). Callers can construct it either from a
  raw pointwise positivity proof or from the boundary discharges above.

* The boundary discharges assume `hP₁_pos` / `hP₂_pos` (full-support source
  pmfs). The `α = 0` case additionally needs `klDivPmf_eq_zero_iff_pmf` from
  `MaxEntropyConstrained.lean`.
-/

namespace InformationTheory.Shannon.HoeffdingSandwichBody

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon.MaxEntropyConstrained
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingSandwich
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase 1 — Full-support predicate (hypothesis pass-through, L-H4-FS) -/

/-- **L-H4-FS pass-through**: the deferred `∀ a, 0 < Qstar a` claim wrapped as a
`Prop` so downstream lemmas can take a single named assumption instead of an
unstructured `∀ a, 0 < Qstar a`.

The general-α discharge of this predicate (any minimizer of `klDivPmf · P₂` on
`hoeffdingConstraintSet P₁ alpha`) is **deferred** (L-H4): the rigorous proof
requires a `HasDerivAt` + `Real.log` singularity computation on the directional
derivative of `klDivPmf · P₂` at a `0`-atom (~30-50 行).

For **boundary** values of `α` (namely `α = 0` and `α ≥ klDivPmf P₂ P₁`), the
predicate is fully discharged from existing Mathlib + Common2026 API
(see Phase 2 below). -/
def IsHoeffdingMinimizerFullSupport (Qstar : α → ℝ) : Prop :=
  ∀ a, 0 < Qstar a

/-- Trivial direct constructor from raw pointwise positivity. -/
lemma IsHoeffdingMinimizerFullSupport.of_pos
    {Qstar : α → ℝ} (h : ∀ a, 0 < Qstar a) :
    IsHoeffdingMinimizerFullSupport Qstar := h

/-- Trivial direct destructor to raw pointwise positivity. -/
lemma IsHoeffdingMinimizerFullSupport.pos
    {Qstar : α → ℝ} (h : IsHoeffdingMinimizerFullSupport Qstar) :
    ∀ a, 0 < Qstar a := h

/-! ## Phase 2 — Boundary full discharge (L-H4-FB) -/

/-- **L-H4-FB part 1** (boundary `α = 0` full discharge): at `α = 0`, every
`Q ∈ hoeffdingConstraintSet P₁ 0` equals `P₁`.

`klDivPmf Q P₁ ≤ 0` (constraint) + `klDivPmf_nonneg` ⇒ `klDivPmf Q P₁ = 0`.
By `klDivPmf_eq_zero_iff_pmf` (full-support `P₁`), `Q = P₁`. -/
lemma hoeffdingConstraintSet_eq_singleton_at_alpha_zero
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1) :
    hoeffdingConstraintSet P₁ (0 : ℝ) = {P₁} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · -- P₁ ∈ K (klDivPmf P₁ P₁ = 0 ≤ 0).
    refine ⟨⟨fun a => (hP₁_pos a).le, hP₁_sum⟩, ?_⟩
    rw [klDivPmf_self_eq_zero P₁ hP₁_pos]
  · -- Any Q ∈ K equals P₁.
    intro Q hQ
    have hQ_simplex : Q ∈ stdSimplex ℝ α := hQ.1
    have hQ_kl_le : klDivPmf Q P₁ ≤ 0 := hQ.2
    have hQ_kl_nn : 0 ≤ klDivPmf Q P₁ :=
      klDivPmf_nonneg Q P₁ hQ_simplex.1 (fun a => (hP₁_pos a).le)
    have hQ_kl_eq : klDivPmf Q P₁ = 0 := le_antisymm hQ_kl_le hQ_kl_nn
    have hP₁_simplex : P₁ ∈ stdSimplex ℝ α := ⟨fun a => (hP₁_pos a).le, hP₁_sum⟩
    -- klDivPmf Q P₁ = 0 ↔ Q = P₁.
    exact (klDivPmf_eq_zero_iff_pmf hQ_simplex hP₁_simplex hP₁_pos).mp hQ_kl_eq

/-- **L-H4-FB part 2** (boundary `α ≥ klDivPmf P₂ P₁` full discharge): when
`α` is at least `klDivPmf P₂ P₁`, then `P₂ ∈ hoeffdingConstraintSet P₁ alpha`. -/
lemma P₂_mem_hoeffdingConstraintSet
    (P₁ P₂ : α → ℝ) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha) :
    P₂ ∈ hoeffdingConstraintSet P₁ alpha := by
  refine ⟨⟨fun a => (hP₂_pos a).le, hP₂_sum⟩, h_alpha_ge⟩

/-- **L-H4-FB part 2 (E2 collapse)**: when `α ≥ klDivPmf P₂ P₁`, the
`hoeffdingE2` value equals `0`, since `P₂` itself realises the minimum. -/
lemma hoeffdingE2_eq_zero_at_alpha_ge_kl
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha) :
    hoeffdingE2 P₁ P₂ alpha = 0 := by
  -- ≤ 0: P₂ ∈ K, klDivPmf P₂ P₂ = 0 ⇒ infimum ≤ 0.
  have h_P₂_in : P₂ ∈ hoeffdingConstraintSet P₁ alpha :=
    P₂_mem_hoeffdingConstraintSet P₁ P₂ hP₂_pos hP₂_sum h_alpha_ge
  have h_klDivPmf_self : klDivPmf P₂ P₂ = 0 := klDivPmf_self_eq_zero P₂ hP₂_pos
  -- hoeffdingE2 = sInf ((klDivPmf · P₂) '' K) ≤ klDivPmf P₂ P₂ = 0.
  have h_le : hoeffdingE2 P₁ P₂ alpha ≤ 0 := by
    unfold hoeffdingE2
    have h_bdd : BddBelow ((fun Q : α → ℝ => klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Q', hQ', rfl⟩
      exact klDivPmf_nonneg Q' P₂ hQ'.1.1 (fun a => (hP₂_pos a).le)
    have h_P₂_in_img :
        klDivPmf P₂ P₂ ∈ (fun Q : α → ℝ => klDivPmf Q P₂) ''
            {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} :=
      ⟨P₂, h_P₂_in, rfl⟩
    have := csInf_le h_bdd h_P₂_in_img
    rw [h_klDivPmf_self] at this
    exact this
  -- ≥ 0: hoeffdingE2_nonneg.
  have h_ge : 0 ≤ hoeffdingE2 P₁ P₂ alpha :=
    hoeffdingE2_nonneg P₁ P₂ hP₁_pos hP₂_pos hP₁_sum alpha h_alpha_nn
  linarith

/-- **L-H4-FB part 2 (predicate form, witness)**: at `α ≥ klDivPmf P₂ P₁`, the
witness `Qstar := P₂` lies in `K`, realises `hoeffdingE2 = klDivPmf P₂ P₂ = 0`,
and is full-support (by `hP₂_pos`). -/
lemma hoeffdingE2_minimizer_at_boundary_alpha_ge_kl
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha) :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ ∧
      IsHoeffdingMinimizerFullSupport Qstar := by
  refine ⟨P₂, ?_, ?_, ?_⟩
  · exact P₂_mem_hoeffdingConstraintSet P₁ P₂ hP₂_pos hP₂_sum h_alpha_ge
  · -- hoeffdingE2 P₁ P₂ alpha = 0 = klDivPmf P₂ P₂.
    rw [hoeffdingE2_eq_zero_at_alpha_ge_kl P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
      h_alpha_nn h_alpha_ge, klDivPmf_self_eq_zero P₂ hP₂_pos]
  · exact hP₂_pos

/-! ## Phase 3 — Pythagoras-based minimizer integration via predicate -/

/-- **`hoeffding_minimizer_ge` via predicate**: variant of
`HoeffdingTradeoff.hoeffding_minimizer_ge` taking
`IsHoeffdingMinimizerFullSupport` instead of raw `hQs_pos`. -/
@[entry_point]
lemma hoeffding_minimizer_ge_via_predicate
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_full : IsHoeffdingMinimizerFullSupport Qstar)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂)
    {P : α → ℝ}
    (hP_mem : P ∈ hoeffdingConstraintSet P₁ alpha)
    (hP_pos : ∀ a, 0 < P a) :
    klDivPmf Qstar P₂ ≤ klDivPmf P P₂ :=
  hoeffding_minimizer_ge P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum alpha h_alpha_nn
    hQs_mem hQs_full.pos hQs_min hP_mem hP_pos

end InformationTheory.Shannon.HoeffdingSandwichBody
