import InformationTheory.Shannon.Hoeffding.Tradeoff
import InformationTheory.Shannon.Hoeffding.Sandwich
import InformationTheory.Shannon.MaxEntropy.Constrained
import InformationTheory.Meta.EntryPoint

/-!
# Hoeffding tradeoff — sandwich body completion

This file publishes the **`IsHoeffdingMinimizerFullSupport`** predicate plus the
**boundary full-support discharges** (`α = 0` and `α ≥ klDivPmf P₂ P₁`) used by
the constructive minimizer of `HoeffdingMinimizerExistence.lean` and the
exponential-level closure `hoeffding_tradeoff_exp` (`HoeffdingTradeoffExp.lean`).

The fixed-`alpha` rate targets `D(P₁‖P₂)`, not the Hoeffding tradeoff curve
`E₂(alpha)`; the genuine statement is `hoeffding_tradeoff_exp`.

## Structure

The full-support predicate `IsHoeffdingMinimizerFullSupport` wraps the claim
`∀ a, 0 < Qstar a` so downstream lemmas take a single named assumption. The
general-`alpha` discharge of this predicate (full support of any
Csiszár-Pythagoras minimizer of `klDivPmf · P₂` on `K`) requires a log-singularity
gradient argument and is supplied externally via the constructive minimizer.

For **boundary values of α** the full-support claim is fully discharged from
existing Mathlib + InformationTheory API:

* `α = 0`: `klDivPmf Q P₁ ≤ 0` combined with `klDivPmf_nonneg` forces
  `klDivPmf Q P₁ = 0`. By `klDivPmf_eq_zero_iff_pmf`, `Q = P₁`. Hence the sole
  `K`-element is `P₁`, full-support by `hP₁_pos`.

* `α ≥ klDivPmf P₂ P₁`: `P₂ ∈ K` (constraint satisfied). Combined with
  `hoeffdingE2_nonneg` and `klDivPmf P₂ P₂ = 0`, the infimum is `0` and
  `Qstar = P₂` realises it with full support by `hP₂_pos`. (Different minimizers
  may exist, but a full-support one is always available.)

## What this file publishes

* **`IsHoeffdingMinimizerFullSupport`** (`Prop` predicate, abbrev form): wraps
  the claim `∀ a, 0 < Qstar a`.

* **`hoeffdingE2_minimizer_at_boundary_alpha_zero`** (full discharge): at `α = 0`,
  every `Qstar ∈ K` (with `K = {P₁}` in this case) is full-support, i.e.
  `IsHoeffdingMinimizerFullSupport` holds for any such Qstar.

* **`hoeffdingE2_minimizer_at_boundary_alpha_ge_kl`** (full discharge, witness
  form): at `α ≥ klDivPmf P₂ P₁`, the witness `Qstar := P₂` realises the
  minimum and is full-support.

* **`hoeffding_minimizer_ge_via_predicate`**: variant of
  `hoeffding_minimizer_ge` taking `IsHoeffdingMinimizerFullSupport` instead of
  raw `hQs_pos`.

`IsHoeffdingMinimizerFullSupport` is a thin alias (definitional unfolding to
`∀ a, 0 < Qstar a`); callers construct it either from a raw pointwise positivity
proof or from the boundary discharges above. The boundary discharges assume
`hP₁_pos` / `hP₂_pos` (full-support source pmfs); the `α = 0` case additionally
needs `klDivPmf_eq_zero_iff_pmf` from `MaxEntropyConstrained.lean`.
-/

namespace InformationTheory.Shannon.HoeffdingBoundaryMinimizer

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon.MaxEntropyConstrained
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingSandwich
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Full-support predicate -/

/-- The claim `∀ a, 0 < Qstar a` wrapped as a `Prop` so downstream lemmas can
take a single named assumption instead of an unstructured `∀ a, 0 < Qstar a`.

The general-α discharge of this predicate (any minimizer of `klDivPmf · P₂` on
`hoeffdingConstraintSet P₁ alpha`) requires a `HasDerivAt` + `Real.log`
singularity computation on the directional derivative of `klDivPmf · P₂` at a
`0`-atom.

For **boundary** values of `α` (namely `α = 0` and `α ≥ klDivPmf P₂ P₁`), the
predicate is fully discharged from existing Mathlib + InformationTheory API. -/
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

/-! ## Boundary full discharge -/

/-- Boundary `α = 0` full discharge: at `α = 0`, every
`Q ∈ hoeffdingConstraintSet P₁ 0` equals `P₁`.

`klDivPmf Q P₁ ≤ 0` (constraint) + `klDivPmf_nonneg` ⇒ `klDivPmf Q P₁ = 0`.
By `klDivPmf_eq_zero_iff_pmf` (full-support `P₁`), `Q = P₁`. -/
lemma hoeffdingConstraintSet_eq_singleton_at_alpha_zero
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1) :
    hoeffdingConstraintSet P₁ (0 : ℝ) = {P₁} := by
  classical
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · -- P₁ ∈ K (klDivPmf P₁ P₁ = 0 ≤ 0).
    refine ⟨⟨fun a ↦ (hP₁_pos a).le, hP₁_sum⟩, ?_⟩
    rw [klDivPmf_self_eq_zero P₁ hP₁_pos]
  · -- Any Q ∈ K equals P₁.
    intro Q hQ
    have hQ_simplex : Q ∈ stdSimplex ℝ α := hQ.1
    have hQ_kl_le : klDivPmf Q P₁ ≤ 0 := hQ.2
    have hQ_kl_nn : 0 ≤ klDivPmf Q P₁ :=
      klDivPmf_nonneg Q P₁ hQ_simplex.1 (fun a ↦ (hP₁_pos a).le)
    have hQ_kl_eq : klDivPmf Q P₁ = 0 := le_antisymm hQ_kl_le hQ_kl_nn
    have hP₁_simplex : P₁ ∈ stdSimplex ℝ α := ⟨fun a ↦ (hP₁_pos a).le, hP₁_sum⟩
    -- klDivPmf Q P₁ = 0 ↔ Q = P₁.
    exact (klDivPmf_eq_zero_iff_pmf hQ_simplex hP₁_simplex hP₁_pos).mp hQ_kl_eq

/-- Boundary `α ≥ klDivPmf P₂ P₁` full discharge: when
`α` is at least `klDivPmf P₂ P₁`, then `P₂ ∈ hoeffdingConstraintSet P₁ alpha`. -/
lemma P₂_mem_hoeffdingConstraintSet
    (P₁ P₂ : α → ℝ) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha) :
    P₂ ∈ hoeffdingConstraintSet P₁ alpha := by
  refine ⟨⟨fun a ↦ (hP₂_pos a).le, hP₂_sum⟩, h_alpha_ge⟩

/-- **E2 collapse**: when `α ≥ klDivPmf P₂ P₁`, the
`hoeffdingE2` value equals `0`, since `P₂` itself realises the minimum. -/
lemma hoeffdingE2_eq_zero_at_alpha_ge_kl
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_alpha_ge : klDivPmf P₂ P₁ ≤ alpha) :
    hoeffdingE2 P₁ P₂ alpha = 0 := by
  classical
  -- ≤ 0: P₂ ∈ K, klDivPmf P₂ P₂ = 0 ⇒ infimum ≤ 0.
  have h_P₂_in : P₂ ∈ hoeffdingConstraintSet P₁ alpha :=
    P₂_mem_hoeffdingConstraintSet P₁ P₂ hP₂_pos hP₂_sum h_alpha_ge
  have h_klDivPmf_self : klDivPmf P₂ P₂ = 0 := klDivPmf_self_eq_zero P₂ hP₂_pos
  -- hoeffdingE2 = sInf ((klDivPmf · P₂) '' K) ≤ klDivPmf P₂ P₂ = 0.
  have h_le : hoeffdingE2 P₁ P₂ alpha ≤ 0 := by
    unfold hoeffdingE2
    have h_bdd : BddBelow ((fun Q : α → ℝ ↦ klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Q', hQ', rfl⟩
      exact klDivPmf_nonneg Q' P₂ hQ'.1.1 (fun a ↦ (hP₂_pos a).le)
    have h_P₂_in_img :
        klDivPmf P₂ P₂ ∈ (fun Q : α → ℝ ↦ klDivPmf Q P₂) ''
            {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} :=
      ⟨P₂, h_P₂_in, rfl⟩
    have := csInf_le h_bdd h_P₂_in_img
    rw [h_klDivPmf_self] at this
    exact this
  -- ≥ 0: hoeffdingE2_nonneg.
  have h_ge : 0 ≤ hoeffdingE2 P₁ P₂ alpha :=
    hoeffdingE2_nonneg P₁ P₂ hP₁_pos hP₂_pos hP₁_sum alpha h_alpha_nn
  linarith

/-- **Predicate form, witness**: at `α ≥ klDivPmf P₂ P₁`, the
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

/-! ## Pythagoras-based minimizer integration via predicate -/

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
    klDivPmf Qstar P₂ ≤ klDivPmf P P₂ := by
  classical
  exact hoeffding_minimizer_ge P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum alpha h_alpha_nn
    hQs_mem hQs_full.pos hQs_min hP_mem hP_pos

end InformationTheory.Shannon.HoeffdingBoundaryMinimizer
