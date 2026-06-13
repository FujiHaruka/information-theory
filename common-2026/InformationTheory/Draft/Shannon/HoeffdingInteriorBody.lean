import InformationTheory.Shannon.Hoeffding.SandwichBody
import InformationTheory.Meta.EntryPoint

/-!
# Hoeffding tradeoff — interior body extension

`HoeffdingSandwichBody` discharges the boundary cases of the
`IsHoeffdingMinimizerFullSupport` predicate:

* `α = 0` — the constraint set collapses to `{P₁}` and full support is `hP₁_pos`.
* `α ≥ klDivPmf P₂ P₁` — `P₂` itself is a feasible minimizer with full support
  `hP₂_pos`.

This file extends that to the interior regime `0 < α < klDivPmf P₂ P₁`. There the textbook
proof identifies the Csiszár I-projection minimizer of `klDivPmf · P₂` over the constraint
set `K(α)` as a one-parameter exponential tilt of `P₁` (Lagrangian / KKT form):

      `Qstar a = c(λ*) * P₁ a ^ (1 - λ*) * P₂ a ^ λ*`

for some `λ* ∈ (0, 1)` chosen so that `klDivPmf Qstar P₁ = α`.

## Main definitions

* `IsHoeffdingInteriorGradient P₁ P₂ alpha` — a predicate wrapping the log-singularity
  gradient claim: no Csiszár–Pythagoras minimizer of `klDivPmf · P₂` on `K(α)` has a
  `0`-atom. It captures the directional-derivative-`= -∞` argument as a hypothesis; the
  underlying `HasDerivAt` discharge is deferred.
* `IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar` — a predicate wrapping the Lagrangian-tilt
  characterization: `Qstar` is full support and arises as the I-projection of `P₂` onto
  `K(α)`.

## Main statements

* `isHoeffdingMinimizerFullSupport_of_interior` / `isHoeffdingMinimizerFullSupport_of_gradient`
  — bridges from the interior predicates to `IsHoeffdingMinimizerFullSupport Qstar`.
* `csiszar_pythagoras_at_interior` — the Pythagorean inequality at an interior minimizer.
* `hoeffding_minimizer_ge_at_interior` — the interior minimizer is `klDivPmf · P₂`-minimal
  over `K(α)`.

## Implementation notes

Both interior pieces are bundled into `Prop`-valued predicates so callers can either supply
a direct full-support proof for a specific `Qstar`, or chain the predicates into
`IsHoeffdingMinimizerFullSupport`. `HoeffdingSandwichBody` is left unmodified; the predicates
plug into its `IsHoeffdingMinimizerFullSupport` constructor. The full `HasDerivAt`
singularity proof and the Lagrangian existence proof are deferred to a follow-up; this file
fixes their interfaces. The production path is the exponential-level `hoeffding_tradeoff_exp`
(`HoeffdingTradeoffExp`), which bypasses these predicates via an IVT + exponential-family
Pythagorean argument.
-/

namespace InformationTheory.Shannon.HoeffdingInteriorBody

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingSandwich
open InformationTheory.Shannon.HoeffdingSandwichBody
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Interior predicates -/

/-- Interior gradient predicate: at interior `α`, every Csiszár–Pythagoras minimizer `Qstar`
of `klDivPmf · P₂` on `K(α)` has full support. Wraps the deferred log-singularity argument
(the directional derivative of `klDivPmf · P₂` at a `Qstar` with `Qstar a₀ = 0` is `-∞`,
contradicting `IsMinOn`). The `Qstar` is universally quantified: the predicate is a property
of `(P₁, P₂, alpha)`, not of any specific `Qstar`.

`@audit:retract-candidate(load-bearing-predicate)` — all hypothesis-form load-bearing
consumers were retreated to body-level `sorry` + `@residual(plan:hoeffding-tradeoff-moonshot-plan)`.
One extract-only bridge `isHoeffdingMinimizerFullSupport_of_gradient` still consumes this as a
pass-through hypothesis (predicate-apply, no load-bearing claim injected). -/
def IsHoeffdingInteriorGradient
    (P₁ P₂ : α → ℝ) (alpha : ℝ) : Prop :=
  ∀ ⦃Qstar : α → ℝ⦄,
    Qstar ∈ hoeffdingConstraintSet P₁ alpha →
    hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ →
    ∀ a, 0 < Qstar a

/-- Interior minimizer predicate: `Qstar` is full support and arises as the Csiszár–Pythagoras
minimizer of `klDivPmf · P₂` on the interior constraint set `K(α)`. The Lagrangian-tilt closed
form `Qstar a ∝ P₁ a ^ (1-λ*) * P₂ a ^ λ*` is not exposed; only its consequences (membership,
infimum-realising, full support) are.

`@audit:retract-candidate(load-bearing-predicate)` — all hypothesis-form load-bearing consumers
were retreated; the remaining consumers are extract-only pass-throughs. No constructor for this
predicate remains, and the production path `hoeffding_tradeoff_exp` (sorryAx-free) bypasses it. -/
structure IsHoeffdingInteriorMinimizer
    (P₁ P₂ : α → ℝ) (alpha : ℝ) (Qstar : α → ℝ) : Prop where
  /-- `Qstar` lies in the constraint set `K(α)`. -/
  mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha
  /-- `Qstar` realises the infimum `hoeffdingE2 P₁ P₂ alpha`. -/
  realises : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂
  /-- `Qstar` is full support — directly derivable from the Lagrangian-tilt
  closed form together with `hP₁_pos`/`hP₂_pos`, but kept as an explicit field
  so the predicate is a one-stop hypothesis pass-through. -/
  full_support : ∀ a, 0 < Qstar a

/-- Trivial extractor of full support. -/
lemma IsHoeffdingInteriorMinimizer.pos
    {P₁ P₂ : α → ℝ} {alpha : ℝ} {Qstar : α → ℝ}
    (h : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar) :
    ∀ a, 0 < Qstar a := h.full_support

/-- Trivial constructor packaging the three facts. -/
lemma IsHoeffdingInteriorMinimizer.mk'
    {P₁ P₂ : α → ℝ} {alpha : ℝ} {Qstar : α → ℝ}
    (h_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (h_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂)
    (h_pos : ∀ a, 0 < Qstar a) :
    IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar :=
  { mem := h_mem
    realises := h_min
    full_support := h_pos }

/-! ## Bridge: interior predicate ⇒ full-support predicate -/

/-- From `IsHoeffdingInteriorMinimizer`, the `IsHoeffdingMinimizerFullSupport` predicate of
`HoeffdingSandwichBody` holds directly. This is the principal hand-off from the interior layer
to the sandwich-body layer. -/
@[entry_point]
lemma isHoeffdingMinimizerFullSupport_of_interior
    {P₁ P₂ : α → ℝ} {alpha : ℝ} {Qstar : α → ℝ}
    (h : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar) :
    IsHoeffdingMinimizerFullSupport Qstar :=
  IsHoeffdingMinimizerFullSupport.of_pos h.full_support

/-- Given the interior gradient predicate and a `Qstar` that lies in `K(α)` and realises the
infimum, conclude `IsHoeffdingMinimizerFullSupport`. The alternative entry point to
`isHoeffdingMinimizerFullSupport_of_interior`, for callers holding the gradient argument plus
an attained-minimizer witness. -/
@[entry_point]
lemma isHoeffdingMinimizerFullSupport_of_gradient
    {P₁ P₂ : α → ℝ} {alpha : ℝ}
    (h_grad : IsHoeffdingInteriorGradient P₁ P₂ alpha)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂) :
    IsHoeffdingMinimizerFullSupport Qstar :=
  IsHoeffdingMinimizerFullSupport.of_pos (h_grad hQs_mem hQs_min)

/-! ## Interior `IsMinOn` consequence -/

/-- From `IsHoeffdingInteriorMinimizer`, the `IsMinOn` flag that
`csiszar_pythagoras_inequality` needs, repackaged from the `hoeffdingE2 = klDivPmf Qstar P₂`
field. -/
lemma IsHoeffdingInteriorMinimizer.isMinOn
    {P₁ P₂ : α → ℝ} {alpha : ℝ} {Qstar : α → ℝ}
    (hP₂_pos : ∀ a, 0 < P₂ a)
    (h : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar) :
    IsMinOn (fun Q : α → ℝ => klDivPmf Q P₂)
      (hoeffdingConstraintSet P₁ alpha) Qstar := by
  intro Q hQ
  -- Goal: klDivPmf Qstar P₂ ≤ klDivPmf Q P₂.
  show klDivPmf Qstar P₂ ≤ klDivPmf Q P₂
  -- hoeffdingE2 ≤ klDivPmf Q P₂ since Q ∈ K (sInf ≤ any image element).
  have h_E2_le : hoeffdingE2 P₁ P₂ alpha ≤ klDivPmf Q P₂ := by
    unfold hoeffdingE2
    have h_bdd : BddBelow ((fun Q : α → ℝ => klDivPmf Q P₂) ''
        {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}) := by
      refine ⟨0, ?_⟩
      rintro y ⟨Q', hQ', rfl⟩
      exact klDivPmf_nonneg Q' P₂ hQ'.1.1 (fun a => (hP₂_pos a).le)
    have h_Q_in_img :
        klDivPmf Q P₂ ∈ (fun Q : α → ℝ => klDivPmf Q P₂) ''
            {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} :=
      ⟨Q, hQ, rfl⟩
    exact csInf_le h_bdd h_Q_in_img
  -- Then klDivPmf Qstar P₂ = hoeffdingE2 ≤ klDivPmf Q P₂.
  linarith [h.realises]

/-! ## Pythagoras at an interior minimizer -/

/-- At interior `α`, given an `IsHoeffdingInteriorMinimizer Qstar`, the Pythagorean
inequality (`csiszar_pythagoras_inequality`) holds against any other full-support
`P ∈ K(α)`. -/
@[entry_point]
theorem csiszar_pythagoras_at_interior
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} {Qstar : α → ℝ}
    (hQs_interior : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar)
    {P : α → ℝ}
    (hP_mem : P ∈ hoeffdingConstraintSet P₁ alpha)
    (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P P₂ ≥ klDivPmf P Qstar + klDivPmf Qstar P₂ :=
  csiszar_pythagoras_inequality
    (hoeffdingConstraintSet_convex P₁ hP₁_pos alpha)
    (hoeffdingConstraintSet_subset_stdSimplex P₁ alpha)
    hP₂_sum hP₂_pos hQs_interior.mem hQs_interior.full_support
    (hQs_interior.isMinOn hP₂_pos) hP_mem hP_pos

/-! ## Hypothesis-form interior result -/

/-- At interior `α`, the `hoeffding_minimizer_ge` consumer of `HoeffdingTradeoff` accepts the
interior minimizer directly without an external full-support hypothesis. -/
@[entry_point]
theorem hoeffding_minimizer_ge_at_interior
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha)
    {Qstar : α → ℝ}
    (hQs_interior : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar)
    {P : α → ℝ}
    (hP_mem : P ∈ hoeffdingConstraintSet P₁ alpha)
    (hP_pos : ∀ a, 0 < P a) :
    klDivPmf Qstar P₂ ≤ klDivPmf P P₂ :=
  hoeffding_minimizer_ge_via_predicate P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
    alpha h_alpha_nn hQs_interior.mem
    (isHoeffdingMinimizerFullSupport_of_interior hQs_interior)
    hQs_interior.realises hP_mem hP_pos

end InformationTheory.Shannon.HoeffdingInteriorBody
