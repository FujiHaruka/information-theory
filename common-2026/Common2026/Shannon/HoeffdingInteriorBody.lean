import Common2026.Shannon.HoeffdingSandwichBody

/-!
# T1-D Hoeffding tradeoff — interior body extension (L-H4-FS interior)

`HoeffdingSandwichBody.lean` (wave6 publish, 335 行) fully discharged the
**boundary** cases of the `IsHoeffdingMinimizerFullSupport` predicate (Phase 2
there, retreat **L-H4-FB**):

* `α = 0` — the constraint set collapses to `{P₁}` and full support is `hP₁_pos`.
* `α ≥ klDivPmf P₂ P₁` — `P₂` itself is a feasible minimizer with full support
  `hP₂_pos`.

This file (wave7 gap-close T1-D) extends the discharge into the **interior**
regime `0 < α < klDivPmf P₂ P₁`. In this regime the textbook proof identifies
the Csiszár I-projection minimizer of `klDivPmf · P₂` over the constraint set
`K(α)` as a one-parameter exponential tilt of `P₁` (Lagrangian / KKT form):

      `Qstar a = c(λ*) * P₁ a ^ (1 - λ*) * P₂ a ^ λ*`

for some `λ* ∈ (0, 1)` chosen so that `klDivPmf Qstar P₁ = α`. Two ingredients
are needed to publish the full-support claim in the interior:

* **Interior gradient (L-H4-FS-grad)**: the directional derivative of
  `klDivPmf · P₂` at a `0`-atom is `-∞`, hence any minimizer with a `0`-atom
  contradicts the constraint `IsMinOn`. This is a `HasDerivAt` / `Real.log`
  singularity argument (the proper rigorous Csiszár textbook step). We capture
  it as a **predicate hypothesis** here — the actual `HasDerivAt` discharge
  remains deferred per the L-H4-FS retreat.

* **Interior characterization (L-H4-FS-char)**: at any interior `α`, the
  minimizer has the exponential-tilt form above with full support inherited
  from `hP₁_pos` and `hP₂_pos`. We capture it as a **predicate hypothesis**.

## Strategy — predicate pass-through

Both pieces above are bundled into Prop-valued predicates so callers can
either:

  (a) supply a direct full-support proof for a specific Qstar (e.g. from a
      bespoke calculation in a particular α regime), or
  (b) chain the two interior predicates `IsHoeffdingInteriorGradient` /
      `IsHoeffdingInteriorMinimizer` into
      `IsHoeffdingMinimizerFullSupport` via
      `isHoeffdingMinimizerFullSupport_of_interior`.

The bridge file `HoeffdingSandwichBody.lean` is unmodified; the new predicates
plug into its `IsHoeffdingMinimizerFullSupport` constructor.

## What this file publishes

* **`IsHoeffdingInteriorGradient P₁ P₂ alpha`** — predicate wrapping the
  log-singularity gradient claim: *no Csiszar-Pythagoras minimizer of
  `klDivPmf · P₂` on `K(α)` can have a `0`-atom*.

* **`IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar`** — predicate wrapping the
  Lagrangian-tilt characterization: `Qstar` is full-support and arises as the
  unique I-projection of `P₂` onto `K(α)`.

* **`isHoeffdingMinimizerFullSupport_of_interior`** — bridge: from
  `IsHoeffdingInteriorMinimizer`, derive
  `IsHoeffdingMinimizerFullSupport Qstar` directly.

* **`hoeffdingE2_interior_minimizer_via_predicates`** — the witness form of
  the interior discharge: given the two interior predicates, produce a witness
  `Qstar` that realises `hoeffdingE2 P₁ P₂ alpha` and is full-support.

* **`hoeffding_tradeoff_sandwich_at_interior_via_predicates`** — interior
  sandwich `Tendsto` wrapper, plumbing
  `hoeffdingE2_interior_minimizer_via_predicates` into
  `hoeffding_tradeoff_sandwich_via_predicate`.

## Retreat lines (L-H4-FS)

The full `HasDerivAt` singularity proof of `IsHoeffdingInteriorGradient` and
the existence proof of `IsHoeffdingInteriorMinimizer` (Lagrangian solving) are
deferred to a follow-up. This file fixes their **interfaces** so that
downstream consumers can wire them into the sandwich pipeline today.
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

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase 1 — Interior predicates (L-H4-FS pass-through) -/

/-- **L-H4-FS interior gradient (predicate)**: at interior `α`, *every*
Csiszar-Pythagoras minimizer `Qstar` of `klDivPmf · P₂` on `K(α)` has full
support.

This wraps the deferred log-singularity gradient computation: the directional
derivative of `klDivPmf · P₂` at a `Qstar` with `Qstar a₀ = 0` is `-∞`,
contradicting `IsMinOn`. The full `HasDerivAt` discharge (~30-50 行) is
deferred per L-H4-FS.

Note the universally-quantified `Qstar`: the predicate is a property of
`(P₁, P₂, alpha)`, not of any specific Qstar. -/
def IsHoeffdingInteriorGradient
    (P₁ P₂ : α → ℝ) (alpha : ℝ) : Prop :=
  ∀ ⦃Qstar : α → ℝ⦄,
    Qstar ∈ hoeffdingConstraintSet P₁ alpha →
    hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ →
    ∀ a, 0 < Qstar a

/-- **L-H4-FS interior minimizer (predicate)**: `Qstar` is full-support and
arises as the Csiszar-Pythagoras minimizer of `klDivPmf · P₂` on the interior
constraint set `K(α)`.

The Lagrangian-tilt closed form
`Qstar a ∝ P₁ a ^ (1-λ*) * P₂ a ^ λ*` is not exposed in this predicate; only
its consequences (membership, infimum-realising, full-support) are. -/
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

/-! ## Phase 2 — Bridge: interior predicate ⇒ full-support predicate -/

/-- **Bridge (L-H4-FS interior ⇒ FS)**: from `IsHoeffdingInteriorMinimizer`,
the existing `IsHoeffdingMinimizerFullSupport` predicate (defined in
`HoeffdingSandwichBody.lean`) holds directly.

This is the principal hand-off from the wave7 interior layer to the wave6
sandwich body layer: callers who can supply
`IsHoeffdingInteriorMinimizer` (e.g. via the textbook Lagrangian construction)
get the `IsHoeffdingMinimizerFullSupport` flag immediately. -/
lemma isHoeffdingMinimizerFullSupport_of_interior
    {P₁ P₂ : α → ℝ} {alpha : ℝ} {Qstar : α → ℝ}
    (h : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar) :
    IsHoeffdingMinimizerFullSupport Qstar :=
  IsHoeffdingMinimizerFullSupport.of_pos h.full_support

/-- **Bridge (L-H4-FS gradient ⇒ FS, given attained minimizer)**: given the
interior gradient predicate and a `Qstar` that lies in `K(α)` and realises the
infimum, conclude `IsHoeffdingMinimizerFullSupport`.

This is the alternative entry point: callers with the textbook gradient
argument (via `IsHoeffdingInteriorGradient`) plus the standard
`hoeffdingE2_attained` witness directly recover the full-support flag. -/
lemma isHoeffdingMinimizerFullSupport_of_gradient
    {P₁ P₂ : α → ℝ} {alpha : ℝ}
    (h_grad : IsHoeffdingInteriorGradient P₁ P₂ alpha)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂) :
    IsHoeffdingMinimizerFullSupport Qstar :=
  IsHoeffdingMinimizerFullSupport.of_pos (h_grad hQs_mem hQs_min)

/-! ## Phase 3 — Interior witness packaged with `hoeffdingE2_attained` -/

/-- **Interior witness from gradient predicate**: given the interior gradient
predicate, the standard attained-minimum witness
(`hoeffdingE2_attained`) is automatically full-support, hence provides a
`IsHoeffdingInteriorMinimizer`.

This combines `hoeffdingE2_attained` with the gradient predicate to produce
the existence of an `IsHoeffdingInteriorMinimizer` witness without requiring
the caller to supply a Lagrangian-tilt construction. -/
theorem isHoeffdingInteriorMinimizer_of_gradient
    (P₁ P₂ : α → ℝ)
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_grad : IsHoeffdingInteriorGradient P₁ P₂ alpha) :
    ∃ Qstar, IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar := by
  obtain ⟨Qstar, hQs_mem, hQs_min⟩ :=
    hoeffdingE2_attained P₁ P₂ hP₁_pos hP₂_pos hP₁_sum alpha h_alpha_nn
  exact ⟨Qstar,
    { mem := hQs_mem
      realises := hQs_min
      full_support := h_grad hQs_mem hQs_min }⟩

/-! ## Phase 4 — Interior `IsMinOn` consequence (Pythagoras ready) -/

/-- **Interior `IsMinOn` extraction**: from `IsHoeffdingInteriorMinimizer`,
extract the `IsMinOn` flag that `csiszar_pythagoras_inequality` needs.

This is a transparent re-packaging — useful because downstream callers ask
for `IsMinOn` rather than `hoeffdingE2 = klDivPmf Qstar P₂`. -/
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

/-! ## Phase 5 — Pythagoras consumption via interior predicate -/

/-- **Pythagoras-on-interior**: at interior `α`, given an
`IsHoeffdingInteriorMinimizer Qstar`, the Pythagorean inequality
(`csiszar_pythagoras_inequality`) holds against any other
full-support `P ∈ K(α)`. -/
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

/-! ## Phase 6 — Sandwich plumbing via interior predicate -/

/-- **Sandwich at interior via interior predicate**: a variant of
`hoeffding_tradeoff_sandwich_via_predicate`
(`HoeffdingSandwichBody.lean`) where the full-support hypothesis is supplied
by an `IsHoeffdingInteriorMinimizer` rather than the more general
`IsHoeffdingMinimizerFullSupport`.

This is the most ergonomic interior entry point for callers: supply the
interior minimizer record + the two variational hypotheses, get the sandwich
`Tendsto`. -/
theorem hoeffding_tradeoff_sandwich_at_interior_via_predicate
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1)
    {Qstar : α → ℝ}
    (hQs_interior : IsHoeffdingInteriorMinimizer P₁ P₂ alpha Qstar)
    (h_liminf : (hoeffdingE2 P₁ P₂ alpha) ≤
      Filter.liminf
        (fun n : ℕ =>
          -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop)
    (h_limsup : Filter.limsup
        (fun n : ℕ =>
          -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop ≤ (hoeffdingE2 P₁ P₂ alpha)) :
    Tendsto (fun n : ℕ =>
        -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) :=
  hoeffding_tradeoff_sandwich_via_predicate P₁ P₂ hP₁_pos hP₂_pos
    hP₁_sum hP₂_sum h_alpha_nn h_alpha_lt
    hQs_interior.mem
    (isHoeffdingMinimizerFullSupport_of_interior hQs_interior)
    hQs_interior.realises h_liminf h_limsup

/-- **Sandwich at interior via gradient predicate**: alternate entry point
where the caller supplies `IsHoeffdingInteriorGradient` instead of a full
`IsHoeffdingInteriorMinimizer`. The minimizer is then constructed via
`hoeffdingE2_attained`.

The witness `Qstar` is existentially quantified in the conclusion to match
the existential interior-discharge interface. -/
theorem hoeffding_tradeoff_sandwich_at_interior_via_gradient
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < 1)
    (h_grad : IsHoeffdingInteriorGradient P₁ P₂ alpha)
    (h_liminf : (hoeffdingE2 P₁ P₂ alpha) ≤
      Filter.liminf
        (fun n : ℕ =>
          -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop)
    (h_limsup : Filter.limsup
        (fun n : ℕ =>
          -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop ≤ (hoeffdingE2 P₁ P₂ alpha)) :
    Tendsto (fun n : ℕ =>
        -((1 : ℝ) / n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) := by
  obtain ⟨Qstar, h_interior⟩ :=
    isHoeffdingInteriorMinimizer_of_gradient P₁ P₂ hP₁_pos hP₂_pos hP₁_sum
      h_alpha_nn h_grad
  exact hoeffding_tradeoff_sandwich_at_interior_via_predicate P₁ P₂
    hP₁_pos hP₂_pos hP₁_sum hP₂_sum h_alpha_nn h_alpha_lt h_interior
    h_liminf h_limsup

/-! ## Phase 7 — `hoeffdingE2` interior characterization via predicates -/

/-- **Interior infimum reached at full-support witness**: from the gradient
predicate, the infimum `hoeffdingE2 P₁ P₂ alpha` is realised at some
full-support `Qstar` lying in `K(α)`.

This packages the existence and full-support consequences as a single witness
extraction, mirroring `hoeffdingE2_minimizer_at_boundary_alpha_ge_kl`
(`HoeffdingSandwichBody.lean` Phase 2). -/
theorem hoeffdingE2_interior_minimizer_via_predicates
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_grad : IsHoeffdingInteriorGradient P₁ P₂ alpha) :
    ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha,
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ ∧
      IsHoeffdingMinimizerFullSupport Qstar := by
  obtain ⟨Qstar, h_interior⟩ :=
    isHoeffdingInteriorMinimizer_of_gradient P₁ P₂ hP₁_pos hP₂_pos hP₁_sum
      h_alpha_nn h_grad
  refine ⟨Qstar, h_interior.mem, h_interior.realises, ?_⟩
  exact isHoeffdingMinimizerFullSupport_of_interior h_interior

/-! ## Phase 8 — Hypothesis-form interior result -/

/-- **L-H4-FS interior, hypothesis-form discharge**: at interior `α`, the
`hoeffding_minimizer_ge` consumer of `HoeffdingTradeoff.lean` accepts the
interior minimizer directly without an external full-support hypothesis. -/
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
