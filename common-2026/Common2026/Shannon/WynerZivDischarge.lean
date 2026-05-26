import Common2026.Meta.EntryPoint
import Common2026.Shannon.WynerZiv

/-!
# Wyner–Ziv body discharge — L-WZ3 partial plumbing (T3-D continuation)

This file publishes a **partial discharge layer** for the Wyner–Ziv body
(`WynerZiv.lean` + `WynerZivAchievability.lean` + `WynerZivConverse.lean`
were published 2026-05-19 in statement-level pass-through form). The full
body discharge of L-WZ1 (auxiliary cardinality bound), L-WZ2 (Csiszár's
sum identity), and L-WZ3 (`R_WZ(D)` convexity) is split across multiple
moonshot plans; this file targets the *most tractable* fragments of L-WZ3
plus surrounding plumbing.

## Scope

* **D-antitone of `wynerZivRatePmf`** — `D ≤ D' ⟹ R_WZ(D') ≤ R_WZ(D)`,
  the *monotone* half of L-WZ3 (convexity in `D`). Fully discharged via
  set-inclusion + `sInf` monotonicity (RD `rateDistortionFunction_antitone`
  pattern verbatim).
* **Constraint set D-monotonicity** — `D ≤ D' ⟹ Cstr(D) ⊆ Cstr(D')`,
  the elementary building block.
* **Affinity of `wzMarginalXY`** and **`wzExpectedDistortion`** in the joint
  pmf `q` — the *affine* build blocks of the (un-completed) full convexity
  proof. These hold *independently* of the Markov cross-product constraint,
  which is non-affine and blocks the full L-WZ3 discharge in the present
  scope.
* **`convex_stdSimplex` re-export** — a one-line wrapper namespaced under
  Common2026.
* **Constraint image ⊆ `stdSimplex` projection** — the natural pmf-level
  containment that suffices to derive `BddBelow` of the Wyner–Ziv objective
  image automatically (compactness of the simplex + continuity of the
  objective).
* **Wyner–Ziv objective `BddBelow`** — fully discharged via the compact-
  image route (no explicit numerical lower bound asserted).

## 撤退ライン

* **L-WZ3 full convexity** (`R_WZ(λD₁ + (1−λ)D₂) ≤ λR_WZ(D₁) + (1−λ)R_WZ(D₂)`)
  — *not discharged*. The Markov cross-product constraint
  `q(x,y,u) · Σ q(x,y',u') = q(x,y,u') · Σ q(x,y',u)` is quadratic and not
  preserved under convex combinations, so the standard "convex hull of two
  feasible points is feasible" argument breaks. The present file discharges
  only the monotone half plus build blocks; full convexity is deferred to
  `wyner-ziv-convexity-discharge-*`.
* **L-WZ1 cardinality bound** and **L-WZ2 Csiszár's sum identity** — outside
  the scope of this file.

## Notation

Throughout, `U` is the auxiliary alphabet (carried as an argument; L-WZ1
defers the cardinality bound). Variable name `qf` denotes a pair
`(q, f) : (α × β × U → ℝ) × (U × β → γ)` — the joint pmf and the decoder.
The image of the *first projection* `qf ↦ qf.1` of the constraint set is
contained in the standard simplex, which is the entry point for both the
`BddBelow` argument and the `convex_stdSimplex` re-export.

-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section ConstraintMonotone

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Constraint set is monotone in `D`.** Increasing the distortion budget
can only enlarge the set of feasible `(q, f)`-pairs: every point feasible at
the lower threshold `D` is *also* feasible at the higher threshold `D'`. -/
@[entry_point]
theorem WynerZivConstraint_mono_in_D
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D') :
    WynerZivConstraint U P_XY d D ⊆ WynerZivConstraint U P_XY d D' := by
  intro qf hqf
  rcases hqf with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, le_trans h4 hD⟩

end ConstraintMonotone

section RateAntitone

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Image-of-constraint monotonicity.** A direct consequence of
`WynerZivConstraint_mono_in_D`: the objective-image at the smaller
threshold is contained in the objective-image at the larger threshold. -/
lemma wynerZivObjective_image_mono_in_D
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D') :
    ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivConstraint U P_XY d D)
      ⊆ ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivConstraint U P_XY d D') := by
  intro v hv
  rcases hv with ⟨qf, hqf, hv_eq⟩
  exact ⟨qf, WynerZivConstraint_mono_in_D U P_XY d hD hqf, hv_eq⟩

/-- **Wyner–Ziv rate function is antitone in `D` (monotone half of L-WZ3).**

For `D ≤ D'`, if the smaller-threshold objective image is non-empty (which
is automatic in the feasible regime — any feasible `(q, f)` at `D` is also
feasible at `D'`) and the larger-threshold image is `BddBelow`, then
`wynerZivRatePmf U P_XY d D' ≤ wynerZivRatePmf U P_XY d D`.

Proof: image-of-constraint inclusion + `csInf` monotonicity. The `BddBelow`
side condition is supplied automatically in the
`wynerZivRatePmf_antitone_of_nonempty` corollary below via the simplex
projection. The non-emptiness condition is genuinely required because of
Mathlib's `Real.sInf_empty = 0` convention: without it, the inequality
`sInf (image D') ≤ sInf (image D) = 0` could fail when the smaller image is
empty and the larger one is non-empty with a negative infimum.

This is the *monotone* (D-antitone) fragment of L-WZ3 (convexity in `D`).
The full convexity statement is blocked by the non-affine Markov
cross-product constraint and is deferred. -/
@[entry_point]
theorem wynerZivRatePmf_antitone
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D')
    (h_ne : ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
              '' WynerZivConstraint U P_XY d D).Nonempty)
    (h_bdd : BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivConstraint U P_XY d D')) :
    wynerZivRatePmf U P_XY d D' ≤ wynerZivRatePmf U P_XY d D := by
  unfold wynerZivRatePmf
  refine le_csInf h_ne ?_
  rintro v hv
  have h_mem :
      v ∈ ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
            '' WynerZivConstraint U P_XY d D') :=
    wynerZivObjective_image_mono_in_D U P_XY d hD hv
  exact csInf_le h_bdd h_mem

end RateAntitone

section Affinity

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- `wzMarginalXY` is **additive** in `q`. Build block for the (deferred)
L-WZ3 full convexity proof: marginalization is a linear operation. -/
lemma wzMarginalXY_add (q₁ q₂ : α × β × U → ℝ) :
    wzMarginalXY U (q₁ + q₂) = wzMarginalXY U q₁ + wzMarginalXY U q₂ := by
  funext p
  unfold wzMarginalXY
  simp [Finset.sum_add_distrib, Pi.add_apply]

/-- `wzMarginalXY` is **homogeneous** in `q`. Build block for the (deferred)
L-WZ3 full convexity proof. -/
lemma wzMarginalXY_smul (c : ℝ) (q : α × β × U → ℝ) :
    wzMarginalXY U (c • q) = c • wzMarginalXY U q := by
  funext p
  unfold wzMarginalXY
  simp [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]

/-- `wzExpectedDistortion` (for fixed decoder `f`) is **additive** in `q`. -/
lemma wzExpectedDistortion_add (d : α → γ → ℝ) (q₁ q₂ : α × β × U → ℝ)
    (f : U × β → γ) :
    wzExpectedDistortion U d (q₁ + q₂) f
      = wzExpectedDistortion U d q₁ f + wzExpectedDistortion U d q₂ f := by
  unfold wzExpectedDistortion
  simp only [Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- `wzExpectedDistortion` (for fixed decoder `f`) is **homogeneous** in `q`. -/
lemma wzExpectedDistortion_smul (d : α → γ → ℝ) (c : ℝ)
    (q : α × β × U → ℝ) (f : U × β → γ) :
    wzExpectedDistortion U d (c • q) f = c * wzExpectedDistortion U d q f := by
  unfold wzExpectedDistortion
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]

end Affinity

section SimplexReexport

variable {α β : Type*}
variable [Fintype α] [Fintype β]
variable (U : Type*) [Fintype U]

/-- `convex_stdSimplex` re-exported for the Wyner–Ziv ambient simplex
`stdSimplex ℝ (α × β × U)`. Build block for the (deferred) full convexity
proof — the joint pmf lives in this simplex. -/
lemma convex_stdSimplex_wynerZiv :
    Convex ℝ (stdSimplex ℝ (α × β × U)) :=
  convex_stdSimplex ℝ _

end SimplexReexport

section ConstraintToSimplex

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The first projection of the Wyner–Ziv constraint set is contained in
the standard simplex on `α × β × U`. This is the natural pmf-level
containment for the joint pmf component. -/
lemma wynerZivConstraint_fst_subset_stdSimplex
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    (fun qf : (α × β × U → ℝ) × (U × β → γ) => qf.1)
        '' WynerZivConstraint U P_XY d D ⊆ stdSimplex ℝ (α × β × U) := by
  intro q hq
  rcases hq with ⟨qf, hqf, hq_eq⟩
  rw [← hq_eq]
  exact hqf.1

/-- **Wyner–Ziv objective image is `BddBelow`** — discharged via the
simplex containment + continuity of the objective. The standard simplex
is compact, so the continuous-image is bounded; passing through the
constraint set inclusion gives the result. -/
lemma wynerZivObjective_image_bddBelow
    [DecidableEq α] [DecidableEq β]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    BddBelow
      ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivConstraint U P_XY d D) := by
  -- We bound the image by `objective '' stdSimplex` which is compact (image of
  -- compact under continuous map).
  set img : Set ℝ :=
    (fun qf : (α × β × U → ℝ) × (U × β → γ) =>
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivConstraint U P_XY d D
  set img_simplex : Set ℝ :=
    (fun q : α × β × U → ℝ =>
              wzMutualInfoXU U q - wzMutualInfoYU U q)
        '' stdSimplex ℝ (α × β × U)
  have h_subset : img ⊆ img_simplex := by
    intro v hv
    rcases hv with ⟨qf, hqf, hv_eq⟩
    refine ⟨qf.1, hqf.1, ?_⟩
    exact hv_eq
  have h_simplex_compact : IsCompact (stdSimplex ℝ (α × β × U)) :=
    isCompact_stdSimplex ℝ _
  have h_cont : Continuous (fun q : α × β × U → ℝ =>
              wzMutualInfoXU U q - wzMutualInfoYU U q) :=
    continuous_wzObjective U
  have h_img_simplex_compact : IsCompact img_simplex :=
    h_simplex_compact.image h_cont
  exact h_img_simplex_compact.bddBelow.mono h_subset

/-- **D-antitone, with `BddBelow` discharged in the body.** Combines
`wynerZivRatePmf_antitone` with `wynerZivObjective_image_bddBelow` to
eliminate the `BddBelow` side condition. The non-emptiness side condition
remains: the user must supply at least one feasible `(q, f)` at the smaller
threshold `D`. -/
theorem wynerZivRatePmf_antitone_of_nonempty
    [DecidableEq α] [DecidableEq β]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D')
    (h_ne : ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
              '' WynerZivConstraint U P_XY d D).Nonempty) :
    wynerZivRatePmf U P_XY d D' ≤ wynerZivRatePmf U P_XY d D :=
  wynerZivRatePmf_antitone U P_XY d hD h_ne
    (wynerZivObjective_image_bddBelow U P_XY d D')

end ConstraintToSimplex

section FeasibilityPropagators

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Image non-emptiness from feasibility witness.** If a feasible
`(q, f) ∈ WynerZivConstraint U P_XY d D` exists, the Wyner–Ziv objective
image at `D` is non-empty. Trivial unwrapping. -/
lemma wynerZivObjective_image_nonempty_of_feasible
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    {qf : (α × β × U → ℝ) × (U × β → γ)}
    (hqf : qf ∈ WynerZivConstraint U P_XY d D) :
    ((fun qf : (α × β × U → ℝ) × (U × β → γ) =>
              wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
        '' WynerZivConstraint U P_XY d D).Nonempty :=
  ⟨wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1, qf, hqf, rfl⟩

/-- **D-antitone, final form — feasibility witness drives everything.**

Given a feasible `(q, f) ∈ WynerZivConstraint U P_XY d D` at the *smaller*
threshold `D`, the Wyner–Ziv rate is antitone: `R_WZ(D') ≤ R_WZ(D)` for any
`D' ≥ D`.

This is the user-facing form for downstream applications: callers supply
only a feasibility witness, and both the non-emptiness and the `BddBelow`
side conditions are discharged internally (via the simplex-projection
route). -/
@[entry_point]
theorem wynerZivRatePmf_antitone_of_feasible
    [DecidableEq α] [DecidableEq β]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {D D' : ℝ} (hD : D ≤ D')
    {qf : (α × β × U → ℝ) × (U × β → γ)}
    (hqf : qf ∈ WynerZivConstraint U P_XY d D) :
    wynerZivRatePmf U P_XY d D' ≤ wynerZivRatePmf U P_XY d D :=
  wynerZivRatePmf_antitone_of_nonempty U P_XY d hD
    (wynerZivObjective_image_nonempty_of_feasible U P_XY d D hqf)

end FeasibilityPropagators

section ConvexCombinationOnSimplex

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Convex combination preserves `stdSimplex` membership.** Direct
specialization of `convex_stdSimplex` to two-point combinations on the
Wyner–Ziv ambient simplex `α × β × U`. Build block for the (deferred)
full L-WZ3 convexity proof, exposing the membership form Lean tactics can
chain into. -/
lemma stdSimplex_convex_combination_mem
    {q₁ q₂ : α × β × U → ℝ}
    (hq₁ : q₁ ∈ stdSimplex ℝ (α × β × U))
    (hq₂ : q₂ ∈ stdSimplex ℝ (α × β × U))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • q₁ + b • q₂ ∈ stdSimplex ℝ (α × β × U) :=
  (convex_stdSimplex_wynerZiv (U := U)) hq₁ hq₂ ha hb hab

/-- `wzMarginalXY` is preserved under convex combinations: if both
`q₁, q₂` have `wzMarginalXY = P_XY`, then so does any convex combination.
Affinity build block for the (deferred) L-WZ3 convexity proof. -/
lemma wzMarginalXY_convex_combination
    (P_XY : α × β → ℝ) {q₁ q₂ : α × β × U → ℝ}
    (h1 : wzMarginalXY U q₁ = P_XY) (h2 : wzMarginalXY U q₂ = P_XY)
    {a b : ℝ} (hab : a + b = 1) :
    wzMarginalXY U (a • q₁ + b • q₂) = P_XY := by
  -- By additivity + homogeneity: marginal (a • q₁ + b • q₂) = a • marginal q₁ + b • marginal q₂.
  rw [wzMarginalXY_add U _ _, wzMarginalXY_smul U a _, wzMarginalXY_smul U b _, h1, h2]
  -- Goal: a • P_XY + b • P_XY = P_XY.
  funext p
  show a * P_XY p + b * P_XY p = P_XY p
  have h_factor : a * P_XY p + b * P_XY p = (a + b) * P_XY p := by ring
  rw [h_factor, hab, one_mul]

/-- `wzExpectedDistortion` (for fixed decoder `f`) is **convex-combination
linear**. Affinity build block for the (deferred) L-WZ3 convexity proof. -/
lemma wzExpectedDistortion_convex_combination
    (d : α → γ → ℝ) (q₁ q₂ : α × β × U → ℝ) (f : U × β → γ)
    {a b : ℝ} :
    wzExpectedDistortion U d (a • q₁ + b • q₂) f
      = a * wzExpectedDistortion U d q₁ f + b * wzExpectedDistortion U d q₂ f := by
  rw [wzExpectedDistortion_add U d _ _ f, wzExpectedDistortion_smul U d a q₁ f,
      wzExpectedDistortion_smul U d b q₂ f]

end ConvexCombinationOnSimplex

end InformationTheory.Shannon
