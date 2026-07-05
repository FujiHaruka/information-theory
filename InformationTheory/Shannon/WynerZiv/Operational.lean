import InformationTheory.Shannon.WynerZiv.Basic
import InformationTheory.Shannon.MutualInfo

/-!
# Wyner–Ziv operational achievability predicate

This file provides the operational-achievability predicate `WynerZivAchievable`
shared by the Wyner–Ziv converse and achievability legs, together with the
single-letter pmf-to-measure bridge relating the pmf-form mutual informations
`wzMutualInfoXU` / `wzMutualInfoYU` to the measure-form `mutualInfo`.

## Main definitions

* `WynerZivAchievable` — a rate `R` is achievable at distortion `D` for the
  i.i.d. source `P_XY` if there is a sequence of Wyner–Ziv block codes whose
  log-cardinality rate tends to `R` and whose expected block distortion is
  eventually within `D + ε` for every `ε > 0`.

## Main statements

* `wzMutualInfoXU_eq_mutualInfo` — the pmf-form `I(X;U)` of the joint pmf
  induced by a measure equals the measure-form `(mutualInfo μ X U).toReal`.
* `wzMutualInfoYU_eq_mutualInfo` — the analogous identity for `I(Y;U)`.

## Implementation notes

The distortion component of `WynerZivAchievable` uses the **distortion-only**
"eventually within `D + ε`" form (equivalently `limsup ≤ D`), matching the
distortion-only rate-distortion achievability/converse templates
(`rate_distortion_achievability`, `rate_distortion_converse_single_shot`); the
`WynerZivCode` structure exposes no codeword, so no error-probability component
is bundled here — error probability is an achievability-internal device deferred
to the achievability leg. The predicate is a pure existential with the two limit
conditions; no proof core is carried inside it.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ## Operational achievability predicate -/

/-- A rate `R` is Wyner–Ziv achievable at distortion `D` for the i.i.d. source
`P_XY` on `α × β` (side information `Y` at the decoder only) if there is a
sequence of Wyner–Ziv block codes `c n : WynerZivCode (M n) n α β γ` such that:

* the log-cardinality rate `log (M n) / n` tends to `R`, and
* for every `ε > 0`, the expected block distortion of `c n` is eventually
  (in `n`) within `D + ε`.

The distortion condition is the distortion-only "eventually `≤ D + ε`" form
(equivalently `limsup ≤ D`). This is a pure existential over code sequences plus
the two limit conditions; no proof content is carried in the predicate. -/
def WynerZivAchievable
    (P_XY : Measure (α × β)) (d : DistortionFn α γ) (R D : ℝ) : Prop :=
  ∃ (M : ℕ → ℕ) (_hM : ∀ n, 0 < M n) (c : ∀ n, WynerZivCode (M n) n α β γ),
    Filter.Tendsto (fun n ↦ Real.log (M n : ℝ) / n) Filter.atTop (nhds R) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε)

/-! ## pmf-to-measure bridge for the single-letter mutual informations -/

/-- The pmf-form mutual information `I(X;U)` of the joint pmf induced by a
probability measure `μ` with coordinates `X`, `Y`, `U` equals the measure-form
`(mutualInfo μ X U).toReal`.

The conclusion is stated in the `.toReal` form so it composes with the
single-letterization of the converse leg. The exact target shape may be refined
when the converse leg (P2) is written.
@residual(plan:wyner-ziv-main-plan) -/
lemma wzMutualInfoXU_eq_mutualInfo
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Uc : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable Uc) :
    wzMutualInfoXU U (fun p : α × β × U ↦
        (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {p})
      = (mutualInfo μ X Uc).toReal := by
  sorry

/-- The pmf-form mutual information `I(Y;U)` of the joint pmf induced by a
probability measure `μ` with coordinates `X`, `Y`, `U` equals the measure-form
`(mutualInfo μ Y U).toReal`.

The conclusion is stated in the `.toReal` form so it composes with the
single-letterization of the converse leg. The exact target shape may be refined
when the converse leg (P2) is written.
@residual(plan:wyner-ziv-main-plan) -/
lemma wzMutualInfoYU_eq_mutualInfo
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Uc : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable Uc) :
    wzMutualInfoYU U (fun p : α × β × U ↦
        (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {p})
      = (mutualInfo μ Y Uc).toReal := by
  sorry

end InformationTheory.Shannon
