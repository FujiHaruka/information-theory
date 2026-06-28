import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Basic

/-!
# Multiple access channel — three-way jointly typical set

The three-way jointly typical set for a two-user MAC, following the single-user
`InformationTheory.Shannon.ChannelCoding.jointlyTypicalSet` conventions
(Cover–Thomas §15.3.1).

## Design

The single-user typical set `InformationTheory.Shannon.typicalSet` is an
*entropy*-typicality set (empirical entropy within `ε` of the true entropy), not a
strong / letter-typicality set.  Consequently a three-way `(X₁, X₂, Y)`-joint-typical
triple does **not** by itself entail any of the pairwise-typical facts (e.g.
`(X₂, Y)`-pair-typical).  The achievability error analysis needs those pairwise facts to
bound the conditional-fibre masses, so `macJointlyTypicalSet` is defined as the
intersection of **all** the single-axis, pairwise, and three-way typicality conditions.

This shape makes each of the three "one user uses a wrong codeword" reductions a
syntactic instance of the single-user jointly-typical set under regrouping:

* user 1 wrong: `X₁ ⟂ (X₂, Y)` reduces to `jointlyTypicalSet μ X₁s (jointSequence X₂s Ys)`,
* user 2 wrong: `X₂ ⟂ (X₁, Y)` reduces to `jointlyTypicalSet μ X₂s (jointSequence X₁s Ys)`,
* both wrong: `(X₁, X₂) ⟂ Y` reduces to `jointlyTypicalSet μ (jointSequence X₁s X₂s) Ys`.

## Main definitions

* `macJointSequence X₁s X₂s Ys` — the three-way joint sequence `i ω ↦ (X₁s i ω, X₂s i ω, Ys i ω)`.
* `macJointlyTypicalSet μ X₁s X₂s Ys n ε` — the three-way jointly typical set, the
  intersection of the three single-axis, three pairwise, and one three-way typicality
  conditions.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The three-way joint sequence over the product alphabet `α₁ × α₂ × β`.  Definitionally
equal to `jointSequence X₁s (jointSequence X₂s Ys)` (right-associated nesting). -/
noncomputable def macJointSequence
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β) :
    ℕ → Ω → α₁ × α₂ × β :=
  fun i ω ↦ (X1s i ω, X2s i ω, Ys i ω)

omit [MeasurableSpace Ω]
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma macJointSequence_eq
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β) :
    macJointSequence X1s X2s Ys = jointSequence X1s (jointSequence X2s Ys) := rfl

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
lemma measurable_macJointSequence
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i)) (i : ℕ) :
    Measurable (macJointSequence X1s X2s Ys i) :=
  (hX1s i).prodMk ((hX2s i).prodMk (hYs i))

/-- The three-way jointly typical set `A_ε^n ⊆ (Fin n → α₁) × (Fin n → α₂) × (Fin n → β)`:
triples `(x₁, x₂, y)` that are simultaneously typical along every single axis, every pair
of axes, and the three-way joint axis.  The seven conditions are exactly what the three
achievability error events `E1`/`E2`/`E3` require.

@audit:ok -/
noncomputable def macJointlyTypicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
  { p |
    (p.1 ∈ InformationTheory.Shannon.typicalSet μ X1s n ε)
    ∧ (p.2.1 ∈ InformationTheory.Shannon.typicalSet μ X2s n ε)
    ∧ (p.2.2 ∈ InformationTheory.Shannon.typicalSet μ Ys n ε)
    ∧ ((fun i ↦ (p.1 i, p.2.1 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence X1s X2s) n ε)
    ∧ ((fun i ↦ (p.1 i, p.2.2 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence X1s Ys) n ε)
    ∧ ((fun i ↦ (p.2.1 i, p.2.2 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence X2s Ys) n ε)
    ∧ ((fun i ↦ (p.1 i, (p.2.1 i, p.2.2 i))) ∈
        InformationTheory.Shannon.typicalSet μ (macJointSequence X1s X2s Ys) n ε) }

omit [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
@[entry_point]
lemma mem_macJointlyTypicalSet_iff
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x1 : Fin n → α₁) (x2 : Fin n → α₂) (y : Fin n → β) :
    (x1, x2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε ↔
      (x1 ∈ InformationTheory.Shannon.typicalSet μ X1s n ε)
      ∧ (x2 ∈ InformationTheory.Shannon.typicalSet μ X2s n ε)
      ∧ (y ∈ InformationTheory.Shannon.typicalSet μ Ys n ε)
      ∧ ((fun i ↦ (x1 i, x2 i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence X1s X2s) n ε)
      ∧ ((fun i ↦ (x1 i, y i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence X1s Ys) n ε)
      ∧ ((fun i ↦ (x2 i, y i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence X2s Ys) n ε)
      ∧ ((fun i ↦ (x1 i, (x2 i, y i))) ∈
          InformationTheory.Shannon.typicalSet μ (macJointSequence X1s X2s Ys) n ε) :=
  Iff.rfl

omit [DecidableEq α₁] [Nonempty α₁]
  [DecidableEq α₂] [Nonempty α₂]
  [DecidableEq β] [Nonempty β] in
theorem measurableSet_macJointlyTypicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    MeasurableSet (macJointlyTypicalSet μ X1s X2s Ys n ε) :=
  (Set.toFinite _).measurableSet

omit [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
lemma macJointlyTypicalSet_finite
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    (macJointlyTypicalSet μ X1s X2s Ys n ε).Finite := Set.toFinite _

end InformationTheory.Shannon.MAC
