/-
PROBE — not an in-project asset (nothing under `InformationTheory/` imports this file).

Material (i) of the two the closedness of the union over joint laws needs: do the twenty-five
slots depend continuously on the joint law in the weak topology?  The kill-line for reading C
already showed the slots reach an entropy form, and the chain rule turns a conditional entropy
into a difference of plain entropies, so the whole of (i) rests on one atom:

  `ν ↦ entropy ν f` is continuous on the space of probability measures of a finite discrete space.

Run:  lake env lean docs/shannon/probes/t3c-n18/continuity.lean
-/
import InformationTheory.Shannon.BroadcastChannel.Thm7Region
import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open InformationTheory.Shannon.BroadcastChannel.Marton

namespace ProbeThm7N18Continuity

universe u

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [DiscreteTopology Ω]
  [CompactSpace Ω] [OpensMeasurableSpace Ω]

lemma continuous_measureReal (S : Set Ω) :
    Continuous fun ν : ProbabilityMeasure Ω ↦ (ν : Measure Ω).real S := by
  have hcont : Continuous fun ν : ProbabilityMeasure Ω ↦
      ∫ ω, (BoundedContinuousFunction.mkOfCompact
        (⟨S.indicator fun _ ↦ (1 : ℝ), continuous_of_discreteTopology⟩ : C(Ω, ℝ))) ω
          ∂(ν : Measure Ω) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction _
  refine hcont.congr fun ν ↦ ?_
  show ∫ ω, S.indicator (fun _ ↦ (1 : ℝ)) ω ∂(ν : Measure Ω) = _
  exact MeasureTheory.integral_indicator_one (isOpen_discrete S).measurableSet

variable {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

lemma continuous_entropy (f : Ω → T) (hf : Measurable f) :
    Continuous fun ν : ProbabilityMeasure Ω ↦ entropy (ν : Measure Ω) f := by
  have hpt : ∀ (ν : ProbabilityMeasure Ω) (x : T),
      ((ν : Measure Ω).map f).real {x} = (ν : Measure Ω).real (f ⁻¹' {x}) := by
    intro ν x
    rw [measureReal_def, measureReal_def, Measure.map_apply hf (measurableSet_singleton x)]
  refine continuous_finsetSum Finset.univ fun x _ ↦ ?_
  exact (Real.continuous_negMulLog.comp (continuous_measureReal (f ⁻¹' {x}))).congr
    fun ν ↦ by rw [hpt ν x]; rfl

section Slots

variable {α β₁ β₂ : Type u} [Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]
  [Fintype β₁] [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [TopologicalSpace β₁] [DiscreteTopology β₁] [BorelSpace β₁]
  [Fintype β₂] [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]
  [TopologicalSpace β₂] [DiscreteTopology β₂] [BorelSpace β₂]

/- Slot 0, the unconditional shape. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    [OpensMeasurableSpace (Thm7Ambient kv kJ α β₁ β₂)]
    [CompactSpace (Thm7Ambient kv kJ α β₁ β₂)] :
    Continuous fun ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂) ↦
      thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) 0 := by
  classical
  haveI : MeasurableSingletonClass α := measurableSingleton_of_standardBorel
  haveI : MeasurableSingletonClass β₁ := measurableSingleton_of_standardBorel
  haveI : MeasurableSingletonClass β₂ := measurableSingleton_of_standardBorel
  have hrw : ∀ ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂),
      thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) 0
        = entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ q.1 (0, 2))
          + entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ q.2.2.1)
          - entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))
              (fun q ↦ (q.1 (0, 2), q.2.2.1)) := fun ν ↦ by
    simpa only [thm7Slots, mutualInfoReal, Matrix.cons_val_zero] using
      InformationTheory.Shannon.MAC.mutualInfo_toReal_eq_entropy_form
        (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) _ _ (by fun_prop) (by fun_prop)
  exact ((((continuous_entropy _ (by fun_prop)).add (continuous_entropy _ (by fun_prop))).sub
    (continuous_entropy _ (by fun_prop)))).congr fun ν ↦ (hrw ν).symm

/- Slot 4, the conditional shape. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    [OpensMeasurableSpace (Thm7Ambient kv kJ α β₁ β₂)]
    [CompactSpace (Thm7Ambient kv kJ α β₁ β₂)] :
    Continuous fun ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂) ↦
      thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) 4 := by
  classical
  haveI : MeasurableSingletonClass α := measurableSingleton_of_standardBorel
  haveI : MeasurableSingletonClass β₁ := measurableSingleton_of_standardBorel
  haveI : MeasurableSingletonClass β₂ := measurableSingleton_of_standardBorel
  have hrw : ∀ ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂),
      thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) 4
        = (entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))
              (fun q ↦ (q.1 (0, 2), q.1 (0, 0)))
            - entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ q.1 (0, 2)))
          - (entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))
                (fun q ↦ ((q.1 (0, 2), q.2.2.1), q.1 (0, 0)))
              - entropy (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))
                  (fun q ↦ (q.1 (0, 2), q.2.2.1))) := fun ν ↦ by
    have h1 := entropy_pair_eq_entropy_add_condEntropy
      (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ q.1 (0, 2)) (fun q ↦ q.1 (0, 0))
      (by fun_prop) (by fun_prop)
    have h2 := entropy_pair_eq_entropy_add_condEntropy
      (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ (q.1 (0, 2), q.2.2.1))
      (fun q ↦ q.1 (0, 0)) (by fun_prop) (by fun_prop)
    have h3 := condMutualInfo_eq_condEntropy_sub_condEntropy
      (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ q.1 (0, 0)) (fun q ↦ q.1 (0, 2))
      (fun q ↦ q.2.2.1) (by fun_prop) (by fun_prop) (by fun_prop)
    have hval : thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) 4
        = condMutualInfoReal (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (fun q ↦ q.1 (0, 0))
            (fun q ↦ q.2.2.1) (fun q ↦ q.1 (0, 2)) := rfl
    rw [hval, condMutualInfoReal, h3]
    linarith [h1, h2]
  exact ((((continuous_entropy _ (by fun_prop)).sub (continuous_entropy _ (by fun_prop))).sub
    ((continuous_entropy _ (by fun_prop)).sub
      (continuous_entropy _ (by fun_prop))))).congr fun ν ↦ (hrw ν).symm

/- Material (ii), the fourth clause of `IsThm7Law`: the input marginal is prescribed. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    [OpensMeasurableSpace (Thm7Ambient kv kJ α β₁ β₂)]
    [CompactSpace (Thm7Ambient kv kJ α β₁ β₂)] (p : ProbabilityMeasure α) :
    IsClosed {ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂) |
      (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)).map (fun q ↦ q.2.1) = (p : Measure α)} := by
  haveI : HasOuterApproxClosed α := inferInstance
  haveI : T2Space (ProbabilityMeasure α) := ProbabilityMeasure.t2Space α
  have hcont : Continuous fun ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂) ↦
      ProbabilityMeasure.map ν
        (f := fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1)
        (continuous_of_discreteTopology.measurable.aemeasurable) :=
    ProbabilityMeasure.continuous_map continuous_of_discreteTopology
  have hset : {ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂) |
      (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)).map (fun q ↦ q.2.1) = (p : Measure α)}
      = (fun ν ↦ ProbabilityMeasure.map ν
          (f := fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1)
          (continuous_of_discreteTopology.measurable.aemeasurable)) ⁻¹' {p} := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      ← ProbabilityMeasure.toMeasure_injective.eq_iff, ProbabilityMeasure.toMeasure_map]
  rw [hset]
  exact (isClosed_singleton).preimage hcont

end Slots

end ProbeThm7N18Continuity
