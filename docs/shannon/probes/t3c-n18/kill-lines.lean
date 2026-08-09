/-
PROBE — not an in-project asset (nothing under `InformationTheory/` imports this file).

The two one-line refutation attempts the N18 brief fixed in advance:

  C  the twenty-five slots reach an entropy form without passing through a pmf coordinate
     (`mutualInfo_toReal_eq_entropy_form` / `condMutualInfo_eq_condEntropy_sub_condEntropy`);
  D  the three topological type classes the compactness tool asks for can be produced inside a
     proof, without touching the signature of any existing declaration.

Silence = the reading survives.  A `failed to synthesize` or a shape mismatch = it dies.

Run:  lake env lean docs/shannon/probes/t3c-n18/kill-lines.lean
-/
import InformationTheory.Shannon.BroadcastChannel.Thm7Region
import InformationTheory.Shannon.MultipleAccess.Reconciliation
import Mathlib.MeasureTheory.Measure.Prokhorov

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open InformationTheory.Shannon.BroadcastChannel.Marton
open InformationTheory.Shannon.MAC

namespace ProbeThm7N18KillLines

universe u

variable {α β₁ β₂ : Type u} [Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Fintype β₁] [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype β₂] [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/- C, conditional half: slot 4 = `I(U ; Y | W)` as a difference of conditional entropies. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsProbabilityMeasure ν] :
    condMutualInfoReal ν (fun q ↦ q.1 (0, 0)) (fun q ↦ q.2.2.1) (fun q ↦ q.1 (0, 2))
      = InformationTheory.MeasureFano.condEntropy ν (fun q ↦ q.1 (0, 0)) (fun q ↦ q.1 (0, 2))
        - InformationTheory.MeasureFano.condEntropy ν (fun q ↦ q.1 (0, 0))
            (fun q ↦ (q.1 (0, 2), q.2.2.1)) := by
  classical
  exact condMutualInfo_eq_condEntropy_sub_condEntropy ν _ _ _ (by fun_prop) (by fun_prop)
    (by fun_prop)

/- C, unconditional half: slot 0 = `I(W ; Y)` as a sum and difference of entropies. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsProbabilityMeasure ν] :
    mutualInfoReal ν (fun q ↦ q.1 (0, 2)) (fun q ↦ q.2.2.1)
      = entropy ν (fun q ↦ q.1 (0, 2)) + entropy ν (fun q ↦ q.2.2.1)
        - entropy ν (fun q ↦ (q.1 (0, 2), q.2.2.1)) := by
  classical
  exact mutualInfo_toReal_eq_entropy_form ν _ _ (by fun_prop) (by fun_prop)

/- D: the compactness of the space of joint laws, produced inside a proof body.

Two conditions the reading did not anticipate are recorded by the code itself: the instance lives
in `Mathlib.MeasureTheory.Measure.Prokhorov`, which is outside the import closure of
`Thm7Region.lean`, and the three ambient-level instances have to be hoisted by hand -- the nested
search for the thirteen-factor product does not reach them on its own, and raising
`synthInstance.maxSize` to 2000 and `synthInstance.maxHeartbeats` to 4000000 does not change that.
-/
example (W : BCChannel α β₁ β₂) (p : Measure α) {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (kv : Thm7AuxIdx → ℕ) : True := by
  letI : TopologicalSpace α := ⊥
  letI : TopologicalSpace β₁ := ⊥
  letI : TopologicalSpace β₂ := ⊥
  haveI : DiscreteTopology α := ⟨rfl⟩
  haveI : DiscreteTopology β₁ := ⟨rfl⟩
  haveI : DiscreteTopology β₂ := ⟨rfl⟩
  haveI : MeasurableSingletonClass α := measurableSingleton_of_standardBorel
  haveI : MeasurableSingletonClass β₁ := measurableSingleton_of_standardBorel
  haveI : MeasurableSingletonClass β₂ := measurableSingleton_of_standardBorel
  haveI : BorelSpace α := DiscreteMeasurableSpace.toBorelSpace
  haveI : BorelSpace β₁ := DiscreteMeasurableSpace.toBorelSpace
  haveI : BorelSpace β₂ := DiscreteMeasurableSpace.toBorelSpace
  haveI : OpensMeasurableSpace (Thm7Ambient kv kJ α β₁ β₂) := inferInstance
  haveI : BorelSpace (Thm7Ambient kv kJ α β₁ β₂) := inferInstance
  haveI : CompactSpace (Thm7Ambient kv kJ α β₁ β₂) := inferInstance
  have : CompactSpace (ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂)) := inferInstance
  trivial

end ProbeThm7N18KillLines
