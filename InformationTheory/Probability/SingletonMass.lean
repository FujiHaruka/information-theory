import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Fintype.BigOperators

/-!
# Singleton masses of a measure on a finite type

Mathlib's `MeasureTheory.sum_measureReal_singleton` evaluates `∑ b ∈ s, μ.real {b}` as
`μ.real ↑s` for a `Finset s`. This module records the specialization used throughout the
library: over a `Fintype` the singleton masses of a probability measure sum to `1`.

The module sits at the bottom of the import DAG — it depends only on Mathlib — so any file
needing the identity can import it without pulling in information-theoretic material.
-/

namespace InformationTheory

open MeasureTheory

lemma sum_measureReal_singleton_univ_eq_one {γ : Type*} [Fintype γ] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] (μ : Measure γ) [IsProbabilityMeasure μ] :
    ∑ z : γ, μ.real {z} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

end InformationTheory
