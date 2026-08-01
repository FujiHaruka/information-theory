import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Singleton masses of a measure on a finite type

Mathlib's `MeasureTheory.sum_measureReal_singleton` evaluates `∑ b ∈ s, μ.real {b}` as
`μ.real ↑s` for a `Finset s`. This module records the two specializations used throughout the
library: over a `Fintype` the singleton masses of a probability measure sum to `1`, and the
singleton masses of a pushforward are the sums of the masses over the fibers.

## Main statements

* `sum_measureReal_singleton_univ_eq_one` — the singleton masses of a probability measure on a
  finite type sum to `1`.
* `map_real_singleton_fiber_sum` — a singleton mass of a pushforward is the sum of the masses
  over the fiber above that point.

## Implementation notes

The module sits at the bottom of the import DAG — it depends only on Mathlib — so any file
needing the identity can import it without pulling in information-theoretic material.
-/

namespace InformationTheory

open MeasureTheory

lemma sum_measureReal_singleton_univ_eq_one {γ : Type*} [Fintype γ] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] (μ : Measure γ) [IsProbabilityMeasure μ] :
    ∑ z : γ, μ.real {z} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

lemma map_real_singleton_fiber_sum {γ δ : Type*} [Fintype γ] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ] [DecidableEq δ]
    (μ : Measure γ) [SigmaFinite μ] (f : γ → δ) (hf : Measurable f) (x : δ) :
    (μ.map f).real {x} = ∑ q ∈ Finset.univ.filter fun q ↦ f q = x, μ.real {q} := by
  rw [map_measureReal_apply hf (measurableSet_singleton x)]
  have hset : f ⁻¹' {x} = ↑(Finset.univ.filter fun q ↦ f q = x) := by
    ext q; simp [Set.mem_preimage, Finset.coe_filter]
  rw [hset, sum_measureReal_singleton]

end InformationTheory
