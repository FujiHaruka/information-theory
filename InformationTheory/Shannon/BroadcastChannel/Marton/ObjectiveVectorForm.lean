import InformationTheory.Meta.EntryPoint
import InformationTheory.Probability.SingletonMass
import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore.Prelim
import InformationTheory.Shannon.BroadcastChannel.Marton.ObjectiveConvexity

/-!
# Marton's inner bound — the per-coordinate law in vector form

The convexity mechanism behind the cardinality bound (`ObjectiveConvexity.lean`) speaks about
weight vectors `q : U → ℝ` and a family of conditional laws `k : U → V × Z → ℝ`, whereas the
Marton informations are stated for the measure `martonJointDistribution pV K W`.  This file
descends the measure-level singleton masses of the projections of that law to explicit finite
sums, which is the form the vector-level objective consumes.

The auxiliary law is written as `pV = q ⊗ₘ κ`, so the outer index `u : V₁` plays the role of the
weight index: the mass the receiver-2 marginal puts on `(v₂, y₂)` is a `q`-weighted sum of a
quantity that depends only on `κ`, `K` and `W`.

## Main statements

* `marton_map_V₂Y₂_real_singleton_eq_sum` — the `(V₂, Y₂)`-marginal of the per-coordinate law is
  the weighted sum, over the outer auxiliary index, of a factor that does not depend on the
  weights.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

private lemma martonJointDistribution_map_real_singleton {γ : Type*}
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq γ]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : V₁ × V₂ × α × β₁ × β₂ → γ) (hg : Measurable g) (c : γ) :
    ((martonJointDistribution pV K W).map g).real {c}
      = ∑ v₁ : V₁, ∑ v₂ : V₂, ∑ x : α, ∑ y₁ : β₁, ∑ y₂ : β₂,
          if g (v₁, v₂, x, y₁, y₂) = c then
            pV.real {(v₁, v₂)} * (K (v₁, v₂)).real {x} * (W x).real {(y₁, y₂)} else 0 := by
  classical
  rw [map_real_singleton_fiber_sum _ g hg c, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v₁ _ ↦ Finset.sum_congr rfl fun v₂ _ ↦
    Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y₁ _ ↦
      Finset.sum_congr rfl fun y₂ _ ↦ ?_
  by_cases hgc : g (v₁, v₂, x, y₁, y₂) = c
  · simp only [hgc, if_true]
    exact martonJointDistribution_real_singleton pV K W (v₁, v₂) x (y₁, y₂)
  · simp only [hgc, if_false]

/-- The mass the `(V₂, Y₂)`-marginal of the per-coordinate law puts on `(v₂, y₂)`, when the
auxiliary pair is generated as `q ⊗ₘ κ`, is the `q`-weighted sum over the outer index `u` of a
factor built from `κ`, `K` and `W` alone. -/
@[entry_point]
theorem marton_map_V₂Y₂_real_singleton_eq_sum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (v₂ : V₂) (y₂ : β₂) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ (p.2.1, p.2.2.2.2))).real {(v₂, y₂)}
      = ∑ u : V₁, q.real {u} *
          ((κ u).real {v₂} * ∑ x : α, (K (u, v₂)).real {x} * ∑ y₁ : β₁, (W x).real {(y₁, y₂)}) := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ (p.2.1, p.2.2.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hcompProd : ∀ (u : V₁) (v : V₂),
      (q ⊗ₘ κ).real {(u, v)} = q.real {u} * (κ u).real {v} := by
    intro u v
    have h := jointDistribution_singleton q κ u v
    rw [jointDistribution_def] at h
    rw [Measure.real, h, ENNReal.toReal_mul]
    rfl
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg (v₂, y₂)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  refine (Finset.sum_eq_single_of_mem v₂ (Finset.mem_univ v₂) ?_).trans ?_
  · intro v _ hv
    refine Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y₁ _ ↦
      Finset.sum_eq_zero fun y _ ↦ ?_
    simp [hv]
  · simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hcompProd u v₂]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y₁ _ ↦ ?_
    ring

end InformationTheory.Shannon.BroadcastChannel.Marton
