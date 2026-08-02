import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Marton.ObjectiveVectorForm

/-!
# Marton's inner bound — the weighted sum of the region informations in vector form

The cardinality bound for the outer auxiliary variable optimizes a weighted sum of the three
informations of the region inequalities: `μ₁` times the first-receiver information plus `μ₃` times
the sum-rate expression `I(V₁; Y₁) + I(V₂; Y₂) - I(V₁; V₂)`.  This file writes that weighted sum
as `auxWeightObjective`, the shape support reduction consumes, plus a term that reads the weights
only through the channel-input aggregate.

The entropy of the outer auxiliary letter cancels twice, once inside the sum-rate expression and
once against the two entropy differences it leaves behind, and those differences are linear in the
weights.  What survives is the negated conditional entropy `-H(V₂ | Y₂)` with coefficient `μ₃`,
which is the convex part of `auxWeightObjective`, together with the entropy of the first output,
which reads the weights only through the aggregate.

## Main definitions

* `martonAuxWeight` — the coefficient vector of the linear part of the objective.
* `martonOutputAggregate` — the part of the objective that reads the weights only through the
  channel-input aggregate.

## Main statements

* `martonWeightedSum_eq_auxWeightObjective_add_aggregate` — the weighted sum of the informations
  is the auxiliary-weight objective plus the aggregate term.
* `exists_support_card_le_martonWeightedSum` — the weights can be replaced by weights supported on
  at most `Fintype.card α` indices, keeping the channel-input aggregate and not decreasing the
  weighted sum.
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

/-- The coefficient vector of the linear part of the weighted-sum objective: at the outer
auxiliary letter `u` it is `μ₃` times the entropy of the inner conditional law `κ u` minus
`μ₁ + μ₃` times the entropy of the first-output row of `u`. -/
noncomputable def martonAuxWeight (κ : Kernel V₁ V₂) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) (μ₁ μ₃ : ℝ) (u : V₁) : ℝ :=
  μ₃ * (∑ v₂ : V₂, Real.negMulLog ((κ u).real {v₂}))
    - (μ₁ + μ₃) * (∑ y₁ : β₁, Real.negMulLog (martonAuxOutput₁Row κ K W u y₁))

/-- The part of the weighted-sum objective that reads the weights only through the channel-input
aggregate `a`: it is `μ₁ + μ₃` times the entropy of the first output marginal induced by `a`. -/
noncomputable def martonOutputAggregate (W : BCChannel α β₁ β₂) (μ₁ μ₃ : ℝ) (a : α → ℝ) : ℝ :=
  (μ₁ + μ₃) * ∑ y₁ : β₁, Real.negMulLog (∑ x : α, a x * ∑ y₂ : β₂, (W x).real {(y₁, y₂)})

omit [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁] [Fintype V₂] [Nonempty V₂]
  [MeasurableSingletonClass V₂] [Nonempty α] [MeasurableSingletonClass α] [Nonempty β₁]
  [MeasurableSingletonClass β₁] [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂] in
lemma martonAuxKernelSlot_nonneg (κ : Kernel V₁ V₂) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) (u : V₁) (p : V₂ × β₂) : 0 ≤ martonAuxKernelSlot κ K W u p := by
  refine mul_nonneg measureReal_nonneg (Finset.sum_nonneg fun x _ ↦ ?_)
  exact mul_nonneg measureReal_nonneg (Finset.sum_nonneg fun y₁ _ ↦ measureReal_nonneg)

omit [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Nonempty α] [MeasurableSingletonClass α] [Nonempty β₁] [MeasurableSingletonClass β₁]
  [Nonempty β₂] [MeasurableSingletonClass β₂] in
lemma sum_mul_martonAuxWeight_eq (q : Measure V₁) (κ : Kernel V₁ V₂) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) (μ₁ μ₃ : ℝ) :
    ∑ u : V₁, q.real {u} * martonAuxWeight κ K W μ₁ μ₃ u
      = μ₃ * (∑ u : V₁, q.real {u} * ∑ v₂ : V₂, Real.negMulLog ((κ u).real {v₂}))
        - (μ₁ + μ₃) * (∑ u : V₁, q.real {u} *
            ∑ y₁ : β₁, Real.negMulLog (martonAuxOutput₁Row κ K W u y₁)) := by
  have h : ∀ u : V₁, q.real {u} * martonAuxWeight κ K W μ₁ μ₃ u
      = μ₃ * (q.real {u} * ∑ v₂ : V₂, Real.negMulLog ((κ u).real {v₂}))
        - (μ₁ + μ₃) * (q.real {u} *
            ∑ y₁ : β₁, Real.negMulLog (martonAuxOutput₁Row κ K W u y₁)) := by
    intro u
    simp only [martonAuxWeight]
    ring
  rw [Finset.sum_congr rfl fun u _ ↦ h u, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

lemma sum_negMulLog_martonAuxKernelSlot_eq_entropy
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∑ p : V₂ × β₂, Real.negMulLog (∑ u : V₁, q.real {u} * martonAuxKernelSlot κ K W u p)
      = entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ (p.2.1, p.2.2.2.2)) := by
  simp only [entropy]
  refine Finset.sum_congr rfl ?_
  rintro ⟨v₂, y₂⟩ -
  rw [marton_map_V₂Y₂_real_singleton_eq_sum q κ K W v₂ y₂]
  simp only [martonAuxKernelSlot]

lemma sum_negMulLog_martonAuxKernelSlot_mixture_eq_entropy
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∑ y₂ : β₂, Real.negMulLog
        (∑ v₂ : V₂, ∑ u : V₁, q.real {u} * martonAuxKernelSlot κ K W u (v₂, y₂))
      = entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ p.2.2.2.2) := by
  simp only [entropy]
  refine Finset.sum_congr rfl fun y₂ _ ↦ ?_
  rw [sum_martonAuxKernelSlot_mixture_eq_aggregate q κ K W y₂,
    marton_map_Y₂_real_singleton_eq_aggregate q κ K W y₂]

lemma martonOutputAggregate_eq_mul_entropy
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (μ₁ μ₃ : ℝ) :
    martonOutputAggregate W μ₁ μ₃ (fun x ↦ ∑ u : V₁, q.real {u} * martonAuxRow κ K u x)
      = (μ₁ + μ₃) * entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ p.2.2.2.1) := by
  simp only [martonOutputAggregate, entropy]
  congr 1
  refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
  rw [marton_map_Y₁_real_singleton_eq_aggregate q κ K W y₁]

/-- The weighted sum of the three informations of the region inequalities is the auxiliary-weight
objective at the weight vector of the outer auxiliary marginal, plus a term reading the weights
only through the channel-input aggregate. -/
@[entry_point]
theorem martonWeightedSum_eq_auxWeightObjective_add_aggregate
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (μ₁ μ₃ : ℝ) :
    μ₁ * martonInfo₁ (q ⊗ₘ κ) K W
      + μ₃ * (martonInfo₁ (q ⊗ₘ κ) K W + martonInfo₂ (q ⊗ₘ κ) K W
              - martonInfoV₁V₂ (q ⊗ₘ κ) K W)
      = auxWeightObjective (martonAuxKernelSlot κ K W) (martonAuxWeight κ K W μ₁ μ₃) 0 μ₃
          (fun u ↦ q.real {u})
        + martonOutputAggregate W μ₁ μ₃ (fun x ↦ ∑ u, q.real {u} * martonAuxRow κ K u x) := by
  simp only [martonInfo₁, martonInfo₂, martonInfoV₁V₂, auxWeightObjective]
  rw [martonOutputAggregate_eq_mul_entropy q κ K W μ₁ μ₃, sum_mul_martonAuxWeight_eq q κ K W μ₁ μ₃,
    sum_negMulLog_martonAuxKernelSlot_mixture_eq_entropy q κ K W,
    sum_negMulLog_martonAuxKernelSlot_eq_entropy q κ K W,
    ← marton_entropy_V₁V₂_sub_entropy_V₁_eq_sum q κ K W,
    ← marton_entropy_V₁Y₁_sub_entropy_V₁_eq_sum q κ K W]
  ring

/-- The weight vector of the outer auxiliary marginal can be replaced by a nonnegative weight
vector supported on at most `Fintype.card α` letters, keeping the channel-input aggregate and not
decreasing the weighted sum of the three informations. -/
@[entry_point]
theorem exists_support_card_le_martonWeightedSum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (μ₁ μ₃ : ℝ) (hμ₃ : 0 ≤ μ₃) :
    ∃ q' : V₁ → ℝ, 0 ≤ q' ∧
      (∀ x, ∑ u, q' u * martonAuxRow κ K u x = ∑ u, q.real {u} * martonAuxRow κ K u x) ∧
      μ₁ * martonInfo₁ (q ⊗ₘ κ) K W
        + μ₃ * (martonInfo₁ (q ⊗ₘ κ) K W + martonInfo₂ (q ⊗ₘ κ) K W
                - martonInfoV₁V₂ (q ⊗ₘ κ) K W)
        ≤ auxWeightObjective (martonAuxKernelSlot κ K W) (martonAuxWeight κ K W μ₁ μ₃) 0 μ₃ q'
          + martonOutputAggregate W μ₁ μ₃ (fun x ↦ ∑ u, q' u * martonAuxRow κ K u x) ∧
      {u | q' u ≠ 0}.ncard ≤ Fintype.card α := by
  obtain ⟨q', hq'nonneg, hq'agg, hle, hcard⟩ :=
    exists_support_card_le_auxWeightObjective_add_aggregate (martonAuxRow κ K)
      (sum_martonAuxRow_eq_one κ K) (martonAuxKernelSlot κ K W)
      (martonAuxKernelSlot_nonneg κ K W) (martonAuxWeight κ K W μ₁ μ₃) 0 μ₃ hμ₃
      (martonOutputAggregate W μ₁ μ₃) (fun u ↦ q.real {u}) fun _ ↦ measureReal_nonneg
  refine ⟨q', hq'nonneg, hq'agg, ?_, hcard⟩
  rw [martonWeightedSum_eq_auxWeightObjective_add_aggregate q κ K W μ₁ μ₃]
  exact hle

end InformationTheory.Shannon.BroadcastChannel.Marton
