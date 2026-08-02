import InformationTheory.Meta.EntryPoint
import InformationTheory.Probability.SingletonMass
import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore.Prelim
import InformationTheory.Shannon.BroadcastChannel.Marton.ObjectiveConvexity

/-!
# Marton's inner bound — the per-coordinate law in vector form

The convexity mechanism behind the cardinality bound (`auxWeightObjective`) speaks about
weight vectors `q : U → ℝ` and a family of conditional laws `k : U → V × Z → ℝ`, whereas the
Marton informations are stated for the measure `martonJointDistribution pV K W`.  This file
descends the measure-level singleton masses of the projections of that law to explicit finite
sums, which is the form the vector-level objective consumes.

The auxiliary law is written as `pV = q ⊗ₘ κ`, so the outer index `u : V₁` plays the role of the
weight index: the mass a marginal puts on a point is a `q`-weighted sum of a quantity that
depends only on `κ`, `K` and `W`.  The channel-input marginal is the aggregate the cardinality
argument has to preserve, and the two output marginals are functions of that aggregate alone.

## Main definitions

* `martonAuxRow` — the row, indexed by the outer auxiliary letter, of the stochastic matrix that
  aggregates the weights into the channel-input marginal.
* `martonAuxOutput₁Row` — the row, indexed by the same letter, of the stochastic matrix that
  aggregates the weights into the first output marginal.
* `martonAuxKernelSlot` — the conditional law, indexed by the outer auxiliary letter, on the pair
  formed by the inner auxiliary letter and the second output letter.

## Main statements

* `sum_martonAuxRow_eq_one` — each row of the aggregation matrix sums to one.
* `marton_map_X_real_singleton_eq_sum` — the channel-input marginal is the weighted sum of the
  rows of the aggregation matrix.
* `marton_map_V₁_real_singleton_eq` — the outer auxiliary marginal is the weight vector.
* `marton_map_V₂_real_singleton_eq_sum` — the inner auxiliary marginal is a weighted sum of a
  factor that does not depend on the weights.
* `marton_map_V₁V₂_real_singleton_eq` — the joint auxiliary marginal factors into the weight and
  the inner conditional law.
* `marton_map_V₁Y₁_real_singleton_eq_sum` — the `(V₁, Y₁)`-marginal factors into the weight and a
  factor built from `κ`, `K` and `W` alone.
* `marton_map_V₂Y₂_real_singleton_eq_sum` — the `(V₂, Y₂)`-marginal is the weighted sum, over the
  outer auxiliary index, of a factor that does not depend on the weights.
* `marton_map_Y₁_real_singleton_eq_aggregate` — the first output marginal reads the weights only
  through the channel-input aggregate.
* `marton_map_Y₂_real_singleton_eq_aggregate` — the second output marginal reads the weights only
  through the channel-input aggregate.
* `marton_entropy_V₁V₂_sub_entropy_V₁_eq_sum` — the entropy the auxiliary pair adds over the
  outer auxiliary letter alone is linear in the weights.
* `sum_martonAuxOutput₁Row_eq_one` — each row of the first-output aggregation matrix sums to one.
* `marton_entropy_V₁Y₁_sub_entropy_V₁_eq_sum` — the entropy the `(V₁, Y₁)`-pair adds over the
  outer auxiliary letter alone is linear in the weights.
* `sum_martonAuxKernelSlot_mixture_eq_aggregate` — the mixture of the conditional laws, summed
  over the inner auxiliary letter, is the second output marginal in aggregate form.
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

/-- The row, indexed by the outer auxiliary letter `u`, of the stochastic matrix that carries a
weight vector on `V₁` to the induced law on the channel input: the mass `u` contributes to the
input letter `x` after the inner auxiliary letter and the channel input have been generated. -/
noncomputable def martonAuxRow (κ : Kernel V₁ V₂) (K : Kernel (V₁ × V₂) α) (u : V₁) (x : α) : ℝ :=
  ∑ v₂ : V₂, (κ u).real {v₂} * (K (u, v₂)).real {x}

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

omit [Nonempty V₁] [Fintype V₂] [Nonempty V₂] in
private lemma compProd_real_singleton_mul (q : Measure V₁) [IsProbabilityMeasure q]
    (κ : Kernel V₁ V₂) [IsMarkovKernel κ] (u : V₁) (v : V₂) :
    (q ⊗ₘ κ).real {(u, v)} = q.real {u} * (κ u).real {v} := by
  have h := jointDistribution_singleton q κ u v
  rw [jointDistribution_def] at h
  rw [Measure.real, h, ENNReal.toReal_mul]
  rfl

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [Nonempty β₁] [Nonempty β₂] in
private lemma sum_bcChannel_real_singleton_eq_one (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (x : α) : ∑ y₁ : β₁, ∑ y₂ : β₂, (W x).real {(y₁, y₂)} = 1 := by
  rw [← Fintype.sum_prod_type (f := fun p : β₁ × β₂ ↦ (W x).real {p})]
  exact sum_measureReal_singleton_univ_eq_one (W x)

omit [Nonempty V₁] [Nonempty V₂] [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma sum_compProd_mul_kernel_real_singleton
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (x : α) :
    ∑ v₁ : V₁, ∑ v₂ : V₂, (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x}
      = ∑ u : V₁, q.real {u} * martonAuxRow κ K u x := by
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  simp only [martonAuxRow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v₂ _ ↦ ?_
  rw [compProd_real_singleton_mul q κ u v₂, mul_assoc]

omit [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [Nonempty α] in
/-- Each row of the aggregation matrix is a probability vector on the channel input. -/
@[entry_point]
theorem sum_martonAuxRow_eq_one (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (u : V₁) :
    ∑ x : α, martonAuxRow κ K u x = 1 := by
  simp only [martonAuxRow]
  rw [Finset.sum_comm]
  have hrow : ∀ v₂ : V₂, ∑ x : α, (κ u).real {v₂} * (K (u, v₂)).real {x} = (κ u).real {v₂} := by
    intro v₂
    rw [← Finset.mul_sum, sum_measureReal_singleton_univ_eq_one (K (u, v₂)), mul_one]
  rw [Finset.sum_congr rfl fun v₂ _ ↦ hrow v₂]
  exact sum_measureReal_singleton_univ_eq_one (κ u)

/-- The channel-input marginal of the per-coordinate law is the weighted sum of the rows of the
aggregation matrix: it is the aggregate the cardinality argument has to preserve. -/
@[entry_point]
theorem marton_map_X_real_singleton_eq_sum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (x : α) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ p.2.2.1)).real {x}
      = ∑ u : V₁, q.real {u} * martonAuxRow κ K u x := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg x,
    ← sum_compProd_mul_kernel_real_singleton q κ K x]
  refine Finset.sum_congr rfl fun v₁ _ ↦ Finset.sum_congr rfl fun v₂ _ ↦ ?_
  refine (Finset.sum_eq_single_of_mem x (Finset.mem_univ x) ?_).trans ?_
  · intro x' _ hx'
    exact Finset.sum_eq_zero fun y₁ _ ↦ Finset.sum_eq_zero fun y₂ _ ↦ by simp [hx']
  · refine Eq.trans (Finset.sum_congr rfl fun y₁ _ ↦
      Finset.sum_congr rfl fun y₂ _ ↦ if_pos rfl) ?_
    simp only [← Finset.mul_sum]
    rw [sum_bcChannel_real_singleton_eq_one W x, mul_one]

/-- The outer auxiliary marginal of the per-coordinate law is the weight vector itself. -/
@[entry_point]
theorem marton_map_V₁_real_singleton_eq
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (u : V₁) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map Prod.fst).real {u} = q.real {u} := by
  classical
  have hg : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hW : ∀ (v₂ : V₂) (x : α), (∑ y₁ : β₁, ∑ y₂ : β₂,
      (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} * (W x).real {(y₁, y₂)})
      = (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} := by
    intro v₂ x
    simp only [← Finset.mul_sum]
    rw [sum_bcChannel_real_singleton_eq_one W x, mul_one]
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg u]
  refine (Finset.sum_eq_single_of_mem u (Finset.mem_univ u) ?_).trans ?_
  · exact fun v _ hv ↦ Finset.sum_eq_zero fun v₂ _ ↦ Finset.sum_eq_zero fun x _ ↦
      Finset.sum_eq_zero fun y₁ _ ↦ Finset.sum_eq_zero fun y₂ _ ↦ by simp [hv]
  · trans ∑ v₂ : V₂, q.real {u} * (κ u).real {v₂}
    · refine Finset.sum_congr rfl fun v₂ _ ↦ ?_
      refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ Eq.trans
        (Finset.sum_congr rfl fun y₁ _ ↦ Finset.sum_congr rfl fun y₂ _ ↦ if_pos rfl)
        (hW v₂ x)) ?_
      rw [← Finset.mul_sum, sum_measureReal_singleton_univ_eq_one (K (u, v₂)), mul_one,
        compProd_real_singleton_mul q κ u v₂]
    · rw [← Finset.mul_sum, sum_measureReal_singleton_univ_eq_one (κ u), mul_one]

/-- The inner auxiliary marginal of the per-coordinate law is the `q`-weighted sum over the outer
index of a factor built from `κ` alone. -/
@[entry_point]
theorem marton_map_V₂_real_singleton_eq_sum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (v₂ : V₂) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ p.2.1)).real {v₂}
      = ∑ u : V₁, q.real {u} * (κ u).real {v₂} := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ p.2.1) :=
    measurable_fst.comp measurable_snd
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg v₂]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have hW : ∀ x : α, (∑ y₁ : β₁, ∑ y₂ : β₂,
      (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} * (W x).real {(y₁, y₂)})
      = (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} := by
    intro x
    simp only [← Finset.mul_sum]
    rw [sum_bcChannel_real_singleton_eq_one W x, mul_one]
  refine (Finset.sum_eq_single_of_mem v₂ (Finset.mem_univ v₂) ?_).trans ?_
  · exact fun v _ hv ↦ Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y₁ _ ↦
      Finset.sum_eq_zero fun y₂ _ ↦ by simp [hv]
  · refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ Eq.trans
      (Finset.sum_congr rfl fun y₁ _ ↦ Finset.sum_congr rfl fun y₂ _ ↦ if_pos rfl)
      (hW x)) ?_
    rw [← Finset.mul_sum, sum_measureReal_singleton_univ_eq_one (K (u, v₂)), mul_one,
      compProd_real_singleton_mul q κ u v₂]

/-- The joint auxiliary marginal of the per-coordinate law factors into the weight at the outer
index and the inner conditional law. -/
@[entry_point]
theorem marton_map_V₁V₂_real_singleton_eq
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (u : V₁) (v₂ : V₂) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ (p.1, p.2.1))).real {(u, v₂)}
      = q.real {u} * (κ u).real {v₂} := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ (p.1, p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hW : ∀ x : α, (∑ y₁ : β₁, ∑ y₂ : β₂,
      (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} * (W x).real {(y₁, y₂)})
      = (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} := by
    intro x
    simp only [← Finset.mul_sum]
    rw [sum_bcChannel_real_singleton_eq_one W x, mul_one]
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg (u, v₂)]
  refine (Finset.sum_eq_single_of_mem u (Finset.mem_univ u) ?_).trans ?_
  · exact fun v _ hv ↦ Finset.sum_eq_zero fun v' _ ↦ Finset.sum_eq_zero fun x _ ↦
      Finset.sum_eq_zero fun y₁ _ ↦ Finset.sum_eq_zero fun y₂ _ ↦ by simp [hv]
  · refine (Finset.sum_eq_single_of_mem v₂ (Finset.mem_univ v₂) ?_).trans ?_
    · exact fun v _ hv ↦ Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y₁ _ ↦
        Finset.sum_eq_zero fun y₂ _ ↦ by simp [hv]
    · refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ Eq.trans
        (Finset.sum_congr rfl fun y₁ _ ↦ Finset.sum_congr rfl fun y₂ _ ↦ if_pos rfl)
        (hW x)) ?_
      rw [← Finset.mul_sum, sum_measureReal_singleton_univ_eq_one (K (u, v₂)), mul_one,
        compProd_real_singleton_mul q κ u v₂]

/-- The mass the `(V₁, Y₁)`-marginal of the per-coordinate law puts on `(u, y₁)`, when the
auxiliary pair is generated as `q ⊗ₘ κ`, is the weight at `u` times a factor built from `κ`, `K`
and `W` alone. -/
@[entry_point]
theorem marton_map_V₁Y₁_real_singleton_eq_sum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (u : V₁) (y₁ : β₁) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ (p.1, p.2.2.2.1))).real {(u, y₁)}
      = q.real {u} * ∑ v₂ : V₂, (κ u).real {v₂} *
          ∑ x : α, (K (u, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)} := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ (p.1, p.2.2.2.1)) :=
    measurable_fst.prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg (u, y₁), Finset.mul_sum]
  refine (Finset.sum_eq_single_of_mem u (Finset.mem_univ u) ?_).trans ?_
  · exact fun v _ hv ↦ Finset.sum_eq_zero fun v₂ _ ↦ Finset.sum_eq_zero fun x _ ↦
      Finset.sum_eq_zero fun y _ ↦ Finset.sum_eq_zero fun y₂ _ ↦ by simp [hv]
  · refine Finset.sum_congr rfl fun v₂ _ ↦ ?_
    have hy : ∀ x : α, (∑ y : β₁, ∑ y₂ : β₂, if ((u : V₁), y) = (u, y₁) then
        (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x} * (W x).real {(y, y₂)} else 0)
        = (q ⊗ₘ κ).real {(u, v₂)} * (K (u, v₂)).real {x}
            * ∑ y₂ : β₂, (W x).real {(y₁, y₂)} := by
      intro x
      refine (Finset.sum_eq_single_of_mem y₁ (Finset.mem_univ y₁) ?_).trans ?_
      · exact fun y _ hyne ↦ Finset.sum_eq_zero fun y₂ _ ↦ by simp [hyne]
      · refine Eq.trans (Finset.sum_congr rfl fun y₂ _ ↦ if_pos rfl) ?_
        rw [Finset.mul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ hy x) ?_
    rw [compProd_real_singleton_mul q κ u v₂]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y₂ _ ↦ by ring

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
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg (v₂, y₂)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  refine (Finset.sum_eq_single_of_mem v₂ (Finset.mem_univ v₂) ?_).trans ?_
  · intro v _ hv
    refine Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y₁ _ ↦
      Finset.sum_eq_zero fun y _ ↦ ?_
    simp [hv]
  · simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [compProd_real_singleton_mul q κ u v₂]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y₁ _ ↦ ?_
    ring

/-- The first output marginal of the per-coordinate law reads the weights only through the
channel-input aggregate: it is a function of `fun x ↦ ∑ u, q.real {u} * martonAuxRow κ K u x`. -/
@[entry_point]
theorem marton_map_Y₁_real_singleton_eq_aggregate
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (y₁ : β₁) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ p.2.2.2.1)).real {y₁}
      = ∑ x : α, (∑ u : V₁, q.real {u} * martonAuxRow κ K u x)
          * ∑ y₂ : β₂, (W x).real {(y₁, y₂)} := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ p.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hinner : ∀ (v₁ : V₁) (v₂ : V₂) (x : α),
      (∑ y : β₁, ∑ y₂ : β₂, if y = y₁ then
          (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x} * (W x).real {(y, y₂)} else 0)
        = (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x}
            * ∑ y₂ : β₂, (W x).real {(y₁, y₂)} := by
    intro v₁ v₂ x
    refine (Finset.sum_eq_single_of_mem y₁ (Finset.mem_univ y₁) ?_).trans ?_
    · exact fun y _ hy ↦ Finset.sum_eq_zero fun y₂ _ ↦ by simp [hy]
    · refine Eq.trans (Finset.sum_congr rfl fun y₂ _ ↦ if_pos rfl) ?_
      rw [Finset.mul_sum]
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg y₁]
  trans ∑ v₁ : V₁, ∑ v₂ : V₂, ∑ x : α,
      (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)}
  · exact Finset.sum_congr rfl fun v₁ _ ↦ Finset.sum_congr rfl fun v₂ _ ↦
      Finset.sum_congr rfl fun x _ ↦ hinner v₁ v₂ x
  · refine Eq.trans Finset.sum_comm_cycle (Finset.sum_congr rfl fun x _ ↦ ?_)
    rw [← sum_compProd_mul_kernel_real_singleton q κ K x]
    simp only [Finset.sum_mul]

/-- The second output marginal of the per-coordinate law reads the weights only through the
channel-input aggregate: it is a function of `fun x ↦ ∑ u, q.real {u} * martonAuxRow κ K u x`. -/
@[entry_point]
theorem marton_map_Y₂_real_singleton_eq_aggregate
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (y₂ : β₂) :
    ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ p.2.2.2.2)).real {y₂}
      = ∑ x : α, (∑ u : V₁, q.real {u} * martonAuxRow κ K u x)
          * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} := by
  classical
  have hg : Measurable (fun p : V₁ × V₂ × α × β₁ × β₂ ↦ p.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hinner : ∀ (v₁ : V₁) (v₂ : V₂) (x : α),
      (∑ y₁ : β₁, ∑ y : β₂, if y = y₂ then
          (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x} * (W x).real {(y₁, y)} else 0)
        = (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x}
            * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} := by
    intro v₁ v₂ x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
    refine (Finset.sum_eq_single_of_mem y₂ (Finset.mem_univ y₂) ?_).trans (if_pos rfl)
    exact fun y _ hy ↦ by simp [hy]
  rw [martonJointDistribution_map_real_singleton (q ⊗ₘ κ) K W _ hg y₂]
  trans ∑ v₁ : V₁, ∑ v₂ : V₂, ∑ x : α,
      (q ⊗ₘ κ).real {(v₁, v₂)} * (K (v₁, v₂)).real {x} * ∑ y₁ : β₁, (W x).real {(y₁, y₂)}
  · exact Finset.sum_congr rfl fun v₁ _ ↦ Finset.sum_congr rfl fun v₂ _ ↦
      Finset.sum_congr rfl fun x _ ↦ hinner v₁ v₂ x
  · refine Eq.trans Finset.sum_comm_cycle (Finset.sum_congr rfl fun x _ ↦ ?_)
    rw [← sum_compProd_mul_kernel_real_singleton q κ K x]
    simp only [Finset.sum_mul]

private lemma sum_negMulLog_mul_sub_eq {ι σ : Type*} [Fintype ι] [Fintype σ]
    (q : ι → ℝ) (c : ι → σ → ℝ) (hc : ∀ i, ∑ s : σ, c i s = 1) :
    (∑ i : ι, ∑ s : σ, Real.negMulLog (q i * c i s)) - ∑ i : ι, Real.negMulLog (q i)
      = ∑ i : ι, q i * ∑ s : σ, Real.negMulLog (c i s) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsplit : ∑ s : σ, Real.negMulLog (q i * c i s)
      = (∑ s : σ, c i s) * Real.negMulLog (q i)
        + q i * ∑ s : σ, Real.negMulLog (c i s) := by
    simp only [Real.negMulLog_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [hsplit, hc i, one_mul]
  ring

/-- The entropy the joint auxiliary pair adds over the outer auxiliary letter alone is linear in
the weights: the coefficient at `u` is the entropy of the inner conditional law `κ u`. -/
@[entry_point]
theorem marton_entropy_V₁V₂_sub_entropy_V₁_eq_sum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ (p.1, p.2.1))
        - entropy (martonJointDistribution (q ⊗ₘ κ) K W) Prod.fst
      = ∑ u : V₁, q.real {u} * ∑ v₂ : V₂, Real.negMulLog ((κ u).real {v₂}) := by
  simp only [entropy, Fintype.sum_prod_type, marton_map_V₁V₂_real_singleton_eq q κ K W,
    marton_map_V₁_real_singleton_eq q κ K W]
  exact sum_negMulLog_mul_sub_eq (fun u ↦ q.real {u}) (fun u v₂ ↦ (κ u).real {v₂})
    fun u ↦ sum_measureReal_singleton_univ_eq_one (κ u)

/-- The row, indexed by the outer auxiliary letter `u`, of the stochastic matrix that carries a
weight vector on `V₁` to the induced law on the first output: the mass `u` contributes to the
output letter `y₁` after the inner auxiliary letter, the channel input and the channel output
have been generated. -/
noncomputable def martonAuxOutput₁Row (κ : Kernel V₁ V₂) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) (u : V₁) (y₁ : β₁) : ℝ :=
  ∑ v₂ : V₂, (κ u).real {v₂} * ∑ x : α, (K (u, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)}

omit [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [Nonempty α]
  [Nonempty β₁] [Nonempty β₂] in
/-- Each row of the first-output aggregation matrix is a probability vector on the first output
alphabet. -/
@[entry_point]
theorem sum_martonAuxOutput₁Row_eq_one (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (u : V₁) : ∑ y₁ : β₁, martonAuxOutput₁Row κ K W u y₁ = 1 := by
  simp only [martonAuxOutput₁Row]
  rw [Finset.sum_comm]
  have hrow : ∀ v₂ : V₂, ∑ y₁ : β₁, (κ u).real {v₂} *
      ∑ x : α, (K (u, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)} = (κ u).real {v₂} := by
    intro v₂
    have hinner : ∑ y₁ : β₁, ∑ x : α, (K (u, v₂)).real {x} * ∑ y₂ : β₂, (W x).real {(y₁, y₂)}
        = ∑ x : α, (K (u, v₂)).real {x} := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← Finset.mul_sum, sum_bcChannel_real_singleton_eq_one W x, mul_one]
    rw [← Finset.mul_sum, hinner, sum_measureReal_singleton_univ_eq_one (K (u, v₂)), mul_one]
  rw [Finset.sum_congr rfl fun v₂ _ ↦ hrow v₂]
  exact sum_measureReal_singleton_univ_eq_one (κ u)

/-- The entropy the `(V₁, Y₁)`-pair adds over the outer auxiliary letter alone is linear in the
weights: the coefficient at `u` is the entropy of the row `martonAuxOutput₁Row κ K W u`. -/
@[entry_point]
theorem marton_entropy_V₁Y₁_sub_entropy_V₁_eq_sum
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    entropy (martonJointDistribution (q ⊗ₘ κ) K W) (fun p ↦ (p.1, p.2.2.2.1))
        - entropy (martonJointDistribution (q ⊗ₘ κ) K W) Prod.fst
      = ∑ u : V₁, q.real {u} * ∑ y₁ : β₁, Real.negMulLog (martonAuxOutput₁Row κ K W u y₁) := by
  have hpair : ∀ (u : V₁) (y₁ : β₁),
      ((martonJointDistribution (q ⊗ₘ κ) K W).map (fun p ↦ (p.1, p.2.2.2.1))).real {(u, y₁)}
        = q.real {u} * martonAuxOutput₁Row κ K W u y₁ :=
    marton_map_V₁Y₁_real_singleton_eq_sum q κ K W
  simp only [entropy, Fintype.sum_prod_type, hpair, marton_map_V₁_real_singleton_eq q κ K W]
  exact sum_negMulLog_mul_sub_eq (fun u ↦ q.real {u}) (martonAuxOutput₁Row κ K W)
    (sum_martonAuxOutput₁Row_eq_one κ K W)

/-- The conditional law, indexed by the outer auxiliary letter `u`, that the vector-level
objective mixes: the mass `u` contributes to the pair consisting of the inner auxiliary letter
and the second output letter. -/
noncomputable def martonAuxKernelSlot (κ : Kernel V₁ V₂) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) (u : V₁) (p : V₂ × β₂) : ℝ :=
  (κ u).real {p.1} * ∑ x : α, (K (u, p.1)).real {x} * ∑ y₁ : β₁, (W x).real {(y₁, p.2)}

omit [Nonempty V₁] [MeasurableSingletonClass V₁] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Nonempty α] [MeasurableSingletonClass α] [Nonempty β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂] in
/-- Summing the mixture of the conditional laws over the inner auxiliary letter recovers the
second output marginal in the aggregate form: the weights are read only through
`fun x ↦ ∑ u, q.real {u} * martonAuxRow κ K u x`. -/
@[entry_point]
theorem sum_martonAuxKernelSlot_mixture_eq_aggregate
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (y₂ : β₂) :
    ∑ v₂ : V₂, ∑ u : V₁, q.real {u} * martonAuxKernelSlot κ K W u (v₂, y₂)
      = ∑ x : α, (∑ u : V₁, q.real {u} * martonAuxRow κ K u x)
          * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} := by
  have hmid : ∀ (v₂ : V₂) (u : V₁), q.real {u} * martonAuxKernelSlot κ K W u (v₂, y₂)
      = ∑ x : α, q.real {u} * (κ u).real {v₂} * (K (u, v₂)).real {x}
          * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} := by
    intro v₂ u
    rw [martonAuxKernelSlot, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  calc ∑ v₂ : V₂, ∑ u : V₁, q.real {u} * martonAuxKernelSlot κ K W u (v₂, y₂)
      = ∑ v₂ : V₂, ∑ u : V₁, ∑ x : α, q.real {u} * (κ u).real {v₂} * (K (u, v₂)).real {x}
          * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} :=
        Finset.sum_congr rfl fun v₂ _ ↦ Finset.sum_congr rfl fun u _ ↦ hmid v₂ u
    _ = ∑ x : α, ∑ v₂ : V₂, ∑ u : V₁, q.real {u} * (κ u).real {v₂} * (K (u, v₂)).real {x}
          * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} := Finset.sum_comm_cycle
    _ = ∑ x : α, (∑ u : V₁, q.real {u} * martonAuxRow κ K u x)
          * ∑ y₁ : β₁, (W x).real {(y₁, y₂)} := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        generalize (∑ y₁ : β₁, (W x).real {(y₁, y₂)}) = S
        rw [Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [martonAuxRow, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun v₂ _ ↦ by ring

end InformationTheory.Shannon.BroadcastChannel.Marton
