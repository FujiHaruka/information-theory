import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Meta.EntryPoint

/-!
# i.i.d. ambient `(μ, Xs, Ys)` from a joint distribution (rate-distortion variant)

This file mirrors `IIDProductInput.lean` (the channel-coding variant built from a
source pmf `p` and channel `W`), but takes a **joint distribution**
`joint : Measure (α × β)` directly as input. This is the shape required by the
rate-distortion achievability proof, where the ambient law is specified jointly
rather than as `(p ⊗ₘ W)`.

The coordinate random variables `iidXs`, `iidYs` and the joint sequence
`jointSequence iidXs iidYs` are **reused verbatim** from
`InformationTheory.Shannon.IIDProductInput`; only the underlying product measure
differs (`Measure.infinitePi (fun _ => joint)` instead of
`Measure.infinitePi (fun _ => jointDistribution p W)`).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon.ChannelCoding
  (iidXs iidYs measurable_iidXs measurable_iidYs jointSequence
    jointSequence_iidXs_iidYs measurable_jointSequence)
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Ambient measure on `ℕ → α × β` -/

/-- The i.i.d. ambient measure built from a joint distribution `joint`:
`Measure.infinitePi (fun _ : ℕ => joint)` on `ℕ → α × β`. -/
noncomputable def iidAmbientJointMeasure
    (joint : Measure (α × β)) : Measure (ℕ → α × β) :=
  Measure.infinitePi (fun _ : ℕ ↦ joint)

instance iidAmbientJointMeasure.instIsProbabilityMeasure
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] :
    IsProbabilityMeasure (iidAmbientJointMeasure joint) := by
  unfold iidAmbientJointMeasure
  infer_instance

/-! ### Marginal laws -/

/-- The joint sequence marginal at index `i` is `joint` itself. -/
lemma iidAmbientJoint_map_jointSequence
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] (i : ℕ) :
    (iidAmbientJointMeasure joint).map (jointSequence iidXs iidYs i) = joint := by
  rw [jointSequence_iidXs_iidYs]
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ joint) i

/-- The `Xs` marginal at index `i` is `joint.map Prod.fst`. -/
lemma iidAmbientJoint_map_iidXs
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] (i : ℕ) :
    (iidAmbientJointMeasure joint).map (iidXs (α := α) (β := β) i)
      = joint.map Prod.fst := by
  have h_comp : iidXs (α := α) (β := β) i
      = Prod.fst ∘ (fun ω : ℕ → α × β ↦ ω i) := by
    funext ω; rfl
  rw [h_comp, ← Measure.map_map measurable_fst (measurable_pi_apply i)]
  have h_eval : (iidAmbientJointMeasure joint).map (fun ω : ℕ → α × β ↦ ω i)
      = joint :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ joint) i
  rw [h_eval]

/-- The `Ys` marginal at index `i` is `joint.map Prod.snd`. -/
lemma iidAmbientJoint_map_iidYs
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] (i : ℕ) :
    (iidAmbientJointMeasure joint).map (iidYs (α := α) (β := β) i)
      = joint.map Prod.snd := by
  have h_comp : iidYs (α := α) (β := β) i
      = Prod.snd ∘ (fun ω : ℕ → α × β ↦ ω i) := by
    funext ω; rfl
  rw [h_comp, ← Measure.map_map measurable_snd (measurable_pi_apply i)]
  have h_eval : (iidAmbientJointMeasure joint).map (fun ω : ℕ → α × β ↦ ω i)
      = joint :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ joint) i
  rw [h_eval]

/-! ### `IdentDistrib` along each axis -/

lemma iidAmbientJoint_identDistrib_iidXs
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] (i : ℕ) :
    IdentDistrib (iidXs (α := α) (β := β) i) (iidXs 0)
      (iidAmbientJointMeasure joint) (iidAmbientJointMeasure joint) where
  aemeasurable_fst := (measurable_iidXs i).aemeasurable
  aemeasurable_snd := (measurable_iidXs 0).aemeasurable
  map_eq := by rw [iidAmbientJoint_map_iidXs, iidAmbientJoint_map_iidXs]

lemma iidAmbientJoint_identDistrib_joint
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] (i : ℕ) :
    IdentDistrib (jointSequence (α := α) (β := β) iidXs iidYs i)
      (jointSequence iidXs iidYs 0)
      (iidAmbientJointMeasure joint) (iidAmbientJointMeasure joint) where
  aemeasurable_fst :=
    (measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs i).aemeasurable
  aemeasurable_snd :=
    (measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs 0).aemeasurable
  map_eq := by rw [iidAmbientJoint_map_jointSequence, iidAmbientJoint_map_jointSequence]

/-! ### `iIndepFun` along each axis -/

lemma iidAmbientJoint_iIndepFun_iidXs
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] :
    iIndepFun (fun i : ℕ ↦ iidXs (α := α) (β := β) i) (iidAmbientJointMeasure joint) := by
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ ↦ joint)
    (X := fun _ : ℕ ↦ Prod.fst (α := α) (β := β))
    (fun _ ↦ measurable_fst)

lemma iidAmbientJoint_iIndepFun_joint
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] :
    iIndepFun (fun i : ℕ ↦ jointSequence (α := α) (β := β) iidXs iidYs i)
      (iidAmbientJointMeasure joint) := by
  have h_eq :
      (fun i : ℕ ↦ jointSequence (α := α) (β := β) iidXs iidYs i)
        = (fun (i : ℕ) (ω : ℕ → α × β) ↦ (id : α × β → α × β) (ω i)) := by
    funext i ω; rfl
  rw [h_eq]
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ ↦ joint)
    (X := fun _ : ℕ ↦ (id : α × β → α × β))
    (fun _ ↦ measurable_id)

/-! ### Positivity of singleton marginals -/

section Positivity

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [MeasurableSingletonClass β] in
lemma iidAmbientJoint_iidXs_real_singleton_pos
    [Nonempty β]
    (joint : Measure (α × β)) [IsProbabilityMeasure joint]
    (h_joint_pos : ∀ p : α × β, 0 < joint.real {p}) (x : α) :
    0 < ((iidAmbientJointMeasure joint).map (iidXs (α := α) (β := β) 0)).real {x} := by
  classical
  rw [iidAmbientJoint_map_iidXs]
  -- Pick any `b₀ : β` and bound `(joint.map Prod.fst) {x} ≥ joint {(x, b₀)} > 0`.
  obtain ⟨b₀⟩ : Nonempty β := inferInstance
  have h_pre : (Prod.fst ⁻¹' ({x} : Set α) : Set (α × β)) = ({x} : Set α) ×ˢ Set.univ := by
    ext ⟨a, b⟩; simp
  have h_map_eq : (joint.map Prod.fst) {x} = joint (({x} : Set α) ×ˢ (Set.univ : Set β)) := by
    rw [Measure.map_apply measurable_fst (measurableSet_singleton _), h_pre]
  have h_sub : ({(x, b₀)} : Set (α × β)) ⊆ ({x} : Set α) ×ˢ (Set.univ : Set β) := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    simp
  have h_le : joint {(x, b₀)} ≤ joint (({x} : Set α) ×ˢ (Set.univ : Set β)) :=
    measure_mono h_sub
  have h_pt_pos : 0 < joint {(x, b₀)} := by
    have := h_joint_pos (x, b₀)
    unfold Measure.real at this
    refine (ENNReal.toReal_pos_iff.mp this).1
  have h_total_pos : 0 < joint (({x} : Set α) ×ˢ (Set.univ : Set β)) :=
    lt_of_lt_of_le h_pt_pos h_le
  have h_total_ne_top :
      joint (({x} : Set α) ×ˢ (Set.univ : Set β)) ≠ ⊤ := measure_ne_top _ _
  unfold Measure.real
  rw [h_map_eq]
  exact ENNReal.toReal_pos h_total_pos.ne' h_total_ne_top

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] [Fintype β] [DecidableEq β] in
lemma iidAmbientJoint_iidYs_real_singleton_pos
    [Nonempty α]
    (joint : Measure (α × β)) [IsProbabilityMeasure joint]
    (h_joint_pos : ∀ p : α × β, 0 < joint.real {p}) (y : β) :
    0 < ((iidAmbientJointMeasure joint).map (iidYs (α := α) (β := β) 0)).real {y} := by
  classical
  rw [iidAmbientJoint_map_iidYs]
  obtain ⟨a₀⟩ : Nonempty α := inferInstance
  have h_pre : (Prod.snd ⁻¹' ({y} : Set β) : Set (α × β)) = Set.univ ×ˢ ({y} : Set β) := by
    ext ⟨a, b⟩; simp
  have h_map_eq : (joint.map Prod.snd) {y} = joint ((Set.univ : Set α) ×ˢ ({y} : Set β)) := by
    rw [Measure.map_apply measurable_snd (measurableSet_singleton _), h_pre]
  have h_sub : ({(a₀, y)} : Set (α × β)) ⊆ (Set.univ : Set α) ×ˢ ({y} : Set β) := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    simp
  have h_le : joint {(a₀, y)} ≤ joint ((Set.univ : Set α) ×ˢ ({y} : Set β)) :=
    measure_mono h_sub
  have h_pt_pos : 0 < joint {(a₀, y)} := by
    have := h_joint_pos (a₀, y)
    unfold Measure.real at this
    refine (ENNReal.toReal_pos_iff.mp this).1
  have h_total_pos : 0 < joint ((Set.univ : Set α) ×ˢ ({y} : Set β)) :=
    lt_of_lt_of_le h_pt_pos h_le
  have h_total_ne_top :
      joint ((Set.univ : Set α) ×ˢ ({y} : Set β)) ≠ ⊤ := measure_ne_top _ _
  unfold Measure.real
  rw [h_map_eq]
  exact ENNReal.toReal_pos h_total_pos.ne' h_total_ne_top

omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [MeasurableSingletonClass β] in
@[entry_point]
lemma iidAmbientJoint_joint_real_singleton_pos
    (joint : Measure (α × β)) [IsProbabilityMeasure joint]
    (h_joint_pos : ∀ p : α × β, 0 < joint.real {p}) (q : α × β) :
    0 < ((iidAmbientJointMeasure joint).map
          (jointSequence (α := α) (β := β) iidXs iidYs 0)).real {q} := by
  rw [iidAmbientJoint_map_jointSequence]
  exact h_joint_pos q

end Positivity

end InformationTheory.Shannon
