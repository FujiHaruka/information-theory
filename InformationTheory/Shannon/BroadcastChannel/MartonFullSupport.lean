import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.MartonUnion
import InformationTheory.Shannon.MultipleAccess.TimeSharing

/-!
# Broadcast channel — Marton's inner bound without the auxiliary support hypotheses

`marton_region_subset_capacity` asks the auxiliary law, the input kernel and the channel to
charge every letter, since the random-coding argument behind it counts jointly typical
sequences.  Only the channel hypothesis is intrinsic: an auxiliary law or an input kernel that
misses a letter is a limit of ones that do not, and the three informations of the quadrilateral
are continuous along such a smoothing, because on a finite alphabet each of them is a fixed
polynomial expression in the singleton masses composed with `Real.negMulLog`.  This file runs
that limit and removes the two auxiliary hypotheses.

## Main definitions

* `martonMixKernel K κ₀ ε` — the input kernel smoothed toward a fixed anchor measure, letter by
  letter, reusing the clamped weight of `InformationTheory.Shannon.MAC.macMix`.

## Main statements

* `marton_region_subset_capacity_of_channel_fullSupport` — a Marton quadrilateral is contained
  in the operational capacity region, under a support hypothesis on the channel alone.
* `martonRegionUnion_subset_capacity` — the whole union, not only its full-support part, is
  contained in the operational capacity region.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open InformationTheory.Shannon.BroadcastChannel InformationTheory.Shannon.ChannelCoding
open InformationTheory.Shannon.MAC
open scoped ENNReal NNReal Topology

universe u

/-! ## Smoothing the input kernel -/

section MixKernel

variable {V₁ V₂ : Type*} [Fintype V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  {α : Type*} [MeasurableSpace α]

/-- The input kernel smoothed toward a fixed anchor measure `κ₀`, letter by letter:
`martonMixKernel K κ₀ ε v = (1 - ε) • K v + ε • κ₀` with the weight clamped to `[0, 1]`.  For
`ε > 0` and a full-support anchor every letter is charged, and at `ε = 0` the kernel is `K`. -/
noncomputable def martonMixKernel (K : Kernel (V₁ × V₂) α) (κ₀ : Measure α) (ε : ℝ) :
    Kernel (V₁ × V₂) α :=
  Kernel.ofFunOfCountable fun v ↦ macMix (K v) κ₀ ε

lemma martonMixKernel_apply (K : Kernel (V₁ × V₂) α) (κ₀ : Measure α) (ε : ℝ) (v : V₁ × V₂) :
    martonMixKernel K κ₀ ε v = macMix (K v) κ₀ ε := rfl

instance martonMixKernel.instIsMarkovKernel (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (κ₀ : Measure α) [IsProbabilityMeasure κ₀] (ε : ℝ) :
    IsMarkovKernel (martonMixKernel K κ₀ ε) :=
  ⟨fun v ↦ by rw [martonMixKernel_apply]; infer_instance⟩

lemma martonMixKernel_zero (K : Kernel (V₁ × V₂) α) (κ₀ : Measure α) :
    martonMixKernel K κ₀ 0 = K :=
  Kernel.ext fun v ↦ by rw [martonMixKernel_apply, macMix_zero]

end MixKernel

/-! ## Continuity of the three informations along the smoothing -/

section Continuity

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

variable (pV μ₀ : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] [IsProbabilityMeasure μ₀]
  (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (κ₀ : Measure α) [IsProbabilityMeasure κ₀]
  (W : BCChannel α β₁ β₂) [IsMarkovKernel W]

lemma martonMixJoint_real_continuous (q : V₁ × V₂ × α × β₁ × β₂) :
    Continuous fun ε : ℝ ↦
      (martonJointDistribution (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W).real {q} := by
  classical
  obtain ⟨v₁, v₂, x, y₁, y₂⟩ := q
  have hrw : (fun ε : ℝ ↦ (martonJointDistribution (macMix pV μ₀ ε)
        (martonMixKernel K κ₀ ε) W).real {(v₁, v₂, x, y₁, y₂)})
      = fun ε : ℝ ↦ (macMix pV μ₀ ε).real {(v₁, v₂)}
        * (macMix (K (v₁, v₂)) κ₀ ε).real {x} * (W x).real {(y₁, y₂)} := by
    funext ε
    simpa [martonMixKernel_apply] using martonJointDistribution_real_singleton
      (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W (v₁, v₂) x (y₁, y₂)
  rw [hrw]
  exact ((macMix_real_continuous pV μ₀ (v₁, v₂)).mul
    (macMix_real_continuous (K (v₁, v₂)) κ₀ x)).mul continuous_const

lemma martonMixJoint_map_real_continuous {γ : Type*}
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (f : V₁ × V₂ × α × β₁ × β₂ → γ) (hf : Measurable f) (x : γ) :
    Continuous fun ε : ℝ ↦
      ((martonJointDistribution (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W).map f).real {x} := by
  classical
  have hrw : (fun ε : ℝ ↦
      ((martonJointDistribution (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W).map f).real {x})
      = fun ε : ℝ ↦ ∑ q ∈ Finset.univ.filter fun q ↦ f q = x,
        (martonJointDistribution (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W).real {q} := by
    funext ε
    exact map_real_singleton_fiber_sum _ f hf x
  rw [hrw]
  exact continuous_finsetSum _ fun q _ ↦ martonMixJoint_real_continuous pV μ₀ K κ₀ W q

lemma martonMix_entropy_continuous {γ : Type*} [Fintype γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (f : V₁ × V₂ × α × β₁ × β₂ → γ) (hf : Measurable f) :
    Continuous fun ε : ℝ ↦
      entropy (martonJointDistribution (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W) f := by
  unfold entropy
  exact continuous_finsetSum _ fun x _ ↦
    Real.continuous_negMulLog.comp (martonMixJoint_map_real_continuous pV μ₀ K κ₀ W f hf x)

lemma martonInfo₁_mix_continuous :
    Continuous fun ε : ℝ ↦ martonInfo₁ (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W := by
  unfold martonInfo₁
  exact ((martonMix_entropy_continuous pV μ₀ K κ₀ W Prod.fst measurable_fst).add
    (martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ q.2.2.2.1) (by fun_prop))).sub
    (martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ (q.1, q.2.2.2.1)) (by fun_prop))

lemma martonInfo₂_mix_continuous :
    Continuous fun ε : ℝ ↦ martonInfo₂ (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W := by
  unfold martonInfo₂
  exact ((martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ q.2.1) (by fun_prop)).add
    (martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ q.2.2.2.2) (by fun_prop))).sub
    (martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ (q.2.1, q.2.2.2.2)) (by fun_prop))

lemma martonInfoV₁V₂_mix_continuous :
    Continuous fun ε : ℝ ↦ martonInfoV₁V₂ (macMix pV μ₀ ε) (martonMixKernel K κ₀ ε) W := by
  unfold martonInfoV₁V₂
  exact ((martonMix_entropy_continuous pV μ₀ K κ₀ W Prod.fst measurable_fst).add
    (martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ q.2.1) (by fun_prop))).sub
    (martonMix_entropy_continuous pV μ₀ K κ₀ W (fun q ↦ (q.1, q.2.1)) (by fun_prop))

end Continuity

/-! ## The inner bound under a channel hypothesis alone -/

section Region

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

private lemma uniformOfFintype_real_singleton_pos {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (x : X) :
    0 < ((PMF.uniformOfFintype X).toMeasure).real {x} := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- Marton's inner bound sits inside the operational capacity region under a support hypothesis
on the channel alone.  Smoothing the auxiliary law and the input kernel toward the uniform ones
makes them charge every letter, and the three informations of the quadrilateral are continuous
along that smoothing, so the two support hypotheses that `marton_region_subset_capacity` asks of
them are not needed.  The channel hypothesis `hW` is a regularity precondition of the coding
argument and carries no part of it. -/
@[entry_point]
theorem marton_region_subset_capacity_of_channel_fullSupport
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegion pV K W ⊆ bcCapacityRegion W := by
  classical
  set μ₀ : Measure (V₁ × V₂) := (PMF.uniformOfFintype (V₁ × V₂)).toMeasure with hμ₀
  set κ₀ : Measure α := (PMF.uniformOfFintype α).toMeasure with hκ₀
  haveI : IsProbabilityMeasure μ₀ := by rw [hμ₀]; infer_instance
  haveI : IsProbabilityMeasure κ₀ := by rw [hκ₀]; infer_instance
  have hμ₀pos : ∀ v : V₁ × V₂, 0 < μ₀.real {v} := by
    rw [hμ₀]; exact fun v ↦ uniformOfFintype_real_singleton_pos v
  have hκ₀pos : ∀ a : α, 0 < κ₀.real {a} := by
    rw [hκ₀]; exact fun a ↦ uniformOfFintype_real_singleton_pos a
  intro p hM
  refine bc_mem_closure_of_strictly_below W p fun ε hε ↦ ?_
  have htend₁ : Tendsto (fun t : ℝ ↦ martonInfo₁ (macMix pV μ₀ t) (martonMixKernel K κ₀ t) W)
      (𝓝[>] (0 : ℝ)) (𝓝 (martonInfo₁ pV K W)) := by
    have h := (martonInfo₁_mix_continuous pV μ₀ K κ₀ W).tendsto 0
    rw [macMix_zero, martonMixKernel_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htend₂ : Tendsto (fun t : ℝ ↦ martonInfo₂ (macMix pV μ₀ t) (martonMixKernel K κ₀ t) W)
      (𝓝[>] (0 : ℝ)) (𝓝 (martonInfo₂ pV K W)) := by
    have h := (martonInfo₂_mix_continuous pV μ₀ K κ₀ W).tendsto 0
    rw [macMix_zero, martonMixKernel_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htend₁₂ : Tendsto (fun t : ℝ ↦ martonInfoV₁V₂ (macMix pV μ₀ t) (martonMixKernel K κ₀ t) W)
      (𝓝[>] (0 : ℝ)) (𝓝 (martonInfoV₁V₂ pV K W)) := by
    have h := (martonInfoV₁V₂_mix_continuous pV μ₀ K κ₀ W).tendsto 0
    rw [macMix_zero, martonMixKernel_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hA := htend₁.eventually_const_lt
    (show martonInfo₁ pV K W - ε / 2 < martonInfo₁ pV K W by linarith)
  have hB := htend₂.eventually_const_lt
    (show martonInfo₂ pV K W - ε / 2 < martonInfo₂ pV K W by linarith)
  have hC := htend₁₂.eventually_lt_const
    (show martonInfoV₁V₂ pV K W < martonInfoV₁V₂ pV K W + ε / 2 by linarith)
  obtain ⟨t, ⟨hA', hB', hC'⟩, ht⟩ :=
    ((hA.and (hB.and hC)).and eventually_mem_nhdsWithin).exists
  refine bc_strict_interior_achievable (macMix pV μ₀ t) (martonMixKernel K κ₀ t) W
    (fun v ↦ macMix_full_support pV μ₀ hμ₀pos ht v) (fun v a ↦ ?_) hW ?_ ?_ ?_
  · rw [martonMixKernel_apply]
    exact macMix_full_support (K v) κ₀ hκ₀pos ht a
  · linarith [hM.bound₁]
  · linarith [hM.bound₂]
  · linarith [hM.boundSum]

end Region

section Union

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- Marton's inner bound is achievable in full: the union over all auxiliary laws and input
kernels, not only over the full-support ones, is contained in the operational capacity region.
Only the channel is required to have full support. -/
@[entry_point]
theorem martonRegionUnion_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegionUnion W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ (bc_capacityRegion_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦ ?_
  exact marton_region_subset_capacity_of_channel_fullSupport pV K W hW

end Union

end InformationTheory.Shannon.BroadcastChannel.Marton
