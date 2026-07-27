import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly

/-!
# Broadcast channel — Marton's inner-bound law as a UV channel law

Marton's inner bound and the UV outer bound both live over five-tuple laws
`(V₁, V₂, X, Y₁, Y₂)` of the same type, but they index the two auxiliaries in opposite order: an
outer information slot pairs the second auxiliary with the first receiver, while an inner one
pairs the first auxiliary with it.  This file puts the two on one index.  The Marton joint law is
a channel law of `W`; exchanging its two auxiliaries preserves that, and re-encoding the two
finite auxiliary alphabets into `ℕ` lands the law in the family indexing the UV outer region.
The two corner informations of the inner bound are then the corresponding slots of the exchanged
law, and its auxiliary dependence is the mutual information of the two auxiliaries of the joint
law.

## Main definitions

* `auxNatIndex X` — the index of a letter of the finite alphabet `X`, as a natural number.
* `martonSwapLaw` — the Marton joint law with its two auxiliaries exchanged.
* `martonUVLaw` — the exchanged law re-encoded over the natural-number auxiliaries indexing
  `bcOuterRegionUV`.

## Main statements

* `martonJointDistribution_isUVChannelLaw` — the Marton joint law is a channel law of `W`.  No
  support hypothesis on the input law, the auxiliary kernel or the channel is needed.
* `martonUVLaw_isUVChannelLaw` — so is its exchanged and re-encoded form, which is therefore one
  of the laws the union defining `bcOuterRegionUV` ranges over.
* `martonInfo₁_eq_uvInfo₁_toReal` and `martonInfo₂_eq_uvInfo₂_toReal` — the two corner
  informations of the inner bound, defined as entropy differences over `ℝ`, are the corresponding
  slots of the exchanged law.
* `martonInfoV₁V₂_eq_mutualInfo_toReal` — the auxiliary dependence of the inner bound is the
  mutual information of the two auxiliaries of the Marton joint law.

## Implementation notes

`IsUVChannelLaw` reads the two auxiliaries and the input letter as one block, so it does not see
their order: the Marton law satisfies it with no exchange at all, and the exchange enters only
where an information slot is read.  The exchanged law is given a name of its own, and an
`IsProbabilityMeasure` instance, because the slot lemmas of the re-encoding need that instance at
a law that is not syntactically a `martonJointDistribution`.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open InformationTheory.Shannon.MAC
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## The Marton joint law is a channel law -/

section ChannelLaw

variable {V₁ V₂ α β₁ β₂ : Type*}
  [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace α]
  [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- The Marton joint law is a channel law of `W`: its outputs are drawn from the channel at the
input letter and the two auxiliaries reach them through that letter only.  The law is built as a
composition-product chain ending in `W`, so this holds with no support hypothesis on the input
law, on the auxiliary kernel or on the channel. -/
@[entry_point]
theorem martonJointDistribution_isUVChannelLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsUVChannelLaw W (martonJointDistribution pV K W) := by
  set g : (V₁ × V₂) × α → V₁ × V₂ × α := fun z ↦ (z.1.1, z.1.2, z.2) with hg_def
  have hg : Measurable g :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hkernel :
      (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)
        = (W.comap (fun r : V₁ × V₂ × α ↦ r.2.2)
            (measurable_snd.comp measurable_snd)).comap g hg :=
    Kernel.ext fun _ ↦ rfl
  have hsplit : Measurable
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) := by fun_prop
  have hfirst : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) := by fun_prop
  unfold IsUVChannelLaw martonJointDistribution
  rw [Measure.map_map hsplit MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (hsplit.comp MeasurableEquiv.prodAssoc.measurable)
      MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map hfirst MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (hfirst.comp MeasurableEquiv.prodAssoc.measurable)
      MeasurableEquiv.prodAssoc.measurable]
  have hcompL :
      ((fun q : V₁ × V₂ × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ∘
        (MeasurableEquiv.prodAssoc :
          ((V₁ × V₂) × α × β₁ × β₂) ≃ᵐ (V₁ × V₂ × α × β₁ × β₂))) ∘
        (MeasurableEquiv.prodAssoc :
          (((V₁ × V₂) × α) × β₁ × β₂) ≃ᵐ ((V₁ × V₂) × α × β₁ × β₂))
        = fun z : ((V₁ × V₂) × α) × (β₁ × β₂) ↦ (g z.1, z.2) := rfl
  have hcompR :
      ((fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) ∘
        (MeasurableEquiv.prodAssoc :
          ((V₁ × V₂) × α × β₁ × β₂) ≃ᵐ (V₁ × V₂ × α × β₁ × β₂))) ∘
        (MeasurableEquiv.prodAssoc :
          (((V₁ × V₂) × α) × β₁ × β₂) ≃ᵐ ((V₁ × V₂) × α × β₁ × β₂))
        = g ∘ Prod.fst := rfl
  rw [hcompL, hcompR, ← Measure.map_map hg measurable_fst,
    show ((pV ⊗ₘ K) ⊗ₘ (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)).map Prod.fst
        = pV ⊗ₘ K from Measure.fst_compProd _ _,
    hkernel,
    compProd_comap_map_prodMap (pV ⊗ₘ K)
      (W.comap (fun r : V₁ × V₂ × α ↦ r.2.2) (measurable_snd.comp measurable_snd)) hg]

/-- The Marton joint law with its two auxiliaries exchanged, which is the order in which the
information slots of the UV outer bound read them. -/
noncomputable def martonSwapLaw (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) : Measure (V₂ × V₁ × α × β₁ × β₂) :=
  (martonJointDistribution pV K W).map fun q ↦ (q.2.1, q.1, q.2.2)

instance martonSwapLaw.instIsProbabilityMeasure
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (martonSwapLaw pV K W) :=
  Measure.isProbabilityMeasure_map
    (by fun_prop : Measurable
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.2.1, q.1, q.2.2))).aemeasurable

lemma martonSwapLaw_isUVChannelLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsUVChannelLaw W (martonSwapLaw pV K W) :=
  (martonJointDistribution_isUVChannelLaw pV K W).swap_auxiliaries

end ChannelLaw

/-! ## The natural-number auxiliaries of the outer region -/

section Relabel

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The index of a letter of a finite alphabet, as a natural number.  This is the re-encoding
carrying a law over finite auxiliary alphabets to the natural-number auxiliaries over which the
union defining `bcOuterRegionUV` is taken. -/
noncomputable def auxNatIndex (X : Type*) [Fintype X] (x : X) : ℕ := Fintype.equivFin X x

lemma auxNatIndex_injective (X : Type*) [Fintype X] : Function.Injective (auxNatIndex X) :=
  fun _ _ h ↦ (Fintype.equivFin X).injective (Fin.val_injective h)

/-- The exchanged Marton joint law, re-encoded over the natural-number auxiliaries indexing the
UV outer region. -/
noncomputable def martonUVLaw (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) : Measure (ℕ × ℕ × α × β₁ × β₂) :=
  (martonSwapLaw pV K W).map
    (uvRelabel (α := α) (β₁ := β₁) (β₂ := β₂) (auxNatIndex V₂) (auxNatIndex V₁))

instance martonUVLaw.instIsProbabilityMeasure
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (martonUVLaw pV K W) :=
  Measure.isProbabilityMeasure_map
    (measurable_uvRelabel (measurable_of_countable (auxNatIndex V₂))
      (measurable_of_countable (auxNatIndex V₁))).aemeasurable

/-- The exchanged and re-encoded Marton joint law is a channel law of `W`, hence one of the laws
the union defining `bcOuterRegionUV` ranges over. -/
@[entry_point]
theorem martonUVLaw_isUVChannelLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsUVChannelLaw W (martonUVLaw pV K W) :=
  (martonSwapLaw_isUVChannelLaw pV K W).map_auxiliaries
    (f := auxNatIndex V₂) (g := auxNatIndex V₁)
    (measurable_of_countable _) (measurable_of_countable _)

lemma uvInfo₁_martonUVLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    uvInfo₁ (martonUVLaw pV K W) = uvInfo₁ (martonSwapLaw pV K W) := by
  have hd : ∀ v : V₁, Function.invFun (auxNatIndex V₁) (auxNatIndex V₁ v) = v :=
    Function.leftInverse_invFun (auxNatIndex_injective V₁)
  exact uvInfo₁_map_uvRelabel _ (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) hd

lemma uvInfo₂_martonUVLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    uvInfo₂ (martonUVLaw pV K W) = uvInfo₂ (martonSwapLaw pV K W) := by
  have hd : ∀ u : V₂, Function.invFun (auxNatIndex V₂) (auxNatIndex V₂ u) = u :=
    Function.leftInverse_invFun (auxNatIndex_injective V₂)
  exact uvInfo₂_map_uvRelabel _ (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) hd

lemma uvInfoSum₂_martonUVLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    uvInfoSum₂ (martonUVLaw pV K W) = uvInfoSum₂ (martonSwapLaw pV K W) := by
  have hd : ∀ u : V₂, Function.invFun (auxNatIndex V₂) (auxNatIndex V₂ u) = u :=
    Function.leftInverse_invFun (auxNatIndex_injective V₂)
  exact uvInfoSum₂_map_uvRelabel _ (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) hd

lemma uvInfoSum₁_martonUVLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    uvInfoSum₁ (martonUVLaw pV K W) = uvInfoSum₁ (martonSwapLaw pV K W) := by
  have hd : ∀ v : V₁, Function.invFun (auxNatIndex V₁) (auxNatIndex V₁ v) = v :=
    Function.leftInverse_invFun (auxNatIndex_injective V₁)
  exact uvInfoSum₁_map_uvRelabel _ (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) hd

/-! ## The informations of the inner bound as slots of the exchanged law -/

lemma martonInfo₁_eq_uvInfo₁_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ pV K W = (uvInfo₁ (martonSwapLaw pV K W)).toReal := by
  rw [martonSwapLaw, uvInfo₁, mutualInfo_map_comp (martonJointDistribution pV K W)
      (fun q ↦ (q.2.1, q.1, q.2.2)) (by fun_prop)
      (fun q ↦ q.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop),
    mutualInfo_toReal_eq_entropy_form (martonJointDistribution pV K W)
      (fun q ↦ q.1) (fun q ↦ q.2.2.2.1) (by fun_prop) (by fun_prop)]
  rfl

lemma martonInfo₂_eq_uvInfo₂_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₂ pV K W = (uvInfo₂ (martonSwapLaw pV K W)).toReal := by
  rw [martonSwapLaw, uvInfo₂, mutualInfo_map_comp (martonJointDistribution pV K W)
      (fun q ↦ (q.2.1, q.1, q.2.2)) (by fun_prop)
      (fun q ↦ q.1) (by fun_prop) (fun q ↦ q.2.2.2.2) (by fun_prop),
    mutualInfo_toReal_eq_entropy_form (martonJointDistribution pV K W)
      (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2) (by fun_prop) (by fun_prop)]
  rfl

lemma martonInfoV₁V₂_eq_mutualInfo_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfoV₁V₂ pV K W
      = (mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1) (fun q ↦ q.2.1)).toReal := by
  rw [mutualInfo_toReal_eq_entropy_form (martonJointDistribution pV K W)
    (fun q ↦ q.1) (fun q ↦ q.2.1) (by fun_prop) (by fun_prop)]
  rfl

end Relabel

end InformationTheory.Shannon.BroadcastChannel.Marton
