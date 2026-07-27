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
law.  The sum rate of the inner bound is bounded by both sum-rate slots of the outer bound, so
the inner quadrilateral is contained in the outer region.

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
* `marton_region_subset_uv` — Marton's inner-bound quadrilateral is contained in the UV outer
  region, again with no support hypothesis.

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

/-! ## The Markov chains carried by the Marton joint law -/

private lemma isMarkovChain_map_comp {Ω Ω' A B C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (Xs : Ω' → A) (hXs : Measurable Xs) (Zc : Ω' → C) (hZc : Measurable Zc)
    (Yo : Ω' → B) (hYo : Measurable Yo)
    (ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T)
    (h : IsMarkovChain μ (fun ω ↦ Xs (T ω)) (fun ω ↦ Zc (T ω)) (fun ω ↦ Yo (T ω))) :
    IsMarkovChain ρ Xs Zc Yo := by
  subst hρ
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hbase : (μ.map T).map Zc = μ.map (fun ω ↦ Zc (T ω)) := Measure.map_map hZc hT
  have hjoint : (μ.map T).map (fun r ↦ (Zc r, Xs r, Yo r))
      = μ.map (fun ω ↦ (Zc (T ω), Xs (T ω), Yo (T ω))) :=
    Measure.map_map (hZc.prodMk (hXs.prodMk hYo)) hT
  have hX := condDistrib_map_comp μ T hT Xs hXs Zc hZc
  have hY := condDistrib_map_comp μ T hT Yo hYo Zc hZc
  rw [hbase] at hX hY
  unfold IsMarkovChain at h ⊢
  rw [hjoint, h, hbase]
  refine Measure.compProd_congr ?_
  filter_upwards [hX, hY] with a hax hay
  ext s hs
  rw [Kernel.prod_apply, Kernel.prod_apply, hax, hay]

private lemma martonJointDistribution_eq_map
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonJointDistribution pV K W
      = ((pV ⊗ₘ K) ⊗ₘ (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)).map
          fun z ↦ (z.1.1.1, z.1.1.2, z.1.2, z.2.1, z.2.2) := by
  rw [martonJointDistribution,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable MeasurableEquiv.prodAssoc.measurable]
  rfl

private lemma martonJointDistribution_isMarkovChain₁
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsMarkovChain (martonJointDistribution pV K W)
      (fun q ↦ (q.2.1, q.1)) (fun q ↦ (q.2.1, q.2.2.1)) (fun q ↦ q.2.2.2.1) := by
  have hg : Measurable (fun m : (V₁ × V₂) × α ↦ ((m.1.2, m.2) : V₂ × α)) := by fun_prop
  have h0 := isMarkovChain_of_compProd_encoder (pV ⊗ₘ K)
    (fun m : (V₁ × V₂) × α ↦ ((m.1.2, m.2) : V₂ × α)) hg
    (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)
    (W.comap (Prod.snd : V₂ × α → α) measurable_snd) (fun _ ↦ rfl)
  have hZc : Measurable
      (fun ω : ((V₁ × V₂) × α) × (β₁ × β₂) ↦ ((ω.1.1.2, ω.1.2) : V₂ × α)) := by fun_prop
  have h1 := isMarkovChain_map_left _
    (Prod.fst : ((V₁ × V₂) × α) × (β₁ × β₂) → (V₁ × V₂) × α)
    (fun ω : ((V₁ × V₂) × α) × (β₁ × β₂) ↦ ((ω.1.1.2, ω.1.2) : V₂ × α))
    (Prod.snd : ((V₁ × V₂) × α) × (β₁ × β₂) → β₁ × β₂)
    measurable_fst hZc measurable_snd
    (f := fun m : (V₁ × V₂) × α ↦ ((m.1.2, m.1.1) : V₂ × V₁)) (by fun_prop) h0
  have h2 := isMarkovChain_swap _ _ _ _ (by fun_prop) hZc measurable_snd h1
  have h3 := isMarkovChain_map_left _ _ _ _ measurable_snd hZc (by fun_prop)
    (f := (Prod.fst : β₁ × β₂ → β₁)) measurable_fst h2
  have h4 := isMarkovChain_swap _ _ _ _ (by fun_prop) hZc (by fun_prop) h3
  exact isMarkovChain_map_comp _ _ (by fun_prop) _ (by fun_prop) _ (by fun_prop) _ (by fun_prop) _
    (martonJointDistribution_eq_map pV K W) h4

private lemma martonJointDistribution_isMarkovChain₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsMarkovChain (martonJointDistribution pV K W)
      (fun q ↦ (q.1, q.2.1)) (fun q ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.2) := by
  have hg : Measurable (fun m : (V₁ × V₂) × α ↦ ((m.1.1, m.2) : V₁ × α)) := by fun_prop
  have h0 := isMarkovChain_of_compProd_encoder (pV ⊗ₘ K)
    (fun m : (V₁ × V₂) × α ↦ ((m.1.1, m.2) : V₁ × α)) hg
    (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)
    (W.comap (Prod.snd : V₁ × α → α) measurable_snd) (fun _ ↦ rfl)
  have hZc : Measurable
      (fun ω : ((V₁ × V₂) × α) × (β₁ × β₂) ↦ ((ω.1.1.1, ω.1.2) : V₁ × α)) := by fun_prop
  have h1 := isMarkovChain_map_left _
    (Prod.fst : ((V₁ × V₂) × α) × (β₁ × β₂) → (V₁ × V₂) × α)
    (fun ω : ((V₁ × V₂) × α) × (β₁ × β₂) ↦ ((ω.1.1.1, ω.1.2) : V₁ × α))
    (Prod.snd : ((V₁ × V₂) × α) × (β₁ × β₂) → β₁ × β₂)
    measurable_fst hZc measurable_snd
    (f := fun m : (V₁ × V₂) × α ↦ ((m.1.1, m.1.2) : V₁ × V₂)) (by fun_prop) h0
  have h2 := isMarkovChain_swap _ _ _ _ (by fun_prop) hZc measurable_snd h1
  have h3 := isMarkovChain_map_left _ _ _ _ measurable_snd hZc (by fun_prop)
    (f := (Prod.snd : β₁ × β₂ → β₂)) measurable_snd h2
  have h4 := isMarkovChain_swap _ _ _ _ (by fun_prop) hZc (by fun_prop) h3
  exact isMarkovChain_map_comp _ _ (by fun_prop) _ (by fun_prop) _ (by fun_prop) _ (by fun_prop) _
    (martonJointDistribution_eq_map pV K W) h4

/-! ## The sum-rate inequalities -/

private lemma mutualInfo_le_add_condMutualInfo {Ω A B C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B]
    [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Ω → A) (Bs : Ω → B) (Cs : Ω → C)
    (hAs : Measurable As) (hBs : Measurable Bs) (hCs : Measurable Cs) :
    mutualInfo μ As Cs ≤ mutualInfo μ As Bs + condMutualInfo μ As Cs Bs := by
  have hpair : Measurable (fun ω ↦ (Bs ω, Cs ω)) := hBs.prodMk hCs
  have hdpi : mutualInfo μ As ((Prod.snd : B × C → C) ∘ fun ω ↦ (Bs ω, Cs ω))
      ≤ mutualInfo μ As (fun ω ↦ (Bs ω, Cs ω)) :=
    mutualInfo_le_of_postprocess μ As (fun ω ↦ (Bs ω, Cs ω)) hAs hpair measurable_snd
  rw [show ((Prod.snd : B × C → C) ∘ fun ω ↦ (Bs ω, Cs ω)) = Cs from rfl,
    mutualInfo_comm μ As (fun ω ↦ (Bs ω, Cs ω)) hAs hpair,
    mutualInfo_chain_rule μ Cs As Bs hCs hAs hBs, mutualInfo_comm μ Bs As hBs hAs,
    condMutualInfo_comm μ Cs As Bs hCs hAs hBs] at hdpi
  exact hdpi

private lemma condMutualInfo_aux₁_le_input
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1) (fun q ↦ q.2.2.2.1)
        (fun q ↦ q.2.1)
      ≤ condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.2.1)
        (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) :=
  ChannelCodingConverseGeneral.condMutualInfo_le_of_markov_joint
    (martonJointDistribution pV K W) (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
    (fun q ↦ q.2.1) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (martonJointDistribution_isMarkovChain₁ pV K W)
    (mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop))

private lemma condMutualInfo_aux₂_le_input
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2)
        (fun q ↦ q.1)
      ≤ condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.2.1)
        (fun q ↦ q.2.2.2.2) (fun q ↦ q.1) :=
  ChannelCodingConverseGeneral.condMutualInfo_le_of_markov_joint
    (martonJointDistribution pV K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
    (fun q ↦ q.1) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (martonJointDistribution_isMarkovChain₂ pV K W)
    (mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop))

private lemma martonInfo₁_eq_mutualInfo_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ pV K W
      = (mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1)
          (fun q ↦ q.2.2.2.1)).toReal := by
  rw [mutualInfo_toReal_eq_entropy_form (martonJointDistribution pV K W)
    (fun q ↦ q.1) (fun q ↦ q.2.2.2.1) (by fun_prop) (by fun_prop)]
  rfl

private lemma martonInfo₂_eq_mutualInfo_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₂ pV K W
      = (mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.1)
          (fun q ↦ q.2.2.2.2)).toReal := by
  rw [mutualInfo_toReal_eq_entropy_form (martonJointDistribution pV K W)
    (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2) (by fun_prop) (by fun_prop)]
  rfl

private lemma condMutualInfo_martonSwapLaw₁
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    condMutualInfo (martonSwapLaw pV K W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.2.1)
          (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) :=
  condMutualInfo_map_comp' (martonJointDistribution pV K W)
    (fun q ↦ (q.2.1, q.1, q.2.2)) (by fun_prop) (martonSwapLaw pV K W) rfl
    _ (by fun_prop) _ (by fun_prop) _ (by fun_prop)

private lemma condMutualInfo_martonSwapLaw₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    condMutualInfo (martonSwapLaw pV K W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)
      = condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.2.1)
          (fun q ↦ q.2.2.2.2) (fun q ↦ q.1) :=
  condMutualInfo_map_comp' (martonJointDistribution pV K W)
    (fun q ↦ (q.2.1, q.1, q.2.2)) (by fun_prop) (martonSwapLaw pV K W) rfl
    _ (by fun_prop) _ (by fun_prop) _ (by fun_prop)

lemma martonInfo₁_sub_martonInfoV₁V₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ pV K W - martonInfoV₁V₂ pV K W
      ≤ (condMutualInfo (martonSwapLaw pV K W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
          (fun q ↦ q.1)).toReal := by
  have hfin_a : mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1) (fun q ↦ q.2.1) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop)
  have hfin_c : condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.2.1)
      (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) ≠ ∞ :=
    condMutualInfo_ne_top _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have hle := (mutualInfo_le_add_condMutualInfo (martonJointDistribution pV K W)
      (fun q ↦ q.1) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)
      (by fun_prop) (by fun_prop) (by fun_prop)).trans
    (add_le_add le_rfl (condMutualInfo_aux₁_le_input pV K W))
  have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin_a, hfin_c⟩) hle
  rw [ENNReal.toReal_add hfin_a hfin_c] at hmono
  rw [martonInfo₁_eq_mutualInfo_toReal, martonInfoV₁V₂_eq_mutualInfo_toReal,
    condMutualInfo_martonSwapLaw₁]
  linarith

lemma martonInfo₂_sub_martonInfoV₁V₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₂ pV K W - martonInfoV₁V₂ pV K W
      ≤ (condMutualInfo (martonSwapLaw pV K W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
          (fun q ↦ q.2.1)).toReal := by
  have hfin_a : mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1) (fun q ↦ q.2.1) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop)
  have hfin_c : condMutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.2.1)
      (fun q ↦ q.2.2.2.2) (fun q ↦ q.1) ≠ ∞ :=
    condMutualInfo_ne_top _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have hle := (mutualInfo_le_add_condMutualInfo (martonJointDistribution pV K W)
      (fun q ↦ q.2.1) (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)
      (by fun_prop) (by fun_prop) (by fun_prop)).trans
    (add_le_add le_rfl (condMutualInfo_aux₂_le_input pV K W))
  rw [mutualInfo_comm (martonJointDistribution pV K W) (fun q ↦ q.2.1) (fun q ↦ q.1)
    (by fun_prop) (by fun_prop)] at hle
  have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin_a, hfin_c⟩) hle
  rw [ENNReal.toReal_add hfin_a hfin_c] at hmono
  rw [martonInfo₂_eq_mutualInfo_toReal, martonInfoV₁V₂_eq_mutualInfo_toReal,
    condMutualInfo_martonSwapLaw₂]
  linarith

lemma martonInfoSum_le_uvInfoSum₂_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W
      ≤ (uvInfoSum₂ (martonSwapLaw pV K W)).toReal := by
  have hfin : uvInfo₂ (martonSwapLaw pV K W) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop)
  have hfinc : condMutualInfo (martonSwapLaw pV K W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ q.1) ≠ ∞ :=
    condMutualInfo_ne_top _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have hA := martonInfo₁_sub_martonInfoV₁V₂_le pV K W
  have hid := martonInfo₂_eq_uvInfo₂_toReal pV K W
  rw [uvInfoSum₂, ENNReal.toReal_add hfin hfinc]
  linarith

lemma martonInfoSum_le_uvInfoSum₁_toReal
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W
      ≤ (uvInfoSum₁ (martonSwapLaw pV K W)).toReal := by
  have hfin : uvInfo₁ (martonSwapLaw pV K W) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop)
  have hfinc : condMutualInfo (martonSwapLaw pV K W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
      (fun q ↦ q.2.1) ≠ ∞ :=
    condMutualInfo_ne_top _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := martonInfo₂_sub_martonInfoV₁V₂_le pV K W
  have hid := martonInfo₁_eq_uvInfo₁_toReal pV K W
  rw [uvInfoSum₁, ENNReal.toReal_add hfin hfinc]
  linarith

/-- Marton's inner-bound quadrilateral is contained in the UV outer region: the exchanged and
re-encoded Marton joint law is one of the laws the outer union ranges over, and the three
informations of the inner bound meet its four constraints at that law.  No support hypothesis
on the input law, the auxiliary kernel or the channel is needed. -/
@[entry_point]
theorem marton_region_subset_uv
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegion pV K W ⊆ bcOuterRegionUV W := by
  rintro ⟨r₁, r₂⟩ ⟨hb₁, hb₂, hbsum⟩
  have g₁ : r₁ ≤ (uvInfo₁ (martonUVLaw pV K W)).toReal := by
    rw [uvInfo₁_martonUVLaw, ← martonInfo₁_eq_uvInfo₁_toReal]
    exact hb₁
  have g₂ : r₂ ≤ (uvInfo₂ (martonUVLaw pV K W)).toReal := by
    rw [uvInfo₂_martonUVLaw, ← martonInfo₂_eq_uvInfo₂_toReal]
    exact hb₂
  have g₃ : r₁ + r₂ ≤ (uvInfoSum₂ (martonUVLaw pV K W)).toReal := by
    rw [uvInfoSum₂_martonUVLaw]
    exact hbsum.trans (martonInfoSum_le_uvInfoSum₂_toReal pV K W)
  have g₄ : r₁ + r₂ ≤ (uvInfoSum₁ (martonUVLaw pV K W)).toReal := by
    rw [uvInfoSum₁_martonUVLaw]
    exact hbsum.trans (martonInfoSum_le_uvInfoSum₁_toReal pV K W)
  exact subset_closure (Set.mem_iUnion.mpr ⟨⟨martonUVLaw pV K W, inferInstance⟩,
    Set.mem_iUnion.mpr ⟨martonUVLaw_isUVChannelLaw pV K W, g₁, g₂, g₃, g₄⟩⟩)

end Relabel

end InformationTheory.Shannon.BroadcastChannel.Marton
