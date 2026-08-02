import InformationTheory.Shannon.BroadcastChannel.Marton.Setup
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient
import InformationTheory.Shannon.Pi

/-!
# Marton's inner bound — exchanging the two receivers

The Marton data `(pV, K, W)` is symmetric in the two receivers: exchanging the two auxiliary
letters of `pV` and `K` and the two outputs of `W` produces Marton data for the same channel
read the other way round.  This file records that symmetry at the level of the five-variable
law and of the three informations of the region inequalities, so that a statement proved for
the first auxiliary alphabet transfers to the second one by reindexing rather than by a
mirrored proof.

## Main statements

* `martonJointDistribution_swap` — the five-variable law of the exchanged data is the
  pushforward of the original law along the map exchanging both auxiliary letters and both
  outputs.
* `martonInfo₁_swap` / `martonInfo₂_swap` — the two receiver informations trade places under
  the exchange.
* `martonInfoV₁V₂_swap` — the auxiliary dependence is unchanged by the exchange.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel

variable {α β₁ β₂ V₁ V₂ : Type*}
  [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
  [MeasurableSpace V₁] [MeasurableSpace V₂]

/-- @audit:ok -/
lemma martonJointDistribution_swap
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonJointDistribution (pV.map Prod.swap) (K.comap Prod.swap measurable_swap)
        (W.map Prod.swap)
      = (martonJointDistribution pV K W).map
          (fun q ↦ (q.2.1, q.1, q.2.2.1, q.2.2.2.2, q.2.2.2.1)) := by
  haveI : IsMarkovKernel (W.map (Prod.swap : β₁ × β₂ → β₂ × β₁)) :=
    Kernel.IsMarkovKernel.map W measurable_swap
  set f : (V₁ × V₂) × α → (V₂ × V₁) × α := fun z ↦ (z.1.swap, z.2) with hf_def
  have hf : Measurable f := (measurable_swap.comp measurable_fst).prodMk measurable_snd
  have hKback :
      (K.comap (Prod.swap : V₂ × V₁ → V₁ × V₂) measurable_swap).comap
        (Prod.swap : V₁ × V₂ → V₂ × V₁) measurable_swap = K :=
    Kernel.ext fun _ ↦ rfl
  have hstep₁ : (pV ⊗ₘ K).map f
      = (pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)) ⊗ₘ
          (K.comap (Prod.swap : V₂ × V₁ → V₁ × V₂) measurable_swap) := by
    have h := compProd_comap_map_prodMap pV
      (K.comap (Prod.swap : V₂ × V₁ → V₁ × V₂) measurable_swap)
      (measurable_swap : Measurable (Prod.swap : V₁ × V₂ → V₂ × V₁))
    rwa [hKback] at h
  have hWmap :
      (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd).map
          (Prod.swap : β₁ × β₂ → β₂ × β₁)
        = ((W.map (Prod.swap : β₁ × β₂ → β₂ × β₁)).comap
            (Prod.snd : (V₂ × V₁) × α → α) measurable_snd).comap f hf :=
    Kernel.ext fun _ ↦ by
      simp only [Kernel.map_apply _ measurable_swap, Kernel.comap_apply, hf_def]
  have hstep₂ :
      ((pV ⊗ₘ K) ⊗ₘ (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)).map
          (Prod.map f (Prod.swap : β₁ × β₂ → β₂ × β₁))
        = ((pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)) ⊗ₘ
            (K.comap (Prod.swap : V₂ × V₁ → V₁ × V₂) measurable_swap)) ⊗ₘ
          ((W.map (Prod.swap : β₁ × β₂ → β₂ × β₁)).comap
            (Prod.snd : (V₂ × V₁) × α → α) measurable_snd) := by
    have h := compProd_map_prodMap (pV ⊗ₘ K)
      (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd) hf measurable_swap
      ((W.map (Prod.swap : β₁ × β₂ → β₂ × β₁)).comap
        (Prod.snd : (V₂ × V₁) × α → α) measurable_snd) hWmap
    rwa [hstep₁] at h
  have hG : Measurable (Prod.map f (Prod.swap : β₁ × β₂ → β₂ × β₁)) := hf.prodMap measurable_swap
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦
      (q.2.1, q.1, q.2.2.1, q.2.2.2.2, q.2.2.2.1)) := by fun_prop
  unfold martonJointDistribution
  rw [← hstep₂, Measure.map_map MeasurableEquiv.prodAssoc.measurable hG,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable
      (MeasurableEquiv.prodAssoc.measurable.comp hG),
    Measure.map_map hQ MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (hQ.comp MeasurableEquiv.prodAssoc.measurable)
      MeasurableEquiv.prodAssoc.measurable]
  rfl

section FirstReceiver

variable [Fintype V₂] [Fintype β₂]

/-- @audit:ok -/
lemma martonInfo₁_swap
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ (pV.map Prod.swap) (K.comap Prod.swap measurable_swap) (W.map Prod.swap)
      = martonInfo₂ pV K W := by
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦
      (q.2.1, q.1, q.2.2.1, q.2.2.2.2, q.2.2.2.1)) := by fun_prop
  unfold martonInfo₁ martonInfo₂
  rw [martonJointDistribution_swap pV K W, entropy_map_comp _ hQ measurable_fst,
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ r.2.2.2.1) _ hQ (by fun_prop),
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ (r.1, r.2.2.2.1)) _ hQ (by fun_prop)]

end FirstReceiver

section SecondReceiver

variable [Fintype V₁] [Fintype β₁]

/-- @audit:ok -/
lemma martonInfo₂_swap
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₂ (pV.map Prod.swap) (K.comap Prod.swap measurable_swap) (W.map Prod.swap)
      = martonInfo₁ pV K W := by
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦
      (q.2.1, q.1, q.2.2.1, q.2.2.2.2, q.2.2.2.1)) := by fun_prop
  unfold martonInfo₁ martonInfo₂
  rw [martonJointDistribution_swap pV K W,
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ r.2.1) _ hQ (by fun_prop),
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ r.2.2.2.2) _ hQ (by fun_prop),
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ (r.2.1, r.2.2.2.2)) _ hQ
      (by fun_prop)]

end SecondReceiver

section Auxiliaries

variable [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]

/-- @audit:ok -/
lemma martonInfoV₁V₂_swap
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfoV₁V₂ (pV.map Prod.swap) (K.comap Prod.swap measurable_swap) (W.map Prod.swap)
      = martonInfoV₁V₂ pV K W := by
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦
      (q.2.1, q.1, q.2.2.1, q.2.2.2.2, q.2.2.2.1)) := by fun_prop
  have hpair : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) := by fun_prop
  have hcomm : entropy (martonJointDistribution pV K W)
        (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.2.1, q.1))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.1)) :=
    entropy_measurableEquiv_comp _ _ hpair MeasurableEquiv.prodComm
  unfold martonInfoV₁V₂
  rw [martonJointDistribution_swap pV K W, entropy_map_comp _ hQ measurable_fst,
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ r.2.1) _ hQ (by fun_prop),
    entropy_map_comp (Xs := fun r : V₂ × V₁ × α × β₂ × β₁ ↦ (r.1, r.2.1)) _ hQ (by fun_prop),
    hcomm]
  ring

end Auxiliaries

end InformationTheory.Shannon.BroadcastChannel.Marton
