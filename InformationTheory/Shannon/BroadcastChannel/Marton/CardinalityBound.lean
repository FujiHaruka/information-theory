import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Marton.ObjectiveAssembly
import InformationTheory.Shannon.BroadcastChannel.MartonUnion
import InformationTheory.Shannon.BroadcastChannel.Marton.Swap

/-!
# Broadcast channel — cardinality bounds for the Marton auxiliary alphabets

The support reduction replaces the law of the outer auxiliary letter by one charging at most
`Fintype.card α` letters, but leaves it on its original alphabet.  This file carries such a law
onto an alphabet of that many letters: the support of the law is a subtype of the original
alphabet, its inclusion is injective, and the three informations of the region inequalities are
unchanged when either auxiliary alphabet is relabeled by an injective measurable map.

The same statement for the inner auxiliary alphabet is the one for the outer alphabet read
through the exchange of the two receivers: the exchange trades the two receiver informations and
fixes the auxiliary dependence, so it trades the two receiver weights and leaves the sum-rate
weight where it is.

## Main definitions

* `martonAuxBound α` — the cardinality cap on a Marton auxiliary alphabet, the size of the input
  alphabet.

## Main statements

* `martonInfo₁_map_injective` / `martonInfo₂_map_injective` / `martonInfoV₁V₂_map_injective` — the
  three informations are unchanged when the auxiliary alphabet they read is relabeled by an
  injective measurable map and the other one by an arbitrary measurable map.
* `exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights` — the outer auxiliary law can be
  replaced by a law on `bcAuxAlphabet k` with `k < martonAuxBound α`, without decreasing the
  weighted sum of the three informations of the region inequalities.
* `exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights_inner` — the same for the inner
  auxiliary alphabet, with the roles of the two receiver weights exchanged.

## Implementation notes

The relabeling invariance of `martonRegion` is stated for measurable equivalences, which cannot
shrink an alphabet.  The maps used here point the other way: the inclusion of the support subtype
into the original alphabet is injective but not surjective, and the transport of the joint
distribution needs no injectivity at all, so the equivalence hypothesis is dropped on both counts.

`entropy_injective_comp` is the injective form of the entropy invariance.  The same statement with
a `DecidableEq` hypothesis is `wz_entropy_map_injective` of
`InformationTheory/Shannon/WynerZiv/Achievability/Covering.lean`, which is outside the import
closure of this file; the two belong next to `entropy_measurableEquiv_comp` in
`InformationTheory/Shannon/Pi.lean` and should be merged there.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel

universe u

section Entropy

lemma entropy_injective_comp {Ω γ₀ δ₀ : Type*} [MeasurableSpace Ω]
    [Fintype γ₀] [Nonempty γ₀] [MeasurableSpace γ₀] [MeasurableSingletonClass γ₀]
    [Fintype δ₀] [Nonempty δ₀] [MeasurableSpace δ₀] [MeasurableSingletonClass δ₀]
    (μ : Measure Ω) (X : Ω → γ₀) (hX : Measurable X)
    (g : γ₀ → δ₀) (hg : Function.Injective g) (hgmeas : Measurable g) :
    entropy μ (fun ω ↦ g (X ω)) = entropy μ X := by
  classical
  have hgX : Measurable (fun ω ↦ g (X ω)) := hgmeas.comp hX
  have hmass : ∀ a : γ₀, (μ.map (fun ω ↦ g (X ω))).real {g a} = (μ.map X).real {a} := by
    intro a
    rw [map_measureReal_apply hgX (MeasurableSet.singleton (g a)),
        map_measureReal_apply hX (MeasurableSet.singleton a)]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ hg h, fun h ↦ by rw [h]⟩
  unfold entropy
  rw [show (∑ a, Real.negMulLog ((μ.map X).real {a}))
        = ∑ a, Real.negMulLog ((μ.map (fun ω ↦ g (X ω))).real {g a}) from
      Finset.sum_congr rfl (fun a _ ↦ by rw [hmass a]),
      ← Finset.sum_image (s := (Finset.univ : Finset γ₀))
        (f := fun d ↦ Real.negMulLog ((μ.map (fun ω ↦ g (X ω))).real {d}))
        (fun a _ b _ h ↦ hg h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  have hpre : (fun ω ↦ g (X ω)) ⁻¹' {d} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hgd
    exact hd (Finset.mem_image.mpr ⟨X ω, Finset.mem_univ _, hgd⟩)
  rw [map_measureReal_apply hgX (MeasurableSet.singleton d), hpre,
      measureReal_empty, Real.negMulLog_zero]

end Entropy

/-! ## Relabeling an auxiliary alphabet by an injective map -/

section Relabel

variable {α : Type u} {β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
  {V₁ V₂ V₁' V₂' : Type*} [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace V₁']
  [MeasurableSpace V₂']

lemma martonJointDistribution_map_injective
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K' : Kernel (V₁' × V₂') α) [IsMarkovKernel K']
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (f₁ : V₁ → V₁') (hf₁ : Measurable f₁) (f₂ : V₂ → V₂') (hf₂ : Measurable f₂) :
    martonJointDistribution (pV.map (fun v ↦ (f₁ v.1, f₂ v.2))) K' W
      = (martonJointDistribution pV
            (K'.comap (fun v ↦ (f₁ v.1, f₂ v.2))
              ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))) W).map
          (fun q ↦ (f₁ q.1, f₂ q.2.1, q.2.2)) := by
  set F : V₁ × V₂ → V₁' × V₂' := fun v ↦ (f₁ v.1, f₂ v.2)
  have hF : Measurable F := (hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd)
  set g : (V₁ × V₂) × α → (V₁' × V₂') × α := fun z ↦ (F z.1, z.2)
  have hg : Measurable g := (hF.comp measurable_fst).prodMk measurable_snd
  have hWcomap :
      (W.comap (Prod.snd : (V₁' × V₂') × α → α) measurable_snd).comap g hg
        = W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd :=
    Kernel.ext fun _ ↦ rfl
  have hstep₁ : (pV ⊗ₘ (K'.comap F hF)).map g = (pV.map F) ⊗ₘ K' :=
    compProd_comap_map_prodMap pV K' hF
  have hstep₂ :
      ((pV ⊗ₘ (K'.comap F hF)) ⊗ₘ (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)).map
          (fun z ↦ (g z.1, z.2))
        = ((pV.map F) ⊗ₘ K') ⊗ₘ
            (W.comap (Prod.snd : (V₁' × V₂') × α → α) measurable_snd) := by
    have h := compProd_comap_map_prodMap (pV ⊗ₘ (K'.comap F hF))
      (W.comap (Prod.snd : (V₁' × V₂') × α → α) measurable_snd) hg
    rwa [hWcomap, hstep₁] at h
  have hG : Measurable (fun z : ((V₁ × V₂) × α) × β₁ × β₂ ↦ (g z.1, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2)) :=
    (hf₁.comp measurable_fst).prodMk
      ((hf₂.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  unfold martonJointDistribution
  rw [← hstep₂, Measure.map_map MeasurableEquiv.prodAssoc.measurable hG,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable
      (MeasurableEquiv.prodAssoc.measurable.comp hG),
    Measure.map_map hQ MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (hQ.comp MeasurableEquiv.prodAssoc.measurable)
      MeasurableEquiv.prodAssoc.measurable]
  rfl

section Information

section FirstReceiver

variable [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁]
  [Fintype V₁'] [Nonempty V₁'] [MeasurableSingletonClass V₁']
  [Fintype β₁] [Nonempty β₁] [MeasurableSingletonClass β₁]

lemma martonInfo₁_map_injective
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K' : Kernel (V₁' × V₂') α) [IsMarkovKernel K']
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (f₁ : V₁ → V₁') (hf₁ : Measurable f₁) (hinj₁ : Function.Injective f₁)
    (f₂ : V₂ → V₂') (hf₂ : Measurable f₂) :
    martonInfo₁ (pV.map (fun v ↦ (f₁ v.1, f₂ v.2))) K' W
      = martonInfo₁ pV
          (K'.comap (fun v ↦ (f₁ v.1, f₂ v.2))
            ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))) W := by
  set K := K'.comap (fun v : V₁ × V₂ ↦ (f₁ v.1, f₂ v.2))
    ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2)) :=
    (hf₁.comp measurable_fst).prodMk
      ((hf₂.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have haux : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) Prod.fst
      = entropy (martonJointDistribution pV K W) Prod.fst := by
    rw [entropy_map_comp _ hQ measurable_fst]
    exact entropy_injective_comp _ Prod.fst measurable_fst f₁ hinj₁ hf₁
  have hout : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ r.2.2.2.1)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.1) :=
    entropy_map_comp _ hQ (by fun_prop)
  have hpair : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ (r.1, r.2.2.2.1))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.2.2.1)) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_injective_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.2.2.1)) (by fun_prop)
      (fun p ↦ (f₁ p.1, p.2)) (fun a b h ↦ by
        simpa [Prod.ext_iff, hinj₁.eq_iff] using h) (by fun_prop)
  unfold martonInfo₁
  rw [martonJointDistribution_map_injective pV K' W f₁ hf₁ f₂ hf₂, haux, hout, hpair]

end FirstReceiver

section SecondReceiver

variable [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Fintype V₂'] [Nonempty V₂'] [MeasurableSingletonClass V₂']
  [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂]

lemma martonInfo₂_map_injective
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K' : Kernel (V₁' × V₂') α) [IsMarkovKernel K']
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (f₁ : V₁ → V₁') (hf₁ : Measurable f₁)
    (f₂ : V₂ → V₂') (hf₂ : Measurable f₂) (hinj₂ : Function.Injective f₂) :
    martonInfo₂ (pV.map (fun v ↦ (f₁ v.1, f₂ v.2))) K' W
      = martonInfo₂ pV
          (K'.comap (fun v ↦ (f₁ v.1, f₂ v.2))
            ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))) W := by
  set K := K'.comap (fun v : V₁ × V₂ ↦ (f₁ v.1, f₂ v.2))
    ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2)) :=
    (hf₁.comp measurable_fst).prodMk
      ((hf₂.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have haux : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ r.2.1)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_injective_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) (by fun_prop) f₂ hinj₂ hf₂
  have hout : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ r.2.2.2.2)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.2) :=
    entropy_map_comp _ hQ (by fun_prop)
  have hpair : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ (r.2.1, r.2.2.2.2))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.2.1, q.2.2.2.2)) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_injective_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.2.1, q.2.2.2.2)) (by fun_prop)
      (fun p ↦ (f₂ p.1, p.2)) (fun a b h ↦ by
        simpa [Prod.ext_iff, hinj₂.eq_iff] using h) (by fun_prop)
  unfold martonInfo₂
  rw [martonJointDistribution_map_injective pV K' W f₁ hf₁ f₂ hf₂, haux, hout, hpair]

end SecondReceiver

section Auxiliaries

variable [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Fintype V₁'] [Nonempty V₁'] [MeasurableSingletonClass V₁']
  [Fintype V₂'] [Nonempty V₂'] [MeasurableSingletonClass V₂']

lemma martonInfoV₁V₂_map_injective
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K' : Kernel (V₁' × V₂') α) [IsMarkovKernel K']
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (f₁ : V₁ → V₁') (hf₁ : Measurable f₁) (hinj₁ : Function.Injective f₁)
    (f₂ : V₂ → V₂') (hf₂ : Measurable f₂) (hinj₂ : Function.Injective f₂) :
    martonInfoV₁V₂ (pV.map (fun v ↦ (f₁ v.1, f₂ v.2))) K' W
      = martonInfoV₁V₂ pV
          (K'.comap (fun v ↦ (f₁ v.1, f₂ v.2))
            ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))) W := by
  set K := K'.comap (fun v : V₁ × V₂ ↦ (f₁ v.1, f₂ v.2))
    ((hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd))
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2)) :=
    (hf₁.comp measurable_fst).prodMk
      ((hf₂.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have haux₁ : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) Prod.fst
      = entropy (martonJointDistribution pV K W) Prod.fst := by
    rw [entropy_map_comp _ hQ measurable_fst]
    exact entropy_injective_comp _ Prod.fst measurable_fst f₁ hinj₁ hf₁
  have haux₂ : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ r.2.1)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_injective_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) (by fun_prop) f₂ hinj₂ hf₂
  have hpair : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (f₁ q.1, f₂ q.2.1, q.2.2))) (fun r ↦ (r.1, r.2.1))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.1)) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_injective_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) (by fun_prop)
      (fun p ↦ (f₁ p.1, f₂ p.2)) (fun a b h ↦ by
        simpa [Prod.ext_iff, hinj₁.eq_iff, hinj₂.eq_iff] using h) (by fun_prop)
  unfold martonInfoV₁V₂
  rw [martonJointDistribution_map_injective pV K' W f₁ hf₁ f₂ hf₂, haux₁, haux₂, hpair]

end Auxiliaries

end Information

end Relabel

/-! ## The support of the outer auxiliary law as an alphabet -/

section Support

variable {V₁ : Type*} [Fintype V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]

open MeasureTheory.Measure in
lemma map_comap_support_coe (q : Measure V₁) [IsProbabilityMeasure q] :
    (Measure.comap (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) q).map Subtype.val = q := by
  classical
  have hmeas : MeasurableSet {u : V₁ | q.real {u} ≠ 0} := (Set.toFinite _).measurableSet
  rw [map_comap_subtype_coe hmeas]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have hsub : {u : V₁ | ¬ (u ∈ {u : V₁ | q.real {u} ≠ 0})} = {u : V₁ | q {u} = 0} := by
    ext u
    simp only [Set.mem_setOf_eq, not_not, Measure.real, ENNReal.toReal_eq_zero_iff,
      measure_ne_top q {u}, or_false]
  rw [hsub, show ({u : V₁ | q {u} = 0} : Set V₁) = ⋃ u ∈ {u : V₁ | q {u} = 0}, ({u} : Set V₁) from
    by ext u; simp]
  exact (measure_biUnion_null_iff (Set.toFinite _).countable).mpr fun u hu ↦ hu

omit [Fintype V₁] [MeasurableSingletonClass V₁] in
lemma card_support_subtype_le (q : Measure V₁) [IsProbabilityMeasure q]
    [Fintype ↥{u : V₁ | q.real {u} ≠ 0}] {n : ℕ}
    (h : {u : V₁ | q.real {u} ≠ 0}.ncard ≤ n) :
    Fintype.card ↥{u : V₁ | q.real {u} ≠ 0} ≤ n := by
  classical
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact h

omit [MeasurableSingletonClass V₁] in
lemma nonempty_support_subtype (q : Measure V₁) [IsProbabilityMeasure q] :
    Nonempty ↥{u : V₁ | q.real {u} ≠ 0} := by
  classical
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  have hempty : {u : V₁ | q.real {u} ≠ 0} = ∅ := Set.isEmpty_coe_sort.mp hcon
  have hall : ∀ u : V₁, q {u} = 0 := by
    intro u
    have hu : q.real {u} = 0 := by
      by_contra hu
      exact Set.eq_empty_iff_forall_notMem.mp hempty u hu
    simpa [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top q {u}] using hu
  have huniv : q (Set.univ : Set V₁) = 0 := by
    rw [show (Set.univ : Set V₁) = ⋃ u : V₁, ({u} : Set V₁) from by ext u; simp]
    exact (measure_iUnion_null_iff).mpr hall
  simp [measure_univ] at huniv

omit [Fintype V₁] [MeasurableSingletonClass V₁] in
lemma isProbabilityMeasure_of_map_subtype_val (q : Measure V₁) [IsProbabilityMeasure q]
    (q' : Measure ↥{u : V₁ | q.real {u} ≠ 0})
    (h : q'.map (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) = q) :
    IsProbabilityMeasure q' := by
  constructor
  have h1 : (q'.map (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁)) Set.univ = 1 := by
    rw [h]; exact measure_univ
  rwa [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ] at h1

end Support

/-! ## Restricting the outer auxiliary law to its support -/

section ComapSupport

variable {α : Type u} {β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
  {V₁ V₂ : Type*} [Fintype V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [MeasurableSpace V₂]

lemma martonInfo₁_comap_support [Nonempty V₁]
    [Fintype β₁] [Nonempty β₁] [MeasurableSingletonClass β₁]
    (q : Measure V₁) [IsProbabilityMeasure q]
    (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (q'' : Measure ↥{u : V₁ | q.real {u} ≠ 0}) [IsProbabilityMeasure q'']
    [Fintype ↥{u : V₁ | q.real {u} ≠ 0}] [Nonempty ↥{u : V₁ | q.real {u} ≠ 0}]
    (hq'' : q''.map (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) = q) :
    martonInfo₁ (q ⊗ₘ κ) K W
      = martonInfo₁ (q'' ⊗ₘ (κ.comap Subtype.val measurable_subtype_coe))
          (K.comap (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2))
            ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)) W := by
  have hι : Measurable (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) := measurable_subtype_coe
  have hpush : (q'' ⊗ₘ (κ.comap Subtype.val hι)).map
      (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2)) = q ⊗ₘ κ := by
    rw [compProd_comap_map_prodMap q'' κ hι, hq'']
  rw [← hpush]
  exact martonInfo₁_map_injective _ K W Subtype.val hι Subtype.val_injective id measurable_id

omit [MeasurableSingletonClass V₁] in
lemma martonInfo₂_comap_support
    [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
    [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂]
    (q : Measure V₁) [IsProbabilityMeasure q]
    (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (q'' : Measure ↥{u : V₁ | q.real {u} ≠ 0}) [IsProbabilityMeasure q'']
    (hq'' : q''.map (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) = q) :
    martonInfo₂ (q ⊗ₘ κ) K W
      = martonInfo₂ (q'' ⊗ₘ (κ.comap Subtype.val measurable_subtype_coe))
          (K.comap (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2))
            ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)) W := by
  have hι : Measurable (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) := measurable_subtype_coe
  have hpush : (q'' ⊗ₘ (κ.comap Subtype.val hι)).map
      (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2)) = q ⊗ₘ κ := by
    rw [compProd_comap_map_prodMap q'' κ hι, hq'']
  rw [← hpush]
  exact martonInfo₂_map_injective _ K W Subtype.val hι id measurable_id Function.injective_id

lemma martonInfoV₁V₂_comap_support [Nonempty V₁]
    [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
    (q : Measure V₁) [IsProbabilityMeasure q]
    (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (q'' : Measure ↥{u : V₁ | q.real {u} ≠ 0}) [IsProbabilityMeasure q'']
    [Fintype ↥{u : V₁ | q.real {u} ≠ 0}] [Nonempty ↥{u : V₁ | q.real {u} ≠ 0}]
    (hq'' : q''.map (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) = q) :
    martonInfoV₁V₂ (q ⊗ₘ κ) K W
      = martonInfoV₁V₂ (q'' ⊗ₘ (κ.comap Subtype.val measurable_subtype_coe))
          (K.comap (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2))
            ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)) W := by
  have hι : Measurable (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) := measurable_subtype_coe
  have hpush : (q'' ⊗ₘ (κ.comap Subtype.val hι)).map
      (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2)) = q ⊗ₘ κ := by
    rw [compProd_comap_map_prodMap q'' κ hι, hq'']
  rw [← hpush]
  exact martonInfoV₁V₂_map_injective _ K W Subtype.val hι Subtype.val_injective id measurable_id
    Function.injective_id

end ComapSupport

/-! ## The cardinality bound for either auxiliary alphabet -/

section Bound

variable {α : Type u} {V₁ V₂ β₁ β₂ : Type*}
  [Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The cardinality cap on a Marton auxiliary alphabet: the size of the channel input alphabet.
An auxiliary alphabet of the union carries `k + 1` letters, so on its index the cap reads
`k < martonAuxBound α`. -/
def martonAuxBound (α : Type*) [Fintype α] : ℕ := Fintype.card α

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
lemma exists_bcAuxAlphabet_martonInfo_eq_of_card {T : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace T] [MeasurableSingletonClass T] {n : ℕ} (hT : Fintype.card T ≤ n)
    (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T V₂) [IsMarkovKernel κ]
    (K : Kernel (T × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∃ (k : ℕ) (_ : k < n) (q' : Measure (bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure q')
      (κ' : Kernel (bcAuxAlphabet.{u} k) V₂) (_ : IsMarkovKernel κ')
      (K' : Kernel (bcAuxAlphabet.{u} k × V₂) α) (_ : IsMarkovKernel K'),
      martonInfo₁ (μ ⊗ₘ κ) K W = martonInfo₁ (q' ⊗ₘ κ') K' W ∧
      martonInfo₂ (μ ⊗ₘ κ) K W = martonInfo₂ (q' ⊗ₘ κ') K' W ∧
      martonInfoV₁V₂ (μ ⊗ₘ κ) K W = martonInfoV₁V₂ (q' ⊗ₘ κ') K' W := by
  classical
  set E : T ≃ᵐ bcAuxAlphabet.{u} (Fintype.card T - 1) := bcAuxMeasurableEquiv T
  have hE : Measurable (E : T → bcAuxAlphabet.{u} (Fintype.card T - 1)) := E.measurable
  have hEs : Measurable (E.symm : bcAuxAlphabet.{u} (Fintype.card T - 1) → T) := E.symm.measurable
  have hbwd : Measurable
      (fun v : bcAuxAlphabet.{u} (Fintype.card T - 1) × V₂ ↦ ((E.symm v.1 : T), v.2)) :=
    (hEs.comp measurable_fst).prodMk measurable_snd
  have hpush : (μ ⊗ₘ κ).map (fun v : T × V₂ ↦ ((E v.1 : bcAuxAlphabet.{u} _), v.2))
      = (μ.map E) ⊗ₘ (κ.comap E.symm hEs) := by
    have h := compProd_comap_map_prodMap μ (κ.comap E.symm hEs) hE
    rwa [show (κ.comap E.symm hEs).comap E hE = κ from Kernel.ext fun v ↦ by simp] at h
  have hKcomap : (K.comap (fun v ↦ ((E.symm v.1 : T), v.2)) hbwd).comap
      (fun v : T × V₂ ↦ ((E v.1 : bcAuxAlphabet.{u} _), v.2))
      ((hE.comp measurable_fst).prodMk measurable_snd) = K := Kernel.ext fun v ↦ by simp
  haveI : IsProbabilityMeasure (μ.map E) := Measure.isProbabilityMeasure_map hE.aemeasurable
  refine ⟨Fintype.card T - 1, by have := Fintype.card_pos (α := T); omega, μ.map E, inferInstance,
    κ.comap E.symm hEs, inferInstance, K.comap (fun v ↦ ((E.symm v.1 : T), v.2)) hbwd,
    inferInstance, ?_, ?_, ?_⟩
  · have h := martonInfo₁_map_injective (μ ⊗ₘ κ)
      (K.comap (fun v ↦ ((E.symm v.1 : T), v.2)) hbwd) W E hE E.injective (fun x ↦ x) measurable_id
    rw [hpush, hKcomap] at h
    exact h.symm
  · have h := martonInfo₂_map_injective (μ ⊗ₘ κ)
      (K.comap (fun v ↦ ((E.symm v.1 : T), v.2)) hbwd) W E hE (fun x ↦ x) measurable_id
      Function.injective_id
    rw [hpush, hKcomap] at h
    exact h.symm
  · have h := martonInfoV₁V₂_map_injective (μ ⊗ₘ κ)
      (K.comap (fun v ↦ ((E.symm v.1 : T), v.2)) hbwd) W E hE E.injective (fun x ↦ x)
      measurable_id Function.injective_id
    rw [hpush, hKcomap] at h
    exact h.symm

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
lemma exists_bcAuxAlphabet_martonInfo_eq {n : ℕ}
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard : {u : V₁ | q.real {u} ≠ 0}.ncard ≤ n) :
    ∃ (k : ℕ) (_ : k < n) (q' : Measure (bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure q')
      (κ' : Kernel (bcAuxAlphabet.{u} k) V₂) (_ : IsMarkovKernel κ')
      (K' : Kernel (bcAuxAlphabet.{u} k × V₂) α) (_ : IsMarkovKernel K'),
      martonInfo₁ (q ⊗ₘ κ) K W = martonInfo₁ (q' ⊗ₘ κ') K' W ∧
      martonInfo₂ (q ⊗ₘ κ) K W = martonInfo₂ (q' ⊗ₘ κ') K' W ∧
      martonInfoV₁V₂ (q ⊗ₘ κ) K W = martonInfoV₁V₂ (q' ⊗ₘ κ') K' W := by
  classical
  haveI : Nonempty ↥{u : V₁ | q.real {u} ≠ 0} := nonempty_support_subtype q
  have hq₀ :
      (Measure.comap (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) q).map Subtype.val = q :=
    map_comap_support_coe q
  haveI : IsProbabilityMeasure
      (Measure.comap (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) q) :=
    isProbabilityMeasure_of_map_subtype_val q _ hq₀
  obtain ⟨k, hk, q', hq', κ', hκ', K', hK', h₁, h₂, h₃⟩ :=
    exists_bcAuxAlphabet_martonInfo_eq_of_card (V₂ := V₂) (β₁ := β₁) (β₂ := β₂)
      (card_support_subtype_le q hcard)
      (Measure.comap (Subtype.val : ↥{u : V₁ | q.real {u} ≠ 0} → V₁) q)
      (κ.comap Subtype.val measurable_subtype_coe)
      (K.comap (fun v : ↥{u : V₁ | q.real {u} ≠ 0} × V₂ ↦ ((v.1 : V₁), v.2))
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)) W
  exact ⟨k, hk, q', hq', κ', hκ', K', hK',
    (martonInfo₁_comap_support q κ K W _ hq₀).trans h₁,
    (martonInfo₂_comap_support q κ K W _ hq₀).trans h₂,
    (martonInfoV₁V₂_comap_support q κ K W _ hq₀).trans h₃⟩

/-- The outer auxiliary law can be replaced by a law on an auxiliary alphabet of the union with at
most `martonAuxBound α` letters, without decreasing the weighted sum of the three informations of
the region inequalities.  The second-receiver weight `μ₂` and the sum-rate weight `μ₃` scale the
two convex entropy slots and are assumed nonnegative; the first-receiver weight `μ₁` is
unrestricted.  The inner auxiliary alphabet is carried along unchanged, and no bound on its
cardinality is claimed.  The replacing law and kernels depend on the weights.

@audit:ok -/
@[entry_point]
theorem exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights
    (q : Measure V₁) [IsProbabilityMeasure q] (κ : Kernel V₁ V₂) [IsMarkovKernel κ]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (μ₁ μ₂ μ₃ : ℝ) (hμ₂ : 0 ≤ μ₂) (hμ₃ : 0 ≤ μ₃) :
    ∃ (k : ℕ) (_ : k < martonAuxBound α) (q' : Measure (bcAuxAlphabet.{u} k))
      (_ : IsProbabilityMeasure q') (κ' : Kernel (bcAuxAlphabet.{u} k) V₂) (_ : IsMarkovKernel κ')
      (K' : Kernel (bcAuxAlphabet.{u} k × V₂) α) (_ : IsMarkovKernel K'),
      μ₁ * martonInfo₁ (q ⊗ₘ κ) K W + μ₂ * martonInfo₂ (q ⊗ₘ κ) K W
        + μ₃ * (martonInfo₁ (q ⊗ₘ κ) K W + martonInfo₂ (q ⊗ₘ κ) K W
                - martonInfoV₁V₂ (q ⊗ₘ κ) K W)
        ≤ μ₁ * martonInfo₁ (q' ⊗ₘ κ') K' W + μ₂ * martonInfo₂ (q' ⊗ₘ κ') K' W
          + μ₃ * (martonInfo₁ (q' ⊗ₘ κ') K' W + martonInfo₂ (q' ⊗ₘ κ') K' W
                  - martonInfoV₁V₂ (q' ⊗ₘ κ') K' W) := by
  obtain ⟨q₁, hq₁, hcard, hle⟩ :=
    exists_support_card_le_martonWeightedSumAllWeights_measure q κ K W μ₁ μ₂ μ₃ hμ₂ hμ₃
  haveI : IsProbabilityMeasure q₁ := hq₁
  obtain ⟨k, hk, q', hq', κ', hκ', K', hK', h₁, h₂, h₃⟩ :=
    exists_bcAuxAlphabet_martonInfo_eq (n := martonAuxBound α) q₁ κ K W hcard
  refine ⟨k, hk, q', hq', κ', hκ', K', hK', ?_⟩
  rw [← h₁, ← h₂, ← h₃]
  exact hle

/-- The inner auxiliary law can be replaced by a law on an auxiliary alphabet of the union with at
most `martonAuxBound α` letters, without decreasing the weighted sum of the three informations of
the region inequalities.  The first-receiver weight `μ₁` and the sum-rate weight `μ₃` are assumed
nonnegative; the second-receiver weight `μ₂` is unrestricted.  The outer auxiliary alphabet is
carried along unchanged, and no bound on its cardinality is claimed.  The replacing law and kernel
depend on the weights.

@audit:ok -/
@[entry_point]
theorem exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights_inner
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (μ₁ μ₂ μ₃ : ℝ) (hμ₁ : 0 ≤ μ₁) (hμ₃ : 0 ≤ μ₃) :
    ∃ (k : ℕ) (_ : k < martonAuxBound α) (pV' : Measure (V₁ × bcAuxAlphabet.{u} k))
      (_ : IsProbabilityMeasure pV') (K' : Kernel (V₁ × bcAuxAlphabet.{u} k) α)
      (_ : IsMarkovKernel K'),
      μ₁ * martonInfo₁ pV K W + μ₂ * martonInfo₂ pV K W
        + μ₃ * (martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W)
        ≤ μ₁ * martonInfo₁ pV' K' W + μ₂ * martonInfo₂ pV' K' W
          + μ₃ * (martonInfo₁ pV' K' W + martonInfo₂ pV' K' W - martonInfoV₁V₂ pV' K' W) := by
  haveI : IsMarkovKernel (W.map (Prod.swap : β₁ × β₂ → β₂ × β₁)) :=
    Kernel.IsMarkovKernel.map W measurable_swap
  haveI : IsProbabilityMeasure (pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have hdis : (pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)).fst ⊗ₘ
      (pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)).condKernel
        = pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁) :=
    Measure.disintegrate _ _
  obtain ⟨k, hk, q', hq', κ', hκ', K', hK', hle⟩ :=
    exists_bcAuxAlphabet_card_le_martonWeightedSumAllWeights
      (pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)).fst
      (pV.map (Prod.swap : V₁ × V₂ → V₂ × V₁)).condKernel
      (K.comap (Prod.swap : V₂ × V₁ → V₁ × V₂) measurable_swap)
      (W.map (Prod.swap : β₁ × β₂ → β₂ × β₁)) μ₂ μ₁ μ₃ hμ₁ hμ₃
  rw [hdis] at hle
  haveI := hq'
  haveI := hκ'
  haveI := hK'
  haveI : IsProbabilityMeasure ((q' ⊗ₘ κ').map (Prod.swap : bcAuxAlphabet.{u} k × V₁ → _)) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  refine ⟨k, hk, (q' ⊗ₘ κ').map Prod.swap, inferInstance,
    K'.comap (Prod.swap : V₁ × bcAuxAlphabet.{u} k → _) measurable_swap, inferInstance, ?_⟩
  have hswap :
      ((q' ⊗ₘ κ').map (Prod.swap : bcAuxAlphabet.{u} k × V₁ → V₁ × bcAuxAlphabet.{u} k)).map
        (Prod.swap : V₁ × bcAuxAlphabet.{u} k → bcAuxAlphabet.{u} k × V₁) = q' ⊗ₘ κ' := by
    rw [Measure.map_map measurable_swap measurable_swap,
      show (Prod.swap : V₁ × bcAuxAlphabet.{u} k → bcAuxAlphabet.{u} k × V₁) ∘
        (Prod.swap : bcAuxAlphabet.{u} k × V₁ → V₁ × bcAuxAlphabet.{u} k) = id from
        funext fun _ ↦ rfl, Measure.map_id]
  have hcomap : (K'.comap (Prod.swap : V₁ × bcAuxAlphabet.{u} k → bcAuxAlphabet.{u} k × V₁)
      measurable_swap).comap
      (Prod.swap : bcAuxAlphabet.{u} k × V₁ → V₁ × bcAuxAlphabet.{u} k) measurable_swap = K' :=
    Kernel.ext fun _ ↦ rfl
  have e₁ : martonInfo₁ (q' ⊗ₘ κ') K' (W.map (Prod.swap : β₁ × β₂ → β₂ × β₁))
      = martonInfo₂ ((q' ⊗ₘ κ').map Prod.swap) (K'.comap Prod.swap measurable_swap) W := by
    have h := martonInfo₁_swap ((q' ⊗ₘ κ').map Prod.swap)
      (K'.comap (Prod.swap : V₁ × bcAuxAlphabet.{u} k → _) measurable_swap) W
    rwa [hswap, hcomap] at h
  have e₂ : martonInfo₂ (q' ⊗ₘ κ') K' (W.map (Prod.swap : β₁ × β₂ → β₂ × β₁))
      = martonInfo₁ ((q' ⊗ₘ κ').map Prod.swap) (K'.comap Prod.swap measurable_swap) W := by
    have h := martonInfo₂_swap ((q' ⊗ₘ κ').map Prod.swap)
      (K'.comap (Prod.swap : V₁ × bcAuxAlphabet.{u} k → _) measurable_swap) W
    rwa [hswap, hcomap] at h
  have e₃ : martonInfoV₁V₂ (q' ⊗ₘ κ') K' (W.map (Prod.swap : β₁ × β₂ → β₂ × β₁))
      = martonInfoV₁V₂ ((q' ⊗ₘ κ').map Prod.swap) (K'.comap Prod.swap measurable_swap) W := by
    have h := martonInfoV₁V₂_swap ((q' ⊗ₘ κ').map Prod.swap)
      (K'.comap (Prod.swap : V₁ × bcAuxAlphabet.{u} k → _) measurable_swap) W
    rwa [hswap, hcomap] at h
  rw [martonInfo₁_swap pV K W, martonInfo₂_swap pV K W, martonInfoV₁V₂_swap pV K W,
    e₁, e₂, e₃] at hle
  linarith

end Bound

end InformationTheory.Shannon.BroadcastChannel.Marton
