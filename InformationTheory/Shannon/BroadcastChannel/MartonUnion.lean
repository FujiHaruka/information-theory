import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.MartonBridge

/-!
# Broadcast channel — Marton's inner bound as a union over auxiliary alphabets

`martonRegion` is the quadrilateral of one fixed pair of auxiliary alphabets, whereas the UV
outer region is a union over five-tuple laws.  This file takes the union on the inner side, so
that the two regions can be compared as sets.

## Main definitions

* `bcAuxAlphabet k` — the auxiliary alphabet of cardinality `k + 1`.
* `martonRegionUnion W` — Marton's inner bound, as the closure of the union of `martonRegion`
  over the auxiliary laws on those alphabets.
* `martonRegionUnionFS W` — the same union restricted to the full-support indices, which is the
  form the achievability theorem applies to.

## Main statements

* `martonRegionUnion_subset_uv` — the union sits inside the UV outer region.
* `martonRegionUnionFS_subset_capacity` — the full-support union sits inside the operational
  capacity region.
* `martonRegion_subset_union` — the union absorbs the quadrilateral of every pair of finite
  auxiliary alphabets, in every universe.
* `martonRegionUnion_isLowerSet` / `martonRegionUnion_nonempty` — the union is a nonempty lower
  set, as the UV outer region is.

## Implementation notes

The auxiliaries range over `ULift (Fin (k + 1))`, one cardinality at a time, in the universe of
the input alphabet: fixing the cardinality avoids quantifying over types, and the universe lift
is what lets the comparison classes be applied at a member of the union.  A countable auxiliary
alphabet is not available here, unlike on the outer side: the dependence between the two
auxiliaries is the one information slot reading no output letter, so it is the one that can be
infinite, and the `toReal` convention would then drop the sum-rate penalty.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel

set_option linter.unusedSectionVars false

universe u

section Union

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The auxiliary alphabet of cardinality `k + 1`, in the universe of the input alphabet.
The successor form keeps every index of the union nonempty, which `martonRegion` requires of its
auxiliary alphabets. -/
abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))

/-- Marton's inner bound as a subset of the plane: the closure of the union of the
quadrilaterals `martonRegion pV K W` over the auxiliary laws on `bcAuxAlphabet`.
The closure makes the union a closed set, as `bcCapacityRegion` and `bcOuterRegionUV` both are,
and costs nothing in either inclusion because a closed superset absorbs it. -/
noncomputable def martonRegionUnion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)

/-- The same union over the full-support indices only: the auxiliary law and the auxiliary
kernel charge every point.  Those are the regularity preconditions of
`marton_region_subset_capacity`, so this is the form of the union that is achievable. -/
noncomputable def martonRegionUnionFS (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (_ : ∀ v : bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂, 0 < pV.real {v})
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K)
    (_ : ∀ (v : bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) (a : α), 0 < (K v).real {a}),
    martonRegion pV K W)

/-- Marton's inner bound is contained in the UV outer region, with no support hypothesis on the
auxiliary law, the auxiliary kernel or the channel. -/
@[entry_point]
theorem martonRegionUnion_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegionUnion W ⊆ bcOuterRegionUV W := by
  refine closure_minimal ?_ (bcOuterRegionUV_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦ ?_
  exact marton_region_subset_uv pV K W

theorem martonRegionUnionFS_subset_union (W : BCChannel α β₁ β₂) :
    martonRegionUnionFS W ⊆ martonRegionUnion W := by
  refine closure_mono ?_
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun _ ↦ Set.iUnion_subset fun K ↦
      Set.iUnion_subset fun hK ↦ Set.iUnion_subset fun _ ↦ ?_
  exact Set.subset_iUnion_of_subset k₁ (Set.subset_iUnion_of_subset k₂
    (Set.subset_iUnion_of_subset pV (Set.subset_iUnion_of_subset hpV
      (Set.subset_iUnion_of_subset K (Set.subset_iUnion_of_subset hK subset_rfl)))))

/-- The full-support form of Marton's inner bound is achievable: it is contained in the
operational capacity region. -/
@[entry_point]
theorem martonRegionUnionFS_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegionUnionFS W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ (bc_capacityRegion_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun hpVpos ↦ Set.iUnion_subset fun K ↦
      Set.iUnion_subset fun hK ↦ Set.iUnion_subset fun hKpos ↦ ?_
  exact marton_region_subset_capacity pV K W hpVpos hKpos hW

end Union

/-! ## Order, convexity and nondegeneracy -/

section Shape

variable {α : Type u} {β₁ β₂ : Type*}
  [MeasurableSpace α] [Fintype β₁] [MeasurableSpace β₁] [Fintype β₂] [MeasurableSpace β₂]

section Quadrilateral

variable {V₁ V₂ : Type*} [Fintype V₁] [MeasurableSpace V₁] [Fintype V₂] [MeasurableSpace V₂]

lemma martonRegion_isLowerSet (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) : IsLowerSet (martonRegion pV K W) := by
  rintro p q hqp ⟨h₁, h₂, hsum⟩
  exact ⟨hqp.1.trans h₁, hqp.2.trans h₂, (add_le_add hqp.1 hqp.2).trans hsum⟩

lemma martonRegion_convex (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) : Convex ℝ (martonRegion pV K W) := by
  rintro p ⟨hp₁, hp₂, hps⟩ q ⟨hq₁, hq₂, hqs⟩ a b ha hb hab
  have key : ∀ x y c : ℝ, x ≤ c → y ≤ c → a * x + b * y ≤ c := fun x y c hx hy ↦ by
    have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    linarith
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · exact key _ _ _ hp₁ hq₁
  · exact key _ _ _ hp₂ hq₂
  · have h := key _ _ _ hps hqs
    linarith

lemma martonRegion_nonempty (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α)
    (W : BCChannel α β₁ β₂) : (martonRegion pV K W).Nonempty := by
  set I₁ := martonInfo₁ pV K W
  set I₂ := martonInfo₂ pV K W
  set I₁₂ := martonInfoV₁V₂ pV K W
  set t := min (min I₁ I₂) ((I₁ + I₂ - I₁₂) / 2)
  have h₁ : t ≤ I₁ := (min_le_left _ _).trans (min_le_left _ _)
  have h₂ : t ≤ I₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hs : t ≤ (I₁ + I₂ - I₁₂) / 2 := min_le_right _ _
  exact ⟨(t, t), h₁, h₂, by linarith⟩

end Quadrilateral

private lemma martonRegion_subset_union_of_bcAux (k₁ k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂)) [IsProbabilityMeasure pV]
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) : martonRegion pV K W ⊆ martonRegionUnion W := by
  refine subset_trans ?_ subset_closure
  exact Set.subset_iUnion_of_subset k₁ (Set.subset_iUnion_of_subset k₂
    (Set.subset_iUnion_of_subset pV (Set.subset_iUnion_of_subset inferInstance
      (Set.subset_iUnion_of_subset K (Set.subset_iUnion_of_subset inferInstance subset_rfl)))))

theorem martonRegionUnion_isLowerSet (W : BCChannel α β₁ β₂) :
    IsLowerSet (martonRegionUnion W) :=
  IsLowerSet.closure (isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦
    isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦
      isLowerSet_iUnion fun _ ↦ martonRegion_isLowerSet _ _ _)

section Witness

variable [Nonempty α]

theorem martonRegionUnion_nonempty (W : BCChannel α β₁ β₂) :
    (martonRegionUnion W).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (bcAuxAlphabet.{u} 0 × bcAuxAlphabet.{u} 0))
  exact (martonRegion_nonempty (Measure.dirac v₀) (Kernel.const _ (Measure.dirac x₀)) W).mono
    (martonRegion_subset_union_of_bcAux 0 0 _ _ W)

end Witness

end Shape

/-! ## Relabeling the auxiliary alphabets -/

private lemma entropy_map_comp {Ω Ω' A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Fintype A] [MeasurableSpace A]
    (μ : Measure Ω) {f : Ω → Ω'} (hf : Measurable f) {X : Ω' → A} (hX : Measurable X) :
    entropy (μ.map f) X = entropy μ (fun ω ↦ X (f ω)) := by
  unfold entropy
  rw [Measure.map_map hX hf]
  rfl

section Relabel

variable {α : Type u} {β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
  {V₁ V₂ V₁' V₂' : Type*} [MeasurableSpace V₁] [MeasurableSpace V₂] [MeasurableSpace V₁']
  [MeasurableSpace V₂']

lemma martonJointDistribution_map_relabel
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂') :
    martonJointDistribution (pV.map (e₁.prodCongr e₂))
        (K.comap (e₁.prodCongr e₂).symm (e₁.prodCongr e₂).symm.measurable) W
      = (martonJointDistribution pV K W).map (fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2)) := by
  set E : (V₁ × V₂) ≃ᵐ (V₁' × V₂') := e₁.prodCongr e₂
  set g : (V₁ × V₂) × α → (V₁' × V₂') × α := fun z ↦ (E z.1, z.2)
  have hg : Measurable g := (E.measurable.comp measurable_fst).prodMk measurable_snd
  have hKcomap : (K.comap E.symm E.symm.measurable).comap E E.measurable = K :=
    Kernel.ext fun v ↦ by simp
  have hWcomap :
      (W.comap (Prod.snd : (V₁' × V₂') × α → α) measurable_snd).comap g hg
        = W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd :=
    Kernel.ext fun _ ↦ rfl
  have hstep₁ : (pV ⊗ₘ K).map g = (pV.map E) ⊗ₘ (K.comap E.symm E.symm.measurable) := by
    have h := compProd_comap_map_prodMap pV (K.comap E.symm E.symm.measurable) E.measurable
    rwa [hKcomap] at h
  have hstep₂ :
      ((pV ⊗ₘ K) ⊗ₘ (W.comap (Prod.snd : (V₁ × V₂) × α → α) measurable_snd)).map
          (fun z ↦ (g z.1, z.2))
        = ((pV.map E) ⊗ₘ (K.comap E.symm E.symm.measurable)) ⊗ₘ
            (W.comap (Prod.snd : (V₁' × V₂') × α → α) measurable_snd) := by
    have h := compProd_comap_map_prodMap (pV ⊗ₘ K)
      (W.comap (Prod.snd : (V₁' × V₂') × α → α) measurable_snd) hg
    rwa [hWcomap, hstep₁] at h
  have hG : Measurable (fun z : ((V₁ × V₂) × α) × β₁ × β₂ ↦ (g z.1, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2)) :=
    (e₁.measurable.comp measurable_fst).prodMk
      ((e₂.measurable.comp (measurable_fst.comp measurable_snd)).prodMk
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

lemma martonInfo₁_map_relabel
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂') :
    martonInfo₁ (pV.map (e₁.prodCongr e₂))
        (K.comap (e₁.prodCongr e₂).symm (e₁.prodCongr e₂).symm.measurable) W
      = martonInfo₁ pV K W := by
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2)) :=
    (e₁.measurable.comp measurable_fst).prodMk
      ((e₂.measurable.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have haux : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) Prod.fst
      = entropy (martonJointDistribution pV K W) Prod.fst := by
    rw [entropy_map_comp _ hQ measurable_fst]
    exact entropy_measurableEquiv_comp _ Prod.fst measurable_fst e₁
  have hout : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ r.2.2.2.1)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.1) :=
    entropy_map_comp _ hQ (by fun_prop)
  have hpair : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ (r.1, r.2.2.2.1))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.2.2.1)) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_measurableEquiv_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.2.2.1)) (by fun_prop)
      (e₁.prodCongr (MeasurableEquiv.refl β₁))
  unfold martonInfo₁
  rw [martonJointDistribution_map_relabel pV K W e₁ e₂, haux, hout, hpair]

end FirstReceiver

section SecondReceiver

variable [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Fintype V₂'] [Nonempty V₂'] [MeasurableSingletonClass V₂']
  [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂]

lemma martonInfo₂_map_relabel
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂') :
    martonInfo₂ (pV.map (e₁.prodCongr e₂))
        (K.comap (e₁.prodCongr e₂).symm (e₁.prodCongr e₂).symm.measurable) W
      = martonInfo₂ pV K W := by
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2)) :=
    (e₁.measurable.comp measurable_fst).prodMk
      ((e₂.measurable.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have haux : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ r.2.1)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_measurableEquiv_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) (by fun_prop) e₂
  have hout : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ r.2.2.2.2)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.2) :=
    entropy_map_comp _ hQ (by fun_prop)
  have hpair : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ (r.2.1, r.2.2.2.2))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.2.1, q.2.2.2.2)) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_measurableEquiv_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.2.1, q.2.2.2.2)) (by fun_prop)
      (e₂.prodCongr (MeasurableEquiv.refl β₂))
  unfold martonInfo₂
  rw [martonJointDistribution_map_relabel pV K W e₁ e₂, haux, hout, hpair]

end SecondReceiver

section Auxiliaries

variable [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Fintype V₁'] [Nonempty V₁'] [MeasurableSingletonClass V₁']
  [Fintype V₂'] [Nonempty V₂'] [MeasurableSingletonClass V₂']

lemma martonInfoV₁V₂_map_relabel
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂') :
    martonInfoV₁V₂ (pV.map (e₁.prodCongr e₂))
        (K.comap (e₁.prodCongr e₂).symm (e₁.prodCongr e₂).symm.measurable) W
      = martonInfoV₁V₂ pV K W := by
  have hQ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2)) :=
    (e₁.measurable.comp measurable_fst).prodMk
      ((e₂.measurable.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have haux₁ : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) Prod.fst
      = entropy (martonJointDistribution pV K W) Prod.fst := by
    rw [entropy_map_comp _ hQ measurable_fst]
    exact entropy_measurableEquiv_comp _ Prod.fst measurable_fst e₁
  have haux₂ : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ r.2.1)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_measurableEquiv_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) (by fun_prop) e₂
  have hpair : entropy ((martonJointDistribution pV K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (e₁ q.1, e₂ q.2.1, q.2.2))) (fun r ↦ (r.1, r.2.1))
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.1)) := by
    rw [entropy_map_comp _ hQ (by fun_prop)]
    exact entropy_measurableEquiv_comp _
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) (by fun_prop) (e₁.prodCongr e₂)
  unfold martonInfoV₁V₂
  rw [martonJointDistribution_map_relabel pV K W e₁ e₂, haux₁, haux₂, hpair]

end Auxiliaries

section Quadrilateral

variable [Fintype V₁] [Nonempty V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSingletonClass V₂]
  [Fintype V₁'] [Nonempty V₁'] [MeasurableSingletonClass V₁']
  [Fintype V₂'] [Nonempty V₂'] [MeasurableSingletonClass V₂']
  [Fintype β₁] [Nonempty β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂]

lemma martonRegion_map_relabel
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (e₁ : V₁ ≃ᵐ V₁') (e₂ : V₂ ≃ᵐ V₂') :
    martonRegion (pV.map (e₁.prodCongr e₂))
        (K.comap (e₁.prodCongr e₂).symm (e₁.prodCongr e₂).symm.measurable) W
      = martonRegion pV K W := by
  unfold martonRegion
  rw [martonInfo₁_map_relabel pV K W e₁ e₂, martonInfo₂_map_relabel pV K W e₁ e₂,
    martonInfoV₁V₂_map_relabel pV K W e₁ e₂]

end Quadrilateral

end Information

end Relabel

section Absorb

variable {α : Type u} {β₁ β₂ : Type*} [MeasurableSpace α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  {V₁ V₂ : Type*}
  [Fintype V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]

/-- A finite nonempty alphabet, as the auxiliary alphabet of the union of its own cardinality:
the discrete measurable structure makes the indexing bijection of `Fintype.equivFin` measurable
both ways, and the universe lift carries it into the universe of the input alphabet. -/
private noncomputable def bcAuxMeasurableEquiv (V : Type*) [Fintype V] [Nonempty V]
    [MeasurableSpace V] [MeasurableSingletonClass V] :
    V ≃ᵐ bcAuxAlphabet.{u} (Fintype.card V - 1) where
  toEquiv := (Fintype.equivFin V).trans
    ((finCongr (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm).trans Equiv.ulift.symm)
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- Every Marton quadrilateral lies in the union, whatever the auxiliary alphabets: the union is
indexed by one alphabet of each finite cardinality, in the universe of the input alphabet, and a
pair of auxiliary alphabets of the same cardinalities is carried onto those by a relabeling that
leaves the three informations of the quadrilateral unchanged. -/
@[entry_point]
theorem martonRegion_subset_union (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegion pV K W ⊆ martonRegionUnion W := by
  have h := martonRegion_map_relabel pV K W
    (bcAuxMeasurableEquiv V₁ : V₁ ≃ᵐ bcAuxAlphabet.{u} (Fintype.card V₁ - 1))
    (bcAuxMeasurableEquiv V₂ : V₂ ≃ᵐ bcAuxAlphabet.{u} (Fintype.card V₂ - 1))
  haveI : IsProbabilityMeasure (pV.map
      ((bcAuxMeasurableEquiv V₁ : V₁ ≃ᵐ bcAuxAlphabet.{u} (Fintype.card V₁ - 1)).prodCongr
        (bcAuxMeasurableEquiv V₂ : V₂ ≃ᵐ bcAuxAlphabet.{u} (Fintype.card V₂ - 1)))) :=
    Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable
  rw [← h]
  exact martonRegion_subset_union_of_bcAux _ _ _ _ W

end Absorb

end InformationTheory.Shannon.BroadcastChannel.Marton
