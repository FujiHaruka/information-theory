import InformationTheory.Shannon.BroadcastChannel.Superposition.TimeShare
import Mathlib.Probability.Distributions.Uniform

/-!
# Broadcast channel — perturbing an achievability pair to full support

The superposition inner bound is a union over the pairs whose cloud law and satellite kernel give
every letter positive mass, whereas the pair read off a channel law need not: the law is free to
ignore part of the auxiliary alphabet or part of the input alphabet.  Mixing the law with the one
whose auxiliary and input letter are uniform and independent repairs both defects at once, because
the mixture dominates a positive multiple of the uniform law on every singleton of the `(U, X)`
marginal, and both the cloud law and the satellite kernel are read off exactly that marginal.

The mixture is carried by the auxiliary `Bool × U`, whose first component records which branch was
taken, so the two information slots of the mixed law are controlled by the slots of the original
one.  Forgetting the tag coarsens the conditioner of the satellite slot, which can only increase
it, while the receiver-2 corner pays the entropy of the tag.  That penalty is additive rather than
multiplicative, and it has to be: the corner of a mixture is not bounded below by any multiple of
the corner of the branch it keeps.  Both losses vanish with the mixing weight, so a rate pair
dominated by the informations of an arbitrary pair is dominated, up to any positive slack, by the
informations of a full-support pair.

## Main definitions

* `uvUniformLaw W v₀` — the channel law whose auxiliary and input letter are uniform and
  independent, the second auxiliary being frozen at `v₀`.
* `uvPerturbLaw W ν v₀ lam` — the channel law mixed with the uniform one with weight `lam`.
* `uvLawOfPair W pU K` — the five-tuple law of an achievability pair.

## Main statements

* `exists_fullSupport_bcInfo_ge` — a rate pair dominated by the two informations of an
  achievability pair is dominated, up to any positive slack, by those of a full-support pair.
* `exists_fullSupport_bcInfo_ge_of_isUVChannelLaw` — the same statement, with the rate pair
  dominated by the two slots of a channel law.
* `exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` — over a less noisy channel, a
  rate pair satisfying the three UV outer inequalities of a channel law is dominated, up to any
  positive slack, by the two informations of a full-support pair.
* `sub_mem_bcSuperpositionRegionNoSumRate_of_lessNoisy_of_isUVChannelLaw` — that shifted rate
  pair lies in the superposition inner bound.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal Topology

universe u

/-! ## Full support of the achievability pair read off a law -/

section Support

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
variable {β₁ : Type*} [MeasurableSpace β₁] {β₂ : Type*} [MeasurableSpace β₂]
variable {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
variable {V : Type*} [MeasurableSpace V]

lemma uvSatelliteKernel_real_singleton_pos (μ : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure μ]
    (hpos : ∀ (u : U) (a : α), 0 < μ.map (fun q ↦ (q.1, q.2.2.1)) {(u, a)})
    (u : U) (a : α) : 0 < (uvSatelliteKernel μ u).real {a} := by
  have hU : Measurable (fun q : U × V × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hX : Measurable (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1) := by fun_prop
  have hpair : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) := hU.prodMk hX
  -- the `U` marginal of `u` dominates the `(U, X)` marginal of `(u, a)`
  have hmono : μ.map (fun q ↦ (q.1, q.2.2.1)) {(u, a)} ≤ μ.map (fun q ↦ q.1) {u} := by
    rw [Measure.map_apply hpair (by simp), Measure.map_apply hU (by simp)]
    refine measure_mono fun q hq ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hq ⊢
    exact hq.1
  have hne : μ.map (fun q ↦ q.1) {u} ≠ 0 := ne_of_gt (lt_of_lt_of_le (hpos u a) hmono)
  have hkey := condDistrib_apply_of_ne_zero (μ := μ)
    (X := fun q : U × V × α × β₁ × β₂ ↦ q.1) (Y := fun q ↦ q.2.2.1) hX u hne {a}
  rw [Set.singleton_prod_singleton] at hkey
  have hval : uvSatelliteKernel μ u {a} = (μ.map (fun q ↦ q.1) {u})⁻¹
      * μ.map (fun q ↦ (q.1, q.2.2.1)) {(u, a)} := hkey
  rw [Measure.real, hval]
  refine ENNReal.toReal_pos (mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (hpos u a).ne') (ENNReal.mul_ne_top ?_ (measure_ne_top _ _))
  simp only [ne_eq, ENNReal.inv_eq_top]
  exact hne

lemma uvCloudLaw_real_singleton_pos (μ : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure μ]
    (hpos : ∀ (u : U) (a : α), 0 < μ.map (fun q ↦ (q.1, q.2.2.1)) {(u, a)}) (u : U) :
    0 < (uvCloudLaw μ).real {u} := by
  have hU : Measurable (fun q : U × V × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hpair : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) := by fun_prop
  obtain ⟨a⟩ : Nonempty α := inferInstance
  have hmono : μ.map (fun q ↦ (q.1, q.2.2.1)) {(u, a)} ≤ μ.map (fun q ↦ q.1) {u} := by
    rw [Measure.map_apply hpair (by simp), Measure.map_apply hU (by simp)]
    refine measure_mono fun q hq ↦ ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hq ⊢
    exact hq.1
  have hne : uvCloudLaw μ {u} ≠ 0 := ne_of_gt (lt_of_lt_of_le (hpos u a) hmono)
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

end Support

/-! ## The perturbed law -/

section Perturb

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁] {β₂ : Type*} [MeasurableSpace β₂]
variable {U : Type*} [Fintype U] [Nonempty U] [MeasurableSpace U]
variable {V : Type*} [MeasurableSpace V]

/-- The channel law whose auxiliary and input letter are uniform and independent of each other,
the second auxiliary being frozen at `v₀`. -/
noncomputable def uvUniformLaw (W : BCChannel α β₁ β₂) (v₀ : V) :
    Measure (U × V × α × β₁ × β₂) :=
  uvLawOfInput W (((PMF.uniformOfFintype U).toMeasure).prod
    ((Measure.dirac v₀).prod ((PMF.uniformOfFintype α).toMeasure)))

instance uvUniformLaw_isProbabilityMeasure (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (v₀ : V) :
    IsProbabilityMeasure (uvUniformLaw (U := U) W v₀) := by
  unfold uvUniformLaw
  infer_instance

lemma uvUniformLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (v₀ : V) :
    IsUVChannelLaw W (uvUniformLaw (U := U) W v₀) :=
  uvLawOfInput_isUVChannelLaw W _

/-- The channel law perturbed toward the uniform one, clamped so that it is a probability measure
for every weight. -/
noncomputable def uvPerturbLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂))
    (v₀ : V) (lam : ℝ≥0∞) : Measure (U × V × α × β₁ × β₂) :=
  (lam ⊓ 1) • ν + (1 - lam) • uvUniformLaw W v₀

instance uvPerturbLaw_isProbabilityMeasure (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] (v₀ : V) (lam : ℝ≥0∞) :
    IsProbabilityMeasure (uvPerturbLaw W ν v₀ lam) := by
  constructor
  simp only [uvPerturbLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rcases le_total lam 1 with h | h
  · rw [inf_of_le_left h]
    exact add_tsub_cancel_of_le h
  · rw [inf_of_le_right h, tsub_eq_zero_of_le h, add_zero]

lemma uvPerturbLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    (v₀ : V) (lam : ℝ≥0∞) : IsUVChannelLaw W (uvPerturbLaw W ν v₀ lam) := by
  haveI : IsFiniteMeasure ((lam ⊓ 1) • ν) :=
    Measure.smul_finite _ (ne_top_of_le_ne_top ENNReal.one_ne_top inf_le_right)
  haveI : IsFiniteMeasure ((1 - lam) • uvUniformLaw (U := U) W v₀) :=
    Measure.smul_finite _ (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  exact (h.smul (lam ⊓ 1)).add ((uvUniformLaw_isUVChannelLaw W v₀).smul (1 - lam))

section FullSupport

variable [MeasurableSingletonClass α] [MeasurableSingletonClass U]

lemma uvUniformLaw_map_aux_input_pos (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (v₀ : V)
    (u : U) (a : α) :
    0 < (uvUniformLaw (U := U) W v₀).map (fun q ↦ (q.1, q.2.2.1)) {(u, a)} := by
  rw [uvUniformLaw, uvLawOfInput_map_aux_input W _]
  have hset : (fun r : U × V × α ↦ (r.1, r.2.2)) ⁻¹' {(u, a)}
      = {u} ×ˢ (Set.univ ×ˢ ({a} : Set α)) := by
    ext r
    simp [Prod.ext_iff, and_comm]
  rw [Measure.map_apply (by fun_prop) (by simp), hset, Measure.prod_prod, Measure.prod_prod]
  have h₁ : 0 < (PMF.uniformOfFintype U).toMeasure {u} := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton u), PMF.uniformOfFintype_apply]
    simp [ENNReal.inv_pos]
  have h₂ : 0 < (PMF.uniformOfFintype α).toMeasure {a} := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), PMF.uniformOfFintype_apply]
    simp [ENNReal.inv_pos]
  have h₃ : (Measure.dirac v₀) Set.univ = 1 := by simp
  rw [h₃, one_mul]
  exact ENNReal.mul_pos h₁.ne' h₂.ne'

lemma uvPerturbLaw_map_aux_input_pos (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] (v₀ : V) {lam : ℝ≥0∞}
    (hlam : lam < 1) (u : U) (a : α) :
    0 < (uvPerturbLaw W ν v₀ lam).map (fun q ↦ (q.1, q.2.2.1)) {(u, a)} := by
  have hpair : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) := by fun_prop
  rw [uvPerturbLaw, Measure.map_add _ _ hpair, Measure.map_smul, Measure.map_smul,
    Measure.coe_add, Pi.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul]
  have hpos := uvUniformLaw_map_aux_input_pos (U := U) W v₀ u a
  have hne : (1 : ℝ≥0∞) - lam ≠ 0 := by
    simp only [ne_eq, tsub_eq_zero_iff_le]
    exact not_le.mpr hlam
  exact lt_of_lt_of_le (ENNReal.mul_pos hne hpos.ne') le_add_self

end FullSupport

end Perturb

/-! ## Forgetting the tag -/

section ForgetSatellite

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂]
variable {U : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

-- The forgetful image is taken as a parameter, since rewriting a measure inside `condMutualInfo`
-- is blocked by the finiteness instance it carries.
lemma condMutualInfo_le_condMutualInfo_of_isUVChannelLaw_of_map_forget
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (μ : Measure ((Bool × U) × V × α × β₁ × β₂)) [IsProbabilityMeasure μ]
    (h : IsUVChannelLaw W μ) (ρ : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ρ]
    (hρ : ρ = μ.map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V))) :
    condMutualInfo μ (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      ≤ condMutualInfo ρ (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) := by
  rw [condMutualInfo_map_comp' μ (uvRelabel (Prod.snd : Bool × U → U) (id : V → V))
    (measurable_uvRelabel measurable_snd measurable_id) ρ hρ
    (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop) (fun q ↦ q.1)
    measurable_fst]
  exact h.condMutualInfo_le_map_cond (f := (Prod.snd : Bool × U → U)) measurable_snd

end ForgetSatellite

section ForgetCorner

variable {α : Type*} [MeasurableSpace α] {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {U : Type*} [Fintype U] [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
  [MeasurableSingletonClass U]
variable {V : Type*} [MeasurableSpace V]

lemma uvInfo₂_le_uvInfo₂_map_forget_add_entropy
    (μ : Measure ((Bool × U) × V × α × β₁ × β₂)) [IsProbabilityMeasure μ] :
    (uvInfo₂ μ).toReal
      ≤ (uvInfo₂ (μ.map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V)))).toReal
        + entropy μ (fun q ↦ q.1.1) := by
  have hT : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1) := by fun_prop
  have hUc : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.2) := by fun_prop
  have hY₂ : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.2.2.2.2) := by fun_prop
  -- swap the tag to the second component of the auxiliary, then split by the chain rule
  have hswap : uvInfo₂ μ = mutualInfo μ (fun q ↦ (q.1.2, q.1.1)) (fun q ↦ q.2.2.2.2) := by
    rw [uvInfo₂]
    exact (mutualInfo_eq_of_leftInverse μ (fun q ↦ q.1) (fun q ↦ q.2.2.2.2) measurable_fst hY₂
      (f := Prod.swap) (g := Prod.swap) measurable_swap measurable_swap (fun _ ↦ rfl)).symm
  have hchain := mutualInfo_chain_rule μ (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1)
    (fun q ↦ q.2.2.2.2) (fun q ↦ q.1.2) hT hY₂ hUc
  have hforget : mutualInfo μ (fun q ↦ q.1.2) (fun q ↦ q.2.2.2.2)
      = uvInfo₂ (μ.map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V))) := by
    rw [uvInfo₂, mutualInfo_map_comp μ (uvRelabel (Prod.snd : Bool × U → U) (id : V → V))
      (measurable_uvRelabel measurable_snd measurable_id) (fun q ↦ q.1) measurable_fst
      (fun q ↦ q.2.2.2.2) (by fun_prop)]
    rfl
  -- the tag term is bounded by the entropy of the tag
  have hpen : (condMutualInfo μ (fun q ↦ q.1.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.1.2)).toReal
      ≤ entropy μ (fun q ↦ q.1.1) := by
    have h1 := condMutualInfo_eq_condEntropy_sub_condEntropy μ
      (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1) (fun q ↦ q.1.2) (fun q ↦ q.2.2.2.2)
      hT hUc hY₂
    have h2 := mutualInfo_eq_entropy_sub_condEntropy μ
      (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1) (fun q ↦ q.1.2) hT hUc
    have h3 := condEntropy_nonneg μ (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1)
      (fun q ↦ (q.1.2, q.2.2.2.2))
    have h4 : (0 : ℝ) ≤ (mutualInfo μ (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1)
      (fun q ↦ q.1.2)).toReal := ENNReal.toReal_nonneg
    linarith
  have hfin₁ : mutualInfo μ (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.2)
      (fun q ↦ q.2.2.2.2) ≠ ∞ := mutualInfo_ne_top_of_fintype_right μ _ _ hUc hY₂
  have hfin₂ : condMutualInfo μ (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1)
      (fun q ↦ q.2.2.2.2) (fun q ↦ q.1.2) ≠ ∞ := condMutualInfo_ne_top μ _ _ _ hT hY₂ hUc
  rw [hswap, hchain, ENNReal.toReal_add hfin₁ hfin₂, hforget]
  linarith

end ForgetCorner

/-! ## The two slots of the perturbed law -/

section PerturbSatellite

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂]
variable {U : Type*} [Fintype U] [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

lemma mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) (v₀ : V) {lam : ℝ≥0∞} (hlam : lam ≤ 1) :
    lam * condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      ≤ condMutualInfo (uvPerturbLaw W ν v₀ lam)
          (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) := by
  have hmix := mul_condMutualInfo_le_condMutualInfo_uvMixLaw ν (uvUniformLaw W v₀) lam hlam
  have hforget := condMutualInfo_le_condMutualInfo_of_isUVChannelLaw_of_map_forget W
    (uvMixLaw ν (uvUniformLaw W v₀) lam)
    (uvMixLaw_isUVChannelLaw W h (uvUniformLaw_isUVChannelLaw W v₀) lam)
    (uvPerturbLaw W ν v₀ lam) (uvMixLaw_map_forget ν (uvUniformLaw W v₀) lam).symm
  exact hmix.trans hforget

end PerturbSatellite

section PerturbCorner

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {U : Type*} [Fintype U] [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
  [MeasurableSingletonClass U]
variable {V : Type*} [MeasurableSpace V]

lemma mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (v₀ : V) {lam : ℝ≥0∞}
    (hlam : lam ≤ 1) :
    lam.toReal * (uvInfo₂ ν).toReal - Real.binEntropy lam.toReal
      ≤ (uvInfo₂ (uvPerturbLaw W ν v₀ lam)).toReal := by
  set μ := uvMixLaw ν (uvUniformLaw W v₀) lam with hμ
  have hlow : lam * uvInfo₂ ν ≤ uvInfo₂ μ :=
    mul_uvInfo₂_le_uvInfo₂_uvMixLaw ν (uvUniformLaw W v₀) lam hlam
  have hlow' : lam.toReal * (uvInfo₂ ν).toReal ≤ (uvInfo₂ μ).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (uvInfo₂_ne_top μ) hlow
  have hpen := uvInfo₂_le_uvInfo₂_map_forget_add_entropy (U := U) μ
  have htag : entropy μ (fun q ↦ q.1.1) = Real.binEntropy lam.toReal :=
    entropy_eq_binEntropy_of_map_boolLaw μ _ hlam (uvMixLaw_map_tag _ _ lam)
  rw [htag, hμ, uvMixLaw_map_forget] at hpen
  have hflat : (lam ⊓ 1) • ν + (1 - lam) • uvUniformLaw W v₀ = uvPerturbLaw W ν v₀ lam := rfl
  rw [hflat] at hpen
  linarith

end PerturbCorner

/-! ## The full-support pair of a channel law -/

section Assembly

variable {α : Type u} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {U : Type u} [Fintype U] [Nonempty U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [StandardBorelSpace U]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

theorem exists_fullSupport_bcInfo_ge_of_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal)
    (h₂ : R₂ ≤ (uvInfo₂ ν).toReal) :
    ∃ (pU : Measure U) (_ : IsProbabilityMeasure pU) (_ : ∀ u : U, 0 < pU.real {u})
      (K : Kernel U α) (_ : IsMarkovKernel K) (_ : ∀ (u : U) (a : α), 0 < (K u).real {a}),
      R₁ - δ ≤ bcInfo₁ pU K W ∧ R₂ - δ ≤ bcInfo₂ pU K W := by
  classical
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  set A := (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal with hA'
  set B := (uvInfo₂ ν).toReal with hB'
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  obtain ⟨ε, hε0, hε1, hεA, hεB⟩ := exists_mul_add_binEntropy_lt hA hB hδ
  set lam := ENNReal.ofReal (1 - ε) with hlam'
  have hlamR : lam.toReal = 1 - ε := ENNReal.toReal_ofReal (by linarith)
  have hlam1 : lam ≤ 1 := by
    rw [hlam', ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hlamlt : lam < 1 := by
    rw [hlam', ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by linarith)
  set μ' := uvPerturbLaw W ν v₀ lam with hμ'
  have hlaw : IsUVChannelLaw W μ' := uvPerturbLaw_isUVChannelLaw W h v₀ lam
  have hpos := uvPerturbLaw_map_aux_input_pos W ν v₀ hlamlt
  refine ⟨uvCloudLaw μ', inferInstance, uvCloudLaw_real_singleton_pos μ' hpos,
    uvSatelliteKernel μ', inferInstance, uvSatelliteKernel_real_singleton_pos μ' hpos, ?_, ?_⟩
  · rw [bcInfo₁_uvCloudLaw W hlaw]
    have hge := mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw W h v₀ hlam1
    have hfin : condMutualInfo μ' (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) ≠ ∞ :=
      condMutualInfo_ne_top μ' _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
    have hmono := ENNReal.toReal_mono hfin hge
    rw [ENNReal.toReal_mul, hlamR, ← hA'] at hmono
    have hb : 0 ≤ Real.binEntropy ε := Real.binEntropy_nonneg hε0.le hε1.le
    nlinarith
  · rw [bcInfo₂_uvCloudLaw W hlaw]
    have hge := mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw W (ν := ν) v₀ hlam1
    rw [hlamR, Real.binEntropy_one_sub, ← hB'] at hge
    nlinarith

end Assembly

/-! ## The pair-level statement -/

section PairLevel

variable {α : Type u} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {U : Type u} [Fintype U] [Nonempty U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [StandardBorelSpace U]

/-- The five-tuple law of an achievability pair, with the second auxiliary a copy of the first, so
that it carries no information beyond it. -/
noncomputable def uvLawOfPair (W : BCChannel α β₁ β₂) (pU : Measure U) (K : Kernel U α) :
    Measure (U × U × α × β₁ × β₂) :=
  uvLawOfInput W ((pU ⊗ₘ K).map (fun p ↦ (p.1, p.1, p.2)))

instance uvLawOfPair_isProbabilityMeasure (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] :
    IsProbabilityMeasure (uvLawOfPair W pU K) := by
  haveI : IsProbabilityMeasure ((pU ⊗ₘ K).map (fun p : U × α ↦ (p.1, p.1, p.2))) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable _).aemeasurable
  unfold uvLawOfPair
  infer_instance

/-- A rate pair dominated by the two informations of an achievability pair is dominated, up to
any positive slack, by the two informations of a pair giving every letter positive mass. -/
@[entry_point]
theorem exists_fullSupport_bcInfo_ge (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K]
    {R₁ R₂ δ : ℝ} (hδ : 0 < δ) (h₁ : R₁ ≤ bcInfo₁ pU K W) (h₂ : R₂ ≤ bcInfo₂ pU K W) :
    ∃ (pU' : Measure U) (_ : IsProbabilityMeasure pU') (_ : ∀ u : U, 0 < pU'.real {u})
      (K' : Kernel U α) (_ : IsMarkovKernel K') (_ : ∀ (u : U) (a : α), 0 < (K' u).real {a}),
      R₁ - δ ≤ bcInfo₁ pU' K' W ∧ R₂ - δ ≤ bcInfo₂ pU' K' W := by
  classical
  haveI : IsProbabilityMeasure ((pU ⊗ₘ K).map (fun p : U × α ↦ (p.1, p.1, p.2))) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable _).aemeasurable
  have hlaw : IsUVChannelLaw W (uvLawOfPair W pU K) := uvLawOfInput_isUVChannelLaw W _
  -- the `(U, X)` marginal of the built law is the pair itself
  have hmarg : (uvLawOfPair W pU K).map (fun q ↦ (q.1, q.2.2.1)) = pU ⊗ₘ K := by
    rw [uvLawOfPair, uvLawOfInput_map_aux_input W _,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  have hjoint : (uvLawOfPair W pU K).map (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2))
      = bcJointDistribution pU K W := by
    rw [hlaw.map_auxiliary_input_output, hmarg, bcJointDistribution]
  have hs₁ : (condMutualInfo (uvLawOfPair W pU K) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ q.1)).toReal = bcInfo₁ pU K W := by
    rw [bcInfo₁_eq_condMutualInfo_toReal pU K W,
      condMutualInfo_map_comp' (uvLawOfPair W pU K) (fun q : U × U × α × β₁ × β₂ ↦
        (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) (by fun_prop) _ hjoint.symm
        (fun q ↦ q.2.1) (by fun_prop) (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.1)
        measurable_fst]
  have hs₂ : (uvInfo₂ (uvLawOfPair W pU K)).toReal = bcInfo₂ pU K W := by
    rw [bcInfo₂_eq_mutualInfo_toReal pU K W, uvInfo₂, ← hjoint,
      mutualInfo_map_comp _ _ (by fun_prop) _ (by fun_prop) _ (by fun_prop)]
  exact exists_fullSupport_bcInfo_ge_of_isUVChannelLaw W hlaw hδ (hs₁ ▸ h₁) (hs₂ ▸ h₂)

end PairLevel

/-! ## Composition with time sharing -/

section Compose

variable {α : Type u} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

/-- Over a less noisy channel, a rate pair satisfying the three UV outer inequalities of a channel
law is dominated, up to any positive slack, by the two informations of an achievability pair whose
cloud law and satellite kernel give every letter positive mass. -/
@[entry_point]
theorem exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (hln : IsBCLessNoisy W) {m : ℕ}
    {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal)
    (hsum : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal) :
    ∃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure pU)
      (_ : ∀ x : Marton.bcAuxAlphabet.{u} k, 0 < pU.real {x})
      (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
      (_ : ∀ (x : Marton.bcAuxAlphabet.{u} k) (a : α), 0 < (K x).real {a}),
      R₁ - δ ≤ bcInfo₁ pU K W ∧ R₂ - δ ≤ bcInfo₂ pU K W := by
  classical
  obtain ⟨k, pU, hpU, K, hK, hb₁, hb₂⟩ :=
    exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw W hln h h₁ h₂ hsum
  obtain ⟨pU', hpU', hfs, K', hK', hfsK, hc₁, hc₂⟩ :=
    exists_fullSupport_bcInfo_ge W pU K hδ hb₁ hb₂
  exact ⟨k, pU', hpU', hfs, K', hK', hfsK, hc₁, hc₂⟩

lemma sub_mem_bcSuperpositionRegionNoSumRate_of_lessNoisy_of_isUVChannelLaw
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hln : IsBCLessNoisy W) {m : ℕ}
    {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal)
    (hsum : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal) :
    ((R₁ - δ, R₂ - δ) : ℝ × ℝ) ∈ bcSuperpositionRegionNoSumRate.{u} W := by
  classical
  obtain ⟨k, pU, hpU, hfs, K, hK, hfsK, hc₁, hc₂⟩ :=
    exists_fullSupport_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw W hln h hδ h₁ h₂ hsum
  refine subset_closure ?_
  simp only [Set.mem_iUnion]
  exact ⟨k, pU, hpU, hfs, K, hK, hfsK, hc₁, hc₂⟩

end Compose

end InformationTheory.Shannon.BroadcastChannel
