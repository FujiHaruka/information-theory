import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Quantization
import InformationTheory.Shannon.BroadcastChannel.Superposition.Region

/-!
# Broadcast channel — absorbing a time-sharing variable into the superposition cloud

A point of the UV outer region is described by a five-tuple law, whose two information slots
`I(U; Y₂)` and `I(X; Y₁ ∣ U)` are the corners of a rectangle the superposition inner bound only
reaches after the rate pair has been traded along a segment.  Time sharing performs that trade:
the auxiliary is kept with probability `lam` and collapsed to a constant with probability
`1 - lam`, and both branches are carried by the single auxiliary `Bool × U`, whose first
component records which branch was taken.

Because the tag is recoverable from the auxiliary, the mixture identities for the two slots are
exact where they need to be.  The receiver-2 corner only needs the branch that keeps the
auxiliary, so the tag's own contribution is discarded and the slot is bounded below by
`lam * I(U; Y₂)`.  The satellite slot is an equality, `lam * I(X; Y₁ ∣ U) + (1 - lam) * I(X; Y₁)`,
because collapsing the auxiliary turns the conditional information into the unconditional one.
The second endpoint is where a less noisy channel enters: it forces
`I(X; Y₁ ∣ U) + I(U; Y₂) ≤ I(X; Y₁)`, so the segment traced by `lam` stays above the outer point.

## Main definitions

* `uvCloudLaw ν` and `uvSatelliteKernel ν` — the achievability pair read off a five-tuple law.
* `boolLaw lam` — the Bernoulli tag law, clamped so that it is a probability measure for every
  weight.
* `uvTagFalse σ`, `uvMixKernel ν σ` and `uvMixLaw ν σ lam` — two channel laws mixed along a
  Bernoulli tag carried by the auxiliary.
* `uvTagTrue ν`, `uvCollapse ν u₀` and `uvTagConst ν u₀` — the two branches, tagging the
  auxiliary and collapsing it.
* `uvTimeShareLaw ν u₀ lam` — the two branches mixed with weight `lam`.
* `boolProdAuxEquiv m` — the tagged auxiliary alphabet re-encoded into `Marton.bcAuxAlphabet`.

## Main statements

* `bcInfo₂_uvCloudLaw`, `bcInfo₁_uvCloudLaw` and `bcInfoJoint_uvCloudLaw` — the three
  informations of the achievability pair read off a channel law are the corresponding slots of
  that law.
* `mul_uvInfo₂_le_uvInfo₂_uvTimeShareLaw` and `condMutualInfo_uvTimeShareLaw` — the two slots of
  the time-shared law against the slots of the original one.
* `exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw` — over a less noisy channel, a rate pair
  satisfying the three UV outer inequalities of a channel law is dominated by the two
  informations of some achievability pair.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal Topology

universe u

/-! ## Time sharing on the auxiliary -/

/-! ### The tag law -/

/-- The Bernoulli tag law with weight `lam`, clamped so that it is a probability measure for
every weight.  The clamp is what makes `IsProbabilityMeasure` an instance rather than a lemma
with a side condition, and the conditional mutual information of the mixture needs that instance
in order to be stated at all. -/
noncomputable def boolLaw (lam : ℝ≥0∞) : Measure Bool :=
  (lam ⊓ 1) • Measure.dirac true + (1 - lam) • Measure.dirac false

instance boolLaw_isProbabilityMeasure (lam : ℝ≥0∞) : IsProbabilityMeasure (boolLaw lam) := by
  constructor
  simp only [boolLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rcases le_total lam 1 with h | h
  · rw [inf_of_le_left h]
    exact add_tsub_cancel_of_le h
  · rw [inf_of_le_right h, tsub_eq_zero_of_le h, add_zero]

lemma lintegral_boolLaw (lam : ℝ≥0∞) (F : Bool → ℝ≥0∞) :
    ∫⁻ t, F t ∂(boolLaw lam) = (lam ⊓ 1) * F true + (1 - lam) * F false := by
  rw [boolLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, smul_eq_mul, smul_eq_mul]

/-! ### The two branches and their mixture -/

section Mixture

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

/-- The branch that keeps the auxiliary, tagging it with `true`. -/
noncomputable def uvTagTrue (ν : Measure (U × V × α × β₁ × β₂)) :
    Measure ((Bool × U) × V × α × β₁ × β₂) :=
  ν.map (uvRelabel (fun u ↦ (true, u)) id)

/-- The branch that keeps the auxiliary, tagging it with `false`. -/
noncomputable def uvTagFalse (σ : Measure (U × V × α × β₁ × β₂)) :
    Measure ((Bool × U) × V × α × β₁ × β₂) :=
  σ.map (uvRelabel (fun u ↦ (false, u)) id)

instance uvTagTrue_isProbabilityMeasure (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (uvTagTrue ν) :=
  Measure.isProbabilityMeasure_map
    (measurable_uvRelabel (measurable_prodMk_left) measurable_id).aemeasurable

instance uvTagFalse_isProbabilityMeasure (σ : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure σ] : IsProbabilityMeasure (uvTagFalse σ) :=
  Measure.isProbabilityMeasure_map
    (measurable_uvRelabel (measurable_prodMk_left) measurable_id).aemeasurable

/-- The kernel that selects one of two tagged laws from the tag. -/
noncomputable def uvMixKernel (ν σ : Measure (U × V × α × β₁ × β₂)) :
    Kernel Bool ((Bool × U) × V × α × β₁ × β₂) :=
  Kernel.ofFunOfCountable (fun t ↦ if t then uvTagTrue ν else uvTagFalse σ)

instance uvMixKernel_isMarkovKernel (ν σ : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] : IsMarkovKernel (uvMixKernel ν σ) := by
  refine ⟨fun t ↦ ?_⟩
  change IsProbabilityMeasure (if t then uvTagTrue ν else uvTagFalse σ)
  cases t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    infer_instance
  · simp only [↓reduceIte]
    infer_instance

/-- The two laws mixed with weight `lam`, carried by the auxiliary `Bool × U`. -/
noncomputable def uvMixLaw (ν σ : Measure (U × V × α × β₁ × β₂)) (lam : ℝ≥0∞) :
    Measure ((Bool × U) × V × α × β₁ × β₂) :=
  ((boolLaw lam) ⊗ₘ (uvMixKernel ν σ)).map Prod.snd

instance uvMixLaw_isProbabilityMeasure (ν σ : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] (lam : ℝ≥0∞) :
    IsProbabilityMeasure (uvMixLaw ν σ lam) :=
  Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

lemma uvMixLaw_eq (ν σ : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure σ] (lam : ℝ≥0∞) :
    uvMixLaw ν σ lam = (lam ⊓ 1) • uvTagTrue ν + (1 - lam) • uvTagFalse σ := by
  ext s hs
  rw [uvMixLaw, ← Measure.snd, Measure.snd_compProd,
    Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_boolLaw]
  simp [uvMixKernel, Kernel.ofFunOfCountable, Measure.add_apply, Measure.smul_apply]

lemma uvMixKernel_ae_tag (ν σ : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure σ] (lam : ℝ≥0∞) :
    ∀ᵐ p ∂((boolLaw lam) ⊗ₘ (uvMixKernel ν σ)), (p.2.1).1 = p.1 := by
  rw [Measure.ae_compProd_iff
    (p := fun p : Bool × ((Bool × U) × V × α × β₁ × β₂) ↦ (p.2.1).1 = p.1)
    (measurableSet_eq_fun
      (measurable_fst.comp (measurable_fst.comp measurable_snd)) measurable_fst)]
  filter_upwards with t
  cases t
  · change ∀ᵐ q ∂(uvMixKernel ν σ false), (q.1).1 = false
    rw [uvMixKernel]
    change ∀ᵐ q ∂(uvTagFalse σ), (q.1).1 = false
    rw [uvTagFalse, ae_map_iff
      (measurable_uvRelabel (measurable_prodMk_left) measurable_id).aemeasurable
      (p := fun q : (Bool × U) × V × α × β₁ × β₂ ↦ (q.1).1 = false)
      (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const)]
    filter_upwards with q
    rfl
  · change ∀ᵐ q ∂(uvMixKernel ν σ true), (q.1).1 = true
    rw [uvMixKernel]
    change ∀ᵐ q ∂(uvTagTrue ν), (q.1).1 = true
    rw [uvTagTrue, ae_map_iff
      (measurable_uvRelabel (measurable_prodMk_left) measurable_id).aemeasurable
      (p := fun q : (Bool × U) × V × α × β₁ × β₂ ↦ (q.1).1 = true)
      (measurableSet_eq_fun (measurable_fst.comp measurable_fst) measurable_const)]
    filter_upwards with q
    rfl

lemma uvTagTrue_map_forget (ν : Measure (U × V × α × β₁ × β₂)) :
    (uvTagTrue ν).map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V)) = ν := by
  rw [uvTagTrue, Measure.map_map (measurable_uvRelabel measurable_snd measurable_id)
    (measurable_uvRelabel (measurable_prodMk_left) measurable_id)]
  exact Measure.map_id

lemma uvTagFalse_map_forget (σ : Measure (U × V × α × β₁ × β₂)) :
    (uvTagFalse σ).map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V)) = σ := by
  rw [uvTagFalse, Measure.map_map (measurable_uvRelabel measurable_snd measurable_id)
    (measurable_uvRelabel (measurable_prodMk_left) measurable_id)]
  exact Measure.map_id

lemma uvMixLaw_map_forget (ν σ : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure σ] (lam : ℝ≥0∞) :
    (uvMixLaw ν σ lam).map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V))
      = (lam ⊓ 1) • ν + (1 - lam) • σ := by
  rw [uvMixLaw_eq, Measure.map_add _ _ (measurable_uvRelabel measurable_snd measurable_id),
    Measure.map_smul, Measure.map_smul, uvTagTrue_map_forget, uvTagFalse_map_forget]

lemma uvMixLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν σ : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : IsUVChannelLaw W ν) (hσ : IsUVChannelLaw W σ) (lam : ℝ≥0∞) :
    IsUVChannelLaw W (uvMixLaw ν σ lam) := by
  haveI : IsFiniteMeasure ((lam ⊓ 1) • uvTagTrue ν) :=
    Measure.smul_finite _ (ne_top_of_le_ne_top ENNReal.one_ne_top inf_le_right)
  haveI : IsFiniteMeasure ((1 - lam) • uvTagFalse σ) :=
    Measure.smul_finite _ (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  rw [uvMixLaw_eq ν σ lam]
  refine ((hν.map_auxiliaries (measurable_prodMk_left) measurable_id).smul (lam ⊓ 1)).add ?_
  exact (hσ.map_auxiliaries (measurable_prodMk_left) measurable_id).smul (1 - lam)

lemma uvMixLaw_map_tag (ν σ : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure σ] (lam : ℝ≥0∞) :
    (uvMixLaw ν σ lam).map (fun q ↦ q.1.1) = boolLaw lam := by
  rw [uvMixLaw, Measure.map_map (by fun_prop) measurable_snd]
  have hae : (fun p : Bool × ((Bool × U) × V × α × β₁ × β₂) ↦ p.2.1.1)
      =ᵐ[(boolLaw lam) ⊗ₘ (uvMixKernel ν σ)] Prod.fst := by
    filter_upwards [uvMixKernel_ae_tag ν σ lam] with p hp using hp
  rw [show ((fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1.1) ∘
      (Prod.snd : Bool × ((Bool × U) × V × α × β₁ × β₂) → _))
      = (fun p : Bool × ((Bool × U) × V × α × β₁ × β₂) ↦ p.2.1.1) from rfl,
    Measure.map_congr hae]
  exact Measure.fst_compProd _ _

/-- The law with its auxiliary collapsed to the constant letter `u₀`. -/
noncomputable def uvCollapse (ν : Measure (U × V × α × β₁ × β₂)) (u₀ : U) :
    Measure (U × V × α × β₁ × β₂) :=
  ν.map (uvRelabel (fun _ ↦ u₀) id)

instance uvCollapse_isProbabilityMeasure (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (u₀ : U) : IsProbabilityMeasure (uvCollapse ν u₀) :=
  Measure.isProbabilityMeasure_map
    (measurable_uvRelabel measurable_const measurable_id).aemeasurable

/-- The branch that collapses the auxiliary to the constant `(false, u₀)`. -/
noncomputable def uvTagConst (ν : Measure (U × V × α × β₁ × β₂)) (u₀ : U) :
    Measure ((Bool × U) × V × α × β₁ × β₂) :=
  uvTagFalse (uvCollapse ν u₀)

instance uvTagConst_isProbabilityMeasure (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (u₀ : U) : IsProbabilityMeasure (uvTagConst ν u₀) :=
  uvTagFalse_isProbabilityMeasure _

lemma uvTagConst_eq_map (ν : Measure (U × V × α × β₁ × β₂)) (u₀ : U) :
    uvTagConst ν u₀ = ν.map (uvRelabel (fun _ ↦ (false, u₀)) (id : V → V)) := by
  rw [uvTagConst, uvTagFalse, uvCollapse, Measure.map_map
    (measurable_uvRelabel (measurable_prodMk_left) measurable_id)
    (measurable_uvRelabel measurable_const measurable_id)]
  rfl

/-- The two branches mixed with weight `lam`, carried by the auxiliary `Bool × U`. -/
noncomputable def uvTimeShareLaw (ν : Measure (U × V × α × β₁ × β₂)) (u₀ : U) (lam : ℝ≥0∞) :
    Measure ((Bool × U) × V × α × β₁ × β₂) :=
  uvMixLaw ν (uvCollapse ν u₀) lam

instance uvTimeShareLaw_isProbabilityMeasure (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (u₀ : U) (lam : ℝ≥0∞) :
    IsProbabilityMeasure (uvTimeShareLaw ν u₀ lam) :=
  uvMixLaw_isProbabilityMeasure _ _ _

lemma uvTimeShareLaw_eq (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] (u₀ : U)
    (lam : ℝ≥0∞) :
    uvTimeShareLaw ν u₀ lam = (lam ⊓ 1) • uvTagTrue ν + (1 - lam) • uvTagConst ν u₀ :=
  uvMixLaw_eq ν (uvCollapse ν u₀) lam

lemma uvTimeShareLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    (u₀ : U) (lam : ℝ≥0∞) : IsUVChannelLaw W (uvTimeShareLaw ν u₀ lam) := by
  refine uvMixLaw_isUVChannelLaw W h ?_ lam
  exact h.map_auxiliaries measurable_const measurable_id

lemma uvInfo₂_uvTagTrue (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] :
    uvInfo₂ (uvTagTrue ν) = uvInfo₂ ν :=
  uvInfo₂_map_uvRelabel ν (measurable_prodMk_left) measurable_id measurable_snd
    (fun _ ↦ rfl)

end Mixture

/-! ## The information slots of the time-shared law -/

/-! ### Conditioning on a constant -/

section Constant

variable {Ω A B C : Type*} [MeasurableSpace Ω]
variable [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
variable [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]

lemma condMutualInfo_eq_mutualInfo_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (Zc : Ω → C) (hXs : Measurable Xs) (hYo : Measurable Yo)
    (hZc : Measurable Zc) (c : C) (hc : Zc =ᵐ[μ] fun _ ↦ c) :
    condMutualInfo μ Xs Yo Zc = mutualInfo μ Xs Yo := by
  have hchain := mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc
  have hzero : mutualInfo μ Zc Yo = 0 := mutualInfo_eq_zero_of_ae_const μ Zc Yo hYo c hc
  have hae : (fun ω ↦ (Zc ω, Xs ω)) =ᵐ[μ] fun ω ↦ (c, Xs ω) := by
    filter_upwards [hc] with ω hω
    rw [hω]
  have hpair : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Xs Yo := by
    rw [mutualInfo_congr_ae μ Yo hae]
    exact mutualInfo_eq_of_leftInverse μ Xs Yo hXs hYo (f := fun a ↦ (c, a)) (g := Prod.snd)
      (measurable_const.prodMk measurable_id) measurable_snd (fun _ ↦ rfl)
  rw [hpair, hzero, zero_add] at hchain
  exact hchain.symm

end Constant

section Slots

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U V : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
variable [MeasurableSpace V]

/-! ### The receiver-2 corner -/

section Corner

variable [Nonempty β₂] [StandardBorelSpace β₂]

lemma mul_uvInfo₂_le_uvInfo₂_uvTimeShareLaw (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (u₀ : U) (lam : ℝ≥0∞) (hlam : lam ≤ 1) :
    lam * uvInfo₂ ν ≤ uvInfo₂ (uvTimeShareLaw ν u₀ lam) := by
  have hU : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hY₂ : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.2.2.2.2) := by fun_prop
  simp only [uvInfo₂, uvTimeShareLaw, uvMixLaw]
  rw [mutualInfo_map_comp _ Prod.snd measurable_snd _ hU _ hY₂,
    mutualInfo_compProd_eq_add_lintegral _ _ hU hY₂ (tag := fun a ↦ a.1) measurable_fst
      (by filter_upwards [uvMixKernel_ae_tag ν (uvCollapse ν u₀) lam] with p hp using hp),
    lintegral_boolLaw, inf_of_le_left hlam]
  have hbr : mutualInfo (uvMixKernel ν (uvCollapse ν u₀) true) (fun q ↦ q.1)
      (fun q ↦ q.2.2.2.2) = uvInfo₂ ν := by
    show mutualInfo (uvTagTrue ν) (fun q ↦ q.1) (fun q ↦ q.2.2.2.2) = uvInfo₂ ν
    exact uvInfo₂_uvTagTrue ν
  rw [hbr]
  exact le_add_left le_self_add

end Corner

/-! ### The satellite conditional information -/

section Satellite

variable [Nonempty α] [StandardBorelSpace α]
variable [Fintype β₁] [Nonempty β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]

lemma condMutualInfo_uvTagTrue (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] :
    condMutualInfo (uvTagTrue ν) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) := by
  rw [condMutualInfo_map_comp' ν (uvRelabel (fun u : U ↦ (true, u)) id)
    (measurable_uvRelabel (measurable_prodMk_left) measurable_id) (uvTagTrue ν) rfl
    (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop) (fun q ↦ q.1)
    measurable_fst]
  exact condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
    (fun q ↦ q.1) (by fun_prop) (by fun_prop) measurable_fst
    (measurable_prodMk_left) measurable_snd (fun _ ↦ rfl)
    (mutualInfo_ne_top_of_fintype_right ν _ _ measurable_fst (by fun_prop))

omit [StandardBorelSpace U] [Nonempty U] [Fintype β₁] [MeasurableSingletonClass β₁] in
lemma condMutualInfo_uvTagConst (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    (u₀ : U) :
    condMutualInfo (uvTagConst ν u₀) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) := by
  rw [condMutualInfo_map_comp' ν (uvRelabel (fun _ : U ↦ (false, u₀)) id)
    (measurable_uvRelabel measurable_const measurable_id) (uvTagConst ν u₀)
    (uvTagConst_eq_map ν u₀)
    (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop) (fun q ↦ q.1)
    measurable_fst]
  exact condMutualInfo_eq_mutualInfo_of_ae_const ν _ _ _ (by fun_prop) (by fun_prop)
    measurable_const (false, u₀) (Filter.Eventually.of_forall fun _ ↦ rfl)

lemma condMutualInfo_uvTimeShareLaw (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    (u₀ : U) (lam : ℝ≥0∞) (hlam : lam ≤ 1) :
    condMutualInfo (uvTimeShareLaw ν u₀ lam)
        (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = lam * condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
        + (1 - lam) * mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) := by
  have hX : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.2.2.1) := by fun_prop
  have hY₁ : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.2.2.2.1) := by fun_prop
  have hU : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hmargfin : ∫⁻ t, mutualInfo (uvMixKernel ν (uvCollapse ν u₀) t) (fun q ↦ q.1)
      (fun q ↦ q.2.2.2.1) ∂(boolLaw lam) ≠ ∞ := by
    rw [lintegral_boolLaw]
    refine ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top inf_le_right) ?_,
        ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) ?_⟩
    · show mutualInfo (uvTagTrue ν) _ _ ≠ ∞
      exact mutualInfo_ne_top_of_fintype_right _ _ _ measurable_fst (by fun_prop)
    · show mutualInfo (uvTagConst ν u₀) _ _ ≠ ∞
      exact mutualInfo_ne_top_of_fintype_right _ _ _ measurable_fst (by fun_prop)
  rw [condMutualInfo_map_comp' ((boolLaw lam) ⊗ₘ (uvMixKernel ν (uvCollapse ν u₀))) Prod.snd
      measurable_snd (uvTimeShareLaw ν u₀ lam) rfl _ hX _ hY₁ _ hU,
    condMutualInfo_compProd_snd_eq_lintegral _ _ hX hY₁ hU (tag := fun a ↦ a.1) measurable_fst
      (by filter_upwards [uvMixKernel_ae_tag ν (uvCollapse ν u₀) lam] with p hp using hp)
      (mutualInfo_ne_top_of_fintype_right _ _ _ measurable_fst (by fun_prop)) hmargfin,
    lintegral_boolLaw, inf_of_le_left hlam]
  congr 1
  · exact congrArg (lam * ·) (condMutualInfo_uvTagTrue ν)
  · exact congrArg ((1 - lam) * ·) (condMutualInfo_uvTagConst ν u₀)

end Satellite

end Slots

/-! ## Reading an achievability pair off a channel law -/

/-! ### The cloud law and the satellite kernel -/

section CloudDefs

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

/-- The cloud law of a five-tuple law: the marginal of the first auxiliary. -/
noncomputable def uvCloudLaw (ν : Measure (U × V × α × β₁ × β₂)) : Measure U :=
  ν.map (fun q ↦ q.1)

/-- The satellite kernel of a five-tuple law: the conditional law of the input letter given
the first auxiliary. -/
noncomputable def uvSatelliteKernel [StandardBorelSpace α] [Nonempty α]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Kernel U α :=
  condDistrib (fun q ↦ q.2.2.1) (fun q ↦ q.1) ν

instance uvCloudLaw_isProbabilityMeasure (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (uvCloudLaw ν) :=
  Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

section SatelliteKernel

variable [Nonempty α] [StandardBorelSpace α]

instance uvSatelliteKernel_isMarkovKernel (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] : IsMarkovKernel (uvSatelliteKernel ν) := by
  unfold uvSatelliteKernel
  infer_instance

theorem bcJointDistribution_uvCloudLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    bcJointDistribution (uvCloudLaw ν) (uvSatelliteKernel ν) W
      = ν.map (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) := by
  rw [h.map_auxiliary_input_output, bcJointDistribution, uvCloudLaw, uvSatelliteKernel,
    compProd_map_condDistrib (X := fun q : U × V × α × β₁ × β₂ ↦ q.1) (by fun_prop)]

end SatelliteKernel

end CloudDefs

/-! ### The three informations of the achievability pair -/

section Bridge

variable {α : Type u} {β₁ β₂ : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
variable [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {U : Type u} [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [StandardBorelSpace U]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

omit [StandardBorelSpace β₁] [StandardBorelSpace β₂] [StandardBorelSpace U]
  [StandardBorelSpace V] [Nonempty V] in
theorem bcInfo₂_uvCloudLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    bcInfo₂ (uvCloudLaw ν) (uvSatelliteKernel ν) W = (uvInfo₂ ν).toReal := by
  rw [bcInfo₂_eq_mutualInfo_toReal, bcJointDistribution_uvCloudLaw W h, uvInfo₂,
    mutualInfo_map_comp ν _ (by fun_prop) _ (by fun_prop) _ (by fun_prop)]

omit [StandardBorelSpace β₂] [StandardBorelSpace U] [StandardBorelSpace V] [Nonempty V] in
theorem bcInfo₁_uvCloudLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    bcInfo₁ (uvCloudLaw ν) (uvSatelliteKernel ν) W
      = (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal := by
  rw [bcInfo₁_eq_condMutualInfo_toReal,
    condMutualInfo_map_comp' ν (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2))
      (by fun_prop) _ (bcJointDistribution_uvCloudLaw W h) _ (by fun_prop) _ (by fun_prop)
      _ (by fun_prop)]

theorem bcInfoJoint_uvCloudLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    bcInfoJoint (uvCloudLaw ν) (uvSatelliteKernel ν) W
      = (mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)).toReal := by
  rw [bcInfoJoint_eq_mutualInfo_toReal, bcJointDistribution_uvCloudLaw W h,
    mutualInfo_map_comp ν _ (by fun_prop) _ (by fun_prop) _ (by fun_prop)]
  congr 1
  -- `I((U, X); Y₁) = I(X; Y₁) + I(U; Y₁ ∣ X)` and the channel law kills the second term.
  have hswap : mutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.1)
      = mutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.1, q.1)) (fun q ↦ q.2.2.2.1) :=
    (mutualInfo_eq_of_leftInverse ν (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1))
      (fun q ↦ q.2.2.2.1) (by fun_prop) (by fun_prop) (f := Prod.swap) (g := Prod.swap)
      measurable_swap measurable_swap (fun _ ↦ rfl)).symm
  have hchain := mutualInfo_chain_rule ν (fun q : U × V × α × β₁ × β₂ ↦ q.1)
    (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.2.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have hzero : condMutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ q.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ q.2.2.1) = 0 :=
    condMutualInfo_eq_zero_of_markov ν (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
      (by fun_prop) (by fun_prop) (by fun_prop) h.isMarkovChain_U_X_Y₁
  rw [hswap, hchain, hzero, add_zero]

end Bridge

/-! ## Landing in the auxiliary alphabet of the inner bound -/

/-- The tagged auxiliary alphabet re-encoded into the auxiliary alphabet of the inner bound. -/
noncomputable def boolProdAuxEquiv (m : ℕ) :
    Bool × Marton.bcAuxAlphabet.{u} m ≃ Marton.bcAuxAlphabet.{u} (2 * m + 1) :=
  (Fintype.equivFinOfCardEq (α := Bool × ULift.{u} (Fin (m + 1))) (n := 2 * m + 1 + 1)
    (by simp; ring)).trans Equiv.ulift.symm

section Landing

variable {α β₁ β₂ : Type*}
variable [Nonempty α] [MeasurableSpace α] [StandardBorelSpace α]
variable [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁]
variable [MeasurableSpace β₂]
variable {U U' : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
  [MeasurableSpace U']
variable {V : Type*} [MeasurableSpace V]

lemma condMutualInfo_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {d₁ : U' → U} (he₁ : Measurable e₁) (hd₁ : Measurable d₁)
    (h₁ : ∀ u, d₁ (e₁ u) = u) :
    condMutualInfo (ν.map (uvRelabel e₁ (id : V → V)))
        (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) := by
  rw [condMutualInfo_map_comp ν (uvRelabel e₁ (id : V → V))
    (measurable_uvRelabel he₁ measurable_id) (fun q ↦ q.2.2.1) (by fun_prop)
    (fun q ↦ q.2.2.2.1) (by fun_prop) (fun q ↦ q.1) measurable_fst]
  exact condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
    (fun q ↦ q.1) (by fun_prop) (by fun_prop) measurable_fst he₁ hd₁ h₁
    (mutualInfo_ne_top_of_fintype_right ν _ _ measurable_fst (by fun_prop))

end Landing

/-! ## Tracing the segment between the two endpoints -/

section Assembly

variable {α : Type u} {β₁ β₂ : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
variable [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

omit [StandardBorelSpace β₂] [StandardBorelSpace V] [Nonempty V] in
lemma exists_bcInfo_ge_of_tagged (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {m : ℕ}
    {ν : Measure ((Bool × Marton.bcAuxAlphabet.{u} m) × V × α × β₁ × β₂)}
    [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) {R₁ R₂ : ℝ}
    (h₁ : R₁ ≤ (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal)
    (h₂ : R₂ ≤ (uvInfo₂ ν).toReal) :
    ∃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure pU)
      (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K),
      R₁ ≤ bcInfo₁ pU K W ∧ R₂ ≤ bcInfo₂ pU K W := by
  have he : Measurable (boolProdAuxEquiv.{u} m) := measurable_of_countable _
  have hd : Measurable (boolProdAuxEquiv.{u} m).symm := measurable_of_countable _
  set ν' := ν.map (uvRelabel (boolProdAuxEquiv.{u} m) (id : V → V)) with hν'
  have hlaw : IsUVChannelLaw W ν' := h.map_auxiliaries he measurable_id
  haveI : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map (measurable_uvRelabel he measurable_id).aemeasurable
  have hcmi : condMutualInfo ν' (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) :=
    condMutualInfo_map_uvRelabel ν he hd (boolProdAuxEquiv.{u} m).symm_apply_apply
  have hinfo₂ : uvInfo₂ ν' = uvInfo₂ ν :=
    uvInfo₂_map_uvRelabel ν he measurable_id hd (boolProdAuxEquiv.{u} m).symm_apply_apply
  refine ⟨2 * m + 1, uvCloudLaw ν', inferInstance, uvSatelliteKernel ν', inferInstance, ?_, ?_⟩
  · rw [bcInfo₁_uvCloudLaw W hlaw, hcmi]
    exact h₁
  · rw [bcInfo₂_uvCloudLaw W hlaw, hinfo₂]
    exact h₂

theorem exists_bcInfo_ge_of_lessNoisy_of_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) {m : ℕ}
    {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {R₁ R₂ : ℝ}
    (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal)
    (hsum : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal) :
    ∃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k)) (_ : IsProbabilityMeasure pU)
      (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K),
      R₁ ≤ bcInfo₁ pU K W ∧ R₂ ≤ bcInfo₂ pU K W := by
  have hBfin : uvInfo₂ ν ≠ ∞ := uvInfo₂_ne_top ν
  have hAfin : condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) ≠ ∞ := by
    have := uvInfoSum₂_ne_top ν
    simp only [uvInfoSum₂, ENNReal.add_ne_top] at this
    exact this.2
  have hJfin : mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) ≠ ∞ :=
    mutualInfo_ne_top_of_fintype_right ν _ _ (by fun_prop) (by fun_prop)
  set a := (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal with ha'
  set b := (uvInfo₂ ν).toReal with hb'
  set J := (mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)).toReal with hJ'
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  -- The sum-rate slot splits into the two slots, both of which are finite.
  have hsum' : R₁ + R₂ ≤ b + a := by
    simp only [uvInfoSum₂, ENNReal.toReal_add hBfin hAfin] at hsum
    exact hsum
  -- A less noisy channel makes the input information dominate the two slots together.
  have hab : a + b ≤ J := by
    have hle := bc_lessNoisy_infoJoint_ge (uvCloudLaw ν) (uvSatelliteKernel ν) W hln
    rwa [bcInfo₁_uvCloudLaw W h, bcInfo₂_uvCloudLaw W h, bcInfoJoint_uvCloudLaw W h] at hle
  -- The receiver-1 corner is dominated by the input information as well.
  have hcJ : (uvInfo₁ ν).toReal ≤ J :=
    ENNReal.toReal_mono hJfin (mutualInfo_le_of_markov ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.1)
      (fun q ↦ q.2.2.2.1) (by fun_prop) (by fun_prop) (by fun_prop) h.isMarkovChain_V_X_Y₁)
  obtain ⟨u₀⟩ : Nonempty (Marton.bcAuxAlphabet.{u} m) := inferInstance
  -- The satellite slot of the time-shared law traces the segment between the two endpoints.
  have hslot₁ : ∀ lam : ℝ≥0∞, lam ≤ 1 →
      (condMutualInfo (uvTimeShareLaw ν u₀ lam) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
          (fun q ↦ q.1)).toReal = lam.toReal * a + (1 - lam.toReal) * J := by
    intro lam hlam
    rw [condMutualInfo_uvTimeShareLaw ν u₀ lam hlam,
      ENNReal.toReal_add
        (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hlam) hAfin)
        (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hJfin),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hlam ENNReal.one_ne_top, ENNReal.toReal_one]
  have hslot₂ : ∀ lam : ℝ≥0∞, lam ≤ 1 →
      lam.toReal * b ≤ (uvInfo₂ (uvTimeShareLaw ν u₀ lam)).toReal := by
    intro lam hlam
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (uvInfo₂_ne_top _)
      (mul_uvInfo₂_le_uvInfo₂_uvTimeShareLaw ν u₀ lam hlam)
  rcases le_or_gt R₂ 0 with hR₂ | hR₂
  · -- A nonpositive second rate asks for a constant auxiliary.
    refine exists_bcInfo_ge_of_tagged W (uvTimeShareLaw_isUVChannelLaw W h u₀ 0) ?_
      (hR₂.trans ENNReal.toReal_nonneg)
    rw [hslot₁ 0 zero_le_one, ENNReal.toReal_zero]
    linarith [h₁]
  · -- A positive second rate is met exactly at `lam = R₂ / I(U; Y₂)`.
    have hb0 : 0 < b := lt_of_lt_of_le hR₂ h₂
    have hlam0 : 0 < R₂ / b := div_pos hR₂ hb0
    have hlam1 : R₂ / b ≤ 1 := (div_le_one hb0).mpr h₂
    have hbb : (R₂ / b) * b = R₂ := div_mul_cancel₀ R₂ (ne_of_gt hb0)
    have hlam : ENNReal.ofReal (R₂ / b) ≤ 1 := ENNReal.ofReal_le_one.mpr hlam1
    have hlamR : (ENNReal.ofReal (R₂ / b)).toReal = R₂ / b :=
      ENNReal.toReal_ofReal hlam0.le
    refine exists_bcInfo_ge_of_tagged W
      (uvTimeShareLaw_isUVChannelLaw W h u₀ (ENNReal.ofReal (R₂ / b))) ?_ ?_
    · rw [hslot₁ _ hlam, hlamR]
      nlinarith [mul_le_mul_of_nonneg_left hab (by linarith : (0 : ℝ) ≤ 1 - R₂ / b)]
    · have hge := hslot₂ _ hlam
      rwa [hlamR, hbb] at hge

end Assembly

end InformationTheory.Shannon.BroadcastChannel
