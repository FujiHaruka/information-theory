import InformationTheory.Shannon.BroadcastChannel.Superposition.FullSupport
import InformationTheory.Shannon.CondMutualInfoMixture

/-!
# Broadcast channel — the more capable comparison and the input-output slot

`IsBCMoreCapable` compares the two marginal channels under every input law.  The converse for a
more capable channel needs that comparison in two further shapes: conditioned on an auxiliary
variable, and read on a five-tuple law of the UV outer region.  Both are averages of the
unconditional statement over the conditional input laws, which is exactly what the mixture
identity for conditional mutual information delivers, so the comparison transports with no new
analysis.

What the comparison buys is the sum-rate inequality `I(V; Y₁) + I(X; Y₂ ∣ V) ≤ I(X; Y₁)`, the
fourth constraint of the UV outer region, which the less noisy converse discards and the more
capable one needs.  The companion bound at the receiver-2 corner, `I(U; Y₂) ≤ I(X; Y₁)`, is the
same comparison composed with the data processing inequality along `U → X → Y₂`; it is what the
sum constraint degenerates to once the first rate is clamped at zero.

The right-hand side of both bounds is `I(X; Y₁)`, the information the input carries about the
first output.  It is the slot of a five-tuple law that the two-constraint inner bound never
needed, so this file names it and records the three facts the assembly asks of it: relabeling the
auxiliaries leaves it alone, time sharing leaves it alone, and it is concave in the law, so a
positive multiple of it survives the mixture that repairs full support.

## Main definitions

* `uvInfoJoint ν` — the information `I(X; Y₁)` of a five-tuple law.

## Main statements

* `IsBCMoreCapable.condMutualInfo_le` — over a more capable channel, the receiver-2 information
  conditioned on the cloud auxiliary is at most the receiver-1 one.
* `uvInfoSum₁_le_uvInfoJoint_of_moreCapable` — over a more capable channel, the fourth UV outer
  slot of a channel law is at most `I(X; Y₁)`.
* `uvInfo₂_le_uvInfoJoint_of_moreCapable` — over a more capable channel, the receiver-2 slot of a
  channel law is at most `I(X; Y₁)`.
* `uvInfoJoint_uvTimeShareLaw` — time sharing leaves `I(X; Y₁)` unchanged.
* `mul_uvInfoJoint_le_uvInfoJoint_uvPerturbLaw` — perturbing a law toward the uniform one with
  weight `lam` keeps at least the fraction `lam` of `I(X; Y₁)`.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal

/-! ## Rewriting the arguments of an information -/

section Congr

lemma condMutualInfo_congr_measure {Ω A B C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]
    {μ ρ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ρ] (h : μ = ρ)
    (Xs : Ω → A) (Yo : Ω → B) (Zc : Ω → C) :
    condMutualInfo μ Xs Yo Zc = condMutualInfo ρ Xs Yo Zc := by
  subst h; rfl

lemma mutualInfo_congr_pair {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) (μ' : Measure Ω')
    {f : Ω → A} {g : Ω → B} {f' : Ω' → A} {g' : Ω' → B}
    (hf : Measurable f) (hg : Measurable g) (hf' : Measurable f') (hg' : Measurable g')
    (h : μ.map (fun ω ↦ (f ω, g ω)) = μ'.map (fun ω ↦ (f' ω, g' ω))) :
    mutualInfo μ f g = mutualInfo μ' f' g' := by
  have e1 : (μ.map fun ω ↦ (f ω, g ω)).map Prod.fst = μ.map f :=
    Measure.map_map measurable_fst (hf.prodMk hg)
  have e1' : (μ'.map fun ω ↦ (f' ω, g' ω)).map Prod.fst = μ'.map f' :=
    Measure.map_map measurable_fst (hf'.prodMk hg')
  have e2 : (μ.map fun ω ↦ (f ω, g ω)).map Prod.snd = μ.map g :=
    Measure.map_map measurable_snd (hf.prodMk hg)
  have e2' : (μ'.map fun ω ↦ (f' ω, g' ω)).map Prod.snd = μ'.map g' :=
    Measure.map_map measurable_snd (hf'.prodMk hg')
  have h1 : μ.map f = μ'.map f' := by rw [← e1, ← e1', h]
  have h2 : μ.map g = μ'.map g' := by rw [← e2, ← e2', h]
  unfold mutualInfo
  rw [h, h1, h2]

end Congr

/-! ## The two marginal channels under a single input law -/

section Pointwise

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

lemma mutualInfo_compProd_out₁ (p : Measure α) [IsProbabilityMeasure p]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    mutualInfo (p ⊗ₘ W) Prod.fst (fun s ↦ s.2.1) = mutualInfoOfChannel p (Kernel.fst W) := by
  rw [mutualInfoOfChannel_eq_mutualInfo_prod p (Kernel.fst W), jointDistribution_def,
    Kernel.fst_eq, Measure.compProd_map (measurable_fst : Measurable (Prod.fst : β₁ × β₂ → β₁)),
    mutualInfo_map_comp _ (Prod.map id (Prod.fst : β₁ × β₂ → β₁)) (by fun_prop)
      _ (by fun_prop) _ (by fun_prop)]
  rfl

lemma mutualInfo_compProd_out₂ (p : Measure α) [IsProbabilityMeasure p]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    mutualInfo (p ⊗ₘ W) Prod.fst (fun s ↦ s.2.2) = mutualInfoOfChannel p (Kernel.snd W) := by
  rw [mutualInfoOfChannel_eq_mutualInfo_prod p (Kernel.snd W), jointDistribution_def,
    Kernel.snd_eq, Measure.compProd_map (measurable_snd : Measurable (Prod.snd : β₁ × β₂ → β₂)),
    mutualInfo_map_comp _ (Prod.map id (Prod.snd : β₁ × β₂ → β₂)) (by fun_prop)
      _ (by fun_prop) _ (by fun_prop)]
  rfl

end Pointwise

/-! ## The conditional form of the more capable comparison -/

section Conditional

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U : Type*} [MeasurableSpace U]

lemma bcJointDistribution_eq_compProd (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcJointDistribution pU K W
      = pU ⊗ₘ (K ⊗ₖ (W.comap (Prod.snd : U × α → α) measurable_snd)) := by
  rw [bcJointDistribution, Measure.compProd_assoc']

lemma compProd_comap_snd_apply (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (u : U) :
    (K ⊗ₖ (W.comap (Prod.snd : U × α → α) measurable_snd)) u = (K u) ⊗ₘ W := by
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  congr 1

section Slots

variable [StandardBorelSpace α] [Nonempty α] [Countable U] [MeasurableSingletonClass U]

section Receiver1

variable [StandardBorelSpace β₁] [Nonempty β₁]

lemma condMutualInfo_bcJoint_out₁ (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1)
      = ∫⁻ u, mutualInfoOfChannel (K u) (Kernel.fst W) ∂pU := by
  rw [condMutualInfo_congr_measure (bcJointDistribution_eq_compProd pU K W) _ _ _,
    condMutualInfo_compProd_fst_eq_lintegral pU (K ⊗ₖ (W.comap (Prod.snd : U × α → α)
      measurable_snd)) (f := Prod.fst) (g := fun s ↦ s.2.1) measurable_fst (by fun_prop)]
  refine lintegral_congr fun u ↦ ?_
  rw [compProd_comap_snd_apply K W u, mutualInfo_compProd_out₁]

end Receiver1

section Receiver2

variable [StandardBorelSpace β₂] [Nonempty β₂]

lemma condMutualInfo_bcJoint_out₂ (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2) (fun q ↦ q.1)
      = ∫⁻ u, mutualInfoOfChannel (K u) (Kernel.snd W) ∂pU := by
  rw [condMutualInfo_congr_measure (bcJointDistribution_eq_compProd pU K W) _ _ _,
    condMutualInfo_compProd_fst_eq_lintegral pU (K ⊗ₖ (W.comap (Prod.snd : U × α → α)
      measurable_snd)) (f := Prod.fst) (g := fun s ↦ s.2.2) measurable_fst (by fun_prop)]
  refine lintegral_congr fun u ↦ ?_
  rw [compProd_comap_snd_apply K W u, mutualInfo_compProd_out₂]

end Receiver2

variable [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂]

theorem IsBCMoreCapable.condMutualInfo_le {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K] :
    condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2) (fun q ↦ q.1)
      ≤ condMutualInfo (bcJointDistribution pU K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.1)
          (fun q ↦ q.1) := by
  rw [condMutualInfo_bcJoint_out₁, condMutualInfo_bcJoint_out₂]
  exact lintegral_mono fun u ↦ hmc (K u)

end Slots

end Conditional

/-! ## The input-output slot of a five-tuple law -/

section JointSlot

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U V U' V' : Type*} [MeasurableSpace U] [MeasurableSpace V]
  [MeasurableSpace U'] [MeasurableSpace V']

/-- The information `I(X; Y₁)` of a five-tuple law. -/
noncomputable def uvInfoJoint (ν : Measure (U × V × α × β₁ × β₂)) : ℝ≥0∞ :=
  mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)

lemma uvInfoJoint_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂))
    {e₁ : U → U'} {e₂ : V → V'} (he₁ : Measurable e₁) (he₂ : Measurable e₂) :
    uvInfoJoint (ν.map (uvRelabel e₁ e₂)) = uvInfoJoint ν := by
  rw [uvInfoJoint, uvInfoJoint,
    mutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
      (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop)]
  rfl

end JointSlot

section Collapse

variable {α β₁ β₂ : Type*} [MeasurableSpace α]
  [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [MeasurableSpace β₂]
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

lemma mutualInfo_pair_out₁_eq_uvInfoJoint {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A] (ν : Measure (U × V × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (Aux : U × V × α × β₁ × β₂ → A) (hAux : Measurable Aux)
    (hmk : IsMarkovChain ν Aux (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)) :
    mutualInfo ν (fun q ↦ (Aux q, q.2.2.1)) (fun q ↦ q.2.2.2.1) = uvInfoJoint ν := by
  have hswap : mutualInfo ν (fun q ↦ (Aux q, q.2.2.1)) (fun q ↦ q.2.2.2.1)
      = mutualInfo ν (fun q ↦ (q.2.2.1, Aux q)) (fun q ↦ q.2.2.2.1) :=
    (mutualInfo_eq_of_leftInverse ν (fun q ↦ (Aux q, q.2.2.1))
      (fun q ↦ q.2.2.2.1) (by fun_prop) (by fun_prop) (f := Prod.swap) (g := Prod.swap)
      measurable_swap measurable_swap (fun _ ↦ rfl)).symm
  have hchain := mutualInfo_chain_rule ν Aux
    (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.2.1) (fun q ↦ q.2.2.1) hAux (by fun_prop) (by fun_prop)
  have hzero : condMutualInfo ν Aux (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.2.1)
      (fun q ↦ q.2.2.1) = 0 :=
    condMutualInfo_eq_zero_of_markov ν Aux (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
      hAux (by fun_prop) (by fun_prop) hmk
  rw [hswap, hchain, hzero, add_zero]
  rfl

end Collapse

/-! ## The Markov chain reaching the second receiver -/

section Transport

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]
variable {U V : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
  [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

lemma IsUVChannelLaw.isMarkovChain_U_X_Y₂ {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    IsMarkovChain ν (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) := by
  have hX : Measurable (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1) := by fun_prop
  have hU : Measurable (fun q : U × V × α × β₁ × β₂ ↦ q.1) := by fun_prop
  have hY : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.2.1, q.2.2.2.2)) := by fun_prop
  have hY₂ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.2.2) := by fun_prop
  have h₁ : IsMarkovChain ν (fun q ↦ q.1) (fun q ↦ q.2.2.1)
      (fun q ↦ (q.2.2.2.1, q.2.2.2.2)) :=
    isMarkovChain_map_left ν (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1))
      (fun q ↦ q.2.2.1) (fun q ↦ (q.2.2.2.1, q.2.2.2.2)) (by fun_prop) hX hY
      (f := (Prod.fst : U × V → U)) measurable_fst h.isMarkovChain_UV_X_Y
  have h₂ : IsMarkovChain ν (fun q ↦ (q.2.2.2.1, q.2.2.2.2)) (fun q ↦ q.2.2.1) (fun q ↦ q.1) :=
    isMarkovChain_swap ν _ _ _ hU hX hY h₁
  have h₃ : IsMarkovChain ν (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.2.1) (fun q ↦ q.1) :=
    isMarkovChain_map_left ν (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.2.1, q.2.2.2.2))
      (fun q ↦ q.2.2.1) (fun q ↦ q.1) hY hX hU
      (f := (Prod.snd : β₁ × β₂ → β₂)) measurable_snd h₂
  exact isMarkovChain_swap ν _ _ _ hY₂ hX hU h₃

end Transport

/-! ## The more capable comparison on a channel law -/

section SumBound

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]
variable {U : Type*} [MeasurableSpace U]
variable {V : Type*} [MeasurableSpace V]

section Chain

variable [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace V] [Nonempty V]

lemma uvInfoJoint_eq_uvInfo₁_add_cond (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν) :
    uvInfoJoint ν
      = uvInfo₁ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) := by
  have hchain := mutualInfo_chain_rule ν (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1)
    (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) (by fun_prop) (by fun_prop) (by fun_prop)
  rw [← mutualInfo_pair_out₁_eq_uvInfoJoint ν (fun q ↦ q.2.1) (by fun_prop)
    h.isMarkovChain_V_X_Y₁, hchain]
  rfl

end Chain

section Compare

variable [Countable V] [MeasurableSingletonClass V]

theorem condMutualInfo_out₂_le_out₁_of_moreCapable (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) :
    condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)
      ≤ condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) := by
  set σ := ν.map (fun q : U × V × α × β₁ × β₂ ↦ (q.2.1, q.1, q.2.2)) with hσ
  have hs : IsUVChannelLaw W σ := h.swap_auxiliaries
  haveI : IsProbabilityMeasure σ :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable _).aemeasurable
  have hkey := hmc.condMutualInfo_le (uvCloudLaw σ) (uvSatelliteKernel σ)
  have hjd : bcJointDistribution (uvCloudLaw σ) (uvSatelliteKernel σ) W
      = σ.map (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) :=
    bcJointDistribution_uvCloudLaw W hs
  have e₁ : condMutualInfo (bcJointDistribution (uvCloudLaw σ) (uvSatelliteKernel σ) W)
        (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1)
      = condMutualInfo σ (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) :=
    condMutualInfo_map_comp' σ (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) (by fun_prop)
      _ hjd (fun q ↦ q.2.1) (by fun_prop) (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.1)
      (by fun_prop)
  have e₂ : condMutualInfo (bcJointDistribution (uvCloudLaw σ) (uvSatelliteKernel σ) W)
        (fun q ↦ q.2.1) (fun q ↦ q.2.2.2) (fun q ↦ q.1)
      = condMutualInfo σ (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.1) :=
    condMutualInfo_map_comp' σ (fun q ↦ (q.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) (by fun_prop)
      _ hjd (fun q ↦ q.2.1) (by fun_prop) (fun q ↦ q.2.2.2) (by fun_prop) (fun q ↦ q.1)
      (by fun_prop)
  rw [e₁, e₂] at hkey
  have f₁ : condMutualInfo σ (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.1) :=
    condMutualInfo_map_comp ν (fun q : U × V × α × β₁ × β₂ ↦ (q.2.1, q.1, q.2.2)) (by fun_prop)
      (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop) (fun q ↦ q.1)
      (by fun_prop)
  have f₂ : condMutualInfo σ (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.1)
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1) :=
    condMutualInfo_map_comp ν (fun q : U × V × α × β₁ × β₂ ↦ (q.2.1, q.1, q.2.2)) (by fun_prop)
      (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.2) (by fun_prop) (fun q ↦ q.1)
      (by fun_prop)
  rw [f₁, f₂] at hkey
  exact hkey

end Compare

variable [StandardBorelSpace U] [Nonempty U] [StandardBorelSpace V] [Nonempty V]
  [Countable V] [MeasurableSingletonClass V]

theorem uvInfoSum₁_le_uvInfoJoint_of_moreCapable (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) :
    uvInfoSum₁ ν ≤ uvInfoJoint ν := by
  rw [uvInfoJoint_eq_uvInfo₁_add_cond W h, uvInfoSum₁]
  exact add_le_add le_rfl (condMutualInfo_out₂_le_out₁_of_moreCapable W hmc h)

end SumBound

section Corner

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

lemma mutualInfo_out₂_le_out₁_of_moreCapable (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) :
    mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
      ≤ mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) := by
  haveI : IsProbabilityMeasure (ν.map fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable _).aemeasurable
  have hmap : ν.map (fun q ↦ (q.2.2.1, q.2.2.2))
      = (ν.map fun q ↦ q.2.2.1) ⊗ₘ W := h.map_input_output
  have e₁ : mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
      = mutualInfoOfChannel (ν.map fun q ↦ q.2.2.1) (Kernel.fst W) := by
    rw [← mutualInfo_compProd_out₁, ← hmap,
      mutualInfo_map_comp ν (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.1, q.2.2.2)) (by fun_prop)
        _ (by fun_prop) _ (by fun_prop)]
  have e₂ : mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
      = mutualInfoOfChannel (ν.map fun q ↦ q.2.2.1) (Kernel.snd W) := by
    rw [← mutualInfo_compProd_out₂, ← hmap,
      mutualInfo_map_comp ν (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.1, q.2.2.2)) (by fun_prop)
        _ (by fun_prop) _ (by fun_prop)]
  rw [e₁, e₂]
  exact hmc _

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁]
  [StandardBorelSpace β₂] [Nonempty β₂] [StandardBorelSpace U] [Nonempty U]
  [StandardBorelSpace V] [Nonempty V]

theorem uvInfo₂_le_uvInfoJoint_of_moreCapable (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) :
    uvInfo₂ ν ≤ uvInfoJoint ν := by
  have hdpi : uvInfo₂ ν ≤ mutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) :=
    mutualInfo_le_of_markov ν (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
      (by fun_prop) (by fun_prop) (by fun_prop) h.isMarkovChain_U_X_Y₂
  exact hdpi.trans (mutualInfo_out₂_le_out₁_of_moreCapable W hmc h)

end Corner

/-! ## The input-output slot under mixing -/

section TimeShareSlot

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

lemma uvInfoJoint_smul_add_smul (ν σ : Measure (U × V × α × β₁ × β₂))
    (hσ : σ.map (fun q ↦ (q.2.2.1, q.2.2.2.1)) = ν.map (fun q ↦ (q.2.2.1, q.2.2.2.1)))
    {a b : ℝ≥0∞} (hab : a + b = 1) :
    uvInfoJoint (a • ν + b • σ) = uvInfoJoint ν := by
  have hXY : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.1, q.2.2.2.1)) := by fun_prop
  refine mutualInfo_congr_pair _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) ?_
  rw [Measure.map_add _ _ hXY, Measure.map_smul, Measure.map_smul, hσ, ← add_smul, hab, one_smul]

lemma uvInfoJoint_uvTimeShareLaw (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    (u₀ : U) (lam : ℝ≥0∞) :
    uvInfoJoint (uvTimeShareLaw ν u₀ lam) = uvInfoJoint ν := by
  have hforget : (uvTimeShareLaw ν u₀ lam).map (uvRelabel (Prod.snd : Bool × U → U) (id : V → V))
      = (lam ⊓ 1) • ν + (1 - lam) • uvCollapse ν u₀ :=
    uvMixLaw_map_forget ν (uvCollapse ν u₀) lam
  have hcoll : (uvCollapse ν u₀).map (fun q ↦ (q.2.2.1, q.2.2.2.1))
      = ν.map (fun q ↦ (q.2.2.1, q.2.2.2.1)) := by
    rw [uvCollapse, Measure.map_map
      (show Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.2.2.1, q.2.2.2.1)) by fun_prop)
      (measurable_uvRelabel (measurable_const (a := u₀)) measurable_id)]
    rfl
  have hab : (lam ⊓ 1) + (1 - lam) = 1 := by
    rcases le_total lam 1 with h | h
    · rw [inf_of_le_left h]; exact add_tsub_cancel_of_le h
    · rw [inf_of_le_right h, tsub_eq_zero_of_le h, add_zero]
  rw [← uvInfoJoint_map_uvRelabel (uvTimeShareLaw ν u₀ lam)
      (measurable_snd : Measurable (Prod.snd : Bool × U → U))
      (measurable_id : Measurable (id : V → V)),
    hforget, uvInfoJoint_smul_add_smul ν (uvCollapse ν u₀) hcoll hab]

end TimeShareSlot

section MixSlot

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]
variable {U V : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
  [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

lemma mul_uvInfoJoint_le_uvInfoJoint_uvMixLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν σ : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] [IsProbabilityMeasure σ]
    (hν : IsUVChannelLaw W ν) (hσ : IsUVChannelLaw W σ) (lam : ℝ≥0∞) (hlam : lam ≤ 1) :
    lam * uvInfoJoint ν ≤ uvInfoJoint (uvMixLaw ν σ lam) := by
  have hY₁ : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ q.2.2.2.1) := by fun_prop
  have hpair : Measurable (fun q : (Bool × U) × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) := by fun_prop
  have hmix : IsUVChannelLaw W (uvMixLaw ν σ lam) := uvMixLaw_isUVChannelLaw W hν hσ lam
  have hcollapse : uvInfoJoint (uvMixLaw ν σ lam)
      = mutualInfo (uvMixLaw ν σ lam) (fun q ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.1) :=
    (mutualInfo_pair_out₁_eq_uvInfoJoint (uvMixLaw ν σ lam) (fun q ↦ q.1) measurable_fst
      hmix.isMarkovChain_U_X_Y₁).symm
  have htrue : IsUVChannelLaw W (uvTagTrue ν) :=
    hν.map_auxiliaries measurable_prodMk_left measurable_id
  have hbr : mutualInfo (uvMixKernel ν σ true) (fun q ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.1)
      = uvInfoJoint ν := by
    change mutualInfo (uvTagTrue ν) (fun q ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.1) = uvInfoJoint ν
    rw [mutualInfo_pair_out₁_eq_uvInfoJoint (uvTagTrue ν) (fun q ↦ q.1) measurable_fst
      htrue.isMarkovChain_U_X_Y₁, uvTagTrue,
      uvInfoJoint_map_uvRelabel ν measurable_prodMk_left measurable_id]
  rw [hcollapse, uvMixLaw,
    mutualInfo_map_comp _ Prod.snd measurable_snd _ hpair _ hY₁,
    mutualInfo_compProd_eq_add_lintegral _ _ hpair hY₁ (tag := fun a ↦ a.1.1)
      (by fun_prop) (by filter_upwards [uvMixKernel_ae_tag ν σ lam] with p hp using hp),
    lintegral_boolLaw, inf_of_le_left hlam, hbr]
  exact le_add_left le_self_add

end MixSlot

section PerturbSlot

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [StandardBorelSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable {β₂ : Type*} [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]
variable {U : Type*} [Fintype U] [Nonempty U] [MeasurableSpace U] [StandardBorelSpace U]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

lemma mul_uvInfoJoint_le_uvInfoJoint_uvPerturbLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    (v₀ : V) {lam : ℝ≥0∞} (hlam : lam ≤ 1) :
    lam * uvInfoJoint ν ≤ uvInfoJoint (uvPerturbLaw W ν v₀ lam) := by
  have hmix := mul_uvInfoJoint_le_uvInfoJoint_uvMixLaw W h (uvUniformLaw_isUVChannelLaw W v₀)
    lam hlam
  have hflat : (lam ⊓ 1) • ν + (1 - lam) • uvUniformLaw W v₀ = uvPerturbLaw W ν v₀ lam := rfl
  have hmap : (uvMixLaw ν (uvUniformLaw W v₀) lam).map
        (uvRelabel (Prod.snd : Bool × U → U) (id : V → V)) = uvPerturbLaw W ν v₀ lam := by
    rw [uvMixLaw_map_forget]; exact hflat
  have hforget : uvInfoJoint (uvPerturbLaw W ν v₀ lam)
      = uvInfoJoint (uvMixLaw ν (uvUniformLaw W v₀) lam) := by
    rw [← hmap, uvInfoJoint_map_uvRelabel _
      (measurable_snd : Measurable (Prod.snd : Bool × U → U))
      (measurable_id : Measurable (id : V → V))]
  rw [hforget]
  exact hmix

end PerturbSlot

end InformationTheory.Shannon.BroadcastChannel
