import InformationTheory.Shannon.BroadcastChannel.Superposition.Assembly
import InformationTheory.Shannon.CondMutualInfoMixture

/-!
# Broadcast channel — the capacity region of a more capable channel

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

The right-hand side of both bounds is `uvInfoJoint`, the information the input carries about the
first output.  It is the slot of a five-tuple law that the two-constraint inner bound never
needed, and this file records the fact the full-support step asks of it beyond its invariance
under relabeling: it is concave in the law, so a positive multiple of it survives the mixture
that repairs full support.

Keeping that slot is what lets the inner bound keep the sum-rate constraint a general broadcast
channel needs, instead of the two-constraint region that is exact only over a less noisy one.
Time sharing between a rate pair and the corner where the cloud auxiliary is constant meets the
two separate constraints at once, and the sum constraint survives the segment because the
input-output slot is the same at both of its endpoints; perturbing the achievability pair the
segment lands on toward the uniform law then repairs its support, at a cost one weight covers for
all three slots at once.  Truncating the auxiliary of a law of the outer region moves that law
onto a finite alphabet, and leaves the input-output slot alone as well, so both costs vanish
along a single sequence of indices and the inner bound, being a closure, recovers the rate pair
itself.  Combined with the outer bound and with the achievability of the inner one, this
describes the capacity region of a more capable broadcast channel by a single-letter expression.
It subsumes the description of a less noisy one, `IsBCLessNoisy` being the stronger comparison.

The sum constraint is carried with the first rate clamped at zero, `max R₁ 0 + R₂`, which is the
form the achievability theorem takes and the form under which the inner bound is achievable with
no comparison between the two receivers.  A negative first rate is then met at the receiver-2
corner rather than by the sum-rate slot of the outer region, which is where the second of the two
comparison bounds is spent.

## Main statements

* `IsBCMoreCapable.condMutualInfo_le` — over a more capable channel, the receiver-2 information
  conditioned on the cloud auxiliary is at most the receiver-1 one.
* `uvInfoSum₁_le_uvInfoJoint_of_moreCapable` — over a more capable channel, the fourth UV outer
  slot of a channel law is at most `I(X; Y₁)`.
* `uvInfo₂_le_uvInfoJoint_of_moreCapable` — over a more capable channel, the receiver-2 slot of a
  channel law is at most `I(X; Y₁)`.
* `mul_uvInfoJoint_le_uvInfoJoint_uvPerturbLaw` — perturbing a law toward the uniform one with
  weight `lam` keeps at least the fraction `lam` of `I(X; Y₁)`.
* `bc_moreCapable_uv_subset_superposition` — the UV outer region of a more capable channel is
  contained in the three-constraint superposition inner bound.
* `bc_moreCapable_capacity_eq_uv` — the single-letter characterization: the capacity region of a
  more capable broadcast channel whose transition law gives every output pair positive mass is
  its UV outer region `bcOuterRegionUV`.
* `bc_degraded_capacity_eq_uv` — the same characterization for a physically degraded channel,
  degradedness being the strongest of the three comparisons.
* `bc_moreCapable_superposition_eq_capacity` — the same capacity region read off the
  superposition inner bound instead of the outer bound.

## Implementation notes

Transporting the comparison means exchanging the measure inside an information, which `rw` cannot
do: `condMutualInfo` takes the finiteness instance on its measure argument, so rewriting that
argument leaves a motive that is not type correct.  `condMutualInfo_congr_measure` performs the
exchange by substitution instead, and `mutualInfo_congr_pair` is the coarser form, where the two
ambient measures may differ as long as the joint law of the compared pair agrees.
`mutualInfo_compProd_out₁` and `mutualInfo_compProd_out₂` read a marginal channel off a
composition product, which is what puts the comparison in the `mutualInfoOfChannel` form
`IsBCMoreCapable` is stated in.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal

universe u

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

lemma condMutualInfo_bcJointDistribution_out₁_eq_lintegral (pU : Measure U)
    [IsProbabilityMeasure pU]
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

lemma condMutualInfo_bcJointDistribution_out₂_eq_lintegral (pU : Measure U)
    [IsProbabilityMeasure pU]
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
  rw [condMutualInfo_bcJointDistribution_out₁_eq_lintegral,
    condMutualInfo_bcJointDistribution_out₂_eq_lintegral]
  exact lintegral_mono fun u ↦ hmc (K u)

end Slots

end Conditional

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

lemma uvInfoJoint_eq_uvInfo₁_add_condMutualInfo (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
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
  set σ := ν.map (fun q : U × V × α × β₁ × β₂ ↦ (q.2.1, q.1, q.2.2))
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
  rw [uvInfoJoint_eq_uvInfo₁_add_condMutualInfo W h, uvInfoSum₁]
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

/-! ## Repairing the support with the sum constraint -/

section FullSupportAssembly

variable {α : Type u} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂]
variable {V : Type*} [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

section Law

variable {U : Type u} [Fintype U] [Nonempty U] [MeasurableSpace U]
  [MeasurableSingletonClass U] [StandardBorelSpace U]

theorem exists_fullSupport_bcInfo_ge_sumRate_of_isUVChannelLaw (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal)
    (h₂ : R₂ ≤ (uvInfo₂ ν).toReal) (h₃ : max R₁ 0 + R₂ ≤ (uvInfoJoint ν).toReal) :
    ∃ (pU : Measure U) (_ : IsProbabilityMeasure pU) (_ : ∀ u : U, 0 < pU.real {u})
      (K : Kernel U α) (_ : IsMarkovKernel K) (_ : ∀ (u : U) (a : α), 0 < (K u).real {a}),
      R₁ - δ ≤ bcInfo₁ pU K W ∧ R₂ - δ ≤ bcInfo₂ pU K W
        ∧ max (R₁ - δ) 0 + (R₂ - δ) ≤ bcInfoJoint pU K W := by
  classical
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  set A := (condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)).toReal with hA'
  set B := (uvInfo₂ ν).toReal with hB'
  set J := (uvInfoJoint ν).toReal with hJ'
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  -- One weight pays for all three slots: the satellite and the input-output slot together are
  -- bounded by `A + J`, so the two-quantity choice covers them both.
  obtain ⟨ε, hε0, hε1, hεAJ, hεB⟩ :=
    exists_mul_add_binEntropy_lt (by linarith : (0 : ℝ) ≤ A + J) hB hδ
  have hbin : 0 ≤ Real.binEntropy ε := Real.binEntropy_nonneg hε0.le hε1.le
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
    uvSatelliteKernel μ', inferInstance, uvSatelliteKernel_real_singleton_pos μ' hpos, ?_, ?_, ?_⟩
  · rw [bcInfo₁_uvCloudLaw W hlaw]
    have hge := mul_condMutualInfo_le_condMutualInfo_uvPerturbLaw W h v₀ hlam1
    have hfin : condMutualInfo μ' (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) ≠ ∞ :=
      condMutualInfo_ne_top μ' _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
    have hmono := ENNReal.toReal_mono hfin hge
    rw [ENNReal.toReal_mul, hlamR, ← hA', show (1 - ε) * A = A - ε * A from by ring] at hmono
    nlinarith [mul_nonneg hε0.le hJ]
  · rw [bcInfo₂_uvCloudLaw W hlaw]
    have hge := mul_uvInfo₂_sub_binEntropy_le_uvInfo₂_uvPerturbLaw W (ν := ν) v₀ hlam1
    rw [hlamR, Real.binEntropy_one_sub, ← hB'] at hge
    nlinarith
  · rw [bcInfoJoint_uvCloudLaw W hlaw]
    have hge := mul_uvInfoJoint_le_uvInfoJoint_uvPerturbLaw W h v₀ hlam1
    have hfin : uvInfoJoint μ' ≠ ∞ :=
      mutualInfo_ne_top_of_fintype_right μ' _ _ (by fun_prop) (by fun_prop)
    have hmono := ENNReal.toReal_mono hfin hge
    rw [ENNReal.toReal_mul, hlamR, ← hJ', show (1 - ε) * J = J - ε * J from by ring] at hmono
    have hmax : max (R₁ - δ) 0 ≤ max R₁ 0 := max_le_max (by linarith) le_rfl
    nlinarith [mul_nonneg hε0.le hA]

theorem exists_fullSupport_bcInfo_ge_sumRate (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K]
    {R₁ R₂ δ : ℝ} (hδ : 0 < δ) (h₁ : R₁ ≤ bcInfo₁ pU K W) (h₂ : R₂ ≤ bcInfo₂ pU K W)
    (h₃ : max R₁ 0 + R₂ ≤ bcInfoJoint pU K W) :
    ∃ (pU' : Measure U) (_ : IsProbabilityMeasure pU') (_ : ∀ u : U, 0 < pU'.real {u})
      (K' : Kernel U α) (_ : IsMarkovKernel K') (_ : ∀ (u : U) (a : α), 0 < (K' u).real {a}),
      R₁ - δ ≤ bcInfo₁ pU' K' W ∧ R₂ - δ ≤ bcInfo₂ pU' K' W
        ∧ max (R₁ - δ) 0 + (R₂ - δ) ≤ bcInfoJoint pU' K' W := by
  classical
  haveI : IsProbabilityMeasure ((pU ⊗ₘ K).map (fun p : U × α ↦ (p.1, p.1, p.2))) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable _).aemeasurable
  have hlaw : IsUVChannelLaw W (uvLawOfPair W pU K) := uvLawOfInput_isUVChannelLaw W _
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
  have hs₃ : (uvInfoJoint (uvLawOfPair W pU K)).toReal = bcInfoJoint pU K W := by
    rw [bcInfoJoint_eq_mutualInfo_toReal pU K W, ← hjoint,
      mutualInfo_map_comp _ _ (by fun_prop) _ (by fun_prop) _ (by fun_prop),
      mutualInfo_pair_out₁_eq_uvInfoJoint (uvLawOfPair W pU K) (fun q ↦ q.1) measurable_fst
        hlaw.isMarkovChain_U_X_Y₁]
  exact exists_fullSupport_bcInfo_ge_sumRate_of_isUVChannelLaw W hlaw hδ (hs₁ ▸ h₁) (hs₂ ▸ h₂)
    (hs₃ ▸ h₃)

end Law

lemma sub_mem_bcSuperpositionRegionSumRate_of_isUVChannelLaw (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W]
    {m : ℕ} {ν : Measure (Marton.bcAuxAlphabet.{u} m × V × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {R₁ R₂ δ : ℝ} (hδ : 0 < δ)
    (h₁ : R₁ ≤ (uvInfo₁ ν).toReal) (h₂ : R₂ ≤ (uvInfo₂ ν).toReal)
    (hs₂ : R₁ + R₂ ≤ (uvInfoSum₂ ν).toReal)
    (hs₁ : max R₁ 0 + R₂ ≤ (uvInfoJoint ν).toReal) :
    ((R₁ - δ, R₂ - δ) : ℝ × ℝ) ∈ bcSuperpositionRegionSumRate.{u} W := by
  classical
  obtain ⟨k, pU, hpU, K, hK, hb₁, hb₂, hb₃⟩ :=
    exists_bcInfo_ge_sumRate_of_isUVChannelLaw W h h₁ h₂ hs₂ hs₁
  obtain ⟨pU', hpU', hfs, K', hK', hfsK, hc₁, hc₂, hc₃⟩ :=
    exists_fullSupport_bcInfo_ge_sumRate W pU K hδ hb₁ hb₂ hb₃
  refine subset_closure ?_
  simp only [Set.mem_iUnion]
  exact ⟨k, pU', hpU', hfs, K', hK', hfsK, hc₁, hc₂, hc₃⟩

end FullSupportAssembly

/-! ## The reverse inclusion -/

section Converse

open Filter

open scoped Topology

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [StandardBorelSpace α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [StandardBorelSpace β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    [StandardBorelSpace β₂]

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Fintype β₁]
  [Nonempty β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Fintype β₂] [Nonempty β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
lemma uvInfoJoint_uvQuantizeLaw (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) (m : ℕ) :
    uvInfoJoint (uvQuantizeLaw.{u} ν m) = uvInfoJoint ν :=
  uvInfoJoint_map_uvRelabel ν (measurable_uvQuantize.{u} m) measurable_id

theorem sub_mem_bcSuperpositionRegionSumRate_of_mem_uvRegion (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {p : ℝ × ℝ} (hp : p ∈ uvRegion ν) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ((p.1 - δ, p.2 - (uvQuantizeSlack ν m).toReal - δ) : ℝ × ℝ)
      ∈ bcSuperpositionRegionSumRate.{u} W := by
  classical
  obtain ⟨hb₁, hb₂, hs₂, hs₁⟩ := hp
  have hlaw : IsUVChannelLaw W (uvQuantizeLaw.{u} ν m) := uvQuantizeLaw_isUVChannelLaw W h m
  have hslack : (0 : ℝ) ≤ (uvQuantizeSlack ν m).toReal := ENNReal.toReal_nonneg
  have hJfin : uvInfoJoint ν ≠ ∞ :=
    mutualInfo_ne_top_of_fintype_right ν _ _ (by fun_prop) (by fun_prop)
  have h₁ : p.1 ≤ (uvInfo₁ (uvQuantizeLaw.{u} ν m)).toReal := by
    rw [uvInfo₁_uvQuantizeLaw ν m]; exact hb₁
  have h₂ : p.2 - (uvQuantizeSlack ν m).toReal ≤ (uvInfo₂ (uvQuantizeLaw.{u} ν m)).toReal := by
    linarith [uvInfo₂_toReal_sub_slack_le.{u} ν m]
  have hsum : p.1 + (p.2 - (uvQuantizeSlack ν m).toReal)
      ≤ (uvInfoSum₂ (uvQuantizeLaw.{u} ν m)).toReal := by
    linarith [uvInfoSum₂_toReal_sub_slack_le.{u} W h m]
  -- The truncation leaves the input-output slot alone, so the sum constraint of the outer region
  -- carries over with the same subtraction; at a negative first rate it is the receiver-2 corner
  -- that carries it instead.
  have hJ : max p.1 0 + (p.2 - (uvQuantizeSlack ν m).toReal)
      ≤ (uvInfoJoint (uvQuantizeLaw.{u} ν m)).toReal := by
    rw [uvInfoJoint_uvQuantizeLaw ν m]
    rcases le_or_gt 0 p.1 with hp₁ | hp₁
    · rw [max_eq_left hp₁]
      linarith [ENNReal.toReal_mono hJfin (uvInfoSum₁_le_uvInfoJoint_of_moreCapable W hmc h)]
    · rw [max_eq_right hp₁.le, zero_add]
      linarith [ENNReal.toReal_mono hJfin (uvInfo₂_le_uvInfoJoint_of_moreCapable W hmc h)]
  exact sub_mem_bcSuperpositionRegionSumRate_of_isUVChannelLaw W hlaw hδ h₁ h₂ hsum hJ

theorem mem_bcSuperpositionRegionSumRate_of_mem_uvRegion (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) {p : ℝ × ℝ} (hp : p ∈ uvRegion ν) :
    p ∈ bcSuperpositionRegionSumRate.{u} W := by
  have ht : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hslack : Tendsto (fun m : ℕ ↦ (uvQuantizeSlack ν m).toReal) atTop (𝓝 0) := by
    have hcomp :=
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp (tendsto_uvQuantizeSlack ν)
    simpa [Function.comp_def] using hcomp
  have h1 : Tendsto (fun k : ℕ ↦ p.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 p.1) := by
    simpa using tendsto_const_nhds.sub ht
  have h2 : Tendsto (fun k : ℕ ↦ p.2 - (uvQuantizeSlack ν k).toReal - 1 / ((k : ℝ) + 1))
      atTop (𝓝 p.2) := by
    simpa using (tendsto_const_nhds.sub hslack).sub ht
  exact (bcSuperpositionRegionSumRate_isClosed W).mem_of_tendsto (h1.prodMk_nhds h2)
    (Eventually.of_forall fun k ↦
      sub_mem_bcSuperpositionRegionSumRate_of_mem_uvRegion W hmc h hp k (by positivity))

/-- The UV outer region of a more capable broadcast channel is contained in the three-constraint
superposition inner bound over the full-support achievability pairs.  The channel needs no support
hypothesis here: the inclusion compares two single-letter regions, and positive mass on every
output pair is asked for only where the inner bound is turned into codes
(`bcSuperpositionRegionSumRate_subset_capacity`). -/
@[entry_point]
theorem bc_moreCapable_uv_subset_superposition (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hmc : IsBCMoreCapable W) :
    bcOuterRegionUV W ⊆ bcSuperpositionRegionSumRate.{u} W := by
  refine closure_minimal ?_ (bcSuperpositionRegionSumRate_isClosed W)
  refine Set.iUnion_subset fun ν ↦ Set.iUnion_subset fun hν ↦ fun p hp ↦ ?_
  exact mem_bcSuperpositionRegionSumRate_of_mem_uvRegion W hmc hν hp

end Converse

/-! ## The capacity region of a more capable channel -/

section Equality

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [StandardBorelSpace α]
  [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [StandardBorelSpace β₁]
  [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    [StandardBorelSpace β₂]

/-- The capacity region of a more capable broadcast channel whose transition law gives every
output pair positive mass is its UV outer region `bcOuterRegionUV`, a single-letter expression in
the four information slots of a five-tuple law. -/
@[entry_point]
theorem bc_moreCapable_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hmc : IsBCMoreCapable W) :
    bcCapacityRegion W = bcOuterRegionUV W := by
  classical
  exact Set.Subset.antisymm (bc_capacity_subset_uv W)
    ((bc_moreCapable_uv_subset_superposition.{u} W hmc).trans
      (bcSuperpositionRegionSumRate_subset_capacity W hW))

/-- The capacity region of a physically degraded broadcast channel whose transition law gives
every output pair positive mass is its UV outer region.  Degradedness is the strongest of the
three comparisons, so the single-letter characterization of a more capable channel applies with
no further analysis. -/
@[entry_point]
theorem bc_degraded_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hdeg : IsBCDegraded W) :
    bcCapacityRegion W = bcOuterRegionUV W := by
  classical
  exact bc_moreCapable_capacity_eq_uv W hW hdeg.isBCLessNoisy.isBCMoreCapable

theorem bc_moreCapable_superposition_eq_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hmc : IsBCMoreCapable W) :
    bcSuperpositionRegionSumRate.{u} W = bcCapacityRegion W := by
  classical
  exact Set.Subset.antisymm (bcSuperpositionRegionSumRate_subset_capacity W hW)
    ((bc_capacity_subset_uv W).trans (bc_moreCapable_uv_subset_superposition.{u} W hmc))

end Equality

end InformationTheory.Shannon.BroadcastChannel
