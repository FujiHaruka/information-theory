import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Operational
import InformationTheory.Shannon.BroadcastChannel.OuterBound
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Region
import InformationTheory.Shannon.CondMutualInfoMixture

/-!
# Broadcast channel — the operational capacity region lies in the UV outer region

The UV outer region `bcOuterRegionUV` is the closure of a union of quadrilaterals indexed by the
five-tuple laws that the channel generates, the laws satisfying `IsUVChannelLaw`.  What is left
is to exhibit a code as such a law: the letter laws of a code are channel laws, and time-sharing
mixes them into a single one whose information slots dominate the letter averages.

The main result is `bc_capacity_subset_uv`: the operational capacity region of the channel lies
in this region.  The rate pair of a code, each coordinate discounted by the error probability of
its receiver and by two bits per letter, is a point of the quadrilateral of the time-shared letter
law; the discount vanishes as the error tolerance shrinks and the block length grows, and the
region is a closed lower set, so the limit and the rate pairs below it are in the region too.

## Main definitions

* `uvRelabel` — re-encoding of the two auxiliary alphabets of a five-tuple.
* `bcUVLetterKernel`, `bcUVLetterIndexLaw`, `bcUVTimeShare` — the letter laws of a code read as a
  Markov kernel from the letter index, the uniform law of that index, and the resulting mixture.

## Main statements

* `bcUVJointDistribution_isUVChannelLaw` — the letter-`i` law of a broadcast code is a channel
  law, so the letter laws of a code index the union.
* `bcUVTimeShare_uvInfo₁_ge` and its three companions — each information slot of the time-shared
  law dominates the average of the letter slots.
* `bc_uv_rate_sub_fanoSlack_mem_of_ceil_exp_le` — the rate pair of a code, shrunk by the Fano
  slack per letter, lies in the region.
* `bc_uv_logCard_mul_one_sub_errorProb_mem` — the same in the form the asymptotic argument
  consumes: each rate is discounted by the error probability of its receiver and by two bits per
  letter, which no longer refers to the message count of the other receiver.
* `bc_achievable_clamp_iff` — clamping a rate pair into the first quadrant leaves achievability
  unchanged, since both ceilings equal one at a nonpositive rate.
* `bc_uv_quadrant_mem_of_achievable` — an achievable rate pair with nonnegative coordinates lies
  in the region, obtained from the code points by letting the error tolerance and the per-letter
  residue vanish.
* `bc_capacity_subset_uv` — the operational capacity region lies in the UV outer region.

## Implementation notes

The asymptotic argument runs on `bc_uv_logCard_mul_one_sub_errorProb_mem` rather than on
`bc_uv_rate_sub_fanoSlack_mem_of_ceil_exp_le`:
the latter subtracts the sum of both Fano slacks from each coordinate, and a slack of the other
receiver is not controlled by the rate of this one, since the message counts of an achievable
pair are bounded from below only.  Discounting each rate by its own error probability removes
that coupling, and the residue is two bits per block whatever the message counts are.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]
variable {M₁ M₂ n : ℕ}

/-! ## The letter laws of a code are channel laws -/

section CodeLaw

variable [Nonempty β₁] [Nonempty β₂]

/-- @audit:ok -/
theorem bcUVJointDistribution_isUVChannelLaw
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    IsUVChannelLaw W (bcUVJointDistribution c W i) := by
  set U := Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂) with hU_def
  set V := Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂) with hV_def
  set G : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → U × V × α :=
    fun ω ↦ (uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i ω,
      uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i ω, c.encoder ω.1 i) with hG_def
  have hg : Measurable (fun r : U × V × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hGm : Measurable G :=
    (measurable_uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₂
        measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
      ((measurable_uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₁
          measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
        ((measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)))
  have hGupd : ∀ (m : Fin M₁ × Fin M₂) (y : Fin n → β₁ × β₂) (b : β₁ × β₂),
      G (m, Function.update y i b) = G (m, y) := by
    intro m y b
    have hpre : ∀ j : Fin i.val,
        bcConverseY₁s (M₁ := M₁) (M₂ := M₂) ⟨j.val, j.isLt.trans i.isLt⟩
            (m, Function.update y i b)
          = bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ (m, y) := fun j ↦
      congrArg Prod.fst
        (Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt j.isLt)) b y)
    have hsuf : ∀ j : {j : Fin n // i.val < j.val},
        bcConverseY₂s (M₁ := M₁) (M₂ := M₂) j.val (m, Function.update y i b)
          = bcConverseY₂s j.val (m, y) := fun j ↦
      congrArg Prod.snd
        (Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt j.2).symm) b y)
    have haux₂ : uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i (m, Function.update y i b)
        = uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i (m, y) :=
      Prod.ext rfl (Prod.ext (funext hpre) (funext hsuf))
    have haux₁ : uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i (m, Function.update y i b)
        = uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i (m, y) :=
      Prod.ext rfl (Prod.ext (funext hpre) (funext hsuf))
    exact Prod.ext (congrArg (uvPadMap i) haux₂)
      (Prod.ext (congrArg (uvPadMap i) haux₁) rfl)
  have hπ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have key := compProd_pi_map_pair_eq_of_update_invariant (bcConverseInput M₁ M₂) c.encoder W
    (bcConverseKernel c W) (fun m ↦ rfl) i G hGm hGupd (fun r : U × V × α ↦ r.2.2) hg
    (fun _ ↦ rfl)
  unfold IsUVChannelLaw bcUVJointDistribution
  rw [Measure.map_map hP (measurable_bcUVTuple c i),
    Measure.map_map hπ (measurable_bcUVTuple c i)]
  exact key

end CodeLaw

/-! ## Re-encoding the auxiliary alphabets -/

section AuxRelabel

variable {U V U' V' : Type*}
variable [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace U'] [MeasurableSpace V']

/-- Re-encoding of the two auxiliary alphabets of a five-tuple, leaving the input letter and the
two output letters alone. -/
def uvRelabel (e₁ : U → U') (e₂ : V → V') :
    U × V × α × β₁ × β₂ → U' × V' × α × β₁ × β₂ :=
  fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2)

lemma measurable_uvRelabel {e₁ : U → U'} {e₂ : V → V'} (he₁ : Measurable e₁)
    (he₂ : Measurable e₂) : Measurable (uvRelabel (α := α) (β₁ := β₁) (β₂ := β₂) e₁ e₂) :=
  (he₁.comp measurable_fst).prodMk
    ((he₂.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

lemma uvInfo₁_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₂ : V' → V} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₂ : Measurable d₂) (h₂ : ∀ v, d₂ (e₂ v) = v) :
    uvInfo₁ (ν.map (uvRelabel e₁ e₂)) = uvInfo₁ ν := by
  rw [uvInfo₁, uvInfo₁, mutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd) (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))]
  exact mutualInfo_eq_of_leftInverse ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp measurable_snd)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    he₂ hd₂ h₂

lemma uvInfo₂_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₁ : U' → U} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₁ : Measurable d₁) (h₁ : ∀ u, d₁ (e₁ u) = u) :
    uvInfo₂ (ν.map (uvRelabel e₁ e₂)) = uvInfo₂ ν := by
  rw [uvInfo₂, uvInfo₂, mutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.1) measurable_fst (fun q ↦ q.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))]
  exact mutualInfo_eq_of_leftInverse ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2) measurable_fst
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    he₁ hd₁ h₁

lemma uvInfoJoint_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂))
    {e₁ : U → U'} {e₂ : V → V'} (he₁ : Measurable e₁) (he₂ : Measurable e₂) :
    uvInfoJoint (ν.map (uvRelabel e₁ e₂)) = uvInfoJoint ν := by
  rw [uvInfoJoint, uvInfoJoint,
    mutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
      (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop)]
  rfl

section Sum

variable [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]
variable [Fintype U] [MeasurableSingletonClass U] [Fintype V] [MeasurableSingletonClass V]

omit [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]
  [Fintype V] [MeasurableSingletonClass V] in
lemma uvInfoSum₂_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₁ : U' → U} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₁ : Measurable d₁) (h₁ : ∀ u, d₁ (e₁ u) = u) :
    uvInfoSum₂ (ν.map (uvRelabel e₁ e₂)) = uvInfoSum₂ ν := by
  rw [uvInfoSum₂, uvInfoSum₂, uvInfo₂_map_uvRelabel ν he₁ he₂ hd₁ h₁]
  congr 1
  rw [condMutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun q ↦ q.1) measurable_fst]
  exact condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
    (fun q ↦ q.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    measurable_fst he₁ hd₁ h₁
    (mutualInfo_ne_top ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.1) measurable_fst
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

omit [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype U] [MeasurableSingletonClass U] in
lemma uvInfoSum₁_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₂ : V' → V} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₂ : Measurable d₂) (h₂ : ∀ v, d₂ (e₂ v) = v) :
    uvInfoSum₁ (ν.map (uvRelabel e₁ e₂)) = uvInfoSum₁ ν := by
  rw [uvInfoSum₁, uvInfoSum₁, uvInfo₁_map_uvRelabel ν he₁ he₂ hd₂ h₂]
  congr 1
  rw [condMutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (fun q ↦ q.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd)]
  exact condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
    (fun q ↦ q.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (measurable_fst.comp measurable_snd) he₂ hd₂ h₂
    (mutualInfo_ne_top ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2) (measurable_fst.comp measurable_snd)
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

end Sum

end AuxRelabel

/-! ## Time sharing -/

section TimeSharing

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/-! ### The time-shared five-tuple law -/

/-- The letter laws of a broadcast code, read as a Markov kernel from the letter index. -/
noncomputable def bcUVLetterKernel (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Kernel (Fin n) ((Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂) :=
  Kernel.ofFunOfCountable (bcUVJointDistribution c W)

/-- The uniform law of the letter index of a length-`n` block code. -/
noncomputable def bcUVLetterIndexLaw (n : ℕ) : Measure (Fin n) :=
  (Fintype.card (Fin n) : ℝ≥0∞)⁻¹ • Measure.count

instance bcUVLetterIndexLaw_isProbabilityMeasure [NeZero n] :
    IsProbabilityMeasure (bcUVLetterIndexLaw n) := by
  unfold bcUVLetterIndexLaw; infer_instance

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Fintype β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
lemma bcUVLetterKernel_apply (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    (i : Fin n) : bcUVLetterKernel c W i = bcUVJointDistribution c W i := rfl

instance bcUVLetterKernel_isMarkovKernel (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] :
    IsMarkovKernel (bcUVLetterKernel c W) := by
  refine ⟨fun i ↦ ?_⟩
  change IsProbabilityMeasure (bcUVJointDistribution c W i)
  infer_instance

/-- The time-shared five-tuple law of a broadcast code: the letter index is drawn uniformly and
the letter-`i` five-tuple is read off the ambient measure.  The letter index survives inside both
auxiliaries, which already carry it as their first component.
@audit:ok -/
noncomputable def bcUVTimeShare (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Measure ((Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂) :=
  ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W).map Prod.snd

instance bcUVTimeShare_isProbabilityMeasure (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    IsProbabilityMeasure (bcUVTimeShare c W) := by
  unfold bcUVTimeShare
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Fintype β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
lemma bcUVTimeShare_eq_sum (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    bcUVTimeShare c W = ∑ i : Fin n, (n : ℝ≥0∞)⁻¹ • bcUVJointDistribution c W i := by
  ext s hs
  rw [bcUVTimeShare, ← Measure.snd, Measure.snd_compProd,
    Measure.bind_apply hs (Kernel.aemeasurable _), bcUVLetterIndexLaw, lintegral_smul_measure,
    lintegral_count, tsum_fintype, smul_eq_mul, Fintype.card_fin, Measure.finsetSum_apply]
  simp [bcUVLetterKernel_apply, Finset.mul_sum]

omit [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] in
lemma bcUVTimeShare_isUVChannelLaw (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    IsUVChannelLaw W (bcUVTimeShare c W) := by
  have hne : ((n : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  haveI : ∀ i : Fin n, IsFiniteMeasure ((n : ℝ≥0∞)⁻¹ • bcUVJointDistribution c W i) := fun i ↦
    Measure.smul_finite _ hne
  rw [bcUVTimeShare_eq_sum]
  exact IsUVChannelLaw.finsetSum
    (fun i ↦ (bcUVJointDistribution_isUVChannelLaw c W i).smul _) Finset.univ

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [StandardBorelSpace β₂] in
lemma bcUVLetterKernel_ae_tag (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    ∀ᵐ p ∂((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W),
      p.2.1.1 = p.1 ∧ p.2.2.1.1 = p.1 := by
  rw [Measure.ae_compProd_iff (Set.toFinite _).measurableSet]
  filter_upwards with i
  rw [bcUVLetterKernel_apply, bcUVJointDistribution,
    ae_map_iff (measurable_bcUVTuple c i).aemeasurable (Set.toFinite _).measurableSet]
  filter_upwards with ω
  exact ⟨rfl, rfl⟩

/-! ### The four slots of the time-shared law dominate the letter averages -/

lemma lintegral_bcUVLetterIndexLaw [NeZero n] (F : Fin n → ℝ≥0∞) :
    ∫⁻ i, F i ∂(bcUVLetterIndexLaw n) = (n : ℝ≥0∞)⁻¹ * ∑ i, F i := by
  rw [bcUVLetterIndexLaw, lintegral_smul_measure, lintegral_count, tsum_fintype, smul_eq_mul,
    Fintype.card_fin]

omit [StandardBorelSpace α] [Nonempty α] in
lemma bcUVTimeShare_uvInfo₁_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i)
      ≤ uvInfo₁ (bcUVTimeShare c W) := by
  have hV : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hY₁ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  rw [uvInfo₁, bcUVTimeShare, mutualInfo_map_comp _ Prod.snd measurable_snd _ hV _ hY₁,
    mutualInfo_compProd_eq_add_lintegral _ _ hV hY₁ (tag := fun a ↦ a.1) measurable_fst
      (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.2),
    lintegral_bcUVLetterIndexLaw]
  simp only [uvInfo₁, bcUVLetterKernel_apply]
  exact le_add_self

omit [StandardBorelSpace α] [Nonempty α] in
lemma bcUVTimeShare_uvInfo₂_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i)
      ≤ uvInfo₂ (bcUVTimeShare c W) := by
  have hU : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hY₂ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  rw [uvInfo₂, bcUVTimeShare, mutualInfo_map_comp _ Prod.snd measurable_snd _ hU _ hY₂,
    mutualInfo_compProd_eq_add_lintegral _ _ hU hY₂ (tag := fun a ↦ a.1) measurable_fst
      (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.1),
    lintegral_bcUVLetterIndexLaw]
  simp only [uvInfo₂, bcUVLetterKernel_apply]
  exact le_add_self

lemma bcUVTimeShare_condMutualInfo₁_eq (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    condMutualInfo (bcUVTimeShare c W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, condMutualInfo (bcUVJointDistribution c W i)
          (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) := by
  have hne : ((n : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hX : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hY₁ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hU : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hmarg : (∫⁻ t, mutualInfo (bcUVLetterKernel c W t) (fun q ↦ q.1) (fun q ↦ q.2.2.2.1)
      ∂(bcUVLetterIndexLaw n)) ≠ ∞ := by
    rw [lintegral_bcUVLetterIndexLaw]
    exact ENNReal.mul_ne_top hne (ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ ↦
      lt_top_iff_ne_top.mpr (mutualInfo_ne_top _ _ _ hU hY₁)))
  have h1 := condMutualInfo_map_comp' ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W) Prod.snd
    measurable_snd (bcUVTimeShare c W) rfl (fun q ↦ q.2.2.1) hX (fun q ↦ q.2.2.2.1) hY₁
    (fun q ↦ q.1) hU
  have h2 := condMutualInfo_compProd_snd_eq_lintegral (bcUVLetterIndexLaw n)
    (bcUVLetterKernel c W) hX hY₁ hU (tag := fun a ↦ a.1) measurable_fst
    (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.1)
    (mutualInfo_ne_top _ _ _ measurable_fst (hY₁.comp measurable_snd)) hmarg
  rw [h1, h2, lintegral_bcUVLetterIndexLaw]
  simp only [bcUVLetterKernel_apply]

lemma bcUVTimeShare_condMutualInfo₂_eq (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    condMutualInfo (bcUVTimeShare c W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)
      = (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, condMutualInfo (bcUVJointDistribution c W i)
          (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1) := by
  have hne : ((n : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hX : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hY₂ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hV : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hmarg : (∫⁻ t, mutualInfo (bcUVLetterKernel c W t) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2)
      ∂(bcUVLetterIndexLaw n)) ≠ ∞ := by
    rw [lintegral_bcUVLetterIndexLaw]
    exact ENNReal.mul_ne_top hne (ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ ↦
      lt_top_iff_ne_top.mpr (mutualInfo_ne_top _ _ _ hV hY₂)))
  have h1 := condMutualInfo_map_comp' ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W) Prod.snd
    measurable_snd (bcUVTimeShare c W) rfl (fun q ↦ q.2.2.1) hX (fun q ↦ q.2.2.2.2) hY₂
    (fun q ↦ q.2.1) hV
  have h2 := condMutualInfo_compProd_snd_eq_lintegral (bcUVLetterIndexLaw n)
    (bcUVLetterKernel c W) hX hY₂ hV (tag := fun a ↦ a.1) measurable_fst
    (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.2)
    (mutualInfo_ne_top _ _ _ measurable_fst (hY₂.comp measurable_snd)) hmarg
  rw [h1, h2, lintegral_bcUVLetterIndexLaw]
  simp only [bcUVLetterKernel_apply]

lemma bcUVTimeShare_uvInfoSum₂_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i)
      ≤ uvInfoSum₂ (bcUVTimeShare c W) := by
  simp only [uvInfoSum₂]
  rw [Finset.sum_add_distrib, mul_add, bcUVTimeShare_condMutualInfo₁_eq]
  exact add_le_add (bcUVTimeShare_uvInfo₂_ge c W) le_rfl

lemma bcUVTimeShare_uvInfoSum₁_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i)
      ≤ uvInfoSum₁ (bcUVTimeShare c W) := by
  simp only [uvInfoSum₁]
  rw [Finset.sum_add_distrib, mul_add, bcUVTimeShare_condMutualInfo₂_eq]
  exact add_le_add (bcUVTimeShare_uvInfo₁_ge c W) le_rfl

/-! ### The shrunk rate point -/

/-- @audit:ok -/
lemma bc_uv_mem_of_mul_le_slot_sums
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) {r₁ r₂ : ℝ}
    (hb₁ : (n : ℝ) * r₁ ≤ (∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i)).toReal)
    (hb₂ : (n : ℝ) * r₂ ≤ (∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i)).toReal)
    (hb₃ : (n : ℝ) * (r₁ + r₂)
      ≤ (∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i)).toReal)
    (hb₄ : (n : ℝ) * (r₁ + r₂)
      ≤ (∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i)).toReal) :
    (r₁, r₂) ∈ bcOuterRegionUV W := by
  haveI : NeZero n := ⟨hn.ne'⟩
  -- re-encode the two auxiliary alphabets of the time-shared law into `ℕ`
  obtain ⟨e₁, hinj₁⟩ := exists_injective_nat (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂))
  obtain ⟨e₂, hinj₂⟩ := exists_injective_nat (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂))
  have hme₁ : Measurable e₁ := measurable_of_countable e₁
  have hme₂ : Measurable e₂ := measurable_of_countable e₂
  have hd₁ : ∀ u, Function.invFun e₁ (e₁ u) = u := Function.leftInverse_invFun hinj₁
  have hd₂ : ∀ v, Function.invFun e₂ (e₂ v) = v := Function.leftInverse_invFun hinj₂
  haveI : IsProbabilityMeasure ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) :=
    Measure.isProbabilityMeasure_map (measurable_uvRelabel hme₁ hme₂).aemeasurable
  have hchan : IsUVChannelLaw W ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) :=
    (bcUVTimeShare_isUVChannelLaw c W).map_auxiliaries hme₁ hme₂
  -- the four slots are unchanged by the re-encoding
  have hs₁ : uvInfo₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) = uvInfo₁ (bcUVTimeShare c W) :=
    uvInfo₁_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₂
  have hs₂ : uvInfo₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) = uvInfo₂ (bcUVTimeShare c W) :=
    uvInfo₂_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₁
  have hs₃ : uvInfoSum₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))
      = uvInfoSum₂ (bcUVTimeShare c W) :=
    uvInfoSum₂_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₁
  have hs₄ : uvInfoSum₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))
      = uvInfoSum₁ (bcUVTimeShare c W) :=
    uvInfoSum₁_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₂
  -- finiteness of the four slots of the time-shared law
  have hfin₁ : uvInfo₁ (bcUVTimeShare c W) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (measurable_fst.comp measurable_snd)
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hfin₂ : uvInfo₂ (bcUVTimeShare c W) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ measurable_fst
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hfin₃ : uvInfoSum₂ (bcUVTimeShare c W) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hfin₂, condMutualInfo_ne_top _ _ _ _
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_fst⟩
  have hfin₄ : uvInfoSum₁ (bcUVTimeShare c W) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hfin₁, condMutualInfo_ne_top _ _ _ _
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      (measurable_fst.comp measurable_snd)⟩
  -- the four bounds at the re-encoded time-shared law
  have g₁ : r₁ ≤ (uvInfo₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₁]; exact bcUVTimeShare_uvInfo₁_ge c W)
      (by rw [hs₁]; exact hfin₁) hb₁
  have g₂ : r₂ ≤ (uvInfo₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₂]; exact bcUVTimeShare_uvInfo₂_ge c W)
      (by rw [hs₂]; exact hfin₂) hb₂
  have g₃ : r₁ + r₂ ≤ (uvInfoSum₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₃]; exact bcUVTimeShare_uvInfoSum₂_ge c W)
      (by rw [hs₃]; exact hfin₃) hb₃
  have g₄ : r₁ + r₂ ≤ (uvInfoSum₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₄]; exact bcUVTimeShare_uvInfoSum₁_ge c W)
      (by rw [hs₄]; exact hfin₄) hb₄
  exact subset_closure (Set.mem_iUnion.mpr
    ⟨⟨(bcUVTimeShare c W).map (uvRelabel e₁ e₂), inferInstance⟩,
      Set.mem_iUnion.mpr ⟨hchan, g₁, g₂, g₃, g₄⟩⟩)

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- @audit:ok -/
lemma bcConverseFanoSlack₁_le [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) :
    bcConverseFanoSlack₁ c W
      ≤ Real.log 2 + (c.averageErrorProb₁ W).toReal * Real.log (M₁ : ℝ) := by
  have hM : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  have hlog : Real.log ((M₁ : ℝ) - 1) ≤ Real.log (M₁ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [bcConverseFanoSlack₁, bcConverse_errorProb₁_eq]
  exact add_le_add Real.binEntropy_le_log_two
    (mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg)

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- @audit:ok -/
lemma bcConverseFanoSlack₂_le [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₂ : 2 ≤ M₂) :
    bcConverseFanoSlack₂ c W
      ≤ Real.log 2 + (c.averageErrorProb₂ W).toReal * Real.log (M₂ : ℝ) := by
  have hM : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  have hlog : Real.log ((M₂ : ℝ) - 1) ≤ Real.log (M₂ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [bcConverseFanoSlack₂, bcConverse_errorProb₂_eq]
  exact add_le_add Real.binEntropy_le_log_two
    (mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg)

/-- @audit:ok -/
lemma bc_uv_converse_slots [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCOuterRegionUV (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i)).toReal + bcConverseFanoSlack₁ c W)
      ((∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i)).toReal + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i)).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i)).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
  have hext := bc_uv_converse_from_code c W hcard₁ hcard₂
  rwa [show (∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
        (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i))
      = ∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_mutualInfo_eq_uvInfo₁_at c W i,
    show (∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
        (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i))
      = ∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_mutualInfo_eq_uvInfo₂_at c W i,
    show (∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
          (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
        + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
          (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i)))
      = ∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_sum_eq_uvInfoSum₂_at c W i,
    show (∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
          (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
        + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
          (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i)))
      = ∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_sum_eq_uvInfoSum₁_at c W i] at hext

/-- The rate pair of a broadcast code, shrunk by the per-letter Fano slack, lies in the UV outer
region.  The letter index is absorbed into the auxiliaries, which already carry it, so the
average of the letter laws is again a channel law and dominates the per-letter averages of all
four information slots.
@audit:ok -/
theorem bc_uv_rate_sub_fanoSlack_mem_of_ceil_exp_le
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ}
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) :
    (R₁ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ),
      R₂ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  -- both Fano slacks are nonnegative, so shrinking by their sum only weakens the bounds
  have hF₁ : 0 ≤ bcConverseFanoSlack₁ c W := by
    unfold bcConverseFanoSlack₁
    exact add_nonneg (Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one)
      (mul_nonneg measureReal_nonneg (Real.log_nonneg (by linarith)))
  have hF₂ : 0 ≤ bcConverseFanoSlack₂ c W := by
    unfold bcConverseFanoSlack₂
    exact add_nonneg (Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one)
      (mul_nonneg measureReal_nonneg (Real.log_nonneg (by linarith)))
  -- the code-level converse, with the four per-letter sums identified as slot sums
  have hslot := bc_uv_converse_slots c W hcard₁ hcard₂
  have hr₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hr₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have hcorner : ∀ r : ℝ, (n : ℝ) * (r - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W)
      / (n : ℝ)) = (n : ℝ) * r - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
    intro r
    field_simp
  have hsumr : (n : ℝ) * ((R₁ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ))
        + (R₂ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ)))
      = (n : ℝ) * R₁ + (n : ℝ) * R₂
        - 2 * (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
    field_simp
    ring
  refine bc_uv_mem_of_mul_le_slot_sums c W hn ?_ ?_ ?_ ?_
  · rw [hcorner]; linarith [hslot.bound₁, hF₂]
  · rw [hcorner]; linarith [hslot.bound₂, hF₁]
  · rw [hsumr]; linarith [hslot.sumBound₂, hF₁, hF₂]
  · rw [hsumr]; linarith [hslot.sumBound₁, hF₁, hF₂]

/-- @audit:ok -/
lemma bc_uv_logCard_mul_one_sub_errorProb_mem [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    ((Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal) - 2 * Real.log 2) / (n : ℝ),
      (Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal) - 2 * Real.log 2) / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hslot := bc_uv_converse_slots c W hcard₁ hcard₂
  have hF₁ := bcConverseFanoSlack₁_le c W hcard₁
  have hF₂ := bcConverseFanoSlack₂_le c W hcard₂
  have hcancel : ∀ x : ℝ, (n : ℝ) * (x / (n : ℝ)) = x := fun x ↦ by field_simp
  have hcancel₂ : ∀ x y : ℝ, (n : ℝ) * (x / (n : ℝ) + y / (n : ℝ)) = x + y := by
    intro x y; field_simp
  have he₁ : Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal)
      = Real.log (M₁ : ℝ) - (c.averageErrorProb₁ W).toReal * Real.log (M₁ : ℝ) := by ring
  have he₂ : Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal)
      = Real.log (M₂ : ℝ) - (c.averageErrorProb₂ W).toReal * Real.log (M₂ : ℝ) := by ring
  refine bc_uv_mem_of_mul_le_slot_sums c W hn ?_ ?_ ?_ ?_
  · rw [hcancel, he₁]; linarith [hslot.bound₁]
  · rw [hcancel, he₂]; linarith [hslot.bound₂]
  · rw [hcancel₂, he₁, he₂]; linarith [hslot.sumBound₂]
  · rw [hcancel₂, he₁, he₂]; linarith [hslot.sumBound₁]

/-- @audit:ok -/
lemma bc_uv_rate_mem_of_mul_le_logCard [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {r₁ r₂ : ℝ}
    (h₁ : (n : ℝ) * r₁ ≤ Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal))
    (h₂ : (n : ℝ) * r₂ ≤ Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal)) :
    (r₁ - 2 * Real.log 2 / (n : ℝ), r₂ - 2 * Real.log 2 / (n : ℝ)) ∈ bcOuterRegionUV W := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine bcOuterRegionUV_isLowerSet W (Prod.mk_le_mk.mpr ⟨?_, ?_⟩)
    (bc_uv_logCard_mul_one_sub_errorProb_mem c W hn hcard₁ hcard₂)
  · have hd : r₁ ≤ Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal) / (n : ℝ) := by
      rw [le_div_iff₀ hn']; linarith [h₁]
    rw [sub_div]
    linarith
  · have hd : r₂ ≤ Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal) / (n : ℝ) := by
      rw [le_div_iff₀ hn']; linarith [h₂]
    rw [sub_div]
    linarith

end TimeSharing

/-! ## The operational region lies in the UV outer region -/

section Operational

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁] [Fintype β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- Clamping a rate pair into the first quadrant leaves achievability unchanged: at a nonpositive
rate the message count `⌈exp (n * R)⌉` a code is asked to carry is one, the same value it takes at
rate zero.
@audit:ok -/
lemma bc_achievable_clamp_iff (W : BCChannel α β₁ β₂) (R₁ R₂ : ℝ) :
    BCAchievable W R₁ R₂ ↔ BCAchievable W (max R₁ 0) (max R₂ 0) := by
  have key : ∀ (R : ℝ) (n : ℕ),
      Nat.ceil (Real.exp ((n : ℝ) * max R 0)) = Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    intro R n
    by_cases hR : 0 ≤ R
    · rw [max_eq_left hR]
    · replace hR : R < 0 := not_le.mp hR
      rw [max_eq_right hR.le, mul_zero, Real.exp_zero, Nat.ceil_one]
      symm
      refine le_antisymm (Nat.ceil_le.mpr ?_) (Nat.ceil_pos.mpr (Real.exp_pos _))
      rw [Nat.cast_one, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR.le)
  constructor
  · intro h ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
    exact ⟨M₁, M₂, by rw [key R₁ n]; exact hM₁, by rw [key R₂ n]; exact hM₂, c, hc⟩
  · intro h ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
    exact ⟨M₁, M₂, by rw [← key R₁ n]; exact hM₁, by rw [← key R₂ n]; exact hM₂, c, hc⟩

/-- @audit:ok -/
lemma bc_uv_rate_mul_one_sub_mem_of_errorProb_le (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (hn : 0 < n) {R₁ R₂ ε : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hε1 : ε ≤ 1)
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
    (he₁ : (c.averageErrorProb₁ W).toReal ≤ ε) (he₂ : (c.averageErrorProb₂ W).toReal ≤ ε) :
    (R₁ * (1 - ε) - 2 * Real.log 2 / (n : ℝ), R₂ * (1 - ε) - 2 * Real.log 2 / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlogM₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have h1M₁ : 1 ≤ M₁ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₁
  have h1M₂ : 1 ≤ M₂ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₂
  have hnR₁ : (0 : ℝ) ≤ (n : ℝ) * R₁ := mul_nonneg hn'.le hR₁
  have hnR₂ : (0 : ℝ) ≤ (n : ℝ) * R₂ := mul_nonneg hn'.le hR₂
  have hprod₁ : (n : ℝ) * (R₁ * (1 - ε))
      ≤ Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal) := by
    rw [← mul_assoc]
    exact mul_le_mul hlogM₁ (by linarith) (by linarith) (hnR₁.trans hlogM₁)
  have hprod₂ : (n : ℝ) * (R₂ * (1 - ε))
      ≤ Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal) := by
    rw [← mul_assoc]
    exact mul_le_mul hlogM₂ (by linarith) (by linarith) (hnR₂.trans hlogM₂)
  -- a padded receiver contributes nothing: its rate is zero and its Fano slack is one bit
  have hpad : ∀ {K₁ K₂ : ℕ} (d : BroadcastCode K₁ K₂ n α β₁ β₂), (2 : ℕ) ≤ K₁ →
      (0 : ℝ) ≤ Real.log ((2 : ℕ) : ℝ) * (1 - (d.averageErrorProb₁ W).toReal) := by
    intro K₁ K₂ d _
    have hle : (d.averageErrorProb₁ W).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (d.averageErrorProb₁_le_one W)
    rw [hcast2]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by linarith)
  have hpad' : ∀ {K₁ K₂ : ℕ} (d : BroadcastCode K₁ K₂ n α β₁ β₂), (2 : ℕ) ≤ K₂ →
      (0 : ℝ) ≤ Real.log ((2 : ℕ) : ℝ) * (1 - (d.averageErrorProb₂ W).toReal) := by
    intro K₁ K₂ d _
    have hle : (d.averageErrorProb₂ W).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (d.averageErrorProb₂_le_one W)
    rw [hcast2]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by linarith)
  rcases eq_or_lt_of_le h1M₁ with h1 | h1
  · -- receiver 1 carries a single message, so its rate is zero and the code needs padding
    subst h1
    have hR₁z : R₁ = 0 := by
      rw [Nat.cast_one, Real.log_one] at hlogM₁
      have : R₁ ≤ 0 := by nlinarith
      linarith
    rcases eq_or_lt_of_le h1M₂ with h2 | h2
    · subst h2
      have hR₂z : R₂ = 0 := by
        rw [Nat.cast_one, Real.log_one] at hlogM₂
        have : R₂ ≤ 0 := by nlinarith
        linarith
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      refine bc_uv_rate_mem_of_mul_le_logCard (c.padFirst.padSecond) W hn le_rfl le_rfl ?_ ?_
      · rw [hR₁z, zero_mul, mul_zero]
        exact hpad _ le_rfl
      · rw [hR₂z, zero_mul, mul_zero]
        exact hpad' _ le_rfl
    · haveI : NeZero M₂ := ⟨by omega⟩
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      refine bc_uv_rate_mem_of_mul_le_logCard c.padFirst W hn le_rfl (by omega) ?_ ?_
      · rw [hR₁z, zero_mul, mul_zero]
        exact hpad _ le_rfl
      · rw [BroadcastCode.averageErrorProb₂_padFirst]
        exact hprod₂
  · rcases eq_or_lt_of_le h1M₂ with h2 | h2
    · subst h2
      have hR₂z : R₂ = 0 := by
        rw [Nat.cast_one, Real.log_one] at hlogM₂
        have : R₂ ≤ 0 := by nlinarith
        linarith
      haveI : NeZero M₁ := ⟨by omega⟩
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      refine bc_uv_rate_mem_of_mul_le_logCard c.padSecond W hn (by omega) le_rfl ?_ ?_
      · rw [BroadcastCode.averageErrorProb₁_padSecond]
        exact hprod₁
      · rw [hR₂z, zero_mul, mul_zero]
        exact hpad' _ le_rfl
    · haveI : NeZero M₁ := ⟨by omega⟩
      haveI : NeZero M₂ := ⟨by omega⟩
      exact bc_uv_rate_mem_of_mul_le_logCard c W hn (by omega) (by omega) hprod₁ hprod₂

/-- An achievable rate pair with nonnegative coordinates lies in the UV outer region.  For every
error tolerance and every block length the pair, discounted by the error probability of each
receiver and by two bits per letter, is a point of the region; those points converge to the pair
itself as the tolerance shrinks and the block length grows, and the region is closed.
@audit:ok -/
lemma bc_uv_quadrant_mem_of_achievable (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hach : BCAchievable W R₁ R₂) :
    (R₁, R₂) ∈ bcOuterRegionUV W := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ η : ℝ, 0 < η → (R₁ - η, R₂ - η) ∈ bcOuterRegionUV W := by
    intro η hη
    have hden : (0 : ℝ) < 2 * (R₁ + R₂ + 1) := by linarith
    set ε := min (1 / 2) (η / (2 * (R₁ + R₂ + 1))) with hεdef
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hεle : ε ≤ η / (2 * (R₁ + R₂ + 1)) := min_le_right _ _
    obtain ⟨N, hN⟩ := hach ε hε0
    obtain ⟨n, hnge⟩ := exists_nat_ge (max (max (N : ℝ) 1) (4 * Real.log 2 / η))
    have hnN : N ≤ n := by
      exact_mod_cast ((le_max_left (N : ℝ) 1).trans (le_max_left _ _)).trans hnge
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := ((le_max_right (N : ℝ) 1).trans (le_max_left _ _)).trans hnge
    have hn : 0 < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    have hn' : (0 : ℝ) < (n : ℝ) := by linarith
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc₁, hc₂⟩ := hN n hnN
    -- the error term and the two-bit term are each at most half the target slack
    have hA : R₁ * ε ≤ η / 2 := by
      have hεD : ε * (2 * (R₁ + R₂ + 1)) ≤ η := (le_div_iff₀ hden).mp hεle
      nlinarith [mul_nonneg hε0.le hR₂, hε0.le]
    have hA' : R₂ * ε ≤ η / 2 := by
      have hεD : ε * (2 * (R₁ + R₂ + 1)) ≤ η := (le_div_iff₀ hden).mp hεle
      nlinarith [mul_nonneg hε0.le hR₁, hε0.le]
    have hB : 2 * Real.log 2 / (n : ℝ) ≤ η / 2 := by
      have h4 : 4 * Real.log 2 / η ≤ (n : ℝ) := (le_max_right _ _).trans hnge
      rw [div_le_iff₀ hη] at h4
      rw [div_le_div_iff₀ hn' (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hmem := bc_uv_rate_mul_one_sub_mem_of_errorProb_le W c hn hR₁ hR₂ hε1 hM₁ hM₂ hc₁.le hc₂.le
    refine bcOuterRegionUV_isLowerSet W (Prod.mk_le_mk.mpr ⟨?_, ?_⟩) hmem
    · have : R₁ * (1 - ε) = R₁ - R₁ * ε := by ring
      rw [this]; linarith
    · have : R₂ * (1 - ε) = R₂ - R₂ * ε := by ring
      rw [this]; linarith
  have ht : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Filter.Tendsto (fun k : ℕ ↦ R₁ - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds R₁) := by
    simpa using tendsto_const_nhds.sub ht
  have h2 : Filter.Tendsto (fun k : ℕ ↦ R₂ - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds R₂) := by
    simpa using tendsto_const_nhds.sub ht
  exact (bcOuterRegionUV_isClosed W).mem_of_tendsto (h1.prodMk_nhds h2)
    (Filter.Eventually.of_forall fun k ↦ key _ (by positivity))

/-- The operational capacity region of a broadcast channel is contained in the UV (Nair–El Gamal)
outer region.  Together with `marton_region_subset_capacity` this places the capacity region
between Marton's inner bound and the UV outer bound as subsets of the plane.

Nonpositive rates are covered without a sign hypothesis: clamping a rate pair into the first
quadrant leaves achievability unchanged, and the outer region is a lower set, so the clamped pair
carries the original one.
@audit:ok -/
@[entry_point]
theorem bc_capacity_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcCapacityRegion W ⊆ bcOuterRegionUV W := by
  rw [bcCapacityRegion]
  refine (bcOuterRegionUV_isClosed W).closure_subset_iff.mpr fun p hp ↦ ?_
  have hmem : (max p.1 0, max p.2 0) ∈ bcOuterRegionUV W :=
    bc_uv_quadrant_mem_of_achievable W (le_max_right _ _) (le_max_right _ _)
      ((bc_achievable_clamp_iff W p.1 p.2).mp hp)
  exact bcOuterRegionUV_isLowerSet W ⟨le_max_left _ _, le_max_left _ _⟩ hmem

end Operational

end InformationTheory.Shannon.BroadcastChannel

