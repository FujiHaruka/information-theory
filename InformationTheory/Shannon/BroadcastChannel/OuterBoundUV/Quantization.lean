import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import InformationTheory.Shannon.MaxEntropy.Basic

/-!
# Broadcast channel — truncating the countable auxiliary of the UV outer region

The UV outer region is indexed by five-tuple laws whose two auxiliaries range over `ℕ`, while an
inner bound reads its auxiliary off a finite alphabet.  Truncating the first auxiliary at a level
`m`, folding every letter at or above `m` into a single one, moves a law of the outer region onto
the finite alphabet `Fin (m + 1)`, and the two slots the truncated auxiliary appears in move in
opposite directions.

The conditional slot `I(X; Y₁ ∣ U)` can only grow: the truncated auxiliary is a function of the
original one, and a channel law makes the auxiliary reach the first output through the input
letter only, so the extra conditioning the original auxiliary would supply is already spent.  The
corner slot `I(U; Y₂)` can shrink, by exactly the information the original auxiliary still carries
once the truncated one is known.  That information lives on the fibers of the truncation, all but
one of which pin the auxiliary to a single letter, so it is carried by the tail alone and the
finite output alphabet caps it by `log |β₂|`.

## Main definitions

* `uvQuantize m` — the truncating quantizer of the countable auxiliary.
* `uvQuantizeLaw ν m` — the five-tuple law with its first auxiliary truncated at level `m`.
* `uvQuantizeSlack ν m` — the tail mass of the auxiliary times `log |β₂|`.

## Main statements

* `uvQuantizeLaw_isUVChannelLaw` — truncating the auxiliary keeps a channel law a channel law.
* `uvInfo₂_le_uvQuantizeLaw` and `uvInfoSum₂_le_uvQuantizeLaw` — the receiver-2 corner slot and
  the sum-rate slot lose at most the slack under the truncation.
* `tendsto_uvQuantizeSlack` — the slack vanishes as the truncation level grows.
* `uvInfo₂_ne_top` and `uvInfoSum₂_ne_top` — the two slots are finite even over a countable
  auxiliary, which is what lets the estimates be read in the reals.
* `mutualInfo_ne_top_of_right` and `mutualInfo_le_ofReal_log_card` — a finite alphabet on one
  side alone bounds the mutual information, which is what the countable auxiliary needs.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal Topology

universe u

/-! ### Mutual information against a finite alphabet -/

section FiniteRange

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
variable {B : Type*} [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem mutualInfo_ne_top_of_right (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≠ ∞ :=
  ne_top_of_le_ne_top (mutualInfo_ne_top μ Yo Yo hYo hYo)
    (mutualInfo_le_of_markov μ Xs Yo Yo hXs hYo hYo
      (isMarkovChain_comp_conditioner_right μ Xs Yo hXs hYo measurable_id))

theorem mutualInfo_le_ofReal_log_card (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≤ ENNReal.ofReal (Real.log (Fintype.card B)) := by
  have htoReal : (mutualInfo μ Xs Yo).toReal ≤ Real.log (Fintype.card B) := by
    rw [mutualInfo_comm μ Xs Yo hXs hYo, mutualInfo_eq_entropy_sub_condEntropy μ Yo Xs hYo hXs]
    have hnn : 0 ≤ InformationTheory.MeasureFano.condEntropy μ Yo Xs := condEntropy_nonneg μ Yo Xs
    have hcard : entropy μ Yo ≤ Real.log (Fintype.card B) :=
      InformationTheory.Shannon.MaxEntropy.entropy_le_log_card μ Yo hYo
    linarith
  calc mutualInfo μ Xs Yo = ENNReal.ofReal (mutualInfo μ Xs Yo).toReal :=
        (ENNReal.ofReal_toReal (mutualInfo_ne_top_of_right μ Xs Yo hXs hYo)).symm
    _ ≤ ENNReal.ofReal (Real.log (Fintype.card B)) := ENNReal.ofReal_le_ofReal htoReal

omit [StandardBorelSpace A] [Nonempty A] [Fintype B] [Nonempty B]
  [MeasurableSingletonClass B] in
theorem mutualInfo_eq_zero_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (hYo : Measurable Yo) (c : A) (hc : Xs =ᵐ[μ] fun _ ↦ c) :
    mutualInfo μ Xs Yo = 0 := by
  rw [mutualInfo_congr_ae μ Yo hc]
  exact (mutualInfo_eq_zero_iff_indep μ (fun _ ↦ c) Yo measurable_const hYo).2
    (indepFun_const_left c Yo)

end FiniteRange

variable {α : Type u} {β₁ β₂ : Type*}
variable [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Finiteness of the slots over a countable auxiliary -/

section Finiteness

variable {U V : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
variable [MeasurableSpace V]

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [Fintype β₁] [Nonempty β₁]
  [MeasurableSingletonClass β₁] in
theorem uvInfo₂_ne_top (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] :
    uvInfo₂ ν ≠ ∞ :=
  mutualInfo_ne_top_of_right ν _ _ (by fun_prop) (by fun_prop)

theorem uvInfoSum₂_ne_top (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν] :
    uvInfoSum₂ ν ≠ ∞ := by
  have hjoint : mutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.2.1))
      (fun q ↦ q.2.2.2.1) ≠ ∞ := mutualInfo_ne_top_of_right ν _ _ (by fun_prop) (by fun_prop)
  rw [mutualInfo_chain_rule ν (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
    (fun q ↦ q.1) (by fun_prop) (by fun_prop) (by fun_prop)] at hjoint
  exact ENNReal.add_ne_top.mpr ⟨uvInfo₂_ne_top ν, (ENNReal.add_ne_top.mp hjoint).2⟩

end Finiteness

/-! ### Coarsening the conditioner of the sum-rate slot -/

section Coarsen

variable {U V : Type*} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
variable [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]

theorem IsUVChannelLaw.condMutualInfo_le_map_cond {U' : Type*} [MeasurableSpace U']
    [StandardBorelSpace U'] [Nonempty U'] {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    {f : U → U'} (hf : Measurable f) :
    condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      ≤ condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ f q.1) := by
  have hfq : Measurable (fun q : U × V × α × β₁ × β₂ ↦ f q.1) := hf.comp measurable_fst
  have hpair : Measurable (fun u : U ↦ (f u, u)) := hf.prodMk measurable_id
  have hfinX : mutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) ≠ ∞ :=
    mutualInfo_ne_top_of_right ν _ _ (by fun_prop) (by fun_prop)
  have hfinUm : mutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ f q.1) (fun q ↦ q.2.2.2.1) ≠ ∞ :=
    mutualInfo_ne_top_of_right ν _ _ hfq (by fun_prop)
  have hfinU : mutualInfo ν (fun q : U × V × α × β₁ × β₂ ↦ q.1) (fun q ↦ q.2.2.2.1) ≠ ∞ :=
    mutualInfo_ne_top_of_right ν _ _ (by fun_prop) (by fun_prop)
  -- the channel law's Markov chain, post-processed, kills `I((U', U); Y₁ ∣ X)`.
  have hzero : condMutualInfo ν (fun q ↦ (f q.1, q.1)) (fun q ↦ q.2.2.2.1)
      (fun q ↦ q.2.2.1) = 0 :=
    condMutualInfo_eq_zero_of_markov ν _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
      (isMarkovChain_map_left ν (fun q ↦ q.1) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
        (by fun_prop) (by fun_prop) (by fun_prop) (f := fun u ↦ (f u, u)) hpair
        h.isMarkovChain_U_X_Y₁)
  have hsplitX := condMutualInfo_chain_rule_X_2var ν (fun q : U × V × α × β₁ × β₂ ↦ f q.1)
    (fun q ↦ q.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.2.2.1) hfq (by fun_prop) (by fun_prop)
    (by fun_prop) hfinX
  rw [hzero] at hsplitX
  have hv : condMutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ (q.2.2.1, f q.1)) = 0 := (add_eq_zero.mp hsplitX.symm).2
  have hv' : condMutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ (f q.1, q.2.2.1)) = 0 := by
    rw [← hv]
    exact condMutualInfo_map_cond_measurableEquiv ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ (q.2.2.1, f q.1)) (by fun_prop) (by fun_prop) (by fun_prop)
      MeasurableEquiv.prodComm
  -- the two orders of the conditional chain rule at the coarsened conditioner.
  have h1 := condMutualInfo_chain_rule_X_2var ν (fun q : U × V × α × β₁ × β₂ ↦ q.1)
    (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ f q.1) (by fun_prop) (by fun_prop)
    (by fun_prop) hfq hfinUm
  have h3 := condMutualInfo_chain_rule_X_2var ν (fun q : U × V × α × β₁ × β₂ ↦ q.2.2.1)
    (fun q ↦ q.1) (fun q ↦ q.2.2.2.1) (fun q ↦ f q.1) (by fun_prop) (by fun_prop)
    (by fun_prop) hfq hfinUm
  have h4 : condMutualInfo ν (fun q ↦ (q.2.2.1, q.1)) (fun q ↦ q.2.2.2.1) (fun q ↦ f q.1)
      = condMutualInfo ν (fun q ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.1) (fun q ↦ f q.1) :=
    condMutualInfo_map_left_measurableEquiv ν (fun q ↦ (q.1, q.2.2.1)) (fun q ↦ q.2.2.2.1)
      (fun q ↦ f q.1) (by fun_prop) (by fun_prop) hfq MeasurableEquiv.prodComm
  have h2 : condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ (f q.1, q.1))
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) :=
    condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
      (fun q ↦ q.1) (by fun_prop) (by fun_prop) (by fun_prop)
      (f := fun u ↦ (f u, u)) (g := Prod.snd) hpair measurable_snd (fun _ ↦ rfl) hfinU
  rw [h2] at h1
  rw [hv', add_zero, h4, h1] at h3
  exact h3 ▸ le_add_self

end Coarsen

/-! ### The truncating quantizer -/

/-- The truncating quantizer of the countable auxiliary: letters below the truncation level are
kept and every letter at or above it is folded into the top one. -/
def uvQuantize (m : ℕ) (k : ℕ) : ULift.{u} (Fin (m + 1)) := ULift.up ⟨min k m, by omega⟩

lemma measurable_uvQuantize (m : ℕ) : Measurable (uvQuantize.{u} m) := measurable_of_countable _

lemma uvQuantize_down_eq_iff (m k : ℕ) : ((uvQuantize.{u} m k).down : ℕ) = m ↔ m ≤ k := by
  simp only [uvQuantize]
  omega

/-- The five-tuple law with its first auxiliary truncated at level `m`. -/
noncomputable def uvQuantizeLaw (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) (m : ℕ) :
    Measure (ULift.{u} (Fin (m + 1)) × ℕ × α × β₁ × β₂) :=
  ν.map (uvRelabel (uvQuantize.{u} m) id)

/-- The information the truncation can cost: the tail mass of the auxiliary times the largest
entropy the second output alphabet can carry. -/
noncomputable def uvQuantizeSlack (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) (m : ℕ) : ℝ≥0∞ :=
  ν {q | m ≤ q.1} * ENNReal.ofReal (Real.log (Fintype.card β₂))

instance isProbabilityMeasure_uvQuantizeLaw (ν : Measure (ℕ × ℕ × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (m : ℕ) : IsProbabilityMeasure (uvQuantizeLaw.{u} ν m) :=
  Measure.isProbabilityMeasure_map
    (measurable_uvRelabel (measurable_uvQuantize.{u} m) measurable_id).aemeasurable

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [Fintype β₁] [Nonempty β₁]
  [MeasurableSingletonClass β₁] [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂] in
theorem uvQuantizeLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) (m : ℕ) :
    IsUVChannelLaw W (uvQuantizeLaw.{u} ν m) :=
  h.map_auxiliaries (measurable_uvQuantize.{u} m) measurable_id

/-! ### The slots of the truncated law -/

section Slots

variable (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν] (m : ℕ)

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [Fintype β₁] [Nonempty β₁]
  [MeasurableSingletonClass β₁] [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂]
  [IsProbabilityMeasure ν] in
theorem uvInfo₂_uvQuantizeLaw :
    uvInfo₂ (uvQuantizeLaw.{u} ν m)
      = mutualInfo ν (fun q ↦ uvQuantize.{u} m q.1) (fun q ↦ q.2.2.2.2) :=
  mutualInfo_map_comp ν (uvRelabel (uvQuantize.{u} m) id)
    (measurable_uvRelabel (measurable_uvQuantize.{u} m) measurable_id)
    (fun q ↦ q.1) measurable_fst (fun q ↦ q.2.2.2.2) (by fun_prop)

omit [Fintype β₂] [Nonempty β₂] [MeasurableSingletonClass β₂] in
theorem condMutualInfo_uvQuantizeLaw :
    condMutualInfo (uvQuantizeLaw.{u} ν m) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
          (fun q ↦ uvQuantize.{u} m q.1) :=
  condMutualInfo_map_comp ν (uvRelabel (uvQuantize.{u} m) id)
    (measurable_uvRelabel (measurable_uvQuantize.{u} m) measurable_id)
    (fun q ↦ q.2.2.1) (by fun_prop) (fun q ↦ q.2.2.2.1) (by fun_prop) (fun q ↦ q.1)
    measurable_fst

end Slots

/-! ### The tail estimate for the corner slot -/

section Tail

variable (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν] (m : ℕ)

theorem ae_ae_uvQuantize_eq_fst :
    ∀ᵐ t ∂(ν.map fun q ↦ uvQuantize.{u} m q.1),
      ∀ᵐ q ∂(condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν t), uvQuantize.{u} m q.1 = t := by
  haveI : IsProbabilityMeasure (ν.map fun q ↦ uvQuantize.{u} m q.1) :=
    Measure.isProbabilityMeasure_map
      ((measurable_uvQuantize.{u} m).comp measurable_fst).aemeasurable
  refine Measure.ae_ae_of_ae_compProd
    (p := fun p : ULift.{u} (Fin (m + 1)) × (ℕ × ℕ × α × β₁ × β₂) ↦
      uvQuantize.{u} m p.2.1 = p.1) ?_
  rw [compProd_map_condDistrib (Y := id) aemeasurable_id]
  refine (ae_map_iff ?_ ?_).2 (Filter.Eventually.of_forall fun q ↦ rfl)
  · exact (((measurable_uvQuantize.{u} m).comp measurable_fst).prodMk
      measurable_id).aemeasurable
  · exact measurableSet_eq_fun (measurable_of_countable _) measurable_fst

theorem lintegral_mutualInfo_condDistrib_le :
    ∫⁻ t, mutualInfo (condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν t)
        (fun q ↦ q.1) (fun q ↦ q.2.2.2.2) ∂(ν.map fun q ↦ uvQuantize.{u} m q.1)
      ≤ uvQuantizeSlack ν m := by
  have hqm : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ uvQuantize.{u} m q.1) :=
    (measurable_uvQuantize.{u} m).comp measurable_fst
  haveI : IsProbabilityMeasure (ν.map fun q ↦ uvQuantize.{u} m q.1) :=
    Measure.isProbabilityMeasure_map hqm.aemeasurable
  set S : Set (ULift.{u} (Fin (m + 1))) := {t | (t.down : ℕ) = m} with hSdef
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.log (Fintype.card β₂)) with hcdef
  have hbound : ∀ᵐ t ∂(ν.map fun q ↦ uvQuantize.{u} m q.1),
      mutualInfo (condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν t) (fun q ↦ q.1)
          (fun q ↦ q.2.2.2.2) ≤ S.indicator (fun _ ↦ c) t := by
    filter_upwards [ae_ae_uvQuantize_eq_fst ν m] with t hfib
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      exact mutualInfo_le_ofReal_log_card _ _ _ (by fun_prop) (by fun_prop)
    · have hlt : (t.down : ℕ) < m :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp t.down.isLt) (by simpa [hSdef] using ht)
      rw [Set.indicator_of_notMem ht]
      refine le_of_eq (mutualInfo_eq_zero_of_ae_const _ _ _ (by fun_prop) (t.down : ℕ) ?_)
      filter_upwards [hfib] with q hq
      have hmin : min q.1 m = (t.down : ℕ) := congrArg (fun x ↦ (x.down : ℕ)) hq
      omega
  calc ∫⁻ t, mutualInfo (condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν t) (fun q ↦ q.1)
          (fun q ↦ q.2.2.2.2) ∂(ν.map fun q ↦ uvQuantize.{u} m q.1)
      ≤ ∫⁻ t, S.indicator (fun _ ↦ c) t ∂(ν.map fun q ↦ uvQuantize.{u} m q.1) :=
        lintegral_mono_ae hbound
    _ = c * (ν.map fun q ↦ uvQuantize.{u} m q.1) S :=
        lintegral_indicator_const (MeasurableSet.of_discrete (s := S)) c
    _ = uvQuantizeSlack ν m := by
        have hmapS : (ν.map fun q ↦ uvQuantize.{u} m q.1) S = ν {q | m ≤ q.1} := by
          rw [Measure.map_apply hqm (MeasurableSet.of_discrete (s := S))]
          refine congrArg ν (Set.ext fun q ↦ ?_)
          simpa [hSdef] using uvQuantize_down_eq_iff.{u} m q.1
        rw [hmapS, uvQuantizeSlack, mul_comm]

theorem mutualInfo_le_mutualInfo_uvQuantize_add_slack :
    mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)
      ≤ mutualInfo ν (fun q ↦ uvQuantize.{u} m q.1) (fun q ↦ q.2.2.2.2)
        + uvQuantizeSlack ν m := by
  have hqm : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ uvQuantize.{u} m q.1) :=
    (measurable_uvQuantize.{u} m).comp measurable_fst
  have hT : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (uvQuantize.{u} m q.1, q)) :=
    hqm.prodMk measurable_id
  haveI : IsProbabilityMeasure (ν.map fun q ↦ uvQuantize.{u} m q.1) :=
    Measure.isProbabilityMeasure_map hqm.aemeasurable
  have hcp : (ν.map fun q ↦ uvQuantize.{u} m q.1) ⊗ₘ
      condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν
      = ν.map (fun q ↦ (uvQuantize.{u} m q.1, q)) := compProd_map_condDistrib aemeasurable_id
  have hrec : ∀ᵐ p ∂((ν.map fun q ↦ uvQuantize.{u} m q.1) ⊗ₘ
        condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν), uvQuantize.{u} m p.2.1 = p.1 := by
    rw [hcp]
    refine (ae_map_iff hT.aemeasurable ?_).2 (Filter.Eventually.of_forall fun q ↦ rfl)
    exact measurableSet_eq_fun (measurable_of_countable _) measurable_fst
  have hsplit := mutualInfo_compProd_eq_add_lintegral
    (ν.map fun q ↦ uvQuantize.{u} m q.1) (condDistrib id (fun q ↦ uvQuantize.{u} m q.1) ν)
    (f := fun q : ℕ × ℕ × α × β₁ × β₂ ↦ q.1) (g := fun q : ℕ × ℕ × α × β₁ × β₂ ↦ q.2.2.2.2)
    (by fun_prop) (by fun_prop) (measurable_uvQuantize.{u} m) hrec
  have hL : mutualInfo (ν.map fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (uvQuantize.{u} m q.1, q))
      (fun p ↦ p.2.1) (fun p ↦ p.2.2.2.2.2)
      = mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2) :=
    mutualInfo_map_comp ν _ hT _ (by fun_prop) _ (by fun_prop)
  have hR : mutualInfo (ν.map fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (uvQuantize.{u} m q.1, q))
      Prod.fst (fun p ↦ p.2.2.2.2.2)
      = mutualInfo ν (fun q ↦ uvQuantize.{u} m q.1) (fun q ↦ q.2.2.2.2) :=
    mutualInfo_map_comp ν _ hT _ (by fun_prop) _ (by fun_prop)
  rw [hcp, hL, hR] at hsplit
  rw [hsplit]
  exact add_le_add le_rfl (lintegral_mutualInfo_condDistrib_le ν m)

end Tail

/-! ### The truncation estimates at the level of the slots -/

theorem uvInfo₂_le_uvQuantizeLaw (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    (m : ℕ) : uvInfo₂ ν ≤ uvInfo₂ (uvQuantizeLaw.{u} ν m) + uvQuantizeSlack ν m := by
  rw [uvInfo₂_uvQuantizeLaw ν m]
  exact mutualInfo_le_mutualInfo_uvQuantize_add_slack ν m

theorem uvInfoSum₂_le_uvQuantizeLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [IsProbabilityMeasure ν] (h : IsUVChannelLaw W ν)
    (m : ℕ) : uvInfoSum₂ ν ≤ uvInfoSum₂ (uvQuantizeLaw.{u} ν m) + uvQuantizeSlack ν m := by
  simp only [uvInfoSum₂, condMutualInfo_uvQuantizeLaw ν m]
  calc uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      ≤ uvInfo₂ (uvQuantizeLaw.{u} ν m) + uvQuantizeSlack ν m
        + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
            (fun q ↦ uvQuantize.{u} m q.1) :=
        add_le_add (uvInfo₂_le_uvQuantizeLaw ν m)
          (h.condMutualInfo_le_map_cond (measurable_uvQuantize.{u} m))
    _ = uvInfo₂ (uvQuantizeLaw.{u} ν m)
          + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
              (fun q ↦ uvQuantize.{u} m q.1) + uvQuantizeSlack ν m := by ring

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] [Fintype β₁] [Nonempty β₁]
  [MeasurableSingletonClass β₁] [Nonempty β₂] [MeasurableSingletonClass β₂] in
theorem tendsto_uvQuantizeSlack (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν] :
    Tendsto (uvQuantizeSlack ν) atTop (𝓝 0) := by
  have hmeas : ∀ m : ℕ, MeasurableSet {q : ℕ × ℕ × α × β₁ × β₂ | m ≤ q.1} := fun m ↦
    measurable_fst (MeasurableSet.of_discrete (s := {n : ℕ | m ≤ n}))
  have hanti : Antitone (fun m : ℕ ↦ {q : ℕ × ℕ × α × β₁ × β₂ | m ≤ q.1}) :=
    fun i j hij q hq ↦ le_trans hij hq
  have hinter : (⋂ m : ℕ, {q : ℕ × ℕ × α × β₁ × β₂ | m ≤ q.1}) = ∅ := by
    ext q
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hq
    exact absurd (hq (q.1 + 1)) (by omega)
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop (μ := ν)
    (fun m ↦ (hmeas m).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  have hmul := ENNReal.Tendsto.mul_const
    (b := ENNReal.ofReal (Real.log (Fintype.card β₂))) hlim (Or.inr ENNReal.ofReal_ne_top)
  rw [zero_mul] at hmul
  exact hmul

end InformationTheory.Shannon.BroadcastChannel
