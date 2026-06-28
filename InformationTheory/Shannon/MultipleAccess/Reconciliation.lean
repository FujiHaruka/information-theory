import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Achievability
import InformationTheory.Shannon.MultipleAccess.Basic
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.Pi

/-!
# Multiple access channel — converse/achievability reconciliation bridge

Under the independent product input `p₁ ⊗ p₂`, the achievability rate quantities
`macInfo₁` / `macInfo₂` / `macInfoBoth` (entropy differences, `ℝ`-valued) of
`InformationTheory.Shannon.MultipleAccess.Achievability` coincide with the converse
information quantities (`condMutualInfo` / `mutualInfo`, `klDiv`-based, `ℝ≥0∞`-valued)
taken on the per-coordinate joint law `macJointDistribution p₁ p₂ W`:

* `macInfo₁ = (I(X₁; Y | X₂))` ,
* `macInfo₂ = (I(X₂; Y | X₁))` ,
* `macInfoBoth = (I((X₁, X₂); Y))` .

The crux is that the input coordinates `X₁`, `X₂` are independent under `p₁ ⊗ p₂`, so the
chain rule `I(X₁; (X₂, Y)) = I(X₁; Y | X₂)` (and its user-2 mirror) closes the gap between
the achievability corner informations and the textbook conditional informations of the
MAC capacity region.

## Main statements

* `macInfo₁_eq_condMutualInfo_toReal` / `macInfo₂_eq_condMutualInfo_toReal` /
  `macInfoBoth_eq_mutualInfo_toReal` — the three corner-information equivalences.
* `mac_capacity_region_reconciliation` — the achievability-region predicate equals the
  converse-region predicate after substituting the three equivalences.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

/-- Generic entropy-form expression of the `klDiv` mutual information, lifting the
`Prod.fst`/`Prod.snd` bridge `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` to an
arbitrary pair of finite-alphabet random variables. -/
lemma mutualInfo_toReal_eq_entropy_form
    {Ω : Type*} [MeasurableSpace Ω]
    {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (g : Ω → B) (hf : Measurable f) (hg : Measurable g) :
    (mutualInfo μ f g).toReal
      = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω)) := by
  classical
  have hh : Measurable (fun ω ↦ (f ω, g ω)) := hf.prodMk hg
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (f ω, g ω))) :=
    Measure.isProbabilityMeasure_map hh.aemeasurable
  have hfst : (μ.map (fun ω ↦ (f ω, g ω))).map Prod.fst = μ.map f := by
    rw [Measure.map_map measurable_fst hh]; rfl
  have hsnd : (μ.map (fun ω ↦ (f ω, g ω))).map Prod.snd = μ.map g := by
    rw [Measure.map_map measurable_snd hh]; rfl
  have hMI : mutualInfo (μ.map (fun ω ↦ (f ω, g ω))) Prod.fst Prod.snd = mutualInfo μ f g := by
    unfold mutualInfo
    have e_joint :
        (μ.map (fun ω ↦ (f ω, g ω))).map (fun z : A × B ↦ (Prod.fst z, Prod.snd z))
          = μ.map (fun ω ↦ (f ω, g ω)) := by
      rw [show (fun z : A × B ↦ (Prod.fst z, Prod.snd z)) = (id : A × B → A × B) from by
            funext z; rfl, Measure.map_id]
    rw [e_joint, hfst, hsnd]
  have hEf : entropy (μ.map (fun ω ↦ (f ω, g ω))) Prod.fst = entropy μ f := by
    unfold entropy; rw [hfst]
  have hEg : entropy (μ.map (fun ω ↦ (f ω, g ω))) Prod.snd = entropy μ g := by
    unfold entropy; rw [hsnd]
  have hEid : entropy (μ.map (fun ω ↦ (f ω, g ω))) id = entropy μ (fun ω ↦ (f ω, g ω)) := by
    unfold entropy; rw [Measure.map_id]
  calc (mutualInfo μ f g).toReal
      = (mutualInfo (μ.map (fun ω ↦ (f ω, g ω))) Prod.fst Prod.snd).toReal := by rw [hMI]
    _ = entropy (μ.map (fun ω ↦ (f ω, g ω))) Prod.fst
          + entropy (μ.map (fun ω ↦ (f ω, g ω))) Prod.snd
          - entropy (μ.map (fun ω ↦ (f ω, g ω))) id :=
        mutualInfo_eq_entropy_add_entropy_sub_jointEntropy (μ.map (fun ω ↦ (f ω, g ω)))
    _ = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω)) := by rw [hEf, hEg, hEid]

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [StandardBorelSpace α₁] [StandardBorelSpace α₂] [StandardBorelSpace β] in
/-- The two input coordinates are independent under the product input `p₁ ⊗ p₂`, hence
their mutual information vanishes.
@audit:ok -/
lemma macJoint_mutualInfo_X1_X2_eq_zero
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    mutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ q.2.1) = 0 := by
  have hX2meas : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  rw [mutualInfo_eq_zero_iff_indep (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ q.2.1)
        measurable_fst hX2meas,
      indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable hX2meas.aemeasurable,
      macJointDistribution_map_fst p₁ p₂ W, macJointDistribution_map_X2 p₁ p₂ W]
  -- Goal: (macJointDistribution p₁ p₂ W).map (fun q ↦ (q.1, q.2.1)) = p₁.prod p₂.
  unfold macJointDistribution
  have hpairmeas : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk hX2meas
  rw [Measure.map_map hpairmeas MeasurableEquiv.prodAssoc.measurable]
  have hcomp : (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) ∘ (MeasurableEquiv.prodAssoc :
      (α₁ × α₂) × β ≃ᵐ α₁ × α₂ × β) = Prod.fst := by
    funext r; rfl
  rw [hcomp]
  show (jointDistribution (p₁.prod p₂) W).fst = p₁.prod p₂
  rw [jointDistribution_def]
  exact Measure.fst_compProd _ _

omit [StandardBorelSpace α₁] [StandardBorelSpace α₂] [StandardBorelSpace β] in
/-- Achievability user-1 corner information equals the joint mutual information
`I(X₁; (X₂, Y))` on the per-coordinate joint law. -/
lemma macInfo₁_eq_mutualInfo_toReal
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfo₁ p₁ p₂ W
      = (mutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ (q.2.1, q.2.2))).toReal := by
  rw [mutualInfo_toReal_eq_entropy_form (macJointDistribution p₁ p₂ W) Prod.fst
        (fun q ↦ (q.2.1, q.2.2)) measurable_fst
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))]
  rfl

omit [StandardBorelSpace α₁] [StandardBorelSpace α₂] [StandardBorelSpace β] in
/-- Achievability user-2 corner information equals the joint mutual information
`I(X₂; (X₁, Y))` on the per-coordinate joint law. -/
lemma macInfo₂_eq_mutualInfo_toReal
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfo₂ p₁ p₂ W
      = (mutualInfo (macJointDistribution p₁ p₂ W)
          (fun q ↦ q.2.1) (fun q ↦ (q.1, q.2.2))).toReal := by
  rw [mutualInfo_toReal_eq_entropy_form (macJointDistribution p₁ p₂ W)
        (fun q ↦ q.2.1) (fun q ↦ (q.1, q.2.2)) (measurable_fst.comp measurable_snd)
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))]
  unfold macInfo₂
  -- The two entropy marginals already agree; reconcile the joint-entropy term with
  -- `entropy J id` via the coordinate permutation `(x₂, (x₁, y)) ↦ (x₁, x₂, y)`.
  have hXsmeas : Measurable (fun q : α₁ × α₂ × β ↦ (q.2.1, (q.1, q.2.2))) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  let e : α₂ × (α₁ × β) ≃ᵐ α₁ × α₂ × β :=
    { toFun := fun p ↦ (p.2.1, p.1, p.2.2)
      invFun := fun q ↦ (q.2.1, q.1, q.2.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun :=
        (measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      measurable_invFun :=
        (measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) }
  have hreshape :
      entropy (macJointDistribution p₁ p₂ W) (id : α₁ × α₂ × β → α₁ × α₂ × β)
        = entropy (macJointDistribution p₁ p₂ W)
            (fun q : α₁ × α₂ × β ↦ (q.2.1, (q.1, q.2.2))) := by
    have h := entropy_measurableEquiv_comp (macJointDistribution p₁ p₂ W)
      (fun q : α₁ × α₂ × β ↦ (q.2.1, (q.1, q.2.2))) hXsmeas e
    rwa [show (fun q : α₁ × α₂ × β ↦ e (q.2.1, (q.1, q.2.2))) = id from by funext q; rfl] at h
  rw [hreshape]

omit [StandardBorelSpace α₂] in
/-- Chain rule under input independence (user 1):
`I(X₁; (X₂, Y)) = I(X₁; Y | X₂)`. -/
lemma macJoint_mutualInfo_eq_condMutualInfo₁
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    mutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ (q.2.1, q.2.2))
      = condMutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ q.2.2)
          (fun q ↦ q.2.1) := by
  have hX1 : Measurable (Prod.fst : α₁ × α₂ × β → α₁) := measurable_fst
  have hX2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  rw [mutualInfo_comm (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ (q.2.1, q.2.2))
        hX1 (hX2.prodMk hY),
      mutualInfo_chain_rule (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2) Prod.fst
        (fun q ↦ q.2.1) hY hX1 hX2,
      mutualInfo_comm (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) Prod.fst hX2 hX1,
      macJoint_mutualInfo_X1_X2_eq_zero p₁ p₂ W, zero_add]
  exact condMutualInfo_comm (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2) Prod.fst
    (fun q ↦ q.2.1) hY hX1 hX2

omit [StandardBorelSpace α₁] in
/-- Chain rule under input independence (user 2):
`I(X₂; (X₁, Y)) = I(X₂; Y | X₁)`. -/
lemma macJoint_mutualInfo_eq_condMutualInfo₂
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    mutualInfo (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) (fun q ↦ (q.1, q.2.2))
      = condMutualInfo (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) (fun q ↦ q.2.2)
          Prod.fst := by
  have hX1 : Measurable (Prod.fst : α₁ × α₂ × β → α₁) := measurable_fst
  have hX2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  rw [mutualInfo_comm (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) (fun q ↦ (q.1, q.2.2))
        hX2 (hX1.prodMk hY),
      mutualInfo_chain_rule (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        Prod.fst hY hX2 hX1,
      macJoint_mutualInfo_X1_X2_eq_zero p₁ p₂ W, zero_add]
  exact condMutualInfo_comm (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2) (fun q ↦ q.2.1)
    Prod.fst hY hX2 hX1

omit [StandardBorelSpace α₂] in
/-- **MAC reconciliation, user-1 corner.**  Under the independent product input
`p₁ ⊗ p₂`, the achievability corner information `macInfo₁` equals the textbook conditional
mutual information `I(X₁; Y | X₂)` of the converse, taken on the per-coordinate joint law
`macJointDistribution p₁ p₂ W`.
@audit:ok -/
@[entry_point]
theorem macInfo₁_eq_condMutualInfo_toReal
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfo₁ p₁ p₂ W
      = (condMutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ q.2.2)
          (fun q ↦ q.2.1)).toReal := by
  rw [macInfo₁_eq_mutualInfo_toReal p₁ p₂ W, macJoint_mutualInfo_eq_condMutualInfo₁ p₁ p₂ W]

omit [StandardBorelSpace α₁] in
/-- **MAC reconciliation, user-2 corner.**  Under the independent product input
`p₁ ⊗ p₂`, the achievability corner information `macInfo₂` equals the textbook conditional
mutual information `I(X₂; Y | X₁)` of the converse.
@audit:ok -/
@[entry_point]
theorem macInfo₂_eq_condMutualInfo_toReal
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfo₂ p₁ p₂ W
      = (condMutualInfo (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) (fun q ↦ q.2.2)
          Prod.fst).toReal := by
  rw [macInfo₂_eq_mutualInfo_toReal p₁ p₂ W, macJoint_mutualInfo_eq_condMutualInfo₂ p₁ p₂ W]

omit [StandardBorelSpace α₁] [StandardBorelSpace α₂] [StandardBorelSpace β] in
/-- **MAC reconciliation, sum corner.**  The achievability sum-corner information
`macInfoBoth` equals the joint mutual information `I((X₁, X₂); Y)` of the converse, taken
on the per-coordinate joint law `macJointDistribution p₁ p₂ W`.
@audit:ok -/
@[entry_point]
theorem macInfoBoth_eq_mutualInfo_toReal
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfoBoth p₁ p₂ W
      = (mutualInfo (macJointDistribution p₁ p₂ W)
          (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)).toReal := by
  rw [mutualInfo_toReal_eq_entropy_form (macJointDistribution p₁ p₂ W)
        (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
        (measurable_snd.comp measurable_snd)]
  unfold macInfoBoth
  -- Reconcile the joint-entropy term with `entropy J id` via `prodAssoc`.
  have hXsmeas : Measurable (fun q : α₁ × α₂ × β ↦ ((q.1, q.2.1), q.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hreshape :
      entropy (macJointDistribution p₁ p₂ W) (id : α₁ × α₂ × β → α₁ × α₂ × β)
        = entropy (macJointDistribution p₁ p₂ W)
            (fun q : α₁ × α₂ × β ↦ ((q.1, q.2.1), q.2.2)) := by
    have h := entropy_measurableEquiv_comp (macJointDistribution p₁ p₂ W)
      (fun q : α₁ × α₂ × β ↦ ((q.1, q.2.1), q.2.2)) hXsmeas
      (MeasurableEquiv.prodAssoc : (α₁ × α₂) × β ≃ᵐ α₁ × α₂ × β)
    rwa [show (fun q : α₁ × α₂ × β ↦
            (MeasurableEquiv.prodAssoc ((q.1, q.2.1), q.2.2) : α₁ × α₂ × β)) = id from by
          funext q; rfl] at h
  rw [hreshape]

/-- **MAC capacity-region reconciliation.**  Under the independent product input
`p₁ ⊗ p₂`, a rate pair lies in the achievability region (with corner informations
`macInfo₁` / `macInfo₂` / `macInfoBoth`) iff it lies in the converse region (with the
textbook conditional/joint informations `I(X₁; Y | X₂)` / `I(X₂; Y | X₁)` /
`I((X₁, X₂); Y)` on `macJointDistribution p₁ p₂ W`).

Substantive (non-vacuous) iff: the LHS `macInfo₁/₂/Both` (entropy-difference `ℝ`
values) and the RHS `condMutualInfo`/`mutualInfo .toReal` (`klDiv`-based) are
syntactically distinct quantities — the iff is closed only via the three genuine
corner-information equivalences, not by a definitional `P ↔ P`.
@audit:ok -/
@[entry_point]
theorem mac_capacity_region_reconciliation
    (R₁ R₂ : ℝ)
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    InMACCapacityRegion R₁ R₂ (macInfo₁ p₁ p₂ W) (macInfo₂ p₁ p₂ W) (macInfoBoth p₁ p₂ W)
      ↔ InMACCapacityRegion R₁ R₂
          (condMutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ q.2.2)
            (fun q ↦ q.2.1)).toReal
          (condMutualInfo (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) (fun q ↦ q.2.2)
            Prod.fst).toReal
          (mutualInfo (macJointDistribution p₁ p₂ W)
            (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)).toReal := by
  rw [macInfo₁_eq_condMutualInfo_toReal p₁ p₂ W, macInfo₂_eq_condMutualInfo_toReal p₁ p₂ W,
    macInfoBoth_eq_mutualInfo_toReal p₁ p₂ W]

end InformationTheory.Shannon.MAC
