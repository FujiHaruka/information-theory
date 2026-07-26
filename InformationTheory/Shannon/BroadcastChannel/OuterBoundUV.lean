import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.ConverseGateway
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Gateway
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMIChainRule
import InformationTheory.Shannon.Entropy
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessMarkov
import InformationTheory.Shannon.Pi

/-!
# General broadcast channel — the UV outer bound (Nair–El Gamal)

Single-letterization of the four information inequalities of the Nair–El Gamal outer bound
for a general (not necessarily degraded) two-receiver broadcast channel, El Gamal–Kim
Ch. 8. The bound reads

```
R₁ ≤ I(V; Y₁),                R₂ ≤ I(U; Y₂),
R₁ + R₂ ≤ I(U; Y₂) + I(X; Y₁ | U),
R₁ + R₂ ≤ I(V; Y₁) + I(X; Y₂ | V).
```

Both auxiliaries carry the *same* time structure `uvAux`, the receiver-1 output prefix
together with the receiver-2 output suffix, and differ only in the message component:
`Uᵢ = (W₂, Y₁^{<i}, Y₂^{>i})` and `Vᵢ = (W₁, Y₁^{<i}, Y₂^{>i})`.

The two corner bounds are pure chain-rule plumbing and carry no structural hypothesis at
all. The two sum bounds consume the Csiszár sum identity with a background conditioner
(`csiszar_sum_identity_cond`) together with a memoryless precondition on the channel — the
same `h_memo` bundle that the degraded converse takes. Unlike the degraded converse, no
degradedness hypothesis appears: the conditioner swap that degradedness performed there is
replaced here by the Csiszár identity, which is why the auxiliaries mix a prefix of one
output with a suffix of the other.

## Main statements

* `bc_uv_singleletterize_r1` / `bc_uv_singleletterize_r2` — the two corner bounds.
* `bc_uv_singleletterize_sum₂` / `bc_uv_singleletterize_sum₁` — the two sum bounds.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ}

/-- The auxiliary variable of the UV outer bound at letter `i`: a message together with the
receiver-1 output prefix `Y₁^{<i}` and the receiver-2 output suffix `Y₂^{>i}`. Both
auxiliaries of the bound have this shape and differ only in the message they carry —
`Uᵢ = uvAux W₂ …` for the receiver-2 corner, `Vᵢ = uvAux W₁ …` for the receiver-1 one. -/
def uvAux {ξ β₁ β₂ : Type*}
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂) (i : Fin n) :
    Ω → ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
  fun ω ↦ (W ω,
    (fun j ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω,
     fun j ↦ Y₂s j.val ω))

section Aux

variable {ξ : Type*} [MeasurableSpace ξ]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]

lemma measurable_uvAux
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW : Measurable W) (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (i : Fin n) :
    Measurable (uvAux W Y₁s Y₂s i) :=
  hW.prodMk ((measurable_pi_iff.mpr fun _ ↦ hY₁s _).prodMk
    (measurable_pi_iff.mpr fun _ ↦ hY₂s _))

end Aux

section CornerBounds

variable {ξ : Type*} [Fintype ξ] [MeasurableSpace ξ] [MeasurableSingletonClass ξ]
  [StandardBorelSpace ξ] [Nonempty ξ]
variable {β₁ : Type*} [Fintype β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Nonempty β₁]
variable {β₂ : Type*} [Fintype β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] [Nonempty β₂]

omit [Fintype ξ] [MeasurableSingletonClass ξ] [Fintype β₂] [MeasurableSingletonClass β₂] in
theorem bc_uv_singleletterize_r1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW₁ : Measurable W₁) (hY₁s : ∀ i, Measurable (Y₁s i))
    (hY₂s : ∀ i, Measurable (Y₂s i)) :
    mutualInfo μ W₁ (fun ω j ↦ Y₁s j ω)
      ≤ ∑ i : Fin n, mutualInfo μ (uvAux W₁ Y₁s Y₂s i) (Y₁s i) := by
  classical
  rw [mutualInfo_chain_rule_Y_fin' μ W₁ Y₁s hW₁ hY₁s]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hpre₁ : Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₁s _
  have hsuf₂ : Measurable
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₂s _
  have ha : condMutualInfo μ W₁ (Y₁s i)
        (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      ≤ mutualInfo μ
          (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W₁ ω))
          (Y₁s i) := by
    rw [mutualInfo_chain_rule μ W₁ (Y₁s i)
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) hW₁ (hY₁s i) hpre₁]
    exact le_add_self
  have hb : mutualInfo μ
        (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W₁ ω))
        (Y₁s i)
      ≤ mutualInfo μ
          (fun ω ↦
            (((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W₁ ω),
              fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
          (Y₁s i) := by
    rw [mutualInfo_chain_rule μ
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
      (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W₁ ω))
      hsuf₂ (hY₁s i) (hpre₁.prodMk hW₁)]
    exact le_self_add
  refine (ha.trans hb).trans_eq ?_
  let e : ((Fin i.val → β₁) × ξ) × ({j : Fin n // i.val < j.val} → β₂)
        ≃ᵐ ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
    { toFun := fun x ↦ (x.1.2, (x.1.1, x.2))
      invFun := fun y ↦ ((y.2.1, y.1), y.2.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := (measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      measurable_invFun := ((measurable_fst.comp measurable_snd).prodMk measurable_fst).prodMk
        (measurable_snd.comp measurable_snd) }
  exact (mutualInfo_map_left_measurableEquiv μ
    (fun ω ↦
      (((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W₁ ω),
        fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
    (Y₁s i) ((hpre₁.prodMk hW₁).prodMk hsuf₂) (hY₁s i) e).symm

omit [Fintype ξ] [MeasurableSingletonClass ξ] [Fintype β₁] [MeasurableSingletonClass β₁] in
theorem bc_uv_singleletterize_r2
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW₂ : Measurable W₂) (hY₁s : ∀ i, Measurable (Y₁s i))
    (hY₂s : ∀ i, Measurable (Y₂s i)) :
    mutualInfo μ W₂ (fun ω j ↦ Y₂s j ω)
      ≤ ∑ i : Fin n, mutualInfo μ (uvAux W₂ Y₁s Y₂s i) (Y₂s i) := by
  classical
  rw [mutualInfo_chain_rule_Y_fin_suffix μ W₂ Y₂s hW₂ hY₂s]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hpre₁ : Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₁s _
  have hsuf₂ : Measurable
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₂s _
  have ha : condMutualInfo μ W₂ (Y₂s i)
        (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω)
      ≤ mutualInfo μ
          (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W₂ ω))
          (Y₂s i) := by
    rw [mutualInfo_chain_rule μ W₂ (Y₂s i)
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) hW₂ (hY₂s i) hsuf₂]
    exact le_add_self
  have hb : mutualInfo μ
        (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W₂ ω))
        (Y₂s i)
      ≤ mutualInfo μ
          (fun ω ↦
            (((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W₂ ω),
              fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
          (Y₂s i) := by
    rw [mutualInfo_chain_rule μ
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
      (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W₂ ω))
      hpre₁ (hY₂s i) (hsuf₂.prodMk hW₂)]
    exact le_self_add
  refine (ha.trans hb).trans_eq ?_
  let e : (({j : Fin n // i.val < j.val} → β₂) × ξ) × (Fin i.val → β₁)
        ≃ᵐ ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
    { toFun := fun x ↦ (x.1.2, (x.2, x.1.1))
      invFun := fun y ↦ ((y.2.2, y.1), y.2.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := (measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
      measurable_invFun := ((measurable_snd.comp measurable_snd).prodMk measurable_fst).prodMk
        (measurable_fst.comp measurable_snd) }
  exact (mutualInfo_map_left_measurableEquiv μ
    (fun ω ↦
      (((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W₂ ω),
        fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    (Y₂s i) ((hsuf₂.prodMk hW₂).prodMk hpre₁) (hY₂s i) e).symm

end CornerBounds

section SumBounds

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α] [Nonempty α]
variable {ξ : Type*} [Fintype ξ] [MeasurableSpace ξ] [MeasurableSingletonClass ξ]
  [StandardBorelSpace ξ] [Nonempty ξ]
variable {β₁ : Type*} [Fintype β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Nonempty β₁]
variable {β₂ : Type*} [Fintype β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] [Nonempty β₂]
variable {ζ : Type*} [Fintype ζ] [MeasurableSpace ζ] [MeasurableSingletonClass ζ]
  [StandardBorelSpace ζ] [Nonempty ζ]

omit [Fintype ξ] [MeasurableSingletonClass ξ] [StandardBorelSpace ξ] [Nonempty ξ]
  [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂] in
private lemma condMutualInfo_pi_collapse_of_markov
    {υ : Type*} [Fintype υ] [MeasurableSpace υ] [MeasurableSingletonClass υ]
    [StandardBorelSpace υ] [Nonempty υ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Yo : Ω → υ) (Zc : Ω → ζ) (i : Fin n)
    (hXs : ∀ j, Measurable (Xs j)) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (hmkv : IsMarkovChain μ
      (fun ω ↦ (Zc ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)) (Xs i) Yo) :
    condMutualInfo μ (fun ω j ↦ Xs j ω) Yo Zc = condMutualInfo μ (Xs i) Yo Zc := by
  classical
  have hXpi : Measurable (fun ω j ↦ Xs j ω) := measurable_pi_iff.mpr hXs
  have hrest : Measurable
      (fun ω ↦ (Zc ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)) :=
    hZc.prodMk (measurable_pi_iff.mpr fun j ↦ hXs j.val)
  -- `Yo ⫫ (Zc, X^{≠i}) | Xᵢ`, and its projection `Yo ⫫ Zc | Xᵢ`.
  have hswap := isMarkovChain_swap μ _ (Xs i) Yo hrest (hXs i) hYo hmkv
  have hZmkv : IsMarkovChain μ Zc (Xs i) Yo :=
    isMarkovChain_map_left μ _ (Xs i) Yo hrest (hXs i) hYo measurable_fst hmkv
  have hZswap := isMarkovChain_swap μ Zc (Xs i) Yo hZc (hXs i) hYo hZmkv
  have hdrop_full := condEntropy_drop_irrelevant_of_markov μ Yo (Xs i)
    (fun ω ↦ (Zc ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω))
    hYo (hXs i) hrest hswap
  have hdrop_Z := condEntropy_drop_irrelevant_of_markov μ Yo (Xs i) Zc
    hYo (hXs i) hZc hZswap
  -- Split `Xⁿ ↔ (Xᵢ, X^{≠i})` and regroup the conditioner.
  let eX : (Fin n → α) ≃ᵐ α × ({j : Fin n // j ≠ i} → α) :=
    ChannelCodingConverseGeneral.measurableEquivExtract (β := α) i
  have hext : (fun ω ↦ eX.symm (Xs i ω,
      fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)) = fun ω j ↦ Xs j ω := by
    funext ω j
    by_cases hj : j = i
    · subst hj
      simp [eX, ChannelCodingConverseGeneral.measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr]
    · simp [eX, ChannelCodingConverseGeneral.measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, hj]
  let E : α × (ζ × ({j : Fin n // j ≠ i} → α)) ≃ᵐ ζ × (Fin n → α) :=
    { toFun := fun x ↦ (x.2.1, eX.symm (x.1, x.2.2))
      invFun := fun y ↦ ((eX y.2).1, (y.1, (eX y.2).2))
      left_inv := fun x ↦ by simp
      right_inv := fun y ↦ by simp
      measurable_toFun := (measurable_fst.comp measurable_snd).prodMk
        (eX.symm.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      measurable_invFun :=
        ((measurable_fst.comp eX.measurable).comp measurable_snd).prodMk
          (measurable_fst.prodMk ((measurable_snd.comp eX.measurable).comp measurable_snd)) }
  have hreshape : InformationTheory.MeasureFano.condEntropy μ Yo
        (fun ω ↦ (Zc ω, fun j ↦ Xs j ω))
      = InformationTheory.MeasureFano.condEntropy μ Yo (Xs i) := by
    have hmeas : Measurable (fun ω ↦ (Xs i ω,
        (Zc ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω))) :=
      (hXs i).prodMk hrest
    have h := condEntropy_measurableEquiv_comp μ Yo hYo
      (fun ω ↦ (Xs i ω, (Zc ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)))
      hmeas E
    have hfun : (fun ω ↦ E (Xs i ω,
          (Zc ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)))
        = fun ω ↦ (Zc ω, fun j ↦ Xs j ω) := by
      funext ω
      exact Prod.ext rfl (congrFun hext ω)
    rw [hfun] at h
    rw [h, hdrop_full]
  have hreshapeZ : InformationTheory.MeasureFano.condEntropy μ Yo
        (fun ω ↦ (Zc ω, Xs i ω))
      = InformationTheory.MeasureFano.condEntropy μ Yo (Xs i) := by
    have h := condEntropy_measurableEquiv_comp μ Yo hYo
      (fun ω ↦ (Zc ω, Xs i ω)) (hZc.prodMk (hXs i)) MeasurableEquiv.prodComm
    rw [show (fun ω ↦ (MeasurableEquiv.prodComm (Zc ω, Xs i ω)))
        = (fun ω ↦ (Xs i ω, Zc ω)) from rfl] at h
    rw [← h, hdrop_Z]
  -- Both conditional mutual informations equal `H(Yo | Zc) − H(Yo | Xᵢ)`.
  have hL : (condMutualInfo μ (fun ω j ↦ Xs j ω) Yo Zc).toReal
      = InformationTheory.MeasureFano.condEntropy μ Yo Zc
        - InformationTheory.MeasureFano.condEntropy μ Yo (Xs i) := by
    rw [condMutualInfo_comm μ (fun ω j ↦ Xs j ω) Yo Zc hXpi hYo hZc,
      condMutualInfo_eq_condEntropy_sub_condEntropy μ Yo Zc (fun ω j ↦ Xs j ω)
        hYo hZc hXpi, hreshape]
  have hR : (condMutualInfo μ (Xs i) Yo Zc).toReal
      = InformationTheory.MeasureFano.condEntropy μ Yo Zc
        - InformationTheory.MeasureFano.condEntropy μ Yo (Xs i) := by
    rw [condMutualInfo_comm μ (Xs i) Yo Zc (hXs i) hYo hZc,
      condMutualInfo_eq_condEntropy_sub_condEntropy μ Yo Zc (Xs i) hYo hZc (hXs i),
      hreshapeZ]
  have hLfin : condMutualInfo μ (fun ω j ↦ Xs j ω) Yo Zc ≠ ∞ :=
    condMutualInfo_ne_top μ _ Yo Zc hXpi hYo hZc
  have hRfin : condMutualInfo μ (Xs i) Yo Zc ≠ ∞ :=
    condMutualInfo_ne_top μ (Xs i) Yo Zc (hXs i) hYo hZc
  exact (ENNReal.toReal_eq_toReal_iff' hLfin hRfin).mp (hL.trans hR.symm)

omit [Fintype ξ] [MeasurableSingletonClass ξ] [Fintype β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSingletonClass β₂] in
private lemma uvAux_absorbs_receiver2_terms
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂) (i : Fin n)
    (hW : Measurable W) (hY₁s : ∀ j, Measurable (Y₁s j))
    (hY₂s : ∀ j, Measurable (Y₂s j)) :
    condMutualInfo μ W (Y₂s i)
        (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω)
      + condMutualInfo μ
          (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
          (fun ω ↦ (W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
      ≤ mutualInfo μ (uvAux W Y₁s Y₂s i) (Y₂s i) := by
  classical
  have hpre₁ : Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₁s _
  have hsuf₂ : Measurable
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₂s _
  have h3 : condMutualInfo μ
        (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
        (fun ω ↦ (W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
      = condMutualInfo μ
          (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
          (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W ω)) := by
    have h := condMutualInfo_map_cond_measurableEquiv μ
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
      (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W ω))
      hpre₁ (hY₂s i) (hsuf₂.prodMk hW) MeasurableEquiv.prodComm
    exact h
  have h1 := mutualInfo_chain_rule μ W (Y₂s i)
    (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) hW (hY₂s i) hsuf₂
  have h2 := mutualInfo_chain_rule μ
    (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
    (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W ω))
    hpre₁ (hY₂s i) (hsuf₂.prodMk hW)
  have hkey : condMutualInfo μ W (Y₂s i)
        (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω)
      + condMutualInfo μ
          (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
          (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W ω))
      ≤ mutualInfo μ
          (fun ω ↦
            (((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W ω),
              fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
          (Y₂s i) := by
    rw [h2, h1, add_assoc]
    exact le_add_self
  rw [h3]
  refine hkey.trans_eq ?_
  let e : (({j : Fin n // i.val < j.val} → β₂) × ξ) × (Fin i.val → β₁)
        ≃ᵐ ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
    { toFun := fun x ↦ (x.1.2, (x.2, x.1.1))
      invFun := fun y ↦ ((y.2.2, y.1), y.2.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := (measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
      measurable_invFun := ((measurable_snd.comp measurable_snd).prodMk measurable_fst).prodMk
        (measurable_fst.comp measurable_snd) }
  exact (mutualInfo_map_left_measurableEquiv μ
    (fun ω ↦
      (((fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω), W ω),
        fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    (Y₂s i) ((hsuf₂.prodMk hW).prodMk hpre₁) (hY₂s i) e).symm

omit [Fintype ξ] [MeasurableSingletonClass ξ] [Fintype β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSingletonClass β₂] in
private lemma uvAux_absorbs_receiver1_terms
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂) (i : Fin n)
    (hW : Measurable W) (hY₁s : ∀ j, Measurable (Y₁s j))
    (hY₂s : ∀ j, Measurable (Y₂s j)) :
    condMutualInfo μ W (Y₁s i)
        (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      + condMutualInfo μ
          (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
          (fun ω ↦ (W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      ≤ mutualInfo μ (uvAux W Y₁s Y₂s i) (Y₁s i) := by
  classical
  have hpre₁ : Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₁s _
  have hsuf₂ : Measurable
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₂s _
  have h3 : condMutualInfo μ
        (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
        (fun ω ↦ (W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      = condMutualInfo μ
          (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
          (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W ω)) :=
    condMutualInfo_map_cond_measurableEquiv μ
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
      (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W ω))
      hsuf₂ (hY₁s i) (hpre₁.prodMk hW) MeasurableEquiv.prodComm
  have h1 := mutualInfo_chain_rule μ W (Y₁s i)
    (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) hW (hY₁s i) hpre₁
  have h2 := mutualInfo_chain_rule μ
    (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
    (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W ω))
    hsuf₂ (hY₁s i) (hpre₁.prodMk hW)
  have hkey : condMutualInfo μ W (Y₁s i)
        (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      + condMutualInfo μ
          (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
          (fun ω ↦ ((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W ω))
      ≤ mutualInfo μ
          (fun ω ↦
            (((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W ω),
              fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
          (Y₁s i) := by
    rw [h2, h1, add_assoc]
    exact le_add_self
  rw [h3]
  refine hkey.trans_eq ?_
  let e : ((Fin i.val → β₁) × ξ) × ({j : Fin n // i.val < j.val} → β₂)
        ≃ᵐ ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
    { toFun := fun x ↦ (x.1.2, (x.1.1, x.2))
      invFun := fun y ↦ ((y.2.1, y.1), y.2.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := (measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      measurable_invFun := ((measurable_fst.comp measurable_snd).prodMk measurable_fst).prodMk
        (measurable_snd.comp measurable_snd) }
  exact (mutualInfo_map_left_measurableEquiv μ
    (fun ω ↦
      (((fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω), W ω),
        fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
    (Y₁s i) ((hpre₁.prodMk hW).prodMk hsuf₂) (hY₁s i) e).symm

omit [Fintype α] [MeasurableSingletonClass α] [Fintype ξ] [MeasurableSingletonClass ξ]
  [Fintype β₁] [MeasurableSingletonClass β₁] [Fintype β₂] [MeasurableSingletonClass β₂] in
private lemma uvAux_markov_of_memo
    {υ : Type*} [MeasurableSpace υ] [StandardBorelSpace υ] [Nonempty υ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ξ) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (Yo : Ω → υ) (i : Fin n)
    (hW : Measurable W) (hXs : ∀ j, Measurable (Xs j))
    (hY₁s : ∀ j, Measurable (Y₁s j)) (hY₂s : ∀ j, Measurable (Y₂s j))
    (hYo : Measurable Yo)
    (h_memo : IsMarkovChain μ
      (fun ω ↦ (W ω,
        ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
         ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
          (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
      (Xs i) Yo) :
    IsMarkovChain μ
      (fun ω ↦ (uvAux W Y₁s Y₂s i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω))
      (Xs i) Yo := by
  classical
  have hblock : Measurable (fun ω ↦ (W ω,
      ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
       ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
        (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω))))) :=
    hW.prodMk
      ((measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hXs j.val).prodMk
      ((measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hY₁s j.val).prodMk
        (measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hY₂s j.val)))
  have hf : Measurable (fun (p : ξ × ((({j : Fin n // j ≠ i} → α)) ×
        ((({j : Fin n // j ≠ i} → β₁)) × ({j : Fin n // j ≠ i} → β₂)))) ↦
      ((p.1,
        ((fun (k : Fin i.val) ↦ p.2.2.1 ⟨⟨k.val, k.isLt.trans i.isLt⟩,
            by intro h; have hval : k.val = i.val := congrArg Fin.val h
               have hk := k.isLt; omega⟩),
         (fun (k : {j : Fin n // i.val < j.val}) ↦ p.2.2.2 ⟨k.val,
            by intro h; have hval : k.val.val = i.val := congrArg Fin.val h
               have hk := k.2; omega⟩))),
       p.2.1)) :=
    (measurable_fst.prodMk
      ((measurable_pi_iff.mpr fun _ ↦ (measurable_pi_apply _).comp
          (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
       (measurable_pi_iff.mpr fun _ ↦ (measurable_pi_apply _).comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd))))).prodMk
      (measurable_fst.comp measurable_snd)
  exact isMarkovChain_map_left μ _ (Xs i) Yo hblock (hXs i) hYo hf h_memo

private lemma bc_uv_input_step
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ξ) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (i : Fin n)
    (hW : Measurable W) (hXs : ∀ j, Measurable (Xs j))
    (hY₁s : ∀ j, Measurable (Y₁s j)) (hY₂s : ∀ j, Measurable (Y₂s j))
    (h_memo : IsMarkovChain μ
      (fun ω ↦ (W ω,
        ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
         ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
          (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
      (Xs i) (Y₁s i)) :
    condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₁s i)
        (fun ω ↦ (W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      ≤ condMutualInfo μ
          (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
          (fun ω ↦ (W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        + condMutualInfo μ (Xs i) (Y₁s i) (uvAux W Y₁s Y₂s i) := by
  classical
  have hXpi : Measurable (fun ω j ↦ Xs j ω) := measurable_pi_iff.mpr hXs
  have hpre₁ : Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₁s _
  have hsuf₂ : Measurable
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₂s _
  have hZ : Measurable
      (fun ω ↦ (W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) :=
    hW.prodMk hpre₁
  have hins := condMutualInfo_le_add_condMutualInfo μ (fun ω j ↦ Xs j ω)
    (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) (Y₁s i)
    (fun ω ↦ (W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    hXpi hsuf₂ (hY₁s i) hZ (mutualInfo_ne_top μ _ (Y₁s i) hZ (hY₁s i))
  refine hins.trans (add_le_add le_rfl ?_)
  have hreshape : condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₁s i)
        (fun ω ↦ ((W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
      = condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₁s i) (uvAux W Y₁s Y₂s i) :=
    (condMutualInfo_map_cond_measurableEquiv μ (fun ω j ↦ Xs j ω) (Y₁s i)
      (fun ω ↦ ((W ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
        fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
      hXpi (hY₁s i) (hZ.prodMk hsuf₂) MeasurableEquiv.prodAssoc).symm
  rw [hreshape]
  exact le_of_eq (condMutualInfo_pi_collapse_of_markov μ Xs (Y₁s i)
    (uvAux W Y₁s Y₂s i) i hXs (hY₁s i)
    (measurable_uvAux W Y₁s Y₂s hW hY₁s hY₂s i)
    (uvAux_markov_of_memo μ W Xs Y₁s Y₂s (Y₁s i) i hW hXs hY₁s hY₂s (hY₁s i) h_memo))

private lemma bc_uv_input_step'
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ξ) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (i : Fin n)
    (hW : Measurable W) (hXs : ∀ j, Measurable (Xs j))
    (hY₁s : ∀ j, Measurable (Y₁s j)) (hY₂s : ∀ j, Measurable (Y₂s j))
    (h_memo : IsMarkovChain μ
      (fun ω ↦ (W ω,
        ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
         ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
          (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
      (Xs i) (Y₂s i)) :
    condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₂s i)
        (fun ω ↦ (W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
      ≤ condMutualInfo μ
          (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
          (fun ω ↦ (W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
        + condMutualInfo μ (Xs i) (Y₂s i) (uvAux W Y₁s Y₂s i) := by
  classical
  have hXpi : Measurable (fun ω j ↦ Xs j ω) := measurable_pi_iff.mpr hXs
  have hpre₁ : Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₁s _
  have hsuf₂ : Measurable
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω) :=
    measurable_pi_iff.mpr fun _ ↦ hY₂s _
  have hZ : Measurable
      (fun ω ↦ (W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω)) :=
    hW.prodMk hsuf₂
  have hins := condMutualInfo_le_add_condMutualInfo μ (fun ω j ↦ Xs j ω)
    (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Y₂s i)
    (fun ω ↦ (W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω))
    hXpi hpre₁ (hY₂s i) hZ (mutualInfo_ne_top μ _ (Y₂s i) hZ (hY₂s i))
  refine hins.trans (add_le_add le_rfl ?_)
  let e : (ξ × ({j : Fin n // i.val < j.val} → β₂)) × (Fin i.val → β₁)
        ≃ᵐ ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
    { toFun := fun x ↦ (x.1.1, (x.2, x.1.2))
      invFun := fun y ↦ ((y.1, y.2.2), y.2.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      measurable_invFun := (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp measurable_snd) }
  have hreshape : condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₂s i)
        (fun ω ↦ ((W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω),
          fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      = condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₂s i) (uvAux W Y₁s Y₂s i) :=
    (condMutualInfo_map_cond_measurableEquiv μ (fun ω j ↦ Xs j ω) (Y₂s i)
      (fun ω ↦ ((W ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω),
        fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      hXpi (hY₂s i) (hZ.prodMk hpre₁) e).symm
  rw [hreshape]
  exact le_of_eq (condMutualInfo_pi_collapse_of_markov μ Xs (Y₂s i)
    (uvAux W Y₁s Y₂s i) i hXs (hY₂s i)
    (measurable_uvAux W Y₁s Y₂s hW hY₁s hY₂s i)
    (uvAux_markov_of_memo μ W Xs Y₁s Y₂s (Y₂s i) i hW hXs hY₁s hY₂s (hY₂s i) h_memo))

theorem bc_uv_singleletterize_sum₂
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → ξ) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW₂ : Measurable W₂) (hXs : ∀ i, Measurable (Xs i))
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (W₂ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
        (Xs i) (Y₁s i)) :
    mutualInfo μ W₂ (fun ω j ↦ Y₂s j ω)
        + condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₁s j ω) W₂
      ≤ ∑ i : Fin n,
          (mutualInfo μ (uvAux W₂ Y₁s Y₂s i) (Y₂s i)
            + condMutualInfo μ (Xs i) (Y₁s i) (uvAux W₂ Y₁s Y₂s i)) := by
  classical
  have hXpi : Measurable (fun ω j ↦ Xs j ω) := measurable_pi_iff.mpr hXs
  have hY₁pi : Measurable (fun ω j ↦ Y₁s j ω) := measurable_pi_iff.mpr hY₁s
  have hA : condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₁s j ω) W₂
      = ∑ i : Fin n, condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₁s i)
          (fun ω ↦ (W₂ ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
    rw [condMutualInfo_comm μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₁s j ω) W₂ hXpi hY₁pi hW₂,
      condMutualInfo_prefix_chain_rule μ Y₁s (fun ω j ↦ Xs j ω) W₂ hY₁s hXpi hW₂
        (mutualInfo_ne_top μ W₂ (fun ω j ↦ Xs j ω) hW₂ hXpi)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact condMutualInfo_comm μ (Y₁s i) (fun ω j ↦ Xs j ω) _ (hY₁s i) hXpi
      (hW₂.prodMk (measurable_pi_iff.mpr fun _ ↦ hY₁s _))
  rw [mutualInfo_chain_rule_Y_fin_suffix μ W₂ Y₂s hW₂ hY₂s, hA]
  refine le_trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦
    bc_uv_input_step μ W₂ Xs Y₁s Y₂s i hW₂ hXs hY₁s hY₂s (h_memo i))) ?_
  simp only [Finset.sum_add_distrib]
  rw [← add_assoc]
  refine add_le_add ?_ le_rfl
  rw [← csiszar_sum_identity_cond μ W₂ Y₁s Y₂s hW₂ hY₁s hY₂s, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦
    uvAux_absorbs_receiver2_terms μ W₂ Y₁s Y₂s i hW₂ hY₁s hY₂s

theorem bc_uv_singleletterize_sum₁
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ : Ω → ξ) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW₁ : Measurable W₁) (hXs : ∀ i, Measurable (Xs i))
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (W₁ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
        (Xs i) (Y₂s i)) :
    mutualInfo μ W₁ (fun ω j ↦ Y₁s j ω)
        + condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₂s j ω) W₁
      ≤ ∑ i : Fin n,
          (mutualInfo μ (uvAux W₁ Y₁s Y₂s i) (Y₁s i)
            + condMutualInfo μ (Xs i) (Y₂s i) (uvAux W₁ Y₁s Y₂s i)) := by
  classical
  have hXpi : Measurable (fun ω j ↦ Xs j ω) := measurable_pi_iff.mpr hXs
  have hY₂pi : Measurable (fun ω j ↦ Y₂s j ω) := measurable_pi_iff.mpr hY₂s
  have hA : condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₂s j ω) W₁
      = ∑ i : Fin n, condMutualInfo μ (fun ω j ↦ Xs j ω) (Y₂s i)
          (fun ω ↦ (W₁ ω,
            fun (j : {j : Fin n // i.val < j.val}) ↦ Y₂s j.val ω)) := by
    rw [condMutualInfo_comm μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₂s j ω) W₁ hXpi hY₂pi hW₁,
      condMutualInfo_suffix_chain_rule_full μ Y₂s (fun ω j ↦ Xs j ω) W₁ hY₂s hXpi hW₁
        (mutualInfo_ne_top μ W₁ (fun ω j ↦ Xs j ω) hW₁ hXpi)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact condMutualInfo_comm μ (Y₂s i) (fun ω j ↦ Xs j ω) _ (hY₂s i) hXpi
      (hW₁.prodMk (measurable_pi_iff.mpr fun _ ↦ hY₂s _))
  rw [mutualInfo_chain_rule_Y_fin' μ W₁ Y₁s hW₁ hY₁s, hA]
  refine le_trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦
    bc_uv_input_step' μ W₁ Xs Y₁s Y₂s i hW₁ hXs hY₁s hY₂s (h_memo i))) ?_
  simp only [Finset.sum_add_distrib]
  rw [← add_assoc]
  refine add_le_add ?_ le_rfl
  rw [csiszar_sum_identity_cond μ W₁ Y₁s Y₂s hW₁ hY₁s hY₂s, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦
    uvAux_absorbs_receiver1_terms μ W₁ Y₁s Y₂s i hW₁ hY₁s hY₂s

end SumBounds

end InformationTheory.Shannon.BroadcastChannel
