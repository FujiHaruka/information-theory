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
  sorry

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
  sorry

end SumBounds

end InformationTheory.Shannon.BroadcastChannel
