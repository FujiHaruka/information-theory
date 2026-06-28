import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.Entropy
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule

/-!
# Degraded broadcast channel — converse single-letterization (gateway probe)

This is a **gateway-atom probe** for the degraded broadcast channel (BC) converse
(Cover–Thomas Thm 15.6.2). It is intentionally NOT registered in `InformationTheory.lean`.

The converse single-letterization for the degraded BC introduces auxiliary variables
`Uᵢ = (W₂, Y₂^{i-1})` and splits into two bounds:

* bound (a) `R₂`-side: `I(W₂; Y₂ⁿ) ≤ ∑ᵢ I(Uᵢ; Y_{2,i})` — pure chain-rule plumbing on a
  *prefix* conditioner, no new infrastructure needed.
* bound (b) `R₁`-side: `I(W₁; Y₁ⁿ | W₂) = ∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` — requires the
  **Csiszár sum identity** to swap the prefix conditioner `Y₁^{i-1}` ↔ `Y₂^{i-1}` under
  degradedness `X → Y₁ → Y₂`.

The Csiszár sum identity is the decisive atom. It is a rearrangement of the MI chain rule
but needs *suffix*-sequence machinery (`B_{i+1}ⁿ`), of which there is no in-project
precedent (all existing chain-rule infrastructure is *prefix*-based `Y^{<i}`).
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ : Type*} [Fintype γ] [Nonempty γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [StandardBorelSpace γ]
variable {n : ℕ}

/-- **Y-axis n-variable MI chain rule** (helper for bound (a)):
`I(W; Bⁿ) = ∑ᵢ I(W; Bᵢ | B^{<i})`.

Derived from the left-axis `mutualInfo_chain_rule_fin` by `mutualInfo_comm` +
`condMutualInfo_comm`.  Prefix conditioner `B^{<i}` only — no suffix machinery. -/
lemma mutualInfo_chain_rule_Y_fin
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → γ) (Bs : Fin n → Ω → γ)
    (hW : Measurable W) (hBs : ∀ i, Measurable (Bs i)) :
    mutualInfo μ W (fun ω j ↦ Bs j ω)
      = ∑ i : Fin n,
          condMutualInfo μ W (Bs i)
            (fun ω (j : Fin i.val) ↦ Bs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  classical
  have hBpi : Measurable (fun ω j ↦ Bs j ω) := measurable_pi_iff.mpr hBs
  rw [mutualInfo_comm μ W (fun ω j ↦ Bs j ω) hW hBpi,
      mutualInfo_chain_rule_fin μ Bs hBs W hW]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpref : Measurable
      (fun ω (j : Fin i.val) ↦ Bs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun j ↦ hBs _
  exact condMutualInfo_comm μ (Bs i) W _ (hBs i) hW hpref

/-- **BC converse bound (a)** (`R₂`-side, the easy half): with `Uᵢ = (W₂, Y₂^{i-1})`,
`I(W₂; Y₂ⁿ) ≤ ∑ᵢ I(Uᵢ; Y_{2,i})`.

Chain-rule plumbing: expand `I(W₂; Y₂ⁿ)` via the Y-axis chain rule into
`∑ᵢ I(W₂; Y_{2,i} | Y₂^{i-1})`, then bound each summand by `I((W₂, Y₂^{i-1}); Y_{2,i})`
(adding the prefix to the data variable can only increase MI).  Prefix conditioner only. -/
theorem bc_converse_bound_a
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → γ) (Y₂s : Fin n → Ω → γ)
    (hW₂ : Measurable W₂) (hY₂s : ∀ i, Measurable (Y₂s i)) :
    (mutualInfo μ W₂ (fun ω j ↦ Y₂s j ω)).toReal
      ≤ ∑ i : Fin n,
          (mutualInfo μ
              (fun ω ↦ (W₂ ω,
                fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
              (Y₂s i)).toReal := by
  classical
  rw [mutualInfo_chain_rule_Y_fin μ W₂ Y₂s hW₂ hY₂s]
  rw [ENNReal.toReal_sum (fun i _ ↦
    condMutualInfo_ne_top μ W₂ (Y₂s i) _ hW₂ (hY₂s i)
      (measurable_pi_iff.mpr fun j ↦ hY₂s _))]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  set pref : Ω → (Fin i.val → γ) :=
    fun ω j ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω with hpref_def
  have hpref : Measurable pref := measurable_pi_iff.mpr fun j ↦ hY₂s _
  have hle : condMutualInfo μ W₂ (Y₂s i) pref
      ≤ mutualInfo μ (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i) := by
    have hreshape : mutualInfo μ (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i)
        = mutualInfo μ (fun ω ↦ (pref ω, W₂ ω)) (Y₂s i) := by
      have h := mutualInfo_map_left_measurableEquiv μ
        (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i) (hW₂.prodMk hpref) (hY₂s i)
        (MeasurableEquiv.prodComm (α := γ) (β := (Fin i.val → γ)))
      simpa [MeasurableEquiv.prodComm] using h.symm
    rw [hreshape, mutualInfo_chain_rule μ W₂ (Y₂s i) pref hW₂ (hY₂s i) hpref]
    exact le_add_self
  have hne1 : condMutualInfo μ W₂ (Y₂s i) pref ≠ ∞ :=
    condMutualInfo_ne_top μ W₂ (Y₂s i) pref hW₂ (hY₂s i) hpref
  have hne2 : mutualInfo μ (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i) ≠ ∞ :=
    mutualInfo_ne_top μ (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i) (hW₂.prodMk hpref) (hY₂s i)
  exact (ENNReal.toReal_le_toReal hne1 hne2).mpr hle

/-- **Csiszár sum identity** (the decisive atom for bound (b)): for any two finite-alphabet
sequences `As`, `Bs` over `Fin n`,
`∑ᵢ I(A^{i-1}; Bᵢ | B_{i+1}ⁿ) = ∑ᵢ I(B_{i+1}ⁿ; Aᵢ | A^{i-1})`.

Here `A^{i-1}` is the *prefix* `fun j : Fin i.val ↦ Aⱼ` and `B_{i+1}ⁿ` is the *suffix*
`fun j : {j : Fin n // i.val < j.val} ↦ Bⱼ`. This is a rearrangement of the MI chain rule
(El Gamal–Kim), but the suffix conditioner `B_{i+1}ⁿ` has no in-project precedent.

@residual(plan:bc-degraded-converse-plan) -/
theorem csiszar_sum_identity
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As Bs : Fin n → Ω → γ)
    (hAs : ∀ i, Measurable (As i)) (hBs : ∀ i, Measurable (Bs i)) :
    ∑ i : Fin n,
        condMutualInfo μ
          (fun ω (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          (Bs i)
          (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)
      = ∑ i : Fin n,
          condMutualInfo μ
            (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)
            (As i)
            (fun ω (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  sorry

end InformationTheory.Shannon.BroadcastChannel
