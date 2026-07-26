import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMIChainRule
import InformationTheory.Shannon.Entropy
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule

/-!
# Degraded broadcast channel — converse single-letterization

Chain-rule material for the converse of the degraded broadcast channel (BC) coding theorem
(Cover–Thomas Thm 15.6.2). The single-letterization introduces auxiliary variables
`Uᵢ = (W₂, Y₂^{i-1})` and splits into two bounds:

* the `R₂`-side bound `I(W₂; Y₂ⁿ) ≤ ∑ᵢ I(Uᵢ; Y_{2,i})` — chain-rule plumbing on a *prefix*
  conditioner.
* the `R₁`-side bound `I(W₁; Y₁ⁿ | W₂) = ∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` — this one requires the
  **Csiszár sum identity** to swap the prefix conditioner `Y₁^{i-1}` ↔ `Y₂^{i-1}` under
  degradedness `X → Y₁ → Y₂`.

## Implementation notes

The Csiszár sum identity is a rearrangement of the mutual-information chain rule, but it is
stated over *suffix* sequences `B_{i+1}ⁿ` whereas the rest of the chain-rule API here is
*prefix*-based (`Y^{<i}`); its proof therefore goes through the reflection-based
`condMutualInfo_suffix_chain_rule`.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

-- Typed analogue of `mutualInfo_chain_rule_Y_fin`: the left variable `W` may live in a
-- different alphabet from the sequence.
lemma mutualInfo_chain_rule_Y_fin' {m : ℕ} {δ γ : Type*}
    [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [StandardBorelSpace γ] [Nonempty γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → δ) (Bs : Fin m → Ω → γ)
    (hW : Measurable W) (hBs : ∀ i, Measurable (Bs i)) :
    mutualInfo μ W (fun ω j ↦ Bs j ω)
      = ∑ i : Fin m,
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

variable {γ : Type*} [Fintype γ] [Nonempty γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [StandardBorelSpace γ]
variable {n : ℕ}

/-- Chain rule for mutual information expanded along the sequence argument:
`I(W; Bⁿ) = ∑ᵢ I(W; Bᵢ | B^{<i})`.

Derived from the left-axis `mutualInfo_chain_rule_fin` by `mutualInfo_comm` +
`condMutualInfo_comm`.  The conditioner is the prefix `B^{<i}` only.
@audit:ok -/
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

/-- Receiver-2 single-letterization for the BC converse: with `Uᵢ = (W₂, Y₂^{i-1})`, the
message–output mutual information obeys `I(W₂; Y₂ⁿ) ≤ ∑ᵢ I(Uᵢ; Y_{2,i})`.

Chain-rule plumbing: expand `I(W₂; Y₂ⁿ)` along the sequence argument into
`∑ᵢ I(W₂; Y_{2,i} | Y₂^{i-1})`, then bound each summand by `I((W₂, Y₂^{i-1}); Y_{2,i})`
(adding the prefix to the data variable can only increase mutual information).
@audit:ok -/
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

/-- **Csiszár sum identity** (the key ingredient of the `R₁`-side bound): for any two
finite-alphabet sequences `As`, `Bs` over `Fin n`,
`∑ᵢ I(A^{i-1}; Bᵢ | B_{i+1}ⁿ) = ∑ᵢ I(B_{i+1}ⁿ; Aᵢ | A^{i-1})`.

Here `A^{i-1}` is the *prefix* `fun j : Fin i.val ↦ Aⱼ` and `B_{i+1}ⁿ` is the *suffix*
`fun j : {j : Fin n // i.val < j.val} ↦ Bⱼ`. Both sides expand (via the prefix chain rule
`condMutualInfo_prefix_chain_rule` for the left, the reflection-based suffix chain rule
`condMutualInfo_suffix_chain_rule` for the right) to the common triangular double sum
`∑_{k<i} I(Aₖ; Bᵢ | A^{k-1}, B_{i+1}ⁿ)`, matched termwise by `condMutualInfo_comm` plus a
`prodComm` relabel of the conditioner (El Gamal–Kim).
@audit:ok -/
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
  classical
  -- Finiteness of the background mutual informations (finite alphabets).
  have hfinB : ∀ i : Fin n,
      mutualInfo μ (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω) (Bs i) ≠ ∞ :=
    fun i ↦ mutualInfo_ne_top μ _ (Bs i) (measurable_pi_iff.mpr fun j ↦ hBs _) (hBs i)
  have hfinA : ∀ i : Fin n,
      mutualInfo μ (fun ω (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω) (As i) ≠ ∞ :=
    fun i ↦ mutualInfo_ne_top μ _ (As i) (measurable_pi_iff.mpr fun j ↦ hAs _) (hAs i)
  -- Common double-sum term (after both expansions, modulo `comm`/`prodComm` on the conditioner).
  -- LHS expands by the *prefix* chain rule; RHS by the *suffix* chain rule.
  -- Expand each summand.
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦
        condMutualInfo_prefix_chain_rule μ
          (fun (j : Fin i.val) ω ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Bs i)
          (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)
          (fun j ↦ hAs _) (hBs i) (measurable_pi_iff.mpr fun j ↦ hBs _) (hfinB i)),
     Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦
        condMutualInfo_suffix_chain_rule i μ Bs (As i)
          (fun ω (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          hBs (hAs i) (measurable_pi_iff.mpr fun j ↦ hAs _) (hfinA i))]
  -- Merge nested sums into sigma sums.
  rw [Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ),
      Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)]
  -- Bijection between the two index sets `{(i,k) : k<i}` and `{(i,j) : i<j}` (transpose).
  refine Finset.sum_nbij'
    (i := fun x ↦ ⟨⟨x.2.val, x.2.isLt.trans x.1.isLt⟩, ⟨x.1, x.2.isLt⟩⟩)
    (j := fun y ↦ ⟨y.2.val, ⟨y.1.val, y.2.property⟩⟩)
    (fun x _ ↦ Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun y _ ↦ Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun x _ ↦ rfl) (fun y _ ↦ rfl) ?_
  rintro ⟨i, k⟩ _
  -- Per-term: `comm` to swap roles, then `R1` (`prodComm`) to swap the conditioner pair.
  simp only
  rw [condMutualInfo_comm μ (As ⟨k.val, k.isLt.trans i.isLt⟩) (Bs i)
        (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω),
          fun (a : Fin k.val) ↦ As ⟨a.val, a.isLt.trans (k.isLt.trans i.isLt)⟩ ω))
        (hAs _) (hBs i)
        ((measurable_pi_iff.mpr fun j ↦ hBs _).prodMk (measurable_pi_iff.mpr fun a ↦ hAs _))]
  rw [← condMutualInfo_map_cond_measurableEquiv μ (Bs i) (As ⟨k.val, k.isLt.trans i.isLt⟩)
        (fun ω ↦ ((fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω),
          fun (a : Fin k.val) ↦ As ⟨a.val, a.isLt.trans (k.isLt.trans i.isLt)⟩ ω))
        (hBs i) (hAs _)
        ((measurable_pi_iff.mpr fun j ↦ hBs _).prodMk (measurable_pi_iff.mpr fun a ↦ hAs _))
        MeasurableEquiv.prodComm]
  rfl

end InformationTheory.Shannon.BroadcastChannel
