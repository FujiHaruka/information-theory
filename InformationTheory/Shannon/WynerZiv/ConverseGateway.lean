import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.CondMIChainRule

/-!
# Wyner–Ziv converse — heterogeneous Csiszár sum identity (gateway probe)

This is a **gateway-atom probe** for the Wyner–Ziv operational converse. It generalizes the
same-alphabet `csiszar_sum_identity`
(`InformationTheory/Shannon/BroadcastChannel/ConverseGateway.lean`) to two sequences over
**distinct** finite alphabets `α` (the source `X`) and `β` (the side information `Y`).

The Wyner–Ziv converse single-letterization needs the Csiszár sum identity to swap the
prefix conditioner `X^{i-1}` ↔ suffix conditioner `Y_{i+1}ⁿ`. Because the source and side
information live in different alphabets, the same-alphabet identity cannot be reused as-is.

The proof is a direct port of the same-alphabet version: the underlying prefix / suffix
conditional chain rules (`condMutualInfo_prefix_chain_rule`, `condMutualInfo_suffix_chain_rule`)
and the swaps (`condMutualInfo_comm`, `condMutualInfo_map_cond_measurableEquiv`) are already
polymorphic in the three role types, so the index plumbing is unchanged; only the two sequence
alphabets differ.
-/

namespace InformationTheory.Shannon.WynerZiv

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Nonempty β]
variable {n : ℕ}

/-- **Heterogeneous Csiszár sum identity** (gateway atom for the Wyner–Ziv converse): for two
finite-alphabet sequences `As : Fin n → Ω → α` and `Bs : Fin n → Ω → β` over *distinct*
alphabets,
`∑ᵢ I(A^{i-1}; Bᵢ | B_{i+1}ⁿ) = ∑ᵢ I(B_{i+1}ⁿ; Aᵢ | A^{i-1})`.

Here `A^{i-1}` is the *prefix* `fun j : Fin i.val ↦ Aⱼ` and `B_{i+1}ⁿ` is the *suffix*
`fun j : {j : Fin n // i.val < j.val} ↦ Bⱼ`, exactly as in the same-alphabet
`csiszar_sum_identity`. Both sides expand (prefix chain rule on the left, reflection-based
suffix chain rule on the right) to the common triangular double sum
`∑_{k<i} I(Aₖ; Bᵢ | A^{k-1}, B_{i+1}ⁿ)`, matched termwise by `condMutualInfo_comm` plus a
`prodComm` relabel of the conditioner. The distinct alphabets flow through untouched because
the chain rules are polymorphic in the sequence / data / conditioner role types.
@audit:ok -/
theorem csiszar_sum_identity_hetero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Fin n → Ω → α) (Bs : Fin n → Ω → β)
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

end InformationTheory.Shannon.WynerZiv
