import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMIChainRule

/-!
# General broadcast channel — chain-rule gateway for the UV outer bound

Chain-rule material for the Nair–El Gamal (UV) outer bound of the general two-receiver
broadcast channel (El Gamal–Kim, Ch. 8). The auxiliary variables of that bound mix a
*prefix* of one output sequence with a *suffix* of the other,
`Uᵢ = (W₂, Y₁^{<i}, Y₂^{>i})` and `Vᵢ = (W₁, Y₁^{<i}, Y₂^{>i})`, which needs three pieces
of plumbing that the degraded converse (`BroadcastChannel.Converse`) did not:

* the *reverse-order* expansions `I(W; Bⁿ) = ∑ᵢ I(W; Bᵢ | B^{>i})` and its conditional form,
  obtained from the forward expansion by reversing the index;
* the step `I(A; C | Z) ≤ I(B; C | Z) + I(A; C | (Z, B))` that inserts the output suffix into
  the conditioner;
* the Csiszár sum identity for two sequences over distinct alphabets carrying a background
  conditioner, which swaps the prefix conditioner `A^{<i}` for the suffix conditioner
  `B^{>i}`.

## Main statements

* `mutualInfo_chain_rule_Y_fin_suffix` — reverse-order expansion of `I(W; Bⁿ)`.
* `condMutualInfo_suffix_chain_rule_full` — the same expansion for `I(Bⁿ; C | Z)`.
* `condMutualInfo_le_add_condMutualInfo` — inserting a variable into the conditioner.
* `csiszar_sum_identity_cond` — the Csiszár sum identity with a background conditioner.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ}

section SuffixChainRule

variable {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
variable {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [StandardBorelSpace γ] [Nonempty γ]

/-- Chain rule for mutual information expanded along the sequence argument in reverse order:
`I(W; Bⁿ) = ∑ᵢ I(W; Bᵢ | B^{>i})`, the conditioner being the *suffix* `B^{>i}`. The suffix
counterpart of `mutualInfo_chain_rule_Y_fin'`, obtained by reindexing the sequence with
`Fin.rev` so that the prefix expansion applies and then transporting the resulting prefix
conditioner back across that reindexing.

@audit:ok -/
lemma mutualInfo_chain_rule_Y_fin_suffix
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → δ) (Bs : Fin n → Ω → γ)
    (hW : Measurable W) (hBs : ∀ i, Measurable (Bs i)) :
    mutualInfo μ W (fun ω j ↦ Bs j ω)
      = ∑ i : Fin n,
          condMutualInfo μ W (Bs i)
            (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω) := by
  classical
  have hBpi : Measurable (fun ω j ↦ Bs j ω) := measurable_pi_iff.mpr hBs
  let σ : Fin n ≃ Fin n :=
    { toFun := Fin.rev, invFun := Fin.rev
      left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }
  have hBs' : ∀ k : Fin n, Measurable (fun ω ↦ Bs (Fin.rev k) ω) := fun k ↦ hBs _
  rw [mutualInfo_comm μ W (fun ω j ↦ Bs j ω) hW hBpi]
  have hrev : mutualInfo μ (fun ω j ↦ Bs j ω) W
      = mutualInfo μ (fun ω (k : Fin n) ↦ Bs (Fin.rev k) ω) W :=
    (mutualInfo_map_left_measurableEquiv μ (fun ω j ↦ Bs j ω) W hBpi hW
      (piReindexMeasurableEquiv (γ := γ) σ)).symm
  rw [hrev,
    mutualInfo_chain_rule_fin μ (fun (k : Fin n) ω ↦ Bs (Fin.rev k) ω) hBs' W hW,
    ← Equiv.sum_comp σ (fun i : Fin n ↦ condMutualInfo μ W (Bs i)
      (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hpre : Measurable
      (fun ω (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω) :=
    measurable_pi_iff.mpr fun a ↦ hBs _
  rw [condMutualInfo_comm μ (fun ω ↦ Bs (Fin.rev k) ω) W
    (fun ω (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω)
    (hBs _) hW hpre]
  let τ : Fin k.val ≃ {j : Fin n // (Fin.rev k).val < j.val} :=
    { toFun := fun a ↦ ⟨Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩, by
        have h1 := a.isLt; have h2 := k.isLt
        simp only [Fin.val_rev]; omega⟩
      invFun := fun j ↦ ⟨(Fin.rev j.val).val, by
        have h1 := j.2; have h2 := j.val.isLt; have h3 := k.isLt
        simp only [Fin.val_rev] at h1 ⊢; omega⟩
      left_inv := fun a ↦ by
        have h1 := a.isLt; have h2 := k.isLt
        apply Fin.ext; simp only [Fin.val_rev]; omega
      right_inv := fun j ↦ by
        have h1 := j.2; have h2 := j.val.isLt
        apply Subtype.ext; apply Fin.ext; simp only [Fin.val_rev]; omega }
  have hcond : (fun ω ↦ (piReindexMeasurableEquiv (γ := γ) τ)
        (fun (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω))
      = fun ω (j : {j : Fin n // (Fin.rev k).val < j.val}) ↦ Bs j.val ω := by
    funext ω j
    change Bs (Fin.rev ⟨(τ.symm j).val, (τ.symm j).isLt.trans k.isLt⟩) ω = Bs j.val ω
    exact congrArg (fun m : Fin n ↦ Bs m ω) (congrArg Subtype.val (τ.apply_symm_apply j))
  rw [← condMutualInfo_map_cond_measurableEquiv μ W (fun ω ↦ Bs (Fin.rev k) ω)
    (fun ω (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω)
    hW (hBs _) hpre (piReindexMeasurableEquiv (γ := γ) τ), hcond]
  rfl

end SuffixChainRule

section CondSuffixChainRule

variable {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
variable {γ : Type*} [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
variable {ζ : Type*} [MeasurableSpace ζ]

/-- Conditional chain rule expanded along the sequence in reverse order:
`I(Bⁿ; C | Z) = ∑ᵢ I(Bᵢ; C | (Z, B^{>i}))`, the background conditioner `Z` riding along
untouched. Same `Fin.rev` reindexing as `mutualInfo_chain_rule_Y_fin_suffix`, applied to
`condMutualInfo_prefix_chain_rule`; `hZC` is the finiteness side condition that expansion
needs in order to cancel the background term `I(Z; C)`.

@audit:ok -/
theorem condMutualInfo_suffix_chain_rule_full
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Bs : Fin n → Ω → γ) (C : Ω → δ) (Z : Ω → ζ)
    (hBs : ∀ i, Measurable (Bs i)) (hC : Measurable C) (hZ : Measurable Z)
    (hZC : mutualInfo μ Z C ≠ ∞) :
    condMutualInfo μ (fun ω j ↦ Bs j ω) C Z
      = ∑ i : Fin n,
          condMutualInfo μ (Bs i) C
            (fun ω ↦ (Z ω,
              fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)) := by
  classical
  have hBpi : Measurable (fun ω j ↦ Bs j ω) := measurable_pi_iff.mpr hBs
  let σ : Fin n ≃ Fin n :=
    { toFun := Fin.rev, invFun := Fin.rev
      left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }
  have hBs' : ∀ k : Fin n, Measurable (fun ω ↦ Bs (Fin.rev k) ω) := fun k ↦ hBs _
  have hrev : condMutualInfo μ (fun ω j ↦ Bs j ω) C Z
      = condMutualInfo μ (fun ω (k : Fin n) ↦ Bs (Fin.rev k) ω) C Z :=
    (condMutualInfo_map_left_measurableEquiv μ (fun ω j ↦ Bs j ω) C Z hBpi hC hZ
      (piReindexMeasurableEquiv (γ := γ) σ)).symm
  rw [hrev,
    condMutualInfo_prefix_chain_rule μ (fun (k : Fin n) ω ↦ Bs (Fin.rev k) ω) C Z hBs' hC hZ hZC,
    ← Equiv.sum_comp σ (fun i : Fin n ↦ condMutualInfo μ (Bs i) C
      (fun ω ↦ (Z ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hpre : Measurable
      (fun ω (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω) :=
    measurable_pi_iff.mpr fun a ↦ hBs _
  let τ : Fin k.val ≃ {j : Fin n // (Fin.rev k).val < j.val} :=
    { toFun := fun a ↦ ⟨Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩, by
        have h1 := a.isLt; have h2 := k.isLt
        simp only [Fin.val_rev]; omega⟩
      invFun := fun j ↦ ⟨(Fin.rev j.val).val, by
        have h1 := j.2; have h2 := j.val.isLt; have h3 := k.isLt
        simp only [Fin.val_rev] at h1 ⊢; omega⟩
      left_inv := fun a ↦ by
        have h1 := a.isLt; have h2 := k.isLt
        apply Fin.ext; simp only [Fin.val_rev]; omega
      right_inv := fun j ↦ by
        have h1 := j.2; have h2 := j.val.isLt
        apply Subtype.ext; apply Fin.ext; simp only [Fin.val_rev]; omega }
  have hcond : (fun ω ↦
        ((MeasurableEquiv.refl ζ).prodCongr (piReindexMeasurableEquiv (γ := γ) τ))
          (Z ω, fun (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω))
      = fun ω ↦ (Z ω, fun (j : {j : Fin n // (Fin.rev k).val < j.val}) ↦ Bs j.val ω) := by
    funext ω
    refine Prod.ext rfl ?_
    funext j
    change Bs (Fin.rev ⟨(τ.symm j).val, (τ.symm j).isLt.trans k.isLt⟩) ω = Bs j.val ω
    exact congrArg (fun m : Fin n ↦ Bs m ω) (congrArg Subtype.val (τ.apply_symm_apply j))
  rw [← condMutualInfo_map_cond_measurableEquiv μ (fun ω ↦ Bs (Fin.rev k) ω) C
    (fun ω ↦ (Z ω, fun (a : Fin k.val) ↦ Bs (Fin.rev ⟨a.val, a.isLt.trans k.isLt⟩) ω))
    (hBs _) hC (hZ.prodMk hpre)
    ((MeasurableEquiv.refl ζ).prodCongr (piReindexMeasurableEquiv (γ := γ) τ)), hcond]
  rfl

end CondSuffixChainRule

section InsertConditioner

variable {κ : Type*} [MeasurableSpace κ] [StandardBorelSpace κ] [Nonempty κ]
variable {lam : Type*} [MeasurableSpace lam] [StandardBorelSpace lam] [Nonempty lam]
variable {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
variable {ζ : Type*} [MeasurableSpace ζ]

/-- Inserting a variable into the conditioner:
`I(A; C | Z) ≤ I(B; C | Z) + I(A; C | (Z, B))`. Expanding `I((Z, A, B); C)` by the chain rule
in the two possible orders gives two decompositions that differ by the nonnegative term
`I(B; C | (Z, A))`, and the inequality is what remains after dropping it. `hZC` cancels the
background term `I(Z; C)` shared by both decompositions.

@audit:ok -/
lemma condMutualInfo_le_add_condMutualInfo
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → κ) (B : Ω → lam) (C : Ω → δ) (Z : Ω → ζ)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hZ : Measurable Z)
    (hZC : mutualInfo μ Z C ≠ ∞) :
    condMutualInfo μ A C Z
      ≤ condMutualInfo μ B C Z + condMutualInfo μ A C (fun ω ↦ (Z ω, B ω)) := by
  classical
  have hZB : Measurable (fun ω ↦ (Z ω, B ω)) := hZ.prodMk hB
  have hZA : Measurable (fun ω ↦ (Z ω, A ω)) := hZ.prodMk hA
  have h1 := mutualInfo_chain_rule μ B C Z hB hC hZ
  have h2 := mutualInfo_chain_rule μ A C (fun ω ↦ (Z ω, B ω)) hA hC hZB
  have h3 := mutualInfo_chain_rule μ A C Z hA hC hZ
  have h4 := mutualInfo_chain_rule μ B C (fun ω ↦ (Z ω, A ω)) hB hC hZA
  let e : (ζ × lam) × κ ≃ᵐ (ζ × κ) × lam :=
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl ζ).prodCongr MeasurableEquiv.prodComm)).trans
      MeasurableEquiv.prodAssoc.symm
  have h5 : mutualInfo μ (fun ω ↦ ((Z ω, B ω), A ω)) C
      = mutualInfo μ (fun ω ↦ ((Z ω, A ω), B ω)) C := by
    have h := mutualInfo_map_left_measurableEquiv μ
      (fun ω ↦ ((Z ω, B ω), A ω)) C (hZB.prodMk hA) hC e
    rw [show (fun ω ↦ e ((Z ω, B ω), A ω)) = (fun ω ↦ ((Z ω, A ω), B ω)) from rfl] at h
    exact h.symm
  rw [h5, h4, h3] at h2
  rw [h1] at h2
  -- `h2 : I(Z;C) + I(B;C|Z) + I(A;C|(Z,B)) = I(Z;C) + I(A;C|Z) + I(B;C|(Z,A))`
  rw [add_assoc, add_assoc] at h2
  have hcancel := WithTop.add_left_cancel hZC h2
  calc condMutualInfo μ A C Z
      ≤ condMutualInfo μ A C Z + condMutualInfo μ B C (fun ω ↦ (Z ω, A ω)) := le_self_add
    _ = condMutualInfo μ B C Z + condMutualInfo μ A C (fun ω ↦ (Z ω, B ω)) := hcancel

end InsertConditioner

section CsiszarCond

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α] [Nonempty α]
variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [Nonempty β]
variable {ξ : Type*} [Fintype ξ] [MeasurableSpace ξ] [MeasurableSingletonClass ξ]

/-- Conditioned form of the **Csiszár sum identity**, for two sequences over distinct
alphabets and a background conditioner `Wc`:
`∑ᵢ I(A^{<i}; Bᵢ | (Wc, B^{>i})) = ∑ᵢ I(B^{>i}; Aᵢ | (Wc, A^{<i}))`. As in
`csiszar_sum_identity`, both sides expand to the common triangular double sum
`∑_{k<i} I(Aₖ; Bᵢ | (Wc, A^{<k}, B^{>i}))` — the left by the prefix chain rule, the right by
the suffix one — and the terms are matched by `condMutualInfo_comm` together with a
`prodComm` relabel of the conditioner (El Gamal–Kim).

@audit:ok -/
theorem csiszar_sum_identity_cond
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Wc : Ω → ξ) (As : Fin n → Ω → α) (Bs : Fin n → Ω → β)
    (hWc : Measurable Wc) (hAs : ∀ i, Measurable (As i)) (hBs : ∀ i, Measurable (Bs i)) :
    ∑ i : Fin n,
        condMutualInfo μ
          (fun ω (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          (Bs i)
          (fun ω ↦ (Wc ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω))
      = ∑ i : Fin n,
          condMutualInfo μ
            (fun ω (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)
            (As i)
            (fun ω ↦ (Wc ω,
              fun (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  classical
  have hfinB : ∀ i : Fin n,
      mutualInfo μ
          (fun ω ↦ (Wc ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω)) (Bs i) ≠ ∞ :=
    fun i ↦ mutualInfo_ne_top μ _ (Bs i)
      (hWc.prodMk (measurable_pi_iff.mpr fun j ↦ hBs _)) (hBs i)
  have hfinA : ∀ i : Fin n,
      mutualInfo μ
          (fun ω ↦ (Wc ω,
            fun (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω)) (As i) ≠ ∞ :=
    fun i ↦ mutualInfo_ne_top μ _ (As i)
      (hWc.prodMk (measurable_pi_iff.mpr fun j ↦ hAs _)) (hAs i)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦
        condMutualInfo_prefix_chain_rule μ
          (fun (j : Fin i.val) ω ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω) (Bs i)
          (fun ω ↦ (Wc ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω))
          (fun j ↦ hAs _) (hBs i)
          (hWc.prodMk (measurable_pi_iff.mpr fun j ↦ hBs _)) (hfinB i)),
     Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦
        condMutualInfo_suffix_chain_rule i μ Bs (As i)
          (fun ω ↦ (Wc ω, fun (j : Fin i.val) ↦ As ⟨j.val, j.isLt.trans i.isLt⟩ ω))
          hBs (hAs i)
          (hWc.prodMk (measurable_pi_iff.mpr fun j ↦ hAs _)) (hfinA i))]
  rw [Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ),
      Finset.sum_sigma' Finset.univ (fun _ ↦ Finset.univ)]
  refine Finset.sum_nbij'
    (i := fun x ↦ ⟨⟨x.2.val, x.2.isLt.trans x.1.isLt⟩, ⟨x.1, x.2.isLt⟩⟩)
    (j := fun y ↦ ⟨y.2.val, ⟨y.1.val, y.2.property⟩⟩)
    (fun x _ ↦ Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun y _ ↦ Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun x _ ↦ rfl) (fun y _ ↦ rfl) ?_
  rintro ⟨i, k⟩ _
  simp only
  have hmeasCond : Measurable (fun ω ↦
      ((Wc ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω),
        fun (a : Fin k.val) ↦ As ⟨a.val, a.isLt.trans (k.isLt.trans i.isLt)⟩ ω)) :=
    (hWc.prodMk (measurable_pi_iff.mpr fun j ↦ hBs _)).prodMk
      (measurable_pi_iff.mpr fun a ↦ hAs _)
  rw [condMutualInfo_comm μ (As ⟨k.val, k.isLt.trans i.isLt⟩) (Bs i) _
    (hAs _) (hBs i) hmeasCond]
  let e : (ξ × ({j : Fin n // i.val < j.val} → β)) × (Fin k.val → α)
        ≃ᵐ (ξ × (Fin k.val → α)) × ({j : Fin n // i.val < j.val} → β) :=
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl ξ).prodCongr MeasurableEquiv.prodComm)).trans
      MeasurableEquiv.prodAssoc.symm
  rw [← condMutualInfo_map_cond_measurableEquiv μ (Bs i) (As ⟨k.val, k.isLt.trans i.isLt⟩)
    (fun ω ↦
      ((Wc ω, fun (j : {j : Fin n // i.val < j.val}) ↦ Bs j.val ω),
        fun (a : Fin k.val) ↦ As ⟨a.val, a.isLt.trans (k.isLt.trans i.isLt)⟩ ω))
    (hBs i) (hAs _) hmeasCond e]
  rfl

end CsiszarCond

end InformationTheory.Shannon.BroadcastChannel
