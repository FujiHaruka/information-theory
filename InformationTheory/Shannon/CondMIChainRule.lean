import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule

/-!
# Conditional mutual-information chain rule over a `Fin`-prefix

The `n`-variable conditional chain rule for mutual information with a background conditioner
`Z` carried throughout:

```
I(A^{<m}; C | Z) = ∑_{k < m} I(A_k; C | (Z, A^{<k})).
```

This is the conditional analogue of `mutualInfo_chain_rule_fin`, obtained by an *additive*
induction (`mutualInfo_prefix_chain_rule_add`) followed by cancellation of the common term
`I(Z; C)`. The additive formulation has a clean base case (the empty prefix reshapes
`(Z, ⟨⟩) ≃ᵐ Z`), avoiding any constant-random-variable measure computation.

## Main statements

* `mutualInfo_prefix_chain_rule_add` — `I((Z, A^{<m}); C) = I(Z; C) + ∑_{k<m} I(A_k; C | (Z, A^{<k}))`.
* `condMutualInfo_prefix_chain_rule` — `I(A^{<m}; C | Z) = ∑_{k<m} I(A_k; C | (Z, A^{<k}))`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ : Type*} [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
variable {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
variable {ζ : Type*} [MeasurableSpace ζ]

/-- Additive prefix chain rule: prepending a `Fin m` prefix of `As` to the background
conditioner `Z` decomposes the mutual information additively as
`I((Z, A^{<m}); C) = I(Z; C) + ∑_{k<m} I(A_k; C | (Z, A^{<k}))`. Proven by induction on `m`. -/
theorem mutualInfo_prefix_chain_rule_add
    {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Fin m → Ω → γ) (C : Ω → δ) (Z : Ω → ζ)
    (hAs : ∀ i, Measurable (As i)) (hC : Measurable C) (hZ : Measurable Z) :
    mutualInfo μ (fun ω ↦ (Z ω, fun j ↦ As j ω)) C
      = mutualInfo μ Z C
        + ∑ k : Fin m,
            condMutualInfo μ (As k) C
              (fun ω ↦ (Z ω,
                fun (j : Fin k.val) ↦ As ⟨j.val, j.isLt.trans k.isLt⟩ ω)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_zero, add_zero]
    -- Reshape `(Z, ⟨⟩) ≃ᵐ Z` (empty prefix is the unique element of `Fin 0 → γ`).
    let eBase : ζ × (Fin 0 → γ) ≃ᵐ ζ :=
      { toFun := Prod.fst
        invFun := fun z ↦ (z, fun j ↦ Fin.elim0 j)
        left_inv := fun p ↦ Prod.ext rfl (Subsingleton.elim _ _)
        right_inv := fun _ ↦ rfl
        measurable_toFun := measurable_fst
        measurable_invFun := measurable_id.prodMk measurable_const }
    have hmeas : Measurable (fun ω ↦ (Z ω, fun (j : Fin 0) ↦ As j ω)) :=
      hZ.prodMk (measurable_pi_iff.mpr hAs)
    have h := mutualInfo_map_left_measurableEquiv μ
      (fun ω ↦ (Z ω, fun (j : Fin 0) ↦ As j ω)) C hmeas hC eBase
    -- `eBase (Z ω, _) = Z ω`, so the LHS of `h` is `mutualInfo μ Z C`.
    exact h.symm
  | succ m IH =>
    set f : Ω → (Fin m → γ) := fun ω j ↦ As j.castSucc ω with hf_def
    set g : Ω → γ := As (Fin.last m) with hg_def
    have hf : Measurable f := measurable_pi_iff.mpr fun j ↦ hAs j.castSucc
    have hg : Measurable g := hAs (Fin.last m)
    have hZpi : Measurable (fun ω ↦ (Z ω, fun i : Fin (m + 1) ↦ As i ω)) :=
      hZ.prodMk (measurable_pi_iff.mpr hAs)
    -- Reshape `(Z, A^{<m+1}) ≃ᵐ ((Z, A^{<m}), A_m)`.
    let ePi : (Fin (m + 1) → γ) ≃ᵐ γ × (Fin m → γ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ ↦ γ) (Fin.last m)
    let eReassoc : ζ × (γ × (Fin m → γ)) ≃ᵐ (ζ × (Fin m → γ)) × γ :=
      ((MeasurableEquiv.refl ζ).prodCongr MeasurableEquiv.prodComm).trans
        (MeasurableEquiv.prodAssoc).symm
    let e : ζ × (Fin (m + 1) → γ) ≃ᵐ (ζ × (Fin m → γ)) × γ :=
      ((MeasurableEquiv.refl ζ).prodCongr ePi).trans eReassoc
    have hePi : ∀ ω, ePi (fun i : Fin (m + 1) ↦ As i ω) = (g ω, f ω) := by
      intro ω
      refine Prod.ext rfl ?_
      funext j
      show As ((Fin.last m).succAbove j) ω = As j.castSucc ω
      rw [Fin.succAbove_last]
    have heq : (fun ω ↦ e (Z ω, fun i : Fin (m + 1) ↦ As i ω))
        = fun ω ↦ ((Z ω, f ω), g ω) := by
      funext ω
      show eReassoc (Z ω, ePi (fun i ↦ As i ω)) = ((Z ω, f ω), g ω)
      rw [hePi ω]
      rfl
    have h_reshape :
        mutualInfo μ (fun ω ↦ ((Z ω, f ω), g ω)) C
          = mutualInfo μ (fun ω ↦ (Z ω, fun i : Fin (m + 1) ↦ As i ω)) C := by
      have h := mutualInfo_map_left_measurableEquiv μ
        (fun ω ↦ (Z ω, fun i : Fin (m + 1) ↦ As i ω)) C hZpi hC e
      rwa [heq] at h
    rw [← h_reshape, mutualInfo_chain_rule μ g C (fun ω ↦ (Z ω, f ω)) hg hC (hZ.prodMk hf)]
    -- Apply IH to the prefix `f = A^{<m} = fun i ↦ As i.castSucc`.
    have IH' := IH (fun i ω ↦ As i.castSucc ω) (fun i ↦ hAs i.castSucc)
    have hIH_lhs :
        mutualInfo μ (fun ω ↦ (Z ω, f ω)) C
          = mutualInfo μ (fun ω ↦ (Z ω, fun (j : Fin m) ↦ As j.castSucc ω)) C := rfl
    rw [hIH_lhs, IH', add_assoc, Fin.sum_univ_castSucc]
    refine congrArg₂ (· + ·) rfl (congrArg₂ (· + ·) ?_ ?_)
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rfl
    · -- last summand matches `condMutualInfo μ g C (Z, f)`.
      rfl

/-- Conditional prefix chain rule:
`I(A^{<m}; C | Z) = ∑_{k<m} I(A_k; C | (Z, A^{<k}))`.

Derived from the additive form by cancelling the common term `I(Z; C)` (requires it finite). -/
theorem condMutualInfo_prefix_chain_rule
    {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (As : Fin m → Ω → γ) (C : Ω → δ) (Z : Ω → ζ)
    (hAs : ∀ i, Measurable (As i)) (hC : Measurable C) (hZ : Measurable Z)
    (hZC : mutualInfo μ Z C ≠ ∞) :
    condMutualInfo μ (fun ω (j : Fin m) ↦ As j ω) C Z
      = ∑ k : Fin m,
          condMutualInfo μ (As k) C
            (fun ω ↦ (Z ω,
              fun (j : Fin k.val) ↦ As ⟨j.val, j.isLt.trans k.isLt⟩ ω)) := by
  have hApi : Measurable (fun ω (j : Fin m) ↦ As j ω) := measurable_pi_iff.mpr hAs
  have h_add := mutualInfo_prefix_chain_rule_add μ As C Z hAs hC hZ
  have h_2var := mutualInfo_chain_rule μ (fun ω (j : Fin m) ↦ As j ω) C Z hApi hC hZ
  rw [h_2var] at h_add
  exact WithTop.add_left_cancel hZC h_add

end InformationTheory.Shannon
