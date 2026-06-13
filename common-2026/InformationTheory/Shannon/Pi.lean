import InformationTheory.Shannon.Entropy

/-!
# Shared Pi-type plumbing for Shannon information theory

`MeasurableEquiv` invariance of entropy/condEntropy under re-indexing of Pi-type random
variables, together with `condEntropy ≥ 0` and subset-split measurable equivalences.

## Main definitions

* `subsetSplitMEquivAux` — `((↥T₁ → α) × (↥R → α)) ≃ᵐ (↥U → α)` for disjoint `T₁, R`
  with `T₁ ∪ R = U`.

## Main statements

* `entropy_measurableEquiv_comp` — `entropy μ (e ∘ X) = entropy μ X`.
* `condEntropy_measurableEquiv_comp` — `condEntropy μ Xc (e ∘ Yo) = condEntropy μ Xc Yo`.
* `condEntropy_nonneg` — `0 ≤ H(W | Y)`.

## Implementation notes

`MeasurableEquiv.coe_piFinsetUnion`, `piFinsetUnion_apply_left/right` lift
`Equiv.piFinsetUnion_left/_right` into the `MeasurableEquiv` namespace for use in
Pi-type reshape proofs across the Shannon moonshot files.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

lemma entropy_measurableEquiv_comp
    {β γ : Type*}
    [Fintype β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure Ω) (Xs : Ω → β) (hXs : Measurable Xs) (e : β ≃ᵐ γ) :
    entropy μ (fun ω => e (Xs ω)) = entropy μ Xs := by
  unfold entropy
  refine (Fintype.sum_equiv e.toEquiv
    (fun x => Real.negMulLog ((μ.map Xs).real {x}))
    (fun y => Real.negMulLog ((μ.map (fun ω => e (Xs ω))).real {y}))
    ?_).symm
  intro x
  have hpre : (e : β → γ) ⁻¹' {e x} = {x} := by
    ext y
    simp [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff, eq_comm]
  show Real.negMulLog ((μ.map Xs).real {x})
      = Real.negMulLog ((μ.map (fun ω => e (Xs ω))).real {(e.toEquiv x : γ)})
  congr 1
  rw [show (e.toEquiv x : γ) = e x from rfl,
      show (fun ω => e (Xs ω)) = (e : β → γ) ∘ Xs from rfl,
      ← Measure.map_map e.measurable hXs,
      measureReal_def, measureReal_def,
      Measure.map_apply e.measurable (measurableSet_singleton _),
      hpre]

omit [DecidableEq α] in
lemma condEntropy_measurableEquiv_comp
    {β γ : Type*}
    [Fintype β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xc : Ω → α) (hXc : Measurable Xc)
    (Yo : Ω → β) (hYo : Measurable Yo) (e : β ≃ᵐ γ) :
    InformationTheory.MeasureFano.condEntropy μ Xc (fun ω => e (Yo ω))
      = InformationTheory.MeasureFano.condEntropy μ Xc Yo := by
  classical
  -- H(Yo, Xc) = H(Yo) + H(Xc | Yo)
  have h₁ := entropy_pair_eq_entropy_add_condEntropy μ Yo Xc hYo hXc
  -- H(e∘Yo, Xc) = H(e∘Yo) + H(Xc | e∘Yo)
  have h₂ := entropy_pair_eq_entropy_add_condEntropy μ
    (fun ω => e (Yo ω)) Xc (e.measurable.comp hYo) hXc
  -- H(e∘Yo) = H(Yo)
  have hY := entropy_measurableEquiv_comp μ Yo hYo e
  -- H(e∘Yo, Xc) = H(Yo, Xc) via the prod equiv (e × refl α)
  have hYX :
      entropy μ (fun ω => (e (Yo ω), Xc ω))
        = entropy μ (fun ω => (Yo ω, Xc ω)) := by
    have := entropy_measurableEquiv_comp μ
      (fun ω => (Yo ω, Xc ω)) (hYo.prodMk hXc)
      (MeasurableEquiv.prodCongr e (.refl α))
    simpa using this
  linarith

/-! ## Basic inequality for conditional entropy -/

theorem condEntropy_nonneg
    {W : Type*} [Fintype W] [Nonempty W]
      [MeasurableSpace W] [MeasurableSingletonClass W]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ws : Ω → W) (Yo : Ω → Y) :
    0 ≤ InformationTheory.MeasureFano.condEntropy μ Ws Yo := by
  unfold InformationTheory.MeasureFano.condEntropy
  refine integral_nonneg fun y => ?_
  refine Finset.sum_nonneg fun x _ => ?_
  exact Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-! ## Subset reshape index equivalences -/

@[simp] lemma _root_.MeasurableEquiv.coe_piFinsetUnion
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t) :
    ⇑(MeasurableEquiv.piFinsetUnion (π := β) h) = Equiv.piFinsetUnion β h := rfl

lemma _root_.MeasurableEquiv.piFinsetUnion_apply_left
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t)
    {f : ∀ i : s, β i} {g : ∀ i : t, β i}
    {i : ι} (hi : i ∈ s) (hi' : i ∈ s ∪ t) :
    MeasurableEquiv.piFinsetUnion (π := β) h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
  rw [MeasurableEquiv.coe_piFinsetUnion]
  exact Equiv.piFinsetUnion_left β h hi hi'

lemma _root_.MeasurableEquiv.piFinsetUnion_apply_right
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t)
    {f : ∀ i : s, β i} {g : ∀ i : t, β i}
    {i : ι} (hi : i ∈ t) (hi' : i ∈ s ∪ t) :
    MeasurableEquiv.piFinsetUnion (π := β) h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩ := by
  rw [MeasurableEquiv.coe_piFinsetUnion]
  exact Equiv.piFinsetUnion_right β h hi hi'

/-- The measurable equivalence `((↥T₁ → α) × (↥R → α)) ≃ᵐ (↥U → α)` for disjoint `T₁, R`
with `T₁ ∪ R = U`. Composed from `MeasurableEquiv.piFinsetUnion` and `MeasurableEquiv.cast`. -/
def subsetSplitMEquivAux {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {T₁ R U : Finset ι}
    (hd : Disjoint T₁ R) (hU : T₁ ∪ R = U) :
    (((i : T₁) → β i) × ((i : R) → β i)) ≃ᵐ ((i : U) → β i) :=
  (MeasurableEquiv.piFinsetUnion (π := β) hd).trans
    (MeasurableEquiv.cast (by rw [hU]) (by rw [hU]))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma subsetSplitMEquivAux_apply
    {n : ℕ} {T₁ R U : Finset (Fin n)}
    (hd : Disjoint T₁ R) (hU : T₁ ∪ R = U) (Xs : Fin n → α) :
    subsetSplitMEquivAux (β := fun _ : Fin n => α) hd hU
      (fun j : ↥T₁ => Xs j.val, fun j : ↥R => Xs j.val)
      = fun j : ↥U => Xs j.val := by
  subst hU
  funext k
  obtain ⟨j, hj⟩ := k
  show ((MeasurableEquiv.piFinsetUnion (π := fun _ : Fin n => α) hd).trans
      (MeasurableEquiv.cast rfl HEq.rfl)
      (fun j : ↥T₁ => Xs j.val, fun j : ↥R => Xs j.val)) ⟨j, hj⟩ = Xs j
  -- The cast over `rfl` is the identity on values.
  by_cases hjT₁ : j ∈ T₁
  · exact MeasurableEquiv.piFinsetUnion_apply_left
      (β := fun _ : Fin n => α) hd hjT₁ hj
  · have hjR : j ∈ R := (Finset.mem_union.mp hj).resolve_left hjT₁
    exact MeasurableEquiv.piFinsetUnion_apply_right
      (β := fun _ : Fin n => α) hd hjR hj

end InformationTheory.Shannon
