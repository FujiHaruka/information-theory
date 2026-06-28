import InformationTheory.Shannon.MultipleAccess.JointTypicality
import InformationTheory.Shannon.IIDProductInput.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# i.i.d. ambient measure for the multiple access channel

This file provides the i.i.d. ambient probability space for the two-user MAC
achievability theorem, the MAC analogue of
`InformationTheory/Shannon/IIDProductInput/Basic.lean`.

## Construction

Given two input distributions `p₁ : Measure α₁`, `p₂ : Measure α₂` (independent,
the product `p₁ ⊗ p₂`) and a MAC channel `W : MACChannel α₁ α₂ β = Kernel (α₁ × α₂) β`,
the per-coordinate joint law is

`macJointDistribution p₁ p₂ W := (jointDistribution (p₁.prod p₂) W).map prodAssoc`

on `α₁ × α₂ × β` (the channel-coding joint `(p₁ ⊗ p₂) ⊗ₘ W` on `(α₁ × α₂) × β`,
reshaped to the right-nested triple).  The ambient space is `Ω := ℕ → α₁ × α₂ × β`
with `μ := Measure.infinitePi (fun _ : ℕ => macJointDistribution p₁ p₂ W)`, and the
three coordinate projections

* `macX1s i ω := (ω i).1`
* `macX2s i ω := (ω i).2.1`
* `macYs  i ω := (ω i).2.2`

supply all the `iIndepFun` / `IdentDistrib` / positivity regularity hypotheses that
the gateway atoms `macJTS_indep_prob_le_X1`/`_X2`/`_both` and the correct-pair AEP
`macJointlyTypicalSet_prob_tendsto_one` demand.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

variable {α₁ α₂ β : Type*}
  [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-! ### Per-coordinate joint distribution -/

/-- The per-coordinate MAC joint law on `α₁ × α₂ × β`: the channel-coding joint
`(p₁ ⊗ p₂) ⊗ₘ W` on `(α₁ × α₂) × β` reshaped to the right-nested triple. -/
noncomputable def macJointDistribution
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) :
    Measure (α₁ × α₂ × β) :=
  (jointDistribution (p₁.prod p₂) W).map (MeasurableEquiv.prodAssoc)

instance macJointDistribution.instIsProbabilityMeasure
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    IsProbabilityMeasure (macJointDistribution p₁ p₂ W) := by
  unfold macJointDistribution
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.prodAssoc.measurable.aemeasurable)

/-! ### Ambient measure on `ℕ → α₁ × α₂ × β` -/

/-- The i.i.d. MAC ambient measure: `Measure.infinitePi (fun _ => macJointDistribution p₁ p₂ W)`. -/
noncomputable def macAmbientMeasure
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) :
    Measure (ℕ → α₁ × α₂ × β) :=
  Measure.infinitePi (fun _ : ℕ ↦ macJointDistribution p₁ p₂ W)

instance macAmbientMeasure.instIsProbabilityMeasure
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    IsProbabilityMeasure (macAmbientMeasure p₁ p₂ W) := by
  unfold macAmbientMeasure
  infer_instance

/-- The first input coordinate `ω ↦ (ω i).1`. -/
def macX1s : ℕ → (ℕ → α₁ × α₂ × β) → α₁ := fun i ω ↦ (ω i).1

/-- The second input coordinate `ω ↦ (ω i).2.1`. -/
def macX2s : ℕ → (ℕ → α₁ × α₂ × β) → α₂ := fun i ω ↦ (ω i).2.1

/-- The output coordinate `ω ↦ (ω i).2.2`. -/
def macYs : ℕ → (ℕ → α₁ × α₂ × β) → β := fun i ω ↦ (ω i).2.2

omit [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] in
@[simp] lemma macX1s_apply (i : ℕ) (ω : ℕ → α₁ × α₂ × β) : macX1s i ω = (ω i).1 := rfl

omit [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] in
@[simp] lemma macX2s_apply (i : ℕ) (ω : ℕ → α₁ × α₂ × β) : macX2s i ω = (ω i).2.1 := rfl

omit [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] in
@[simp] lemma macYs_apply (i : ℕ) (ω : ℕ → α₁ × α₂ × β) : macYs i ω = (ω i).2.2 := rfl

lemma measurable_macX1s (i : ℕ) : Measurable (macX1s (α₁ := α₁) (α₂ := α₂) (β := β) i) :=
  (measurable_pi_apply i).fst

lemma measurable_macX2s (i : ℕ) : Measurable (macX2s (α₁ := α₁) (α₂ := α₂) (β := β) i) :=
  (measurable_pi_apply i).snd.fst

lemma measurable_macYs (i : ℕ) : Measurable (macYs (α₁ := α₁) (α₂ := α₂) (β := β) i) :=
  (measurable_pi_apply i).snd.snd

/-! ### Generic coordinate-selector map / independence / positivity

Every random variable consumed by the gateway atoms and the AEP has the form
`fun ω ↦ g (ω i)` for a measurable coordinate selector `g : α₁ × α₂ × β → γ`. -/

/-- The map of a coordinate selector under the ambient measure equals the map of the
selector under the per-coordinate joint law. -/
lemma macAmbient_map_coord {γ : Type*} [MeasurableSpace γ]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (g : α₁ × α₂ × β → γ) (hg : Measurable g) (i : ℕ) :
    (macAmbientMeasure p₁ p₂ W).map (fun ω ↦ g (ω i))
      = (macJointDistribution p₁ p₂ W).map g := by
  have h_comp : (fun ω : ℕ → α₁ × α₂ × β ↦ g (ω i)) = g ∘ (fun ω ↦ ω i) := rfl
  rw [h_comp, ← Measure.map_map hg (measurable_pi_apply i)]
  congr 1
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ macJointDistribution p₁ p₂ W) i

/-- Mutual independence of any coordinate selector under the ambient measure. -/
lemma macAmbient_iIndepFun_coord {γ : Type*} [MeasurableSpace γ]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (g : α₁ × α₂ × β → γ) (hg : Measurable g) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → α₁ × α₂ × β) ↦ g (ω i)) (macAmbientMeasure p₁ p₂ W) :=
  iIndepFun_infinitePi (P := fun _ : ℕ ↦ macJointDistribution p₁ p₂ W)
    (X := fun _ : ℕ ↦ g) (fun _ ↦ hg)

/-- Pairwise independence of any coordinate selector. -/
lemma macAmbient_pairwise_coord {γ : Type*} [MeasurableSpace γ]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (g : α₁ × α₂ × β → γ) (hg : Measurable g) :
    Pairwise fun i j ↦
      IndepFun (fun ω : ℕ → α₁ × α₂ × β ↦ g (ω i)) (fun ω ↦ g (ω j))
        (macAmbientMeasure p₁ p₂ W) := by
  intro i j hij
  exact (macAmbient_iIndepFun_coord p₁ p₂ W g hg).indepFun hij

/-- Identical distribution of a coordinate selector across indices. -/
lemma macAmbient_identDistrib_coord {γ : Type*} [MeasurableSpace γ]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (g : α₁ × α₂ × β → γ) (hg : Measurable g) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → α₁ × α₂ × β ↦ g (ω i)) (fun ω ↦ g (ω 0))
      (macAmbientMeasure p₁ p₂ W) (macAmbientMeasure p₁ p₂ W) where
  aemeasurable_fst := (hg.comp (measurable_pi_apply i)).aemeasurable
  aemeasurable_snd := (hg.comp (measurable_pi_apply 0)).aemeasurable
  map_eq := by
    rw [macAmbient_map_coord p₁ p₂ W g hg i, macAmbient_map_coord p₁ p₂ W g hg 0]

/-- Entropy of a coordinate selector under the ambient measure equals its entropy
under the per-coordinate joint law. -/
lemma macAmbient_entropy_coord {γ : Type*}
    [Fintype γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (g : α₁ × α₂ × β → γ) (hg : Measurable g) (i : ℕ) :
    entropy (macAmbientMeasure p₁ p₂ W) (fun ω ↦ g (ω i))
      = entropy (macJointDistribution p₁ p₂ W) g := by
  refine entropy_eq_of_identDistrib (macAmbientMeasure p₁ p₂ W)
    (macJointDistribution p₁ p₂ W) (fun ω ↦ g (ω i)) g ?_
  refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable, hg.aemeasurable, ?_⟩
  rw [macAmbient_map_coord p₁ p₂ W g hg i]

/-! ### Positivity of the per-coordinate joint law and coordinate marginals -/

section Positivity

variable [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂] in
/-- The product input law has positive singleton mass. -/
lemma prod_real_singleton_pos
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (q : α₁ × α₂) :
    0 < (p₁.prod p₂).real {q} := by
  obtain ⟨a₁, a₂⟩ := q
  have h_sgl : ({(a₁, a₂)} : Set (α₁ × α₂)) = ({a₁} : Set α₁) ×ˢ ({a₂} : Set α₂) := by
    ext ⟨x, y⟩; simp [Prod.ext_iff]
  rw [h_sgl, measureReal_prod_prod]
  exact mul_pos (hp₁ a₁) (hp₂ a₂)

omit [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq α₁] [Nonempty α₁]
  [DecidableEq α₂] [Nonempty α₂] in
/-- The per-coordinate MAC joint law has positive singleton mass. -/
lemma macJointDistribution_real_singleton_pos
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    (q : α₁ × α₂ × β) :
    0 < (macJointDistribution p₁ p₂ W).real {q} := by
  obtain ⟨a₁, a₂, b⟩ := q
  -- macJointDistribution = (jointDistribution (p₁.prod p₂) W).map prodAssoc.
  unfold macJointDistribution
  rw [Measure.real,
    Measure.map_apply MeasurableEquiv.prodAssoc.measurable (measurableSet_singleton _)]
  -- prodAssoc ⁻¹' {(a₁, a₂, b)} = {((a₁, a₂), b)}.
  have h_pre : (MeasurableEquiv.prodAssoc ⁻¹' ({(a₁, a₂, b)} : Set (α₁ × α₂ × β)))
      = ({((a₁, a₂), b)} : Set ((α₁ × α₂) × β)) := by
    ext ⟨⟨x, y⟩, z⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre]
  -- Reduce to positivity of jointDistribution (p₁.prod p₂) W.
  have h_pos :=
    jointDistribution_singleton_pos (p₁.prod p₂) W
      (prod_real_singleton_pos p₁ p₂ hp₁ hp₂) hW ((a₁, a₂)) b
  rw [Measure.real] at h_pos
  exact h_pos

omit [DecidableEq α₁] [Nonempty α₁] [DecidableEq α₂] [Nonempty α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] in
/-- Positivity of any coordinate-selector marginal singleton, reduced to the
per-coordinate joint positivity via a chosen fiber witness. -/
lemma macAmbient_map_coord_real_singleton_pos {γ : Type*}
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    (g : α₁ × α₂ × β → γ) (hg : Measurable g) (i : ℕ)
    (q : γ) (r : α₁ × α₂ × β) (hr : g r = q) :
    0 < ((macAmbientMeasure p₁ p₂ W).map (fun ω ↦ g (ω i))).real {q} := by
  rw [macAmbient_map_coord p₁ p₂ W g hg i, Measure.real,
    Measure.map_apply hg (measurableSet_singleton q)]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  have hsub : ({r} : Set (α₁ × α₂ × β)) ⊆ g ⁻¹' {q} := by
    intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; simp [hr]
  have hpos : 0 < macJointDistribution p₁ p₂ W {r} := by
    have := macJointDistribution_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW r
    rw [Measure.real] at this
    exact ENNReal.toReal_pos_iff.mp this |>.1
  exact (lt_of_lt_of_le hpos (measure_mono hsub)).ne'

end Positivity

end InformationTheory.Shannon.MAC
