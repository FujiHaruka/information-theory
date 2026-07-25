import InformationTheory.Shannon.BroadcastChannel.Marton.Setup
import InformationTheory.Shannon.RateDistortion.AchievabilityJointStrongTypicality

/-!
# Marton's inner bound — coordinate laws shared by the two receivers

The conditional AEP of the Marton ensemble is proved once per receiver, and the two proofs share
the facts about the per-coordinate law that do not see the receiver index: the singleton masses of
`martonJointDistribution`, its `(V₁, V₂)`- and `((V₁, V₂), X)`-marginals, and the identity
rewriting a sum against a pushed-forward law as a sum against the source law.  Radius monotonicity
of the strongly typical sets is collected here as well, because an assembly consuming both
receivers pins its blocks at the minimum of the two radii and has to reopen each pin at the radius
its own receiver asks for.

## Main statements

* `sum_map_real_singleton_mul` — a finite sum of a statistic against a pushed-forward law equals
  the sum of its pullback against the source law.
* `martonJointDistribution_real_singleton` — the mass the per-coordinate law puts on a quintuple
  factors as `pV{v} · K(v){x} · W(x){y}`.
* `martonJointDistribution_map_VX` — the `((V₁, V₂), X)`-marginal of the per-coordinate law is
  `pV ⊗ₘ K`.
* `marton_map_V₁V₂` — the ambient law of the auxiliary pair coordinate is `pV`.
* `stronglyTypicalSet_mono_radius` and `jointStronglyTypicalSet_mono_radius` — the strongly
  typical sets grow with the radius.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Sums against a pushed-forward law -/

lemma sum_map_real_singleton_mul {Ω γ : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → γ) (hg : Measurable g) (f : γ → ℝ) :
    ∑ c : γ, (P.map g).real {c} * f c = ∑ z : Ω, P.real {z} * f (g z) := by
  haveI : IsFiniteMeasure (P.map g) := Measure.isFiniteMeasure_map P g
  have h1 : ∫ c, f c ∂(P.map g) = ∑ c : γ, (P.map g).real {c} * f c := by
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun c _ ↦ smul_eq_mul _ _
  have h2 : ∫ c, f c ∂(P.map g) = ∫ z, f (g z) ∂P :=
    integral_map hg.aemeasurable (measurable_of_finite f).aestronglyMeasurable
  have h3 : ∫ z, f (g z) ∂P = ∑ z : Ω, P.real {z} * f (g z) := by
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun z _ ↦ smul_eq_mul _ _
  rw [← h1, h2, h3]

/-! ### Singleton masses of the per-coordinate law -/

lemma martonJointDistribution_real_singleton
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (v : V₁ × V₂) (x : α) (y : β₁ × β₂) :
    (martonJointDistribution pV K W).real {(v.1, v.2, x, y.1, y.2)}
      = pV.real {v} * (K v).real {x} * (W x).real {y} := by
  obtain ⟨v₁, v₂⟩ := v
  obtain ⟨y₁, y₂⟩ := y
  unfold martonJointDistribution
  rw [Measure.real, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
  have h_pre₂ : (MeasurableEquiv.prodAssoc ⁻¹'
      ({(v₁, v₂, x, y₁, y₂)} : Set (V₁ × V₂ × α × β₁ × β₂)))
      = ({((v₁, v₂), x, y₁, y₂)} : Set ((V₁ × V₂) × α × β₁ × β₂)) := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  have h_pre₁ : (MeasurableEquiv.prodAssoc ⁻¹'
      ({((v₁, v₂), x, y₁, y₂)} : Set ((V₁ × V₂) × α × β₁ × β₂)))
      = ({(((v₁, v₂), x), y₁, y₂)} : Set (((V₁ × V₂) × α) × β₁ × β₂)) := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre₂, h_pre₁]
  -- Split the outer compProd, then the inner one.
  have houter := jointDistribution_singleton (pV ⊗ₘ K)
    (W.comap Prod.snd measurable_snd : Kernel ((V₁ × V₂) × α) (β₁ × β₂)) ((v₁, v₂), x) (y₁, y₂)
  rw [jointDistribution_def, Kernel.comap_apply] at houter
  have hinner := jointDistribution_singleton pV K (v₁, v₂) x
  rw [jointDistribution_def] at hinner
  rw [houter, hinner, ENNReal.toReal_mul, ENNReal.toReal_mul]
  rfl

/-! ### Marginals of the per-coordinate law -/

lemma martonJointDistribution_map_VX
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonJointDistribution pV K W).map (fun q ↦ ((q.1, q.2.1), q.2.2.1)) = pV ⊗ₘ K := by
  have hmeas : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ ((q.1, q.2.1), q.2.2.1)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  unfold martonJointDistribution
  rw [Measure.map_map hmeas MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (hmeas.comp MeasurableEquiv.prodAssoc.measurable)
      MeasurableEquiv.prodAssoc.measurable]
  have hcomp : ((fun q : V₁ × V₂ × α × β₁ × β₂ ↦ ((q.1, q.2.1), q.2.2.1)) ∘
      (MeasurableEquiv.prodAssoc : ((V₁ × V₂) × α × β₁ × β₂) ≃ᵐ (V₁ × V₂ × α × β₁ × β₂))) ∘
      (MeasurableEquiv.prodAssoc : (((V₁ × V₂) × α) × β₁ × β₂) ≃ᵐ ((V₁ × V₂) × α × β₁ × β₂))
      = Prod.fst := rfl
  rw [hcomp]
  exact Measure.fst_compProd _ _

lemma marton_map_V₁V₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (jointSequence martonV₁s martonV₂s 0) = pV := by
  have h : (martonAmbientMeasure pV K W).map (jointSequence martonV₁s martonV₂s 0)
      = (martonJointDistribution pV K W).map (fun q ↦ (q.1, q.2.1)) :=
    martonAmbient_map_coord pV K W (fun q ↦ (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) 0
  rw [h, martonJointDistribution_map_V pV K W]

/-! ### Radius monotonicity of the strongly typical sets -/

section RadiusMonotone

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]
variable {δ : Type*} [Fintype δ] [DecidableEq δ] [Nonempty δ]
  [MeasurableSpace δ] [MeasurableSingletonClass δ]

lemma stronglyTypicalSet_mono_radius
    (μ : Measure Ω) (Xs : ℕ → Ω → γ) (n : ℕ) {ε ε' : ℝ} (hε : ε ≤ ε') :
    stronglyTypicalSet μ Xs n ε ⊆ stronglyTypicalSet μ Xs n ε' :=
  fun _ hx a ↦ le_trans (hx a) hε

lemma jointStronglyTypicalSet_mono_radius
    (μ : Measure Ω) (Xs : ℕ → Ω → γ) (Ys : ℕ → Ω → δ) (n : ℕ) {ε ε' : ℝ} (hε : ε ≤ ε') :
    jointStronglyTypicalSet μ Xs Ys n ε ⊆ jointStronglyTypicalSet μ Xs Ys n ε' :=
  fun _ hp ↦ stronglyTypicalSet_mono_radius μ (jointSequence Xs Ys) n hε hp

end RadiusMonotone

end InformationTheory.Shannon.BroadcastChannel.Marton
