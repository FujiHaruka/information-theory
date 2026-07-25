import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.Entropy
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Basic.Converse
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
# Marton's inner bound — five-variable ambient setup

The random-coding ensemble behind Marton's inner bound carries a *pair* of auxiliary variables
`(V₁, V₂)`, one per receiver, so the per-coordinate law is a quintuple `(V₁, V₂, X, Y₁, Y₂)`
rather than the quadruple `(U, X, Y₁, Y₂)` of superposition coding.  This file builds that law
from a joint auxiliary distribution `pV` on `V₁ × V₂`, an input kernel `K : Kernel (V₁ × V₂) α`
and a broadcast channel `W`, together with its i.i.d. ambient measure, the coordinate facts
consumed downstream, and the three informations appearing in the region inequalities.

The input is produced by a general kernel `K` rather than a deterministic map `x = f(v₁, v₂)`:
a deterministic kernel puts zero mass off its image, which is incompatible with the full-support
hypotheses `hpV` / `hK` / `hW` that every typicality bound in this development requires.

## Main definitions

* `martonJointDistribution pV K W` — the per-coordinate law on `V₁ × V₂ × α × β₁ × β₂`.
* `martonAmbientMeasure pV K W` — its i.i.d. ambient measure on `ℕ → V₁ × V₂ × α × β₁ × β₂`.
* `martonInfo₁` / `martonInfo₂` / `martonInfoV₁V₂` — the informations `I(V₁; Y₁)`, `I(V₂; Y₂)`
  and `I(V₁; V₂)` of the per-coordinate law, in entropy-difference form.

## Implementation notes

The informations are entropy differences over `ℝ` rather than `InformationTheory.Shannon.mutualInfo`
(valued in `ℝ≥0∞`), matching the form in which the typicality bounds of this development state
their exponents.
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

/-! ### Per-coordinate joint distribution -/

/-- The per-coordinate Marton joint law on `V₁ × V₂ × α × β₁ × β₂`: the compProd chain
`pV → K → W` (`(V₁, V₂) ∼ pV`, `X ∣ (V₁, V₂) ∼ K`, `(Y₁, Y₂) ∣ X ∼ W`), reshaped from the
left-nested `((V₁ × V₂) × α) × (β₁ × β₂)` to the right-nested quintuple.  Two reassociations
are needed, one more than for the four-variable superposition law. -/
noncomputable def martonJointDistribution
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    Measure (V₁ × V₂ × α × β₁ × β₂) :=
  (((pV ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map
      MeasurableEquiv.prodAssoc).map MeasurableEquiv.prodAssoc

instance martonJointDistribution.instIsProbabilityMeasure
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (martonJointDistribution pV K W) := by
  unfold martonJointDistribution
  haveI : IsProbabilityMeasure
      (((pV ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map
        MeasurableEquiv.prodAssoc) :=
    Measure.isProbabilityMeasure_map MeasurableEquiv.prodAssoc.measurable.aemeasurable
  exact Measure.isProbabilityMeasure_map MeasurableEquiv.prodAssoc.measurable.aemeasurable

lemma martonJointDistribution_map_V
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonJointDistribution pV K W).map (fun q ↦ (q.1, q.2.1)) = pV := by
  have hmeas : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  unfold martonJointDistribution
  rw [Measure.map_map hmeas MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map (hmeas.comp MeasurableEquiv.prodAssoc.measurable)
      MeasurableEquiv.prodAssoc.measurable]
  have hcomp : ((fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) ∘
      (MeasurableEquiv.prodAssoc : ((V₁ × V₂) × α × β₁ × β₂) ≃ᵐ (V₁ × V₂ × α × β₁ × β₂))) ∘
      (MeasurableEquiv.prodAssoc : (((V₁ × V₂) × α) × β₁ × β₂) ≃ᵐ ((V₁ × V₂) × α × β₁ × β₂))
      = Prod.fst ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst]
  have h1 : ((pV ⊗ₘ K) ⊗ₘ
      (W.comap Prod.snd measurable_snd : Kernel ((V₁ × V₂) × α) (β₁ × β₂))).map Prod.fst
      = pV ⊗ₘ K := Measure.fst_compProd _ _
  have h2 : (pV ⊗ₘ K).map Prod.fst = pV := Measure.fst_compProd _ _
  rw [h1, h2]

lemma martonJointDistribution_singleton_pos
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (q : V₁ × V₂ × α × β₁ × β₂) :
    0 < (martonJointDistribution pV K W).real {q} := by
  obtain ⟨v₁, v₂, x, y⟩ := q
  unfold martonJointDistribution
  rw [Measure.real, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
  have h_pre₂ : (MeasurableEquiv.prodAssoc ⁻¹'
      ({(v₁, v₂, x, y)} : Set (V₁ × V₂ × α × β₁ × β₂)))
      = ({((v₁, v₂), x, y)} : Set ((V₁ × V₂) × α × β₁ × β₂)) := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  have h_pre₁ : (MeasurableEquiv.prodAssoc ⁻¹'
      ({((v₁, v₂), x, y)} : Set ((V₁ × V₂) × α × β₁ × β₂)))
      = ({(((v₁, v₂), x), y)} : Set (((V₁ × V₂) × α) × β₁ × β₂)) := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre₂, h_pre₁]
  have hVXpos : ∀ p : (V₁ × V₂) × α, 0 < (pV ⊗ₘ K).real {p} := by
    rintro ⟨v, a⟩
    have := jointDistribution_singleton_pos pV K hpV hK v a
    rwa [jointDistribution_def] at this
  have hW'pos : ∀ p : (V₁ × V₂) × α, ∀ b : β₁ × β₂,
      0 < ((W.comap Prod.snd measurable_snd : Kernel ((V₁ × V₂) × α) (β₁ × β₂)) p).real {b} := by
    rintro ⟨v, a⟩ b
    rw [Kernel.comap_apply]
    exact hW a b
  have h_pos := jointDistribution_singleton_pos (pV ⊗ₘ K)
    (W.comap Prod.snd measurable_snd : Kernel ((V₁ × V₂) × α) (β₁ × β₂)) hVXpos hW'pos
    ((v₁, v₂), x) y
  rw [jointDistribution_def, Measure.real] at h_pos
  exact h_pos

/-! ### I.i.d. ambient measure on `ℕ → V₁ × V₂ × α × β₁ × β₂` -/

/-- The i.i.d. Marton ambient measure:
`Measure.infinitePi (fun _ => martonJointDistribution pV K W)`. -/
noncomputable def martonAmbientMeasure
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    Measure (ℕ → V₁ × V₂ × α × β₁ × β₂) :=
  Measure.infinitePi (fun _ : ℕ ↦ martonJointDistribution pV K W)

instance martonAmbientMeasure.instIsProbabilityMeasure
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (martonAmbientMeasure pV K W) := by
  unfold martonAmbientMeasure
  infer_instance

/-- The first auxiliary coordinate `ω ↦ (ω i).1`. -/
def martonV₁s : ℕ → (ℕ → V₁ × V₂ × α × β₁ × β₂) → V₁ := fun i ω ↦ (ω i).1

/-- The second auxiliary coordinate `ω ↦ (ω i).2.1`. -/
def martonV₂s : ℕ → (ℕ → V₁ × V₂ × α × β₁ × β₂) → V₂ := fun i ω ↦ (ω i).2.1

/-- The channel input coordinate `ω ↦ (ω i).2.2.1`. -/
def martonXs : ℕ → (ℕ → V₁ × V₂ × α × β₁ × β₂) → α := fun i ω ↦ (ω i).2.2.1

/-- The first output coordinate `ω ↦ (ω i).2.2.2.1`. -/
def martonY₁s : ℕ → (ℕ → V₁ × V₂ × α × β₁ × β₂) → β₁ := fun i ω ↦ (ω i).2.2.2.1

/-- The second output coordinate `ω ↦ (ω i).2.2.2.2`. -/
def martonY₂s : ℕ → (ℕ → V₁ × V₂ × α × β₁ × β₂) → β₂ := fun i ω ↦ (ω i).2.2.2.2

/-! ### Coordinate facts for the Marton ambient measure -/

lemma martonAmbient_map_coord {γ : Type*} [MeasurableSpace γ]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : V₁ × V₂ × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) :
    (martonAmbientMeasure pV K W).map (fun ω ↦ g (ω i))
      = (martonJointDistribution pV K W).map g := by
  have h_comp : (fun ω : ℕ → V₁ × V₂ × α × β₁ × β₂ ↦ g (ω i)) = g ∘ (fun ω ↦ ω i) := rfl
  rw [h_comp, ← Measure.map_map hg (measurable_pi_apply i)]
  congr 1
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ martonJointDistribution pV K W) i

lemma martonAmbient_iIndepFun_coord {γ : Type*} [MeasurableSpace γ]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : V₁ × V₂ × α × β₁ × β₂ → γ) (hg : Measurable g) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → V₁ × V₂ × α × β₁ × β₂) ↦ g (ω i))
      (martonAmbientMeasure pV K W) :=
  iIndepFun_infinitePi (P := fun _ : ℕ ↦ martonJointDistribution pV K W)
    (X := fun _ : ℕ ↦ g) (fun _ ↦ hg)

lemma martonAmbient_identDistrib_coord {γ : Type*} [MeasurableSpace γ]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : V₁ × V₂ × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → V₁ × V₂ × α × β₁ × β₂ ↦ g (ω i)) (fun ω ↦ g (ω 0))
      (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) where
  aemeasurable_fst := (hg.comp (measurable_pi_apply i)).aemeasurable
  aemeasurable_snd := (hg.comp (measurable_pi_apply 0)).aemeasurable
  map_eq := by
    rw [martonAmbient_map_coord pV K W g hg i, martonAmbient_map_coord pV K W g hg 0]

lemma martonAmbient_entropy_coord {γ : Type*}
    [Fintype γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : V₁ × V₂ × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) :
    entropy (martonAmbientMeasure pV K W) (fun ω ↦ g (ω i))
      = entropy (martonJointDistribution pV K W) g := by
  refine entropy_eq_of_identDistrib (martonAmbientMeasure pV K W)
    (martonJointDistribution pV K W) (fun ω ↦ g (ω i)) g ?_
  refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable, hg.aemeasurable, ?_⟩
  rw [martonAmbient_map_coord pV K W g hg i]

lemma martonAmbient_coord_marginal_pos {γ : Type*}
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (g : V₁ × V₂ × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ)
    (c : γ) (r : V₁ × V₂ × α × β₁ × β₂) (hr : g r = c) :
    0 < ((martonAmbientMeasure pV K W).map (fun ω ↦ g (ω i))).real {c} := by
  rw [martonAmbient_map_coord pV K W g hg i, Measure.real,
    Measure.map_apply hg (measurableSet_singleton c)]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  have hsub : ({r} : Set (V₁ × V₂ × α × β₁ × β₂)) ⊆ g ⁻¹' {c} := by
    intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz; simp [hr]
  have hpos : 0 < martonJointDistribution pV K W {r} := by
    have := martonJointDistribution_singleton_pos pV K W hpV hK hW r
    rw [Measure.real] at this
    exact ENNReal.toReal_pos_iff.mp this |>.1
  exact (lt_of_lt_of_le hpos (measure_mono hsub)).ne'

/-! ### The three informations of the region inequalities -/

/-- The first-receiver information `I(V₁; Y₁) = H(V₁) + H(Y₁) − H(V₁, Y₁)` of the
per-coordinate Marton joint law. -/
noncomputable def martonInfo₁
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (martonJointDistribution pV K W) Prod.fst
    + entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.1)
    - entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.2.2.1))

/-- The second-receiver information `I(V₂; Y₂) = H(V₂) + H(Y₂) − H(V₂, Y₂)` of the
per-coordinate Marton joint law. -/
noncomputable def martonInfo₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1)
    + entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.2)
    - entropy (martonJointDistribution pV K W) (fun q ↦ (q.2.1, q.2.2.2.2))

/-- The auxiliary-variable dependence `I(V₁; V₂) = H(V₁) + H(V₂) − H(V₁, V₂)` of the
per-coordinate Marton joint law.  This is the penalty subtracted from the sum rate: it is the
rate at which the two subcodebooks have to be over-provisioned for a jointly typical pair to
exist. -/
noncomputable def martonInfoV₁V₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (martonJointDistribution pV K W) Prod.fst
    + entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1)
    - entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.1))

private lemma entropy_diff_eq_zero_of_indepFun {Ω γ δ : Type*} [MeasurableSpace Ω]
    [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ] [MeasurableSpace δ] [MeasurableSingletonClass δ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → γ) (Y : Ω → δ) (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    entropy μ X + entropy μ Y - entropy μ (fun ω ↦ (X ω, Y ω)) = 0 := by
  rw [entropy_pair_eq_entropy_add_condEntropy μ X Y hX hY,
    condEntropy_eq_entropy_of_indepFun μ Y X hY hX h.symm]
  ring

lemma martonInfo₁_eq_zero_of_subsingleton [Subsingleton V₁]
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfo₁ pV K W = 0 := by
  have hX : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hY : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hconst : IndepFun (fun _ : V₁ × V₂ × α × β₁ × β₂ ↦ (Classical.arbitrary V₁))
      (fun q ↦ q.2.2.2.1) (martonJointDistribution pV K W) :=
    indepFun_const_left _ _
  have hindep := hconst.congr
    (Filter.Eventually.of_forall fun q ↦ Subsingleton.elim (Classical.arbitrary V₁) q.1)
    (Filter.EventuallyEq.refl _ _)
  exact entropy_diff_eq_zero_of_indepFun (martonJointDistribution pV K W) _ _ hX hY hindep

lemma martonInfoV₁V₂_eq_zero_of_prod
    (p₁ : Measure V₁) [IsProbabilityMeasure p₁] (p₂ : Measure V₂) [IsProbabilityMeasure p₂]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonInfoV₁V₂ (p₁.prod p₂) K W = 0 := by
  have hX : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hY : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hpair : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) := hX.prodMk hY
  have hmap := martonJointDistribution_map_V (p₁.prod p₂) K W
  have hfst : (martonJointDistribution (p₁.prod p₂) K W).map
      (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) = p₁ := by
    have hsplit : (martonJointDistribution (p₁.prod p₂) K W).map
        (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁)
        = ((martonJointDistribution (p₁.prod p₂) K W).map
            (fun q ↦ (q.1, q.2.1))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hpair]; rfl
    rw [hsplit, hmap]
    exact Measure.fst_prod
  have hsnd : (martonJointDistribution (p₁.prod p₂) K W).map
      (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) = p₂ := by
    have hsplit : (martonJointDistribution (p₁.prod p₂) K W).map
        (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1)
        = ((martonJointDistribution (p₁.prod p₂) K W).map
            (fun q ↦ (q.1, q.2.1))).map Prod.snd := by
      rw [Measure.map_map measurable_snd hpair]; rfl
    rw [hsplit, hmap]
    exact Measure.snd_prod
  have hindep : IndepFun (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) (fun q ↦ q.2.1)
      (martonJointDistribution (p₁.prod p₂) K W) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hfst, hsnd]
    exact hmap
  exact entropy_diff_eq_zero_of_indepFun (martonJointDistribution (p₁.prod p₂) K W) _ _
    hX hY hindep

end InformationTheory.Shannon.BroadcastChannel.Marton
