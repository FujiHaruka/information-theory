import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.MultipleAccess.JointTypicality
import InformationTheory.Shannon.MultipleAccess.IIDAmbient
import InformationTheory.Shannon.SlepianWolf.ConditionalTypicalSlice

/-!
# Degraded broadcast channel — achievability (superposition inner bound)

The achievability half of the degraded broadcast-channel coding theorem
(Cover–Thomas *Elements of Information Theory* Thm 15.6.2): the superposition (two-tier
cloud / satellite) random-coding inner bound.  The net-new tier relative to the
multiple-access achievability (`InformationTheory.Shannon.MAC`) is the **conditional
(superposition) random codebook**: satellite codewords are drawn from a conditional
product law `Πᵢ K(Uᵢ)` steered by the cloud codeword, rather than a flat product law.

## Main definitions

* `bcJointDistribution pU K W` — the per-coordinate joint law of `(U, X, Y₁, Y₂)`,
  `U ∼ pU`, `X ∣ U ∼ K`, `(Y₁, Y₂) ∣ X ∼ W`.
* `bcInfo₂ pU K W` — the cloud information `I(U; Y₂) = H(U) + H(Y₂) − H(U, Y₂)`.
* `bcInfo₁ pU K W` — the satellite conditional information
  `I(X; Y₁ ∣ U) = H(U, X) + H(U, Y₁) − H(U, X, Y₁) − H(U)`.
* `IsBCDegraded W` — physical degradedness `X → Y₁ → Y₂` (there is a degrading kernel).
* `BCCloudCodebook` / `BCSatelliteCodebook` and their random-coding measures
  `bcCloudCodebookMeasure`, `bcSatelliteCodebookMeasure`, `bcCodebookMeasure` — the
  two-tier ensemble; the satellite law is a **conditional product** `Πᵢ K(Uᵢ)`.

## Main results

* `bc_conditional_slice_prob_le` — the gateway covering bound: the conditional-product
  mass of the jointly-typical satellite slice is `≤ exp(−n (I(X; Y₁ ∣ U) − ε))`.
* `bc_achievability` — the headline: any rate pair strictly inside the degraded-BC region
  `R₁ < I(X; Y₁ ∣ U)`, `R₂ < I(U; Y₂)` is achievable with vanishing per-receiver error.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.MAC
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

variable {U α β₁ β₂ : Type*}
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Physical degradedness -/

/-- Physical degradedness `X → Y₁ → Y₂`: the second (degraded) output is a stochastic
function of the first output alone.  There is a Markov kernel `Q : Kernel β₁ β₂` (the
degrading channel) such that sampling `(y₁, y₂) ∼ W x` is the same as sampling
`y₁ ∼ (W x).map Prod.fst` and then `y₂ ∼ Q y₁`.  A structural precondition of the
degraded-BC achievability theorem (parity with the converse's block-prefix degradedness),
not a load-bearing hypothesis. -/
def IsBCDegraded (W : BCChannel α β₁ β₂) : Prop :=
  ∃ Q : Kernel β₁ β₂, IsMarkovKernel Q ∧
    ∀ a : α, W a = ((W a).map Prod.fst).bind (fun y₁ ↦ (Q y₁).map (fun y₂ ↦ (y₁, y₂)))

/-! ### Per-coordinate joint distribution -/

/-- The per-coordinate broadcast joint law on `U × α × β₁ × β₂`: the compProd chain
`pU → K → W` (`U ∼ pU`, `X ∣ U ∼ K`, `(Y₁, Y₂) ∣ X ∼ W`), reshaped from the left-nested
`(U × α) × (β₁ × β₂)` to the right-nested quadruple. -/
noncomputable def bcJointDistribution
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) :
    Measure (U × α × β₁ × β₂) :=
  ((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc

instance bcJointDistribution.instIsProbabilityMeasure
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (bcJointDistribution pU K W) := by
  unfold bcJointDistribution
  exact Measure.isProbabilityMeasure_map MeasurableEquiv.prodAssoc.measurable.aemeasurable

/-! ### I.i.d. ambient measure on `ℕ → U × α × β₁ × β₂` -/

/-- The i.i.d. broadcast ambient measure:
`Measure.infinitePi (fun _ => bcJointDistribution pU K W)`. -/
noncomputable def bcAmbientMeasure
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) :
    Measure (ℕ → U × α × β₁ × β₂) :=
  Measure.infinitePi (fun _ : ℕ ↦ bcJointDistribution pU K W)

instance bcAmbientMeasure.instIsProbabilityMeasure
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsProbabilityMeasure (bcAmbientMeasure pU K W) := by
  unfold bcAmbientMeasure
  infer_instance

/-- The cloud coordinate `ω ↦ (ω i).1`. -/
def bcUs : ℕ → (ℕ → U × α × β₁ × β₂) → U := fun i ω ↦ (ω i).1

/-- The satellite input coordinate `ω ↦ (ω i).2.1`. -/
def bcXs : ℕ → (ℕ → U × α × β₁ × β₂) → α := fun i ω ↦ (ω i).2.1

/-- The strong-receiver output coordinate `ω ↦ (ω i).2.2.1`. -/
def bcY₁s : ℕ → (ℕ → U × α × β₁ × β₂) → β₁ := fun i ω ↦ (ω i).2.2.1

/-- The degraded-receiver output coordinate `ω ↦ (ω i).2.2.2`. -/
def bcY₂s : ℕ → (ℕ → U × α × β₁ × β₂) → β₂ := fun i ω ↦ (ω i).2.2.2

/-! ### Auxiliary-variable informations -/

/-- The cloud information `I(U; Y₂) = H(U) + H(Y₂) − H(U, Y₂)` of the per-coordinate joint
law.  This is the achievable rate of receiver 2 (the degraded receiver). -/
noncomputable def bcInfo₂
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (bcJointDistribution pU K W) Prod.fst
    + entropy (bcJointDistribution pU K W) (fun q ↦ q.2.2.2)
    - entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.2.2))

/-- The satellite conditional information
`I(X; Y₁ ∣ U) = H(U, X) + H(U, Y₁) − H(U, X, Y₁) − H(U)` of the per-coordinate joint law.
This is the achievable rate of receiver 1 (the strong receiver) given the cloud `U`.  Unlike
the MAC `macInfo`, this is a genuine four-entropy *conditional* mutual information, not a
plain three-term unconditional one. -/
noncomputable def bcInfo₁
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1))
    + entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.2.1))
    - entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1, q.2.2.1))
    - entropy (bcJointDistribution pU K W) Prod.fst

/-! ### Two-tier (cloud / satellite) random codebook -/

/-- A length-`n` cloud codebook: for each cloud message `w₂` a cloud codeword `Uⁿ(w₂)`. -/
abbrev BCCloudCodebook (M₂ n : ℕ) (U : Type*) := Fin M₂ → (Fin n → U)

/-- A length-`n` satellite codebook: for each message pair `(w₁, w₂)` a satellite codeword
`Xⁿ(w₁, w₂)`.  Definitionally the `BroadcastCode` joint encoder. -/
abbrev BCSatelliteCodebook (M₁ M₂ n : ℕ) (α : Type*) := Fin M₁ × Fin M₂ → (Fin n → α)

/-- The cloud codebook law: `pU`-i.i.d. over all `M₂ · n` cloud letters. -/
noncomputable def bcCloudCodebookMeasure
    (pU : Measure U) (M₂ n : ℕ) : Measure (BCCloudCodebook M₂ n U) :=
  Measure.pi (fun _ : Fin M₂ ↦ Measure.pi (fun _ : Fin n ↦ pU))

/-- The satellite codebook law *conditional on* the cloud codebook `u`: each satellite
letter `Xₗ(w₁, w₂)` is drawn from `K (u w₂ l)`, independently across pairs and letters.  This
is the conditional product `Πᵢ K(Uᵢ)` at the heart of superposition coding — the single point
of departure from the MAC flat-product ensemble. -/
noncomputable def bcSatelliteCodebookMeasure
    (K : Kernel U α) (M₁ M₂ n : ℕ) (u : BCCloudCodebook M₂ n U) :
    Measure (BCSatelliteCodebook M₁ M₂ n α) :=
  Measure.pi (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l : Fin n ↦ K (u p.2 l)))

/-- The joint two-tier codebook law on `(cloud, satellite)` pairs: draw the cloud codebook
from `bcCloudCodebookMeasure`, then the satellite codebook conditionally from
`bcSatelliteCodebookMeasure`. -/
noncomputable def bcCodebookMeasure
    (pU : Measure U) (K : Kernel U α) (M₁ M₂ n : ℕ) :
    Measure (BCCloudCodebook M₂ n U × BCSatelliteCodebook M₁ M₂ n α) :=
  (bcCloudCodebookMeasure pU M₂ n).bind
    (fun u ↦ (bcSatelliteCodebookMeasure K M₁ M₂ n u).map (fun x ↦ (u, x)))

/-! ### Gateway atom infrastructure: i.i.d. coordinate facts for the BC ambient measure

Every random variable consumed by the covering bound has the form `fun ω ↦ g (ω i)` for a
measurable coordinate selector `g : U × α × β₁ × β₂ → γ`.  These are the BC analogues of the
`InformationTheory.Shannon.MAC` `macAmbient_*` lemmas (`IIDAmbient.lean`), proven the same way
via `Measure.infinitePi_map_eval` / `iIndepFun_infinitePi`. -/

/-- The map of a coordinate selector under the BC ambient measure equals the map of the
selector under the per-coordinate joint law. -/
lemma bcAmbient_map_coord {γ : Type*} [MeasurableSpace γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) :
    (bcAmbientMeasure pU K W).map (fun ω ↦ g (ω i))
      = (bcJointDistribution pU K W).map g := by
  have h_comp : (fun ω : ℕ → U × α × β₁ × β₂ ↦ g (ω i)) = g ∘ (fun ω ↦ ω i) := rfl
  rw [h_comp, ← Measure.map_map hg (measurable_pi_apply i)]
  congr 1
  exact Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ bcJointDistribution pU K W) i

/-- Mutual independence of any coordinate selector under the BC ambient measure. -/
lemma bcAmbient_iIndepFun_coord {γ : Type*} [MeasurableSpace γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → U × α × β₁ × β₂) ↦ g (ω i)) (bcAmbientMeasure pU K W) :=
  iIndepFun_infinitePi (P := fun _ : ℕ ↦ bcJointDistribution pU K W)
    (X := fun _ : ℕ ↦ g) (fun _ ↦ hg)

/-- Identical distribution of a coordinate selector across indices. -/
lemma bcAmbient_identDistrib_coord {γ : Type*} [MeasurableSpace γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → U × α × β₁ × β₂ ↦ g (ω i)) (fun ω ↦ g (ω 0))
      (bcAmbientMeasure pU K W) (bcAmbientMeasure pU K W) where
  aemeasurable_fst := (hg.comp (measurable_pi_apply i)).aemeasurable
  aemeasurable_snd := (hg.comp (measurable_pi_apply 0)).aemeasurable
  map_eq := by
    rw [bcAmbient_map_coord pU K W g hg i, bcAmbient_map_coord pU K W g hg 0]

/-- Entropy of a coordinate selector under the BC ambient measure equals its entropy under
the per-coordinate joint law. -/
lemma bcAmbient_entropy_coord {γ : Type*}
    [Fintype γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ) :
    entropy (bcAmbientMeasure pU K W) (fun ω ↦ g (ω i))
      = entropy (bcJointDistribution pU K W) g := by
  refine entropy_eq_of_identDistrib (bcAmbientMeasure pU K W)
    (bcJointDistribution pU K W) (fun ω ↦ g (ω i)) g ?_
  refine ⟨(hg.comp (measurable_pi_apply i)).aemeasurable, hg.aemeasurable, ?_⟩
  rw [bcAmbient_map_coord pU K W g hg i]

/-! ### Positivity of the BC per-coordinate joint law and coordinate marginals -/

/-- The per-coordinate BC joint law has positive singleton mass. -/
lemma bcJointDistribution_singleton_pos
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (q : U × α × β₁ × β₂) :
    0 < (bcJointDistribution pU K W).real {q} := by
  obtain ⟨a, x, y⟩ := q
  unfold bcJointDistribution
  rw [Measure.real,
    Measure.map_apply MeasurableEquiv.prodAssoc.measurable (measurableSet_singleton _)]
  have h_pre : (MeasurableEquiv.prodAssoc ⁻¹' ({(a, x, y)} : Set (U × α × β₁ × β₂)))
      = ({((a, x), y)} : Set ((U × α) × β₁ × β₂)) := by
    ext ⟨⟨u', x'⟩, y'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre]
  have hUXpos : ∀ p : U × α, 0 < (pU ⊗ₘ K).real {p} := by
    rintro ⟨u', x'⟩
    have := jointDistribution_singleton_pos pU K hpU hK u' x'
    rwa [jointDistribution_def] at this
  have hW'pos : ∀ p : U × α, ∀ b : β₁ × β₂,
      0 < ((W.comap Prod.snd measurable_snd : Kernel (U × α) (β₁ × β₂)) p).real {b} := by
    rintro ⟨u', x'⟩ b
    rw [Kernel.comap_apply]
    exact hW x' b
  have h_pos := jointDistribution_singleton_pos (pU ⊗ₘ K)
    (W.comap Prod.snd measurable_snd : Kernel (U × α) (β₁ × β₂)) hUXpos hW'pos (a, x) y
  rw [jointDistribution_def, Measure.real] at h_pos
  exact h_pos

/-- Positivity of any coordinate-selector marginal singleton, reduced to the per-coordinate
joint positivity via a chosen fiber witness. -/
lemma bcAmbient_coord_marginal_pos {γ : Type*}
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) (i : ℕ)
    (c : γ) (r : U × α × β₁ × β₂) (hr : g r = c) :
    0 < ((bcAmbientMeasure pU K W).map (fun ω ↦ g (ω i))).real {c} := by
  rw [bcAmbient_map_coord pU K W g hg i, Measure.real,
    Measure.map_apply hg (measurableSet_singleton c)]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  have hsub : ({r} : Set (U × α × β₁ × β₂)) ⊆ g ⁻¹' {c} := by
    intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz; simp [hr]
  have hpos : 0 < bcJointDistribution pU K W {r} := by
    have := bcJointDistribution_singleton_pos pU K W hpU hK hW r
    rw [Measure.real] at this
    exact ENNReal.toReal_pos_iff.mp this |>.1
  exact (lt_of_lt_of_le hpos (measure_mono hsub)).ne'

/-! ### `(U, X)` marginal factorization -/

/-- The `U`-marginal of the BC joint law is `pU`. -/
lemma bcJointDistribution_map_fst
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (bcJointDistribution pU K W).map (fun q ↦ q.1) = pU := by
  unfold bcJointDistribution
  rw [Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.measurable]
  have hcomp : ((fun q : U × α × β₁ × β₂ ↦ q.1) ∘
      (MeasurableEquiv.prodAssoc : ((U × α) × β₁ × β₂) ≃ᵐ (U × α × β₁ × β₂)))
      = Prod.fst ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst]
  have h1 : ((pU ⊗ₘ K) ⊗ₘ
      (W.comap Prod.snd measurable_snd : Kernel (U × α) (β₁ × β₂))).map Prod.fst = pU ⊗ₘ K :=
    Measure.fst_compProd _ _
  have h2 : (pU ⊗ₘ K).map Prod.fst = pU := Measure.fst_compProd _ _
  rw [h1, h2]

/-- The `(U, X)`-marginal singleton mass of the BC joint law factorizes as
`pU {u} · K u {x}`. -/
lemma bcJointDistribution_map_UX_singleton
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (a : U) (x : α) :
    ((bcJointDistribution pU K W).map (fun q ↦ (q.1, q.2.1))).real {(a, x)}
      = pU.real {a} * (K a).real {x} := by
  have hmeas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hmap : (bcJointDistribution pU K W).map (fun q ↦ (q.1, q.2.1)) = pU ⊗ₘ K := by
    unfold bcJointDistribution
    rw [Measure.map_map hmeas MeasurableEquiv.prodAssoc.measurable]
    have hcomp : ((fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) ∘
        (MeasurableEquiv.prodAssoc : ((U × α) × β₁ × β₂) ≃ᵐ (U × α × β₁ × β₂)))
        = Prod.fst := rfl
    rw [hcomp]
    exact Measure.fst_compProd _ _
  rw [hmap, ← jointDistribution_def, Measure.real, jointDistribution_singleton,
    ENNReal.toReal_mul]
  rfl

/-! ### Relabeling invariance of the typical set (BC-local copy of the MAC helper) -/

/-- Relabeling invariance of the typical set along a measurable equivalence of finite
alphabets. -/
private lemma typicalSet_relabel'
    {Ω γ δ : Type*} [MeasurableSpace Ω]
    [Fintype γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [Fintype δ] [Nonempty δ] [MeasurableSpace δ] [MeasurableSingletonClass δ]
    (μ : Measure Ω) (Zs : ℕ → Ω → γ) (hZs : ∀ i, Measurable (Zs i)) (e : γ ≃ᵐ δ)
    (n : ℕ) (ε : ℝ) (z : Fin n → γ)
    (hz : z ∈ typicalSet μ Zs n ε) :
    (fun i ↦ e (z i)) ∈ typicalSet μ (fun i ω ↦ e (Zs i ω)) n ε := by
  rw [mem_typicalSet_iff] at hz ⊢
  have hsingle : ∀ x : γ,
      (μ.map (fun ω ↦ e ((Zs 0) ω))).real {e x} = (μ.map (Zs 0)).real {x} := by
    intro x
    rw [show (fun ω ↦ e ((Zs 0) ω)) = (e : γ → δ) ∘ (Zs 0) from rfl,
      ← Measure.map_map e.measurable (hZs 0),
      map_measureReal_apply e.measurable (measurableSet_singleton _)]
    congr 1
    ext w
    simp [e.injective.eq_iff]
  have hpmf : ∀ x : γ,
      pmfLog μ (fun i ω ↦ e (Zs i ω)) (e x) = pmfLog μ Zs x := by
    intro x
    change -Real.log ((μ.map (fun ω ↦ e ((Zs 0) ω))).real {e x})
        = -Real.log ((μ.map (Zs 0)).real {x})
    rw [hsingle x]
  have hent : entropy μ ((fun i ω ↦ e (Zs i ω)) 0) = entropy μ (Zs 0) :=
    entropy_measurableEquiv_comp μ (Zs 0) (hZs 0) e
  rw [hent]
  simp only [hpmf]
  exact hz

/-! ### The two exponential ingredients of the covering bound -/

/-- Per-sequence conditional mass bound: for a typical cloud `u` and a satellite `x` whose
`(U, X)`-pair sequence is typical, the conditional-product mass of `x` is at most
`exp(−n (H(U, X) − H(U) − 2ε))`. -/
lemma bc_perseq_mass_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    {n : ℕ} {ε : ℝ} (u : Fin n → U) (x : Fin n → α)
    (hu : u ∈ typicalSet (bcAmbientMeasure pU K W) bcUs n ε)
    (hux : (fun i ↦ (u i, x i)) ∈
      typicalSet (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs) n ε) :
    (Measure.pi (fun l : Fin n ↦ K (u l))).real {x}
      ≤ Real.exp (-(n : ℝ) *
          (entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs 0)
            - entropy (bcAmbientMeasure pU K W) (bcUs 0) - 2 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set H_U : ℝ := entropy μ (bcUs 0) with hHU_def
  set H_UX : ℝ := entropy μ (jointSequence bcUs bcXs 0) with hHUX_def
  have hgU_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hgUX_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  -- Coordinate marginals.
  have hmapU : μ.map (bcUs 0) = pU := by
    have hseq : (bcUs 0 : (ℕ → U × α × β₁ × β₂) → U)
        = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ q.1) (ω 0) := rfl
    rw [hseq, bcAmbient_map_coord pU K W (fun q ↦ q.1) hgU_meas 0, bcJointDistribution_map_fst]
  have hmapUX : ∀ a : U, ∀ b : α,
      (μ.map (jointSequence bcUs bcXs 0)).real {(a, b)} = pU.real {a} * (K a).real {b} := by
    intro a b
    have hseq : (jointSequence bcUs bcXs 0 : (ℕ → U × α × β₁ × β₂) → U × α)
        = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) (ω 0) := rfl
    rw [hseq, bcAmbient_map_coord pU K W (fun q ↦ (q.1, q.2.1)) hgUX_meas 0,
      bcJointDistribution_map_UX_singleton]
  -- Positivity of the per-letter conditional masses.
  have hKpos : ∀ i : Fin n, 0 < (K (u i)).real {x i} := fun i ↦ hK (u i) (x i)
  have hUpos : ∀ i : Fin n, 0 < pU.real {u i} := fun i ↦ hpU (u i)
  -- Per-letter log identity: log (K uᵢ xᵢ) = pmfLog_U uᵢ − pmfLog_UX (uᵢ, xᵢ).
  have hlog_eq : ∀ i : Fin n, Real.log ((K (u i)).real {x i})
      = pmfLog μ bcUs (u i) - pmfLog μ (jointSequence bcUs bcXs) (u i, x i) := by
    intro i
    have h1 : pmfLog μ bcUs (u i) = -Real.log (pU.real {u i}) := by
      unfold pmfLog; rw [hmapU]
    have h2 : pmfLog μ (jointSequence bcUs bcXs) (u i, x i)
        = -Real.log (pU.real {u i} * (K (u i)).real {x i}) := by
      unfold pmfLog; rw [hmapUX (u i) (x i)]
    rw [h1, h2, Real.log_mul (hUpos i).ne' (hKpos i).ne']
    ring
  -- The conditional-product mass at `x`.
  have hνpos : 0 < (Measure.pi (fun l : Fin n ↦ K (u l))).real {x} := by
    rw [show (Measure.pi (fun l : Fin n ↦ K (u l))).real {x}
        = ∏ i : Fin n, (K (u i)).real {x i} from by
      show ((Measure.pi (fun l : Fin n ↦ K (u l))) {x}).toReal = _
      rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl]
    exact Finset.prod_pos fun i _ ↦ hKpos i
  have hν_log : Real.log ((Measure.pi (fun l : Fin n ↦ K (u l))).real {x})
      = (∑ i : Fin n, pmfLog μ bcUs (u i))
        - ∑ i : Fin n, pmfLog μ (jointSequence bcUs bcXs) (u i, x i) := by
    rw [show (Measure.pi (fun l : Fin n ↦ K (u l))).real {x}
        = ∏ i : Fin n, (K (u i)).real {x i} from by
      show ((Measure.pi (fun l : Fin n ↦ K (u l))) {x}).toReal = _
      rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl]
    rw [Real.log_prod (fun i _ ↦ (hKpos i).ne')]
    rw [show (∑ i : Fin n, Real.log ((K (u i)).real {x i}))
        = ∑ i : Fin n, (pmfLog μ bcUs (u i)
          - pmfLog μ (jointSequence bcUs bcXs) (u i, x i)) from
      Finset.sum_congr rfl fun i _ ↦ hlog_eq i]
    rw [Finset.sum_sub_distrib]
  -- Reduce to `log ≤`.
  rw [← Real.exp_log hνpos, hν_log]
  refine Real.exp_le_exp.mpr ?_
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  · have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [mem_typicalSet_iff] at hu hux
    have hSU : (∑ i : Fin n, pmfLog μ bcUs (u i)) < (n : ℝ) * (H_U + ε) := by
      have hlt := (abs_lt.mp hu).2
      have : (∑ i : Fin n, pmfLog μ bcUs (u i)) / n < H_U + ε := by linarith
      have := (div_lt_iff₀ hn_pos_R).mp this
      linarith
    have hSUX : (n : ℝ) * (H_UX - ε) < ∑ i : Fin n, pmfLog μ (jointSequence bcUs bcXs) (u i, x i) := by
      have hgt := (abs_lt.mp hux).1
      have : H_UX - ε < (∑ i : Fin n, pmfLog μ (jointSequence bcUs bcXs) (u i, x i)) / n := by
        linarith
      have := (lt_div_iff₀ hn_pos_R).mp this
      linarith
    nlinarith [hSU, hSUX]

/-- Slice-cardinality bound: the number of satellites `x` making `(u, x, y₁)` jointly typical
is at most `exp(n (H(X, (U, Y₁)) − H(U, Y₁) + 2ε))`. -/
lemma bc_slice_card_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {n : ℕ} {ε : ℝ} (u : Fin n → U) (y₁ : Fin n → β₁) :
    (({ x : Fin n → α |
          (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε
        }).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) *
          (entropy (bcAmbientMeasure pU K W) (jointSequence bcXs (jointSequence bcUs bcY₁s) 0)
            - entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcY₁s 0) + 2 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  -- Coordinate measurabilities.
  have hbcUs : ∀ i, Measurable (bcUs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hbcXs : ∀ i, Measurable (bcXs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.fst
  have hbcY₁s : ∀ i, Measurable (bcY₁s (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.fst
  have hYseq : ∀ i, Measurable (jointSequence bcUs bcY₁s i) :=
    fun i ↦ measurable_jointSequence bcUs bcY₁s hbcUs hbcY₁s i
  have hZseq : ∀ i, Measurable (jointSequence bcXs (jointSequence bcUs bcY₁s) i) :=
    fun i ↦ measurable_jointSequence bcXs (jointSequence bcUs bcY₁s) hbcXs hYseq i
  have hmacseq : ∀ i, Measurable (macJointSequence bcUs bcXs bcY₁s i) :=
    fun i ↦ measurable_macJointSequence bcUs bcXs bcY₁s hbcUs hbcXs hbcY₁s i
  -- The two coordinate selectors used as the `(U, Y₁)` and `(X, (U, Y₁))` axes.
  have hgY_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hgZ_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.2.1, (q.1, q.2.2.1))) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  -- Independence / identical distribution of the two axes.
  have hindepY : iIndepFun (fun i ↦ jointSequence bcUs bcY₁s i) μ :=
    bcAmbient_iIndepFun_coord pU K W (fun q ↦ (q.1, q.2.2.1)) hgY_meas
  have hidentY : ∀ i, IdentDistrib (jointSequence bcUs bcY₁s i) (jointSequence bcUs bcY₁s 0) μ μ :=
    fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.2.1)) hgY_meas i
  have hindepZ :
      iIndepFun (fun i ↦ jointSequence bcXs (jointSequence bcUs bcY₁s) i) μ :=
    bcAmbient_iIndepFun_coord pU K W (fun q ↦ (q.2.1, (q.1, q.2.2.1))) hgZ_meas
  have hidentZ : ∀ i, IdentDistrib (jointSequence bcXs (jointSequence bcUs bcY₁s) i)
      (jointSequence bcXs (jointSequence bcUs bcY₁s) 0) μ μ :=
    fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.2.1, (q.1, q.2.2.1))) hgZ_meas i
  -- Positivity of the two coordinate marginals.
  have hposY : ∀ q : U × β₁, 0 < (μ.map (jointSequence bcUs bcY₁s 0)).real {q} := by
    intro q
    exact bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun r ↦ (r.1, r.2.2.1)) hgY_meas 0
      q (q.1, Classical.arbitrary α, q.2, Classical.arbitrary β₂) rfl
  have hposZ : ∀ q : α × U × β₁,
      0 < (μ.map (jointSequence bcXs (jointSequence bcUs bcY₁s) 0)).real {q} := by
    intro q
    exact bcAmbient_coord_marginal_pos pU K W hpU hK hW
      (fun r ↦ (r.2.1, (r.1, r.2.2.1))) hgZ_meas 0
      q (q.2.1, q.1, q.2.2, Classical.arbitrary β₂) rfl
  -- The conditional slice-size bound (Slepian–Wolf), instantiated with `Xs = bcXs`,
  -- `Ys = (U, Y₁)`-pair and the fixed block `w = (u, y₁)`.
  have hcard := conditionalTypicalSlice_card_le μ bcXs (jointSequence bcUs bcY₁s)
    hbcXs hYseq hindepY hidentY hindepZ hidentZ hposY hposZ n (ε := ε) (fun i ↦ (u i, y₁ i))
  refine le_trans ?_ hcard
  -- The mac slice embeds into the conditional typical slice via the `(U,X,Y₁) → (X,U,Y₁)` relabel.
  let e : (U × α × β₁) ≃ᵐ (α × U × β₁) :=
    { toFun := fun p ↦ (p.2.1, (p.1, p.2.2))
      invFun := fun p ↦ (p.2.1, (p.1, p.2.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun :=
        (measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      measurable_invFun :=
        (measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) }
  have hsub : { x : Fin n → α |
      (u, x, y₁) ∈ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε } ⊆
      conditionalTypicalSlice μ bcXs (jointSequence bcUs bcY₁s) n ε (fun i ↦ (u i, y₁ i)) := by
    intro x hx
    replace hx : (u, x, y₁) ∈ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε := hx
    rw [mem_macJointlyTypicalSet_iff] at hx
    obtain ⟨_c1, c2, _c3, _c4, c5, _c6, c7⟩ := hx
    rw [mem_conditionalTypicalSlice_iff, mem_jointlyTypicalSet_iff]
    refine ⟨c2, c5, ?_⟩
    have hrelabel := typicalSet_relabel' μ (macJointSequence bcUs bcXs bcY₁s) hmacseq e n ε
      (fun i ↦ (u i, x i, y₁ i)) c7
    have helem : (fun i ↦ e (u i, x i, y₁ i)) = (fun i ↦ (x i, u i, y₁ i)) := by
      funext i; rfl
    have hseq : (fun (i : ℕ) (ω : ℕ → U × α × β₁ × β₂) ↦ e (macJointSequence bcUs bcXs bcY₁s i ω))
        = jointSequence bcXs (jointSequence bcUs bcY₁s) := by funext i ω; rfl
    rw [helem, hseq] at hrelabel
    exact hrelabel
  have hfin_sub : ({ x : Fin n → α |
        (u, x, y₁) ∈ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε }).toFinite.toFinset ⊆
      (conditionalTypicalSlice μ bcXs (jointSequence bcUs bcY₁s) n ε
        (fun i ↦ (u i, y₁ i))).toFinite.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz ⊢
    exact hsub hz
  exact_mod_cast Finset.card_le_card hfin_sub

/-! ### Gateway atom: conditional-slice satellite typicality bound -/

/-- **Conditional-slice satellite typicality probability bound** (superposition covering
step).  For a fixed *typical* cloud codeword `u` and a fixed *typical* received word `y₁`,
the probability under the conditional product law `Πᵢ K(uᵢ)` that an independently drawn
satellite `x` is jointly typical with `(u, y₁)` is at most `exp(−n (I(X; Y₁ ∣ U) − 4ε))`.
This is the receiver-1 "wrong satellite, correct cloud" sub-event of the superposition
random-coding argument (Cover–Thomas Thm 15.6.2); the exponent matches `bcInfo₁`, with the
`4ε` slack the sum of the four entropy-typicality windows (matching the `3ε` slack of the
MAC atoms `macJTS_indep_prob_le_*`).  Full support (`hpU`/`hK`/`hW`) is a regularity
precondition of the AEP mass bounds, not load-bearing. -/
theorem bc_conditional_slice_prob_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {n : ℕ} {ε : ℝ}
    (u : Fin n → U) (y₁ : Fin n → β₁)
    (hu : u ∈ typicalSet (bcAmbientMeasure pU K W) bcUs n ε)
    (hy₁ : y₁ ∈ typicalSet (bcAmbientMeasure pU K W) bcY₁s n ε) :
    (Measure.pi (fun l : Fin n ↦ K (u l))).real
        { x : Fin n → α |
          (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
  classical
  set S : Set (Fin n → α) :=
    { x : Fin n → α |
      (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
    with hS_def
  -- Entropy identities: coordinate entropies under the ambient law equal the joint-law
  -- entropies appearing in `bcInfo₁`.
  have hmeasUXY : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  let e' : (U × α × β₁) ≃ᵐ (α × U × β₁) :=
    { toFun := fun p ↦ (p.2.1, (p.1, p.2.2))
      invFun := fun p ↦ (p.2.1, (p.1, p.2.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := (measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      measurable_invFun := (measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) }
  have hHU : entropy (bcAmbientMeasure pU K W) (bcUs 0)
      = entropy (bcJointDistribution pU K W) Prod.fst :=
    bcAmbient_entropy_coord pU K W (fun q ↦ q.1) measurable_fst 0
  have hHUX : entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1)) :=
    bcAmbient_entropy_coord pU K W (fun q ↦ (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) 0
  have hHUY : entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcY₁s 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.2.1)) :=
    bcAmbient_entropy_coord pU K W (fun q ↦ (q.1, q.2.2.1))
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))) 0
  have hHUXY : entropy (bcAmbientMeasure pU K W) (jointSequence bcXs (jointSequence bcUs bcY₁s) 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1, q.2.2.1)) := by
    have h1 : entropy (bcAmbientMeasure pU K W)
          (jointSequence bcXs (jointSequence bcUs bcY₁s) 0)
        = entropy (bcJointDistribution pU K W) (fun q ↦ (q.2.1, (q.1, q.2.2.1))) :=
      bcAmbient_entropy_coord pU K W (fun q ↦ (q.2.1, (q.1, q.2.2.1)))
        ((measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))) 0
    rw [h1]
    exact entropy_measurableEquiv_comp (bcJointDistribution pU K W)
      (fun q ↦ (q.1, q.2.1, q.2.2.1)) hmeasUXY e'
  -- The slice-cardinality bound.
  have hcardbound := bc_slice_card_le pU K W hpU hK hW (ε := ε) u y₁
  -- Decompose the slice mass as a sum over the finite slice.
  have hsum : (Measure.pi (fun l : Fin n ↦ K (u l))).real S
      = ∑ x ∈ S.toFinite.toFinset, (Measure.pi (fun l : Fin n ↦ K (u l))).real {x} := by
    have hss := sum_measureReal_singleton (μ := Measure.pi (fun l : Fin n ↦ K (u l)))
      S.toFinite.toFinset
    rw [Set.Finite.coe_toFinset] at hss
    exact hss.symm
  rw [hsum]
  calc (∑ x ∈ S.toFinite.toFinset, (Measure.pi (fun l : Fin n ↦ K (u l))).real {x})
      ≤ ∑ _x ∈ S.toFinite.toFinset,
          Real.exp (-(n : ℝ) * (entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs 0)
            - entropy (bcAmbientMeasure pU K W) (bcUs 0) - 2 * ε)) := by
        refine Finset.sum_le_sum (fun x hx ↦ ?_)
        have hxS : x ∈ S := (Set.Finite.mem_toFinset _).mp hx
        have hxmac : (u, x, y₁) ∈
            macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε := hxS
        rw [mem_macJointlyTypicalSet_iff] at hxmac
        exact bc_perseq_mass_le pU K W hpU hK u x hu hxmac.2.2.2.1
    _ = (S.toFinite.toFinset.card : ℝ) *
          Real.exp (-(n : ℝ) * (entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs 0)
            - entropy (bcAmbientMeasure pU K W) (bcUs 0) - 2 * ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp ((n : ℝ) *
            (entropy (bcAmbientMeasure pU K W) (jointSequence bcXs (jointSequence bcUs bcY₁s) 0)
              - entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcY₁s 0) + 2 * ε)) *
          Real.exp (-(n : ℝ) * (entropy (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs 0)
            - entropy (bcAmbientMeasure pU K W) (bcUs 0) - 2 * ε)) :=
        mul_le_mul_of_nonneg_right hcardbound (Real.exp_nonneg _)
    _ = Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hHU, hHUX, hHUY, hHUXY]
        unfold bcInfo₁
        ring

/-! ### Headline: degraded broadcast achievability -/

/-- **Broadcast channel achievability (degraded, superposition inner bound).**
Cover–Thomas *Elements of Information Theory* Thm 15.6.2 achievability.  Over a physically
degraded broadcast channel `W` with cloud law `pU` and conditional input kernel `K`, any
rate pair strictly inside the auxiliary-variable region

* `R₁ < I(X; Y₁ ∣ U)` (`= bcInfo₁`, the strong receiver), and
* `R₂ < I(U; Y₂)` (`= bcInfo₂`, the degraded receiver)

is achievable: for all large enough block lengths `n` there is a `BroadcastCode` whose two
per-receiver average error probabilities are both below any prescribed `ε' > 0`.  The proof
is the two-tier superposition random-coding argument; degradedness `X → Y₁ → Y₂` is a
structural precondition ensuring the receiver-1 joint-decoding rate sum is met automatically.
@residual(plan:bc-achievability-plan) -/
theorem bc_achievability
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hdeg : IsBCDegraded W)
    {R₁ R₂ : ℝ} (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : BroadcastCode M₁ M₂ n α β₁ β₂),
        (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε' := by
  sorry

end InformationTheory.Shannon.BroadcastChannel
