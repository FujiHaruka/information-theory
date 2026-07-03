import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.MultipleAccess.JointTypicality
import InformationTheory.Shannon.MultipleAccess.IIDAmbient
import InformationTheory.Shannon.MultipleAccess.Achievability
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
precondition of the AEP mass bounds, not load-bearing.
@audit:ok -/
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

/-! ### Two-tier decoders and the assembled broadcast code -/

/-- Receiver-2 (cloud / degraded receiver) joint-typical decoder.  Given a received word
`y₂`, returns the unique cloud message `w₂` whose codeword `Uⁿ(w₂)` is jointly typical with
`y₂`, falling back to `⟨0, hM₂⟩` if no such `w₂` exists or it is not unique.  This is a
single-user joint-typical decoder over the cloud codebook — receiver 2 never needs the
satellite tier. -/
noncomputable def bcCloudTypicalDecoder
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂)
    {M₂ n : ℕ} (hM₂ : 0 < M₂) (ε : ℝ) (cU : BCCloudCodebook M₂ n U) :
    (Fin n → β₂) → Fin M₂ := fun y₂ ↦
  haveI : Decidable (∃! w₂ : Fin M₂,
      (cU w₂, y₂) ∈ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε) :=
    Classical.propDecidable _
  if h : ∃! w₂ : Fin M₂,
      (cU w₂, y₂) ∈ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε
    then Classical.choose h.exists
    else ⟨0, hM₂⟩

/-- Receiver-1 (strong receiver) superposition joint-typical decoder.  Given a received word
`y₁`, returns the unique message pair `(w₁, w₂)` such that the cloud/satellite/output triple
`(Uⁿ(w₂), Xⁿ(w₁, w₂), y₁)` is jointly typical, falling back to `(⟨0, hM₁⟩, ⟨0, hM₂⟩)`
otherwise.  The typical-set argument order `bcUs, bcXs, bcY₁s` matches the covering bound
`bc_conditional_slice_prob_le`. -/
noncomputable def bcJointTypicalDecoder
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂)
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α) :
    (Fin n → β₁) → Fin M₁ × Fin M₂ := fun y₁ ↦
  haveI : Decidable (∃! p : Fin M₁ × Fin M₂,
      (cU p.2, cX p, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε) :=
    Classical.propDecidable _
  if h : ∃! p : Fin M₁ × Fin M₂,
      (cU p.2, cX p, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε
    then Classical.choose h.exists
    else (⟨0, hM₁⟩, ⟨0, hM₂⟩)

/-- Bundle a cloud codebook `cU` and satellite codebook `cX` into a `BroadcastCode`: `cX` is
the joint encoder, receiver 1 uses the superposition joint decoder, receiver 2 the cloud
decoder. -/
noncomputable def bcCodebookToCode
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂)
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α) :
    BroadcastCode M₁ M₂ n α β₁ β₂ where
  encoder := cX
  decoder₁ := fun y₁ ↦ (bcJointTypicalDecoder pU K W hM₁ hM₂ ε cU cX y₁).1
  decoder₂ := bcCloudTypicalDecoder pU K W hM₂ ε cU

/-! ### Receiver-2 (cloud) error analysis -/

/-- **Receiver-2 two-event Bonferroni bound.**  When the pair `m` is sent, the receiver-2
per-pair error probability of the cloud joint-typical decoder is bounded by the correct-cloud
atypical event `E0` plus the wrong-cloud alias union bound.  This is the single-user
`errorProbAt_le_E1_plus_E2` applied along the `β₂`-projection `fun i ↦ (y i).2` of the block
output. -/
theorem bc_errorProbAt₂_le_bonferroni
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α)
    (m : Fin M₁ × Fin M₂) :
    ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂ W m).toReal
      ≤ (Measure.pi (fun i ↦ W (cX m i))).real
          { y : Fin n → β₁ × β₂ |
            (cU m.2, fun i ↦ (y i).2) ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
        + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
            (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU w₂', fun i ↦ (y i).2) ∈
                  jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε } := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set JTS : Set ((Fin n → U) × (Fin n → β₂)) := jointlyTypicalSet μ bcUs bcY₂s n ε with hJTS_def
  set c : BroadcastCode M₁ M₂ n α β₁ β₂ := bcCodebookToCode pU K W hM₁ hM₂ ε cU cX with hc_def
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi (fun i ↦ W (cX m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  -- The correct-cloud atypical event and the wrong-cloud alias events.
  set E0 : Set (Fin n → β₁ × β₂) :=
    { y | (cU m.2, fun i ↦ (y i).2) ∉ JTS } with hE0_def
  set Ealias : Fin M₂ → Set (Fin n → β₁ × β₂) :=
    fun w₂' ↦ { y | (cU w₂', fun i ↦ (y i).2) ∈ JTS } with hEalias_def
  -- Step 1: `c.errorEvent₂ m ⊆ E0 ∪ (⋃ w₂' ∈ univ.erase m.2, Ealias w₂')`.
  have h_sub :
      c.errorEvent₂ m ⊆ E0 ∪ ⋃ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, Ealias w₂' := by
    intro y hy
    rw [BroadcastCode.errorEvent₂, Set.mem_setOf_eq] at hy
    -- `c.decoder₂ (fun i ↦ (y i).2) = bcCloudTypicalDecoder … cU (fun i ↦ (y i).2)`.
    have hdec : c.decoder₂ (fun i ↦ (y i).2)
        = bcCloudTypicalDecoder pU K W hM₂ ε cU (fun i ↦ (y i).2) := rfl
    by_cases hu : ∃! w₂ : Fin M₂, (cU w₂, fun i ↦ (y i).2) ∈ JTS
    · -- A unique typical cloud exists; the decoder returns `Classical.choose hu.exists`.
      have hch : c.decoder₂ (fun i ↦ (y i).2) = Classical.choose hu.exists := by
        rw [hdec]; unfold bcCloudTypicalDecoder; rw [dif_pos hu]
      set w₂' := Classical.choose hu.exists with hw₂'_def
      have hw₂'_mem : (cU w₂', fun i ↦ (y i).2) ∈ JTS := Classical.choose_spec hu.exists
      have hw₂'_ne : w₂' ≠ m.2 := by
        intro hmm; apply hy; rw [hch, ← hmm]
      by_cases hm_typ : (cU m.2, fun i ↦ (y i).2) ∈ JTS
      · exact absurd (hu.unique hw₂'_mem hm_typ) hw₂'_ne
      · exact Or.inl hm_typ
    · by_cases hexists : ∃ w₂ : Fin M₂, (cU w₂, fun i ↦ (y i).2) ∈ JTS
      · by_cases hm_typ : (cU m.2, fun i ↦ (y i).2) ∈ JTS
        · -- `m.2` typical but not unique ⇒ some `w₂'' ≠ m.2` is also typical.
          have h_alias : ∃ w₂'' : Fin M₂,
              (cU w₂'', fun i ↦ (y i).2) ∈ JTS ∧ w₂'' ≠ m.2 := by
            by_contra h_none
            apply hu
            refine ⟨m.2, hm_typ, ?_⟩
            intro w₂'' hw₂''_typ
            by_contra hne
            exact h_none ⟨w₂'', hw₂''_typ, hne⟩
          obtain ⟨w₂'', hw₂''_typ, hw₂''_ne⟩ := h_alias
          refine Or.inr ?_
          refine Set.mem_iUnion.mpr ⟨w₂'', ?_⟩
          exact Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hw₂''_ne, Finset.mem_univ _⟩, hw₂''_typ⟩
        · exact Or.inl hm_typ
      · refine Or.inl ?_
        intro hm_typ
        exact hexists ⟨m.2, hm_typ⟩
  -- Step 2: `c.errorProbAt₂ W m = ν (c.errorEvent₂ m)` (defeq of `bcCodebookToCode`).
  have h_real_eq : (c.errorProbAt₂ W m).toReal = ν.real (c.errorEvent₂ m) := rfl
  rw [h_real_eq]
  -- Step 3: monotonicity + union bound.
  calc ν.real (c.errorEvent₂ m)
      ≤ ν.real (E0 ∪ ⋃ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, Ealias w₂') :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ν.real E0 + ν.real (⋃ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, Ealias w₂') :=
        measureReal_union_le _ _
    _ ≤ ν.real E0 + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, ν.real (Ealias w₂') := by
        gcongr
        exact measureReal_biUnion_finset_le _ _

/-- **Receiver-2 cloud independent-pair bound.**  Under the product of the cloud block law and
the `Y₂` block law (the random-coding measure for a wrong cloud codeword drawn independently of
the received output), the probability of joint typicality is at most `exp(−n (I(U; Y₂) − 3ε))`.
A wrapper of the single-user `jointlyTypicalSet_indep_prob_le` with the exponent rewritten into
the `bcInfo₂` form; full support is a regularity precondition, not load-bearing. -/
theorem bc_cloud_indep_prob_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((bcAmbientMeasure pU K W).map (jointRV bcUs n)).prod
        ((bcAmbientMeasure pU K W).map (jointRV bcY₂s n))).real
        (jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε)
      ≤ Real.exp (-(n : ℝ) * (bcInfo₂ pU K W - 3 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  -- Coordinate selectors and their measurabilities.
  have hgU_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hgY₂_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hgUY₂_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hbcUs : ∀ i, Measurable (bcUs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hbcY₂s : ∀ i, Measurable (bcY₂s (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.snd
  -- Independence / identical distribution of the two axes.
  have hindepU : iIndepFun (fun i ↦ bcUs i) μ :=
    bcAmbient_iIndepFun_coord pU K W (fun q ↦ q.1) hgU_meas
  have hidentU : ∀ i, IdentDistrib (bcUs i) (bcUs 0) μ μ :=
    fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.1) hgU_meas i
  have hindepY₂ : iIndepFun (fun i ↦ bcY₂s i) μ :=
    bcAmbient_iIndepFun_coord pU K W (fun q ↦ q.2.2.2) hgY₂_meas
  have hidentY₂ : ∀ i, IdentDistrib (bcY₂s i) (bcY₂s 0) μ μ :=
    fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.2.2) hgY₂_meas i
  -- Positivity of the two coordinate marginals and the joint marginal.
  have hposU : ∀ x : U, 0 < (μ.map (bcUs 0)).real {x} := fun x ↦
    bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun q ↦ q.1) hgU_meas 0
      x (x, Classical.arbitrary α, Classical.arbitrary β₁, Classical.arbitrary β₂) rfl
  have hposY₂ : ∀ y : β₂, 0 < (μ.map (bcY₂s 0)).real {y} := fun y ↦
    bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun q ↦ q.2.2.2) hgY₂_meas 0
      y (Classical.arbitrary U, Classical.arbitrary α, Classical.arbitrary β₁, y) rfl
  have hposZ : ∀ p : U × β₂, 0 < (μ.map (jointSequence bcUs bcY₂s 0)).real {p} := fun p ↦
    bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun q ↦ (q.1, q.2.2.2)) hgUY₂_meas 0
      p (p.1, Classical.arbitrary α, Classical.arbitrary β₁, p.2) rfl
  -- Entropy identities: coordinate entropies equal the joint-law entropies in `bcInfo₂`.
  have hHU : entropy μ (bcUs 0) = entropy (bcJointDistribution pU K W) Prod.fst :=
    bcAmbient_entropy_coord pU K W (fun q ↦ q.1) measurable_fst 0
  have hHY₂ : entropy μ (bcY₂s 0) = entropy (bcJointDistribution pU K W) (fun q ↦ q.2.2.2) :=
    bcAmbient_entropy_coord pU K W (fun q ↦ q.2.2.2) hgY₂_meas 0
  have hHUY₂ : entropy μ (jointSequence bcUs bcY₂s 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.2.2)) :=
    bcAmbient_entropy_coord pU K W (fun q ↦ (q.1, q.2.2.2)) hgUY₂_meas 0
  -- The single-user independent-pair bound, then rewrite the exponent to `bcInfo₂`.
  refine (jointlyTypicalSet_indep_prob_le μ bcUs bcY₂s hbcUs hbcY₂s hindepU hidentU
    hindepY₂ hidentY₂ hposU hposY₂ hposZ n hε).trans (le_of_eq ?_)
  congr 1
  rw [hHU, hHY₂, hHUY₂]
  unfold bcInfo₂
  ring

/-! ### Receiver-2 random-codebook averaging: `(U, Y₂)` channel fold and wrong-cloud swap

The receiver-2 random-coding legs.  The single point of departure from the MAC flat-product
averaging is the broadcast **pair output** `β₁ × β₂`: the block output law lives on
`Fin n → β₁ × β₂` and receiver 2 sees only the `β₂`-projection.  The `(U, Y₂)` channel fold
(`bc_chan_fold_Y₂_set`) folds the cloud/satellite/channel chain into the ambient `Y₂`-block
marginal after marginalizing `β₂`; the wrong-cloud swap (`bc_random_codebook_wrongcloud_swap`)
recognizes the codebook average of a wrong cloud alias as the independent product law
`(U-block) ⊗ (Y₂-block)` and applies `bc_cloud_indep_prob_le`. -/

/-- The strong/degraded output *pair* coordinate `ω ↦ (ω i).2.2 : β₁ × β₂`. -/
def bcYPs : ℕ → (ℕ → U × α × β₁ × β₂) → β₁ × β₂ := fun i ω ↦ (ω i).2.2

/-- Finite-sum change of variables under a pushforward. -/
private lemma sum_weighted_map {γ δ : Type*}
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [Fintype δ] [MeasurableSpace δ] [MeasurableSingletonClass δ]
    (μ : Measure γ) [IsProbabilityMeasure μ] (f : γ → δ) (hf : Measurable f) (g : δ → ℝ) :
    ∑ c : γ, μ.real {c} * g (f c) = ∑ z : δ, (μ.map f).real {z} * g z := by
  classical
  have hmap : ∀ z : δ, (μ.map f).real {z} = ∑ c : γ, (if f c = z then μ.real {c} else 0) := by
    intro z
    rw [map_measureReal_apply hf (measurableSet_singleton z), measureReal_eq_sum_ite μ (f ⁻¹' {z})]
    refine Finset.sum_congr rfl (fun c _ ↦ ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hrhs : ∑ z : δ, (μ.map f).real {z} * g z
      = ∑ z : δ, ∑ c : γ, (if f c = z then μ.real {c} else 0) * g z := by
    refine Finset.sum_congr rfl (fun z _ ↦ ?_)
    rw [hmap z, Finset.sum_mul]
  rw [hrhs, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ ↦ ?_)
  have hpush : ∀ z : δ, (if f c = z then μ.real {c} else 0) * g z
      = (if f c = z then μ.real {c} * g z else 0) := by
    intro z; by_cases h : f c = z <;> simp [h]
  rw [Finset.sum_congr rfl (fun z _ ↦ hpush z),
    Finset.sum_ite_eq Finset.univ (f c) (fun z ↦ μ.real {c} * g z)]
  simp

/-- The BC per-coordinate joint law singleton mass:
`ν{(u, a, y₁, y₂)} = pU{u} · K(u){a} · W(a){(y₁, y₂)}`. -/
lemma bcJointDistribution_singleton_eq
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (u : U) (a : α) (y₁ : β₁) (y₂ : β₂) :
    (bcJointDistribution pU K W).real {(u, a, y₁, y₂)}
      = pU.real {u} * (K u).real {a} * (W a).real {(y₁, y₂)} := by
  unfold bcJointDistribution
  rw [Measure.real,
    Measure.map_apply MeasurableEquiv.prodAssoc.measurable (measurableSet_singleton _)]
  have h_pre : (MeasurableEquiv.prodAssoc ⁻¹' ({(u, a, y₁, y₂)} : Set (U × α × β₁ × β₂)))
      = ({((u, a), y₁, y₂)} : Set ((U × α) × β₁ × β₂)) := by
    ext ⟨⟨u', a'⟩, p'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre]
  have h_val := jointDistribution_singleton (pU ⊗ₘ K)
    (W.comap Prod.snd measurable_snd) (u, a) (y₁, y₂)
  rw [jointDistribution_def, Kernel.comap_apply] at h_val
  have h_ux := jointDistribution_singleton pU K u a
  rw [jointDistribution_def] at h_ux
  rw [h_val, h_ux, ENNReal.toReal_mul, ENNReal.toReal_mul]
  rfl

/-- The `U`-block law under the BC ambient measure equals `Measure.pi pU`. -/
lemma bc_block_law_U
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (n : ℕ) :
    (bcAmbientMeasure pU K W).map (jointRV bcUs n) = Measure.pi (fun _ : Fin n ↦ pU) := by
  refine block_law_X_eq_pi_p (bcAmbientMeasure pU K W) bcUs
    (fun i ↦ (measurable_pi_apply i).fst)
    (bcAmbient_iIndepFun_coord pU K W (fun q ↦ q.1) measurable_fst)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.1) measurable_fst i) pU ?_ n
  rw [show (bcUs 0 : (ℕ → U × α × β₁ × β₂) → U) = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ q.1) (ω 0)
      from rfl,
    bcAmbient_map_coord pU K W (fun q ↦ q.1) measurable_fst 0, bcJointDistribution_map_fst]

/-- The per-coordinate `(U, X, Ypair)`-reshaped joint law singleton mass factorizes as
`pU{u} · K(u){a} · W(a){yp}`. -/
lemma bcJointDistribution_map_UXY_singleton
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (u : U) (a : α) (yp : β₁ × β₂) :
    ((bcJointDistribution pU K W).map
        (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2))).real {(u, a, yp)}
      = pU.real {u} * (K u).real {a} * (W a).real {yp} := by
  obtain ⟨y₁, y₂⟩ := yp
  have hmeas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2)) :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  rw [map_measureReal_apply hmeas (measurableSet_singleton _)]
  have h_pre : (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2)) ⁻¹' {(u, a, (y₁, y₂))}
      = ({(u, a, y₁, y₂)} : Set (U × α × β₁ × β₂)) := by
    ext ⟨u', a', z₁', z₂'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [h_pre, bcJointDistribution_singleton_eq pU K W u a y₁ y₂]

/-- The `(U, X, Ypair)`-split block-law singleton mass factorizes over coordinates as a product
of the per-coordinate reshaped joint masses. -/
lemma bc_block_law_UXY_singleton
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (u : Fin n → U) (x : Fin n → α) (yp : Fin n → β₁ × β₂) :
    ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).real {(u, x, yp)}
      = ∏ i, ((bcJointDistribution pU K W).map
          (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2))).real {(u i, x i, yp i)} := by
  classical
  have hbcUs : ∀ i, Measurable (bcUs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hbcXs : ∀ i, Measurable (bcXs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.fst
  have hbcYPs : ∀ i, Measurable (bcYPs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.snd
  have hg_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2)) :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  set g₀ : (ℕ → U × α × β₁ × β₂) → (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) :=
    fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω) with hg₀_def
  set ê : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) → (Fin n → U × α × (β₁ × β₂)) :=
    fun q i ↦ (q.1 i, q.2.1 i, q.2.2 i) with hê_def
  have hg₀_meas : Measurable g₀ :=
    (measurable_jointRV bcUs hbcUs n).prodMk
      ((measurable_jointRV bcXs hbcXs n).prodMk (measurable_jointRV bcYPs hbcYPs n))
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))
  set ρ : Measure (Fin n → U × α × (β₁ × β₂)) :=
    (bcAmbientMeasure pU K W).map (jointRV (macJointSequence bcUs bcXs bcYPs) n) with hρ_def
  haveI : IsProbabilityMeasure
      ((bcJointDistribution pU K W).map (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2))) :=
    Measure.isProbabilityMeasure_map hg_meas.aemeasurable
  have hρ_eq : ρ = Measure.pi (fun _ : Fin n ↦
      (bcJointDistribution pU K W).map (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2))) := by
    refine block_law_X_eq_pi_p (bcAmbientMeasure pU K W) (macJointSequence bcUs bcXs bcYPs)
      (fun i ↦ measurable_macJointSequence bcUs bcXs bcYPs hbcUs hbcXs hbcYPs i)
      (bcAmbient_iIndepFun_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2)) hg_meas)
      (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2)) hg_meas i)
      ((bcJointDistribution pU K W).map (fun q ↦ (q.1, q.2.1, q.2.2))) ?_ n
    rw [show (macJointSequence bcUs bcXs bcYPs 0 : (ℕ → U × α × β₁ × β₂) → U × α × (β₁ × β₂))
          = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2)) (ω 0) from rfl,
      bcAmbient_map_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2)) hg_meas 0]
  have hν_eq_ρ : ((bcAmbientMeasure pU K W).map g₀).map ê = ρ := by
    rw [Measure.map_map hê_meas hg₀_meas, hρ_def]; congr 1
  have h_pre : ê ⁻¹' {ê (u, x, yp)}
      = {((u, x, yp) : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂))} := by
    ext ⟨v, w, z⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hv : v = u := by funext i; exact congrArg (·.1) (congrFun h i)
      have hw : w = x := by funext i; exact congrArg (fun p ↦ p.2.1) (congrFun h i)
      have hz : z = yp := by funext i; exact congrArg (fun p ↦ p.2.2) (congrFun h i)
      rw [hv, hw, hz]
    · intro h; rw [h]
  calc ((bcAmbientMeasure pU K W).map g₀).real {(u, x, yp)}
      = ((bcAmbientMeasure pU K W).map g₀).real (ê ⁻¹' {ê (u, x, yp)}) := by rw [h_pre]
    _ = (((bcAmbientMeasure pU K W).map g₀).map ê).real {ê (u, x, yp)} :=
        (map_measureReal_apply hê_meas (measurableSet_singleton _)).symm
    _ = ρ.real {ê (u, x, yp)} := by rw [hν_eq_ρ]
    _ = (Measure.pi (fun _ : Fin n ↦
          (bcJointDistribution pU K W).map (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2)))).real
          {fun i ↦ (u i, x i, yp i)} := by rw [hρ_eq]
    _ = ∏ i, ((bcJointDistribution pU K W).map
          (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2))).real {(u i, x i, yp i)} :=
        measureReal_pi_singleton_eq_prod _ _

/-- **Master superposition channel fold.**  The `(U, X, Ypair)`-split block law of a finite
set `T` equals the average over the cloud codeword `u ~ pUⁿ` and the *conditional* satellite
codeword `x ~ Πₗ K(uₗ)` of the paired-channel mass of the corresponding slice of `T`.  This is
the BC analogue of `mac_chan_fold_triple_set`, with the conditional (superposition) satellite
law replacing the second MAC input's flat product. -/
lemma bc_chan_fold_master
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂))) :
    ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).real T
      = ∑ u : Fin n → U, ∑ x : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
            * (Measure.pi (fun l ↦ K (u l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real {y | (u, x, y) ∈ T} := by
  classical
  set νt : Measure ((Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂)) :=
    (bcAmbientMeasure pU K W).map
      (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω)) with hνt_def
  haveI : IsProbabilityMeasure νt := by
    rw [hνt_def]
    exact Measure.isProbabilityMeasure_map
      ((measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).prodMk
        ((measurable_jointRV bcXs (fun i ↦ (measurable_pi_apply i).snd.fst) n).prodMk
          (measurable_jointRV bcYPs (fun i ↦ (measurable_pi_apply i).snd.snd) n))).aemeasurable
  have h_single : ∀ (u : Fin n → U) (x : Fin n → α) (yp : Fin n → β₁ × β₂),
      νt.real {(u, x, yp)}
        = (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
          * (Measure.pi (fun l ↦ K (u l))).real {x}
          * (Measure.pi (fun i ↦ W (x i))).real {yp} := by
    intro u x yp
    rw [hνt_def, bc_block_law_UXY_singleton pU K W n u x yp,
      Finset.prod_congr rfl
        (fun i _ ↦ bcJointDistribution_map_UXY_singleton pU K W (u i) (x i) (yp i)),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← measureReal_pi_singleton_eq_prod (fun _ : Fin n ↦ pU) u,
      ← measureReal_pi_singleton_eq_prod (fun l ↦ K (u l)) x,
      ← measureReal_pi_singleton_eq_prod (fun i ↦ W (x i)) yp]
  rw [measureReal_eq_sum_ite νt T, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [measureReal_eq_sum_ite (Measure.pi (fun i ↦ W (x i))) {y | (u, x, y) ∈ T}, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun yp _ ↦ ?_)
  simp only [Set.mem_setOf_eq]
  rw [h_single u x yp]
  by_cases h : (u, x, yp) ∈ T
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **`(U, Y₂)` channel fold (β₂-marginal form).**  The `Y₂`-block law of a finite set `T`
equals the cloud/satellite/channel average of the `β₂`-projected channel mass.  Derived from
the master fold by projecting out `U`, `X`, and the `β₁`-output.  This is the receiver-2
analytic core: the pair output is marginalized to `β₂`. -/
lemma bc_chan_fold_Y₂_set
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (T : Set (Fin n → β₂)) :
    ((bcAmbientMeasure pU K W).map (jointRV bcY₂s n)).real T
      = ∑ u : Fin n → U, ∑ x : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
            * (Measure.pi (fun l ↦ K (u l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real {y | (fun i ↦ (y i).2) ∈ T} := by
  classical
  have hmeas_master : Measurable (fun ω : ℕ → U × α × β₁ × β₂ ↦
      (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω)) :=
    (measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).prodMk
      ((measurable_jointRV bcXs (fun i ↦ (measurable_pi_apply i).snd.fst) n).prodMk
        (measurable_jointRV bcYPs (fun i ↦ (measurable_pi_apply i).snd.snd) n))
  have hproj_meas : Measurable
      (fun t : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) ↦ (fun i ↦ (t.2.2 i).2 : Fin n → β₂)) :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).snd
  have hmap : (bcAmbientMeasure pU K W).map (jointRV bcY₂s n)
      = ((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).map
        (fun t ↦ fun i ↦ (t.2.2 i).2) := by
    rw [Measure.map_map hproj_meas hmeas_master]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    bc_chan_fold_master pU K W n
      ((fun t ↦ (fun i ↦ (t.2.2 i).2 : Fin n → β₂)) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- **Receiver-2 wrong-cloud averaged swap.**  For a wrong cloud message `w₂' ≠ m.2`, the
two-tier random-codebook average of the wrong-cloud alias event (drawn independently of the
transmitted satellite `cX m`) equals the independent product law `(U-block) ⊗ (Y₂-block)`, and
is therefore at most `exp(−n (I(U; Y₂) − 3ε))`.  Combines the satellite single-row marginal
(`measurePreserving_eval`), the cloud two-row marginal (`codebook_marginal_two`), the `(U, Y₂)`
channel fold, and the independent-pair bound `bc_cloud_indep_prob_le`. -/
theorem bc_random_codebook_wrongcloud_swap
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (m : Fin M₁ × Fin M₂) (w₂' : Fin M₂) (hne : w₂' ≠ m.2) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU w₂', fun i ↦ (y i).2)
                      ∈ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfo₂ pU K W - 3 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set JTS := jointlyTypicalSet μ bcUs bcY₂s n ε with hJTS_def
  haveI : IsProbabilityMeasure (μ.map (jointRV bcUs n)) :=
    Measure.isProbabilityMeasure_map
      (measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (jointRV bcY₂s n)) :=
    Measure.isProbabilityMeasure_map
      (measurable_jointRV bcY₂s (fun i ↦ (measurable_pi_apply i).snd.snd.snd) n).aemeasurable
  -- Step 1: satellite single-row marginalization (per cloud codebook).
  have hsat : ∀ cU : BCCloudCodebook M₂ n U,
      (∑ cX : BCSatelliteCodebook M₁ M₂ n α, (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
          * (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ | (cU w₂', fun i ↦ (y i).2) ∈ JTS })
        = ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (cU w₂', fun i ↦ (y i).2) ∈ JTS } := by
    intro cU
    haveI : IsProbabilityMeasure (bcSatelliteCodebookMeasure K M₁ M₂ n cU) := by
      unfold bcSatelliteCodebookMeasure; infer_instance
    have hmp : (bcSatelliteCodebookMeasure K M₁ M₂ n cU).map (Function.eval m)
        = Measure.pi (fun l ↦ K (cU m.2 l)) :=
      (measurePreserving_eval
        (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l ↦ K (cU p.2 l))) m).map_eq
    have h1 := sum_weighted_map (bcSatelliteCodebookMeasure K M₁ M₂ n cU) (Function.eval m)
      (measurable_pi_apply m)
      (fun z : Fin n → α ↦ (Measure.pi (fun i ↦ W (z i))).real
        { y : Fin n → β₁ × β₂ | (cU w₂', fun i ↦ (y i).2) ∈ JTS })
    rw [hmp] at h1
    exact h1
  -- Step 2: the codebook average equals the independent product law of `(U-block) ⊗ (Y₂-block)`.
  have hmain :
      ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
          * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
              (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
                * (Measure.pi (fun i ↦ W (cX m i))).real
                    { y : Fin n → β₁ × β₂ | (cU w₂', fun i ↦ (y i).2) ∈ JTS }
        = ((μ.map (jointRV bcUs n)).prod (μ.map (jointRV bcY₂s n))).real JTS := by
    rw [show bcCloudCodebookMeasure pU M₂ n = codebookMeasure pU M₂ n from rfl]
    -- Fold the satellite tier and reduce the cloud codebook to two rows.
    have e1 : ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
          * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
              (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
                * (Measure.pi (fun i ↦ W (cX m i))).real
                    { y : Fin n → β₁ × β₂ | (cU w₂', fun i ↦ (y i).2) ∈ JTS }
        = ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
          * (fun a b ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (b, fun i ↦ (y i).2) ∈ JTS }) (cU m.2) (cU w₂') := by
      refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
      rw [hsat cU]
    rw [e1, codebook_marginal_two pU M₂ n m.2 w₂' hne.symm
        (fun a b ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
          * (Measure.pi (fun i ↦ W (x i))).real
              { y : Fin n → β₁ × β₂ | (b, fun i ↦ (y i).2) ∈ JTS })
        (fun _ _ ↦ Finset.sum_nonneg
          (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
    rw [mac_prodReal_eq_slice_sum (μ.map (jointRV bcUs n)) (μ.map (jointRV bcY₂s n)) JTS,
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ ↦ ?_)
    rw [bc_block_law_U pU K W n]
    have hslice : (μ.map (jointRV bcY₂s n)).real
          {y₂ : Fin n → β₂ | (b, y₂) ∈ JTS}
        = ∑ a : Fin n → U, ∑ x : Fin n → α,
            (Measure.pi (fun _ : Fin n ↦ pU)).real {a}
              * (Measure.pi (fun l ↦ K (a l))).real {x}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (b, fun i ↦ (y i).2) ∈ JTS } := by
      rw [bc_chan_fold_Y₂_set pU K W n {y₂ : Fin n → β₂ | (b, y₂) ∈ JTS}]
      rfl
    rw [hslice, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    ring
  rw [hmain]
  exact bc_cloud_indep_prob_le pU K W hpU hK hW n hε

/-- **`(U, Y₂)` channel fold (joint form).**  The joint `(U, Y₂)`-block law of a finite set
`T` equals the cloud/satellite/channel average of the `β₂`-projected channel mass, retaining
the cloud block `u` inside the slice.  Derived from the master fold by projecting out `X` and
the `β₁`-output while keeping `U`.  This is the receiver-2 correct-cloud analytic core, where
the transmitted cloud both indexes the slice and steers the satellite (the `U`-preserving
counterpart of `bc_chan_fold_Y₂_set`). -/
lemma bc_chan_fold_UY₂_set
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → U) × (Fin n → β₂))) :
    ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real T
      = ∑ u : Fin n → U, ∑ x : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
            * (Measure.pi (fun l ↦ K (u l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real {y | (u, fun i ↦ (y i).2) ∈ T} := by
  classical
  have hmeas_master : Measurable (fun ω : ℕ → U × α × β₁ × β₂ ↦
      (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω)) :=
    (measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).prodMk
      ((measurable_jointRV bcXs (fun i ↦ (measurable_pi_apply i).snd.fst) n).prodMk
        (measurable_jointRV bcYPs (fun i ↦ (measurable_pi_apply i).snd.snd) n))
  have hproj_meas : Measurable
      (fun t : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) ↦
        ((t.1, fun i ↦ (t.2.2 i).2) : (Fin n → U) × (Fin n → β₂))) :=
    measurable_fst.prodMk
      (measurable_pi_lambda _ fun i ↦
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).snd)
  have hmap : (bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))
      = ((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).map
        (fun t ↦ (t.1, fun i ↦ (t.2.2 i).2)) := by
    rw [Measure.map_map hproj_meas hmeas_master]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    bc_chan_fold_master pU K W n
      ((fun t ↦ ((t.1, fun i ↦ (t.2.2 i).2) : (Fin n → U) × (Fin n → β₂))) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- **Receiver-2 correct-cloud averaged swap (E0).**  The two-tier random-codebook average of
the correct-cloud atypical event equals the *joint* `(U, Y₂)`-block law of the atypical set:
the correct cloud `cU m.2` steers the satellite, so `(cU m.2, Y₂)` follows the ambient joint
law (not the independent product).  Combines the satellite single-row marginal
(`measurePreserving_eval`), the cloud single-row marginal (`codebook_marginal_one`), and the
joint `(U, Y₂)` channel fold (`bc_chan_fold_UY₂_set`).  This is a true equality; the typicality
LLN that makes the joint mass vanish is a separate receiver-2 leg. -/
theorem bc_random_codebook_E0₂_swap
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ}
    (m : Fin M₁ × Fin M₂) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU m.2, fun i ↦ (y i).2)
                      ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
      = ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
          { q : (Fin n → U) × (Fin n → β₂) |
            q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε } := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set JTS := jointlyTypicalSet μ bcUs bcY₂s n ε with hJTS_def
  -- Step 1: satellite single-row marginalization (per cloud codebook). The correct cloud
  -- `cU m.2` both steers the satellite and indexes the atypical slice.
  have hsat : ∀ cU : BCCloudCodebook M₂ n U,
      (∑ cX : BCSatelliteCodebook M₁ M₂ n α, (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
          * (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ | (cU m.2, fun i ↦ (y i).2) ∉ JTS })
        = ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (cU m.2, fun i ↦ (y i).2) ∉ JTS } := by
    intro cU
    haveI : IsProbabilityMeasure (bcSatelliteCodebookMeasure K M₁ M₂ n cU) := by
      unfold bcSatelliteCodebookMeasure; infer_instance
    have hmp : (bcSatelliteCodebookMeasure K M₁ M₂ n cU).map (Function.eval m)
        = Measure.pi (fun l ↦ K (cU m.2 l)) :=
      (measurePreserving_eval
        (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l ↦ K (cU p.2 l))) m).map_eq
    have h1 := sum_weighted_map (bcSatelliteCodebookMeasure K M₁ M₂ n cU) (Function.eval m)
      (measurable_pi_apply m)
      (fun z : Fin n → α ↦ (Measure.pi (fun i ↦ W (z i))).real
        { y : Fin n → β₁ × β₂ | (cU m.2, fun i ↦ (y i).2) ∉ JTS })
    rw [hmp] at h1
    exact h1
  -- Step 2: reduce the cloud codebook to the single transmitted row `m.2` via
  -- `codebook_marginal_one` (correct cloud, so only one row survives).
  rw [show bcCloudCodebookMeasure pU M₂ n = codebookMeasure pU M₂ n from rfl]
  have e1 : ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ | (cU m.2, fun i ↦ (y i).2) ∉ JTS }
      = ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * (fun a ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (a, fun i ↦ (y i).2) ∉ JTS }) (cU m.2) := by
    refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
    rw [hsat cU]
  rw [e1, codebook_marginal_one pU M₂ n m.2
      (fun a ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
        * (Measure.pi (fun i ↦ W (x i))).real
            { y : Fin n → β₁ × β₂ | (a, fun i ↦ (y i).2) ∉ JTS })
      (fun _ ↦ Finset.sum_nonneg
        (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
  -- Step 3: fold the resulting cloud/satellite/channel average back into the joint
  -- `(U, Y₂)`-block law of the atypical set.
  rw [bc_chan_fold_UY₂_set pU K W n {q | q ∉ JTS}]
  simp only [Set.mem_setOf_eq]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  ring

/-! ### Receiver-1 (strong) error analysis -/

/-- **Receiver-1 three-event Bonferroni bound.**  When the pair `m` is sent, the receiver-1
per-pair error probability of the superposition joint-typical decoder is bounded by three
sub-events along the `β₁`-projection `fun i ↦ (y i).1` of the block output:

* `E0` — the correct triple `(Uⁿ(m₂), Xⁿ(m), y₁)` is not jointly typical;
* `E_b` (wrong satellite, correct cloud) — some `m₁' ≠ m₁` makes
  `(Uⁿ(m₂), Xⁿ(m₁', m₂), y₁)` jointly typical;
* `E_c` (wrong cloud, any satellite) — some cloud alias `m₂' ≠ m₂` with any `m₁'` makes
  `(Uⁿ(m₂'), Xⁿ(m₁', m₂'), y₁)` jointly typical.

Because a wrong-cloud alias steers its satellite from an independent cloud, the two "correct
cloud / wrong cloud" families collapse the four MAC alias events into three: the MAC
`E1`/`E2`/`E3` split is absorbed as `E_b` (`m₂' = m₂`, `m₁' ≠ m₁`) and `E_c`
(`m₂' ≠ m₂`, any `m₁'`).  This is the receiver-1 analogue of `mac_errorProbAt_le_bonferroni4`
reworked to the superposition decoder; `E_b`/`E_c` are left as raw measure terms for the
exponent-bounding legs. -/
theorem bc_errorProbAt₁_le_bonferroni3
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α)
    (m : Fin M₁ × Fin M₂) :
    ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁ W m).toReal
      ≤ (Measure.pi (fun i ↦ W (cX m i))).real
          { y : Fin n → β₁ × β₂ |
            (cU m.2, cX m, fun i ↦ (y i).1) ∉
              macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
        + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
            (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1) ∈
                  macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
        + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                  (Finset.univ : Finset (Fin M₁)),
            (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1) ∈
                  macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε } := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set J : Set ((Fin n → U) × (Fin n → α) × (Fin n → β₁)) :=
    macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε with hJ_def
  -- Index sets for the two alias families.
  set S_b : Finset (Fin M₁) := (Finset.univ : Finset (Fin M₁)).erase m.1 with hS_b_def
  set S_c : Finset (Fin M₂ × Fin M₁) :=
    (Finset.univ : Finset (Fin M₂)).erase m.2 ×ˢ (Finset.univ : Finset (Fin M₁)) with hS_c_def
  set c : BroadcastCode M₁ M₂ n α β₁ β₂ := bcCodebookToCode pU K W hM₁ hM₂ ε cU cX with hc_def
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi (fun i ↦ W (cX m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  -- The three error events: E0 (correct triple atypical), E_b (wrong satellite / correct
  -- cloud), E_c (wrong cloud / any satellite).
  set E0 : Set (Fin n → β₁ × β₂) :=
    { y | (cU m.2, cX m, fun i ↦ (y i).1) ∉ J } with hE0_def
  set E_b : Fin M₁ → Set (Fin n → β₁ × β₂) :=
    fun a ↦ { y | (cU m.2, cX (a, m.2), fun i ↦ (y i).1) ∈ J } with hE_b_def
  set E_c : Fin M₂ × Fin M₁ → Set (Fin n → β₁ × β₂) :=
    fun p ↦ { y | (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1) ∈ J } with hE_c_def
  -- Step 1: the receiver-1 error event is contained in the union of the three events.
  have h_sub : c.errorEvent₁ m ⊆ (E0 ∪ ⋃ a ∈ S_b, E_b a) ∪ ⋃ p ∈ S_c, E_c p := by
    intro y hy
    rw [BroadcastCode.errorEvent₁, Set.mem_setOf_eq] at hy
    set y₁ : Fin n → β₁ := fun i ↦ (y i).1 with hy₁_def
    -- A typical alias pair `q ≠ (m.1, m.2)` lands in one of the two alias unions.
    have place : ∀ q : Fin M₁ × Fin M₂,
        (cU q.2, cX q, y₁) ∈ J → q ≠ (m.1, m.2) →
        y ∈ (E0 ∪ ⋃ a ∈ S_b, E_b a) ∪ ⋃ p ∈ S_c, E_c p := by
      intro q hq_mem hq_ne
      by_cases hb : q.2 = m.2
      · -- correct cloud, so the satellite index must be wrong (E_b).
        have ha : q.1 ≠ m.1 := fun ha ↦ hq_ne (Prod.ext_iff.mpr ⟨ha, hb⟩)
        refine Or.inl (Or.inr ?_)
        refine Set.mem_iUnion.mpr ⟨q.1, ?_⟩
        refine Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, ?_⟩
        show (cU m.2, cX (q.1, m.2), y₁) ∈ J
        rw [← hb]; exact hq_mem
      · -- wrong cloud, any satellite index (E_c).
        refine Or.inr ?_
        refine Set.mem_iUnion.mpr ⟨(q.2, q.1), ?_⟩
        refine Set.mem_iUnion.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩,
            Finset.mem_univ _⟩, ?_⟩
        show (cU q.2, cX (q.1, q.2), y₁) ∈ J
        exact hq_mem
    -- Case analyse on whether the correct triple is typical.
    by_cases hc_typ : (cU m.2, cX m, y₁) ∈ J
    · by_cases h_alias : ∃ q : Fin M₁ × Fin M₂, (cU q.2, cX q, y₁) ∈ J ∧ q ≠ (m.1, m.2)
      · obtain ⟨q, hq_mem, hq_ne⟩ := h_alias
        exact place q hq_mem hq_ne
      · exfalso
        apply hy
        -- No alias ⇒ `(m.1, m.2)` is the unique typical pair ⇒ the decoder outputs it.
        have huniq : ∃! p : Fin M₁ × Fin M₂,
            (cU p.2, cX p, y₁) ∈
              macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε := by
          refine ⟨(m.1, m.2), hc_typ, ?_⟩
          intro p hp
          by_contra hne
          exact h_alias ⟨p, hp, hne⟩
        change (bcJointTypicalDecoder pU K W hM₁ hM₂ ε cU cX y₁).1 = m.1
        unfold bcJointTypicalDecoder
        rw [dif_pos huniq]
        rw [huniq.unique (Classical.choose_spec huniq.exists) hc_typ]
    · exact Or.inl (Or.inl hc_typ)
  -- Step 2: `errorProbAt₁` is the block-law measure of the error event (defeq).
  have h_real_eq : (c.errorProbAt₁ W m).toReal = ν.real (c.errorEvent₁ m) := rfl
  rw [h_real_eq]
  -- Step 3: monotonicity + union bound over the three events.
  calc ν.real (c.errorEvent₁ m)
      ≤ ν.real ((E0 ∪ ⋃ a ∈ S_b, E_b a) ∪ ⋃ p ∈ S_c, E_c p) :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ν.real (E0 ∪ ⋃ a ∈ S_b, E_b a) + ν.real (⋃ p ∈ S_c, E_c p) :=
        measureReal_union_le _ _
    _ ≤ (ν.real E0 + ν.real (⋃ a ∈ S_b, E_b a)) + ν.real (⋃ p ∈ S_c, E_c p) :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ (ν.real E0 + ∑ a ∈ S_b, ν.real (E_b a)) + ∑ p ∈ S_c, ν.real (E_c p) :=
        add_le_add (add_le_add le_rfl (measureReal_biUnion_finset_le _ _))
          (measureReal_biUnion_finset_le _ _)

/-! ### Receiver-1 random-coding averaged swaps (E_b, E_c) -/

/-- Two-coordinate marginalization of a finite product measure: summing a `(cᵢ, cⱼ)`-weighted
functional against `Measure.pi ρ` factors into the double sum over the two independent
coordinate marginals `ρ i`, `ρ j` (for distinct `i ≠ j`).  The satellite generalization of
`codebook_marginal_two`, allowing the per-coordinate measures to differ.
@audit:ok -/
private lemma pi_marginal_two {ι δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] [MeasurableSpace δ] [MeasurableSingletonClass δ]
    (ρ : ι → Measure δ) [∀ i, IsProbabilityMeasure (ρ i)]
    (i j : ι) (hij : i ≠ j) (g : δ → δ → ℝ) :
    ∑ c : ι → δ, (Measure.pi ρ).real {c} * g (c i) (c j)
      = ∑ x : δ, ∑ x' : δ, (ρ i).real {x} * (ρ j).real {x'} * g x x' := by
  classical
  haveI : MeasurableSingletonClass (ι → δ) := Pi.instMeasurableSingletonClass
  have h_cm : ∀ c : ι → δ, (Measure.pi ρ).real {c} = ∏ k : ι, (ρ k).real {c k} := by
    intro c
    rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  rw [Finset.sum_congr rfl (fun c _ ↦ by rw [h_cm c])]
  let toFun : (ι → δ) → δ × δ × ({k : ι // k ≠ i ∧ k ≠ j} → δ) :=
    fun c ↦ (c i, c j, fun k ↦ c k.1)
  let invFun : δ × δ × ({k : ι // k ≠ i ∧ k ≠ j} → δ) → (ι → δ) :=
    fun ⟨x, x', c''⟩ idx ↦
      if h : idx = i then x
      else if h' : idx = j then x'
      else c'' ⟨idx, h, h'⟩
  have left_inv : ∀ c, invFun (toFun c) = c := by
    intro c
    funext idx
    by_cases h1 : idx = i
    · subst h1; simp [toFun, invFun]
    · by_cases h2 : idx = j
      · subst h2; simp [toFun, invFun, h1]
      · simp [toFun, invFun, h1, h2]
  have right_inv : ∀ q, toFun (invFun q) = q := by
    intro ⟨x, x', c''⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [toFun, invFun]
    · simp [toFun, invFun, hij.symm]
    · funext ⟨idx, h1, h2⟩
      simp [toFun, invFun, h1, h2]
  set e : (ι → δ) ≃ δ × δ × ({k : ι // k ≠ i ∧ k ≠ j} → δ) :=
    { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }
  rw [← Equiv.sum_comp e.symm (fun c ↦ (∏ k : ι, (ρ k).real {c k}) * g (c i) (c j))]
  show ∑ y : δ × δ × _,
        (∏ k : ι, (ρ k).real {(invFun y) k}) * g ((invFun y) i) ((invFun y) j) = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x' _ ↦ ?_)
  have h_at_i : ∀ (c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ), invFun (x, x', c'') i = x := by
    intro c''; show (if _h : i = i then x else _) = x; simp
  have h_at_j : ∀ (c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ), invFun (x, x', c'') j = x' := by
    intro c''
    show (if _h : j = i then x else if _h' : j = j then x' else _) = x'
    simp [hij.symm]
  have h_split : ∀ (c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ),
      (∏ k : ι, (ρ k).real {(invFun (x, x', c'')) k})
        = (ρ i).real {x} * (ρ j).real {x'} *
          ∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j,
            (ρ k).real {(invFun (x, x', c'')) k} := by
    intro c''
    rw [← Finset.mul_prod_erase Finset.univ (fun k ↦ (ρ k).real {(invFun (x, x', c'')) k})
          (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase i)
          (fun k ↦ (ρ k).real {(invFun (x, x', c'')) k})
          (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)]
    rw [h_at_i c'', h_at_j c'']
    ring
  rw [Finset.sum_congr rfl (fun c'' _ ↦ by rw [h_split c'', h_at_i c'', h_at_j c''])]
  have h_inner_eq : ∀ (c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ),
      ((ρ i).real {x} * (ρ j).real {x'} *
        ∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j,
          (ρ k).real {(invFun (x, x', c'')) k}) * g x x'
      = ((ρ i).real {x} * (ρ j).real {x'} * g x x') *
        ∏ k : {k : ι // k ≠ i ∧ k ≠ j}, (ρ k.1).real {c'' k} := by
    intro c''
    have h_other_prod :
        (∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j,
            (ρ k).real {(invFun (x, x', c'')) k})
        = ∏ k : {k : ι // k ≠ i ∧ k ≠ j}, (ρ k.1).real {c'' k} := by
      have h_val : ∀ idx : ι, ∀ h_ne_i : idx ≠ i, ∀ h_ne_j : idx ≠ j,
          (invFun (x, x', c'')) idx = c'' ⟨idx, h_ne_i, h_ne_j⟩ := by
        intro idx h_ne_i h_ne_j
        show (if _h : idx = i then x else if _h' : idx = j then x' else c'' ⟨idx, _h, _h'⟩)
          = c'' ⟨idx, h_ne_i, h_ne_j⟩
        simp [h_ne_i, h_ne_j]
      symm
      apply Finset.prod_bij (fun (k : {k : ι // k ≠ i ∧ k ≠ j}) _ ↦ k.1)
      · intro a _
        exact Finset.mem_erase.mpr ⟨a.2.2, Finset.mem_erase.mpr ⟨a.2.1, Finset.mem_univ _⟩⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro b hb
        have hb1 : b ≠ j := (Finset.mem_erase.mp hb).1
        have hb2 : b ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
        exact ⟨⟨b, hb2, hb1⟩, Finset.mem_univ _, rfl⟩
      · intro a _
        rw [h_val a.1 a.2.1 a.2.2]
    rw [h_other_prod]; ring
  rw [Finset.sum_congr rfl (fun c'' _ ↦ h_inner_eq c'')]
  rw [← Finset.mul_sum]
  have h_sum_other : ∑ c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ,
      ∏ k : {k : ι // k ≠ i ∧ k ≠ j}, (ρ k.1).real {c'' k} = 1 := by
    haveI : MeasurableSingletonClass ({k : ι // k ≠ i ∧ k ≠ j} → δ) :=
      Pi.instMeasurableSingletonClass
    have h1 : ∀ c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ,
        (Measure.pi (fun k : {k : ι // k ≠ i ∧ k ≠ j} ↦ ρ k.1)).real {c''}
          = ∏ k : {k : ι // k ≠ i ∧ k ≠ j}, (ρ k.1).real {c'' k} := by
      intro c''
      rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]; rfl
    calc ∑ c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ,
          ∏ k : {k : ι // k ≠ i ∧ k ≠ j}, (ρ k.1).real {c'' k}
        = ∑ c'' : {k : ι // k ≠ i ∧ k ≠ j} → δ,
            (Measure.pi (fun k : {k : ι // k ≠ i ∧ k ≠ j} ↦ ρ k.1)).real {c''} :=
          Finset.sum_congr rfl (fun c'' _ ↦ (h1 c'').symm)
      _ = 1 := sum_measureReal_singleton_univ_eq_one _
  rw [h_sum_other, mul_one]

/-- **`(U, Y₁)` channel fold (β₁-marginal form).**  The `Y₁`-block law of a finite set `T`
equals the cloud/satellite/channel average of the `β₁`-projected channel mass.  The
receiver-1 analogue of `bc_chan_fold_Y₂_set`.
@audit:ok -/
lemma bc_chan_fold_Y₁_set
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (T : Set (Fin n → β₁)) :
    ((bcAmbientMeasure pU K W).map (jointRV bcY₁s n)).real T
      = ∑ u : Fin n → U, ∑ x : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
            * (Measure.pi (fun l ↦ K (u l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real {y | (fun i ↦ (y i).1) ∈ T} := by
  classical
  have hmeas_master : Measurable (fun ω : ℕ → U × α × β₁ × β₂ ↦
      (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω)) :=
    (measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).prodMk
      ((measurable_jointRV bcXs (fun i ↦ (measurable_pi_apply i).snd.fst) n).prodMk
        (measurable_jointRV bcYPs (fun i ↦ (measurable_pi_apply i).snd.snd) n))
  have hproj_meas : Measurable
      (fun t : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) ↦ (fun i ↦ (t.2.2 i).1 : Fin n → β₁)) :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).fst
  have hmap : (bcAmbientMeasure pU K W).map (jointRV bcY₁s n)
      = ((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).map
        (fun t ↦ fun i ↦ (t.2.2 i).1) := by
    rw [Measure.map_map hproj_meas hmeas_master]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    bc_chan_fold_master pU K W n
      ((fun t ↦ (fun i ↦ (t.2.2 i).1 : Fin n → β₁)) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- The joint information `I((U, X); Y₁) = H(U, X) + H(Y₁) − H(U, X, Y₁)` of the per-coordinate
joint law.  This is the exponent of the receiver-1 wrong-cloud error: a wrong cloud alias
carries an *independent* `(U, X)` pair, so the false-alarm exponent is the full joint
information `I((U, X); Y₁)` (which under degradedness dominates `R₁ + R₂`).
@audit:ok -/
noncomputable def bcInfoJoint
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) : ℝ :=
  entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1))
    + entropy (bcJointDistribution pU K W) (fun q ↦ q.2.2.1)
    - entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1, q.2.2.1))

/-- The `(U, X)`-split block-law singleton mass factorizes as `pUⁿ{u} · Kⁿ(u){x}`, derived
from the ambient block law of the paired `(U, X)` coordinate.
@audit:ok -/
lemma bc_block_law_UX_paired_singleton
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (u : Fin n → U) (x : Fin n → α) :
    ((bcAmbientMeasure pU K W).map (jointRV (jointSequence bcUs bcXs) n)).real
        {fun i ↦ (u i, x i)}
      = (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
          * (Measure.pi (fun l ↦ K (u l))).real {x} := by
  classical
  have hsel_meas : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  haveI : IsProbabilityMeasure
      ((bcJointDistribution pU K W).map (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1))) :=
    Measure.isProbabilityMeasure_map hsel_meas.aemeasurable
  have hρ_eq : (bcAmbientMeasure pU K W).map (jointRV (jointSequence bcUs bcXs) n)
      = Measure.pi (fun _ : Fin n ↦
          (bcJointDistribution pU K W).map (fun q ↦ (q.1, q.2.1))) := by
    refine block_law_X_eq_pi_p (bcAmbientMeasure pU K W) (jointSequence bcUs bcXs)
      (fun i ↦ measurable_jointSequence bcUs bcXs (fun i ↦ (measurable_pi_apply i).fst)
        (fun i ↦ (measurable_pi_apply i).snd.fst) i)
      (bcAmbient_iIndepFun_coord pU K W (fun q ↦ (q.1, q.2.1)) hsel_meas)
      (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1)) hsel_meas i)
      ((bcJointDistribution pU K W).map (fun q ↦ (q.1, q.2.1))) ?_ n
    rw [show (jointSequence bcUs bcXs 0 : (ℕ → U × α × β₁ × β₂) → U × α)
          = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) (ω 0) from rfl,
      bcAmbient_map_coord pU K W (fun q ↦ (q.1, q.2.1)) hsel_meas 0]
  rw [hρ_eq, measureReal_pi_singleton_eq_prod,
    Finset.prod_congr rfl (fun i _ ↦ bcJointDistribution_map_UX_singleton pU K W (u i) (x i)),
    Finset.prod_mul_distrib,
    ← measureReal_pi_singleton_eq_prod (fun _ : Fin n ↦ pU) u,
    ← measureReal_pi_singleton_eq_prod (fun l ↦ K (u l)) x]

/-- **Receiver-1 wrong-cloud independent-pair bound.**  The distributed average over an
independent `(U, X)` pair and the `Y₁`-block law of the jointly-typical event is at most
`exp(−n (I((U, X); Y₁) − 3ε))`.  BC instantiation of `macJTS_indep_prob_le_both` with the
axes `(U, X) ⟂ Y₁`.
@audit:ok -/
theorem bc_joint_indep_prob_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∑ u' : Fin n → U, ∑ x' : Fin n → α,
        (Measure.pi (fun _ : Fin n ↦ pU)).real {u'}
          * (Measure.pi (fun l ↦ K (u' l))).real {x'}
          * ((bcAmbientMeasure pU K W).map (jointRV bcY₁s n)).real
              { y₁ : Fin n → β₁ |
                (u', x', y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfoJoint pU K W - 3 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  have hbcUs : ∀ i, Measurable (bcUs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hbcXs : ∀ i, Measurable (bcXs (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.fst
  have hbcY₁s : ∀ i, Measurable (bcY₁s (U := U) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.fst
  have hselUX : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hselY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hselUXY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ ((q.1, q.2.1), q.2.2.1)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  haveI : IsProbabilityMeasure (μ.map (jointRV (jointSequence bcUs bcXs) n)) :=
    Measure.isProbabilityMeasure_map
      (measurable_jointRV (jointSequence bcUs bcXs)
        (fun i ↦ measurable_jointSequence bcUs bcXs hbcUs hbcXs i) n).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (jointRV bcY₁s n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV bcY₁s hbcY₁s n).aemeasurable
  set Puxblk := μ.map (jointRV (jointSequence bcUs bcXs) n) with hPuxblk_def
  set Py₁blk := μ.map (jointRV bcY₁s n) with hPy₁blk_def
  -- The gateway independent-pair bound (reshaped macJTS).
  have h_gw := macJTS_indep_prob_le_both μ bcUs bcXs bcY₁s hbcUs hbcXs hbcY₁s
    (bcAmbient_iIndepFun_coord pU K W (fun q ↦ (q.1, q.2.1)) hselUX)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1)) hselUX i)
    (bcAmbient_iIndepFun_coord pU K W (fun q ↦ q.2.2.1) hselY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.2.1) hselY₁ i)
    (fun p ↦ bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun q ↦ (q.1, q.2.1)) hselUX 0
      p (p.1, p.2, Classical.arbitrary β₁, Classical.arbitrary β₂) rfl)
    (fun y ↦ bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun q ↦ q.2.2.1) hselY₁ 0
      y (Classical.arbitrary U, Classical.arbitrary α, y, Classical.arbitrary β₂) rfl)
    (fun p ↦ bcAmbient_coord_marginal_pos pU K W hpU hK hW (fun q ↦ ((q.1, q.2.1), q.2.2.1))
      hselUXY₁ 0 p (p.1.1, p.1.2, p.2, Classical.arbitrary β₂) rfl)
    n hε
  -- Rewrite the distributed sum as the product-measure mass of the reshaped set.
  set e : (Fin n → U × α) ≃ (Fin n → U) × (Fin n → α) :=
    { toFun := fun w ↦ ((fun i ↦ (w i).1), (fun i ↦ (w i).2))
      invFun := fun q ↦ fun i ↦ (q.1 i, q.2 i)
      left_inv := fun w ↦ by funext i; rfl
      right_inv := fun q ↦ rfl } with he_def
  have h_dist :
      (Puxblk.prod Py₁blk).real
          ((fun q : (Fin n → U × α) × (Fin n → β₁) ↦
              (((fun i ↦ (q.1 i).1) : Fin n → U),
                (((fun i ↦ (q.1 i).2) : Fin n → α), q.2))) ⁻¹'
            macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε)
        = ∑ u' : Fin n → U, ∑ x' : Fin n → α,
            (Measure.pi (fun _ : Fin n ↦ pU)).real {u'}
              * (Measure.pi (fun l ↦ K (u' l))).real {x'}
              * Py₁blk.real
                  { y₁ | (u', x', y₁) ∈ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε } := by
    rw [mac_prodReal_eq_slice_sum Puxblk Py₁blk]
    rw [← Equiv.sum_comp e.symm
      (fun w ↦ Puxblk.real {w} * Py₁blk.real
        { y₁ | (w, y₁) ∈ (fun q : (Fin n → U × α) × (Fin n → β₁) ↦
              (((fun i ↦ (q.1 i).1) : Fin n → U),
                (((fun i ↦ (q.1 i).2) : Fin n → α), q.2))) ⁻¹'
            macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε }), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun u' _ ↦ Finset.sum_congr rfl (fun x' _ ↦ ?_))
    have hsym : (e.symm (u', x') : Fin n → U × α) = fun i ↦ (u' i, x' i) := rfl
    rw [hsym, bc_block_law_UX_paired_singleton pU K W n u' x']
    congr 2
  -- Assemble: distributed sum ≤ exp, exponent rewritten to bcInfoJoint.
  rw [← h_dist]
  refine h_gw.trans (le_of_eq ?_)
  have hHUX : entropy μ (jointSequence bcUs bcXs 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1)) := by
    rw [show (jointSequence bcUs bcXs 0 : (ℕ → U × α × β₁ × β₂) → U × α)
          = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) (ω 0) from rfl]
    exact bcAmbient_entropy_coord pU K W (fun q ↦ (q.1, q.2.1)) hselUX 0
  have hHY₁ : entropy μ (bcY₁s 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ q.2.2.1) :=
    bcAmbient_entropy_coord pU K W (fun q ↦ q.2.2.1) hselY₁ 0
  have hHUXY₁ : entropy μ (macJointSequence bcUs bcXs bcY₁s 0)
      = entropy (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1, q.2.2.1)) := by
    rw [show (macJointSequence bcUs bcXs bcY₁s 0 : (ℕ → U × α × β₁ × β₂) → U × α × β₁)
          = fun ω ↦ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) (ω 0) from rfl]
    exact bcAmbient_entropy_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2.1))
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))) 0
  rw [hHUX, hHY₁, hHUXY₁]
  unfold bcInfoJoint
  ring

/-- **Unconditional conditional-slice satellite covering bound.**  The typicality hypotheses
of `bc_conditional_slice_prob_le` are dropped: when `u` or `y₁` is atypical the slice is empty
(joint typicality forces both marginals typical), so the bound holds vacuously; when both are
typical it is the gateway atom.
@audit:ok -/
theorem bc_conditional_slice_prob_le_uncond
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ a : U, 0 < pU.real {a}) (hK : ∀ (a : U) (b : α), 0 < (K a).real {b})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {n : ℕ} {ε : ℝ}
    (u : Fin n → U) (y₁ : Fin n → β₁) :
    (Measure.pi (fun l : Fin n ↦ K (u l))).real
        { x : Fin n → α |
          (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
  classical
  by_cases hu : u ∈ typicalSet (bcAmbientMeasure pU K W) bcUs n ε
  · by_cases hy₁ : y₁ ∈ typicalSet (bcAmbientMeasure pU K W) bcY₁s n ε
    · exact bc_conditional_slice_prob_le pU K W hpU hK hW u y₁ hu hy₁
    · have hempty : { x : Fin n → α |
          (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε } = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Set.mem_setOf_eq, mem_macJointlyTypicalSet_iff] at hx
        exact hy₁ hx.2.2.1
      rw [hempty, measureReal_empty]
      exact Real.exp_nonneg _
  · have hempty : { x : Fin n → α |
        (u, x, y₁) ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε } = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_setOf_eq, mem_macJointlyTypicalSet_iff] at hx
      exact hu hx.1
    rw [hempty, measureReal_empty]
    exact Real.exp_nonneg _

/-- **Receiver-1 wrong-satellite/correct-cloud averaged swap (E_b).**  For a wrong satellite
index `m₁' ≠ m.1` (same cloud column `m.2`), the two-tier random-codebook average of the
wrong-satellite alias event is at most `exp(−n (I(X; Y₁ ∣ U) − 4ε))`.  Both the transmitted
satellite `cX m` (channel driver) and the alias `cX (m₁', m.2)` are drawn i.i.d. from the same
cloud column `m.2`; averaging out the alias inside the channel integral yields the conditional
covering bound `bc_conditional_slice_prob_le_uncond`.
@audit:ok -/
theorem bc_random_codebook_Eb_swap
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ}
    (m : Fin M₁ × Fin M₂) (m₁' : Fin M₁) (hne : m₁' ≠ m.1) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1)
                      ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set J := macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε with hJ_def
  haveI : IsProbabilityMeasure (bcCloudCodebookMeasure pU M₂ n) := by
    unfold bcCloudCodebookMeasure; infer_instance
  have hij : m ≠ (m₁', m.2) := by
    intro h; exact hne (congrArg Prod.fst h).symm
  -- The per-cloud-codebook bound: average out the two same-column satellite rows.
  have hperCU : ∀ cU : BCCloudCodebook M₂ n U,
      ∑ cX : BCSatelliteCodebook M₁ M₂ n α, (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
          * (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ | (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1) ∈ J }
        ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
    intro cU
    -- Step 1: two-row satellite marginalization (both rows drawn from column `m.2`).
    have hmarg : ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
          (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
            * (Measure.pi (fun i ↦ W (cX m i))).real
                { y : Fin n → β₁ × β₂ | (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1) ∈ J }
        = ∑ x : Fin n → α, ∑ x' : Fin n → α,
            (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
              * (Measure.pi (fun l ↦ K (cU m.2 l))).real {x'}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J } :=
      pi_marginal_two (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l : Fin n ↦ K (cU p.2 l)))
        m (m₁', m.2) hij
        (fun x x' ↦ (Measure.pi (fun i ↦ W (x i))).real
          { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J })
    rw [hmarg]
    -- Step 2: for each transmitted `x`, average out the wrong satellite `x'` (Fubini) and apply
    -- the unconditional covering bound.
    have hx : ∀ x : Fin n → α,
        ∑ x' : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x'}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J }
          ≤ Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
      intro x
      haveI : IsProbabilityMeasure (Measure.pi (fun i ↦ W (x i))) := by infer_instance
      have hstep : ∑ x' : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x'}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J }
          = ∑ y : Fin n → β₁ × β₂, (Measure.pi (fun i ↦ W (x i))).real {y}
              * (Measure.pi (fun l ↦ K (cU m.2 l))).real
                  { x' : Fin n → α | (cU m.2, x', fun i ↦ (y i).1) ∈ J } := by
        rw [Finset.sum_congr rfl (fun x' _ ↦ by
          rw [measureReal_eq_sum_ite (Measure.pi (fun i ↦ W (x i)))
            { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J }, Finset.mul_sum])]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ ↦ ?_)
        rw [measureReal_eq_sum_ite (Measure.pi (fun l ↦ K (cU m.2 l)))
          { x' : Fin n → α | (cU m.2, x', fun i ↦ (y i).1) ∈ J }, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x' _ ↦ ?_)
        by_cases hc : (cU m.2, x', fun i ↦ (y i).1) ∈ J
        · simp only [Set.mem_setOf_eq, hc, if_true]; ring
        · simp only [Set.mem_setOf_eq, hc, if_false]; ring
      rw [hstep]
      calc ∑ y : Fin n → β₁ × β₂, (Measure.pi (fun i ↦ W (x i))).real {y}
              * (Measure.pi (fun l ↦ K (cU m.2 l))).real
                  { x' : Fin n → α | (cU m.2, x', fun i ↦ (y i).1) ∈ J }
          ≤ ∑ y : Fin n → β₁ × β₂, (Measure.pi (fun i ↦ W (x i))).real {y}
              * Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
            refine Finset.sum_le_sum (fun y _ ↦ ?_)
            exact mul_le_mul_of_nonneg_left
              (bc_conditional_slice_prob_le_uncond pU K W hpU hK hW (cU m.2) (fun i ↦ (y i).1))
              measureReal_nonneg
        _ = Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
            rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]
    calc ∑ x : Fin n → α, ∑ x' : Fin n → α,
            (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
              * (Measure.pi (fun l ↦ K (cU m.2 l))).real {x'}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J }
        ≤ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
            * Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
          refine Finset.sum_le_sum (fun x _ ↦ ?_)
          rw [show ∑ x' : Fin n → α,
              (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
                * (Measure.pi (fun l ↦ K (cU m.2 l))).real {x'}
                * (Measure.pi (fun i ↦ W (x i))).real
                    { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J }
            = (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
                * ∑ x' : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x'}
                    * (Measure.pi (fun i ↦ W (x i))).real
                        { y : Fin n → β₁ × β₂ | (cU m.2, x', fun i ↦ (y i).1) ∈ J } from by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x' _ ↦ by ring)]
          exact mul_le_mul_of_nonneg_left (hx x) measureReal_nonneg
      _ = Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
          rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]
  -- Average over the cloud codebook.
  calc ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
          * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
              (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
                * (Measure.pi (fun i ↦ W (cX m i))).real
                    { y : Fin n → β₁ × β₂ | (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1) ∈ J }
      ≤ ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
          * Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
        refine Finset.sum_le_sum (fun cU _ ↦ ?_)
        exact mul_le_mul_of_nonneg_left (hperCU cU) measureReal_nonneg
    _ = Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)) := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]

/-- **Receiver-1 wrong-cloud averaged swap (E_c).**  For a wrong cloud message `p.1 ≠ m.2`
(with any satellite index `p.2`), the two-tier random-codebook average of the wrong-cloud alias
event is at most `exp(−n (I((U, X); Y₁) − 3ε))`.  The wrong cloud `cU p.1` and its satellite
`cX (p.2, p.1)` are drawn independently of the transmitted `(cX m)`-driven channel, giving the
independent-pair bound `bc_joint_indep_prob_le`.
@audit:ok -/
theorem bc_random_codebook_Ec_swap
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (m : Fin M₁ × Fin M₂) (p : Fin M₂ × Fin M₁) (hp : p.1 ≠ m.2) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1)
                      ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (bcInfoJoint pU K W - 3 * ε)) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set J := macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε with hJ_def
  have hij_sat : m ≠ (p.2, p.1) := by
    intro h; exact hp (congrArg Prod.snd h).symm
  have hij_cloud : m.2 ≠ p.1 := fun h ↦ hp h.symm
  -- Step 1: two-row satellite marginalization (transmitted column `m.2`, alias column `p.1`).
  have hsat : ∀ cU : BCCloudCodebook M₂ n U,
      ∑ cX : BCSatelliteCodebook M₁ M₂ n α, (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
          * (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ | (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1) ∈ J }
        = ∑ x : Fin n → α, ∑ x' : Fin n → α,
            (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
              * (Measure.pi (fun l ↦ K (cU p.1 l))).real {x'}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (cU p.1, x', fun i ↦ (y i).1) ∈ J } :=
    fun cU ↦ pi_marginal_two (fun q : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l : Fin n ↦ K (cU q.2 l)))
      m (p.2, p.1) hij_sat
      (fun x x' ↦ (Measure.pi (fun i ↦ W (x i))).real
        { y : Fin n → β₁ × β₂ | (cU p.1, x', fun i ↦ (y i).1) ∈ J })
  rw [show bcCloudCodebookMeasure pU M₂ n = codebookMeasure pU M₂ n from rfl]
  have e1 : ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ | (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1) ∈ J }
      = ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * (fun a a' ↦ ∑ x : Fin n → α, ∑ x' : Fin n → α,
            (Measure.pi (fun l ↦ K (a l))).real {x}
              * (Measure.pi (fun l ↦ K (a' l))).real {x'}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (a', x', fun i ↦ (y i).1) ∈ J }) (cU m.2) (cU p.1) := by
    refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
    rw [hsat cU]
  rw [e1, codebook_marginal_two pU M₂ n m.2 p.1 hij_cloud
      (fun a a' ↦ ∑ x : Fin n → α, ∑ x' : Fin n → α,
        (Measure.pi (fun l ↦ K (a l))).real {x}
          * (Measure.pi (fun l ↦ K (a' l))).real {x'}
          * (Measure.pi (fun i ↦ W (x i))).real
              { y : Fin n → β₁ × β₂ | (a', x', fun i ↦ (y i).1) ∈ J })
      (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg
        (fun _ _ ↦ mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
          measureReal_nonneg)))]
  -- Step 2: reorder the four sums into the distributed form, folding the transmitted `(u, x)`
  -- into the `Y₁`-block law via `bc_chan_fold_Y₁_set`, and apply the independent-pair bound.
  have hreorder : ∑ u : Fin n → U, ∑ u' : Fin n → U,
        (Measure.pi (fun _ : Fin n ↦ pU)).real {u} * (Measure.pi (fun _ : Fin n ↦ pU)).real {u'}
          * ∑ x : Fin n → α, ∑ x' : Fin n → α,
              (Measure.pi (fun l ↦ K (u l))).real {x} * (Measure.pi (fun l ↦ K (u' l))).real {x'}
                * (Measure.pi (fun i ↦ W (x i))).real
                    { y : Fin n → β₁ × β₂ | (u', x', fun i ↦ (y i).1) ∈ J }
      = ∑ u' : Fin n → U, ∑ x' : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u'} * (Measure.pi (fun l ↦ K (u' l))).real {x'}
            * (μ.map (jointRV bcY₁s n)).real { y₁ | (u', x', y₁) ∈ J } := by
    have hExpandL : ∑ u : Fin n → U, ∑ u' : Fin n → U,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u} * (Measure.pi (fun _ : Fin n ↦ pU)).real {u'}
            * ∑ x : Fin n → α, ∑ x' : Fin n → α,
                (Measure.pi (fun l ↦ K (u l))).real {x} * (Measure.pi (fun l ↦ K (u' l))).real {x'}
                  * (Measure.pi (fun i ↦ W (x i))).real
                      { y : Fin n → β₁ × β₂ | (u', x', fun i ↦ (y i).1) ∈ J }
        = ∑ u : Fin n → U, ∑ u' : Fin n → U, ∑ x : Fin n → α, ∑ x' : Fin n → α,
            (Measure.pi (fun _ : Fin n ↦ pU)).real {u} * (Measure.pi (fun _ : Fin n ↦ pU)).real {u'}
              * (Measure.pi (fun l ↦ K (u l))).real {x} * (Measure.pi (fun l ↦ K (u' l))).real {x'}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (u', x', fun i ↦ (y i).1) ∈ J } := by
      refine Finset.sum_congr rfl (fun u _ ↦ Finset.sum_congr rfl (fun u' _ ↦ ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x' _ ↦ by ring)
    have hExpandR : ∑ u' : Fin n → U, ∑ x' : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u'} * (Measure.pi (fun l ↦ K (u' l))).real {x'}
            * (μ.map (jointRV bcY₁s n)).real { y₁ | (u', x', y₁) ∈ J }
        = ∑ u' : Fin n → U, ∑ x' : Fin n → α, ∑ u : Fin n → U, ∑ x : Fin n → α,
            (Measure.pi (fun _ : Fin n ↦ pU)).real {u} * (Measure.pi (fun _ : Fin n ↦ pU)).real {u'}
              * (Measure.pi (fun l ↦ K (u l))).real {x} * (Measure.pi (fun l ↦ K (u' l))).real {x'}
              * (Measure.pi (fun i ↦ W (x i))).real
                  { y : Fin n → β₁ × β₂ | (u', x', fun i ↦ (y i).1) ∈ J } := by
      refine Finset.sum_congr rfl (fun u' _ ↦ Finset.sum_congr rfl (fun x' _ ↦ ?_))
      rw [bc_chan_fold_Y₁_set pU K W n { y₁ | (u', x', y₁) ∈ J }, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ ↦ ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ ↦ ?_)
      simp only [Set.mem_setOf_eq]
      ring
    rw [hExpandL, hExpandR]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u' _ ↦ ?_)
    rw [Finset.sum_congr rfl (fun u _ ↦ Finset.sum_comm)]
    rw [Finset.sum_comm]
  rw [hreorder]
  exact bc_joint_indep_prob_le pU K W hpU hK hW n hε

/-! ### Assembly (superposition random-coding, two receivers)

The receiver-1/receiver-2 swap lemmas above are stitched into the headline through the
same skeleton as the MAC achievability assembly (`InformationTheory.Shannon.MAC`
`Achievability.lean`), adapted to the two-tier (cloud / conditional-satellite) codebook and
the two per-receiver error probabilities:

* **C.1** — E0 vanishing: the correct-cloud (`(U, Y₂)`) and correct-triple (`(U, X, Y₁)`)
  atypical masses tend to `0` (AEP / LLN).
* **C.2** — per-codebook `averageErrorProb.toReal` decomposition into the Bonferroni terms.
* **C.3** — two-codebook average bounds (weight-summed swaps).
* **C.4** — pigeonhole to a deterministic codebook pair.
* **C.5** — rate-slack vanishing + degradedness `I((U, X); Y₁) ≥ I(X; Y₁ ∣ U) + I(U; Y₂)`.
-/

/-- Pairwise independence of any BC coordinate selector under the ambient measure. -/
lemma bcAmbient_pairwise_coord {γ : Type*} [MeasurableSpace γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) :
    Pairwise fun i j ↦
      IndepFun (fun ω : ℕ → U × α × β₁ × β₂ ↦ g (ω i)) (fun ω ↦ g (ω j))
        (bcAmbientMeasure pU K W) := by
  intro i j hij
  exact (bcAmbient_iIndepFun_coord pU K W g hg).indepFun hij

/-! #### C.1 — E0 vanishing -/

/-- **`(U, X, Y₁)` channel fold.**  The `(U, X, Y₁)`-block law of a finite set `T` equals the
cloud/satellite/channel average of the `β₁`-projected channel mass.  Receiver-1 analogue of
`bc_chan_fold_UY₂_set`, obtained from the master fold by projecting the pair output to `β₁`. -/
lemma bc_chan_fold_UXY₁_set
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → U) × (Fin n → α) × (Fin n → β₁))) :
    ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real T
      = ∑ u : Fin n → U, ∑ x : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
            * (Measure.pi (fun l ↦ K (u l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real {y | (u, x, fun i ↦ (y i).1) ∈ T} := by
  classical
  have hmeas_master : Measurable (fun ω : ℕ → U × α × β₁ × β₂ ↦
      (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω)) :=
    (measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).prodMk
      ((measurable_jointRV bcXs (fun i ↦ (measurable_pi_apply i).snd.fst) n).prodMk
        (measurable_jointRV bcYPs (fun i ↦ (measurable_pi_apply i).snd.snd) n))
  have hproj_meas : Measurable
      (fun t : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) ↦
        ((t.1, t.2.1, fun i ↦ (t.2.2 i).1) : (Fin n → U) × (Fin n → α) × (Fin n → β₁))) :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_pi_lambda _ fun i ↦
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).fst))
  have hmap : (bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))
      = ((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).map
        (fun t ↦ (t.1, t.2.1, fun i ↦ (t.2.2 i).1)) := by
    rw [Measure.map_map hproj_meas hmeas_master]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    bc_chan_fold_master pU K W n
      ((fun t ↦ ((t.1, t.2.1, fun i ↦ (t.2.2 i).1) :
        (Fin n → U) × (Fin n → α) × (Fin n → β₁))) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- **Receiver-1 correct-triple averaged swap (E0).**  The two-tier random-codebook average of
the correct-triple atypical event equals the joint `(U, X, Y₁)`-block law of the atypical set.
Receiver-1 analogue of `bc_random_codebook_E0₂_swap`. -/
theorem bc_random_codebook_E0₁_swap
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ}
    (m : Fin M₁ × Fin M₂) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU m.2, cX m, fun i ↦ (y i).1)
                      ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      = ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
          { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
            q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε } := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set J := macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε with hJ_def
  -- Step 1: satellite single-row marginalization (per cloud codebook).  The correct row `m`
  -- both drives the channel and indexes the atypical slice.
  have hsat : ∀ cU : BCCloudCodebook M₂ n U,
      (∑ cX : BCSatelliteCodebook M₁ M₂ n α, (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
          * (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ | (cU m.2, cX m, fun i ↦ (y i).1) ∉ J })
        = ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (cU m.2, x, fun i ↦ (y i).1) ∉ J } := by
    intro cU
    haveI : IsProbabilityMeasure (bcSatelliteCodebookMeasure K M₁ M₂ n cU) := by
      unfold bcSatelliteCodebookMeasure; infer_instance
    have hmp : (bcSatelliteCodebookMeasure K M₁ M₂ n cU).map (Function.eval m)
        = Measure.pi (fun l ↦ K (cU m.2 l)) :=
      (measurePreserving_eval
        (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l ↦ K (cU p.2 l))) m).map_eq
    have h1 := sum_weighted_map (bcSatelliteCodebookMeasure K M₁ M₂ n cU) (Function.eval m)
      (measurable_pi_apply m)
      (fun z : Fin n → α ↦ (Measure.pi (fun i ↦ W (z i))).real
        { y : Fin n → β₁ × β₂ | (cU m.2, z, fun i ↦ (y i).1) ∉ J })
    rw [hmp] at h1
    exact h1
  -- Step 2: reduce the cloud codebook to the single transmitted row `m.2`.
  rw [show bcCloudCodebookMeasure pU M₂ n = codebookMeasure pU M₂ n from rfl]
  have e1 : ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ | (cU m.2, cX m, fun i ↦ (y i).1) ∉ J }
      = ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * (fun a ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (a, x, fun i ↦ (y i).1) ∉ J }) (cU m.2) := by
    refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
    rw [hsat cU]
  rw [e1, codebook_marginal_one pU M₂ n m.2
      (fun a ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
        * (Measure.pi (fun i ↦ W (x i))).real
            { y : Fin n → β₁ × β₂ | (a, x, fun i ↦ (y i).1) ∉ J })
      (fun _ ↦ Finset.sum_nonneg
        (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
  -- Step 3: fold the cloud/satellite/channel average back into the joint `(U, X, Y₁)`-block law.
  rw [bc_chan_fold_UXY₁_set pU K W n {q | q ∉ J}]
  simp only [Set.mem_setOf_eq]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  ring

/-- **Receiver-2 E0 vanishing.**  The correct-cloud atypical `(U, Y₂)`-block mass tends to `0`
by the two-variable joint AEP (`jointlyTypicalSet_prob_tendsto_one`). -/
theorem bc_E0₂_vanishing
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
          { q : (Fin n → U) × (Fin n → β₂) |
            q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε })
      Filter.atTop (nhds 0) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hmU : ∀ i, Measurable (bcUs i : (ℕ → U × α × β₁ × β₂) → U) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hmY₂ : ∀ i, Measurable (bcY₂s i : (ℕ → U × α × β₁ × β₂) → β₂) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.snd
  have hgY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hgUY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.2.2)) :=
    measurable_fst.prodMk hgY₂
  -- The AEP: the correct-cloud typical probability tends to 1.
  have h_aep := jointlyTypicalSet_prob_tendsto_one μ bcUs bcY₂s hmU hmY₂
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.1) measurable_fst)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.1) measurable_fst i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.2.2.2) hgY₂)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.2.2) hgY₂ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.2.2)) hgUY₂)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.2.2)) hgUY₂ i)
    hε
  -- Real version: the typical probability (as a real) tends to 1.
  have h_real : Filter.Tendsto
      (fun n : ℕ ↦ μ.real {ω | (jointRV bcUs n ω, jointRV bcY₂s n ω) ∈
          jointlyTypicalSet μ bcUs bcY₂s n ε}) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr (fun _ ↦ rfl) ((ENNReal.tendsto_toReal (by simp)).comp h_aep)
  -- The map-form atypical mass equals `1 − (typical real)`.
  have hg_n : ∀ n, Measurable
      (fun ω : ℕ → U × α × β₁ × β₂ ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω)) :=
    fun n ↦ (measurable_jointRV bcUs hmU n).prodMk (measurable_jointRV bcY₂s hmY₂ n)
  have key : ∀ n, ((μ.map (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
        { q : (Fin n → U) × (Fin n → β₂) | q ∉ jointlyTypicalSet μ bcUs bcY₂s n ε })
      = 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcY₂s n ω) ∈
          jointlyTypicalSet μ bcUs bcY₂s n ε} := by
    intro n
    rw [show { q : (Fin n → U) × (Fin n → β₂) | q ∉ jointlyTypicalSet μ bcUs bcY₂s n ε }
          = (jointlyTypicalSet μ bcUs bcY₂s n ε)ᶜ from rfl,
      map_measureReal_apply (hg_n n) (measurableSet_jointlyTypicalSet μ bcUs bcY₂s n ε).compl,
      Set.preimage_compl,
      probReal_compl_eq_one_sub ((hg_n n) (measurableSet_jointlyTypicalSet μ bcUs bcY₂s n ε))]
    rfl
  have h0 : Filter.Tendsto
      (fun n : ℕ ↦ 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcY₂s n ω) ∈
          jointlyTypicalSet μ bcUs bcY₂s n ε}) Filter.atTop (nhds 0) := by
    simpa using h_real.const_sub (1 : ℝ)
  exact Filter.Tendsto.congr (fun n ↦ (key n).symm) h0

/-- **Receiver-1 E0 vanishing.**  The correct-triple atypical `(U, X, Y₁)`-block mass tends to
`0` by the three-variable joint AEP (`macJointlyTypicalSet_prob_tendsto_one`). -/
theorem bc_E0₁_vanishing
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
          { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
            q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε })
      Filter.atTop (nhds 0) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hmU : ∀ i, Measurable (bcUs i : (ℕ → U × α × β₁ × β₂) → U) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hmX : ∀ i, Measurable (bcXs i : (ℕ → U × α × β₁ × β₂) → α) :=
    fun i ↦ (measurable_pi_apply i).snd.fst
  have hmY₁ : ∀ i, Measurable (bcY₁s i : (ℕ → U × α × β₁ × β₂) → β₁) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.fst
  have hgX : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hgY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hgUX : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) := measurable_fst.prodMk hgX
  have hgUY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) := measurable_fst.prodMk hgY₁
  have hgXY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.2.1, q.2.2.1)) := hgX.prodMk hgY₁
  have hgUXY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk (hgX.prodMk hgY₁)
  -- The AEP: the correct-triple typical probability tends to 1.
  have h_aep := macJointlyTypicalSet_prob_tendsto_one μ bcUs bcXs bcY₁s hmU hmX hmY₁
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.1) measurable_fst)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.1) measurable_fst i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.2.1) hgX)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.1) hgX i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.2.2.1) hgY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.2.1) hgY₁ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.1)) hgUX)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1)) hgUX i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.2.1)) hgUY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.2.1)) hgUY₁ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.2.1, q.2.2.1)) hgXY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.2.1, q.2.2.1)) hgXY₁ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2.1)) hgUXY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2.1)) hgUXY₁ i)
    hε
  have h_real : Filter.Tendsto
      (fun n : ℕ ↦ μ.real {ω | (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω) ∈
          macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε}) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr (fun _ ↦ rfl) ((ENNReal.tendsto_toReal (by simp)).comp h_aep)
  have hg_n : ∀ n, Measurable
      (fun ω : ℕ → U × α × β₁ × β₂ ↦
        (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω)) :=
    fun n ↦ (measurable_jointRV bcUs hmU n).prodMk
      ((measurable_jointRV bcXs hmX n).prodMk (measurable_jointRV bcY₁s hmY₁ n))
  have key : ∀ n, ((μ.map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
        { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
          q ∉ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε })
      = 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω) ∈
          macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε} := by
    intro n
    rw [show { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
              q ∉ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε }
          = (macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε)ᶜ from rfl,
      map_measureReal_apply (hg_n n)
        (measurableSet_macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε).compl,
      Set.preimage_compl,
      probReal_compl_eq_one_sub
        ((hg_n n) (measurableSet_macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε))]
    rfl
  have h0 : Filter.Tendsto
      (fun n : ℕ ↦ 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω) ∈
          macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε}) Filter.atTop (nhds 0) := by
    simpa using h_real.const_sub (1 : ℝ)
  exact Filter.Tendsto.congr (fun n ↦ (key n).symm) h0

/-! #### C.2 — per-codebook `averageErrorProb.toReal` decomposition -/

/-- **Receiver-2 per-codebook averaging bound.**  The `.toReal` of the receiver-2 average error
probability of the deterministic code `bcCodebookToCode cU cX` is at most the uniform average of
the two-event Bonferroni bound (`bc_errorProbAt₂_le_bonferroni`). -/
theorem bc_averageErrorProb₂_toReal_le
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α) :
    ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal
      ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU m.2, fun i ↦ (y i).2) ∉
                  jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
            + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
                (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU w₂', fun i ↦ (y i).2) ∈
                      jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }) := by
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have h_ne_top : ∀ m : Fin M₁ × Fin M₂,
      (bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂ W m ≠ ⊤ :=
    fun m ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂_le_one W m)
  have h_eq : ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂ W m).toReal := by
    unfold BroadcastCode.averageErrorProb₂
    rw [if_neg hMpos.ne', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum (fun m _ ↦ bc_errorProbAt₂_le_bonferroni pU K W hM₁ hM₂ cU cX m)

/-- **Receiver-1 per-codebook averaging bound.**  The `.toReal` of the receiver-1 average error
probability of `bcCodebookToCode cU cX` is at most the uniform average of the three-event
Bonferroni bound (`bc_errorProbAt₁_le_bonferroni3`). -/
theorem bc_averageErrorProb₁_toReal_le
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α) :
    ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU m.2, cX m, fun i ↦ (y i).1) ∉
                  macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
                (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1) ∈
                      macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                      (Finset.univ : Finset (Fin M₁)),
                (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1) ∈
                      macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }) := by
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have h_ne_top : ∀ m : Fin M₁ × Fin M₂,
      (bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁ W m ≠ ⊤ :=
    fun m ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁_le_one W m)
  have h_eq : ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁ W m).toReal := by
    unfold BroadcastCode.averageErrorProb₁
    rw [if_neg hMpos.ne', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum (fun m _ ↦ bc_errorProbAt₁_le_bonferroni3 pU K W hM₁ hM₂ cU cX m)

/-! #### C.3 — two-codebook average bounds -/

/-- **Receiver-2 two-codebook average bound.**  The random-codebook expectation of the
receiver-2 average error is at most the (vanishing) E0 mass plus the wrong-cloud exponent.
@residual(plan:bc-achievability-plan) -/
theorem bc_random_codebook_average₂_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (hε : 0 < ε) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal
      ≤ ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
          { q | q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₂ pU K W) + 3 * ε)) := by
  sorry

/-- **Receiver-1 two-codebook average bound.**  The random-codebook expectation of the
receiver-1 average error is at most the (vanishing) E0 mass plus the wrong-satellite (`E_b`)
and wrong-cloud (`E_c`) exponents.
@residual(plan:bc-achievability-plan) -/
theorem bc_random_codebook_average₁_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (hε : 0 < ε) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      ≤ ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
          { q | q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε))
        + ((M₂ : ℝ) - 1) * (M₁ : ℝ) *
            Real.exp ((n : ℝ) * (-(bcInfoJoint pU K W) + 3 * ε)) := by
  sorry

/-! #### C.4 — random → deterministic (two-tier pigeonhole) -/

/-- **Two-tier pigeonhole.**  If the random-codebook expectation of the summed per-receiver
errors is `≤ B`, some deterministic cloud/satellite codebook pair achieves the summed error
`≤ B`.  Bounding the *sum* lets a single codebook meet both receivers' targets simultaneously.
@residual(plan:bc-achievability-plan) -/
theorem bc_exists_codebook_le_avg
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (B : ℝ)
    (h_avg :
      ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
                 + ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal) ≤ B) :
    ∃ (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α),
      ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
        + ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal ≤ B := by
  sorry

/-! #### C.5 — degradedness + rate slack -/

/-- **Degradedness superadditivity.**  Under physical degradedness `X → Y₁ → Y₂`, the joint
information `I((U, X); Y₁)` dominates the sum of the two per-receiver informations
`I(X; Y₁ ∣ U) + I(U; Y₂)`.  Chain rule `I((U, X); Y₁) = I(U; Y₁) + I(X; Y₁ ∣ U)` plus data
processing `I(U; Y₁) ≥ I(U; Y₂)`.  This makes the receiver-1 joint-decoding rate sum
`R₁ + R₂ < I((U, X); Y₁)` follow automatically from the two corner constraints.
@residual(plan:bc-achievability-plan) -/
theorem bc_degraded_infoJoint_ge
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) :
    bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W := by
  sorry

/-- **Receiver-1 wrong-cloud rate-slack vanishing (`E_c`).**  With the joint AEP gap
`I((U, X); Y₁) − (R₁ + R₂) − 3ε > 0` and non-negative rate `0 ≤ R₁`, the wrong-cloud
prefactor `(⌈exp(nR₂)⌉−1)·⌈exp(nR₁)⌉` times `exp(n(−I((U, X); Y₁) + 3ε))` falls below any
tolerance for large `n`.  The `0 ≤ R₁` hypothesis is essential: for `R₁ < 0` the ceil
`⌈exp(nR₁)⌉` floors at `1` instead of shrinking like `exp(nR₁)`, so the negative slack the
gap allocates to the `R₁` factor is not delivered and the prefactor diverges.  The caller
`bc_achievability` supplies `0 < R₁`, so this precondition is met.
@residual(plan:bc-achievability-plan) -/
theorem bc_Ec_lt_of_rate {Ijoint R₁ R₂ ε ε' : ℝ}
    (hR₁ : 0 ≤ R₁) (hgap : 0 < Ijoint - (R₁ + R₂) - 3 * ε) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N,
      ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
        (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) *
        Real.exp ((n : ℝ) * (-Ijoint + 3 * ε)) < ε' := by
  sorry

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
