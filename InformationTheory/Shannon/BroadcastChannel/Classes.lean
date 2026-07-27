import InformationTheory.Shannon.BroadcastChannel.Achievability.Assembly
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient

/-!
# Broadcast channel — comparison classes of the two receivers

Three classes of two-receiver broadcast channel on which the first receiver is at least as good
as the second.  Two of them form a chain refining physical degradedness: a degraded channel is
less noisy, and a less noisy channel is more capable.  Semi-determinism is a separate condition
on the first output alone and does not enter that chain.

## Main definitions

* `IsBCLessNoisy W` — every auxiliary variable feeding the input carries at least as much
  information about the first output as about the second.
* `IsBCMoreCapable W` — every input law reaches the first receiver at a rate at least that of
  the second.
* `IsBCSemiDeterministic W` — the first output is a function of the input letter.

## Main statements

* `IsBCDegraded.isBCLessNoisy` — a physically degraded channel is less noisy.
* `IsBCLessNoisy.isBCMoreCapable` — a less noisy channel is more capable.
* `bc_lessNoisy_infoJoint_ge` — over a less noisy channel the joint information `I((U, X); Y₁)`
  dominates the sum `I(X; Y₁ ∣ U) + I(U; Y₂)` of the two per-receiver informations.
* `IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero` — a semi-deterministic channel with
  at least two first-output letters gives some output pair probability zero.

## Implementation notes

The auxiliary variable of `IsBCLessNoisy` ranges over the universe of the input alphabet, which
is what lets the input itself be taken as the auxiliary; that instantiation is the whole step
from less noisy to more capable.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.MAC
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### The three classes -/

/-- The first receiver is less noisy than the second: for every auxiliary variable `U` feeding
the input letter through a Markov kernel, the first output carries at least as much information
about `U` as the second does.  Unlike `IsBCDegraded`, this is a condition on the two output
marginals of `W` only, not on their joint law.

Quantifying the auxiliary alphabet over the input alphabet's universe is no restriction: every
finite type is measurably isomorphic to one of this universe, and mutual information is invariant
under such a relabeling.
@audit:ok -/
def IsBCLessNoisy (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U]
      [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU]
      (K : Kernel U α) [IsMarkovKernel K],
    mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2)
      ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)

/-- The first receiver is more capable than the second: under every input law the first output
carries at least as much information about the input as the second does.  Stated on the two
marginal channels `Kernel.fst W` and `Kernel.snd W` so that the channel-side vocabulary of
`mutualInfoOfChannel` applies directly.
@audit:ok -/
def IsBCMoreCapable (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (p : Measure α) [IsProbabilityMeasure p],
    mutualInfoOfChannel p (Kernel.snd W) ≤ mutualInfoOfChannel p (Kernel.fst W)

/-- The channel is semi-deterministic: the first output is a function of the input letter, while
the second output stays arbitrary.  Stated as an equality of the first marginal channel with a
Dirac kernel, matching the `∃ kernel, ∀ letter, equality` shape of `IsBCDegraded`.
@audit:ok -/
def IsBCSemiDeterministic (W : BCChannel α β₁ β₂) : Prop :=
  ∃ f : α → β₁, ∀ a : α, Kernel.fst W a = Measure.dirac (f a)

/-! ### Less noisy: the superposition rate sum -/

/-- Superadditivity over a less noisy channel: the joint information `I((U, X); Y₁)` dominates
the sum of the two per-receiver informations `I(X; Y₁ ∣ U) + I(U; Y₂)`.  Chain rule
`I((U, X); Y₁) = I(U; Y₁) + I(X; Y₁ ∣ U)` plus the defining inequality `I(U; Y₁) ≥ I(U; Y₂)`.
This generalizes `bc_degraded_infoJoint_ge`, whose degradedness hypothesis is used only through
that inequality.
@audit:ok -/
@[entry_point]
theorem bc_lessNoisy_infoJoint_ge {U : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) :
    bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W := by
  classical
  set μ := bcJointDistribution pU K W with hμ
  have hU : Measurable (Prod.fst : U × α × β₁ × β₂ → U) := measurable_fst
  have hY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  have hY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  have hmi := hln U pU K
  have hne1 : mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1) ≠ ⊤ :=
    mutualInfo_ne_top μ Prod.fst (fun q ↦ q.2.2.1) hU hY₁
  have htoReal :
      (mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.2)).toReal
        ≤ (mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1)).toReal :=
    ENNReal.toReal_mono hne1 hmi
  have hb2 := mutualInfo_toReal_eq_entropy_form μ (Prod.fst : U × α × β₁ × β₂ → U)
    (fun q ↦ q.2.2.2) hU hY₂
  have hb1 := mutualInfo_toReal_eq_entropy_form μ (Prod.fst : U × α × β₁ × β₂ → U)
    (fun q ↦ q.2.2.1) hU hY₁
  rw [hb2, hb1] at htoReal
  simp only [bcInfo₁, bcInfo₂, bcInfoJoint, ← hμ]
  linarith [htoReal]

/-! ### Degraded implies less noisy -/

/-- A physically degraded channel is less noisy.  Degradedness gives the Markov chain
`(U, X) → Y₁ → Y₂` on the per-coordinate joint law for every auxiliary; post-processing the
source to `U` and applying data processing along the reversed chain yields the defining
inequality.  The reverse implication is not available: less noisy constrains only the two
output marginals, degradedness their joint law.
@audit:ok -/
@[entry_point]
theorem IsBCDegraded.isBCLessNoisy {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) : IsBCLessNoisy W := by
  intro U _ _ _ _ _ pU _ K _
  set μ := bcJointDistribution pU K W with hμ
  have hU : Measurable (Prod.fst : U × α × β₁ × β₂ → U) := measurable_fst
  have hY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  have hY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  have hUX : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hbase := bcMarkovChain_UX_Y₁_Y₂ pU K W hdeg
  have hUY :
      IsMarkovChain μ (Prod.fst : U × α × β₁ × β₂ → U)
        (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    isMarkovChain_map_left μ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1))
      (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2) hUX hY₁ hY₂ (f := Prod.fst) measurable_fst hbase
  have hswap :
      IsMarkovChain μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.2)
        (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) (Prod.fst : U × α × β₁ × β₂ → U) :=
    isMarkovChain_swap μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1)
      (fun q ↦ q.2.2.2) hU hY₁ hY₂ hUY
  have hdpi :
      mutualInfo μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) (Prod.fst : U × α × β₁ × β₂ → U)
        ≤ mutualInfo μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) (Prod.fst : U × α × β₁ × β₂ → U) :=
    mutualInfo_le_of_markov μ (fun q ↦ q.2.2.2) (fun q ↦ q.2.2.1)
      (Prod.fst : U × α × β₁ × β₂ → U) hY₂ hY₁ hU hswap
  rw [mutualInfo_comm μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.2) hU hY₂,
      mutualInfo_comm μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1) hU hY₁]
  exact hdpi

/-! ### Less noisy implies more capable -/

theorem bcJointDistribution_id_eq (p : Measure α) [IsProbabilityMeasure p]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcJointDistribution p Kernel.id W
      = (p ⊗ₘ W).map (fun z : α × β₁ × β₂ ↦ (z.1, z.1, z.2)) := by
  have hd : Measurable (fun x : α ↦ (x, x)) := measurable_id.prodMk measurable_id
  have hcomap : (W.comap (Prod.snd : α × α → α) measurable_snd).comap (fun x : α ↦ (x, x)) hd
      = W := rfl
  have hstep :
      (p.map (fun x : α ↦ (x, x))) ⊗ₘ (W.comap (Prod.snd : α × α → α) measurable_snd)
        = (p ⊗ₘ W).map (fun z : α × β₁ × β₂ ↦ ((z.1, z.1), z.2)) := by
    rw [← compProd_comap_map_prodMap p (W.comap (Prod.snd : α × α → α) measurable_snd) hd,
      hcomap]
  unfold bcJointDistribution
  rw [Measure.compProd_id, hstep,
    Measure.map_map (MeasurableEquiv.prodAssoc (α := α) (β := α) (γ := β₁ × β₂)).measurable
      ((measurable_fst.prodMk measurable_fst).prodMk measurable_snd)]
  rfl

theorem mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution {γ : Type*}
    [MeasurableSpace γ] (p : Measure α) [IsProbabilityMeasure p]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {g : β₁ × β₂ → γ} (hg : Measurable g) :
    mutualInfoOfChannel p (W.map g)
      = mutualInfo (bcJointDistribution p Kernel.id W) Prod.fst (fun q ↦ g q.2.2) := by
  haveI : IsMarkovKernel (W.map g) := Kernel.IsMarkovKernel.map W hg
  have hD : Measurable (fun z : α × β₁ × β₂ ↦ (z.1, z.1, z.2)) :=
    measurable_fst.prodMk measurable_id
  have hpairMap : Measurable (fun q : α × α × β₁ × β₂ ↦ (q.1, g q.2.2)) :=
    measurable_fst.prodMk (hg.comp (measurable_snd.comp measurable_snd))
  have hpair : (bcJointDistribution p Kernel.id W).map
      (fun q : α × α × β₁ × β₂ ↦ (q.1, g q.2.2)) = p ⊗ₘ (W.map g) := by
    rw [bcJointDistribution_id_eq p W, Measure.map_map hpairMap hD, Measure.compProd_map hg]
    rfl
  have hfst : (bcJointDistribution p Kernel.id W).map (Prod.fst : α × α × β₁ × β₂ → α)
      = (p ⊗ₘ (W.map g)).map Prod.fst := by
    rw [← hpair, Measure.map_map measurable_fst hpairMap]
    rfl
  have hsnd : (bcJointDistribution p Kernel.id W).map (fun q : α × α × β₁ × β₂ ↦ g q.2.2)
      = (p ⊗ₘ (W.map g)).map Prod.snd := by
    rw [← hpair, Measure.map_map measurable_snd hpairMap]
    rfl
  rw [mutualInfoOfChannel_eq_mutualInfo_prod p (W.map g)]
  simp only [jointDistribution_def, mutualInfo]
  rw [hpair, hfst, hsnd]
  congr 1
  exact Measure.map_id

/-- A less noisy channel is more capable: take the input itself as the auxiliary variable, so
that the defining inequality of `IsBCLessNoisy` at the identity kernel is the comparison of the
two marginal channels.  The reverse implication is not available: more capable compares the
input alone, less noisy every auxiliary.
@audit:ok -/
@[entry_point]
theorem IsBCLessNoisy.isBCMoreCapable {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) : IsBCMoreCapable W := by
  intro p _
  rw [Kernel.fst_eq, Kernel.snd_eq,
    mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution p W
      (measurable_snd : Measurable (Prod.snd : β₁ × β₂ → β₂)),
    mutualInfoOfChannel_map_eq_mutualInfo_bcJointDistribution p W
      (measurable_fst : Measurable (Prod.fst : β₁ × β₂ → β₁))]
  exact hln α p Kernel.id

/-! ### Semi-determinism and full support -/

/-- A semi-deterministic channel with at least two letters at the first output puts zero mass on
some output pair: the first output is concentrated on `f a`, so every pair whose first component
differs from `f a` is null.  The full-support hypothesis of `marton_achievability` therefore
fails on this class, so `marton_region_subset_capacity` is unavailable on it.
@audit:ok -/
@[entry_point]
theorem IsBCSemiDeterministic.exists_prob_real_singleton_eq_zero {W : BCChannel α β₁ β₂}
    (hsd : IsBCSemiDeterministic W) (hcard : 1 < Fintype.card β₁) (a : α) :
    ∃ b : β₁ × β₂, (W a).real {b} = 0 := by
  obtain ⟨f, hf⟩ := hsd
  obtain ⟨y₁, hy₁⟩ := Fintype.exists_ne_of_one_lt_card hcard (f a)
  refine ⟨(y₁, Classical.arbitrary β₂), ?_⟩
  have hmarg : (W a) (Prod.fst ⁻¹' {y₁}) = 0 := by
    have hfa : (W a).map Prod.fst = Measure.dirac (f a) := by rw [← Kernel.fst_apply]; exact hf a
    have h1 : ((W a).map Prod.fst) {y₁} = Measure.dirac (f a) {y₁} := by rw [hfa]
    rw [Measure.map_apply measurable_fst (measurableSet_singleton y₁),
      Measure.dirac_apply' _ (measurableSet_singleton y₁)] at h1
    simpa [hy₁] using h1
  have hsubset : ({(y₁, Classical.arbitrary β₂)} : Set (β₁ × β₂)) ⊆ Prod.fst ⁻¹' {y₁} :=
    Set.singleton_subset_iff.mpr rfl
  have hsub : (W a) {((y₁ : β₁), Classical.arbitrary β₂)} = 0 := measure_mono_null hsubset hmarg
  simp [Measure.real, hsub]

end InformationTheory.Shannon.BroadcastChannel
