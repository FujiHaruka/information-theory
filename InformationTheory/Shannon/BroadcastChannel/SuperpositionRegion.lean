import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Classes
import InformationTheory.Shannon.BroadcastChannel.MartonUnion

/-!
# Broadcast channel — the superposition inner bound over a less noisy channel

Superposition coding sends a cloud centre `U` to both receivers and a satellite `X` to the
first one only.  Its inner bound is achievable as soon as the first receiver decodes the cloud
at least as well as the second one does, which is exactly what `IsBCLessNoisy` asks; physical
degradedness is not needed.  This file takes the union of that bound over the auxiliary
alphabets, so that it can be compared with the outer bounds as a set.

## Main definitions

* `bcSuperpositionRegionFullSupport W` — the superposition inner bound as a union over
  auxiliary alphabets, restricted to the full-support indices.

## Main statements

* `bc_lessNoisy_achievability` — the superposition rate pairs of a less noisy channel are
  achievable.
* `bcSuperpositionRegionFullSupport_subset_capacity` — the superposition inner bound sits inside
  the operational capacity region.

## Implementation notes

The auxiliary alphabets range over `Marton.bcAuxAlphabet`, one cardinality at a time in the
universe of the input alphabet.  That universe is forced: `IsBCLessNoisy` quantifies its
auxiliary variable over the universe of the input alphabet, so a member of the union has to live
there for the class hypothesis to apply to it.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Nonnegativity of the satellite information -/

theorem bcInfo₁_nonneg {U : Type*}
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    0 ≤ bcInfo₁ pU K W := by
  set μ := bcJointDistribution pU K W with hμ
  have hU : Measurable (Prod.fst : U × α × β₁ × β₂ → U) := measurable_fst
  have hX : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  -- `H(U, Y₁) = H(U) + H(Y₁ ∣ U)` and `H((U, X), Y₁) = H(U, X) + H(Y₁ ∣ U, X)`.
  have h2 := entropy_pair_eq_entropy_add_condEntropy μ (Prod.fst : U × α × β₁ × β₂ → U)
    (fun q ↦ q.2.2.1) hU hY₁
  have h3 := entropy_pair_eq_entropy_add_condEntropy μ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1))
    (fun q ↦ q.2.2.1) (hU.prodMk hX) hY₁
  -- The nested triple carries the same entropy as the flat one appearing in `bcInfo₁`.
  have h4 : entropy μ (fun q : U × α × β₁ × β₂ ↦ ((q.1, q.2.1), q.2.2.1))
      = entropy μ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    entropy_measurableEquiv_comp μ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1))
      (hU.prodMk (hX.prodMk hY₁)) (MeasurableEquiv.prodAssoc (α := U) (β := α) (γ := β₁)).symm
  have h5 := condEntropy_le_condEntropy_of_pair μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.1)
    (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.1) hY₁ hU hX
  simp only [bcInfo₁, ← hμ]
  linarith

/-! ### Achievability over a less noisy channel -/

/-- Achievability half of the superposition inner bound over a less noisy broadcast channel.
Degradedness enters `bc_achievability` only through the rate-sum inequality
`I(X; Y₁ ∣ U) + I(U; Y₂) ≤ I((U, X); Y₁)`, which `bc_lessNoisy_infoJoint_ge` supplies from the
weaker class hypothesis, so the same two-tier random-coding argument applies verbatim.
@audit:ok -/
@[entry_point]
theorem bc_lessNoisy_achievability {U : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hln : IsBCLessNoisy W)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : BroadcastCode M₁ M₂ n α β₁ β₂),
        (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε' :=
  bc_achievability_of_infoJoint_ge pU K W hpU hK hW
    (bc_lessNoisy_infoJoint_ge pU K W hln) hR₁ hR₂ hR₁lt hR₂lt hε'

/-! ### The superposition inner bound as a region -/

/-- The superposition inner bound of a broadcast channel: the closure of the union, over the
full-support auxiliary laws on `Marton.bcAuxAlphabet`, of the rectangles cut out by
`R₁ ≤ I(X; Y₁ ∣ U)` and `R₂ ≤ I(U; Y₂)`.

The full-support indices are the ones the achievability theorem applies to, so this is the form
of the union that is achievable.  As for `bcCapacityRegion` and the outer bounds, no sign
constraint is imposed: a nonpositive rate asks only for a single message.
@audit:ok -/
noncomputable def bcSuperpositionRegionFullSupport (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k))
    (_ : IsProbabilityMeasure pU) (_ : ∀ x : Marton.bcAuxAlphabet.{u} k, 0 < pU.real {x})
    (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
    (_ : ∀ (x : Marton.bcAuxAlphabet.{u} k) (a : α), 0 < (K x).real {a}),
    {p : ℝ × ℝ | p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W})

/-- The superposition inner bound of a less noisy broadcast channel is achievable: it is
contained in the operational capacity region.
@audit:ok -/
@[entry_point]
theorem bcSuperpositionRegionFullSupport_subset_capacity (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hln : IsBCLessNoisy W) :
    bcSuperpositionRegionFullSupport W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ (bc_capacityRegion_isClosed W)
  refine Set.iUnion_subset fun k ↦ Set.iUnion_subset fun pU ↦ Set.iUnion_subset fun hpU ↦
    Set.iUnion_subset fun hpUpos ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦
      Set.iUnion_subset fun hKpos ↦ ?_
  intro p hp
  have hsum := bc_lessNoisy_infoJoint_ge pU K W hln
  have hnn := bcInfo₁_nonneg pU K W
  refine bc_mem_closure_of_strictly_below W p fun ε hε ↦ ?_
  intro ε' hε'
  refine bc_achievability_of_rate_lt pU K W hpUpos hKpos hW
    (by linarith [hp.1]) (by linarith [hp.2]) ?_ hε'
  -- A nonpositive first rate asks for a single satellite codeword, so the wrong-cloud slack is
  -- measured at `max (p.1 - ε) 0`, which the satellite information dominates.
  have hmax : max (p.1 - ε) 0 ≤ bcInfo₁ pU K W := max_le (by linarith [hp.1]) hnn
  linarith [hp.2]

end InformationTheory.Shannon.BroadcastChannel
