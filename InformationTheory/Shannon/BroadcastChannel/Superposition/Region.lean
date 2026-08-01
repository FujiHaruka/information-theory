import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Classes
import InformationTheory.Shannon.BroadcastChannel.MartonUnion

/-!
# Broadcast channel — the superposition inner bound

Superposition coding sends a cloud center `U` to both receivers and a satellite `X` to the
first one only.  This file takes the union of its inner bound over the auxiliary alphabets, so
that it can be compared with the outer bounds as a set.

Two unions are taken, over the same full-support indices and differing only in the constraints
cutting out each member.  Keeping the sum-rate constraint gives the general superposition bound,
achievable over any broadcast channel; dropping it gives a superset, achievable as soon as the
first receiver decodes the cloud at least as well as the second one does — which is exactly what
`IsBCLessNoisy` asks, physical degradedness is not needed — because `I(U; Y₁) ≥ I(U; Y₂)` makes
the omitted inequality follow from the two kept ones.

## Main definitions

* `bcSuperpositionRegionNoSumRate W` — the superposition inner bound without its sum-rate
  constraint, as a union over auxiliary alphabets, restricted to the full-support indices.
* `bcSuperpositionRegionSumRate W` — the same union with the sum-rate constraint kept.

## Main statements

* `bc_lessNoisy_achievability` — the superposition rate pairs of a less noisy channel are
  achievable.
* `bcSuperpositionRegionNoSumRate_subset_capacity` — the two-constraint inner bound sits inside
  the operational capacity region of a less noisy channel.
* `bcSuperpositionRegionSumRate_subset_capacity` — the three-constraint inner bound sits inside
  the operational capacity region, for any broadcast channel.

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

/-! ### The three informations as (conditional) mutual informations -/

theorem bcInfo₂_eq_mutualInfo_toReal {U : Type*}
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcInfo₂ pU K W
      = (mutualInfo (bcJointDistribution pU K W)
          (fun q ↦ q.1) (fun q ↦ q.2.2.2)).toReal := by
  rw [MAC.mutualInfo_toReal_eq_entropy_form (bcJointDistribution pU K W)
    (fun q ↦ q.1) (fun q ↦ q.2.2.2) (by fun_prop) (by fun_prop)]
  rfl

theorem bcInfoJoint_eq_mutualInfo_toReal {U : Type*}
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcInfoJoint pU K W
      = (mutualInfo (bcJointDistribution pU K W)
          (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2.1)).toReal := by
  -- The nested triple carries the same entropy as the flat one appearing in `bcInfoJoint`.
  have hflat : entropy (bcJointDistribution pU K W)
        (fun q : U × α × β₁ × β₂ ↦ ((q.1, q.2.1), q.2.2.1))
      = entropy (bcJointDistribution pU K W)
        (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    entropy_measurableEquiv_comp _ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1))
      (by fun_prop) (MeasurableEquiv.prodAssoc (α := U) (β := α) (γ := β₁)).symm
  rw [MAC.mutualInfo_toReal_eq_entropy_form (bcJointDistribution pU K W)
    (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) (fun q ↦ q.2.2.1) (by fun_prop) (by fun_prop),
    hflat]
  rfl

theorem bcInfo₁_eq_condMutualInfo_toReal {U : Type*}
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcInfo₁ pU K W
      = (condMutualInfo (bcJointDistribution pU K W)
          (fun q ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1)).toReal := by
  -- `I((U, X); Y₁) = I(U; Y₁) + I(X; Y₁ ∣ U)`, read in `ℝ` against the two identified slots.
  have hchain := mutualInfo_chain_rule (bcJointDistribution pU K W)
    (fun q : U × α × β₁ × β₂ ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1)
    (by fun_prop) (by fun_prop) (by fun_prop)
  have hfinU : mutualInfo (bcJointDistribution pU K W)
      (fun q : U × α × β₁ × β₂ ↦ q.1) (fun q ↦ q.2.2.1) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (by fun_prop) (by fun_prop)
  have hfinX : condMutualInfo (bcJointDistribution pU K W)
      (fun q : U × α × β₁ × β₂ ↦ q.2.1) (fun q ↦ q.2.2.1) (fun q ↦ q.1) ≠ ∞ :=
    condMutualInfo_ne_top _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have htoReal := congrArg ENNReal.toReal hchain
  rw [ENNReal.toReal_add hfinU hfinX, ← bcInfoJoint_eq_mutualInfo_toReal pU K W,
    MAC.mutualInfo_toReal_eq_entropy_form (bcJointDistribution pU K W)
      (fun q : U × α × β₁ × β₂ ↦ q.1) (fun q ↦ q.2.2.1) (by fun_prop) (by fun_prop)] at htoReal
  simp only [bcInfoJoint, bcInfo₁] at htoReal ⊢
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

The general superposition bound also constrains the rate sum by `R₁ + R₂ ≤ I((U, X); Y₁)`, and
that constraint is dropped here.  Dropping it is exact over a less noisy channel, where
`I(U; Y₁) ≥ I(U; Y₂)` forces `I(X; Y₁ ∣ U) + I(U; Y₂) ≤ I((U, X); Y₁)`
(`bc_lessNoisy_infoJoint_ge`), so the omitted inequality already follows from the two kept ones.
Outside that class this set is only a superset of the superposition bound.

The full-support indices are the ones the achievability theorem applies to, so this is the form
of the union that is achievable.  As for `bcCapacityRegion` and the outer bounds, no sign
constraint is imposed: a nonpositive rate asks only for a single message.
@audit:ok -/
noncomputable def bcSuperpositionRegionNoSumRate (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k))
    (_ : IsProbabilityMeasure pU) (_ : ∀ x : Marton.bcAuxAlphabet.{u} k, 0 < pU.real {x})
    (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
    (_ : ∀ (x : Marton.bcAuxAlphabet.{u} k) (a : α), 0 < (K x).real {a}),
    {p : ℝ × ℝ | p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W})

omit [DecidableEq α] [DecidableEq β₁] [DecidableEq β₂] in
theorem bcSuperpositionRegionNoSumRate_isClosed (W : BCChannel α β₁ β₂) :
    IsClosed (bcSuperpositionRegionNoSumRate.{u} W) := isClosed_closure

/-- The superposition inner bound of a less noisy broadcast channel is achievable: it is
contained in the operational capacity region.
@audit:ok -/
@[entry_point]
theorem bcSuperpositionRegionNoSumRate_subset_capacity (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hln : IsBCLessNoisy W) :
    bcSuperpositionRegionNoSumRate W ⊆ bcCapacityRegion W := by
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

/-! ### The superposition inner bound with the sum-rate constraint kept -/

section SumRate

omit [DecidableEq α] [DecidableEq β₁] [DecidableEq β₂]

/-- The superposition inner bound of a broadcast channel with the sum-rate constraint kept: the
closure of the union, over the full-support auxiliary laws on `Marton.bcAuxAlphabet`, of the
regions cut out by `R₁ ≤ I(X; Y₁ ∣ U)`, `R₂ ≤ I(U; Y₂)` and `max R₁ 0 + R₂ ≤ I((U, X); Y₁)`.

The sum constraint is written with the first rate clamped at zero because that is the form the
achievability theorem takes: a nonpositive first rate asks for a single satellite codeword, so the
wrong-cloud slack it costs is measured at `max R₁ 0`.  With that shape the whole set is achievable
with no comparison-class hypothesis, whereas the plain sum `R₁ + R₂` would need one on the branch
where the first rate is negative.

`bcSuperpositionRegionNoSumRate` drops the sum constraint, which is exact over a less noisy
channel but not in general; this set is the general superposition bound and is contained in
it. -/
noncomputable def bcSuperpositionRegionSumRate (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k))
    (_ : IsProbabilityMeasure pU) (_ : ∀ x : Marton.bcAuxAlphabet.{u} k, 0 < pU.real {x})
    (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
    (_ : ∀ (x : Marton.bcAuxAlphabet.{u} k) (a : α), 0 < (K x).real {a}),
    {p : ℝ × ℝ | p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W
      ∧ max p.1 0 + p.2 ≤ bcInfoJoint pU K W})

omit [Nonempty α] [MeasurableSingletonClass α] [Nonempty β₁] [MeasurableSingletonClass β₁]
  [Nonempty β₂] [MeasurableSingletonClass β₂] in
theorem bcSuperpositionRegionSumRate_isClosed (W : BCChannel α β₁ β₂) :
    IsClosed (bcSuperpositionRegionSumRate.{u} W) := isClosed_closure

/-- The three-constraint superposition inner bound of a broadcast channel is achievable: it is
contained in the operational capacity region.  No comparison between the two receivers is needed,
because the region carries the sum constraint the achievability theorem asks for. -/
@[entry_point]
theorem bcSuperpositionRegionSumRate_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    bcSuperpositionRegionSumRate.{u} W ⊆ bcCapacityRegion W := by
  classical
  refine closure_minimal ?_ (bc_capacityRegion_isClosed W)
  refine Set.iUnion_subset fun k ↦ Set.iUnion_subset fun pU ↦ Set.iUnion_subset fun hpU ↦
    Set.iUnion_subset fun hpUpos ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦
      Set.iUnion_subset fun hKpos ↦ ?_
  intro p hp
  refine bc_mem_closure_of_strictly_below W p fun ε hε ↦ ?_
  intro ε' hε'
  refine bc_achievability_of_rate_lt pU K W hpUpos hKpos hW
    (by linarith [hp.1]) (by linarith [hp.2]) ?_ hε'
  have hmax : max (p.1 - ε) 0 ≤ max p.1 0 := max_le_max (by linarith) le_rfl
  linarith [hp.2.2]

end SumRate

end InformationTheory.Shannon.BroadcastChannel
