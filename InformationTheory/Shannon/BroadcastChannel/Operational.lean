import InformationTheory.Shannon.BroadcastChannel.Marton.Achievability

/-!
# Broadcast channel — operational capacity region

The operational capacity region of a general two-receiver broadcast channel, following the
multiple-access template of `InformationTheory.Shannon.MAC.macCapacityRegion`: an operational
achievability predicate on rate pairs, whose closure is taken as a subset of the plane, so that
inner and outer bounds can be compared as sets.

Marton's inner bound, stated pointwise by `InMartonRegion`, is lifted to a subset of the plane
here and shown to sit inside the operational region.

## Main definitions

* `BCAchievable W R₁ R₂` — the operational achievability predicate for the rate pair `(R₁, R₂)`:
  for every target error `ε' > 0`, at every large enough block length there is a code with at
  least `⌈exp (n R₁)⌉` / `⌈exp (n R₂)⌉` messages per receiver whose two average error
  probabilities are both `< ε'`.  This is the conclusion of `marton_achievability`, abstracted
  over `ε'`.
* `bcCapacityRegion W` — the operational capacity region, the topological closure of the
  achievable set.  (The achievable set is described by strict inequalities and is not closed, so
  the region is defined as its closure.)
* `martonRegion pV K W` — Marton's inner bound as a subset of the plane, cut out by
  `InMartonRegion` for the three informations of the auxiliary law `pV`, input kernel `K` and
  channel `W`.

## Main statements

* `marton_region_subset_capacity` — Marton's inner bound is contained in the operational capacity
  region.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open scoped ENNReal NNReal BigOperators Topology

section Operational

variable {α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- The operational achievability predicate for the broadcast rate pair `(R₁, R₂)`: for every
target error `ε' > 0` there is a block length `N` such that for all `n ≥ N` there is a length-`n`
broadcast code with at least `⌈exp (n R₁)⌉` / `⌈exp (n R₂)⌉` messages per receiver whose two
average error probabilities are both below `ε'`.  This is the `∀ ε'`-abstraction of the
conclusion of `marton_achievability`.

Both message counts are at least one, since `1 ≤ ⌈exp (n R)⌉₊` at every real rate, so the
degenerate `M₁ * M₂ = 0` branch of `averageErrorProb₁` — which reports an error probability of
`0` — is out of reach: an empty code cannot witness achievability.
@audit:ok -/
def BCAchievable (W : BCChannel α β₁ β₂) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (M₁ M₂ : ℕ) (_ : ⌈Real.exp ((n : ℝ) * R₁)⌉₊ ≤ M₁) (_ : ⌈Real.exp ((n : ℝ) * R₂)⌉₊ ≤ M₂)
      (c : BroadcastCode M₁ M₂ n α β₁ β₂),
      (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'

/-- The operational broadcast capacity region: the topological closure of the achievable set.
The achievable set is cut out by strict inequalities and is not closed (boundary faces enter only
in the closure), so the capacity region is defined as its closure.

The region is a down-set of the whole plane rather than of the first quadrant, since a
nonpositive rate asks only for a single message and is achievable.  An outer bound should
therefore be stated without a sign constraint, or compared after intersecting with the first
quadrant.
@audit:ok -/
def bcCapacityRegion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure {p | BCAchievable W p.1 p.2}

theorem bc_achievable_mono {W : BCChannel α β₁ β₂} {R₁ R₂ R₁' R₂' : ℝ}
    (h : BCAchievable W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) :
    BCAchievable W R₁' R₂' := by
  intro ε' hε'
  obtain ⟨N, hN⟩ := h ε' hε'
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
  have hmul₁ : (n : ℝ) * R₁' ≤ (n : ℝ) * R₁ :=
    mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg n)
  have hmul₂ : (n : ℝ) * R₂' ≤ (n : ℝ) * R₂ :=
    mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n)
  exact ⟨M₁, M₂,
    le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr hmul₁)) hM₁,
    le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr hmul₂)) hM₂, c, hc⟩

theorem bc_mem_closure_of_strictly_below (W : BCChannel α β₁ β₂) (p : ℝ × ℝ)
    (h : ∀ ε : ℝ, 0 < ε → BCAchievable W (p.1 - ε) (p.2 - ε)) :
    p ∈ closure {q : ℝ × ℝ | BCAchievable W q.1 q.2} := by
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun k ↦ (p.1 - 1 / ((k : ℝ) + 1), p.2 - 1 / ((k : ℝ) + 1)), ?_, ?_⟩
  · intro k
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact h _ hpos
  · have ht : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k : ℕ ↦ p.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 p.1) := by
      simpa using tendsto_const_nhds.sub ht
    have h2 : Tendsto (fun k : ℕ ↦ p.2 - 1 / ((k : ℝ) + 1)) atTop (𝓝 p.2) := by
      simpa using tendsto_const_nhds.sub ht
    exact h1.prodMk_nhds h2

theorem bc_capacityRegion_isClosed (W : BCChannel α β₁ β₂) :
    IsClosed (bcCapacityRegion W) := isClosed_closure

end Operational

namespace Marton

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- Marton's inner bound as a subset of the plane: the rate pairs satisfying the three
inequalities of `InMartonRegion` for the informations `martonInfo₁`, `martonInfo₂` and
`martonInfoV₁V₂` of the auxiliary law `pV`, input kernel `K` and channel `W`.
This is the region of one fixed choice of `pV`, `K` and `W`; the union over auxiliary alphabets
is not taken.

Like `bcCapacityRegion` and the outer bounds, the region carries no sign constraint: a
nonpositive rate asks only for a single message and is achievable, so cutting the bound down to
the first quadrant would place it strictly inside the capacity region for no gain and would
break every comparison against a region of the whole plane.
@audit:ok -/
def martonRegion (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    Set (ℝ × ℝ) :=
  {p | InMartonRegion p.1 p.2 (martonInfo₁ pV K W) (martonInfo₂ pV K W) (martonInfoV₁V₂ pV K W)}

theorem bc_strict_interior_achievable
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁ R₂ : ℝ}
    (hR₁lt : R₁ < martonInfo₁ pV K W) (hR₂lt : R₂ < martonInfo₂ pV K W)
    (hRsum : R₁ + R₂ < martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W) :
    BCAchievable W R₁ R₂ := by
  intro ε' hε'
  exact marton_achievability pV K W hpV hK hW hR₁lt hR₂lt hRsum hε'

/-- Marton's inner bound sits inside the operational capacity region.  A rate pair of the region
satisfies the three region inequalities non-strictly, so shrinking both rates by any `ε > 0`
makes all three strict and `marton_achievability` applies; letting `ε` tend to `0` recovers the
pair in the closure.

The hypotheses `hpV`, `hK` and `hW` are the full-support regularity preconditions of
`marton_achievability` and carry no part of the coding argument.  The shrunk pair may leave the
first quadrant, which costs nothing: a nonpositive rate asks only for a single message.
@audit:ok -/
@[entry_point]
theorem marton_region_subset_capacity
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegion pV K W ⊆ bcCapacityRegion W := by
  intro p hM
  refine bc_mem_closure_of_strictly_below W p fun ε hε ↦ ?_
  exact bc_strict_interior_achievable pV K W hpV hK hW
    (by linarith [hM.bound₁]) (by linarith [hM.bound₂]) (by linarith [hM.boundSum])

end Marton

end InformationTheory.Shannon.BroadcastChannel
