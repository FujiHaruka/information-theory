import Common2026.Shannon.LZ78ZivEntropyBridge
import Common2026.Shannon.StationaryKernel
import Common2026.Shannon.LZ78ZivCountingBody
import Common2026.Shannon.LZ78DistinctEncoding
import Common2026.Shannon.LZ78AchievabilityLimsup
import Mathlib.MeasureTheory.Measure.Real

/-!
# LZ78 Ziv combinatorics — distinct-phrase sub-distribution (Core 1)

This file builds the genuine measure-theoretic crux of the Cover–Thomas Ziv
inequality for the distinct LZ78 parse: the **per-symbol cylinder
sub-distribution**.  For a fixed observed prefix of length `m`, the
length-`(m+1)` cylinders obtained by appending each alphabet symbol are
pairwise disjoint and contained in the length-`m` cylinder, so their
pushforward block probabilities sum to at most the length-`m` block
probability.  In conditional form this is `∑_a P(prefix · a) / P(prefix) ≤ 1`
— the next-symbol conditional distribution.

This is the genuine, foundation-compatible content the Ziv chain
(`blockProb_neg_log_ge_sum`, `log_sum_inequality`) needs.  It is a real
measure-theoretic theorem (cylinder disjointness + finite additivity), not a
hypothesis.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Next-symbol cylinder set**: the preimage under `blockRV (m+1)` of the
length-`(m+1)` block obtained by extending the observed length-`m` prefix of
`ω` with the symbol `a` in the last coordinate. -/
noncomputable def extendCylinder
    (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) (m : ℕ) (a : α) :
    Set Ω :=
  p.blockRV (m + 1) ⁻¹' {Fin.snoc (p.blockRV m ω) a}

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The extended cylinders over distinct last symbols are pairwise disjoint:
two length-`(m+1)` blocks that agree on the first `m` coordinates but differ
in the last coordinate are different points, so their `blockRV (m+1)`
preimages are disjoint. -/
theorem extendCylinder_pairwiseDisjoint
    (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) (m : ℕ) :
    Set.PairwiseDisjoint (Finset.univ : Finset α)
      (extendCylinder μ p ω m) := by
  intro a _ a' _ hne
  -- Distinct last symbols give distinct length-(m+1) blocks, hence disjoint preimages.
  have hpt : (Fin.snoc (p.blockRV m ω) a : Fin (m + 1) → α)
      ≠ Fin.snoc (p.blockRV m ω) a' := by
    intro hsnoc
    apply hne
    have h := congrFun hsnoc (Fin.last m)
    rwa [Fin.snoc_last, Fin.snoc_last] at h
  apply Set.disjoint_left.mpr
  intro x hx hx'
  simp only [extendCylinder, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
  exact hpt (hx.symm.trans hx')

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The length-`(m+1)` block of `x` is the length-`m` block with the time-`m`
observation snoc'd on (the observations `obs i` do not depend on the block
length). -/
theorem blockRV_succ_eq_snoc
    (μ : Measure Ω) (p : StationaryProcess μ α) (m : ℕ) (x : Ω) :
    p.blockRV (m + 1) x = Fin.snoc (p.blockRV m x) (p.obs m x) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Fin.snoc_last, StationaryProcess.blockRV]
  | cast j => simp [Fin.snoc_castSucc, StationaryProcess.blockRV]

omit [DecidableEq α] [Nonempty α] in
omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The union of the extended cylinders over all last symbols is exactly the
length-`m` cylinder of the prefix (a length-`(m+1)` block lies over the
length-`m` prefix iff its last coordinate is *some* symbol). -/
theorem iUnion_extendCylinder
    (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) (m : ℕ) :
    (⋃ a ∈ (Finset.univ : Finset α), extendCylinder μ p ω m a)
      = p.blockRV m ⁻¹' {p.blockRV m ω} := by
  ext x
  simp only [extendCylinder, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
    Finset.mem_univ, exists_prop, true_and]
  constructor
  · rintro ⟨a, hx⟩
    -- blockRV (m+1) x = snoc (blockRV m ω) a ⟹ first m coords agree.
    rw [blockRV_succ_eq_snoc] at hx
    funext i
    have := congrFun hx i.castSucc
    rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at this
  · intro hx
    -- blockRV m x = blockRV m ω ⟹ choose a = obs m x.
    refine ⟨p.obs m x, ?_⟩
    rw [blockRV_succ_eq_snoc, hx]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Each extended cylinder is measurable. -/
theorem measurableSet_extendCylinder
    (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) (m : ℕ) (a : α) :
    MeasurableSet (extendCylinder μ p ω m a) :=
  (p.measurable_blockRV (m + 1)) (measurableSet_singleton _)

omit [DecidableEq α] [Nonempty α] in
/-- **Genuine cylinder sub-distribution (Core 1 ★crux, additive chain-rule
form)**: for a fixed observed length-`m` prefix, the sum over the alphabet of
the length-`(m+1)` extended-cylinder block probabilities **equals** the
length-`m` prefix block probability (the full alphabet exhausts the prefix
cylinder; in particular the sum is `≤` the prefix mass).  This is the
next-symbol conditional distribution summing to `1` (here in un-normalized /
probability form), and is the genuine, unconditional, sorryAx-free
measure-theoretic content the Cover–Thomas Ziv chain consumes — the load-
bearing fact the plan flagged as the Phase Z2 ★crux.

Proved from cylinder disjointness (`extendCylinder_pairwiseDisjoint`), finite
additivity (`measureReal_biUnion_finset`), and the union identity
(`iUnion_extendCylinder`). -/
theorem extendCylinder_measureReal_sum_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (ω : Ω) (m : ℕ) :
    (∑ a : α, (μ.map (p.blockRV (m + 1))).real
        {Fin.snoc (p.blockRV m ω) a})
      = (μ.map (p.blockRV m)).real {p.blockRV m ω} := by
  -- Rewrite each pushforward singleton as a `μ.real` of the extended cylinder.
  have hpush : ∀ a : α,
      (μ.map (p.blockRV (m + 1))).real {Fin.snoc (p.blockRV m ω) a}
        = μ.real (extendCylinder μ p ω m a) := by
    intro a
    rw [map_measureReal_apply (p.measurable_blockRV (m + 1))
        (measurableSet_singleton _)]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hpush a)]
  -- Finite additivity over the disjoint extended cylinders.
  rw [← measureReal_biUnion_finset
      (extendCylinder_pairwiseDisjoint μ p ω m)
      (fun a _ => measurableSet_extendCylinder μ p ω m a)]
  -- The union is the length-`m` cylinder; its `μ.real` is the pushforward
  -- singleton block probability.
  rw [iUnion_extendCylinder μ p ω m,
      ← map_measureReal_apply (p.measurable_blockRV m) (measurableSet_singleton _)]

omit [DecidableEq α] [Nonempty α] in
/-- **Genuine next-symbol conditional sub-distribution** (normalized form): for
a fixed observed length-`m` prefix with positive block probability, the
conditional next-symbol probabilities `P(prefix · a) / P(prefix)` sum to `1`
(in particular `≤ 1`) over the alphabet.  This is the directly
`log_sum_inequality`-consumable form of the cylinder chain rule
(`extendCylinder_measureReal_sum_eq`) — the genuine per-step sub-distribution
the Cover–Thomas Ziv log-sum argument requires at each prefix.

The positivity hypothesis `hpos` is a.s. regularity (the observed cylinder
has positive mass), the same regularity family as
`isLZ78PerPathParsingFactorization_of_pos`. -/
theorem condNextSymbol_sum_eq_one
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (ω : Ω) (m : ℕ)
    (hpos : 0 < (μ.map (p.blockRV m)).real {p.blockRV m ω}) :
    (∑ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc (p.blockRV m ω) a}
        / (μ.map (p.blockRV m)).real {p.blockRV m ω})
      = 1 := by
  rw [← Finset.sum_div, extendCylinder_measureReal_sum_eq μ p ω m,
      div_self hpos.ne']

end InformationTheory.Shannon
