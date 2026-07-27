import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.MartonBridge

/-!
# Broadcast channel — Marton's inner bound as a union over auxiliary alphabets

`martonRegion` is the quadrilateral of one fixed pair of auxiliary alphabets, whereas the UV
outer region is a union over five-tuple laws.  This file takes the union on the inner side, so
that the two regions can be compared as sets.

## Main definitions

* `bcAuxAlphabet k` — the auxiliary alphabet of cardinality `k + 1`.
* `martonRegionUnion W` — Marton's inner bound, as the closure of the union of `martonRegion`
  over the auxiliary laws on those alphabets.
* `martonRegionUnionFS W` — the same union restricted to the full-support indices, which is the
  form the achievability theorem applies to.

## Main statements

* `martonRegionUnion_subset_uv` — the union sits inside the UV outer region.
* `martonRegionUnionFS_subset_capacity` — the full-support union sits inside the operational
  capacity region.

## Implementation notes

The auxiliaries range over `ULift (Fin (k + 1))`, one cardinality at a time, in the universe of
the input alphabet: fixing the cardinality avoids quantifying over types, and the universe lift
is what lets the comparison classes be applied at a member of the union.  A countable auxiliary
alphabet is not available here, unlike on the outer side: the dependence between the two
auxiliaries is the one information slot reading no output letter, so it is the one that can be
infinite, and the `toReal` convention would then drop the sum-rate penalty.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} {β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The auxiliary alphabet of cardinality `k + 1`, in the universe of the input alphabet.
The successor form keeps every index of the union nonempty, which `martonRegion` requires of its
auxiliary alphabets. -/
abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))

/-- Marton's inner bound as a subset of the plane: the closure of the union of the
quadrilaterals `martonRegion pV K W` over the auxiliary laws on `bcAuxAlphabet`.
The closure makes the union a closed set, as `bcCapacityRegion` and `bcOuterRegionUV` both are,
and costs nothing in either inclusion because a closed superset absorbs it. -/
noncomputable def martonRegionUnion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K), martonRegion pV K W)

/-- The same union over the full-support indices only: the auxiliary law and the auxiliary
kernel charge every point.  Those are the regularity preconditions of
`marton_region_subset_capacity`, so this is the form of the union that is achievable. -/
noncomputable def martonRegionUnionFS (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k₁ : ℕ) (k₂ : ℕ)
    (pV : Measure (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂))
    (_ : IsProbabilityMeasure pV)
    (_ : ∀ v : bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂, 0 < pV.real {v})
    (K : Kernel (bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) α)
    (_ : IsMarkovKernel K)
    (_ : ∀ (v : bcAuxAlphabet.{u} k₁ × bcAuxAlphabet.{u} k₂) (a : α), 0 < (K v).real {a}),
    martonRegion pV K W)

/-- Marton's inner bound is contained in the UV outer region, with no support hypothesis on the
auxiliary law, the auxiliary kernel or the channel. -/
@[entry_point]
theorem martonRegionUnion_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegionUnion W ⊆ bcOuterRegionUV W := by
  refine closure_minimal ?_ (bcOuterRegionUV_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun K ↦ Set.iUnion_subset fun hK ↦ ?_
  exact marton_region_subset_uv pV K W

theorem martonRegionUnionFS_subset_union (W : BCChannel α β₁ β₂) :
    martonRegionUnionFS W ⊆ martonRegionUnion W := by
  refine closure_mono ?_
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun _ ↦ Set.iUnion_subset fun K ↦
      Set.iUnion_subset fun hK ↦ Set.iUnion_subset fun _ ↦ ?_
  exact Set.subset_iUnion_of_subset k₁ (Set.subset_iUnion_of_subset k₂
    (Set.subset_iUnion_of_subset pV (Set.subset_iUnion_of_subset hpV
      (Set.subset_iUnion_of_subset K (Set.subset_iUnion_of_subset hK subset_rfl)))))

/-- The full-support form of Marton's inner bound is achievable: it is contained in the
operational capacity region. -/
@[entry_point]
theorem martonRegionUnionFS_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    martonRegionUnionFS W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ (bc_capacityRegion_isClosed W)
  refine Set.iUnion_subset fun k₁ ↦ Set.iUnion_subset fun k₂ ↦ Set.iUnion_subset fun pV ↦
    Set.iUnion_subset fun hpV ↦ Set.iUnion_subset fun hpVpos ↦ Set.iUnion_subset fun K ↦
      Set.iUnion_subset fun hK ↦ Set.iUnion_subset fun hKpos ↦ ?_
  exact marton_region_subset_capacity pV K W hpVpos hKpos hW

end InformationTheory.Shannon.BroadcastChannel.Marton
