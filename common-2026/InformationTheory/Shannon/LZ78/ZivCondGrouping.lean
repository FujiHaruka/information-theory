import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.ZivMeasureBridge
import InformationTheory.Shannon.LZ78.ZivLengthGrouping
import InformationTheory.Shannon.SMB.AlgoetCover.Core
import Mathlib.Data.ENNReal.BigOperators

/-!
# LZ78 conditional (k-state, length) grouping bridge

This file supplies the **conditional** analogue of the length-grouping measure
bridge for the LZ78 achievability wall `ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`,
`@residual(wall:lz78-aseventual-ziv)`), route LOCK = `markovFactor`.

## Approach

The dead marginal route (`ZivMeasureBridge.lean`,
`lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead`) fibers phrases
by `List.length` and lower-bounds the entropy by `∑ -log P_ℓ` for the *marginal*
`P_ℓ`. That direction is D8-dead (the marginal sum bound runs the wrong way for
the Ziv connection). This file instead uses the **conditional** per-`k`-state
product sub-distribution `condQkState μ p k s` (from `markovFactor`, leg 7) as
the grouping vehicle, fibering phrases by the **pair** `(k-state, length)`:

1. **Outer grouping** over `ι = (Fin k → α) × ℕ`: apply
   `card_mul_log_le_sum_group_mul_log_add_card_log` to the image
   `G = phrases.image (st w, w.length)`, giving
   `c · log c ≤ ∑_g c_g · log c_g + c · log (G.card)`, where the fibers
   `grp g = phrases.filter (st w, w.length) = g` partition `phrases`.

2. **Per-fiber log-sum step**: within a fiber `(s, ℓ)`, all phrases have length
   `ℓ`, so `toFinVec ℓ` injects them into `Fin ℓ → α`. With
   `P Z = (condQkState μ p k s ℓ Z).toReal`, `group_card_mul_log_le_sum_neg_log`
   gives `card · log card ≤ ∑ -log P`.

   - The **`.toReal` sub-distribution bound** `∑_{Z} P Z ≤ 1` is derived from the
     `ℝ≥0∞` fact `condQkState_sum_le_one` via `ENNReal.toReal_sum` (each term is
     `≤ 1 < ⊤`, so finite) and `ENNReal.toReal_mono`. This is the route's `.toReal`
     bridge `(iii)`.

3. **Aggregation**: sum the per-fiber bounds back into a single sum over phrases.

The result `condState_grouping_bound` is stated abstractly (a `Finset (List α)`
of phrases with an arbitrary `k`-state assignment `st`); wiring it to the actual
LZ78 parse structure is a downstream leg.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-! ## Per-element bound and finiteness for `condQkState` -/

omit [DecidableEq α] in
/-- Each conditional mass `condQkState μ p k s ℓ Z` is at most `1`: a single
summand is bounded by the total `≤ 1` sub-distribution sum. -/
lemma condQkState_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k : ℕ) (s : Fin k → α) (ℓ : ℕ) (Z : Fin ℓ → α) :
    condQkState μ p k s ℓ Z ≤ 1 := by
  calc condQkState μ p k s ℓ Z
      ≤ ∑ w : Fin ℓ → α, condQkState μ p k s ℓ w :=
        Finset.single_le_sum (fun w _ => zero_le') (Finset.mem_univ Z)
    _ ≤ 1 := condQkState_sum_le_one μ p k s ℓ

/-! ## The `.toReal` sub-distribution bridge (route step iii) -/

omit [DecidableEq α] in
/-- **`.toReal` sub-distribution bound**: the real-valued conditional masses on a
finite set `S` of distinct strings sum to at most `1`. Pushes the `ℝ≥0∞` fact
`condQkState_sum_le_one` through `.toReal` (each term `≤ 1 < ⊤`). -/
lemma sum_condQkState_toReal_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k : ℕ) (s : Fin k → α) (ℓ : ℕ) (S : Finset (Fin ℓ → α)) :
    (∑ Z ∈ S, (condQkState μ p k s ℓ Z).toReal) ≤ 1 := by
  -- Each summand is finite (`≤ 1 < ⊤`), so `.toReal` commutes with the sum.
  have hfin : ∀ Z ∈ S, condQkState μ p k s ℓ Z ≠ ⊤ := fun Z _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (condQkState_le_one μ p k s ℓ Z)
  rw [← ENNReal.toReal_sum hfin]
  -- The `ℝ≥0∞` partial sum is `≤ 1`; `.toReal` is monotone with target `1`.
  have hsum_le : (∑ Z ∈ S, condQkState μ p k s ℓ Z) ≤ 1 := by
    calc (∑ Z ∈ S, condQkState μ p k s ℓ Z)
        ≤ ∑ Z : Fin ℓ → α, condQkState μ p k s ℓ Z :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ ≤ 1 := condQkState_sum_le_one μ p k s ℓ
  calc (∑ Z ∈ S, condQkState μ p k s ℓ Z).toReal
      ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hsum_le
    _ = 1 := ENNReal.toReal_one

/-! ## Conditional (k-state, length) grouping bound -/

/-- **Conditional `(k-state, length)` grouped entropy bound for an abstract phrase
set**.

Given a finite phrase set `phrases : Finset (List α)`, a `k`-state assignment
`st : List α → (Fin k → α)`, and positivity of the per-phrase conditional mass,

```
c · log c ≤ ∑_{w ∈ phrases} -log (condQkState μ p k (st w) |w| (toFinVec |w| w))
            + c · log D,
```

where `c = #phrases` and `D = #{(st w, |w|)}` is the number of distinct
`(k-state, length)` pairs. This is the conditional analogue of the dead marginal
bound `lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead`, with the
grouping index lifted from `length` to `(k-state, length)` and the marginal
replaced by the `markovFactor`-derived conditional sub-distribution `condQkState`. -/
theorem condState_grouping_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ)
    (phrases : Finset (List α)) (st : List α → (Fin k → α))
    (hpos : ∀ w ∈ phrases,
      0 < (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal) :
    (phrases.card : ℝ) * Real.log (phrases.card : ℝ)
      ≤ (∑ w ∈ phrases,
            - Real.log (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal)
        + (phrases.card : ℝ)
            * Real.log (((phrases.image (fun w => (st w, w.length))).card : ℝ)) := by
  classical
  -- Outer grouping index: distinct `(k-state, length)` pairs.
  set keyf : List α → (Fin k → α) × ℕ := fun w => (st w, w.length) with hkeyf
  set G : Finset ((Fin k → α) × ℕ) := phrases.image keyf with hGdef
  -- Per-fiber count.
  set kk : ((Fin k → α) × ℕ) → ℕ :=
    fun g => (phrases.filter (fun w => keyf w = g)).card with hkk
  -- The fibers partition `phrases`: `∑ g ∈ G, kk g = #phrases`.
  have hfiber_card : phrases.card = ∑ g ∈ G, kk g := by
    rw [hGdef, hkk]
    exact Finset.card_eq_sum_card_image keyf phrases
  rcases phrases.eq_empty_or_nonempty with hpe | hpne
  · -- Degenerate empty case: both sides vanish.
    subst hpe; simp
  -- `G` is nonempty since `phrases` is.
  have hGne : G.Nonempty := by
    rw [hGdef]; exact hpne.image keyf
  -- Per-state conditional masses (real-valued), indexed by the `k`-state.
  set Pm : (Fin k → α) → (ℓ : ℕ) → (Fin ℓ → α) → ℝ :=
    fun s ℓ Z => (condQkState μ p k s ℓ Z).toReal with hPm
  -- Per-fiber log-sum bound, summed over `G`:
  -- `∑_g (kk g)·log(kk g) ≤ ∑_g ∑_{w in fiber g} -log P(st w)|w|(toFinVec |w| w)`.
  have hgroup :
      (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
      ≤ ∑ g ∈ G, ∑ w ∈ phrases.filter (fun w => keyf w = g),
            - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    refine Finset.sum_le_sum (fun g _ => ?_)
    -- Decompose the pair `g = (s, ℓ)`.
    obtain ⟨s, ℓ⟩ := g
    -- The fiber: all phrases with `(st w, |w|) = (s, ℓ)`.
    set grp : Finset (List α) := phrases.filter (fun w => keyf w = (s, ℓ)) with hgrp
    -- In the fiber, each `w` has length `ℓ` and state `s`.
    have hgrp_len : ∀ w ∈ grp, w.length = ℓ := by
      intro w hw
      have := (Finset.mem_filter.mp hw).2
      rw [hkeyf] at this
      exact (Prod.ext_iff.mp this).2
    have hgrp_st : ∀ w ∈ grp, st w = s := by
      intro w hw
      have := (Finset.mem_filter.mp hw).2
      rw [hkeyf] at this
      exact (Prod.ext_iff.mp this).1
    -- `toFinVec ℓ` is injective on `grp` (all elements have length `ℓ`).
    have hinj : Set.InjOn (toFinVec ℓ) (grp : Set (List α)) := by
      intro w hw v hv hwv
      exact toFinVec_injOn ℓ (hgrp_len w hw) (hgrp_len v hv) hwv
    -- The image of `grp` under `toFinVec ℓ` in `Fin ℓ → α`.
    set S : Finset (Fin ℓ → α) := grp.image (toFinVec ℓ) with hSdef
    have hScard : S.card = grp.card := by
      rw [hSdef, Finset.card_image_of_injOn hinj]
    -- Positivity of the conditional mass on each image point.
    have hSpos : ∀ Z ∈ S, 0 < Pm s ℓ Z := by
      intro Z hZ
      rw [hSdef, Finset.mem_image] at hZ
      obtain ⟨w, hw, rfl⟩ := hZ
      have hwlen : w.length = ℓ := hgrp_len w hw
      have hwst : st w = s := hgrp_st w hw
      have hwmem : w ∈ phrases := (Finset.mem_filter.mp hw).1
      have hp := hpos w hwmem
      rw [hwlen, hwst] at hp
      simpa only [hPm] using hp
    -- Sub-distribution bound (the `.toReal` bridge, step iii).
    have hSsum : (∑ Z ∈ S, Pm s ℓ Z) ≤ 1 :=
      sum_condQkState_toReal_le_one μ p k s ℓ S
    -- Per-fiber log-sum step.
    have hlogsum := group_card_mul_log_le_sum_neg_log S (Pm s ℓ) hSpos hSsum
    rw [hScard] at hlogsum
    -- Transfer the RHS sum from `S` back to `grp` via the injection.
    have hrhs_eq : (∑ Z ∈ S, - Real.log (Pm s ℓ Z))
        = ∑ w ∈ grp, - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
      rw [hSdef, Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [hgrp_len w hw, hgrp_st w hw]
    rw [hrhs_eq] at hlogsum
    -- `kk (s, ℓ) = grp.card` definitionally.
    show ((phrases.filter (fun w => keyf w = (s, ℓ))).card : ℝ)
          * Real.log ((phrases.filter (fun w => keyf w = (s, ℓ))).card : ℝ)
        ≤ ∑ w ∈ phrases.filter (fun w => keyf w = (s, ℓ)),
            - Real.log (Pm (st w) w.length (toFinVec w.length w))
    rw [← hgrp]
    exact hlogsum
  -- Reassemble the fibers into a single sum over all phrases.
  have hfiber_sum :
      (∑ g ∈ G, ∑ w ∈ phrases.filter (fun w => keyf w = g),
          - Real.log (Pm (st w) w.length (toFinVec w.length w)))
      = ∑ w ∈ phrases, - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [hGdef]
    exact Finset.sum_fiberwise_of_maps_to (fun w hw =>
      Finset.mem_image_of_mem keyf hw) _
  -- Outer grouping inequality.
  have hmain := card_mul_log_le_sum_group_mul_log_add_card_log G kk hGne
  rw [← hfiber_card] at hmain
  -- Combine.
  calc (phrases.card : ℝ) * Real.log (phrases.card : ℝ)
      ≤ (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
          + (phrases.card : ℝ) * Real.log (G.card : ℝ) := hmain
    _ ≤ (∑ g ∈ G, ∑ w ∈ phrases.filter (fun w => keyf w = g),
              - Real.log (Pm (st w) w.length (toFinVec w.length w)))
          + (phrases.card : ℝ) * Real.log (G.card : ℝ) := by gcongr
    _ = (∑ w ∈ phrases,
              - Real.log (Pm (st w) w.length (toFinVec w.length w)))
          + (phrases.card : ℝ) * Real.log (G.card : ℝ) := by rw [hfiber_sum]

end InformationTheory.Shannon
