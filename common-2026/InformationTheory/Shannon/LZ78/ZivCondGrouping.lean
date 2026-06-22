import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.ZivMeasureBridge
import InformationTheory.Shannon.LZ78.ZivLengthGrouping
import InformationTheory.Shannon.LZ78.EmpiricalEntropyMean
import InformationTheory.Shannon.SMB.AlgoetCover.MarkovLikelihoodRatio
import Mathlib.Data.ENNReal.BigOperators

/-!
# LZ78 conditional (k-state, length) grouping bridge

This file supplies the **conditional** analogue of the length-grouping measure
bridge for the LZ78 achievability wall `ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean`,
slug `lz78-aseventual-ziv`), via the `markovFactor` route.

## Approach

The dead marginal route (`ZivMeasureBridge.lean`,
`lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead`) fibers phrases
by `List.length` and lower-bounds the entropy by `∑ -log P_ℓ` for the *marginal*
`P_ℓ`. That direction is dead (the marginal sum bound runs the wrong way for
the Ziv connection). This file instead uses the **conditional** per-`k`-state
product sub-distribution `condQkState μ p k s` (from `markovFactor`) as
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
        Finset.single_le_sum (fun w _ ↦ zero_le') (Finset.mem_univ Z)
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
  have hfin : ∀ Z ∈ S, condQkState μ p k s ℓ Z ≠ ⊤ := fun Z _ ↦
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

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
theorem condState_grouping_lengthProfile_counts {σ : Type*} [DecidableEq σ]
    (phrases : Finset (List α)) (keyf : List α → σ × ℕ)
    (hkey2 : ∀ w, (keyf w).2 = w.length) (ℓ : ℕ) :
    (∑ g ∈ (phrases.image keyf).filter (fun g ↦ g.2 = ℓ),
        (phrases.filter (fun w ↦ keyf w = g)).card)
      = (phrases.filter (fun w ↦ w.length = ℓ)).card := by
  classical
  set G : Finset (σ × ℕ) := phrases.image keyf with hGdef
  set kk : (σ × ℕ) → ℕ :=
    fun g ↦ (phrases.filter (fun w ↦ keyf w = g)).card with hkk
  set Pℓ : Finset (List α) := phrases.filter (fun w ↦ w.length = ℓ) with hPℓ
  -- `Pℓ.card = ∑_{g ∈ Pℓ.image keyf} (Pℓ.filter (keyf = g)).card`.
  have hcardP := Finset.card_eq_sum_card_image keyf Pℓ
  -- (a) `Pℓ.image keyf = G.filter (·.2 = ℓ)`.
  have ha : Pℓ.image keyf = G.filter (fun g ↦ g.2 = ℓ) := by
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, hPℓ, hGdef]
    constructor
    · rintro ⟨w, ⟨hwp, hwℓ⟩, rfl⟩
      exact ⟨⟨w, hwp, rfl⟩, by rw [hkey2]; exact hwℓ⟩
    · rintro ⟨⟨w, hwp, rfl⟩, hg2⟩
      refine ⟨w, ⟨hwp, ?_⟩, rfl⟩
      rw [hkey2] at hg2; exact hg2
  -- (b) For `g` with `g.2 = ℓ`, filtering `keyf = g` over `Pℓ` or all of
  --     `phrases` gives the same count (since `keyf w = g ⇒ |w| = ℓ`).
  have hb : ∀ g ∈ Pℓ.image keyf,
      (Pℓ.filter (fun w ↦ keyf w = g)).card = kk g := by
    intro g hg
    rw [hkk]
    congr 1
    ext w
    simp only [Finset.mem_filter, hPℓ]
    constructor
    · rintro ⟨⟨hwp, _⟩, hwk⟩; exact ⟨hwp, hwk⟩
    · rintro ⟨hwp, hwk⟩
      refine ⟨⟨hwp, ?_⟩, hwk⟩
      -- `keyf w = g` and `g ∈ Pℓ.image keyf` (so `g.2 = ℓ`) give `|w| = ℓ`.
      rw [ha, Finset.mem_filter] at hg
      have : w.length = g.2 := by rw [← hkey2 w, hwk]
      rw [this]; exact hg.2
  rw [← ha]
  rw [Finset.sum_congr rfl hb] at hcardP
  exact hcardP.symm

theorem condState_grouping_perFiber_logsum
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ)
    (phrases : Finset (List α)) (st : List α → (Fin k → α))
    (hpos : ∀ w ∈ phrases,
      0 < (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal) :
    (∑ g ∈ phrases.image (fun w ↦ (st w, w.length)),
        ((phrases.filter (fun w ↦ (st w, w.length) = g)).card : ℝ)
          * Real.log ((phrases.filter (fun w ↦ (st w, w.length) = g)).card : ℝ))
      ≤ ∑ g ∈ phrases.image (fun w ↦ (st w, w.length)),
          ∑ w ∈ phrases.filter (fun w ↦ (st w, w.length) = g),
            - Real.log (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal := by
  classical
  set keyf : List α → (Fin k → α) × ℕ := fun w ↦ (st w, w.length) with hkeyf
  set Pm : (Fin k → α) → (ℓ : ℕ) → (Fin ℓ → α) → ℝ :=
    fun s ℓ Z ↦ (condQkState μ p k s ℓ Z).toReal with hPm
  refine Finset.sum_le_sum (fun g _ ↦ ?_)
  obtain ⟨s, ℓ⟩ := g
  set grp : Finset (List α) := phrases.filter (fun w ↦ keyf w = (s, ℓ)) with hgrp
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
  have hinj : Set.InjOn (toFinVec ℓ) (grp : Set (List α)) := by
    intro w hw v hv hwv
    exact toFinVec_injOn ℓ (hgrp_len w hw) (hgrp_len v hv) hwv
  set S : Finset (Fin ℓ → α) := grp.image (toFinVec ℓ) with hSdef
  have hScard : S.card = grp.card := by
    rw [hSdef, Finset.card_image_of_injOn hinj]
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
  have hSsum : (∑ Z ∈ S, Pm s ℓ Z) ≤ 1 :=
    sum_condQkState_toReal_le_one μ p k s ℓ S
  have hlogsum := group_card_mul_log_le_sum_neg_log S (Pm s ℓ) hSpos hSsum
  rw [hScard] at hlogsum
  have hrhs_eq : (∑ Z ∈ S, - Real.log (Pm s ℓ Z))
      = ∑ w ∈ grp, - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [hSdef, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun w hw ↦ ?_)
    rw [hgrp_len w hw, hgrp_st w hw]
  rw [hrhs_eq] at hlogsum
  change ((phrases.filter (fun w ↦ keyf w = (s, ℓ))).card : ℝ)
        * Real.log ((phrases.filter (fun w ↦ keyf w = (s, ℓ))).card : ℝ)
      ≤ ∑ w ∈ phrases.filter (fun w ↦ keyf w = (s, ℓ)),
          - Real.log (Pm (st w) w.length (toFinVec w.length w))
  rw [← hgrp]
  exact hlogsum

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
            * Real.log (((phrases.image (fun w ↦ (st w, w.length))).card : ℝ)) := by
  classical
  -- Outer grouping index: distinct `(k-state, length)` pairs.
  set keyf : List α → (Fin k → α) × ℕ := fun w ↦ (st w, w.length) with hkeyf
  set G : Finset ((Fin k → α) × ℕ) := phrases.image keyf with hGdef
  -- Per-fiber count.
  set kk : ((Fin k → α) × ℕ) → ℕ :=
    fun g ↦ (phrases.filter (fun w ↦ keyf w = g)).card with hkk
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
    fun s ℓ Z ↦ (condQkState μ p k s ℓ Z).toReal with hPm
  -- Per-fiber log-sum bound, summed over `G`:
  -- `∑_g (kk g)·log(kk g) ≤ ∑_g ∑_{w in fiber g} -log P(st w)|w|(toFinVec |w| w)`.
  have hgroup :
      (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
      ≤ ∑ g ∈ G, ∑ w ∈ phrases.filter (fun w ↦ keyf w = g),
            - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [hGdef, hkeyf, hkk, hPm]
    exact condState_grouping_perFiber_logsum μ p k phrases st hpos
  -- Reassemble the fibers into a single sum over all phrases.
  have hfiber_sum :
      (∑ g ∈ G, ∑ w ∈ phrases.filter (fun w ↦ keyf w = g),
          - Real.log (Pm (st w) w.length (toFinVec w.length w)))
      = ∑ w ∈ phrases, - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [hGdef]
    exact Finset.sum_fiberwise_of_maps_to (fun w hw ↦
      Finset.mem_image_of_mem keyf hw) _
  -- Outer grouping inequality.
  have hmain := card_mul_log_le_sum_group_mul_log_add_card_log G kk hGne
  rw [← hfiber_card] at hmain
  -- Combine.
  calc (phrases.card : ℝ) * Real.log (phrases.card : ℝ)
      ≤ (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
          + (phrases.card : ℝ) * Real.log (G.card : ℝ) := hmain
    _ ≤ (∑ g ∈ G, ∑ w ∈ phrases.filter (fun w ↦ keyf w = g),
              - Real.log (Pm (st w) w.length (toFinVec w.length w)))
          + (phrases.card : ℝ) * Real.log (G.card : ℝ) := by gcongr
    _ = (∑ w ∈ phrases,
              - Real.log (Pm (st w) w.length (toFinVec w.length w)))
          + (phrases.card : ℝ) * Real.log (G.card : ℝ) := by rw [hfiber_sum]

/-! ## State-marginalization (a finer partition has higher entropy) -/

/-- **State-marginalization grouping inequality** (abstract `Finset`/`Real`).

Fibering a pair-indexed count function `kk : (σ × ℕ) → ℕ` by the length
coordinate, the length-marginal `∑·log` sum is bounded by the full pair `∑·log`
sum plus an entropy correction `(∑ kk)·log nStates`, provided every length fiber
has at most `nStates` distinct states:

```
∑_ℓ (c_ℓ · log c_ℓ) ≤ ∑_g (c_g · log c_g) + (∑_g c_g) · log nStates,
```

where `c_ℓ = ∑_{g.2 = ℓ} kk g` and `c_g = kk g`. This is the discrete form of
`H(state | length) ≤ log nStates`: a finer partition (by `(state, length)`)
carries at most `log nStates` more entropy per phrase than the coarser
length-only partition. Applying `card_mul_log_le_sum_group_mul_log_add_card_log`
inside each length fiber and bounding the fiber's group count `≤ nStates`. -/
theorem state_marginalization_bound
    {σ : Type*} [DecidableEq σ]
    (G : Finset (σ × ℕ)) (kk : (σ × ℕ) → ℕ) (nStates : ℕ)
    (hfiber_le : ∀ ℓ ∈ G.image Prod.snd,
      (G.filter (fun g ↦ g.2 = ℓ)).card ≤ nStates) :
    (∑ ℓ ∈ G.image Prod.snd,
        ((∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), kk g : ℕ) : ℝ)
          * Real.log ((∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), kk g : ℕ) : ℝ))
      ≤ (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
        + ((∑ g ∈ G, kk g : ℕ) : ℝ) * Real.log (nStates : ℝ) := by
  classical
  set L : Finset ℕ := G.image Prod.snd with hL
  set cf : ℕ → ℝ := fun ℓ ↦ ((∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), kk g : ℕ) : ℝ)
    with hcf
  -- Per-length-fiber grouping bound + state-count correction.
  have hper : ∀ ℓ ∈ L,
      cf ℓ * Real.log (cf ℓ)
        ≤ (∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), (kk g : ℝ) * Real.log (kk g : ℝ))
          + cf ℓ * Real.log (nStates : ℝ) := by
    intro ℓ hℓ
    -- The fiber is nonempty (since `ℓ` is in the image).
    have hfne : (G.filter (fun g ↦ g.2 = ℓ)).Nonempty := by
      rw [hL, Finset.mem_image] at hℓ
      obtain ⟨g, hg, hgℓ⟩ := hℓ
      exact ⟨g, Finset.mem_filter.mpr ⟨hg, hgℓ⟩⟩
    -- Abstract grouping inequality inside the fiber: the correction multiplier
    -- is `cf ℓ = ∑ kk`, not the fiber cardinality.
    have hgroup := card_mul_log_le_sum_group_mul_log_add_card_log
      (G.filter (fun g ↦ g.2 = ℓ)) kk hfne
    -- `cf ℓ · log (card fiber) ≤ cf ℓ · log nStates` since `cf ℓ ≥ 0` and
    -- `card fiber ≤ nStates`.
    have hflpos : (0 : ℝ) < ((G.filter (fun g ↦ g.2 = ℓ)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hfne
    have hlogle : Real.log ((G.filter (fun g ↦ g.2 = ℓ)).card : ℝ)
        ≤ Real.log (nStates : ℝ) := by
      apply Real.log_le_log hflpos
      exact_mod_cast hfiber_le ℓ hℓ
    have hcfnn : (0 : ℝ) ≤ cf ℓ := by rw [hcf]; positivity
    have hcorr : cf ℓ * Real.log ((G.filter (fun g ↦ g.2 = ℓ)).card : ℝ)
        ≤ cf ℓ * Real.log (nStates : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle hcfnn
    -- Combine `hgroup` (with `∑ kk = cf ℓ`) and `hcorr`.
    calc cf ℓ * Real.log (cf ℓ)
        ≤ (∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), (kk g : ℝ) * Real.log (kk g : ℝ))
            + cf ℓ * Real.log ((G.filter (fun g ↦ g.2 = ℓ)).card : ℝ) := hgroup
      _ ≤ (∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), (kk g : ℝ) * Real.log (kk g : ℝ))
            + cf ℓ * Real.log (nStates : ℝ) := by gcongr
  -- Sum the per-fiber bound over all lengths.
  have hsum := Finset.sum_le_sum hper
  -- Identify the two RHS aggregate sums via fiberwise reindexing.
  have hmaps : ∀ g ∈ G, g.2 ∈ L := fun g hg ↦ by
    rw [hL]; exact Finset.mem_image_of_mem Prod.snd hg
  have hfib1 : (∑ ℓ ∈ L, ∑ g ∈ G.filter (fun g ↦ g.2 = ℓ),
        (kk g : ℝ) * Real.log (kk g : ℝ))
      = ∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hfib2 : (∑ ℓ ∈ L, cf ℓ) = ((∑ g ∈ G, kk g : ℕ) : ℝ) := by
    rw [hcf]
    push_cast
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun g ↦ (kk g : ℝ))
  calc (∑ ℓ ∈ L, cf ℓ * Real.log (cf ℓ))
      ≤ ∑ ℓ ∈ L, ((∑ g ∈ G.filter (fun g ↦ g.2 = ℓ),
            (kk g : ℝ) * Real.log (kk g : ℝ)) + cf ℓ * Real.log (nStates : ℝ)) :=
        hsum
    _ = (∑ ℓ ∈ L, ∑ g ∈ G.filter (fun g ↦ g.2 = ℓ),
            (kk g : ℝ) * Real.log (kk g : ℝ))
          + (∑ ℓ ∈ L, cf ℓ * Real.log (nStates : ℝ)) := Finset.sum_add_distrib
    _ = (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
          + ((∑ g ∈ G, kk g : ℕ) : ℝ) * Real.log (nStates : ℝ) := by
        rw [hfib1, ← Finset.sum_mul, hfib2]

/-! ## Conditional grouping bound with mean-length overhead -/

/-- **Conditional `(k-state, length)` grouped entropy bound with mean-length
overhead** (LZ78 achievability, `o(n)` form).

The mean-length / empirical-entropy upgrade of `condState_grouping_bound`: the
loose `c · log D` overhead (worst-case `Θ(n)`) is replaced by the manifestly
`o(n)` empirical-entropy overhead `c · log (N / c) + c + c · log #states`, where
`N = ∑_{w ∈ phrases} |w|` is the total parsed length and
`#states = (Fintype.card α)^k`:

```
c · log c ≤ ∑_{w ∈ phrases} -log (condQkState μ p k (st w) |w| (toFinVec |w| w))
            + (c · log (N / c) + c + c · log #states).
```

Here `c · log (N / c)` is the mean-length term (`o(n)` since the mean length is
`~ log n` for the LZ78 parse) and `c · log #states = c · k · log (card α)` is
`o(n)` for fixed `k` (since `c = O(n / log n)`). The proof composes
`empirical_entropy_le_log_mean` (length empirical entropy ≤ `c·log(mean)+c`),
`state_marginalization_bound` (state correction ≤ `c·log #states`), and the
per-fiber log-sum step of `condState_grouping_bound`. -/
@[entry_point]
theorem condState_grouping_bound_mean
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ)
    (phrases : Finset (List α)) (st : List α → (Fin k → α))
    (hpos : ∀ w ∈ phrases,
      0 < (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal)
    (hlen1 : ∀ w ∈ phrases, 1 ≤ w.length)
    (hne : phrases.Nonempty) :
    (phrases.card : ℝ) * Real.log (phrases.card : ℝ)
      ≤ (∑ w ∈ phrases,
            - Real.log (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal)
        + ((phrases.card : ℝ)
              * Real.log ((∑ w ∈ phrases, (w.length : ℝ)) / (phrases.card : ℝ))
            + (phrases.card : ℝ)
            + (phrases.card : ℝ) * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ)) := by
  classical
  -- Notation: `c = #phrases`, `N = ∑|w|`, length counts `cℓ`, length set `L`.
  set c : ℝ := (phrases.card : ℝ) with hc
  set N : ℝ := (∑ w ∈ phrases, (w.length : ℝ)) with hN
  set L : Finset ℕ := phrases.image List.length with hL
  set cℓ : ℕ → ℝ := fun ℓ ↦ ((phrases.filter (fun w ↦ w.length = ℓ)).card : ℝ)
    with hcℓ
  -- The grouping vehicle, identical to `condState_grouping_bound`.
  set keyf : List α → (Fin k → α) × ℕ := fun w ↦ (st w, w.length) with hkeyf
  set G : Finset ((Fin k → α) × ℕ) := phrases.image keyf with hGdef
  set kk : ((Fin k → α) × ℕ) → ℕ :=
    fun g ↦ (phrases.filter (fun w ↦ keyf w = g)).card with hkk
  set Pm : (Fin k → α) → (ℓ : ℕ) → (Fin ℓ → α) → ℝ :=
    fun s ℓ Z ↦ (condQkState μ p k s ℓ Z).toReal with hPm
  -- `c > 0` from nonemptiness.
  have hc_pos : 0 < c := by rw [hc]; exact_mod_cast Finset.card_pos.mpr hne
  -- (Step A) Empirical-entropy/mean bound on the length profile:
  --   `c·log c ≤ ∑_ℓ cℓ·log cℓ + (c·log(N/c) + c)`.
  -- Length counts sum to `c` and length-weighted counts sum to `N`.
  have hsumC : (∑ ℓ ∈ L, cℓ ℓ) = c := by
    rw [hcℓ, hc, hL]
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_image List.length phrases).symm
  have hsumN : (∑ ℓ ∈ L, (ℓ : ℝ) * cℓ ℓ) = N := by
    rw [hN, hL]
    -- `∑_ℓ ℓ·#(phrases of length ℓ) = ∑_w |w|` by fiberwise reindexing.
    have hmaps : ∀ w ∈ phrases, w.length ∈ phrases.image List.length :=
      fun w hw ↦ Finset.mem_image_of_mem List.length hw
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun w ↦ (w.length : ℝ))]
    refine Finset.sum_congr rfl (fun ℓ hℓ ↦ ?_)
    -- Inside the fiber `{w | |w| = ℓ}`, each summand is `ℓ`, and there are `cℓ ℓ`.
    rw [hcℓ]
    rw [Finset.sum_congr rfl (fun w hw ↦ by
      rw [(Finset.mem_filter.mp hw).2]), Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have hpos_cℓ : ∀ ℓ ∈ L, 0 < cℓ ℓ := by
    intro ℓ hℓ
    simp only [hcℓ]
    rw [hL, Finset.mem_image] at hℓ
    obtain ⟨w, hw, hwℓ⟩ := hℓ
    have hnec : (phrases.filter (fun w ↦ w.length = ℓ)).Nonempty :=
      ⟨w, Finset.mem_filter.mpr ⟨hw, hwℓ⟩⟩
    exact_mod_cast Finset.card_pos.mpr hnec
  have hl1_L : ∀ ℓ ∈ L, 1 ≤ ℓ := by
    intro ℓ hℓ
    rw [hL, Finset.mem_image] at hℓ
    obtain ⟨w, hw, hwℓ⟩ := hℓ
    rw [← hwℓ]; exact hlen1 w hw
  have hC_pos : 0 < ∑ ℓ ∈ L, cℓ ℓ := by rw [hsumC]; exact hc_pos
  -- Apply the empirical-entropy/mean lemma.
  have hemp := empirical_entropy_le_log_mean L cℓ hpos_cℓ hl1_L hC_pos
  rw [hsumC, hsumN] at hemp
  -- Rewrite the LHS empirical entropy as `c·log c − ∑ cℓ·log cℓ`.
  have hLHS : (∑ ℓ ∈ L, cℓ ℓ * Real.log (c / cℓ ℓ))
      = c * Real.log c - ∑ ℓ ∈ L, cℓ ℓ * Real.log (cℓ ℓ) := by
    have hCsum : c * Real.log c = ∑ ℓ ∈ L, cℓ ℓ * Real.log c := by
      rw [← Finset.sum_mul, hsumC]
    rw [hCsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ℓ hℓ ↦ ?_)
    rw [Real.log_div hc_pos.ne' (hpos_cℓ ℓ hℓ).ne']
    ring
  rw [hLHS] at hemp
  have hmean : c * Real.log c
      ≤ (∑ ℓ ∈ L, cℓ ℓ * Real.log (cℓ ℓ)) + (c * Real.log (N / c) + c) := by
    linarith [hemp]
  -- (Step B) State-marginalization correction:
  --   `∑_ℓ cℓ·log cℓ ≤ ∑_g kk·log kk + c·log #states`.
  -- (M1) The length-image of `G` equals the length set `L`.
  have hM1 : G.image Prod.snd = L := by
    rw [hGdef, hL, hkeyf, Finset.image_image]
    rfl
  -- (M2) Per-length: the pair counts marginalize to the length count (as nats).
  have hM2 : ∀ ℓ ∈ L,
      (∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), kk g)
        = (phrases.filter (fun w ↦ w.length = ℓ)).card := by
    intro ℓ _
    rw [hkk, hGdef]
    exact condState_grouping_lengthProfile_counts phrases keyf (fun _ ↦ rfl) ℓ
  -- (M3) The pair counts sum to `c` (cast to ℝ).
  have hM3 : ((∑ g ∈ G, kk g : ℕ) : ℝ) = c := by
    rw [hc]
    congr 1
    rw [hkk, hGdef]
    exact (Finset.card_eq_sum_card_image keyf phrases).symm
  -- (M4) The fiber-cardinality bound: ≤ `(card α)^k = #(Fin k → α)`.
  have hM4 : ∀ ℓ ∈ G.image Prod.snd,
      (G.filter (fun g ↦ g.2 = ℓ)).card ≤ (Fintype.card α) ^ k := by
    intro ℓ _
    have hcard_fun : (Fintype.card α) ^ k = Fintype.card (Fin k → α) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    rw [hcard_fun]
    -- `Prod.fst` is injective on the fiber (the second coordinate is fixed).
    refine Finset.card_le_card_of_injOn Prod.fst (fun g _ ↦ Finset.mem_univ _) ?_
    intro g hg g' hg' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hg hg'
    exact Prod.ext heq (hg.2.trans hg'.2.symm)
  -- Apply the abstract state-marginalization bound and bridge.
  have hsm := state_marginalization_bound G kk ((Fintype.card α) ^ k) hM4
  rw [hM1] at hsm
  -- Rewrite the LHS sum of `hsm` to `∑_ℓ cℓ·log cℓ` via (M2).
  have hLHSeq : (∑ ℓ ∈ L,
        ((∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), kk g : ℕ) : ℝ)
          * Real.log ((∑ g ∈ G.filter (fun g ↦ g.2 = ℓ), kk g : ℕ) : ℝ))
      = ∑ ℓ ∈ L, cℓ ℓ * Real.log (cℓ ℓ) := by
    refine Finset.sum_congr rfl (fun ℓ hℓ ↦ ?_)
    rw [hM2 ℓ hℓ, hcℓ]
  rw [hLHSeq, hM3] at hsm
  have hstate : (∑ ℓ ∈ L, cℓ ℓ * Real.log (cℓ ℓ))
      ≤ (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
        + c * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ) := hsm
  -- (Step C) Per-fiber log-sum step (the `markovFactor` `.toReal` bridge):
  --   `∑_g kk·log kk ≤ ∑_w -log P_w`.
  have hgroup :
      (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
      ≤ ∑ g ∈ G, ∑ w ∈ phrases.filter (fun w ↦ keyf w = g),
            - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [hGdef, hkeyf, hkk, hPm]
    exact condState_grouping_perFiber_logsum μ p k phrases st hpos
  have hfiber_sum :
      (∑ g ∈ G, ∑ w ∈ phrases.filter (fun w ↦ keyf w = g),
          - Real.log (Pm (st w) w.length (toFinVec w.length w)))
      = ∑ w ∈ phrases, - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [hGdef]
    exact Finset.sum_fiberwise_of_maps_to (fun w hw ↦
      Finset.mem_image_of_mem keyf hw) _
  have hfiber : (∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
      ≤ ∑ w ∈ phrases, - Real.log (Pm (st w) w.length (toFinVec w.length w)) := by
    rw [← hfiber_sum]; exact hgroup
  -- Combine the three steps.
  calc c * Real.log c
      ≤ (∑ ℓ ∈ L, cℓ ℓ * Real.log (cℓ ℓ)) + (c * Real.log (N / c) + c) := hmean
    _ ≤ ((∑ g ∈ G, (kk g : ℝ) * Real.log (kk g : ℝ))
          + c * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ))
          + (c * Real.log (N / c) + c) := by gcongr
    _ ≤ ((∑ w ∈ phrases, - Real.log (Pm (st w) w.length (toFinVec w.length w)))
          + c * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ))
          + (c * Real.log (N / c) + c) := by gcongr
    _ = (∑ w ∈ phrases, - Real.log (Pm (st w) w.length (toFinVec w.length w)))
          + (c * Real.log (N / c) + c
            + c * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ)) := by ring

end InformationTheory.Shannon
