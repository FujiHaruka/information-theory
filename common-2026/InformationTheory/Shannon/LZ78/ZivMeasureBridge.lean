import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.ZivLengthGrouping
import InformationTheory.Shannon.LZ78.ZivEntropyBridge
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# LZ78 length-grouping measure bridge — per-length sub-distribution + log-sum

This file supplies the **measure-theoretic + log-sum** layer of the
length-grouping route for the LZ78 achievability wall
`ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`,
`@residual(wall:lz78-aseventual-ziv)`).

## Approach

Leg 4 (`ZivLengthGrouping.lean`) produced the abstract grouping inequality

```
c · log c ≤ ∑_ℓ c_ℓ · log c_ℓ + c · log D
```

(`lz78PhraseStrings_card_mul_log_le_sum_length_group`), fibering the distinct
LZ78 phrases by `List.length` (`c` = #phrases, `c_ℓ` = #{phrases of length
`ℓ`}, `D` = #distinct lengths). This file converts the inner `c_ℓ · log c_ℓ`
terms into negative-log marginal probabilities and aggregates:

1. **Per-length sub-distribution** (`sum_marginal_real_le_one`): for the
   length-`ℓ` marginal `P_ℓ(Z) = (μ.map (blockRV ℓ)).real {Z}` and a finite
   set `S` of distinct strings `Z : Fin ℓ → α`, `∑_{Z ∈ S} P_ℓ(Z) ≤ 1`. This
   is a pure probability fact: distinct singletons are disjoint, so the sum
   is the measure of the finset, bounded by the measure of the whole space.

2. **Per-length log-sum step** (`group_card_mul_log_le_sum_neg_log`): applying
   `log_sum_inequality` (`ZivEntropyBridge.lean`) with `aᵢ ≡ 1`, `bᵢ = P_ℓ(Zᵢ)`
   over a group `S` of `card S` distinct strings with `∑ P ≤ 1` and `P > 0`
   gives `card S · log (card S) ≤ ∑_{Z ∈ S} -log P_ℓ(Z)`.

3. **Aggregation** (`lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead`):
   combine leg 4's grouping inequality with step 2 applied per length group,
   instantiating `P_ℓ` at the actual phrase marginals via the injection
   `w ↦ (w[·]) : List α → (Fin ℓ → α)` (injective on length-`ℓ` lists), giving

   ```
   c · log c ≤ ∑_{phrases w} -log P_{|w|}(w) + c · log D.
   ```

The remaining crux — connecting the marginal sum `∑_w -log P_{|w|}(w)` to the
joint `-log Pₙ = n · blockLogAvg` with an `o(n)` slack — is a genuine wall
(`ziv_aseventual_le_blockLogAvg₂`) and is NOT discharged here; see the GATEWAY
section at the end for the precise obstruction.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-! ## Step 1 — per-length sub-distribution -/

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- **Per-length sub-distribution bound**: for the length-`ℓ` marginal
`P_ℓ(Z) = (μ.map (blockRV ℓ)).real {Z}` and any finite set `S` of distinct
strings `Z : Fin ℓ → α`, the marginal masses sum to at most `1`.

Pure probability fact: distinct singletons are pairwise disjoint, so the sum
equals the marginal measure of `S` (`sum_measureReal_singleton`), bounded by
the total mass `1` of the pushed-forward probability measure
(`measureReal_le_one`). -/
theorem sum_marginal_real_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (ℓ : ℕ) (S : Finset (Fin ℓ → α)) :
    (∑ Z ∈ S, (μ.map (p.blockRV ℓ)).real {Z}) ≤ 1 := by
  -- The pushforward marginal is a probability measure.
  have hprob : IsProbabilityMeasure (μ.map (p.blockRV ℓ)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV ℓ).aemeasurable
  -- The sum of singleton masses equals the measure of the finset.
  rw [sum_measureReal_singleton]
  -- bounded by the total mass `1` of a probability measure.
  exact measureReal_le_one

/-! ## Step 2 — per-length log-sum step -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [MeasurableSpace Ω] in
/-- **Per-length log-sum step**: for a finite group `S` of distinct strings
`Z : Fin ℓ → α` with strictly positive marginals `P_ℓ(Z) > 0` whose masses
sum to at most `1`,

```
card S · log (card S) ≤ ∑_{Z ∈ S} -log P_ℓ(Z).
```

`log_sum_inequality` with `aᵢ ≡ 1`, `bᵢ = P_ℓ(Zᵢ)`: the LHS becomes
`card S · log (card S / ∑ P)` and `∑ P ≤ 1` makes the `-log (∑ P) ≥ 0`
correction only help. -/
theorem group_card_mul_log_le_sum_neg_log
    {ℓ : ℕ} (S : Finset (Fin ℓ → α)) (P : (Fin ℓ → α) → ℝ)
    (hPpos : ∀ Z ∈ S, 0 < P Z) (hPsum : (∑ Z ∈ S, P Z) ≤ 1) :
    (S.card : ℝ) * Real.log (S.card : ℝ)
      ≤ ∑ Z ∈ S, - Real.log (P Z) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp
  -- `∑ P > 0` from positivity on a nonempty index set.
  have hsumP_pos : 0 < ∑ Z ∈ S, P Z := Finset.sum_pos hPpos hS
  -- log-sum inequality with `a ≡ 1`, `b = P`.
  have hlog := log_sum_inequality S (fun _ => (1 : ℝ)) P
    (fun _ _ => zero_le_one) hPpos
  -- LHS sum of `a`: `∑ 1 = card S`.
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hlog
  -- RHS terms: `1 · log(1/P Z) = -log (P Z)`.
  have hrhs : (∑ Z ∈ S, (1 : ℝ) * Real.log (1 / P Z))
      = ∑ Z ∈ S, - Real.log (P Z) := by
    refine Finset.sum_congr rfl (fun Z hZ => ?_)
    rw [one_mul, Real.log_div one_ne_zero (hPpos Z hZ).ne', Real.log_one, zero_sub]
  rw [hrhs] at hlog
  -- `hlog : card S · log (card S / ∑ P) ≤ ∑ -log P`.
  refine le_trans ?_ hlog
  -- `card S · log (card S) ≤ card S · log (card S / ∑ P)` since `∑ P ≤ 1`.
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.log_le_log hcard_pos
  -- `card S ≤ card S / ∑ P` since `0 < ∑ P ≤ 1`.
  rw [le_div_iff₀ hsumP_pos]
  calc (S.card : ℝ) * (∑ Z ∈ S, P Z)
      ≤ (S.card : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left hPsum (Nat.cast_nonneg _)
    _ = (S.card : ℝ) := mul_one _

/-! ## Step 3 — aggregation over phrases -/

/-- **List-to-vector conversion**: read the first `ℓ` entries of a list into a
`Fin ℓ → α` function, defaulting past the end. Injective on length-`ℓ`
lists. -/
noncomputable def toFinVec (ℓ : ℕ) (w : List α) : Fin ℓ → α :=
  fun i => (w[(i : ℕ)]?).getD (Classical.arbitrary α)

omit [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace Ω] in
theorem toFinVec_injOn (ℓ : ℕ) :
    Set.InjOn (toFinVec ℓ) {w : List α | w.length = ℓ} := by
  intro w hw v hv heq
  have hwlen : w.length = ℓ := hw
  have hvlen : v.length = ℓ := hv
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ℓ
  · -- Within the window: the tuple equality at index `i` gives `w[i] = v[i]`.
    have hiw : i < w.length := by omega
    have hiv : i < v.length := by omega
    have hfun := congrFun heq ⟨i, hi⟩
    simp only [toFinVec, List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hiv,
      Option.getD_some] at hfun
    rw [List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hiv, hfun]
  · -- Past the window: both lists are too short, so both `none`.
    have hi' : ℓ ≤ i := not_lt.mp hi
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

omit [Fintype α] in
/-- **Length-grouped marginal entropy bound for the LZ78 phrase set**.

Instantiating the abstract grouping inequality (leg 4) at the actual
length-`ℓ` marginals, with `c = #phrases`, `D = #distinct lengths`:

```
c · log c ≤ ∑_{phrases w} -log P_{|w|}(w) + c · log D,
```

where `P_{|w|}(w) = (μ.map (blockRV |w|)).real {toFinVec |w| w}` is the marginal
mass of the cylinder of the string `w` (read as a `Fin |w| → α` vector). The
positivity `P_{|w|}(w) > 0` over the (a.s.) observed phrases is a regularity
precondition.

The sub-distribution hypothesis is discharged genuinely from step 1
(`sum_marginal_real_le_one`) via the length-fiber injection `toFinVec`; the
positivity is the only precondition. -/
theorem lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (input : List α)
    (hpos : ∀ w ∈ (lz78PhraseStrings input).toFinset,
      0 < (μ.map (p.blockRV w.length)).real {toFinVec w.length w}) :
    let phrases := (lz78PhraseStrings input).toFinset
    ((lz78PhraseStrings input).length : ℝ)
        * Real.log ((lz78PhraseStrings input).length : ℝ)
      ≤ (∑ w ∈ phrases,
            - Real.log ((μ.map (p.blockRV w.length)).real {toFinVec w.length w}))
        + ((lz78PhraseStrings input).length : ℝ)
            * Real.log ((phrases.image List.length).card : ℝ) := by
  intro phrases
  classical
  set G : Finset ℕ := phrases.image List.length with hGdef
  -- Per-length count and abbreviated marginal.
  set Pm : ∀ ℓ, (Fin ℓ → α) → ℝ :=
    fun ℓ Z => (μ.map (p.blockRV ℓ)).real {Z} with hPm
  -- Step 2 applied per length group ℓ, summed over G:
  -- `∑_ℓ c_ℓ·log c_ℓ ≤ ∑_ℓ ∑_{w in group ℓ} -log P_{|w|}(w)`.
  have hgroup :
      (∑ ℓ ∈ G, ((phrases.filter (fun w => w.length = ℓ)).card : ℝ)
          * Real.log ((phrases.filter (fun w => w.length = ℓ)).card : ℝ))
      ≤ ∑ ℓ ∈ G, ∑ w ∈ phrases.filter (fun w => w.length = ℓ),
            - Real.log (Pm w.length (toFinVec w.length w)) := by
    refine Finset.sum_le_sum (fun ℓ _ => ?_)
    -- The length-`ℓ` fiber, all of length exactly `ℓ`.
    set grp : Finset (List α) := phrases.filter (fun w => w.length = ℓ) with hgrp
    have hgrp_len : ∀ w ∈ grp, w.length = ℓ := by
      intro w hw; exact (Finset.mem_filter.mp hw).2
    -- `toFinVec ℓ` is injective on `grp` (all elements have length `ℓ`).
    have hinj : Set.InjOn (toFinVec ℓ) (grp : Set (List α)) := by
      intro w hw v hv hwv
      exact toFinVec_injOn ℓ (hgrp_len w hw) (hgrp_len v hv) hwv
    -- The image of `grp` under `toFinVec ℓ` in `Fin ℓ → α`.
    set S : Finset (Fin ℓ → α) := grp.image (toFinVec ℓ) with hSdef
    -- Cardinality is preserved by the injection.
    have hScard : S.card = grp.card := by
      rw [hSdef, Finset.card_image_of_injOn hinj]
    -- Positivity of the marginal on each image point.
    have hSpos : ∀ Z ∈ S, 0 < Pm ℓ Z := by
      intro Z hZ
      rw [hSdef, Finset.mem_image] at hZ
      obtain ⟨w, hw, rfl⟩ := hZ
      have hwlen : w.length = ℓ := hgrp_len w hw
      have hwmem : w ∈ phrases := (Finset.mem_filter.mp hw).1
      have hp := hpos w hwmem
      rw [hwlen] at hp
      simpa only [hPm] using hp
    -- Sub-distribution bound from step 1.
    have hSsum : (∑ Z ∈ S, Pm ℓ Z) ≤ 1 := sum_marginal_real_le_one μ p ℓ S
    -- Step 2 on `S`.
    have hlogsum := group_card_mul_log_le_sum_neg_log S (Pm ℓ) hSpos hSsum
    rw [hScard] at hlogsum
    -- Transfer the RHS sum from `S` back to `grp` via the injection.
    have hrhs_eq : (∑ Z ∈ S, - Real.log (Pm ℓ Z))
        = ∑ w ∈ grp, - Real.log (Pm w.length (toFinVec w.length w)) := by
      rw [hSdef, Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [hgrp_len w hw]
    rw [hrhs_eq] at hlogsum
    exact hlogsum
  -- Reassemble the length fibers into a single sum over all phrases.
  have hfiber :
      (∑ ℓ ∈ G, ∑ w ∈ phrases.filter (fun w => w.length = ℓ),
          - Real.log (Pm w.length (toFinVec w.length w)))
      = ∑ w ∈ phrases, - Real.log (Pm w.length (toFinVec w.length w)) := by
    rw [hGdef]
    exact Finset.sum_fiberwise_of_maps_to (fun w hw =>
      Finset.mem_image_of_mem List.length hw) _
  -- Combine leg 4's grouping inequality with the per-group log-sum bound.
  have hleg4 := lz78PhraseStrings_card_mul_log_le_sum_length_group (α := α) input
  simp only at hleg4
  calc ((lz78PhraseStrings input).length : ℝ)
          * Real.log ((lz78PhraseStrings input).length : ℝ)
      ≤ (∑ ℓ ∈ G, ((phrases.filter (fun w => w.length = ℓ)).card : ℝ)
            * Real.log ((phrases.filter (fun w => w.length = ℓ)).card : ℝ))
          + ((lz78PhraseStrings input).length : ℝ)
              * Real.log (G.card : ℝ) := hleg4
    _ ≤ (∑ ℓ ∈ G, ∑ w ∈ phrases.filter (fun w => w.length = ℓ),
              - Real.log (Pm w.length (toFinVec w.length w)))
          + ((lz78PhraseStrings input).length : ℝ)
              * Real.log (G.card : ℝ) := by
        gcongr
    _ = (∑ w ∈ phrases,
              - Real.log (Pm w.length (toFinVec w.length w)))
          + ((lz78PhraseStrings input).length : ℝ)
              * Real.log (G.card : ℝ) := by rw [hfiber]

end InformationTheory.Shannon
