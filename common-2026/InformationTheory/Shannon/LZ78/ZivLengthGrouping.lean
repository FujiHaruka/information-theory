import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.GreedyLongestPrefix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# LZ78 length-grouping Jensen inequality

This file supplies the abstract grouping inequality at the heart of the
length-grouping route for the LZ78 achievability wall
`ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean`,
slug `lz78-aseventual-ziv`).

## Approach

The gateway atom is a pure `Finset`/`Real` statement, free of any
measure-theoretic or LZ78 content: grouping `c = ∑ k i` distinct items into
`D = G.card` groups and applying Jensen's inequality to the convex function
`x ↦ x · log x` yields

```
c · log c ≤ ∑ i, k i · log (k i) + c · log D.
```

Mathematically this is `ConvexOn.map_sum_le` for `Real.convexOn_mul_log`
with uniform weights `wᵢ = 1/D` at points `pᵢ = k i`:
`f (c/D) ≤ (1/D) ∑ f (k i)`, i.e. `c · log (c/D) ≤ ∑ k i · log (k i)` after
multiplying by `D`, then `log (c/D) = log c − log D` rearranges to the goal.
The degenerate `c = 0` case (all `k i = 0`) is handled directly.
-/

namespace InformationTheory.Shannon

open scoped BigOperators

/-- The abstract length-grouping Jensen inequality (gateway atom for the LZ78
length-grouping route). For a nonempty finite index set `G` and weights
`k : ι → ℕ`, writing `c = ∑ i ∈ G, k i` and `D = G.card`,

```
c · log c ≤ ∑ i ∈ G, k i · log (k i) + c · log D.
```

This is Jensen's inequality for the convex function `x ↦ x · log x` with
uniform weights `1/D` at points `k i`. -/
theorem card_mul_log_le_sum_group_mul_log_add_card_log
    {ι : Type*} (G : Finset ι) (k : ι → ℕ) (hG : G.Nonempty) :
    ((∑ i ∈ G, k i : ℕ) : ℝ) * Real.log ((∑ i ∈ G, k i : ℕ) : ℝ)
      ≤ (∑ i ∈ G, (k i : ℝ) * Real.log (k i : ℝ))
        + ((∑ i ∈ G, k i : ℕ) : ℝ) * Real.log (G.card : ℝ) := by
  -- Real-valued abbreviations.
  set c : ℝ := ((∑ i ∈ G, k i : ℕ) : ℝ) with hc
  set D : ℝ := (G.card : ℝ) with hD
  -- `D ≥ 1` from nonemptiness, hence `D > 0` and `D ≠ 0`.
  have hDcard_pos : 0 < G.card := Finset.card_pos.mpr hG
  have hD_pos : (0 : ℝ) < D := by rw [hD]; exact_mod_cast hDcard_pos
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  -- `c ≥ 0` as a cast of a `ℕ` sum.
  have hc_nonneg : 0 ≤ c := by rw [hc]; positivity
  -- The real-valued group sum equals `c`.
  have hsum_real : (∑ i ∈ G, (k i : ℝ)) = c := by
    rw [hc]; push_cast; rfl
  rcases eq_or_lt_of_le hc_nonneg with hc0 | hc_pos
  · -- Degenerate case `c = 0`: every `k i = 0`, so all three terms vanish.
    rw [← hc0]
    -- `c = 0`, so `c * log c = 0` and `c * log D = 0`.
    have hsum0 : (∑ i ∈ G, (k i : ℝ) * Real.log (k i : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      -- From `∑ k i = 0` (nats) we get each `k i = 0`.
      have hki : k i = 0 := by
        have hsumnat : (∑ i ∈ G, k i) = 0 := by
          have h := hc0.symm
          rw [hc] at h
          exact_mod_cast h
        exact (Finset.sum_eq_zero_iff.mp hsumnat) i hi
      simp [hki]
    rw [hsum0]
    simp
  · -- Main case `c > 0`. Apply Jensen to `x ↦ x · log x`.
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    -- Jensen with uniform weights `1/D` at points `k i`.
    have hjensen :
        (fun x ↦ x * Real.log x) (∑ i ∈ G, (1 / D) • (k i : ℝ))
          ≤ ∑ i ∈ G, (1 / D) • ((fun x ↦ x * Real.log x) (k i : ℝ)) := by
      refine Real.convexOn_mul_log.map_sum_le ?_ ?_ ?_
      · intro i _; positivity
      · -- `∑ i ∈ G, 1/D = G.card • (1/D) = D * (1/D) = 1`.
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [← hD]
        field_simp
      · intro i _
        exact Set.mem_Ici.mpr (by positivity)
    -- Simplify both sides of the Jensen inequality.
    -- LHS argument: `∑ (1/D) • k i = (1/D) * ∑ k i = c/D`.
    have hlhs_arg : (∑ i ∈ G, (1 / D) • (k i : ℝ)) = c / D := by
      simp only [smul_eq_mul]
      rw [← Finset.mul_sum, hsum_real]
      ring
    -- RHS: `∑ (1/D) • (k i · log (k i)) = (1/D) * ∑ (k i · log (k i))`.
    have hrhs : (∑ i ∈ G, (1 / D) • ((k i : ℝ) * Real.log (k i : ℝ)))
        = (1 / D) * (∑ i ∈ G, (k i : ℝ) * Real.log (k i : ℝ)) := by
      simp only [smul_eq_mul]
      rw [← Finset.mul_sum]
    rw [hlhs_arg, hrhs] at hjensen
    -- `hjensen : (c/D) * log (c/D) ≤ (1/D) * ∑ (k i) log (k i)`.
    -- Multiply both sides by `D > 0`.
    have hmul : c * Real.log (c / D)
        ≤ ∑ i ∈ G, (k i : ℝ) * Real.log (k i : ℝ) := by
      have := mul_le_mul_of_nonneg_left hjensen (le_of_lt hD_pos)
      -- `D * ((c/D) * log(c/D)) = c * log(c/D)` and `D * ((1/D) * S) = S`.
      rw [show D * (c / D * Real.log (c / D)) = c * Real.log (c / D) by
        field_simp] at this
      rw [show D * (1 / D * (∑ i ∈ G, (k i : ℝ) * Real.log (k i : ℝ)))
        = ∑ i ∈ G, (k i : ℝ) * Real.log (k i : ℝ) by field_simp] at this
      exact this
    -- `log (c/D) = log c - log D`.
    rw [Real.log_div hc_ne hD_ne] at hmul
    -- `c * (log c - log D) ≤ S`  ⟹  `c * log c ≤ S + c * log D`.
    nlinarith [hmul]

/-! ## Length-grouped instantiation for `lz78PhraseStrings` -/

section LengthGrouping

variable {α : Type*} [DecidableEq α]

/-- The length-grouped entropy bound for the LZ78 phrase set, obtained by instantiating
the abstract Jensen grouping inequality at the distinct LZ78 phrases, fibered
by `List.length`. With `c = #phrases`, `c_ℓ = #{phrase | length = ℓ}` and
`D = #{distinct lengths}`,

```
c · log c ≤ ∑_ℓ c_ℓ · log c_ℓ + c · log D.
```

The phrase set is `Nodup` (`lz78PhraseStrings_nodup`), so its `toFinset`
cardinality equals its length, and `card_eq_sum_card_image` over
`List.length` distributes `c` across the length fibers. -/
theorem lz78PhraseStrings_card_mul_log_le_sum_length_group
    (input : List α) :
    let phrases := (lz78PhraseStrings input).toFinset
    ((lz78PhraseStrings input).length : ℝ)
        * Real.log ((lz78PhraseStrings input).length : ℝ)
      ≤ (∑ ℓ ∈ phrases.image List.length,
            ((phrases.filter (fun w ↦ w.length = ℓ)).card : ℝ)
              * Real.log ((phrases.filter (fun w ↦ w.length = ℓ)).card : ℝ))
        + ((lz78PhraseStrings input).length : ℝ)
            * Real.log ((phrases.image List.length).card : ℝ) := by
  intro phrases
  -- The phrase list is `Nodup`, so `#phrases = (lz78PhraseStrings input).length`.
  have hnodup : (lz78PhraseStrings input).Nodup := lz78PhraseStrings_nodup input
  have hcard_eq : phrases.card = (lz78PhraseStrings input).length :=
    List.toFinset_card_of_nodup hnodup
  -- Index set `G` = distinct lengths, weights `k ℓ` = count of phrases of length `ℓ`.
  set G : Finset ℕ := phrases.image List.length with hG
  set k : ℕ → ℕ := fun ℓ ↦ (phrases.filter (fun w ↦ w.length = ℓ)).card with hk
  -- The length fibers partition `phrases`: `∑ ℓ ∈ G, k ℓ = #phrases`.
  have hfiber : (∑ ℓ ∈ G, k ℓ) = phrases.card := by
    rw [hG, hk]
    exact (Finset.card_eq_sum_card_image List.length phrases).symm
  -- Hence `∑ ℓ ∈ G, k ℓ = (lz78PhraseStrings input).length`.
  have hfiber_len : (∑ ℓ ∈ G, k ℓ) = (lz78PhraseStrings input).length := by
    rw [hfiber, hcard_eq]
  rcases Finset.eq_empty_or_nonempty G with hGempty | hGne
  · -- Empty length set ⇒ no phrases ⇒ `c = 0`, both sides vanish.
    have hlen0 : (lz78PhraseStrings input).length = 0 := by
      have : (∑ ℓ ∈ G, k ℓ) = 0 := by rw [hGempty]; simp
      rw [hfiber_len] at this
      exact this
    rw [hGempty]
    simp [hlen0]
  · -- Nonempty: apply the abstract Jensen grouping inequality.
    have hmain := card_mul_log_le_sum_group_mul_log_add_card_log G k hGne
    -- Rewrite `∑ ℓ ∈ G, k ℓ` (a `ℕ`) to `(lz78PhraseStrings input).length`.
    rw [hfiber_len] at hmain
    -- `hmain` now matches the goal after unfolding `G` and `k`.
    exact hmain

end LengthGrouping

end InformationTheory.Shannon
