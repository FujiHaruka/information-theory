import Common2026.Shannon.LZ78ZivEntropyBridge
import Common2026.Shannon.EntropyRate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Stationary-process telescoping layer (LZ78 blockRV refactor, Phase K)

This file derives the genuine **algebraic telescoping** backbone of the LZ78
per-path parsing factorization `Pₙ{block ω} = ∏ⱼ condPhraseProb …`
(`IsLZ78PerPathParsingFactorization`, `LZ78ZivEntropyBridge.lean`).

`condPhraseProb μ p n ω j` is *defined* as the ratio of successive
parsing-prefix block probabilities
`prefixBlockProb ω (boundary (j+1)) / prefixBlockProb ω (boundary j)`. Over
the phrase positions `j ∈ range c` this product **telescopes** to
`prefixBlockProb ω (boundary c) / prefixBlockProb ω (boundary 0)`
(`Finset.prod_range_div`). Since `boundary 0 = 0` and the length-`0` block
has probability `1`, the denominator is `1`, leaving
`prefixBlockProb ω (boundary c)`.

The remaining content that connects this to `Pₙ{block ω}` is the
**parse-completeness** fact `boundary c = n` (the parse consumes all `n`
symbols) — together with the **positivity** of each ratio. These are the
genuinely process-dependent inputs of the factorization; the telescoping
algebra itself is unconditional and lives here.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `parsingBoundary μ p n ω 0 = 0`: the empty parsing prefix consumes no
symbols. -/
theorem parsingBoundary_zero
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    parsingBoundary μ p n ω 0 = 0 := by
  simp [parsingBoundary]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **`prefixBlockProb` of the empty prefix is `1`**: `Pₘ{block_m ω}` at
`m = 0` is the probability of the unique length-`0` block, which is `1`. -/
theorem prefixBlockProb_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (ω : Ω) :
    prefixBlockProb μ p ω 0 = 1 := by
  unfold prefixBlockProb
  have _ : IsProbabilityMeasure (μ.map (p.blockRV 0)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV 0).aemeasurable
  have h_default : ∀ x : (Fin 0 → α), x = default := fun x => by
    funext i; exact i.elim0
  have h_singleton_eq_univ :
      ({(p.blockRV 0 ω : Fin 0 → α)} : Set (Fin 0 → α)) = Set.univ := by
    ext x; simp [h_default x, h_default (p.blockRV 0 ω)]
  rw [h_singleton_eq_univ]
  simp [measureReal_def, measure_univ]

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Genuine telescoping**: the product of the per-phrase conditional
probabilities over `range c` telescopes to
`prefixBlockProb ω (boundary c)`, using `boundary 0 = 0` and
`prefixBlockProb ω 0 = 1`.

Proved by induction on `c` (a `ℝ` field telescoping, where the `prod_range_div`
group lemma does not apply): each step cancels the denominator ratio against
the previous prefix probability, which is nonzero by `hpos`. -/
theorem prod_condPhraseProb_telescope
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω) (c : ℕ)
    (hpos : ∀ j ≤ c, prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0) :
    ∏ j ∈ Finset.range c, condPhraseProb μ p n ω j
      = prefixBlockProb μ p ω (parsingBoundary μ p n ω c) := by
  induction c with
  | zero =>
      simp [parsingBoundary_zero, prefixBlockProb_zero]
  | succ k ih =>
      have hk : ∀ j ≤ k, prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0 :=
        fun j hj => hpos j (Nat.le_succ_of_le hj)
      rw [Finset.prod_range_succ, ih hk]
      -- `prefix(b k) * (prefix(b (k+1)) / prefix(b k)) = prefix(b (k+1))`.
      unfold condPhraseProb
      rw [mul_div_cancel₀ _ (hpos k (Nat.le_succ k))]

/-! ## Reduction of the factorization to parse-completeness + positivity

The telescoping above reduces the `factor` field of
`IsLZ78PerPathParsingFactorization` to two genuinely process-dependent
facts about the LZ78 parse: positivity of the intermediate prefix block
probabilities, and **parse-completeness** `boundary c = n` (the parse
consumes all `n` symbols). The latter is the load-bearing residual: the
genuine longest-prefix greedy parse `lz78PhraseStrings` leaves an
*unfinished tail* (`lz78PhraseStrings_total_length_le` is `≤`, not `=`), so
`boundary c = n` is **not** unconditionally true for the present parse — it
is the Cover–Thomas "last partial phrase" content. -/

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Factorization from parse-completeness + positivity**: if, for the
observed block, the parse consumes all `n` symbols (`boundary c = n`, where
`c` is the phrase count) and every intermediate prefix block probability is
nonzero, then the block probability factorizes as the product of per-phrase
conditional probabilities — exactly the `factor` field of
`IsLZ78PerPathParsingFactorization`.

The telescoping is genuine (`prod_condPhraseProb_telescope`); the two
hypotheses are the honest, strictly-localized residual content of the
factorization (positivity is regularity; parse-completeness is the genuine
Cover–Thomas last-phrase fact). -/
theorem factor_of_complete_of_pos
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω)
    (hcomplete :
      parsingBoundary μ p n ω (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length = n)
    (hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
      prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0) :
    (μ.map (p.blockRV n)).real {p.blockRV n ω}
      = ∏ j ∈ Finset.range
            (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
          condPhraseProb μ p n ω j := by
  rw [prod_condPhraseProb_telescope μ p n ω _ hpos, hcomplete]
  rfl

end InformationTheory.Shannon
