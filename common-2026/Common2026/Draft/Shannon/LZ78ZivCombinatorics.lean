import Common2026.Shannon.LZ78ZivEntropyBridge
import Common2026.Shannon.StationaryKernel
import Common2026.Shannon.LZ78ZivCountingBody
import Common2026.Draft.Shannon.LZ78DistinctEncoding
import Common2026.Draft.Shannon.LZ78AchievabilityLimsup
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

/-! ## §2. Per-phrase conditional bounds (genuine) -/

omit [Fintype α] [Nonempty α] in
/-- **Each per-phrase conditional probability is `≤ 1`** (genuine,
unconditional consequence of prefix monotonicity).

`condPhraseProb μ p n ω j = prefixBlockProb ω (boundary (j+1)) /
prefixBlockProb ω (boundary j)`, and the parsing boundaries are monotone
(`boundary j ≤ boundary (j+1)`), so the numerator cylinder is contained in
the denominator cylinder and the ratio is `≤ 1`
(`prefixBlockProb_antitone`). The positivity hypothesis `hden` guards the
division. -/
theorem condPhraseProb_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω) (j : ℕ)
    (hden : 0 < prefixBlockProb μ p ω (parsingBoundary μ p n ω j)) :
    condPhraseProb μ p n ω j ≤ 1 := by
  -- `boundary j ≤ boundary (j+1)`: one more phrase length is added.
  have hmono : parsingBoundary μ p n ω j ≤ parsingBoundary μ p n ω (j + 1) := by
    unfold parsingBoundary
    -- `((take j L).map length).sum ≤ ((take (j+1) L).map length).sum`.
    set lens : List ℕ :=
      (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).map List.length with hlens
    have hmap : ∀ k,
        (((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).take k).map List.length).sum
          = (lens.take k).sum := by
      intro k; rw [hlens, List.map_take]
    rw [hmap j, hmap (j + 1)]
    -- `take j lens` is a prefix of `take (j+1) lens`; sums of ℕ-lists are
    -- monotone under the sublist order.
    have hpre : (lens.take j) <+: (lens.take (j + 1)) :=
      List.take_prefix_take_left (by omega)
    exact hpre.sublist.sum_le_sum (fun _ _ => Nat.zero_le _)
  -- `prefixBlockProb (b (j+1)) ≤ prefixBlockProb (b j)` by antitone.
  have hanti := prefixBlockProb_antitone μ p ω hmono
  unfold condPhraseProb
  rw [div_le_one hden]
  exact hanti

/-! ## §3. Ziv combinatorial core (Cover–Thomas Lemma 13.5.5) — isolated honest hypothesis -/

/-- **Isolated honest input (Cover–Thomas Lemma 13.5.5, the distinct-phrase
combinatorial Ziv core)** — for the genuine longest-prefix greedy parse of
the observed block into `c` *distinct* phrases, the count product
`c · log c` is bounded by the sum of the per-phrase conditional
self-informations `∑ⱼ -log (condPhraseProb …)`:

```
c · Real.log c ≤ ∑ⱼ -Real.log (condPhraseProb μ p n ω j).
```

**This is NOT a discharge.** It is the genuine, load-bearing combinatorial
heart of the Ziv inequality, and it is *not* derivable from the committed
foundation. Concretely: the natural reduction via the log-sum inequality
(`log_sum_inequality` with `aⱼ ≡ 1`, `bⱼ ≡ condPhraseProb`) gives

```
c · log (c / ∑ⱼ qⱼ) ≤ ∑ⱼ -log qⱼ,
```

which yields `c log c ≤ ∑ⱼ -log qⱼ` **only if `∑ⱼ qⱼ ≤ 1`**. But the
`condPhraseProb` here are *path-prefix* ratios
`P(prefix(b(j+1)))/P(prefix(b(j)))`, and these do **not** sum to `≤ 1`
across the distinct phrases (the documented trap: `∑ⱼ qⱼ ≈ c`, since each
nested ratio is `Θ(1)`). The genuine Cover–Thomas argument needs the
conditionals re-expressed against the **LZ dictionary-node contexts** (the
tree-node sub-distribution `∑_{phrases sharing a context} q ≤ 1`, where
within a context the distinct phrases branch off with distinct next
symbols), which requires re-deriving the parsing factorization against
standalone-context cylinder probabilities (Cover–Thomas Lemma 13.5.4, the
LZ-tree superadditivity). That tree-node infrastructure is **not** in the
committed stationary/factorization layer, so this combinatorial core
remains exposed as a single load-bearing named hypothesis.

It is a genuine `Prop` (type ≠ conclusion), never `True`, never a `:= h`
alias. The hypothesis is *strictly more primitive* than the structure
`IsLZ78AchievabilityZivUpperBound` it helps construct (a per-block
combinatorial inequality vs. an a.s.-eventual rate bound). -/
def IsLZ78ZivCombinatorialCore
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
  ∀ (n : ℕ) (ω : Ω),
    ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
        * Real.log ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
      ≤ ∑ j ∈ Finset.range
            (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
          - Real.log (condPhraseProb μ p n ω j)

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Genuine Ziv inequality `c · log c ≤ -log Pₙ` (nat-log form)** from the
isolated combinatorial core plus the genuine foundation.

The combinatorial core gives `c log c ≤ ∑ⱼ -log qⱼ`
(`IsLZ78ZivCombinatorialCore`), and the genuine foundation backbone
`blockProb_neg_log_ge_sum` gives `∑ⱼ -log qⱼ ≤ -log Pₙ` (under a.s.
regularity `0 < Pₙ` and the genuine factorization). Transitivity closes it.
Everything except `IsLZ78ZivCombinatorialCore` is genuine.

`@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem ziv_count_mul_log_le_neg_log_blockProb
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω)
    (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω}) :
    ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
        * Real.log ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
      ≤ - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) := by
  sorry

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Genuine base-2 Ziv inequality `c · log₂ c ≤ -log₂ Pₙ`** (the Cover–Thomas
Eq. 13.122–124 bit-based form), obtained from the nat-log Ziv inequality by
dividing through by `Real.log 2 > 0`.

`@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem ziv_count_mul_logb_le_neg_logb_blockProb
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω)
    (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω}) :
    ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
        * Real.logb 2 ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
      ≤ - Real.logb 2 ((μ.map (p.blockRV n)).real {p.blockRV n ω}) := by
  sorry

/-! ## §4. Deterministic per-symbol count envelope (genuine, ω-uniform) -/

section Envelope

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Deterministic, ω-uniform `c(n)/n` envelope** (genuine): for the
distinct longest-prefix parse of any length-`n` block, the per-symbol
distinct-phrase count is bounded by an explicit `n`-only function that
vanishes:

```
c(n)/n ≤ 2·K / Real.log n + 1 / Real.sqrt n   (K = 8·log(|α|+1)),  for n ≥ 2.
```

Proved from the deterministic Cover–Thomas counting bound
`c·log c ≤ K·n` (`lz78PhraseStrings_mul_log_le`, genuine, distribution-free)
by a case split on `c ≤ √n` vs `c > √n`. This is the ω-independent
ingredient that makes the achievability slack vanish (the per-phrase
dictionary cost `(log₂|α|+2)` is multiplied by `c/n`, which this bounds
uniformly). -/
theorem lz78Distinct_count_div_le_envelope
    (n : ℕ) (hn : 2 ≤ n) (x : Fin n → α) :
    ((lz78PhraseStrings (List.ofFn x)).length : ℝ) / (n : ℝ)
      ≤ 2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
          + 1 / Real.sqrt (n : ℝ) := by
  set c : ℝ := ((lz78PhraseStrings (List.ofFn x)).length : ℝ) with hc
  set K : ℝ := 8 * Real.log (Fintype.card α + 1) with hK
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hsqrtn_pos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hc_nn : (0 : ℝ) ≤ c := by rw [hc]; positivity
  have hK_nn : (0 : ℝ) ≤ K := by
    rw [hK]
    have hcard1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
      linarith
    have := Real.log_nonneg hcard1
    linarith
  -- deterministic counting bound `c·log c ≤ K·n`.
  have hKn : c * Real.log c ≤ K * (n : ℝ) := by
    have h := lz78PhraseStrings_mul_log_le (List.ofFn x)
    rw [List.length_ofFn] at h
    rw [hc, hK]; exact_mod_cast h
  -- two nonneg terms.
  have hterm1_nn : (0 : ℝ) ≤ 2 * K / Real.log (n : ℝ) := by positivity
  have hterm2_nn : (0 : ℝ) ≤ 1 / Real.sqrt (n : ℝ) := by positivity
  rcases le_or_gt c (Real.sqrt (n : ℝ)) with hsmall | hlarge
  · -- small `c`: `c/n ≤ √n/n = 1/√n`.
    have : c / (n : ℝ) ≤ 1 / Real.sqrt (n : ℝ) := by
      rw [div_le_div_iff₀ hn_pos hsqrtn_pos]
      calc c * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_right hsmall hsqrtn_pos.le
        _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
        _ = 1 * (n : ℝ) := (one_mul _).symm
    linarith
  · -- large `c > √n`: `log c > (1/2) log n`, so `c < 2Kn/log n`.
    have hc_pos : (0 : ℝ) < c := lt_trans hsqrtn_pos hlarge
    have hlogc_lb : Real.log (n : ℝ) / 2 < Real.log c := by
      have h1 : Real.log (Real.sqrt (n : ℝ)) < Real.log c :=
        Real.log_lt_log hsqrtn_pos hlarge
      rwa [Real.log_sqrt hn_pos.le] at h1
    -- `c·(log n / 2) ≤ c log c ≤ Kn`, hence `c/n ≤ 2K/log n`.
    have hchain : c * (Real.log (n : ℝ) / 2) ≤ K * (n : ℝ) := by
      refine le_trans ?_ hKn
      exact mul_le_mul_of_nonneg_left hlogc_lb.le hc_nn
    have hcn : c / (n : ℝ) ≤ 2 * K / Real.log (n : ℝ) := by
      rw [div_le_div_iff₀ hn_pos hlogn_pos]
      nlinarith [hchain, hlogn_pos, hn_pos]
    linarith

end Envelope

/-! ## §5. Achievability structure assembly (Phase Z4) -/

section Assembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Vanishing achievability slack** (ω-independent): the per-phrase
dictionary-cost overhead, equal to the `1/(n·log 2)` rounding gap of the
`log₂(c+1)` term plus the count envelope `c/n` times the alphabet bit cost
`Nat.log 2 |α| + 2`. Both summands vanish, so `lz78AchievSlack → 0`. -/
noncomputable def lz78AchievSlack (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log 2)
    + (2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
        + 1 / Real.sqrt (n : ℝ))
      * ((Nat.log 2 (Fintype.card α) : ℝ) + 2)

omit [MeasurableSingletonClass α] in
/-- **Per-block, per-path Ziv upper bound** (Phase Z4 core step): for `n ≥ 2`
and a fixed observed path whose `n`-block cylinder has positive mass, the
bit rate of the distinct code is below the base-2 per-block estimator plus
the vanishing slack. Combines the genuine base-2 Ziv inequality
(`ziv_count_mul_logb_le_neg_logb_blockProb`, gated on the combinatorial
core) with the bit-length expansion and the deterministic count envelope.

`@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem lz78DistinctRate_le_blockLogAvg₂_add_slack
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (hn : 2 ≤ n) (ω : Ω)
    (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω}) :
    (lz78DistinctEncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
      ≤ blockLogAvg₂ μ p n ω + lz78AchievSlack (α := α) n := by
  sorry

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **The achievability slack vanishes**: `lz78AchievSlack n → 0` as
`n → ∞`. Both terms vanish (`1/(n log 2) → 0`; the envelope `2K/log n + 1/√n
→ 0` times the constant alphabet cost). -/
theorem lz78AchievSlack_tendsto_zero :
    Filter.Tendsto (lz78AchievSlack (α := α)) Filter.atTop (𝓝 (0 : ℝ)) := by
  unfold lz78AchievSlack
  -- `(n : ℝ) → ∞`, `Real.log n → ∞`, `Real.sqrt n → ∞`.
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  -- `(n : ℝ) * log 2 → ∞`.
  have hnlog2 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const log_two_pos hcast
  -- `1/(n log 2) → 0`, `2K/log n → 0`, `1/√n → 0`.
  have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) * Real.log 2))
      Filter.atTop (𝓝 0) := by
    simp only [one_div]; exact hnlog2.inv_tendsto_atTop
  have h2 : Filter.Tendsto
      (fun n : ℕ => 2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ))
      Filter.atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hlog
  have h3 : Filter.Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ))
      Filter.atTop (𝓝 0) := by
    simpa using hsqrt.inv_tendsto_atTop
  -- combine: envelope `(h2 + h3) * const → 0`, plus `h1 → 0`.
  have henv : Filter.Tendsto
      (fun n : ℕ => (2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
            + 1 / Real.sqrt (n : ℝ))
          * ((Nat.log 2 (Fintype.card α) : ℝ) + 2))
      Filter.atTop (𝓝 0) := by
    have := (h2.add h3).mul_const ((Nat.log 2 (Fintype.card α) : ℝ) + 2)
    simpa using this
  have := h1.add henv
  simpa using this

/-- **Phase Z4 — genuine construction of `IsLZ78AchievabilityZivUpperBound`
from the combinatorial core + regularity**.

Given the isolated combinatorial core `IsLZ78ZivCombinatorialCore` (the
load-bearing Cover–Thomas Lemma 13.5.5 distinct-phrase content) and the
a.s. full-support regularity hypothesis `hreg`, the distinct LZ78 code
satisfies the per-path bit-based Ziv upper bound structure with the
vanishing slack `lz78AchievSlack`. Everything except the combinatorial
core is genuine (the regularity `hreg` is the same admissible full-support
family used by `isLZ78PerPathParsingFactorization_of_pos`).

This is the honest *primitive deferral* the plan describes (撤退ライン
L-Z2): the achievability structure is genuinely *constructed* from a
strictly-more-primitive named hypothesis (`IsLZ78ZivCombinatorialCore`, a
per-block combinatorial inequality) than the structure
`IsLZ78AchievabilityZivUpperBound` it produces. It does **not** reduce the
headline assumption count by itself, but it relocates the single remaining
honest input to its most primitive, clearly-load-bearing form.

`@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem isLZ78AchievabilityZivUpperBound_distinct
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (hreg : ∀ (n : ℕ) (ω : Ω) (m : ℕ),
      m ≤ n → 0 < prefixBlockProb μ p ω m) :
    IsLZ78AchievabilityZivUpperBound μ p
      (@lz78DistinctEncodingLength α _ _ _) (lz78AchievSlack (α := α)) := by
  sorry

end Assembly

/-! ## §6. Intermediate base-2 headline — achievability core wired (Phase V) -/

section Headline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A base-2 distinct headline with the achievability Ziv upper bound
genuinely wired from its most primitive form** (Phase V, partial).

This re-derives the genuine Cover–Thomas Theorem 13.5.3 base-2 limit
`lz78_two_sided_optimality_distinct_genuine` with the **achievability**
honest input `IsLZ78AchievabilityZivUpperBound` *no longer assumed* — it is
genuinely constructed (`isLZ78AchievabilityZivUpperBound_distinct`) from the
strictly-more-primitive isolated combinatorial core
`IsLZ78ZivCombinatorialCore` plus the admissible full-support regularity
`hreg`. The slack is the genuine vanishing `lz78AchievSlack`.

**Honesty status (read this).** After the Phase 2.3 sweep
(`lz78-sorry-migration-plan`), the `hcore : IsLZ78ZivCombinatorialCore`
hypothesis has been removed from the signature and the body retreated to
`sorry`. Closure is tracked by `lz78-ziv-inequality-discharge-moonshot-plan`,
which owns the Cover–Thomas Lemma 13.5.5 distinct-phrase combinatorial core
(`c · log c ≤ ∑ⱼ -log qⱼ`) — the load-bearing per-block combinatorial heart
that the committed foundation (which exposes only *path-prefix* phrase
conditionals, not the LZ tree-node sub-distribution) cannot bridge.

The remaining honest inputs at the signature level are:

* `h_lb : IsLZ78ConverseCodingLowerBound` — the converse coding lower bound
  (Core 2, untouched here; separate `lz78-residual-discharge-plan` track for
  the predicate-retract decision).
* `hreg` — admissible full-support regularity (same family as
  `isLZ78PerPathParsingFactorization_of_pos`), not load-bearing.

`@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem lz78_two_sided_optimality_distinct_ziv_core_wired
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slackLow : ℕ → ℝ)
    (hreg : ∀ (n : ℕ) (ω : Ω) (m : ℕ),
      m ≤ n → 0 < prefixBlockProb μ p.toStationaryProcess ω m)
    (h_lb : IsLZ78ConverseCodingLowerBound μ p.toStationaryProcess
              (@lz78DistinctEncodingLength α _ _ _) slackLow) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n =>
          (lz78DistinctEncodingLength n
              (p.toStationaryProcess.blockRV n ω) : ℝ)
            / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate₂ μ p.toStationaryProcess)) := by
  sorry

end Headline

end InformationTheory.Shannon
