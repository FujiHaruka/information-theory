import Common2026.Shannon.ShannonMcMillanBreiman
import Common2026.Shannon.LZ78GreedyLongestPrefix
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-!
# LZ78 Ziv-inequality entropy bridge — foundational lemmas (T4-A)

This file hosts the foundational, mutually-independent lemmas of the LZ78
Ziv-inequality entropy bridge (Cover–Thomas §13.5), built on top of the
already-genuine SMB layer (`blockLogAvg`, `ShannonMcMillanBreiman.lean`).

## Main results

* `log_sum_inequality` — the (finite) **log-sum inequality**
  `(∑ aᵢ)·log((∑aᵢ)/(∑bᵢ)) ≤ ∑ aᵢ·log(aᵢ/bᵢ)`, derived from convexity of
  `x ↦ x·log x` (`Real.convexOn_mul_log`) via finite Jensen
  (`ConvexOn.map_sum_le`).
* `blockLogAvg_eq_neg_log_blockProb` — the trivial restatement
  `n · blockLogAvg μ p n ω = -log Pₙ{block ω}` for `0 < n`, the form the Ziv
  chain consumes.

## Per-path parsing factorization (L-LZ-Z5 scaffolding)

The true crux of the Ziv bridge — that the pushforward block probability
`Pₙ{block ω}` factorizes as a product of per-phrase conditional
probabilities along the LZ78 parse — is *not* dischargeable from the
current stationary layer (`StationaryProcess` is a measure-preserving shift
plus a single observable, with no kernel / `compProd` / disintegration).
We therefore expose it as an **isolated honest hypothesis**, strictly more
primitive than the `blockLogAvg`-level `h_achiev` / `h_converse`:

* `condPhraseProb` — the per-phrase conditional probability indexed by
  phrase position `j`, defined concretely as the ratio of successive
  parsing-prefix block probabilities (telescoping to `Pₙ{block ω}`).
* `IsLZ78PerPathParsingFactorization` — the named honest `Prop`
  (`Pₙ{block ω} = ∏ⱼ condPhraseProb …`), carrying a positivity field so
  `Real.log_prod` applies.
* `blockProb_neg_log_eq_sum` — a *genuine* proof, from that hypothesis,
  that `-log Pₙ{block ω} = ∑ⱼ -log (condPhraseProb …)`.

The intricate per-path Ziv inequality and the achievability / converse
assembly are deferred; this file only lays the clean base.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Log-sum inequality** (finite form).

For nonnegative `aᵢ` and strictly positive `bᵢ` over a finite index set `s`,
`(∑ aᵢ)·log((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ·log(aᵢ/bᵢ)`.

Proved from convexity of `x ↦ x·log x` (`Real.convexOn_mul_log`) via finite
Jensen (`ConvexOn.map_sum_le`) with weights `bᵢ/(∑ b)` and points `aᵢ/bᵢ`. -/
theorem log_sum_inequality
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp
  -- `B := ∑ b > 0`, weights `w i = b i / B`, points `p i = a i / b i`.
  set B : ℝ := ∑ i ∈ s, b i with hB_def
  have hB_pos : 0 < B := Finset.sum_pos hb hs
  have hB_ne : B ≠ 0 := hB_pos.ne'
  set A : ℝ := ∑ i ∈ s, a i with hA_def
  -- Jensen for `x ↦ x * log x` on `Set.Ici 0`.
  have h₀ : ∀ i ∈ s, 0 ≤ b i / B := fun i hi =>
    div_nonneg (hb i hi).le hB_pos.le
  have h₁ : ∑ i ∈ s, b i / B = 1 := by
    rw [← Finset.sum_div, ← hB_def, div_self hB_ne]
  have hmem : ∀ i ∈ s, a i / b i ∈ Set.Ici (0 : ℝ) := fun i hi => by
    simp only [Set.mem_Ici]; exact div_nonneg (ha i hi) (hb i hi).le
  have hJensen :=
    Real.convexOn_mul_log.map_sum_le (t := s)
      (w := fun i => b i / B) (p := fun i => a i / b i) h₀ h₁ hmem
  -- Simplify the two `smul`-sums on `ℝ`.
  have hpt : ∀ i ∈ s, (b i / B) • (a i / b i) = a i / B := fun i hi => by
    have hbi : b i ≠ 0 := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  have hlhs_arg : (∑ i ∈ s, (b i / B) • (a i / b i)) = A / B := by
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, ← hA_def]
  have hrhs : (∑ i ∈ s, (b i / B) • ((a i / b i) * Real.log (a i / b i)))
      = ∑ i ∈ s, (a i / B) * Real.log (a i / b i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hbi : b i ≠ 0 := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  rw [hlhs_arg, hrhs] at hJensen
  -- `hJensen : (A/B) * log (A/B) ≤ ∑ (a i / B) * log (a i / b i)`.
  -- Multiply both sides by `B > 0`.
  have hkey := mul_le_mul_of_nonneg_right hJensen hB_pos.le
  calc A * Real.log (A / B)
      = (A / B) * Real.log (A / B) * B := by field_simp
    _ ≤ (∑ i ∈ s, (a i / B) * Real.log (a i / b i)) * B := hkey
    _ = ∑ i ∈ s, a i * Real.log (a i / b i) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        field_simp

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Restatement of `blockLogAvg` as a negative log block-probability.**

For `0 < n`, `n · blockLogAvg μ p n ω = -log Pₙ{block ω}` where
`Pₙ = μ.map (blockRV n)`. Trivial unfolding of the `blockLogAvg` definition;
this is the form the per-path Ziv inequality consumes. -/
theorem blockLogAvg_eq_neg_log_blockProb
    (μ : Measure Ω) (p : StationaryProcess μ α) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    (n : ℝ) * blockLogAvg μ p n ω
      = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold blockLogAvg
  field_simp

/-! ## Per-path parsing factorization (L-LZ-Z5 scaffolding) -/

/-- **Cumulative parsing boundary length.**

The number of input symbols consumed by the first `j` emitted LZ78 phrases
of the observed block `blockRV n ω`, i.e. the sum of the lengths of the
first `j` distinct phrase strings. Used as a `blockRV` index to read the
block probability of the corresponding parsing prefix. -/
def parsingBoundary
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) (j : ℕ) : ℕ :=
  (((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).take j).map List.length).sum

/-- **Prefix block probability.**

The pushforward block probability of the length-`m` parsing prefix of the
observed path, `Pₘ{blockRV m ω} = (μ.map (blockRV m)).real {blockRV m ω}`. -/
noncomputable def prefixBlockProb
    (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) (m : ℕ) : ℝ :=
  (μ.map (p.blockRV m)).real {p.blockRV m ω}

/-- **Per-phrase conditional probability** (Cover–Thomas §13.5, chain-rule
per-path form), indexed by phrase position `j`.

Concretely the ratio of the block probabilities of the parsing prefix after
`j+1` phrases and after `j` phrases:
`condPhraseProb μ p n ω j = Pₘ₊₁{prefix} / Pₘ{prefix}` where `m`-prefix is the
prefix ending at the `j`-th phrase boundary. Over the phrase positions of
the parse this product telescopes to `Pₙ{block ω}` — the content of
`IsLZ78PerPathParsingFactorization`.

This is `ℝ`-valued so that `Real.log_prod` applies directly in
`blockProb_neg_log_eq_sum` (Mathlib-shape-driven: the dominant downstream
lemma is `Real.log_prod`). -/
noncomputable def condPhraseProb
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) (j : ℕ) : ℝ :=
  prefixBlockProb μ p ω (parsingBoundary μ p n ω (j + 1))
    / prefixBlockProb μ p ω (parsingBoundary μ p n ω j)

/-- **Isolated honest input (L-LZ-Z5)**: the per-path block probability of a
stationary process factorizes as the product of the LZ78 parse's per-phrase
conditional probabilities (Cover–Thomas §13.5, the per-path / per-realization
form of the entropy chain rule).

This is *strictly more primitive* than the `blockLogAvg`-level chain
hypotheses `h_achiev` / `h_converse`: it is a single, parsing-level
measure-theoretic identity. It is **not** the expectation-level
`jointEntropy_chain_rule`, which is not interchangeable with this per-path
statement. The current stationary layer carries no kernel / `compProd`
structure to derive it, so it is exposed as a named honest hypothesis (a
genuine `Prop`, never `True`).

The `pos` field records strict positivity of each conditional factor over
the phrase positions; this discharges the side condition of `Real.log_prod`
in `blockProb_neg_log_eq_sum`. -/
structure IsLZ78PerPathParsingFactorization
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop where
  /-- The block probability factorizes as the product of per-phrase
  conditional probabilities over the parse of the observed block. -/
  factor : ∀ (n : ℕ) (ω : Ω),
    (μ.map (p.blockRV n)).real {p.blockRV n ω}
      = ∏ j ∈ Finset.range
            (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
          condPhraseProb μ p n ω j
  /-- Each conditional factor is strictly positive over the phrase positions
  of the parse (positivity side condition for `Real.log_prod`). -/
  pos : ∀ (n : ℕ) (ω : Ω) (j : ℕ),
    j ∈ Finset.range (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length →
      0 < condPhraseProb μ p n ω j

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Genuine backbone (L-LZ-Z3 + factorization → additive log form).**

From the honest factorization hypothesis, the negative log block
probability is the sum, over the phrase positions of the parse, of the
negative logs of the per-phrase conditional probabilities:
`-log Pₙ{block ω} = ∑ⱼ -log (condPhraseProb …)`.

Proved via `Real.log_prod` (positivity of each factor supplied by the
`pos` field of the hypothesis). This is the additive form the per-path Ziv
inequality consumes; combined with `blockLogAvg_eq_neg_log_blockProb` it
expresses `n · blockLogAvg` as the same sum. -/
theorem blockProb_neg_log_eq_sum
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (h : IsLZ78PerPathParsingFactorization μ p) (n : ℕ) (ω : Ω) :
    - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
      = ∑ j ∈ Finset.range
            (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
          - Real.log (condPhraseProb μ p n ω j) := by
  have hne : ∀ j ∈ Finset.range
      (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
      condPhraseProb μ p n ω j ≠ 0 := fun j hj => (h.pos n ω j hj).ne'
  rw [h.factor n ω, Real.log_prod hne, ← Finset.sum_neg_distrib]

/-! ## Base-2 (bit) layer — unit correction for the LZ78 headline

The LZ78 encoding length `lz78DistinctEncodingLength` is measured in **bits**
(`LZ78Phrase.bitLength` uses `Nat.log 2`, the binary code-length), whereas
`blockLogAvg` / `entropyRate` are **natural-log** quantities (nats). The
genuine Cover–Thomas Theorem 13.5.3 statement is bit-based:

```
(lz n x)/n → H₂   where  H₂ = (entropy rate in bits) = entropyRate / log 2.
```

We therefore introduce the base-2 (bit) versions `blockLogAvg₂` and
`entropyRate₂` as the natural-log quantities divided by `Real.log 2`. These
are *unit conversions*, not new content: `blockLogAvg₂ = blockLogAvg / log 2`
converges to `entropyRate₂ = entropyRate / log 2` directly from SMB. The
LZ78 achievability / converse bounds, being genuinely bit-based
(`c·log₂c ≤ -log₂ Pₙ`), are stated against `blockLogAvg₂`. -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `0 < Real.log 2` — the unit-conversion constant between nats and bits. -/
theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- **Base-2 (bit) per-block empirical entropy estimator**:
`blockLogAvg₂ μ p n ω = blockLogAvg μ p n ω / Real.log 2`, the per-block
negative log-likelihood measured in **bits** (`-(1/n) log₂ Pₙ{block}`). This
is the quantity the bit-based LZ78 rate `(lz n x)/n` is compared against. -/
noncomputable def blockLogAvg₂
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω => blockLogAvg μ p n ω / Real.log 2

/-- **Base-2 (bit) entropy rate**: `entropyRate₂ μ p = entropyRate μ p / Real.log 2`,
the entropy rate measured in **bits per symbol**. This is the genuine
Cover–Thomas Theorem 13.5.3 limit for the bit-based LZ78 per-symbol rate. -/
noncomputable def entropyRate₂ (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ :=
  entropyRate μ p / Real.log 2

end InformationTheory.Shannon
