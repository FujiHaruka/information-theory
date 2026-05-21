import Common2026.Shannon.LZ78ZivCombinatorics
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

/-!
# LZ78 tree-induced (path-prefix) coding measure `Q_c` and its AEP upper half

This file constructs the **LZ78 path-prefix tree-induced sub-probability
measure** `Q_c(x^n)` and genuinely proves its **AEP upper half**

```
∀ᵐ ω, limsup_n (-log₂ Q_c(x^n) / n) ≤ entropyRate₂ μ p.
```

It is the achievability-side analogue of `algoet_cover_limsup_bound`
(`SMBAlgoetCover.lean`, the path-block-law `Pₙ` AEP limsup), specialised to
the LZ tree-induced coding measure.

## What `Q_c` is here (read this — the route taken)

`Q_c(x^n)` is the **path-prefix product** of the LZ78 per-phrase conditional
probabilities along the parse,
`Q_c(x^n) = ∏ⱼ condPhraseProb μ p n ω j = prefixBlockProb ω (boundary c)`
(`treeInducedProb`). This is the genuine *coding distribution* the Ziv chain
factorizes against: `blockProb_le_prod_condPhraseProb` (`StationaryKernel.lean`,
genuine, unconditional under positivity) gives `Pₙ ≤ Q_c`, i.e. the tree-induced
coding measure *over-estimates* the true block probability of the realised path
(prefix monotonicity of the cylinder mass, `prefixBlockProb_antitone`).

## How the AEP upper half closes (genuine, no new ergodic content)

Because `Pₙ ≤ Q_c`, taking `-log` reverses to `-log Q_c ≤ -log Pₙ = n·blockLogAvg`,
so the per-symbol tree-induced rate is dominated by the path-block-law rate:

```
(-log Q_c) / n  ≤  blockLogAvg μ p n ω.
```

Taking `limsup` and using the **already-genuine** path-block-law AEP limsup
`algoet_cover_limsup_bound` (`limsup blockLogAvg ≤ entropyRate`, proved
internally by the fixed-`k` `qkSingleton` sandwich + `H_k → H`) closes the
upper half. Dividing through by `Real.log 2 > 0` gives the base-2 form against
`entropyRate₂`. **No fresh ergodic theorem is built**: the route reduces the
tree-induced AEP to the existing path-block-law AEP via the genuine coding
inequality `Pₙ ≤ Q_c`. (This is the cleaner discharge than the planned
fixed-`k` *sandwich of `Q_c`*: the relation `Pₙ ≤ Q_c` is already in the
committed layer, whereas a factor-by-factor `Q_c ≥ qkSingleton(k)` does **not**
hold — conditional probabilities are not monotone in context depth for general
ergodic sources, so the planned route-C error term `δ_k(n)` is not
ω-uniformly controllable. See the M0 finding in the proof log.)

## Honesty status — what this DOES and does NOT discharge (read before reuse)

* **DOES** (genuine, regularity-only): the tree-induced AEP **upper half**
  `limsup (-log₂ Q_c / n) ≤ entropyRate₂`, with `Q_c` the path-prefix coding
  measure. Zero `sorry`, no load-bearing hypothesis; the only side condition is
  full-support regularity (`hreg`, the same admissible family as
  `isLZ78PerPathParsingFactorization_of_pos`), used to get `0 < Pₙ`.

* **DOES NOT** discharge the LZ78 achievability gap. The achievability gap is
  the **per-block combinatorial Ziv core** `c·log c ≤ -log Q_c`
  (`IsLZ78ZivCombinatorialCore`, `LZ78ZivCombinatorics.lean`), **not** the
  `Q_c` AEP. Two obstructions, established in the M0 analysis:

  1. For the **path-prefix** `Q_c` used here, the conditionals do **not** sum
     to `≤ 1` per dictionary stratum (`∑ⱼ qⱼ ≈ c`, the documented trap at
     `IsLZ78ZivCombinatorialCore`'s docstring), so the log-sum step
     `c·log c ≤ ∑ⱼ -log qⱼ` fails — the Ziv combinatorial core is *false*
     for this `Q_c`. (Constant-process witness: every conditional is `1`, so
     `-log Q_c = 0` while `c·log c > 0`; the same `(a^16)` witness as
     `not_isLZ78ZivCombinatorialCoreOverhead`.)

  2. For the **tree-node** `Q_c^{tree}` (where `∑ q ≤ 1` *does* hold per node,
     so `node_logsum_step` applies and the log-sum step is genuine), the
     relation `Pₙ ≤ Q_c^{tree}` is **not** in the committed layer, and its AEP
     `-log Q_c^{tree}/n → H` would need genuinely new ergodic content (the
     route-C sandwich, which does not close — see above). The genuine Ziv
     lemma there carries a `c·log(D_c)` *grouping overhead* (`D_c` ≈ distinct
     tree nodes), with `(c log D_c)/n → 0`, so optimality is **a.s.-eventual**,
     not a per-block `∀n∀ω` inequality.

  The plan's premise that "`c·log c ≤ -log Q_c` is TRUE (the disproof is `Pₙ`
  only)" is therefore **mathematically false** for both forms of `Q_c`: the
  constant-process witness applies to the path-prefix `Q_c` (1), and the
  tree-node `Q_c^{tree}` needs the grouping overhead (2). This is flagged in
  the proof log as an honesty defect in the plan; this file does **not** build
  on it.

The genuine value published here is the tree-induced AEP upper half itself
(a reusable AEP statement) plus the honest localisation of the true frontier.

## File layout

* **§1.** `treeInducedProb` — the path-prefix tree-induced coding measure `Q_c`
  and `negLogbTreeInducedRate`.
* **§2.** `treeInducedProb_ge_blockProb` — the genuine coding inequality
  `Pₙ ≤ Q_c` (from `blockProb_le_prod_condPhraseProb`).
* **§3.** `negLogbTreeInducedRate_le_blockLogAvg₂` — the per-`n` domination
  `(-log₂ Q_c)/n ≤ blockLogAvg₂`.
* **§4.** `treeInducedProb_negLogb_div_limsup_le_entropyRate₂` — the main
  AEP upper half, via `algoet_cover_limsup_bound`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

section TreeInduced

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-! ## §1. The path-prefix tree-induced coding measure `Q_c` -/

/-- **LZ78 path-prefix tree-induced coding measure `Q_c(x^n)`**: the product,
over the phrase positions of the LZ78 parse of the observed block, of the
per-phrase conditional probabilities `condPhraseProb`. By
`prod_condPhraseProb_telescope` this equals `prefixBlockProb ω (boundary c)`,
the cylinder mass of the longest *complete-phrase* parse prefix; the genuine
coding inequality `Pₙ ≤ Q_c` (`blockProb_le_prod_condPhraseProb`) makes it a
super-estimate of the true block probability. -/
noncomputable def treeInducedProb
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.range (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
    condPhraseProb μ p n ω j

/-- **Per-symbol base-2 negative-log tree-induced rate** `(-log₂ Q_c)/n`. -/
noncomputable def negLogbTreeInducedRate
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) : ℝ :=
  - Real.log (treeInducedProb μ p n ω) / ((n : ℝ) * Real.log 2)

/-! ## §2. Genuine coding inequality `Pₙ ≤ Q_c` -/

/-- **Genuine coding inequality `Pₙ ≤ Q_c`** (under full-support regularity):
the true block probability is bounded above by the tree-induced coding measure.
Direct from `blockProb_le_prod_condPhraseProb` (`StationaryKernel.lean`,
genuine, unconditional given positivity of the parse-prefix masses). -/
theorem treeInducedProb_ge_blockProb
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω)
    (hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
      prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0) :
    (μ.map (p.blockRV n)).real {p.blockRV n ω} ≤ treeInducedProb μ p n ω := by
  unfold treeInducedProb
  exact blockProb_le_prod_condPhraseProb μ p n ω hpos

/-! ## §3. Per-`n` domination by the path-block-law rate -/

/-- **Per-`n` domination** `(-log₂ Q_c)/n ≤ blockLogAvg₂`: since `Pₙ ≤ Q_c`
and `0 < Pₙ`, taking `-log` reverses to `-log Q_c ≤ -log Pₙ = n·blockLogAvg`,
and dividing by `n·log 2 > 0` gives the per-symbol base-2 bound. -/
theorem negLogbTreeInducedRate_le_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    {n : ℕ} (hn : 0 < n) (ω : Ω)
    (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω})
    (hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
      prefixBlockProb μ p ω (parsingBoundary μ p n ω j) ≠ 0) :
    negLogbTreeInducedRate μ p n ω ≤ blockLogAvg₂ μ p n ω := by
  set Pn : ℝ := (μ.map (p.blockRV n)).real {p.blockRV n ω} with hPndef
  set Qc : ℝ := treeInducedProb μ p n ω with hQcdef
  have hle : Pn ≤ Qc := treeInducedProb_ge_blockProb μ p n ω hpos
  have hQc_pos : 0 < Qc := lt_of_lt_of_le hPn hle
  -- `-log Qc ≤ -log Pn` (log monotone on positives).
  have hlog : - Real.log Qc ≤ - Real.log Pn :=
    neg_le_neg (Real.log_le_log hPn hle)
  -- denominators are positive.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2_pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hden_pos : (0 : ℝ) < (n : ℝ) * Real.log 2 := mul_pos hn_pos hlog2_pos
  -- `blockLogAvg₂ = -log Pn / (n log 2)`.
  have hblk : blockLogAvg₂ μ p n ω = - Real.log Pn / ((n : ℝ) * Real.log 2) := by
    unfold blockLogAvg₂ blockLogAvg
    rw [hPndef]; field_simp
  unfold negLogbTreeInducedRate
  rw [← hQcdef, hblk]
  gcongr

end TreeInduced

/-! ## §4. AEP upper half -/

section AEPUpperHalf

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Tree-induced AEP upper half (main theorem)**:
`∀ᵐ ω, limsup (-log₂ Q_c / n) ≤ entropyRate₂ μ p`.

Per-`n` the tree-induced rate is dominated by the path-block-law base-2 rate
`blockLogAvg₂` (`negLogbTreeInducedRate_le_blockLogAvg₂`, eventually in `n`
since it needs `n ≥ 1`); taking `limsup` and using the genuine path-block-law
AEP limsup `algoet_cover_limsup_bound` (in nats, `/log 2`-converted to base-2)
gives the bound. Regularity-only: `hreg` supplies `0 < Pₙ` and the
parse-prefix positivity. **NOT** a discharge of LZ78 achievability — see file
docstring (the achievability gap is the per-block combinatorial Ziv core,
not this AEP). -/
theorem treeInducedProb_negLogb_div_limsup_le_entropyRate₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)
    (hreg : ∀ (n : ℕ) (ω : Ω) (m : ℕ),
      m ≤ n → 0 < prefixBlockProb μ p.toStationaryProcess ω m) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => negLogbTreeInducedRate μ p.toStationaryProcess n ω)
        Filter.atTop
      ≤ entropyRate₂ μ p.toStationaryProcess := by
  set q := p.toStationaryProcess with hq
  -- base-2 SMB: `blockLogAvg₂ → entropyRate₂` a.s.
  filter_upwards [shannon_mcmillan_breiman₂ μ p] with ω h_smb
  set R : ℕ → ℝ := fun n => negLogbTreeInducedRate μ q n ω with hR
  set B : ℕ → ℝ := fun n => blockLogAvg₂ μ q n ω with hB
  set H : ℝ := entropyRate₂ μ q with hH
  -- (a) eventual domination `R n ≤ B n` for `n ≥ 1`.
  have h_ev_le : ∀ᶠ n in Filter.atTop, R n ≤ B n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : 0 < n := hn
    -- parse-prefix positivity from `hreg`.
    have hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length,
        prefixBlockProb μ q ω (parsingBoundary μ q n ω j) ≠ 0 := by
      intro j _
      exact (hreg n ω (parsingBoundary μ q n ω j)
        (parsingBoundary_le_n μ q n ω j)).ne'
    -- `0 < Pₙ` is `hreg` at the full length (via `prefixBlockProb` definitional unfold).
    have hPn : 0 < (μ.map (q.blockRV n)).real {q.blockRV n ω} := by
      have := hreg n ω n (le_refl n)
      simpa [prefixBlockProb] using this
    exact negLogbTreeInducedRate_le_blockLogAvg₂ μ q hn_pos ω hPn hpos
  -- (b) `limsup R ≤ limsup B`.
  have h_limsup_le : Filter.limsup R Filter.atTop ≤ Filter.limsup B Filter.atTop := by
    refine Filter.limsup_le_limsup h_ev_le ?_ ?_
    · -- `R` is bounded below by `0` (since `Q_c ≤ 1`), hence cobounded for `≤`.
      refine (Filter.isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)).isCoboundedUnder_le
      -- `R n = -log Q_c / (n log 2) ≥ 0` because `0 < Q_c ≤ 1`.
      have hn_pos : 0 < n := hn
      have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
      have hlog2_pos : (0 : ℝ) < Real.log 2 := log_two_pos
      have hden_pos : (0 : ℝ) < (n : ℝ) * Real.log 2 := mul_pos hnR_pos hlog2_pos
      -- `Q_c = prefixBlockProb (boundary c) ≤ 1`.
      have hQc_le_one : treeInducedProb μ q n ω ≤ 1 := by
        unfold treeInducedProb
        have hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length,
            prefixBlockProb μ q ω (parsingBoundary μ q n ω j) ≠ 0 := by
          intro j _
          exact (hreg n ω (parsingBoundary μ q n ω j)
            (parsingBoundary_le_n μ q n ω j)).ne'
        rw [prod_condPhraseProb_telescope μ q n ω _ hpos]
        unfold prefixBlockProb
        have : IsProbabilityMeasure
            (μ.map (q.blockRV (parsingBoundary μ q n ω
              (lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length))) :=
          Measure.isProbabilityMeasure_map (q.measurable_blockRV _).aemeasurable
        exact measureReal_le_one
      have hlogQc_nonpos : Real.log (treeInducedProb μ q n ω) ≤ 0 := by
        apply Real.log_nonpos _ hQc_le_one
        -- `0 ≤ Q_c`: it is a finite product of nonneg ratios; here just need ≤ via
        -- the telescoped probability which is nonneg.
        unfold treeInducedProb
        have hpos : ∀ j ≤ (lz78PhraseStrings (List.ofFn (q.blockRV n ω))).length,
            prefixBlockProb μ q ω (parsingBoundary μ q n ω j) ≠ 0 := by
          intro j _
          exact (hreg n ω (parsingBoundary μ q n ω j)
            (parsingBoundary_le_n μ q n ω j)).ne'
        rw [prod_condPhraseProb_telescope μ q n ω _ hpos]
        unfold prefixBlockProb
        exact measureReal_nonneg
      show 0 ≤ R n
      rw [hR]
      unfold negLogbTreeInducedRate
      apply div_nonneg _ hden_pos.le
      linarith
    · -- `B` is bounded above because it converges (`h_smb`).
      exact h_smb.isBoundedUnder_le
  -- (c) `limsup B = entropyRate₂`.
  have h_limsup_B : Filter.limsup B Filter.atTop = H := h_smb.limsup_eq
  rw [← h_limsup_B]
  exact h_limsup_le

end AEPUpperHalf

end InformationTheory.Shannon
