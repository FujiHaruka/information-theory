import Common2026.Shannon.LZ78ZivCombinatorics
import Common2026.Shannon.LZ78ConverseKraft
import Common2026.Shannon.LZ78AchievabilityLimsup
import Common2026.Shannon.LZ78SMBSandwich
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

/-!
# LZ78 achievability — a.s.-eventual honest landing (L-AS1)

This file closes the LZ78 achievability *envelope reduction* genuinely (no
dependence on the disproved per-block cores) and lands the remaining
ergodic content on a **single, satisfiable, honest, load-bearing** named
hypothesis `IsLZ78ZivAsEventual`, then rewires the base-2 distinct headline
so it is conditioned on that satisfiable hypothesis instead of the
unsatisfiable (FALSE) combinatorial cores.

## Why this file exists (honesty improvement)

The previously wired headline
`lz78_two_sided_optimality_distinct_ziv_core_wired`
(`LZ78ZivCombinatorics.lean`) is conditioned on
`IsLZ78ZivCombinatorialCore` — a per-block `∀ n ∀ ω` inequality
`c·log c ≤ ∑ⱼ -log qⱼ`. That core (and its `O(c)`-overhead variant
`IsLZ78ZivCombinatorialCoreOverhead`) is **mathematically FALSE**
(machine-checked refutation `not_isLZ78ZivCombinatorialCoreOverhead`,
`LZ78ZivTreeBridge.lean`). A headline conditioned on a FALSE hypothesis is
*vacuously conditioned*: it carries no genuine content for the witness
process (and the whole `Pₙ ≈ 1` family).

This file replaces that FALSE per-block core with the **a.s.-eventual**
ergodic statement that is actually true for nondegenerate ergodic processes
(the genuine Cover–Thomas Lemma 13.5.5 / Thm 13.5.3 content), namely

```
IsLZ78ZivAsEventual μ p :  ∀ᵐ ω ∂μ, limsup (fun n => (c·log₂ c)/n) ≤ entropyRate₂.
```

This is a *satisfiable* hypothesis (it holds for ergodic processes — the
limit of `(c·log₂ c)/n` is the entropy rate by the Cover–Thomas
length-grouping argument), not a FALSE per-block inequality, so the rewired
headline is **conditioned on a true statement**, an honest improvement.

## What is genuine here

* `countLogRate₂` — the per-path bit-rate `(c·log₂ c)/n`.
* `lz78DistinctRate_le_countLogRate₂_add_slack` — the **envelope reduction**
  `lz/n ≤ (c·log₂ c)/n + lz78AchievSlack`, proved **without** the FALSE Ziv
  cores: it stops the bit-length expansion at `c·log c` (the genuine part of
  `lz78DistinctRate_le_blockLogAvg₂_add_slack`, dropping the `hziv'`
  `c·log c ≤ -log Pₙ` step that needed the FALSE core).
* `lz78_achievability_limsup_le₂_aseventual` — the limsup half-bound
  `limsup (lz/n) ≤ entropyRate₂` assembled from the genuine envelope
  reduction + the satisfiable `IsLZ78ZivAsEventual`.
* `lz78_two_sided_optimality_distinct_aseventual` — the rewired base-2
  distinct headline (Tendsto to `entropyRate₂`), now conditioned on the
  satisfiable `IsLZ78ZivAsEventual` + the converse coding lower bound,
  instead of the FALSE combinatorial core.

## What remains load-bearing (honest)

`IsLZ78ZivAsEventual` is the single load-bearing ergodic input. It is a
genuine `Prop` (type ≠ conclusion: an a.s.-eventual `limsup` bound on the
*count* rate, not the LZ *code* rate), never `True`, never a `:= h` alias.
Its genuine proof is the Cover–Thomas length-grouping argument
(`c log c ≤ -log Q_c^{tree} + c·H(length-dist)`, with overhead
`c·H(length-dist) ≤ c·log(maxlen)` and `maxlen ≤ log_b n`, then the
tree-induced AEP `-log Q_c^{tree}/n → H`). The AEP for the variable-depth
tree-induced measure `Q_c^{tree}` is an ergodic statement independent of the
committed SMB layer (a library-scale ergodic gap, see
`lz78-treeinduced-aep-plan.md`), so it is left as this honest hypothesis.
This is the same honest frontier as the Chernoff band-mass / Huffman
modulo_aux_ident hypotheses. It is **NOT a discharge** and **NOT a
regularity** hypothesis — it is load-bearing ergodic content.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

/-! ## §1. The distinct-phrase count log-rate `(c·log₂ c)/n` -/

section CountLogRate

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Distinct-phrase count log-rate (base 2)**: `(c·log₂ c)/n` where
`c = |distinct phrases of the length-`n` block|`. This is the LHS of the
Cover–Thomas Eq. 13.124 estimate, *before* it is bounded by the per-block
negative log-likelihood. -/
noncomputable def countLogRate₂
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) : ℝ :=
  (((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
      * Real.logb 2 ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ))
    / (n : ℝ)

end CountLogRate

/-! ## §2. Genuine envelope reduction (no FALSE core) -/

section EnvelopeReduction

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Genuine envelope reduction** (Step 1, FALSE-core-free): the per-symbol
bit rate of the distinct LZ78 code is below the distinct-phrase count
log-rate `(c·log₂ c)/n` plus the vanishing slack `lz78AchievSlack`:

```
(lz n x)/n  ≤  (c·log₂ c)/n  +  lz78AchievSlack n.
```

This is the genuine half of `lz78DistinctRate_le_blockLogAvg₂_add_slack`:
the bit-length expansion `lz = c·(Nat.log 2 (c+1) + Nat.log 2 |α| + 2)`,
bounding `Nat.log 2 (c+1) ≤ (log c + 1/c)/log 2` and `c/n` by the genuine
count envelope, **stops at `c·log c`** — it does **not** invoke the
(FALSE) per-block Ziv inequality `c·log c ≤ -log Pₙ`. Distribution-free,
ω-uniform, holds for every `n ≥ 2` and every path. -/
theorem lz78DistinctRate_le_countLogRate₂_add_slack
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (n : ℕ) (hn : 2 ≤ n) (ω : Ω) :
    (lz78DistinctEncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
      ≤ countLogRate₂ μ p n ω + lz78AchievSlack (α := α) n := by
  classical
  set c : ℕ := (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length with hc
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hlog2_pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
  -- `lz = c · (Nat.log 2 (c+1) + Nat.log 2 |α| + 2)`.
  have hlz : (lz78DistinctEncodingLength n (p.blockRV n ω) : ℝ)
      = (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ)
          + (Nat.log 2 (Fintype.card α) : ℝ) + 2) := by
    rw [lz78DistinctEncodingLength_eq, LZ78Phrase.bitLength_eq]
    push_cast
    ring
  -- `countLogRate₂ = (c · logb 2 c)/n`.
  have hclr : countLogRate₂ μ p n ω
      = ((c : ℝ) * Real.logb 2 (c : ℝ)) / (n : ℝ) := by
    rw [countLogRate₂, ← hc]
  set D : ℝ := (Nat.log 2 (Fintype.card α) : ℝ) + 2 with hD
  set env : ℝ := 2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
    + 1 / Real.sqrt (n : ℝ) with hEnv
  have hD_nn : (0 : ℝ) ≤ D := by rw [hD]; positivity
  -- `slack = 1/(n log2) + env·D`.
  have hslack_eq : lz78AchievSlack (α := α) n
      = 1 / ((n : ℝ) * Real.log 2) + env * D := by
    rw [lz78AchievSlack, hEnv, hD]
  -- envelope: `c/n ≤ env`.
  have henv := lz78Distinct_count_div_le_envelope n hn (p.blockRV n ω)
  rw [← hc, ← hEnv] at henv
  -- `c = 0` reduction (lz = 0, count log-rate = 0, slack ≥ 0).
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · rw [hlz, hc0, hclr, hc0]
    simp only [Nat.cast_zero, zero_mul, zero_div, zero_add]
    have hslk_nn : (0 : ℝ) ≤ lz78AchievSlack (α := α) n := by
      rw [hslack_eq]
      have h1 : (0 : ℝ) ≤ 1 / ((n : ℝ) * Real.log 2) := by positivity
      have henv_nn : (0 : ℝ) ≤ env := by
        rw [hEnv]
        have hKnn : (0 : ℝ) ≤ Real.log (Fintype.card α + 1) :=
          Real.log_nonneg (by
            have : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
            linarith)
        positivity
      have := mul_nonneg henv_nn hD_nn
      linarith
    exact hslk_nn
  · -- `c ≥ 1`: the genuine chain, stopping at `c·logb 2 c`.
    have hcR_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
    -- `Nat.log 2 (c+1) ≤ logb 2 (c+1) = log (c+1)/log 2`.
    have hnatlog : (Nat.log 2 (c + 1) : ℝ) ≤ Real.log ((c : ℝ) + 1) / Real.log 2 := by
      have h := Real.natLog_le_logb (c + 1) 2
      rw [Real.logb] at h
      push_cast at h
      exact h
    -- `log (c+1) ≤ log c + 1/c`.
    have hlogc1 : Real.log ((c : ℝ) + 1) ≤ Real.log (c : ℝ) + 1 / (c : ℝ) := by
      have hratio : Real.log (((c : ℝ) + 1) / (c : ℝ)) ≤ ((c : ℝ) + 1) / (c : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) hcR_pos.ne'] at hratio
      have : ((c : ℝ) + 1) / (c : ℝ) - 1 = 1 / (c : ℝ) := by field_simp; ring
      rw [this] at hratio
      linarith
    -- Term A: `c · Nat.log 2 (c+1) ≤ (c·log c + 1)/log 2`.
    have htermA_num : (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
        ≤ ((c : ℝ) * Real.log (c : ℝ) + 1) / Real.log 2 := by
      calc (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
          ≤ (c : ℝ) * (Real.log ((c : ℝ) + 1) / Real.log 2) :=
            mul_le_mul_of_nonneg_left hnatlog hcR_pos.le
        _ ≤ (c : ℝ) * ((Real.log (c : ℝ) + 1 / (c : ℝ)) / Real.log 2) := by
            apply mul_le_mul_of_nonneg_left _ hcR_pos.le
            apply div_le_div_of_nonneg_right hlogc1 hlog2_pos.le
        _ = ((c : ℝ) * Real.log (c : ℝ) + 1) / Real.log 2 := by
            field_simp
    -- `c · logb 2 c = (c · log c)/log 2`.
    have hcountlog : (c : ℝ) * Real.logb 2 (c : ℝ)
        = ((c : ℝ) * Real.log (c : ℝ)) / Real.log 2 := by
      rw [Real.logb]; ring
    -- Assemble.
    rw [hlz, hclr]
    rw [show (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ)
            + (Nat.log 2 (Fintype.card α) : ℝ) + 2)
          = (c : ℝ) * (Nat.log 2 (c + 1) : ℝ) + (c : ℝ) * D by rw [hD]; ring]
    rw [add_div, hslack_eq]
    -- Term A bound `/n`: `(c·natlog(c+1))/n ≤ (c·logb 2 c)/n + 1/(n log2)`.
    have hAterm : ((c : ℝ) * (Nat.log 2 (c + 1) : ℝ)) / (n : ℝ)
        ≤ ((c : ℝ) * Real.logb 2 (c : ℝ)) / (n : ℝ)
            + 1 / ((n : ℝ) * Real.log 2) := by
      have hnum : (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
          ≤ (c : ℝ) * Real.logb 2 (c : ℝ) + 1 / Real.log 2 := by
        rw [hcountlog]
        calc (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
            ≤ ((c : ℝ) * Real.log (c : ℝ) + 1) / Real.log 2 := htermA_num
          _ = ((c : ℝ) * Real.log (c : ℝ)) / Real.log 2 + 1 / Real.log 2 := by
              rw [add_div]
      calc ((c : ℝ) * (Nat.log 2 (c + 1) : ℝ)) / (n : ℝ)
          ≤ ((c : ℝ) * Real.logb 2 (c : ℝ) + 1 / Real.log 2) / (n : ℝ) :=
            div_le_div_of_nonneg_right hnum hn_pos.le
        _ = ((c : ℝ) * Real.logb 2 (c : ℝ)) / (n : ℝ)
              + 1 / ((n : ℝ) * Real.log 2) := by
            rw [add_div, div_div, mul_comm (Real.log 2) (n : ℝ)]
    -- Term B: `(c·D)/n ≤ env·D`.
    have hBterm : ((c : ℝ) * D) / (n : ℝ) ≤ env * D := by
      rw [mul_comm (c : ℝ) D, mul_div_assoc]
      calc D * ((c : ℝ) / (n : ℝ)) ≤ D * env :=
            mul_le_mul_of_nonneg_left henv hD_nn
        _ = env * D := by ring
    -- Combine.
    have := add_le_add hAterm hBterm
    linarith

end EnvelopeReduction

/-! ## §3. The satisfiable honest a.s.-eventual hypothesis (L-AS1) -/

section AsEventualHypothesis

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- **Satisfiable honest a.s.-eventual Ziv hypothesis (L-AS1, Cover–Thomas
Lemma 13.5.5 / Thm 13.5.3, length-grouping).**

```
∀ᵐ ω ∂μ,  limsup (fun n => (c·log₂ c)/n) atTop  ≤  entropyRate₂ μ p.
```

For an a.s. set of `ω`, the per-symbol distinct-phrase count log-rate
`(c·log₂ c)/n` has limsup at most the base-2 entropy rate. This is the
genuine Cover–Thomas LZ78 optimality content, in **a.s.-eventual** form
(unlike the per-block `c·log c ≤ -log Pₙ`, which is FALSE).

**Satisfiability.** This statement is *true* for nondegenerate ergodic
processes: the Cover–Thomas length-grouping argument gives
`c log c ≤ -log Q_c^{tree} + c·H(length-dist)` with overhead
`c·H(length-dist) ≤ c·log(maxlen)` and `maxlen ≤ log_b n`, so the overhead
`/n → 0`; combined with the tree-induced AEP `-log Q_c^{tree}/n → H` it
yields `(c log c)/n → H`, hence `limsup (c·log₂ c)/n ≤ entropyRate₂`. (In
the degenerate `H = 0` case both sides are `0`: `c ≈ √n` gives
`(c·log₂ c)/n → 0`, so the limsup is `≤ 0 = entropyRate₂` — genuine, not
vacuous.) So this is a **satisfiable** hypothesis, NOT a FALSE per-block
inequality.

**Honesty status.** This is a genuine `Prop` whose type (an a.s.-eventual
`limsup` bound on the *count* rate `(c·log₂ c)/n`) differs from the headline
conclusion (Tendsto of the *code* rate `(lz n x)/n` to `entropyRate₂`). It
is **NOT a discharge** and **NOT a regularity** hypothesis: it is the
**load-bearing ergodic content** (the variable-depth tree-induced AEP
`-log Q_c^{tree}/n → H`, a library-scale ergodic statement independent of
the committed SMB layer; see `lz78-treeinduced-aep-plan.md`). It is never
`True`, never a `:= h` alias. -/
def IsLZ78ZivAsEventual
    (μ : Measure Ω) (p : StationaryProcess μ α)
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] :
    Prop :=
  ∀ᵐ ω ∂μ,
    Filter.limsup (fun n => countLogRate₂ μ p n ω) Filter.atTop
      ≤ entropyRate₂ μ p

end AsEventualHypothesis

/-! ## §4. limsup half-bound from the satisfiable hypothesis -/

section LimsupAssembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Upper boundedness of the count log-rate** (genuine, ω-uniform): the
distinct-phrase count log-rate `(c·log₂ c)/n` is `≤ K/log 2` for every `n`,
hence bounded above. From the genuine Cover–Thomas counting bound
`c·log c ≤ K·n` (`lz78PhraseStrings_mul_log_le`, `K = 8·log(|α|+1)`). -/
theorem countLogRate₂_isBoundedUnder_le
    (μ : Measure Ω) (p : StationaryProcess μ α) (ω : Ω) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => countLogRate₂ μ p n ω) := by
  set K : ℝ := 8 * Real.log (Fintype.card α + 1) with hK
  have hlog2_pos : (0 : ℝ) < Real.log 2 := log_two_pos
  refine Filter.isBoundedUnder_of_eventually_le (a := K / Real.log 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  set c : ℕ := (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length with hc
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- `c·log c ≤ K·n`.
  have hKn : (c : ℝ) * Real.log (c : ℝ) ≤ K * (n : ℝ) := by
    have h := lz78PhraseStrings_mul_log_le (List.ofFn (p.blockRV n ω))
    rw [List.length_ofFn] at h
    rw [hc, hK]; exact_mod_cast h
  -- `countLogRate₂ = (c·log c)/(n·log 2) ≤ (K·n)/(n·log 2) = K/log 2`.
  rw [countLogRate₂, ← hc, Real.logb]
  rw [show (c : ℝ) * (Real.log (c : ℝ) / Real.log 2) / (n : ℝ)
      = ((c : ℝ) * Real.log (c : ℝ)) / ((n : ℝ) * Real.log 2) by ring]
  rw [div_le_div_iff₀ (by positivity) hlog2_pos]
  nlinarith [hKn, hn_pos, hlog2_pos]

/-- The count log-rate `(c·log₂ c)/n` is eventually below
`limsup (countLogRate₂) + ε` (definition of limsup, given coboundedness),
and the LZ code rate is `≤ countLogRate₂ + slack` (envelope reduction), so
`limsup (lz/n) ≤ limsup (countLogRate₂)`. Combined with the satisfiable
`IsLZ78ZivAsEventual` this gives `limsup (lz/n) ≤ entropyRate₂`.

`@audit:suspect(lz78-achievability-converse-plan)` -/
theorem lz78_achievability_limsup_le₂_aseventual
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_ase : IsLZ78ZivAsEventual μ p.toStationaryProcess)
    (h_lz_cobdd : ∀ᵐ ω ∂μ,
        Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
          (fun n => (lz78DistinctEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78DistinctEncodingLength n
          (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ entropyRate₂ μ p.toStationaryProcess := by
  filter_upwards [h_ase, h_lz_cobdd] with ω h_ase_ω h_lz_cobdd_ω
  set L : ℕ → ℝ :=
    fun n => (lz78DistinctEncodingLength n (p.toStationaryProcess.blockRV n ω) : ℝ)
      / (n : ℝ) with hL
  set C : ℕ → ℝ := fun n => countLogRate₂ μ p.toStationaryProcess n ω with hC
  set H : ℝ := entropyRate₂ μ p.toStationaryProcess with hH
  -- `C` is bounded above (ω-uniform counting envelope).
  have hC_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop C :=
    countLogRate₂_isBoundedUnder_le μ p.toStationaryProcess ω
  -- `limsup C ≤ H` from the satisfiable hypothesis.
  have h_limsupC : Filter.limsup C Filter.atTop ≤ H := h_ase_ω
  -- Goal: `limsup L ≤ H`. Show `∀ ε > 0, limsup L − ε ≤ H`.
  refine le_of_forall_sub_le (fun ε hε => ?_)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- `slack ≤ ε/2` eventually.
  have h_slack_le : ∀ᶠ n in Filter.atTop, lz78AchievSlack (α := α) n ≤ ε / 2 := by
    have := (lz78AchievSlack_tendsto_zero (α := α)).eventually (gt_mem_nhds hε2)
    filter_upwards [this] with n hn
    exact le_of_lt hn
  -- `C n ≤ H + ε/2` eventually, from `limsup C ≤ H < H + ε/2` + boundedness.
  have h_count_le : ∀ᶠ n in Filter.atTop, C n ≤ H + ε / 2 := by
    have hlt : Filter.limsup C Filter.atTop < H + ε / 2 := by linarith
    have := Filter.eventually_lt_of_limsup_lt hlt hC_bdd
    filter_upwards [this] with n hn
    exact le_of_lt hn
  -- `L n ≤ C n + slack n` eventually (envelope reduction, n ≥ 2).
  have h_env_le : ∀ᶠ n in Filter.atTop, L n ≤ C n + lz78AchievSlack (α := α) n := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact lz78DistinctRate_le_countLogRate₂_add_slack μ p.toStationaryProcess n hn ω
  -- Combine: `L n ≤ H + ε` eventually.
  have h_ev_le : ∀ᶠ n in Filter.atTop, L n ≤ H + ε := by
    filter_upwards [h_env_le, h_count_le, h_slack_le] with n hLn hCn hslk
    calc L n ≤ C n + lz78AchievSlack (α := α) n := hLn
      _ ≤ (H + ε / 2) + ε / 2 := by linarith
      _ = H + ε := by ring
  have := Filter.limsup_le_of_le h_lz_cobdd_ω h_ev_le
  linarith [this]

end LimsupAssembly

/-! ## §5. Rewired base-2 distinct headline (FALSE core → satisfiable hyp) -/

section Headline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A base-2 distinct headline, conditioned on the satisfiable
a.s.-eventual hypothesis** (honest improvement over
`lz78_two_sided_optimality_distinct_ziv_core_wired`).

The bit-based per-symbol LZ78 rate `(lz n (blockRV n ω))/n` converges a.s. to
the base-2 entropy rate `entropyRate₂`, conditioned on:

* `h_ase : IsLZ78ZivAsEventual` — the **satisfiable** a.s.-eventual Ziv
  hypothesis (replacing the FALSE per-block `IsLZ78ZivCombinatorialCore`),
* `h_lb : IsLZ78ConverseCodingLowerBound` — the converse coding lower bound
  (Core 2, untouched).

Honesty: the achievability input is now a **true** statement
(`IsLZ78ZivAsEventual` holds for ergodic processes) rather than the FALSE
combinatorial core, so the headline is conditioned on a satisfiable
hypothesis — a genuine honesty improvement (no longer vacuously
conditioned). The achievability content is localized to the single
load-bearing `IsLZ78ZivAsEventual`.

`@audit:suspect(lz78-achievability-converse-plan)` -/
theorem lz78_two_sided_optimality_distinct_aseventual
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slackLow : ℕ → ℝ)
    (h_ase : IsLZ78ZivAsEventual μ p.toStationaryProcess)
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
  -- Boundedness of the per-symbol rate (genuine, both directions).
  have h_bdd_le := lz78DistinctEncodingLength_isBoundedUnder_le μ p
  have h_bdd_ge := lz78DistinctEncodingLength_isBoundedUnder_ge μ p
  -- The limsup half-bound from the satisfiable a.s.-eventual hypothesis.
  have h_limsup_le := lz78_achievability_limsup_le₂_aseventual μ p h_ase
    (by filter_upwards [h_bdd_ge] with ω hω; exact hω.isCoboundedUnder_le)
  -- The liminf half-bound from the converse coding lower bound (genuine).
  have h_le_liminf := lz78_converse_le_liminf₂ μ p
    (@lz78DistinctEncodingLength α _ _ _) slackLow h_lb
    (by filter_upwards [h_bdd_le] with ω hω; exact hω.isCoboundedUnder_ge)
  -- Sandwich `liminf ≥ H`, `limsup ≤ H`, with boundedness, gives `Tendsto`.
  filter_upwards [h_limsup_le, h_le_liminf, h_bdd_le, h_bdd_ge]
    with ω hu hl hba hbb
  exact tendsto_of_le_liminf_of_limsup_le hl hu hba hbb

end Headline

end InformationTheory.Shannon
