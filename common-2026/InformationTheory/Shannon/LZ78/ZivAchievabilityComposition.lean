import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.ZivThreading
import InformationTheory.Shannon.LZ78.ZivCondGrouping

/-!
# LZ78 achievability composition: threading + `(k-state, length)` grouping

This file composes the two sorryAx-free upstream bricks of the LZ78 achievability
wall `ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`,
`@residual(wall:lz78-aseventual-ziv)`):

* `negLogQk_parse_threading` (`ZivThreading.lean`): the a.s. threading identity
  `negLogQk μ p k n ω = (leading boundary) + (per-phrase sum) + (trailing tail)`,
  where the per-phrase sum is **position-indexed** (`∑ j : Fin c`).
* `condState_grouping_bound_mean` (`ZivCondGrouping.lean`): the
  `(k-state, length)` grouped entropy bound with `o(n)` mean-length overhead, on a
  `Finset (List α)` of distinct phrase strings.

The composition target is the a.s. lower bound `c · log c ≤ negLogQk + overhead`
in the manifestly-`o(n)` mean-length form, the input to the downstream
"divide by `n`, limsup, diagonalize `k → ∞`" step.

## Two sub-steps

* **(A) boundary-nonneg.** The threading identity carries two boundary sums of
  `pmfLogCondMarkov μ p k i ω`. Since `pmfLogCondMarkov` is `-log` of a conditional
  kernel singleton mass `≤ 1` (the kernel is a Markov kernel, so its value at every
  point is a probability measure), each term is `≥ 0`, hence the per-phrase sum is
  `≤ negLogQk`. This holds **unconditionally** (no a.s. caveat needed for the
  positivity).
* **(B) reindex `Fin c → Finset` + apply `condState_grouping_bound_mean`.** The
  threading phrase sum is position-indexed; `condState_grouping_bound_mean` consumes
  a `Finset (List α)` of distinct phrase strings. Bridging the two requires the `c`
  tiled phrases to be distinct as strings (so `card = c`) and the content/state
  correspondence between the position-indexed terms and the string-indexed terms.
  This reindexing bridge is the present leg's residual.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {μ : Measure Ω}

/-! ## Telescoping helper -/

/-- Telescoping of consecutive differences of a monotone `ℕ → ℕ` sequence:
`∑_{j<c} (M (j+1) - M j) = M c - M 0`. -/
theorem sum_range_consecutive_sub_of_monotone
    (M : ℕ → ℕ) (hMmono : ∀ i, M i ≤ M (i + 1)) (c : ℕ) :
    (∑ j ∈ Finset.range c, (M (j + 1) - M j)) = M c - M 0 := by
  have hMmono_le : ∀ i j, i ≤ j → M i ≤ M j := by
    intro i j hij
    induction j with
    | zero => simp_all
    | succ j ihj =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ihj (Nat.lt_succ_iff.mp h)).trans (hMmono j)
      · have : i = j + 1 := le_antisymm hij h
        subst this; exact le_refl _
  induction c with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hm0 : M 0 ≤ M m := hMmono_le 0 m (Nat.zero_le m)
    have hmm1 : M m ≤ M (m + 1) := hMmono m
    omega

/-! ## Sub-step (A): nonnegativity of the per-step Markov log-likelihood -/

omit [DecidableEq α] in
/-- The per-step `k`-Markov negative conditional log-likelihood is nonnegative:
`pmfLogCondMarkov μ p k i ω = -log m` where `m = (condDistrib … ).real {…}` is a
singleton mass of a probability measure (`condDistrib` is a Markov kernel), hence
`0 ≤ m ≤ 1` and `-log m ≥ 0`. Holds for every `ω` (no a.s. caveat). -/
theorem pmfLogCondMarkov_nonneg
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k i : ℕ)
    (ω : Ω) :
    0 ≤ pmfLogCondMarkov μ p k i ω := by
  -- `pmfLogCondMarkov = -log m` with `m = (condDistrib …).real {…} ≤ 1`, so `-log m ≥ 0`.
  -- `pmfLogCond` is `-log` of a `condDistrib` singleton mass (a probability measure).
  have hnonneg : ∀ (j : ℕ) (ω' : Ω), 0 ≤ pmfLogCond μ p j ω' := by
    intro j ω'
    unfold pmfLogCond
    set m : ℝ := (condDistrib (p.obs j) (p.blockRV j) μ (p.blockRV j ω')).real {p.obs j ω'}
      with hm
    have hle : m ≤ 1 := by rw [hm]; exact measureReal_le_one
    have h0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
    have : Real.log m ≤ 0 := Real.log_nonpos h0 hle
    linarith
  unfold pmfLogCondMarkov
  by_cases h : i ≤ k
  · simp only [h, if_true]; exact hnonneg i ω
  · simp only [h, if_false]; exact hnonneg k _

/-! ## Sub-step (A): the per-phrase sum is bounded by `negLogQk` -/

omit [DecidableEq α] in
/-- The position-indexed per-phrase sum from the threading identity is bounded above
by `negLogQk`, because the two boundary sums (`pmfLogCondMarkov` over `[0,b)` and
`[e,n)`) are nonnegative.  Stated abstractly in the shape produced by
`negLogQk_parse_threading`. -/
theorem phraseSum_le_negLogQk
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ)
    (ω : Ω) (b c e : ℕ) (N : Fin (c + 1) → ℕ)
    (hthread : negLogQk μ p k n ω
        = (∑ i ∈ Finset.range b, pmfLogCondMarkov μ p k i ω)
          + (∑ j : Fin c,
              -Real.log
                (condQkState μ p k (windowState p k (N j.castSucc) ω)
                  (N j.succ - N j.castSucc)
                  (fun m => p.obs (N j.castSucc + m.val) ω)).toReal)
          + ∑ i ∈ Finset.Ico e n, pmfLogCondMarkov μ p k i ω) :
    (∑ j : Fin c,
        -Real.log
          (condQkState μ p k (windowState p k (N j.castSucc) ω)
            (N j.succ - N j.castSucc)
            (fun m => p.obs (N j.castSucc + m.val) ω)).toReal)
      ≤ negLogQk μ p k n ω := by
  -- The two boundary sums are nonnegative (each summand is `≥ 0` by `pmfLogCondMarkov_nonneg`).
  have hA : 0 ≤ ∑ i ∈ Finset.range b, pmfLogCondMarkov μ p k i ω :=
    Finset.sum_nonneg (fun i _ => pmfLogCondMarkov_nonneg μ p k i ω)
  have hB : 0 ≤ ∑ i ∈ Finset.Ico e n, pmfLogCondMarkov μ p k i ω :=
    Finset.sum_nonneg (fun i _ => pmfLogCondMarkov_nonneg μ p k i ω)
  rw [hthread]
  linarith

/-! ## Sub-step (B): the achievability composition lemma -/

/-- **LZ78 achievability composition** (a.s. form): for a.e. `ω`, the tiled phrase
count `c` and total parsed length `Ntot ≤ n` satisfy the `o(n)`-overhead Ziv lower
bound
`c · log c ≤ negLogQk μ p k n ω + (c · log (Ntot / c) + c + c · log (#states))`,
with the phrase count `c` anchored to the genuine distinct-phrase count of the
parse (`c + bAbsorbed = (lz78PhraseStrings …).length`, `bAbsorbed ≤ k+1`).

This is the input to the downstream "divide by `n`, limsup, diagonalize `k → ∞`"
step: divide by `n`, the overhead is `o(n)` (mean length `~ log n`, `c = O(n/log n)`),
and the boundary terms vanish.

@residual(wall:lz78-aseventual-ziv) -/
theorem ziv_achievability_composition
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∀ᵐ ω ∂μ, ∃ (c bAbsorbed Ntot : ℕ),
      c + bAbsorbed = (lz78PhraseStrings (List.ofFn (fun i => p.blockRV n ω i))).length ∧
      bAbsorbed ≤ k + 1 ∧
      Ntot ≤ n ∧
      (c : ℝ) * Real.log (c : ℝ)
        ≤ negLogQk μ p k n ω
          + ((c : ℝ) * Real.log ((Ntot : ℝ) / (c : ℝ))
              + (c : ℝ)
              + (c : ℝ) * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ)) := by
  classical
  filter_upwards [negLogQk_parse_threading μ p k n] with ω hthread
  obtain ⟨b, c, e, bAbsorbed, Lmax, N, hNb, hNe, hen, hmono, hstart, hcount, hbA,
    hne_tail, hb_bound, hthread_eq⟩ := hthread
  -- Total parsed length `Ntot = ∑_j len_j`, where `len_j = N j.succ - N j.castSucc`.
  set Ntot : ℕ := ∑ j : Fin c, (N j.succ - N j.castSucc) with hNtot_def
  refine ⟨c, bAbsorbed, Ntot, hcount, hbA, ?_, ?_⟩
  · -- `Ntot ≤ n`: the per-phrase lengths sum to `e - b ≤ e ≤ n` (telescoping).
    -- Extend `N` to a total monotone `M` to telescope (idiom from `negLogQk_phrase_threading`).
    set M : ℕ → ℕ := fun i => if h : i < c + 1 then N ⟨i, h⟩ else e with hM_def
    have hMN : ∀ (i : ℕ) (h : i < c + 1), M i = N ⟨i, h⟩ := by
      intro i h; simp only [hM_def, h, dif_pos]
    have hMcastSucc : ∀ j : Fin c, M j.val = N j.castSucc := by
      intro j; rw [hMN j.val (by omega)]; congr 1
    have hMsucc : ∀ j : Fin c, M (j.val + 1) = N j.succ := by
      intro j; rw [hMN (j.val + 1) (by omega)]; congr 1
    have hM0 : M 0 = b := by rw [hMN 0 (by omega), ← hNb]; congr 1
    have hMc : M c = e := by rw [hMN c (by omega), ← hNe]; congr 1
    have hMmono : ∀ i, M i ≤ M (i + 1) := by
      intro i
      by_cases hic : i + 1 < c + 1
      · have hi : i < c := by omega
        have h1 : M i = N (⟨i, hi⟩ : Fin c).castSucc := hMN i (by omega)
        have h2 : M (i + 1) = N (⟨i, hi⟩ : Fin c).succ := hMN (i + 1) (by omega)
        rw [h1, h2]; exact le_of_lt (hmono ⟨i, hi⟩)
      · have hMi1 : M (i + 1) = e := by
          simp only [hM_def, Nat.not_lt.mpr (Nat.not_lt.mp hic), dif_neg, not_false_eq_true]
        rcases Nat.lt_or_ge i (c + 1) with hi | hi
        · have hieq : i = c := by omega
          rw [hMi1, ← hMc, hieq]
        · have hMi : M i = e := by
            simp only [hM_def, Nat.not_lt.mpr hi, dif_neg, not_false_eq_true]
          rw [hMi, hMi1]
    -- Telescoping of differences: `∑_{j<c} (M (j+1) - M j) = M c - M 0`.
    have htel : (∑ j ∈ Finset.range c, (M (j + 1) - M j)) = M c - M 0 :=
      sum_range_consecutive_sub_of_monotone M hMmono c
    -- Rewrite `Ntot` over `range c` matching `M`.
    have hNtot_range : Ntot = ∑ j ∈ Finset.range c, (M (j + 1) - M j) := by
      rw [hNtot_def, Finset.sum_range fun j => M (j + 1) - M j]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hMcastSucc j, hMsucc j]
    rw [hNtot_range, htel, hM0, hMc]
    omega
  · -- The Ziv lower bound.  (A) gives `phraseSum ≤ negLogQk`; the reindex + grouping
    -- step (B) gives `c·log c ≤ phraseSum + overhead`.  Chain the two.
    have hA :
        (∑ j : Fin c,
            -Real.log
              (condQkState μ p k (windowState p k (N j.castSucc) ω)
                (N j.succ - N j.castSucc)
                (fun m => p.obs (N j.castSucc + m.val) ω)).toReal)
          ≤ negLogQk μ p k n ω :=
      phraseSum_le_negLogQk μ p k n ω b c e N hthread_eq
    -- (B) reindex `Fin c → Finset (List α)` of distinct phrase strings, then apply
    -- `condState_grouping_bound_mean`.  This is the residual reindexing bridge.
    -- @residual(wall:lz78-aseventual-ziv)
    have hB :
        (c : ℝ) * Real.log (c : ℝ)
          ≤ (∑ j : Fin c,
              -Real.log
                (condQkState μ p k (windowState p k (N j.castSucc) ω)
                  (N j.succ - N j.castSucc)
                  (fun m => p.obs (N j.castSucc + m.val) ω)).toReal)
            + ((c : ℝ) * Real.log ((Ntot : ℝ) / (c : ℝ))
                + (c : ℝ)
                + (c : ℝ) * Real.log (((Fintype.card α) ^ k : ℕ) : ℝ)) := by
      sorry
    linarith

end InformationTheory.Shannon
