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
  This is now discharged (sorryAx-free): the slice/content correspondence
  `flatten_drop_take_getElem` (threaded through the tiling chain) identifies the
  `j`-th tiled slice with the `(bAbsorbed + j)`-th greedy phrase, `lz78PhraseStrings_nodup`
  gives distinctness (`card = c`), and the per-term reindex composes via `Finset.sum_image`.
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

omit [DecidableEq α] in
/-- Congruence for `condQkState` under a length equality: equal state `s`, equal
lengths (`ℓ₁ = ℓ₂`), and continuations equal after the `Fin.cast` give equal masses.
Used to bridge the `(phrase j).length`-indexed term to the `N j.succ - N j.castSucc`-indexed
threading term. -/
theorem condQkState_congr_length
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k : ℕ)
    (s : Fin k → α) (ℓ₁ ℓ₂ : ℕ) (hℓ : ℓ₁ = ℓ₂)
    (Z₁ : Fin ℓ₁ → α) (Z₂ : Fin ℓ₂ → α)
    (hZ : ∀ i : Fin ℓ₁, Z₁ i = Z₂ (Fin.cast hℓ i)) :
    condQkState μ p k s ℓ₁ Z₁ = condQkState μ p k s ℓ₂ Z₂ := by
  subst hℓ
  congr 1
  funext i
  simpa using hZ i

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

**Now genuinely closed (sorryAx-free).** The former residual was the (B) reindexing
bridge from the position-indexed threading sum (`∑ j : Fin c`) onto the distinct-phrase
`Finset` consumed by `condState_grouping_bound_mean`. It is discharged by:

* the slice/content correspondence `flatten_drop_take_getElem`
  (`GreedyLongestPrefix.lean`, sorryAx-free) threaded through the tiling chain
  (`lz78_parse_tiling_positions` → `lz78_block_tiling` → `negLogQk_parse_threading`),
  which exposes that the `j`-th tiled slice is the `(bAbsorbed + j)`-th greedy phrase
  string;
* the distinctness of those slices via `lz78PhraseStrings_nodup` (so the image `Finset`
  has card `= c`);
* the per-term reindex `condQkState (windowState …) (…) (fun m => p.obs …) ↦
  condQkState (st w) |w| (toFinVec |w| w)` with `st` the trailing `k`-state read off the
  parse inverse, plus the per-phrase positivity `condQkState_pos_of_markovFactor_pos`.

The `c = 0` boundary degenerates honestly to `0 ≤ 0`. The broader achievability wall
`@residual(wall:lz78-aseventual-ziv)` (M3 variable-depth length-grouping AEP + W2 limsup
discharge connecting to `entropyRate₂`) lives downstream at
`ziv_aseventual_le_blockLogAvg₂` / `lz78GreedyImpl_achievability_ae`; this brick
(`c·log c ≤ negLogQk + o(n)`) is no longer part of it. -/
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
    hne_tail, hb_bound, hslice, hpphpos, hthread_eq⟩ := hthread
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
    -- `condState_grouping_bound_mean`.
    set input : List α := List.ofFn (fun i => p.blockRV n ω i) with hinput_def
    -- The `j`-th phrase string is the tiled slice (from `hslice`).
    set phrase : Fin c → List α :=
      fun j => (input.drop (N j.castSucc)).take (N j.succ - N j.castSucc) with hphrase_def
    -- Monotonicity `N j.succ ≤ e` (so each phrase fits inside `[0, n)`).
    have hN_mono_nat : ∀ (i j : ℕ) (hi : i < c + 1) (hj : j < c + 1), i ≤ j →
        N ⟨i, hi⟩ ≤ N ⟨j, hj⟩ := by
      intro i j hi hj hij
      induction j with
      | zero => simp_all
      | succ j ihj =>
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · have hjc : j < c := by omega
          have hstep : N (⟨j, by omega⟩ : Fin c).castSucc + 1
              ≤ N (⟨j, by omega⟩ : Fin c).succ := hmono ⟨j, by omega⟩
          have hcast : (⟨j, by omega⟩ : Fin c).castSucc = (⟨j, by omega⟩ : Fin (c + 1)) := by
            apply Fin.ext; simp
          have hsucc : (⟨j, by omega⟩ : Fin c).succ = (⟨j + 1, by omega⟩ : Fin (c + 1)) := by
            apply Fin.ext; simp
          rw [hcast, hsucc] at hstep
          exact (ihj (by omega) (Nat.lt_succ_iff.mp h)).trans (by omega)
        · have : i = j + 1 := le_antisymm hij h
          subst this; exact le_refl _
    have hNsucc_le_e : ∀ j : Fin c, N j.succ ≤ e := by
      intro j
      rw [← hNe]
      have h1 : N j.succ = N (⟨j.val + 1, by omega⟩ : Fin (c + 1)) := by
        congr 1
      have h2 : N (Fin.last c) = N (⟨c, by omega⟩ : Fin (c + 1)) := by
        congr 1
      rw [h1, h2]
      exact hN_mono_nat (j.val + 1) c (by omega) (by omega) (by have := j.isLt; omega)
    -- Each tiled slice has the prescribed length `N j.succ - N j.castSucc`.
    have hinput_len : input.length = n := by rw [hinput_def]; exact List.length_ofFn
    have hphrase_len : ∀ j : Fin c, (phrase j).length = N j.succ - N j.castSucc := by
      intro j
      rw [hphrase_def]
      simp only [List.length_take, List.length_drop, hinput_len]
      have h1 : N j.succ ≤ e := hNsucc_le_e j
      have h2 : N j.castSucc + 1 ≤ N j.succ := hmono j
      omega
    -- The slice content reads off `obs` (the obs-coherence half).
    have hphrase_get : ∀ (j : Fin c) (m : ℕ), m < N j.succ - N j.castSucc →
        (phrase j)[m]? = some (p.obs (N j.castSucc + m) ω) := by
      intro j m hm
      rw [hphrase_def]
      rw [List.getElem?_take_of_lt hm, List.getElem?_drop]
      have hlt : N j.castSucc + m < n := by
        have h1 : N j.succ ≤ e := hNsucc_le_e j
        omega
      have hlt' : N j.castSucc + m < input.length := by rw [hinput_len]; exact hlt
      rw [List.getElem?_eq_getElem hlt']
      congr 1
      simp only [hinput_def, List.getElem_ofFn]
      rfl
    -- Injectivity of `phrase` (the slices are distinct phrase strings, `Nodup`).
    have hLnodup : (lz78PhraseStrings input).Nodup := lz78PhraseStrings_nodup input
    have hphrase_idx : ∀ j : Fin c,
        ∃ (h : bAbsorbed + j.val < (lz78PhraseStrings input).length),
          (lz78PhraseStrings input)[bAbsorbed + j.val] = phrase j := by
      intro j
      have := hslice j
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨h, heq⟩ := this
      exact ⟨h, heq⟩
    have hphrase_inj : Function.Injective phrase := by
      intro j₁ j₂ heq
      obtain ⟨h₁, he₁⟩ := hphrase_idx j₁
      obtain ⟨h₂, he₂⟩ := hphrase_idx j₂
      have hval : (lz78PhraseStrings input)[bAbsorbed + j₁.val]
          = (lz78PhraseStrings input)[bAbsorbed + j₂.val] := by
        rw [he₁, he₂, heq]
      have hget : (lz78PhraseStrings input).get ⟨bAbsorbed + j₁.val, h₁⟩
          = (lz78PhraseStrings input).get ⟨bAbsorbed + j₂.val, h₂⟩ := by
        simpa [List.get_eq_getElem] using hval
      have hidx : (⟨bAbsorbed + j₁.val, h₁⟩ : Fin _) = ⟨bAbsorbed + j₂.val, h₂⟩ :=
        (hLnodup.get_inj_iff).mp hget
      have : j₁.val = j₂.val := by
        have := Fin.mk.inj_iff.mp hidx
        omega
      exact Fin.ext this
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
      rcases Nat.eq_zero_or_pos c with hc0 | hcpos
      · -- `c = 0`: both sides degenerate to `0 ≤ 0`.
        subst hc0
        simp [hNtot_def]
      · -- `c > 0`: reindex onto the distinct-phrase `Finset` and apply the grouping bound.
        haveI : Nonempty (Fin c) := ⟨⟨0, hcpos⟩⟩
        -- The state function on phrase strings: invert `phrase`, read the trailing state.
        set st : List α → (Fin k → α) :=
          fun w => windowState p k (N (Function.invFun phrase w).castSucc) ω with hst_def
        -- On `phrase j`, `st` recovers the trailing `k`-state at `N j.castSucc`.
        have hst_phrase : ∀ j : Fin c, st (phrase j) = windowState p k (N j.castSucc) ω := by
          intro j
          simp only [hst_def]
          rw [Function.leftInverse_invFun hphrase_inj j]
        -- The distinct-phrase `Finset`.
        set phrases : Finset (List α) := Finset.univ.image phrase with hphrases_def
        have hcard : phrases.card = c := by
          rw [hphrases_def, Finset.card_image_of_injective _ hphrase_inj,
            Finset.card_univ, Fintype.card_fin]
        have hne : phrases.Nonempty := by
          rw [hphrases_def]
          exact (Finset.univ_nonempty (α := Fin c)).image _
        have hInjOn : Set.InjOn phrase (Finset.univ : Finset (Fin c)) :=
          hphrase_inj.injOn
        -- Per-term identity: the string-indexed summand equals the threading summand.
        have hterm : ∀ j : Fin c,
            condQkState μ p k (st (phrase j)) (phrase j).length
                (toFinVec (phrase j).length (phrase j))
              = condQkState μ p k (windowState p k (N j.castSucc) ω)
                  (N j.succ - N j.castSucc)
                  (fun m => p.obs (N j.castSucc + m.val) ω) := by
          intro j
          rw [hst_phrase j]
          refine condQkState_congr_length μ p k _ _ _ (hphrase_len j) _ _ ?_
          intro i
          -- `toFinVec` reads `phrase j` at `i`; `hphrase_get` identifies it with `obs`.
          have hi : (i : ℕ) < N j.succ - N j.castSucc := by
            have := hphrase_len j; have := i.isLt; omega
          simp only [toFinVec]
          rw [hphrase_get j i.val hi]
          rfl
        -- `hpos` / `hlen1` inputs for `condState_grouping_bound_mean`.
        have hpos : ∀ w ∈ phrases,
            0 < (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal := by
          intro w hw
          rw [hphrases_def, Finset.mem_image] at hw
          obtain ⟨j, _, rfl⟩ := hw
          rw [hterm j]
          exact hpphpos j
        have hlen1 : ∀ w ∈ phrases, 1 ≤ w.length := by
          intro w hw
          rw [hphrases_def, Finset.mem_image] at hw
          obtain ⟨j, _, rfl⟩ := hw
          rw [hphrase_len j]
          have := hmono j; omega
        -- Apply the grouping bound on `phrases`.
        have hgroup := condState_grouping_bound_mean μ p k phrases st hpos hlen1 hne
        rw [hcard] at hgroup
        -- Reindex the entropy sum from `phrases` onto `Fin c`.
        have hsum_re :
            (∑ w ∈ phrases,
                -Real.log (condQkState μ p k (st w) w.length (toFinVec w.length w)).toReal)
              = ∑ j : Fin c,
                  -Real.log
                    (condQkState μ p k (windowState p k (N j.castSucc) ω)
                      (N j.succ - N j.castSucc)
                      (fun m => p.obs (N j.castSucc + m.val) ω)).toReal := by
          rw [hphrases_def, Finset.sum_image hInjOn]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hterm j]
        -- Reindex the total length `∑ |w| = ∑ (N j.succ - N j.castSucc) = Ntot`.
        have hNtot_re : (∑ w ∈ phrases, (w.length : ℝ)) = (Ntot : ℝ) := by
          rw [hphrases_def, Finset.sum_image hInjOn, hNtot_def]
          push_cast
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hphrase_len j]
        rw [hsum_re, hNtot_re] at hgroup
        exact hgroup
    linarith

end InformationTheory.Shannon
