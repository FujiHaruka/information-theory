import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.AlgoetCover.Core
import InformationTheory.Shannon.LZ78.GreedyLongestPrefix
import Mathlib.Data.Fin.Tuple.Basic

/-!
# LZ78 threading: per-phrase `negLogQk` decomposition (foundation)

This file builds the **threading foundation** for the LZ78 achievability wall
`ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`,
`@residual(wall:lz78-aseventual-ziv)`, route LOCK = `markovFactor`).

The genuine Ziv `(k-state, length)`-grouping (Cover-Thomas Lemma 13.5.5) needs to
identify the `k`-Markov negative log-likelihood of a block,
`negLogQk μ p k n ω = ∑_{i<n} pmfLogCondMarkov μ p k i ω` (`Core.lean:200`),
with a sum over the LZ phrases, where the contribution of a phrase is read off
the per-`k`-state conditional product `condQkState μ p k s ℓ` (`Core.lean:490`).

## Approach (gateway-atom-first)

The decisive linchpin is **position invariance** of the per-step factor:
`markovFactor_eq_of_window_eq` (`Core.lean:465`) says that, for positions `> k`,
`markovFactor μ p k n y` depends only on the trailing `k+1` symbols of `y`. The
factors entering `negLogQk` at absolute positions are
`markovFactor μ p k i (blockRV (i+1) ω)`; the factors entering
`condQk μ p k start z` at relative position `m` are
`markovFactor μ p k (start+m) (Fin.append z w ∘ Fin.cast)`. Because both feeds are
ultimately the *same* trailing-window kernel singleton, a phrase block read at any
absolute position `N ≥ k` reproduces the conditional product started from its
trailing `k`-state — with only the leading `k` positions of the whole block as
boundary (`O(k)`).

This file proves that factor-level correspondence, assembles the per-phrase
`negLogQk`-segment identity, and assembles the full block threading decomposition
`negLogQk_phrase_threading` (sorryAx-free, conditional on an explicit tiling +
per-position positivity supplied as regularity hypotheses). The tiling itself —
turning the `List (List α)` greedy parse into an absolute-position `Fin`-tiling of
the block (materializing `N`, `c`, and the tiling hypotheses) — is supplied a.s. by
the `lz78_block_tiling` atom, now **sorryAx-free**: the deterministic position
tiling `lz78_parse_tiling_positions` (`GreedyLongestPrefix.lean`) supplies the
length-only conjuncts and `markovFactor_blockRV_pos_ae` (`Core.lean`) supplies the
a.s. per-position positivity. The remaining LZ78 achievability blocker
(`@residual(wall:lz78-aseventual-ziv)`) is downstream: composing this a.s. threading
identity with the Ziv `c·log c` counting and the SMB rate, plus the boundary-length
sub-blocker (`b ≤ k + Lmax`, `n - e ≤ Lmax`) noted on `lz78_block_tiling`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {μ : Measure Ω}

/-! ## Trailing-window state of a block at an absolute position -/

/-- The trailing `k`-state of the infinite trajectory just before absolute
position `N` (i.e. the symbols at positions `N-k, …, N-1`), read off `blockRV`.
This is the `k`-state `s : Fin k → α` that conditions a phrase starting at
position `N`. Defined via `obs` so it is position-coherent with `blockRV`
(`blockRV m ω j = obs j ω` for any `m`). -/
noncomputable def windowState
    (p : StationaryProcess μ α) (k N : ℕ) (ω : Ω) : Fin k → α :=
  fun j => p.obs (N - k + j.val) ω

/-! ## Gateway atom — single-factor absolute↔relative correspondence -/

omit [DecidableEq α] in
/-- **Gateway atom (single-factor position correspondence).** Let a phrase start
at absolute position `N` with `k ≤ N`, and consider its offset `m`. The
per-position factor entering `negLogQk` at the absolute position `N + m`,
`markovFactor μ p k (N+m) (blockRV (N+m+1) ω)`, equals the factor entering the
conditional product `condQk` started from the trailing `k`-state
`s = windowState p k N ω`, namely `markovFactor μ p k (k+m) t` for the
`condQk`-shaped tuple `t = Fin.append s w ∘ Fin.cast` whose continuation `w`
matches the block on the phrase window.

Both positions `N+m` and `k+m` exceed `k` once `m ≥ 1` (and the `m = 0` case
reduces both branches to the full-prefix kernel `condDistrib (obs k) (blockRV k)`),
so `markovFactor_eq_of_window_eq` applies after checking the window/last
coincidence. This is the linchpin of the whole threading decomposition. -/
lemma markovFactor_blockRV_eq_window
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (k N m : ℕ) (hkN : k < N) (ω : Ω)
    (s : Fin k → α) (w : Fin (m + 1) → α)
    (hs : s = windowState p k N ω)
    (hw : ∀ j : Fin (m + 1), w j = p.obs (N + j.val) ω) :
    markovFactor μ p k (N + m) (p.blockRV (N + m + 1) ω)
      = markovFactor μ p k (k + m)
          (Fin.append s w ∘ Fin.cast (by omega : k + (m + 1) = k + m + 1)) := by
  -- Abbreviate the RHS tuple.
  set t : Fin (k + m + 1) → α :=
    Fin.append s w ∘ Fin.cast (by omega : k + (m + 1) = k + m + 1) with ht_def
  -- Pointwise evaluation of `t` at an index given by its natural value.
  have ht_lt : ∀ (i : ℕ) (hi : i < k + m + 1) (hik : i < k),
      t ⟨i, hi⟩ = s ⟨i, hik⟩ := by
    intro i hi hik
    have hcasti : (Fin.cast (by omega : k + (m + 1) = k + m + 1) ⟨i, hi⟩ : Fin (k + (m + 1)))
        = Fin.castAdd (m + 1) ⟨i, hik⟩ := by
      apply Fin.ext; simp [Fin.castAdd]
    simp only [ht_def, Function.comp_apply, hcasti, Fin.append_left]
  have ht_ge : ∀ (i : ℕ) (hi : i < k + m + 1) (hik : k ≤ i),
      t ⟨i, hi⟩ = w ⟨i - k, by omega⟩ := by
    intro i hi hik
    have hcasti : (Fin.cast (by omega : k + (m + 1) = k + m + 1) ⟨i, hi⟩ : Fin (k + (m + 1)))
        = Fin.natAdd k ⟨i - k, by omega⟩ := by
      apply Fin.ext; simp [Fin.natAdd]; omega
    simp only [ht_def, Function.comp_apply, hcasti, Fin.append_right]
  -- The last coordinate of `t` is `w ⟨m⟩ = obs (N + m) ω`.
  have ht_last : t (Fin.last (k + m)) = p.obs (N + m) ω := by
    rw [show (Fin.last (k + m) : Fin (k + m + 1)) = ⟨k + m, by omega⟩ from rfl,
      ht_ge (k + m) (by omega) (by omega)]
    have hwm := hw ⟨m, by omega⟩
    rw [show (⟨k + m - k, by omega⟩ : Fin (m + 1)) = (⟨m, by omega⟩ : Fin (m + 1)) from by
      apply Fin.ext; simp only [Nat.add_sub_cancel_left]]
    simpa using hwm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- Boundary `m = 0`: RHS sits at position `k` (full-prefix branch), LHS at `N > k`
    -- (window branch); both use kernel `condDistrib (obs k) (blockRV k)`.
    subst hm0
    -- LHS: position `N > k`, so the window branch. RHS: position `k ≤ k`, full prefix.
    simp only [Nat.add_zero] at *
    unfold markovFactor
    rw [dif_neg (Nat.not_le.mpr hkN), dif_pos (le_refl k)]
    -- Match kernel arguments and singleton sets.
    congr 1
    · -- Window prefix of LHS equals `Fin.init t`.
      congr 1
      funext j
      show p.blockRV (N + 1) ω ⟨N - k + j.val, by have := j.isLt; omega⟩
          = Fin.init t j
      have hL : p.blockRV (N + 1) ω ⟨N - k + j.val, by have := j.isLt; omega⟩
          = p.obs (N - k + j.val) ω := rfl
      rw [hL, Fin.init]
      rw [show (Fin.castSucc j : Fin (k + 1)) = ⟨j.val, by have := j.isLt; omega⟩ from by
        apply Fin.ext; simp,
        ht_lt j.val (by have := j.isLt; omega) j.isLt, hs]
      rfl
    · -- Last symbols agree.
      show {p.blockRV (N + 1) ω (Fin.last N)} = {t (Fin.last k)}
      rw [ht_last]
      rfl
  · -- Main case `m ≥ 1`: both positions exceed `k`; apply position invariance.
    refine markovFactor_eq_of_window_eq μ p k (by omega) (by omega) _ _ ?_ ?_
    · -- Window coincidence.
      intro j
      -- LHS window index: `obs ((N+m) - k + j) ω`.
      show p.blockRV (N + m + 1) ω ⟨N + m - k + j.val, by have := j.isLt; omega⟩
          = t ⟨k + m - k + j.val, by have := j.isLt; omega⟩
      have hL : p.blockRV (N + m + 1) ω ⟨N + m - k + j.val, by have := j.isLt; omega⟩
          = p.obs (N + m - k + j.val) ω := rfl
      rw [hL]
      -- RHS index value: `m + j` (since `k + m - k = m`).
      rw [show (⟨k + m - k + j.val, by have := j.isLt; omega⟩ : Fin (k + m + 1))
            = ⟨m + j.val, by have := j.isLt; omega⟩ from by apply Fin.ext; simp only []; omega]
      by_cases hjk : m + j.val < k
      · rw [ht_lt _ _ hjk, hs]
        show p.obs (N + m - k + j.val) ω = p.obs (N - k + (m + j.val)) ω
        congr 1; omega
      · rw [ht_ge _ _ (by omega), hw]
        show p.obs (N + m - k + j.val) ω = p.obs (N + (m + j.val - k)) ω
        congr 1; omega
    · -- Last-symbol coincidence.
      show p.blockRV (N + m + 1) ω (Fin.last (N + m)) = t (Fin.last (k + m))
      rw [ht_last]
      rfl

/-! ## `pmfLogCondMarkov` as the negative log of a `markovFactor` -/

omit [DecidableEq α] in
/-- For an absolute position `i > k`, the per-step `k`-Markov approximation term
`pmfLogCondMarkov μ p k i ω` (entering `negLogQk`) is exactly the negative log of
the `markovFactor` read off the block: `pmfLogCondMarkov μ p k i ω =
- log (markovFactor μ p k i (blockRV (i+1) ω)).toReal`. This is the deterministic
bridge identifying each `negLogQk` term with a `markovFactor`, the form the
gateway atom `markovFactor_blockRV_eq_window` rewrites. -/
lemma pmfLogCondMarkov_eq_neg_log_markovFactor
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (k i : ℕ) (hki : k < i) (ω : Ω) :
    pmfLogCondMarkov μ p k i ω
      = - Real.log (markovFactor μ p k i (p.blockRV (i + 1) ω)).toReal := by
  -- For `i > k`, `pmfLogCondMarkov k i ω = pmfLogCond μ p k (T^[i-k] ω)`.
  have hmarkov_eq : pmfLogCondMarkov μ p k i ω = pmfLogCond μ p k (p.T^[i - k] ω) := by
    unfold pmfLogCondMarkov
    simp [Nat.not_le.mpr hki]
  rw [hmarkov_eq]
  -- `pmfLogCond μ p k (T^[i-k] ω) = -log ((cd (obs k) (blockRV k) μ (blockRV k (T^[i-k] ω))).real {obs k (T^[i-k] ω)})`.
  unfold pmfLogCond
  congr 2
  -- Identify the kernel singleton with `markovFactor μ p k i (blockRV (i+1) ω)`.
  have hki' : k ≤ i := hki.le
  unfold markovFactor
  rw [dif_neg (Nat.not_le.mpr hki)]
  -- Window prefix: `fun j => blockRV (i+1) ω ⟨i-k+j⟩ = blockRV k (T^[i-k] ω)`.
  have h_arg : (fun j : Fin k => p.blockRV (i + 1) ω
        ⟨i - k + j.val, by have := j.isLt; omega⟩)
      = p.blockRV k (p.T^[i - k] ω) := by
    funext j
    show p.obs (i - k + j.val) ω = p.obs j.val (p.T^[i - k] ω)
    unfold StationaryProcess.obs
    show p.X (p.T^[i - k + j.val] ω) = p.X (p.T^[j.val] (p.T^[i - k] ω))
    rw [← Function.iterate_add_apply p.T j.val (i - k) ω, Nat.add_comm j.val (i - k)]
  have h_last : p.blockRV (i + 1) ω (Fin.last i) = p.obs k (p.T^[i - k] ω) := by
    show p.obs i ω = p.obs k (p.T^[i - k] ω)
    unfold StationaryProcess.obs
    show p.X (p.T^[i] ω) = p.X (p.T^[k] (p.T^[i - k] ω))
    rw [← Function.iterate_add_apply]
    congr 2
    omega
  rw [h_arg, h_last]
  rfl

omit [DecidableEq α] in
/-- **Product form of `condQk` along a block segment.** When the continuation `Z`
matches the block on the phrase window (`Z j = obs (N+j) ω`) and the trailing
`k`-state `s` is `windowState p k N ω`, the conditional product
`condQk μ p k k s ℓ Z` equals the product of the absolute-position `markovFactor`s
over the phrase positions `N, …, N+ℓ-1`. Proved by induction on `ℓ` using the
gateway atom `markovFactor_blockRV_eq_window` at each peeled factor (the
`condQk` recursion peels the offset-`ℓ` factor; the gateway atom rewrites the
relative-position factor to the absolute one). -/
lemma condQk_eq_prod_markovFactor
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (k N : ℕ) (hkN : k < N) (ω : Ω)
    (s : Fin k → α) (hs : s = windowState p k N ω) :
    ∀ (ℓ : ℕ) (Z : Fin ℓ → α), (∀ j : Fin ℓ, Z j = p.obs (N + j.val) ω) →
      condQk μ p k k s ℓ Z
        = ∏ m ∈ Finset.range ℓ,
            markovFactor μ p k (N + m) (p.blockRV (N + m + 1) ω) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro Z _
    simp [condQk]
  | succ ℓ ih =>
    intro Z hZ
    -- Peel the offset-`ℓ` factor.
    have hrec : condQk μ p k k s (ℓ + 1) Z
        = condQk μ p k k s ℓ (Fin.init Z)
          * markovFactor μ p k (k + ℓ)
              (Fin.append s Z ∘ Fin.cast (by omega)) := rfl
    rw [hrec]
    -- IH on the truncated continuation.
    have hZinit : ∀ j : Fin ℓ, Fin.init Z j = p.obs (N + j.val) ω := by
      intro j
      rw [Fin.init]
      have := hZ (Fin.castSucc j)
      simpa using this
    rw [ih (Fin.init Z) hZinit]
    -- Rewrite the peeled factor via the gateway atom.
    have hgate := markovFactor_blockRV_eq_window μ p k N ℓ hkN ω s Z hs hZ
    rw [Finset.prod_range_succ, ← hgate]

/-! ## Per-phrase `negLogQk`-segment identity -/

omit [DecidableEq α] in
/-- **Per-phrase segment identity.** A phrase of length `ℓ` starting at absolute
position `N > k` contributes, to `negLogQk μ p k (N+ℓ) ω`, exactly the negative
log of the per-`k`-state conditional product `condQkState μ p k s ℓ Z` of the
phrase content `Z`, where `s` is the trailing `k`-state at `N`. Concretely:

`∑_{m<ℓ} pmfLogCondMarkov μ p k (N+m) ω = - log (condQkState μ p k s ℓ Z).toReal`,

i.e. the block of factors of `negLogQk` over the phrase positions telescopes to a
single `condQkState` entry. This is the per-phrase atom the `(k-state, length)`
grouping consumes; it follows from the single-factor correspondence
`markovFactor_blockRV_eq_window` applied position-by-position, plus the recursive
shape shared by `negLogQk` and `condQk` (both products / sums of the same
`markovFactor`s).

The positivity hypothesis `hposfac` (each per-position `markovFactor` is `> 0`) is
the genuine regularity input: it is `cond_singleton_pos_ae` along the phrase
positions, and is needed only to move `-log` through the product. It is a
precondition, not the proof core (which is the deterministic factor correspondence
already in `markovFactor_blockRV_eq_window`). Proved here (sorryAx-free) from the
gateway atom + `condQk_eq_prod_markovFactor`; no residual. -/
lemma negLogQk_segment_eq_condQkState
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k N ℓ : ℕ) (hkN : k < N) (ω : Ω)
    (s : Fin k → α) (Z : Fin ℓ → α)
    (hs : s = windowState p k N ω)
    (hZ : ∀ j : Fin ℓ, Z j = p.obs (N + j.val) ω)
    (hposfac : ∀ m < ℓ,
      0 < (markovFactor μ p k (N + m) (p.blockRV (N + m + 1) ω)).toReal) :
    (∑ m ∈ Finset.range ℓ, pmfLogCondMarkov μ p k (N + m) ω)
      = - Real.log (condQkState μ p k s ℓ Z).toReal := by
  classical
  -- Abbreviate the per-position absolute-block factor.
  set f : ℕ → ℝ := fun m => (markovFactor μ p k (N + m) (p.blockRV (N + m + 1) ω)).toReal
    with hf_def
  -- Each `negLogQk` term is `-log` of the corresponding factor (bridge).
  have hterm : ∀ m ∈ Finset.range ℓ,
      pmfLogCondMarkov μ p k (N + m) ω = - Real.log (f m) := by
    intro m _
    rw [hf_def]
    exact pmfLogCondMarkov_eq_neg_log_markovFactor μ p k (N + m) (by omega) ω
  rw [Finset.sum_congr rfl hterm]
  -- `∑ -log f m = -log (∏ f m)` by positivity.
  rw [Finset.sum_neg_distrib]
  -- Reduce to `∑ log (f m) = log (condQkState ...).toReal`.
  congr 1
  have hlogprod : ∑ m ∈ Finset.range ℓ, Real.log (f m)
      = Real.log (∏ m ∈ Finset.range ℓ, f m) := by
    rw [Real.log_prod (s := Finset.range ℓ) (f := f) (fun m hm => by
      have hpm := hposfac m (Finset.mem_range.mp hm)
      exact ne_of_gt hpm)]
  rw [hlogprod]
  -- `∏ f m = (condQkState μ p k s ℓ Z).toReal` via `condQk_eq_prod_markovFactor`.
  congr 1
  unfold condQkState
  rw [condQk_eq_prod_markovFactor μ p k N hkN ω s hs ℓ Z hZ, hf_def, ENNReal.toReal_prod]

/-! ## Threading decomposition (genuine blocker: List↔Fin tiling) -/

/-- **Telescoping of an `Ico` over a monotone partition.** For a monotone
`M : ℕ → ℕ` (`M i ≤ M (i+1)`) and any `g : ℕ → β` valued in an additive commutative
monoid, the interval `[M 0, M c)` splits as the sum over `j < c` of the consecutive
pieces `[M j, M (j+1))`. Pure `Finset` bookkeeping (induction on `c` via
`Finset.sum_Ico_consecutive`); used to turn the LZ tiling into the per-phrase sum. -/
lemma sum_Ico_telescope_of_monotone {β : Type*} [AddCommMonoid β]
    (M : ℕ → ℕ) (hM : ∀ i, M i ≤ M (i + 1)) (g : ℕ → β) :
    ∀ c : ℕ, (∑ i ∈ Finset.Ico (M 0) (M c), g i)
      = ∑ j ∈ Finset.range c, ∑ i ∈ Finset.Ico (M j) (M (j + 1)), g i := by
  intro c
  induction c with
  | zero => simp
  | succ c ih =>
    have hmono_le : ∀ i j, i ≤ j → M i ≤ M j := by
      intro i j hij
      induction j with
      | zero => simp_all
      | succ j ihj =>
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact (ihj (Nat.lt_succ_iff.mp h)).trans (hM j)
        · have : i = j + 1 := le_antisymm hij h
          subst this; exact le_refl _
    rw [Finset.sum_range_succ, ← ih,
      Finset.sum_Ico_consecutive g (hmono_le 0 c (Nat.zero_le c)) (hM c)]

omit [DecidableEq α] in
/-- **Threading decomposition (target of this leg).** Given an explicit tiling of a
prefix `[0, e)` of the block `[0, n)` into a leading boundary `[0, N 0)` and `c` phrase
segments `[N j, N (j+1))` (encoded by a monotone `N : Fin (c+1) → ℕ`, `N 0 = b` the
leading-boundary length, `N (Fin.last c) = e ≤ n` the parse-covered length, and each
phrase start `> k`), plus a trailing boundary `[e, n)` for the unfinished tail, the
`k`-Markov negative log-likelihood `negLogQk μ p k n ω` splits as the leading-boundary
contribution over `[0, b)`, plus the sum over phrases of the per-phrase conditional
contributions `- log (condQkState μ p k sⱼ ℓⱼ Zⱼ).toReal` (supplied by
`negLogQk_segment_eq_condQkState`), plus the trailing-boundary contribution over `[e, n)`.

The tiling hypotheses (`hNb` leading-boundary start, `hNe` parse-covered length, `hen`
the `≤`-slack, `hmono` strict monotonicity giving a contiguous partition of `[b, e)`,
`hstart` each phrase start `> k`) record the position bookkeeping as a *regularity* input
describing the LZ parse — the plain combinatorial structure of `lz78PhraseStrings`, not
the proof core (which is the factor-level correspondence already established in
`markovFactor_blockRV_eq_window` / `negLogQk_segment_eq_condQkState`). The positivity
input `hposfac` (each per-position `markovFactor` along a phrase is `> 0`) is the genuine
regularity precondition of `negLogQk_segment_eq_condQkState`, needed only to move `-log`
through the product; it is `cond_singleton_pos_ae` along the phrase positions, not the
proof core.

The body is filled (sorryAx-free under these tiling/positivity regularity hypotheses):
the `negLogQk` sum over `[0, n)` is split into `[0, b) ∪ [b, e) ∪ [e, n)`; the middle
`[b, e) = [N 0, N (last c))` is telescoped over the partition by
`sum_Ico_telescope_of_monotone`, each piece is reindexed to a phrase-local sum by
`Finset.sum_Ico_eq_sum_range`, and the per-phrase sum is discharged by
`negLogQk_segment_eq_condQkState`. The trailing `[e, n)` remains as the unfinished-tail
boundary term.

The remaining **genuine blocker** is producing this tiling from the actual greedy parse;
see `lz78_block_tiling` below. The reconstruction invariant
`lz78PhraseStrings_flatten_prefix` (parse phrases concatenate to a prefix of the input,
sorryAx-free) furnishes the cumulative-position function; the residual sub-blockers are
the per-phrase substring coherence (read phrase `j` off `obs` at its cumulative position),
the leading-`k` boundary absorption, and the trailing-tail length `n - e`.

Independent honesty audit (2026-06-21): body fill is sorryAx-free
(`#print axioms = [propext, Classical.choice, Quot.sound]`, fresh-olean machine check).
The signature additions vs. the prior leg are all regularity, not core bundling: `hstart`
(each phrase start `> k`) and `hmono` are partition bookkeeping; `hposfac` (per-position
`markovFactor > 0`) is the `cond_singleton_pos_ae` precondition of
`negLogQk_segment_eq_condQkState` needed only to move `-log` through the product; the
trailing-boundary generalization (`hNe : N (last c) = e`, `hen : e ≤ n`, plus the `[e, n)`
term) relaxes the prior `N (last) = n` constraint and adds no core. The conclusion is an
*exact equality* assembled by interval-split + telescope + the established factor
correspondence — no hypothesis carries the conclusion. @audit:ok (non-circular,
non-bundled, sorryAx-free). -/
lemma negLogQk_phrase_threading
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k n b c e : ℕ) (ω : Ω)
    (N : Fin (c + 1) → ℕ) (hNb : N 0 = b) (hNe : N (Fin.last c) = e) (hen : e ≤ n)
    (hmono : ∀ j : Fin c, N j.castSucc + 1 ≤ N j.succ)
    (hstart : ∀ j : Fin c, k < N j.castSucc)
    (hposfac : ∀ (j : Fin c) (m : ℕ), m < N j.succ - N j.castSucc →
      0 < (markovFactor μ p k (N j.castSucc + m)
            (p.blockRV (N j.castSucc + m + 1) ω)).toReal) :
    negLogQk μ p k n ω
      = (∑ i ∈ Finset.range b, pmfLogCondMarkov μ p k i ω)
        + (∑ j : Fin c,
            - Real.log
              (condQkState μ p k (windowState p k (N j.castSucc) ω)
                (N j.succ - N j.castSucc)
                (fun m => p.obs (N j.castSucc + m.val) ω)).toReal)
        + ∑ i ∈ Finset.Ico e n, pmfLogCondMarkov μ p k i ω := by
  classical
  set f : ℕ → ℝ := fun i => pmfLogCondMarkov μ p k i ω with hf_def
  -- Extend `N` to a total monotone `M : ℕ → ℕ` so the telescoping helper applies.
  -- Off-grid values are pinned to `e = N (last c)` so `M c = e`.
  set M : ℕ → ℕ := fun i => if h : i < c + 1 then N ⟨i, h⟩ else e with hM_def
  -- `M` agrees with `N` on `Fin (c+1)`.
  have hMN : ∀ (i : ℕ) (h : i < c + 1), M i = N ⟨i, h⟩ := by
    intro i h; simp only [hM_def, h, dif_pos]
  -- For `j < c`, the partition endpoints are the phrase start/end.
  have hMcastSucc : ∀ j : Fin c, M j.val = N j.castSucc := by
    intro j; rw [hMN j.val (by omega)]; congr 1
  have hMsucc : ∀ j : Fin c, M (j.val + 1) = N j.succ := by
    intro j; rw [hMN (j.val + 1) (by omega)]; congr 1
  -- Endpoints of the partitioned prefix `[b, e)`.
  have hM0 : M 0 = b := by rw [hMN 0 (by omega), ← hNb]; congr 1
  have hMc : M c = e := by rw [hMN c (by omega), ← hNe]; congr 1
  -- Monotonicity of `M`.
  have hMmono : ∀ i, M i ≤ M (i + 1) := by
    intro i
    by_cases hic : i + 1 < c + 1
    · -- both `i` and `i+1` index into `N`; use `hmono` at the `Fin c` slot `i`.
      have hi : i < c := by omega
      have h1 : M i = N (⟨i, hi⟩ : Fin c).castSucc := hMN i (by omega)
      have h2 : M (i + 1) = N (⟨i, hi⟩ : Fin c).succ := hMN (i + 1) (by omega)
      rw [h1, h2]; exact le_of_lt (hmono ⟨i, hi⟩)
    · -- `i + 1 ≥ c + 1`, so `M (i+1) = e`. Either `M i = e` too, or `i = c`.
      have hMi1 : M (i + 1) = e := by
        simp only [hM_def, Nat.not_lt.mpr (Nat.not_lt.mp hic), dif_neg, not_false_eq_true]
      rcases Nat.lt_or_ge i (c + 1) with hi | hi
      · -- `i < c + 1 ≤ i + 1`, so `i = c`, hence `M i = e` and `M (i+1) = e`.
        have hieq : i = c := by omega
        rw [hMi1, ← hMc, hieq]
      · -- `i ≥ c + 1`, both off the grid.
        have hMi : M i = e := by
          simp only [hM_def, Nat.not_lt.mpr hi, dif_neg, not_false_eq_true]
        rw [hMi, hMi1]
  -- Monotone `M i ≤ M j` for `i ≤ j`.
  have hMmono_le : ∀ i j, i ≤ j → M i ≤ M j := by
    intro i j hij
    induction j with
    | zero => simp_all
    | succ j ihj =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ihj (Nat.lt_succ_iff.mp h)).trans (hMmono j)
      · have : i = j + 1 := le_antisymm hij h
        subst this; exact le_refl _
  have hbe : b ≤ e := by rw [← hM0, ← hMc]; exact hMmono_le 0 c (Nat.zero_le c)
  have hbn : b ≤ n := hbe.trans hen
  -- Step 1: `negLogQk = ∑ over [0,n)`.
  rw [show negLogQk μ p k n ω = ∑ i ∈ Finset.range n, f i from rfl]
  -- Step 2: split `[0,n)` into `[0,b) ∪ [b,n)`, then `[b,n)` into `[b,e) ∪ [e,n)`.
  rw [← Finset.sum_range_add_sum_Ico f hbn, ← Finset.sum_Ico_consecutive f hbe hen]
  -- Reassociate: (boundary + Ico b e) + Ico e n matches the target shape.
  rw [← add_assoc]
  -- The leading-boundary sum and trailing `[e,n)` sum are already in target form;
  -- discharge the middle `[b, e)` to the phrase sum.
  congr 2
  -- Step 3: telescope `[b, e) = [M 0, M c)` over the partition.
  rw [show b = M 0 from hM0.symm, show e = M c from hMc.symm,
    sum_Ico_telescope_of_monotone M hMmono f c]
  -- Step 4: convert `∑ j ∈ range c` to `∑ j : Fin c` and discharge each piece.
  rw [Finset.sum_range fun j => ∑ i ∈ Finset.Ico (M j) (M (j + 1)), f i]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Identify the partition endpoints with the phrase start/end.
  rw [hMcastSucc j, hMsucc j]
  -- Reindex `[N j.castSucc, N j.succ)` to a phrase-local `range (ℓ)` sum.
  rw [Finset.sum_Ico_eq_sum_range]
  -- The phrase length.
  set ℓ : ℕ := N j.succ - N j.castSucc with hℓ_def
  -- Apply the per-phrase segment identity. `f (N j.castSucc + i) = pmfLogCondMarkov ...`.
  have hseg := negLogQk_segment_eq_condQkState μ p k (N j.castSucc) ℓ
    (hstart j) ω (windowState p k (N j.castSucc) ω)
    (fun m => p.obs (N j.castSucc + m.val) ω) rfl (fun _ => rfl)
    (fun m hm => hposfac j m hm)
  rw [← hseg]

/-! ## Tiling materialization from the greedy parse (genuine blocker) -/

/-- **Tiling materialization from the LZ parse (a.s. threading input).** For the
block `blockRV n ω`, the greedy longest-prefix parse
`lz78PhraseStrings (List.ofFn (fun i => blockRV n ω i))` yields, **a.s. in `ω`**, the
absolute-position tiling consumed by `negLogQk_phrase_threading`: a leading boundary
length `b`, a phrase count `c`, a parse-covered length `e ≤ n`, the absorbed-count
`bAbsorbed`, and the cumulative-position function `N : Fin (c+1) → ℕ` with `N 0 = b`,
`N (last c) = e`, the partition `[b, e)` strictly monotone (`hmono`), every phrase
start `> k` (`hstart`, leading phrases below position `k` absorbed into the boundary),
and the per-position positivity `hposfac`. Composing with `negLogQk_phrase_threading`
threads `negLogQk` over the genuine parse.

**Three findings pinned into this signature (vs. the prior per-ω skeleton):**
* **A.s., not per-ω.** The per-position positivity `hposfac` cannot hold for *all* `ω`
  — `markovFactor`'s positivity comes only from `cond_singleton_pos_ae`, an a.s.
  statement. So the whole tiling is an `∀ᵐ ω ∂μ, ∃ …`; positivity is then discharged
  by `markovFactor_blockRV_pos_ae` (Core). The downstream M3/limsup argument is a.s.
  anyway, so an a.s. threading identity is the correct shape.
* **`bAbsorbed ≤ k + 1`, not `≤ k`.** When the leading phrases all have length `1`, the
  least index whose cumulative length exceeds `k` is `k + 1`; the cumulative length
  increases by `≥ 1` per phrase, so at most `k + 1` phrases fit below position `k`.
* **Phrase *content* coherence is unnecessary.** `negLogQk_phrase_threading` reads
  phrase content directly as `fun m => obs (N j.castSucc + m) ω`; it never references
  the parse phrase *strings'* content, only the cumulative-length *positions*. So the
  tiling needs only the phrase **lengths** (via `lz78_parse_tiling_positions`), not a
  `List.flatten`-content-indexing chain.

The deterministic position tiling (`lz78_parse_tiling_positions`,
`GreedyLongestPrefix.lean`, sorryAx-free) supplies `b c e bAbsorbed N` and the
length-only conjuncts (monotonicity, `hstart`, `e ≤ n`, the parse-anchored count, and
`bAbsorbed ≤ k + 1`); `markovFactor_blockRV_pos_ae` (Core, sorryAx-free) supplies the
a.s. per-position positivity. The body assembles these — there is no remaining sorry on
this leg.

**Non-vacuity anchor.** The plain existence of *some* tiling is vacuously true (`c = 0`,
empty partition), so the genuine content is encoded by anchoring the tiling to the
*parse*: the phrase count `c` is the genuine distinct-phrase count of the parse minus the
leading phrases absorbed below position `k`, pinned by `c + bAbsorbed = parseCount` with
the absorbed-count `bAbsorbed ≤ k + 1`. For a long block whose parse has `parseCount > k`
phrases this forces `c > 0`, so the empty-tiling escape is unavailable.

**Boundary-length bounds (supplied, for the W2 limsup discharge).** The threading
identity (`negLogQk_phrase_threading`) leaves the leading-boundary sum over `[0, b)` and
the trailing-tail sum over `[e, n)` as additive terms; the W2 limsup discharge (Phase 3/4)
needs `b / n → 0` and `(n - e) / n → 0` to vanish those boundary contributions. This
signature now carries `b ≤ k + Lmax` and `n - e ≤ Lmax` with `Lmax` the longest phrase
length (from `lz78_parse_tiling_positions`, sorryAx-free): the leading boundary is one
phrase past the `≤ k` absorbed prefix, and the un-emitted trailing tail is one dictionary
phrase or empty (`lz78PhraseStrings_flatten_tail_mem`). For the W2 vanishing, the closure
still needs `Lmax = o(n)` a.s. (the longest LZ78 phrase grows sublinearly), which is part
of the achievability wall, not of this tiling atom. The present lemma is the a.s. threading
mechanism + non-vacuity anchor + boundary-length bounds (genuine, sorryAx-free).

@audit:ok (independent audit 2026-06-21, sorryAx-free `[propext, Classical.choice,
Quot.sound]`; non-circular, non-bundled = only `[IsProbabilityMeasure μ]` regularity +
produces the existential; the a.s. `∀ᵐ ω, ∃ …` shape is the genuinely-provable form
(per-ω positivity is false — it comes only from `cond_singleton_pos_ae`); vs. the prior
per-ω skeleton no conjunct was dropped — every partition/positivity conjunct preserved,
`bAbsorbed ≤ k` relaxed to the provable `≤ k+1`, two W2 boundary conjuncts added;
non-vacuity genuine: `c + bAbsorbed = parseCount ∧ bAbsorbed ≤ k+1` forces `c > 0` for
`parseCount > k+1`; wall slug `lz78-aseventual-ziv` correctly NOT on this closed decl —
it lives at `ziv_aseventual_le_blockLogAvg₂`). -/
lemma lz78_block_tiling
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (k n : ℕ) :
    ∀ᵐ ω ∂μ, ∃ (b c e bAbsorbed Lmax : ℕ) (N : Fin (c + 1) → ℕ),
      -- the partition + boundary regularity consumed by `negLogQk_phrase_threading`
      N 0 = b ∧ N (Fin.last c) = e ∧ e ≤ n ∧
      (∀ j : Fin c, N j.castSucc + 1 ≤ N j.succ) ∧
      (∀ j : Fin c, k < N j.castSucc) ∧
      (∀ (j : Fin c) (m : ℕ), m < N j.succ - N j.castSucc →
        0 < (markovFactor μ p k (N j.castSucc + m)
              (p.blockRV (N j.castSucc + m + 1) ω)).toReal) ∧
      -- non-vacuity: the tiling is the *parse* tiling (phrase count anchored to the
      -- genuine distinct-phrase count, minus `bAbsorbed ≤ k + 1` leading phrases).
      c + bAbsorbed
        = (lz78PhraseStrings (List.ofFn (fun i => p.blockRV n ω i))).length ∧
      bAbsorbed ≤ k + 1 ∧
      -- boundary-length bounds for the W2 limsup discharge (`Lmax` = longest phrase).
      n - e ≤ Lmax ∧
      b ≤ k + Lmax := by
  filter_upwards [markovFactor_blockRV_pos_ae μ p k] with ω hpos
  obtain ⟨b, c, e, bAbsorbed, Lmax, N, hN0, hNlast, he_le, hmono, hstart, hcount, hbA,
    htail, hbb⟩ := lz78_parse_tiling_positions (List.ofFn (fun i => p.blockRV n ω i)) k
  have hlen : (List.ofFn (fun i => p.blockRV n ω i)).length = n := List.length_ofFn
  refine ⟨b, c, e, bAbsorbed, Lmax, N, hN0, hNlast, ?_, hmono, hstart, ?_, hcount, hbA,
    ?_, hbb⟩
  · -- `e ≤ (List.ofFn …).length = n`.
    rwa [hlen] at he_le
  · -- per-position positivity from the a.s. asset.
    intro j m _
    exact hpos (N j.castSucc + m)
  · -- `n - e ≤ Lmax`.
    rwa [hlen] at htail

end InformationTheory.Shannon
