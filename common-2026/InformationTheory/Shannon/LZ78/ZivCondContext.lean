import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LZ78.ZivEntropyBridge
import InformationTheory.Shannon.Stationary.Kernel
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# LZ78 conditional-context sub-distribution (node-context route)

This file supplies the first measure-theoretic atom of the **conditional-context**
route for the LZ78 achievability wall `ziv_aseventual_le_blockLogAvg₂`
(`InformationTheory/Shannon/LZ78/AsymptoticOptimality.lean`,
slug `lz78-aseventual-ziv`).

## Background

The two simple grouping routes are ruled out: node-position grouping (the
overhead trap) and marginal-length grouping (`ZivMeasureBridge.lean`, the
direction is wrong since `∑ -log P_marginal ≥ -log Pₙ` for sources with memory).
The genuine surviving structure is the **conditional** sub-distribution
`q(symbol | context)`, which reaches `-log Pₙ` via the chain rule. The first
building block of that route is the per-context (fixed-tuple) conditional
sub-distribution `∑_a q(v · a | v) ≤ 1`.

## Main definitions

* `condContextProb` — the fixed-tuple conditional probability
  `q(v, a) = P(blockRV (m+1) = Fin.snoc v a) / P(blockRV m = v)`, the
  ω-independent node-context conditional (NOT the path-prefix `condPhraseProb`,
  which is observation-dependent and a dead start).

## Main results

* `sum_extend_marginal_real_eq` — **Kolmogorov consistency**:
  `∑_a P(blockRV (m+1) = Fin.snoc v a) = P(blockRV m = v)`. The first `m`
  coordinates of `blockRV (m+1)` are `blockRV m`, so the events
  `{blockRV (m+1) = snoc v a}` partition `{blockRV m = v}` disjointly over `a`.
* `condContext_sum_eq_one` / `condContext_sum_le_one` — the per-context
  conditional masses sum to `1` (resp. `≤ 1`) when `0 < P(blockRV m = v)`. This
  is the sub-distribution input the conditional log-sum step consumes.
* `condContext_card_mul_log_le_sum_neg_log` — per-context log-sum step:
  `card S · log (card S) ≤ ∑_{a ∈ S} -log q(v, a)` for a set `S` of symbols with
  positive conditional masses; the conditional analogue of
  `group_card_mul_log_le_sum_neg_log` (`ZivMeasureBridge.lean`).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-! ## Step 1 — Kolmogorov consistency of the extended marginal -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Block-extension fibre identity** (genuine, unconditional): for a fixed
tuple `v : Fin m → α` and symbol `a`, the preimage of the extended cylinder
`{blockRV (m+1) = Fin.snoc v a}` is exactly the set of `ω` whose `m`-block is
`v` and whose time-`m` observation is `a`. -/
theorem blockRV_succ_preimage_snoc
    (μ : Measure Ω) (p : StationaryProcess μ α) (m : ℕ) (v : Fin m → α) (a : α) :
    p.blockRV (m + 1) ⁻¹' {Fin.snoc v a}
      = {ω | p.blockRV m ω = v ∧ p.obs m ω = a} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  -- `blockRV (m+1) ω = snoc v a` iff its init is `v` and its last is `a`.
  rw [← Fin.snoc_init_self (p.blockRV (m + 1) ω), Fin.snoc_inj]
  -- `init (blockRV (m+1) ω) = blockRV m ω` and `blockRV (m+1) ω (last m) = obs m ω`.
  have hinit : Fin.init (p.blockRV (m + 1) ω) = p.blockRV m ω := by
    funext j
    simp only [Fin.init, StationaryProcess.blockRV, Fin.val_castSucc]
  have hlast : p.blockRV (m + 1) ω (Fin.last m) = p.obs m ω := by
    simp only [StationaryProcess.blockRV, Fin.val_last]
  rw [hinit, hlast]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Disjoint cover**: over the symbol `a`, the extended-cylinder preimages
`{blockRV (m+1) = Fin.snoc v a}` partition the `m`-block cylinder
`{blockRV m = v}`. -/
theorem blockRV_succ_preimage_iUnion_eq
    (μ : Measure Ω) (p : StationaryProcess μ α) (m : ℕ) (v : Fin m → α) :
    (⋃ a ∈ (Finset.univ : Finset α), p.blockRV (m + 1) ⁻¹' {Fin.snoc v a})
      = p.blockRV m ⁻¹' {v} := by
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_univ, Set.iUnion_true,
    blockRV_succ_preimage_snoc, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, hv, _⟩; exact hv
  · intro hv; exact ⟨p.obs m ω, hv, rfl⟩

omit [DecidableEq α] [Nonempty α] in
/-- **Kolmogorov consistency** (genuine, unconditional): the extended length-`m+1`
marginals over the last symbol sum to the length-`m` marginal,
`∑_a P(blockRV (m+1) = Fin.snoc v a) = P(blockRV m = v)`. The first `m`
coordinates of `blockRV (m+1)` agree with `blockRV m`, so the extended cylinders
form a disjoint partition of the `m`-block cylinder; finite additivity of the
pushforward gives the identity. This is the conditional analogue of the marginal
sub-distribution `sum_marginal_real_le_one` (`ZivMeasureBridge.lean`). -/
theorem sum_extend_marginal_real_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (m : ℕ) (v : Fin m → α) :
    (∑ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a})
      = (μ.map (p.blockRV m)).real {v} := by
  classical
  -- Each pushforward singleton mass is the μ-measure of its preimage cylinder.
  have hpush : ∀ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
      = μ.real (p.blockRV (m + 1) ⁻¹' {Fin.snoc v a}) := fun a ↦
    map_measureReal_apply (p.measurable_blockRV (m + 1)) (measurableSet_singleton _)
  simp only [hpush]
  -- The preimage cylinders are pairwise disjoint (injectivity of `snoc v`).
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset α))
      (fun a : α ↦ p.blockRV (m + 1) ⁻¹' {Fin.snoc v a}) := by
    intro a _ b _ hab
    have hsing : Disjoint ({Fin.snoc v a} : Set (Fin (m + 1) → α)) {Fin.snoc v b} :=
      Set.disjoint_singleton.mpr (fun h ↦ hab (Fin.snoc_inj.mp h).2)
    exact hsing.preimage _
  have hmeas : ∀ a ∈ (Finset.univ : Finset α),
      MeasurableSet (p.blockRV (m + 1) ⁻¹' {Fin.snoc v a}) := fun a _ ↦
    (p.measurable_blockRV (m + 1)) (measurableSet_singleton _)
  -- Finite additivity collapses the sum into the measure of the disjoint union.
  rw [← measureReal_biUnion_finset hdisj hmeas]
  -- The disjoint union is the `m`-block cylinder.
  rw [blockRV_succ_preimage_iUnion_eq μ p m v]
  -- which is the μ-measure of the `m`-block preimage = the length-`m` marginal.
  rw [← map_measureReal_apply (p.measurable_blockRV m) (measurableSet_singleton _)]

omit [DecidableEq α] [Nonempty α] in
/-- **Extended-marginal sub-distribution bound**: a `≤` form of consistency, the
input the per-context log-sum step needs. -/
theorem sum_extend_marginal_real_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (m : ℕ) (v : Fin m → α) :
    (∑ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a})
      ≤ (μ.map (p.blockRV m)).real {v} :=
  le_of_eq (sum_extend_marginal_real_eq μ p m v)

/-! ## Step 2 — conditional sub-distribution -/

/-- **Fixed-tuple conditional probability** `q(v, a)` (node-context, ω-independent):
the conditional mass of the extended block `Fin.snoc v a` given the context block
`v`, `q(v, a) = P(blockRV (m+1) = Fin.snoc v a) / P(blockRV m = v)`.

This is the genuine conditional `q(symbol | context)` the LZ78 achievability
chain rule requires — NOT the path-prefix ratio `condPhraseProb`, which is
observation-dependent and a dead start (`∑ⱼ qⱼ ≈ c`). -/
noncomputable def condContextProb
    (μ : Measure Ω) (p : StationaryProcess μ α)
    {m : ℕ} (v : Fin m → α) (a : α) : ℝ :=
  (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
    / (μ.map (p.blockRV m)).real {v}

omit [DecidableEq α] [Nonempty α] in
/-- **Per-context normalization**: when the context mass `P(blockRV m = v)` is
strictly positive, the conditional masses sum to `1`. Immediate from Kolmogorov
consistency `sum_extend_marginal_real_eq`. -/
theorem condContext_sum_eq_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    {m : ℕ} (v : Fin m → α)
    (hpos : 0 < (μ.map (p.blockRV m)).real {v}) :
    (∑ a : α, condContextProb μ p v a) = 1 := by
  simp only [condContextProb]
  rw [← Finset.sum_div, sum_extend_marginal_real_eq μ p m v, div_self hpos.ne']

omit [DecidableEq α] [Nonempty α] in
/-- **Per-context sub-distribution bound** `∑_a q(v · a | v) ≤ 1`: the genuine
node-context conditional sub-distribution. This is the missing measure-theoretic
piece the conditional log-sum step consumes (the third quantity, neither
marginal nor path-prefix). -/
theorem condContext_sum_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    {m : ℕ} (v : Fin m → α)
    (hpos : 0 < (μ.map (p.blockRV m)).real {v}) :
    (∑ a : α, condContextProb μ p v a) ≤ 1 :=
  le_of_eq (condContext_sum_eq_one μ p v hpos)

/-! ## Step 3 — per-context log-sum step -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Per-context log-sum step**: for a finite set `S` of symbols with strictly
positive conditional masses `q(v, a) > 0` whose masses sum to at most `1`,

```
card S · log (card S) ≤ ∑_{a ∈ S} -log q(v, a).
```

The conditional analogue of `group_card_mul_log_le_sum_neg_log`
(`ZivMeasureBridge.lean`); `log_sum_inequality` with `aᵢ ≡ 1`, `bᵢ = q(v, aᵢ)`. -/
theorem condContext_card_mul_log_le_sum_neg_log
    (μ : Measure Ω) (p : StationaryProcess μ α)
    {m : ℕ} (v : Fin m → α) (S : Finset α)
    (hPpos : ∀ a ∈ S, 0 < condContextProb μ p v a)
    (hPsum : (∑ a ∈ S, condContextProb μ p v a) ≤ 1) :
    (S.card : ℝ) * Real.log (S.card : ℝ)
      ≤ ∑ a ∈ S, - Real.log (condContextProb μ p v a) := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp
  -- `∑ q > 0` from positivity on a nonempty index set.
  have hsumP_pos : 0 < ∑ a ∈ S, condContextProb μ p v a := Finset.sum_pos hPpos hS
  -- log-sum inequality with `a ≡ 1`, `b = condContextProb`.
  have hlog := log_sum_inequality S (fun _ ↦ (1 : ℝ)) (condContextProb μ p v)
    (fun _ _ ↦ zero_le_one) hPpos
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hlog
  -- RHS terms: `1 · log (1 / q a) = -log (q a)`.
  have hrhs : (∑ a ∈ S, (1 : ℝ) * Real.log (1 / condContextProb μ p v a))
      = ∑ a ∈ S, - Real.log (condContextProb μ p v a) := by
    refine Finset.sum_congr rfl (fun a ha ↦ ?_)
    rw [one_mul, Real.log_div one_ne_zero (hPpos a ha).ne', Real.log_one, zero_sub]
  rw [hrhs] at hlog
  refine le_trans ?_ hlog
  -- `card S · log (card S) ≤ card S · log (card S / ∑ q)` since `∑ q ≤ 1`.
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.log_le_log hcard_pos
  rw [le_div_iff₀ hsumP_pos]
  calc (S.card : ℝ) * (∑ a ∈ S, condContextProb μ p v a)
      ≤ (S.card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hPsum (Nat.cast_nonneg _)
    _ = (S.card : ℝ) := mul_one _

/-! ## Step 4 — symbol-by-symbol chain rule (conditional route reaches -log Pₙ) -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Pointwise block-extension: `blockRV (m+1) ω = Fin.snoc (blockRV m ω) (obs m ω)`. -/
theorem blockRV_succ_eq_snoc (p : StationaryProcess μ α) (m : ℕ) (ω : Ω) :
    p.blockRV (m + 1) ω = Fin.snoc (p.blockRV m ω) (p.obs m ω) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [StationaryProcess.blockRV, Fin.snoc_last, Fin.val_last]
  · intro j
    simp only [StationaryProcess.blockRV, Fin.snoc_castSucc, Fin.val_castSucc]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Per-step identity: the node-context conditional along the path equals the
ratio of successive prefix block probabilities,
`condContextProb μ p (blockRV m ω) (obs m ω) = prefixBlockProb (m+1) / prefixBlockProb m`. -/
theorem condContextProb_path_eq_ratio
    (μ : Measure Ω) (p : StationaryProcess μ α) (m : ℕ) (ω : Ω) :
    condContextProb μ p (p.blockRV m ω) (p.obs m ω)
      = prefixBlockProb μ p ω (m + 1) / prefixBlockProb μ p ω m := by
  unfold condContextProb prefixBlockProb
  rw [← blockRV_succ_eq_snoc p m ω]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Symbol-by-symbol chain-rule telescoping** (genuine, equality): the per-path
block probability factorizes as the product of node-context conditionals along
the path, given positivity of the intermediate prefix masses. -/
theorem prod_condContextProb_path_telescope
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω)
    (hpos : ∀ m ≤ n, prefixBlockProb μ p ω m ≠ 0) :
    (∏ m ∈ Finset.range n, condContextProb μ p (p.blockRV m ω) (p.obs m ω))
      = prefixBlockProb μ p ω n := by
  induction n with
  | zero => simp [prefixBlockProb_zero]
  | succ k ih =>
      have hk : ∀ m ≤ k, prefixBlockProb μ p ω m ≠ 0 :=
        fun m hm ↦ hpos m (Nat.le_succ_of_le hm)
      rw [Finset.prod_range_succ, ih hk, condContextProb_path_eq_ratio μ p k ω,
        mul_div_cancel₀ _ (hpos k (Nat.le_succ k))]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Conditional chain rule reaches `-log Pₙ`** (genuine, equality): unlike the
marginal route (direction-mismatched), the node-context conditional sum
reaches the block neg-log-probability exactly,
`∑_{m<n} -log q_cond = -log Pₙ{block ω}`. -/
theorem sum_neg_log_condContextProb_path_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (ω : Ω)
    (hpos : ∀ m ≤ n, prefixBlockProb μ p ω m ≠ 0) :
    (∑ m ∈ Finset.range n,
        - Real.log (condContextProb μ p (p.blockRV m ω) (p.obs m ω)))
      = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω}) := by
  have hne : ∀ m ∈ Finset.range n,
      condContextProb μ p (p.blockRV m ω) (p.obs m ω) ≠ 0 := by
    intro m hm
    have hmn : m < n := Finset.mem_range.mp hm
    rw [condContextProb_path_eq_ratio μ p m ω]
    exact div_ne_zero (hpos (m + 1) hmn) (hpos m hmn.le)
  rw [Finset.sum_neg_distrib, ← Real.log_prod hne,
    prod_condContextProb_path_telescope μ p n ω hpos, prefixBlockProb]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Conditional chain rule = `n · blockLogAvg`** (genuine, equality): the
SMB-controlled quantity. Combined with SMB (`blockLogAvg → entropyRate`), this
connects the conditional-context route to the source entropy limit. -/
theorem sum_neg_log_condContextProb_path_eq_blockLogAvg
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    {n : ℕ} (hn : 0 < n) (ω : Ω)
    (hpos : ∀ m ≤ n, prefixBlockProb μ p ω m ≠ 0) :
    (∑ m ∈ Finset.range n,
        - Real.log (condContextProb μ p (p.blockRV m ω) (p.obs m ω)))
      = (n : ℝ) * blockLogAvg μ p n ω := by
  rw [sum_neg_log_condContextProb_path_eq μ p n ω hpos,
    ← blockLogAvg_eq_neg_log_blockProb μ p hn ω]

end InformationTheory.Shannon
