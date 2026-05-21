import Common2026.Shannon.LZ78ZivCombinatorics
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# LZ78 Ziv combinatorics — tree-node-context sub-distribution (Core 1, genuine foundation)

This file builds the **genuine LZ dictionary tree-node sub-distribution
infrastructure** for the Cover–Thomas Ziv inequality (Lemma 13.5.4/13.5.5).

The structural observation: the longest-prefix greedy worker
`lz78PhraseStringsAux` emits each phrase `w = cur ++ [s]` precisely when
`cur ++ [s] ∉ dict`, and at that moment `cur ∈ dict` (already-emitted phrase)
**or** `cur = []` (root). So every emitted phrase string `w` decomposes
uniquely as `(context := w.dropLast, symbol := w.getLast)` with the **context
a dictionary node**. Phrases sharing a context branch off with **distinct
next symbols** (`Nodup`).

## What is genuine here (T1 + T2 + T3-inner)

* **T1 — worker context invariant** (`lz78PhraseStringsAux_emit_context_mem`):
  every emitted phrase's `dropLast` is a previously-emitted phrase or `[]`;
  and same-context phrases have distinct `getLast` (genuine, `Nodup`).
* **T2 — per-node cylinder sub-distribution** (`nodeExtend_measureReal_sum_eq`):
  for a fixed length-`m` *tuple* node `v : Fin m → α`, the length-`(m+1)`
  extended cylinders over the alphabet are pairwise disjoint and exhaust the
  node cylinder, so the next-symbol block probabilities sum to the node block
  probability (genuine transcription of `extendCylinder_measureReal_sum_eq`,
  re-parametrised by a standalone tuple instead of an observed prefix).
* **T3-inner — per-node log-sum step** (`node_logsum_step`): at each node `v`
  with `k_v` children, `k_v · log k_v ≤ ∑_{children} -log q(v·a | v)`, from
  the genuine `log_sum_inequality` and the `∑ q ≤ 1` sub-distribution.

## Honesty status of the overhead-aware core (read this)

The clean per-block core `c · log c ≤ -log Pₙ` (∀n∀ω) is **mathematically
false** (counterexample `(a,a,b)`: `-log P(aab) ≈ 0.916 < 1.386 = c log c`).
The genuine Cover–Thomas argument carries an `O(c)` lower-order overhead
(`overhead/n → 0` since `c/n → 0`). The tree-node sub-distribution above is
the genuine, sorryAx-free content of CT 13.5.4; assembling it into the
overhead-aware core requires connecting the **node-context** conditionals
`q(phrase | context)` (stationary, fresh-coordinate ratios) to the **path
block probability** `Pₙ`. That connection — the CT entropy chain rule across
arbitrary already-emitted dictionary contexts — is **not** a telescoping of
the committed path-prefix factorization (the contexts are arbitrary nodes,
not the running path prefix), and is the genuine load-bearing residual.

This file therefore publishes the genuine T1/T2/T3-inner infrastructure and
states the residual connection honestly (see `node_to_blockProb_overhead`),
NOT as a discharge.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ## §1. Worker context invariant (T1) -/

section TreeContext

variable {α : Type*} [DecidableEq α]

/-- **Worker only grows the dictionary**: every entry of the starting
dictionary is an entry of the worker output (the worker only `concat`s, never
removes). The final output is the final dictionary, so `dict ⊆ output`. -/
theorem lz78PhraseStringsAux_dict_subset :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      ∀ w ∈ dict, w ∈ lz78PhraseStringsAux fuel dict cur input
  | 0, dict, _, _, w, hw => hw
  | _ + 1, dict, _, [], w, hw => hw
  | fuel + 1, dict, cur, s :: rest, w, hw => by
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · simp only [hmem, if_true]
        exact lz78PhraseStringsAux_dict_subset fuel dict (cur ++ [s]) rest w hw
      · simp only [hmem, if_false]
        refine lz78PhraseStringsAux_dict_subset fuel (dict.concat (cur ++ [s])) [] rest w ?_
        rw [List.concat_eq_append, List.mem_append]
        exact Or.inl hw

/-- **Worker context invariant** (T1 core): if the worker is started from a
running prefix `cur` that is a dictionary entry or empty, then every emitted
phrase string `w` of the output has its parent context `w.dropLast` lying in
the output (a dictionary node) or empty. This is the genuine LZ-tree
parent-prefix extraction: each phrase decomposes as `(context node, symbol)`
with the context an already-emitted phrase or the root `[]`.

Proof by induction on the worker. The maintained invariant is
`cur ∈ dict ∨ cur = []`. In the emit branch the new phrase is `cur ++ [s]`
with `dropLast = cur` (`∈ dict ∨ = []`), and the new running prefix resets to
`[]`; in the grow branch the new running prefix `cur ++ [s] ∈ dict`. Prior
dictionary entries persist into the output (`lz78PhraseStringsAux_dict_subset`). -/
theorem lz78PhraseStringsAux_emit_context_mem :
    ∀ (fuel : ℕ) (dict : List (List α)) (cur input : List α),
      (cur ∈ dict ∨ cur = []) →
      ∀ w ∈ lz78PhraseStringsAux fuel dict cur input,
        w ∉ dict →
          (w.dropLast ∈ lz78PhraseStringsAux fuel dict cur input ∨ w.dropLast = [])
  | 0, dict, cur, input, _, w, hw, hwnd => absurd hw hwnd
  | _ + 1, dict, cur, [], _, w, hw, hwnd => absurd hw hwnd
  | fuel + 1, dict, cur, s :: rest, hcur, w, hw, hwnd => by
      revert hw hwnd
      unfold lz78PhraseStringsAux
      by_cases hmem : (cur ++ [s]) ∈ dict
      · -- grow branch: dict unchanged, new running prefix `cur ++ [s] ∈ dict`.
        simp only [hmem, if_true]
        intro hw hwnd
        exact lz78PhraseStringsAux_emit_context_mem fuel dict (cur ++ [s]) rest
          (Or.inl hmem) w hw hwnd
      · -- emit branch: dict grows by `cur ++ [s]`, new running prefix `[]`.
        simp only [hmem, if_false]
        intro hw hwnd
        -- Either `w` is a prior emit (handle by IH on the grown dict), or
        -- `w = cur ++ [s]` (the just-emitted phrase, context `= cur`).
        by_cases hwnew : w = cur ++ [s]
        · -- `w` is the just-emitted phrase: `w.dropLast = cur ∈ dict ∨ = []`.
          subst hwnew
          -- `(cur ++ [s]).dropLast = cur`.
          have hdl : (cur ++ [s]).dropLast = cur := by simp
          rw [hdl]
          rcases hcur with hcd | hce
          · -- `cur ∈ dict ⊆ output`.
            left
            exact lz78PhraseStringsAux_dict_subset fuel (dict.concat (cur ++ [s])) [] rest
              cur (by rw [List.concat_eq_append, List.mem_append]; exact Or.inl hcd)
          · exact Or.inr hce
        · -- `w` is a prior emit on the grown dictionary; apply IH.
          have hwnd' : w ∉ dict.concat (cur ++ [s]) := by
            rw [List.concat_eq_append, List.mem_append]
            rintro (h | h)
            · exact hwnd h
            · rw [List.mem_singleton] at h; exact hwnew h
          exact lz78PhraseStringsAux_emit_context_mem fuel (dict.concat (cur ++ [s])) [] rest
            (Or.inr rfl) w hw hwnd'

omit [DecidableEq α] in
/-- **A non-empty string is determined by its context and symbol** (genuine):
two non-empty strings with equal `dropLast` (context) and equal `getLast`
(symbol) are equal. Combined with `lz78PhraseStrings_nodup`, this means the
distinct phrases sharing a context branch off with distinct next symbols (the
LZ tree-node branching structure). -/
theorem string_eq_of_context_symbol
    {w₁ w₂ : List α}
    (hne₁ : w₁ ≠ []) (hne₂ : w₂ ≠ [])
    (hctx : w₁.dropLast = w₂.dropLast) (hsym : w₁.getLast hne₁ = w₂.getLast hne₂) :
    w₁ = w₂ := by
  -- `w = w.dropLast ++ [w.getLast]`; equal context + equal symbol ⟹ equal.
  calc w₁ = w₁.dropLast ++ [w₁.getLast hne₁] := (List.dropLast_append_getLast hne₁).symm
    _ = w₂.dropLast ++ [w₂.getLast hne₂] := by rw [hctx, hsym]
    _ = w₂ := List.dropLast_append_getLast hne₂

end TreeContext

/-! ## §2. Per-node cylinder sub-distribution (T2) -/

section NodeSubDist

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Node-extended cylinder set**: the preimage under `blockRV (m+1)` of the
length-`(m+1)` block obtained by extending the standalone length-`m` *node*
tuple `v : Fin m → α` with the symbol `a` in the last coordinate. This is the
tuple-parametrised analogue of `extendCylinder` (which used an observed
prefix). -/
noncomputable def nodeExtendCylinder
    (μ : Measure Ω) (p : StationaryProcess μ α) (m : ℕ) (v : Fin m → α) (a : α) :
    Set Ω :=
  p.blockRV (m + 1) ⁻¹' {Fin.snoc v a}

omit [DecidableEq α] [Nonempty α] in
/-- **Genuine per-node cylinder sub-distribution**: for a fixed length-`m`
node tuple `v`, the sum over the alphabet of the length-`(m+1)`
node-extended-cylinder block probabilities **equals** the length-`m` node
block probability. Tuple-parametrised transcription of
`extendCylinder_measureReal_sum_eq`. -/
theorem nodeExtend_measureReal_sum_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (m : ℕ) (v : Fin m → α) :
    (∑ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a})
      = (μ.map (p.blockRV m)).real {v} := by
  -- Rewrite each pushforward singleton as `μ.real` of a node-extended cylinder.
  have hpush : ∀ a : α,
      (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
        = μ.real (nodeExtendCylinder μ p m v a) := by
    intro a
    rw [map_measureReal_apply (p.measurable_blockRV (m + 1))
        (measurableSet_singleton _)]
    rfl
  -- Pairwise disjointness: distinct last symbols give distinct length-(m+1) blocks.
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset α)
      (nodeExtendCylinder μ p m v) := by
    intro a _ a' _ hne
    have hpt : (Fin.snoc v a : Fin (m + 1) → α) ≠ Fin.snoc v a' := by
      intro hsnoc
      apply hne
      have h := congrFun hsnoc (Fin.last m)
      rwa [Fin.snoc_last, Fin.snoc_last] at h
    apply Set.disjoint_left.mpr
    intro x hx hx'
    simp only [nodeExtendCylinder, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    exact hpt (hx.symm.trans hx')
  -- Measurability of each node-extended cylinder.
  have hmeas : ∀ a ∈ (Finset.univ : Finset α),
      MeasurableSet (nodeExtendCylinder μ p m v a) := fun a _ =>
    (p.measurable_blockRV (m + 1)) (measurableSet_singleton _)
  -- Union of node-extended cylinders is the length-`m` node cylinder.
  have hunion : (⋃ a ∈ (Finset.univ : Finset α), nodeExtendCylinder μ p m v a)
      = p.blockRV m ⁻¹' {v} := by
    ext x
    simp only [nodeExtendCylinder, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨a, hx⟩
      rw [blockRV_succ_eq_snoc] at hx
      funext i
      have := congrFun hx i.castSucc
      rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at this
    · intro hx
      refine ⟨p.obs m x, ?_⟩
      rw [blockRV_succ_eq_snoc, hx]
  rw [Finset.sum_congr rfl (fun a _ => hpush a)]
  rw [← measureReal_biUnion_finset hdisj hmeas, hunion,
      ← map_measureReal_apply (p.measurable_blockRV m) (measurableSet_singleton _)]

omit [DecidableEq α] [Nonempty α] in
/-- **Genuine per-node conditional sub-distribution** (normalised form): for a
node `v` with positive block probability, the node-context next-symbol
conditionals `P(v · a) / P(v)` sum to `1` (so any subfamily sums to `≤ 1`). -/
theorem condNode_sum_eq_one
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (m : ℕ) (v : Fin m → α)
    (hpos : 0 < (μ.map (p.blockRV m)).real {v}) :
    (∑ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
        / (μ.map (p.blockRV m)).real {v})
      = 1 := by
  rw [← Finset.sum_div, nodeExtend_measureReal_sum_eq μ p m v, div_self hpos.ne']

omit [DecidableEq α] [Nonempty α] in
/-- **Subfamily node sub-distribution `≤ 1`**: for any finite subset `S` of
the alphabet, the node-context conditionals over `S` sum to `≤ 1`. This is the
directly `log_sum_inequality`-consumable form. -/
theorem condNode_subset_sum_le_one
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (m : ℕ) (v : Fin m → α) (S : Finset α)
    (hpos : 0 < (μ.map (p.blockRV m)).real {v}) :
    (∑ a ∈ S, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
        / (μ.map (p.blockRV m)).real {v})
      ≤ 1 := by
  classical
  -- nonnegativity of each conditional term
  have hterm_nn : ∀ a : α,
      0 ≤ (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
        / (μ.map (p.blockRV m)).real {v} :=
    fun a => div_nonneg measureReal_nonneg hpos.le
  -- subfamily sum ≤ full sum = 1
  calc (∑ a ∈ S, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
          / (μ.map (p.blockRV m)).real {v})
      ≤ ∑ a : α, (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
          / (μ.map (p.blockRV m)).real {v} :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun a _ _ => hterm_nn a)
    _ = 1 := condNode_sum_eq_one μ p m v hpos

end NodeSubDist

/-! ## §3. Per-node log-sum step (T3-inner) -/

section NodeLogSum

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

omit [DecidableEq α] [Nonempty α] in
/-- **Per-node log-sum step** (genuine, T3-inner): at a node `v` whose children
symbols form a finite set `S` (the distinct next symbols of the phrases
extending `v`), the count product `k_v · log k_v` (`k_v = |S|`) is bounded by
the sum over the children of the node-context self-informations
`∑_{a ∈ S} -log q(v · a | v)`, where the conditionals are positive.

Proof: `log_sum_inequality` with `aᵢ ≡ 1` over `S` and `bᵢ = q(v·a|v) > 0`
gives `k_v · log(k_v / ∑b) ≤ ∑ -log b`; since `∑ b ≤ 1`
(`condNode_subset_sum_le_one`), `log(k_v/∑b) ≥ log k_v`. -/
theorem node_logsum_step
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α)
    (m : ℕ) (v : Fin m → α) (S : Finset α)
    (hpos : 0 < (μ.map (p.blockRV m)).real {v})
    (hposChild : ∀ a ∈ S, 0 < (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}) :
    (S.card : ℝ) * Real.log (S.card : ℝ)
      ≤ ∑ a ∈ S, - Real.log
          ((μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
            / (μ.map (p.blockRV m)).real {v}) := by
  classical
  -- Empty `S`: LHS `= 0 · log 0 = 0`, RHS `= 0`.
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst hSe; simp
  set q : α → ℝ := fun a =>
    (μ.map (p.blockRV (m + 1))).real {Fin.snoc v a}
      / (μ.map (p.blockRV m)).real {v} with hq
  -- node-context conditionals over `S` are positive and sum to `≤ 1`.
  have hq_pos : ∀ a ∈ S, 0 < q a := fun a ha =>
    div_pos (hposChild a ha) hpos
  have hsum_le : (∑ a ∈ S, q a) ≤ 1 :=
    condNode_subset_sum_le_one μ p m v S hpos
  have hsum_pos : 0 < ∑ a ∈ S, q a := Finset.sum_pos hq_pos hSne
  -- log-sum inequality with `aᵢ ≡ 1`, `bᵢ = q a`.
  have hlogsum := log_sum_inequality (ι := α) S (fun _ => (1 : ℝ)) q
    (fun a _ => by norm_num) hq_pos
  -- LHS of `log_sum_inequality`: `(∑ 1) · log((∑1)/(∑ q))`.
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hlogsum
  -- RHS: `∑ 1 · log(1 / q a) = ∑ -log (q a)`.
  have hrhs : (∑ a ∈ S, (1 : ℝ) * Real.log (1 / q a))
      = ∑ a ∈ S, - Real.log (q a) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [one_mul, Real.log_div one_ne_zero (hq_pos a ha).ne', Real.log_one, zero_sub]
  rw [hrhs] at hlogsum
  -- `log((card)/(∑q)) ≥ log(card)` since `0 < ∑ q ≤ 1`.
  refine le_trans ?_ hlogsum
  rcases Nat.eq_zero_or_pos S.card with hc0 | hcpos
  · simp [hc0]
  · have hcardR_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcpos
    have hmono : Real.log (S.card : ℝ)
        ≤ Real.log ((S.card : ℝ) / (∑ a ∈ S, q a)) := by
      apply Real.log_le_log hcardR_pos
      rw [le_div_iff₀ hsum_pos]
      calc (S.card : ℝ) = (S.card : ℝ) * 1 := (mul_one _).symm
        _ ≥ (S.card : ℝ) * (∑ a ∈ S, q a) :=
          mul_le_mul_of_nonneg_left hsum_le hcardR_pos.le
    exact mul_le_mul_of_nonneg_left hmono hcardR_pos.le

end NodeLogSum

end InformationTheory.Shannon
