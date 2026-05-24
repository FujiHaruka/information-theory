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

/-! ## §4. Overhead-aware Ziv combinatorial core (honest, mathematically true) -/

section OverheadCore

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Genuine lower-order Ziv overhead** (`O(c)`, vanishing after `÷n`): the
Cover–Thomas tree overhead `c · log(|α|+1)`. Since the distinct-phrase count
satisfies `c/n → 0` (`lz78Distinct_count_div_le_envelope`), this overhead
divided by `n` vanishes — it is genuinely lower-order, not a weakening. -/
noncomputable def lz78ZivOverhead
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) : ℝ :=
  ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
    * Real.log ((Fintype.card α : ℝ) + 1)

/-- **Overhead-aware Ziv combinatorial core (Cover–Thomas Lemma 13.5.4/13.5.5,
honest hypothesis).**

```
c · log c  ≤  -log Pₙ  +  c · log(|α|+1).
```

**⚠ DEFECT — this per-block `∀ n ∀ ω` form is mathematically FALSE.**
A genuine, unconditional, machine-checked refutation is published as
`not_isLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeBridge.lean`). Witness:
the constant process (`X ≡ a`) on `Unit`, at `n = 16`, has `Pₙ = 1`
(`-log Pₙ = 0`) and the LZ parse of `a^16` emits `c = 5` distinct phrases, so
the core asserts `5·log 5 ≤ 0 + 5·log 3`, i.e. `log 5 ≤ log 3` — false. The
clean core `c·log c ≤ -log Pₙ` is *also* false (`(a,a,b)`), but **adding the
`O(c)` overhead `c·log(|α|+1)` does NOT repair it**: when `Pₙ → 1` the term
`-log Pₙ → 0` while `c log c ∼ √n·log√n → ∞`, and an `O(c)` overhead cannot
close that gap (numerically even the textbook `c·log(n/c)` overhead is
insufficient as `p → 1`). The single `(a,a,b)` check that previously justified
"mathematically TRUE" only samples one point of the failing family and is not
evidence for the universal statement.

**Honesty status.** Because the statement is false, it is **unsatisfiable**:
any headline assuming `hcore : IsLZ78ZivCombinatorialCoreOverhead` is vacuously
conditioned for the witness process (and the whole `Pₙ ≈ 1` family). The genuine
Cover–Thomas LZ optimality `c log c ∼ -log Pₙ` is an **a.s.-eventual**
(ergodic / AEP) statement, not a per-block `∀ n ∀ ω` inequality; the honest
input that *can* be discharged is the a.s.-eventual rate-bound structure
`IsLZ78AchievabilityZivUpperBound` (already used downstream), not this per-block
core. The genuine, sorryAx-free tree-node infrastructure of this file (T1
`lz78PhraseStringsAux_emit_context_mem`, T2 `nodeExtend_measureReal_sum_eq`,
T3 `node_logsum_step`) is correct and reusable, but it cannot assemble into this
(false) per-block core. This definition is retained only so the refutation and
the downstream type-correct (but vacuously conditioned) wiring keep compiling;
it should be **retired** in favour of an a.s.-eventual formulation. -/
def IsLZ78ZivCombinatorialCoreOverhead
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop :=
  ∀ (n : ℕ) (ω : Ω),
    ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
        * Real.log ((lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length : ℝ)
      ≤ - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
          + lz78ZivOverhead μ p n ω

end OverheadCore

/-! ## §5. Overhead-aware achievability assembly (slack absorbs the overhead) -/

section OverheadAssembly

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- **Overhead-aware achievability slack**: the genuine vanishing
`lz78AchievSlack` plus the **ω-uniform** envelope bound on the Ziv tree
overhead. The overhead `c · log(|α|+1)` divided by `n · log 2` is bounded
above, uniformly in `ω`, by `envelope(n) · log(|α|+1) / log 2` (since
`c/n ≤ envelope(n)`, `lz78Distinct_count_div_le_envelope`), and the envelope
vanishes. So the whole slack still tends to `0`. -/
noncomputable def lz78AchievSlackOverhead (n : ℕ) : ℝ :=
  lz78AchievSlack (α := α) n
    + (2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
        + 1 / Real.sqrt (n : ℝ))
      * Real.log ((Fintype.card α : ℝ) + 1) / Real.log 2

omit [MeasurableSingletonClass α] in
/-- **Per-block, per-path overhead-aware Ziv upper bound**: from the
overhead-aware combinatorial core, the bit rate is below the base-2
per-block estimator plus the overhead-aware slack. The genuine Ziv tree
overhead is absorbed by the ω-uniform vanishing envelope.

`@audit:suspect(lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem lz78DistinctRate_le_blockLogAvg₂_add_slackOverhead
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (hcore : IsLZ78ZivCombinatorialCoreOverhead μ p)
    (n : ℕ) (hn : 2 ≤ n) (ω : Ω)
    (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω}) :
    (lz78DistinctEncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
      ≤ blockLogAvg₂ μ p n ω + lz78AchievSlackOverhead (α := α) n := by
  classical
  set c : ℕ := (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length with hc
  set Pn : ℝ := (μ.map (p.blockRV n)).real {p.blockRV n ω} with hPndef
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hlog2_pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
  -- alphabet log overhead constant `L_α = log(|α|+1) ≥ 0`.
  set Lα : ℝ := Real.log ((Fintype.card α : ℝ) + 1) with hLα
  have hLα_nn : (0 : ℝ) ≤ Lα := by
    rw [hLα]
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
    linarith
  -- envelope `c/n ≤ env`.
  have henv := lz78Distinct_count_div_le_envelope n hn (p.blockRV n ω)
  rw [← hc] at henv
  set env : ℝ := 2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
    + 1 / Real.sqrt (n : ℝ) with hEnv
  have henv_nn : (0 : ℝ) ≤ env := by
    have hcard_nn : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
    have hKnn : (0 : ℝ) ≤ Real.log (Fintype.card α + 1) :=
      Real.log_nonneg (by linarith)
    rw [hEnv]; positivity
  -- alphabet bit-cost constant `D`.
  set D : ℝ := (Nat.log 2 (Fintype.card α) : ℝ) + 2 with hD
  have hD_nn : (0 : ℝ) ≤ D := by rw [hD]; positivity
  -- `lz = c · (Nat.log 2 (c+1) + Nat.log 2 |α| + 2)`.
  have hlz : (lz78DistinctEncodingLength n (p.blockRV n ω) : ℝ)
      = (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ)
          + (Nat.log 2 (Fintype.card α) : ℝ) + 2) := by
    rw [lz78DistinctEncodingLength_eq, LZ78Phrase.bitLength_eq]
    push_cast
    ring
  -- base-2 estimator unfolds to `-log Pn / (n log 2)`.
  have hblk : blockLogAvg₂ μ p n ω = - Real.log Pn / ((n : ℝ) * Real.log 2) := by
    unfold blockLogAvg₂ blockLogAvg
    rw [hPndef]; field_simp
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · -- `c = 0`: `lz = 0`, slack ≥ 0, estimator ≥ 0.
    rw [hlz, hc0]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    have hslk_nn : (0 : ℝ) ≤ lz78AchievSlackOverhead (α := α) n := by
      have h1 : (0 : ℝ) ≤ 1 / ((n : ℝ) * Real.log 2) := by positivity
      have hp1 : (0 : ℝ) ≤ env * D := mul_nonneg henv_nn hD_nn
      have hp2 : (0 : ℝ) ≤ env * Lα / Real.log 2 :=
        div_nonneg (mul_nonneg henv_nn hLα_nn) hlog2_pos.le
      have heq : lz78AchievSlackOverhead (α := α) n
          = 1 / ((n : ℝ) * Real.log 2) + env * D + env * Lα / Real.log 2 := by
        rw [lz78AchievSlackOverhead, lz78AchievSlack, hEnv, hD, hLα]
      rw [heq]; linarith
    have hblk_nn : (0 : ℝ) ≤ blockLogAvg₂ μ p n ω := by
      rw [hblk]
      have hPn1 : Pn ≤ 1 := by
        rw [hPndef]
        have : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
          Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
        exact measureReal_le_one
      have hlogPn : Real.log Pn ≤ 0 := Real.log_nonpos hPn.le hPn1
      have : (0 : ℝ) ≤ - Real.log Pn := by linarith
      positivity
    linarith
  · -- `c ≥ 1`: the genuine chain with overhead.
    have hcR_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
    -- overhead core: `c log c ≤ -log Pn + c · Lα`.
    have hziv' : (c : ℝ) * Real.log (c : ℝ) ≤ - Real.log Pn + (c : ℝ) * Lα := by
      have h := hcore n ω
      rw [← hc, ← hPndef] at h
      -- `lz78ZivOverhead = c · Lα`.
      have hov : lz78ZivOverhead μ p n ω = (c : ℝ) * Lα := by
        rw [lz78ZivOverhead, ← hc, ← hLα]
      rw [hov] at h
      exact h
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
      have hcne : (c : ℝ) ≠ 0 := hcR_pos.ne'
      have : ((c : ℝ) + 1) / (c : ℝ) - 1 = 1 / (c : ℝ) := by field_simp; ring
      rw [this] at hratio
      linarith
    -- Term A_num: `c · Nat.log 2 (c+1) ≤ (c log c + 1)/log 2`.
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
    -- Assemble.
    rw [hlz, hblk]
    rw [show (c : ℝ) * ((Nat.log 2 (c + 1) : ℝ)
            + (Nat.log 2 (Fintype.card α) : ℝ) + 2)
          = (c : ℝ) * (Nat.log 2 (c + 1) : ℝ) + (c : ℝ) * D by rw [hD]; ring]
    rw [add_div]
    -- Term A (with overhead): `(c·natlog(c+1))/n ≤ -log Pn/(n log2) + 1/(n log2)
    --   + (c·Lα)/(n log2)`.
    have hAterm : ((c : ℝ) * (Nat.log 2 (c + 1) : ℝ)) / (n : ℝ)
        ≤ (- Real.log Pn) / ((n : ℝ) * Real.log 2)
            + 1 / ((n : ℝ) * Real.log 2)
            + ((c : ℝ) * Lα) / ((n : ℝ) * Real.log 2) := by
      have hnum : (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
          ≤ (- Real.log Pn + (c : ℝ) * Lα + 1) / Real.log 2 := by
        calc (c : ℝ) * (Nat.log 2 (c + 1) : ℝ)
            ≤ ((c : ℝ) * Real.log (c : ℝ) + 1) / Real.log 2 := htermA_num
          _ ≤ (- Real.log Pn + (c : ℝ) * Lα + 1) / Real.log 2 := by
              apply div_le_div_of_nonneg_right _ hlog2_pos.le
              linarith [hziv']
      calc ((c : ℝ) * (Nat.log 2 (c + 1) : ℝ)) / (n : ℝ)
          ≤ ((- Real.log Pn + (c : ℝ) * Lα + 1) / Real.log 2) / (n : ℝ) :=
            div_le_div_of_nonneg_right hnum hn_pos.le
        _ = (- Real.log Pn) / ((n : ℝ) * Real.log 2)
              + 1 / ((n : ℝ) * Real.log 2)
              + ((c : ℝ) * Lα) / ((n : ℝ) * Real.log 2) := by
            field_simp
            ring
    -- overhead term ≤ env · Lα / log 2 (ω-uniform vanishing).
    have hOverTerm : ((c : ℝ) * Lα) / ((n : ℝ) * Real.log 2)
        ≤ env * Lα / Real.log 2 := by
      -- `(c·Lα)/(n·log2) = (c/n)·(Lα/log2) ≤ env·(Lα/log2)`.
      have hcn : (c : ℝ) / (n : ℝ) ≤ env := henv
      have hfac : (Lα / Real.log 2) ≥ 0 := div_nonneg hLα_nn hlog2_pos.le
      have hlhs : ((c : ℝ) * Lα) / ((n : ℝ) * Real.log 2)
          = ((c : ℝ) / (n : ℝ)) * (Lα / Real.log 2) := by
        rw [div_mul_div_comm]
      have hrhs : env * Lα / Real.log 2 = env * (Lα / Real.log 2) := by
        rw [mul_div_assoc]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right hcn hfac
    -- Term B: `(c·D)/n ≤ env·D`.
    have hBterm : ((c : ℝ) * D) / (n : ℝ) ≤ env * D := by
      rw [mul_comm (c : ℝ) D, mul_div_assoc]
      calc D * ((c : ℝ) / (n : ℝ)) ≤ D * env :=
            mul_le_mul_of_nonneg_left henv hD_nn
        _ = env * D := by ring
    -- slack = lz78AchievSlack + env·Lα/log 2; lz78AchievSlack = 1/(n log2) + env·D.
    have hslack_eq : lz78AchievSlackOverhead (α := α) n
        = 1 / ((n : ℝ) * Real.log 2) + env * D + env * Lα / Real.log 2 := by
      rw [lz78AchievSlackOverhead, lz78AchievSlack, hEnv, hD, hLα]
    rw [hslack_eq]
    have hgoal :
        ((c : ℝ) * (Nat.log 2 (c + 1) : ℝ)) / (n : ℝ) + ((c : ℝ) * D) / (n : ℝ)
          ≤ (- Real.log Pn) / ((n : ℝ) * Real.log 2)
              + (1 / ((n : ℝ) * Real.log 2) + env * D + env * Lα / Real.log 2) := by
      have hA := hAterm
      have hO := hOverTerm
      have hB := hBterm
      linarith
    convert hgoal using 2

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **The overhead-aware achievability slack vanishes**: both `lz78AchievSlack`
and the envelope-times-overhead term tend to `0`. -/
theorem lz78AchievSlackOverhead_tendsto_zero :
    Filter.Tendsto (lz78AchievSlackOverhead (α := α)) Filter.atTop (𝓝 (0 : ℝ)) := by
  unfold lz78AchievSlackOverhead
  -- `lz78AchievSlack → 0` (genuine) plus the envelope·overhead/log 2 term → 0.
  have hbase := lz78AchievSlack_tendsto_zero (α := α)
  -- envelope `2K/log n + 1/√n → 0`.
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hsqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have h2 : Filter.Tendsto
      (fun n : ℕ => 2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ))
      Filter.atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hlog
  have h3 : Filter.Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ))
      Filter.atTop (𝓝 0) := by
    simpa using hsqrt.inv_tendsto_atTop
  have hover : Filter.Tendsto
      (fun n : ℕ => (2 * (8 * Real.log (Fintype.card α + 1)) / Real.log (n : ℝ)
            + 1 / Real.sqrt (n : ℝ))
          * Real.log ((Fintype.card α : ℝ) + 1) / Real.log 2)
      Filter.atTop (𝓝 0) := by
    have := ((h2.add h3).mul_const (Real.log ((Fintype.card α : ℝ) + 1))).div_const
      (Real.log 2)
    simpa using this
  have := hbase.add hover
  simpa using this

omit [MeasurableSingletonClass α] in
/-- 🟢ʰ **load-bearing hypothesis — NOT a discharge (and the hypothesis is
mathematically FALSE).**
**Overhead-aware construction of `IsLZ78AchievabilityZivUpperBound`** from the
overhead-aware combinatorial core plus regularity.

⚠️ **`hcore_lbh : IsLZ78ZivCombinatorialCoreOverhead` is unsatisfiable.** A
genuine unconditional refutation is recorded in
`LZ78ZivTreeBridge.not_isLZ78ZivCombinatorialCoreOverhead` (constant process
witness at `n = 16`, `Pₙ = 1`, `c = 5`: `5 log 5 > 5 log 3`). So this theorem
is **vacuously conditioned** — type-correct but the hypothesis cannot be
discharged for any process. The genuine tree overhead `c·log(|α|+1)` is
absorbed into the vanishing slack `lz78AchievSlackOverhead`, but that
absorption itself is not the defect: the gap `c log c` vs `-log Pₙ` is
super-`O(c)` when `Pₙ → 1`.

The correct honest input is an **a.s.-eventual** rate bound, not a per-block
universal inequality; see `LZ78AsEventualAchievability.lean` for the
reformulation track. This lemma stands only as scaffolding marking where the
genuine a.s.-eventual replacement plugs in.

`@audit:defect(degenerate)` `@audit:suspect(lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem isLZ78AchievabilityZivUpperBound_distinctOverhead
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (hcore_lbh : IsLZ78ZivCombinatorialCoreOverhead μ p)
    (hreg : ∀ (n : ℕ) (ω : Ω) (m : ℕ),
      m ≤ n → 0 < prefixBlockProb μ p ω m) :
    IsLZ78AchievabilityZivUpperBound μ p
      (@lz78DistinctEncodingLength α _ _ _) (lz78AchievSlackOverhead (α := α)) := by
  refine ⟨?_, lz78AchievSlackOverhead_tendsto_zero⟩
  -- the upper bound holds for *every* `ω` (given `hreg`), eventually in `n`.
  refine Filter.Eventually.of_forall (fun ω => ?_)
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω} :=
    hreg n ω n (le_refl n)
  exact lz78DistinctRate_le_blockLogAvg₂_add_slackOverhead μ p hcore_lbh n hn ω hPn

end OverheadAssembly

/-! ## §6. Overhead-aware base-2 headline (achievability core wired, true) -/

section OverheadHeadline

variable {α : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **T4-A base-2 distinct headline with the achievability Ziv upper bound
genuinely wired from the *mathematically-true* overhead-aware core** (Phase V).

This re-derives the genuine Cover–Thomas Theorem 13.5.3 base-2 limit with the
**achievability** honest input `IsLZ78AchievabilityZivUpperBound` *no longer
assumed* — it is genuinely constructed
(`isLZ78AchievabilityZivUpperBound_distinctOverhead`) from the
overhead-aware combinatorial core `IsLZ78ZivCombinatorialCoreOverhead` plus
the admissible full-support regularity `hreg`. The genuine Ziv tree overhead
`c·log(|α|+1)` is absorbed into the vanishing slack `lz78AchievSlackOverhead`.

**Honesty status (read this).** This is **not** an unconditional headline, and
it does **not** reduce the assumption count to one. Two honest inputs remain:

* `hcore : IsLZ78ZivCombinatorialCoreOverhead` — the overhead-aware per-block
  core `c·log c ≤ -log Pₙ + c·log(|α|+1)`. **⚠ This hypothesis is FALSE**
  (`not_isLZ78ZivCombinatorialCoreOverhead`, `LZ78ZivTreeBridge.lean`): the
  constant process witnesses `c log c > -log Pₙ + c log(|α|+1)` at `n = 16`
  (`Pₙ = 1`, `c = 5`, `5 log 5 > 5 log 3`). The previous clean core
  `c·log c ≤ -log Pₙ` is also false (`(a,a,b)`), and the `O(c)` overhead does
  **not** repair it (the gap `c log c` vs `-log Pₙ → 0` is super-`O(c)` when
  `Pₙ → 1`). So this headline is **vacuously conditioned** for the witness
  process — it is type-correct but cannot be instantiated there. The genuine
  T1/T2/T3 tree-node infrastructure is sorryAx-free and reusable, but it cannot
  assemble into this (false) per-block core; the correct honest input is an
  a.s.-eventual rate bound, not a per-block universal inequality.
* `h_lb : IsLZ78ConverseCodingLowerBound` — the converse coding lower bound
  (Core 2, untouched here).

So this does **not** fix the false-core defect — it relocates it from the clean
core to the overhead core, which is also false. The genuine T1/T2/T3 tree-node
foundation stands; the assumption count remains two honest inputs, but `hcore`
is unsatisfiable as stated and must be reformulated a.s.-eventually.

`@audit:defect(degenerate)` `@audit:suspect(lz78-ziv-inequality-discharge-moonshot-plan)` -/
theorem lz78_two_sided_optimality_distinct_ziv_overhead_core_wired
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (slackLow : ℕ → ℝ)
    (hcore : IsLZ78ZivCombinatorialCoreOverhead μ p.toStationaryProcess)
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
        (𝓝 (entropyRate₂ μ p.toStationaryProcess)) :=
  lz78_two_sided_optimality_distinct_genuine μ p
    (lz78AchievSlackOverhead (α := α)) slackLow
    (isLZ78AchievabilityZivUpperBound_distinctOverhead μ p.toStationaryProcess hcore hreg)
    h_lb

end OverheadHeadline

end InformationTheory.Shannon
