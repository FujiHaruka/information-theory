import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ShannonCode.Basic
import InformationTheory.Shannon.ShannonCode.KraftReverse

/-!
# Huffman code lengths

Constructs the binary Huffman code length function `huffmanLength` for a finite alphabet `α`
equipped with a probability measure, following Cover–Thomas Theorem 5.8.1.

## Main definitions

* `groupKey` — deterministic comparison key (lex on probability then colex) used to break ties
  in `huffmanStep`.
* `HuffmanGrouping` — invariant on the working multiset: no-duplicates, nonempty groups,
  pairwise-disjoint carriers.
* `huffmanStep` — one merge step: extracts the two minimum-probability groups and returns the
  merged multiset together with a proof that `HuffmanGrouping` is preserved.
* `huffmanLengthAux` — recursion on the multiset; assigns a codeword length to each `α`-element.
* `initMultiset` — initial multiset of singleton groups `({a}, P.real {a})`.
* `huffmanLength` — the published codeword-length function `huffmanLengthAux (initMultiset P)`.
* `huffmanCost` — multiset-level expected length used in the cost-level optimality proof.

## Main statements

* `groupKey_injective` — `groupKey` is injective (probability + colex breaks all ties).
* `huffmanStep_min_fst` / `huffmanStep_min_snd` — the two extracted groups have minimum
  probability in `s` (resp. `s.erase .val.1`).
* `huffmanLength_pos` — `huffmanLength P a > 0` when `card α ≥ 2`.
* `huffmanLength_kraft_eq_one` — the Kraft sum equals `1` exactly.
* `huffmanLength_kraft_le_one` — the Kraft inequality holds.
* `exists_huffman_prefix_code` — a prefix-free binary code of the Huffman lengths exists.
* `huffmanCost_step` — `huffmanCost` decreases by the merged-group probability at each step.
* `huffmanCost_eq_of_prob_multiset` — `huffmanCost` depends only on the probability multiset.
* `expectedLength_eq_huffmanCost` — the expected length of `huffmanLength P` equals
  `huffmanCost (initMultiset P)`.

## Implementation notes

The merge step uses `groupKey` (a lex order on `ℝ ×ₗ Colex (Finset α)`) rather than a plain
probability ordering so that the minimum selection is deterministic even under probability ties.
This is essential for the carrier-crossing cost argument (`huffmanCost_eq_of_prob_multiset`).
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Deterministic comparison key for `huffmanStep`: primary key is probability `p.2` (ascending),
tie-break is `toColex p.1` (colex order). The resulting `Prod.Lex` total order on
`ℝ ×ₗ Colex (Finset α)` makes the minimum selection unique even under probability ties. -/
noncomputable def groupKey (p : Finset α × ℝ) : ℝ ×ₗ Colex (Finset α) :=
  toLex (p.2, toColex p.1)

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
@[entry_point]
lemma groupKey_injective : Function.Injective (groupKey (α := α)) := by
  intro p q h
  unfold groupKey at h
  have h1 : p.2 = q.2 := congrArg (fun z => (ofLex z).1) h
  have h2 : toColex p.1 = toColex q.1 := congrArg (fun z => (ofLex z).2) h
  rw [toColex_inj] at h2
  exact Prod.ext h2 h1

omit [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma groupKey_le_imp_snd_le {p q : Finset α × ℝ} (h : groupKey p ≤ groupKey q) :
    p.2 ≤ q.2 := by
  unfold groupKey at h
  rw [Prod.Lex.le_iff] at h
  rcases h with h | ⟨h1, _⟩
  · exact le_of_lt h
  · exact le_of_eq h1

/-! ### Internal implementation: Multiset-based Huffman recursion -/

/-- Invariant on a working group multiset: no duplicates, every group is nonempty,
and distinct groups have disjoint carriers. -/
def HuffmanGrouping (s : Multiset (Finset α × ℝ)) : Prop :=
  s.Nodup ∧
  (∀ p ∈ s, p.1.Nonempty) ∧
  (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint p.1 q.1)

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma HuffmanGrouping.nodup {s : Multiset (Finset α × ℝ)} (h : HuffmanGrouping s) :
    s.Nodup := h.1


omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma HuffmanGrouping.nonempty {s : Multiset (Finset α × ℝ)} (h : HuffmanGrouping s)
    {p : Finset α × ℝ} (hp : p ∈ s) : p.1.Nonempty := h.2.1 p hp

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma HuffmanGrouping.disjoint {s : Multiset (Finset α × ℝ)} (h : HuffmanGrouping s)
    {p q : Finset α × ℝ} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) :
    Disjoint p.1 q.1 := h.2.2 p hp q hq hpq

omit [Fintype α] [LinearOrder α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanMerged_notMem_eraseErase
    {s : Multiset (Finset α × ℝ)} (hg : HuffmanGrouping s)
    {x1 x2 : Finset α × ℝ} (hx1_mem : x1 ∈ s) (hx2_mem_s : x2 ∈ s) (hx12_ne : x1 ≠ x2) :
    (x1.1 ∪ x2.1, x1.2 + x2.2) ∉ (s.erase x1).erase x2 := by
  classical
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  intro hmem_ee
  -- q := merged ∈ erase erase ⊆ s
  have hmem_s' : merged ∈ s.erase x1 := Multiset.mem_of_mem_erase hmem_ee
  have hmem_s : merged ∈ s := Multiset.mem_of_mem_erase hmem_s'
  -- merged ≠ x1: merged.1 = x1.1 ∪ x2.1, contains x2.1's elements,
  --   while x1.1 disjoint from x2.1 (x1 ≠ x2 + HuffmanGrouping)
  have h_merged_ne_x1 : merged ≠ x1 := by
    intro heq
    have hfst : merged.1 = x1.1 := by rw [heq]
    -- merged.1 = x1.1 ∪ x2.1; x2.1 is nonempty; so x2.1 ⊆ x1.1
    have hx2_ne : x2.1.Nonempty := hg.nonempty hx2_mem_s
    obtain ⟨a, ha⟩ := hx2_ne
    have ha_in_merged : a ∈ merged.1 := by
      show a ∈ x1.1 ∪ x2.1
      exact Finset.mem_union_right _ ha
    rw [hfst] at ha_in_merged
    have h_disj : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_mem_s hx12_ne
    exact (Finset.disjoint_left.mp h_disj ha_in_merged) ha
  -- merged ≠ x2: symmetric
  have h_merged_ne_x2 : merged ≠ x2 := by
    intro heq
    have hfst : merged.1 = x2.1 := by rw [heq]
    have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
    obtain ⟨a, ha⟩ := hx1_ne
    have ha_in_merged : a ∈ merged.1 := by
      show a ∈ x1.1 ∪ x2.1
      exact Finset.mem_union_left _ ha
    rw [hfst] at ha_in_merged
    have h_disj : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_mem_s hx12_ne
    exact (Finset.disjoint_right.mp h_disj ha_in_merged) ha
  -- HuffmanGrouping.disjoint gives Disjoint merged.1 x1.1,
  -- but merged.1 ⊇ x1.1 and x1.1 is nonempty, contradiction.
  have h_disj_merged_x1 : Disjoint merged.1 x1.1 :=
    hg.disjoint hmem_s hx1_mem h_merged_ne_x1
  have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
  obtain ⟨a, ha⟩ := hx1_ne
  have ha_in_merged : a ∈ merged.1 := by
    show a ∈ x1.1 ∪ x2.1
    exact Finset.mem_union_left _ ha
  exact (Finset.disjoint_left.mp h_disj_merged_x1 ha_in_merged) ha

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma kraftTerm_of_const_depth
    {g : Finset α} (hg_ne : g.Nonempty) (f : α → ℤ) (d : ℤ)
    (hconst : ∀ a ∈ g, f a = d) :
    (∑ a ∈ g, (2 : ℝ) ^ (-(f a))) / (g.card : ℝ) = (2 : ℝ) ^ (-d) := by
  have hcard_pos : (0 : ℝ) < g.card := by
    exact_mod_cast Finset.card_pos.mpr hg_ne
  have hsum : (∑ a ∈ g, (2 : ℝ) ^ (-(f a)))
      = (g.card : ℝ) * (2 : ℝ) ^ (-d) := by
    rw [show (g.card : ℝ) * (2 : ℝ) ^ (-d)
        = ∑ _x ∈ g, (2 : ℝ) ^ (-d) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hconst a ha]
  rw [hsum]
  field_simp

/-- One Huffman merge step: extracts the two minimum-`groupKey` groups from `s` and returns
the merged multiset together with membership witnesses and the proof that `HuffmanGrouping`
is preserved. Requires `s.card ≥ 2` and `HuffmanGrouping s`. -/
noncomputable def huffmanStep
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    { p : (Finset α × ℝ) × (Finset α × ℝ) × Multiset (Finset α × ℝ) //
        p.1 ∈ s ∧
        p.2.1 ∈ s.erase p.1 ∧
        p.2.2 =
          (p.1.1 ∪ p.2.1.1, p.1.2 + p.2.1.2) ::ₘ
            ((s.erase p.1).erase p.2.1) ∧
        HuffmanGrouping p.2.2 } := by
  classical
  have hs_ne : s ≠ 0 := by
    intro heq; rw [heq, Multiset.card_zero] at hs; omega
  let x1 := Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
    (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  have hx1k : x1 ∈ s ∧ ∀ z ∈ s, groupKey x1 ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  have hx1 : x1 ∈ s ∧ ∀ z ∈ s, x1.2 ≤ z.2 :=
    ⟨hx1k.1, fun z hz => groupKey_le_imp_snd_le (hx1k.2 z hz)⟩
  let s' := s.erase x1
  have hs'_ne : s' ≠ 0 := by
    have hcard_s' : s'.card = s.card - 1 :=
      Multiset.card_erase_of_mem hx1.1
    intro heq
    rw [heq, Multiset.card_zero] at hcard_s'
    omega
  let x2 := Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
    (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)
  have hx2k : x2 ∈ s' ∧ ∀ z ∈ s', groupKey x2 ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)
  have hx2 : x2 ∈ s' ∧ ∀ z ∈ s', x2.2 ≤ z.2 :=
    ⟨hx2k.1, fun z hz => groupKey_le_imp_snd_le (hx2k.2 z hz)⟩
  -- Assemble witnesses for HuffmanGrouping preservation.
  have hx1_mem : x1 ∈ s := hx1.1
  have hx2_mem_s' : x2 ∈ s' := hx2.1
  -- x2 ∈ s.erase x1 implies x2 ∈ s.
  have hx2_mem_s : x2 ∈ s := Multiset.mem_of_mem_erase hx2_mem_s'
  -- Nodup implies x1 ≠ x2 (since x2 ∈ s.erase x1).
  have hx12_ne : x1 ≠ x2 := by
    intro heq
    rw [← heq] at hx2_mem_s'
    exact hg.nodup.notMem_erase hx2_mem_s'
  -- Nodup is preserved under double erase.
  have h_ee_nodup : ((s.erase x1).erase x2).Nodup :=
    ((hg.nodup.erase x1).erase x2)
  -- Show that merged = (x1.1 ∪ x2.1, x1.2 + x2.2) is not in the double-erase multiset.
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  have h_merged_not_in :
      merged ∉ ((s.erase x1).erase x2) :=
    huffmanMerged_notMem_eraseErase hg hx1_mem hx2_mem_s hx12_ne
  refine ⟨(x1, x2, (x1.1 ∪ x2.1, x1.2 + x2.2) ::ₘ s'.erase x2), ?_, ?_, ?_, ?_⟩
  · exact hx1_mem
  · exact hx2_mem_s'
  · rfl
  -- Verify HuffmanGrouping for (merged ::ₘ erase erase).
  refine ⟨?_, ?_, ?_⟩
  · -- Nodup: merged ∉ erase erase so cons is nodup.
    exact (Multiset.nodup_cons).mpr ⟨h_merged_not_in, h_ee_nodup⟩
  · -- ∀ p ∈ cons, p.1.Nonempty
    intro p hp
    rcases Multiset.mem_cons.mp hp with hp_merged | hp_ee
    · -- p = merged
      rw [hp_merged]
      change (x1.1 ∪ x2.1).Nonempty
      have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
      exact hx1_ne.mono (Finset.subset_union_left)
    · -- p ∈ erase erase ⊆ s
      have hp_s' : p ∈ s' := Multiset.mem_of_mem_erase hp_ee
      have hp_s : p ∈ s := Multiset.mem_of_mem_erase hp_s'
      exact hg.nonempty hp_s
  · -- Disjoint
    intro p hp q hq hpq
    rcases Multiset.mem_cons.mp hp with hp_merged | hp_ee
    · -- p = merged
      rcases Multiset.mem_cons.mp hq with hq_merged | hq_ee
      · -- q = merged = p contradicts hpq
        exact absurd (hp_merged.trans hq_merged.symm) hpq
      · -- q ∈ erase erase ⊆ s, q ≠ x1, q ≠ x2
        have hq_s' : q ∈ s' := Multiset.mem_of_mem_erase hq_ee
        have hq_s : q ∈ s := Multiset.mem_of_mem_erase hq_s'
        have hq_ne_x1 : q ≠ x1 := by
          intro heq
          rw [heq] at hq_s'
          exact hg.nodup.notMem_erase hq_s'
        have hq_ne_x2 : q ≠ x2 := by
          intro heq
          rw [heq] at hq_ee
          exact (hg.nodup.erase x1).notMem_erase hq_ee
        -- p.1 = x1.1 ∪ x2.1, Disjoint with q.1 ⟺ Disjoint x1.1 q.1 ∧ Disjoint x2.1 q.1
        rw [hp_merged]
        change Disjoint (x1.1 ∪ x2.1) q.1
        rw [Finset.disjoint_union_left]
        exact ⟨hg.disjoint hx1_mem hq_s hq_ne_x1.symm,
               hg.disjoint hx2_mem_s hq_s hq_ne_x2.symm⟩
    · -- p ∈ erase erase
      rcases Multiset.mem_cons.mp hq with hq_merged | hq_ee
      · -- p ∈ erase erase, q = merged
        have hp_s' : p ∈ s' := Multiset.mem_of_mem_erase hp_ee
        have hp_s : p ∈ s := Multiset.mem_of_mem_erase hp_s'
        have hp_ne_x1 : p ≠ x1 := by
          intro heq
          rw [heq] at hp_s'
          exact hg.nodup.notMem_erase hp_s'
        have hp_ne_x2 : p ≠ x2 := by
          intro heq
          rw [heq] at hp_ee
          exact (hg.nodup.erase x1).notMem_erase hp_ee
        rw [hq_merged]
        change Disjoint p.1 (x1.1 ∪ x2.1)
        rw [Finset.disjoint_union_right]
        exact ⟨hg.disjoint hp_s hx1_mem hp_ne_x1,
               hg.disjoint hp_s hx2_mem_s hp_ne_x2⟩
      · -- both p, q ∈ erase erase ⊆ s, original disjoint
        have hp_s' : p ∈ s' := Multiset.mem_of_mem_erase hp_ee
        have hp_s : p ∈ s := Multiset.mem_of_mem_erase hp_s'
        have hq_s' : q ∈ s' := Multiset.mem_of_mem_erase hq_ee
        have hq_s : q ∈ s := Multiset.mem_of_mem_erase hq_s'
        exact hg.disjoint hp_s hq_s hpq

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanStep_spec
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    (huffmanStep s hs hg).val.1 ∈ s ∧
    (huffmanStep s hs hg).val.2.1 ∈ s.erase (huffmanStep s hs hg).val.1 ∧
    (huffmanStep s hs hg).val.2.2 =
      ((huffmanStep s hs hg).val.1.1 ∪ (huffmanStep s hs hg).val.2.1.1,
        (huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) ::ₘ
        ((s.erase (huffmanStep s hs hg).val.1).erase (huffmanStep s hs hg).val.2.1) ∧
    HuffmanGrouping (huffmanStep s hs hg).val.2.2 :=
  (huffmanStep s hs hg).property

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `.val.1` minimizes `groupKey` over all of `s`. -/
@[entry_point]
lemma huffmanStep_key_min_fst
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s, groupKey (huffmanStep s hs hg).val.1 ≤ groupKey z := by
  classical
  have hs_ne : s ≠ 0 := by
    intro heq; rw [heq, Multiset.card_zero] at hs; omega
  have hx1 : (Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)) ∈ s ∧
      ∀ z ∈ s, groupKey (Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
        (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)) ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  intro z hz
  show groupKey (huffmanStep s hs hg).val.1 ≤ groupKey z
  unfold huffmanStep
  exact hx1.2 z hz

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `.val.1` has minimum probability in `s`. -/
@[entry_point]
lemma huffmanStep_min_fst
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s, (huffmanStep s hs hg).val.1.2 ≤ z.2 := by
  intro z hz
  exact groupKey_le_imp_snd_le (huffmanStep_key_min_fst s hs hg z hz)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `.val.2.1` minimizes `groupKey` over `s.erase .val.1`. -/
@[entry_point]
lemma huffmanStep_key_min_snd
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s.erase (huffmanStep s hs hg).val.1,
      groupKey (huffmanStep s hs hg).val.2.1 ≤ groupKey z := by
  classical
  have hs_ne : s ≠ 0 := by
    intro heq; rw [heq, Multiset.card_zero] at hs; omega
  -- Reconstruct x1 and s' = s.erase x1.
  set x1 := Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
    (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne) with hx1_def
  have hx1 : x1 ∈ s ∧ ∀ z ∈ s, groupKey x1 ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  have hs'_ne : s.erase x1 ≠ 0 := by
    have hcard_s' : (s.erase x1).card = s.card - 1 :=
      Multiset.card_erase_of_mem hx1.1
    intro heq
    rw [heq, Multiset.card_zero] at hcard_s'
    omega
  have hx2 : (Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)) ∈ s.erase x1 ∧
      ∀ z ∈ s.erase x1, groupKey (Classical.choose (Multiset.exists_min_image
        (α := Finset α × ℝ) (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)) ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)
  -- (huffmanStep s hs hg).val.1 = x1, .val.2.1 = x2, so s.erase .val.1 = s.erase x1
  have hfst : (huffmanStep s hs hg).val.1 = x1 := by unfold huffmanStep; rfl
  intro z hz
  rw [hfst] at hz
  show groupKey (huffmanStep s hs hg).val.2.1 ≤ groupKey z
  unfold huffmanStep
  exact hx2.2 z hz

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `.val.2.1` has minimum probability in `s.erase .val.1`. -/
@[entry_point]
lemma huffmanStep_min_snd
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s.erase (huffmanStep s hs hg).val.1,
      (huffmanStep s hs hg).val.2.1.2 ≤ z.2 := by
  intro z hz
  exact groupKey_le_imp_snd_le (huffmanStep_key_min_snd s hs hg z hz)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanStep_grouping
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    HuffmanGrouping (huffmanStep s hs hg).val.2.2 :=
  (huffmanStep s hs hg).property.2.2.2

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanStep_card_eq
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    (huffmanStep s hs hg).val.2.2.card = s.card - 1 := by
  classical
  obtain ⟨hx1_mem, hx2_mem, hshape, _⟩ := (huffmanStep s hs hg).property
  have hs'_card : (s.erase (huffmanStep s hs hg).val.1).card = s.card - 1 :=
    Multiset.card_erase_of_mem hx1_mem
  rw [hshape, Multiset.card_cons,
    Multiset.card_erase_of_mem hx2_mem, hs'_card]
  have hpred : (s.card - 1).pred = s.card - 2 := by
    rw [Nat.pred_eq_sub_one]; omega
  rw [hpred]
  omega

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanStep_card_lt
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    (huffmanStep s hs hg).val.2.2.card < s.card := by
  rw [huffmanStep_card_eq s hs hg]; omega

/-- Internal recursion on `s.card`: assigns a codeword length to each `α`-element by strong
induction on `s.card`, merging the two minimum-probability groups at each step. Returns the
zero function on out-of-spec inputs (where `HuffmanGrouping s` fails). -/
noncomputable def huffmanLengthAux
    (s : Multiset (Finset α × ℝ)) : α → ℕ := by
  classical
  exact
    if hg : HuffmanGrouping s then
      if h : 2 ≤ s.card then
        let step := (huffmanStep s h hg).val
        let A := step.1.1
        let B := step.2.1.1
        let s'' := step.2.2
        have : s''.card < s.card := huffmanStep_card_lt s h hg
        let g := huffmanLengthAux s''
        fun a => if a ∈ A ∨ a ∈ B then g a + 1 else g a
      else
        fun _ => 0
    else
      fun _ => 0
termination_by s.card

/-- Initial working multiset: each element `a : α` maps to the singleton group `({a}, P.real {a})`. -/
noncomputable def initMultiset (P : Measure α) : Multiset (Finset α × ℝ) :=
  (Finset.univ : Finset α).val.map (fun a => ({a}, P.real {a}))

/-! ### Unfolding lemmas and structural invariants for `huffmanLengthAux` -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanLengthAux_eq_step (s : Multiset (Finset α × ℝ)) (h : 2 ≤ s.card)
    (hg : HuffmanGrouping s) :
    huffmanLengthAux s =
      let step := (huffmanStep s h hg).val
      let A := step.1.1
      let B := step.2.1.1
      let s'' := step.2.2
      let g := huffmanLengthAux s''
      fun a => if a ∈ A ∨ a ∈ B then g a + 1 else g a := by
  rw [huffmanLengthAux]
  simp only [dif_pos hg, dif_pos h]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanLengthAux_eq_zero (s : Multiset (Finset α × ℝ)) (h : s.card ≤ 1)
    (hg : HuffmanGrouping s) :
    huffmanLengthAux s = fun _ => 0 := by
  have h' : ¬ 2 ≤ s.card := by omega
  rw [huffmanLengthAux]
  simp only [dif_pos hg, dif_neg h']

/-! ### Main definition -/

/-- Binary Huffman codeword-length function: `huffmanLengthAux` applied to the initial
singleton-group multiset of `P`. -/
noncomputable def huffmanLength (P : Measure α) : α → ℕ :=
  huffmanLengthAux (initMultiset P)

/-! ### Main theorems -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanLengthAux_pos_of_mem
    (s : Multiset (Finset α × ℝ)) (a : α)
    (hmem : ∃ p ∈ s, a ∈ p.1) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    0 < huffmanLengthAux s a := by
  -- strong induction on s.card
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    -- n = s.card ≥ 2
    rw [huffmanLengthAux_eq_step s hs hg]
    simp only
    set step := (huffmanStep s hs hg).val with hstep_def
    obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := huffmanStep_spec s hs hg
    by_cases h_in_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1
    · simp [h_in_AB]
    · simp only [h_in_AB, ↓reduceIte, gt_iff_lt]
      push Not at h_in_AB
      obtain ⟨h_not_A, h_not_B⟩ := h_in_AB
      obtain ⟨p, hp_mem, hp_a⟩ := hmem
      have hp_ne_x1 : p ≠ step.1 := by
        rintro rfl; exact h_not_A hp_a
      have hp_ne_x2 : p ≠ step.2.1 := by
        rintro rfl; exact h_not_B hp_a
      have hp_in_s' : p ∈ s.erase step.1 :=
        (Multiset.mem_erase_of_ne hp_ne_x1).mpr hp_mem
      have hp_in_s'' :
          p ∈ (s.erase step.1).erase step.2.1 :=
        (Multiset.mem_erase_of_ne hp_ne_x2).mpr hp_in_s'
      have hp_in_step22 : p ∈ step.2.2 := by
        rw [hshape]; exact Multiset.mem_cons_of_mem hp_in_s''
      have hmem' : ∃ q ∈ step.2.2, a ∈ q.1 := ⟨p, hp_in_step22, hp_a⟩
      have hs''_lt : step.2.2.card < s.card := huffmanStep_card_lt s hs hg
      by_cases hs''_two : 2 ≤ step.2.2.card
      · have hn' : step.2.2.card < n := by omega
        exact ih step.2.2.card hn' step.2.2 hmem' hs''_two hg'' rfl
      · -- step.2.2.card = 1, so the double-erase is empty, giving p ∉ 0, contradiction.
        push Not at hs''_two
        have h_ee_card : ((s.erase step.1).erase step.2.1).card = 0 := by
          have : step.2.2.card = ((s.erase step.1).erase step.2.1).card + 1 := by
            rw [hshape, Multiset.card_cons]
          omega
        have h_ee_zero : (s.erase step.1).erase step.2.1 = 0 :=
          Multiset.card_eq_zero.mp h_ee_card
        rw [h_ee_zero] at hp_in_s''
        exact absurd hp_in_s'' (Multiset.notMem_zero _)

omit [DecidableEq α] [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
lemma mem_initMultiset (P : Measure α) (a : α) :
    ∃ p ∈ initMultiset P, a ∈ p.1 := by
  refine ⟨({a}, P.real {a}), ?_, ?_⟩
  · -- ({a}, _) ∈ Finset.univ.val.map (fun a => ({a}, _))
    unfold initMultiset
    simp
  · simp

omit [DecidableEq α] [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
lemma initMultiset_huffmanGrouping (P : Measure α) :
    HuffmanGrouping (initMultiset P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Nodup: the map a ↦ ({a}, P.real {a}) is injective via the first coordinate.
    unfold initMultiset
    have hinj : Function.Injective
        (fun a : α => (({a} : Finset α), P.real {a})) := by
      intro a b hab
      simp only [Prod.mk.injEq, Finset.singleton_inj] at hab
      exact hab.1
    exact (Finset.univ : Finset α).nodup.map hinj
  · -- Nonempty
    intro p hp
    unfold initMultiset at hp
    rw [Multiset.mem_map] at hp
    obtain ⟨a, _, ha_eq⟩ := hp
    rw [← ha_eq]
    exact Finset.singleton_nonempty a
  · -- Disjoint: distinct singletons are disjoint.
    intro p hp q hq hpq
    unfold initMultiset at hp hq
    rw [Multiset.mem_map] at hp hq
    obtain ⟨a, _, ha_eq⟩ := hp
    obtain ⟨b, _, hb_eq⟩ := hq
    rw [← ha_eq, ← hb_eq]
    have hab : a ≠ b := by
      intro heq
      apply hpq
      rw [← ha_eq, ← hb_eq, heq]
    simp [hab]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- `huffmanLength P a > 0` when `Fintype.card α ≥ 2`. -/
theorem huffmanLength_pos (P : Measure α) [IsProbabilityMeasure P]
    (_hP : ∀ a, 0 < P.real {a}) (h_card : 2 ≤ Fintype.card α) (a : α) :
    0 < huffmanLength P a := by
  unfold huffmanLength
  have hcard_init : (initMultiset P).card = Fintype.card α := by
    unfold initMultiset
    rw [Multiset.card_map]
    rfl
  apply huffmanLengthAux_pos_of_mem _ _ (mem_initMultiset P a)
  · rw [hcard_init]; exact h_card
  · exact initMultiset_huffmanGrouping P

/-! ### Kraft inequality: auxiliary lemmas (constancy and invariants) -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanLengthAux_const_on_group
    (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s)
    (p : Finset α × ℝ) (hp : p ∈ s) (a b : α) (ha : a ∈ p.1) (hb : b ∈ p.1) :
    huffmanLengthAux s a = huffmanLengthAux s b := by
  induction hn : s.card using Nat.strong_induction_on
    generalizing s p a b with
  | _ n ih =>
    by_cases h2 : 2 ≤ s.card
    · rw [huffmanLengthAux_eq_step s h2 hg]
      simp only
      set step := (huffmanStep s h2 hg).val with hstep_def
      obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := huffmanStep_spec s h2 hg
      have hs''_lt : step.2.2.card < n := by
        have hlt : (huffmanStep s h2 hg).val.2.2.card < s.card :=
          huffmanStep_card_lt s h2 hg
        show (huffmanStep s h2 hg).val.2.2.card < n
        omega
      by_cases hp_x1 : p = step.1
      · -- p = x1 ⇒ a, b ∈ x1.1
        rw [hp_x1] at ha hb
        have ha_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1 := Or.inl ha
        have hb_AB : b ∈ step.1.1 ∨ b ∈ step.2.1.1 := Or.inl hb
        simp only [ha_AB, ↓reduceIte, hb_AB, Nat.add_right_cancel_iff]
        -- merged ∈ s'', a ∈ merged.1 = x1.1 ∪ x2.1, b ∈ same
        have ha_merged : a ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_left _ ha
        have hb_merged : b ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_left _ hb
        have hmerged_in :
            (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2) ∈ step.2.2 := by
          rw [hshape]; exact Multiset.mem_cons_self _ _
        exact ih step.2.2.card hs''_lt (s := step.2.2) hg''
          (p := (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2))
          hmerged_in (a := a) (b := b) ha_merged hb_merged rfl
      · by_cases hp_x2 : p = step.2.1
        · -- p = x2: a, b ∈ x2.1
          rw [hp_x2] at ha hb
          have ha_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1 := Or.inr ha
          have hb_AB : b ∈ step.1.1 ∨ b ∈ step.2.1.1 := Or.inr hb
          simp only [ha_AB, ↓reduceIte, hb_AB, Nat.add_right_cancel_iff]
          have ha_merged : a ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_right _ ha
          have hb_merged : b ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_right _ hb
          have hmerged_in :
              (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2) ∈ step.2.2 := by
            rw [hshape]; exact Multiset.mem_cons_self _ _
          exact ih step.2.2.card hs''_lt (s := step.2.2) hg''
            (p := (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2))
            hmerged_in (a := a) (b := b) ha_merged hb_merged rfl
        · -- p ∈ ee
          have hp_ee : p ∈ (s.erase step.1).erase step.2.1 := by
            have hp_s' : p ∈ s.erase step.1 :=
              (Multiset.mem_erase_of_ne hp_x1).mpr hp
            exact (Multiset.mem_erase_of_ne hp_x2).mpr hp_s'
          have hp_s'' : p ∈ step.2.2 := by
            rw [hshape]; exact Multiset.mem_cons_of_mem hp_ee
          have h_disj_x1 : Disjoint p.1 step.1.1 :=
            hg.disjoint hp hx1_mem hp_x1
          have h_disj_x2 : Disjoint p.1 step.2.1.1 := by
            have hx2_s : step.2.1 ∈ s := Multiset.mem_of_mem_erase hx2_mem
            exact hg.disjoint hp hx2_s hp_x2
          have ha_notAB : ¬ (a ∈ step.1.1 ∨ a ∈ step.2.1.1) := by
            rintro (ha1 | ha2)
            · exact (Finset.disjoint_left.mp h_disj_x1 ha) ha1
            · exact (Finset.disjoint_left.mp h_disj_x2 ha) ha2
          have hb_notAB : ¬ (b ∈ step.1.1 ∨ b ∈ step.2.1.1) := by
            rintro (hb1 | hb2)
            · exact (Finset.disjoint_left.mp h_disj_x1 hb) hb1
            · exact (Finset.disjoint_left.mp h_disj_x2 hb) hb2
          simp only [ha_notAB, ↓reduceIte, hb_notAB]
          exact ih step.2.2.card hs''_lt (s := step.2.2) hg''
            (p := p) hp_s'' (a := a) (b := b) ha hb rfl
    · rw [huffmanLengthAux_eq_zero s (by omega) hg]

/-- Per-group Kraft sum: `∑_p (∑_{a ∈ p.1} 2^(-huffmanLengthAux s a)) / p.1.card`.
By `huffmanLengthAux_const_on_group` this equals `∑_p 2^(-depth(p))`. -/
noncomputable def kraftPerGroup (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p =>
    (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma kraftPerGroup_eq_card_of_base
    (s : Multiset (Finset α × ℝ)) (h : s.card ≤ 1) (hg : HuffmanGrouping s) :
    kraftPerGroup s = (s.card : ℝ) := by
  unfold kraftPerGroup
  rw [huffmanLengthAux_eq_zero s h hg]
  -- Each term: (∑_{a ∈ p.1} 2^0) / p.1.card = 1, so the multiset sum equals s.card.
  have hterm : ∀ p ∈ s,
      (∑ a ∈ p.1, (2 : ℝ) ^ (-((0 : ℕ) : ℤ))) / (p.1.card : ℝ) = 1 := by
    intro p hp
    have hp_ne : p.1.Nonempty := hg.nonempty hp
    have hcard_pos : 0 < p.1.card := Finset.card_pos.mpr hp_ne
    have hcard_ne : (p.1.card : ℝ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
    rw [show -((0 : ℕ) : ℤ) = 0 from rfl, zpow_zero]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    field_simp
  rw [show s.map (fun p =>
      (∑ a ∈ p.1, (2 : ℝ) ^ (-((fun _ : α => (0 : ℕ)) a : ℤ))) / (p.1.card : ℝ))
      = s.map (fun _ => 1) from ?_]
  · rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  · apply Multiset.map_congr rfl
    intro p hp
    exact hterm p hp

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanStep_orig_decomp
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    s = (huffmanStep s hs hg).val.1 ::ₘ (huffmanStep s hs hg).val.2.1 ::ₘ
        ((s.erase (huffmanStep s hs hg).val.1).erase (huffmanStep s hs hg).val.2.1) := by
  obtain ⟨hx1_mem, hx2_mem, _, _⟩ := (huffmanStep s hs hg).property
  have h1 : s = (huffmanStep s hs hg).val.1 ::ₘ s.erase (huffmanStep s hs hg).val.1 :=
    (Multiset.cons_erase hx1_mem).symm
  have h2 : s.erase (huffmanStep s hs hg).val.1 =
      (huffmanStep s hs hg).val.2.1 ::ₘ
        (s.erase (huffmanStep s hs hg).val.1).erase (huffmanStep s hs hg).val.2.1 :=
    (Multiset.cons_erase hx2_mem).symm
  exact h1.trans (congr_arg ((huffmanStep s hs hg).val.1 ::ₘ ·) h2)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux s a = huffmanLengthAux s'' a + 1` for `a ∈ x1.1 ∪ x2.1`. -/
lemma huffmanLengthAux_step_merged
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    {a : α} (ha : a ∈ (huffmanStep s hs hg).val.1.1 ∨
                  a ∈ (huffmanStep s hs hg).val.2.1.1) :
    huffmanLengthAux s a =
      huffmanLengthAux (huffmanStep s hs hg).val.2.2 a + 1 := by
  rw [huffmanLengthAux_eq_step s hs hg]
  simp [ha]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux s a = huffmanLengthAux s'' a` for `a ∉ x1.1 ∪ x2.1`. -/
lemma huffmanLengthAux_step_other
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    {a : α} (ha : ¬ (a ∈ (huffmanStep s hs hg).val.1.1 ∨
                  a ∈ (huffmanStep s hs hg).val.2.1.1)) :
    huffmanLengthAux s a =
      huffmanLengthAux (huffmanStep s hs hg).val.2.2 a := by
  rw [huffmanLengthAux_eq_step s hs hg]
  simp [ha]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma huffmanLengthAux_step_eq_on_other_group
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (q : Finset α × ℝ)
    (hq : q ∈ (s.erase (huffmanStep s hs hg).val.1).erase
              (huffmanStep s hs hg).val.2.1)
    {a : α} (ha : a ∈ q.1) :
    huffmanLengthAux s a =
      huffmanLengthAux (huffmanStep s hs hg).val.2.2 a := by
  obtain ⟨hx1_mem, hx2_mem, _, _⟩ := (huffmanStep s hs hg).property
  have hq_s' : q ∈ s.erase (huffmanStep s hs hg).val.1 :=
    Multiset.mem_of_mem_erase hq
  have hq_s : q ∈ s := Multiset.mem_of_mem_erase hq_s'
  have hq_ne_x1 : q ≠ (huffmanStep s hs hg).val.1 := by
    intro heq; rw [heq] at hq_s'
    exact hg.nodup.notMem_erase hq_s'
  have hq_ne_x2 : q ≠ (huffmanStep s hs hg).val.2.1 := by
    intro heq; rw [heq] at hq
    exact (hg.nodup.erase _).notMem_erase hq
  have hx2_s : (huffmanStep s hs hg).val.2.1 ∈ s :=
    Multiset.mem_of_mem_erase hx2_mem
  have h_disj_x1 : Disjoint q.1 (huffmanStep s hs hg).val.1.1 :=
    hg.disjoint hq_s hx1_mem hq_ne_x1
  have h_disj_x2 : Disjoint q.1 (huffmanStep s hs hg).val.2.1.1 :=
    hg.disjoint hq_s hx2_s hq_ne_x2
  have ha_notAB : ¬ (a ∈ (huffmanStep s hs hg).val.1.1 ∨
                     a ∈ (huffmanStep s hs hg).val.2.1.1) := by
    rintro (h1 | h2)
    · exact (Finset.disjoint_left.mp h_disj_x1 ha) h1
    · exact (Finset.disjoint_left.mp h_disj_x2 ha) h2
  exact huffmanLengthAux_step_other s hs hg ha_notAB

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma kraftPerGroup_step
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    kraftPerGroup s = kraftPerGroup (huffmanStep s hs hg).val.2.2 := by
  obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := (huffmanStep s hs hg).property
  set x1 := (huffmanStep s hs hg).val.1 with hx1_def
  set x2 := (huffmanStep s hs hg).val.2.1 with hx2_def
  set s'' := (huffmanStep s hs hg).val.2.2 with hs''_def
  set ee := (s.erase x1).erase x2 with hee_def
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  have hshape' : s'' = merged ::ₘ ee := hshape
  have hx1_x2_ne : x1 ≠ x2 := by
    intro heq; rw [← heq] at hx2_mem
    exact hg.nodup.notMem_erase hx2_mem
  have hs_decomp : s = x1 ::ₘ x2 ::ₘ ee := huffmanStep_orig_decomp s hs hg
  have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
  have hx2_s : x2 ∈ s := Multiset.mem_of_mem_erase hx2_mem
  have hx2_ne : x2.1.Nonempty := hg.nonempty hx2_s
  have hmerged_ne : merged.1.Nonempty := hx1_ne.mono Finset.subset_union_left
  have hx1_card_pos : (0 : ℝ) < x1.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx1_ne
  have hx2_card_pos : (0 : ℝ) < x2.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx2_ne
  have hmerged_card_pos : (0 : ℝ) < merged.1.card := by
    exact_mod_cast Finset.card_pos.mpr hmerged_ne
  -- disjoint
  have hdisj_x1x2 : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_s hx1_x2_ne
  have hmerged_card : (merged.1.card : ℝ) = x1.1.card + x2.1.card := by
    show ((x1.1 ∪ x2.1).card : ℝ) = _
    rw [Finset.card_union_of_disjoint hdisj_x1x2]
    push_cast; ring
  -- depth values: pick a₀ ∈ x1.1, then d_x1 := huffmanLengthAux s a₀
  -- Need: depth is constant on x1.1, x2.1, merged.1
  -- Use constancy lemma + step relation
  -- Define depths as `huffmanLengthAux s'' a` for some specific a in merged.1
  -- Expand kraftPerGroup via sum_cons without rewriting hs_decomp inside huffmanLengthAux s.
  -- Instead use sum_cons directly via the multiset equality.
  have lhs_eq :
      kraftPerGroup s =
      (∑ a ∈ x1.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x1.1.card : ℝ)
      + ((∑ a ∈ x2.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x2.1.card : ℝ)
      + (ee.map (fun p =>
          (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum) := by
    unfold kraftPerGroup
    -- (s.map f).sum = ((x1 ::ₘ x2 ::ₘ ee).map f).sum (using hs_decomp at the multiset arg only)
    have : (s.map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum
        = ((x1 ::ₘ x2 ::ₘ ee).map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum := by
      exact congr_arg _ (congr_arg _ hs_decomp)
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  have rhs_eq :
      kraftPerGroup s'' =
      (∑ a ∈ merged.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (merged.1.card : ℝ)
      + (ee.map (fun p =>
          (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum := by
    unfold kraftPerGroup
    have : (s''.map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum
        = ((merged ::ₘ ee).map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum := by
      exact congr_arg _ (congr_arg _ hshape')
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  rw [lhs_eq, rhs_eq]
  -- LHS: f_s x1 + (f_s x2 + (ee.map f_s).sum)
  -- RHS: f_s'' merged + (ee.map f_s'').sum
  have h_ee_sum :
      (ee.map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum
      = (ee.map (fun p =>
          (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum := by
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro q hq
    apply congr_arg (· / (q.1.card : ℝ))
    apply Finset.sum_congr rfl
    intro a ha
    rw [huffmanLengthAux_step_eq_on_other_group s hs hg q hq ha]
  obtain ⟨a0, ha0⟩ := hx1_ne
  obtain ⟨b0, hb0⟩ := hx2_ne
  have hmerged_in_s'' : merged ∈ s'' := by rw [hshape']; exact Multiset.mem_cons_self _ _
  have ha0_merged : a0 ∈ merged.1 := Finset.mem_union_left _ ha0
  have hb0_merged : b0 ∈ merged.1 := Finset.mem_union_right _ hb0
  set d_m := huffmanLengthAux s'' a0 with hd_m_def
  have h_merged_const : ∀ a ∈ merged.1, huffmanLengthAux s'' a = d_m := by
    intro a ha
    exact huffmanLengthAux_const_on_group s'' hg'' merged hmerged_in_s'' a a0 ha ha0_merged
  -- For a ∈ x1.1 (⊆ merged.1): huffmanLengthAux s'' a = d_m, so huffmanLengthAux s a = d_m + 1
  have h_x1_aux : ∀ a ∈ x1.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 := by
      apply huffmanLengthAux_step_merged s hs hg
      exact Or.inl ha
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_left _ ha)
    omega
  have h_x2_aux : ∀ a ∈ x2.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 := by
      apply huffmanLengthAux_step_merged s hs hg
      exact Or.inr ha
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_right _ ha)
    omega
  have h_x1_term :
      (∑ a ∈ x1.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x1.1.card : ℝ)
      = (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) :=
    kraftTerm_of_const_depth (hg.nonempty hx1_mem) (fun a => (huffmanLengthAux s a : ℤ))
      ((d_m + 1 : ℕ) : ℤ) (fun a ha => by
        show (huffmanLengthAux s a : ℤ) = ((d_m + 1 : ℕ) : ℤ); exact_mod_cast h_x1_aux a ha)
  have h_x2_term :
      (∑ a ∈ x2.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x2.1.card : ℝ)
      = (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) :=
    kraftTerm_of_const_depth (hg.nonempty hx2_s) (fun a => (huffmanLengthAux s a : ℤ))
      ((d_m + 1 : ℕ) : ℤ) (fun a ha => by
        show (huffmanLengthAux s a : ℤ) = ((d_m + 1 : ℕ) : ℤ); exact_mod_cast h_x2_aux a ha)
  have h_merged_term :
      (∑ a ∈ merged.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (merged.1.card : ℝ)
      = (2 : ℝ) ^ (-(d_m : ℤ)) :=
    kraftTerm_of_const_depth hmerged_ne (fun a => (huffmanLengthAux s'' a : ℤ))
      (d_m : ℤ) (fun a ha => by
        show (huffmanLengthAux s'' a : ℤ) = (d_m : ℤ); exact_mod_cast h_merged_const a ha)
  rw [h_x1_term, h_x2_term, h_merged_term, h_ee_sum]
  -- Goal: 2^(-(d_m+1)) + (2^(-(d_m+1)) + rest) = 2^(-d_m) + rest
  -- i.e. 2^(-(d_m+1)) + 2^(-(d_m+1)) = 2^(-d_m)
  have h_two_half : (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ))
      = (2 : ℝ) ^ (-(d_m : ℤ)) := by
    have h_pow : (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(d_m : ℤ)) / 2 := by
      have : -((d_m + 1 : ℕ) : ℤ) = -(d_m : ℤ) - 1 := by push_cast; ring
      rw [this, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [h_pow]; ring
  linarith

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma kraftPerGroup_eq_one
    (s : Multiset (Finset α × ℝ)) (hs : 1 ≤ s.card) (hg : HuffmanGrouping s) :
    kraftPerGroup s = 1 := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases h2 : 2 ≤ s.card
    · rw [kraftPerGroup_step s h2 hg]
      have hlt : (huffmanStep s h2 hg).val.2.2.card < s.card :=
        huffmanStep_card_lt s h2 hg
      have hs'' : (huffmanStep s h2 hg).val.2.2.card < n := by
        show (huffmanStep s h2 hg).val.2.2.card < n; omega
      have hs''_card_pos : 1 ≤ (huffmanStep s h2 hg).val.2.2.card := by
        rw [huffmanStep_card_eq s h2 hg]; omega
      exact ih _ hs'' _ hs''_card_pos (huffmanStep_grouping s h2 hg) rfl
    · -- s.card = 1
      have h1 : s.card = 1 := by omega
      rw [kraftPerGroup_eq_card_of_base s (by omega) hg]
      simp [h1]

omit [Nonempty α] [MeasurableSingletonClass α] in
lemma kraftPerGroup_initMultiset_eq_kraft (P : Measure α) :
    kraftPerGroup (initMultiset P)
      = ∑ a : α, (2 : ℝ) ^ (-(huffmanLength P a : ℤ)) := by
  classical
  have hsimp : ∀ a : α,
      (∑ x ∈ ({a} : Finset α),
          (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) x : ℤ)))
        / (({a} : Finset α).card : ℝ)
      = (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) a : ℤ)) := by
    intro a
    simp
  unfold kraftPerGroup
  show ((initMultiset P).map _).sum
    = ∑ a : α, (2 : ℝ) ^ (-(huffmanLength P a : ℤ))
  unfold initMultiset
  rw [Multiset.map_map]
  unfold huffmanLength
  rw [show ∑ a : α, (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) a : ℤ))
      = ((Finset.univ : Finset α).val.map
          (fun a => (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) a : ℤ)))).sum from rfl]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  exact hsimp a

omit [MeasurableSingletonClass α] in
/-- The Kraft sum of `huffmanLength P` equals `1`. -/
@[entry_point]
theorem huffmanLength_kraft_eq_one (P : Measure α) [IsProbabilityMeasure P]
    (_hP : ∀ a, 0 < P.real {a}) :
    ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) = 1 := by
  rw [← kraftPerGroup_initMultiset_eq_kraft P]
  have hinit : HuffmanGrouping (initMultiset P) := initMultiset_huffmanGrouping P
  have hcard : 1 ≤ (initMultiset P).card := by
    unfold initMultiset
    rw [Multiset.card_map]
    have : 0 < Fintype.card α := Fintype.card_pos
    exact this
  exact kraftPerGroup_eq_one _ hcard hinit

omit [MeasurableSingletonClass α] in
/-- `huffmanLength P` satisfies the binary Kraft inequality (in fact with equality). -/
@[entry_point]
theorem huffmanLength_kraft_le_one (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) :
    ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) ≤ 1 := by
  rw [huffmanLength_kraft_eq_one P hP]

omit [MeasurableSingletonClass α] in
/-- A prefix-free binary code realising the `huffmanLength P` exists. -/
@[entry_point]
theorem exists_huffman_prefix_code
    (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) (h_card : 2 ≤ Fintype.card α) :
    ∃ c : α → List (Fin 2),
      Function.Injective c ∧
      (∀ a, (c a).length = huffmanLength P a) ∧
      InformationTheory.Shannon.ShannonCodeKraftReverse.IsPrefixFree c := by
  apply InformationTheory.Shannon.ShannonCodeKraftReverse.exists_prefix_code_of_kraft
    (D := 2) (by norm_num)
  · intro a; exact huffmanLength_pos P hP h_card a
  · exact huffmanLength_kraft_le_one P hP

/-! ### Cost-level recurrence for the optimality proof -/

/-- Multiset-level expected length: `∑_p p.2 * (∑_{a ∈ p.1} huffmanLengthAux s a) / p.1.card`.
By `huffmanLengthAux_const_on_group`, depth is constant on each group, so this equals
`∑_p p.2 * depth(p)`.
@audit:ok -/
noncomputable def huffmanCost (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p =>
    p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanCost s = huffmanCost s'' + (x1.2 + x2.2)` where `s''` is the merged multiset.
@audit:ok -/
lemma huffmanCost_step
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    huffmanCost s
      = huffmanCost (huffmanStep s hs hg).val.2.2
        + ((huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) := by
  obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := (huffmanStep s hs hg).property
  set x1 := (huffmanStep s hs hg).val.1 with hx1_def
  set x2 := (huffmanStep s hs hg).val.2.1 with hx2_def
  set s'' := (huffmanStep s hs hg).val.2.2 with hs''_def
  set ee := (s.erase x1).erase x2 with hee_def
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  have hshape' : s'' = merged ::ₘ ee := hshape
  have hx1_x2_ne : x1 ≠ x2 := by
    intro heq; rw [← heq] at hx2_mem
    exact hg.nodup.notMem_erase hx2_mem
  have hs_decomp : s = x1 ::ₘ x2 ::ₘ ee := huffmanStep_orig_decomp s hs hg
  have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
  have hx2_s : x2 ∈ s := Multiset.mem_of_mem_erase hx2_mem
  have hx2_ne : x2.1.Nonempty := hg.nonempty hx2_s
  have hmerged_ne : merged.1.Nonempty := hx1_ne.mono Finset.subset_union_left
  have hx1_card_pos : (0 : ℝ) < x1.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx1_ne
  have hx2_card_pos : (0 : ℝ) < x2.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx2_ne
  have hmerged_card_pos : (0 : ℝ) < merged.1.card := by
    exact_mod_cast Finset.card_pos.mpr hmerged_ne
  have hdisj_x1x2 : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_s hx1_x2_ne
  have hmerged_card : (merged.1.card : ℝ) = x1.1.card + x2.1.card := by
    show ((x1.1 ∪ x2.1).card : ℝ) = _
    rw [Finset.card_union_of_disjoint hdisj_x1x2]
    push_cast; ring
  -- Expand LHS and RHS per-group, mirroring the kraftPerGroup_step proof.
  have lhs_eq :
      huffmanCost s =
      x1.2 * ((∑ a ∈ x1.1, (huffmanLengthAux s a : ℝ)) / (x1.1.card : ℝ))
      + (x2.2 * ((∑ a ∈ x2.1, (huffmanLengthAux s a : ℝ)) / (x2.1.card : ℝ))
      + (ee.map (fun p =>
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum) := by
    unfold huffmanCost
    have : (s.map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum
        = ((x1 ::ₘ x2 ::ₘ ee).map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum := by
      exact congr_arg _ (congr_arg _ hs_decomp)
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  have rhs_eq :
      huffmanCost s'' =
      merged.2 * ((∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ)) / (merged.1.card : ℝ))
      + (ee.map (fun p =>
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
    unfold huffmanCost
    have : (s''.map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum
        = ((merged ::ₘ ee).map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
      exact congr_arg _ (congr_arg _ hshape')
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  rw [lhs_eq, rhs_eq]
  -- contribution equation for ee
  have h_ee_sum :
      (ee.map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum
      = (ee.map (fun p =>
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro q hq
    apply congr_arg (q.2 * ·)
    apply congr_arg (· / (q.1.card : ℝ))
    apply Finset.sum_congr rfl
    intro a ha
    rw [huffmanLengthAux_step_eq_on_other_group s hs hg q hq ha]
  obtain ⟨a0, ha0⟩ := hx1_ne
  obtain ⟨b0, hb0⟩ := hx2_ne
  have hmerged_in_s'' : merged ∈ s'' := by rw [hshape']; exact Multiset.mem_cons_self _ _
  have ha0_merged : a0 ∈ merged.1 := Finset.mem_union_left _ ha0
  have hb0_merged : b0 ∈ merged.1 := Finset.mem_union_right _ hb0
  set d_m := huffmanLengthAux s'' a0 with hd_m_def
  have h_merged_const : ∀ a ∈ merged.1, huffmanLengthAux s'' a = d_m := by
    intro a ha
    exact huffmanLengthAux_const_on_group s'' hg'' merged hmerged_in_s'' a a0 ha ha0_merged
  have h_x1_aux : ∀ a ∈ x1.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 :=
      huffmanLengthAux_step_merged s hs hg (Or.inl ha)
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_left _ ha)
    omega
  have h_x2_aux : ∀ a ∈ x2.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 :=
      huffmanLengthAux_step_merged s hs hg (Or.inr ha)
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_right _ ha)
    omega
  have h_x1_term :
      (∑ a ∈ x1.1, (huffmanLengthAux s a : ℝ)) / (x1.1.card : ℝ)
      = ((d_m : ℝ) + 1) := by
    have hsum : (∑ a ∈ x1.1, (huffmanLengthAux s a : ℝ))
        = (x1.1.card : ℝ) * ((d_m : ℝ) + 1) := by
      rw [show (x1.1.card : ℝ) * ((d_m : ℝ) + 1)
          = ∑ _x ∈ x1.1, ((d_m : ℝ) + 1) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_x1_aux a ha]; push_cast; ring
    rw [hsum]; field_simp
  have h_x2_term :
      (∑ a ∈ x2.1, (huffmanLengthAux s a : ℝ)) / (x2.1.card : ℝ)
      = ((d_m : ℝ) + 1) := by
    have hsum : (∑ a ∈ x2.1, (huffmanLengthAux s a : ℝ))
        = (x2.1.card : ℝ) * ((d_m : ℝ) + 1) := by
      rw [show (x2.1.card : ℝ) * ((d_m : ℝ) + 1)
          = ∑ _x ∈ x2.1, ((d_m : ℝ) + 1) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_x2_aux a ha]; push_cast; ring
    rw [hsum]; field_simp
  have h_merged_term :
      (∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ)) / (merged.1.card : ℝ)
      = (d_m : ℝ) := by
    have hsum : (∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ))
        = (merged.1.card : ℝ) * (d_m : ℝ) := by
      rw [show (merged.1.card : ℝ) * (d_m : ℝ)
          = ∑ _x ∈ merged.1, (d_m : ℝ) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_merged_const a ha]
    rw [hsum]; field_simp
  rw [h_x1_term, h_x2_term, h_merged_term, h_ee_sum]
  -- merged.2 = x1.2 + x2.2
  show x1.2 * ((d_m : ℝ) + 1)
      + (x2.2 * ((d_m : ℝ) + 1) + _)
      = (x1.2 + x2.2) * (d_m : ℝ) + _ + (x1.2 + x2.2)
  ring

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanCost s = 0` when `s.card ≤ 1`.
@audit:ok -/
lemma huffmanCost_eq_zero_of_base
    (s : Multiset (Finset α × ℝ)) (h : s.card ≤ 1) (hg : HuffmanGrouping s) :
    huffmanCost s = 0 := by
  unfold huffmanCost
  rw [huffmanLengthAux_eq_zero s h hg]
  rw [show s.map (fun p =>
      p.2 * ((∑ a ∈ p.1, ((fun _ : α => (0 : ℕ)) a : ℝ)) / (p.1.card : ℝ)))
      = s.map (fun _ => (0 : ℝ)) from ?_]
  · simp
  · apply Multiset.map_congr rfl
    intro p _
    simp

private lemma map_snd_erase {α : Type*} [DecidableEq α]
    (s : Multiset (Finset α × ℝ)) (x : Finset α × ℝ) (hx : x ∈ s) :
    (s.erase x).map Prod.snd = (s.map Prod.snd).erase x.2 := by
  classical
  conv_rhs => rw [show s = x ::ₘ s.erase x from (Multiset.cons_erase hx).symm]
  rw [Multiset.map_cons, Multiset.erase_cons_head]

/-- `huffmanCost` depends only on the probability multiset `s.map Prod.snd`.
@audit:ok -/
lemma huffmanCost_eq_of_prob_multiset
    {α : Type*} [DecidableEq α] [LinearOrder α]
    {β : Type*} [DecidableEq β] [LinearOrder β]
    (s : Multiset (Finset α × ℝ)) (t : Multiset (Finset β × ℝ))
    (hsg : HuffmanGrouping s) (htg : HuffmanGrouping t)
    (h : s.map Prod.snd = t.map Prod.snd) :
    huffmanCost s = huffmanCost t := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s t β with
  | _ n ih =>
    -- cardinalities agree
    have hcard_eq : s.card = t.card := by
      have h1 : (s.map Prod.snd).card = s.card := Multiset.card_map _ _
      have h2 : (t.map Prod.snd).card = t.card := Multiset.card_map _ _
      rw [← h1, ← h2, h]
    by_cases h2 : 2 ≤ s.card
    · -- step case
      have h2t : 2 ≤ t.card := by rw [← hcard_eq]; exact h2
      -- step decomposition for s
      set xs1 := (huffmanStep s h2 hsg).val.1 with hxs1
      set xs2 := (huffmanStep s h2 hsg).val.2.1 with hxs2
      set s'' := (huffmanStep s h2 hsg).val.2.2 with hs''
      obtain ⟨hxs1_mem, hxs2_mem, hshape_s, hg_s''⟩ := (huffmanStep s h2 hsg).property
      -- step decomposition for t
      set yt1 := (huffmanStep t h2t htg).val.1 with hyt1
      set yt2 := (huffmanStep t h2t htg).val.2.1 with hyt2
      set t'' := (huffmanStep t h2t htg).val.2.2 with ht''
      obtain ⟨hyt1_mem, hyt2_mem, hshape_t, hg_t''⟩ := (huffmanStep t h2t htg).property
      -- minimality of chosen probabilities
      have hxs1_min : ∀ z ∈ s, xs1.2 ≤ z.2 := huffmanStep_min_fst s h2 hsg
      have hxs2_min : ∀ z ∈ s.erase xs1, xs2.2 ≤ z.2 := huffmanStep_min_snd s h2 hsg
      have hyt1_min : ∀ z ∈ t, yt1.2 ≤ z.2 := huffmanStep_min_fst t h2t htg
      have hyt2_min : ∀ z ∈ t.erase yt1, yt2.2 ≤ z.2 := huffmanStep_min_snd t h2t htg
      have hxs2_mem_s : xs2 ∈ s := Multiset.mem_of_mem_erase hxs2_mem
      have hyt2_mem_t : yt2 ∈ t := Multiset.mem_of_mem_erase hyt2_mem
      -- identify xs1.2 = yt1.2 via antisymmetry over the shared probability multiset
      have hxs1_min_M : ∀ v ∈ s.map Prod.snd, xs1.2 ≤ v := by
        intro v hv
        rw [Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hxs1_min z hz
      have hyt1_min_M : ∀ v ∈ s.map Prod.snd, yt1.2 ≤ v := by
        intro v hv
        rw [h, Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hyt1_min z hz
      have hxs1v_M : xs1.2 ∈ s.map Prod.snd := Multiset.mem_map_of_mem _ hxs1_mem
      have hyt1v_M : yt1.2 ∈ s.map Prod.snd := by
        rw [h]; exact Multiset.mem_map_of_mem _ hyt1_mem
      have hv1_eq : xs1.2 = yt1.2 :=
        le_antisymm (hxs1_min_M _ hyt1v_M) (hyt1_min_M _ hxs1v_M)
      -- (s.erase xs1).map snd = (s.map snd).erase xs1.2
      have hsnd_s' : (s.erase xs1).map Prod.snd = (s.map Prod.snd).erase xs1.2 :=
        map_snd_erase s xs1 hxs1_mem
      have hsnd_t' : (t.erase yt1).map Prod.snd = (s.map Prod.snd).erase yt1.2 := by
        rw [map_snd_erase t yt1 hyt1_mem, ← h]
      -- xs2.2, yt2.2 are minima of (s.map snd).erase xs1.2 = ....erase yt1.2
      have hMe : (s.map Prod.snd).erase xs1.2 = (s.map Prod.snd).erase yt1.2 := by
        rw [hv1_eq]
      have hxs2v_Me : xs2.2 ∈ (s.map Prod.snd).erase xs1.2 := by
        rw [← hsnd_s']; exact Multiset.mem_map_of_mem _ hxs2_mem
      have hyt2v_Me : yt2.2 ∈ (s.map Prod.snd).erase yt1.2 := by
        rw [← hsnd_t']; exact Multiset.mem_map_of_mem _ hyt2_mem
      have hxs2_min_Me : ∀ v ∈ (s.map Prod.snd).erase xs1.2, xs2.2 ≤ v := by
        intro v hv
        rw [← hsnd_s', Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hxs2_min z hz
      have hyt2_min_Me : ∀ v ∈ (s.map Prod.snd).erase yt1.2, yt2.2 ≤ v := by
        intro v hv
        rw [← hsnd_t', Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hyt2_min z hz
      have hv2_eq : xs2.2 = yt2.2 := by
        apply le_antisymm
        · exact hxs2_min_Me _ (hMe ▸ hyt2v_Me)
        · exact hyt2_min_Me _ (hMe ▸ hxs2v_Me)
      -- penalties agree
      have hpen : xs1.2 + xs2.2 = yt1.2 + yt2.2 := by rw [hv1_eq, hv2_eq]
      -- s''.map snd = t''.map snd
      have hsnd_s'' : s''.map Prod.snd
          = (xs1.2 + xs2.2) ::ₘ (((s.map Prod.snd).erase xs1.2).erase xs2.2) := by
        rw [hs'', hshape_s, Multiset.map_cons]
        congr 1
        rw [map_snd_erase (s.erase xs1) xs2 hxs2_mem, hsnd_s']
      have hsnd_t'' : t''.map Prod.snd
          = (yt1.2 + yt2.2) ::ₘ (((s.map Prod.snd).erase yt1.2).erase yt2.2) := by
        rw [ht'', hshape_t, Multiset.map_cons]
        congr 1
        rw [map_snd_erase (t.erase yt1) yt2 hyt2_mem, hsnd_t']
      have hsnd_eq : s''.map Prod.snd = t''.map Prod.snd := by
        rw [hsnd_s'', hsnd_t'', hpen, hv1_eq, hv2_eq]
      -- induction hypothesis
      have hcard_s'' : s''.card < s.card := huffmanStep_card_lt s h2 hsg
      have hcard_s''_lt_n : s''.card < n := by omega
      have hcost_s'' : huffmanCost s'' = huffmanCost t'' :=
        ih s''.card hcard_s''_lt_n s'' t'' hg_s'' hg_t'' hsnd_eq rfl
      -- combine
      rw [huffmanCost_step s h2 hsg, huffmanCost_step t h2t htg,
          ← hxs1, ← hxs2, ← hs'', ← hyt1, ← hyt2, ← ht'',
          hcost_s'', hpen]
    · -- base case: s.card ≤ 1
      have hs_le : s.card ≤ 1 := by omega
      have ht_le : t.card ≤ 1 := by rw [← hcard_eq]; exact hs_le
      rw [huffmanCost_eq_zero_of_base s hs_le hsg,
          huffmanCost_eq_zero_of_base t ht_le htg]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- `expectedLength P (huffmanLength P) = huffmanCost (initMultiset P)`.
@audit:ok -/
lemma expectedLength_eq_huffmanCost (P : Measure α) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      = huffmanCost (initMultiset P) := by
  classical
  unfold InformationTheory.Shannon.ShannonCode.expectedLength huffmanCost
  unfold huffmanLength
  rw [show ∑ a : α, P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ)
      = ((Finset.univ : Finset α).val.map
          (fun a => P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ))).sum from rfl]
  conv_rhs => rw [initMultiset, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  -- each singleton group collapses: p.2 * (∑_{x∈{a}} d)/card = P.real{a} * (d a)
  show P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ)
    = P.real {a} * ((∑ x ∈ ({a} : Finset α),
        (huffmanLengthAux (initMultiset P) x : ℝ)) / (({a} : Finset α).card : ℝ))
  simp

end InformationTheory.Shannon.Huffman
