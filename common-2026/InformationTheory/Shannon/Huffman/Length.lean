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
equipped with a probability measure, following Cover–Thomas Theorem 5.8.1. This file holds the
recursive construction and its positivity invariant; the Kraft sum and the cost-level recurrence
live in `KraftSum` and `ExpectedLength`.

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

## Main statements

* `groupKey_injective` — `groupKey` is injective (probability + colex breaks all ties).
* `huffmanStep_min_fst` / `huffmanStep_min_snd` — the two extracted groups have minimum
  probability in `s` (resp. `s.erase .val.1`).
* `huffmanLength_pos` — `huffmanLength P a > 0` when `card α ≥ 2`.

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

end InformationTheory.Shannon.Huffman
