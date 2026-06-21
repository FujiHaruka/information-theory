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
import InformationTheory.Shannon.Huffman.Length

/-!
# Kraft inequality for Huffman code lengths

The Kraft sum of the Huffman codeword-length function equals `1` exactly, hence the lengths
satisfy the binary Kraft inequality and a prefix-free code realising them exists. The auxiliary
constancy lemma `huffmanLengthAux_const_on_group` (depth is constant on each group) is shared with
the cost-level recurrence in `ExpectedLength`.

## Main statements

* `huffmanLength_kraft_eq_one` — the Kraft sum equals `1` exactly.
* `huffmanLength_kraft_le_one` — the Kraft inequality holds.
* `exists_huffman_prefix_code` — a prefix-free binary code of the Huffman lengths exists.
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

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

end InformationTheory.Shannon.Huffman
