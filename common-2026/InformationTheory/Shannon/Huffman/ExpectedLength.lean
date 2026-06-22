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
import InformationTheory.Shannon.Huffman.KraftSum

/-!
# Expected length of the Huffman code

The multiset-level cost `huffmanCost` aggregates the expected codeword length of
`huffmanLengthAux`. Its merge-step recurrence and dependence only on the probability multiset are
the machinery used in the optimality proof; `expectedLength_eq_huffmanCost` ties it back to the
expected length of the published `huffmanLength`.

## Main definitions

* `huffmanCost` — multiset-level expected length used in the cost-level optimality proof.

## Main statements

* `huffmanCost_step` — `huffmanCost` decreases by the merged-group probability at each step.
* `huffmanCost_eq_of_prob_multiset` — `huffmanCost` depends only on the probability multiset.
* `expectedLength_eq_huffmanCost` — the expected length of `huffmanLength P` equals
  `huffmanCost (initMultiset P)`.
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Cost-level recurrence for the optimality proof -/

/-- Multiset-level expected length `∑_p p.2 * (∑_{a ∈ p.1} huffmanLengthAux s a) / p.1.card`.
Since depth is constant on each group, this equals `∑_p p.2 * depth(p)`.
@audit:ok -/
noncomputable def huffmanCost (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p ↦
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
      + (ee.map (fun p ↦
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum) := by
    unfold huffmanCost
    have : (s.map (fun p ↦
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum
        = ((x1 ::ₘ x2 ::ₘ ee).map (fun p ↦
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum := by
      exact congr_arg _ (congr_arg _ hs_decomp)
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  have rhs_eq :
      huffmanCost s'' =
      merged.2 * ((∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ)) / (merged.1.card : ℝ))
      + (ee.map (fun p ↦
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
    unfold huffmanCost
    have : (s''.map (fun p ↦
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum
        = ((merged ::ₘ ee).map (fun p ↦
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
      exact congr_arg _ (congr_arg _ hshape')
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  rw [lhs_eq, rhs_eq]
  -- contribution equation for ee
  have h_ee_sum :
      (ee.map (fun p ↦
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum
      = (ee.map (fun p ↦
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
  rw [show s.map (fun p ↦
      p.2 * ((∑ a ∈ p.1, ((fun _ : α ↦ (0 : ℕ)) a : ℝ)) / (p.1.card : ℝ)))
      = s.map (fun _ ↦ (0 : ℝ)) from ?_]
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
          (fun a ↦ P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ))).sum from rfl]
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
