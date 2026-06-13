import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Huffman.Optimality
import InformationTheory.Shannon.Huffman.SwapNormCompletion
import InformationTheory.Shannon.Huffman.SwapNormProof

/-!
# Swap normalization and Huffman optimality (Cover–Thomas Theorem 5.8.1)

Provides the constructive proof that `SwapNormalizationHypothesis` holds
(`swap_normalization_proof`), and thereby establishes the unconditional optimality theorem
`huffmanLength_optimal`.

## Main statements

* `swap_normalization_strong` — given a Kraft-feasible `ll` and the two minimum-probability
  elements `(a, b)` (a = global-min, b = second-min), there exists `l_norm` with
  `l_norm a = l_norm b`, Kraft ≤ 1, and expected length ≤ that of `ll`.
* `swap_normalization_proof` — discharges `SwapNormalizationHypothesis` unconditionally.
* `huffmanLength_optimal` — Cover–Thomas Theorem 5.8.1: `huffmanLength P` is optimal among
  all Kraft-feasible length functions.

## Implementation notes

The swap normalization proof proceeds in three steps:
1. Shorten `ll` to a complete code `l1` (Kraft = 1) via `shorten_to_kraft_one`.
2. Find two equal-longest leaves `c₁ ≠ c₂` of `l1` via `exists_two_equal_longest`.
3. Swap `a ↔ c₁` then `b ↔ c₂` using `swap_step_le`, so that `l_norm a = l_norm b = L`.
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

universe u

/-- Constructive core of swap normalization: given Kraft-feasible `ll` and minimum-probability
pair `(a, b)` (`a` = global-min, `b` = second-min), produces `l_norm` satisfying
`l_norm a = l_norm b`, Kraft ≤ 1, positive, and `expectedLength Q l_norm ≤ expectedLength Q ll`. -/
@[entry_point]
theorem swap_normalization_strong
    {β : Type u} [Fintype β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  classical
  have h_card2 : 2 ≤ Fintype.card β := by omega
  -- Step 1: shorten to Kraft = 1
  obtain ⟨l1, hl1_pos, hl1_le, hl1_kraft1⟩ :=
    shorten_to_kraft_one ll hll_pos hll_kraft h_card2
  have hl1_kraft_le : ∑ x : β, ((2 : ℝ)) ^ (-(l1 x : ℤ)) ≤ 1 := le_of_eq hl1_kraft1
  -- E[l1] ≤ E[ll]  (pointwise l1 ≤ ll, probabilities nonneg)
  have hE_l1_le_ll :
      InformationTheory.Shannon.ShannonCode.expectedLength Q l1
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
    unfold InformationTheory.Shannon.ShannonCode.expectedLength
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    exact_mod_cast hl1_le x
  -- Step 2: two equal-longest leaves c₁ ≠ c₂
  obtain ⟨c₁, c₂, hc12, hc1_max, hc12_eq⟩ :=
    exists_two_equal_longest l1 hl1_pos hl1_kraft1
  set L := l1 c₁ with hL_def
  have hc2_L : l1 c₂ = L := hc12_eq.symm
  -- Choose labeling (d₁, d₂) so that d₂ ≠ a
  obtain ⟨d₁, d₂, hd12, hd1_L, hd2_L, hd2_ne_a⟩ :
      ∃ d₁ d₂ : β, d₁ ≠ d₂ ∧ l1 d₁ = L ∧ l1 d₂ = L ∧ d₂ ≠ a := by
    by_cases hc2a : c₂ = a
    · -- c₂ = a, so use (c₂, c₁); need c₁ ≠ a, which is hc12 with c₂ = a
      refine ⟨c₂, c₁, hc12.symm, hc2_L, rfl, ?_⟩
      rw [hc2a] at hc12; exact hc12
    · exact ⟨c₁, c₂, hc12, rfl, hc2_L, hc2a⟩
  -- Step A: swap a ↔ d₁ on l1
  have hA := swap_step_le Q l1 hl1_pos hl1_kraft_le a d₁
    (by rw [hd1_L]; exact hc1_max a) (h_a_min d₁)
  set lA : β → ℕ := l1 ∘ Equiv.swap a d₁ with hlA_def
  obtain ⟨hlA_pos, hlA_kraft, hlA_E_le, hlA_a, hlA_d₁⟩ := hA
  -- lA d₂ = L  (d₂ ∉ {a, d₁}? d₂ ≠ a always; if d₂ = d₁ then lA d₂ = l1 a, handle generally)
  have hlA_d₂ : lA d₂ = L := by
    rw [hlA_def]
    show l1 (Equiv.swap a d₁ d₂) = L
    by_cases hd2d1 : d₂ = d₁
    · rw [hd2d1, Equiv.swap_apply_right]
      -- l1 a — but we need this = L; only holds if a is a max leaf. Not general.
      -- d₂ ≠ d₁ by hd12, so this branch is vacuous.
      exact absurd hd2d1 (Ne.symm hd12)
    · rw [Equiv.swap_apply_of_ne_of_ne hd2_ne_a hd2d1]; exact hd2_L
  -- lA b ≤ L  (l1 of anything ≤ L)
  have hlA_b_le : lA b ≤ L := by
    rw [hlA_def]; show l1 (Equiv.swap a d₁ b) ≤ L
    exact hc1_max (Equiv.swap a d₁ b)
  -- Step B: swap b ↔ d₂ on lA
  have hB := swap_step_le Q lA hlA_pos hlA_kraft b d₂
    (by rw [hlA_d₂]; exact hlA_b_le) (h_b_min d₂ hd2_ne_a)
  set lB : β → ℕ := lA ∘ Equiv.swap b d₂ with hlB_def
  obtain ⟨hlB_pos, hlB_kraft, hlB_E_le, hlB_b, hlB_d₂⟩ := hB
  -- l_norm := lB.  l_norm a = L (untouched by swap b d₂ since a ∉ {b, d₂}), l_norm b = L.
  have hlB_a : lB a = L := by
    rw [hlB_def]; show lA (Equiv.swap b d₂ a) = L
    rw [Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hd2_ne_a)]
    rw [hlA_a, hd1_L]
  -- l_norm a = l_norm b
  have h_eq_ab : lB a = lB b := by rw [hlB_a, hlB_b, hlA_d₂]
  refine ⟨lB, hlB_pos, hlB_kraft, h_eq_ab, ?_⟩
  -- E[lB] ≤ E[lA] ≤ E[l1] ≤ E[ll]
  calc InformationTheory.Shannon.ShannonCode.expectedLength Q lB
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q lA := hlB_E_le
    _ ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q l1 := hlA_E_le
    _ ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := hE_l1_le_ll

/-! ### Unconditional Huffman optimality -/
@[entry_point]
theorem swap_normalization_proof : SwapNormalizationHypothesis.{u} := by
  intro β _ _ _ _ _ _ Q _ ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card
  exact swap_normalization_strong Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card

/-- **Cover–Thomas Theorem 5.8.1**: `huffmanLength P` minimizes expected codeword length
among all positive Kraft-feasible length functions.
@audit:ok -/
@[entry_point]
theorem huffmanLength_optimal
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_aux (Fintype.card α) swap_normalization_proof
    P hP l hl_pos hl_kraft rfl

end InformationTheory.Shannon.Huffman
