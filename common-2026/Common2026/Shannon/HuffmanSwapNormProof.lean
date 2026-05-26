import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Common2026.Meta.EntryPoint

/-!
# T1-A'' — `strict_kraft_one_implies_pairing` keystone (genuine combinatorial heart)

A self-contained, fully-proved lemma that is the genuine combinatorial heart of the
Cover–Thomas swap-normalization argument and is **not present in Mathlib**.

**Statement**: if `l : β → ℕ` is positive and satisfies the binary Kraft equality
`∑ c, (2:ℝ)^(-(l c)) = 1`, then the maximum codeword length is attained by at least
**two distinct** symbols. Equivalently: there is no unique longest leaf.

This is the parity argument: scaling the Kraft equality by `2^M` (where `M` is the max
length) turns it into the natural-number identity `∑ c, 2^(M - l c) = 2^M`. If the max
were unique at `b`, the sum would be `1 + (even)`, i.e. odd, contradicting `2^M` even.
-/

namespace InformationTheory.Shannon.Huffman

open scoped BigOperators

/-- **Natural-number form of the Kraft equality.** If `l` is positive, `M` bounds every
`l c` (`∀ c, l c ≤ M`), and the real binary Kraft sum equals `1`, then the rescaled
natural-number sum `∑ c, 2^(M - l c)` equals `2^M`. -/
@[entry_point]
theorem kraft_one_nat_sum
    {β : Type*} [Fintype β]
    (l : β → ℕ) (M : ℕ) (hM : ∀ c, l c ≤ M)
    (hkraft : ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) = 1) :
    ∑ c : β, 2 ^ (M - l c) = 2 ^ M := by
  -- Work in ℝ via the cast, then transfer back by injectivity.
  have hcast : ((∑ c : β, 2 ^ (M - l c) : ℕ) : ℝ) = ((2 ^ M : ℕ) : ℝ) := by
    push_cast
    -- ∑ c, (2:ℝ)^(M - l c) = (2:ℝ)^M
    have hterm : ∀ c : β,
        ((2 : ℝ)) ^ (M - l c) = (2 : ℝ) ^ M * ((2 : ℝ)) ^ (-(l c : ℤ)) := by
      intro c
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hle : l c ≤ M := hM c
      have hzpow : (2 : ℝ) ^ M * ((2 : ℝ)) ^ (-(l c : ℤ))
          = (2 : ℝ) ^ ((M : ℤ) - (l c : ℤ)) := by
        rw [zpow_sub₀ h2, ← zpow_natCast (2 : ℝ) M, zpow_neg, div_eq_mul_inv]
      rw [hzpow, ← zpow_natCast (2 : ℝ) (M - l c)]
      congr 1
      push_cast [hle]
      omega
    calc (∑ c : β, (2 : ℝ) ^ (M - l c))
        = ∑ c : β, (2 : ℝ) ^ M * ((2 : ℝ)) ^ (-(l c : ℤ)) := by
          exact Finset.sum_congr rfl (fun c _ => hterm c)
      _ = (2 : ℝ) ^ M * ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) := by
          rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ M := by rw [hkraft, mul_one]
  exact_mod_cast hcast

/-- **Keystone: Kraft = 1 forbids a unique longest leaf.** If `l` is positive on a
`Fintype` and the binary Kraft sum is exactly `1`, then for every `b` there exists a
distinct `c ≠ b` with `l b ≤ l c`. In particular the maximum length is attained by at
least two symbols. -/
@[entry_point]
theorem strict_kraft_one_implies_pairing
    {β : Type*} [Fintype β] [DecidableEq β]
    (l : β → ℕ) (hl_pos : ∀ c, 0 < l c)
    (hkraft : ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) = 1)
    (b : β) (hb_max : ∀ c, l c ≤ l b) :
    ∃ c, c ≠ b ∧ l b ≤ l c := by
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ c, c ≠ b → l c < l b
  set M := l b with hM_def
  have hMpos : 0 < M := hl_pos b
  -- Natural-number Kraft identity: ∑ c, 2^(M - l c) = 2^M
  have hnat : ∑ c : β, 2 ^ (M - l c) = 2 ^ M := kraft_one_nat_sum l M hb_max hkraft
  -- Split off the b term.
  rw [← Finset.sum_erase_add (Finset.univ : Finset β) (fun c => 2 ^ (M - l c))
      (Finset.mem_univ b)] at hnat
  -- b term: 2^(M - l b) = 2^0 = 1
  have hb_term : 2 ^ (M - l b) = 1 := by rw [hM_def]; simp
  rw [hb_term] at hnat
  -- The erased sum is even: every c ≠ b has l c < M, so M - l c ≥ 1, so 2^(M-l c) even.
  have heven : Even (∑ c ∈ (Finset.univ : Finset β).erase b, 2 ^ (M - l c)) := by
    apply Finset.even_sum
    intro c hc
    have hc_ne : c ≠ b := Finset.ne_of_mem_erase hc
    have hlt : l c < M := hcon c hc_ne
    have hge1 : 1 ≤ M - l c := by omega
    obtain ⟨k, hk⟩ : ∃ k, M - l c = k + 1 := ⟨M - l c - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  -- So 2^M = (even) + 1 is odd, contradicting 2^M even (M ≥ 1).
  have hodd : Odd (2 ^ M) := by
    rw [← hnat]
    exact heven.add_one
  have hMeven : Even (2 ^ M) := by
    obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  exact (Nat.not_odd_iff_even.mpr hMeven) hodd

/-- **Corollary: a complete (Kraft = 1) binary code has two equal-longest leaves.**
For a positive length function whose binary Kraft sum is exactly `1`, the maximum codeword
length is attained by **two distinct** symbols. This is the structural fact Cover–Thomas
uses to argue that the two longest leaves of an optimal binary code are siblings. -/
@[entry_point]
theorem exists_two_equal_longest
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (l : β → ℕ) (hl_pos : ∀ c, 0 < l c)
    (hkraft : ∑ c : β, ((2 : ℝ)) ^ (-(l c : ℤ)) = 1) :
    ∃ c₁ c₂ : β, c₁ ≠ c₂ ∧ (∀ d, l d ≤ l c₁) ∧ l c₁ = l c₂ := by
  classical
  -- Pick a global argmax c₁.
  obtain ⟨c₁, _, hc₁⟩ :=
    Finset.exists_max_image (Finset.univ : Finset β) l Finset.univ_nonempty
  have hc₁_max : ∀ d, l d ≤ l c₁ := fun d => hc₁ d (Finset.mem_univ d)
  -- The keystone gives a distinct c₂ with l c₁ ≤ l c₂; maximality forces equality.
  obtain ⟨c₂, hc₂_ne, hc₂_ge⟩ := strict_kraft_one_implies_pairing l hl_pos hkraft c₁ hc₁_max
  refine ⟨c₁, c₂, fun h => hc₂_ne h.symm, hc₁_max, ?_⟩
  exact le_antisymm hc₂_ge (hc₁_max c₂)

end InformationTheory.Shannon.Huffman
