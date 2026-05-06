/-
第1問 (1)(ⅰ)

  U = { n ∈ ℕ | 2 ≤ n ∧ n ≤ 20 }
  A(a) = { k ∈ U | ∃ d ∈ ℕ, d ≠ 1 ∧ d ∣ k ∧ d ∣ a }
  B(b) = { k ∈ U | ∃ d ∈ ℕ, d ≠ 1 ∧ d ∣ k ∧ d ∣ b }

  a = 3, b = 4 のとき
    1. A を求めよ
    2. B を求めよ
    3. A ∩ B を求めよ
    4. A ∩ Bᶜ を求めよ（Bᶜ は U における補集合）
-/

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

namespace Common2026.A_Q1_1_i

def U (n : Nat) : Prop := 2 ≤ n ∧ n ≤ 20

def A (a k : Nat) : Prop := U k ∧ ∃ d : Nat, d ≠ 1 ∧ d ∣ k ∧ d ∣ a

def B (b k : Nat) : Prop := U k ∧ ∃ d : Nat, d ≠ 1 ∧ d ∣ k ∧ d ∣ b

/-- B の U における補集合。`ᶜ` は Lean のトークンとして予約されているため別名にしている。 -/
def Bc (b k : Nat) : Prop := U k ∧ ¬ B b k

/-- a = 3 の場合、`∃ d ≠ 1, d ∣ k ∧ d ∣ 3` は `3 ∣ k` と同値。 -/
private lemma exists_dvd_three (k : Nat) :
    (∃ d : Nat, d ≠ 1 ∧ d ∣ k ∧ d ∣ 3) ↔ 3 ∣ k := by
  constructor
  · rintro ⟨d, hd1, hdk, hd3⟩
    have hd_le : d ≤ 3 := Nat.le_of_dvd (by decide) hd3
    interval_cases d
    · exact absurd hd3 (by decide)
    · exact absurd rfl hd1
    · exact absurd hd3 (by decide)
    · exact hdk
  · intro h
    exact ⟨3, by decide, h, dvd_refl _⟩

/-- b = 4 の場合、`∃ d ≠ 1, d ∣ k ∧ d ∣ 4` は `2 ∣ k` と同値。 -/
private lemma exists_dvd_four (k : Nat) :
    (∃ d : Nat, d ≠ 1 ∧ d ∣ k ∧ d ∣ 4) ↔ 2 ∣ k := by
  constructor
  · rintro ⟨d, hd1, hdk, hd4⟩
    have hd_le : d ≤ 4 := Nat.le_of_dvd (by decide) hd4
    interval_cases d
    · exact absurd hd4 (by decide)
    · exact absurd rfl hd1
    · exact hdk
    · exact absurd hd4 (by decide)
    · exact (by decide : (2 : Nat) ∣ 4).trans hdk
  · intro h
    exact ⟨2, by decide, h, by decide⟩

/-- 1. a = 3 のとき A = {3, 6, 9, 12, 15, 18}。 -/
theorem A_of_three :
    ∀ k, A 3 k ↔
      k = 3 ∨ k = 6 ∨ k = 9 ∨ k = 12 ∨ k = 15 ∨ k = 18 := by
  intro k
  unfold A U
  rw [exists_dvd_three]
  constructor
  · rintro ⟨⟨h2, h20⟩, hk⟩
    interval_cases k <;> revert hk <;> decide
  · rintro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨⟨by decide, by decide⟩, by decide⟩

/-- 2. b = 4 のとき B = {2, 4, 6, 8, 10, 12, 14, 16, 18, 20}。 -/
theorem B_of_four :
    ∀ k, B 4 k ↔
      k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨
      k = 12 ∨ k = 14 ∨ k = 16 ∨ k = 18 ∨ k = 20 := by
  intro k
  unfold B U
  rw [exists_dvd_four]
  constructor
  · rintro ⟨⟨h2, h20⟩, hk⟩
    interval_cases k <;> revert hk <;> decide
  · rintro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨⟨by decide, by decide⟩, by decide⟩

/-- 3. a = 3, b = 4 のとき A ∩ B = {6, 12, 18}。 -/
theorem A_inter_B :
    ∀ k, (A 3 k ∧ B 4 k) ↔ k = 6 ∨ k = 12 ∨ k = 18 := by
  intro k
  rw [A_of_three, B_of_four]
  omega

/-- 4. a = 3, b = 4 のとき A ∩ Bᶜ = {3, 9, 15}。 -/
theorem A_inter_Bc :
    ∀ k, (A 3 k ∧ Bc 4 k) ↔ k = 3 ∨ k = 9 ∨ k = 15 := by
  intro k
  unfold Bc U
  rw [A_of_three, B_of_four]
  omega

end Common2026.A_Q1_1_i
