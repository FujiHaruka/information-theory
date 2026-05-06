/-
第1問 (1)(ⅱ)

  U = { n ∈ ℕ | 2 ≤ n ∧ n ≤ 20 }
  A(a) = { k ∈ U | ∃ d ∈ ℕ, d ≠ 1 ∧ d ∣ k ∧ d ∣ a }
  B(b) = { k ∈ U | ∃ d ∈ ℕ, d ≠ 1 ∧ d ∣ k ∧ d ∣ b }

  2 ≤ a ≤ 9, 2 ≤ b ≤ 9 のとき
    1. Aᶜ の要素に 2 の倍数も 3 の倍数もないとき，a を求めよ
    2. A ∩ Bᶜ = {5} のとき，a, b を求めよ
-/

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

namespace Common2026.A_Q1_1_ii

def U (n : Nat) : Prop := 2 ≤ n ∧ n ≤ 20

def A (a k : Nat) : Prop := U k ∧ ∃ d : Nat, d ≠ 1 ∧ d ∣ k ∧ d ∣ a

def B (b k : Nat) : Prop := U k ∧ ∃ d : Nat, d ≠ 1 ∧ d ∣ k ∧ d ∣ b

/-- A の U における補集合。 -/
def Ac (a k : Nat) : Prop := U k ∧ ¬ A a k

/-- B の U における補集合。 -/
def Bc (b k : Nat) : Prop := U k ∧ ¬ B b k

/-- 任意の `a` について、`∃ d ≠ 1, d ∣ 2 ∧ d ∣ a` は `2 ∣ a` と同値。 -/
private lemma exists_dvd_two (a : Nat) :
    (∃ d : Nat, d ≠ 1 ∧ d ∣ 2 ∧ d ∣ a) ↔ 2 ∣ a := by
  constructor
  · rintro ⟨d, hd1, hd2, hda⟩
    have hd_le : d ≤ 2 := Nat.le_of_dvd (by decide) hd2
    interval_cases d
    · exact absurd hd2 (by decide)
    · exact absurd rfl hd1
    · exact hda
  · intro h
    exact ⟨2, by decide, by decide, h⟩

/-- 任意の `a` について、`∃ d ≠ 1, d ∣ 3 ∧ d ∣ a` は `3 ∣ a` と同値。 -/
private lemma exists_dvd_three (a : Nat) :
    (∃ d : Nat, d ≠ 1 ∧ d ∣ 3 ∧ d ∣ a) ↔ 3 ∣ a := by
  constructor
  · rintro ⟨d, hd1, hd3, hda⟩
    have hd_le : d ≤ 3 := Nat.le_of_dvd (by decide) hd3
    interval_cases d
    · exact absurd hd3 (by decide)
    · exact absurd rfl hd1
    · exact absurd hd3 (by decide)
    · exact hda
  · intro h
    exact ⟨3, by decide, by decide, h⟩

/-- 任意の `a` について、`∃ d ≠ 1, d ∣ 5 ∧ d ∣ a` は `5 ∣ a` と同値。 -/
private lemma exists_dvd_five (a : Nat) :
    (∃ d : Nat, d ≠ 1 ∧ d ∣ 5 ∧ d ∣ a) ↔ 5 ∣ a := by
  constructor
  · rintro ⟨d, hd1, hd5, hda⟩
    have hd_le : d ≤ 5 := Nat.le_of_dvd (by decide) hd5
    interval_cases d
    · exact absurd hd5 (by decide)
    · exact absurd rfl hd1
    · exact absurd hd5 (by decide)
    · exact absurd hd5 (by decide)
    · exact absurd hd5 (by decide)
    · exact hda
  · intro h
    exact ⟨5, by decide, by decide, h⟩

/-- (i) 2 ≤ a ≤ 9 のとき、Aᶜ の要素に 2 の倍数も 3 の倍数もないことと a = 6 は同値。 -/
theorem part_i (a : Nat) (ha2 : 2 ≤ a) (ha9 : a ≤ 9) :
    (∀ k, Ac a k → ¬(2 ∣ k) ∧ ¬(3 ∣ k)) ↔ a = 6 := by
  constructor
  · intro h
    have h2a : 2 ∣ a := by
      by_contra h2
      have hAc : Ac a 2 := by
        refine ⟨⟨by decide, by decide⟩, ?_⟩
        rintro ⟨_, hex⟩
        exact h2 ((exists_dvd_two a).mp hex)
      exact (h 2 hAc).1 (by decide)
    have h3a : 3 ∣ a := by
      by_contra h3
      have hAc : Ac a 3 := by
        refine ⟨⟨by decide, by decide⟩, ?_⟩
        rintro ⟨_, hex⟩
        exact h3 ((exists_dvd_three a).mp hex)
      exact (h 3 hAc).2 (by decide)
    omega
  · rintro rfl
    rintro k ⟨hkU, hkA⟩
    refine ⟨?_, ?_⟩
    · intro h2k
      exact hkA ⟨hkU, 2, by decide, h2k, by decide⟩
    · intro h3k
      exact hkA ⟨hkU, 3, by decide, h3k, by decide⟩

/-- (ii) 2 ≤ a, b ≤ 9 のとき、A ∩ Bᶜ = {5} と (a, b) = (5, 6) は同値。 -/
theorem part_ii (a b : Nat)
    (ha2 : 2 ≤ a) (ha9 : a ≤ 9) (hb2 : 2 ≤ b) (hb9 : b ≤ 9) :
    (∀ k, (A a k ∧ Bc b k) ↔ k = 5) ↔ (a = 5 ∧ b = 6) := by
  constructor
  · intro h
    -- k = 5 から 5 ∣ a と 5 ∤ b が従う
    have h5_pos : A a 5 ∧ Bc b 5 := (h 5).mpr rfl
    have h5a : 5 ∣ a := (exists_dvd_five a).mp h5_pos.1.2
    have ha_eq : a = 5 := by omega
    subst ha_eq
    have h5b_not : ¬ (5 ∣ b) := fun h5b =>
      h5_pos.2.2 ⟨⟨by decide, by decide⟩, 5, by decide, by decide, h5b⟩
    -- k = 10 から 2 ∣ b
    have hA10 : A 5 10 :=
      ⟨⟨by decide, by decide⟩, 5, by decide, by decide, by decide⟩
    have hB10 : B b 10 := by
      by_contra hnB10
      have h10eq5 : (10 : Nat) = 5 :=
        (h 10).mp ⟨hA10, ⟨by decide, by decide⟩, hnB10⟩
      exact absurd h10eq5 (by decide)
    have h2b : 2 ∣ b := by
      obtain ⟨_, d, hd1, hd10, hdb⟩ := hB10
      have hd_le : d ≤ 10 := Nat.le_of_dvd (by decide) hd10
      interval_cases d
      · exact absurd hd10 (by decide)
      · exact absurd rfl hd1
      · exact hdb
      · exact absurd hd10 (by decide)
      · exact absurd hd10 (by decide)
      · exact absurd hdb h5b_not
      · exact absurd hd10 (by decide)
      · exact absurd hd10 (by decide)
      · exact absurd hd10 (by decide)
      · exact absurd hd10 (by decide)
      · exfalso
        have h10b : 10 ≤ b := Nat.le_of_dvd (by omega) hdb
        omega
    -- k = 15 から 3 ∣ b
    have hA15 : A 5 15 :=
      ⟨⟨by decide, by decide⟩, 5, by decide, by decide, by decide⟩
    have hB15 : B b 15 := by
      by_contra hnB15
      have h15eq5 : (15 : Nat) = 5 :=
        (h 15).mp ⟨hA15, ⟨by decide, by decide⟩, hnB15⟩
      exact absurd h15eq5 (by decide)
    have h3b : 3 ∣ b := by
      obtain ⟨_, d, hd1, hd15, hdb⟩ := hB15
      have hd_le : d ≤ 15 := Nat.le_of_dvd (by decide) hd15
      interval_cases d
      · exact absurd hd15 (by decide)
      · exact absurd rfl hd1
      · exact absurd hd15 (by decide)
      · exact hdb
      · exact absurd hd15 (by decide)
      · exact absurd hdb h5b_not
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exact absurd hd15 (by decide)
      · exfalso
        have h15b : 15 ≤ b := Nat.le_of_dvd (by omega) hdb
        omega
    have hb_eq : b = 6 := by omega
    exact ⟨rfl, hb_eq⟩
  · rintro ⟨rfl, rfl⟩
    intro k
    constructor
    · rintro ⟨hA, hBc⟩
      obtain ⟨hkU, d, hd1, hdk, hd5⟩ := hA
      have hd_le : d ≤ 5 := Nat.le_of_dvd (by decide) hd5
      have h5k : 5 ∣ k := by
        interval_cases d
        · exact absurd hd5 (by decide)
        · exact absurd rfl hd1
        · exact absurd hd5 (by decide)
        · exact absurd hd5 (by decide)
        · exact absurd hd5 (by decide)
        · exact hdk
      have h2nk : ¬ (2 ∣ k) := fun h2k =>
        hBc.2 ⟨hkU, 2, by decide, h2k, by decide⟩
      have h3nk : ¬ (3 ∣ k) := fun h3k =>
        hBc.2 ⟨hkU, 3, by decide, h3k, by decide⟩
      obtain ⟨hk2, hk20⟩ := hkU
      omega
    · rintro rfl
      refine ⟨⟨⟨by decide, by decide⟩, 5, by decide, by decide, by decide⟩,
              ⟨by decide, by decide⟩, ?_⟩
      rintro ⟨_, d, hd1, hd5, hd6⟩
      have hd_le : d ≤ 5 := Nat.le_of_dvd (by decide) hd5
      interval_cases d
      · exact absurd hd5 (by decide)
      · exact absurd rfl hd1
      · exact absurd hd5 (by decide)
      · exact absurd hd5 (by decide)
      · exact absurd hd5 (by decide)
      · exact absurd hd6 (by decide)

end Common2026.A_Q1_1_ii
