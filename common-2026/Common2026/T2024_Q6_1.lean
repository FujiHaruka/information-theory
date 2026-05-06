/-
東大 2024 第6問 (1)

  f(x) = x³ + 10x² + 20x とする。
  f(n) が素数となるような整数 n をすべて求めよ。

  答え: n = 1, -3, -7
    f(1)  = 1 + 10 + 20 = 31  (素数)
    f(-3) = -27 + 90 - 60 = 3 (素数)
    f(-7) = -343 + 490 - 140 = 7 (素数)

  方針:
    f(n) = n · (n² + 10n + 20) = n · q(n) と分解。
    f(n) が正の素数 p なら、|n| · |q(n)| = p で、p は素数の natAbs。
    よって |n| = 1 または |q(n)| = 1。

    Case |n| = 1:
      n = 1 ⟹ f(1) = 31 (素数 ✓)
      n = -1 ⟹ f(-1) = -11 < 0 (正でない ✗)

    Case |q(n)| = 1:
      q(n) = 1 ⟹ n²+10n+19 = 0
        (n+5)² = 6 だが平方が 6 となる整数は存在しない。
        n+5 ∈ {-2, -1, 0, 1, 2} の 5 ケースを列挙して反証。
      q(n) = -1 ⟹ n²+10n+21 = 0 ⟺ (n+3)(n+7) = 0 ⟹ n = -3, -7
        f(-3) = 3, f(-7) = 7 はどちらも素数。
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Common2026.T2024_Q6_1

/-- f(x) = x³ + 10x² + 20x。 -/
def f (x : ℤ) : ℤ := x ^ 3 + 10 * x ^ 2 + 20 * x

/-- 「素数」 (問題の定義: 2 以上で正の約数が 1 と自身のみの整数)。
    `Nat.Prime` を ℤ に持ち上げたもの。 -/
def IsPrimePos (p : ℤ) : Prop := 0 < p ∧ p.natAbs.Prime

/-- f(n) = n · (n² + 10n + 20)。 -/
private lemma f_factor (n : ℤ) : f n = n * (n ^ 2 + 10 * n + 20) := by
  unfold f; ring

/-- |a · b| が素数なら、|a| = 1 または |b| = 1。 -/
private lemma natAbs_eq_one_of_mul_prime {a b : ℤ}
    (h : (a * b).natAbs.Prime) : a.natAbs = 1 ∨ b.natAbs = 1 := by
  rw [Int.natAbs_mul] at h
  rcases h.eq_one_or_self_of_dvd a.natAbs ⟨b.natAbs, rfl⟩ with h1 | h1
  · exact Or.inl h1
  · right
    have ha_pos : 0 < a.natAbs := by
      rcases Nat.eq_zero_or_pos a.natAbs with h0 | h0
      · rw [h0, Nat.zero_mul] at h
        exact absurd h Nat.not_prime_zero
      · exact h0
    have heq : a.natAbs * b.natAbs = a.natAbs * 1 := by
      rw [Nat.mul_one]; exact h1.symm
    exact Nat.eq_of_mul_eq_mul_left ha_pos heq

/-- n.natAbs = 1 ⟺ n = 1 ∨ n = -1 (ℤ)。 -/
private lemma int_natAbs_eq_one {n : ℤ} (h : n.natAbs = 1) : n = 1 ∨ n = -1 := by
  rcases Int.natAbs_eq n with hh | hh
  · left
    rw [hh, h]; rfl
  · right
    rw [hh, h]; rfl

/-- n² + 10n + 19 = 0 は整数解なし。
    (n+5)² = 6 だが平方が 6 となる整数は存在しない。 -/
private lemma no_root_q_minus_one (n : ℤ) : n ^ 2 + 10 * n + 19 ≠ 0 := by
  intro h
  have hsq : (n + 5) ^ 2 = 6 := by linear_combination h
  have h_ub : n ≤ -3 := by
    have h1 : 6 * (n + 5) ≤ 15 := by nlinarith [hsq, sq_nonneg (n + 5 - 3)]
    omega
  have h_lb : -7 ≤ n := by
    have h1 : -15 ≤ 6 * (n + 5) := by nlinarith [hsq, sq_nonneg (n + 5 + 3)]
    omega
  -- n ∈ [-7, -3], 5 通りを列挙して矛盾
  interval_cases n <;> norm_num at hsq

/-- 主定理: f(n) が素数となる整数 n は {1, -3, -7}。 -/
theorem prime_solutions (n : ℤ) :
    IsPrimePos (f n) ↔ n = 1 ∨ n = -3 ∨ n = -7 := by
  constructor
  · -- 必要性
    intro hprime
    obtain ⟨hpos, hp⟩ := hprime
    rw [f_factor] at hpos hp
    rcases natAbs_eq_one_of_mul_prime hp with hn1 | hq1
    · -- n.natAbs = 1
      rcases int_natAbs_eq_one hn1 with rfl | rfl
      · exact Or.inl rfl
      · -- n = -1: 0 < -11 で矛盾
        norm_num at hpos
    · -- (n²+10n+20).natAbs = 1
      rcases int_natAbs_eq_one hq1 with hq | hq
      · -- q = 1: 整数解なし
        have : n ^ 2 + 10 * n + 19 = 0 := by linarith
        exact absurd this (no_root_q_minus_one n)
      · -- q = -1: (n+3)(n+7) = 0
        have hfact : (n + 3) * (n + 7) = 0 := by linear_combination hq
        rcases mul_eq_zero.mp hfact with hn | hn
        · right; left; linarith
        · right; right; linarith
  · -- 十分性: n = 1, -3, -7 で f(n) は 31, 3, 7
    rintro (rfl | rfl | rfl)
    · refine ⟨by norm_num [f], ?_⟩
      show (f 1).natAbs.Prime
      have : f 1 = 31 := by norm_num [f]
      rw [this]; decide
    · refine ⟨by norm_num [f], ?_⟩
      show (f (-3)).natAbs.Prime
      have : f (-3) = 3 := by norm_num [f]
      rw [this]; decide
    · refine ⟨by norm_num [f], ?_⟩
      show (f (-7)).natAbs.Prime
      have : f (-7) = 7 := by norm_num [f]
      rw [this]; decide

end Common2026.T2024_Q6_1
