/-
東大 2024 第6問 (2)

  a, b を整数の定数とし、g(x) = x³ + ax² + bx とする。
  g(n) が素数となるような整数 n の個数は 3 個以下であることを示せ。

  方針:
    g(n) = n · (n² + an + b) = n · q(n) と分解。
    g(n) が正の素数 ⟹ |n| · |q(n)| が素数 ⟹ |n| = 1 or |q(n)| = 1。
    したがって n は次の 4 通りのいずれか:
      (A)  n = 1                     かつ q(1) が素数
      (B)  n = -1                    かつ -q(-1) が素数
      (C)  q(n) = 1, n ≥ 2           かつ n が素数
      (D)  q(n) = -1, n ≤ -2         かつ -n が素数

    主な制約:
      (F1) C 型と D 型は同時に存在しない。
           q(α) = 1, q(γ) = -1 ⟹ (α-γ)(α+γ+a) = 2 だが
           α ≥ 2, γ ≤ -2 で α-γ ≥ 4 となり整数解なし。
      (F2) C 型が 2 つあると q(-1) ≥ 13 となり、B 型は存在しない。
           q(α) = q(β) = 1 (α ≠ β, ≥ 2) ⟹ q(-1) = (α+1)(β+1) + 1 ≥ 13。
      (F3) D 型が 2 つあると q(-1) ≥ 1 となり、B 型は存在しない。
           q(γ) = q(δ) = -1 (γ ≠ δ, ≤ -2) ⟹ q(-1) = (γ+1)(δ+1) - 1 ≥ 1。

    さらに、(A) は最大 1 個、(B) は最大 1 個、(C) は最大 2 個 (q-1=0 の根)、
    (D) は最大 2 個 (q+1=0 の根)。これらと F1, F2, F3 から
    A + B + C + D ≤ 3 が従う。

  形式化:
    「相異なる 4 つの整数 n₁, n₂, n₃, n₄ で g(n_i) がすべて素数になることはない」
    という形で証明する。
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Common2026.T2024_Q6_2

/-- q(x) = x² + ax + b。 -/
def q (a b x : ℤ) : ℤ := x ^ 2 + a * x + b

/-- g(x) = x³ + ax² + bx = x · q(x)。 -/
def g (a b x : ℤ) : ℤ := x ^ 3 + a * x ^ 2 + b * x

/-- 「素数」 (問題の定義: 2 以上で正の約数が 1 と自身のみの整数)。 -/
def IsPrimePos (p : ℤ) : Prop := 0 < p ∧ p.natAbs.Prime

/-- g(n) = n · q(n)。 -/
private lemma g_factor (a b x : ℤ) : g a b x = x * q a b x := by
  unfold g q; ring

/-! ### natAbs 関連の補助補題 -/

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

/-- n.natAbs = 1 ⟺ n = 1 ∨ n = -1。 -/
private lemma int_natAbs_eq_one {n : ℤ} (h : n.natAbs = 1) : n = 1 ∨ n = -1 := by
  rcases Int.natAbs_eq n with hh | hh
  · left; rw [hh, h]; rfl
  · right; rw [hh, h]; rfl

/-! ### 分類補題 -/

/-- 強化版分類: g(n) が素数なら、n は 4 通りのいずれか。 -/
private lemma category (a b n : ℤ) (h : IsPrimePos (g a b n)) :
    n = 1 ∨ n = -1 ∨ (q a b n = 1 ∧ 2 ≤ n) ∨ (q a b n = -1 ∧ n ≤ -2) := by
  obtain ⟨hpos, hp⟩ := h
  rw [g_factor] at hpos hp
  rcases natAbs_eq_one_of_mul_prime hp with hn1 | hq1
  · rcases int_natAbs_eq_one hn1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases int_natAbs_eq_one hq1 with hq | hq
    · -- q(n) = 1: g(n) = n · 1 = n、IsPrimePos より 2 ≤ n
      right; right; left
      refine ⟨hq, ?_⟩
      rw [hq] at hpos hp
      simp only [mul_one] at hpos hp
      have h2 : 2 ≤ n.natAbs := hp.two_le
      have h_eq : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hpos.le
      have h3 : (2 : ℤ) ≤ (n.natAbs : ℤ) := by exact_mod_cast h2
      linarith
    · -- q(n) = -1: g(n) = -n、IsPrimePos より n ≤ -2
      right; right; right
      refine ⟨hq, ?_⟩
      rw [hq] at hpos hp
      have hpos' : (0 : ℤ) < -n := by linarith [hpos]
      have h_eq : (n * (-1 : ℤ)).natAbs = n.natAbs := by
        rw [Int.natAbs_mul]; simp
      rw [h_eq] at hp
      have h2 : 2 ≤ n.natAbs := hp.two_le
      have h_eq2 : ((-n).natAbs : ℤ) = -n := Int.natAbs_of_nonneg hpos'.le
      have h_eq3 : (-n).natAbs = n.natAbs := Int.natAbs_neg n
      have h3 : (2 : ℤ) ≤ ((-n).natAbs : ℤ) := by
        rw [h_eq3]; exact_mod_cast h2
      linarith

/-- n = 1 で g(n) が素数なら q(1) は素数 (≥ 2)。 -/
private lemma q_one_pos (a b : ℤ) (h : IsPrimePos (g a b 1)) : 2 ≤ q a b 1 := by
  obtain ⟨hpos, hp⟩ := h
  rw [g_factor] at hpos hp
  simp only [one_mul] at hpos hp
  have h2 : 2 ≤ (q a b 1).natAbs := hp.two_le
  have h_eq : ((q a b 1).natAbs : ℤ) = q a b 1 := Int.natAbs_of_nonneg hpos.le
  have h3 : (2 : ℤ) ≤ ((q a b 1).natAbs : ℤ) := by exact_mod_cast h2
  linarith

/-- n = -1 で g(n) が素数なら q(-1) ≤ -2 (i.e., -q(-1) ≥ 2)。 -/
private lemma q_neg_one_neg (a b : ℤ) (h : IsPrimePos (g a b (-1))) : q a b (-1) ≤ -2 := by
  obtain ⟨hpos, hp⟩ := h
  rw [g_factor] at hpos hp
  -- hpos: 0 < (-1) * q(-1) = -q(-1)
  have h_neg : q a b (-1) < 0 := by nlinarith [hpos]
  have h_eq : ((-1 : ℤ) * q a b (-1)).natAbs = (q a b (-1)).natAbs := by
    rw [Int.natAbs_mul]; simp
  rw [h_eq] at hp
  have h2 : 2 ≤ (q a b (-1)).natAbs := hp.two_le
  -- q(-1) < 0 なので natAbs = -q(-1)
  have h_eq2 : ((q a b (-1)).natAbs : ℤ) = -(q a b (-1)) := by
    have : (-(q a b (-1))).natAbs = (q a b (-1)).natAbs := Int.natAbs_neg _
    rw [← this]
    exact Int.natAbs_of_nonneg (by linarith)
  have h3 : (2 : ℤ) ≤ ((q a b (-1)).natAbs : ℤ) := by exact_mod_cast h2
  linarith

/-! ### 主要不等式 (F1, F2, F3) -/

/-- F1: q(α) = 1 (α ≥ 2), q(γ) = -1 (γ ≤ -2) は両立しない。 -/
private lemma no_both_signs (a b α γ : ℤ) (hα : 2 ≤ α) (hγ : γ ≤ -2)
    (hqα : q a b α = 1) (hqγ : q a b γ = -1) : False := by
  unfold q at hqα hqγ
  have h2 : (α - γ) * (α + γ + a) = 2 := by linear_combination hqα - hqγ
  have hαγ : 4 ≤ α - γ := by linarith
  have h_pos : (0 : ℤ) ≤ α - γ := by linarith
  rcases lt_trichotomy (α + γ + a) 0 with h_neg | h_zero | h_pos2
  · have hk_le : α + γ + a ≤ -1 := by linarith
    have h_prod_le : (α - γ) * (α + γ + a) ≤ (α - γ) * (-1) :=
      mul_le_mul_of_nonneg_left hk_le h_pos
    have hcalc : (α - γ) * (-1 : ℤ) = -(α - γ) := by ring
    linarith
  · rw [h_zero, mul_zero] at h2; exact absurd h2 (by norm_num)
  · have hk_ge : 1 ≤ α + γ + a := by linarith
    have h_prod_ge : (α - γ) * 1 ≤ (α - γ) * (α + γ + a) :=
      mul_le_mul_of_nonneg_left hk_ge h_pos
    have hcalc : (α - γ) * 1 = α - γ := by ring
    linarith

/-- F2: q(α) = q(β) = 1 (α ≠ β, α, β ≥ 2) ⟹ q(-1) ≥ 13。 -/
private lemma q_neg_one_large_C (a b α β : ℤ) (hα : 2 ≤ α) (hβ : 2 ≤ β) (hαβ : α ≠ β)
    (hqα : q a b α = 1) (hqβ : q a b β = 1) : 13 ≤ q a b (-1) := by
  unfold q at hqα hqβ ⊢
  have hab : (α - β) * (α + β + a) = 0 := by linear_combination hqα - hqβ
  have hsum : α + β + a = 0 := by
    rcases mul_eq_zero.mp hab with h | h
    · exfalso; apply hαβ; linarith
    · exact h
  have ha : a = -(α + β) := by linarith
  have hbeq : b = α * β + 1 := by
    have h1 : α ^ 2 + a * α + b = 1 := hqα
    have h2 : a * α = -(α + β) * α := by rw [ha]
    nlinarith [h1, h2]
  -- q(-1) = (α+1)(β+1) + 1
  have hq_neg_eq : (-1 : ℤ) ^ 2 + a * (-1) + b = (α + 1) * (β + 1) + 1 := by
    rw [ha, hbeq]; ring
  rw [hq_neg_eq]
  -- (α+1)(β+1) ≥ 12
  rcases lt_or_gt_of_ne hαβ with hαβ' | hαβ'
  · -- α < β: α ≥ 2, β ≥ 3
    have hβ3 : 3 ≤ β := by linarith
    have h1 : (3 : ℤ) ≤ α + 1 := by linarith
    have h2 : (4 : ℤ) ≤ β + 1 := by linarith
    have hbig : (12 : ℤ) ≤ (α + 1) * (β + 1) := by
      calc (12 : ℤ) = 3 * 4 := by norm_num
        _ ≤ (α + 1) * (β + 1) := mul_le_mul h1 h2 (by linarith) (by linarith)
    linarith
  · have hα3 : 3 ≤ α := by linarith
    have h1 : (4 : ℤ) ≤ α + 1 := by linarith
    have h2 : (3 : ℤ) ≤ β + 1 := by linarith
    have hbig : (12 : ℤ) ≤ (α + 1) * (β + 1) := by
      calc (12 : ℤ) = 4 * 3 := by norm_num
        _ ≤ (α + 1) * (β + 1) := mul_le_mul h1 h2 (by linarith) (by linarith)
    linarith

/-- F3: q(γ) = q(δ) = -1 (γ ≠ δ, γ, δ ≤ -2) ⟹ q(-1) ≥ 1。 -/
private lemma q_neg_one_large_D (a b γ δ : ℤ) (hγ : γ ≤ -2) (hδ : δ ≤ -2) (hγδ : γ ≠ δ)
    (hqγ : q a b γ = -1) (hqδ : q a b δ = -1) : 1 ≤ q a b (-1) := by
  unfold q at hqγ hqδ ⊢
  have hab : (γ - δ) * (γ + δ + a) = 0 := by linear_combination hqγ - hqδ
  have hsum : γ + δ + a = 0 := by
    rcases mul_eq_zero.mp hab with h | h
    · exfalso; apply hγδ; linarith
    · exact h
  have ha : a = -(γ + δ) := by linarith
  have hbeq : b = γ * δ - 1 := by
    have h1 : γ ^ 2 + a * γ + b = -1 := hqγ
    have h2 : a * γ = -(γ + δ) * γ := by rw [ha]
    nlinarith [h1, h2]
  have hq_neg_eq : (-1 : ℤ) ^ 2 + a * (-1) + b = (γ + 1) * (δ + 1) - 1 := by
    rw [ha, hbeq]; ring
  rw [hq_neg_eq]
  -- (γ+1)(δ+1) ≥ 2
  rcases lt_or_gt_of_ne hγδ with hγδ' | hγδ'
  · -- γ < δ ⟹ γ ≤ -3
    have hγ3 : γ ≤ -3 := by linarith
    have h1 : (2 : ℤ) ≤ -(γ + 1) := by linarith
    have h2 : (1 : ℤ) ≤ -(δ + 1) := by linarith
    have hbig : (2 : ℤ) ≤ (-(γ + 1)) * (-(δ + 1)) := by
      calc (2 : ℤ) = 2 * 1 := by norm_num
        _ ≤ (-(γ + 1)) * (-(δ + 1)) := mul_le_mul h1 h2 (by norm_num) (by linarith)
    have hprod : (-(γ + 1)) * (-(δ + 1)) = (γ + 1) * (δ + 1) := by ring
    linarith
  · have hδ3 : δ ≤ -3 := by linarith
    have h1 : (1 : ℤ) ≤ -(γ + 1) := by linarith
    have h2 : (2 : ℤ) ≤ -(δ + 1) := by linarith
    have hbig : (2 : ℤ) ≤ (-(γ + 1)) * (-(δ + 1)) := by
      calc (2 : ℤ) = 1 * 2 := by norm_num
        _ ≤ (-(γ + 1)) * (-(δ + 1)) := mul_le_mul h1 h2 (by norm_num) (by linarith)
    have hprod : (-(γ + 1)) * (-(δ + 1)) = (γ + 1) * (δ + 1) := by ring
    linarith

/-- C 型 (q(n) = 1) の根は高々 2 つ (二次方程式)。
    3 つの異なる n が q(n) = 1 を満たすことはない。 -/
private lemma at_most_two_C (a b n₁ n₂ n₃ : ℤ)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    (hq1 : q a b n₁ = 1) (hq2 : q a b n₂ = 1) (hq3 : q a b n₃ = 1) : False := by
  unfold q at hq1 hq2 hq3
  have h_12 : n₁ + n₂ + a = 0 := by
    have heq : (n₁ - n₂) * (n₁ + n₂ + a) = 0 := by linear_combination hq1 - hq2
    rcases mul_eq_zero.mp heq with h | h
    · exfalso; apply h12; linarith
    · exact h
  have h_13 : n₁ + n₃ + a = 0 := by
    have heq : (n₁ - n₃) * (n₁ + n₃ + a) = 0 := by linear_combination hq1 - hq3
    rcases mul_eq_zero.mp heq with h | h
    · exfalso; apply h13; linarith
    · exact h
  apply h23; linarith

/-- D 型 (q(n) = -1) の根も高々 2 つ。 -/
private lemma at_most_two_D (a b n₁ n₂ n₃ : ℤ)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    (hq1 : q a b n₁ = -1) (hq2 : q a b n₂ = -1) (hq3 : q a b n₃ = -1) : False := by
  unfold q at hq1 hq2 hq3
  have h_12 : n₁ + n₂ + a = 0 := by
    have heq : (n₁ - n₂) * (n₁ + n₂ + a) = 0 := by linear_combination hq1 - hq2
    rcases mul_eq_zero.mp heq with h | h
    · exfalso; apply h12; linarith
    · exact h
  have h_13 : n₁ + n₃ + a = 0 := by
    have heq : (n₁ - n₃) * (n₁ + n₃ + a) = 0 := by linear_combination hq1 - hq3
    rcases mul_eq_zero.mp heq with h | h
    · exfalso; apply h13; linarith
    · exact h
  apply h23; linarith

/-! ### 主定理 -/

/-- 主定理: g(n) が素数となる相異なる 4 つの整数 n₁, n₂, n₃, n₄ は存在しない。
    すなわち、g(n) が素数となる整数 n の個数は高々 3 個。

    各 n_i を A: n=1, B: n=-1, C: q=1∧≥2, D: q=-1∧≤-2 に分類して場合分け。
    A, B は高々 1 個 (distinctness), C, D は高々 2 個 (二次方程式の根)。
    C と D の共存は F1 で禁止、C 2 個 + B は F2、D 2 個 + B は F3 で禁止。 -/
theorem at_most_three (a b : ℤ) (n₁ n₂ n₃ n₄ : ℤ)
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h14 : n₁ ≠ n₄)
    (h23 : n₂ ≠ n₃) (h24 : n₂ ≠ n₄) (h34 : n₃ ≠ n₄)
    (hp1 : IsPrimePos (g a b n₁)) (hp2 : IsPrimePos (g a b n₂))
    (hp3 : IsPrimePos (g a b n₃)) (hp4 : IsPrimePos (g a b n₄)) : False := by
  rcases category a b n₁ hp1 with rfl | rfl | ⟨c1_q, c1_b⟩ | ⟨c1_q, c1_b⟩
  · -- Case: n₁ = 1
    rcases category a b n₂ hp2 with rfl | rfl | ⟨c2_q, c2_b⟩ | ⟨c2_q, c2_b⟩
    · exact h12 rfl
    · -- n₁=1, n₂=-1
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · exact h13 rfl
      · exact h23 rfl
      · -- n₁=1, n₂=-1, n₃ ∈ C
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h14 rfl
        · exact h24 rfl
        · -- 2 C-roots: n₃, n₄. F2 vs q_neg_one_neg.
          have hF2 := q_neg_one_large_C a b n₃ n₄ c3_b c4_b h34 c3_q c4_q
          have hNeg := q_neg_one_neg a b hp2
          linarith
        · exact no_both_signs a b n₃ n₄ c3_b c4_b c3_q c4_q
      · -- n₁=1, n₂=-1, n₃ ∈ D
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h14 rfl
        · exact h24 rfl
        · exact no_both_signs a b n₄ n₃ c4_b c3_b c4_q c3_q
        · -- 2 D-roots
          have hF3 := q_neg_one_large_D a b n₃ n₄ c3_b c4_b h34 c3_q c4_q
          have hNeg := q_neg_one_neg a b hp2
          linarith
    · -- n₁=1, n₂ ∈ C
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · exact h13 rfl
      · -- n₃ = -1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h14 rfl
        · exact h34 rfl
        · -- 2 C: n₂, n₄
          have hF2 := q_neg_one_large_C a b n₂ n₄ c2_b c4_b h24 c2_q c4_q
          have hNeg := q_neg_one_neg a b hp3
          linarith
        · exact no_both_signs a b n₂ n₄ c2_b c4_b c2_q c4_q
      · -- n₃ ∈ C
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h14 rfl
        · -- n₄=-1, n₂, n₃ ∈ C
          have hF2 := q_neg_one_large_C a b n₂ n₃ c2_b c3_b h23 c2_q c3_q
          have hNeg := q_neg_one_neg a b hp4
          linarith
        · -- 3 C: n₂, n₃, n₄
          exact at_most_two_C a b n₂ n₃ n₄ h23 h24 h34 c2_q c3_q c4_q
        · exact no_both_signs a b n₂ n₄ c2_b c4_b c2_q c4_q
      · -- n₃ ∈ D, n₂ ∈ C
        exact no_both_signs a b n₂ n₃ c2_b c3_b c2_q c3_q
    · -- n₁=1, n₂ ∈ D
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · exact h13 rfl
      · -- n₃=-1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h14 rfl
        · exact h34 rfl
        · exact no_both_signs a b n₄ n₂ c4_b c2_b c4_q c2_q
        · -- 2 D: n₂, n₄
          have hF3 := q_neg_one_large_D a b n₂ n₄ c2_b c4_b h24 c2_q c4_q
          have hNeg := q_neg_one_neg a b hp3
          linarith
      · exact no_both_signs a b n₃ n₂ c3_b c2_b c3_q c2_q
      · -- n₃ ∈ D
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h14 rfl
        · -- 2 D: n₂, n₃
          have hF3 := q_neg_one_large_D a b n₂ n₃ c2_b c3_b h23 c2_q c3_q
          have hNeg := q_neg_one_neg a b hp4
          linarith
        · exact no_both_signs a b n₄ n₂ c4_b c2_b c4_q c2_q
        · -- 3 D
          exact at_most_two_D a b n₂ n₃ n₄ h23 h24 h34 c2_q c3_q c4_q
  · -- Case: n₁ = -1
    rcases category a b n₂ hp2 with rfl | rfl | ⟨c2_q, c2_b⟩ | ⟨c2_q, c2_b⟩
    · -- n₂ = 1
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · exact h23 rfl
      · exact h13 rfl
      · -- n₃ ∈ C
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h24 rfl
        · exact h14 rfl
        · -- 2 C: n₃, n₄, B = -1 (from n₁)
          have hF2 := q_neg_one_large_C a b n₃ n₄ c3_b c4_b h34 c3_q c4_q
          have hNeg := q_neg_one_neg a b hp1
          linarith
        · exact no_both_signs a b n₃ n₄ c3_b c4_b c3_q c4_q
      · -- n₃ ∈ D
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h24 rfl
        · exact h14 rfl
        · exact no_both_signs a b n₄ n₃ c4_b c3_b c4_q c3_q
        · -- 2 D
          have hF3 := q_neg_one_large_D a b n₃ n₄ c3_b c4_b h34 c3_q c4_q
          have hNeg := q_neg_one_neg a b hp1
          linarith
    · exact h12 rfl
    · -- n₂ ∈ C
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · -- n₃ = 1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h34 rfl
        · exact h14 rfl
        · -- 2 C
          have hF2 := q_neg_one_large_C a b n₂ n₄ c2_b c4_b h24 c2_q c4_q
          have hNeg := q_neg_one_neg a b hp1
          linarith
        · exact no_both_signs a b n₂ n₄ c2_b c4_b c2_q c4_q
      · exact h13 rfl
      · -- n₃ ∈ C
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · -- n₄ = 1
          have hF2 := q_neg_one_large_C a b n₂ n₃ c2_b c3_b h23 c2_q c3_q
          have hNeg := q_neg_one_neg a b hp1
          linarith
        · exact h14 rfl
        · -- 3 C
          exact at_most_two_C a b n₂ n₃ n₄ h23 h24 h34 c2_q c3_q c4_q
        · exact no_both_signs a b n₂ n₄ c2_b c4_b c2_q c4_q
      · exact no_both_signs a b n₂ n₃ c2_b c3_b c2_q c3_q
    · -- n₂ ∈ D
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · -- n₃ = 1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h34 rfl
        · exact h14 rfl
        · exact no_both_signs a b n₄ n₂ c4_b c2_b c4_q c2_q
        · -- 2 D
          have hF3 := q_neg_one_large_D a b n₂ n₄ c2_b c4_b h24 c2_q c4_q
          have hNeg := q_neg_one_neg a b hp1
          linarith
      · exact h13 rfl
      · exact no_both_signs a b n₃ n₂ c3_b c2_b c3_q c2_q
      · -- n₃ ∈ D
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · -- n₄ = 1, 2 D: n₂, n₃
          have hF3 := q_neg_one_large_D a b n₂ n₃ c2_b c3_b h23 c2_q c3_q
          have hNeg := q_neg_one_neg a b hp1
          linarith
        · exact h14 rfl
        · exact no_both_signs a b n₄ n₂ c4_b c2_b c4_q c2_q
        · exact at_most_two_D a b n₂ n₃ n₄ h23 h24 h34 c2_q c3_q c4_q
  · -- Case: n₁ ∈ C
    rcases category a b n₂ hp2 with rfl | rfl | ⟨c2_q, c2_b⟩ | ⟨c2_q, c2_b⟩
    · -- n₂ = 1
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · exact h23 rfl
      · -- n₃ = -1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h24 rfl
        · exact h34 rfl
        · -- 2 C: n₁, n₄
          have hF2 := q_neg_one_large_C a b n₁ n₄ c1_b c4_b h14 c1_q c4_q
          have hNeg := q_neg_one_neg a b hp3
          linarith
        · exact no_both_signs a b n₁ n₄ c1_b c4_b c1_q c4_q
      · -- n₃ ∈ C
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h24 rfl
        · -- n₄ = -1, 2 C: n₁, n₃
          have hF2 := q_neg_one_large_C a b n₁ n₃ c1_b c3_b h13 c1_q c3_q
          have hNeg := q_neg_one_neg a b hp4
          linarith
        · -- 3 C: n₁, n₃, n₄
          exact at_most_two_C a b n₁ n₃ n₄ h13 h14 h34 c1_q c3_q c4_q
        · exact no_both_signs a b n₁ n₄ c1_b c4_b c1_q c4_q
      · exact no_both_signs a b n₁ n₃ c1_b c3_b c1_q c3_q
    · -- n₂ = -1
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · -- n₃ = 1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h34 rfl
        · exact h24 rfl
        · -- 2 C: n₁, n₄
          have hF2 := q_neg_one_large_C a b n₁ n₄ c1_b c4_b h14 c1_q c4_q
          have hNeg := q_neg_one_neg a b hp2
          linarith
        · exact no_both_signs a b n₁ n₄ c1_b c4_b c1_q c4_q
      · exact h23 rfl
      · -- n₃ ∈ C
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · -- n₄ = 1, 2 C: n₁, n₃
          have hF2 := q_neg_one_large_C a b n₁ n₃ c1_b c3_b h13 c1_q c3_q
          have hNeg := q_neg_one_neg a b hp2
          linarith
        · exact h24 rfl
        · -- 3 C
          exact at_most_two_C a b n₁ n₃ n₄ h13 h14 h34 c1_q c3_q c4_q
        · exact no_both_signs a b n₁ n₄ c1_b c4_b c1_q c4_q
      · exact no_both_signs a b n₁ n₃ c1_b c3_b c1_q c3_q
    · -- n₂ ∈ C
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · -- n₃ = 1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h34 rfl
        · -- n₄ = -1
          have hF2 := q_neg_one_large_C a b n₁ n₂ c1_b c2_b h12 c1_q c2_q
          have hNeg := q_neg_one_neg a b hp4
          linarith
        · -- 3 C
          exact at_most_two_C a b n₁ n₂ n₄ h12 h14 h24 c1_q c2_q c4_q
        · exact no_both_signs a b n₁ n₄ c1_b c4_b c1_q c4_q
      · -- n₃ = -1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · -- n₄ = 1
          have hF2 := q_neg_one_large_C a b n₁ n₂ c1_b c2_b h12 c1_q c2_q
          have hNeg := q_neg_one_neg a b hp3
          linarith
        · exact h34 rfl
        · -- 3 C
          exact at_most_two_C a b n₁ n₂ n₄ h12 h14 h24 c1_q c2_q c4_q
        · exact no_both_signs a b n₁ n₄ c1_b c4_b c1_q c4_q
      · -- n₃ ∈ C: 3 C in n₁, n₂, n₃
        exact at_most_two_C a b n₁ n₂ n₃ h12 h13 h23 c1_q c2_q c3_q
      · exact no_both_signs a b n₁ n₃ c1_b c3_b c1_q c3_q
    · exact no_both_signs a b n₁ n₂ c1_b c2_b c1_q c2_q
  · -- Case: n₁ ∈ D
    rcases category a b n₂ hp2 with rfl | rfl | ⟨c2_q, c2_b⟩ | ⟨c2_q, c2_b⟩
    · -- n₂ = 1
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · exact h23 rfl
      · -- n₃ = -1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h24 rfl
        · exact h34 rfl
        · exact no_both_signs a b n₄ n₁ c4_b c1_b c4_q c1_q
        · -- 2 D: n₁, n₄
          have hF3 := q_neg_one_large_D a b n₁ n₄ c1_b c4_b h14 c1_q c4_q
          have hNeg := q_neg_one_neg a b hp3
          linarith
      · exact no_both_signs a b n₃ n₁ c3_b c1_b c3_q c1_q
      · -- n₃ ∈ D
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h24 rfl
        · -- n₄ = -1, 2 D: n₁, n₃
          have hF3 := q_neg_one_large_D a b n₁ n₃ c1_b c3_b h13 c1_q c3_q
          have hNeg := q_neg_one_neg a b hp4
          linarith
        · exact no_both_signs a b n₄ n₁ c4_b c1_b c4_q c1_q
        · exact at_most_two_D a b n₁ n₃ n₄ h13 h14 h34 c1_q c3_q c4_q
    · -- n₂ = -1
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · -- n₃ = 1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h34 rfl
        · exact h24 rfl
        · exact no_both_signs a b n₄ n₁ c4_b c1_b c4_q c1_q
        · -- 2 D: n₁, n₄
          have hF3 := q_neg_one_large_D a b n₁ n₄ c1_b c4_b h14 c1_q c4_q
          have hNeg := q_neg_one_neg a b hp2
          linarith
      · exact h23 rfl
      · exact no_both_signs a b n₃ n₁ c3_b c1_b c3_q c1_q
      · -- n₃ ∈ D
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · -- n₄ = 1
          have hF3 := q_neg_one_large_D a b n₁ n₃ c1_b c3_b h13 c1_q c3_q
          have hNeg := q_neg_one_neg a b hp2
          linarith
        · exact h24 rfl
        · exact no_both_signs a b n₄ n₁ c4_b c1_b c4_q c1_q
        · exact at_most_two_D a b n₁ n₃ n₄ h13 h14 h34 c1_q c3_q c4_q
    · exact no_both_signs a b n₂ n₁ c2_b c1_b c2_q c1_q
    · -- n₂ ∈ D
      rcases category a b n₃ hp3 with rfl | rfl | ⟨c3_q, c3_b⟩ | ⟨c3_q, c3_b⟩
      · -- n₃ = 1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · exact h34 rfl
        · -- n₄ = -1
          have hF3 := q_neg_one_large_D a b n₁ n₂ c1_b c2_b h12 c1_q c2_q
          have hNeg := q_neg_one_neg a b hp4
          linarith
        · exact no_both_signs a b n₄ n₁ c4_b c1_b c4_q c1_q
        · exact at_most_two_D a b n₁ n₂ n₄ h12 h14 h24 c1_q c2_q c4_q
      · -- n₃ = -1
        rcases category a b n₄ hp4 with rfl | rfl | ⟨c4_q, c4_b⟩ | ⟨c4_q, c4_b⟩
        · -- n₄ = 1
          have hF3 := q_neg_one_large_D a b n₁ n₂ c1_b c2_b h12 c1_q c2_q
          have hNeg := q_neg_one_neg a b hp3
          linarith
        · exact h34 rfl
        · exact no_both_signs a b n₄ n₁ c4_b c1_b c4_q c1_q
        · exact at_most_two_D a b n₁ n₂ n₄ h12 h14 h24 c1_q c2_q c4_q
      · exact no_both_signs a b n₃ n₁ c3_b c1_b c3_q c1_q
      · -- 3 D
        exact at_most_two_D a b n₁ n₂ n₃ h12 h13 h23 c1_q c2_q c3_q

end Common2026.T2024_Q6_2
