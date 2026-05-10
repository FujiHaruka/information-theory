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
    主定理は Finset 形式 `S.card ≤ 3` で表現する。証明は S を 4 つの subset
    A, B, C, D に分け、各カードの上界 + F1, F2, F3 で組み立てる
    (場合分けは (C.card, D.card) のみ)。
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
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

/-- C 型 (q(n) = 1) の根は高々 2 つ (二次方程式)。 -/
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

/-! ### 主定理 (Finset 形式) -/

/-- 主定理: g(n) が素数となる整数 n からなる任意の有限集合の大きさは 3 以下。

    各 n を 4 つの型 A: n=1, B: n=-1, C: q(n)=1∧≥2, D: q(n)=-1∧≤-2 に分類し、
    対応する Finset filter のカードを足し合わせて評価する。
    場合分けは (C.card, D.card) のみ。 -/
theorem at_most_three (a b : ℤ) (S : Finset ℤ)
    (hS : ∀ n ∈ S, IsPrimePos (g a b n)) : S.card ≤ 3 := by
  -- S を 4 つの subset に分ける
  let A := S.filter (· = (1 : ℤ))
  let B := S.filter (· = (-1 : ℤ))
  let C := S.filter (fun n => q a b n = 1 ∧ 2 ≤ n)
  let D := S.filter (fun n => q a b n = -1 ∧ n ≤ -2)
  -- 各 n ∈ S は category 補題により A, B, C, D のいずれかに属する
  have hsub : S ⊆ A ∪ B ∪ C ∪ D := by
    intro n hn
    rcases category a b n (hS n hn) with rfl | rfl | ⟨hq, hb⟩ | ⟨hq, hb⟩
    · simp [A, B, C, D, Finset.mem_union, Finset.mem_filter, hn]
    · simp [A, B, C, D, Finset.mem_union, Finset.mem_filter, hn]
    · simp [A, B, C, D, Finset.mem_union, Finset.mem_filter, hn, hq, hb]
    · simp [A, B, C, D, Finset.mem_union, Finset.mem_filter, hn, hq, hb]
  -- card sum bound
  have hcard : S.card ≤ A.card + B.card + C.card + D.card := by
    calc S.card
        ≤ (A ∪ B ∪ C ∪ D).card := Finset.card_le_card hsub
      _ ≤ (A ∪ B ∪ C).card + D.card := Finset.card_union_le _ _
      _ ≤ ((A ∪ B).card + C.card) + D.card := by
          have := Finset.card_union_le (A ∪ B) C; linarith
      _ ≤ (A.card + B.card + C.card) + D.card := by
          have := Finset.card_union_le A B; linarith
      _ = A.card + B.card + C.card + D.card := by ring
  -- 各カードの上界
  have hA : A.card ≤ 1 := by
    have h_sub : A ⊆ ({1} : Finset ℤ) := by
      intro n hn; rw [Finset.mem_filter] at hn; simp [hn.2]
    calc A.card ≤ ({1} : Finset ℤ).card := Finset.card_le_card h_sub
      _ = 1 := Finset.card_singleton _
  have hB : B.card ≤ 1 := by
    have h_sub : B ⊆ ({-1} : Finset ℤ) := by
      intro n hn; rw [Finset.mem_filter] at hn; simp [hn.2]
    calc B.card ≤ ({-1} : Finset ℤ).card := Finset.card_le_card h_sub
      _ = 1 := Finset.card_singleton _
  have hC : C.card ≤ 2 := by
    by_contra hc
    have hc : 2 < _ := not_le.mp hc
    obtain ⟨α, β, γ, hα, hβ, hγ, hαβ, hαγ, hβγ⟩ := Finset.two_lt_card_iff.mp hc
    rw [Finset.mem_filter] at hα hβ hγ
    exact at_most_two_C a b α β γ hαβ hαγ hβγ hα.2.1 hβ.2.1 hγ.2.1
  have hD : D.card ≤ 2 := by
    by_contra hc
    have hc : 2 < _ := not_le.mp hc
    obtain ⟨α, β, γ, hα, hβ, hγ, hαβ, hαγ, hβγ⟩ := Finset.two_lt_card_iff.mp hc
    rw [Finset.mem_filter] at hα hβ hγ
    exact at_most_two_D a b α β γ hαβ hαγ hβγ hα.2.1 hβ.2.1 hγ.2.1
  -- F1: C.card ≥ 1 ∧ D.card ≥ 1 → False
  have hF1 : 0 < C.card → 0 < D.card → False := by
    intro hC1 hD1
    obtain ⟨α, hα⟩ := Finset.card_pos.mp hC1
    obtain ⟨γ, hγ⟩ := Finset.card_pos.mp hD1
    rw [Finset.mem_filter] at hα hγ
    exact no_both_signs a b α γ hα.2.2 hγ.2.2 hα.2.1 hγ.2.1
  -- F2: C.card = 2 → B.card = 0
  have hF2 : C.card = 2 → B.card = 0 := by
    intro hC2
    obtain ⟨α, β, hαβ, hCeq⟩ := Finset.card_eq_two.mp hC2
    have hα_in : α ∈ C := by rw [hCeq]; simp
    have hβ_in : β ∈ C := by rw [hCeq]; simp
    rw [Finset.mem_filter] at hα_in hβ_in
    rw [Finset.card_eq_zero, ← Finset.subset_empty]
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hn_in, rfl⟩ := hn
    have h_neg := hS _ hn_in
    have hF := q_neg_one_large_C a b α β hα_in.2.2 hβ_in.2.2 hαβ hα_in.2.1 hβ_in.2.1
    have hN := q_neg_one_neg a b h_neg
    linarith
  -- F3: D.card = 2 → B.card = 0
  have hF3 : D.card = 2 → B.card = 0 := by
    intro hD2
    obtain ⟨γ, δ, hγδ, hDeq⟩ := Finset.card_eq_two.mp hD2
    have hγ_in : γ ∈ D := by rw [hDeq]; simp
    have hδ_in : δ ∈ D := by rw [hDeq]; simp
    rw [Finset.mem_filter] at hγ_in hδ_in
    rw [Finset.card_eq_zero, ← Finset.subset_empty]
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hn_in, rfl⟩ := hn
    have h_neg := hS _ hn_in
    have hF := q_neg_one_large_D a b γ δ hγ_in.2.2 hδ_in.2.2 hγδ hγ_in.2.1 hδ_in.2.1
    have hN := q_neg_one_neg a b h_neg
    linarith
  -- 仕上げ: (C.card, D.card) で場合分け
  rcases Nat.eq_zero_or_pos C.card with hC0 | hC1
  · rcases Nat.eq_zero_or_pos D.card with hD0 | hD1
    · -- C = 0, D = 0: S.card ≤ A + B ≤ 2
      omega
    · -- C = 0, D ≥ 1: D = 1 or D = 2
      by_cases hD2 : D.card = 2
      · have := hF3 hD2; omega
      · -- D ≤ 1
        omega
  · rcases Nat.eq_zero_or_pos D.card with hD0 | hD1
    · -- C ≥ 1, D = 0: C = 1 or C = 2
      by_cases hC2 : C.card = 2
      · have := hF2 hC2; omega
      · omega
    · -- C ≥ 1 ∧ D ≥ 1: F1 矛盾
      exact (hF1 hC1 hD1).elim

end Common2026.T2024_Q6_2
