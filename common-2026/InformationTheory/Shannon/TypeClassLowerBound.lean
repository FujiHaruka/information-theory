import InformationTheory.Shannon.Sanov.LDPEquality

/-!
# Type-class size lower bound (E-2)

Method of types の **size 下界** (Cover-Thomas 11.1.3):
`|T(c)| ≥ (n+1)^{-|α|} · exp(n · H(c/n))`

ここで `T(c) := { x : Fin n → α | ∀ a, typeCount x a = c a }` は count vector `c` の type class、
`H(c/n) := -∑ (c(a)/n) · log(c(a)/n)` は経験分布 `c/n` の Shannon entropy。

## 既存資産との関係

`SanovLDPEquality.lean:705` `typeClassByCount_card_ge` は同等の不等式を
**`(n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|`** 形 (生形) で publish 済み。
本ファイルは bridge identity `n^n / ∏ c(a)^{c(a)} = exp(n · H(c/n))` を加えて
entropy 形に書き直す。

## 設計判断

- **新規 file**: `SanovLDPEquality.lean` (1394 行) は十分大きく、E-2 publish 形を
  独立に切り出して downstream (Cover-Thomas 11 系) からの import を容易にする。
- **`entropyByCount` 定義**: `klDivIndex c n (uniformOn univ)` 経由ではなく直接定義。
  `klDivIndex` は asymmetric (`Q.real {a}` を取る) のため uniform `Q` 代入が plumbing 重い。
- **Mathlib `Real.log 0 = 0` 規約**: `c(a) = 0` の atom は両辺で 0 を吐くため、support
  制限なしで identity が成立 (証明内で per-`a` `Nat.eq_zero_or_pos` 分岐)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Empirical entropy of the count vector `c` at length `n`:
`H(c/n) := -∑ a, (c(a)/n) · log(c(a)/n)`. -/
@[entry_point]
noncomputable def entropyByCount (c : α → ℕ) (n : ℕ) : ℝ :=
  -∑ a : α, ((c a : ℝ) / n) * Real.log ((c a : ℝ) / n)

/-- Per-atom identity: `c · log(c/n) = c · log c - c · log n` for any `c : ℕ`, `n : ℕ`
with `(n : ℝ) ≠ 0`. Holds also for `c = 0` by the `log 0 = 0` convention. -/
private lemma cnt_mul_log_div
    (c_a : ℕ) {n : ℕ} (hn : (n : ℝ) ≠ 0) :
    (c_a : ℝ) * Real.log ((c_a : ℝ) / n)
      = (c_a : ℝ) * Real.log (c_a : ℝ) - (c_a : ℝ) * Real.log n := by
  rcases Nat.eq_zero_or_pos c_a with h | h
  · rw [h]; simp
  · have : (0 : ℝ) < (c_a : ℝ) := by exact_mod_cast h
    rw [Real.log_div this.ne' hn]
    ring

/-- **Bridge identity**: `(n^n) / ∏ a, (c a)^{c a} = exp (n · H(c/n))` for
`∑ c = n`. Holds for all `n` including `n = 0` (both sides equal 1). -/
@[entry_point]
lemma pow_div_prod_pow_eq_exp_n_entropyByCount
    {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a))
      = Real.exp ((n : ℝ) * entropyByCount c n) := by
  classical
  -- ∏ a, (c a : ℝ)^(c a) > 0 (every factor 0^0 = 1 or pos^pos > 0).
  have h_prod_pos : (0 : ℝ) < ∏ a, (c a : ℝ) ^ (c a) := by
    refine Finset.prod_pos fun a _ => ?_
    rcases Nat.eq_zero_or_pos (c a) with h | h
    · rw [h, pow_zero]; norm_num
    · exact pow_pos (by exact_mod_cast h) _
  have h_prod_ne : ∏ a, (c a : ℝ) ^ (c a) ≠ 0 := h_prod_pos.ne'
  by_cases hn : n = 0
  · -- n = 0 case: c is zero everywhere, both sides = 1.
    subst hn
    have hc_zero : ∀ a, c a = 0 := fun a => by
      have h_le : c a ≤ ∑ a', c a' := Finset.single_le_sum (f := c)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      omega
    have h_prod_one : ∏ a, (c a : ℝ) ^ (c a) = 1 := by
      refine Finset.prod_eq_one fun a _ => ?_
      rw [hc_zero a, pow_zero]
    have h_entropy_zero : entropyByCount c 0 = 0 := by
      unfold entropyByCount
      refine neg_eq_zero.mpr ?_
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hc_zero a]
      simp
    rw [h_prod_one, h_entropy_zero]
    simp
  · -- n > 0 case: use log.
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
    have hn_real_ne : (n : ℝ) ≠ 0 := hn_real_pos.ne'
    have h_lhs_pos : (0 : ℝ) < (n : ℝ) ^ n / ∏ a, (c a : ℝ) ^ (c a) :=
      div_pos (pow_pos hn_real_pos _) h_prod_pos
    -- Show via taking log of both sides.
    rw [← Real.exp_log h_lhs_pos]
    congr 1
    -- Goal: log((n^n) / ∏ c^c) = n · entropyByCount c n
    rw [Real.log_div (pow_pos hn_real_pos _).ne' h_prod_ne, Real.log_pow]
    -- LHS = n · log n - log(∏ c^c)
    -- log(∏ c^c) = ∑ log(c^c) = ∑ c · log c.
    have h_each_ne : ∀ a ∈ (Finset.univ : Finset α), (c a : ℝ) ^ (c a) ≠ 0 := fun a _ => by
      rcases Nat.eq_zero_or_pos (c a) with h | h
      · rw [h, pow_zero]; exact one_ne_zero
      · exact (pow_pos (by exact_mod_cast h) _).ne'
    rw [Real.log_prod h_each_ne]
    have h_each_log : ∀ a, Real.log ((c a : ℝ) ^ (c a)) = (c a : ℝ) * Real.log (c a : ℝ) :=
      fun a => Real.log_pow _ _
    rw [Finset.sum_congr rfl (fun a _ => h_each_log a)]
    -- Goal: (n : ℝ) · log n - ∑ a, (c a) · log (c a) = n · entropyByCount c n
    unfold entropyByCount
    -- n · (-∑ (c/n)·log(c/n)) = -∑ c·log(c/n) = -∑ (c·log c - c·log n)
    --                       = -∑ c·log c + (∑ c)·log n = -∑ c·log c + n·log n
    have h_inner : ∀ a, (c a : ℝ) * Real.log ((c a : ℝ) / n)
        = (c a : ℝ) * Real.log (c a : ℝ) - (c a : ℝ) * Real.log n :=
      fun a => cnt_mul_log_div (c a) hn_real_ne
    -- Rearrange RHS: (n : ℝ) · (-∑ (c/n)·log(c/n)) = -∑ c·log(c/n)
    have h_factor : (n : ℝ) * (-∑ a, ((c a : ℝ) / n) * Real.log ((c a : ℝ) / n))
        = -∑ a, (c a : ℝ) * Real.log ((c a : ℝ) / n) := by
      rw [mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      field_simp
    rw [h_factor]
    -- Now: -∑ c·log(c/n) = -∑ (c·log c - c·log n) = -∑ c·log c + (∑ c)·log n
    have h_sum_eq : (∑ a, (c a : ℝ) * Real.log ((c a : ℝ) / n))
        = (∑ a, ((c a : ℝ) * Real.log (c a : ℝ) - (c a : ℝ) * Real.log n)) :=
      Finset.sum_congr rfl (fun a _ => h_inner a)
    rw [h_sum_eq, Finset.sum_sub_distrib]
    -- ∑ c · log n = (∑ c) · log n = n · log n
    have h_swap : (∑ a, (c a : ℝ) * Real.log n) = (∑ a, (c a : ℝ)) * Real.log n := by
      rw [← Finset.sum_mul]
    rw [h_swap]
    have hsum_R : (∑ a, (c a : ℝ)) = (n : ℝ) := by exact_mod_cast hc_sum
    rw [hsum_R]
    ring

end InformationTheory.Shannon
