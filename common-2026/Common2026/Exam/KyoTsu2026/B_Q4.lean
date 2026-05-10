/-
2B 第4問 (階差数列)

  数列 {a_n} に対し b_n = a_{n+1} - a_n を {a_n} の階差数列という。

  (1) a_1 = 1, b_n = 4n - 1 のとき:
    (i) b_1 = 3 (ア), a_2 = a_1 + b_1 = 4 (イ)。
        b_2 = 7 (ウ), a_3 = a_2 + b_2 = 11 (エオ)。
    (ii) n ≥ 2 のとき
           a_n = a_1 + Σ_{k=1}^{n-1} b_k    (空欄カ = ⓪ n-1)
         であり、Σ_{k=1}^{n-1} (4k - 1) = (n-1)(2n-1) より
           a_n = 1 + (n-1)(2n-1) = 2n^2 - 3n + 2
         (キ=2, ク=3, ケ=2)。n=1 でも一致。

  (2) d_n = (2n+1) · 2^n の和:
    階差が d_n となる数列を c_n = (p n + q) · 2^n とおくと
      c_{n+1} - c_n = (p n + (2p + q)) · 2^n
    (空欄コ = ⓪ p, サ = ⑤ 2p + q)。
    これが (2n+1)·2^n に等しい条件は p = 2, 2p + q = 1、すなわち
    q = -3 (シ=2, スセ=-3)。よって c_n = (2n - 3)·2^n。
      Σ_{k=1}^{n} d_k = c_{n+1} - c_1 = (2n - 1) · 2^{n+1} + 2
    (ソ=③ 2n-1, タ=2)。

  (3) d_n = (n^2 - n - 1) · 2^n の和:
    c_n = (p n^2 + q n + r) · 2^n とおくと
      c_{n+1} - c_n = (p n^2 + (4p + q) n + (2p + 2q + r)) · 2^n。
    (n^2 - n - 1)·2^n に一致するには p = 1, q = -5, r = 7。
    したがって c_n = (n^2 - 5n + 7) · 2^n、
      Σ_{k=1}^{n} d_k = c_{n+1} - c_1 = (n^2 - 3n + 3) · 2^{n+1} - 6
    (チ=⑦ n^2-3n+3, ツ=6)。

  本ファイルでは数列の帰納法による形式化は行わず、関連する代数恒等式
  (階差・閉形式の差・係数比較) を ring で確認する形を採る。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.B_Q4

/-! ## (1) 階差数列 b_n = 4n - 1, 初項 a_1 = 1 -/

namespace part1

/-- b_n = 4n - 1 -/
def b (n : ℝ) : ℝ := 4 * n - 1

/-- b_1 = 3 (ア) -/
theorem b1 : b 1 = 3 := by unfold b; norm_num

/-- b_2 = 7 (ウ) -/
theorem b2 : b 2 = 7 := by unfold b; norm_num

/-- a_2 = a_1 + b_1 = 1 + 3 = 4 (イ) -/
theorem a2 : (1 : ℝ) + b 1 = 4 := by rw [b1]; norm_num

/-- a_3 = a_2 + b_2 = 4 + 7 = 11 (エオ) -/
theorem a3 : (4 : ℝ) + b 2 = 11 := by rw [b2]; norm_num

/-- 一般項の閉形式 a_n = 2n^2 - 3n + 2 (キ=2, ク=3, ケ=2)。n=1 でも一致するので全 n。 -/
def aFormula (n : ℝ) : ℝ := 2 * n^2 - 3 * n + 2

theorem aFormula_at_1 : aFormula 1 = 1 := by unfold aFormula; norm_num
theorem aFormula_at_2 : aFormula 2 = 4 := by unfold aFormula; norm_num
theorem aFormula_at_3 : aFormula 3 = 11 := by unfold aFormula; norm_num

/-- 階差検証: aFormula(n+1) - aFormula(n) = b(n) -/
theorem aFormula_diff (n : ℝ) : aFormula (n + 1) - aFormula n = b n := by
  unfold aFormula b; ring

end part1

/-! ## (2) d_n = (2n+1)·2^n の和 -/

namespace part2

/-- 一般係数 c_n = (p n + q) · 2^n の階差。
    (p(n+1) + q) · 2^{n+1} - (p n + q) · 2^n = (p n + (2 p + q)) · 2^n。 -/
theorem c_diff (p q : ℝ) (n : ℕ) :
    (p * (n + 1) + q) * (2 : ℝ)^(n + 1) - (p * n + q) * (2 : ℝ)^n
      = (p * n + (2 * p + q)) * (2 : ℝ)^n := by
  rw [pow_succ]; ring

/-- p = 2, q = -3 のとき係数 (p n + (2p + q)) は 2n + 1 に一致。 -/
theorem coeff_match (n : ℕ) :
    ((2 : ℝ) * n + (2 * 2 + (-3))) * (2 : ℝ)^n = (2 * n + 1) * (2 : ℝ)^n := by
  ring

/-- 和の閉形式: c_n = (2n - 3) · 2^n を用いて
    c_{n+1} - c_1 = (2n - 1) · 2^{n+1} + 2。 -/
theorem sum_formula (n : ℕ) :
    (2 * ((n : ℝ) + 1) - 3) * (2 : ℝ)^(n + 1) - (2 * 1 - 3) * (2 : ℝ)^1
      = (2 * (n : ℝ) - 1) * (2 : ℝ)^(n + 1) + 2 := by
  ring

end part2

/-! ## (3) d_n = (n^2 - n - 1)·2^n の和 -/

namespace part3

/-- 一般係数 c_n = (p n^2 + q n + r) · 2^n の階差。 -/
theorem c_diff (p q r : ℝ) (n : ℕ) :
    (p * ((n : ℝ) + 1)^2 + q * ((n : ℝ) + 1) + r) * (2 : ℝ)^(n + 1)
      - (p * (n : ℝ)^2 + q * n + r) * (2 : ℝ)^n
      = (p * (n : ℝ)^2 + (4 * p + q) * n + (2 * p + 2 * q + r)) * (2 : ℝ)^n := by
  rw [pow_succ]; ring

/-- p = 1, q = -5, r = 7 のとき係数 (p n^2 + (4p+q) n + (2p+2q+r)) は n^2 - n - 1 に一致。 -/
theorem coeff_match (n : ℕ) :
    ((1 : ℝ) * (n : ℝ)^2 + (4 * 1 + (-5)) * n + (2 * 1 + 2 * (-5) + 7)) * (2 : ℝ)^n
      = ((n : ℝ)^2 - n - 1) * (2 : ℝ)^n := by
  ring

/-- 和の閉形式: c_n = (n^2 - 5n + 7) · 2^n を用いて
    c_{n+1} - c_1 = (n^2 - 3n + 3) · 2^{n+1} - 6。 -/
theorem sum_formula (n : ℕ) :
    (((n : ℝ) + 1)^2 - 5 * ((n : ℝ) + 1) + 7) * (2 : ℝ)^(n + 1)
        - (1 - 5 + 7) * (2 : ℝ)^1
      = ((n : ℝ)^2 - 3 * n + 3) * (2 : ℝ)^(n + 1) - 6 := by
  ring

end part3

end Common2026.B_Q4
