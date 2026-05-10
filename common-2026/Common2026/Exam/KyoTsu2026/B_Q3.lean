/-
2B 第3問

  k を実数とし、関数
    f(x) = (1/3)x³ - 2x² + 3x + k
  を考える。

  (1)(i) f'(x) = x² - 4x + 3 = (x - 1)(x - 3)。
         よって f は x = 1 で極大、x = 3 で極小となり、
         極大値 f(1) = 4/3 + k、極小値 f(3) = k。

  (1)(iii) α = min(1, 3) = 1 とする。0 ≤ x ≤ α の範囲で y = f(x) と
           x 軸および直線 x = α、y 軸とで囲まれた 2 つの部分の面積が
           等しいとき、k の値を求める。

           f(0) < 0 < f(α) より -4/3 < k < 0。
           面積が等しい条件は ∫₀^α f(x) dx = 0 と同値で、
           原始関数 F(x) = x⁴/12 - 2x³/3 + 3x²/2 + kx を用いて
           F(1) - F(0) = 11/12 + k = 0 より k = -11/12。

  本ファイルでは微分・積分そのものを Lean で扱う代わりに、
  導関数・原始関数を多項式として `def` で与え、それらの値や
  恒等式を ring/linarith で確認する形式化を採る。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.B_Q3

/-- f(x) = (1/3)x³ - 2x² + 3x + k -/
noncomputable def f (k x : ℝ) : ℝ := (1/3) * x^3 - 2*x^2 + 3*x + k

/-- f の原始関数の候補 F(x) = x⁴/12 - 2x³/3 + 3x²/2 + kx。
    F'(x) = f(x) は微分定義からの計算で確認 (本ファイルでは F の値を定積分の代用として使う)。 -/
noncomputable def F (k x : ℝ) : ℝ := x^4/12 - 2*x^3/3 + 3*x^2/2 + k*x

/-- f' (導関数) を表す多項式 -/
def f' (x : ℝ) : ℝ := x^2 - 4*x + 3

/-- f'(x) = (x-1)(x-3) -/
theorem fprime_factor (x : ℝ) : f' x = (x - 1) * (x - 3) := by
  unfold f'; ring

/-- f(1) = 4/3 + k -/
theorem f_at_1 (k : ℝ) : f k 1 = 4/3 + k := by unfold f; ring

/-- f(3) = k -/
theorem f_at_3 (k : ℝ) : f k 3 = k := by unfold f; ring

/-- f(0) = k -/
theorem f_at_0 (k : ℝ) : f k 0 = k := by unfold f; ring

/-- f(α) > 0 かつ f(0) < 0 (α = 1) ⇔ -4/3 < k < 0 -/
theorem k_range (k : ℝ) :
    (f k 0 < 0 ∧ 0 < f k 1) ↔ (-4/3 < k ∧ k < 0) := by
  rw [f_at_0, f_at_1]
  constructor
  · intro ⟨h1, h2⟩; constructor <;> linarith
  · intro ⟨h1, h2⟩; constructor <;> linarith

/-- F(1) - F(0) = 11/12 + k (= ∫₀^1 f dx の値) -/
theorem F_diff (k : ℝ) : F k 1 - F k 0 = 11/12 + k := by unfold F; ring

/-- 面積条件 ∫₀^α f dx = 0 (α=1) ⇒ k = -11/12 -/
theorem k_value (k : ℝ) (h : F k 1 - F k 0 = 0) : k = -11/12 := by
  rw [F_diff] at h
  linarith

end Common2026.B_Q3
