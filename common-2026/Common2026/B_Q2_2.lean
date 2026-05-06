/-
2B 第2問 (2)

  関数 f(x) を
    f(x) = sin(x + 5π/12) + sin(x + π/12)
  とする。0 ≤ x < 2π の範囲で f(x) の最大値を考えよう。

  和積公式 ① を用いると
    f(x) = 2 sin(x + π/4) cos(π/6)
         = 2 cos(π/6) sin(x + π/4)
  と変形できる。2 cos(π/6) = √3 は正の定数であるから、0 ≤ x < 2π の範囲において、
  f(x) は x = π/4 で最大値 √3 をとる。
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

namespace Common2026.B_Q2_2

open Real

/-- 関数 f(x) = sin(x + 5π/12) + sin(x + π/12)。 -/
noncomputable def f (x : ℝ) : ℝ := sin (x + 5 * π / 12) + sin (x + π / 12)

/-- 和積公式による変形 f(x) = 2 cos(π/6) · sin(x + π/4)。 -/
theorem f_eq (x : ℝ) : f x = 2 * cos (π / 6) * sin (x + π / 4) := by
  unfold f
  set α := x + π / 4 with hα
  set β := π / 6 with hβ
  have h1 : x + 5 * π / 12 = α + β := by simp [hα, hβ]; ring
  have h2 : x + π / 12 = α - β := by simp [hα, hβ]; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- 2 cos(π/6) = √3。 -/
theorem two_cos_pi_six : 2 * cos (π / 6) = Real.sqrt 3 := by
  rw [Real.cos_pi_div_six]
  ring

/-- x = π/4 において f は最大値 √3 をとる。 -/
theorem f_at_pi_div_four : f (π / 4) = Real.sqrt 3 := by
  rw [f_eq]
  have hx : π / 4 + π / 4 = π / 2 := by ring
  rw [hx, Real.sin_pi_div_two]
  rw [two_cos_pi_six]
  ring

/-- 0 ≤ x < 2π の範囲において f(x) ≤ √3。 -/
theorem f_le_sqrt3 (x : ℝ) : f x ≤ Real.sqrt 3 := by
  rw [f_eq]
  have hsin : sin (x + π / 4) ≤ 1 := Real.sin_le_one _
  have h2cos : 2 * cos (π / 6) = Real.sqrt 3 := two_cos_pi_six
  have hsqrt3_nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have h2cos_nn : 0 ≤ 2 * cos (π / 6) := by rw [h2cos]; exact hsqrt3_nn
  calc 2 * cos (π / 6) * sin (x + π / 4)
      ≤ 2 * cos (π / 6) * 1 := by
        exact mul_le_mul_of_nonneg_left hsin h2cos_nn
    _ = 2 * cos (π / 6) := by ring
    _ = Real.sqrt 3 := h2cos

end Common2026.B_Q2_2
