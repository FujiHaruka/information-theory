/-
第1問 [2](1)

  四角形 ABCD の内角を A, B, C, D とする。対角線 BD を共通の 1 辺とする
  △ABD, △BCD の面積をそれぞれ

    S₁ = (AB · AD / 2) · sin A
    S₂ = (BC · CD / 2) · sin C

  とする。四角形の内角の和は 360° (= 2π) であり、A + C = B + D を満たすとき、

    1. A + C = π (= 180°) である。
    2. sin C = sin A であるから、
         S = S₁ + S₂ = ((AB · AD + BC · CD) / 2) · sin A
       となる。
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

namespace Common2026.Q1_2_1

open Real

/-- 四角形の内角の和が 2π であり、A + C = B + D を満たすとき A + C = π。 -/
theorem angle_sum_eq_pi
    (A B C D : ℝ)
    (h_sum : A + B + C + D = 2 * π)
    (h_eq : A + C = B + D) :
    A + C = π := by
  linarith

/-- A + C = π のとき、`(AB·AD/2)·sin A + (BC·CD/2)·sin C` は
    `((AB·AD + BC·CD)/2)·sin A` と等しい。 -/
theorem area_sum_eq
    (A C AB AD BC CD : ℝ)
    (h_AC : A + C = π) :
    (AB * AD / 2) * sin A + (BC * CD / 2) * sin C
      = ((AB * AD + BC * CD) / 2) * sin A := by
  have hC : C = π - A := by linarith
  rw [hC, sin_pi_sub]
  ring

end Common2026.Q1_2_1
