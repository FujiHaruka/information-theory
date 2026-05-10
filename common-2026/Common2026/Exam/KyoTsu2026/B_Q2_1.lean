/-
2B 第2問 (1)

  二つの角 A, B に対し
    sin A + sin B = 2 sin((A+B)/2) cos((A-B)/2)     ……①
  が成り立つことを示そう。

  二つの角 α, β に対し、加法定理から
    sin(α+β) = sin α cos β + cos α sin β            ……②
    sin(α-β) = sin α cos β - cos α sin β            ……③
  である。② と ③ の左辺どうし、右辺どうしを加え、
    α = (A+B)/2,  β = (A-B)/2
  とすると ① が得られる。
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Common2026.B_Q2_1

open Real

/-- 和積公式 sin A + sin B = 2 sin((A+B)/2) cos((A-B)/2)。 -/
theorem sin_add_sin (A B : ℝ) :
    sin A + sin B = 2 * sin ((A + B) / 2) * cos ((A - B) / 2) := by
  set α := (A + B) / 2 with hα
  set β := (A - B) / 2 with hβ
  have hA : A = α + β := by simp [hα, hβ]; ring
  have hB : B = α - β := by simp [hα, hβ]; ring
  rw [hA, hB, Real.sin_add, Real.sin_sub]
  ring

end Common2026.B_Q2_1
