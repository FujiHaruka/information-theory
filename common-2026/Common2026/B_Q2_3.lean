/-
2B 第2問 (3)

  a を 0 < a < π を満たす定数とし、関数 g(x) を
    g(x) = sin(x + a) + sin(x + 2a) + sin(x + 3a)
  とする。

  ① (和積公式) を用いると、関数 sin(x+a), sin(x+2a), sin(x+3a) のうちの二つの関数の和
    sin(x + a) + sin(x + 3a)
  は、残りの関数 sin(x + 2a) の定数倍となる:
    sin(x + a) + sin(x + 3a) = 2 cos a · sin(x + 2a).
  したがって、関数 g(x) は
    g(x) = (2 cos a + 1) sin(x + 2a)
  と変形することができる。

  (ⅱ) a = 5π/6 のとき、0 ≤ x < 2π の範囲において、g(x) は x = (11/6)π で
       最大値 √3 - 1 をとる。
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

namespace Common2026.B_Q2_3

open Real

/-- 関数 g(x) = sin(x+a) + sin(x+2a) + sin(x+3a)。 -/
noncomputable def g (a x : ℝ) : ℝ :=
  sin (x + a) + sin (x + 2 * a) + sin (x + 3 * a)

/-- sin(x+a) + sin(x+3a) = 2 cos a · sin(x+2a)。 -/
theorem pair_eq (a x : ℝ) :
    sin (x + a) + sin (x + 3 * a) = 2 * cos a * sin (x + 2 * a) := by
  -- 加法定理を陽に適用してから ring で閉じる。
  have hsub : sin ((x + 2 * a) - a)
      = sin (x + 2 * a) * cos a - cos (x + 2 * a) * sin a := Real.sin_sub _ _
  have hadd : sin ((x + 2 * a) + a)
      = sin (x + 2 * a) * cos a + cos (x + 2 * a) * sin a := Real.sin_add _ _
  have e1 : x + a = (x + 2 * a) - a := by ring
  have e2 : x + 3 * a = (x + 2 * a) + a := by ring
  rw [e1, e2, hsub, hadd]
  ring

/-- g(x) = (2 cos a + 1) · sin(x + 2a)。 -/
theorem g_eq (a x : ℝ) : g a x = (2 * cos a + 1) * sin (x + 2 * a) := by
  unfold g
  have hpair := pair_eq a x
  -- g(x) = sin(x+a) + sin(x+2a) + sin(x+3a)
  --      = (sin(x+a) + sin(x+3a)) + sin(x+2a)
  --      = 2 cos a sin(x+2a) + sin(x+2a)
  --      = (2 cos a + 1) sin(x+2a)
  linarith [hpair]

/-- a = 5π/6 のとき 2 cos a + 1 = 1 - √3。 -/
theorem coeff_at_5pi_6 : 2 * cos (5 * π / 6) + 1 = 1 - Real.sqrt 3 := by
  have h : (5 * π / 6 : ℝ) = π - π / 6 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_six]
  ring

/-- sin(7π/2) = -1。 -/
theorem sin_seven_pi_div_two : sin (7 * π / 2) = -1 := by
  -- 7π/2 = (π/2 + π) + (2π) で sin(π/2 + π) = -sin(π/2) = -1。
  have h1 : (7 * π / 2 : ℝ) = (π / 2 + π) + 2 * π := by ring
  have h2 : sin ((π / 2 + π) + 2 * π) = sin (π / 2 + π) :=
    Real.sin_periodic _
  rw [h1, h2, Real.sin_add_pi, Real.sin_pi_div_two]

/-- a = 5π/6, x = 11π/6 のとき g = √3 - 1。 -/
theorem g_at_max :
    g (5 * π / 6) (11 * π / 6) = Real.sqrt 3 - 1 := by
  rw [g_eq, coeff_at_5pi_6]
  have hx : (11 * π / 6 : ℝ) + 2 * (5 * π / 6) = 7 * π / 2 := by ring
  rw [hx, sin_seven_pi_div_two]
  ring

end Common2026.B_Q2_3
