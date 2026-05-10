/-
2B 第1問 (1)

  O を原点とする座標平面において、方程式
    x² + y² − 7y + (2x − 5y + 25) = 0     ……①
  の表す円を C₁、方程式
    x² + y² − 7y − (2x − 5y + 25) = 0     ……②
  の表す円を C₂ とする。

  (1) C₁ の中心の座標は (−1, 6) である。
      C₁ の半径を r₁、C₂ の半径を r₂、C₁ の中心と C₂ の中心の間の距離を d とすると、
        r₁ = 2√3,  r₂ = 3√3,  d = √29
      r₁, r₂ と d の関係から、C₁ と C₂ は 2 点で交わる
      (|r₁ − r₂| < d < r₁ + r₂):
        |r₁ − r₂| = √3,  r₁ + r₂ = 5√3,  √3 < √29 < 5√3。
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Common2026.B_Q1_1

/-! ## 円の方程式 -/

/-- ① の表す円 C₁。 -/
def C1 (x y : ℝ) : Prop := x^2 + y^2 - 7*y + (2*x - 5*y + 25) = 0

/-- ② の表す円 C₂。 -/
def C2 (x y : ℝ) : Prop := x^2 + y^2 - 7*y - (2*x - 5*y + 25) = 0

/-- 平方完成: C₁ は中心 (−1, 6)、半径の 2 乗が 12 の円。 -/
theorem C1_eq_circle (x y : ℝ) :
    C1 x y ↔ (x - (-1))^2 + (y - 6)^2 = 12 := by
  unfold C1
  have key : (x - (-1))^2 + (y - 6)^2 - 12
      = x^2 + y^2 - 7*y + (2*x - 5*y + 25) := by ring
  constructor <;> intro h <;> linarith

/-- 平方完成: C₂ は中心 (1, 1)、半径の 2 乗が 27 の円。 -/
theorem C2_eq_circle (x y : ℝ) :
    C2 x y ↔ (x - 1)^2 + (y - 1)^2 = 27 := by
  unfold C2
  have key : (x - 1)^2 + (y - 1)^2 - 27
      = x^2 + y^2 - 7*y - (2*x - 5*y + 25) := by ring
  constructor <;> intro h <;> linarith

/-- C₁ の中心 (−1, 6)。 -/
def center1 : ℝ × ℝ := (-1, 6)

/-- C₂ の中心 (1, 1)。 -/
def center2 : ℝ × ℝ := (1, 1)

/-- C₁ の半径 r₁ = 2√3。 -/
noncomputable def r1 : ℝ := 2 * Real.sqrt 3

/-- C₂ の半径 r₂ = 3√3。 -/
noncomputable def r2 : ℝ := 3 * Real.sqrt 3

/-- 中心間の距離 d = √29。 -/
noncomputable def d : ℝ := Real.sqrt 29

/-- r₁² = 12。 -/
theorem r1_sq : r1^2 = 12 := by
  unfold r1
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- r₂² = 27。 -/
theorem r2_sq : r2^2 = 27 := by
  unfold r2
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-- d² = 29。 -/
theorem d_sq : d^2 = 29 := by
  unfold d
  exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 29)

/-- r₁, r₂ はいずれも非負。 -/
theorem r1_nonneg : 0 ≤ r1 := by unfold r1; positivity

theorem r2_nonneg : 0 ≤ r2 := by unfold r2; positivity

theorem d_nonneg : 0 ≤ d := by unfold d; exact Real.sqrt_nonneg _

/-- C₁ と C₂ の中心間距離の 2 乗 = (1−(−1))² + (1−6)² = 29 = d²。 -/
theorem center_dist_sq :
    (center1.1 - center2.1)^2 + (center1.2 - center2.2)^2 = d^2 := by
  rw [d_sq]
  unfold center1 center2
  norm_num

/-- 2 円が 2 点で交わるための条件 |r₁ − r₂| < d < r₁ + r₂ を確認する。
    r₁ = 2√3, r₂ = 3√3 より r₁ − r₂ = −√3, r₁ + r₂ = 5√3。
    したがって |r₁ − r₂| = √3 < √29 = d (∵ 3 < 29) と
    d = √29 < √75 = 5√3 (∵ 29 < 75) が成り立つ。 -/
theorem two_points_intersection : |r1 - r2| < d ∧ d < r1 + r2 := by
  have h3 : (0:ℝ) ≤ 3 := by norm_num
  have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · -- |r₁ − r₂| < d
    have hdiff : r1 - r2 = -Real.sqrt 3 := by unfold r1 r2; ring
    have habs : |r1 - r2| = Real.sqrt 3 := by
      rw [hdiff, abs_neg, abs_of_nonneg hsqrt3]
    rw [habs]
    show Real.sqrt 3 < d
    unfold d
    exact Real.sqrt_lt_sqrt h3 (by norm_num)
  · -- d < r₁ + r₂
    have hsum : r1 + r2 = 5 * Real.sqrt 3 := by unfold r1 r2; ring
    rw [hsum]
    -- 5 √3 = √75 として比較する。
    have h5sqrt3 : (5 : ℝ) * Real.sqrt 3 = Real.sqrt 75 := by
      have : (75 : ℝ) = 5^2 * 3 := by norm_num
      rw [this, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
    rw [h5sqrt3]
    show d < Real.sqrt 75
    unfold d
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end Common2026.B_Q1_1
