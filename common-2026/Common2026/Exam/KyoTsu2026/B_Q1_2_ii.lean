/-
2B 第1問 (2)(ⅱ)

  O を原点とする座標平面において、方程式
    x² + y² − 7y + (2x − 5y + 25) = 0     ……①
  の表す円を C₁、方程式
    x² + y² − 7y − (2x − 5y + 25) = 0     ……②
  の表す円を C₂ とする。

  ① と ② の左辺の差をとると
    2 (2x − 5y + 25) = 0
  すなわち
    2x − 5y + 25 = 0                       ……④
  が得られる。これは直線 ℓ の方程式である。

  したがって、点 P が C₁ 上かつ C₂ 上にあるならば、P は ℓ 上にある。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.B_Q1_2_ii

/-- ① の表す円 C₁。 -/
def C1 (x y : ℝ) : Prop := x^2 + y^2 - 7*y + (2*x - 5*y + 25) = 0

/-- ② の表す円 C₂。 -/
def C2 (x y : ℝ) : Prop := x^2 + y^2 - 7*y - (2*x - 5*y + 25) = 0

/-- 直線 ℓ: `2x − 5y + 25 = 0`。 -/
def l (x y : ℝ) : Prop := 2*x - 5*y + 25 = 0

/-- C₁ 上かつ C₂ 上にある点は、直線 ℓ 上にある。 -/
theorem on_both_circles_implies_on_line :
    ∀ x y : ℝ, C1 x y → C2 x y → l x y := by
  intro x y h1 h2
  unfold C1 at h1
  unfold C2 at h2
  unfold l
  -- ① の左辺 − ② の左辺 = 2 (2x − 5y + 25) = 0
  linarith

end Common2026.B_Q1_2_ii
