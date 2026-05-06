/-
2B 第1問 (2)(ⅰ)

  O を原点とする座標平面において、不等式
    x² + y² − 7y + |2x − 5y + 25| < 0      ……③
  を考える。

  座標平面を、`2x − 5y + 25 ≥ 0` を満たす領域 D と、
  `2x − 5y + 25 < 0` を満たす領域 E に分ける。

  このとき、
    ・原点 O = (0, 0) は D に含まれる。
    ・C₁ の中心 (−1, 6) は E に含まれる。
    ・C₂ の中心 (1, 1) は D に含まれる。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Common2026.B_Q1_2_i

/-! ## 領域 D, E -/

/-- 領域 D: `2x − 5y + 25 ≥ 0` を満たす点全体。 -/
def D (x y : ℝ) : Prop := 2*x - 5*y + 25 ≥ 0

/-- 領域 E: `2x − 5y + 25 < 0` を満たす点全体。 -/
def E (x y : ℝ) : Prop := 2*x - 5*y + 25 < 0

/-! ## 各点の所属 -/

/-- 原点 O = (0, 0) は D に含まれる。 -/
theorem origin_mem_D : D 0 0 := by
  unfold D; norm_num

/-- C₁ の中心 (−1, 6) は E に含まれる。 -/
theorem center1_mem_E : E (-1) 6 := by
  unfold E; norm_num

/-- C₂ の中心 (1, 1) は D に含まれる。 -/
theorem center2_mem_D : D 1 1 := by
  unfold D; norm_num

end Common2026.B_Q1_2_i
