/-
第2問 〔1〕(1)

  f : ℝ → ℝ, f(x) = 2x² − 8x + 5 を考える。
  0 ≤ x ≤ 3 において
    1. x = 0 で最大値 5 をとる。
    2. x = 2 で最小値 −3 をとる。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.Q2_1_1

def f (x : ℝ) : ℝ := 2 * x ^ 2 - 8 * x + 5

/-- 平方完成: f(x) = 2(x − 2)² − 3 -/
private lemma f_completed_square (x : ℝ) : f x = 2 * (x - 2) ^ 2 - 3 := by
  unfold f; ring

/-- 0 ≤ x ≤ 3 において、x = 0 で最大値 5 をとる。 -/
theorem max_value :
    f 0 = 5 ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 3 → f x ≤ 5 := by
  refine ⟨by unfold f; norm_num, ?_⟩
  intro x hx0 hx3
  unfold f
  have h : 0 ≤ x * (4 - x) := mul_nonneg hx0 (by linarith)
  nlinarith [h]

/-- 0 ≤ x ≤ 3 において、x = 2 で最小値 −3 をとる。 -/
theorem min_value :
    f 2 = -3 ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 3 → -3 ≤ f x := by
  refine ⟨by unfold f; norm_num, ?_⟩
  intro x _ _
  rw [f_completed_square]
  have h : 0 ≤ (x - 2) ^ 2 := sq_nonneg _
  linarith

end Common2026.Q2_1_1
