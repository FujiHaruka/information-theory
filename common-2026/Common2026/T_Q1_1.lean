/-
東大 2026 第1問 (1)

  関数 f(θ) = sin θ - θ + θ³/6 の区間 -1 ≤ θ ≤ 1 における
  最大値 M および最小値 m を求めよ。

  答え:
    M = sin 1 - 5/6
    m = 5/6 - sin 1
  （f は ℝ 上で単調増加。M と m は端点で達成。）
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith

namespace Common2026.T_Q1_1

open Real

noncomputable def f (θ : ℝ) : ℝ := sin θ - θ + θ ^ 3 / 6

/-- 補助 Taylor 不等式: `cos θ ≥ 1 - θ²/2` を変形したもの。 -/
private lemma cos_taylor_lower (θ : ℝ) : 0 ≤ cos θ - 1 + θ ^ 2 / 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := θ)
  linarith

/-- f は微分可能で、その導関数は `cos θ - 1 + θ²/2`。 -/
private lemma f_hasDerivAt (θ : ℝ) :
    HasDerivAt f (cos θ - 1 + θ ^ 2 / 2) θ := by
  have hsin : HasDerivAt sin (cos θ) θ := Real.hasDerivAt_sin θ
  have hid : HasDerivAt (fun x : ℝ => x) (1 : ℝ) θ := hasDerivAt_id θ
  have hpow : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (θ ^ 2 / 2) θ := by
    have h := (hasDerivAt_pow 3 θ).div_const 6
    convert h using 1
    push_cast
    ring
  have h := (hsin.sub hid).add hpow
  exact h

/-- f' ≥ 0 より f は ℝ 上単調非減少。 -/
lemma f_monotone : Monotone f := by
  apply monotone_of_hasDerivAt_nonneg f_hasDerivAt
  intro θ
  exact cos_taylor_lower θ

lemma f_one : f 1 = sin 1 - 5 / 6 := by
  show sin 1 - 1 + (1 : ℝ) ^ 3 / 6 = sin 1 - 5 / 6
  ring

lemma f_neg_one : f (-1) = 5 / 6 - sin 1 := by
  show sin (-1) - (-1) + (-1 : ℝ) ^ 3 / 6 = 5 / 6 - sin 1
  rw [Real.sin_neg]
  ring

/-- 区間 [-1,1] 上の最大値は `sin 1 - 5/6`、達成点は θ = 1。 -/
theorem max_value : ∀ θ ∈ Set.Icc (-1 : ℝ) 1, f θ ≤ sin 1 - 5 / 6 := by
  intro θ hθ
  have h : f θ ≤ f 1 := f_monotone hθ.2
  rw [f_one] at h
  exact h

theorem max_attained : f 1 = sin 1 - 5 / 6 := f_one

/-- 区間 [-1,1] 上の最小値は `5/6 - sin 1`、達成点は θ = -1。 -/
theorem min_value : ∀ θ ∈ Set.Icc (-1 : ℝ) 1, 5 / 6 - sin 1 ≤ f θ := by
  intro θ hθ
  have h : f (-1) ≤ f θ := f_monotone hθ.1
  rw [f_neg_one] at h
  exact h

theorem min_attained : f (-1) = 5 / 6 - sin 1 := f_neg_one

end Common2026.T_Q1_1
