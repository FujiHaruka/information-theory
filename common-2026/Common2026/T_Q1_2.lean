/-
東大 2026 第1問 (2)

  (1) で定めた M = sin 1 - 5/6 に対し、次の不等式を示せ:
    7π/8 ≤ ∫₀^{2π} sin(cos x - x) dx ≤ 7π/8 + 4M

  方針:
    sin(cos x - x) = sin(cos x) cos x - cos(cos x) sin x
    ∫₀^{2π} cos(cos x) sin x dx = 0  （置換 u = cos x で原始関数 -sin(cos x)、両端で値が等しい）
    sin θ = θ - θ³/6 + f(θ)  （f は (1) の関数）
    ⇒ sin(cos x) cos x = cos²x - cos⁴x/6 + f(cos x) cos x
    ∫₀^{2π} cos²x dx = π,  ∫₀^{2π} cos⁴x dx = 3π/4  ⇒ 主項 = π - π/8 = 7π/8
    f は奇関数で f' ≥ 0 ⇒ sign(f θ) = sign θ  ⇒  f(cos x) cos x ≥ 0
    f(cos x) ≤ M, |cos x| の積分は 4  ⇒  ∫ f(cos x) cos x ≤ 4M
-/

import Common2026.T_Q1_1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Common2026.T_Q1

open Real MeasureTheory intervalIntegral

/-! ### 補題群 -/

/-- 置換による消失: 原始関数 `-sin(cos x)` の両端値が `-sin(cos 2π) = -sin(cos 0) = -sin 1`。 -/
private lemma integral_cos_cos_mul_sin :
    ∫ x in (0 : ℝ)..(2 * π), cos (cos x) * sin x = 0 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun y => -sin (cos y)) (cos (cos x) * sin x) x := by
    intro x _
    have h1 : HasDerivAt cos (-sin x) x := Real.hasDerivAt_cos x
    have h2 : HasDerivAt sin (cos (cos x)) (cos x) := Real.hasDerivAt_sin (cos x)
    have h3 : HasDerivAt (fun y => sin (cos y)) (cos (cos x) * (-sin x)) x := h2.comp x h1
    convert h3.neg using 1
    ring
  have hint : IntervalIntegrable (fun x => cos (cos x) * sin x) volume 0 (2 * π) :=
    ((Real.continuous_cos.comp Real.continuous_cos).mul Real.continuous_sin).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.cos_two_pi, Real.cos_zero]

/-- 加法定理 + 上の消失で `∫ sin(cos x - x) = ∫ sin(cos x) cos x`。 -/
private lemma integral_sin_eq :
    ∫ x in (0 : ℝ)..(2 * π), sin (cos x - x) =
      ∫ x in (0 : ℝ)..(2 * π), sin (cos x) * cos x := by
  have hint1 : IntervalIntegrable (fun x => sin (cos x) * cos x) volume 0 (2 * π) :=
    ((Real.continuous_sin.comp Real.continuous_cos).mul Real.continuous_cos).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => cos (cos x) * sin x) volume 0 (2 * π) :=
    ((Real.continuous_cos.comp Real.continuous_cos).mul Real.continuous_sin).intervalIntegrable _ _
  calc ∫ x in (0 : ℝ)..(2 * π), sin (cos x - x)
      = ∫ x in (0 : ℝ)..(2 * π), (sin (cos x) * cos x - cos (cos x) * sin x) := by
            apply intervalIntegral.integral_congr
            intro x _; exact Real.sin_sub _ _
    _ = (∫ x in (0 : ℝ)..(2 * π), sin (cos x) * cos x)
          - ∫ x in (0 : ℝ)..(2 * π), cos (cos x) * sin x :=
            intervalIntegral.integral_sub hint1 hint2
    _ = ∫ x in (0 : ℝ)..(2 * π), sin (cos x) * cos x := by
            rw [integral_cos_cos_mul_sin]; ring

/-- 標準: `∫₀^{2π} cos²x dx = π`。 -/
private lemma integral_cos_sq_zero_two_pi :
    ∫ x in (0 : ℝ)..(2 * π), cos x ^ 2 = π := by
  rw [integral_cos_sq, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero]
  ring

/-- 標準: `∫₀^{2π} cos⁴x dx = 3π/4`。reduction formula 経由。 -/
private lemma integral_cos_four_zero_two_pi :
    ∫ x in (0 : ℝ)..(2 * π), cos x ^ 4 = 3 * π / 4 := by
  have h := integral_cos_pow (n := 2) (a := (0 : ℝ)) (b := 2 * π)
  rw [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero,
      integral_cos_sq_zero_two_pi] at h
  -- h : ∫ cos x^4 = (1^3 * 0 - 1^3 * 0) / 4 + 3/4 * π
  linarith

/-- f の Taylor 展開: `sin θ = θ - θ³/6 + f θ`（定義の単純な変形）。 -/
private lemma sin_eq_taylor_plus_f (θ : ℝ) :
    sin θ = θ - θ ^ 3 / 6 + f θ := by
  show sin θ = θ - θ ^ 3 / 6 + (sin θ - θ + θ ^ 3 / 6)
  ring

/-- 被積分関数の分解: `sin(cos x) cos x = cos²x - cos⁴x/6 + f(cos x) cos x`。 -/
private lemma sin_cos_mul_cos_eq (x : ℝ) :
    sin (cos x) * cos x = cos x ^ 2 - cos x ^ 4 / 6 + f (cos x) * cos x := by
  rw [sin_eq_taylor_plus_f (cos x)]
  ring

/-- 連続性。 -/
private lemma continuous_sin_cos_sub :
    Continuous fun x : ℝ => sin (cos x - x) :=
  Real.continuous_sin.comp (Real.continuous_cos.sub continuous_id)

private lemma continuous_sin_cos_mul_cos :
    Continuous fun x : ℝ => sin (cos x) * cos x :=
  (Real.continuous_sin.comp Real.continuous_cos).mul Real.continuous_cos

private lemma continuous_cos_pow (n : ℕ) :
    Continuous fun x : ℝ => cos x ^ n :=
  Real.continuous_cos.pow n

private lemma continuous_f_cos_mul_cos :
    Continuous fun x : ℝ => f (cos x) * cos x := by
  have hf : Continuous f := by
    unfold f
    exact (Real.continuous_sin.sub continuous_id).add ((continuous_id.pow 3).div_const 6)
  exact (hf.comp Real.continuous_cos).mul Real.continuous_cos

/-- 主等式: `∫ sin(cos x - x) dx = 7π/8 + ∫ f(cos x) cos x dx`。 -/
private lemma integral_eq_main :
    ∫ x in (0 : ℝ)..(2 * π), sin (cos x - x) =
      7 * π / 8 + ∫ x in (0 : ℝ)..(2 * π), f (cos x) * cos x := by
  rw [integral_sin_eq]
  have h1 : IntervalIntegrable (fun x : ℝ => cos x ^ 2) volume 0 (2 * π) :=
    (continuous_cos_pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => cos x ^ 4 / 6) volume 0 (2 * π) :=
    ((continuous_cos_pow 4).div_const 6).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ => f (cos x) * cos x) volume 0 (2 * π) :=
    continuous_f_cos_mul_cos.intervalIntegrable _ _
  have hcongr :
      ∫ x in (0 : ℝ)..(2 * π), sin (cos x) * cos x =
        ∫ x in (0 : ℝ)..(2 * π), (cos x ^ 2 - cos x ^ 4 / 6 + f (cos x) * cos x) := by
    apply intervalIntegral.integral_congr
    intro x _; exact sin_cos_mul_cos_eq x
  rw [hcongr, intervalIntegral.integral_add (h1.sub h2) h3,
      intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_div,
      integral_cos_sq_zero_two_pi, integral_cos_four_zero_two_pi]
  ring

/-! ### 余りの符号評価 -/

/-- f(0) = 0。 -/
private lemma f_zero : f 0 = 0 := by
  show sin 0 - 0 + (0 : ℝ) ^ 3 / 6 = 0
  rw [Real.sin_zero]; ring

/-- f は f(0)=0 で単調増加、よって f θ と θ は同符号。 -/
private lemma f_mul_self_nonneg (θ : ℝ) : 0 ≤ f θ * θ := by
  by_cases hθ : 0 ≤ θ
  · have h := f_monotone hθ
    rw [f_zero] at h
    exact mul_nonneg h hθ
  · have hθ' : θ ≤ 0 := (not_le.mp hθ).le
    have h := f_monotone hθ'
    rw [f_zero] at h
    have h1 : 0 ≤ -(f θ) := by linarith
    have h2 : 0 ≤ -θ := by linarith
    have := mul_nonneg h1 h2
    nlinarith

/-- M = sin 1 - 5/6 = f(1)。-1 ≤ θ ≤ 1 では f θ * θ ≤ M * |θ|。 -/
private lemma f_mul_le_M_abs (θ : ℝ) (h₁ : -1 ≤ θ) (h₂ : θ ≤ 1) :
    f θ * θ ≤ (sin 1 - 5 / 6) * |θ| := by
  by_cases hθ : 0 ≤ θ
  · rw [abs_of_nonneg hθ]
    have hupper : f θ ≤ sin 1 - 5 / 6 := by
      have := f_monotone h₂
      rw [f_one] at this; exact this
    exact mul_le_mul_of_nonneg_right hupper hθ
  · have hθ_neg : θ ≤ 0 := (not_le.mp hθ).le
    rw [abs_of_nonpos hθ_neg]
    have hlower : 5 / 6 - sin 1 ≤ f θ := by
      have := f_monotone h₁
      rw [f_neg_one] at this; exact this
    have h_neg : -(sin 1 - 5 / 6) ≤ f θ := by linarith
    have := mul_le_mul_of_nonpos_right h_neg hθ_neg
    linarith

/-- 補助: cos x ∈ [-1, 1] -/
private lemma neg_one_le_cos (x : ℝ) : -1 ≤ cos x := Real.neg_one_le_cos x
private lemma cos_le_one (x : ℝ) : cos x ≤ 1 := Real.cos_le_one x

/-- ∫₀^{2π} f(cos x) cos x dx ≥ 0 -/
private lemma integral_f_cos_mul_cos_nonneg :
    0 ≤ ∫ x in (0 : ℝ)..(2 * π), f (cos x) * cos x := by
  apply intervalIntegral.integral_nonneg
  · linarith [Real.pi_pos]
  · intro x _; exact f_mul_self_nonneg (cos x)

/-- ∫₀^{2π} |cos x| dx = 4。`[0, π/2]`, `[π/2, 3π/2]`, `[3π/2, 2π]` で cos の符号で場合分け。 -/
private lemma integral_abs_cos : ∫ x in (0 : ℝ)..(2 * π), |cos x| = 4 := by
  have hπ : 0 < π := Real.pi_pos
  have h0 : (0 : ℝ) ≤ π / 2 := by linarith
  have h1 : (π / 2 : ℝ) ≤ 3 * π / 2 := by linarith
  have h2 : (3 * π / 2 : ℝ) ≤ 2 * π := by linarith
  have hcont : Continuous fun x : ℝ => |cos x| := Real.continuous_cos.abs
  have hint01 : IntervalIntegrable (fun x : ℝ => |cos x|) volume 0 (π / 2) :=
    hcont.intervalIntegrable _ _
  have hint12 : IntervalIntegrable (fun x : ℝ => |cos x|) volume (π / 2) (3 * π / 2) :=
    hcont.intervalIntegrable _ _
  have hint23 : IntervalIntegrable (fun x : ℝ => |cos x|) volume (3 * π / 2) (2 * π) :=
    hcont.intervalIntegrable _ _
  have piece1 : ∫ x in (0 : ℝ)..(π / 2), |cos x| = 1 := by
    have hcongr : ∫ x in (0 : ℝ)..(π / 2), |cos x| = ∫ x in (0 : ℝ)..(π / 2), cos x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h0] at hx
      have : 0 ≤ cos x :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩
      simp [abs_of_nonneg this]
    rw [hcongr, integral_cos, Real.sin_pi_div_two, Real.sin_zero]; ring
  have hsin_three_pi_two : Real.sin (3 * π / 2) = -1 := by
    have heq : (3 * π / 2 : ℝ) = π / 2 + π := by ring
    rw [heq, Real.sin_add_pi, Real.sin_pi_div_two]
  have piece2 : ∫ x in (π / 2 : ℝ)..(3 * π / 2), |cos x| = 2 := by
    have hcongr :
        ∫ x in (π / 2 : ℝ)..(3 * π / 2), |cos x| =
          ∫ x in (π / 2 : ℝ)..(3 * π / 2), -cos x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h1] at hx
      have : cos x ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2])
      simp [abs_of_nonpos this]
    rw [hcongr, intervalIntegral.integral_neg, integral_cos,
        hsin_three_pi_two, Real.sin_pi_div_two]; ring
  have piece3 : ∫ x in (3 * π / 2 : ℝ)..(2 * π), |cos x| = 1 := by
    have hcongr :
        ∫ x in (3 * π / 2 : ℝ)..(2 * π), |cos x| =
          ∫ x in (3 * π / 2 : ℝ)..(2 * π), cos x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h2] at hx
      have hxshift : x - 2 * π ∈ Set.Icc (-(π / 2)) (π / 2) := by
        constructor
        · linarith [hx.1]
        · linarith [hx.2]
      have hcos_shift : 0 ≤ cos (x - 2 * π) := Real.cos_nonneg_of_mem_Icc hxshift
      have : 0 ≤ cos x := by rwa [Real.cos_sub_two_pi] at hcos_shift
      simp [abs_of_nonneg this]
    rw [hcongr, integral_cos, Real.sin_two_pi, hsin_three_pi_two]; ring
  calc
    ∫ x in (0 : ℝ)..(2 * π), |cos x|
        = (∫ x in (0 : ℝ)..(π / 2), |cos x|) + ∫ x in (π / 2 : ℝ)..(2 * π), |cos x| := by
              rw [intervalIntegral.integral_add_adjacent_intervals hint01
                (hint12.trans hint23)]
      _ = (∫ x in (0 : ℝ)..(π / 2), |cos x|)
            + ((∫ x in (π / 2 : ℝ)..(3 * π / 2), |cos x|)
              + ∫ x in (3 * π / 2 : ℝ)..(2 * π), |cos x|) := by
              rw [intervalIntegral.integral_add_adjacent_intervals hint12 hint23]
      _ = 1 + (2 + 1) := by rw [piece1, piece2, piece3]
      _ = 4 := by ring

/-- ∫₀^{2π} f(cos x) cos x dx ≤ 4M -/
private lemma integral_f_cos_mul_cos_le :
    ∫ x in (0 : ℝ)..(2 * π), f (cos x) * cos x ≤ 4 * (sin 1 - 5 / 6) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by linarith [Real.pi_pos]
  have hint_lhs : IntervalIntegrable (fun x => f (cos x) * cos x) volume 0 (2 * π) :=
    continuous_f_cos_mul_cos.intervalIntegrable _ _
  have hint_rhs : IntervalIntegrable
      (fun x => (sin 1 - 5 / 6) * |cos x|) volume 0 (2 * π) :=
    (continuous_const.mul Real.continuous_cos.abs).intervalIntegrable _ _
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) (2 * π),
      f (cos x) * cos x ≤ (sin 1 - 5 / 6) * |cos x| := by
    intro x _
    exact f_mul_le_M_abs (cos x) (neg_one_le_cos x) (cos_le_one x)
  have hmono := intervalIntegral.integral_mono_on h2π hint_lhs hint_rhs hpoint
  rw [intervalIntegral.integral_const_mul, integral_abs_cos] at hmono
  linarith

/-! ### 主結果 -/

theorem main_lower :
    7 * π / 8 ≤ ∫ x in (0 : ℝ)..(2 * π), sin (cos x - x) := by
  rw [integral_eq_main]
  linarith [integral_f_cos_mul_cos_nonneg]

theorem main_upper :
    ∫ x in (0 : ℝ)..(2 * π), sin (cos x - x) ≤ 7 * π / 8 + 4 * (sin 1 - 5 / 6) := by
  rw [integral_eq_main]
  linarith [integral_f_cos_mul_cos_le]

end Common2026.T_Q1
