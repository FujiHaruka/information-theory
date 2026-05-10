/-
東大 2026 第5問

  複素数平面上の原点を中心とする半径 1 の円を C とする。
  複素数 α と C 上の点 P(z) に対し、w = (z − α)³ とおく。
  P が C 上を動くときの点 Q(w) の軌跡を D とする。

(1) α = −3 とし、w の偏角を θ とおく。
    P が C 上を動くとき、sin θ がとりうる値の範囲を求めよ。

  答え: sin θ ∈ [−23/27, 23/27]。

  方針:
    z = (x, y) (x² + y² = 1) として α = −3 で w = (z + 3)³。
      Im(w) = y(3(x+3)² − y²)
      |z+3|² = (x+3)² + y² = 10 + 6x  (∵ x² + y² = 1)
      |w| = |z+3|³ = (10+6x)^{3/2}
    sin θ := Im(w)/|w| とすれば、ψ = arg(z+3) とおくと
      sin ψ = y/√(10+6x), sin θ = sin 3ψ = 3 sin ψ − 4 sin³ ψ。

    Step 1: 9y² ≤ 10 + 6x  ((3x+1)² ≥ 0 より 9 − 9x² ≤ 10 + 6x)。
            ⇒ t := y/√(10+6x) について t² ≤ 1/9。
    Step 2: t² ≤ 1/9 のとき |3t − 4t³| ≤ 23/27。
            キーの分解:
              2(23 − 81t + 108t³) = (3t−1)²(24t + 31) + 15(1 − 9t²)
              (24t + 31 ≥ 24·(−1/3) + 31 = 23 > 0)
    Step 3: 逆向き — 中間値の定理。
            f(x) := sinTheta(x, √(1−x²)) は [−1, 1] で連続で
              f(−1) = 0, f(−1/3) = 23/27。
            IVT で [0, 23/27] が網羅される。負側は y = −√(1−x²) で同様。

(2) α が次の条件を満たすように動く:
    条件: D は実軸の正の部分および負の部分の両方と共有点を持つ。
    複素数平面上の点 R(α) が動きうる範囲の面積を求めよ。

  答え: 4√3。

  方針 (要約; 本ファイルでは形式化していない):
    ω = e^{2πi/3}。
      (z − α)³ ∈ ℝ_{>0} ⇔ z − α ∈ ℝ_{>0}{1, ω, ω²} (3 方向)
      (z − α)³ ∈ ℝ_{<0} ⇔ z − α ∈ ℝ_{>0}{−1, −ω, −ω²} (3 方向)
    α からの 6 方向 (kπ/3, k=0..5) のうち、偶 k の方向 (cube roots of 1) と
    奇 k の方向 (cube roots of −1) の少なくとも 1 本ずつが単位円と交わる必要がある。

    α = (r, γ) のとき α から方向 θ の半直線が単位円と交わるのは:
      r ≤ 1: 任意の θ
      r > 1: θ ∈ [β−δ, β+δ] (β = γ+π, δ = arcsin(1/r))。

    良い α の集合の面積:
      r ≤ 2/√3 (δ ≥ π/3): 弧の長さが 2π/3 以上で常に 2 連続方向を含む。
                          面積 = π · (2/√3)² = 4π/3。
      2/√3 < r < 2 (π/6 < δ < π/3): 良い γ の弧の合計長さ = 12 arcsin(1/r) − 2π。
                          ∫_{2/√3}^2 r(12 arcsin(1/r) − 2π) dr。
                          ∫ r arcsin(1/r) dr = (r²/2)arcsin(1/r) + (1/2)√(r²−1)。
                          [F(2) − F(2/√3)] = π/9 + √3/3。
                          12(π/9 + √3/3) − 2π · (4/3) = −4π/3 + 4√3。
      r ≥ 2 (δ ≤ π/6): 良い γ なし (測度 0)。
    合計: 4π/3 + (−4π/3 + 4√3) = 4√3。

  本ファイルでは
    (1) を完全形式化、
    (2) は予述語 `IsGoodAlpha` の定義と単位開円板の包含 (構造的補題) のみ形式化し、
        面積 4√3 は上記で略述するに留める。
        (積分 ∫r arcsin(1/r) dr の Lean 形式化が大規模になるため)。
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Common2026.T_Q5

open Real

/-! ## (1) sin θ の取り得る値の範囲 -/

/-! ### 共通定義 -/

/-- z = (x, y) が単位円上 (x² + y² = 1)。 -/
def OnCircle (z : ℝ × ℝ) : Prop := z.1 ^ 2 + z.2 ^ 2 = 1

/-- |z + 3| (z on unit circle なら √(10 + 6x))。 -/
noncomputable def Rabs (z : ℝ × ℝ) : ℝ := sqrt (10 + 6 * z.1)

/-- sin θ = Im((z+3)³) / |z+3|³ = y(3(x+3)² − y²) / (10+6x)^{3/2}。 -/
noncomputable def sinTheta (z : ℝ × ℝ) : ℝ :=
  z.2 * (3 * (z.1 + 3) ^ 2 - z.2 ^ 2) / (Rabs z) ^ 3

/-! ### Rabs の基本性質 -/

private lemma onCircle_x_lb {z : ℝ × ℝ} (h : OnCircle z) : -1 ≤ z.1 := by
  have hh : z.1 ^ 2 + z.2 ^ 2 = 1 := h
  nlinarith [sq_nonneg z.2, sq_nonneg (z.1 + 1), hh]

private lemma onCircle_x_ub {z : ℝ × ℝ} (h : OnCircle z) : z.1 ≤ 1 := by
  have hh : z.1 ^ 2 + z.2 ^ 2 = 1 := h
  nlinarith [sq_nonneg z.2, sq_nonneg (z.1 - 1), hh]

private lemma ten_plus_six_x_pos {z : ℝ × ℝ} (h : OnCircle z) : 0 < 10 + 6 * z.1 := by
  have := onCircle_x_lb h; linarith

lemma Rabs_pos {z : ℝ × ℝ} (h : OnCircle z) : 0 < Rabs z :=
  sqrt_pos.mpr (ten_plus_six_x_pos h)

lemma Rabs_sq {z : ℝ × ℝ} (h : OnCircle z) : (Rabs z) ^ 2 = 10 + 6 * z.1 := by
  unfold Rabs
  rw [sq, mul_self_sqrt (ten_plus_six_x_pos h).le]

/-! ### sin θ = 3t − 4t³ の表示 -/

/-- 分子の書き換え: y(3(x+3)² − y²) = 3y·R² − 4y³ (z on circle で R² = 10+6x)。 -/
private lemma sinTheta_num_eq {z : ℝ × ℝ} (h : OnCircle z) :
    z.2 * (3 * (z.1 + 3) ^ 2 - z.2 ^ 2) = 3 * z.2 * (Rabs z) ^ 2 - 4 * z.2 ^ 3 := by
  rw [Rabs_sq h]
  have hh : z.1 ^ 2 + z.2 ^ 2 = 1 := h
  linear_combination 3 * z.2 * hh

/-- z が単位円上のとき sin θ = 3t − 4t³ (t = y/Rabs z)。 -/
lemma sinTheta_eq_cubic {z : ℝ × ℝ} (h : OnCircle z) :
    sinTheta z = 3 * (z.2 / Rabs z) - 4 * (z.2 / Rabs z) ^ 3 := by
  unfold sinTheta
  rw [sinTheta_num_eq h]
  have hR_ne : Rabs z ≠ 0 := (Rabs_pos h).ne'
  field_simp

/-! ### t² ≤ 1/9 -/

/-- z が単位円上のとき t = y/Rabs z は t² ≤ 1/9 を満たす。 -/
lemma t_sq_le {z : ℝ × ℝ} (h : OnCircle z) :
    (z.2 / Rabs z) ^ 2 ≤ 1 / 9 := by
  rw [div_pow, Rabs_sq h]
  rw [div_le_iff₀ (ten_plus_six_x_pos h)]
  -- z.2² ≤ (10+6x)/9 ⇔ 9 z.2² ≤ 10+6x ⇔ 9(1−x²) ≤ 10+6x ⇔ 0 ≤ (3x+1)²
  have hh : z.1 ^ 2 + z.2 ^ 2 = 1 := h
  nlinarith [sq_nonneg (3 * z.1 + 1), hh]

/-! ### 多項式不等式: t² ≤ 1/9 ⇒ |3t − 4t³| ≤ 23/27 -/

/-- 鍵となる多項式恒等式:
    2(23 − 81t + 108t³) = (3t−1)²(24t + 31) + 15(1 − 9t²)。 -/
private lemma upper_poly_id (t : ℝ) :
    2 * (23 - 81 * t + 108 * t ^ 3) =
      (3 * t - 1) ^ 2 * (24 * t + 31) + 15 * (1 - 9 * t ^ 2) := by
  ring

/-- t² ≤ 1/9 のとき −1/3 ≤ t。 -/
private lemma t_lb {t : ℝ} (h : t ^ 2 ≤ 1/9) : -1/3 ≤ t := by
  nlinarith [sq_nonneg (3 * t + 1), h]

/-- 上限: t² ≤ 1/9 ⇒ 3t − 4t³ ≤ 23/27。 -/
lemma cubic_le {t : ℝ} (h : t ^ 2 ≤ 1/9) : 3 * t - 4 * t ^ 3 ≤ 23 / 27 := by
  have h_lb : -1/3 ≤ t := t_lb h
  have h_pos : 0 ≤ 24 * t + 31 := by linarith
  have h_diff : 0 ≤ 1 - 9 * t ^ 2 := by linarith
  have h_id := upper_poly_id t
  have h_prod : 0 ≤ (3 * t - 1) ^ 2 * (24 * t + 31) :=
    mul_nonneg (sq_nonneg _) h_pos
  have h_15 : 0 ≤ 15 * (1 - 9 * t ^ 2) := by linarith
  -- 2(23 − 81t + 108t³) = h_prod + h_15 ≥ 0 ⇒ 27(3t − 4t³) ≤ 23
  linarith

/-- 下限: t² ≤ 1/9 ⇒ −23/27 ≤ 3t − 4t³ (上限を −t に適用)。 -/
lemma cubic_ge {t : ℝ} (h : t ^ 2 ≤ 1/9) : -(23 / 27) ≤ 3 * t - 4 * t ^ 3 := by
  have h' : (-t) ^ 2 ≤ 1/9 := by rw [neg_pow]; simpa using h
  have := cubic_le h'
  nlinarith [this]

/-! ### 順方向: sin θ ∈ [−23/27, 23/27] -/

theorem sinTheta_le {z : ℝ × ℝ} (h : OnCircle z) : sinTheta z ≤ 23 / 27 := by
  rw [sinTheta_eq_cubic h]; exact cubic_le (t_sq_le h)

theorem sinTheta_ge {z : ℝ × ℝ} (h : OnCircle z) : -(23 / 27) ≤ sinTheta z := by
  rw [sinTheta_eq_cubic h]; exact cubic_ge (t_sq_le h)

/-! ### 逆方向: 中間値の定理 -/

/-- 上半円のパラメータ表示。 -/
noncomputable def fUpper (x : ℝ) : ℝ := sinTheta (x, sqrt (1 - x ^ 2))

/-- 下半円のパラメータ表示。 -/
noncomputable def fLower (x : ℝ) : ℝ := sinTheta (x, -sqrt (1 - x ^ 2))

/-- x² ≤ 1 のとき (x, √(1−x²)) は単位円上。 -/
private lemma onCircle_upper {x : ℝ} (h : x ^ 2 ≤ 1) :
    OnCircle (x, sqrt (1 - x ^ 2)) := by
  show x ^ 2 + (sqrt (1 - x ^ 2)) ^ 2 = 1
  rw [sq_sqrt (by linarith : (0:ℝ) ≤ 1 - x ^ 2)]; ring

private lemma onCircle_lower {x : ℝ} (h : x ^ 2 ≤ 1) :
    OnCircle (x, -sqrt (1 - x ^ 2)) := by
  show x ^ 2 + (-sqrt (1 - x ^ 2)) ^ 2 = 1
  have h1 : (-sqrt (1 - x ^ 2)) ^ 2 = (sqrt (1 - x ^ 2)) ^ 2 := by ring
  rw [h1, sq_sqrt (by linarith : (0:ℝ) ≤ 1 - x ^ 2)]; ring

/-! ### 端点の値計算 -/

/-- f(−1) = 0。 -/
private lemma fUpper_neg_one : fUpper (-1 : ℝ) = 0 := by
  unfold fUpper
  have hsqrt : sqrt (1 - (-1 : ℝ) ^ 2) = 0 := by
    rw [show (1 - (-1 : ℝ) ^ 2 : ℝ) = 0 from by norm_num]; exact sqrt_zero
  show sinTheta ((-1 : ℝ), sqrt (1 - (-1) ^ 2)) = 0
  rw [hsqrt]
  unfold sinTheta
  show (0 : ℝ) * (3 * ((-1 : ℝ) + 3) ^ 2 - (0 : ℝ) ^ 2) / (Rabs ((-1 : ℝ), 0)) ^ 3 = 0
  ring

/-- g(−1) = 0。 -/
private lemma fLower_neg_one : fLower (-1 : ℝ) = 0 := by
  unfold fLower
  have hsqrt : sqrt (1 - (-1 : ℝ) ^ 2) = 0 := by
    rw [show (1 - (-1 : ℝ) ^ 2 : ℝ) = 0 from by norm_num]; exact sqrt_zero
  show sinTheta ((-1 : ℝ), -sqrt (1 - (-1) ^ 2)) = 0
  rw [hsqrt]
  unfold sinTheta
  show (-(0 : ℝ)) * (3 * ((-1 : ℝ) + 3) ^ 2 - (-(0 : ℝ)) ^ 2)
        / (Rabs ((-1 : ℝ), -(0 : ℝ))) ^ 3 = 0
  ring

/-- 補題: √(8/9) = √8 / 3。 -/
private lemma sqrt_eight_ninths_eq : sqrt (8 / 9 : ℝ) = sqrt 8 / 3 := by
  have h : (sqrt 8 / 3 : ℝ) ^ 2 = 8 / 9 := by
    rw [div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  have h1 : (0 : ℝ) ≤ sqrt 8 / 3 := div_nonneg (sqrt_nonneg _) (by norm_num)
  rw [show (8 / 9 : ℝ) = (sqrt 8 / 3) ^ 2 from h.symm]
  exact sqrt_sq h1

/-- 補題: √(8/9) / √8 = 1/3。 -/
private lemma sqrt_ratio_eq : sqrt (8 / 9 : ℝ) / sqrt 8 = 1 / 3 := by
  rw [sqrt_eight_ninths_eq]
  have h8 : (0 : ℝ) < sqrt 8 := sqrt_pos.mpr (by norm_num)
  field_simp

/-- f(−1/3) = 23/27。 -/
private lemma fUpper_neg_third : fUpper (-1/3 : ℝ) = 23 / 27 := by
  unfold fUpper
  have h_inner : (1 - (-1/3 : ℝ) ^ 2 : ℝ) = 8 / 9 := by norm_num
  rw [h_inner]
  have hOC : OnCircle ((-1/3 : ℝ), sqrt (8 / 9)) := by
    show (-1/3 : ℝ) ^ 2 + (sqrt (8 / 9)) ^ 2 = 1
    rw [sq_sqrt (by norm_num : (0:ℝ) ≤ 8/9)]; norm_num
  rw [sinTheta_eq_cubic hOC]
  have h_t : (sqrt (8/9) : ℝ) / Rabs ((-1/3 : ℝ), sqrt (8/9)) = 1/3 := by
    show sqrt (8/9) / sqrt (10 + 6 * (-1/3 : ℝ)) = 1/3
    rw [show ((10 : ℝ) + 6 * (-1/3 : ℝ)) = 8 from by ring]
    exact sqrt_ratio_eq
  show 3 * (sqrt (8/9) / Rabs ((-1/3 : ℝ), sqrt (8/9))) -
       4 * (sqrt (8/9) / Rabs ((-1/3 : ℝ), sqrt (8/9))) ^ 3 = 23 / 27
  rw [h_t]; norm_num

/-- g(−1/3) = −23/27。 -/
private lemma fLower_neg_third : fLower (-1/3 : ℝ) = -(23 / 27) := by
  unfold fLower
  have h_inner : (1 - (-1/3 : ℝ) ^ 2 : ℝ) = 8 / 9 := by norm_num
  rw [h_inner]
  have hOC : OnCircle ((-1/3 : ℝ), -sqrt (8 / 9)) := by
    show (-1/3 : ℝ) ^ 2 + (-sqrt (8 / 9)) ^ 2 = 1
    have hh : (-sqrt (8/9 : ℝ)) ^ 2 = (sqrt (8/9 : ℝ)) ^ 2 := by ring
    rw [hh, sq_sqrt (by norm_num : (0:ℝ) ≤ 8/9)]; norm_num
  rw [sinTheta_eq_cubic hOC]
  have h_t : (-sqrt (8/9) : ℝ) / Rabs ((-1/3 : ℝ), -sqrt (8/9)) = -(1/3) := by
    show -sqrt (8/9) / sqrt (10 + 6 * (-1/3 : ℝ)) = -(1/3)
    rw [show ((10 : ℝ) + 6 * (-1/3 : ℝ)) = 8 from by ring]
    rw [neg_div, sqrt_ratio_eq]
  show 3 * (-sqrt (8/9) / Rabs ((-1/3 : ℝ), -sqrt (8/9))) -
       4 * (-sqrt (8/9) / Rabs ((-1/3 : ℝ), -sqrt (8/9))) ^ 3 = -(23 / 27)
  rw [h_t]; norm_num

/-! ### 連続性 -/

private lemma continuous_sqrt_one_sub_sq :
    ContinuousOn (fun x : ℝ => sqrt (1 - x ^ 2)) (Set.Icc (-1 : ℝ) 1) := by
  apply Real.continuous_sqrt.comp_continuousOn
  exact continuous_const.continuousOn.sub (continuous_pow 2).continuousOn

private lemma continuous_Rabs_aux :
    ContinuousOn (fun x : ℝ => Rabs (x, sqrt (1 - x ^ 2))) (Set.Icc (-1 : ℝ) 1) := by
  unfold Rabs
  apply Real.continuous_sqrt.comp_continuousOn
  exact (continuous_const.continuousOn).add ((continuous_const.continuousOn).mul
    continuousOn_id)

/-- fUpper は [-1, 1] で連続。 -/
private lemma fUpper_continuousOn :
    ContinuousOn fUpper (Set.Icc (-1 : ℝ) 1) := by
  unfold fUpper sinTheta
  apply ContinuousOn.div
  · -- 分子
    apply ContinuousOn.mul continuous_sqrt_one_sub_sq
    apply ContinuousOn.sub
    · exact continuousOn_const.mul ((continuousOn_id.add
        continuousOn_const).pow 2)
    · exact continuous_sqrt_one_sub_sq.pow 2
  · exact continuous_Rabs_aux.pow 3
  · intro x hx
    have hx_sq : x ^ 2 ≤ 1 := by
      rcases hx with ⟨h1, h2⟩
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
    exact (pow_pos (Rabs_pos (onCircle_upper hx_sq)) 3).ne'

/-- fLower は [-1, 1] で連続。 -/
private lemma fLower_continuousOn :
    ContinuousOn fLower (Set.Icc (-1 : ℝ) 1) := by
  unfold fLower sinTheta
  apply ContinuousOn.div
  · apply ContinuousOn.mul continuous_sqrt_one_sub_sq.neg
    apply ContinuousOn.sub
    · exact continuousOn_const.mul ((continuousOn_id.add
        continuousOn_const).pow 2)
    · exact continuous_sqrt_one_sub_sq.neg.pow 2
  · -- Rabs(x, -sqrt(...)) = Rabs(x, sqrt(...)) (depends only on x.1)
    have h_eq : (fun x : ℝ => (Rabs (x, -sqrt (1 - x ^ 2))) ^ 3) =
                (fun x : ℝ => (Rabs (x, sqrt (1 - x ^ 2))) ^ 3) := by
      funext x; rfl
    rw [h_eq]; exact continuous_Rabs_aux.pow 3
  · intro x hx
    have hx_sq : x ^ 2 ≤ 1 := by
      rcases hx with ⟨h1, h2⟩
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
    exact (pow_pos (Rabs_pos (onCircle_lower hx_sq)) 3).ne'

/-! ### 中間値の定理を用いた逆方向 -/

/-- s ∈ [0, 23/27] のとき sinTheta z = s となる z が存在。 -/
private lemma exists_z_pos {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 23/27) :
    ∃ z, OnCircle z ∧ sinTheta z = s := by
  have hcont : ContinuousOn fUpper (Set.Icc (-1 : ℝ) (-1/3)) :=
    fUpper_continuousOn.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
  have h_le : (-1 : ℝ) ≤ -1/3 := by norm_num
  have h_endpts := intermediate_value_Icc h_le hcont
  rw [fUpper_neg_one, fUpper_neg_third] at h_endpts
  obtain ⟨x, hx_mem, hx_eq⟩ := h_endpts ⟨h0, h1⟩
  refine ⟨(x, sqrt (1 - x ^ 2)), ?_, hx_eq⟩
  apply onCircle_upper
  rcases hx_mem with ⟨ha, hb⟩
  nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]

/-- s ∈ [−23/27, 0] のとき sinTheta z = s となる z が存在。 -/
private lemma exists_z_neg {s : ℝ} (h0 : -(23/27) ≤ s) (h1 : s ≤ 0) :
    ∃ z, OnCircle z ∧ sinTheta z = s := by
  have hcont : ContinuousOn fLower (Set.Icc (-1 : ℝ) (-1/3)) :=
    fLower_continuousOn.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
  have h_le : (-1 : ℝ) ≤ -1/3 := by norm_num
  -- fLower は単調減少 (−1 で 0, −1/3 で −23/27) なので intermediate_value_Icc' を使う
  have h_endpts := intermediate_value_Icc' h_le hcont
  rw [fLower_neg_one, fLower_neg_third] at h_endpts
  obtain ⟨x, hx_mem, hx_eq⟩ := h_endpts ⟨h0, h1⟩
  refine ⟨(x, -sqrt (1 - x ^ 2)), ?_, hx_eq⟩
  apply onCircle_lower
  rcases hx_mem with ⟨ha, hb⟩
  nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]

/-! ### (1) 主結果 -/

/-- (1) sin θ の取り得る値の集合。 -/
def SinThetaSet : Set ℝ := { s | ∃ z, OnCircle z ∧ s = sinTheta z }

/-- (1) sin θ の値域は [−23/27, 23/27]。 -/
theorem sinTheta_range : SinThetaSet = Set.Icc (-(23/27)) (23/27) := by
  ext s
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hOC, rfl⟩
    exact ⟨sinTheta_ge hOC, sinTheta_le hOC⟩
  · intro hs
    by_cases h0 : 0 ≤ s
    · obtain ⟨z, hOC, hs_eq⟩ := exists_z_pos h0 hs.2
      exact ⟨z, hOC, hs_eq.symm⟩
    · have h0' : s ≤ 0 := (lt_of_not_ge h0).le
      obtain ⟨z, hOC, hs_eq⟩ := exists_z_neg hs.1 h0'
      exact ⟨z, hOC, hs_eq.symm⟩

/-! ## (2) D が実軸の正・負の両部分と共有点を持つ α の範囲

  本セクションでは IsGoodAlpha 述語を定義し、構造的補題を示す。
  単位開円板内 (|α| < 1) は条件を満たす。
  完全な面積 4√3 の証明は積分計算 (∫ r arcsin(1/r) dr) を要するため
  本ファイルでは扱わない (冒頭 docstring に方針を記述)。 -/

/-- 複素数 (Re z, Im z) の 3 乗を (Re, Im) で表したもの。 -/
def cube (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 ^ 3 - 3 * z.1 * z.2 ^ 2, 3 * z.1 ^ 2 * z.2 - z.2 ^ 3)

/-- D が実軸の正の部分と共有点を持つ。 -/
def MeetsPos (α : ℝ × ℝ) : Prop :=
  ∃ z, OnCircle z ∧
    (cube (z.1 - α.1, z.2 - α.2)).2 = 0 ∧ 0 < (cube (z.1 - α.1, z.2 - α.2)).1

/-- D が実軸の負の部分と共有点を持つ。 -/
def MeetsNeg (α : ℝ × ℝ) : Prop :=
  ∃ z, OnCircle z ∧
    (cube (z.1 - α.1, z.2 - α.2)).2 = 0 ∧ (cube (z.1 - α.1, z.2 - α.2)).1 < 0

/-- (2) の条件: D が実軸の正と負の両方と共有点を持つ。 -/
def IsGoodAlpha (α : ℝ × ℝ) : Prop := MeetsPos α ∧ MeetsNeg α

/-- 良い α の集合。 -/
def GoodSet : Set (ℝ × ℝ) := { α | IsGoodAlpha α }

/-! ### 単位開円板は良い α の集合に含まれる -/

/-- α が単位開円板 (|α|² < 1) 内なら IsGoodAlpha α が成り立つ。
    z = (±√(1 − α.2²), α.2) を取れば z は単位円上で、
    z − α は実軸上にあり (虚部 0)、
    Re((z − α)³) は実軸上の値で正/負を切り替えられる。 -/
theorem isGoodAlpha_of_inside {α : ℝ × ℝ} (h : α.1 ^ 2 + α.2 ^ 2 < 1) :
    IsGoodAlpha α := by
  have hα2_lt : α.2 ^ 2 < 1 := by linarith [sq_nonneg α.1]
  have hs_sq_eq : (sqrt (1 - α.2 ^ 2)) ^ 2 = 1 - α.2 ^ 2 :=
    sq_sqrt (by linarith : (0:ℝ) ≤ 1 - α.2 ^ 2)
  have hs_pos : 0 < sqrt (1 - α.2 ^ 2) := sqrt_pos.mpr (by linarith)
  -- α.1 < √(1 − α.2²) と −√(1 − α.2²) < α.1 を示す。
  have hα1_sq_lt : α.1 ^ 2 < (sqrt (1 - α.2 ^ 2)) ^ 2 := by rw [hs_sq_eq]; linarith
  have hα1_lt : α.1 < sqrt (1 - α.2 ^ 2) := by
    by_cases hα : 0 ≤ α.1
    · nlinarith [hs_pos, hα1_sq_lt]
    · linarith [hs_pos]
  have hα1_gt : -sqrt (1 - α.2 ^ 2) < α.1 := by
    by_cases hα : α.1 ≤ 0
    · nlinarith [hs_pos, hα1_sq_lt]
    · linarith [hs_pos]
  refine ⟨?_, ?_⟩
  · -- MeetsPos: z = (√(1−α.2²), α.2)
    refine ⟨(sqrt (1 - α.2 ^ 2), α.2), ?_, ?_, ?_⟩
    · show (sqrt (1 - α.2 ^ 2)) ^ 2 + α.2 ^ 2 = 1
      rw [hs_sq_eq]; ring
    · show (cube (sqrt (1 - α.2 ^ 2) - α.1, α.2 - α.2)).2 = 0
      unfold cube
      show 3 * (sqrt (1 - α.2 ^ 2) - α.1) ^ 2 * (α.2 - α.2) - (α.2 - α.2) ^ 3 = 0
      ring
    · show 0 < (cube (sqrt (1 - α.2 ^ 2) - α.1, α.2 - α.2)).1
      unfold cube
      show 0 < (sqrt (1 - α.2 ^ 2) - α.1) ^ 3
        - 3 * (sqrt (1 - α.2 ^ 2) - α.1) * (α.2 - α.2) ^ 2
      have h_simp : (sqrt (1 - α.2 ^ 2) - α.1) ^ 3
        - 3 * (sqrt (1 - α.2 ^ 2) - α.1) * (α.2 - α.2) ^ 2
        = (sqrt (1 - α.2 ^ 2) - α.1) ^ 3 := by ring
      rw [h_simp]
      exact pow_pos (by linarith) 3
  · -- MeetsNeg: z = (−√(1−α.2²), α.2)
    refine ⟨(-sqrt (1 - α.2 ^ 2), α.2), ?_, ?_, ?_⟩
    · show (-sqrt (1 - α.2 ^ 2)) ^ 2 + α.2 ^ 2 = 1
      have h1 : (-sqrt (1 - α.2 ^ 2)) ^ 2 = (sqrt (1 - α.2 ^ 2)) ^ 2 := by ring
      rw [h1, hs_sq_eq]; ring
    · show (cube (-sqrt (1 - α.2 ^ 2) - α.1, α.2 - α.2)).2 = 0
      unfold cube
      show 3 * (-sqrt (1 - α.2 ^ 2) - α.1) ^ 2 * (α.2 - α.2) - (α.2 - α.2) ^ 3 = 0
      ring
    · show (cube (-sqrt (1 - α.2 ^ 2) - α.1, α.2 - α.2)).1 < 0
      unfold cube
      show (-sqrt (1 - α.2 ^ 2) - α.1) ^ 3
        - 3 * (-sqrt (1 - α.2 ^ 2) - α.1) * (α.2 - α.2) ^ 2 < 0
      have h_simp : (-sqrt (1 - α.2 ^ 2) - α.1) ^ 3
        - 3 * (-sqrt (1 - α.2 ^ 2) - α.1) * (α.2 - α.2) ^ 2
        = -(sqrt (1 - α.2 ^ 2) + α.1) ^ 3 := by ring
      rw [h_simp]
      have h_pos3 : 0 < (sqrt (1 - α.2 ^ 2) + α.1) ^ 3 := pow_pos (by linarith) 3
      linarith

/-- 単位開円板は GoodSet に含まれる。 -/
theorem openDisk_subset_GoodSet :
    { α : ℝ × ℝ | α.1 ^ 2 + α.2 ^ 2 < 1 } ⊆ GoodSet :=
  fun _ h => isGoodAlpha_of_inside h

end Common2026.T_Q5
