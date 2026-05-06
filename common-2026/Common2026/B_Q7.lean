/-
2B 第7問 (複素数平面)

  z を 0 でない複素数とし、w = z + 1/z とする。また、r を正の実数とし、
  複素数平面上で原点 O を中心とする半径 r の円を C とする。

  (1) z = √3 + i のとき
        |z| = 2,
        w = (5√3)/4 + (3/4) i.
      空欄: ア = 2, イ = 5, ウ = 3, エ = 4, オ = 3, カ = 4。

  (2) z = r(cosθ + i sinθ) と表すと
        w = (r + 1/r) cosθ + i (r − 1/r) sinθ.
      空欄キ = ⑥ (r + 1/r)cosθ, 空欄ク = ⑨ (r − 1/r)sinθ。

      (i) θ によらず Im(w) = 0 となるのは r = 1 のとき。空欄ケ = 1。

      (ii) r = 1 のとき: w = 2 cosθ ∈ [−2, 2] (実軸上の線分)。空欄コ = ① −2 ≤ x ≤ 2。

      (iii) r ≠ 1 のとき: x = (r+1/r)cosθ, y = (r−1/r)sinθ より
        x²/(r+1/r)² + y²/(r−1/r)² = 1 (楕円)。
        空欄サ = ② x²/(r+1/r)² + y²/(r−1/r)² = 1。

  (3) (i) w² = z² + 1/z² + 2。空欄シ = ③。

      (ii) z² の絶対値は r²。z² + 1/z² = X + iY とおくと
        X²/(r²+1/r²)² + Y²/(r²−1/r²)² = 1 (楕円)。
        空欄ス = ② x²/(r²+1/r²)² + y²/(r²−1/r²)² = 1。
        w² = (X + 2) + iY なので、軌跡は中心 (2, 0) の楕円 (空欄セ = 図形選択)。

  本ファイルでは図形選択 (コ, セ) は形式化対象外として上記 docstring に
  記述するに留め、形式化可能な代数恒等式・絶対値計算のみを theorem として定義する。
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Common2026.B_Q7

open Complex

/-! ## (1) z = √3 + i での具体計算 -/

/-- 補題: (√3)*(√3) = 3。 -/
private lemma sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 := by
  rw [← sq]; exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)

/-- z = √3 + i の絶対値の2乗は 4。 -/
theorem normSq_specific :
    Complex.normSq (Real.sqrt 3 + Complex.I) = 4 := by
  rw [Complex.normSq_apply]
  have h_re : ((Real.sqrt 3 : ℂ) + Complex.I).re = Real.sqrt 3 := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.I_re]; ring
  have h_im : ((Real.sqrt 3 : ℂ) + Complex.I).im = 1 := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.I_im]; ring
  rw [h_re, h_im, sqrt3_mul_self]
  norm_num

/-- |√3 + i| = 2。 -/
theorem norm_specific : ‖((Real.sqrt 3 : ℂ) + Complex.I)‖ = 2 := by
  rw [Complex.norm_def, normSq_specific]
  rw [show (4:ℝ) = 2^2 by norm_num]
  exact Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)

/-- z = √3 + i は 0 でない。 -/
private lemma z_ne_zero : ((Real.sqrt 3 : ℂ) + Complex.I) ≠ 0 := by
  intro h
  have h2 : Complex.normSq ((Real.sqrt 3 : ℂ) + Complex.I) = 0 := by
    rw [Complex.normSq_eq_zero]; exact h
  rw [normSq_specific] at h2
  norm_num at h2

/-- z = √3 + i の逆数の実部は √3 / 4。 -/
theorem inv_re_specific :
    ((Real.sqrt 3 : ℂ) + Complex.I)⁻¹.re = Real.sqrt 3 / 4 := by
  rw [Complex.inv_re, normSq_specific]
  rw [Complex.add_re, Complex.ofReal_re, Complex.I_re]
  ring

/-- z = √3 + i の逆数の虚部は -1/4。 -/
theorem inv_im_specific :
    ((Real.sqrt 3 : ℂ) + Complex.I)⁻¹.im = -(1 / 4) := by
  rw [Complex.inv_im, normSq_specific]
  rw [Complex.add_im, Complex.ofReal_im, Complex.I_im]
  ring

/-- w = z + 1/z の実部 (z = √3 + i のとき) は 5√3/4。 -/
theorem w_re_specific :
    (((Real.sqrt 3 : ℂ) + Complex.I) + ((Real.sqrt 3 : ℂ) + Complex.I)⁻¹).re
      = 5 * Real.sqrt 3 / 4 := by
  rw [Complex.add_re, inv_re_specific, Complex.add_re, Complex.ofReal_re, Complex.I_re]
  ring

/-- w = z + 1/z の虚部 (z = √3 + i のとき) は 3/4。 -/
theorem w_im_specific :
    (((Real.sqrt 3 : ℂ) + Complex.I) + ((Real.sqrt 3 : ℂ) + Complex.I)⁻¹).im
      = 3 / 4 := by
  rw [Complex.add_im, inv_im_specific, Complex.add_im, Complex.ofReal_im, Complex.I_im]
  ring

/-- w = z + 1/z は (5√3/4) + (3/4) i (z = √3 + i のとき)。 -/
theorem w_specific :
    ((Real.sqrt 3 : ℂ) + Complex.I) + ((Real.sqrt 3 : ℂ) + Complex.I)⁻¹
      = ((5 * Real.sqrt 3 / 4 : ℝ) : ℂ) + ((3 / 4 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [w_re_specific, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · rw [w_im_specific, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

/-! ## (2) 一般 z = r(cosθ + i sinθ) での w の表示

  この問題では z の偏角 θ を用いた極形式から
    Re(w) = (r + 1/r) cosθ,
    Im(w) = (r − 1/r) sinθ
  となる。ここでは z を実数 c = cosθ, s = sinθ で展開し、
  c² + s² = 1 のもとで成り立つ恒等式として証明する。
-/

/-- 補助: (c + s i).re = c。 -/
private lemma re_inner (c s : ℝ) :
    ((c : ℂ) + (s : ℂ) * Complex.I).re = c := by
  rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  ring

/-- 補助: (c + s i).im = s。 -/
private lemma im_inner (c s : ℝ) :
    ((c : ℂ) + (s : ℂ) * Complex.I).im = s := by
  rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  ring

/-- 補助補題: z = r * (c + s * i) (c, s, r 実) の正規化二乗。
    c² + s² = 1 のとき normSq z = r²。 -/
private lemma normSq_polar (r c s : ℝ) (hcs : c^2 + s^2 = 1) :
    Complex.normSq ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)) = r^2 := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_apply,
      re_inner, im_inner]
  nlinarith [hcs]

/-- z = r(c + s i) の実部 = r * c。 -/
private lemma re_polar (r c s : ℝ) :
    ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)).re = r * c := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, re_inner, im_inner]
  ring

/-- z = r(c + s i) の虚部 = r * s。 -/
private lemma im_polar (r c s : ℝ) :
    ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)).im = r * s := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, re_inner, im_inner]
  ring

/-- z = r(c + s i) の逆数の実部 (c² + s² = 1, r > 0)。 -/
theorem inv_re_polar (r c s : ℝ) (hr : 0 < r) (hcs : c^2 + s^2 = 1) :
    ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I))⁻¹.re = (1 / r) * c := by
  rw [Complex.inv_re, normSq_polar r c s hcs, re_polar]
  have hr2 : (r : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  field_simp

/-- z = r(c + s i) の逆数の虚部 (c² + s² = 1, r > 0)。 -/
theorem inv_im_polar (r c s : ℝ) (hr : 0 < r) (hcs : c^2 + s^2 = 1) :
    ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I))⁻¹.im = -((1 / r) * s) := by
  rw [Complex.inv_im, normSq_polar r c s hcs, im_polar]
  have hr2 : (r : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  field_simp

/-- w = z + 1/z の実部 = (r + 1/r) c (c² + s² = 1, r > 0)。 -/
theorem w_re_polar (r c s : ℝ) (hr : 0 < r) (hcs : c^2 + s^2 = 1) :
    (let z : ℂ := (r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)
     z + z⁻¹).re = (r + 1/r) * c := by
  show ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)
        + ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I))⁻¹).re = _
  rw [Complex.add_re, re_polar, inv_re_polar r c s hr hcs]
  ring

/-- w = z + 1/z の虚部 = (r − 1/r) s (c² + s² = 1, r > 0)。 -/
theorem w_im_polar (r c s : ℝ) (hr : 0 < r) (hcs : c^2 + s^2 = 1) :
    (let z : ℂ := (r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)
     z + z⁻¹).im = (r - 1/r) * s := by
  show ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I)
        + ((r : ℂ) * ((c : ℂ) + (s : ℂ) * Complex.I))⁻¹).im = _
  rw [Complex.add_im, im_polar, inv_im_polar r c s hr hcs]
  ring

/-! ## (2)(i) Im(w) が θ によらず 0 となるのは r = 1 のとき -/

/-- (r − 1/r) sinθ が任意の θ で 0 ⇔ r = 1 (r > 0)。 -/
theorem im_zero_iff_r_eq_one (r : ℝ) (hr : 0 < r) :
    (∀ θ : ℝ, (r - 1/r) * Real.sin θ = 0) ↔ r = 1 := by
  constructor
  · intro h
    have hpi := h (Real.pi / 2)
    rw [Real.sin_pi_div_two] at hpi
    -- (r − 1/r) * 1 = 0 ⇒ r − 1/r = 0
    have h1 : r - 1/r = 0 := by linarith
    have hne : r ≠ 0 := ne_of_gt hr
    have hrr : r * r = 1 := by
      field_simp at h1
      linarith
    -- r * r = 1, r > 0 ⇒ r = 1
    nlinarith [sq_nonneg (r - 1), hrr, hr]
  · intro h θ
    rw [h]; ring

/-! ## (2)(iii) r ≠ 1 (r > 0) のときの楕円方程式 -/

/-- 楕円方程式: x = (r + 1/r) cosθ, y = (r − 1/r) sinθ ならば
    x²/(r + 1/r)² + y²/(r − 1/r)² = 1。
    一般に c² + s² = 1 を満たす c, s について成り立つ恒等式として証明。 -/
theorem ellipse_eq (r c s : ℝ) (hcs : c^2 + s^2 = 1)
    (h_plus : r + 1/r ≠ 0) (h_minus : r - 1/r ≠ 0) :
    ((r + 1/r) * c)^2 / (r + 1/r)^2 + ((r - 1/r) * s)^2 / (r - 1/r)^2 = 1 := by
  have hp2 : (r + 1/r)^2 ≠ 0 := pow_ne_zero _ h_plus
  have hm2 : (r - 1/r)^2 ≠ 0 := pow_ne_zero _ h_minus
  have e1 : ((r + 1/r) * c)^2 / (r + 1/r)^2 = c^2 := by
    rw [mul_pow, mul_comm ((r + 1/r)^2) (c^2), mul_div_assoc, div_self hp2, mul_one]
  have e2 : ((r - 1/r) * s)^2 / (r - 1/r)^2 = s^2 := by
    rw [mul_pow, mul_comm ((r - 1/r)^2) (s^2), mul_div_assoc, div_self hm2, mul_one]
  rw [e1, e2]; linarith [hcs]

/-- r > 0 ⇒ r + 1/r > 0、特に ≠ 0。 -/
theorem r_plus_inv_ne_zero (r : ℝ) (hr : 0 < r) : r + 1/r ≠ 0 := by
  have h1 : 0 < 1/r := by positivity
  linarith

/-- r > 0, r ≠ 1 ⇒ r − 1/r ≠ 0。 -/
theorem r_minus_inv_ne_zero (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) : r - 1/r ≠ 0 := by
  intro h
  have hne : r ≠ 0 := ne_of_gt hr
  field_simp at h
  -- h : r^2 - 1 = 0
  have hrr : r * r = 1 := by linarith
  have : (r - 1) * (r + 1) = 0 := by nlinarith [hrr]
  rcases mul_eq_zero.mp this with h | h
  · exact hr1 (by linarith)
  · linarith

/-! ## (3) w² の展開 -/

/-- w² = z² + 1/z² + 2 (z ≠ 0)。 -/
theorem w_sq_decomp (z : ℂ) (hz : z ≠ 0) :
    (z + z⁻¹)^2 = z^2 + (z⁻¹)^2 + 2 := by
  field_simp
  ring

/-! ## (3)(ii) z² + 1/z² の楕円方程式 (実数版)

    z² の絶対値が r² なので、z² = r²(cos(2θ) + i sin(2θ)) と表される。
    そこから z² + 1/z² の実部 X と虚部 Y は、(2) と同じ形の楕円方程式
      X²/(r² + 1/r²)² + Y²/(r² − 1/r²)² = 1
    を満たす。これは ellipse_eq の r を r² に置き換えた式である。 -/

/-- (3)(ii) の楕円方程式: パラメトリック形式 X = (s + 1/s) c', Y = (s − 1/s) s',
    c'² + s'² = 1 ならば X²/(s + 1/s)² + Y²/(s − 1/s)² = 1。
    s := r², c' := cos(2θ), s' := sin(2θ) と置けば設問の主張になる。 -/
theorem ellipse_eq_sq (s c' s' : ℝ) (hcs : c'^2 + s'^2 = 1)
    (h_plus : s + 1/s ≠ 0) (h_minus : s - 1/s ≠ 0) :
    ((s + 1/s) * c')^2 / (s + 1/s)^2 + ((s - 1/s) * s')^2 / (s - 1/s)^2 = 1 :=
  ellipse_eq s c' s' hcs h_plus h_minus

end Common2026.B_Q7
