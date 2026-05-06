/-
東大 2026 第3問 (2)

  (2) 線分 PQ が通過する範囲を xy 平面上に図示せよ。

  答え: A = (x, y) について、A が通過範囲内にあることは
    x² + y² ≤ 25  かつ  5(x − 3)² − 4y² ≤ 20  かつ  (x, y) ≠ (5, 0)
  と同値。すなわち、半径 5 の閉円板と、焦点 O(0, 0), F(6, 0)、頂点 (1, 0), (5, 0) の
  双曲線 (x − 3)²/4 − y²/5 = 1 の左枝を含む側との共通部分から (5, 0) を除いた集合。

  方針:
    A が線分 PQ 上 (M を中点とする) ⇔ A · M = |M|² かつ |OA| ≤ 5。
    |M|² = 6m − 5 (M 軌跡円の式から) なので、A · M = |M|² は線形条件
      (6 − x) m − y n = 5
    に書き換わる。これと小円 (m − 3)² + n² = 4 が交点を持つ条件は
    Cauchy–Schwarz より 5(x − 3)² − 4y² ≤ 20。

    また x = 5 が線形方程式の唯一解 (5, 0) と整合するのは A = (5, 0) のときに限り、
    そのとき P = Q = (5, 0) となり P ≠ Q に反するため (5, 0) は除く。
-/

import Common2026.T_Q3_1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.T_Q3_2

open Common2026.T_Q3_1

/-- A が線分 PQ (xy 平面上の) 上にあること: A = (1 − t) P + t Q, t ∈ [0, 1]。 -/
def OnSegment (A : ℝ × ℝ) (cfg : Config) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    A.1 = (1 - t) * cfg.P.1 + t * cfg.Q.1 ∧
    A.2 = (1 - t) * cfg.P.2 + t * cfg.Q.2

/-- 通過範囲の特徴付け: 円板 ∩ 双曲線内側 ∖ {(5, 0)}。 -/
def SweptRange (A : ℝ × ℝ) : Prop :=
  A.1 ^ 2 + A.2 ^ 2 ≤ 25 ∧
  5 * (A.1 - 3) ^ 2 - 4 * A.2 ^ 2 ≤ 20 ∧
  A ≠ (5, 0)

/-! ### 順方向: A が線分上 ⇒ SweptRange -/

/-- |P − Q|² ≥ 0 と球面条件から P · Q ≤ 25。 -/
private lemma dot_le_of_sphere (cfg : Config) :
    cfg.P.1 * cfg.Q.1 + cfg.P.2 * cfg.Q.2 ≤ 25 := by
  nlinarith [cfg.hP, cfg.hQ, sq_nonneg (cfg.P.1 - cfg.Q.1), sq_nonneg (cfg.P.2 - cfg.Q.2)]

/-- A が線分 PQ 上なら |OA|² ≤ 25 (円板内)。 -/
private lemma disk_of_segment (A : ℝ × ℝ) (cfg : Config)
    (hA : OnSegment A cfg) : A.1 ^ 2 + A.2 ^ 2 ≤ 25 := by
  obtain ⟨t, ht0, ht1, hAx, hAy⟩ := hA
  rw [hAx, hAy]
  have hPQ_dot := dot_le_of_sphere cfg
  have ht_mul : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  nlinarith [cfg.hP, cfg.hQ, hPQ_dot, ht_mul, sq_nonneg t, sq_nonneg (1 - t)]

/-- 中点を取り出す。 -/
private noncomputable def midpointOf (cfg : Config) : ℝ × ℝ :=
  ((cfg.P.1 + cfg.Q.1) / 2, (cfg.P.2 + cfg.Q.2) / 2)

private lemma midpointOf_fst (cfg : Config) :
    (midpointOf cfg).1 = (cfg.P.1 + cfg.Q.1) / 2 := rfl

private lemma midpointOf_snd (cfg : Config) :
    (midpointOf cfg).2 = (cfg.P.2 + cfg.Q.2) / 2 := rfl

private lemma midpoint_isMidpoint (cfg : Config) :
    IsMidpoint (midpointOf cfg) cfg := by
  unfold IsMidpoint midpointOf
  refine ⟨?_, ?_⟩ <;> ring

/-- 中点 M は (m − 3)² + n² = 4 を満たす。 -/
private lemma midpoint_on_circle (cfg : Config) :
    ((midpointOf cfg).1 - 3) ^ 2 + (midpointOf cfg).2 ^ 2 = 4 := by
  -- circle_eq_of_config は private なので Q3_1 の locus_iff を介する代わりに再導出する。
  -- 直接 Config の重心条件と球面条件から計算。
  unfold midpointOf
  have hRx : cfg.R.1 = 6 - (cfg.P.1 + cfg.Q.1) := by linarith [cfg.hG_x]
  have hRy : cfg.R.2.1 = -(cfg.P.2 + cfg.Q.2) := by linarith [cfg.hG_y]
  have hRz : cfg.R.2.2 = 3 := cfg.hG_z
  have hRsphere : cfg.R.1 ^ 2 + cfg.R.2.1 ^ 2 + cfg.R.2.2 ^ 2 = 25 := cfg.hR
  rw [hRx, hRy, hRz] at hRsphere
  nlinarith [hRsphere]

/-- A が線分 PQ 上なら A · M = M · M。 -/
private lemma dot_eq_of_segment (A : ℝ × ℝ) (cfg : Config)
    (hA : OnSegment A cfg) :
    A.1 * (midpointOf cfg).1 + A.2 * (midpointOf cfg).2 =
      (midpointOf cfg).1 ^ 2 + (midpointOf cfg).2 ^ 2 := by
  obtain ⟨t, _, _, hAx, hAy⟩ := hA
  unfold midpointOf
  rw [hAx, hAy]
  -- A · M − M · M = (A − M) · M = (1/2 − t)(P − Q) · (P + Q)/2
  --                                 = (1/2 − t)(|P|² − |Q|²)/2 = 0
  have hP : cfg.P.1 ^ 2 + cfg.P.2 ^ 2 = 25 := cfg.hP
  have hQ : cfg.Q.1 ^ 2 + cfg.Q.2 ^ 2 = 25 := cfg.hQ
  nlinarith [hP, hQ]

/-- A が線分 PQ 上なら 5(x − 3)² − 4y² ≤ 20。 -/
private lemma hyperbola_of_segment (A : ℝ × ℝ) (cfg : Config)
    (hA : OnSegment A cfg) :
    5 * (A.1 - 3) ^ 2 - 4 * A.2 ^ 2 ≤ 20 := by
  set M := midpointOf cfg with hM
  have hCircle : (M.1 - 3) ^ 2 + M.2 ^ 2 = 4 := midpoint_on_circle cfg
  have hDot : A.1 * M.1 + A.2 * M.2 = M.1 ^ 2 + M.2 ^ 2 :=
    dot_eq_of_segment A cfg hA
  -- |M|² = 6 M.1 − 5 (from hCircle)
  have hMsq : M.1 ^ 2 + M.2 ^ 2 = 6 * M.1 - 5 := by nlinarith [hCircle]
  -- 線形条件: (6 − x) M.1 − y M.2 = 5
  have hLin : (6 - A.1) * M.1 - A.2 * M.2 = 5 := by
    have : A.1 * M.1 + A.2 * M.2 = 6 * M.1 - 5 := by rw [hDot, hMsq]
    linarith
  -- a = M.1 − 3, b = M.2 として a² + b² = 4, (6 − x)a − yb = 3x − 13 を得る
  set a := M.1 - 3 with ha_def
  set b := M.2 with hb_def
  have hab : a ^ 2 + b ^ 2 = 4 := by show (M.1 - 3)^2 + M.2^2 = 4; exact hCircle
  have hLin' : (6 - A.1) * a - A.2 * b = 3 * A.1 - 13 := by
    have h1 : M.1 = a + 3 := by show M.1 = (M.1 - 3) + 3; ring
    rw [h1] at hLin
    linarith
  -- Cauchy–Schwarz: ((6 − x)a − y b)² ≤ ((6 − x)² + y²)(a² + b²)
  have hCS : ((6 - A.1) * a - A.2 * b) ^ 2 ≤
      ((6 - A.1) ^ 2 + A.2 ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg ((6 - A.1) * b + A.2 * a)]
  rw [hLin', hab] at hCS
  -- (3x − 13)² ≤ 4((6 − x)² + y²)
  nlinarith [hCS]

/-- A が線分 PQ 上なら A ≠ (5, 0)。
    A = (5, 0) なら |A| = 5、よって A は端点 (P または Q) でなければならず、
    その対応する中点 M は小円上だが結局 P = Q となり矛盾。 -/
private lemma ne_five_zero_of_segment (A : ℝ × ℝ) (cfg : Config)
    (hA : OnSegment A cfg) : A ≠ (5, 0) := by
  intro hA_eq
  have hA1 : A.1 = 5 := congrArg Prod.fst hA_eq
  have hA2 : A.2 = 0 := congrArg Prod.snd hA_eq
  obtain ⟨t, ht0, ht1, hAx, hAy⟩ := hA
  -- A = (5, 0), |A|² = 25, A on segment ⇒ t = 0 or t = 1
  -- t = 0: A = P ⇒ P = (5, 0)
  -- t = 1: A = Q ⇒ Q = (5, 0)
  -- 中点 M も小円上、よって他方の点も (5, 0)、つまり P = Q で矛盾。
  --
  -- 直接: 上の hyperbola_of_segment を A = (5, 0) に適用すると
  --   5 * (5 − 3)² − 4 · 0² = 20  ⇒ 等号成立。
  -- 等号成立の場合は、Cauchy–Schwarz の等号条件から M = (5, 0)。
  -- すると |M| = 5、|P − M| = √(25 − 25) = 0、よって P = Q = M = (5, 0)。
  -- これは cfg.hPQ に矛盾。
  --
  -- 形式化: M.1 = 5, M.2 = 0 を導く。
  set M := midpointOf cfg with hM
  have hCircle : (M.1 - 3) ^ 2 + M.2 ^ 2 = 4 := midpoint_on_circle cfg
  have hDot : A.1 * M.1 + A.2 * M.2 = M.1 ^ 2 + M.2 ^ 2 :=
    dot_eq_of_segment A cfg ⟨t, ht0, ht1, hAx, hAy⟩
  have hDisk : A.1 ^ 2 + A.2 ^ 2 ≤ 25 :=
    disk_of_segment A cfg ⟨t, ht0, ht1, hAx, hAy⟩
  -- A = (5, 0) を代入: 5 * M.1 = M.1² + M.2² = 6 M.1 − 5
  -- ⇒ M.1 = 5
  rw [hA1, hA2] at hDot
  have hMsq : M.1 ^ 2 + M.2 ^ 2 = 6 * M.1 - 5 := by nlinarith [hCircle]
  have hM1_eq : M.1 = 5 := by linarith [hDot, hMsq]
  have hM2_eq : M.2 = 0 := by
    have h1 : (M.1 - 3) ^ 2 = 4 := by rw [hM1_eq]; ring
    have h2 : M.2 ^ 2 = 0 := by linarith [hCircle]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  -- ここで M = (5, 0)。M は中点なので P + Q = (10, 0)。
  -- |P|, |Q| ≤ 5 ⇒ P = Q = (5, 0)、cfg.hPQ に矛盾。
  rw [midpointOf_fst] at hM1_eq
  rw [midpointOf_snd] at hM2_eq
  have hPQ_x : cfg.P.1 + cfg.Q.1 = 10 := by linarith [hM1_eq]
  have hPQ_y : cfg.P.2 + cfg.Q.2 = 0 := by linarith [hM2_eq]
  have hP1ub : cfg.P.1 ≤ 5 := by
    nlinarith [cfg.hP, sq_nonneg cfg.P.2, sq_nonneg (cfg.P.1 - 5)]
  have hQ1ub : cfg.Q.1 ≤ 5 := by
    nlinarith [cfg.hQ, sq_nonneg cfg.Q.2, sq_nonneg (cfg.Q.1 - 5)]
  have hP1eq : cfg.P.1 = 5 := by linarith
  have hQ1eq : cfg.Q.1 = 5 := by linarith
  have hP2 : cfg.P.2 = 0 := by
    have : cfg.P.2 ^ 2 = 0 := by nlinarith [cfg.hP, hP1eq]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp this
  have hQ2 : cfg.Q.2 = 0 := by
    have : cfg.Q.2 ^ 2 = 0 := by nlinarith [cfg.hQ, hQ1eq]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp this
  apply cfg.hPQ
  apply Prod.ext
  · rw [hP1eq, hQ1eq]
  · rw [hP2, hQ2]

/-! ### 順方向の主結果 -/

private lemma forward (A : ℝ × ℝ) (h : ∃ cfg, OnSegment A cfg) : SweptRange A := by
  obtain ⟨cfg, hA⟩ := h
  exact ⟨disk_of_segment A cfg hA, hyperbola_of_segment A cfg hA,
    ne_five_zero_of_segment A cfg hA⟩

/-! ### 逆方向: SweptRange A ⇒ ∃ cfg, OnSegment A cfg

  A = (x, y) から M = (m, n) を構成する。線形条件 (6−x)m − yn = 5 と
  小円 (m−3)² + n² = 4 の交点を陽に取り、Q3_1 の mkLocusConfig で Config を作る。
  最後に t を陽に書き下し、A が線分 PQ 上にあることを示す。 -/

/-- A が SweptRange を満たすとき x ≠ 5。 -/
private lemma x_ne_five {x y : ℝ} (h : SweptRange (x, y)) : x ≠ 5 := by
  intro hx
  apply h.2.2
  apply Prod.ext
  · exact hx
  · -- y² ≤ 0 from disk
    show (x, y).2 = ((5 : ℝ), (0 : ℝ)).2
    have : y ^ 2 = 0 := by nlinarith [h.1, hx, sq_nonneg y]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp this

/-- D := (6−x)² + y² > 0 (A の disk 条件 ⇒ A ≠ (6, 0))。 -/
private lemma D_pos {x y : ℝ} (hDisk : x ^ 2 + y ^ 2 ≤ 25) :
    (0 : ℝ) < (6 - x) ^ 2 + y ^ 2 := by
  -- 等号成立は (6-x)² = 0 かつ y = 0、つまり x = 6, y = 0、しかし x² + y² = 36 > 25
  have h_nn : (0 : ℝ) ≤ (6 - x) ^ 2 + y ^ 2 := by positivity
  rcases lt_or_eq_of_le h_nn with hlt | heq
  · exact hlt
  · exfalso
    have h_sq_x : (6 - x) ^ 2 = 0 := by nlinarith [sq_nonneg y, heq.symm]
    have h_sq_y : y ^ 2 = 0 := by nlinarith [sq_nonneg (6 - x), heq.symm]
    have hx6 : 6 - x = 0 :=
      pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq_x
    have hy0 : y = 0 :=
      pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq_y
    have hx : x = 6 := by linarith
    rw [hx, hy0] at hDisk
    norm_num at hDisk

/-- M を構成し、必要な性質をまとめて与える補題。 -/
private lemma exists_midpoint {x y : ℝ} (hDisk : x ^ 2 + y ^ 2 ≤ 25)
    (hHyp : 5 * (x - 3) ^ 2 - 4 * y ^ 2 ≤ 20) (hxNe5 : x ≠ 5) :
    ∃ m n : ℝ, (m - 3) ^ 2 + n ^ 2 = 4 ∧
      (m, n) ≠ ((5 : ℝ), (0 : ℝ)) ∧
      x * m + y * n = 6 * m - 5 := by
  have hD_pos : (0 : ℝ) < (6 - x) ^ 2 + y ^ 2 := D_pos hDisk
  have hD_ne : ((6 - x) ^ 2 + y ^ 2) ≠ 0 := hD_pos.ne'
  have hE_nn : (0 : ℝ) ≤ 4 * ((6 - x) ^ 2 + y ^ 2) - (3 * x - 13) ^ 2 := by
    nlinarith [hHyp]
  set sqrtE : ℝ := Real.sqrt (4 * ((6 - x) ^ 2 + y ^ 2) - (3 * x - 13) ^ 2)
    with hsqrtE_def
  have hsqrtE_sq : sqrtE ^ 2 = 4 * ((6 - x) ^ 2 + y ^ 2) - (3 * x - 13) ^ 2 := by
    rw [hsqrtE_def, sq, Real.mul_self_sqrt hE_nn]
  -- m = 3 + a/D, n = b/D where a = (6-x)(3x-13) + y·sqrtE, b = -y(3x-13) + (6-x)·sqrtE
  set a : ℝ := (6 - x) * (3 * x - 13) + y * sqrtE with ha_def
  set b : ℝ := -(y * (3 * x - 13)) + (6 - x) * sqrtE with hb_def
  set D : ℝ := (6 - x) ^ 2 + y ^ 2 with hD_def
  -- 重要な代数恒等式: a² + b² = D · ((3x-13)² + sqrtE²) = 4 D²
  have h_a2_b2 : a ^ 2 + b ^ 2 = 4 * D ^ 2 := by
    have : a ^ 2 + b ^ 2 = D * ((3 * x - 13) ^ 2 + sqrtE ^ 2) := by
      show ((6 - x) * (3 * x - 13) + y * sqrtE) ^ 2 +
            (-(y * (3 * x - 13)) + (6 - x) * sqrtE) ^ 2 =
            ((6 - x) ^ 2 + y ^ 2) * ((3 * x - 13) ^ 2 + sqrtE ^ 2)
      ring
    rw [this, hsqrtE_sq]
    show D * ((3 * x - 13) ^ 2 + (4 * D - (3 * x - 13) ^ 2)) = 4 * D ^ 2
    ring
  -- 線形結合: (6-x) a − y b = ((6-x)² + y²) · (3x - 13) = D (3x - 13)
  have h_lin_combo : (6 - x) * a - y * b = D * (3 * x - 13) := by
    show (6 - x) * ((6 - x) * (3 * x - 13) + y * sqrtE) -
          y * (-(y * (3 * x - 13)) + (6 - x) * sqrtE) =
          ((6 - x) ^ 2 + y ^ 2) * (3 * x - 13)
    ring
  -- a, b, D をブラックボックスにする: 以後 a, b, D の中身は使わない
  clear_value a b D
  refine ⟨3 + a / D, b / D, ?_, ?_, ?_⟩
  · -- (m - 3)² + n² = 4
    show ((3 + a / D) - 3) ^ 2 + (b / D) ^ 2 = 4
    have h_simp : (3 + a / D) - 3 = a / D := by ring
    rw [h_simp, div_pow, div_pow, ← add_div, h_a2_b2,
        mul_div_assoc, div_self (pow_ne_zero 2 hD_ne), mul_one]
  · -- (m, n) ≠ (5, 0)
    intro h
    have hm5 : 3 + a / D = 5 := congrArg Prod.fst h
    have hn0 : b / D = 0 := congrArg Prod.snd h
    have ha_eq : a = 2 * D := by
      have h1 : a / D = 2 := by linarith
      have := (div_eq_iff hD_ne).mp h1
      linarith
    have hb_eq : b = 0 := by
      have := (div_eq_iff hD_ne).mp hn0
      linarith
    rw [ha_eq, hb_eq] at h_lin_combo
    -- (6-x) · 2D - y · 0 = D · (3x-13)
    have h1 : (2 * (6 - x) - (3 * x - 13)) * D = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h | h
    · have : x = 5 := by linarith
      exact hxNe5 this
    · exact absurd h hD_ne
  · -- x m + y n = 6m - 5
    show x * (3 + a / D) + y * (b / D) = 6 * (3 + a / D) - 5
    -- ((6-x)·a − y·b) / D = (D · (3x-13)) / D = 3x - 13
    -- ⇒ (6-x)·(a/D) − y·(b/D) = 3x - 13
    -- 整理: x·(3 + a/D) + y·(b/D) - 6·(3 + a/D) + 5 = -((6-x)·(a/D) - y·(b/D)) - (3x - 13) = 0
    have h_combo_div : (6 - x) * (a / D) - y * (b / D) = 3 * x - 13 := by
      have h1 : ((6 - x) * a - y * b) / D = D * (3 * x - 13) / D := by rw [h_lin_combo]
      have h2 : D * (3 * x - 13) / D = 3 * x - 13 := by
        rw [mul_comm, mul_div_assoc, div_self hD_ne, mul_one]
      have h3 : ((6 - x) * a - y * b) / D = (6 - x) * (a / D) - y * (b / D) := by
        rw [sub_div, mul_div_assoc, mul_div_assoc]
      linarith
    linarith

/-- 鍵となる不等式: (6m-5)(y-n)² ≤ (30-6m)m²。
    線形条件 + 円条件 + 円板条件から従う。 -/
private lemma key_sq_ineq {m n x y : ℝ}
    (hMsq : m ^ 2 + n ^ 2 = 6 * m - 5)
    (hLine : x * m + y * n = 6 * m - 5)
    (hDisk : x ^ 2 + y ^ 2 ≤ 25) :
    (6 * m - 5) * (y - n) ^ 2 ≤ (30 - 6 * m) * m ^ 2 := by
  -- m(x − m) = −n(y − n)
  have h_lin : m * (x - m) = -(n * (y - n)) := by nlinarith [hLine, hMsq]
  -- |A − M|² ≤ 30 − 6m
  have h_AM : (x - m) ^ 2 + (y - n) ^ 2 ≤ 30 - 6 * m := by
    have hexpand : (x - m) ^ 2 + (y - n) ^ 2 =
      x ^ 2 + y ^ 2 - 2 * (x * m + y * n) + (m ^ 2 + n ^ 2) := by ring
    rw [hexpand, hLine, hMsq]
    linarith
  -- m²(x−m)² = n²(y−n)²
  have h_sq : m ^ 2 * (x - m) ^ 2 = n ^ 2 * (y - n) ^ 2 := by
    have h := congrArg (·^2) h_lin
    have e1 : (m * (x - m)) ^ 2 = m ^ 2 * (x - m) ^ 2 := by ring
    have e2 : (-(n * (y - n))) ^ 2 = n ^ 2 * (y - n) ^ 2 := by ring
    linarith [h, e1, e2]
  -- m²((x−m)² + (y−n)²) = (m² + n²)(y−n)² = (6m−5)(y−n)²
  have h_id : m ^ 2 * ((x - m) ^ 2 + (y - n) ^ 2) = (6 * m - 5) * (y - n) ^ 2 := by
    have e1 : m ^ 2 * ((x - m) ^ 2 + (y - n) ^ 2)
            = m ^ 2 * (x - m) ^ 2 + m ^ 2 * (y - n) ^ 2 := by ring
    have e2 : n ^ 2 * (y - n) ^ 2 + m ^ 2 * (y - n) ^ 2
            = (m ^ 2 + n ^ 2) * (y - n) ^ 2 := by ring
    have e3 : (m ^ 2 + n ^ 2) * (y - n) ^ 2 = (6 * m - 5) * (y - n) ^ 2 := by
      rw [hMsq]
    linarith [e1, e2, e3, h_sq]
  -- 結論
  have hm2_nn : 0 ≤ m ^ 2 := sq_nonneg m
  have hmul := mul_le_mul_of_nonneg_left h_AM hm2_nn
  -- m²((x−m)² + (y−n)²) ≤ m²(30 − 6m)
  -- ⇒ (6m−5)(y−n)² ≤ (30 − 6m) m²
  have e : m ^ 2 * (30 - 6 * m) = (30 - 6 * m) * m ^ 2 := by ring
  linarith [h_id, hmul, e]

/-- A が線分 PQ 上 (P, Q は mkLocusConfig 由来) であることの十分条件:
    A · M = M · M (線分上) かつ x² + y² ≤ 25 (端点を超えない)。 -/
private lemma onSegment_mkLocusConfig {m n x y : ℝ}
    (hCircle : (m - 3) ^ 2 + n ^ 2 = 4)
    (hNotFive : (m, n) ≠ ((5 : ℝ), (0 : ℝ)))
    (hLine : x * m + y * n = 6 * m - 5)
    (hDisk : x ^ 2 + y ^ 2 ≤ 25) :
    OnSegment (x, y) (mkLocusConfig m n hCircle hNotFive) := by
  have hm_ge : 1 ≤ m := m_ge_one_of_locus hCircle
  have hm_lt : m < 5 := m_lt_five_of_locus hCircle hNotFive
  have hMsq : m ^ 2 + n ^ 2 = 6 * m - 5 := by nlinarith [hCircle]
  have hρ_pos : 0 < mkρ m := mkρ_pos hm_ge
  have hσ_pos : 0 < mkσ m := mkσ_pos hm_lt
  have hρ_sq : (mkρ m) ^ 2 = 6 * m - 5 := mkρ_sq hm_ge
  have hσ_sq : (mkσ m) ^ 2 = 30 - 6 * m := mkσ_sq hm_lt
  have hρ_ne : mkρ m ≠ 0 := hρ_pos.ne'
  have hσ_ne : mkσ m ≠ 0 := hσ_pos.ne'
  have hm_pos : 0 < m := by linarith
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have hσm_pos : 0 < mkσ m * m := mul_pos hσ_pos hm_pos
  have hσm_ne : mkσ m * m ≠ 0 := hσm_pos.ne'
  -- u := ρ(n−y)/(σ m), t := (1+u)/2, A = M + u(P − M) と書ける
  let u : ℝ := mkρ m * (n - y) / (mkσ m * m)
  let t : ℝ := (1 + u) / 2
  -- 鍵: u² ≤ 1
  have h_key : (6 * m - 5) * (y - n) ^ 2 ≤ (30 - 6 * m) * m ^ 2 :=
    key_sq_ineq hMsq hLine hDisk
  have h_u_sq : u ^ 2 ≤ 1 := by
    show (mkρ m * (n - y) / (mkσ m * m)) ^ 2 ≤ 1
    rw [div_pow, mul_pow]
    rw [div_le_one (by positivity : (0 : ℝ) < (mkσ m * m) ^ 2)]
    rw [mul_pow, hρ_sq, hσ_sq]
    have h_yn : (n - y) ^ 2 = (y - n) ^ 2 := by ring
    rw [h_yn]
    linarith [h_key]
  have h_u_lb : -1 ≤ u := by nlinarith [h_u_sq, sq_nonneg (u + 1)]
  have h_u_ub : u ≤ 1 := by nlinarith [h_u_sq, sq_nonneg (u - 1)]
  -- 線形条件 → m(x − m) = n(n − y) は (1−t)P + tQ の x 座標を計算するのに使う
  have h_lin : m * (x - m) = n * (n - y) := by nlinarith [hLine, hMsq]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ t
    show 0 ≤ (1 + u) / 2; linarith
  · -- t ≤ 1
    show (1 + u) / 2 ≤ 1; linarith
  · -- (x, y).1 = (1−t) P.1 + t Q.1
    show x = (1 - (1 + u) / 2) * (mkLocusConfig m n hCircle hNotFive).P.1 +
            (1 + u) / 2 * (mkLocusConfig m n hCircle hNotFive).Q.1
    rw [mkLocusConfig_P, mkLocusConfig_Q]
    show x = (1 - (1 + u) / 2) * (m - mkσ m * n / mkρ m) +
            (1 + u) / 2 * (m + mkσ m * n / mkρ m)
    -- (1−t)P + tQ = M + u(P − M)x = m + u · σn/ρ
    -- u · σn/ρ = ρ(n−y)/(σm) · σn/ρ = n(n−y)/m
    -- なので x = m + n(n−y)/m ⇔ m·x = m² + n(n−y) ⇔ m(x−m) = n(n−y) ✓
    have h_u_form : u * (mkσ m * n / mkρ m) = n * (n - y) / m := by
      show mkρ m * (n - y) / (mkσ m * m) * (mkσ m * n / mkρ m) = n * (n - y) / m
      field_simp
    have h_eq : (1 - (1 + u) / 2) * (m - mkσ m * n / mkρ m) +
                (1 + u) / 2 * (m + mkσ m * n / mkρ m) =
                m + u * (mkσ m * n / mkρ m) := by ring
    rw [h_eq, h_u_form]
    -- 目標: x = m + n(n − y)/m
    field_simp
    linear_combination h_lin
  · -- (x, y).2 = (1−t) P.2 + t Q.2
    show y = (1 - (1 + u) / 2) * (mkLocusConfig m n hCircle hNotFive).P.2 +
            (1 + u) / 2 * (mkLocusConfig m n hCircle hNotFive).Q.2
    rw [mkLocusConfig_P, mkLocusConfig_Q]
    show y = (1 - (1 + u) / 2) * (n + mkσ m * m / mkρ m) +
            (1 + u) / 2 * (n - mkσ m * m / mkρ m)
    -- y 座標: n − u · σm/ρ = n − (ρ(n−y)/(σm)) · σm/ρ = n − (n − y) = y ✓
    have h_u_form : u * (mkσ m * m / mkρ m) = n - y := by
      show mkρ m * (n - y) / (mkσ m * m) * (mkσ m * m / mkρ m) = n - y
      field_simp
    have h_eq : (1 - (1 + u) / 2) * (n + mkσ m * m / mkρ m) +
                (1 + u) / 2 * (n - mkσ m * m / mkρ m) =
                n - u * (mkσ m * m / mkρ m) := by ring
    rw [h_eq, h_u_form]; ring

private lemma backward (A : ℝ × ℝ) (h : SweptRange A) : ∃ cfg, OnSegment A cfg := by
  obtain ⟨x, y⟩ := A
  have hxNe5 : x ≠ 5 := x_ne_five h
  obtain ⟨hDisk, hHyp, hNot5⟩ := h
  obtain ⟨m, n, hCircle, hNotFive, hLine⟩ := exists_midpoint hDisk hHyp hxNe5
  exact ⟨mkLocusConfig m n hCircle hNotFive, onSegment_mkLocusConfig hCircle hNotFive hLine hDisk⟩

/-! ### 主結果 -/

/-- (2) A = (x, y) について、線分 PQ が A を通過する配置が存在することは、
    A が大円板内かつ双曲線内側にあり、(5, 0) でないことと同値。 -/
theorem swept_range_iff (A : ℝ × ℝ) :
    (∃ cfg : Config, OnSegment A cfg) ↔ SweptRange A :=
  ⟨forward A, backward A⟩

end Common2026.T_Q3_2
