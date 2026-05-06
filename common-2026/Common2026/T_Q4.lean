/-
東大 2026 第4問

  k を実数とし、座標平面上の曲線 C を y = x³ − kx で定める。
  C 上の 2 点 P, Q に対する以下の条件 (*) を考える。
    条件 (*): 原点 O, 点 P, 点 Q は相異なり、C の O, P, Q における接線のうち、
              どの 2 本も交わり、そのなす角はすべて π/3 となる。
    ただし、2 直線のなす角は 0 以上 π/2 以下の範囲で考えるものとする。

(1) 条件 (*) を満たす P, Q が存在するような k の範囲を求めよ。

  答え: k > √3 / 3。

  方針:
    接線の傾きは O で −k, x = a で 3a²−k。
    傾き m₁, m₂ がなす角が π/3
      ⇔ (m₁ − m₂)² = 3 (1 + m₁ m₂)²
      （実数体上では平行・直交は自動排除される）。

    O, P 間の角条件: (-3p²)² = 3(1 + k² − 3kp²)²
      ⇔ 3 (p²)² = (1 + k² − 3kp²)²
      ⇔ ((1+k²−3kp²) − √3 p²)((1+k²−3kp²) + √3 p²) = 0
      ⇔ (3k + √3) p² = 1+k²  または  (3k − √3) p² = 1+k²

    p² ≠ q² (hPQ から) で 1+k² > 0 なので、p², q² は異なる根を取り、
    両方の分母 (3k+√3, 3k−√3) が正である必要 ⇒ k > √3/3。

    逆に k > √3/3 のとき、p² = (1+k²)/(3k+√3), q² = (1+k²)/(3k−√3) で
    Config を構成できる。

(2) k が (1) で定まる範囲 (k > √3/3) にあるとする。
  P, Q が条件 (*) を満たすように動くとき、C の O, P, Q における接線によって
  囲まれる三角形の面積 S の最大値を M、最小値を m とおく。
  ただし、3 本の接線が 1 点で交わるときは S = 0 とする。
  M = 4m となる k の値を求めよ。

  答え: k = 5√3 / 12。

  方針:
    O での接線: y = −k x。
    P (x=p) での接線: y = (3p²−k) x − 2p³。
    Q (x=q) での接線: y = (3q²−k) x − 2q³。
    O-P 交点 A = (2p/3, −2kp/3), O-Q 交点 B = (2q/3, −2kq/3),
    P-Q 交点 C は省略 (計算で求める)。
    底辺 AB = (2/3)|p−q|√(1+k²), 高さ = 2 p² q² / (|p+q|√(1+k²))。
    ⇒ S = 2 p² q² |p−q| / (3 |p+q|)。

    Config の (1) からの帰結: {p², q²} = {α², β²} where α := mkP k, β := mkQ k。
    (p − q)² + (p + q)² = 2(p² + q²) = 2(α² + β²) は固定。
    (p − q)²(p + q)² = (p² − q²)² = (β² − α²)² も固定。
    ⇒ {(p−q)², (p+q)²} = {(α+β)², (β−α)²}。
    ⇒ |p−q|, |p+q| は (α+β), (β−α) のいずれか（順は p, q の符号に依存）。

    S は 2 値:
      areaMinus = 2 α² β² (β − α) / (3 (α + β))   (|p+q| = α+β の場合)
      areaPlus  = 2 α² β² (α + β) / (3 (β − α))   (|p+q| = β−α の場合)

    両方とも実現可能 (mkP k, mkQ k 同符号 ⇒ areaMinus, 異符号 ⇒ areaPlus)。
    areaPlus / areaMinus = ((α + β) / (β − α))² > 1 なので
    M = areaPlus, m = areaMinus。

    M = 4m ⇔ ((α+β)/(β−α))² = 4 ⇔ α+β = 2(β−α) ⇔ β = 3α
           ⇔ β² = 9α² ⇔ (3k+√3)/(3k−√3) = 9 ⇔ k = 5√3/12。
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Common2026.T_Q4

open Real

/-! ## 共通定義 -/

/-- y = x³ − kx の x = a における接線の傾き。 -/
def slopeAt (k a : ℝ) : ℝ := 3 * a ^ 2 - k

/-- 2 直線（傾き m₁, m₂）のなす角が π/3 となる条件。
    平行（m₁ = m₂）と直交（1 + m₁ m₂ = 0）は実数体上では自動排除される。 -/
def AngleEq60 (m₁ m₂ : ℝ) : Prop :=
  (m₁ - m₂) ^ 2 = 3 * (1 + m₁ * m₂) ^ 2

/-- 条件 (*) を満たす配置。各 hX は対応する 2 接線がなす角が π/3。 -/
structure Config (k : ℝ) where
  p : ℝ
  q : ℝ
  hOP : AngleEq60 (slopeAt k 0) (slopeAt k p)
  hOQ : AngleEq60 (slopeAt k 0) (slopeAt k q)
  hPQ : AngleEq60 (slopeAt k p) (slopeAt k q)

lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num : (3 : ℝ) ≥ 0)

lemma sqrt3_sq' : (Real.sqrt 3) ^ 2 = 3 := by
  rw [sq]; exact sqrt3_sq

lemma sqrt3_pos : 0 < Real.sqrt 3 :=
  Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)

lemma one_plus_k_sq_pos (k : ℝ) : 0 < 1 + k ^ 2 := by
  nlinarith [sq_nonneg k]

/-! ## (1) 順方向: Config から k > √3/3 -/

/-- hOP の代数的書き換え: 3 (p²)² = (1+k²−3kp²)²。 -/
private lemma hOP_eqn (k : ℝ) (cfg : Config k) :
    3 * (cfg.p ^ 2) ^ 2 = (1 + k ^ 2 - 3 * k * cfg.p ^ 2) ^ 2 := by
  have h := cfg.hOP
  unfold AngleEq60 slopeAt at h
  nlinarith [h]

private lemma hOQ_eqn (k : ℝ) (cfg : Config k) :
    3 * (cfg.q ^ 2) ^ 2 = (1 + k ^ 2 - 3 * k * cfg.q ^ 2) ^ 2 := by
  have h := cfg.hOQ
  unfold AngleEq60 slopeAt at h
  nlinarith [h]

/-- p² は (3k+√3)·u = 1+k² または (3k−√3)·u = 1+k² の解。 -/
lemma p_sq_root (k : ℝ) (cfg : Config k) :
    cfg.p ^ 2 * (3 * k + Real.sqrt 3) = 1 + k ^ 2 ∨
    cfg.p ^ 2 * (3 * k - Real.sqrt 3) = 1 + k ^ 2 := by
  have h := hOP_eqn k cfg
  have hfactor :
      ((1 + k ^ 2 - 3 * k * cfg.p ^ 2) - Real.sqrt 3 * cfg.p ^ 2) *
      ((1 + k ^ 2 - 3 * k * cfg.p ^ 2) + Real.sqrt 3 * cfg.p ^ 2) = 0 := by
    have hexp : ((1 + k ^ 2 - 3 * k * cfg.p ^ 2) - Real.sqrt 3 * cfg.p ^ 2) *
                ((1 + k ^ 2 - 3 * k * cfg.p ^ 2) + Real.sqrt 3 * cfg.p ^ 2) =
                (1 + k ^ 2 - 3 * k * cfg.p ^ 2) ^ 2
                - (Real.sqrt 3 * Real.sqrt 3) * (cfg.p ^ 2) ^ 2 := by ring
    rw [hexp, sqrt3_sq]
    linarith [h]
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · left; linarith [h1]
  · right; linarith [h2]

lemma q_sq_root (k : ℝ) (cfg : Config k) :
    cfg.q ^ 2 * (3 * k + Real.sqrt 3) = 1 + k ^ 2 ∨
    cfg.q ^ 2 * (3 * k - Real.sqrt 3) = 1 + k ^ 2 := by
  have h := hOQ_eqn k cfg
  have hfactor :
      ((1 + k ^ 2 - 3 * k * cfg.q ^ 2) - Real.sqrt 3 * cfg.q ^ 2) *
      ((1 + k ^ 2 - 3 * k * cfg.q ^ 2) + Real.sqrt 3 * cfg.q ^ 2) = 0 := by
    have hexp : ((1 + k ^ 2 - 3 * k * cfg.q ^ 2) - Real.sqrt 3 * cfg.q ^ 2) *
                ((1 + k ^ 2 - 3 * k * cfg.q ^ 2) + Real.sqrt 3 * cfg.q ^ 2) =
                (1 + k ^ 2 - 3 * k * cfg.q ^ 2) ^ 2
                - (Real.sqrt 3 * Real.sqrt 3) * (cfg.q ^ 2) ^ 2 := by ring
    rw [hexp, sqrt3_sq]
    linarith [h]
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · left; linarith [h1]
  · right; linarith [h2]

/-- p² > 0 (P ≠ O が hOP から従う)。 -/
lemma p_sq_pos (k : ℝ) (cfg : Config k) : 0 < cfg.p ^ 2 := by
  have h_nn : 0 ≤ cfg.p ^ 2 := sq_nonneg _
  rcases lt_or_eq_of_le h_nn with hlt | heq
  · exact hlt
  · exfalso
    have hk_sq_pos : 0 < 1 + k ^ 2 := one_plus_k_sq_pos k
    rcases p_sq_root k cfg with h | h
    all_goals
      rw [← heq] at h
      simp at h
      linarith [h, hk_sq_pos]

lemma q_sq_pos (k : ℝ) (cfg : Config k) : 0 < cfg.q ^ 2 := by
  have h_nn : 0 ≤ cfg.q ^ 2 := sq_nonneg _
  rcases lt_or_eq_of_le h_nn with hlt | heq
  · exact hlt
  · exfalso
    have hk_sq_pos : 0 < 1 + k ^ 2 := one_plus_k_sq_pos k
    rcases q_sq_root k cfg with h | h
    all_goals
      rw [← heq] at h
      simp at h
      linarith [h, hk_sq_pos]

/-- p² ≠ q²（hPQ から）。 -/
lemma p_sq_ne_q_sq (k : ℝ) (cfg : Config k) : cfg.p ^ 2 ≠ cfg.q ^ 2 := by
  intro heq
  have h := cfg.hPQ
  unfold AngleEq60 slopeAt at h
  rw [heq] at h
  have hLHS : (3 * cfg.q ^ 2 - k - (3 * cfg.q ^ 2 - k)) ^ 2 = 0 := by ring
  rw [hLHS] at h
  have hpos : 0 < (1 + (3 * cfg.q ^ 2 - k) * (3 * cfg.q ^ 2 - k)) ^ 2 := by
    have : 0 ≤ (3 * cfg.q ^ 2 - k) * (3 * cfg.q ^ 2 - k) := mul_self_nonneg _
    have h1 : (1 : ℝ) ≤ 1 + (3 * cfg.q ^ 2 - k) * (3 * cfg.q ^ 2 - k) := by linarith
    have : 0 < 1 + (3 * cfg.q ^ 2 - k) * (3 * cfg.q ^ 2 - k) := by linarith
    positivity
  linarith [h, hpos]

/-- 順方向: Config から k > √3/3。 -/
private lemma forward_direction (k : ℝ) (cfg : Config k) : Real.sqrt 3 / 3 < k := by
  have hp_pos : 0 < cfg.p ^ 2 := p_sq_pos k cfg
  have hq_pos : 0 < cfg.q ^ 2 := q_sq_pos k cfg
  have hpq_ne : cfg.p ^ 2 ≠ cfg.q ^ 2 := p_sq_ne_q_sq k cfg
  have hk_sq_pos : 0 < 1 + k ^ 2 := one_plus_k_sq_pos k
  rcases p_sq_root k cfg with hp | hp <;> rcases q_sq_root k cfg with hq | hq
  · -- 両方 (3k+√3) 根 ⇒ p² = q²、矛盾
    exfalso
    have hadd_ne : 3 * k + Real.sqrt 3 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hp
      linarith [hp, hk_sq_pos]
    have heq : cfg.p ^ 2 = cfg.q ^ 2 := by
      have h : cfg.p ^ 2 * (3 * k + Real.sqrt 3) = cfg.q ^ 2 * (3 * k + Real.sqrt 3) := by
        rw [hp, hq]
      exact mul_right_cancel₀ hadd_ne h
    exact hpq_ne heq
  · -- p² 「+」根, q² 「−」根
    have h2 : 0 < 3 * k - Real.sqrt 3 := by
      have hpos_lhs : 0 < cfg.q ^ 2 * (3 * k - Real.sqrt 3) := by rw [hq]; exact hk_sq_pos
      exact (mul_pos_iff_of_pos_left hq_pos).mp hpos_lhs
    linarith [h2]
  · -- p² 「−」根, q² 「+」根
    have h1 : 0 < 3 * k - Real.sqrt 3 := by
      have hpos_lhs : 0 < cfg.p ^ 2 * (3 * k - Real.sqrt 3) := by rw [hp]; exact hk_sq_pos
      exact (mul_pos_iff_of_pos_left hp_pos).mp hpos_lhs
    linarith [h1]
  · -- 両方 (3k−√3) 根 ⇒ p² = q²、矛盾
    exfalso
    have hsub_ne : 3 * k - Real.sqrt 3 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hp
      linarith [hp, hk_sq_pos]
    have heq : cfg.p ^ 2 = cfg.q ^ 2 := by
      have h : cfg.p ^ 2 * (3 * k - Real.sqrt 3) = cfg.q ^ 2 * (3 * k - Real.sqrt 3) := by
        rw [hp, hq]
      exact mul_right_cancel₀ hsub_ne h
    exact hpq_ne heq

/-! ## (1) 逆方向: k > √3/3 から Config を構成 -/

lemma three_k_add_sqrt3_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    0 < 3 * k + Real.sqrt 3 := by
  have h : Real.sqrt 3 < 3 * k := by linarith
  linarith [sqrt3_pos]

lemma three_k_sub_sqrt3_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    0 < 3 * k - Real.sqrt 3 := by linarith

/-- p² = (1+k²)/(3k+√3) (正値)。 -/
noncomputable def mkP (k : ℝ) : ℝ :=
  Real.sqrt ((1 + k ^ 2) / (3 * k + Real.sqrt 3))

noncomputable def mkQ (k : ℝ) : ℝ :=
  Real.sqrt ((1 + k ^ 2) / (3 * k - Real.sqrt 3))

lemma mkP_sq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (mkP k) ^ 2 = (1 + k ^ 2) / (3 * k + Real.sqrt 3) := by
  unfold mkP
  rw [sq]
  apply Real.mul_self_sqrt
  apply div_nonneg
  · exact (one_plus_k_sq_pos k).le
  · exact (three_k_add_sqrt3_pos hk).le

lemma mkQ_sq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (mkQ k) ^ 2 = (1 + k ^ 2) / (3 * k - Real.sqrt 3) := by
  unfold mkQ
  rw [sq]
  apply Real.mul_self_sqrt
  apply div_nonneg
  · exact (one_plus_k_sq_pos k).le
  · exact (three_k_sub_sqrt3_pos hk).le

/-- (3k+√3) (mkP k)² = 1+k²。 -/
private lemma mkP_eq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (3 * k + Real.sqrt 3) * (mkP k) ^ 2 = 1 + k ^ 2 := by
  have hd : 3 * k + Real.sqrt 3 ≠ 0 := (three_k_add_sqrt3_pos hk).ne'
  rw [mkP_sq hk]
  field_simp

/-- (3k−√3) (mkQ k)² = 1+k²。 -/
private lemma mkQ_eq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (3 * k - Real.sqrt 3) * (mkQ k) ^ 2 = 1 + k ^ 2 := by
  have hd : 3 * k - Real.sqrt 3 ≠ 0 := (three_k_sub_sqrt3_pos hk).ne'
  rw [mkQ_sq hk]
  field_simp

/-- O-P 間の角条件 (mkP は構成上満たす)。 -/
lemma mkConfig_hOP {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    AngleEq60 (slopeAt k 0) (slopeAt k (mkP k)) := by
  unfold AngleEq60 slopeAt
  set p2 := (mkP k) ^ 2 with hp2def
  -- (3k+√3) p² = 1+k² より 1+k² − 3kp² = √3 p²
  have hP : (3 * k + Real.sqrt 3) * p2 = 1 + k ^ 2 := mkP_eq hk
  have h_diff : 1 + k ^ 2 - 3 * k * p2 = Real.sqrt 3 * p2 := by linarith [hP]
  -- key: 3 p²² = (1+k²−3kp²)² = (√3 p²)² = 3 p²²
  have key : 3 * p2 ^ 2 = (1 + k ^ 2 - 3 * k * p2) ^ 2 := by
    rw [h_diff, mul_pow, sqrt3_sq']
  -- 目標: (3*0² − k − (3*p² − k))² = 3 (1 + (3*0² − k)(3*p² − k))²
  show (3 * (0 : ℝ) ^ 2 - k - (3 * p2 - k)) ^ 2 =
       3 * (1 + (3 * (0 : ℝ) ^ 2 - k) * (3 * p2 - k)) ^ 2
  have hLHS : (3 * (0 : ℝ) ^ 2 - k - (3 * p2 - k)) ^ 2 = 9 * p2 ^ 2 := by ring
  have hRHS_inner : 1 + (3 * (0 : ℝ) ^ 2 - k) * (3 * p2 - k) = 1 + k ^ 2 - 3 * k * p2 := by ring
  rw [hLHS, hRHS_inner]
  linarith [key]

lemma mkConfig_hOQ {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    AngleEq60 (slopeAt k 0) (slopeAt k (mkQ k)) := by
  unfold AngleEq60 slopeAt
  set q2 := (mkQ k) ^ 2 with hq2def
  have hQ : (3 * k - Real.sqrt 3) * q2 = 1 + k ^ 2 := mkQ_eq hk
  have h_diff : 1 + k ^ 2 - 3 * k * q2 = -(Real.sqrt 3) * q2 := by linarith [hQ]
  have key : 3 * q2 ^ 2 = (1 + k ^ 2 - 3 * k * q2) ^ 2 := by
    rw [h_diff]
    have : (-(Real.sqrt 3) * q2) ^ 2 = (Real.sqrt 3) ^ 2 * q2 ^ 2 := by ring
    rw [this, sqrt3_sq']
  show (3 * (0 : ℝ) ^ 2 - k - (3 * q2 - k)) ^ 2 =
       3 * (1 + (3 * (0 : ℝ) ^ 2 - k) * (3 * q2 - k)) ^ 2
  have hLHS : (3 * (0 : ℝ) ^ 2 - k - (3 * q2 - k)) ^ 2 = 9 * q2 ^ 2 := by ring
  have hRHS_inner : 1 + (3 * (0 : ℝ) ^ 2 - k) * (3 * q2 - k) = 1 + k ^ 2 - 3 * k * q2 := by ring
  rw [hLHS, hRHS_inner]
  linarith [key]

/-- (3k+√3)(3p²−k) = 3 − √3 k。 -/
private lemma mkP_slope_eq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (3 * k + Real.sqrt 3) * (3 * (mkP k) ^ 2 - k) = 3 - Real.sqrt 3 * k := by
  have h := mkP_eq hk
  linear_combination 3 * h

/-- (3k−√3)(3q²−k) = 3 + √3 k。 -/
private lemma mkQ_slope_eq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (3 * k - Real.sqrt 3) * (3 * (mkQ k) ^ 2 - k) = 3 + Real.sqrt 3 * k := by
  have h := mkQ_eq hk
  linear_combination 3 * h

/-- 3k² − 1 ≠ 0（k > √3/3 から 3k² > 1）。 -/
private lemma three_k_sq_minus_one_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    0 < 3 * k ^ 2 - 1 := by
  have h1 : 0 < 3 * k + Real.sqrt 3 := three_k_add_sqrt3_pos hk
  have h2 : 0 < 3 * k - Real.sqrt 3 := three_k_sub_sqrt3_pos hk
  have h12 : 0 < (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) := mul_pos h1 h2
  have h_eq : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) = 9 * k ^ 2 - 3 := by
    have : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) =
        (3 * k) ^ 2 - (Real.sqrt 3) ^ 2 := by ring
    rw [this, sqrt3_sq']; ring
  rw [h_eq] at h12
  linarith [h12]

/-- P-Q 間の角条件 (代数的に直接検証)。 -/
lemma mkConfig_hPQ {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    AngleEq60 (slopeAt k (mkP k)) (slopeAt k (mkQ k)) := by
  unfold AngleEq60 slopeAt
  set p2 := (mkP k) ^ 2 with hp2def
  set q2 := (mkQ k) ^ 2 with hq2def
  have hd1 : 3 * k + Real.sqrt 3 ≠ 0 := (three_k_add_sqrt3_pos hk).ne'
  have hd2 : 3 * k - Real.sqrt 3 ≠ 0 := (three_k_sub_sqrt3_pos hk).ne'
  have hd12 : 3 * k ^ 2 - 1 ≠ 0 := (three_k_sq_minus_one_pos hk).ne'
  have hP : (3 * k + Real.sqrt 3) * p2 = 1 + k ^ 2 := mkP_eq hk
  have hQ : (3 * k - Real.sqrt 3) * q2 = 1 + k ^ 2 := mkQ_eq hk
  -- (3k+√3)(3k−√3)(3p²−k)(3q²−k) = (3 − √3 k)(3 + √3 k) = 9 − 3k²
  have hPQ_prod : (3 * k ^ 2 - 1) * ((3 * p2 - k) * (3 * q2 - k)) = 3 - k ^ 2 := by
    have hP' := mkP_slope_eq hk
    have hQ' := mkQ_slope_eq hk
    -- (3k+√3)(3p²−k) · (3k−√3)(3q²−k) = (3 − √3 k)(3 + √3 k)
    have hmul : ((3 * k + Real.sqrt 3) * (3 * p2 - k)) *
                ((3 * k - Real.sqrt 3) * (3 * q2 - k)) =
                (3 - Real.sqrt 3 * k) * (3 + Real.sqrt 3 * k) := by
      rw [show (3 * p2 - k) = (3 * (mkP k) ^ 2 - k) from rfl,
          show (3 * q2 - k) = (3 * (mkQ k) ^ 2 - k) from rfl]
      rw [hP', hQ']
    -- 左辺 = (3k+√3)(3k−√3) (3p²−k)(3q²−k) = (9k²−3) ... = 3(3k²−1)·...
    have hL : ((3 * k + Real.sqrt 3) * (3 * p2 - k)) *
              ((3 * k - Real.sqrt 3) * (3 * q2 - k)) =
              ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) *
              ((3 * p2 - k) * (3 * q2 - k)) := by ring
    have hR : (3 - Real.sqrt 3 * k) * (3 + Real.sqrt 3 * k) =
              9 - (Real.sqrt 3) ^ 2 * k ^ 2 := by ring
    have hR' : (3 - Real.sqrt 3 * k) * (3 + Real.sqrt 3 * k) = 9 - 3 * k ^ 2 := by
      rw [hR, sqrt3_sq']
    have hL_eq : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) = 9 * k ^ 2 - 3 := by
      have : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) =
          (3 * k) ^ 2 - (Real.sqrt 3) ^ 2 := by ring
      rw [this, sqrt3_sq']; ring
    rw [hL, hL_eq] at hmul
    rw [hR'] at hmul
    -- hmul : (9k² − 3) * ((3p²−k)(3q²−k)) = 9 − 3k²
    -- ⇒ 3(3k²−1) * (...) = -3(k²−3) = 3(3 − k²)
    -- ⇒ (3k²−1) * (...) = 3 − k²
    linarith [hmul]
  -- (3k+√3)(3p²−k) − (3k−√3)(3q²−k) = (3−√3k) − (3+√3k) = −2√3 k と思いきや、
  -- ここで欲しいのは (3p²−k) − (3q²−k)。これは 3(p²−q²)。
  -- p² − q² の値: (1+k²)/(3k+√3) − (1+k²)/(3k−√3) = (1+k²) · ((3k−√3) − (3k+√3))/D
  --                                              = (1+k²) · (−2√3)/D, D = (3k+√3)(3k−√3) = 3(3k²−1)
  -- ⇒ p² − q² = −2√3(1+k²)/(3(3k²−1))
  -- ⇒ 3(p²−q²) = −2√3(1+k²)/(3k²−1)
  have hPQ_diff : (3 * k ^ 2 - 1) * ((3 * p2 - k) - (3 * q2 - k)) =
                  -2 * Real.sqrt 3 * (1 + k ^ 2) := by
    -- 3(p²−q²) · (3k²−1) = ?
    -- p²·(3k²−1) を計算: p² = (1+k²)/(3k+√3) なので
    -- p² · (3k²−1) · 3 = ...
    -- 別のアプローチ: hP, hQ を使う
    -- (3k+√3) p² = 1+k², (3k−√3) q² = 1+k²
    -- ⇒ (3k+√3) p² − (3k−√3) q² = 0  (両辺 1+k²)
    -- ⇒ 3k(p²−q²) + √3(p²+q²) = 0  ※ √3 p² − (−√3) q² = √3(p²+q²)
    -- 別経路: (3k−√3) p² − (3k+√3) q² = ((3k+√3)−2√3) p² − ((3k−√3)+2√3) q²
    --       = ((3k+√3)p² − (3k−√3)q²) − 2√3(p²+q²) = (1+k²) − (1+k²) − 2√3(p²+q²) = −2√3(p²+q²)
    -- これも単純化に有用ではない。
    -- 単純に (1+k²) を共通分母にして書き直す:
    -- (3k+√3) p² = 1+k², (3k−√3) q² = 1+k² なので
    -- (3k−√3)(3k+√3) p² q² の合成を活用:
    --   p² = (1+k²)/(3k+√3) ⇒ (3k+√3)(3k−√3) p² = (3k−√3)(1+k²)
    --                       ⇒ (9k²−3) p² = (3k−√3)(1+k²)
    --   q² = (1+k²)/(3k−√3) ⇒ (9k²−3) q² = (3k+√3)(1+k²)
    -- 引き算: (9k²−3)(p²−q²) = (3k−√3)(1+k²) − (3k+√3)(1+k²) = −2√3 (1+k²)
    -- ⇒ 3(3k²−1)(p²−q²) = −2√3(1+k²)
    -- 両辺 ×3: (3k²−1)·3(p²−q²) = −2√3(1+k²)
    -- 一方 (3p²−k) − (3q²−k) = 3(p²−q²)
    have hp_scaled : (9 * k ^ 2 - 3) * p2 = (3 * k - Real.sqrt 3) * (1 + k ^ 2) := by
      -- (3k+√3) p² = 1+k² の両辺に (3k−√3) を掛ける
      have : (3 * k - Real.sqrt 3) * ((3 * k + Real.sqrt 3) * p2) =
             (3 * k - Real.sqrt 3) * (1 + k ^ 2) := by rw [hP]
      have h_eq : (3 * k - Real.sqrt 3) * ((3 * k + Real.sqrt 3) * p2) =
                  ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) * p2 := by ring
      rw [h_eq] at this
      have h_prod : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) = 9 * k ^ 2 - 3 := by
        have e : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) =
                 (3 * k) ^ 2 - (Real.sqrt 3) ^ 2 := by ring
        rw [e, sqrt3_sq']; ring
      rw [h_prod] at this
      exact this
    have hq_scaled : (9 * k ^ 2 - 3) * q2 = (3 * k + Real.sqrt 3) * (1 + k ^ 2) := by
      have : (3 * k + Real.sqrt 3) * ((3 * k - Real.sqrt 3) * q2) =
             (3 * k + Real.sqrt 3) * (1 + k ^ 2) := by rw [hQ]
      have h_eq : (3 * k + Real.sqrt 3) * ((3 * k - Real.sqrt 3) * q2) =
                  ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) * q2 := by ring
      rw [h_eq] at this
      have h_prod : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) = 9 * k ^ 2 - 3 := by
        have e : (3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3) =
                 (3 * k) ^ 2 - (Real.sqrt 3) ^ 2 := by ring
        rw [e, sqrt3_sq']; ring
      rw [h_prod] at this
      exact this
    -- (9k²−3)(p²−q²) = (3k−√3)(1+k²) − (3k+√3)(1+k²) = −2√3(1+k²)
    have hsub : (9 * k ^ 2 - 3) * (p2 - q2) = -2 * Real.sqrt 3 * (1 + k ^ 2) := by
      have h1 : (9 * k ^ 2 - 3) * p2 - (9 * k ^ 2 - 3) * q2 =
                (3 * k - Real.sqrt 3) * (1 + k ^ 2) - (3 * k + Real.sqrt 3) * (1 + k ^ 2) := by
        rw [hp_scaled, hq_scaled]
      have h2 : (9 * k ^ 2 - 3) * p2 - (9 * k ^ 2 - 3) * q2 =
                (9 * k ^ 2 - 3) * (p2 - q2) := by ring
      have h3 : (3 * k - Real.sqrt 3) * (1 + k ^ 2) - (3 * k + Real.sqrt 3) * (1 + k ^ 2) =
                -2 * Real.sqrt 3 * (1 + k ^ 2) := by ring
      linarith [h1, h2, h3]
    -- (3k²−1) · ((3p²−k)−(3q²−k)) = (3k²−1) · 3(p²−q²) = 3(p²−q²)·(3k²−1) = (9k²−3)(p²−q²) = −2√3(1+k²)
    have h_target : (3 * k ^ 2 - 1) * ((3 * p2 - k) - (3 * q2 - k)) =
                    (9 * k ^ 2 - 3) * (p2 - q2) := by ring
    rw [h_target]
    exact hsub
  -- ここから組み立て:
  -- LHS = ((3p²−k) − (3q²−k))² = (−2√3(1+k²)/(3k²−1))² = 12(1+k²)²/(3k²−1)²
  -- 1 + (3p²−k)(3q²−k) = 1 + (3−k²)/(3k²−1) = (3k²−1+3−k²)/(3k²−1) = 2(1+k²)/(3k²−1)
  -- RHS = 3 · (2(1+k²)/(3k²−1))² = 12(1+k²)²/(3k²−1)²
  -- ⇒ LHS = RHS
  -- 形式化: 両辺を (3k²−1)² 倍してみる
  show ((3 * p2 - k) - (3 * q2 - k)) ^ 2 = 3 * (1 + (3 * p2 - k) * (3 * q2 - k)) ^ 2
  have h_lhs_scaled : (3 * k ^ 2 - 1) ^ 2 * ((3 * p2 - k) - (3 * q2 - k)) ^ 2 =
                      12 * (1 + k ^ 2) ^ 2 := by
    have h := hPQ_diff
    have : ((3 * k ^ 2 - 1) * ((3 * p2 - k) - (3 * q2 - k))) ^ 2 =
           (-2 * Real.sqrt 3 * (1 + k ^ 2)) ^ 2 := by rw [h]
    have e1 : ((3 * k ^ 2 - 1) * ((3 * p2 - k) - (3 * q2 - k))) ^ 2 =
              (3 * k ^ 2 - 1) ^ 2 * ((3 * p2 - k) - (3 * q2 - k)) ^ 2 := by ring
    have e2 : (-2 * Real.sqrt 3 * (1 + k ^ 2)) ^ 2 =
              4 * (Real.sqrt 3) ^ 2 * (1 + k ^ 2) ^ 2 := by ring
    rw [sqrt3_sq'] at e2
    rw [e1] at this
    rw [this, e2]; ring
  have h_inner_scaled : (3 * k ^ 2 - 1) * (1 + (3 * p2 - k) * (3 * q2 - k)) =
                        2 * (1 + k ^ 2) := by
    -- (3k²−1) · (1 + (3p²−k)(3q²−k)) = (3k²−1) + (3k²−1)(3p²−k)(3q²−k)
    --                                = (3k²−1) + (3 − k²)
    --                                = 2k² + 2 = 2(1+k²)
    have h := hPQ_prod
    have : (3 * k ^ 2 - 1) * (1 + (3 * p2 - k) * (3 * q2 - k)) =
           (3 * k ^ 2 - 1) + (3 * k ^ 2 - 1) * ((3 * p2 - k) * (3 * q2 - k)) := by ring
    rw [this, h]
    ring
  have h_rhs_scaled : (3 * k ^ 2 - 1) ^ 2 * (3 * (1 + (3 * p2 - k) * (3 * q2 - k)) ^ 2) =
                      12 * (1 + k ^ 2) ^ 2 := by
    have h := h_inner_scaled
    have step : ((3 * k ^ 2 - 1) * (1 + (3 * p2 - k) * (3 * q2 - k))) ^ 2 =
                (2 * (1 + k ^ 2)) ^ 2 := by rw [h]
    have e1 : ((3 * k ^ 2 - 1) * (1 + (3 * p2 - k) * (3 * q2 - k))) ^ 2 =
              (3 * k ^ 2 - 1) ^ 2 * (1 + (3 * p2 - k) * (3 * q2 - k)) ^ 2 := by ring
    have e2 : (2 * (1 + k ^ 2)) ^ 2 = 4 * (1 + k ^ 2) ^ 2 := by ring
    rw [e1, e2] at step
    linarith [step]
  -- (3k²−1)² · LHS = (3k²−1)² · RHS から (3k²−1)² ≠ 0 でキャンセル
  have h_sq_ne : (3 * k ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hd12
  have heq_scaled : (3 * k ^ 2 - 1) ^ 2 * ((3 * p2 - k) - (3 * q2 - k)) ^ 2 =
                    (3 * k ^ 2 - 1) ^ 2 * (3 * (1 + (3 * p2 - k) * (3 * q2 - k)) ^ 2) := by
    rw [h_lhs_scaled, h_rhs_scaled]
  exact mul_left_cancel₀ h_sq_ne heq_scaled

/-- Config の構成。 -/
noncomputable def mkConfig {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : Config k where
  p := mkP k
  q := mkQ k
  hOP := mkConfig_hOP hk
  hOQ := mkConfig_hOQ hk
  hPQ := mkConfig_hPQ hk

/-! ## (1) 主結果 -/

/-- 条件 (*) を満たす配置の存在範囲は k > √3/3。 -/
theorem existence_iff (k : ℝ) :
    Nonempty (Config k) ↔ Real.sqrt 3 / 3 < k := by
  refine ⟨fun ⟨cfg⟩ => forward_direction k cfg, fun hk => ⟨mkConfig hk⟩⟩

/-! ## (2) 三角形の面積 (公式) -/

/-- 接線 O-P-Q による三角形の面積（公式 S = 2 p² q² |p−q|/(3|p+q|)）。 -/
noncomputable def triArea {k : ℝ} (cfg : Config k) : ℝ :=
  2 * cfg.p ^ 2 * cfg.q ^ 2 * |cfg.p - cfg.q| / (3 * |cfg.p + cfg.q|)

/-! ### 補助: 非負実数の平方の単射性 -/

/-- a, b ≥ 0 なら a² = b² ↔ a = b。 -/
private lemma sq_eq_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 = b ^ 2 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have : (a - b) * (a + b) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp this with h1 | h2
  · linarith
  · -- a + b = 0 と a, b ≥ 0 から a = b = 0
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    linarith

/-! ### Config の補助性質 -/

lemma p_ne_zero {k : ℝ} (cfg : Config k) : cfg.p ≠ 0 := by
  intro h
  have := p_sq_pos k cfg
  rw [h] at this; norm_num at this

lemma q_ne_zero {k : ℝ} (cfg : Config k) : cfg.q ≠ 0 := by
  intro h
  have := q_sq_pos k cfg
  rw [h] at this; norm_num at this

lemma p_ne_neg_q {k : ℝ} (cfg : Config k) : cfg.p + cfg.q ≠ 0 := by
  intro h
  have hsq : cfg.p ^ 2 = cfg.q ^ 2 := by
    have hpq : cfg.p = -cfg.q := by linarith
    rw [hpq]; ring
  exact p_sq_ne_q_sq k cfg hsq

lemma p_ne_q {k : ℝ} (cfg : Config k) : cfg.p ≠ cfg.q := by
  intro h
  have : cfg.p ^ 2 = cfg.q ^ 2 := by rw [h]
  exact p_sq_ne_q_sq k cfg this

/-! ### α := mkP k, β := mkQ k の正値性と α < β -/

lemma mkP_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : 0 < mkP k := by
  unfold mkP
  apply Real.sqrt_pos.mpr
  exact div_pos (one_plus_k_sq_pos k) (three_k_add_sqrt3_pos hk)

lemma mkQ_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : 0 < mkQ k := by
  unfold mkQ
  apply Real.sqrt_pos.mpr
  exact div_pos (one_plus_k_sq_pos k) (three_k_sub_sqrt3_pos hk)

/-- mkP k < mkQ k。 -/
lemma mkP_lt_mkQ {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : mkP k < mkQ k := by
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have hsq_lt : (mkP k) ^ 2 < (mkQ k) ^ 2 := by
    rw [mkP_sq hk, mkQ_sq hk]
    apply div_lt_div_of_pos_left (one_plus_k_sq_pos k) (three_k_sub_sqrt3_pos hk)
    linarith [sqrt3_pos]
  -- (mkP k)² < (mkQ k)² から、両方正なので mkP k < mkQ k
  by_contra h_ge
  have h_ge' : mkQ k ≤ mkP k := not_lt.mp h_ge
  have : (mkQ k) ^ 2 ≤ (mkP k) ^ 2 := by nlinarith [hP_pos, hQ_pos, h_ge']
  linarith [hsq_lt]

private lemma mkP_sq_ne_mkQ_sq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (mkP k) ^ 2 ≠ (mkQ k) ^ 2 := by
  have h := mkP_lt_mkQ hk
  have hP_pos : 0 < mkP k := mkP_pos hk
  have : (mkP k) ^ 2 < (mkQ k) ^ 2 := by nlinarith [h, hP_pos]
  exact this.ne

/-! ### p², q² の値分配 -/

private lemma p_sq_val {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    cfg.p ^ 2 = (mkP k) ^ 2 ∨ cfg.p ^ 2 = (mkQ k) ^ 2 := by
  rcases p_sq_root k cfg with h | h
  · left
    rw [mkP_sq hk, eq_div_iff (three_k_add_sqrt3_pos hk).ne']
    linarith [h]
  · right
    rw [mkQ_sq hk, eq_div_iff (three_k_sub_sqrt3_pos hk).ne']
    linarith [h]

private lemma q_sq_val {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    cfg.q ^ 2 = (mkP k) ^ 2 ∨ cfg.q ^ 2 = (mkQ k) ^ 2 := by
  rcases q_sq_root k cfg with h | h
  · left
    rw [mkP_sq hk, eq_div_iff (three_k_add_sqrt3_pos hk).ne']
    linarith [h]
  · right
    rw [mkQ_sq hk, eq_div_iff (three_k_sub_sqrt3_pos hk).ne']
    linarith [h]

/-- {p², q²} = {α², β²}。 -/
private lemma pq_sq_partition {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    (cfg.p ^ 2 = (mkP k) ^ 2 ∧ cfg.q ^ 2 = (mkQ k) ^ 2) ∨
    (cfg.p ^ 2 = (mkQ k) ^ 2 ∧ cfg.q ^ 2 = (mkP k) ^ 2) := by
  have hpq_ne := p_sq_ne_q_sq k cfg
  rcases p_sq_val hk cfg with hp | hp <;> rcases q_sq_val hk cfg with hq | hq
  · exfalso; rw [hp, hq] at hpq_ne; exact hpq_ne rfl
  · left; exact ⟨hp, hq⟩
  · right; exact ⟨hp, hq⟩
  · exfalso; rw [hp, hq] at hpq_ne; exact hpq_ne rfl

/-! ### (p ± q)² の値分配 -/

private lemma pq_sq_sum {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    cfg.p ^ 2 + cfg.q ^ 2 = (mkP k) ^ 2 + (mkQ k) ^ 2 := by
  rcases pq_sq_partition hk cfg with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]
  · rw [hp, hq]; ring

private lemma pq_sq_prod {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    cfg.p ^ 2 * cfg.q ^ 2 = (mkP k) ^ 2 * (mkQ k) ^ 2 := by
  rcases pq_sq_partition hk cfg with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]
  · rw [hp, hq]; ring

private lemma pq_pm {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    cfg.p * cfg.q = mkP k * mkQ k ∨ cfg.p * cfg.q = -(mkP k * mkQ k) := by
  have hsq : (cfg.p * cfg.q) ^ 2 = (mkP k * mkQ k) ^ 2 := by
    have h1 : (cfg.p * cfg.q) ^ 2 = cfg.p ^ 2 * cfg.q ^ 2 := by ring
    have h2 : (mkP k * mkQ k) ^ 2 = (mkP k) ^ 2 * (mkQ k) ^ 2 := by ring
    rw [h1, h2]; exact pq_sq_prod hk cfg
  have h : (cfg.p * cfg.q - mkP k * mkQ k) * (cfg.p * cfg.q + mkP k * mkQ k) = 0 := by
    have : (cfg.p * cfg.q - mkP k * mkQ k) * (cfg.p * cfg.q + mkP k * mkQ k) =
           (cfg.p * cfg.q) ^ 2 - (mkP k * mkQ k) ^ 2 := by ring
    rw [this, hsq]; ring
  rcases mul_eq_zero.mp h with h1 | h1
  · left; linarith [h1]
  · right; linarith [h1]

/-- {(p − q)², (p + q)²} = {(α+β)², (β−α)²}。 -/
private lemma pq_diff_sum_partition {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    ((cfg.p - cfg.q) ^ 2 = (mkQ k - mkP k) ^ 2 ∧
       (cfg.p + cfg.q) ^ 2 = (mkP k + mkQ k) ^ 2) ∨
    ((cfg.p - cfg.q) ^ 2 = (mkP k + mkQ k) ^ 2 ∧
       (cfg.p + cfg.q) ^ 2 = (mkQ k - mkP k) ^ 2) := by
  have hsum := pq_sq_sum hk cfg
  rcases pq_pm hk cfg with hpq | hpq
  · left; refine ⟨?_, ?_⟩
    · have h1 : (cfg.p - cfg.q) ^ 2 = cfg.p ^ 2 + cfg.q ^ 2 - 2 * (cfg.p * cfg.q) := by ring
      rw [h1, hsum, hpq]; ring
    · have h1 : (cfg.p + cfg.q) ^ 2 = cfg.p ^ 2 + cfg.q ^ 2 + 2 * (cfg.p * cfg.q) := by ring
      rw [h1, hsum, hpq]; ring
  · right; refine ⟨?_, ?_⟩
    · have h1 : (cfg.p - cfg.q) ^ 2 = cfg.p ^ 2 + cfg.q ^ 2 - 2 * (cfg.p * cfg.q) := by ring
      rw [h1, hsum, hpq]; ring
    · have h1 : (cfg.p + cfg.q) ^ 2 = cfg.p ^ 2 + cfg.q ^ 2 + 2 * (cfg.p * cfg.q) := by ring
      rw [h1, hsum, hpq]; ring

/-- |p − q|, |p + q| の値分配。 -/
private lemma pq_abs_partition {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    (|cfg.p - cfg.q| = mkQ k - mkP k ∧ |cfg.p + cfg.q| = mkP k + mkQ k) ∨
    (|cfg.p - cfg.q| = mkP k + mkQ k ∧ |cfg.p + cfg.q| = mkQ k - mkP k) := by
  have hPQ_lt := mkP_lt_mkQ hk
  have hP_pos := mkP_pos hk
  have hQ_pos := mkQ_pos hk
  have hQminusP_pos : 0 < mkQ k - mkP k := by linarith
  have hsum_pos : 0 < mkP k + mkQ k := by linarith
  rcases pq_diff_sum_partition hk cfg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; refine ⟨?_, ?_⟩
    · have h_abs_sq : |cfg.p - cfg.q| ^ 2 = (mkQ k - mkP k) ^ 2 := by
        rw [sq_abs]; exact h1
      exact (sq_eq_iff_of_nonneg (abs_nonneg _) hQminusP_pos.le).mp h_abs_sq
    · have h_abs_sq : |cfg.p + cfg.q| ^ 2 = (mkP k + mkQ k) ^ 2 := by
        rw [sq_abs]; exact h2
      exact (sq_eq_iff_of_nonneg (abs_nonneg _) hsum_pos.le).mp h_abs_sq
  · right; refine ⟨?_, ?_⟩
    · have h_abs_sq : |cfg.p - cfg.q| ^ 2 = (mkP k + mkQ k) ^ 2 := by
        rw [sq_abs]; exact h1
      exact (sq_eq_iff_of_nonneg (abs_nonneg _) hsum_pos.le).mp h_abs_sq
    · have h_abs_sq : |cfg.p + cfg.q| ^ 2 = (mkQ k - mkP k) ^ 2 := by
        rw [sq_abs]; exact h2
      exact (sq_eq_iff_of_nonneg (abs_nonneg _) hQminusP_pos.le).mp h_abs_sq

/-! ### 面積の二値性 -/

/-- 同符号での面積 S₋。 -/
noncomputable def areaMinus (k : ℝ) : ℝ :=
  2 * (mkP k) ^ 2 * (mkQ k) ^ 2 * (mkQ k - mkP k) / (3 * (mkP k + mkQ k))

/-- 異符号での面積 S₊。 -/
noncomputable def areaPlus (k : ℝ) : ℝ :=
  2 * (mkP k) ^ 2 * (mkQ k) ^ 2 * (mkP k + mkQ k) / (3 * (mkQ k - mkP k))

/-- 任意の Config の面積は areaMinus k または areaPlus k のいずれか。 -/
theorem triArea_eq {k : ℝ} (hk : Real.sqrt 3 / 3 < k) (cfg : Config k) :
    triArea cfg = areaMinus k ∨ triArea cfg = areaPlus k := by
  unfold triArea areaMinus areaPlus
  have hp2q2 : cfg.p ^ 2 * cfg.q ^ 2 = (mkP k) ^ 2 * (mkQ k) ^ 2 := pq_sq_prod hk cfg
  rcases pq_abs_partition hk cfg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [h1, h2]
    -- 2 * cfg.p^2 * cfg.q^2 を 2 * mkP^2 * mkQ^2 に置換
    have : 2 * cfg.p ^ 2 * cfg.q ^ 2 = 2 * (mkP k) ^ 2 * (mkQ k) ^ 2 := by linarith [hp2q2]
    rw [this]
  · right
    rw [h1, h2]
    have : 2 * cfg.p ^ 2 * cfg.q ^ 2 = 2 * (mkP k) ^ 2 * (mkQ k) ^ 2 := by linarith [hp2q2]
    rw [this]

/-! ### 両方の面積を達成する Config の存在 -/

/-- 同符号 (p = mkP k, q = mkQ k) の Config。-/
noncomputable def cfgMinus {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : Config k := mkConfig hk

/-- 異符号 (p = mkP k, q = -mkQ k) の Config。-/
noncomputable def cfgPlus {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : Config k where
  p := mkP k
  q := -(mkQ k)
  hOP := mkConfig_hOP hk
  hOQ := by
    have hslope_eq : slopeAt k (-(mkQ k)) = slopeAt k (mkQ k) := by
      unfold slopeAt; ring
    rw [hslope_eq]; exact mkConfig_hOQ hk
  hPQ := by
    have hslope_eq : slopeAt k (-(mkQ k)) = slopeAt k (mkQ k) := by
      unfold slopeAt; ring
    rw [hslope_eq]; exact mkConfig_hPQ hk

private lemma cfgMinus_p {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : (cfgMinus hk).p = mkP k := rfl
private lemma cfgMinus_q {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : (cfgMinus hk).q = mkQ k := rfl
private lemma cfgPlus_p {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : (cfgPlus hk).p = mkP k := rfl
private lemma cfgPlus_q {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : (cfgPlus hk).q = -(mkQ k) := rfl

theorem triArea_cfgMinus {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    triArea (cfgMinus hk) = areaMinus k := by
  unfold triArea areaMinus
  rw [cfgMinus_p, cfgMinus_q]
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have h_sum : (0 : ℝ) < mkP k + mkQ k := by linarith
  have h_diff : (0 : ℝ) < mkQ k - mkP k := by linarith [mkP_lt_mkQ hk]
  rw [show |mkP k - mkQ k| = mkQ k - mkP k from by
        rw [abs_sub_comm]; exact abs_of_pos h_diff,
      show |mkP k + mkQ k| = mkP k + mkQ k from abs_of_pos h_sum]

theorem triArea_cfgPlus {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    triArea (cfgPlus hk) = areaPlus k := by
  unfold triArea areaPlus
  rw [cfgPlus_p, cfgPlus_q]
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have h_sum : (0 : ℝ) < mkP k + mkQ k := by linarith
  have h_diff : (0 : ℝ) < mkQ k - mkP k := by linarith [mkP_lt_mkQ hk]
  have h1 : |mkP k - -(mkQ k)| = mkP k + mkQ k := by
    rw [show mkP k - -(mkQ k) = mkP k + mkQ k from by ring, abs_of_pos h_sum]
  have h2 : |mkP k + -(mkQ k)| = mkQ k - mkP k := by
    rw [show mkP k + -(mkQ k) = -(mkQ k - mkP k) from by ring, abs_neg, abs_of_pos h_diff]
  rw [h1, h2]
  have hsq : (-(mkQ k)) ^ 2 = (mkQ k) ^ 2 := by ring
  rw [hsq]

/-! ### areaMinus < areaPlus -/

theorem areaMinus_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : 0 < areaMinus k := by
  unfold areaMinus
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have h_sum : (0 : ℝ) < mkP k + mkQ k := by linarith
  have h_diff : (0 : ℝ) < mkQ k - mkP k := by linarith [mkP_lt_mkQ hk]
  positivity

theorem areaPlus_pos {k : ℝ} (hk : Real.sqrt 3 / 3 < k) : 0 < areaPlus k := by
  unfold areaPlus
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have h_sum : (0 : ℝ) < mkP k + mkQ k := by linarith
  have h_diff : (0 : ℝ) < mkQ k - mkP k := by linarith [mkP_lt_mkQ hk]
  positivity

theorem areaMinus_lt_areaPlus {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    areaMinus k < areaPlus k := by
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have h_sum_pos : (0 : ℝ) < mkP k + mkQ k := by linarith
  have h_diff_pos : (0 : ℝ) < mkQ k - mkP k := by linarith [mkP_lt_mkQ hk]
  have hd1_ne : (3 * (mkP k + mkQ k)) ≠ 0 := by positivity
  have hd2_ne : (3 * (mkQ k - mkP k)) ≠ 0 := by positivity
  -- 差を計算: areaPlus − areaMinus = 8 α³ β³ / (3 (α+β)(β−α)) > 0
  have h_diff_eq : areaPlus k - areaMinus k =
      8 * (mkP k) ^ 3 * (mkQ k) ^ 3 /
        (3 * (mkP k + mkQ k) * (mkQ k - mkP k)) := by
    unfold areaPlus areaMinus
    field_simp
    ring
  have h_pos : 0 < 8 * (mkP k) ^ 3 * (mkQ k) ^ 3 /
                  (3 * (mkP k + mkQ k) * (mkQ k - mkP k)) := by
    apply div_pos
    · positivity
    · have : (0 : ℝ) < 3 * (mkP k + mkQ k) * (mkQ k - mkP k) := by
        have h1 : (0 : ℝ) < 3 * (mkP k + mkQ k) := by linarith
        exact mul_pos h1 h_diff_pos
      exact this
  linarith [h_diff_eq, h_pos]

/-! ### M = areaPlus k, m = areaMinus k -/

theorem areaPlus_is_max {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (∀ cfg : Config k, triArea cfg ≤ areaPlus k) ∧
    (∃ cfg : Config k, triArea cfg = areaPlus k) := by
  refine ⟨?_, ⟨cfgPlus hk, triArea_cfgPlus hk⟩⟩
  intro cfg
  rcases triArea_eq hk cfg with h | h
  · rw [h]; exact (areaMinus_lt_areaPlus hk).le
  · rw [h]

theorem areaMinus_is_min {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (∀ cfg : Config k, areaMinus k ≤ triArea cfg) ∧
    (∃ cfg : Config k, triArea cfg = areaMinus k) := by
  refine ⟨?_, ⟨cfgMinus hk, triArea_cfgMinus hk⟩⟩
  intro cfg
  rcases triArea_eq hk cfg with h | h
  · rw [h]
  · rw [h]; exact (areaMinus_lt_areaPlus hk).le

/-! ### M = 4m ⇔ k = 5√3/12 -/

/-- M = 4m ⇔ (mkP + mkQ)² = 4(mkQ − mkP)² ⇔ mkQ = 3 mkP。-/
private lemma four_aMinus_eq_aPlus_iff {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    areaPlus k = 4 * areaMinus k ↔ mkQ k = 3 * mkP k := by
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have h_sum_pos : (0 : ℝ) < mkP k + mkQ k := by linarith
  have h_diff_pos : (0 : ℝ) < mkQ k - mkP k := by linarith [mkP_lt_mkQ hk]
  have hd_prod_pos : (0 : ℝ) < 3 * (mkQ k - mkP k) * (mkP k + mkQ k) := by positivity
  constructor
  · intro h
    -- 差で書き換え: areaPlus − 4·areaMinus = 0
    have h_zero : areaPlus k - 4 * areaMinus k = 0 := by linarith
    -- 公約: areaPlus − 4 areaMinus = 2α²β² · ((α+β)² − 4(β−α)²) / (3(β−α)(α+β))
    have h_expr : areaPlus k - 4 * areaMinus k =
                  2 * (mkP k) ^ 2 * (mkQ k) ^ 2 *
                  ((mkP k + mkQ k) ^ 2 - 4 * (mkQ k - mkP k) ^ 2) /
                  (3 * (mkQ k - mkP k) * (mkP k + mkQ k)) := by
      unfold areaPlus areaMinus
      field_simp
    rw [h_expr] at h_zero
    -- 分子 = 0 (分母正)
    have h_num_zero : 2 * (mkP k) ^ 2 * (mkQ k) ^ 2 *
                      ((mkP k + mkQ k) ^ 2 - 4 * (mkQ k - mkP k) ^ 2) = 0 := by
      have h_or := div_eq_zero_iff.mp h_zero
      rcases h_or with h | h
      · exact h
      · exfalso; linarith [hd_prod_pos]
    have hαβ_pos : (0 : ℝ) < 2 * (mkP k) ^ 2 * (mkQ k) ^ 2 := by positivity
    have h_factor : (mkP k + mkQ k) ^ 2 - 4 * (mkQ k - mkP k) ^ 2 = 0 := by
      have h_or := mul_eq_zero.mp h_num_zero
      rcases h_or with h | h
      · exfalso; linarith [hαβ_pos]
      · exact h
    have hkey : (mkP k + mkQ k) ^ 2 = 4 * (mkQ k - mkP k) ^ 2 := by linarith [h_factor]
    have hsqrt : mkP k + mkQ k = 2 * (mkQ k - mkP k) := by
      have h_sq : (mkP k + mkQ k) ^ 2 = (2 * (mkQ k - mkP k)) ^ 2 := by
        rw [hkey]; ring
      have h_pos1 : 0 ≤ mkP k + mkQ k := h_sum_pos.le
      have h_pos2 : 0 ≤ 2 * (mkQ k - mkP k) := by linarith
      exact (sq_eq_iff_of_nonneg h_pos1 h_pos2).mp h_sq
    linarith [hsqrt]
  · intro h
    -- mkQ = 3 mkP を代入: areaPlus = 12 mkP^4, areaMinus = 3 mkP^4 ⇒ areaPlus = 4 areaMinus
    unfold areaPlus areaMinus
    rw [h]
    have h2P_ne : 2 * mkP k ≠ 0 := by positivity
    have h4P_ne : 4 * mkP k ≠ 0 := by positivity
    field_simp
    ring

/-- mkQ k = 3 mkP k ⇔ k = 5√3/12。-/
private lemma mkQ_eq_three_mkP_iff {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    mkQ k = 3 * mkP k ↔ k = 5 * Real.sqrt 3 / 12 := by
  have hP_pos : 0 < mkP k := mkP_pos hk
  have hQ_pos : 0 < mkQ k := mkQ_pos hk
  have hP_sq := mkP_sq hk
  have hQ_sq := mkQ_sq hk
  have hd_add_pos : 0 < 3 * k + Real.sqrt 3 := three_k_add_sqrt3_pos hk
  have hd_sub_pos : 0 < 3 * k - Real.sqrt 3 := three_k_sub_sqrt3_pos hk
  have h1pk_pos : 0 < 1 + k ^ 2 := one_plus_k_sq_pos k
  constructor
  · intro h
    have hsq : (mkQ k) ^ 2 = 9 * (mkP k) ^ 2 := by rw [h]; ring
    rw [hP_sq, hQ_sq] at hsq
    -- (1+k²)/(3k−√3) = 9·(1+k²)/(3k+√3)
    -- 両辺 ×(3k−√3)(3k+√3): (1+k²)(3k+√3) = 9(1+k²)(3k−√3)
    have hsq' : (1 + k ^ 2) * (3 * k + Real.sqrt 3) =
                9 * (1 + k ^ 2) * (3 * k - Real.sqrt 3) := by
      have h_clear : (1 + k ^ 2) / (3 * k - Real.sqrt 3) * ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) =
                     9 * ((1 + k ^ 2) / (3 * k + Real.sqrt 3)) *
                     ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) := by rw [hsq]
      rw [show (1 + k ^ 2) / (3 * k - Real.sqrt 3) * ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) =
            (1 + k ^ 2) * (3 * k + Real.sqrt 3) *
            ((3 * k - Real.sqrt 3) / (3 * k - Real.sqrt 3)) from by
              field_simp,
          show 9 * ((1 + k ^ 2) / (3 * k + Real.sqrt 3)) *
                ((3 * k + Real.sqrt 3) * (3 * k - Real.sqrt 3)) =
                9 * (1 + k ^ 2) * (3 * k - Real.sqrt 3) *
                ((3 * k + Real.sqrt 3) / (3 * k + Real.sqrt 3)) from by
              field_simp,
          div_self hd_sub_pos.ne', div_self hd_add_pos.ne'] at h_clear
      linarith [h_clear]
    -- (1+k²) でキャンセル: 3k+√3 = 9(3k−√3)
    have hkey : 3 * k + Real.sqrt 3 = 9 * (3 * k - Real.sqrt 3) := by
      have h3 : (1 + k ^ 2) * (3 * k + Real.sqrt 3) =
                (1 + k ^ 2) * (9 * (3 * k - Real.sqrt 3)) := by linarith [hsq']
      exact mul_left_cancel₀ h1pk_pos.ne' h3
    -- 3k+√3 = 27k−9√3 ⇒ 24k = 10√3 ⇒ k = 5√3/12
    linarith [hkey]
  · intro h
    rw [h]
    have hk5 : Real.sqrt 3 / 3 < 5 * Real.sqrt 3 / 12 := by
      have hs := sqrt3_pos
      nlinarith [hs]
    have hP_pos' : 0 < mkP (5 * Real.sqrt 3 / 12) := mkP_pos hk5
    have hQ_pos' : 0 < mkQ (5 * Real.sqrt 3 / 12) := mkQ_pos hk5
    -- (mkQ)² = 9 (mkP)² を直接計算
    have hsq_rel : (mkQ (5 * Real.sqrt 3 / 12)) ^ 2 =
                   9 * (mkP (5 * Real.sqrt 3 / 12)) ^ 2 := by
      rw [mkQ_sq hk5, mkP_sq hk5]
      have hd1 : 3 * (5 * Real.sqrt 3 / 12) + Real.sqrt 3 = 9 * Real.sqrt 3 / 4 := by ring
      have hd2_eq : 3 * (5 * Real.sqrt 3 / 12) - Real.sqrt 3 = Real.sqrt 3 / 4 := by ring
      rw [hd1, hd2_eq]
      have hs_pos := sqrt3_pos
      have hs_ne : Real.sqrt 3 ≠ 0 := hs_pos.ne'
      have h9_ne : (9 : ℝ) * Real.sqrt 3 / 4 ≠ 0 := by positivity
      have h_div : Real.sqrt 3 / 4 ≠ 0 := by positivity
      field_simp
    have h3P_pos : 0 < 3 * mkP (5 * Real.sqrt 3 / 12) := by linarith
    have hsq_eq : (mkQ (5 * Real.sqrt 3 / 12)) ^ 2 =
                  (3 * mkP (5 * Real.sqrt 3 / 12)) ^ 2 := by
      rw [hsq_rel]; ring
    exact (sq_eq_iff_of_nonneg hQ_pos'.le h3P_pos.le).mp hsq_eq

/-- areaPlus k = 4 · areaMinus k ⇔ k = 5√3/12。 -/
theorem areaPlus_eq_four_areaMinus_iff {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    areaPlus k = 4 * areaMinus k ↔ k = 5 * Real.sqrt 3 / 12 := by
  rw [four_aMinus_eq_aPlus_iff hk, mkQ_eq_three_mkP_iff hk]

/-- (2) 主結果: M = 4m ⇔ k = 5√3/12。 -/
theorem main_part2 {k : ℝ} (hk : Real.sqrt 3 / 3 < k) :
    (∃ M m : ℝ,
      (∀ cfg : Config k, triArea cfg ≤ M) ∧
      (∃ cfg : Config k, triArea cfg = M) ∧
      (∀ cfg : Config k, m ≤ triArea cfg) ∧
      (∃ cfg : Config k, triArea cfg = m) ∧
      M = 4 * m) ↔
    k = 5 * Real.sqrt 3 / 12 := by
  constructor
  · rintro ⟨M, m, hM_ub, hM_ach, hm_lb, hm_ach, hMm⟩
    have hM_eq : M = areaPlus k := by
      obtain ⟨cfgM, hcfgM⟩ := hM_ach
      have h1 : triArea cfgM ≤ areaPlus k := (areaPlus_is_max hk).1 cfgM
      have h2 : triArea (cfgPlus hk) ≤ M := hM_ub _
      rw [triArea_cfgPlus hk] at h2
      linarith [h1, h2, hcfgM.symm.le, hcfgM.symm.ge]
    have hm_eq : m = areaMinus k := by
      obtain ⟨cfgm, hcfgm⟩ := hm_ach
      have h1 : areaMinus k ≤ triArea cfgm := (areaMinus_is_min hk).1 cfgm
      have h2 : m ≤ triArea (cfgMinus hk) := hm_lb _
      rw [triArea_cfgMinus hk] at h2
      linarith [h1, h2, hcfgm.symm.le, hcfgm.symm.ge]
    rw [hM_eq, hm_eq] at hMm
    exact (areaPlus_eq_four_areaMinus_iff hk).mp hMm
  · intro hk_val
    refine ⟨areaPlus k, areaMinus k, ?_, ?_, ?_, ?_, ?_⟩
    · exact (areaPlus_is_max hk).1
    · exact (areaPlus_is_max hk).2
    · exact (areaMinus_is_min hk).1
    · exact (areaMinus_is_min hk).2
    · exact (areaPlus_eq_four_areaMinus_iff hk).mpr hk_val

end Common2026.T_Q4
