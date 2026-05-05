/-
第1問 [2](2)

  点 O を中心とする半径 6 の円 O が、線分 PQ 上の P, Q と異なる点 M で
  線分 PQ に接している。P, Q を通る円 O の接線で、直線 PQ と異なるものを
  引き、円との接点をそれぞれ K, L とする。直線 PK と QL の交点を R、
  ∠KPM = P, ∠LQM = Q とおく。

  接線の性質より:
    PM = PK, QM = QL    (外部点からの 2 接線)
    OM = OK = OL = 6    (半径)
    ∠M = ∠K = π/2 (PMOK), ∠M = ∠L = π/2 (QLOM)
  四角形 PMOK は対角線 PO により直角三角形 △PMO ≅ △PKO に分割される。

  (i) PK = 12, QL = 9 (R は直線 PQ に関して O と同じ側):
        四角形 PMOK の面積 = 72,
        sin P = 4/5, sin Q = 12/13, PR : QR = 15 : 13, RL = 21/2,
        PR = 45/2, QR = 39/2, PQ = 21.
  (ii) PK = 4√2, QL = 3√2 (R は反対側):
         sin P = 12√2/17, sin Q = 2√2/3, RL = 21√2,
         PR = 17√2, QR = 18√2, PQ = 7√2.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace Common2026.Q1_2_2

/-- 「凧型」四角形 (PM = PK, OM = OK, ∠M = ∠K = π/2) の面積方程式
    `PM · OM = ((PM² + OM²) / 2) · sin P` から sin P を解いた式。
    左辺は対角線 PO で 2 つの直角三角形に分割した面積、
    右辺は Q1_2_1 の `area_sum_eq` (= ①) を A = ∠P, C = ∠O,
    AB = PM, AD = PK = PM, BC = MO = OM, CD = OK = OM として適用したもの。 -/
theorem sin_eq_of_kite_area
    (PM OM sP : ℝ) (h_pos : 0 < PM^2 + OM^2)
    (h_area : PM * OM = ((PM^2 + OM^2) / 2) * sP) :
    sP = 2 * PM * OM / (PM^2 + OM^2) := by
  have hne : PM^2 + OM^2 ≠ 0 := ne_of_gt h_pos
  field_simp
  linarith

namespace part_i

/-- 四角形 PMOK の面積 = △PMO + △PKO = 2·(½·12·6) = 72。 -/
theorem area_PMOK : ((1/2) * 12 * 6 + (1/2) * 12 * 6 : ℝ) = 72 := by norm_num

/-- 面積 = 72 と ① から sin P = 4/5。 -/
theorem sin_P {sP : ℝ}
    (h : (12 : ℝ) * 6 = ((12^2 + 6^2 : ℝ) / 2) * sP) :
    sP = 4/5 := by
  have eq := sin_eq_of_kite_area 12 6 sP (by norm_num) h
  rw [eq]; norm_num

/-- 同様に四角形 QLOM から sin Q = 12/13。 -/
theorem sin_Q {sQ : ℝ}
    (h : (9 : ℝ) * 6 = ((9^2 + 6^2 : ℝ) / 2) * sQ) :
    sQ = 12/13 := by
  have eq := sin_eq_of_kite_area 9 6 sQ (by norm_num) h
  rw [eq]; norm_num

/-- 正弦定理 QR/sin P = PR/sin Q から PR : QR = sin Q : sin P = 15 : 13。 -/
theorem PR_QR_ratio : (13 : ℝ) * (12/13) = 15 * (4/5) := by norm_num

/-- R は O と同じ側にあるので K は P と R の間、L は Q と R の間。
    PR = PK + KR, QR = QL + LR で KR = LR (= t) (R から円への 2 接線)。
    PR : QR = 15 : 13 を 13(12 + t) = 15(9 + t) として解いて t = 21/2。
    したがって RL = 21/2。 -/
theorem RL {t : ℝ} (h : 13 * (12 + t) = 15 * (9 + t)) : t = 21/2 := by linarith

/-- △PQR の辺長:
      PR = PK + KR = 12 + 21/2 = 45/2,
      QR = QL + LR = 9 + 21/2 = 39/2,
      PQ = PM + MQ = 12 + 9 = 21. -/
theorem sides :
    (12 + 21/2 : ℝ) = 45/2 ∧ (9 + 21/2 : ℝ) = 39/2 ∧ (12 + 9 : ℝ) = 21 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

end part_i

namespace part_ii

/-- PM² = 32 (PM = 4√2), OM = 6 のとき面積方程式から sin P = 3·PM/17。
    PM = 4√2 を代入すれば sin P = 12√2/17。 -/
theorem sin_P {PM sP : ℝ} (hPM : PM^2 = 32)
    (h : PM * 6 = ((PM^2 + 6^2 : ℝ) / 2) * sP) :
    sP = 3 * PM / 17 := by
  have h_pos : (0 : ℝ) < PM^2 + 6^2 := by rw [hPM]; norm_num
  have eq := sin_eq_of_kite_area PM 6 sP h_pos h
  rw [eq, hPM]; ring

/-- QM² = 18 (QM = 3√2), OM = 6 のとき sin Q = 2·QM/9。
    QM = 3√2 を代入すれば sin Q = 6√2/9 = 2√2/3。 -/
theorem sin_Q {QM sQ : ℝ} (hQM : QM^2 = 18)
    (h : QM * 6 = ((QM^2 + 6^2 : ℝ) / 2) * sQ) :
    sQ = 2 * QM / 9 := by
  have h_pos : (0 : ℝ) < QM^2 + 6^2 := by rw [hQM]; norm_num
  have eq := sin_eq_of_kite_area QM 6 sQ h_pos h
  rw [eq, hQM]; ring

/-- 接線等式 PR + PK = QR + QL (R が O と反対側、P, Q がそれぞれ R-K, R-L の間)。
    `s` は √2。 -/
theorem tangent_eq (s : ℝ) : 17 * s + 4 * s = 18 * s + 3 * s := by ring

/-- 比 PR : QR = 17 : 18。 -/
theorem ratio_eq (s : ℝ) : 18 * (17 * s) = 17 * (18 * s) := by ring

/-- RL = QR + QL = 21 √2。 -/
theorem RL_eq (s : ℝ) : 18 * s + 3 * s = 21 * s := by ring

/-- PQ = PM + MQ = 4 √2 + 3 √2 = 7 √2。 -/
theorem PQ_eq (s : ℝ) : 4 * s + 3 * s = 7 * s := by ring

end part_ii

end Common2026.Q1_2_2
