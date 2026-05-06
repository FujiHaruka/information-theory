/-
2B 第5問 (統計的な推測)

  ある自治体では地域知識を問う資格試験 (200 点満点) を毎年実施しており,
  120 点以上を合格としている。

  (1) 今年の受験者全体の得点 X は正規分布 N(116, 25²) に従う。
      Y = (X - 116) / 25 とおくと Y は標準正規分布 N(0,1) に従う
      (空欄ア = ① (X - 116) / 25)。
      P(X ≥ 120) = P(Y ≥ 0.16) ≈ 0.5 - 0.0636 = 0.4364
      よって空欄イ = ⑤ 0.44。

  (2) A 地域の合格率を p とし、合否を表す確率変数 W_i を定義 (合格 1, 不合格 0)。

    (i) ベルヌーイ分布 W_i:
        E(W_i) = 0·(1-p) + 1·p = p (空欄ウ = ⓪ p)
        V(W_i) = (0-p)²(1-p) + (1-p)²·p = p(1-p) (空欄エ = ③ p(1-p))

    (ii) 標本平均 W̄ ~ N(p, p(1-p)/n) (近似的に, 空欄オ = ⑦ p(1-p)/n)。
        帰無仮説 p = 0.4 のもとで n = 400, σ(W̄) = √(0.4·0.6/400) = √6/100
        (空欄カ = ② √6/100)。
        z = (0.46 - 0.4) / (√6/100) = 6/√6 = √6 ≈ 2.45。
        P(W̄ ≥ 0.46) = P(Y ≥ 2.45) ≈ 0.5 - 0.4929 = 0.0071
        (空欄キ = ② 0.0071)。
        0.71% < 5% なので帰無仮説は棄却される (空欄ク = ① 小さいから棄却される)。
        よって合格率は 0.4 より高いと判断できる (空欄ケ = ⓪ 高いと判断できる)。

  (3) n = 100 のとき、σ(W̄) = √(0.24/100) = √6/50。
      z = (0.46 - 0.4) / (√6/50) = 3/√6 = √6/2 ≈ 1.225。
      P(W̄ ≥ 0.46) = P(Y ≥ 1.225) ≈ 0.5 - 0.3888 = 0.1112 = 11.12%。
      11.12% > 5% なので帰無仮説は棄却されない
      (空欄コ = ① 大きい, 空欄サ = ① 棄却されない)。

  本ファイルでは正規分布表に基づく数値選択 (どの選択肢を選ぶか) は
  形式化対象外として上記 docstring に記述するに留め、形式化可能な
  代数恒等式のみを theorem として定義する。
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Common2026.B_Q5

/-! ## (1) 標準化 -/

/-- X = 116 + 25·Y ⇔ Y = (X - 116)/25 -/
theorem standardize (X Y : ℝ) :
    X = 116 + 25 * Y ↔ Y = (X - 116) / 25 := by
  constructor
  · intro h; rw [h]; ring
  · intro h; rw [h]; ring

/-! ## (2)(i) ベルヌーイ分布の期待値・分散 -/

/-- 期待値 E(W) = 0·(1-p) + 1·p = p -/
theorem bernoulli_expectation (p : ℝ) :
    0 * (1 - p) + 1 * p = p := by ring

/-- 分散 V(W) = (0-p)²·(1-p) + (1-p)²·p = p(1-p) -/
theorem bernoulli_variance (p : ℝ) :
    (0 - p)^2 * (1 - p) + (1 - p)^2 * p = p * (1 - p) := by ring

/-! ## (2)(ii) σ(W̄) と z 値の代数計算 (n = 400, p = 0.4) -/

/-- σ²(W̄) = p(1-p)/n。p = 0.4, n = 400 で σ² = 6/10000。 -/
theorem variance_value : (0.4 : ℝ) * (1 - 0.4) / 400 = 6 / 10000 := by norm_num

/-- σ(W̄) = √6 / 100 -/
theorem sd_value :
    Real.sqrt ((0.4 : ℝ) * (1 - 0.4) / 400) = Real.sqrt 6 / 100 := by
  rw [variance_value]
  rw [show (6 / 10000 : ℝ) = 6 * (1/100)^2 by norm_num]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/100)]
  ring

/-- z 値 = (0.46 - 0.4) / (√6/100) = √6 -/
theorem z_value :
    (0.46 - 0.4) / (Real.sqrt 6 / 100) = Real.sqrt 6 := by
  have h6 : (0:ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 6 * Real.sqrt 6 = 6 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 6)
  rw [eq_comm, eq_div_iff (by positivity)]
  field_simp
  linarith [hsq]

/-! ## (3) n = 100 のときの σ(W̄) と z 値 -/

/-- σ²(W̄) = p(1-p)/n。p = 0.4, n = 100 で σ² = 6/2500。 -/
theorem variance_value_100 : (0.4 : ℝ) * (1 - 0.4) / 100 = 6 / 2500 := by norm_num

/-- σ(W̄) = √6 / 50 -/
theorem sd_value_100 :
    Real.sqrt ((0.4 : ℝ) * (1 - 0.4) / 100) = Real.sqrt 6 / 50 := by
  rw [variance_value_100]
  rw [show (6 / 2500 : ℝ) = 6 * (1/50)^2 by norm_num]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/50)]
  ring

/-- z 値 = (0.46 - 0.4) / (√6/50) = √6/2 -/
theorem z_value_100 :
    (0.46 - 0.4) / (Real.sqrt 6 / 50) = Real.sqrt 6 / 2 := by
  have h6 : (0:ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 6 * Real.sqrt 6 = 6 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 6)
  rw [eq_comm, div_eq_div_iff (by norm_num) (by positivity)]
  field_simp
  linarith [hsq]

end Common2026.B_Q5
