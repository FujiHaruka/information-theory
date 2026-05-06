/-
第3問 (図形)

  AB = AC = 10, BC = 12 の二等辺三角形 ABC について
    I: △ABC の内心
    G: △IBC の重心
    P: G を通り平面 ABC に垂直な直線上の点 (G ≠ P)
    D: 直線 AI と辺 BC の交点 (BC の中点; AD は中線・高さ・∠A の二等分線)
    E: 辺 PA 上の点で ∠PED = ∠PID

  (1) 数値計算
      - BI は ∠ABC を二等分 (内心の定義)
      - AD = √(10² − 6²) = 8 (高さ)
      - AI : ID = (AB + AC) : BC = 20 : 12 = 5 : 3 → AI = 5, ID = 3
      - 4 点 E, I, D, P が同一円周上
        (∠PED = ∠PID から PD を共通弦とする弧上の円周角条件)
      - 方べき: AE · AP = AI · AD = 5 · 8 = 40

  (2) 体積 V₁, V₂ (3D 幾何; 形式化対象外)

      仮定 1: IF : FP = 3 : 2 から PE : EA, AP, V₁ を求める。
      仮定 2: IF : FP = 1 : 3 から V₂, V₂ : V₁ を求める。

      これらは多変数の比の関係と 3D 体積計算で、Lean の素朴な実数演算では
      点・面・直線などの 3D 幾何構造を組み立てる必要があり、本ファイルでは
      形式化を断念する (docstring に問題内容のみを記す)。

  本ファイルでは (1) の数値部分のみを実数の算術として形式化する。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.A_Q3

/-- 二等辺三角形の中線の長さ AD。
    AB = AC = 10, BC = 12 の二等辺三角形で D を BC の中点とすると
    AD² = AB² − BD² = 100 − 36 = 64、ゆえに AD = 8。 -/
theorem AD_squared : (10 : ℝ)^2 - 6^2 = 8^2 := by norm_num

/-- 内心の AI : ID 比。AI : ID = (AB + AC) : BC = 20 : 12 = 5 : 3。
    AD = AI + ID = 8 と組み合わせて AI = 5, ID = 3。 -/
theorem AI_ID_lengths
    (AI ID : ℝ) (h_ratio : 3 * AI = 5 * ID) (h_sum : AI + ID = 8) :
    AI = 5 ∧ ID = 3 := by
  refine ⟨?_, ?_⟩ <;> linarith

/-- 方べきの定理: 4 点 E, I, D, P が同一円周上にあるとき、
    A から見て AE · AP = AI · AD。AI · AD = 5 · 8 = 40。 -/
theorem AE_AP_value : (5 : ℝ) * 8 = 40 := by norm_num

end Common2026.A_Q3
