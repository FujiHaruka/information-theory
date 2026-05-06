/-
2B 第6問 (選択問題) ベクトル

  平面上に △ABC と点 M がある。

  (1) 等式 MP = MA + 2MB - MC を満たす点 P を考える。図1の正三角形 △ABC
      および正六角形 DEFGCA の位置関係において:
      ・M が A と一致するとき, P は □ア□ と一致する。
      ・M が D と一致するとき, P は □イ□ と一致する。
      (図形依存・選択肢問題のため形式化対象外。)

  (2) a, b, c を実数とする。等式
        MP = a·MA + b·MB + c·MC      ……②
      を満たす点 P を考える。② の両辺を A を始点とするベクトルで表すと、
        左辺 MP = AP - AM     (□ウ□ = ② AP - AM)
        右辺 a·MA + b·MB + c·MC
            = b·AB + c·AC + (-a-b-c)·AM
              (□エ□ = b, □オ□ = c, □カ□ = -a-b-c)
      よって ② は
        AP = b·AB + c·AC + (1-a-b-c)·AM
      と変形でき (□キ□ = b, □ク□ = c, □ケ□ = 1-a-b-c)、
      M の位置によらず P の位置が変わらない必要十分条件は
        a + b + c = 1   (□コ□ = ⑦)
      である。

  (3) 図形・選択肢に依存する小問のため形式化対象外。

  本ファイルでは (2) の代数的本質、すなわち
    P - M = a(A-M) + b(B-M) + c(C-M)
  という条件下で
    P - A = b(B-A) + c(C-A) + (1-a-b-c)(M-A)
  であることを示し、a + b + c = 1 のとき P が M に依らず定まることを示す。
-/

import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

namespace Common2026.B_Q6

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- ② の右辺の展開:
    `a·(A-M) + b·(B-M) + c·(C-M) = b·(B-A) + c·(C-A) + (-(a+b+c))·(M-A)`。 -/
theorem rhs_expand (A B C M : V) (a b c : ℝ) :
    a • (A - M) + b • (B - M) + c • (C - M)
      = b • (B - A) + c • (C - A) + (-(a + b + c)) • (M - A) := by
  module

/-- 主結果: 仮定 `P - M = a(A-M) + b(B-M) + c(C-M)` のもとで
    `P - A = b(B-A) + c(C-A) + (1 - a - b - c)(M-A)`。 -/
theorem AP_formula (A B C M P : V) (a b c : ℝ)
    (h : P - M = a • (A - M) + b • (B - M) + c • (C - M)) :
    P - A = b • (B - A) + c • (C - A) + (1 - a - b - c) • (M - A) := by
  have hPA : P - A = (P - M) + (M - A) := by module
  rw [hPA, h, rhs_expand]
  module

/-- M に依らず P が定まる十分条件: `a + b + c = 1` のとき
    `P - A = b·(B-A) + c·(C-A)` (M を含まない式)。 -/
theorem M_invariant (A B C M P : V) (a b c : ℝ)
    (h : P - M = a • (A - M) + b • (B - M) + c • (C - M))
    (hsum : a + b + c = 1) :
    P - A = b • (B - A) + c • (C - A) := by
  have key := AP_formula A B C M P a b c h
  have hzero : (1 - a - b - c : ℝ) = 0 := by linarith
  rw [hzero] at key
  rw [key]
  module

end Common2026.B_Q6
