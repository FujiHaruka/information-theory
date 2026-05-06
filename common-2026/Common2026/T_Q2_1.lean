/-
東大 2026 第2問 (1)

  正の整数 n に対し、座標平面上の 3n 個の格子点
    S_n = {(x, y) ∈ ℤ² | 1 ≤ x ≤ 3, 1 ≤ y ≤ n}
  から相異なる 3 点を等確率で選ぶ。3 点が三角形をなす確率を p_n とする。

  (1) p_5 を求めよ。

  答え: p_5 = 412 / 455

  方針:
    総選び方 = C(15, 3) = 455
    同一直線上の 3 点 = (縦) + (横) + (斜め)
      縦 (x = c の列に 3 点): 3 · C(5, 3) = 30
      横 + 斜め (各列に 1 点ずつ; y が等差数列):
        パラメータ (y₀, y₂) ∈ {1..5}² で y₀ + y₂ が偶数
        偶 2 個・奇 3 個 ⇒ 同パリティ対 = 2² + 3² = 13
        うち横 (y₀ = y₂) は 5、斜め本体 = 8
      合計 30 + 5 + 8 = 43
    三角形 = 455 − 43 = 412
    p_5 = 412 / 455

  実装上は `Pt n := Fin 3 × Fin n` を点の型とし、3 元集合の同一直線判定を
  クロス積 (= 行列式) で定義する。共通定義 (`Pt`, `coll3`, `IsCollinear` etc.)
  はこのファイルに置き、(2) では本ファイルを import する。
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace Common2026.T_Q2_1

/-! ### 共通定義 -/

abbrev Pt (n : ℕ) := Fin 3 × Fin n

/-- 3 点 a, b, c が (順序つきで) 同一直線上にある: クロス積条件。 -/
def coll3 {n : ℕ} (a b c : Pt n) : Prop :=
  ((b.1.val : ℤ) - a.1.val) * ((c.2.val : ℤ) - a.2.val) =
    ((c.1.val : ℤ) - a.1.val) * ((b.2.val : ℤ) - a.2.val)

instance {n : ℕ} (a b c : Pt n) : Decidable (coll3 a b c) := by
  unfold coll3; infer_instance

/-- 3 点集合 s が同一直線上 (= 順序つきの coll3 を満たす相異なる 3 点に展開できる)。 -/
def IsCollinear {n : ℕ} (s : Finset (Pt n)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ s = {a, b, c} ∧ coll3 a b c

instance {n : ℕ} (s : Finset (Pt n)) : Decidable (IsCollinear s) := by
  unfold IsCollinear; infer_instance

/-- 全 3 元部分集合 -/
def allTriples (n : ℕ) : Finset (Finset (Pt n)) :=
  (Finset.univ : Finset (Pt n)).powersetCard 3

/-- 同一直線上の 3 元部分集合 -/
def collTriples (n : ℕ) : Finset (Finset (Pt n)) :=
  (allTriples n).filter IsCollinear

/-- 三角形をなす 3 元部分集合 -/
def triangleTriples (n : ℕ) : Finset (Finset (Pt n)) :=
  (allTriples n).filter (fun s => ¬ IsCollinear s)

/-- 全選び方の数 = C(3n, 3)。 -/
theorem allTriples_card (n : ℕ) : (allTriples n).card = (3 * n).choose 3 := by
  show ((Finset.univ : Finset (Pt n)).powersetCard 3).card = (3 * n).choose 3
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]

/-- 同一直線 + 三角形 = 全部。 -/
theorem coll_add_triangle_eq_all (n : ℕ) :
    (collTriples n).card + (triangleTriples n).card = (allTriples n).card := by
  unfold triangleTriples collTriples
  exact Finset.card_filter_add_card_filter_not _

/-! ### n = 5 の場合: p_5 = 412/455 -/

/-- n = 5 の同一直線 3 点組は 43 個。`decide` で計算。 -/
theorem collTriples_5_card : (collTriples 5).card = 43 := by
  decide

theorem allTriples_5_card : (allTriples 5).card = 455 := by
  rw [allTriples_card]; decide

theorem triangleTriples_5_card : (triangleTriples 5).card = 412 := by
  have h := coll_add_triangle_eq_all 5
  rw [collTriples_5_card, allTriples_5_card] at h
  omega

/-- 主結果: p_5 = 412 / 455。 -/
theorem p_5 :
    ((triangleTriples 5).card : ℚ) / (allTriples 5).card = 412 / 455 := by
  rw [triangleTriples_5_card, allTriples_5_card]
  norm_num

end Common2026.T_Q2_1
