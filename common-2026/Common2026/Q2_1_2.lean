/-
第2問 〔1〕(2)

  (i) 2 次関数 y = f(x) が次の条件1を満たすとする。
    条件1: −3 ≤ x ≤ 0 において
      - x = −1 で最大値 3 をとる
      - x = −3 で最小値 −5 をとる
  このとき、f(x) のグラフの頂点の座標は (−1, 3) であり、
    f(x) = −2x² − 4x + 1 (= −2(x + 1)² + 3)
  である。

  (ii) 2 次関数 y = g(x) について、a > 0 を定数とし、g の [0, a] における
  最大値 M、最小値 m が次の条件2を満たすとする。
    条件2:
      - 0 < a < 3 ならば m > −2、a ≥ 3 ならば m = −2
      - 0 < a ≤ 6 ならば M = 7、a > 6 ならば M > 7
  このとき g(x) = x² − 6x + 7 (= (x − 3)² − 2) であり、
  グラフは下に凸、頂点 (3, −2)、g(0) = g(6) = 7 となる。

  (iii) 2 次関数 y = h(x) について、b ∈ ℝ を定数とし、h の [b−1, b+1] における
  最大値 M が次の条件3を満たすとする。
    条件3:
      - 1 ≤ b ≤ 7 ならば M ≥ 0
      - b < 1 または b > 7 ならば M < 0
  このとき h のグラフと x 軸の共有点は x = 2 と x = 6 である (h は一意でない)。
  本ファイルでは具体例として h(x) = −(x − 2)(x − 6) (上に凸、頂点 (4, 4)) を
  取り、これが条件3 を満たし、根が 2, 6 であることを確認する。

  ここでは各小問の答えが条件を満たすこと (forward 方向のみ) を検証する。

  注: 条件 1, 2 から 2 次関数を一意に導く方向の証明 (条件を満たす f, g は
  …に限る) は、頂点位置を「内点での極値」条件から決定する連続的な極値の
  議論を要し、Lean では極限論法 (∀ ε > 0, … から従う等式) が必要になる。
  本ファイルではその方向は扱わず、答えが条件を満たすことのみ確認する。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Common2026.Q2_1_2

def f (x : ℝ) : ℝ := -2 * x ^ 2 - 4 * x + 1

/-- 頂点形: f(x) = −2(x + 1)² + 3。よって頂点は (−1, 3)。 -/
theorem f_vertex_form (x : ℝ) : f x = -2 * (x + 1) ^ 2 + 3 := by
  unfold f; ring

/-- −3 ≤ x ≤ 0 において、x = −1 で最大値 3 をとる。 -/
theorem max_value :
    f (-1) = 3 ∧ ∀ x : ℝ, -3 ≤ x → x ≤ 0 → f x ≤ 3 := by
  refine ⟨by unfold f; norm_num, ?_⟩
  intro x _ _
  rw [f_vertex_form]
  have h : 0 ≤ (x + 1) ^ 2 := sq_nonneg _
  linarith

/-- −3 ≤ x ≤ 0 において、x = −3 で最小値 −5 をとる。 -/
theorem min_value :
    f (-3) = -5 ∧ ∀ x : ℝ, -3 ≤ x → x ≤ 0 → -5 ≤ f x := by
  refine ⟨by unfold f; norm_num, ?_⟩
  intro x hx_low hx_high
  unfold f
  -- −5 ≤ −2x² − 4x + 1  ⟺  (x + 3)(1 − x) ≥ 0、これは [−3, 0] で成立。
  have h : 0 ≤ (x + 3) * (1 - x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

/-! ## (ii) 条件 2 — g(x) = x² − 6x + 7 -/

def g (x : ℝ) : ℝ := x ^ 2 - 6 * x + 7

/-- 頂点形: g(x) = (x − 3)² − 2。係数 1 > 0 より下に凸、頂点 (3, −2)。 -/
theorem g_vertex_form (x : ℝ) : g x = (x - 3) ^ 2 - 2 := by
  unfold g; ring

/-- 0 < a < 3 のとき [0, a] における最小値は g(a)、その値は −2 より大きい。 -/
theorem min_lt3 (a : ℝ) (_ha_pos : 0 < a) (ha_lt : a < 3) :
    (∀ x : ℝ, 0 ≤ x → x ≤ a → g a ≤ g x) ∧ g a > -2 := by
  refine ⟨?_, ?_⟩
  · intro x hx0 hxa
    -- g(x) − g(a) = (x − a)(x + a − 6); 0 ≤ x ≤ a < 3 より x + a − 6 < 0、x − a ≤ 0
    rw [g_vertex_form, g_vertex_form]
    -- (a − 3)² − 2 ≤ (x − 3)² − 2 ⟺ (a − 3)² ≤ (x − 3)²
    -- 0 ≤ x ≤ a < 3 のとき 3 − a ≤ 3 − x かつ 0 < 3 − a, 0 < 3 − x
    have h1 : 3 - a ≤ 3 - x := by linarith
    have h2 : 0 ≤ 3 - a := by linarith
    have h3 : 0 ≤ 3 - x := by linarith
    have h4 : (3 - a) ^ 2 ≤ (3 - x) ^ 2 := by nlinarith [sq_nonneg (3 - a), sq_nonneg (3 - x)]
    have e1 : (a - 3) ^ 2 = (3 - a) ^ 2 := by ring
    have e2 : (x - 3) ^ 2 = (3 - x) ^ 2 := by ring
    linarith [e1.symm ▸ e2.symm ▸ h4]
  · -- g(a) − (−2) = (a − 3)² > 0 (a ≠ 3)
    rw [g_vertex_form]
    have h1 : a - 3 ≠ 0 := by intro h; linarith
    have h2 : 0 < (a - 3) ^ 2 := by positivity
    linarith

/-- a ≥ 3 のとき [0, a] における最小値は −2 で、x = 3 で達成される。 -/
theorem min_ge3 (a : ℝ) (ha : a ≥ 3) :
    (∀ x : ℝ, 0 ≤ x → x ≤ a → -2 ≤ g x) ∧
    (g 3 = -2 ∧ (0 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ _
    rw [g_vertex_form]
    have : 0 ≤ (x - 3) ^ 2 := sq_nonneg _
    linarith
  · unfold g; norm_num
  · norm_num
  · exact ha

/-- 0 < a ≤ 6 のとき [0, a] における最大値は 7 で、x = 0 で達成される。 -/
theorem max_le6 (a : ℝ) (ha_pos : 0 < a) (ha_le : a ≤ 6) :
    (∀ x : ℝ, 0 ≤ x → x ≤ a → g x ≤ 7) ∧
    (g 0 = 7 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx0 hxa
    -- g(x) ≤ 7 ⟺ (x − 3)² ≤ 9 ⟺ |x − 3| ≤ 3 ⟺ 0 ≤ x ≤ 6
    rw [g_vertex_form]
    have hx6 : x ≤ 6 := by linarith
    -- (x − 3)² ≤ 9 from 0 ≤ x ≤ 6
    have h_low : -3 ≤ x - 3 := by linarith
    have h_high : x - 3 ≤ 3 := by linarith
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 6), sq_nonneg x]
  · unfold g; norm_num
  · norm_num
  · linarith

/-- a > 6 のとき [0, a] における最大値は 7 より大きい (具体的に x = a が反例)。 -/
theorem max_gt6 (a : ℝ) (ha : a > 6) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ a ∧ g x > 7 := by
  refine ⟨a, ?_, le_refl _, ?_⟩
  · linarith
  · -- g(a) − 7 = a² − 6a = a(a − 6) > 0
    unfold g
    nlinarith

/-! ## (iii) 条件 3 — h(x) = −(x − 2)(x − 6) の例 -/

def h (x : ℝ) : ℝ := -(x - 2) * (x - 6)

/-- 因数分解形から h(2) = 0, h(6) = 0。よって x 軸との共有点の x 座標は 2 と 6。 -/
theorem h_roots : h 2 = 0 ∧ h 6 = 0 := by
  refine ⟨?_, ?_⟩ <;> · unfold h; ring

/-- 頂点形: h(x) = 4 − (x − 4)²。係数 −1 < 0 より上に凸、頂点 (4, 4)。 -/
theorem h_vertex_form (x : ℝ) : h x = 4 - (x - 4) ^ 2 := by
  unfold h; ring

/-- h(x) ≥ 0 ⟺ 2 ≤ x ≤ 6 (上に凸で根 2, 6)。本ファイルでは「2 ≤ x ≤ 6 ⇒ h x ≥ 0」を使う。 -/
private lemma h_nonneg_of_mem (x : ℝ) (hx2 : 2 ≤ x) (hx6 : x ≤ 6) : 0 ≤ h x := by
  unfold h
  -- −(x − 2)(x − 6) = (x − 2)(6 − x) ≥ 0
  have h1 : 0 ≤ x - 2 := by linarith
  have h2 : 0 ≤ 6 - x := by linarith
  nlinarith

/-- 1 ≤ b ≤ 7 のとき、[b−1, b+1] の中に h(x) ≥ 0 となる x が存在する。 -/
theorem cond3_holds_left (b : ℝ) (hb1 : 1 ≤ b) (hb7 : b ≤ 7) :
    ∃ x : ℝ, b - 1 ≤ x ∧ x ≤ b + 1 ∧ 0 ≤ h x := by
  -- 場合分け: b ≤ 3 / 3 ≤ b ≤ 5 / b ≥ 5
  rcases le_or_gt b 3 with hb3 | hb3
  · -- 1 ≤ b ≤ 3 のとき x = b + 1 を取る (b + 1 ∈ [2, 4] ⊂ [2, 6])
    refine ⟨b + 1, by linarith, le_refl _, ?_⟩
    apply h_nonneg_of_mem <;> linarith
  · rcases le_or_gt b 5 with hb5 | hb5
    · -- 3 < b ≤ 5 のとき x = 4 を取る (|b − 4| ≤ 1 とは限らないが…)
      -- 3 < b ≤ 5 で 4 − b ∈ [−1, 1) ⊂ [−1, 1] なので 4 ∈ [b − 1, b + 1]
      refine ⟨4, by linarith, by linarith, ?_⟩
      apply h_nonneg_of_mem <;> linarith
    · -- 5 < b ≤ 7 のとき x = b − 1 を取る (b − 1 ∈ (4, 6] ⊂ [2, 6])
      refine ⟨b - 1, le_refl _, by linarith, ?_⟩
      apply h_nonneg_of_mem <;> linarith

/-- b < 1 または b > 7 のとき、[b−1, b+1] の任意の x で h(x) < 0。 -/
theorem cond3_holds_right (b : ℝ) (hb : b < 1 ∨ b > 7) :
    ∀ x : ℝ, b - 1 ≤ x → x ≤ b + 1 → h x < 0 := by
  intro x hx_low hx_high
  rcases hb with hb | hb
  · -- b < 1: x ≤ b + 1 < 2、x − 2 < 0, x − 6 < 0、−(x−2)(x−6) < 0
    have hx2 : x < 2 := by linarith
    have hx6 : x < 6 := by linarith
    unfold h
    -- (x − 2) < 0, (x − 6) < 0、よって (x−2)(x−6) > 0、−(x−2)(x−6) < 0
    have h1 : x - 2 < 0 := by linarith
    have h2 : x - 6 < 0 := by linarith
    nlinarith
  · -- b > 7: x ≥ b − 1 > 6、x − 2 > 0, x − 6 > 0
    have hx6 : x > 6 := by linarith
    have hx2 : x > 2 := by linarith
    unfold h
    have h1 : 0 < x - 2 := by linarith
    have h2 : 0 < x - 6 := by linarith
    nlinarith

end Common2026.Q2_1_2
