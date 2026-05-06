/-
東大 2026 第2問

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
  クロス積 (= 行列式) で定義する。

(2) m を 2 以上の整数とする。p_{2m} を求めよ。

  答え: p_{2m} = m(16m − 7) / ((6m − 1)(3m − 1))

  方針:
    n = 2m とする。
    総選び方 = C(6m, 3) = 2m(6m − 1)(3m − 1)
    同一直線 = 縦 + 横斜め (= 各列に 1 点ずつかつ y が等差数列)
      縦: 3 · C(2m, 3) = 2m(m − 1)(2m − 1)
      横斜め: (y₀, y₂) ∈ Fin 2m × Fin 2m で y₀ + y₂ が偶数
        偶 m 個・奇 m 個 ⇒ 同パリティ対 = m² + m² = 2m²
    同一直線 = 2m(m − 1)(2m − 1) + 2m² = 2m(2m² − 2m + 1)
    三角形 = 2m(6m − 1)(3m − 1) − 2m(2m² − 2m + 1) = 2m²(16m − 7)
    p_{2m} = 2m²(16m − 7) / (2m(6m − 1)(3m − 1)) = m(16m − 7) / ((6m − 1)(3m − 1))

  Strategy:
    `IsCollinear s` ↔ `s ∈ vertTriples n` ∨ `s ∈ lineTriples n` (and disjoint)
      vertTriples: 全 3 点が同じ x を持つ
      lineTriples: 各列に 1 点ずつ + y が等差数列 (横線も含む)

    各々を image として定義 → bijection で個数計算。
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Common2026.T_Q2

/-! ## 共通定義 -/

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

/-! ## (1) n = 5 の場合: p_5 = 412/455 -/

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

/-! ## (2) `coll3` の補助補題 -/

/-- coll3 は a と b の交換で不変。 -/
private lemma coll3_swap_ab {n : ℕ} {a b c : Pt n} (h : coll3 a b c) : coll3 b a c := by
  unfold coll3 at h ⊢
  linear_combination -h

/-- coll3 は b と c の交換で不変。 -/
private lemma coll3_swap_bc {n : ℕ} {a b c : Pt n} (h : coll3 a b c) : coll3 a c b := by
  unfold coll3 at h ⊢
  linear_combination -h

/-- coll3 は a と c の交換で不変。 -/
private lemma coll3_swap_ac {n : ℕ} {a b c : Pt n} (h : coll3 a b c) : coll3 c b a := by
  unfold coll3 at h ⊢
  linear_combination -h

/-- 巡回置換: coll3 a b c → coll3 b c a。 -/
private lemma coll3_rot_bca {n : ℕ} {a b c : Pt n} (h : coll3 a b c) : coll3 b c a :=
  coll3_swap_bc (coll3_swap_ab h)

/-- 巡回置換: coll3 a b c → coll3 c a b。 -/
private lemma coll3_rot_cab {n : ℕ} {a b c : Pt n} (h : coll3 a b c) : coll3 c a b :=
  coll3_swap_ab (coll3_swap_bc h)


/-- 全 3 点の x 座標が等しいなら同一直線。 -/
private lemma coll3_of_same_first {n : ℕ} (a b c : Pt n)
    (hab : a.1 = b.1) (hac : a.1 = c.1) : coll3 a b c := by
  unfold coll3
  have h1 : ((b.1.val : ℤ) - a.1.val) = 0 := by
    rw [show b.1 = a.1 from hab.symm]; ring
  have h2 : ((c.1.val : ℤ) - a.1.val) = 0 := by
    rw [show c.1 = a.1 from hac.symm]; ring
  rw [h1, h2]; ring

/-- a.1 = b.1 ≠ c.1 かつ a ≠ b, b ≠ c のとき同一直線でない。 -/
private lemma not_coll3_of_two_same_first {n : ℕ} (a b c : Pt n)
    (hab1 : a.1 = b.1) (hac1 : a.1 ≠ c.1) (hab : a ≠ b) :
    ¬ coll3 a b c := by
  intro h
  unfold coll3 at h
  have hb1 : ((b.1.val : ℤ) - a.1.val) = 0 := by
    rw [show b.1 = a.1 from hab1.symm]; ring
  rw [hb1] at h
  -- 0 * _ = (c.1 - a.1) * (b.2 - a.2)
  rw [zero_mul] at h
  -- 0 = (c.1 - a.1) * (b.2 - a.2)
  have hc_ne : ((c.1.val : ℤ) - a.1.val) ≠ 0 := by
    intro he
    apply hac1
    apply Fin.ext
    linarith [Int.toNat_natCast (c.1.val), Int.toNat_natCast (a.1.val)]
  -- so b.2 - a.2 = 0
  have hb2 : ((b.2.val : ℤ) - a.2.val) = 0 := by
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hc_ne
    · exact h'
  -- so b.2 = a.2
  have : a.2 = b.2 := by
    apply Fin.ext
    have : (b.2.val : ℤ) = a.2.val := by linarith
    exact_mod_cast this.symm
  -- combined with a.1 = b.1, gives a = b
  apply hab
  exact Prod.ext hab1 this

/-! ### 3 元集合と allTriples の補助 -/

/-- 異なる 3 点 a, b, c を持つ Finset。`{a, b, c}` のカードが 3。 -/
private lemma triple_card_eq_three {n : ℕ} (a b c : Pt n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset (Pt n)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]),
      Finset.card_singleton]

/-- 異なる 3 点が同一直線上にあるなら、3 元集合は collTriples に属する。 -/
private lemma triple_mem_collTriples_of_coll3 {n : ℕ} (a b c : Pt n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : coll3 a b c) :
    ({a, b, c} : Finset (Pt n)) ∈ collTriples n := by
  rw [collTriples, Finset.mem_filter]
  refine ⟨?_, a, ?_, b, ?_, c, ?_, hab, hac, hbc, rfl, h⟩
  · rw [allTriples, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, triple_card_eq_three a b c hab hac hbc⟩
  · simp
  · simp
  · simp

/-! ### 縦線の 3 点組 -/

/-- 縦線の 3 点組: 全点が同じ x を持つ。 -/
def vertTriples (n : ℕ) : Finset (Finset (Pt n)) :=
  ((Finset.univ : Finset (Fin 3)) ×ˢ
    ((Finset.univ : Finset (Fin n)).powersetCard 3)).image
    (fun p => p.2.image (fun y => (p.1, y)))

/-- (c, y₁), (c, y₂), (c, y₃) は同一直線。 -/
private lemma coll3_same_col {n : ℕ} (c : Fin 3) (y₁ y₂ y₃ : Fin n) :
    coll3 ((c, y₁) : Pt n) (c, y₂) (c, y₃) := by
  unfold coll3
  simp

theorem vertTriples_subset_coll (n : ℕ) : vertTriples n ⊆ collTriples n := by
  intro s hs
  rw [vertTriples, Finset.mem_image] at hs
  obtain ⟨⟨c, ys⟩, hp, rfl⟩ := hs
  rw [Finset.mem_product, Finset.mem_powersetCard] at hp
  obtain ⟨_, _, hys_card⟩ := hp
  rw [Finset.card_eq_three] at hys_card
  obtain ⟨y₁, y₂, y₃, h12, h13, h23, rfl⟩ := hys_card
  -- ys.image (Prod.mk c) = {(c, y₁), (c, y₂), (c, y₃)}
  have heq : (({y₁, y₂, y₃} : Finset (Fin n)).image (fun y => (c, y))) =
             ({(c, y₁), (c, y₂), (c, y₃)} : Finset (Pt n)) := by
    simp [Finset.image_insert, Finset.image_singleton]
  rw [heq]
  refine triple_mem_collTriples_of_coll3 _ _ _ ?_ ?_ ?_ (coll3_same_col c y₁ y₂ y₃)
  · simp [h12]
  · simp [h13]
  · simp [h23]

private lemma prod_mk_injective {α β : Type*} (a : α) :
    Function.Injective (fun b : β => (a, b)) := by
  intro x y h
  exact (Prod.mk.injEq a x a y).mp h |>.2

theorem vertTriples_card (n : ℕ) : (vertTriples n).card = 3 * n.choose 3 := by
  unfold vertTriples
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · -- InjOn
    rintro ⟨c, ys⟩ hp ⟨c', ys'⟩ hp' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ,
               true_and, Finset.mem_coe, Finset.mem_powersetCard,
               Finset.subset_univ] at hp hp'
    have hys_card : ys.card = 3 := hp
    have hys'_card : ys'.card = 3 := hp'
    have hys_pos : 0 < ys.card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hys_pos
    -- h, after beta-reducing the projection, says ys.image (·, c) = ys'.image (·, c')
    have h' : ys.image (fun y => ((c, y) : Pt n)) = ys'.image (fun y => ((c', y) : Pt n)) := h
    have hin : ((c, y) : Pt n) ∈ ys'.image (fun y' => ((c', y') : Pt n)) := by
      rw [← h']; exact Finset.mem_image_of_mem _ hy
    rw [Finset.mem_image] at hin
    obtain ⟨y', _, hyy'⟩ := hin
    -- hyy' : (c', y') = (c, y)
    have hcc : c' = c := (Prod.mk.injEq c' y' c y).mp hyy' |>.1
    subst hcc
    have hyy : ys = ys' := Finset.image_injective (prod_mk_injective c') h'
    rw [hyy]

/-! ### 横斜め線の 3 点組 (各列に 1 点ずつ + y が等差数列) -/

/-- (y₀, y₂) ∈ Fin n × Fin n で y₀ + y₂ が偶数なるもの。 -/
def lineParam (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => (p.1.val + p.2.val) % 2 = 0)

private lemma midY_lt {n : ℕ} (p : Fin n × Fin n) :
    (p.1.val + p.2.val) / 2 < n := by
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  omega

/-- 中点 y₁ = (y₀ + y₂) / 2 (y₀ + y₂ が偶数のときに y₁ が AP の中項)。 -/
def midY {n : ℕ} (p : Fin n × Fin n) : Fin n :=
  ⟨(p.1.val + p.2.val) / 2, midY_lt p⟩

/-- (y₀, y₂) → {(0, y₀), (1, midY), (2, y₂)} -/
def lineMap {n : ℕ} (p : Fin n × Fin n) : Finset (Pt n) :=
  ({((0 : Fin 3), p.1), ((1 : Fin 3), midY p), ((2 : Fin 3), p.2)} : Finset (Pt n))

/-- 各列に 1 点ずつ + AP な 3 点組 (横線含む)。 -/
def lineTriples (n : ℕ) : Finset (Finset (Pt n)) :=
  (lineParam n).image lineMap

private lemma lineMap_injective {n : ℕ} : Function.Injective (lineMap (n := n)) := by
  rintro ⟨y0, y2⟩ ⟨y0', y2'⟩ h
  unfold lineMap at h
  -- h : {(0, y0), (1, midY (y0, y2)), (2, y2)} = {(0, y0'), (1, midY (y0', y2')), (2, y2')}
  have h0 : ((0, y0) : Pt n) ∈
      ({((0 : Fin 3), y0'), ((1 : Fin 3), midY (y0', y2')), ((2 : Fin 3), y2')}
        : Finset (Pt n)) := by
    rw [← h]; simp
  have h2 : ((2, y2) : Pt n) ∈
      ({((0 : Fin 3), y0'), ((1 : Fin 3), midY (y0', y2')), ((2 : Fin 3), y2')}
        : Finset (Pt n)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h0 h2
  have hy0 : y0 = y0' := by
    rcases h0 with ⟨_, h⟩ | ⟨hb, _⟩ | ⟨hc, _⟩
    · exact h
    · exact absurd hb (by decide)
    · exact absurd hc (by decide)
  have hy2 : y2 = y2' := by
    rcases h2 with ⟨ha, _⟩ | ⟨hb, _⟩ | ⟨_, h⟩
    · exact absurd ha (by decide)
    · exact absurd hb (by decide)
    · exact h
  exact Prod.ext hy0 hy2

theorem lineTriples_card (n : ℕ) :
    (lineTriples n).card = (lineParam n).card := by
  unfold lineTriples
  exact Finset.card_image_of_injective _ lineMap_injective

/-- (0, y₀), (1, mid), (2, y₂) は y₀ + y₂ が偶数なら同一直線。 -/
private lemma coll3_lineMap {n : ℕ} (p : Fin n × Fin n) (hp : (p.1.val + p.2.val) % 2 = 0) :
    coll3 ((0, p.1) : Pt n) (1, midY p) (2, p.2) := by
  have hmid : 2 * (midY p).val = p.1.val + p.2.val := by
    show 2 * ((p.1.val + p.2.val) / 2) = p.1.val + p.2.val
    omega
  unfold coll3
  show ((1 : Fin 3).val - (0 : Fin 3).val : ℤ) * ((p.2.val : ℤ) - p.1.val) =
    ((2 : Fin 3).val - (0 : Fin 3).val : ℤ) * ((midY p).val - p.1.val)
  have h1 : ((1 : Fin 3).val : ℤ) = 1 := by decide
  have h0 : ((0 : Fin 3).val : ℤ) = 0 := by decide
  have h2 : ((2 : Fin 3).val : ℤ) = 2 := by decide
  rw [h0, h1, h2]
  have : 2 * ((midY p).val : ℤ) = p.1.val + p.2.val := by exact_mod_cast hmid
  linarith

theorem lineTriples_subset_coll (n : ℕ) : lineTriples n ⊆ collTriples n := by
  intro s hs
  rw [lineTriples, Finset.mem_image] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  rw [lineParam, Finset.mem_filter] at hp
  obtain ⟨_, hp_even⟩ := hp
  -- s = lineMap p = {(0, p.1), (1, midY p), (2, p.2)}
  unfold lineMap
  refine triple_mem_collTriples_of_coll3 _ _ _ ?_ ?_ ?_ (coll3_lineMap p hp_even)
  · -- (0, p.1) ≠ (1, midY p): different first coords
    intro h
    have : ((0 : Fin 3) : Fin 3) = 1 := (Prod.mk.injEq _ _ _ _).mp h |>.1
    exact absurd this (by decide)
  · intro h
    have : ((0 : Fin 3) : Fin 3) = 2 := (Prod.mk.injEq _ _ _ _).mp h |>.1
    exact absurd this (by decide)
  · intro h
    have : ((1 : Fin 3) : Fin 3) = 2 := (Prod.mk.injEq _ _ _ _).mp h |>.1
    exact absurd this (by decide)

/-! ### 縦と (横斜め) は素 -/

theorem vert_disjoint_line (n : ℕ) :
    Disjoint (vertTriples n) (lineTriples n) := by
  rw [Finset.disjoint_left]
  intro s hs1 hs2
  rw [vertTriples, Finset.mem_image] at hs1
  obtain ⟨⟨c, ys⟩, _, rfl⟩ := hs1
  rw [lineTriples, Finset.mem_image] at hs2
  obtain ⟨p, _, hLM⟩ := hs2
  -- ys.image (·, c) = lineMap p = {(0, p.1), (1, midY p), (2, p.2)}
  have h0 : ((0 : Fin 3), p.1) ∈ ys.image (fun y => ((c, y) : Pt n)) := by
    rw [← hLM]; unfold lineMap; simp
  have h1 : ((1 : Fin 3), midY p) ∈ ys.image (fun y => ((c, y) : Pt n)) := by
    rw [← hLM]; unfold lineMap; simp
  rw [Finset.mem_image] at h0 h1
  obtain ⟨_, _, h0eq⟩ := h0
  obtain ⟨_, _, h1eq⟩ := h1
  -- h0eq : (c, _) = (0, p.1) ⇒ c = 0
  -- h1eq : (c, _) = (1, midY p) ⇒ c = 1
  have hc0 : c = 0 := (Prod.mk.injEq _ _ _ _).mp h0eq |>.1
  have hc1 : c = 1 := (Prod.mk.injEq _ _ _ _).mp h1eq |>.1
  exact absurd (hc0.symm.trans hc1) (by decide)

/-! ### 同一直線 = 縦 ∪ 横斜め -/

/-- 全 3 点が同じ x なら vertTriples に属する。 -/
private lemma mem_vertTriples_of_same_col {n : ℕ} (s : Finset (Pt n)) (c : Fin 3)
    (h_card : s.card = 3) (h_all : ∀ p ∈ s, p.1 = c) :
    s ∈ vertTriples n := by
  refine Finset.mem_image.mpr ⟨(c, s.image Prod.snd), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨Finset.mem_univ _, Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injOn]
    · exact h_card
    · intro p hp p' hp' hp_eq
      have h1 : p.1 = p'.1 := by rw [h_all p hp, h_all p' hp']
      exact Prod.ext h1 hp_eq
  · show (s.image Prod.snd).image (fun y => (c, y)) = s
    ext p
    refine ⟨?_, ?_⟩
    · rintro hp
      rw [Finset.mem_image] at hp
      obtain ⟨y, hy, rfl⟩ := hp
      rw [Finset.mem_image] at hy
      obtain ⟨p', hp', rfl⟩ := hy
      have h1 : p'.1 = c := h_all p' hp'
      have : ((c, p'.2) : Pt n) = p' := by
        cases p'; simp at h1; subst h1; rfl
      rw [this]; exact hp'
    · intro hp
      rw [Finset.mem_image]
      refine ⟨p.2, Finset.mem_image_of_mem _ hp, ?_⟩
      have h1 : p.1 = c := h_all p hp
      cases p; simp at h1; subst h1; rfl

/-- 3 元集合 {a, b, c} の置換不変性。 -/
private lemma triple_set_perm_acb {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = ({a, c, b} : Finset α) := by
  ext x; simp; tauto

private lemma triple_set_perm_bac {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = ({b, a, c} : Finset α) := by
  ext x; simp; tauto

private lemma triple_set_perm_bca {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = ({b, c, a} : Finset α) := by
  ext x; simp; tauto

private lemma triple_set_perm_cab {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = ({c, a, b} : Finset α) := by
  ext x; simp; tauto

private lemma triple_set_perm_cba {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α) = ({c, b, a} : Finset α) := by
  ext x; simp; tauto

/-- Fin 3 の任意の値は 0, 1, 2 のいずれか。 -/
private lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have := (by decide : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2)
  exact this x

/-- 3 点とも異なる x を持つ場合: x ∈ {0, 1, 2} の置換。各列の点を見つけ、
    かつ任意の coll3 a b c から coll3 p₀ p₁ p₂ を導くマップを返す。 -/
private lemma exists_col_match {n : ℕ} {a b c : Pt n}
    (hab1 : a.1 ≠ b.1) (hac1 : a.1 ≠ c.1) (hbc1 : b.1 ≠ c.1) :
    ∃ p₀ p₁ p₂ : Pt n,
      ({a, b, c} : Finset (Pt n)) = ({p₀, p₁, p₂} : Finset (Pt n)) ∧
      p₀.1 = 0 ∧ p₁.1 = 1 ∧ p₂.1 = 2 ∧
      (coll3 a b c → coll3 p₀ p₁ p₂) := by
  rcases fin3_cases a.1 with ha | ha | ha <;>
  rcases fin3_cases b.1 with hb | hb | hb <;>
  rcases fin3_cases c.1 with hc | hc | hc
  all_goals (first
    | (exact absurd (ha.trans hb.symm) hab1)
    | (exact absurd (ha.trans hc.symm) hac1)
    | (exact absurd (hb.trans hc.symm) hbc1)
    | exact ⟨a, b, c, rfl, ha, hb, hc, id⟩
    | exact ⟨a, c, b, triple_set_perm_acb _ _ _, ha, hc, hb, coll3_swap_bc⟩
    | exact ⟨b, a, c, triple_set_perm_bac _ _ _, hb, ha, hc, coll3_swap_ab⟩
    | exact ⟨b, c, a, triple_set_perm_bca _ _ _, hb, hc, ha, coll3_rot_bca⟩
    | exact ⟨c, a, b, triple_set_perm_cab _ _ _, hc, ha, hb, coll3_rot_cab⟩
    | exact ⟨c, b, a, triple_set_perm_cba _ _ _, hc, hb, ha, coll3_swap_ac⟩)

theorem coll_eq_vert_union_line (n : ℕ) :
    collTriples n = vertTriples n ∪ lineTriples n := by
  apply Finset.Subset.antisymm
  · -- collTriples ⊆ vertTriples ∪ lineTriples
    intro s hs
    rw [collTriples, Finset.mem_filter] at hs
    obtain ⟨h_all, a, ha, b, hb, c, hc, hab, hac, hbc, rfl, hcoll⟩ := hs
    rw [Finset.mem_union]
    -- Case on first-coord pattern
    by_cases h_eq_ab : a.1 = b.1
    · by_cases h_eq_ac : a.1 = c.1
      · -- All same: vertical
        left
        apply mem_vertTriples_of_same_col _ a.1 (triple_card_eq_three a b c hab hac hbc)
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · rfl
        · exact h_eq_ab.symm
        · exact h_eq_ac.symm
      · -- a.1 = b.1 ≠ c.1: contradict coll
        exact absurd hcoll (not_coll3_of_two_same_first a b c h_eq_ab h_eq_ac hab)
    · by_cases h_eq_ac : a.1 = c.1
      · -- a.1 = c.1 ≠ b.1
        -- Use coll3_swap_bc to swap b and c, then apply not_coll3
        have h' : coll3 a c b := coll3_swap_bc hcoll
        -- Now a.1 = c.1 ≠ b.1 (with c, b swapped: original h_eq_ac, ¬h_eq_ab)
        have h_eq_ac' : a.1 ≠ b.1 := h_eq_ab
        exact absurd h' (not_coll3_of_two_same_first a c b h_eq_ac h_eq_ac' hac)
      · by_cases h_eq_bc : b.1 = c.1
        · -- b.1 = c.1, a.1 ≠ b.1, a.1 ≠ c.1
          have h' : coll3 b a c := coll3_swap_ab hcoll
          -- coll3 b a c with b.1 = c.1, but b.1 ≠ a.1
          -- not_coll3_of_two_same_first wants the 1st two with same first coord
          -- b.1 = ? we want b's first coord = first arg's first coord
          -- "first arg first = second arg first ≠ third arg first", but here we have
          -- b.1 = c.1, with first arg = b, second arg = a, third arg = c
          -- So we need: b.1 = a.1, which is FALSE.
          -- Hmm let me use coll3_swap_bc on h' instead
          have h'' : coll3 b c a := coll3_swap_bc h'
          -- Now: b.1 = c.1 ≠ a.1 (i.e., second arg's first = first arg's first ≠ third arg's first)
          -- Wait: not_coll3_of_two_same_first a b c h_eq_ab h_eq_ac hab says:
          --   "a.1 = b.1 ∧ a.1 ≠ c.1 ∧ a ≠ b → ¬ coll3 a b c"
          -- Apply with a := b, b := c, c := a:
          --   "b.1 = c.1 ∧ b.1 ≠ a.1 ∧ b ≠ c → ¬ coll3 b c a"
          have hbc1 : b.1 ≠ a.1 := fun h => h_eq_ab h.symm
          exact absurd h'' (not_coll3_of_two_same_first b c a h_eq_bc hbc1 hbc)
        · -- All distinct: lineTriples
          right
          obtain ⟨p₀, p₁, p₂, hs_eq, h0, h1, h2, hperm⟩ :=
            exists_col_match h_eq_ab h_eq_ac h_eq_bc
          have hcoll' : coll3 p₀ p₁ p₂ := hperm hcoll
          -- coll3 p₀ p₁ p₂ with p₀.1 = 0, p₁.1 = 1, p₂.1 = 2
          -- This means p₀.2.val + p₂.2.val is even and = 2 * p₁.2.val
          unfold coll3 at hcoll'
          rw [show p₀.1 = (0 : Fin 3) from h0,
              show p₁.1 = (1 : Fin 3) from h1,
              show p₂.1 = (2 : Fin 3) from h2] at hcoll'
          -- hcoll' : (1 - 0) * (p₂.2 - p₀.2) = (2 - 0) * (p₁.2 - p₀.2)
          have h01v : ((1 : Fin 3).val : ℤ) - (0 : Fin 3).val = 1 := by decide
          have h02v : ((2 : Fin 3).val : ℤ) - (0 : Fin 3).val = 2 := by decide
          rw [h01v, h02v] at hcoll'
          -- hcoll' : 1 * (p₂.2 - p₀.2) = 2 * (p₁.2 - p₀.2)
          -- Hence p₂.2.val + p₀.2.val = 2 * p₁.2.val
          have hsum : (p₀.2.val : ℤ) + p₂.2.val = 2 * p₁.2.val := by linarith
          have hsum_nat : 2 * p₁.2.val = p₀.2.val + p₂.2.val := by
            have : (2 * p₁.2.val : ℤ) = p₀.2.val + p₂.2.val := by linarith
            exact_mod_cast this
          -- So (p₀.2.val + p₂.2.val) is even
          have hsum_even : (p₀.2.val + p₂.2.val) % 2 = 0 := by omega
          -- And midY (p₀.2, p₂.2) = p₁.2
          have hmid : midY (p₀.2, p₂.2) = p₁.2 := by
            unfold midY
            apply Fin.ext
            show (p₀.2.val + p₂.2.val) / 2 = p₁.2.val
            omega
          -- Show {a, b, c} = lineMap (p₀.2, p₂.2)
          rw [lineTriples, Finset.mem_image]
          refine ⟨(p₀.2, p₂.2), ?_, ?_⟩
          · rw [lineParam, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hsum_even⟩
          · -- lineMap (p₀.2, p₂.2) = {a, b, c}
            unfold lineMap
            -- = {(0, p₀.2), (1, midY), (2, p₂.2)} = {(0, p₀.2), (1, p₁.2), (2, p₂.2)}
            rw [hmid]
            -- {(0, p₀.2), (1, p₁.2), (2, p₂.2)} = {p₀, p₁, p₂} = {a, b, c}
            have hp₀ : ((0 : Fin 3), p₀.2) = p₀ := by
              rcases p₀ with ⟨pp1, pp2⟩
              simp at h0; subst h0; rfl
            have hp₁ : ((1 : Fin 3), p₁.2) = p₁ := by
              rcases p₁ with ⟨pp1, pp2⟩
              simp at h1; subst h1; rfl
            have hp₂ : ((2 : Fin 3), p₂.2) = p₂ := by
              rcases p₂ with ⟨pp1, pp2⟩
              simp at h2; subst h2; rfl
            rw [hp₀, hp₁, hp₂]
            exact hs_eq.symm
  · -- vertTriples ∪ lineTriples ⊆ collTriples
    intro s hs
    rw [Finset.mem_union] at hs
    rcases hs with h | h
    · exact vertTriples_subset_coll n h
    · exact lineTriples_subset_coll n h

/-- 同一直線の数 = 縦 + 横斜め。 -/
theorem collTriples_card_eq (n : ℕ) :
    (collTriples n).card = (vertTriples n).card + (lineTriples n).card := by
  rw [coll_eq_vert_union_line, Finset.card_union_of_disjoint (vert_disjoint_line n)]

/-! ### Nat.choose 3 の閉形式 -/

/-- 任意の n に対して 6 · C(n, 3) = n(n-1)(n-2)。 -/
private lemma six_mul_choose_three (n : ℕ) :
    6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h_dvd : (3 : ℕ).factorial ∣ n.descFactorial 3 :=
    Nat.factorial_dvd_descFactorial _ _
  have h_choose : n.choose 3 * (3 : ℕ).factorial = n.descFactorial 3 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    exact Nat.div_mul_cancel h_dvd
  have h_fact : (3 : ℕ).factorial = 6 := rfl
  have h_desc : n.descFactorial 3 = (n - 2) * ((n - 1) * (n * 1)) := rfl
  have h6 : n.choose 3 * 6 = (n - 2) * ((n - 1) * (n * 1)) := by
    rw [← h_fact, h_choose, h_desc]
  linarith [h6]

/-! ### lineParam の濃度: n = 2m で 2m² -/

/-- evens (2m) のカード = m。 -/
private lemma evens_image_two_mul (m : ℕ) :
    ((Finset.univ : Finset (Fin (2 * m))).filter (fun y => y.val % 2 = 0)) =
    (Finset.univ : Finset (Fin m)).image
      (fun k : Fin m => (⟨2 * k.val, by have := k.isLt; omega⟩ : Fin (2 * m))) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨⟨y.val / 2, ?_⟩, ?_⟩
    · have := y.isLt; omega
    · apply Fin.ext
      show 2 * (y.val / 2) = y.val
      omega
  · rintro ⟨k, rfl⟩
    show (2 * k.val) % 2 = 0
    omega

private lemma evens_card_two_mul (m : ℕ) :
    ((Finset.univ : Finset (Fin (2 * m))).filter (fun y => y.val % 2 = 0)).card = m := by
  rw [evens_image_two_mul]
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro a b hab
    have : (2 * a.val : ℕ) = 2 * b.val := congr_arg Fin.val hab
    apply Fin.ext; omega

/-- odds (2m) のカード = m。 -/
private lemma odds_image_two_mul (m : ℕ) :
    ((Finset.univ : Finset (Fin (2 * m))).filter (fun y => y.val % 2 = 1)) =
    (Finset.univ : Finset (Fin m)).image
      (fun k : Fin m => (⟨2 * k.val + 1, by have := k.isLt; omega⟩ : Fin (2 * m))) := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨⟨y.val / 2, ?_⟩, ?_⟩
    · have := y.isLt; omega
    · apply Fin.ext
      show 2 * (y.val / 2) + 1 = y.val
      omega
  · rintro ⟨k, rfl⟩
    show (2 * k.val + 1) % 2 = 1
    omega

private lemma odds_card_two_mul (m : ℕ) :
    ((Finset.univ : Finset (Fin (2 * m))).filter (fun y => y.val % 2 = 1)).card = m := by
  rw [odds_image_two_mul]
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro a b hab
    have : (2 * a.val + 1 : ℕ) = 2 * b.val + 1 := congr_arg Fin.val hab
    apply Fin.ext; omega

/-- lineParam = (evens × evens) ∪ (odds × odds)。 -/
private lemma lineParam_eq_union (n : ℕ) :
    lineParam n =
      (((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 0)) ×ˢ
        ((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 0))) ∪
      (((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 1)) ×ˢ
        ((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 1))) := by
  ext ⟨y₀, y₂⟩
  simp only [lineParam, Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.mem_union, Finset.mem_product]
  omega

private lemma lineParam_disjoint (n : ℕ) :
    Disjoint
      (((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 0)) ×ˢ
        ((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 0)))
      (((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 1)) ×ˢ
        ((Finset.univ : Finset (Fin n)).filter (fun y => y.val % 2 = 1))) := by
  rw [Finset.disjoint_left]
  rintro ⟨y₀, y₂⟩ h1 h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at h1 h2
  omega

theorem lineParam_card_two_mul (m : ℕ) :
    (lineParam (2 * m)).card = 2 * m * m := by
  rw [lineParam_eq_union, Finset.card_union_of_disjoint (lineParam_disjoint _),
      Finset.card_product, Finset.card_product,
      evens_card_two_mul, odds_card_two_mul]
  ring

/-! ### n = 2m での主結果 -/

/-- n = 2m での総選び方: 2m(6m − 1)(3m − 1)。 -/
theorem allTriples_card_two_mul (m : ℕ) (hm : 1 ≤ m) :
    (allTriples (2 * m)).card = 2 * m * (6 * m - 1) * (3 * m - 1) := by
  rw [allTriples_card, show 3 * (2 * m) = 6 * m from by ring]
  have h6 : 6 * (6 * m).choose 3 =
      (6 * m) * (6 * m - 1) * (6 * m - 2) := six_mul_choose_three _
  rcases m with _ | k
  · omega
  · have hsub : 6 * (k + 1) - 2 = 2 * (3 * (k + 1) - 1) := by omega
    rw [hsub] at h6
    have hY : 6 * (6 * (k + 1)).choose 3 =
        6 * (2 * (k + 1) * (6 * (k + 1) - 1) * (3 * (k + 1) - 1)) := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 6) hY

/-- n = 2m での縦線の数: 2m(m − 1)(2m − 1)。 -/
theorem vertTriples_card_two_mul (m : ℕ) (hm : 1 ≤ m) :
    (vertTriples (2 * m)).card = 2 * m * (m - 1) * (2 * m - 1) := by
  rw [vertTriples_card]
  have h6 : 6 * (2 * m).choose 3 = (2 * m) * (2 * m - 1) * (2 * m - 2) :=
    six_mul_choose_three _
  rcases m with _ | k
  · omega
  · have hsub : 2 * (k + 1) - 2 = 2 * k := by omega
    have hk : (k + 1 : ℕ) - 1 = k := by omega
    rw [hsub] at h6
    rw [hk]
    -- h6 : 6 * X = 2(k+1) * (2(k+1)-1) * 2k
    -- Goal: 3 * X = 2(k+1) * k * (2(k+1)-1)
    have hY : 2 * (3 * (2 * (k + 1)).choose 3) =
        2 * (2 * (k + 1) * k * (2 * (k + 1) - 1)) := by
      linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hY

/-- n = 2m での同一直線の数: 2m(m-1)(2m-1) + 2m²。 -/
theorem collTriples_card_two_mul (m : ℕ) (hm : 1 ≤ m) :
    (collTriples (2 * m)).card =
      2 * m * (m - 1) * (2 * m - 1) + 2 * m * m := by
  rw [collTriples_card_eq, vertTriples_card_two_mul m hm,
      lineTriples_card, lineParam_card_two_mul]

/-- n = 2m での三角形の数: 2m²(16m − 7)。 -/
theorem triangleTriples_card_two_mul (m : ℕ) (hm : 1 ≤ m) :
    (triangleTriples (2 * m)).card = 2 * m * m * (16 * m - 7) := by
  have h_total := allTriples_card_two_mul m hm
  have h_coll := collTriples_card_two_mul m hm
  have h_eq := coll_add_triangle_eq_all (2 * m)
  rw [h_total, h_coll] at h_eq
  rcases m with _ | k
  · omega
  · -- Subtract: triangle = total - coll. Reduce all 'a - b' subtractions to k-form.
    have h6_5 : 6 * (k + 1) - 1 = 6 * k + 5 := by omega
    have h3_2 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
    have h2_1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have hkm : (k + 1 : ℕ) - 1 = k := by omega
    have h16_7 : 16 * (k + 1) - 7 = 16 * k + 9 := by omega
    rw [h6_5, h3_2, h2_1, hkm] at h_eq
    rw [h16_7]
    -- Polynomial identity: 2(k+1)(6k+5)(3k+2) = 2(k+1)k(2k+1) + 2(k+1)(k+1) + 2(k+1)(k+1)(16k+9)
    have h_poly :
        2 * (k + 1) * (6 * k + 5) * (3 * k + 2) =
          2 * (k + 1) * k * (2 * k + 1) + 2 * (k + 1) * (k + 1)
          + 2 * (k + 1) * (k + 1) * (16 * k + 9) := by ring
    linarith

/-- 主結果: m ≥ 2 のとき p_{2m} = m(16m − 7) / ((6m − 1)(3m − 1))。 -/
theorem p_2m (m : ℕ) (hm : 2 ≤ m) :
    ((triangleTriples (2 * m)).card : ℚ) / (allTriples (2 * m)).card =
      m * (16 * m - 7) / ((6 * m - 1) * (3 * m - 1)) := by
  have h1 : 1 ≤ m := by omega
  have h_16_7 : 7 ≤ 16 * m := by omega
  have h_6_1 : 1 ≤ 6 * m := by omega
  have h_3_1 : 1 ≤ 3 * m := by omega
  rw [triangleTriples_card_two_mul m h1, allTriples_card_two_mul m h1]
  push_cast [Nat.cast_sub h_16_7, Nat.cast_sub h_6_1, Nat.cast_sub h_3_1]
  have hm_pos : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have h_6m1_pos : (0 : ℚ) < 6 * m - 1 := by
    have : (12 : ℚ) ≤ 6 * m := by exact_mod_cast (by omega : 12 ≤ 6 * m)
    linarith
  have h_3m1_pos : (0 : ℚ) < 3 * m - 1 := by
    have : (6 : ℚ) ≤ 3 * m := by exact_mod_cast (by omega : 6 ≤ 3 * m)
    linarith
  field_simp

end Common2026.T_Q2
