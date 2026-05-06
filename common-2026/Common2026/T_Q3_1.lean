/-
東大 2026 第3問 (1)

  座標空間内の原点を中心とする半径 5 の球面を S とする。S 上の相異なる 3 点
  P, Q, R が次の条件を満たすように動く。
    条件: P, Q は xy 平面上にあり、三角形 PQR の重心は G(2, 0, 1) である。
  以下の問いに答えよ。

  (1) 線分 PQ の中点 M の軌跡を xy 平面上に図示せよ。

  答え: M = (x, y) は円 (x − 3)² + y² = 4 上を動く。ただし M = (5, 0) は除く。

  方針:
    P = (P₁, P₂, 0), Q = (Q₁, Q₂, 0), R = (R₁, R₂, R₃) と置くと、
      重心条件: P₁ + Q₁ + R₁ = 6, P₂ + Q₂ + R₂ = 0, R₃ = 3
      球面条件 (R): R₁² + R₂² + R₃² = 25 ⇒ R₁² + R₂² = 16
    M = ((P₁ + Q₁) / 2, (P₂ + Q₂) / 2) = (x, y) と置くと
      R₁ = 6 − 2x, R₂ = −2y であり、
      (6 − 2x)² + 4y² = 16  ⇔  (x − 3)² + y² = 4

    M = (5, 0) では P + Q = (10, 0) かつ |P|, |Q| ≤ 5 から P = Q = (5, 0)
    となり P ≠ Q に反する。

    逆向き: M = (m, n) が (m − 3)² + n² = 4 かつ M ≠ (5, 0) を満たすとき
      |M|² = 6m − 5 で m ∈ [1, 5)、よって 0 < |M| < 5。
      σ := √(30 − 6m), ρ := √(6m − 5) と置き、
        P := (m − σn/ρ, n + σm/ρ),  Q := (m + σn/ρ, n − σm/ρ),
        R := (6 − 2m, −2n, 3)
      で配置を構成できる。
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace Common2026.T_Q3_1

/-- 問題の条件を満たす配置 `(P, Q, R)`。
    P, Q は xy 平面上の点なので 2D, R は 3D で表す。 -/
structure Config where
  P : ℝ × ℝ
  Q : ℝ × ℝ
  R : ℝ × ℝ × ℝ
  hP : P.1 ^ 2 + P.2 ^ 2 = 25
  hQ : Q.1 ^ 2 + Q.2 ^ 2 = 25
  hR : R.1 ^ 2 + R.2.1 ^ 2 + R.2.2 ^ 2 = 25
  hPQ : P ≠ Q
  hG_x : P.1 + Q.1 + R.1 = 6
  hG_y : P.2 + Q.2 + R.2.1 = 0
  hG_z : R.2.2 = 3

/-- 軌跡: 円 (x − 3)² + y² = 4 から (5, 0) を除いた集合。 -/
def Locus (M : ℝ × ℝ) : Prop :=
  (M.1 - 3) ^ 2 + M.2 ^ 2 = 4 ∧ M ≠ (5, 0)

/-- M が線分 PQ の (xy 平面上の) 中点であること。 -/
def IsMidpoint (M : ℝ × ℝ) (cfg : Config) : Prop :=
  cfg.P.1 + cfg.Q.1 = 2 * M.1 ∧ cfg.P.2 + cfg.Q.2 = 2 * M.2

/-! ### 順方向: Config から Locus を導く -/

/-- Config が与えられたとき、中点は (x − 3)² + y² = 4 を満たす。 -/
private lemma circle_eq_of_config (cfg : Config) (M : ℝ × ℝ)
    (hM : IsMidpoint M cfg) : (M.1 - 3) ^ 2 + M.2 ^ 2 = 4 := by
  obtain ⟨hMx, hMy⟩ := hM
  -- centroid から R₁, R₂ を M で表す
  have hRx : cfg.R.1 = 6 - 2 * M.1 := by linarith [cfg.hG_x]
  have hRy : cfg.R.2.1 = -(2 * M.2) := by linarith [cfg.hG_y]
  have hRz : cfg.R.2.2 = 3 := cfg.hG_z
  have hRsphere : cfg.R.1 ^ 2 + cfg.R.2.1 ^ 2 + cfg.R.2.2 ^ 2 = 25 := cfg.hR
  rw [hRx, hRy, hRz] at hRsphere
  nlinarith [hRsphere]

/-- Config が与えられたとき、中点は (5, 0) ではない。
    P + Q = (10, 0) と |P|, |Q| ≤ 5 から P = Q となるため。 -/
private lemma midpoint_ne_five_zero (cfg : Config) (M : ℝ × ℝ)
    (hM : IsMidpoint M cfg) : M ≠ (5, 0) := by
  intro h
  have hM1 : M.1 = 5 := by rw [h]
  have hM2 : M.2 = 0 := by rw [h]
  obtain ⟨hMx, hMy⟩ := hM
  have hPQ_x : cfg.P.1 + cfg.Q.1 = 10 := by rw [hMx, hM1]; ring
  have hPQ_y : cfg.P.2 + cfg.Q.2 = 0 := by rw [hMy, hM2]; ring
  -- P.1 ≤ 5, Q.1 ≤ 5 から P.1 = Q.1 = 5
  have hP1ub : cfg.P.1 ≤ 5 := by nlinarith [cfg.hP, sq_nonneg cfg.P.2, sq_nonneg (cfg.P.1 - 5)]
  have hQ1ub : cfg.Q.1 ≤ 5 := by nlinarith [cfg.hQ, sq_nonneg cfg.Q.2, sq_nonneg (cfg.Q.1 - 5)]
  have hP1eq : cfg.P.1 = 5 := by linarith
  have hQ1eq : cfg.Q.1 = 5 := by linarith
  -- 球面条件で P.2 = 0, Q.2 = 0
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

/-! ### 逆方向: Locus から Config を構成 -/

/-- 補助: M ∈ Locus なら m ≥ 1 (m は M.1)。 -/
lemma m_ge_one_of_locus {m n : ℝ} (h : (m - 3) ^ 2 + n ^ 2 = 4) : 1 ≤ m := by
  nlinarith [sq_nonneg n, sq_nonneg (m - 3), h]

/-- 補助: M ∈ Locus かつ M ≠ (5, 0) なら m < 5。 -/
lemma m_lt_five_of_locus {m n : ℝ} (h : (m - 3) ^ 2 + n ^ 2 = 4)
    (hne : (m, n) ≠ ((5 : ℝ), (0 : ℝ))) : m < 5 := by
  by_contra hge
  have hge' : 5 ≤ m := not_lt.mp hge
  have hm_ub : m ≤ 5 := by nlinarith [sq_nonneg n, h]
  have hm_eq : m = 5 := le_antisymm hm_ub hge'
  have hn_eq : n = 0 := by
    have h1 : (5 - 3 : ℝ) ^ 2 + n ^ 2 = 4 := by rw [← hm_eq]; exact h
    have hnsq : n ^ 2 = 0 := by nlinarith [h1]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hnsq
  exact hne (Prod.ext hm_eq hn_eq)

/-! ### Locus 上から Config を陽に構成する。 -/

/-- σ := √(30 − 6m) (弦の半長)。 -/
noncomputable def mkσ (m : ℝ) : ℝ := Real.sqrt (30 - 6 * m)

/-- ρ := √(6m − 5) (|OM|)。 -/
noncomputable def mkρ (m : ℝ) : ℝ := Real.sqrt (6 * m - 5)

/-- P 成分 = (m − σn/ρ, n + σm/ρ)。 -/
noncomputable def mkP (m n : ℝ) : ℝ × ℝ :=
  (m - mkσ m * n / mkρ m, n + mkσ m * m / mkρ m)

/-- Q 成分 = (m + σn/ρ, n − σm/ρ)。 -/
noncomputable def mkQ (m n : ℝ) : ℝ × ℝ :=
  (m + mkσ m * n / mkρ m, n - mkσ m * m / mkρ m)

/-- R 成分 = (6 − 2m, −2n, 3)。 -/
def mkR (m n : ℝ) : ℝ × ℝ × ℝ := (6 - 2 * m, -(2 * n), 3)

/-- σ² = 30 − 6m (m < 5 のとき)。 -/
lemma mkσ_sq {m : ℝ} (h : m < 5) : (mkσ m) ^ 2 = 30 - 6 * m := by
  unfold mkσ
  rw [sq, Real.mul_self_sqrt (by linarith)]

/-- ρ² = 6m − 5 (m ≥ 1 のとき)。 -/
lemma mkρ_sq {m : ℝ} (h : 1 ≤ m) : (mkρ m) ^ 2 = 6 * m - 5 := by
  unfold mkρ
  rw [sq, Real.mul_self_sqrt (by linarith)]

lemma mkσ_pos {m : ℝ} (h : m < 5) : 0 < mkσ m :=
  Real.sqrt_pos.mpr (by linarith)

lemma mkρ_pos {m : ℝ} (h : 1 ≤ m) : 0 < mkρ m :=
  Real.sqrt_pos.mpr (by linarith)

/-- (mkP m n).1 + (mkQ m n).1 = 2m (中点の x 成分)。 -/
lemma mkP_add_mkQ_fst (m n : ℝ) : (mkP m n).1 + (mkQ m n).1 = 2 * m := by
  show (m - mkσ m * n / mkρ m) + (m + mkσ m * n / mkρ m) = 2 * m
  ring

/-- (mkP m n).2 + (mkQ m n).2 = 2n。 -/
lemma mkP_add_mkQ_snd (m n : ℝ) : (mkP m n).2 + (mkQ m n).2 = 2 * n := by
  show (n + mkσ m * m / mkρ m) + (n - mkσ m * m / mkρ m) = 2 * n
  ring

/-- P が球面上。 -/
lemma mkP_sphere {m n : ℝ} (hCircle : (m - 3) ^ 2 + n ^ 2 = 4)
    (hm_ge : 1 ≤ m) (hm_lt : m < 5) :
    (mkP m n).1 ^ 2 + (mkP m n).2 ^ 2 = 25 := by
  show (m - mkσ m * n / mkρ m) ^ 2 + (n + mkσ m * m / mkρ m) ^ 2 = 25
  have hMsq : m ^ 2 + n ^ 2 = 6 * m - 5 := by nlinarith [hCircle]
  have hρ_pos : 0 < mkρ m := mkρ_pos hm_ge
  have hρ_ne : mkρ m ≠ 0 := hρ_pos.ne'
  have hρ_sq : (mkρ m) ^ 2 = 6 * m - 5 := mkρ_sq hm_ge
  have hσ_sq : (mkσ m) ^ 2 = 30 - 6 * m := mkσ_sq hm_lt
  have key : (m - mkσ m * n / mkρ m) ^ 2 + (n + mkσ m * m / mkρ m) ^ 2
      = (m ^ 2 + n ^ 2) + (mkσ m) ^ 2 * (m ^ 2 + n ^ 2) / (mkρ m) ^ 2 := by
    field_simp
    ring
  rw [key, hMsq, hσ_sq, hρ_sq]
  have h_pos : (6 * m - 5 : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- Q が球面上。 -/
lemma mkQ_sphere {m n : ℝ} (hCircle : (m - 3) ^ 2 + n ^ 2 = 4)
    (hm_ge : 1 ≤ m) (hm_lt : m < 5) :
    (mkQ m n).1 ^ 2 + (mkQ m n).2 ^ 2 = 25 := by
  show (m + mkσ m * n / mkρ m) ^ 2 + (n - mkσ m * m / mkρ m) ^ 2 = 25
  have hMsq : m ^ 2 + n ^ 2 = 6 * m - 5 := by nlinarith [hCircle]
  have hρ_pos : 0 < mkρ m := mkρ_pos hm_ge
  have hρ_ne : mkρ m ≠ 0 := hρ_pos.ne'
  have hρ_sq : (mkρ m) ^ 2 = 6 * m - 5 := mkρ_sq hm_ge
  have hσ_sq : (mkσ m) ^ 2 = 30 - 6 * m := mkσ_sq hm_lt
  have key : (m + mkσ m * n / mkρ m) ^ 2 + (n - mkσ m * m / mkρ m) ^ 2
      = (m ^ 2 + n ^ 2) + (mkσ m) ^ 2 * (m ^ 2 + n ^ 2) / (mkρ m) ^ 2 := by
    field_simp
    ring
  rw [key, hMsq, hσ_sq, hρ_sq]
  have h_pos : (6 * m - 5 : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- R が球面上。 -/
lemma mkR_sphere {m n : ℝ} (hCircle : (m - 3) ^ 2 + n ^ 2 = 4) :
    (mkR m n).1 ^ 2 + (mkR m n).2.1 ^ 2 + (mkR m n).2.2 ^ 2 = 25 := by
  show (6 - 2 * m) ^ 2 + (-(2 * n)) ^ 2 + (3 : ℝ) ^ 2 = 25
  nlinarith [hCircle]

/-- P ≠ Q (m, n が m < 5 を満たすとき)。 -/
lemma mkP_ne_mkQ {m n : ℝ} (hCircle : (m - 3) ^ 2 + n ^ 2 = 4)
    (hm_ge : 1 ≤ m) (hm_lt : m < 5) : mkP m n ≠ mkQ m n := by
  intro heq
  have hρ_pos : 0 < mkρ m := mkρ_pos hm_ge
  have hρ_ne : mkρ m ≠ 0 := hρ_pos.ne'
  have hσ_pos : 0 < mkσ m := mkσ_pos hm_lt
  have h1 : (mkP m n).1 = (mkQ m n).1 := congrArg Prod.fst heq
  -- m − σn/ρ = m + σn/ρ ⇒ σn/ρ = 0
  have h1' : (m - mkσ m * n / mkρ m) = (m + mkσ m * n / mkρ m) := h1
  have hσn_div : mkσ m * n / mkρ m = 0 := by linarith
  have hσn : mkσ m * n = 0 := by
    have heq2 : mkσ m * n / mkρ m * mkρ m = 0 := by rw [hσn_div]; ring
    rwa [div_mul_cancel₀ _ hρ_ne] at heq2
  rcases mul_eq_zero.mp hσn with hσ0 | hn0
  · exact absurd hσ0 hσ_pos.ne'
  · -- n = 0 ⇒ P.2 = Q.2 ⇒ σm/ρ = 0 ⇒ m = 0
    have h2 : (mkP m n).2 = (mkQ m n).2 := congrArg Prod.snd heq
    have h2' : (n + mkσ m * m / mkρ m) = (n - mkσ m * m / mkρ m) := h2
    have hσm_div : mkσ m * m / mkρ m = 0 := by linarith
    have hσm : mkσ m * m = 0 := by
      have heq2 : mkσ m * m / mkρ m * mkρ m = 0 := by rw [hσm_div]; ring
      rwa [div_mul_cancel₀ _ hρ_ne] at heq2
    rcases mul_eq_zero.mp hσm with hσ0 | hm0
    · exact absurd hσ0 hσ_pos.ne'
    · rw [hm0, hn0] at hCircle
      norm_num at hCircle

/-- Locus 上の (m, n) から Config を構成。 -/
noncomputable def mkLocusConfig (m n : ℝ)
    (hCircle : (m - 3) ^ 2 + n ^ 2 = 4)
    (hNotFive : (m, n) ≠ ((5 : ℝ), (0 : ℝ))) : Config :=
  let hm_ge : 1 ≤ m := m_ge_one_of_locus hCircle
  let hm_lt : m < 5 := m_lt_five_of_locus hCircle hNotFive
  { P := mkP m n
    Q := mkQ m n
    R := mkR m n
    hP := mkP_sphere hCircle hm_ge hm_lt
    hQ := mkQ_sphere hCircle hm_ge hm_lt
    hR := mkR_sphere hCircle
    hPQ := mkP_ne_mkQ hCircle hm_ge hm_lt
    hG_x := by
      show (mkP m n).1 + (mkQ m n).1 + (mkR m n).1 = 6
      rw [mkP_add_mkQ_fst]; show 2 * m + (6 - 2 * m) = 6; ring
    hG_y := by
      show (mkP m n).2 + (mkQ m n).2 + (mkR m n).2.1 = 0
      rw [mkP_add_mkQ_snd]; show 2 * n + (-(2 * n)) = 0; ring
    hG_z := rfl
  }

@[simp] lemma mkLocusConfig_P (m n : ℝ) (h₁ h₂) :
    (mkLocusConfig m n h₁ h₂).P = mkP m n := rfl

@[simp] lemma mkLocusConfig_Q (m n : ℝ) (h₁ h₂) :
    (mkLocusConfig m n h₁ h₂).Q = mkQ m n := rfl

/-- 逆方向の本体: M ∈ Locus から Config を構成し中点が M となることを示す。 -/
private lemma exists_config_of_locus (M : ℝ × ℝ) (h : Locus M) :
    ∃ cfg : Config, IsMidpoint M cfg := by
  obtain ⟨m, n⟩ := M
  obtain ⟨hCircle, hNotFive⟩ := h
  refine ⟨mkLocusConfig m n hCircle hNotFive, ?_, ?_⟩
  · show (mkP m n).1 + (mkQ m n).1 = 2 * m
    exact mkP_add_mkQ_fst m n
  · show (mkP m n).2 + (mkQ m n).2 = 2 * n
    exact mkP_add_mkQ_snd m n

/-! ### 主結果 -/

/-- (1) M = (x, y) が線分 PQ の中点であり得るための必要十分条件は、
    M が円 (x − 3)² + y² = 4 上にあり、かつ M ≠ (5, 0) であること。 -/
theorem locus_iff (M : ℝ × ℝ) :
    (∃ cfg : Config, IsMidpoint M cfg) ↔ Locus M := by
  refine ⟨?_, exists_config_of_locus M⟩
  rintro ⟨cfg, hM⟩
  exact ⟨circle_eq_of_config cfg M hM, midpoint_ne_five_zero cfg M hM⟩

end Common2026.T_Q3_1
