import Common2026.Shannon.RateDistortionConvexity
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# `klDiv` joint convexity discharge for E-4'' (E-4''')

[`docs/shannon/rate-distortion-convexity-plan.md`](../../../docs/shannon/rate-distortion-convexity-plan.md)
の **E-4'' Phase B core** が hypothesis 化していた `klDiv` joint convexity
(`h_klDiv_conv`) を **pmf 形 (per-atom log-sum inequality)** で discharge する。

## Approach

Mathlib には measure-level の `klDiv` joint convexity がない。**有限アルファベット
pmf 形** に降りて `convexOn_klFun` (`Mathlib.InformationTheory.KullbackLeibler.KLFun`)
を per-atom に適用する戦略を取る。

Step A (this file, ~Phase α): 2 点 joint convexity の **算術核**
`klFun_weighted_two_point` を直接示す。比率 `(λp₁+(1-λ)p₂)/(λq₁+(1-λ)q₂)` を
重み付き barycentre `w₁(p₁/q₁) + w₂(p₂/q₂)` に書き換え、`convexOn_klFun.2` を
press する。Boundary case `Z = λq₁+(1-λ)q₂ = 0` は per-atom AC 条件と
`q ≥ 0, λ ∈ [0,1]` の符号評価で各項 = 0 を導く。

## 設計判断

* **Real-side pmf 形のみ**: `klDivPmf` (`CsiszarProjection`) の Fintype 文脈に乗らずに
  汎用 pmf 関数 `P, Q : α → ℝ` で書く。これにより Step A が下流の Step B
  (measure → pmf) の前提から独立になる。
* **measure-level の bridge (B/C/D)** は **deferred**: Mathlib API ギャップ
  (`klDiv = ENNReal.ofReal klDivSumForm` 形の AC 条件付き bridge、Fintype 由来
  integrability の流通) が ~200 行の追加実装を要するため、本 phase は **Step A 完成**
  をもって publish。`docs/moonshot-seeds.md` の `E-4'''` は **partial** で更新。
-/

namespace InformationTheory.Shannon

open InformationTheory Real
open scoped BigOperators

/-! ## Step A — Per-atom 2 点 joint convexity (算術核) -/

/-- **`klFun` weighted-pair joint convexity**: per-atom form of the log-sum
inequality.

For non-negative `p₁, p₂, q₁, q₂` and per-atom absolute continuity
(`qᵢ = 0 → pᵢ = 0`), the function `(p, q) ↦ q · klFun (p/q)` is jointly convex.
This is the **algebraic core** of `klDiv` joint convexity at the pmf level:
summed over the alphabet it yields `klDivPmf` joint convexity, which then
lifts via `klDivSumForm_eq_toReal_klDiv` to `klDiv` joint convexity.

The boundary case `Z := λq₁ + (1-λ)q₂ = 0` is handled by per-atom AC: when
`Z = 0` both `λq₁ = 0` and `(1-λ)q₂ = 0`, and the AC hypothesis collapses the
RHS to 0. The interior case uses `convexOn_klFun` applied to the barycentric
weights `wᵢ := λqᵢ/Z` (resp. `(1-λ)q₂/Z`). -/
lemma klFun_weighted_two_point
    {p₁ p₂ q₁ q₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hac : (q₁ = 0 → p₁ = 0) ∧ (q₂ = 0 → p₂ = 0))
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    (lam * q₁ + (1 - lam) * q₂) * klFun ((lam * p₁ + (1 - lam) * p₂)
        / (lam * q₁ + (1 - lam) * q₂))
      ≤ lam * (q₁ * klFun (p₁ / q₁)) + (1 - lam) * (q₂ * klFun (p₂ / q₂)) := by
  set Z : ℝ := lam * q₁ + (1 - lam) * q₂ with hZ_def
  have h1lam : 0 ≤ 1 - lam := by linarith
  have hlamq₁ : 0 ≤ lam * q₁ := mul_nonneg hlam₀ hq₁
  have h1lamq₂ : 0 ≤ (1 - lam) * q₂ := mul_nonneg h1lam hq₂
  have hZ_nn : 0 ≤ Z := add_nonneg hlamq₁ h1lamq₂
  -- p/q ≥ 0 for both atoms (Real.div: 0/0 = 0, q > 0 ⟹ p/q ≥ 0).
  have hr₁_nn : 0 ≤ p₁ / q₁ := div_nonneg hp₁ hq₁
  have hr₂_nn : 0 ≤ p₂ / q₂ := div_nonneg hp₂ hq₂
  -- Per-atom klFun ≥ 0.
  have hkl₁_nn : 0 ≤ klFun (p₁ / q₁) := klFun_nonneg hr₁_nn
  have hkl₂_nn : 0 ≤ klFun (p₂ / q₂) := klFun_nonneg hr₂_nn
  -- Per-atom q · klFun ≥ 0.
  have hq_kl₁ : 0 ≤ q₁ * klFun (p₁ / q₁) := mul_nonneg hq₁ hkl₁_nn
  have hq_kl₂ : 0 ≤ q₂ * klFun (p₂ / q₂) := mul_nonneg hq₂ hkl₂_nn
  -- Case split on Z = 0 vs Z > 0.
  rcases eq_or_lt_of_le hZ_nn with hZ_eq | hZ_pos
  · -- Z = 0: both lam*q₁ = 0 and (1-lam)*q₂ = 0, so LHS = 0; RHS ≥ 0.
    have hZ0 : Z = 0 := hZ_eq.symm
    -- LHS computation: Z * klFun(_/Z) = 0 * klFun(_) = 0.
    rw [hZ0, zero_mul]
    -- RHS ≥ 0.
    have h_rhs1 : 0 ≤ lam * (q₁ * klFun (p₁ / q₁)) := mul_nonneg hlam₀ hq_kl₁
    have h_rhs2 : 0 ≤ (1 - lam) * (q₂ * klFun (p₂ / q₂)) := mul_nonneg h1lam hq_kl₂
    linarith
  · -- Z > 0: use convexOn_klFun.
    -- Barycentric weights w₁ := lam*q₁/Z, w₂ := (1-lam)*q₂/Z.
    set w₁ : ℝ := lam * q₁ / Z with hw₁_def
    set w₂ : ℝ := (1 - lam) * q₂ / Z with hw₂_def
    have hw₁_nn : 0 ≤ w₁ := div_nonneg hlamq₁ hZ_nn
    have hw₂_nn : 0 ≤ w₂ := div_nonneg h1lamq₂ hZ_nn
    have hZ_ne : Z ≠ 0 := hZ_pos.ne'
    have hw_sum : w₁ + w₂ = 1 := by
      rw [hw₁_def, hw₂_def, ← add_div]
      exact div_self hZ_ne
    -- Barycentre identity: (lam*p₁ + (1-lam)*p₂)/Z = w₁ * (p₁/q₁) + w₂ * (p₂/q₂).
    -- We argue: Z * [w₁ * (p₁/q₁) + w₂ * (p₂/q₂)] = lam*p₁ + (1-lam)*p₂.
    have h_bary_mul :
        Z * (w₁ * (p₁ / q₁) + w₂ * (p₂ / q₂)) = lam * p₁ + (1 - lam) * p₂ := by
      -- Z * w₁ * (p₁/q₁) = lam*q₁ * (p₁/q₁) since w₁ = lam*q₁/Z.
      have hZw₁ : Z * w₁ = lam * q₁ := by
        rw [hw₁_def, mul_div_cancel₀ _ hZ_ne]
      have hZw₂ : Z * w₂ = (1 - lam) * q₂ := by
        rw [hw₂_def, mul_div_cancel₀ _ hZ_ne]
      -- Now LHS = Z * w₁ * (p₁/q₁) + Z * w₂ * (p₂/q₂) = (lam*q₁)*(p₁/q₁) + ((1-lam)*q₂)*(p₂/q₂).
      rw [mul_add, ← mul_assoc, ← mul_assoc, hZw₁, hZw₂]
      -- (lam*q₁)*(p₁/q₁) = lam*p₁ — needs case split on q₁ = 0.
      have hcancel₁ : lam * q₁ * (p₁ / q₁) = lam * p₁ := by
        rcases eq_or_lt_of_le hq₁ with hq₁_eq | hq₁_pos
        · -- q₁ = 0 ⟹ p₁ = 0 by AC; both sides = 0.
          have hq₁0 : q₁ = 0 := hq₁_eq.symm
          have hp₁0 : p₁ = 0 := hac.1 hq₁0
          rw [hq₁0, hp₁0]; ring
        · -- q₁ > 0: standard cancellation.
          field_simp
      have hcancel₂ : (1 - lam) * q₂ * (p₂ / q₂) = (1 - lam) * p₂ := by
        rcases eq_or_lt_of_le hq₂ with hq₂_eq | hq₂_pos
        · have hq₂0 : q₂ = 0 := hq₂_eq.symm
          have hp₂0 : p₂ = 0 := hac.2 hq₂0
          rw [hq₂0, hp₂0]; ring
        · field_simp
      rw [hcancel₁, hcancel₂]
    -- Hence (lam*p₁+(1-lam)*p₂)/Z = w₁*(p₁/q₁) + w₂*(p₂/q₂).
    have h_bary : (lam * p₁ + (1 - lam) * p₂) / Z
        = w₁ * (p₁ / q₁) + w₂ * (p₂ / q₂) := by
      rw [← h_bary_mul, mul_div_cancel_left₀ _ hZ_ne]
    -- Apply convexOn_klFun.
    have h_conv := (convexOn_klFun).2 (x := p₁ / q₁) (y := p₂ / q₂)
      hr₁_nn hr₂_nn hw₁_nn hw₂_nn hw_sum
    -- Goal: Z * klFun((lam*p₁+(1-lam)*p₂)/Z) ≤ lam*(q₁*klFun(...)) + (1-lam)*(q₂*klFun(...)).
    rw [h_bary]
    -- LHS = Z * klFun(w₁ * r₁ + w₂ * r₂) ≤ Z * (w₁ * klFun r₁ + w₂ * klFun r₂).
    have h_mul_le : Z * klFun (w₁ * (p₁ / q₁) + w₂ * (p₂ / q₂))
        ≤ Z * (w₁ * klFun (p₁ / q₁) + w₂ * klFun (p₂ / q₂)) :=
      mul_le_mul_of_nonneg_left h_conv hZ_nn
    refine h_mul_le.trans (le_of_eq ?_)
    -- Z * (w₁ * klFun r₁ + w₂ * klFun r₂)
    -- = (Z*w₁) * klFun r₁ + (Z*w₂) * klFun r₂
    -- = (lam*q₁) * klFun r₁ + ((1-lam)*q₂) * klFun r₂
    -- = lam*(q₁*klFun r₁) + (1-lam)*(q₂*klFun r₂)
    have hZw₁ : Z * w₁ = lam * q₁ := by
      rw [hw₁_def, mul_div_cancel₀ _ hZ_ne]
    have hZw₂ : Z * w₂ = (1 - lam) * q₂ := by
      rw [hw₂_def, mul_div_cancel₀ _ hZ_ne]
    calc Z * (w₁ * klFun (p₁ / q₁) + w₂ * klFun (p₂ / q₂))
        = Z * w₁ * klFun (p₁ / q₁) + Z * w₂ * klFun (p₂ / q₂) := by ring
      _ = lam * q₁ * klFun (p₁ / q₁) + (1 - lam) * q₂ * klFun (p₂ / q₂) := by
          rw [hZw₁, hZw₂]
      _ = lam * (q₁ * klFun (p₁ / q₁)) + (1 - lam) * (q₂ * klFun (p₂ / q₂)) := by ring

/-! ## Step A (aggregate) — pmf 形 2 点 joint convexity

Step A の per-atom 不等式を有限アルファベット `α` (Fintype) 上で和に集約することで、
pmf 形 `klDivPmf P Q := ∑ a, Q a · klFun (P a / Q a)` の joint convexity を得る。
これは E-4''' の核となる **finite-alphabet pmf-level** の 2 点凸性であり、後段で
measure → pmf bridge を経由して `klDiv` 形の `h_klDiv_conv` を inhabit する出発点になる。 -/

/-- **pmf 形 2 点 joint convexity** (Step A aggregate):
有限アルファベット上で pmf 関数として与えられた `P₁, P₂, Q₁, Q₂ : α → ℝ` (非負 +
per-atom AC) に対し、`∑ a, Q a · klFun (P a / Q a)` は `(P, Q)` について 2 点 joint
凸性を満たす。

per-atom `klFun_weighted_two_point` を `Finset.sum_le_sum` で集約し、`Finset.mul_sum`
で λ, (1-λ) を線形性経由で外に押し出す。 -/
theorem klDivPmf_joint_convex_two_point {α : Type*} [Fintype α]
    {P₁ P₂ Q₁ Q₂ : α → ℝ}
    (hP₁ : ∀ a, 0 ≤ P₁ a) (hP₂ : ∀ a, 0 ≤ P₂ a)
    (hQ₁ : ∀ a, 0 ≤ Q₁ a) (hQ₂ : ∀ a, 0 ≤ Q₂ a)
    (hac₁ : ∀ a, Q₁ a = 0 → P₁ a = 0) (hac₂ : ∀ a, Q₂ a = 0 → P₂ a = 0)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    (∑ a : α, (lam * Q₁ a + (1 - lam) * Q₂ a)
      * klFun ((lam * P₁ a + (1 - lam) * P₂ a) / (lam * Q₁ a + (1 - lam) * Q₂ a)))
      ≤ lam * (∑ a : α, Q₁ a * klFun (P₁ a / Q₁ a))
        + (1 - lam) * (∑ a : α, Q₂ a * klFun (P₂ a / Q₂ a)) := by
  -- Step 1: per-atom bound from `klFun_weighted_two_point`.
  have h_per : ∀ a : α,
      (lam * Q₁ a + (1 - lam) * Q₂ a)
          * klFun ((lam * P₁ a + (1 - lam) * P₂ a) / (lam * Q₁ a + (1 - lam) * Q₂ a))
        ≤ lam * (Q₁ a * klFun (P₁ a / Q₁ a))
          + (1 - lam) * (Q₂ a * klFun (P₂ a / Q₂ a)) := by
    intro a
    exact klFun_weighted_two_point (hP₁ a) (hP₂ a) (hQ₁ a) (hQ₂ a)
      ⟨hac₁ a, hac₂ a⟩ hlam₀ hlam₁
  -- Step 2: sum_le_sum then factor λ and (1-λ).
  refine (Finset.sum_le_sum (fun a _ => h_per a)).trans (le_of_eq ?_)
  -- ∑ a, [λ·X_a + (1-λ)·Y_a] = λ·∑ X_a + (1-λ)·∑ Y_a.
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end InformationTheory.Shannon
