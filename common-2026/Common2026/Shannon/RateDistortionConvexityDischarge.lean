import Common2026.Shannon.RateDistortionConvexity
import Common2026.Shannon.Sanov
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
open scoped BigOperators ENNReal

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

/-! ## Step B — measure → pmf bridge

E-4''' Step B. `mixtureMeasure` の pointwise pmf reduction と `klDivSumForm`
の joint convexity (mixture vs marginal product) を Step A から導く。 -/

open MeasureTheory ProbabilityTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Nonempty α] [Nonempty β]
  [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Nonempty α] [Nonempty β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- `mixtureMeasure` の pointwise pmf 形 reduction (`Measure.real` 形). -/
lemma mixtureMeasure_real_singleton
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (ν₁ ν₂ : Measure (α × β)) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (p : α × β) :
    (mixtureMeasure lam ν₁ ν₂).real {p}
      = lam * ν₁.real {p} + (1 - lam) * ν₂.real {p} := by
  unfold mixtureMeasure
  have h1lam : 0 ≤ 1 - lam := by linarith
  have hfin1 : (ENNReal.ofReal lam • ν₁) {p} ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hfin2 : (ENNReal.ofReal (1 - lam) • ν₂) {p} ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [measureReal_add_apply hfin1 hfin2, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hlam₀,
    ENNReal.toReal_ofReal h1lam]

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β] in
/-- product 周辺積測度を pointwise に展開. -/
lemma marginalProd_real_singleton
    (ν : Measure (α × β)) [IsFiniteMeasure ν] (a : α) (b : β) :
    ((ν.map Prod.fst).prod (ν.map Prod.snd)).real {(a, b)}
      = ν.real (Prod.fst ⁻¹' {a}) * ν.real (Prod.snd ⁻¹' {b}) := by
  have h_eq : ({(a, b)} : Set (α × β)) = ({a} ×ˢ {b}) := by
    ext ⟨x, y⟩; simp
  rw [h_eq]
  show ((ν.map Prod.fst).prod (ν.map Prod.snd) ({a} ×ˢ {b})).toReal = _
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rw [Measure.map_apply measurable_fst (measurableSet_singleton a),
      Measure.map_apply measurable_snd (measurableSet_singleton b)]
  rfl

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β] in
/-- **Summed identity bridge** (`klDivPmf` ↔ `klDivSumForm`): for prob measures
`ν, marg` on `α × β` with `ν ≪ marg`,
  `∑ p, marg.real{p} · klFun(ν.real{p}/marg.real{p}) = klDivSumForm ν marg`.

Per-atom the two terms differ by `marg.real{p} - ν.real{p}`, but summed
this correction = `∑marg.real - ∑ν.real = 1 - 1 = 0` by prob normalization. -/
lemma sum_marg_klFun_eq_klDivSumForm
    (ν : Measure (α × β)) [IsProbabilityMeasure ν]
    (marg : Measure (α × β)) [IsProbabilityMeasure marg]
    (h_ac : ν ≪ marg) :
    ∑ p : α × β, marg.real {p}
        * klFun (ν.real {p} / marg.real {p}) = klDivSumForm ν marg := by
  unfold klDivSumForm klFun
  -- Per-atom: marg · ((ν/marg) · log(ν/marg) + 1 - ν/marg)
  --           = ν · (log ν - log marg) + (marg - ν).
  -- Summed: correction term cancels by prob normalization.
  have h_atom : ∀ p : α × β,
      marg.real {p} * (ν.real {p} / marg.real {p}
          * Real.log (ν.real {p} / marg.real {p}) + 1 - ν.real {p} / marg.real {p})
        = ν.real {p} * (Real.log (ν.real {p}) - Real.log (marg.real {p}))
          + (marg.real {p} - ν.real {p}) := by
    intro p
    by_cases hmarg0 : marg.real {p} = 0
    · have hν0 : ν.real {p} = 0 := by
        have h_meas_eq : marg {p} = 0 := by
          rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hmarg0
          rcases hmarg0 with h | h
          · exact h
          · exact absurd h (measure_ne_top _ _)
        have : ν {p} = 0 := h_ac h_meas_eq
        simp [Measure.real, this]
      rw [hmarg0, hν0]; simp
    · have hmarg_pos : 0 < marg.real {p} :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hmarg0)
      by_cases hν0 : ν.real {p} = 0
      · rw [hν0]; simp
      · have h_log_div : Real.log (ν.real {p} / marg.real {p})
            = Real.log (ν.real {p}) - Real.log (marg.real {p}) :=
          Real.log_div hν0 hmarg0
        rw [h_log_div]
        field_simp
        ring
  simp_rw [h_atom]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h_sum_marg : ∑ p : α × β, marg.real {p} = 1 := by
    rw [sum_measureReal_singleton]
    show marg.real ((Finset.univ : Finset (α × β)) : Set (α × β)) = 1
    rw [Finset.coe_univ]; exact probReal_univ
  have h_sum_ν : ∑ p : α × β, ν.real {p} = 1 := by
    rw [sum_measureReal_singleton]
    show ν.real ((Finset.univ : Finset (α × β)) : Set (α × β)) = 1
    rw [Finset.coe_univ]; exact probReal_univ
  rw [h_sum_marg, h_sum_ν]
  ring

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β] in
/-- Helper: when X-marginals agree, mixture's product-marginal is a convex
combination of components' product-marginals (pointwise on singletons). -/
private lemma mixMarg_real_singleton_eq
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (ν₁ ν₂ : Measure (α × β))
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h_marg_eq : ν₁.map Prod.fst = ν₂.map Prod.fst)
    (p : α × β) :
    (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
        ((mixtureMeasure lam ν₁ ν₂).map Prod.snd)).real {p}
      = lam * ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)).real {p}
        + (1 - lam) * ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)).real {p} := by
  have h1lam : 0 ≤ 1 - lam := by linarith
  have h_mix_fin : IsFiniteMeasure (mixtureMeasure lam ν₁ ν₂) := by
    refine ⟨?_⟩
    unfold mixtureMeasure
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        measure_univ, measure_univ, mul_one, mul_one,
        ← ENNReal.ofReal_add hlam₀ h1lam, show lam + (1 - lam) = 1 from by ring,
        ENNReal.ofReal_one]
    exact ENNReal.one_lt_top
  obtain ⟨a, b⟩ := p
  -- Step 1: rewrite each marg.real{(a,b)} via marginalProd_real_singleton.
  rw [marginalProd_real_singleton, marginalProd_real_singleton,
      marginalProd_real_singleton]
  -- Step 2: (mix.map fst).real{a} = (ν₁.map fst).real{a} (since X-marg agrees & mix
  -- is convex comb of equal measures).
  have h_mix_fst : (mixtureMeasure lam ν₁ ν₂).real (Prod.fst ⁻¹' {a})
      = ν₁.real (Prod.fst ⁻¹' {a}) := by
    have h_apply : (mixtureMeasure lam ν₁ ν₂) (Prod.fst ⁻¹' {a})
        = ν₁ (Prod.fst ⁻¹' {a}) := by
      unfold mixtureMeasure
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      have h_eq_meas : ν₂ (Prod.fst ⁻¹' {a}) = ν₁ (Prod.fst ⁻¹' {a}) := by
        have h1 : ν₁ (Prod.fst ⁻¹' {a}) = (ν₁.map Prod.fst) {a} :=
          (Measure.map_apply measurable_fst (measurableSet_singleton a)).symm
        have h2 : ν₂ (Prod.fst ⁻¹' {a}) = (ν₂.map Prod.fst) {a} :=
          (Measure.map_apply measurable_fst (measurableSet_singleton a)).symm
        rw [h1, h2, h_marg_eq]
      rw [h_eq_meas]
      rw [show ENNReal.ofReal lam * ν₁ (Prod.fst ⁻¹' {a})
          + ENNReal.ofReal (1 - lam) * ν₁ (Prod.fst ⁻¹' {a})
          = (ENNReal.ofReal lam + ENNReal.ofReal (1 - lam)) * ν₁ (Prod.fst ⁻¹' {a}) by ring]
      rw [← ENNReal.ofReal_add hlam₀ h1lam,
          show lam + (1 - lam) = 1 from by ring, ENNReal.ofReal_one, one_mul]
    show ((mixtureMeasure lam ν₁ ν₂) (Prod.fst ⁻¹' {a})).toReal = _
    rw [h_apply]; rfl
  -- Step 3: (mix.map snd).real{b} = λ (ν₁.map snd).real{b} + (1-λ) (ν₂.map snd).real{b}.
  have h_mix_snd : (mixtureMeasure lam ν₁ ν₂).real (Prod.snd ⁻¹' {b})
      = lam * ν₁.real (Prod.snd ⁻¹' {b}) + (1 - lam) * ν₂.real (Prod.snd ⁻¹' {b}) := by
    unfold mixtureMeasure
    show ((ENNReal.ofReal lam • ν₁ + ENNReal.ofReal (1 - lam) • ν₂)
        (Prod.snd ⁻¹' {b})).toReal = _
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hlam₀, ENNReal.toReal_ofReal h1lam]
    rfl
  -- Step 4: combine.
  rw [h_mix_fst, h_mix_snd]
  -- ν₁_fst.real{a} (= ν₂_fst.real{a}) abbreviated as P_a; ν_i_snd.real{b} as Q_ib.
  -- (ν₁_fst.real{a}) · (λ ν₁_Y + (1-λ) ν₂_Y) = λ ν₁_fst · ν₁_Y + (1-λ) ν₁_fst · ν₂_Y.
  -- Need second to be (1-λ) ν₂_fst · ν₂_Y, which holds since ν₁_fst = ν₂_fst.
  have h_marg_eq_real : ν₁.real (Prod.fst ⁻¹' {a}) = ν₂.real (Prod.fst ⁻¹' {a}) := by
    have h1 : ν₁.real (Prod.fst ⁻¹' {a}) = (ν₁.map Prod.fst).real {a} := by
      rw [map_measureReal_apply measurable_fst (measurableSet_singleton a)]
    have h2 : ν₂.real (Prod.fst ⁻¹' {a}) = (ν₂.map Prod.fst).real {a} := by
      rw [map_measureReal_apply measurable_fst (measurableSet_singleton a)]
    rw [h1, h2, h_marg_eq]
  rw [h_marg_eq_real]
  ring

set_option linter.unusedSectionVars false in
/-- **mixture の `klDivSumForm` joint convexity** (Step B 主補題).

ν₁, ν₂ : prob measure on `α × β` with shared X-marginal, AC to own
marginal product. Then `klDivSumForm` of mixture (with marginal product of
mixture) ≤ convex combination of `klDivSumForm`s.

**X-marginal 共有が必要**: product-marginal `(mix.map fst).prod (mix.map snd)`
は X-marginal が共有でない限り convex combination 形に reduce できない (cross
terms が出る)。共有のとき `marg(mix) = λ marg(ν₁) + (1-λ) marg(ν₂)` が成立し、
Step A `klFun_weighted_two_point` を per-atom 適用可能。 -/
lemma klDivSumForm_mixtureMeasure_le
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (ν₁ ν₂ : Measure (α × β))
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hac₁ : ν₁ ≪ (ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
    (hac₂ : ν₂ ≪ (ν₂.map Prod.fst).prod (ν₂.map Prod.snd))
    (h_marg_eq : ν₁.map Prod.fst = ν₂.map Prod.fst) :
    klDivSumForm (mixtureMeasure lam ν₁ ν₂)
      (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
        ((mixtureMeasure lam ν₁ ν₂).map Prod.snd))
      ≤ lam * klDivSumForm ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
        + (1 - lam) * klDivSumForm ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
  -- mixture is a prob measure (convex combination of prob, λ ∈ [0,1] with sum 1).
  have h1lam : 0 ≤ 1 - lam := by linarith
  have h_mix_prob : IsProbabilityMeasure (mixtureMeasure lam ν₁ ν₂) := by
    refine ⟨?_⟩
    unfold mixtureMeasure
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        measure_univ, measure_univ, mul_one, mul_one,
        ← ENNReal.ofReal_add hlam₀ h1lam, show lam + (1 - lam) = 1 from by ring,
        ENNReal.ofReal_one]
  -- Marginal product measures are prob (pushforward of prob is prob).
  have h_ν₁fst_prob : IsProbabilityMeasure (ν₁.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_ν₁snd_prob : IsProbabilityMeasure (ν₁.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have h_ν₂fst_prob : IsProbabilityMeasure (ν₂.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_ν₂snd_prob : IsProbabilityMeasure (ν₂.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  -- Set abbreviations.
  set mix := mixtureMeasure lam ν₁ ν₂ with h_mix_def
  set marg1 := (ν₁.map Prod.fst).prod (ν₁.map Prod.snd) with h_marg1_def
  set marg2 := (ν₂.map Prod.fst).prod (ν₂.map Prod.snd) with h_marg2_def
  set margMix := (mix.map Prod.fst).prod (mix.map Prod.snd) with h_margMix_def
  have h_mix_fst_prob : IsProbabilityMeasure (mix.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_mix_snd_prob : IsProbabilityMeasure (mix.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have h_margMix_prob : IsProbabilityMeasure margMix := by
    show IsProbabilityMeasure ((mix.map Prod.fst).prod (mix.map Prod.snd)); infer_instance
  have h_marg1_prob : IsProbabilityMeasure marg1 := by
    show IsProbabilityMeasure ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)); infer_instance
  have h_marg2_prob : IsProbabilityMeasure marg2 := by
    show IsProbabilityMeasure ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)); infer_instance
  -- AC for mix to margMix via per-singleton analysis (Fintype + product structure).
  have h_mix_ac : mix ≪ margMix := by
    intro s h_margMix0
    -- Reduce to singleton case via Fintype-level singleton decomposition.
    have h_s_fin : (s : Set (α × β)).Finite := Set.toFinite _
    rw [← Set.Finite.coe_toFinset h_s_fin] at h_margMix0 ⊢
    rw [← sum_measure_singleton] at h_margMix0 ⊢
    have h_margMix_per_atom : ∀ p ∈ h_s_fin.toFinset, margMix {p} = 0 := by
      have h_nn : ∀ p ∈ h_s_fin.toFinset, 0 ≤ margMix {p} := fun _ _ => bot_le
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nn).mp h_margMix0
    refine Finset.sum_eq_zero ?_
    intro p hp
    have hp_marg0 : margMix {p} = 0 := h_margMix_per_atom p hp
    -- margMix{p} = (mix.map fst){p.1} · (mix.map snd){p.2}.
    have h_prod : margMix {p} = (mix.map Prod.fst) {p.1} * (mix.map Prod.snd) {p.2} := by
      show ((mix.map Prod.fst).prod (mix.map Prod.snd)) {p} = _
      obtain ⟨a, b⟩ := p
      have h_singleton_prod : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
        ext ⟨x, y⟩; simp
      rw [h_singleton_prod, Measure.prod_prod]
    rw [h_prod, mul_eq_zero] at hp_marg0
    rcases hp_marg0 with hfst0 | hsnd0
    · rw [Measure.map_apply measurable_fst (measurableSet_singleton _)] at hfst0
      have h_subset : ({p} : Set (α × β)) ⊆ Prod.fst ⁻¹' {p.1} := by
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; simp
      exact le_zero_iff.mp (le_trans (measure_mono h_subset) hfst0.le)
    · rw [Measure.map_apply measurable_snd (measurableSet_singleton _)] at hsnd0
      have h_subset : ({p} : Set (α × β)) ⊆ Prod.snd ⁻¹' {p.2} := by
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; simp
      exact le_zero_iff.mp (le_trans (measure_mono h_subset) hsnd0.le)
  -- Now: convert LHS klDivSumForm (mix, margMix) → ∑ margMix · klFun(mix/margMix).
  have h_lhs_eq : klDivSumForm mix margMix
      = ∑ p : α × β, margMix.real {p} * klFun (mix.real {p} / margMix.real {p}) :=
    (sum_marg_klFun_eq_klDivSumForm mix margMix h_mix_ac).symm
  have h_rhs1_eq : klDivSumForm ν₁ marg1
      = ∑ p : α × β, marg1.real {p} * klFun (ν₁.real {p} / marg1.real {p}) :=
    (sum_marg_klFun_eq_klDivSumForm ν₁ marg1 hac₁).symm
  have h_rhs2_eq : klDivSumForm ν₂ marg2
      = ∑ p : α × β, marg2.real {p} * klFun (ν₂.real {p} / marg2.real {p}) :=
    (sum_marg_klFun_eq_klDivSumForm ν₂ marg2 hac₂).symm
  rw [h_lhs_eq, h_rhs1_eq, h_rhs2_eq]
  -- Pointwise inequality: apply Step A's klFun_weighted_two_point per atom.
  have h_per : ∀ p : α × β,
      margMix.real {p} * klFun (mix.real {p} / margMix.real {p})
        ≤ lam * (marg1.real {p} * klFun (ν₁.real {p} / marg1.real {p}))
          + (1 - lam) * (marg2.real {p} * klFun (ν₂.real {p} / marg2.real {p})) := by
    intro p
    have h_mix_p := mixtureMeasure_real_singleton lam hlam₀ hlam₁ ν₁ ν₂ p
    have h_margMix_p := mixMarg_real_singleton_eq hlam₀ hlam₁ ν₁ ν₂ h_marg_eq p
    rw [h_mix_p, h_margMix_p]
    have h_ac1 : marg1.real {p} = 0 → ν₁.real {p} = 0 := by
      intro h0
      have h_meas0 : marg1 {p} = 0 := by
        rw [Measure.real, ENNReal.toReal_eq_zero_iff] at h0
        rcases h0 with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      have : ν₁ {p} = 0 := hac₁ h_meas0
      simp [Measure.real, this]
    have h_ac2 : marg2.real {p} = 0 → ν₂.real {p} = 0 := by
      intro h0
      have h_meas0 : marg2 {p} = 0 := by
        rw [Measure.real, ENNReal.toReal_eq_zero_iff] at h0
        rcases h0 with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      have : ν₂ {p} = 0 := hac₂ h_meas0
      simp [Measure.real, this]
    exact klFun_weighted_two_point measureReal_nonneg measureReal_nonneg
      measureReal_nonneg measureReal_nonneg ⟨h_ac1, h_ac2⟩ hlam₀ hlam₁
  refine (Finset.sum_le_sum (fun p _ => h_per p)).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## Step C — `klDiv` ↔ `klDivSumForm` ENNReal/Real bridge -/

set_option linter.unusedSectionVars false in
/-- **Step C**: `klDiv ν marg = ENNReal.ofReal (klDivSumForm ν marg)` under
prob + AC. Sanov の `klDivSumForm_eq_toReal_klDiv` の有限アルファベット pmf 形を
**`Q` full support 仮説なし**で適用するために、`Q.real{a} = 0` の atom は AC
経由で contribution 0 と確認する。 -/
lemma klDiv_eq_ofReal_klDivSumForm
    (ν : Measure (α × β)) [IsProbabilityMeasure ν]
    (h_ac : ν ≪ (ν.map Prod.fst).prod (ν.map Prod.snd)) :
    klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))
      = ENNReal.ofReal
          (klDivSumForm ν ((ν.map Prod.fst).prod (ν.map Prod.snd))) := by
  set marg := (ν.map Prod.fst).prod (ν.map Prod.snd) with h_marg_def
  have h_ν_fst_prob : IsProbabilityMeasure (ν.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_ν_snd_prob : IsProbabilityMeasure (ν.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have h_marg_prob : IsProbabilityMeasure marg := by
    show IsProbabilityMeasure ((ν.map Prod.fst).prod (ν.map Prod.snd)); infer_instance
  -- klDiv ν marg ≠ ∞ via AC + Fintype-automatic integrability.
  have h_int : Integrable (llr ν marg) ν := by
    refine ⟨(measurable_llr _ _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  have h_ne_top : klDiv ν marg ≠ ∞ := klDiv_ne_top h_ac h_int
  -- klDivSumForm ν marg = (klDiv ν marg).toReal (without `Q full support`).
  have h_sum_eq_toReal : klDivSumForm ν marg = (klDiv ν marg).toReal := by
    -- Mimic Sanov's proof, with case-split on Q.real {a} = 0.
    have h_univ : ν Set.univ = marg Set.univ := by rw [measure_univ, measure_univ]
    rw [toReal_klDiv_of_measure_eq h_ac h_univ]
    rw [integral_fintype h_int]
    unfold klDivSumForm
    refine Finset.sum_congr rfl fun a _ => ?_
    -- Case 1: ν.real {a} = 0 ⟹ both sides 0 (0 · _ = 0).
    by_cases hPa : ν.real {a} = 0
    · rw [hPa]; simp
    -- Case 2: ν.real {a} > 0.
    have hPa_pos : 0 < ν.real {a} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hPa)
    have hP_ne : ν {a} ≠ 0 := by
      intro h; apply hPa; rw [Measure.real, h]; rfl
    -- ν ≪ marg ⟹ if marg.real{a} = 0 then ν.real{a} = 0, contradicting hPa_pos.
    have hQa_pos : 0 < marg.real {a} := by
      by_contra h_le
      have h_le' : marg.real {a} ≤ 0 := not_lt.mp h_le
      have hQa : marg.real {a} = 0 := le_antisymm h_le' measureReal_nonneg
      have hQ_meas_0 : marg {a} = 0 := by
        rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hQa
        rcases hQa with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      have : ν {a} = 0 := h_ac hQ_meas_0
      exact hP_ne this
    have hQne : marg.real {a} ≠ 0 := hQa_pos.ne'
    -- rnDeriv identification: (ν.rnDeriv marg a) * marg {a} = ν {a}.
    have h_rnD_enn : (ν.rnDeriv marg a) * marg {a} = ν {a} := by
      have h_wd : marg.withDensity (ν.rnDeriv marg) = ν :=
        Measure.withDensity_rnDeriv_eq ν marg h_ac
      have h1 : (marg.withDensity (ν.rnDeriv marg)) {a} = ν {a} := by rw [h_wd]
      rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton] at h1
      exact h1
    have h_rnD_real : (ν.rnDeriv marg a).toReal * marg.real {a} = ν.real {a} := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
    have h_rnD_eq : (ν.rnDeriv marg a).toReal = ν.real {a} / marg.real {a} := by
      field_simp at h_rnD_real ⊢
      linarith [h_rnD_real]
    have h_llr : llr ν marg a = Real.log (ν.real {a}) - Real.log (marg.real {a}) := by
      unfold llr
      rw [h_rnD_eq, Real.log_div hPa_pos.ne' hQne]
    rw [h_llr, smul_eq_mul]
  rw [← ENNReal.ofReal_toReal h_ne_top, ← h_sum_eq_toReal]

/-! ## Step D — `h_klDiv_conv` inhabit (measure-level joint convexity) -/

set_option linter.unusedSectionVars false in
/-- **`klDiv` mixture joint convexity** (Step D 主補題, Cover-Thomas 2.7.2 measure 化形). -/
theorem klDiv_mixture_joint_convex
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (D₁ D₂ : ℝ)
    (ν₁ ν₂ : Measure (α × β))
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h_marg₁ : ν₁.map Prod.fst = P) (h_marg₂ : ν₂.map Prod.fst = P)
    (_h_int₁ : Integrable (fun p => d p.1 p.2) ν₁)
    (_h_int₂ : Integrable (fun p => d p.1 p.2) ν₂)
    (_h_dist₁ : expectedDistortion d ν₁ ≤ D₁)
    (_h_dist₂ : expectedDistortion d ν₂ ≤ D₂)
    (h_ac₁ : ν₁ ≪ (ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
    (h_ac₂ : ν₂ ≪ (ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) :
    klDiv (mixtureMeasure lam ν₁ ν₂)
        (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
          ((mixtureMeasure lam ν₁ ν₂).map Prod.snd))
      ≤ ENNReal.ofReal lam * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
        + ENNReal.ofReal (1 - lam) * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
  have h1lam : 0 ≤ 1 - lam := by linarith
  have h_marg_eq : ν₁.map Prod.fst = ν₂.map Prod.fst := h_marg₁.trans h_marg₂.symm
  -- mixture is a prob measure.
  have h_mix_prob : IsProbabilityMeasure (mixtureMeasure lam ν₁ ν₂) := by
    refine ⟨?_⟩
    unfold mixtureMeasure
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
        measure_univ, measure_univ, mul_one, mul_one,
        ← ENNReal.ofReal_add hlam₀ h1lam, show lam + (1 - lam) = 1 from by ring,
        ENNReal.ofReal_one]
  -- AC of mixture to marg(mixture): follows from per-singleton analysis (same as in Step B).
  -- We re-derive it here as it's needed for Step C bridge of LHS.
  set mix := mixtureMeasure lam ν₁ ν₂
  set marg1 := (ν₁.map Prod.fst).prod (ν₁.map Prod.snd)
  set marg2 := (ν₂.map Prod.fst).prod (ν₂.map Prod.snd)
  set margMix := (mix.map Prod.fst).prod (mix.map Prod.snd)
  have h_mix_fst_prob : IsProbabilityMeasure (mix.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_mix_snd_prob : IsProbabilityMeasure (mix.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have h_margMix_prob : IsProbabilityMeasure margMix := by
    show IsProbabilityMeasure ((mix.map Prod.fst).prod (mix.map Prod.snd)); infer_instance
  have h_mix_ac : mix ≪ margMix := by
    intro s h_margMix0
    have h_s_fin : (s : Set (α × β)).Finite := Set.toFinite _
    rw [← Set.Finite.coe_toFinset h_s_fin] at h_margMix0 ⊢
    rw [← sum_measure_singleton] at h_margMix0 ⊢
    have h_margMix_per_atom : ∀ p ∈ h_s_fin.toFinset, margMix {p} = 0 := by
      have h_nn : ∀ p ∈ h_s_fin.toFinset, 0 ≤ margMix {p} := fun _ _ => bot_le
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nn).mp h_margMix0
    refine Finset.sum_eq_zero ?_
    intro p hp
    have hp_marg0 : margMix {p} = 0 := h_margMix_per_atom p hp
    have h_prod : margMix {p} = (mix.map Prod.fst) {p.1} * (mix.map Prod.snd) {p.2} := by
      show ((mix.map Prod.fst).prod (mix.map Prod.snd)) {p} = _
      obtain ⟨a, b⟩ := p
      have h_singleton_prod : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
        ext ⟨x, y⟩; simp
      rw [h_singleton_prod, Measure.prod_prod]
    rw [h_prod, mul_eq_zero] at hp_marg0
    rcases hp_marg0 with hfst0 | hsnd0
    · rw [Measure.map_apply measurable_fst (measurableSet_singleton _)] at hfst0
      have h_subset : ({p} : Set (α × β)) ⊆ Prod.fst ⁻¹' {p.1} := by
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; simp
      exact le_zero_iff.mp (le_trans (measure_mono h_subset) hfst0.le)
    · rw [Measure.map_apply measurable_snd (measurableSet_singleton _)] at hsnd0
      have h_subset : ({p} : Set (α × β)) ⊆ Prod.snd ⁻¹' {p.2} := by
        intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; simp
      exact le_zero_iff.mp (le_trans (measure_mono h_subset) hsnd0.le)
  -- Step B: Real-side convexity inequality.
  have h_realB := klDivSumForm_mixtureMeasure_le hlam₀ hlam₁ ν₁ ν₂ h_ac₁ h_ac₂ h_marg_eq
  -- Step C: bridge each klDiv to ofReal · klDivSumForm.
  have h_C_mix := klDiv_eq_ofReal_klDivSumForm mix h_mix_ac
  have h_C_1 := klDiv_eq_ofReal_klDivSumForm ν₁ h_ac₁
  have h_C_2 := klDiv_eq_ofReal_klDivSumForm ν₂ h_ac₂
  -- Substitute Step C bridges into goal.
  rw [show klDiv mix margMix = ENNReal.ofReal (klDivSumForm mix margMix) from h_C_mix,
      show klDiv ν₁ marg1 = ENNReal.ofReal (klDivSumForm ν₁ marg1) from h_C_1,
      show klDiv ν₂ marg2 = ENNReal.ofReal (klDivSumForm ν₂ marg2) from h_C_2]
  -- Goal: ofReal (klDivSumForm mix margMix)
  --       ≤ ofReal lam * ofReal (klDivSumForm ν₁ marg1)
  --         + ofReal (1-lam) * ofReal (klDivSumForm ν₂ marg2).
  -- Use ofReal_mul (lam, 1-lam ≥ 0) + ofReal_add (nonneg klDivSumForm) + ofReal_le_ofReal_iff.
  -- Nonneg of klDivSumForm: via bridge `klDivSumForm = ∑ marg · klFun(ν/marg)` and `klFun ≥ 0`.
  have h_marg1_prob : IsProbabilityMeasure marg1 := by
    show IsProbabilityMeasure ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
    have : IsProbabilityMeasure (ν₁.map Prod.fst) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have : IsProbabilityMeasure (ν₁.map Prod.snd) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    infer_instance
  have h_marg2_prob : IsProbabilityMeasure marg2 := by
    show IsProbabilityMeasure ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd))
    have : IsProbabilityMeasure (ν₂.map Prod.fst) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have : IsProbabilityMeasure (ν₂.map Prod.snd) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    infer_instance
  have h_kl_nn : ∀ (μ μ' : Measure (α × β)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'],
      μ ≪ μ' → 0 ≤ klDivSumForm μ μ' := by
    intro μ μ' _ _ h_ac
    rw [← sum_marg_klFun_eq_klDivSumForm μ μ' h_ac]
    refine Finset.sum_nonneg fun p _ => ?_
    exact mul_nonneg measureReal_nonneg (klFun_nonneg
      (div_nonneg measureReal_nonneg measureReal_nonneg))
  have h_kl1_nn : 0 ≤ klDivSumForm ν₁ marg1 := h_kl_nn ν₁ marg1 h_ac₁
  have h_kl2_nn : 0 ≤ klDivSumForm ν₂ marg2 := h_kl_nn ν₂ marg2 h_ac₂
  -- Step B inequality lifted to ENNReal.
  rw [← ENNReal.ofReal_mul hlam₀, ← ENNReal.ofReal_mul h1lam,
      ← ENNReal.ofReal_add (mul_nonneg hlam₀ h_kl1_nn) (mul_nonneg h1lam h_kl2_nn)]
  exact ENNReal.ofReal_le_ofReal h_realB

/-! ## Step E — 仮説なし R(D) 凸性主定理 -/

set_option linter.unusedSectionVars false in
/-- Helper: Fintype 由来 integrability for any joint with `Prod.fst` marginal = P.
`d : α → β → ℝ` is bounded on the finite product alphabet, so it is integrable
on any finite measure (in particular any feasible joint, which is a probability
measure since its X-marginal is P). -/
private lemma integrable_d_of_marg_eq
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    (ν : Measure (α × β)) (h_marg : ν.map Prod.fst = P) :
    Integrable (fun p => d p.1 p.2) ν := by
  have h_meas : Measurable (fun p : α × β => d p.1 p.2) := by measurability
  have h_ν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have h_univ : ν Set.univ = (ν.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]; simp
    rw [h_univ, h_marg, measure_univ]
  refine Integrable.mono' (g := fun _ : α × β =>
      (Finset.univ.sup' Finset.univ_nonempty (fun q : α × β => |d q.1 q.2|)))
    (integrable_const _) h_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have h_le : |d p.1 p.2| ≤
      Finset.univ.sup' Finset.univ_nonempty (fun q : α × β => |d q.1 q.2|) :=
    Finset.le_sup' (f := fun q : α × β => |d q.1 q.2|) (Finset.mem_univ p)
  simpa [Real.norm_eq_abs] using h_le

set_option linter.unusedSectionVars false in
/-- Helper: per-pair convexity bound at the `klDiv` level.

For any two feasible joints `ν₁, ν₂` (`Prod.fst`-marginal = `P`, distortion
bounds `D₁, D₂`), the rate-distortion function at the mixed threshold
`lam * D₁ + (1 - lam) * D₂` is bounded by the convex combination of the per-
witness `klDiv` values. AC of `νᵢ` to its product marginal is extracted by
case-splitting on `klDiv νᵢ marg(νᵢ) = ∞` (top side trivializes the bound). -/
private lemma rateDistortionFunction_le_convex_combo_of_pair
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (D₁ D₂ : ℝ)
    (ν₁ ν₂ : Measure (α × β))
    (h_marg₁ : ν₁.map Prod.fst = P) (h_marg₂ : ν₂.map Prod.fst = P)
    (h_dist₁ : expectedDistortion d ν₁ ≤ D₁)
    (h_dist₂ : expectedDistortion d ν₂ ≤ D₂) :
    rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
      ≤ ENNReal.ofReal lam
          * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
        + ENNReal.ofReal (1 - lam)
          * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
  -- ν₁, ν₂ are probability measures (X-marginal = P, P is prob).
  have h_ν₁_prob : IsProbabilityMeasure ν₁ := by
    refine ⟨?_⟩
    have h_univ : ν₁ Set.univ = (ν₁.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]; simp
    rw [h_univ, h_marg₁, measure_univ]
  have h_ν₂_prob : IsProbabilityMeasure ν₂ := by
    refine ⟨?_⟩
    have h_univ : ν₂ Set.univ = (ν₂.map Prod.fst) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]; simp
    rw [h_univ, h_marg₂, measure_univ]
  -- Integrability of d under νᵢ.
  have h_int₁ : Integrable (fun p => d p.1 p.2) ν₁ :=
    integrable_d_of_marg_eq d P ν₁ h_marg₁
  have h_int₂ : Integrable (fun p => d p.1 p.2) ν₂ :=
    integrable_d_of_marg_eq d P ν₂ h_marg₂
  set marg1 := (ν₁.map Prod.fst).prod (ν₁.map Prod.snd)
  set marg2 := (ν₂.map Prod.fst).prod (ν₂.map Prod.snd)
  -- Case-split on klDiv νᵢ margᵢ = ∞.
  by_cases h_top1 : klDiv ν₁ marg1 = ∞
  · -- klDiv ν₁ = ∞. If ofReal lam ≠ 0 the RHS is ∞.
    by_cases hlam_eq0 : lam = 0
    · -- lam = 0 boundary: RHS = ofReal 0 * ∞ + ofReal 1 * klDiv ν₂ = klDiv ν₂.
      subst hlam_eq0
      have h_lhs_eq : (0 : ℝ) * D₁ + (1 - 0) * D₂ = D₂ := by ring
      rw [h_lhs_eq]
      simp only [ENNReal.ofReal_zero, zero_mul, zero_add, sub_zero, ENNReal.ofReal_one,
        one_mul]
      exact rateDistortionFunction_le_of_feasible d P D₂ ν₂ h_marg₂ h_dist₂
    · -- lam > 0: RHS = ∞.
      have hlam_pos : 0 < lam := lt_of_le_of_ne hlam₀ (Ne.symm hlam_eq0)
      have h_lam_ne_zero : ENNReal.ofReal lam ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hlam_pos
      rw [h_top1, ENNReal.mul_top h_lam_ne_zero]
      exact le_top
  by_cases h_top2 : klDiv ν₂ marg2 = ∞
  · -- klDiv ν₂ = ∞. If ofReal (1-lam) ≠ 0 the RHS is ∞.
    by_cases hlam_eq1 : lam = 1
    · subst hlam_eq1
      have h_lhs_eq : (1 : ℝ) * D₁ + (1 - 1) * D₂ = D₁ := by ring
      rw [h_lhs_eq]
      simp only [sub_self, ENNReal.ofReal_zero, zero_mul, add_zero, ENNReal.ofReal_one,
        one_mul]
      exact rateDistortionFunction_le_of_feasible d P D₁ ν₁ h_marg₁ h_dist₁
    · have h1lam_pos : 0 < 1 - lam :=
        sub_pos.mpr (lt_of_le_of_ne hlam₁ hlam_eq1)
      have h_1lam_ne_zero : ENNReal.ofReal (1 - lam) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr h1lam_pos
      rw [h_top2, ENNReal.mul_top h_1lam_ne_zero]
      have h_rhs : ENNReal.ofReal lam * klDiv ν₁ marg1 + ∞ = ∞ := by
        rw [add_comm]; exact top_add _
      rw [h_rhs]
      exact le_top
  -- Both finite: extract AC and apply Step D via the mixture witness.
  have h_ac₁ : ν₁ ≪ marg1 := (klDiv_ne_top_iff.mp h_top1).1
  have h_ac₂ : ν₂ ≪ marg2 := (klDiv_ne_top_iff.mp h_top2).1
  -- Mixture is feasible at the mixed threshold.
  obtain ⟨h_mix_marg, h_mix_dist⟩ :=
    mixtureMeasure_feasible hlam₀ hlam₁ P d ν₁ ν₂ h_marg₁ h_marg₂
      h_dist₁ h_dist₂ h_int₁ h_int₂
  -- LHS ≤ klDiv (mix) marg(mix).
  have h_feas := rateDistortionFunction_le_of_feasible d P
    (lam * D₁ + (1 - lam) * D₂) (mixtureMeasure lam ν₁ ν₂) h_mix_marg h_mix_dist
  -- Convexity from Step D.
  have h_conv := klDiv_mixture_joint_convex d P hlam₀ hlam₁ D₁ D₂ ν₁ ν₂
    h_marg₁ h_marg₂ h_int₁ h_int₂ h_dist₁ h_dist₂ h_ac₁ h_ac₂
  exact h_feas.trans h_conv

set_option linter.unusedSectionVars false in
/-- **R(D) 凸性 (仮説なし、有限アルファベット版)**: Step A-D 全段 discharge.

Recovered direct proof (2026-05-26, post-Round 3 rewrite recovery): rather
than going through the now-`sorry`'d parent `rateDistortionFunction_convexOn`,
this declaration discharges convexity directly at the `iInf` level. For any
pair of feasible witnesses `ν₁, ν₂` (at `D₁, D₂`), the mixture
`mixtureMeasure lam ν₁ ν₂` is feasible at `lam D₁ + (1-lam) D₂`
(`mixtureMeasure_feasible`), and `klDiv` of the mixture is bounded by the
convex combination of per-witness `klDiv` values via the local Step D
discharge `klDiv_mixture_joint_convex`. AC of `νᵢ` to its product-marginal is
extracted by case-splitting on `klDiv νᵢ margᵢ = ∞` (`klDiv_ne_top_iff`);
boundary cases `lam = 0` and `lam = 1` reduce to `rateDistortionFunction_le_of_feasible`
applied to one of the witnesses. The `iInf` push-through is handled by
`le_iInf_add_iInf` together with `ENNReal.mul_iInf_of_ne` (for the strict
interior `0 < lam < 1`) and direct case-split at the boundary.

This bypasses the parent's transitive `sorry` (load-bearing `h_klDiv_conv`
retreat) by reusing only the genuine pieces: Step D (`klDiv_mixture_joint_convex`,
unchanged) and basic feasibility / `iInf` bookkeeping. Result: proof done
(0 sorry, 0 @residual). -/
theorem rateDistortionFunction_convexOn_pmf
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (D₁ D₂ : ℝ) :
    rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
      ≤ ENNReal.ofReal lam * rateDistortionFunction d P D₁
        + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P D₂ := by
  -- Strategy: case-split on lam ∈ {0, 1} (boundary) vs strict interior. On the
  -- interior, push the scalars inside ALL iInf binders via repeated
  -- `ENNReal.mul_iInf_of_ne`, then apply `ENNReal.le_iInf_add_iInf` plus inner
  -- `le_iInf` peels, and finish with the pair helper.
  rcases eq_or_lt_of_le hlam₀ with hlam_eq0 | hlam_pos
  · -- lam = 0 boundary: substitute and reduce both sides to R(P, D₂).
    rw [← hlam_eq0]
    have h_eq : (0 : ℝ) * D₁ + (1 - 0) * D₂ = D₂ := by ring
    rw [h_eq]
    simp [ENNReal.ofReal_zero, ENNReal.ofReal_one]
  rcases eq_or_lt_of_le hlam₁ with hlam_eq1 | hlam_lt1
  · -- lam = 1 boundary.
    subst hlam_eq1
    have h_eq : (1 : ℝ) * D₁ + (1 - 1) * D₂ = D₁ := by ring
    rw [h_eq]
    simp [ENNReal.ofReal_one, ENNReal.ofReal_zero]
  -- Strict interior 0 < lam < 1.
  have h1lam_pos : (0 : ℝ) < 1 - lam := sub_pos.mpr hlam_lt1
  have h_lam_ne0 : ENNReal.ofReal lam ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hlam_pos
  have h_lam_ne_top : ENNReal.ofReal lam ≠ ∞ := ENNReal.ofReal_ne_top
  have h_1lam_ne0 : ENNReal.ofReal (1 - lam) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr h1lam_pos
  have h_1lam_ne_top : ENNReal.ofReal (1 - lam) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Unfold R(P, Dᵢ) and push scalars through the iInf binders on RHS.
  unfold rateDistortionFunction
  -- LHS: ⨅ ν (_ : ν.map fst = P) (_ : ED d ν ≤ lam*D₁+(1-lam)*D₂), klDiv ν m
  -- RHS: ofReal lam * (⨅ ν h h', klDiv ν m₁) + ofReal(1-lam) * (⨅ ν h h', klDiv ν m₂).
  -- Apply `le_iInf_add_iInf` first: for each (ν₁, ν₂), prove LHS ≤
  -- ofReal lam * (⨅ h h', klDiv ν₁ m₁) + ofReal(1-lam) * (⨅ h h', klDiv ν₂ m₂).
  rw [ENNReal.mul_iInf_of_ne h_lam_ne0 h_lam_ne_top,
      ENNReal.mul_iInf_of_ne h_1lam_ne0 h_1lam_ne_top]
  refine ENNReal.le_iInf_add_iInf ?_
  intro ν₁ ν₂
  -- Per pair (ν₁, ν₂): bound by case-splitting on whether they are feasible.
  -- For feasible ν₁ (with h_marg₁ : ν₁.map fst = P, h_dist₁ : ED d ν₁ ≤ D₁),
  -- the inner iInf collapses to klDiv ν₁ m₁ (no functional binders).
  -- For non-feasible ν₁, the inner iInf is ⊤ since no witnesses exist.
  by_cases hf₁ : ν₁.map Prod.fst = P ∧ expectedDistortion d ν₁ ≤ D₁
  · by_cases hf₂ : ν₂.map Prod.fst = P ∧ expectedDistortion d ν₂ ≤ D₂
    · obtain ⟨h_marg₁, h_dist₁⟩ := hf₁
      obtain ⟨h_marg₂, h_dist₂⟩ := hf₂
      -- Collapse inner iInf via `iInf_pos`.
      have h_inner₁ :
          (⨅ (_ : ν₁.map Prod.fst = P) (_ : expectedDistortion d ν₁ ≤ D₁),
              klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)))
            = klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)) := by
        rw [iInf_pos h_marg₁, iInf_pos h_dist₁]
      have h_inner₂ :
          (⨅ (_ : ν₂.map Prod.fst = P) (_ : expectedDistortion d ν₂ ≤ D₂),
              klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)))
            = klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
        rw [iInf_pos h_marg₂, iInf_pos h_dist₂]
      rw [h_inner₁, h_inner₂]
      exact rateDistortionFunction_le_convex_combo_of_pair d P hlam₀ hlam₁ D₁ D₂
        ν₁ ν₂ h_marg₁ h_marg₂ h_dist₁ h_dist₂
    · -- ν₂ not feasible: the right iInf = ⊤, so RHS-side = ⊤.
      have h_inner₂ :
          (⨅ (_ : ν₂.map Prod.fst = P) (_ : expectedDistortion d ν₂ ≤ D₂),
              klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)))
            = ⊤ := by
        by_cases h_marg₂ : ν₂.map Prod.fst = P
        · have h_dist_neg : ¬ expectedDistortion d ν₂ ≤ D₂ := fun h => hf₂ ⟨h_marg₂, h⟩
          rw [iInf_pos h_marg₂, iInf_neg h_dist_neg]
        · rw [iInf_neg h_marg₂]
      rw [h_inner₂]
      have h_top_mul : ENNReal.ofReal (1 - lam) * ⊤ = ⊤ :=
        ENNReal.mul_top h_1lam_ne0
      rw [h_top_mul]
      rw [show (ENNReal.ofReal lam *
          (⨅ (_ : ν₁.map Prod.fst = P) (_ : expectedDistortion d ν₁ ≤ D₁),
              klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)))) + (⊤ : ℝ≥0∞) = ⊤
        from by rw [add_comm]; exact top_add _]
      exact le_top
  · -- ν₁ not feasible: left iInf = ⊤.
    have h_inner₁ :
        (⨅ (_ : ν₁.map Prod.fst = P) (_ : expectedDistortion d ν₁ ≤ D₁),
            klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)))
          = ⊤ := by
      by_cases h_marg₁ : ν₁.map Prod.fst = P
      · have h_dist_neg : ¬ expectedDistortion d ν₁ ≤ D₁ := fun h => hf₁ ⟨h_marg₁, h⟩
        rw [iInf_pos h_marg₁, iInf_neg h_dist_neg]
      · rw [iInf_neg h_marg₁]
    rw [h_inner₁]
    have h_top_mul : ENNReal.ofReal lam * ⊤ = ⊤ :=
      ENNReal.mul_top h_lam_ne0
    rw [h_top_mul]
    rw [show (⊤ : ℝ≥0∞) + ENNReal.ofReal (1 - lam) *
        (⨅ (_ : ν₂.map Prod.fst = P) (_ : expectedDistortion d ν₂ ≤ D₂),
            klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd))) = ⊤ from
      top_add _]
    exact le_top

end InformationTheory.Shannon
