import Common2026.Meta.EntryPoint
import Common2026.Shannon.Bridge
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Pinsker 不等式 (TV と KL の bridge)

Common2026 B-5 ムーンショット ([`docs/shannon/pinsker-moonshot-plan.md`])。

有限アルファベット `α` 上の確率測度 `P, Q` (`P ≪ Q`) について
`tvNorm P Q ≤ √((klDiv P Q).toReal)` を Lean 化。
ここで `tvNorm P Q := (1/2) * Σ |P.real {x} - Q.real {x}|`。

**注**: 本シードでは elementary な calculus を抑えるため、**定数 √2 ゆるい版**
`TV ≤ √(KL)` (`Real.sqrt` の中に `/2` が無い) で commit。Cover-Thomas 11.6 strict
形 `TV ≤ √(KL/2)` は `klFun(t) ≥ 3(t-1)^2/(2(t+2))` を要し、本シードでは扱わない。
Sanov / Strong Stein など下流 qualitative 用途には定数の √2 落ちは影響なし。

## 主定理

* `klFun_eq_sub_sqrt_sq_add` (private) — 算術的恒等式: `klFun t = (1 - √t)^2 + 2 * √t * klFun (√t)`
* `klFun_ge_sub_sqrt_sq` — 点別 Bretagnolle-Huber 下界: `(√t - 1)^2 ≤ klFun t` for `t ≥ 0`
* `tvNorm` — 有限 alphabet 上 2 確率測度間の TV ノルム
* `tvNorm_le_sqrt_klDiv` — Pinsker (弱形): `tvNorm P Q ≤ √(klDiv P Q).toReal`

## 戦略

1. **Phase A (Real-only)**: 算術恒等式
   `klFun(t) = (1-√t)^2 + 2*√t * klFun(√t)` for `t ≥ 0`
   から `klFun_nonneg` で `klFun(t) ≥ (1-√t)^2`。Bretagnolle-Huber 下界。

2. **Phase B**: discrete Pinsker
   - per-element: `Q.real{x} * klFun(P.real{x}/Q.real{x}) ≥ (√P.real{x} - √Q.real{x})^2`
     (algebraic, no calculus)
   - 和: `(klDiv P Q).toReal ≥ Σ (√p_x - √q_x)^2` (Hellinger² ≤ KL)
   - Cauchy-Schwarz on `|p - q| = |√p - √q| * (√p + √q)`:
     `(Σ |p-q|)^2 ≤ Σ (√p-√q)^2 * Σ (√p+√q)^2`
   - `Σ (√p+√q)^2 ≤ Σ 2(p+q) = 4` (algebra)
   - `(2 tvNorm)^2 ≤ H² * 4 ≤ 4 (klDiv P Q).toReal`
   - `tvNorm² ≤ (klDiv P Q).toReal` ⟹ `tvNorm ≤ √(klDiv P Q).toReal`
-/

namespace InformationTheory.Shannon.Pinsker

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## Phase A — Bretagnolle-Huber 点別不等式 -/

/-- 算術恒等式: `klFun(t) = (1-√t)^2 + 2*√t * klFun(√t)` for `t ≥ 0`.

非自明な代数: `klFun(t) - (1-√t)^2 = 2√t * klFun(√t)`、よって
`klFun ≥ 0` から `klFun(t) ≥ (1-√t)^2` (Bretagnolle-Huber 下界)。 -/
private lemma klFun_eq_sub_sqrt_sq_add (t : ℝ) (ht : 0 ≤ t) :
    klFun t = (1 - Real.sqrt t) ^ 2 + 2 * Real.sqrt t * klFun (Real.sqrt t) := by
  -- 展開: klFun(t) = t log t + 1 - t, klFun(√t) = √t log(√t) + 1 - √t.
  -- (√t)^2 = t, log(√t) = (log t)/2 ⟹ 2*√t*klFun(√t) = t log t + 2√t - 2 t.
  -- (1-√t)^2 + 2√t klFun(√t) = (1 - 2√t + t) + (t log t + 2√t - 2t) = t log t + 1 - t = klFun(t).
  unfold klFun
  have h_sqrt_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have h_log_sqrt : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht
  -- 2 * √t * (√t * log(√t)) = 2 * (√t * √t) * log(√t) = 2 * t * (log t / 2) = t * log t
  have h_2sqrt_logsqrt : 2 * Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t))
      = t * Real.log t := by
    rw [show 2 * Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t))
          = 2 * (Real.sqrt t * Real.sqrt t) * Real.log (Real.sqrt t) by ring,
      h_sqrt_sq, h_log_sqrt]
    ring
  -- 展開して `nlinarith` / `linarith` で潰す
  have h_expand :
      2 * Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t) + 1 - Real.sqrt t)
        = t * Real.log t + 2 * Real.sqrt t - 2 * t := by
    have e1 : 2 * Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t) + 1 - Real.sqrt t)
        = 2 * Real.sqrt t * (Real.sqrt t * Real.log (Real.sqrt t))
          + 2 * Real.sqrt t * 1 - 2 * (Real.sqrt t * Real.sqrt t) := by ring
    rw [e1, h_2sqrt_logsqrt, h_sqrt_sq]
    ring
  rw [h_expand]
  have h_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  nlinarith [h_sq]

/-- 点別 Bretagnolle-Huber 下界: `(√t - 1)^2 ≤ klFun t` for `t ≥ 0`.

(`(√t - 1)^2 = (1 - √t)^2` で、`(√t)^2 = t` から `(√t - 1)^2 = (t-1)^2/(√t+1)^2`。) -/
@[entry_point]
lemma klFun_ge_sub_sqrt_sq (t : ℝ) (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ klFun t := by
  have h_id := klFun_eq_sub_sqrt_sq_add t ht
  have h_sqrt_nn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h_klFun_sqrt : 0 ≤ klFun (Real.sqrt t) := klFun_nonneg h_sqrt_nn
  have h_sq : (Real.sqrt t - 1) ^ 2 = (1 - Real.sqrt t) ^ 2 := by ring
  rw [h_sq, h_id]
  have h_rest : 0 ≤ 2 * Real.sqrt t * klFun (Real.sqrt t) := by positivity
  linarith

/-! ## Phase B — 有限 alphabet TV + Pinsker 主定理 -/

variable {α : Type*} [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

omit [DecidableEq α] [MeasurableSingletonClass α] in
/-- 有限 alphabet 上の 2 確率測度間の全変動 (TV) ノルム。 -/
noncomputable def tvNorm (P Q : Measure α) : ℝ :=
  (1/2) * ∑ x : α, |P.real {x} - Q.real {x}|


omit [DecidableEq α] in
/-- **Pinsker 不等式 (弱形)**: 有限 alphabet 上の `P ≪ Q` 確率測度について
`tvNorm P Q ≤ √(klDiv P Q).toReal`。

シャープな `TV ≤ √(KL/2)` (Cover-Thomas 11.6 strict) ではなく、定数 1
(本来の Pinsker 定数 1/√2 の √2 倍ゆるい) 版。`klFun(t) ≥ (√t - 1)^2` (Bretagnolle-
Huber) + Cauchy-Schwarz on `|p - q| = |√p - √q| * (√p + √q)` 経由。 -/
@[entry_point]
theorem tvNorm_le_sqrt_klDiv
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    tvNorm P Q ≤ Real.sqrt (klDiv P Q).toReal := by
  classical
  -- Step 1: 各 x で rnDeriv 識別 — `(P.rnDeriv Q x) * Q{x} = P{x}`.
  have h_rnD_enn : ∀ x, (P.rnDeriv Q x) * Q {x} = P {x} := by
    intro x
    have h_wd : Q.withDensity (P.rnDeriv Q) = P :=
      Measure.withDensity_rnDeriv_eq P Q hPQ
    have h1 : (Q.withDensity (P.rnDeriv Q)) {x} = P {x} := by rw [h_wd]
    rw [withDensity_apply _ (measurableSet_singleton x),
      lintegral_singleton] at h1
    exact h1
  -- Step 2: KL.toReal = Σ_x Q.real{x} * klFun(rnDeriv x)
  have h_KL_eq : (klDiv P Q).toReal
      = ∑ x : α, Q.real {x} * klFun (P.rnDeriv Q x).toReal := by
    rw [toReal_klDiv_eq_integral_klFun hPQ]
    -- ∫ x, klFun (P.rnDeriv Q x).toReal ∂Q = ∑ x : α, Q.real {x} * klFun (...)
    have h_int : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q := by
      refine ⟨(stronglyMeasurable_klFun.comp_measurable
        ((Measure.measurable_rnDeriv P Q).ennreal_toReal)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
      exact ENNReal.sum_lt_top.mpr fun _ _ =>
        ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
    rw [integral_fintype h_int]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_eq_mul]
  -- Step 3: per-element Bretagnolle-Huber: Q.real{x} * klFun(rnDeriv x)
  --         ≥ (√P.real{x} - √Q.real{x})^2.
  have h_per_x : ∀ x : α,
      (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2
        ≤ Q.real {x} * klFun (P.rnDeriv Q x).toReal := by
    intro x
    by_cases hQx : Q.real {x} = 0
    · -- Q.real{x} = 0 ⟹ P.real{x} = 0 (by AC); both sides 0
      have hQ_ne : Q {x} = 0 := by
        rw [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top Q _)] at hQx
        exact hQx
      have hP_ne : P {x} = 0 := hPQ hQ_ne
      have hPx : P.real {x} = 0 := by rw [Measure.real, hP_ne]; rfl
      simp [hQx, hPx]
    -- Q.real{x} > 0
    have hQx_pos : 0 < Q.real {x} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hQx)
    have hQ_ne : Q {x} ≠ 0 := by
      intro h
      apply hQx
      rw [Measure.real, h]; rfl
    -- rnDeriv .toReal = P.real / Q.real
    have h_rnD_real : (P.rnDeriv Q x).toReal * Q.real {x} = P.real {x} := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
    have h_rnD_div : (P.rnDeriv Q x).toReal = P.real {x} / Q.real {x} := by
      field_simp
      linarith [h_rnD_real]
    -- Apply Bretagnolle-Huber and multiply by Q.real{x}.
    have h_t_nn : 0 ≤ (P.rnDeriv Q x).toReal := ENNReal.toReal_nonneg
    have h_bh : (Real.sqrt ((P.rnDeriv Q x).toReal) - 1)^2
        ≤ klFun ((P.rnDeriv Q x).toReal) :=
      klFun_ge_sub_sqrt_sq _ h_t_nn
    -- (√(p/q) - 1)^2 = (√p - √q)^2 / q
    have hP_nn : 0 ≤ P.real {x} := measureReal_nonneg
    have hQ_pos_R : 0 < Q.real {x} := hQx_pos
    have h_sqrt_div : Real.sqrt ((P.rnDeriv Q x).toReal)
        = Real.sqrt (P.real {x}) / Real.sqrt (Q.real {x}) := by
      rw [h_rnD_div, Real.sqrt_div measureReal_nonneg]
    -- 計算: q * (√(p/q) - 1)^2 = q * ((√p - √q)/√q)^2 = (√p - √q)^2
    have h_sqrt_q_pos : 0 < Real.sqrt (Q.real {x}) := Real.sqrt_pos.mpr hQx_pos
    have h_sqrt_q_ne : Real.sqrt (Q.real {x}) ≠ 0 := h_sqrt_q_pos.ne'
    have h_sqrt_q_sq : Real.sqrt (Q.real {x}) * Real.sqrt (Q.real {x}) = Q.real {x} :=
      Real.mul_self_sqrt measureReal_nonneg
    have h_id : Q.real {x} * (Real.sqrt ((P.rnDeriv Q x).toReal) - 1)^2
        = (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2 := by
      rw [h_sqrt_div]
      -- Q.real{x} * ((√p/√q) - 1)^2 = Q.real{x} * (√p - √q)^2 / q
      have : Real.sqrt (P.real {x}) / Real.sqrt (Q.real {x}) - 1
          = (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x})) / Real.sqrt (Q.real {x}) := by
        field_simp
      rw [this, div_pow]
      rw [show (Real.sqrt (Q.real {x}))^2 = Q.real {x} from
        sq (Real.sqrt (Q.real {x})) ▸ h_sqrt_q_sq]
      field_simp
    have h_bh_scaled : (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2
        ≤ Q.real {x} * klFun ((P.rnDeriv Q x).toReal) := by
      have := mul_le_mul_of_nonneg_left h_bh hQx_pos.le
      linarith [h_id]
    exact h_bh_scaled
  -- Step 4: KL.toReal ≥ Σ_x (√P.real{x} - √Q.real{x})^2 = H^2 (Hellinger^2)
  have h_KL_ge_H2 : ∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2
      ≤ (klDiv P Q).toReal := by
    rw [h_KL_eq]
    exact Finset.sum_le_sum fun x _ => h_per_x x
  -- Step 5: Cauchy-Schwarz
  -- (Σ |p - q|)^2 = (Σ |√p - √q| * (√p + √q))^2
  --              ≤ Σ (√p - √q)^2 * Σ (√p + √q)^2
  -- with r_x := |√p - √q| * (√p + √q), f_x := (√p - √q)^2, g_x := (√p + √q)^2.
  -- But we have r_x = |p - q|, not in the right Cauchy-Schwarz format directly.
  -- Use `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`:
  --   (Σ r_i)^2 ≤ (Σ f_i)(Σ g_i) when r_i^2 = f_i * g_i.
  -- Set r_x := |P.real{x} - Q.real{x}|, f_x := (√p - √q)^2, g_x := (√p + √q)^2.
  -- Verify r_x^2 = f_x * g_x: (|p-q|)^2 = (p-q)^2 = (√p - √q)^2 * (√p + √q)^2.
  have h_CS : (∑ x : α, |P.real {x} - Q.real {x}|)^2
      ≤ (∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2)
        * (∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset α) ?_ ?_ ?_
    · intro i _; exact sq_nonneg _
    · intro i _; exact sq_nonneg _
    · intro i _
      -- |p - q|^2 = (p - q)^2 = (√p - √q)^2 * (√p + √q)^2
      have h_sq_p : Real.sqrt (P.real {i}) * Real.sqrt (P.real {i}) = P.real {i} :=
        Real.mul_self_sqrt measureReal_nonneg
      have h_sq_q : Real.sqrt (Q.real {i}) * Real.sqrt (Q.real {i}) = Q.real {i} :=
        Real.mul_self_sqrt measureReal_nonneg
      have h_diff_sq : (Real.sqrt (P.real {i}) - Real.sqrt (Q.real {i}))^2
          * (Real.sqrt (P.real {i}) + Real.sqrt (Q.real {i}))^2
          = (P.real {i} - Q.real {i})^2 := by
        have : (Real.sqrt (P.real {i}) - Real.sqrt (Q.real {i}))
            * (Real.sqrt (P.real {i}) + Real.sqrt (Q.real {i}))
            = P.real {i} - Q.real {i} := by
          ring_nf
          rw [show Real.sqrt (P.real {i})^2 = P.real {i} from
            sq (Real.sqrt (P.real {i})) ▸ h_sq_p,
            show Real.sqrt (Q.real {i})^2 = Q.real {i} from
              sq (Real.sqrt (Q.real {i})) ▸ h_sq_q]
        calc (Real.sqrt (P.real {i}) - Real.sqrt (Q.real {i}))^2
            * (Real.sqrt (P.real {i}) + Real.sqrt (Q.real {i}))^2
            = ((Real.sqrt (P.real {i}) - Real.sqrt (Q.real {i}))
              * (Real.sqrt (P.real {i}) + Real.sqrt (Q.real {i})))^2 := by ring
          _ = (P.real {i} - Q.real {i})^2 := by rw [this]
      rw [show |P.real {i} - Q.real {i}|^2 = (P.real {i} - Q.real {i})^2 from sq_abs _,
        ← h_diff_sq]
  -- Step 6: Σ (√p + √q)^2 ≤ 4 (using (a+b)^2 ≤ 2(a^2 + b^2) = 2(p+q), sum = 2*2 = 4)
  have h_sum_sq_sum_le_4 : ∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2 ≤ 4 := by
    have h_per_x_le : ∀ x : α,
        (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2 ≤ 2 * (P.real {x} + Q.real {x}) := by
      intro x
      have h_sq_p : Real.sqrt (P.real {x})^2 = P.real {x} :=
        Real.sq_sqrt measureReal_nonneg
      have h_sq_q : Real.sqrt (Q.real {x})^2 = Q.real {x} :=
        Real.sq_sqrt measureReal_nonneg
      have h_AM_GM : 2 * (Real.sqrt (P.real {x}) * Real.sqrt (Q.real {x}))
          ≤ Real.sqrt (P.real {x})^2 + Real.sqrt (Q.real {x})^2 := by
        nlinarith [sq_nonneg (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))]
      nlinarith [h_sq_p, h_sq_q, h_AM_GM]
    have h_sum_le : ∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2
        ≤ ∑ x : α, 2 * (P.real {x} + Q.real {x}) :=
      Finset.sum_le_sum fun x _ => h_per_x_le x
    have h_sum_PQ : ∑ x : α, 2 * (P.real {x} + Q.real {x}) = 4 := by
      have h_P : ∑ x : α, P.real {x} = 1 := by
        rw [show (∑ x : α, P.real {x}) = ∑ x ∈ (Finset.univ : Finset α), P.real {x} from rfl,
          sum_measureReal_singleton]
        rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
        simp [measureReal_def, measure_univ]
      have h_Q : ∑ x : α, Q.real {x} = 1 := by
        rw [show (∑ x : α, Q.real {x}) = ∑ x ∈ (Finset.univ : Finset α), Q.real {x} from rfl,
          sum_measureReal_singleton]
        rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
        simp [measureReal_def, measure_univ]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, h_P, h_Q]
      ring
    linarith
  -- Step 7: combine. (2 * tvNorm)^2 = (Σ |p-q|)^2 ≤ H² * 4 ≤ 4 * KL.toReal.
  -- So tvNorm^2 ≤ KL.toReal, hence tvNorm ≤ √KL.toReal.
  have h_sum_abs : ∑ x : α, |P.real {x} - Q.real {x}| = 2 * tvNorm P Q := by
    unfold tvNorm; ring
  have h_KL_nn : 0 ≤ (klDiv P Q).toReal := ENNReal.toReal_nonneg
  have h_H2_nn : 0 ≤ ∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h_sum_sum_sq_nn :
      0 ≤ ∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- (2 * tvNorm)^2 ≤ Σ (√p-√q)^2 * Σ (√p+√q)^2 ≤ Σ (√p-√q)^2 * 4 ≤ KL.toReal * 4
  have h_main_sq : (2 * tvNorm P Q)^2 ≤ 4 * (klDiv P Q).toReal := by
    have h1 : (2 * tvNorm P Q)^2 ≤
        (∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2) *
        (∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2) := by
      rw [← h_sum_abs]; exact h_CS
    have h2 : (∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2) *
        (∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2)
        ≤ (∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2) * 4 :=
      mul_le_mul_of_nonneg_left h_sum_sq_sum_le_4 h_H2_nn
    have h3 : (∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2) * 4
        ≤ (klDiv P Q).toReal * 4 :=
      mul_le_mul_of_nonneg_right h_KL_ge_H2 (by norm_num)
    linarith
  -- tvNorm^2 ≤ KL.toReal
  have h_tv_sq : (tvNorm P Q)^2 ≤ (klDiv P Q).toReal := by
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have : (2 * tvNorm P Q)^2 = 4 * (tvNorm P Q)^2 := by ring
    linarith
  -- tvNorm ≤ √(KL.toReal)
  exact Real.le_sqrt_of_sq_le h_tv_sq

end InformationTheory.Shannon.Pinsker
