import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Pinsker's inequality (total variation and Kullback–Leibler divergence)

For probability measures `P, Q` on a finite alphabet `α` with `P ≪ Q`, the total-variation
norm `tvNorm P Q := (1/2) * ∑ x, |P.real {x} - Q.real {x}|` is bounded by the square root of
the Kullback–Leibler divergence: `tvNorm P Q ≤ √((klDiv P Q).toReal)`.

This is the weak form with constant `1`; the sharp Cover–Thomas (11.6) form
`tvNorm P Q ≤ √((klDiv P Q).toReal / 2)` is proved separately in `Pinsker/Sharp.lean`.

## Main definitions

* `tvNorm` — the total-variation norm between two probability measures on a finite alphabet.

## Main statements

* `klFun_ge_sub_sqrt_sq` — the pointwise Bretagnolle–Huber bound `(√t - 1)^2 ≤ klFun t`.
* `tvNorm_le_sqrt_klDiv` — Pinsker's inequality (weak form) `tvNorm P Q ≤ √((klDiv P Q).toReal)`.

## Implementation notes

The proof combines the pointwise Bretagnolle–Huber bound `klFun t ≥ (√t - 1)^2` with the
Cauchy–Schwarz factorization `|p - q| = |√p - √q| · (√p + √q)`, bounding `∑ (√p + √q)^2 ≤ 4`.
-/

namespace InformationTheory.Shannon.Pinsker

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ### Bretagnolle–Huber pointwise inequality -/

private lemma klFun_eq_sub_sqrt_sq_add (t : ℝ) (ht : 0 ≤ t) :
    klFun t = (1 - Real.sqrt t) ^ 2 + 2 * Real.sqrt t * klFun (Real.sqrt t) := by
  -- klFun t = t log t + 1 - t, klFun (√t) = √t log(√t) + 1 - √t;
  -- (√t)^2 = t, log(√t) = (log t)/2 give (1-√t)^2 + 2√t klFun(√t) = t log t + 1 - t.
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
  -- expand and close with `nlinarith` / `linarith`
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

/-- The pointwise Bretagnolle–Huber bound `(√t - 1)^2 ≤ klFun t` for `t ≥ 0`. -/
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

/-! ### Cauchy-Schwarz and sum bound helpers -/

private lemma finset_cs_sqrt_sq
    {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    (∑ i : α, |p i - q i|)^2
      ≤ (∑ i : α, (Real.sqrt (p i) - Real.sqrt (q i))^2)
        * (∑ i : α, (Real.sqrt (p i) + Real.sqrt (q i))^2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset α) ?_ ?_ ?_
  · intro i _; exact sq_nonneg _
  · intro i _; exact sq_nonneg _
  · intro i _
    have h_sq_p : Real.sqrt (p i) * Real.sqrt (p i) = p i :=
      Real.mul_self_sqrt (hp i)
    have h_sq_q : Real.sqrt (q i) * Real.sqrt (q i) = q i :=
      Real.mul_self_sqrt (hq i)
    have h_diff_sq : (Real.sqrt (p i) - Real.sqrt (q i))^2
        * (Real.sqrt (p i) + Real.sqrt (q i))^2
        = (p i - q i)^2 := by
      have : (Real.sqrt (p i) - Real.sqrt (q i))
          * (Real.sqrt (p i) + Real.sqrt (q i))
          = p i - q i := by
        ring_nf
        rw [show Real.sqrt (p i)^2 = p i from
          sq (Real.sqrt (p i)) ▸ h_sq_p,
          show Real.sqrt (q i)^2 = q i from
            sq (Real.sqrt (q i)) ▸ h_sq_q]
      calc (Real.sqrt (p i) - Real.sqrt (q i))^2
          * (Real.sqrt (p i) + Real.sqrt (q i))^2
          = ((Real.sqrt (p i) - Real.sqrt (q i))
            * (Real.sqrt (p i) + Real.sqrt (q i)))^2 := by ring
        _ = (p i - q i)^2 := by rw [this]
    rw [show |p i - q i|^2 = (p i - q i)^2 from sq_abs _, ← h_diff_sq]

private lemma sum_sqrt_add_sq_le_four
    {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i : α, p i = 1) (hqsum : ∑ i : α, q i = 1) :
    ∑ i : α, (Real.sqrt (p i) + Real.sqrt (q i))^2 ≤ 4 := by
  have h_per_i : ∀ i : α,
      (Real.sqrt (p i) + Real.sqrt (q i))^2 ≤ 2 * (p i + q i) := by
    intro i
    have h_sq_p : Real.sqrt (p i)^2 = p i := Real.sq_sqrt (hp i)
    have h_sq_q : Real.sqrt (q i)^2 = q i := Real.sq_sqrt (hq i)
    have h_AM_GM : 2 * (Real.sqrt (p i) * Real.sqrt (q i))
        ≤ Real.sqrt (p i)^2 + Real.sqrt (q i)^2 := by
      nlinarith [sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i))]
    nlinarith [h_sq_p, h_sq_q, h_AM_GM]
  have h_sum_le : ∑ i : α, (Real.sqrt (p i) + Real.sqrt (q i))^2
      ≤ ∑ i : α, 2 * (p i + q i) :=
    Finset.sum_le_sum fun i _ => h_per_i i
  have h_sum_PQ : ∑ i : α, 2 * (p i + q i) = 4 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hpsum, hqsum]; ring
  linarith

/-! ### Total variation and Pinsker's inequality -/

variable {α : Type*} [Fintype α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

omit [DecidableEq α] [MeasurableSingletonClass α] in
/-- The total-variation norm between two probability measures on a finite alphabet. -/
noncomputable def tvNorm (P Q : Measure α) : ℝ :=
  (1/2) * ∑ x : α, |P.real {x} - Q.real {x}|


omit [DecidableEq α] in
/-- Pinsker's inequality (weak form, constant `1`): for probability measures `P ≪ Q` on a
finite alphabet, `tvNorm P Q ≤ √((klDiv P Q).toReal)`. -/
@[entry_point]
theorem tvNorm_le_sqrt_klDiv
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    tvNorm P Q ≤ Real.sqrt (klDiv P Q).toReal := by
  classical
  -- Step 1: identify the Radon–Nikodym derivative at each `x`: `(P.rnDeriv Q x) * Q{x} = P{x}`.
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
    -- compute: q * (√(p/q) - 1)^2 = q * ((√p - √q)/√q)^2 = (√p - √q)^2
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
  -- Step 5: Cauchy-Schwarz (via finset_cs_sqrt_sq)
  have h_CS : (∑ x : α, |P.real {x} - Q.real {x}|)^2
      ≤ (∑ x : α, (Real.sqrt (P.real {x}) - Real.sqrt (Q.real {x}))^2)
        * (∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2) :=
    finset_cs_sqrt_sq _ _ (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
  -- Step 6: Σ (√p + √q)^2 ≤ 4 (via sum_sqrt_add_sq_le_four)
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
  have h_sum_sq_sum_le_4 : ∑ x : α, (Real.sqrt (P.real {x}) + Real.sqrt (Q.real {x}))^2 ≤ 4 :=
    sum_sqrt_add_sq_le_four _ _ (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
      h_P h_Q
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
