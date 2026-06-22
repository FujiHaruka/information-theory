import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Pinsker.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sharp Pinsker inequality (constant `1/√2`)

For probability measures `P, Q` on a finite alphabet `α` with `P ≪ Q`, the sharp Cover–Thomas
(11.6) form of Pinsker's inequality: `tvNorm P Q ≤ √((klDiv P Q).toReal / 2)`. The total-variation
norm `tvNorm` is shared with the weak form in `Pinsker/Basic.lean`.

## Main statements

* `klFun_sharp_lower` — the pointwise sharp bound `3 * (t - 1)^2 ≤ 2 * (t + 2) * klFun t`.
* `tvNorm_le_sqrt_klDiv_div_two` — the sharp Pinsker inequality
  `tvNorm P Q ≤ √((klDiv P Q).toReal / 2)`.

## Implementation notes

The pointwise bound is obtained from the auxiliary `H t := 2 (t + 2) · klFun t - 3 (t - 1)^2`,
whose second derivative `4 (log t + 1/t - 1)` is nonnegative on `(0, ∞)` and which has a minimum
of `0` at `t = 1`. The global bound follows by a per-element application together with the
Cauchy–Schwarz step and `∑ (p + 2q) = 3`.
-/

namespace InformationTheory.Shannon.PinskerSharp

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ### Pointwise sharp Pinsker inequality -/

/-- The auxiliary function `H t := 2 (t + 2) · klFun t - 3 (t - 1)^2`. -/
private noncomputable def H (t : ℝ) : ℝ := 2 * (t + 2) * klFun t - 3 * (t - 1) ^ 2

/-- Closed form of the first derivative of `H`. -/
private noncomputable def Hderiv (t : ℝ) : ℝ := 4 * ((t + 1) * Real.log t - 2 * (t - 1))

/-- Closed form of the second derivative of `H`. -/
private noncomputable def Hderiv2 (t : ℝ) : ℝ := 4 * (Real.log t + 1 / t - 1)

private lemma hasDerivAt_H {t : ℝ} (ht : 0 < t) :
    HasDerivAt H (Hderiv t) t := by
  unfold H Hderiv
  have ht_ne : t ≠ 0 := ht.ne'
  -- derivative of `2 * (t + 2)` is `2`
  have h1 : HasDerivAt (fun t : ℝ => 2 * (t + 2)) 2 t := by
    have hid : HasDerivAt (fun t : ℝ => t + 2) 1 t :=
      (hasDerivAt_id t).add_const 2
    have := hid.const_mul 2
    simpa using this
  have h2 : HasDerivAt klFun (Real.log t) t := hasDerivAt_klFun ht_ne
  have h3 : HasDerivAt (fun t => 2 * (t + 2) * klFun t)
      (2 * klFun t + 2 * (t + 2) * Real.log t) t := by
    have hmul := h1.mul h2
    convert hmul using 1
  -- derivative of `3 * (t - 1) ^ 2` is `6 * (t - 1)`
  have hid' : HasDerivAt (fun t : ℝ => t - 1) 1 t :=
    (hasDerivAt_id t).sub_const 1
  have h4 : HasDerivAt (fun t : ℝ => (t - 1) ^ 2) (2 * (t - 1) * 1) t := by
    have := hid'.pow 2
    simpa using this
  have h5 : HasDerivAt (fun t => 3 * (t - 1) ^ 2) (3 * (2 * (t - 1) * 1)) t :=
    h4.const_mul 3
  have h_sub := h3.sub h5
  convert h_sub using 1
  unfold klFun
  ring

private lemma hasDerivAt_Hderiv {t : ℝ} (ht : 0 < t) :
    HasDerivAt Hderiv (Hderiv2 t) t := by
  unfold Hderiv Hderiv2
  have ht_ne : t ≠ 0 := ht.ne'
  -- derivative of `(t + 1) * log t`: `1 * log t + (t + 1) * (1/t)`
  have h_log : HasDerivAt Real.log (1 / t) t := by
    rw [one_div]; exact Real.hasDerivAt_log ht_ne
  have h_t1 : HasDerivAt (fun t : ℝ => t + 1) 1 t :=
    (hasDerivAt_id t).add_const 1
  have h_t1_log : HasDerivAt (fun t : ℝ => (t + 1) * Real.log t)
      (1 * Real.log t + (t + 1) * (1 / t)) t :=
    h_t1.mul h_log
  -- derivative of `2 * (t - 1)`: `2`
  have h_tm1 : HasDerivAt (fun t : ℝ => t - 1) 1 t :=
    (hasDerivAt_id t).sub_const 1
  have h_2tm1 : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 t := by
    have := h_tm1.const_mul 2
    simpa using this
  -- derivative of `(t+1)*log t - 2*(t-1)`: `log t + (t+1)/t - 2`
  have h_inner := h_t1_log.sub h_2tm1
  -- derivative of `4 * (...)`: `4 * (log t + (t+1)/t - 2)`
  have h_4 := h_inner.const_mul 4
  convert h_4 using 1
  field_simp
  ring

private lemma Hderiv2_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ Hderiv2 t := by
  unfold Hderiv2
  have h := Real.one_sub_inv_le_log_of_pos ht
  -- h : 1 - t⁻¹ ≤ log t, want: 0 ≤ 4 * (log t + 1/t - 1)
  have h2 : 1 - 1 / t ≤ Real.log t := by
    rw [one_div]; exact h
  linarith

private lemma Hderiv_one : Hderiv 1 = 0 := by
  unfold Hderiv
  simp

private lemma H_one : H 1 = 0 := by
  unfold H
  rw [klFun_one]
  ring


private lemma Hderiv_monotoneOn : MonotoneOn Hderiv (Set.Ioi (0 : ℝ)) := by
  have hconv : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi 0
  have hint : interior (Set.Ioi (0 : ℝ)) = Set.Ioi (0 : ℝ) := interior_Ioi
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := Hderiv2) hconv ?_ ?_ ?_
  · -- ContinuousOn Hderiv (Ioi 0)
    intro t ht
    have ht_pos : 0 < t := ht
    exact (hasDerivAt_Hderiv ht_pos).continuousAt.continuousWithinAt
  · -- HasDerivWithinAt Hderiv (Hderiv2 _) (interior (Ioi 0)) x
    intro t ht
    rw [hint] at ht
    exact (hasDerivAt_Hderiv ht).hasDerivWithinAt
  · intro t ht
    rw [hint] at ht
    exact Hderiv2_nonneg ht

private lemma continuous_H : Continuous H := by
  unfold H
  fun_prop

private lemma H_monotoneOn_Ici_one : MonotoneOn H (Set.Ici (1 : ℝ)) := by
  have hconv : Convex ℝ (Set.Ici (1 : ℝ)) := convex_Ici 1
  have hint : interior (Set.Ici (1 : ℝ)) = Set.Ioi (1 : ℝ) := interior_Ici
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := Hderiv) hconv
    continuous_H.continuousOn ?_ ?_
  · intro t ht
    rw [hint] at ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    exact (hasDerivAt_H ht_pos).hasDerivWithinAt
  · intro t ht
    rw [hint] at ht
    -- ht : 1 < t. Want 0 ≤ Hderiv t.
    -- Hderiv is monotone on (0, ∞), Hderiv 1 = 0, t > 1, so Hderiv t ≥ Hderiv 1 = 0.
    have h1_ioi : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by simp
    have ht_ioi : t ∈ Set.Ioi (0 : ℝ) := by
      show (0 : ℝ) < t; exact zero_lt_one.trans ht
    have hmono := Hderiv_monotoneOn h1_ioi ht_ioi ht.le
    rw [Hderiv_one] at hmono
    exact hmono


private lemma H_antitoneOn_Ioc_zero_one : AntitoneOn H (Set.Ioc (0 : ℝ) 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ioc (0 : ℝ) 1)
    (convex_Ioc 0 1) continuous_H.continuousOn (f' := Hderiv) ?_ ?_
  · intro t ht
    rw [interior_Ioc] at ht
    exact (hasDerivAt_H ht.1).hasDerivWithinAt
  · intro t ht
    rw [interior_Ioc] at ht
    -- monotone Hderiv on (0, ∞) + Hderiv 1 = 0 + t < 1 ⟹ Hderiv t ≤ Hderiv 1 = 0
    have ht1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have ht_ioi : t ∈ Set.Ioi (0 : ℝ) := ht.1
    have hmono := Hderiv_monotoneOn ht_ioi ht1 ht.2.le
    rw [Hderiv_one] at hmono
    exact hmono

private lemma H_nonneg_of_pos {t : ℝ} (ht : 0 < t) : 0 ≤ H t := by
  rcases le_or_gt t 1 with h_le | h_gt
  · -- t ≤ 1: AntitoneOn (0, 1] H, t ≤ 1, so H t ≥ H 1 = 0.
    have ht_mem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht, h_le⟩
    have h1_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_refl 1⟩
    have h := H_antitoneOn_Ioc_zero_one ht_mem h1_mem h_le
    rw [H_one] at h
    exact h
  · -- t > 1: MonotoneOn [1, ∞) H, 1 ≤ t, so H t ≥ H 1 = 0.
    have h1_mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.self_mem_Ici
    have ht_mem : t ∈ Set.Ici (1 : ℝ) := h_gt.le
    have h := H_monotoneOn_Ici_one h1_mem ht_mem h_gt.le
    rw [H_one] at h
    exact h

/-- The pointwise sharp Pinsker inequality `3 · (t - 1)^2 ≤ 2 · (t + 2) · klFun t` for `t ≥ 0`. -/
@[entry_point]
lemma klFun_sharp_lower (t : ℝ) (ht : 0 ≤ t) :
    3 * (t - 1) ^ 2 ≤ 2 * (t + 2) * klFun t := by
  rcases eq_or_lt_of_le ht with h_eq | h_pos
  · -- t = 0
    rw [← h_eq, klFun_zero]
    ring_nf
    norm_num
  · -- t > 0
    have h_H := H_nonneg_of_pos h_pos
    unfold H at h_H
    linarith

/-! ### Sharp Pinsker inequality -/

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- per-element sharp bound: `3·(p-q)² / (2·(p+2q)) ≤ q · klFun(p/q)` for finite-measure setup. -/
private lemma per_element_sharp
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (x : α) :
    3 * (P.real {x} - Q.real {x}) ^ 2 / (2 * (P.real {x} + 2 * Q.real {x}))
      ≤ Q.real {x} * klFun (P.rnDeriv Q x).toReal := by
  -- identify the Radon–Nikodym derivative
  have h_rnD_enn : (P.rnDeriv Q x) * Q {x} = P {x} := by
    have h_wd : Q.withDensity (P.rnDeriv Q) = P :=
      Measure.withDensity_rnDeriv_eq P Q hPQ
    have h1 : (Q.withDensity (P.rnDeriv Q)) {x} = P {x} := by rw [h_wd]
    rw [withDensity_apply _ (measurableSet_singleton x),
      lintegral_singleton] at h1
    exact h1
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
  -- apply the pointwise bound
  have h_t_nn : 0 ≤ (P.rnDeriv Q x).toReal := ENNReal.toReal_nonneg
  have h_sharp : 3 * ((P.rnDeriv Q x).toReal - 1) ^ 2
      ≤ 2 * ((P.rnDeriv Q x).toReal + 2) * klFun ((P.rnDeriv Q x).toReal) :=
    klFun_sharp_lower _ h_t_nn
  -- algebra: scale by Q.real{x}
  -- t = p/q, want 3(p-q)²/(2(p+2q)) ≤ q · klFun(t).
  -- From h_sharp: 3(t-1)² ≤ 2(t+2) klFun(t).
  -- Multiply by q²: 3(p-q)² ≤ 2(p+2q) q · klFun(t) (since q·(t-1) = p-q, q·(t+2) = p+2q).
  -- Then divide by 2(p+2q): 3(p-q)²/(2(p+2q)) ≤ q · klFun(t).
  set p := P.real {x}
  set q := Q.real {x}
  have hp_nn : 0 ≤ p := measureReal_nonneg
  -- p + 2q > 0
  have hpq_pos : 0 < p + 2 * q := by linarith
  -- key algebraic identities
  have h_qtm1 : q * ((P.rnDeriv Q x).toReal - 1) = p - q := by
    rw [h_rnD_div]
    field_simp
  have h_qtp2 : q * ((P.rnDeriv Q x).toReal + 2) = p + 2 * q := by
    rw [h_rnD_div]
    field_simp
  -- multiply h_sharp by q^2 ≥ 0
  have hq_sq_nn : 0 ≤ q ^ 2 := sq_nonneg q
  have h_sharp_q2 : q ^ 2 * (3 * ((P.rnDeriv Q x).toReal - 1) ^ 2)
      ≤ q ^ 2 * (2 * ((P.rnDeriv Q x).toReal + 2) * klFun ((P.rnDeriv Q x).toReal)) :=
    mul_le_mul_of_nonneg_left h_sharp hq_sq_nn
  -- LHS: q^2 * 3 * (t-1)^2 = 3 * (q*(t-1))^2 = 3*(p-q)^2
  have h_LHS : q ^ 2 * (3 * ((P.rnDeriv Q x).toReal - 1) ^ 2) = 3 * (p - q) ^ 2 := by
    have : q ^ 2 * ((P.rnDeriv Q x).toReal - 1) ^ 2
        = (q * ((P.rnDeriv Q x).toReal - 1)) ^ 2 := by ring
    rw [show q ^ 2 * (3 * ((P.rnDeriv Q x).toReal - 1) ^ 2)
        = 3 * (q ^ 2 * ((P.rnDeriv Q x).toReal - 1) ^ 2) by ring, this, h_qtm1]
  -- RHS: q^2 * 2 * (t+2) * klFun(t) = 2 * q * (q*(t+2)) * klFun(t) = 2*q*(p+2q)*klFun(t)
  have h_RHS : q ^ 2 * (2 * ((P.rnDeriv Q x).toReal + 2) * klFun ((P.rnDeriv Q x).toReal))
      = 2 * (p + 2 * q) * (q * klFun ((P.rnDeriv Q x).toReal)) := by
    have : q ^ 2 * (2 * ((P.rnDeriv Q x).toReal + 2) * klFun ((P.rnDeriv Q x).toReal))
        = 2 * (q * ((P.rnDeriv Q x).toReal + 2)) * (q * klFun ((P.rnDeriv Q x).toReal)) := by
      ring
    rw [this, h_qtp2]
  rw [h_LHS, h_RHS] at h_sharp_q2
  -- Now: 3 * (p - q)^2 ≤ 2 * (p + 2*q) * (q * klFun(t))
  -- Divide by 2 * (p + 2*q) > 0
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (p + 2 * q))]
  linarith

/-- The sharp Pinsker inequality: for probability measures `P ≪ Q` on a finite alphabet,
`tvNorm P Q ≤ √((klDiv P Q).toReal / 2)`. -/
@[entry_point]
theorem tvNorm_le_sqrt_klDiv_div_two
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) :
    Pinsker.tvNorm P Q ≤ Real.sqrt ((klDiv P Q).toReal / 2) := by
  classical
  -- Step 1: KL.toReal = Σ x, Q.real{x} · klFun((P.rnDeriv Q x).toReal)
  have h_KL_eq : (klDiv P Q).toReal
      = ∑ x : α, Q.real {x} * klFun (P.rnDeriv Q x).toReal := by
    rw [toReal_klDiv_eq_integral_klFun hPQ]
    have h_int : Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q := by
      refine ⟨(stronglyMeasurable_klFun.comp_measurable
        ((Measure.measurable_rnDeriv P Q).ennreal_toReal)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
      exact ENNReal.sum_lt_top.mpr fun _ _ =>
        ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
    rw [integral_fintype h_int]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_eq_mul]
  -- Step 2: Σ x, 3·(p_x - q_x)² / (2·(p_x + 2·q_x)) ≤ KL.toReal
  have h_KL_ge : ∑ x : α, 3 * (P.real {x} - Q.real {x}) ^ 2
        / (2 * (P.real {x} + 2 * Q.real {x}))
      ≤ (klDiv P Q).toReal := by
    rw [h_KL_eq]
    exact Finset.sum_le_sum fun x _ => per_element_sharp P Q hPQ x
  -- Step 3: Cauchy-Schwarz with
  -- r_x := |p_x - q_x|, f_x := (p-q)²/(p+2q) (or 0 if p+2q = 0), g_x := p+2q
  -- f_x · g_x = (p-q)² = r_x²
  -- (Σ r)² ≤ (Σ f) · (Σ g)
  -- Σ g = 1 + 2*1 = 3
  -- So (Σ r)² ≤ 3·Σ f ≤ 3·(2/3)·KL = 2·KL.
  -- Define f safely (= 0 when denom is 0). We split: where p+2q > 0 use the fraction;
  -- where p+2q = 0, both p=q=0 so f_x = 0 anyway.
  -- Implement: use the same fraction expression directly; verify r²= f·g pointwise.
  have h_CS : (∑ x : α, |P.real {x} - Q.real {x}|) ^ 2
      ≤ (∑ x : α, (P.real {x} - Q.real {x}) ^ 2 / (P.real {x} + 2 * Q.real {x}))
        * (∑ x : α, (P.real {x} + 2 * Q.real {x})) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset α) ?_ ?_ ?_
    · intro i _
      -- 0 ≤ (p - q)² / (p + 2q)
      have hp_nn : (0 : ℝ) ≤ P.real {i} := measureReal_nonneg
      have hq_nn : (0 : ℝ) ≤ Q.real {i} := measureReal_nonneg
      have h_den_nn : (0 : ℝ) ≤ P.real {i} + 2 * Q.real {i} := by linarith
      exact div_nonneg (sq_nonneg _) h_den_nn
    · intro i _
      -- 0 ≤ p + 2q
      have hp_nn : (0 : ℝ) ≤ P.real {i} := measureReal_nonneg
      have hq_nn : (0 : ℝ) ≤ Q.real {i} := measureReal_nonneg
      linarith
    · intro i _
      -- |p - q|² = (p - q)² / (p + 2q) · (p + 2q)
      have hp_nn : (0 : ℝ) ≤ P.real {i} := measureReal_nonneg
      have hq_nn : (0 : ℝ) ≤ Q.real {i} := measureReal_nonneg
      have h_abs_sq : |P.real {i} - Q.real {i}| ^ 2 = (P.real {i} - Q.real {i}) ^ 2 := sq_abs _
      rw [h_abs_sq]
      by_cases hd : P.real {i} + 2 * Q.real {i} = 0
      · -- p + 2q = 0 ⟹ p = q = 0 (both nonneg)
        have hq0 : Q.real {i} = 0 := by linarith
        have hp0 : P.real {i} = 0 := by linarith
        rw [hp0, hq0]
        ring
      · -- p + 2q ≠ 0
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
  -- Step 4: Σ (p + 2q) = 1 + 2 = 3
  have h_sum_g : ∑ x : α, (P.real {x} + 2 * Q.real {x}) = 3 := by
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
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h_P, h_Q]
    ring
  -- Step 5: Σ (p-q)²/(p+2q) ≤ (2/3) · KL.toReal
  have h_sum_f_le : ∑ x : α, (P.real {x} - Q.real {x}) ^ 2 / (P.real {x} + 2 * Q.real {x})
      ≤ (2 / 3) * (klDiv P Q).toReal := by
    -- Σ f ≤ (2/3) KL.toReal since Σ 3·f / 2 ≤ KL.toReal
    have hf_id : ∀ x, 3 * (P.real {x} - Q.real {x}) ^ 2
          / (2 * (P.real {x} + 2 * Q.real {x}))
        = (3 / 2) * ((P.real {x} - Q.real {x}) ^ 2 / (P.real {x} + 2 * Q.real {x})) := by
      intro x
      have hp_nn : (0 : ℝ) ≤ P.real {x} := measureReal_nonneg
      have hq_nn : (0 : ℝ) ≤ Q.real {x} := measureReal_nonneg
      have h_den_nn : (0 : ℝ) ≤ P.real {x} + 2 * Q.real {x} := by linarith
      by_cases hd : P.real {x} + 2 * Q.real {x} = 0
      · have hq0 : Q.real {x} = 0 := by linarith
        have hp0 : P.real {x} = 0 := by linarith
        rw [hp0, hq0]
        ring
      · field_simp
    have h_3_2_sum_le : (3 / 2) * ∑ x : α, (P.real {x} - Q.real {x}) ^ 2
          / (P.real {x} + 2 * Q.real {x})
        ≤ (klDiv P Q).toReal := by
      have h_sum_id : ∑ x : α, 3 * (P.real {x} - Q.real {x}) ^ 2
            / (2 * (P.real {x} + 2 * Q.real {x}))
          = (3 / 2) * ∑ x : α, (P.real {x} - Q.real {x}) ^ 2
            / (P.real {x} + 2 * Q.real {x}) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => hf_id x
      linarith [h_sum_id ▸ h_KL_ge]
    linarith
  -- Step 6: combine
  have h_tv_sq_eq : 2 * Pinsker.tvNorm P Q = ∑ x : α, |P.real {x} - Q.real {x}| := by
    unfold Pinsker.tvNorm; ring
  have h_main_sq : (2 * Pinsker.tvNorm P Q) ^ 2 ≤ 2 * (klDiv P Q).toReal := by
    rw [h_tv_sq_eq]
    calc (∑ x : α, |P.real {x} - Q.real {x}|) ^ 2
        ≤ (∑ x : α, (P.real {x} - Q.real {x}) ^ 2 / (P.real {x} + 2 * Q.real {x}))
          * (∑ x : α, (P.real {x} + 2 * Q.real {x})) := h_CS
      _ = (∑ x : α, (P.real {x} - Q.real {x}) ^ 2 / (P.real {x} + 2 * Q.real {x})) * 3 := by
          rw [h_sum_g]
      _ ≤ ((2 / 3) * (klDiv P Q).toReal) * 3 :=
          mul_le_mul_of_nonneg_right h_sum_f_le (by norm_num)
      _ = 2 * (klDiv P Q).toReal := by ring
  -- (2*TV)² = 4 TV², so 4 TV² ≤ 2 KL, hence TV² ≤ KL/2
  have h_tv_sq : Pinsker.tvNorm P Q ^ 2 ≤ (klDiv P Q).toReal / 2 := by
    have : (2 * Pinsker.tvNorm P Q) ^ 2 = 4 * Pinsker.tvNorm P Q ^ 2 := by ring
    linarith
  exact Real.le_sqrt_of_sq_le h_tv_sq

end InformationTheory.Shannon.PinskerSharp
