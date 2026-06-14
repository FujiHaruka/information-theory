import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.SeedLemmas
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.PmfLogBounds
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremFullDischarge.SmoothInstantiation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Outer `N` construction — max-error closed form

Part file split from `ShannonTheoremFullDischarge`. Constructs the outer `N₀` that
simultaneously controls the TV smoothing error and the smooth-channel achievability.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

open InformationTheory.Shannon (pmfLog)

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Outer `N` construction

For any `R < capacity W` and `ε > 0`, we build an `N₀` such that for every
`n ≥ N₀` we can simultaneously:

* pick `δ_n ∈ (0, δ_B]` with `2 n δ_n < ε/2` (so the TV bound contributes ≤ `ε/2`);
* build a code at the smooth channel `W_smooth δ_n` with `max-error < ε/2`.

The construction:

1. The uniform smooth-capacity bound gives `p_full := pSmooth p₀ δ_p` (full support)
   with `R < I_lb < I(p_full; W_smooth δ)` for all `δ ∈ (0, δ_B]`.
2. Choose an interior rate `R' := (R + I_lb)/2 < I_lb` for the closed-form
   average-error code; we then upgrade to max-error at rate `R` via the
   subcode trick (giving `max-error ≤ 2 · avg < ε/2`).
3. Choose `δ_n := min(δ_B, ε/(16(n+1)))` and check `2 n δ_n < ε/4 < ε/2`.
4. Bound `V_Y(δ_n), V_Z(δ_n) ≤ const + 2 · (log(n+1))²` via the closed-form
   pmfLog bounds, using `1/δ_n ≤ (1/δ_B + 16/ε)·(n+1)` and `(a+b)² ≤ 2a²+2b²`.
5. The closed-form `channelCodingSmoothMinN` is then `O((log(n+1))²)`;
   `exists_N_log_sq_plus_const_le_n` produces the outer `N₀`.
-/

lemma one_le_mul_div_mul_of_le_one {a b p d : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hp_pos : 0 < p) (hp_le : p ≤ 1) (hd_pos : 0 < d) (hd_le : d ≤ 1) :
    (1 : ℝ) ≤ a * b / (p * d) := by
  have hpd_pos : 0 < p * d := mul_pos hp_pos hd_pos
  have hab_ge : (1 : ℝ) ≤ a * b := by nlinarith
  have hpd_le_one : p * d ≤ 1 := by
    have : p * d ≤ 1 * 1 := mul_le_mul hp_le hd_le hd_pos.le (by norm_num)
    linarith
  rw [le_div_iff₀ hpd_pos]
  calc (1 : ℝ) * (p * d) ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left hpd_le_one (by norm_num)
    _ = 1 := by norm_num
    _ ≤ a * b := hab_ge

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Every entry of `pSmooth p₀ δ` is at least `δ / |α|`. -/
lemma pSmooth_ge {p₀ : α → ℝ} (hp₀ : p₀ ∈ stdSimplex ℝ α)
    {δ : ℝ} (_hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) (a : α) :
    δ / (Fintype.card α : ℝ) ≤ pSmooth p₀ δ a := by
  unfold pSmooth uniformInput
  have h1 : 0 ≤ (1 - δ) * p₀ a := mul_nonneg (by linarith) (hp₀.1 a)
  have h_eq : δ * (Fintype.card α : ℝ)⁻¹ = δ / (Fintype.card α : ℝ) := by
    rw [div_eq_mul_inv]
  linarith [h_eq]

/-- For `δ_n := min(δ_B, ε/(16(n+1)))`, `1/δ_n ≤ (1/δ_B + 16/ε)·(n+1)`. -/
lemma one_div_smooth_n_le
    {δ_B ε : ℝ} (hδ_B_pos : 0 < δ_B) (hε_pos : 0 < ε) (n : ℕ) :
    let δ_n : ℝ := min δ_B (ε / (16 * ((n : ℝ) + 1)))
    1 / δ_n ≤ (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) := by
  intro δ_n
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hε_n_pos : (0 : ℝ) < ε / (16 * ((n : ℝ) + 1)) := by positivity
  have hδ_n_pos : 0 < δ_n := lt_min hδ_B_pos hε_n_pos
  -- 1/min(a,b) = max(1/a, 1/b) for a,b > 0; bound by sum.
  have h_inv_le : 1 / δ_n ≤ 1 / δ_B + 1 / (ε / (16 * ((n : ℝ) + 1))) := by
    -- 1/δ_n ≤ 1/δ_B and 1/δ_n ≤ 1/(ε/(16(n+1))).
    have h1 : δ_n ≤ δ_B := min_le_left _ _
    have h2 : δ_n ≤ ε / (16 * ((n : ℝ) + 1)) := min_le_right _ _
    have h_inv1 : 1 / δ_B ≤ 1 / δ_n := one_div_le_one_div_of_le hδ_n_pos h1
    have h_inv2 : 1 / (ε / (16 * ((n : ℝ) + 1))) ≤ 1 / δ_n :=
      one_div_le_one_div_of_le hδ_n_pos h2
    -- max(1/δ_B, 1/(ε/(16(n+1)))) ≤ 1/δ_n ≤ max + 0 ≤ sum.
    -- Easier: a/δ_n_min uses 1/δ_n = max(1/δ_B, 1/(...))
    -- But simpler: split cases.
    rcases le_or_gt δ_B (ε / (16 * ((n : ℝ) + 1))) with h_case | h_case
    · -- δ_n = δ_B
      have : δ_n = δ_B := by simp [δ_n, min_eq_left h_case]
      rw [this]
      have h_pos2 : 0 < 1 / (ε / (16 * ((n : ℝ) + 1))) := by positivity
      linarith
    · -- δ_n = ε/(16(n+1))
      have : δ_n = ε / (16 * ((n : ℝ) + 1)) := by
        simp [δ_n, min_eq_right h_case.le]
      rw [this]
      have h_pos1 : 0 < 1 / δ_B := by positivity
      linarith
  -- Now `1/(ε/(16(n+1))) = 16(n+1)/ε`.
  have h_inv_eq : (1 : ℝ) / (ε / (16 * ((n : ℝ) + 1))) = 16 * ((n : ℝ) + 1) / ε := by
    rw [one_div, inv_div]
  rw [h_inv_eq] at h_inv_le
  -- 1/δ_B + 16(n+1)/ε ≤ (1/δ_B + 16/ε)(n+1).
  -- (1/δ_B + 16/ε)(n+1) = (n+1)/δ_B + 16(n+1)/ε ≥ 1/δ_B + 16(n+1)/ε iff (n+1)/δ_B ≥ 1/δ_B, true.
  have h_target : 1 / δ_B + 16 * ((n : ℝ) + 1) / ε ≤ (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) := by
    have h_n1_ge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h1 : 1 / δ_B ≤ ((n : ℝ) + 1) / δ_B := by
      rw [div_le_div_iff₀ hδ_B_pos hδ_B_pos]
      have h2 : (1 : ℝ) * δ_B ≤ ((n : ℝ) + 1) * δ_B :=
        mul_le_mul_of_nonneg_right h_n1_ge_one hδ_B_pos.le
      linarith
    have h_expand : (1 / δ_B + 16 / ε) * ((n : ℝ) + 1)
        = ((n : ℝ) + 1) / δ_B + 16 * ((n : ℝ) + 1) / ε := by
      rw [add_mul]
      rw [show (1 / δ_B) * ((n : ℝ) + 1) = ((n : ℝ) + 1) / δ_B from by
        rw [one_div, inv_mul_eq_div]]
      rw [show (16 / ε) * ((n : ℝ) + 1) = 16 * ((n : ℝ) + 1) / ε from by
        rw [div_mul_eq_mul_div]]
    linarith
  exact h_inv_le.trans h_target

lemma typicalSetMinN_le_div_add_two {η ε : ℝ} (hηε : 0 < η * ε ^ 2)
    {V : ℝ} (hV : 0 ≤ V) :
    (typicalSetMinN V η ε : ℝ) ≤ V / (η * ε ^ 2) + 2 := by
  unfold typicalSetMinN
  have h_div_nn : 0 ≤ V / (η * ε ^ 2) := div_nonneg hV hηε.le
  have h_ceil_le : (Nat.ceil (V / (η * ε ^ 2)) : ℝ)
      ≤ V / (η * ε ^ 2) + 1 := by
    have := Nat.ceil_lt_add_one h_div_nn
    linarith
  have h_max_le : ((max 1 (Nat.ceil (V / (η * ε ^ 2)) + 1) : ℕ) : ℝ)
      ≤ V / (η * ε ^ 2) + 2 := by
    have h_1_le : (1 : ℝ) ≤ V / (η * ε ^ 2) + 2 := by linarith
    have h_ceil_plus_1_le :
        ((Nat.ceil (V / (η * ε ^ 2)) + 1 : ℕ) : ℝ)
          ≤ V / (η * ε ^ 2) + 2 := by
      push_cast; linarith
    have h_max_real : ((max 1 (Nat.ceil (V / (η * ε ^ 2)) + 1) : ℕ) : ℝ)
        ≤ max 1 (V / (η * ε ^ 2) + 2) := by
      push_cast
      have h1 : (1 : ℝ) ≤ max 1 (V / (η * ε ^ 2) + 2) := le_max_left _ _
      have h2 : (Nat.ceil (V / (η * ε ^ 2)) + 1 : ℝ)
          ≤ max 1 (V / (η * ε ^ 2) + 2) := by
        exact le_max_of_le_right (by linarith)
      exact max_le h1 h2
    have h_max_le_rhs : max 1 (V / (η * ε ^ 2) + 2) ≤ V / (η * ε ^ 2) + 2 :=
      max_le h_1_le le_rfl
    linarith
  exact h_max_le

lemma log_div_le_log_add_log_add_log_succ
    {c s δ m : ℝ} (hc_pos : 0 < c) (hs_pos : 0 < s) (hδ_pos : 0 < δ) (hm1_pos : 0 < m + 1)
    (h_one_div_le : 1 / δ ≤ s * (m + 1)) :
    Real.log (c / δ) ≤ Real.log c + Real.log s + Real.log (m + 1) := by
  have h_eq1 : c / δ = c * (1 / δ) := by
    rw [one_div, div_eq_mul_inv]
  have h_lhs_le : c / δ ≤ c * s * (m + 1) := by
    rw [h_eq1]
    have h_mul_le : c * (1 / δ) ≤ c * (s * (m + 1)) :=
      mul_le_mul_of_nonneg_left h_one_div_le hc_pos.le
    linarith [h_mul_le]
  have h_lhs_pos : (0 : ℝ) < c / δ := by positivity
  have h_mid_pos : (0 : ℝ) < c * s := mul_pos hc_pos hs_pos
  have h_log_le := Real.log_le_log h_lhs_pos h_lhs_le
  have h_log_split : Real.log (c * s * (m + 1))
      = Real.log c + Real.log s + Real.log (m + 1) := by
    rw [Real.log_mul h_mid_pos.ne' hm1_pos.ne', Real.log_mul hc_pos.ne' hs_pos.ne']
  linarith [h_log_le, h_log_split]

lemma two_mul_lt_half_of_le_div
    {ε δ : ℝ} (hε : 0 < ε) (n : ℕ) (hn1_pos : (0 : ℝ) < (n : ℝ) + 1)
    (hδ_le : δ ≤ ε / (16 * ((n : ℝ) + 1))) :
    2 * (n : ℝ) * δ < ε / 2 := by
  have h_target : 2 * (n : ℝ) * δ ≤ 2 * (n : ℝ) * (ε / (16 * ((n : ℝ) + 1))) := by
    have hn_nn : 0 ≤ 2 * (n : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hδ_le hn_nn
  have h_simp : 2 * (n : ℝ) * (ε / (16 * ((n : ℝ) + 1)))
      = ε * ((n : ℝ) / ((n : ℝ) + 1)) / 8 := by
    field_simp; ring
  have h_n_n1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1_pos]
    linarith
  have h_n_n1_nn : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
    apply div_nonneg (Nat.cast_nonneg _) hn1_pos.le
  have h_chain : ε * ((n : ℝ) / ((n : ℝ) + 1)) / 8 < ε / 2 := by
    have h1 : ε * ((n : ℝ) / ((n : ℝ) + 1)) ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left h_n_n1 hε.le
    have h2 : ε * 1 / 8 < ε / 2 := by linarith
    have h3 : ε * ((n : ℝ) / ((n : ℝ) + 1)) / 8 ≤ ε * 1 / 8 := by
      exact div_le_div_of_nonneg_right h1 (by norm_num)
    linarith
  linarith [h_target, h_simp, h_chain]

lemma sq_le_two_mul_sq_add_two_mul_sq_of_nonneg_of_le_add
    {x K y : ℝ} (hx : 0 ≤ x) (hxle : x ≤ K + y) :
    x ^ 2 ≤ 2 * K ^ 2 + 2 * y ^ 2 := by
  have h_abs : x ≤ |K| + |y| := by
    have h1 : K ≤ |K| := le_abs_self _
    have h2 : y ≤ |y| := le_abs_self _
    linarith
  have h_sq : x ^ 2 = |x| ^ 2 := by rw [sq_abs]
  rw [h_sq]
  have h_sq_le : |x| ^ 2 ≤ (|K| + |y|) ^ 2 := by
    have h_abs_nn : 0 ≤ |x| := abs_nonneg _
    rw [abs_of_nonneg hx]
    exact pow_le_pow_left₀ hx h_abs 2
  refine h_sq_le.trans ?_
  have h_expand : (|K| + |y|) ^ 2 ≤ 2 * |K| ^ 2 + 2 * |y| ^ 2 := by
    have h := sq_nonneg (|K| - |y|)
    nlinarith
  have h_eq1 : |K| ^ 2 = K ^ 2 := sq_abs _
  have h_eq2 : |y| ^ 2 = y ^ 2 := sq_abs _
  linarith

lemma logSq_div_le_two_sq_add_two_logSq {c s δ m : ℝ} (hc : 1 ≤ c) (hs_pos : 0 < s)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) (hm1_pos : 0 < m + 1)
    (h_one_div_le : 1 / δ ≤ s * (m + 1)) :
    (Real.log (c / δ)) ^ 2
      ≤ 2 * (Real.log c + Real.log s) ^ 2 + 2 * (Real.log (m + 1)) ^ 2 := by
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have h_div_ge : (1 : ℝ) ≤ c / δ := by
    rw [le_div_iff₀ hδ_pos]; nlinarith
  have h_log_nn : 0 ≤ Real.log (c / δ) := Real.log_nonneg h_div_ge
  have h_log_le : Real.log (c / δ) ≤ (Real.log c + Real.log s) + Real.log (m + 1) :=
    log_div_le_log_add_log_add_log_succ hc_pos hs_pos hδ_pos hm1_pos h_one_div_le
  exact sq_le_two_mul_sq_add_two_mul_sq_of_nonneg_of_le_add h_log_nn h_log_le

lemma typicalSetMinN_real_le_two_coef_logSq_add
    {V A Lsq C D η3 εg : ℝ} (hs : 0 < η3 * εg ^ 2) (hV : 0 ≤ V)
    (hVA : V ≤ A + 2 * Lsq) (hLsq : 0 ≤ Lsq)
    (hC : C = 2 / (η3 * εg ^ 2)) (hD : A / (η3 * εg ^ 2) + 2 ≤ D) :
    (typicalSetMinN V η3 εg : ℝ) ≤ 2 * C * Lsq + D := by
  have hbase : (typicalSetMinN V η3 εg : ℝ) ≤ V / (η3 * εg ^ 2) + 2 :=
    typicalSetMinN_le_div_add_two hs hV
  have h_div_le : V / (η3 * εg ^ 2) ≤ (A + 2 * Lsq) / (η3 * εg ^ 2) :=
    div_le_div_of_nonneg_right hVA hs.le
  have h_split : (A + 2 * Lsq) / (η3 * εg ^ 2)
      = A / (η3 * εg ^ 2) + 2 * Lsq / (η3 * εg ^ 2) := by rw [add_div]
  have h_2C : 2 * Lsq / (η3 * εg ^ 2) ≤ 2 * C * Lsq := by
    rw [hC]
    have h_eq : 2 * (2 / (η3 * εg ^ 2)) * Lsq = 4 * Lsq / (η3 * εg ^ 2) := by
      field_simp; ring
    rw [h_eq]
    have h24 : 2 * Lsq ≤ 4 * Lsq := by linarith
    exact div_le_div_of_nonneg_right h24 hs.le
  linarith

lemma channelCodingSmoothMinN_real_le_two_coef_logSq_add
    {V_X V_Y V_Z A_Y A_Z Lsq C D η3 εg I_lb R' ε' : ℝ}
    (hη3 : η3 = ε' / 2 / 3) (hεg : εg = (I_lb - R') / 6) (hs : 0 < η3 * εg ^ 2)
    (hVX : 0 ≤ V_X) (hVY : V_Y ≤ A_Y + 2 * Lsq) (hVZ : V_Z ≤ A_Z + 2 * Lsq)
    (hLsq : 0 ≤ Lsq)
    (hVY_nn : 0 ≤ V_Y) (hVZ_nn : 0 ≤ V_Z)
    (hC : C = 2 / (η3 * εg ^ 2))
    (hDX : V_X / (η3 * εg ^ 2) + 2 ≤ D) (hDY : A_Y / (η3 * εg ^ 2) + 2 ≤ D)
    (hDZ : A_Z / (η3 * εg ^ 2) + 2 ≤ D)
    (hDexp : (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) ≤ D)
    (hD1 : (1 : ℝ) ≤ D) (hCLsq : 0 ≤ 2 * C * Lsq) :
    (channelCodingSmoothMinN V_X V_Y V_Z I_lb R' ε' : ℝ) ≤ 2 * C * Lsq + D := by
  have hAt : (typicalSetMinN V_X η3 εg : ℝ) ≤ 2 * C * Lsq + D :=
    typicalSetMinN_real_le_two_coef_logSq_add hs hVX
      (by linarith) hLsq hC hDX
  have hAY' : (typicalSetMinN V_Y η3 εg : ℝ) ≤ 2 * C * Lsq + D :=
    typicalSetMinN_real_le_two_coef_logSq_add hs hVY_nn hVY hLsq hC hDY
  have hAZ' : (typicalSetMinN V_Z η3 εg : ℝ) ≤ 2 * C * Lsq + D :=
    typicalSetMinN_real_le_two_coef_logSq_add hs hVZ_nn hVZ hLsq hC hDZ
  have hAExp : (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) ≤ 2 * C * Lsq + D := by
    linarith
  have hA1 : (1 : ℝ) ≤ 2 * C * Lsq + D := by linarith
  unfold channelCodingSmoothMinN jointlyTypicalSetMinN
  subst hη3 hεg
  push_cast
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) hAExp) hA1
  · exact hAt
  · exact hAY'
  · exact hAZ'

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
lemma exists_subcode_maxError_lt_two_mul
    {n M' : ℕ} (c : Code M' n α β) (W' : Channel α β) [IsMarkovKernel W']
    {R R' ε' : ℝ} (hR_pos : 0 < R)
    (hM'_lb : Nat.ceil (Real.exp ((n : ℝ) * R')) ≤ M')
    (hrate : 2 * Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ Nat.ceil (Real.exp ((n : ℝ) * R')))
    (h_avg_lt : (c.averageErrorProb W').toReal < ε') :
    ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (cs : Code M n α β),
      ∀ m, (cs.errorProbAt W' m).toReal < 2 * ε' := by
  classical
  have hK : (1 : ℝ) < 2 := by norm_num
  have h_filter_bound := errorProbAt_filter_card_bound (M := M') (n := n) c W' hK
  set T : Finset (Fin M') := (Finset.univ : Finset (Fin M')).filter
      (fun m => 2 * (c.averageErrorProb W').toReal <
        (c.errorProbAt W' m).toReal) with hT_def
  set S : Finset (Fin M') := (Finset.univ : Finset (Fin M')).filter
      (fun m => (c.errorProbAt W' m).toReal ≤
        2 * (c.averageErrorProb W').toReal) with hS_def
  have hST_partition : S.card + T.card = M' := by
    have h_union : S ∪ T = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro m
      rw [Finset.mem_union, hS_def, hT_def, Finset.mem_filter, Finset.mem_filter]
      rcases le_or_gt ((c.errorProbAt W' m).toReal)
          (2 * (c.averageErrorProb W').toReal) with h | h
      · exact Or.inl ⟨Finset.mem_univ m, h⟩
      · exact Or.inr ⟨Finset.mem_univ m, h⟩
    have h_disj : Disjoint S T := by
      rw [hS_def, hT_def]
      refine Finset.disjoint_filter.mpr ?_
      intro m _ hm
      exact not_lt_of_ge hm
    have := Finset.card_union_of_disjoint h_disj
    rw [h_union, Finset.card_univ, Fintype.card_fin] at this
    linarith
  have h_T_card_le : 2 * T.card ≤ M' := by
    have h_real : ((T.card : ℝ) * 2 : ℝ) ≤ (M' : ℝ) := h_filter_bound
    have h_real' : ((2 * T.card : ℕ) : ℝ) ≤ ((M' : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h_real'
  have h_2S_ge_M : M' ≤ 2 * S.card := by
    have : M' = S.card + T.card := hST_partition.symm
    omega
  have h_rate_inequality : 2 * Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ 2 * S.card :=
    hrate.trans (hM'_lb.trans h_2S_ge_M)
  have h_ceil_le_S_card : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ S.card := by
    have h2 : (2 : ℕ) > 0 := by norm_num
    exact Nat.le_of_mul_le_mul_left h_rate_inequality h2
  have h_exp_nR_pos : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR_pos.le
  have h_ceil_ge_1 : 1 ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
    exact lt_of_lt_of_le zero_lt_one (Real.one_le_exp h_exp_nR_pos)
  have hS_pos : 0 < S.card := lt_of_lt_of_le h_ceil_ge_1 h_ceil_le_S_card
  refine ⟨S.card, h_ceil_le_S_card, c.subcode S hS_pos, ?_⟩
  intro m'
  have h_sub_le := c.subcode_errorProbAt_le W' S hS_pos m'
  set m₀ : Fin M' := (S.equivFin.symm ⟨m'.val, by simp [Fin.is_lt]⟩).val with hm₀_def
  have hm₀_mem : m₀ ∈ S := (S.equivFin.symm ⟨m'.val, by simp [Fin.is_lt]⟩).property
  have h_m₀_le : (c.errorProbAt W' m₀).toReal ≤
      2 * (c.averageErrorProb W').toReal := by
    rw [hS_def, Finset.mem_filter] at hm₀_mem
    exact hm₀_mem.2
  have h_sub_le_top : c.errorProbAt W' m₀ ≠ ∞ := by
    haveI : IsProbabilityMeasure
        (Measure.pi (fun i => W' (c.encoder m₀ i))) := by infer_instance
    exact ((prob_le_one
      (μ := Measure.pi (fun i => W' (c.encoder m₀ i)))
      (s := c.errorEvent m₀)).trans_lt ENNReal.one_lt_top).ne
  have h_sub_le_toReal :
      ((c.subcode S hS_pos).errorProbAt W' m').toReal
        ≤ (c.errorProbAt W' m₀).toReal :=
    (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top h_sub_le_top h_sub_le) h_sub_le_top).mpr h_sub_le
  calc ((c.subcode S hS_pos).errorProbAt W' m').toReal
      ≤ (c.errorProbAt W' m₀).toReal := h_sub_le_toReal
    _ ≤ 2 * (c.averageErrorProb W').toReal := h_m₀_le
    _ < 2 * ε' := by linarith

omit [DecidableEq α] [DecidableEq β] in
set_option maxHeartbeats 1200000 in
/-- For any `R < capacity W` and `ε > 0`, there exists `N₀` such that for all
`n ≥ N₀` one can pick `δ_n` with `2 n δ_n < ε/2` and a code at the smooth channel
`Channel.smooth W δ_n` achieving max-error less than `ε/2`. -/
theorem exists_N_for_smooth_achievability_uniform
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1),
        2 * (n : ℝ) * δ < ε / 2 ∧
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
          (c : Code M n α β),
          ∀ m, (c.errorProbAt (Channel.smooth W δ) m).toReal < ε / 2 := by
  classical
  -- Step 1: extract uniform smooth capacity.
  obtain ⟨p₀, hp₀_mem, δ_p, δ_B, hδ_p_pos, hδ_p_le, hδ_B_pos, hδ_B_le,
          I_lb, hR_lt_I_lb, hp_full_pos, hp_full_mem, h_MI_uniform⟩ :=
    pSmooth_smooth_capacity_gt_uniform W hR
  -- Step 2: interior rate `R'` and avg target `ε' := ε/8` (so max-error ≤ 2·ε' = ε/4 < ε/2).
  set R' : ℝ := (R + I_lb) / 2 with hR'_def
  have hR_lt_R' : R < R' := by rw [hR'_def]; linarith
  have hR'_lt_I_lb : R' < I_lb := by rw [hR'_def]; linarith
  have hR'_pos : 0 < R' := lt_trans hR_pos hR_lt_R'
  set ε' : ℝ := ε / 8 with hε'_def
  have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
  -- Step 3: `α`/`β` cardinalities and p_min.
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  set p_min : ℝ := δ_p / (Fintype.card α : ℝ) with hp_min_def
  have hp_min_pos : 0 < p_min := by rw [hp_min_def]; positivity
  -- Lower bound: every `pSmooth p₀ δ_p a ≥ p_min`.
  have hp_min_le : ∀ a : α, p_min ≤ pSmooth p₀ δ_p a :=
    fun a => pSmooth_ge hp₀_mem hδ_p_pos hδ_p_le a
  -- Also for the measure version:
  haveI : IsProbabilityMeasure (pmfToMeasure (pSmooth p₀ δ_p)) :=
    pmfToMeasure_isProbabilityMeasure hp_full_mem
  have hp_min_le_meas : ∀ a : α,
      p_min ≤ (pmfToMeasure (pSmooth p₀ δ_p)).real {a} := by
    intro a
    rw [pmfToMeasure_real_singleton hp_full_mem]
    exact hp_min_le a
  -- Step 4: closed-form constant `V_X` (δ-independent).
  -- We use the absolute-value bound `pmfLogBound (iidAmbientMeasure (pmfToMeasure p_full) W) iidXs`,
  -- and `pmfLog_iidXs_const_in_smooth` to lift to the smooth channel.
  set V_X_B : ℝ :=
    pmfLogBound (iidAmbientMeasure (pmfToMeasure (pSmooth p₀ δ_p)) W) iidXs with hV_X_B_def
  set V_X : ℝ := V_X_B ^ 2 with hV_X_def
  -- Step 5: pre-compute log/exp constants for V_Y, V_Z bounds.
  -- K_Y := log(|β|) + log(1/δ_B + 16/ε); we'll show log(|β|/δ_n) ≤ K_Y + log(n+1).
  set K_Y : ℝ := Real.log ((Fintype.card β : ℝ)) +
    Real.log (1 / δ_B + 16 / ε) with hK_Y_def
  -- K_Z := log(|α|·|β|/p_min) + log(1/δ_B + 16/ε); log(|α||β|/(p_min δ_n)) ≤ K_Z + log(n+1).
  set K_Z : ℝ := Real.log ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) / p_min) +
    Real.log (1 / δ_B + 16 / ε) with hK_Z_def
  -- Step 6: identify the constant `D` and coefficient `C` for outer-N.
  -- V_Y(δ_n) ≤ 2·K_Y² + 2·(log(n+1))², V_Z(δ_n) ≤ 2·K_Z² + 2·(log(n+1))².
  -- jointlyTypicalSetMinN V_X V_Y V_Z (ε'/2) ((I_lb - R')/6)
  --   = max(max(typicalSetMinN V_X (ε'/6) ε_gap, typicalSetMinN V_Y(δ_n) (ε'/6) ε_gap),
  --       typicalSetMinN V_Z(δ_n) (ε'/6) ε_gap)
  -- where ε_gap := (I_lb - R')/6.
  -- typicalSetMinN V η ε_gap = max(1, ⌈V/(η·ε_gap²)⌉ + 1) ≤ V/(η·ε_gap²) + 2 + 1.
  set ε_gap : ℝ := (I_lb - R') / 6 with hε_gap_def
  have hI_lb_gt_R' : 0 < I_lb - R' := by linarith
  have hε_gap_pos : 0 < ε_gap := by rw [hε_gap_def]; positivity
  set η : ℝ := ε' / 2 with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; linarith
  have hη3_pos : 0 < η / 3 := by linarith
  -- Coefficient C absorbs `2 / ((η/3) · ε_gap²)`.
  set C_coef : ℝ := 2 / ((η / 3) * ε_gap ^ 2) with hC_coef_def
  have hC_coef_pos : 0 < C_coef := by
    rw [hC_coef_def]; positivity
  -- D_const = sum of: V_X / ((η/3) · ε_gap²) + 2 (the +1 typicalSetMinN constants for X),
  -- + (2·K_Y² + 2·K_Z²) / ((η/3) · ε_gap²) + 4 (for Y, Z),
  -- + expNegMulMinN ((I_lb-R')/2) (ε'/2)  -- constant
  -- + 1 (for the outer max-with-1 of channelCodingSmoothMinN).
  -- We need a numerical upper bound.
  set V_const : ℝ := V_X + 2 * K_Y ^ 2 + 2 * K_Z ^ 2 with hV_const_def
  set D_const : ℝ := V_const / ((η / 3) * ε_gap ^ 2) + 6
    + (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℕ) + 1 with hD_const_def
  -- Step 7: rate inequality for max-error upgrade: 2 ⌈exp(nR)⌉ ≤ ⌈exp(nR')⌉ eventually.
  obtain ⟨N_rate, hN_rate⟩ := exists_N_two_ceil_exp_le hR_pos hR_lt_R'
  -- Step 8: outer N₀ from log-sq absorption.
  obtain ⟨N_log, hN_log⟩ := exists_N_log_sq_plus_const_le_n (2 * C_coef) D_const
    (by linarith [hC_coef_pos])
  set N₀ : ℕ := max N_log N_rate with hN₀_def
  refine ⟨N₀, fun n hn => ?_⟩
  -- Bind δ_n, n inequalities, etc.
  have hn_log : N_log ≤ n := (le_max_left _ _).trans hn
  have hn_rate : N_rate ≤ n := (le_max_right _ _).trans hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  -- Choose δ_n.
  set δ_n : ℝ := min δ_B (ε / (16 * ((n : ℝ) + 1))) with hδ_n_def
  have hε_n_pos : (0 : ℝ) < ε / (16 * ((n : ℝ) + 1)) := by positivity
  have hδ_n_pos : 0 < δ_n := lt_min hδ_B_pos hε_n_pos
  have hδ_n_le_δ_B : δ_n ≤ δ_B := min_le_left _ _
  have hδ_n_le : δ_n ≤ 1 := hδ_n_le_δ_B.trans hδ_B_le
  have hδ_n_le_target : δ_n ≤ ε / (16 * ((n : ℝ) + 1)) := min_le_right _ _
  -- TV target: 2 n δ_n < ε/2.
  have h_2nδ_lt : 2 * (n : ℝ) * δ_n < ε / 2 :=
    two_mul_lt_half_of_le_div hε n hn1_pos hδ_n_le_target
  -- δ_n is in the smooth-capacity range (0, δ_B], so I_lb < MI(p_full; W_smooth δ_n).
  have hδ_n_mem : δ_n ∈ Set.Ioc (0 : ℝ) δ_B := ⟨hδ_n_pos, hδ_n_le_δ_B⟩
  have hMI_δ_n : I_lb <
      (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p))
        (Channel.smooth W δ_n)).toReal :=
    h_MI_uniform δ_n hδ_n_mem
  have hR'_lt_MI : R' < (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p))
        (Channel.smooth W δ_n)).toReal :=
    hR'_lt_I_lb.trans hMI_δ_n
  -- Variance upper bounds:
  -- V_X bound is via `pmfLog_iidXs_const_in_smooth` + `pmfLogVariance_le_sq_of_bounded`.
  -- We work in `μ := iidAmbientMeasure (pmfToMeasure p_full) (Channel.smooth W δ_n)`.
  haveI hWsmooth_mk : IsMarkovKernel (Channel.smooth W δ_n) :=
    Channel.smooth_isMarkovKernel W hδ_n_pos.le hδ_n_le
  set p_meas : Measure α := pmfToMeasure (pSmooth p₀ δ_p) with hp_meas_def
  set μ : Measure (ℕ → α × β) :=
    iidAmbientMeasure p_meas (Channel.smooth W δ_n) with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hXs : ∀ i, Measurable (iidXs (α := α) (β := β) i) := measurable_iidXs
  have hYs : ∀ i, Measurable (iidYs (α := α) (β := β) i) := measurable_iidYs
  -- V_X bound:
  have hV_X_pointwise : ∀ a : α, |pmfLog μ iidXs a| ≤ V_X_B := by
    intro a
    rw [hμ_def, pmfLog_iidXs_const_in_smooth p_meas W hδ_n_pos hδ_n_le a]
    exact abs_pmfLog_le_bound (iidAmbientMeasure p_meas W) iidXs a
  have hV_X_bound : pmfLogVariance μ iidXs ≤ V_X :=
    pmfLogVariance_le_sq_of_bounded μ iidXs hXs hV_X_pointwise
  -- V_Y pointwise bound: |pmfLog μ iidYs b| ≤ log(|β|/δ_n).
  have hV_Y_pointwise : ∀ b : β,
      |pmfLog μ iidYs b| ≤ Real.log ((Fintype.card β : ℝ) / δ_n) := by
    intro b
    rw [hμ_def]
    exact pmfLog_iidYs_bound_smooth p_meas W hδ_n_pos hδ_n_le b
  -- V_Z pointwise bound: |pmfLog μ joint| ≤ log(|α||β|/(p_min·δ_n)).
  have hV_Z_pointwise : ∀ ab : α × β,
      |pmfLog μ (jointSequence iidXs iidYs) ab| ≤
        Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n)) := by
    intro ab
    rw [hμ_def]
    exact pmfLog_jointSequence_bound_smooth p_meas hp_min_pos hp_min_le_meas
      W hδ_n_pos hδ_n_le ab
  -- Now bound log(|β|/δ_n) ≤ K_Y + log(n+1), and (log(|β|/δ_n))² ≤ 2 K_Y² + 2 (log(n+1))².
  have h_one_div_δ_n_le : 1 / δ_n ≤ (1 / δ_B + 16 / ε) * ((n : ℝ) + 1) :=
    one_div_smooth_n_le hδ_B_pos hε n
  have h_sum_pos : (0 : ℝ) < 1 / δ_B + 16 / ε := by positivity
  -- (log)² ≤ 2 K² + 2 (log(n+1))²: combine the log-div bound with `(a+b)² ≤ 2a² + 2b²`.
  set V_Y_n : ℝ := (Real.log ((Fintype.card β : ℝ) / δ_n)) ^ 2 with hV_Y_n_def
  set V_Z_n : ℝ := (Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ))
                              / (p_min * δ_n))) ^ 2 with hV_Z_n_def
  have hβ1 : (1 : ℝ) ≤ (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hα1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have h_V_Y_n_bound : V_Y_n ≤ 2 * K_Y ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2 := by
    rw [hV_Y_n_def, hK_Y_def]
    exact logSq_div_le_two_sq_add_two_logSq hβ1 h_sum_pos hδ_n_pos hδ_n_le hn1_pos
      h_one_div_δ_n_le
  have h_V_Z_n_bound : V_Z_n ≤ 2 * K_Z ^ 2 + 2 * (Real.log ((n : ℝ) + 1)) ^ 2 := by
    have hp_min_le_one : p_min ≤ 1 := by
      rw [hp_min_def, div_le_one hα_pos]; linarith
    have hαβ_pmin_ge : (1 : ℝ) ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) / p_min := by
      rw [le_div_iff₀ hp_min_pos]; nlinarith
    rw [hV_Z_n_def, hK_Z_def,
      show ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ_n)
        = ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) / p_min) / δ_n from
        div_mul_eq_div_div _ _ _]
    exact logSq_div_le_two_sq_add_two_logSq hαβ_pmin_ge h_sum_pos hδ_n_pos hδ_n_le
      hn1_pos h_one_div_δ_n_le
  -- Variance bounds.
  have hV_Y_bound : pmfLogVariance μ iidYs ≤ V_Y_n :=
    pmfLogVariance_le_sq_of_bounded μ iidYs hYs hV_Y_pointwise
  have hZ_meas : ∀ i, Measurable (jointSequence (α := α) (β := β) iidXs iidYs i) :=
    fun i => measurable_jointSequence iidXs iidYs hXs hYs i
  have hV_Z_bound : pmfLogVariance μ (jointSequence iidXs iidYs) ≤ V_Z_n :=
    pmfLogVariance_le_sq_of_bounded μ (jointSequence iidXs iidYs) hZ_meas hV_Z_pointwise
  -- Step 9: Apply `channel_coding_achievability_smooth_at_N_le` at `R'` with V_X, V_Y_n, V_Z_n.
  --   We need `channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' ≤ n`.
  -- Decompose this max.
  -- a) typicalSetMinN V_X (η/3) ε_gap ≤ V_X / ((η/3)·ε_gap²) + 2.
  -- b) typicalSetMinN V_Y_n (η/3) ε_gap ≤ (2 K_Y² + 2 (log(n+1))²) / ((η/3)·ε_gap²) + 2.
  -- c) typicalSetMinN V_Z_n (η/3) ε_gap ≤ (2 K_Z² + 2 (log(n+1))²) / ((η/3)·ε_gap²) + 2.
  -- d) expNegMulMinN((I_lb - R')/2)(ε'/2) ≤ const.
  -- e) +1 (the outer max-with-1).
  -- Sum: D_const + 2·C_coef·(log(n+1))². Compare against `n`.
  have hηε_sq : 0 < (η / 3) * ε_gap ^ 2 := by positivity
  have hV_X_nn : 0 ≤ V_X := by rw [hV_X_def]; exact sq_nonneg _
  have hV_Y_n_nn : 0 ≤ V_Y_n := by rw [hV_Y_n_def]; exact sq_nonneg _
  have hV_Z_n_nn : 0 ≤ V_Z_n := by rw [hV_Z_n_def]; exact sq_nonneg _
  -- Each `typicalSetMinN`/`expNegMulMinN` axis is bounded by `2·C_coef·(log(n+1))² + D_const`.
  -- The three `D_const`-side inequalities (`hDX`/`hDY`/`hDZ`) split `V_const/s` into nonneg parts.
  have h_total_split : V_const / ((η / 3) * ε_gap ^ 2)
      = V_X / ((η / 3) * ε_gap ^ 2) + 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2)
        + 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by
    rw [hV_const_def, add_div, add_div]
  have h_VX_nn : 0 ≤ V_X / ((η / 3) * ε_gap ^ 2) := by positivity
  have h_KY_nn : 0 ≤ 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2) := by positivity
  have h_KZ_nn : 0 ≤ 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) := by positivity
  have h_expNeg_nn : 0 ≤ (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) := Nat.cast_nonneg _
  have hDX : V_X / ((η / 3) * ε_gap ^ 2) + 2 ≤ D_const := by
    rw [hD_const_def, h_total_split]; linarith
  have hDY : 2 * K_Y ^ 2 / ((η / 3) * ε_gap ^ 2) + 2 ≤ D_const := by
    rw [hD_const_def, h_total_split]; linarith
  have hDZ : 2 * K_Z ^ 2 / ((η / 3) * ε_gap ^ 2) + 2 ≤ D_const := by
    rw [hD_const_def, h_total_split]; linarith
  have hDexp : (expNegMulMinN ((I_lb - R') / 2) (ε' / 2) : ℝ) ≤ D_const := by
    rw [hD_const_def, h_total_split]; linarith
  have hD1 : (1 : ℝ) ≤ D_const := by
    rw [hD_const_def, h_total_split]; linarith
  have hCLsq : 0 ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 := by positivity
  have h_smoothN_le :
      (channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' : ℝ)
        ≤ 2 * C_coef * (Real.log ((n : ℝ) + 1)) ^ 2 + D_const :=
    channelCodingSmoothMinN_real_le_two_coef_logSq_add
      (by rw [hη_def]) hε_gap_def hηε_sq hV_X_nn h_V_Y_n_bound h_V_Z_n_bound
      (sq_nonneg _) hV_Y_n_nn hV_Z_n_nn hC_coef_def hDX hDY hDZ hDexp hD1 hCLsq
  -- From outer N₀: 2·C_coef · (log(n+1))² + D_const ≤ n.
  have h_log_le_n := hN_log n hn_log
  have h_smoothN_le_n :
      (channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' : ℝ) ≤ (n : ℝ) :=
    h_smoothN_le.trans h_log_le_n
  have h_smoothN_le_n_nat :
      channelCodingSmoothMinN V_X V_Y_n V_Z_n I_lb R' ε' ≤ n := by
    exact_mod_cast h_smoothN_le_n
  -- Step 10: apply the closed-form average-error theorem.
  obtain ⟨M', hM'_lb, c', h_avg_lt⟩ :=
    channel_coding_achievability_smooth_at_N_le W p₀ hp₀_mem hδ_p_pos hδ_p_le
      hδ_n_pos hδ_n_le hR'_pos hR'_lt_I_lb hMI_δ_n.le V_X V_Y_n V_Z_n
      hV_X_bound hV_Y_bound hV_Z_bound hε'_pos n h_smoothN_le_n_nat
  -- Step 11: max-error upgrade via subcode trick (mirror `channel_coding_achievability_max_error`).
  -- Let M' ≥ ⌈exp(nR')⌉ and avg < ε' = ε/8. The subcode trick gives a code of size
  -- ≥ ⌈exp(nR)⌉ with max-error < 2·ε' = ε/4 < ε/2.
  obtain ⟨M, hM_lb, cs, h_max_lt⟩ :=
    exists_subcode_maxError_lt_two_mul c' (Channel.smooth W δ_n) hR_pos hM'_lb
      (hN_rate n hn_rate) h_avg_lt
  refine ⟨δ_n, hδ_n_pos, hδ_n_le, h_2nδ_lt, M, hM_lb, cs, ?_⟩
  intro m'
  have h2ε'_lt : 2 * ε' < ε / 2 := by rw [hε'_def]; linarith
  exact (h_max_lt m').trans h2ε'_lt

end InformationTheory.Shannon.ChannelCoding
