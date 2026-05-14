import Common2026.Shannon.AEP
import Mathlib.Probability.Moments.Variance

/-!
# AEP — rate-uniform 形 (Chebyshev 経由)

[D-1'' ムーンショット plan](../../../docs/shannon/channel-coding-shannon-theorem-general-plan.md)
の Step 1: 既存 `typicalSet_prob_tendsto_one` (`AEP.lean:375`) は `Tendsto … (𝓝 1)` 形のみで
closed-form bound を持たない。本ファイルは Chebyshev 不等式
(`ProbabilityTheory.meas_ge_le_variance_div_sq`) と pairwise variance sum
(`ProbabilityTheory.IndepFun.variance_sum`) を経由して **explicit な `N(ε, η)`** で

  `n ≥ N → μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} ≥ 1 - η`

を確立する。D-1'' Step 2-5 の主定理組み立てで `δ ⊆ (0, δ_B]` 上の N(δ) bound に再利用する。

`pmfLog μ Xs : α → ℝ` は alphabet 上の有限関数のため、`logLikelihood μ Xs i` は
`pmfLog` の値域 (有限集合) で a.s. bounded → `MemLp _ 2 μ`。よって全部品が揃う。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- 共通の bound: `pmfLog μ Xs` の絶対値の sup. -/
noncomputable def pmfLogBound (μ : Measure Ω) (Xs : ℕ → Ω → α) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : α => |pmfLog μ Xs a|)

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma pmfLogBound_nonneg (μ : Measure Ω) (Xs : ℕ → Ω → α) :
    0 ≤ pmfLogBound μ Xs := by
  unfold pmfLogBound
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  refine le_trans (abs_nonneg (pmfLog μ Xs a₀)) ?_
  exact Finset.le_sup' (f := fun a : α => |pmfLog μ Xs a|) (Finset.mem_univ a₀)

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma abs_pmfLog_le_bound (μ : Measure Ω) (Xs : ℕ → Ω → α) (a : α) :
    |pmfLog μ Xs a| ≤ pmfLogBound μ Xs := by
  unfold pmfLogBound
  exact Finset.le_sup' (f := fun a : α => |pmfLog μ Xs a|) (Finset.mem_univ a)

omit [DecidableEq α] [MeasurableSingletonClass α] in
/-- `logLikelihood μ Xs i ω` is bounded by `pmfLogBound μ Xs` for every `ω`. -/
lemma abs_logLikelihood_le_bound
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (i : ℕ) (ω : Ω) :
    |logLikelihood μ Xs i ω| ≤ pmfLogBound μ Xs := by
  unfold logLikelihood
  exact abs_pmfLog_le_bound μ Xs (Xs i ω)

/-- `logLikelihood μ Xs i` is in `L²(μ)`. -/
lemma memLp_logLikelihood
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : ℕ) :
    MemLp (logLikelihood μ Xs i) 2 μ := by
  refine MemLp.of_bound (measurable_logLikelihood μ Xs hXs i).aestronglyMeasurable
    (pmfLogBound μ Xs) ?_
  exact Filter.Eventually.of_forall (fun ω => by
    have := abs_logLikelihood_le_bound μ Xs i ω
    simpa [Real.norm_eq_abs] using this)

/-- The single-symbol variance `Var[logLikelihood μ Xs 0; μ]`. The 0-th index suffices because
all `Xs i` are identically distributed. -/
noncomputable def pmfLogVariance (μ : Measure Ω) (Xs : ℕ → Ω → α) : ℝ :=
  variance (logLikelihood μ Xs 0) μ

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma pmfLogVariance_nonneg (μ : Measure Ω) (Xs : ℕ → Ω → α) :
    0 ≤ pmfLogVariance μ Xs := by
  unfold pmfLogVariance variance
  exact ENNReal.toReal_nonneg

/-- Variance is invariant under `IdentDistrib`. -/
lemma variance_logLikelihood_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (i : ℕ) :
    variance (logLikelihood μ Xs i) μ = pmfLogVariance μ Xs := by
  unfold pmfLogVariance
  exact (identDistrib_logLikelihood μ Xs hident i).variance_eq

/-- Chebyshev applied to `∑ i ∈ range n, logLikelihood μ Xs i` and divided by `n`:
for `n ≥ 1` and `ε > 0`,

  `μ {ω | ε ≤ |(∑ i ∈ range n, logLikelihood μ Xs i ω) / n - H|}`
    `≤ ENNReal.ofReal (pmfLogVariance μ Xs / (n * ε^2))`.

This is the **explicit-rate** version of `aep_inProbability`. -/
lemma aep_chebyshev_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    μ {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                  - entropy μ (Xs 0)|}
      ≤ ENNReal.ofReal (pmfLogVariance μ Xs / (n * ε ^ 2)) := by
  classical
  -- Denote the n-step sum (no `set` to avoid `eta` beta-reduction issues).
  -- MemLp for each summand.
  have h_memLp_each : ∀ i, MemLp (logLikelihood μ Xs i) 2 μ :=
    fun i => memLp_logLikelihood μ Xs hXs i
  -- MemLp for the sum.
  have h_memLp_S :
      MemLp (fun ω => ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) 2 μ := by
    refine memLp_finsetSum (Finset.range n) ?_
    intro i _
    exact h_memLp_each i
  -- Expectation of each summand = H.
  have h_int_each : ∀ i, ∫ ω, logLikelihood μ Xs i ω ∂μ = entropy μ (Xs 0) := by
    intro i
    rw [(identDistrib_logLikelihood μ Xs hident i).integral_eq]
    exact integral_logLikelihood_zero μ Xs hXs
  -- Expectation of the sum = n · H.
  have h_int_S :
      ∫ ω, (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) ∂μ
        = (n : ℝ) * entropy μ (Xs 0) := by
    rw [integral_finsetSum _ (fun i _ => (h_memLp_each i).integrable (by norm_num))]
    rw [Finset.sum_congr rfl (fun i _ => h_int_each i)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Variance of the sum: pairwise indep + ident ⇒ Var[∑] = n · V.
  have h_var_S :
      variance (∑ i ∈ Finset.range n, logLikelihood μ Xs i) μ
        = n * pmfLogVariance μ Xs := by
    have h_pairwise :
        Set.Pairwise (Finset.range n : Set ℕ)
          (fun i j => logLikelihood μ Xs i ⟂ᵢ[μ] logLikelihood μ Xs j) := by
      intro i _ j _ hij
      exact indepFun_logLikelihood μ Xs hindep hij
    rw [IndepFun.variance_sum (fun i _ => h_memLp_each i) h_pairwise]
    rw [Finset.sum_congr rfl
      (fun i _ => variance_logLikelihood_eq μ Xs hident i)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h_var_S_fun :
      variance (fun ω => ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) μ
        = n * pmfLogVariance μ Xs := by
    have h_ext :
        (fun ω => ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω)
        = (∑ i ∈ Finset.range n, logLikelihood μ Xs i) := by
      ext ω; rw [Finset.sum_apply]
    rw [h_ext]
    exact h_var_S
  -- Real factor n > 0.
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- Rewrite the event: ε ≤ |S n ω / n - H| ⟺ n * ε ≤ |S n ω - n * H|.
  have h_event_eq :
      {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                  - entropy μ (Xs 0)|}
      = {ω | (n : ℝ) * ε ≤
              |(∑ i ∈ Finset.range n, logLikelihood μ Xs i ω)
                - (∫ ω', (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω') ∂μ)|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [h_int_S]
    have h_factor :
        (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n - entropy μ (Xs 0)
        = ((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω)
            - (n : ℝ) * entropy μ (Xs 0)) / n := by
      field_simp
    rw [h_factor, abs_div, abs_of_pos hn_real_pos]
    rw [le_div_iff₀ hn_real_pos, mul_comm ε (n : ℝ)]
  rw [h_event_eq]
  -- Apply Chebyshev with c := n * ε > 0.
  have hc_pos : 0 < (n : ℝ) * ε := mul_pos hn_real_pos hε
  have h_cheb := meas_ge_le_variance_div_sq h_memLp_S hc_pos
  refine h_cheb.trans ?_
  rw [h_var_S_fun]
  apply ENNReal.ofReal_le_ofReal
  have hV_nn : 0 ≤ pmfLogVariance μ Xs := pmfLogVariance_nonneg μ Xs
  have hne1 : 0 < (n : ℝ) * ε ^ 2 := mul_pos hn_real_pos (pow_pos hε 2)
  have hne2 : 0 < ((n : ℝ) * ε) ^ 2 := pow_pos hc_pos 2
  -- Goal: (n * V) / (n * ε)^2 ≤ V / (n * ε^2).
  -- (n * ε)^2 = n^2 * ε^2, so (n V) / (n² ε²) = V / (n ε²).  These are equal.
  have h_eq : ((n : ℝ) * pmfLogVariance μ Xs) / ((n : ℝ) * ε) ^ 2
      = pmfLogVariance μ Xs / ((n : ℝ) * ε ^ 2) := by
    rw [mul_pow]
    field_simp
  rw [h_eq]

/-- The typical-set event has the same complement as the Chebyshev "bad" set, re-indexed
from `range n` to `Fin n`. -/
private lemma typicalSet_compl_eq
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) {ε : ℝ} :
    {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}
      = {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                    - entropy μ (Xs 0)|}ᶜ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, mem_typicalSet_iff,
    not_le, jointRV_apply]
  have h_sum : (∑ i : Fin n, pmfLog μ Xs (Xs i ω))
      = ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω :=
    Fin.sum_univ_eq_sum_range (fun i => pmfLog μ Xs (Xs i ω)) n
  rw [h_sum]

/-- **Step 1 main result**: explicit-rate AEP. For any `ε, η > 0`, there is `N(ε, η)` such that
for all `n ≥ N`, the typical-set has μ-measure ≥ `1 - η`.

The explicit bound is `N := ⌈pmfLogVariance / (η · ε²)⌉ + 1`, so `n ≥ N ⇒
pmfLogVariance / (n · ε²) ≤ η`. -/
theorem typicalSet_prob_ge_of_rate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      1 - η ≤ (μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}).toReal := by
  classical
  -- Define N := max(1, ⌈V / (η · ε²)⌉ + 1).
  set V : ℝ := pmfLogVariance μ Xs with hV_def
  have hV_nn : 0 ≤ V := pmfLogVariance_nonneg μ Xs
  set Nreal : ℝ := V / (η * ε ^ 2) with hNreal_def
  set N : ℕ := max 1 (Nat.ceil Nreal + 1) with hN_def
  refine ⟨N, ?_⟩
  intro n hn_ge
  have hn_pos : 0 < n := by
    have h1 : 1 ≤ N := le_max_left _ _
    exact lt_of_lt_of_le Nat.zero_lt_one (h1.trans hn_ge)
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- Key inequality: V / (n · ε²) ≤ η.
  have h_rate : V / ((n : ℝ) * ε ^ 2) ≤ η := by
    have hnε : 0 < (n : ℝ) * ε ^ 2 := mul_pos hn_real_pos (pow_pos hε 2)
    have hηε : 0 < η * ε ^ 2 := mul_pos hη (pow_pos hε 2)
    rw [div_le_iff₀ hnε]
    -- V ≤ η · (n · ε²) = (η · ε²) · n. Use Nreal = V / (η · ε²) ≤ N - 1 ≤ n.
    have h_ceil : Nreal ≤ (Nat.ceil Nreal : ℝ) := Nat.le_ceil _
    have h_N_le : (Nat.ceil Nreal + 1 : ℝ) ≤ (N : ℝ) := by
      have : (Nat.ceil Nreal + 1 : ℕ) ≤ N := le_max_right _ _
      exact_mod_cast this
    have h_N_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
    have h_Nreal_le_n : Nreal ≤ (n : ℝ) := by
      have h_ceil_le : (Nat.ceil Nreal : ℝ) ≤ (Nat.ceil Nreal + 1 : ℝ) := by linarith
      have h1 : Nreal ≤ (Nat.ceil Nreal : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil Nreal : ℝ) ≤ (n : ℝ) := by
        have h_lt : (Nat.ceil Nreal : ℝ) < (Nat.ceil Nreal + 1 : ℝ) := by linarith
        linarith [h_N_le, h_N_le_n]
      linarith
    -- Multiply both sides by (η · ε²) > 0.
    have h_V_le : V ≤ (n : ℝ) * (η * ε ^ 2) := by
      rw [hNreal_def] at h_Nreal_le_n
      have := (div_le_iff₀ hηε).mp h_Nreal_le_n
      linarith
    linarith
  -- Now use h_rate + Chebyshev to bound the bad set.
  have h_bad := aep_chebyshev_bound μ Xs hXs hindep hident hε hn_pos
  set bad : Set Ω := {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                                - entropy μ (Xs 0)|}
  -- μ(bad) ≤ ofReal η.
  have h_bound : μ bad ≤ ENNReal.ofReal η := by
    refine h_bad.trans ?_
    exact ENNReal.ofReal_le_ofReal h_rate
  -- bad is measurable (subset of ℝ via measurable function).
  have h_meas_bad : MeasurableSet bad := by
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_logLikelihood μ Xs hXs i
    have h_div : Measurable
        (fun ω => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n) :=
      h_sum_meas.div_const _
    have h_diff : Measurable
        (fun ω => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n
                    - entropy μ (Xs 0)) :=
      h_div.sub_const _
    have h_abs : Measurable
        (fun ω => |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n
                    - entropy μ (Xs 0))|) :=
      _root_.continuous_abs.measurable.comp h_diff
    exact measurableSet_le measurable_const h_abs
  -- Convert to real-valued bound on the complement.
  have h_event_eq := typicalSet_compl_eq μ Xs n (ε := ε)
  rw [h_event_eq]
  -- (μ bad)ᶜ.toReal = 1 - (μ bad).toReal.
  have h_bad_le_one : μ bad ≤ 1 := by
    rw [← measure_univ (μ := μ)]; exact measure_mono (Set.subset_univ _)
  have h_compl_toReal : (μ badᶜ).toReal = 1 - (μ bad).toReal := by
    rw [measure_compl h_meas_bad (measure_ne_top μ _)]
    rw [measure_univ]
    rw [ENNReal.toReal_sub_of_le h_bad_le_one (by simp)]
    simp
  rw [h_compl_toReal]
  have h_bad_toReal_le : (μ bad).toReal ≤ η := by
    have hη_ne_top : ENNReal.ofReal η ≠ ∞ := ENNReal.ofReal_ne_top
    have := (ENNReal.toReal_le_toReal (measure_ne_top μ _) hη_ne_top).mpr h_bound
    simpa [ENNReal.toReal_ofReal hη.le] using this
  linarith

end InformationTheory.Shannon
