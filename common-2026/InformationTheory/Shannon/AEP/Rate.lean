import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AEP.Basic
import InformationTheory.Shannon.ChannelCoding.Basic
import Mathlib.Probability.Moments.Variance

/-!
# AEP — rate-uniform form (via Chebyshev)

`typicalSet_prob_tendsto_one` gives only the `Tendsto … (𝓝 1)` form and carries no
closed-form bound. This module establishes an explicit `N(ε, η)` with

  `n ≥ N → μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} ≥ 1 - η`

via the Chebyshev inequality (`ProbabilityTheory.meas_ge_le_variance_div_sq`) and
the pairwise variance sum (`ProbabilityTheory.IndepFun.variance_sum`).

Since `pmfLog μ Xs : α → ℝ` is a finite function on the alphabet, each
`logLikelihood μ Xs i` is a.s. bounded by the range of `pmfLog` (a finite set),
hence `MemLp _ 2 μ`, which supplies the integrability ingredients.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The supremum of `|pmfLog μ Xs|` over the alphabet. -/
noncomputable def pmfLogBound (μ : Measure Ω) (Xs : ℕ → Ω → α) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : α => |pmfLog μ Xs a|)

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma abs_pmfLog_le_bound (μ : Measure Ω) (Xs : ℕ → Ω → α) (a : α) :
    |pmfLog μ Xs a| ≤ pmfLogBound μ Xs := by
  unfold pmfLogBound
  exact Finset.le_sup' (f := fun a : α => |pmfLog μ Xs a|) (Finset.mem_univ a)

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma abs_logLikelihood_le_bound
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (i : ℕ) (ω : Ω) :
    |logLikelihood μ Xs i ω| ≤ pmfLogBound μ Xs := by
  unfold logLikelihood
  exact abs_pmfLog_le_bound μ Xs (Xs i ω)

omit [DecidableEq α] in
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

omit [DecidableEq α] [Nonempty α] in
/-- A pointwise bound `|pmfLog Xs a| ≤ B` gives `pmfLogVariance ≤ B²`. -/
lemma pmfLogVariance_le_sq_of_bounded
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {B : ℝ}
    (hB : ∀ a : α, |pmfLog μ Xs a| ≤ B) :
    pmfLogVariance μ Xs ≤ B ^ 2 := by
  unfold pmfLogVariance
  have h_ae_Icc : ∀ᵐ ω ∂μ, logLikelihood μ Xs 0 ω ∈ Set.Icc (-B) B := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have h := hB (Xs 0 ω)
    have h_eq : logLikelihood μ Xs 0 ω = pmfLog μ Xs (Xs 0 ω) := rfl
    rw [h_eq]
    rw [abs_le] at h
    exact ⟨h.1, h.2⟩
  have hAEm : AEMeasurable (logLikelihood μ Xs 0) μ :=
    (measurable_logLikelihood μ Xs hXs 0).aemeasurable
  have h := variance_le_sq_of_bounded (μ := μ) (X := logLikelihood μ Xs 0)
    (a := -B) (b := B) h_ae_Icc hAEm
  -- (b - a) / 2 = (B - (-B)) / 2 = B
  have h_eq : ((B - (-B)) / 2) ^ 2 = B ^ 2 := by ring
  rw [h_eq] at h
  exact h

omit [DecidableEq α] [Nonempty α] in
lemma variance_logLikelihood_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (i : ℕ) :
    variance (logLikelihood μ Xs i) μ = pmfLogVariance μ Xs := by
  unfold pmfLogVariance
  exact (identDistrib_logLikelihood μ Xs hident i).variance_eq

omit [DecidableEq α] in
/-- Explicit-rate version of `aep_inProbability`: for `n ≥ 1` and `ε > 0`,
`μ {ω | ε ≤ |(∑ i ∈ range n, logLikelihood μ Xs i ω) / n - H|}
  ≤ ENNReal.ofReal (pmfLogVariance μ Xs / (n * ε^2))`. -/
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

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
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

omit [DecidableEq α] in
/-- **Explicit-rate AEP**: for any `ε, η > 0`, there is `N(ε, η)` such that for all
`n ≥ N`, the typical set has μ-measure ≥ `1 - η`. The explicit bound is
`N := ⌈pmfLogVariance / (η · ε²)⌉ + 1`, so `n ≥ N ⇒ pmfLogVariance / (n · ε²) ≤ η`. -/
@[entry_point]
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

/-- Closed-form `N(g, ε')` for exponential decay: for any `g, ε' > 0`, there is
`N` such that `exp(- n · g) < ε'` for all `n ≥ N`. Concretely
`N := ⌈max 0 (-log ε' / g)⌉ + 1`. -/
@[entry_point]
theorem exp_neg_mul_lt_of_rate {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (- (n : ℝ) * g) < ε' := by
  set t : ℝ := max 0 (-Real.log ε' / g) with ht_def
  set N : ℕ := Nat.ceil t + 1 with hN_def
  refine ⟨N, ?_⟩
  intro n hn_ge
  -- (n : ℝ) ≥ N ≥ ⌈t⌉ + 1 > t, since ⌈t⌉ < ⌈t⌉ + 1 ≤ n.
  have h_t_nn : 0 ≤ t := le_max_left _ _
  have h_ceil_lt_succ : (Nat.ceil t : ℝ) < (Nat.ceil t + 1 : ℝ) := by linarith
  have h_t_le_ceil : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil _
  have h_N_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have h_N_eq : (N : ℝ) = (Nat.ceil t : ℝ) + 1 := by
    simp [hN_def]
  have h_t_lt_n : t < (n : ℝ) := by
    have : t < (N : ℝ) := by rw [h_N_eq]; linarith
    linarith
  -- t ≥ -log ε' / g, so -log ε' / g < n, hence -log ε' < n * g (g > 0).
  have h_div_le_t : -Real.log ε' / g ≤ t := le_max_right _ _
  have h_div_lt_n : -Real.log ε' / g < (n : ℝ) := lt_of_le_of_lt h_div_le_t h_t_lt_n
  have h_neg_log_lt : -Real.log ε' < (n : ℝ) * g := by
    rw [div_lt_iff₀ hg] at h_div_lt_n
    exact h_div_lt_n
  have h_lt_log : - ((n : ℝ) * g) < Real.log ε' := by linarith
  -- Conclude via `Real.lt_log_iff_exp_lt`.
  have h_iff := Real.lt_log_iff_exp_lt (x := - ((n : ℝ) * g)) (y := ε') hε'
  have h_step : Real.exp (- ((n : ℝ) * g)) < ε' := h_iff.mp h_lt_log
  -- Rewrite `- (n : ℝ) * g = - ((n : ℝ) * g)`.
  have h_neg_eq : - (n : ℝ) * g = - ((n : ℝ) * g) := by ring
  rw [h_neg_eq]
  exact h_step

/-- Closed-form `N(I, R, ε, ε')` for the channel-coding E2 term. Given the AEP
gap `g := I - R - 3ε > 0` and any tolerance `ε' > 0`, there is `N` such that
`(⌈exp(n·R)⌉ - 1) · exp(n · (-I + 3ε)) < ε'` for all `n ≥ N`. -/
@[entry_point]
theorem channelCoding_E2_lt_of_rate
    {I R ε ε' : ℝ} (hgap : 0 < I - R - 3 * ε) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N,
      ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε)) < ε' := by
  obtain ⟨N, hN⟩ := exp_neg_mul_lt_of_rate hgap hε'
  refine ⟨N, ?_⟩
  intro n hn
  -- Pointwise upper bound (mirrors `h_upper` in ChannelCodingAchievability).
  have h_ceil_sub_le :
      ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) ≤ Real.exp ((n : ℝ) * R) := by
    have h_lt : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) <
        Real.exp ((n : ℝ) * R) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith
  have h_mul : ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε))
      ≤ Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (-I + 3 * ε)) :=
    mul_le_mul_of_nonneg_right h_ceil_sub_le (Real.exp_pos _).le
  have h_exp_eq :
      Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (-I + 3 * ε))
        = Real.exp (- (n : ℝ) * (I - R - 3 * ε)) := by
    rw [← Real.exp_add]
    congr 1; ring
  have h_upper_le : ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε))
      ≤ Real.exp (- (n : ℝ) * (I - R - 3 * ε)) := by
    rw [← h_exp_eq]; exact h_mul
  exact lt_of_le_of_lt h_upper_le (hN n hn)

omit [DecidableEq α] in
/-- **Joint AEP — closed-form rate**: for any `ε, η > 0`, there exists `N` such that for all
`n ≥ N`, the jointly typical set has μ-measure ≥ `1 - η`. The bound `N` is built from three
independent applications of `typicalSet_prob_ge_of_rate` (X, Y, Z = X × Y), with `η / 3` each
plus a union bound (Bonferroni). -/
@[entry_point]
theorem jointlyTypicalSet_prob_ge_of_rate
    {β : Type*} [Fintype β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
        ChannelCoding.jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
        (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      1 - η ≤ (μ {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                       InformationTheory.Shannon.jointRV Ys n ω) ∈
                       ChannelCoding.jointlyTypicalSet μ Xs Ys n ε}).toReal := by
  classical
  have hη3 : 0 < η / 3 := by linarith
  -- Three rate-uniform single-axis bounds.
  obtain ⟨N_X, hN_X⟩ :=
    typicalSet_prob_ge_of_rate μ Xs hXs hindepX hidentX hε hη3
  obtain ⟨N_Y, hN_Y⟩ :=
    typicalSet_prob_ge_of_rate μ Ys hYs hindepY hidentY hε hη3
  set Zs : ℕ → Ω → α × β := ChannelCoding.jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    ChannelCoding.measurable_jointSequence Xs Ys hXs hYs i
  obtain ⟨N_Z, hN_Z⟩ :=
    typicalSet_prob_ge_of_rate μ Zs hZs hindepZ hidentZ hε hη3
  refine ⟨max (max N_X N_Y) N_Z, ?_⟩
  intro n hn
  have hn_N_X : N_X ≤ n :=
    (le_max_left _ _).trans <| (le_max_left _ _).trans hn
  have hn_N_Y : N_Y ≤ n :=
    (le_max_right _ _).trans <| (le_max_left _ _).trans hn
  have hn_N_Z : N_Z ≤ n := (le_max_right _ _).trans hn
  -- Single-axis events and their complements.
  set goodX : Set Ω :=
    {ω | InformationTheory.Shannon.jointRV Xs n ω ∈
          InformationTheory.Shannon.typicalSet μ Xs n ε} with hgoodX_def
  set goodY : Set Ω :=
    {ω | InformationTheory.Shannon.jointRV Ys n ω ∈
          InformationTheory.Shannon.typicalSet μ Ys n ε} with hgoodY_def
  set goodZ : Set Ω :=
    {ω | InformationTheory.Shannon.jointRV Zs n ω ∈
          InformationTheory.Shannon.typicalSet μ Zs n ε} with hgoodZ_def
  set jointEvt : Set Ω :=
    {ω | (InformationTheory.Shannon.jointRV Xs n ω,
          InformationTheory.Shannon.jointRV Ys n ω) ∈
          ChannelCoding.jointlyTypicalSet μ Xs Ys n ε} with hjointEvt_def
  set badX : Set Ω := goodXᶜ
  set badY : Set Ω := goodYᶜ
  set badZ : Set Ω := goodZᶜ
  -- Measurability of single-axis events.
  have h_meas_goodX : MeasurableSet goodX :=
    (InformationTheory.Shannon.measurable_jointRV Xs hXs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Xs n ε)
  have h_meas_goodY : MeasurableSet goodY :=
    (InformationTheory.Shannon.measurable_jointRV Ys hYs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Ys n ε)
  have h_meas_goodZ : MeasurableSet goodZ :=
    (InformationTheory.Shannon.measurable_jointRV Zs hZs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Zs n ε)
  -- Joint decomposition.
  have h_joint_decomp : jointEvt = goodX ∩ goodY ∩ goodZ := by
    ext ω
    constructor
    · intro hω
      obtain ⟨hX', hY', hZ'⟩ := hω
      exact ⟨⟨hX', hY'⟩, hZ'⟩
    · rintro ⟨⟨hX', hY'⟩, hZ'⟩
      exact ⟨hX', hY', hZ'⟩
  have h_meas_joint : MeasurableSet jointEvt := by
    rw [h_joint_decomp]
    exact ((h_meas_goodX.inter h_meas_goodY).inter h_meas_goodZ)
  -- Complement ⊆ union of single-axis bads.
  have h_compl_sub : jointEvtᶜ ⊆ badX ∪ badY ∪ badZ := by
    rw [h_joint_decomp]
    intro ω hω
    rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
        not_and_or, not_and_or] at hω
    rcases hω with (h_or | hZ_bad)
    · rcases h_or with hX_bad | hY_bad
      · exact Set.mem_union_left _ (Set.mem_union_left _ hX_bad)
      · exact Set.mem_union_left _ (Set.mem_union_right _ hY_bad)
    · exact Set.mem_union_right _ hZ_bad
  -- Union bound on the complement measure (in ℝ≥0∞).
  have h_bound_compl :
      μ jointEvtᶜ ≤ μ badX + μ badY + μ badZ := by
    calc μ jointEvtᶜ
        ≤ μ (badX ∪ badY ∪ badZ) := measure_mono h_compl_sub
      _ ≤ μ (badX ∪ badY) + μ badZ := measure_union_le _ _
      _ ≤ (μ badX + μ badY) + μ badZ := by
          gcongr; exact measure_union_le badX badY
      _ = μ badX + μ badY + μ badZ := by ring
  -- Each single-axis bad has toReal ≤ η / 3.
  -- From hN_X: 1 - η/3 ≤ (μ goodX).toReal, with (μ badX).toReal = 1 - (μ goodX).toReal.
  have h_goodX_le_one : μ goodX ≤ 1 := prob_le_one
  have h_goodY_le_one : μ goodY ≤ 1 := prob_le_one
  have h_goodZ_le_one : μ goodZ ≤ 1 := prob_le_one
  have h_badX_toReal_eq : (μ badX).toReal = 1 - (μ goodX).toReal := by
    rw [show badX = goodXᶜ from rfl,
        measure_compl h_meas_goodX (measure_ne_top μ _), measure_univ,
        ENNReal.toReal_sub_of_le h_goodX_le_one (by simp)]
    simp
  have h_badY_toReal_eq : (μ badY).toReal = 1 - (μ goodY).toReal := by
    rw [show badY = goodYᶜ from rfl,
        measure_compl h_meas_goodY (measure_ne_top μ _), measure_univ,
        ENNReal.toReal_sub_of_le h_goodY_le_one (by simp)]
    simp
  have h_badZ_toReal_eq : (μ badZ).toReal = 1 - (μ goodZ).toReal := by
    rw [show badZ = goodZᶜ from rfl,
        measure_compl h_meas_goodZ (measure_ne_top μ _), measure_univ,
        ENNReal.toReal_sub_of_le h_goodZ_le_one (by simp)]
    simp
  have h_X_bound : (μ badX).toReal ≤ η / 3 := by
    have := hN_X n hn_N_X
    rw [h_badX_toReal_eq]; linarith
  have h_Y_bound : (μ badY).toReal ≤ η / 3 := by
    have := hN_Y n hn_N_Y
    rw [h_badY_toReal_eq]; linarith
  have h_Z_bound : (μ badZ).toReal ≤ η / 3 := by
    have := hN_Z n hn_N_Z
    rw [h_badZ_toReal_eq]; linarith
  -- Convert the ENNReal bound to a Real bound on toReal.
  have h_badX_ne_top : μ badX ≠ ∞ := measure_ne_top μ _
  have h_badY_ne_top : μ badY ≠ ∞ := measure_ne_top μ _
  have h_badZ_ne_top : μ badZ ≠ ∞ := measure_ne_top μ _
  have h_sum_ne_top : μ badX + μ badY + μ badZ ≠ ∞ := by
    simp [h_badX_ne_top, h_badY_ne_top, h_badZ_ne_top]
  have h_compl_toReal_le :
      (μ jointEvtᶜ).toReal ≤ (μ badX).toReal + (μ badY).toReal + (μ badZ).toReal := by
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top μ _) h_sum_ne_top).mpr h_bound_compl
    have h_sum_eq :
        (μ badX + μ badY + μ badZ).toReal
          = (μ badX).toReal + (μ badY).toReal + (μ badZ).toReal := by
      rw [ENNReal.toReal_add (by simp [h_badX_ne_top, h_badY_ne_top])
            h_badZ_ne_top,
          ENNReal.toReal_add h_badX_ne_top h_badY_ne_top]
    rw [h_sum_eq] at h1; exact h1
  have h_compl_le : (μ jointEvtᶜ).toReal ≤ η := by
    have := h_compl_toReal_le
    linarith
  -- Convert (μ jointEvt).toReal = 1 - (μ jointEvtᶜ).toReal.
  have h_joint_le_one : μ jointEvt ≤ 1 := prob_le_one
  have h_jointEvt_toReal_eq : (μ jointEvt).toReal = 1 - (μ jointEvtᶜ).toReal := by
    have h_compl_eq : μ jointEvtᶜ = 1 - μ jointEvt := by
      rw [measure_compl h_meas_joint (measure_ne_top μ _), measure_univ]
    rw [h_compl_eq, ENNReal.toReal_sub_of_le h_joint_le_one (by simp)]
    simp
  linarith [h_jointEvt_toReal_eq, h_compl_le]

/-! ## Closed-form `N(ε, η)` variants

The `_of_rate` form (`∃ N, ∀ n ≥ N, P`) suffices for many callers. When the outer
construction needs to substitute a sequence `δ_n → 0` and conclude `N(δ_n) ≤ n`,
`N` must instead be exposed as a closed-form function of the inputs.

The closed-form `N` is the same one extracted in the `_of_rate` proof bodies,
hoisted out as a `def`. The `_at_N` theorems differ from `_of_rate` only in that
the existential is collapsed to the explicit `def`. -/

/-- Closed-form `N(V, η, ε)` for `typicalSet_prob_ge` — extracted from the
proof of `typicalSet_prob_ge_of_rate`. -/
noncomputable def typicalSetMinN (V η ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (V / (η * ε ^ 2)) + 1)

lemma typicalSetMinN_mono_V {V V' η ε : ℝ} (hηε : 0 < η * ε ^ 2)
    (hVV' : V ≤ V') :
    typicalSetMinN V η ε ≤ typicalSetMinN V' η ε := by
  unfold typicalSetMinN
  refine max_le_max le_rfl ?_
  refine Nat.add_le_add_right ?_ 1
  refine Nat.ceil_le_ceil ?_
  exact div_le_div_of_nonneg_right hVV' hηε.le

omit [DecidableEq α] in
/-- Closed-form `N` version of `typicalSet_prob_ge_of_rate`. -/
@[entry_point]
theorem typicalSet_prob_ge_at_N
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ n, typicalSetMinN (pmfLogVariance μ Xs) η ε ≤ n →
      1 - η ≤ (μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}).toReal := by
  classical
  intro n hn_ge
  set V : ℝ := pmfLogVariance μ Xs with hV_def
  have hV_nn : 0 ≤ V := pmfLogVariance_nonneg μ Xs
  set Nreal : ℝ := V / (η * ε ^ 2) with hNreal_def
  -- `typicalSetMinN V η ε = max 1 (⌈Nreal⌉ + 1)`.
  have hN_eq : typicalSetMinN V η ε = max 1 (Nat.ceil Nreal + 1) := by
    unfold typicalSetMinN
    rfl
  rw [hN_eq] at hn_ge
  have hn_pos : 0 < n := by
    have h1 : 1 ≤ max 1 (Nat.ceil Nreal + 1) := le_max_left _ _
    exact lt_of_lt_of_le Nat.zero_lt_one (h1.trans hn_ge)
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- Key inequality: V / (n · ε²) ≤ η.
  have h_rate : V / ((n : ℝ) * ε ^ 2) ≤ η := by
    have hnε : 0 < (n : ℝ) * ε ^ 2 := mul_pos hn_real_pos (pow_pos hε 2)
    have hηε : 0 < η * ε ^ 2 := mul_pos hη (pow_pos hε 2)
    rw [div_le_iff₀ hnε]
    have h_N_le : (Nat.ceil Nreal + 1 : ℝ) ≤ ((max 1 (Nat.ceil Nreal + 1) : ℕ) : ℝ) := by
      have : (Nat.ceil Nreal + 1 : ℕ) ≤ max 1 (Nat.ceil Nreal + 1) := le_max_right _ _
      exact_mod_cast this
    have h_N_le_n : ((max 1 (Nat.ceil Nreal + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn_ge
    have h_Nreal_le_n : Nreal ≤ (n : ℝ) := by
      have h1 : Nreal ≤ (Nat.ceil Nreal : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil Nreal : ℝ) ≤ (Nat.ceil Nreal + 1 : ℝ) := by linarith
      linarith
    have h_V_le : V ≤ (n : ℝ) * (η * ε ^ 2) := by
      rw [hNreal_def] at h_Nreal_le_n
      have := (div_le_iff₀ hηε).mp h_Nreal_le_n
      linarith
    linarith
  -- Reuse the body of `typicalSet_prob_ge_of_rate` from `h_rate` onward.
  have h_bad := aep_chebyshev_bound μ Xs hXs hindep hident hε hn_pos
  set bad : Set Ω := {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                                - entropy μ (Xs 0)|}
  have h_bound : μ bad ≤ ENNReal.ofReal η := by
    refine h_bad.trans ?_
    exact ENNReal.ofReal_le_ofReal h_rate
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
  have h_event_eq := typicalSet_compl_eq μ Xs n (ε := ε)
  rw [h_event_eq]
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

omit [DecidableEq α] in
/-- Variance-upper-bound version of `typicalSet_prob_ge_at_N`. The caller
provides an upper bound `V_upper ≥ pmfLogVariance μ Xs`, and the closed-form `N`
is `typicalSetMinN V_upper η ε` (independent of the true variance). -/
@[entry_point]
theorem typicalSet_prob_ge_at_N_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (V_upper : ℝ) (hV_upper : pmfLogVariance μ Xs ≤ V_upper)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ n, typicalSetMinN V_upper η ε ≤ n →
      1 - η ≤ (μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}).toReal := by
  intro n hn_ge
  have hηε : 0 < η * ε ^ 2 := mul_pos hη (pow_pos hε 2)
  have h_mono : typicalSetMinN (pmfLogVariance μ Xs) η ε ≤ typicalSetMinN V_upper η ε :=
    typicalSetMinN_mono_V hηε hV_upper
  exact typicalSet_prob_ge_at_N μ Xs hXs hindep hident hε hη n (h_mono.trans hn_ge)

/-- Closed-form `N(g, ε')` for exponential decay `exp(-n g) < ε'`. -/
noncomputable def expNegMulMinN (g ε' : ℝ) : ℕ :=
  Nat.ceil (max 0 (-Real.log ε' / g)) + 1

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- Closed-form `N` version of `exp_neg_mul_lt_of_rate`. -/
@[entry_point]
theorem exp_neg_mul_lt_at_N {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∀ n, expNegMulMinN g ε' ≤ n → Real.exp (- (n : ℝ) * g) < ε' := by
  intro n hn_ge
  set t : ℝ := max 0 (-Real.log ε' / g) with ht_def
  have h_t_nn : 0 ≤ t := le_max_left _ _
  have h_ceil_lt_succ : (Nat.ceil t : ℝ) < (Nat.ceil t + 1 : ℝ) := by linarith
  have h_t_le_ceil : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil _
  have h_N_le_n : ((expNegMulMinN g ε' : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have h_N_eq : ((expNegMulMinN g ε' : ℕ) : ℝ) = (Nat.ceil t : ℝ) + 1 := by
    unfold expNegMulMinN
    push_cast
    rfl
  have h_t_lt_n : t < (n : ℝ) := by
    have : t < ((expNegMulMinN g ε' : ℕ) : ℝ) := by rw [h_N_eq]; linarith
    linarith
  have h_div_le_t : -Real.log ε' / g ≤ t := le_max_right _ _
  have h_div_lt_n : -Real.log ε' / g < (n : ℝ) := lt_of_le_of_lt h_div_le_t h_t_lt_n
  have h_neg_log_lt : -Real.log ε' < (n : ℝ) * g := by
    rw [div_lt_iff₀ hg] at h_div_lt_n
    exact h_div_lt_n
  have h_lt_log : - ((n : ℝ) * g) < Real.log ε' := by linarith
  have h_iff := Real.lt_log_iff_exp_lt (x := - ((n : ℝ) * g)) (y := ε') hε'
  have h_step : Real.exp (- ((n : ℝ) * g)) < ε' := h_iff.mp h_lt_log
  have h_neg_eq : - (n : ℝ) * g = - ((n : ℝ) * g) := by ring
  rw [h_neg_eq]
  exact h_step

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- Closed-form `N` version of `channelCoding_E2_lt_of_rate`.
The `N` is `expNegMulMinN (I - R - 3ε) ε'`. -/
@[entry_point]
theorem channelCoding_E2_lt_at_N
    {I R ε ε' : ℝ} (hgap : 0 < I - R - 3 * ε) (hε' : 0 < ε') :
    ∀ n, expNegMulMinN (I - R - 3 * ε) ε' ≤ n →
      ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε)) < ε' := by
  intro n hn
  have hN := exp_neg_mul_lt_at_N hgap hε' n hn
  have h_ceil_sub_le :
      ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) ≤ Real.exp ((n : ℝ) * R) := by
    have h_lt : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) <
        Real.exp ((n : ℝ) * R) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith
  have h_mul : ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε))
      ≤ Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (-I + 3 * ε)) :=
    mul_le_mul_of_nonneg_right h_ceil_sub_le (Real.exp_pos _).le
  have h_exp_eq :
      Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (-I + 3 * ε))
        = Real.exp (- (n : ℝ) * (I - R - 3 * ε)) := by
    rw [← Real.exp_add]
    congr 1; ring
  have h_upper_le : ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε))
      ≤ Real.exp (- (n : ℝ) * (I - R - 3 * ε)) := by
    rw [← h_exp_eq]; exact h_mul
  exact lt_of_le_of_lt h_upper_le hN

/-- Closed-form `N(V_X, V_Y, V_Z, η, ε)` for the joint AEP rate bound.
Splits `η/3` across three axes. -/
noncomputable def jointlyTypicalSetMinN
    (V_X V_Y V_Z η ε : ℝ) : ℕ :=
  max (max (typicalSetMinN V_X (η / 3) ε) (typicalSetMinN V_Y (η / 3) ε))
      (typicalSetMinN V_Z (η / 3) ε)

omit [DecidableEq α] in
/-- Variance-upper-bound version of joint AEP. The caller provides axis-wise
variance upper bounds `V_X, V_Y, V_Z`, and the closed-form `N` is
`jointlyTypicalSetMinN V_X V_Y V_Z η ε`. -/
@[entry_point]
theorem jointlyTypicalSet_prob_ge_at_N_le
    {β : Type*} [Fintype β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
        ChannelCoding.jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
        (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    (V_X V_Y V_Z : ℝ)
    (hV_X : pmfLogVariance μ Xs ≤ V_X)
    (hV_Y : pmfLogVariance μ Ys ≤ V_Y)
    (hV_Z : pmfLogVariance μ (ChannelCoding.jointSequence Xs Ys) ≤ V_Z)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ n, jointlyTypicalSetMinN V_X V_Y V_Z η ε ≤ n →
      1 - η ≤ (μ {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                       InformationTheory.Shannon.jointRV Ys n ω) ∈
                       ChannelCoding.jointlyTypicalSet μ Xs Ys n ε}).toReal := by
  classical
  intro n hn
  have hη3 : 0 < η / 3 := by linarith
  -- Three axis-wise bounds via the closed-form `_at_N_le` lemma.
  have hn_N_X : typicalSetMinN V_X (η / 3) ε ≤ n :=
    (le_max_left _ _).trans <| (le_max_left _ _).trans hn
  have hn_N_Y : typicalSetMinN V_Y (η / 3) ε ≤ n :=
    (le_max_right _ _).trans <| (le_max_left _ _).trans hn
  have hn_N_Z : typicalSetMinN V_Z (η / 3) ε ≤ n :=
    (le_max_right _ _).trans hn
  have hN_X := typicalSet_prob_ge_at_N_le μ Xs hXs hindepX hidentX V_X hV_X hε hη3 n hn_N_X
  have hN_Y := typicalSet_prob_ge_at_N_le μ Ys hYs hindepY hidentY V_Y hV_Y hε hη3 n hn_N_Y
  set Zs : ℕ → Ω → α × β := ChannelCoding.jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    ChannelCoding.measurable_jointSequence Xs Ys hXs hYs i
  have hN_Z := typicalSet_prob_ge_at_N_le μ Zs hZs hindepZ hidentZ V_Z hV_Z hε hη3 n hn_N_Z
  -- The body below mirrors `jointlyTypicalSet_prob_ge_of_rate`'s union-bound step.
  set goodX : Set Ω :=
    {ω | InformationTheory.Shannon.jointRV Xs n ω ∈
          InformationTheory.Shannon.typicalSet μ Xs n ε} with hgoodX_def
  set goodY : Set Ω :=
    {ω | InformationTheory.Shannon.jointRV Ys n ω ∈
          InformationTheory.Shannon.typicalSet μ Ys n ε} with hgoodY_def
  set goodZ : Set Ω :=
    {ω | InformationTheory.Shannon.jointRV Zs n ω ∈
          InformationTheory.Shannon.typicalSet μ Zs n ε} with hgoodZ_def
  set jointEvt : Set Ω :=
    {ω | (InformationTheory.Shannon.jointRV Xs n ω,
          InformationTheory.Shannon.jointRV Ys n ω) ∈
          ChannelCoding.jointlyTypicalSet μ Xs Ys n ε} with hjointEvt_def
  set badX : Set Ω := goodXᶜ
  set badY : Set Ω := goodYᶜ
  set badZ : Set Ω := goodZᶜ
  have h_meas_goodX : MeasurableSet goodX :=
    (InformationTheory.Shannon.measurable_jointRV Xs hXs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Xs n ε)
  have h_meas_goodY : MeasurableSet goodY :=
    (InformationTheory.Shannon.measurable_jointRV Ys hYs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Ys n ε)
  have h_meas_goodZ : MeasurableSet goodZ :=
    (InformationTheory.Shannon.measurable_jointRV Zs hZs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Zs n ε)
  have h_joint_decomp : jointEvt = goodX ∩ goodY ∩ goodZ := by
    ext ω
    constructor
    · intro hω
      obtain ⟨hX', hY', hZ'⟩ := hω
      exact ⟨⟨hX', hY'⟩, hZ'⟩
    · rintro ⟨⟨hX', hY'⟩, hZ'⟩
      exact ⟨hX', hY', hZ'⟩
  have h_meas_joint : MeasurableSet jointEvt := by
    rw [h_joint_decomp]
    exact ((h_meas_goodX.inter h_meas_goodY).inter h_meas_goodZ)
  have h_compl_sub : jointEvtᶜ ⊆ badX ∪ badY ∪ badZ := by
    rw [h_joint_decomp]
    intro ω hω
    rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
        not_and_or, not_and_or] at hω
    rcases hω with (h_or | hZ_bad)
    · rcases h_or with hX_bad | hY_bad
      · exact Set.mem_union_left _ (Set.mem_union_left _ hX_bad)
      · exact Set.mem_union_left _ (Set.mem_union_right _ hY_bad)
    · exact Set.mem_union_right _ hZ_bad
  have h_bound_compl :
      μ jointEvtᶜ ≤ μ badX + μ badY + μ badZ := by
    calc μ jointEvtᶜ
        ≤ μ (badX ∪ badY ∪ badZ) := measure_mono h_compl_sub
      _ ≤ μ (badX ∪ badY) + μ badZ := measure_union_le _ _
      _ ≤ (μ badX + μ badY) + μ badZ := by
          gcongr; exact measure_union_le badX badY
      _ = μ badX + μ badY + μ badZ := by ring
  have h_goodX_le_one : μ goodX ≤ 1 := prob_le_one
  have h_goodY_le_one : μ goodY ≤ 1 := prob_le_one
  have h_goodZ_le_one : μ goodZ ≤ 1 := prob_le_one
  have h_badX_toReal_eq : (μ badX).toReal = 1 - (μ goodX).toReal := by
    rw [show badX = goodXᶜ from rfl,
        measure_compl h_meas_goodX (measure_ne_top μ _), measure_univ,
        ENNReal.toReal_sub_of_le h_goodX_le_one (by simp)]
    simp
  have h_badY_toReal_eq : (μ badY).toReal = 1 - (μ goodY).toReal := by
    rw [show badY = goodYᶜ from rfl,
        measure_compl h_meas_goodY (measure_ne_top μ _), measure_univ,
        ENNReal.toReal_sub_of_le h_goodY_le_one (by simp)]
    simp
  have h_badZ_toReal_eq : (μ badZ).toReal = 1 - (μ goodZ).toReal := by
    rw [show badZ = goodZᶜ from rfl,
        measure_compl h_meas_goodZ (measure_ne_top μ _), measure_univ,
        ENNReal.toReal_sub_of_le h_goodZ_le_one (by simp)]
    simp
  have h_X_bound : (μ badX).toReal ≤ η / 3 := by
    rw [h_badX_toReal_eq]; linarith
  have h_Y_bound : (μ badY).toReal ≤ η / 3 := by
    rw [h_badY_toReal_eq]; linarith
  have h_Z_bound : (μ badZ).toReal ≤ η / 3 := by
    rw [h_badZ_toReal_eq]; linarith
  have h_badX_ne_top : μ badX ≠ ∞ := measure_ne_top μ _
  have h_badY_ne_top : μ badY ≠ ∞ := measure_ne_top μ _
  have h_badZ_ne_top : μ badZ ≠ ∞ := measure_ne_top μ _
  have h_sum_ne_top : μ badX + μ badY + μ badZ ≠ ∞ := by
    simp [h_badX_ne_top, h_badY_ne_top, h_badZ_ne_top]
  have h_compl_toReal_le :
      (μ jointEvtᶜ).toReal ≤ (μ badX).toReal + (μ badY).toReal + (μ badZ).toReal := by
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top μ _) h_sum_ne_top).mpr h_bound_compl
    have h_sum_eq :
        (μ badX + μ badY + μ badZ).toReal
          = (μ badX).toReal + (μ badY).toReal + (μ badZ).toReal := by
      rw [ENNReal.toReal_add (by simp [h_badX_ne_top, h_badY_ne_top])
            h_badZ_ne_top,
          ENNReal.toReal_add h_badX_ne_top h_badY_ne_top]
    rw [h_sum_eq] at h1; exact h1
  have h_compl_le : (μ jointEvtᶜ).toReal ≤ η := by
    linarith
  have h_joint_le_one : μ jointEvt ≤ 1 := prob_le_one
  have h_jointEvt_toReal_eq : (μ jointEvt).toReal = 1 - (μ jointEvtᶜ).toReal := by
    have h_compl_eq : μ jointEvtᶜ = 1 - μ jointEvt := by
      rw [measure_compl h_meas_joint (measure_ne_top μ _), measure_univ]
    rw [h_compl_eq, ENNReal.toReal_sub_of_le h_joint_le_one (by simp)]
    simp
  linarith [h_jointEvt_toReal_eq, h_compl_le]

end InformationTheory.Shannon
