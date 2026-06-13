import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem
import InformationTheory.Shannon.ChannelCoding.ShannonTheoremGeneral
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# δ-asymptotic `pmfLog` bounds for the smooth channel

Part file split from `ShannonTheoremFullDischarge`. Provides pointwise `pmfLog` bounds
for `iidXs`, `iidYs`, and `jointSequence` under `iidAmbientMeasure p (Channel.smooth W δ)`,
and analytic lemmas `exists_N_log_sq_le_n` / `exists_N_log_sq_plus_const_le_n`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Pointwise `pmfLog` bounds and analytic growth lemmas -/

open InformationTheory.Shannon (pmfLog)

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [MeasurableSingletonClass β] in
/-- The pmfLog of `iidXs` is independent of `W` and `δ`, since the marginal is always `p`. -/
lemma pmfLog_iidXs_const_in_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (a : α) :
    pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidXs a
      = pmfLog (iidAmbientMeasure p W) iidXs a := by
  haveI : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  unfold pmfLog
  rw [iidAmbient_map_iidXs p (Channel.smooth W δ) 0, iidAmbient_map_iidXs p W 0]

omit [DecidableEq α] [Nonempty α] [DecidableEq β] in
/-- `|pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidYs b| ≤ log(|β|/δ)`,
via the output lower bound `(W_smooth δ a).real {b} ≥ δ/|β|`. -/
lemma pmfLog_iidYs_bound_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (b : β) :
    |pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidYs b|
      ≤ Real.log ((Fintype.card β : ℝ) / δ) := by
  classical
  haveI : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  -- |β| ≥ 1.
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_inv_pos : (0 : ℝ) < (Fintype.card β : ℝ)⁻¹ := inv_pos.mpr hβ_pos
  -- Step 1: pmfLog rewritten as -log of the smooth output.
  have h_map : (iidAmbientMeasure p (Channel.smooth W δ)).map (iidYs 0)
      = outputDistribution p (Channel.smooth W δ) :=
    iidAmbient_map_iidYs p (Channel.smooth W δ) 0
  have h_pmfLog_eq : pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidYs b
      = -Real.log ((outputDistribution p (Channel.smooth W δ)).real {b}) := by
    unfold pmfLog
    rw [h_map]
  -- Step 2: lower bound for the output.
  -- (outputDistribution p (W_smooth δ)).real {b} ≥ δ / |β|.
  have h_out_sum : (outputDistribution p (Channel.smooth W δ)).real {b}
      = ∑ a : α, p.real {a} * (Channel.smooth W δ a).real {b} := by
    -- Reuse the inline argument from `ChannelCodingAchievability`.
    have h1 : (outputDistribution p (Channel.smooth W δ)) {b}
        = (jointDistribution p (Channel.smooth W δ)) (Set.univ ×ˢ ({b} : Set β)) := by
      show (jointDistribution p (Channel.smooth W δ)).snd {b} = _
      rw [Measure.snd_apply (measurableSet_singleton _)]
      congr 1; ext ⟨a, b'⟩; simp
    rw [measureReal_def, h1, jointDistribution_def]
    have h2 : (p ⊗ₘ (Channel.smooth W δ)) (Set.univ ×ˢ ({b} : Set β))
        = ∫⁻ a, (Channel.smooth W δ a) {b} ∂p := by
      rw [Measure.compProd_apply (MeasurableSet.univ.prod (measurableSet_singleton _))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      show (Channel.smooth W δ a) (Prod.mk a ⁻¹' (Set.univ ×ˢ ({b} : Set β)))
          = (Channel.smooth W δ a) {b}
      congr 1; ext y; simp
    rw [h2, lintegral_fintype,
        ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
          (measure_ne_top _ _) (measure_ne_top _ _))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ENNReal.toReal_mul]
    show (Channel.smooth W δ a).real {b} * p.real {a}
        = p.real {a} * (Channel.smooth W δ a).real {b}
    ring
  -- Each (W_smooth δ a).real{b} ≥ δ / |β|.
  have h_term_lb : ∀ a : α,
      δ * (Fintype.card β : ℝ)⁻¹ ≤ (Channel.smooth W δ a).real {b} := by
    intro a
    rw [Channel.smooth_real_singleton W hδ_pos.le hδ_le]
    have h1 : 0 ≤ (1 - δ) * (W a).real {b} :=
      mul_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  -- Sum lower bound.
  have h_sum_p : ∑ a : α, p.real {a} = 1 := by
    have h_univ : (∑ a : α, p.real {a}) = p.real (Set.univ : Set α) := by
      rw [measureReal_def]
      have h_sum_ennreal : (∑ a : α, p {a}) = p (Set.univ : Set α) := by
        rw [← measure_biUnion_finset (s := (Finset.univ : Finset α))
          (f := fun a => ({a} : Set α))
          (fun i _ j _ hij => by
            simpa [Set.disjoint_singleton] using hij)
          (fun i _ => measurableSet_singleton _)]
        congr 1
        ext a
        simp
      rw [← h_sum_ennreal, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
      rfl
    rw [h_univ]
    exact MeasureTheory.probReal_univ
  have h_out_lb : δ * (Fintype.card β : ℝ)⁻¹
      ≤ (outputDistribution p (Channel.smooth W δ)).real {b} := by
    rw [h_out_sum]
    calc δ * (Fintype.card β : ℝ)⁻¹
        = (∑ a : α, p.real {a}) * (δ * (Fintype.card β : ℝ)⁻¹) := by
          rw [h_sum_p]; ring
      _ = ∑ a : α, p.real {a} * (δ * (Fintype.card β : ℝ)⁻¹) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ a : α, p.real {a} * (Channel.smooth W δ a).real {b} := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          have hpa_nn : 0 ≤ p.real {a} := ENNReal.toReal_nonneg
          exact mul_le_mul_of_nonneg_left (h_term_lb a) hpa_nn
  -- Upper bound: ≤ 1 (probability measure).
  haveI : IsProbabilityMeasure (outputDistribution p (Channel.smooth W δ)) := by
    unfold outputDistribution; infer_instance
  have h_out_ub : (outputDistribution p (Channel.smooth W δ)).real {b} ≤ 1 := by
    rw [measureReal_def]
    have h_le : (outputDistribution p (Channel.smooth W δ)) {b} ≤ 1 := by
      have h1 := prob_le_one (μ := outputDistribution p (Channel.smooth W δ)) (s := ({b} : Set β))
      exact h1
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by rw [ENNReal.ofReal_one]; exact h_le)
  -- Lower bound of output > 0.
  have h_dlb_pos : 0 < δ * (Fintype.card β : ℝ)⁻¹ := mul_pos hδ_pos hβ_inv_pos
  have h_out_pos : 0 < (outputDistribution p (Channel.smooth W δ)).real {b} :=
    lt_of_lt_of_le h_dlb_pos h_out_lb
  -- Step 3: combine: log of value in [δ/|β|, 1] has |.| ≤ log(|β|/δ).
  rw [h_pmfLog_eq]
  -- log_target := log((outputDistribution).real {b})
  set q : ℝ := (outputDistribution p (Channel.smooth W δ)).real {b} with hq_def
  -- We have q ∈ (0, 1], q ≥ δ / |β|.
  -- log q ∈ [log(δ/|β|), 0], so -log q ∈ [0, -log(δ/|β|)] = [0, log(|β|/δ)].
  have h_log_nonpos : Real.log q ≤ 0 := Real.log_nonpos h_out_pos.le h_out_ub
  have h_log_lb : Real.log (δ * (Fintype.card β : ℝ)⁻¹) ≤ Real.log q :=
    Real.log_le_log h_dlb_pos h_out_lb
  have h_neg_log_lb : 0 ≤ -Real.log q := by linarith
  have h_target_eq : Real.log ((Fintype.card β : ℝ) / δ)
      = -Real.log (δ * (Fintype.card β : ℝ)⁻¹) := by
    rw [show (Fintype.card β : ℝ) / δ = (δ * (Fintype.card β : ℝ)⁻¹)⁻¹ by
      field_simp]
    exact Real.log_inv _
  rw [abs_of_nonneg h_neg_log_lb, h_target_eq]
  linarith

omit [DecidableEq α] [DecidableEq β] in
/-- `|pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) (jointSequence iidXs iidYs) (a,b)|
≤ log(|α|·|β| / (p_min · δ))`. -/
lemma pmfLog_jointSequence_bound_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    {p_min : ℝ} (hp_min_pos : 0 < p_min)
    (hp_min_le : ∀ a : α, p_min ≤ p.real {a})
    (W : Channel α β) [IsMarkovKernel W]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (ab : α × β) :
    |pmfLog (iidAmbientMeasure p (Channel.smooth W δ))
        (jointSequence iidXs iidYs) ab|
      ≤ Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ))
          / (p_min * δ)) := by
  classical
  haveI : IsMarkovKernel (Channel.smooth W δ) :=
    Channel.smooth_isMarkovKernel W hδ_pos.le hδ_le
  obtain ⟨a, b⟩ := ab
  -- Cardinality positivity.
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_pos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hβ_inv_pos : (0 : ℝ) < (Fintype.card β : ℝ)⁻¹ := inv_pos.mpr hβ_pos
  have hαβ_pos : (0 : ℝ) < (Fintype.card α : ℝ) * (Fintype.card β : ℝ) :=
    mul_pos hα_pos hβ_pos
  have hp_min_δ_pos : (0 : ℝ) < p_min * δ := mul_pos hp_min_pos hδ_pos
  -- Step 1: marginal identification.
  have h_map : (iidAmbientMeasure p (Channel.smooth W δ)).map
      (jointSequence iidXs iidYs 0) = jointDistribution p (Channel.smooth W δ) :=
    iidAmbient_map_jointSequence p (Channel.smooth W δ) 0
  have h_pmfLog_eq : pmfLog (iidAmbientMeasure p (Channel.smooth W δ))
        (jointSequence iidXs iidYs) (a, b)
      = -Real.log ((jointDistribution p (Channel.smooth W δ)).real {(a, b)}) := by
    unfold pmfLog
    rw [h_map]
  -- Step 2: joint singleton real-value = p.real {a} * (W_smooth δ a).real {b}.
  have h_joint_real : (jointDistribution p (Channel.smooth W δ)).real {(a, b)}
      = p.real {a} * (Channel.smooth W δ a).real {b} := by
    rw [measureReal_def, jointDistribution_singleton, ENNReal.toReal_mul]
    rfl
  -- Step 3: lower bound. (W_smooth δ a).real{b} ≥ δ/|β|, p.real{a} ≥ p_min.
  have h_term_lb : δ * (Fintype.card β : ℝ)⁻¹
      ≤ (Channel.smooth W δ a).real {b} := by
    rw [Channel.smooth_real_singleton W hδ_pos.le hδ_le]
    have h1 : 0 ≤ (1 - δ) * (W a).real {b} :=
      mul_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  have h_term_lb_pos : (0 : ℝ) < δ * (Fintype.card β : ℝ)⁻¹ := mul_pos hδ_pos hβ_inv_pos
  have h_smooth_pos : 0 < (Channel.smooth W δ a).real {b} :=
    lt_of_lt_of_le h_term_lb_pos h_term_lb
  -- joint ≥ p_min * (δ/|β|).
  have h_joint_lb : p_min * (δ * (Fintype.card β : ℝ)⁻¹)
      ≤ (jointDistribution p (Channel.smooth W δ)).real {(a, b)} := by
    rw [h_joint_real]
    exact mul_le_mul (hp_min_le a) h_term_lb h_term_lb_pos.le ENNReal.toReal_nonneg
  -- joint > 0.
  have h_joint_lb_pos : (0 : ℝ) < p_min * (δ * (Fintype.card β : ℝ)⁻¹) :=
    mul_pos hp_min_pos h_term_lb_pos
  have h_joint_pos : 0 < (jointDistribution p (Channel.smooth W δ)).real {(a, b)} :=
    lt_of_lt_of_le h_joint_lb_pos h_joint_lb
  -- Step 4: upper bound ≤ 1.
  have h_joint_ub : (jointDistribution p (Channel.smooth W δ)).real {(a, b)} ≤ 1 := by
    rw [measureReal_def]
    have h_le : (jointDistribution p (Channel.smooth W δ)) {(a, b)} ≤ 1 :=
      prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by rw [ENNReal.ofReal_one]; exact h_le)
  -- Step 5: target log.
  -- Loose target: log(|α||β| / (p_min·δ)) ≥ log(|β|/(p_min·δ)) ≥ -log(p_min · (δ/|β|)).
  have h_target_eq_alt : Real.log ((Fintype.card β : ℝ) / (p_min * δ))
      = -Real.log (p_min * (δ * (Fintype.card β : ℝ)⁻¹)) := by
    rw [show ((Fintype.card β : ℝ) / (p_min * δ))
          = (p_min * (δ * (Fintype.card β : ℝ)⁻¹))⁻¹ by
      field_simp]
    exact Real.log_inv _
  -- |α| ≥ 1 ⇒ log(|α|·|β| / (p_min·δ)) ≥ log(|β| / (p_min·δ)).
  have hα_ge_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have h_div_le : (Fintype.card β : ℝ) / (p_min * δ)
      ≤ ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ) := by
    refine div_le_div_of_nonneg_right ?_ hp_min_δ_pos.le
    have hβ_nn : 0 ≤ (Fintype.card β : ℝ) := hβ_pos.le
    calc (Fintype.card β : ℝ)
        = 1 * (Fintype.card β : ℝ) := (one_mul _).symm
      _ ≤ (Fintype.card α : ℝ) * (Fintype.card β : ℝ) :=
          mul_le_mul_of_nonneg_right hα_ge_one hβ_nn
  have h_log_div_le : Real.log ((Fintype.card β : ℝ) / (p_min * δ))
      ≤ Real.log (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) / (p_min * δ)) := by
    refine Real.log_le_log ?_ h_div_le
    exact div_pos hβ_pos hp_min_δ_pos
  -- Combine: -log q ≤ -log(p_min · δ/|β|) = log(|β|/(p_min·δ)) ≤ log(|α|·|β|/(p_min·δ)).
  rw [h_pmfLog_eq]
  set q : ℝ := (jointDistribution p (Channel.smooth W δ)).real {(a, b)} with hq_def
  have h_log_q_nonpos : Real.log q ≤ 0 := Real.log_nonpos h_joint_pos.le h_joint_ub
  have h_log_q_lb : Real.log (p_min * (δ * (Fintype.card β : ℝ)⁻¹)) ≤ Real.log q :=
    Real.log_le_log h_joint_lb_pos h_joint_lb
  have h_neg_log_nn : 0 ≤ -Real.log q := by linarith
  rw [abs_of_nonneg h_neg_log_nn]
  -- -log q ≤ -log(p_min · δ/|β|) = log(|β|/(p_min·δ))
  have h_neg_log_q_le : -Real.log q ≤ Real.log ((Fintype.card β : ℝ) / (p_min * δ)) := by
    rw [h_target_eq_alt]; linarith
  linarith

/-- For any `C > 0`, there exists `N` such that `C · (log (n+1))² + 1 ≤ n` for all `n ≥ N`. -/
lemma exists_N_log_sq_le_n (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (Real.log ((n : ℝ) + 1))^2 + 1 ≤ (n : ℝ) := by
  -- Step 1: (log x)^2 / x → 0 as x → ∞.
  have h_lim : Filter.Tendsto (fun x : ℝ => (Real.log x)^2 / x) Filter.atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    -- `(fun x => log x ^ 2 / (1 * x + 0))` simplifies to `(fun x => (log x)^2 / x)`.
    simpa using h
  -- Step 2: eventually (log x)^2 / x < 1 / (4C).
  have h_pos : (0 : ℝ) < 1 / (4 * C) := by positivity
  have h_ev : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x)^2 / x < 1 / (4 * C) := by
    -- |.| → 0 at nhds 0 gives the eventual upper bound.
    exact h_lim.eventually_lt_const h_pos
  -- Step 3: pick `x₀ ≥ max (1, 4)` so the bound + `x ≥ 4` together suffice.
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨x₀, hx₀⟩ := h_ev
  set N : ℕ := max (Nat.ceil x₀) 4 with hN_def
  refine ⟨N, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := by
    have : (4 : ℕ) ≤ N := le_max_right _ _
    exact this.trans hn
  have hn_x₀ : x₀ ≤ (n : ℝ) := by
    have h1 : (Nat.ceil x₀ : ℕ) ≤ N := le_max_left _ _
    have h2 : x₀ ≤ (Nat.ceil x₀ : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil x₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1.trans hn
    linarith
  -- We want `C * (log (n+1))^2 + 1 ≤ n`. Apply the eventual bound at `x := n + 1`.
  have hn1_x₀ : x₀ ≤ (n : ℝ) + 1 := by linarith
  have hbound : (Real.log ((n : ℝ) + 1))^2 / ((n : ℝ) + 1) < 1 / (4 * C) := hx₀ ((n : ℝ) + 1) hn1_x₀
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    linarith
  -- Multiply the bound by (n+1) > 0:  (log(n+1))^2 < (n+1) / (4C).
  have hsq_bound : (Real.log ((n : ℝ) + 1))^2 < ((n : ℝ) + 1) / (4 * C) := by
    have := (div_lt_iff₀ h_n1_pos).mp hbound
    have h4C_pos : (0 : ℝ) < 4 * C := by linarith
    rw [div_eq_mul_inv, ← div_eq_mul_inv] at this
    -- this : (log (n+1))^2 < (n+1) * (1 / (4C)) = (n+1) / (4C).
    have h_rewrite : ((n : ℝ) + 1) * (1 / (4 * C)) = ((n : ℝ) + 1) / (4 * C) := by
      field_simp
    linarith [this, h_rewrite]
  -- Hence C * (log(n+1))^2 < (n+1) / 4.
  have hCsq : C * (Real.log ((n : ℝ) + 1))^2 < ((n : ℝ) + 1) / 4 := by
    have h_mul := (mul_lt_mul_of_pos_left hsq_bound hC)
    -- C * ((n+1)/(4C)) = (n+1) / 4.
    have h_eq : C * (((n : ℝ) + 1) / (4 * C)) = ((n : ℝ) + 1) / 4 := by
      field_simp
    linarith
  -- Finally: (n+1)/4 + 1 ≤ n iff n ≥ 5/3, but our n ≥ 4 gives a more comfortable margin:
  -- (n+1)/4 + 1 = (n+5)/4. We want (n+5)/4 ≤ n, i.e., n+5 ≤ 4n, i.e., n ≥ 5/3.
  -- Since n ≥ 4, we have n ≥ 2, so 3n ≥ 5.
  have hn_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have h_final : ((n : ℝ) + 1) / 4 + 1 ≤ (n : ℝ) := by linarith
  linarith

/-- For any `C > 0` and constant `D`, there exists `N` such that `C * (log(n+1))² + D ≤ n`
for all `n ≥ N`. -/
lemma exists_N_log_sq_plus_const_le_n (C D : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (Real.log ((n : ℝ) + 1))^2 + D ≤ (n : ℝ) := by
  -- Use exists_N_log_sq_le_n with `2C`, then absorb D via N ≥ 2|D|.
  obtain ⟨N₁, hN₁⟩ := exists_N_log_sq_le_n (2 * C) (by linarith)
  set N : ℕ := max N₁ (Nat.ceil (2 * D + 2))
  refine ⟨N, fun n hn => ?_⟩
  have hN₁_le : N₁ ≤ n := (le_max_left _ _).trans hn
  have h2D_le : (Nat.ceil (2 * D + 2) : ℕ) ≤ n := (le_max_right _ _).trans hn
  have h2D_real : 2 * D + 2 ≤ (n : ℝ) := by
    have h_le : (2 * D + 2 : ℝ) ≤ (Nat.ceil (2 * D + 2 : ℝ) : ℝ) := Nat.le_ceil _
    have h_nat_le : ((Nat.ceil (2 * D + 2 : ℝ) : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h2D_le
    linarith
  -- From hN₁: 2C(log(n+1))² + 1 ≤ n, so C(log(n+1))² ≤ (n - 1)/2.
  have h_log_sq := hN₁ n hN₁_le
  have hC_log_sq_le : C * (Real.log ((n : ℝ) + 1))^2 ≤ ((n : ℝ) - 1) / 2 := by
    have h1 : 2 * C * (Real.log ((n : ℝ) + 1))^2 ≤ (n : ℝ) - 1 := by linarith
    linarith
  -- D ≤ (n - 2)/2 from `2 * D + 2 ≤ n`, i.e., `D ≤ (n - 2)/2`.
  have hD_le : D ≤ ((n : ℝ) - 2) / 2 := by linarith
  linarith

end InformationTheory.Shannon.ChannelCoding
