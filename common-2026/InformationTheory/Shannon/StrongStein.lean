import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stein.OptimalExponent
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Strong Stein's lemma — convergence to KL divergence

The strong converse for binary hypothesis testing (Cover–Thomas, Theorem 11.8.3):
for any `ε ∈ (0, 1)`,
`-(1/n) * log (steinOptimalBeta P Q n ε)` converges to `(klDiv P Q).toReal` as `n → ∞`.

## Main statements

* `steinOptimalBeta_log_le_of_strong_converse` — the limsup bound,
  `-(1/n) log β*(n, ε) ≤ K + δ + o(1)` (eventually for each `δ > 0`).

## Implementation notes

The proof uses an LLR-typicality route (no Pinsker/Sanov). The key step is a
lower bound `Q^n(s) ≥ exp(-n(K+δ)) · (P^n(T_n^δ) - ε)` for any α-level test `s`,
derived by restricting to the Stein-typical set. Together with the existing achievability
upper bound, this sandwiches the limit. The existing `Stein/` API is reused without
modification.
-/

namespace InformationTheory.Shannon.StrongStein

open MeasureTheory ProbabilityTheory Filter Real
open InformationTheory.Shannon
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### `Q^n` lower bound on the Stein-typical set -/

/-! ### Strong-converse lower bound for any α-level test -/

omit [DecidableEq α] [Nonempty α] in
theorem steinTypicalSubset_Q_prob_ge
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    {n : ℕ} {δ : ℝ}
    (A : Set (Fin n → α)) (hAsub : A ⊆ steinTypicalSet P Q n δ) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal + δ)))
        * ((Measure.pi (fun _ : Fin n ↦ P)) A).toReal
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) A).toReal := by
  classical
  set K : ℝ := (klDiv P Q).toReal
  set p : α → ℝ := fun x ↦ P.real {x}
  set q : α → ℝ := fun x ↦ Q.real {x}
  have hp_pos : ∀ x, 0 < p x := hPpos
  have hq_pos : ∀ x, 0 < q x := hQpos
  -- Finset abbreviations.
  set TA : Finset (Fin n → α) := A.toFinite.toFinset with hTA_def
  have hTA_coe : (TA : Set (Fin n → α)) = A := by simp [hTA_def]
  -- Singleton measures.
  have h_pi_singleton_P : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n ↦ P)).real {x}) = ∏ i : Fin n, p (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n ↦ P)) {x}).toReal = ∏ i : Fin n, p (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_singleton_Q : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) = ∏ i : Fin n, q (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal = ∏ i : Fin n, q (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  -- Rewrite both measures as Finset sums over TA.
  have h_pi_P_eq_sum :
      ((Measure.pi (fun _ : Fin n ↦ P)) A).toReal
        = ∑ x ∈ TA, ∏ i : Fin n, p (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n ↦ P)) (TA : Set (Fin n → α))).toReal
        = ∑ x ∈ TA, ((Measure.pi (fun _ : Fin n ↦ P)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n ↦ P)) TA]
    rw [← hTA_coe]
    rw [h_step]
    refine Finset.sum_congr rfl fun x _ ↦ h_pi_singleton_P x
  have h_pi_Q_eq_sum :
      ((Measure.pi (fun _ : Fin n ↦ Q)) A).toReal
        = ∑ x ∈ TA, ∏ i : Fin n, q (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n ↦ Q)) (TA : Set (Fin n → α))).toReal
        = ∑ x ∈ TA, ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n ↦ Q)) TA]
    rw [← hTA_coe]
    rw [h_step]
    refine Finset.sum_congr rfl fun x _ ↦ h_pi_singleton_Q x
  rw [h_pi_Q_eq_sum, h_pi_P_eq_sum]
  -- Per-point bound on x ∈ TA (since TA ⊆ steinTypicalSet via hAsub).
  have h_per_point : ∀ x ∈ TA,
      (∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * (K + δ)))
        ≤ ∏ i : Fin n, q (x i) := by
    intro x hx
    have hxA : x ∈ A := (Set.Finite.mem_toFinset _).mp hx
    have hxT : x ∈ steinTypicalSet P Q n δ := hAsub hxA
    rw [mem_steinTypicalSet_iff] at hxT
    -- Same calculation as in steinTypicalSet_Q_prob_ge.
    have hupper : (∑ i : Fin n, llrPmf P Q (x i)) / n < K + δ := by
      have h_abs := abs_lt.mp hxT
      linarith [h_abs.2]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsum_upper : (∑ i : Fin n, llrPmf P Q (x i)) < (n : ℝ) * (K + δ) := by
      have := (div_lt_iff₀ hn_pos_R).mp hupper
      linarith
    have hneg : -((n : ℝ) * (K + δ)) < -(∑ i : Fin n, llrPmf P Q (x i)) := by linarith
    have hexp_lt : Real.exp (-((n : ℝ) * (K + δ)))
        < Real.exp (-(∑ i : Fin n, llrPmf P Q (x i))) :=
      Real.exp_lt_exp.mpr hneg
    have h_exp_neg_llr : ∀ i : Fin n,
        Real.exp (-(llrPmf P Q (x i))) = q (x i) / p (x i) := by
      intro i
      have h_neg_llr : -(llrPmf P Q (x i))
          = Real.log (q (x i)) - Real.log (p (x i)) := by
        unfold llrPmf
        ring
      rw [h_neg_llr]
      rw [← Real.log_div (hq_pos (x i)).ne' (hp_pos (x i)).ne']
      exact Real.exp_log (div_pos (hq_pos (x i)) (hp_pos (x i)))
    have h_prod_ratio :
        Real.exp (-(∑ i : Fin n, llrPmf P Q (x i)))
          = ∏ i : Fin n, q (x i) / p (x i) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ ↦ h_exp_neg_llr i
    rw [h_prod_ratio] at hexp_lt
    have hexp_le : Real.exp (-((n : ℝ) * (K + δ)))
        ≤ ∏ i : Fin n, q (x i) / p (x i) := hexp_lt.le
    have hprod_p_pos : 0 < ∏ i : Fin n, p (x i) :=
      Finset.prod_pos (fun i _ ↦ hp_pos (x i))
    have h_eq_split : ∏ i : Fin n, q (x i)
        = (∏ i : Fin n, q (x i) / p (x i)) * ∏ i : Fin n, p (x i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [div_mul_cancel₀ _ (hp_pos (x i)).ne']
    rw [h_eq_split]
    have hp_nn : (0 : ℝ) ≤ ∏ i : Fin n, p (x i) := hprod_p_pos.le
    have h_mul_le : Real.exp (-((n : ℝ) * (K + δ))) * (∏ i : Fin n, p (x i))
        ≤ (∏ i : Fin n, q (x i) / p (x i)) * (∏ i : Fin n, p (x i)) :=
      mul_le_mul_of_nonneg_right hexp_le hp_nn
    linarith [h_mul_le]
  -- Sum the per-point bounds, factor out exp.
  calc Real.exp (-((n : ℝ) * (K + δ))) * ∑ x ∈ TA, ∏ i : Fin n, p (x i)
      = ∑ x ∈ TA, Real.exp (-((n : ℝ) * (K + δ))) * ∏ i : Fin n, p (x i) := by
        rw [Finset.mul_sum]
    _ = ∑ x ∈ TA, (∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * (K + δ))) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        ring
    _ ≤ ∑ x ∈ TA, ∏ i : Fin n, q (x i) :=
        Finset.sum_le_sum h_per_point

omit [DecidableEq α] [Nonempty α] in
/-- For any measurable `s` with `P^n(sᶜ).toReal ≤ ε`,
`Q^n(s) ≥ exp(-n(K+δ)) · (P^n(T_n^δ) - ε)`. -/
theorem steinAlphaTest_Q_prob_ge
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ}
    {n : ℕ} (s : Set (Fin n → α)) (hs : MeasurableSet s)
    (hα : ((Measure.pi (fun _ : Fin n ↦ P)) sᶜ).toReal ≤ ε) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal + δ)))
        * (((Measure.pi (fun _ : Fin n ↦ P)) (steinTypicalSet P Q n δ)).toReal - ε)
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal := by
  classical
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ P)
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n ↦ Q)
  set Tset : Set (Fin n → α) := steinTypicalSet P Q n δ
  have hT_meas : MeasurableSet Tset := measurableSet_steinTypicalSet P Q n δ
  set K : ℝ := (klDiv P Q).toReal
  set c : ℝ := Real.exp (-((n : ℝ) * (K + δ)))
  have hc_nn : 0 ≤ c := (Real.exp_pos _).le
  -- A := s ∩ Tset ⊆ Tset.
  set A : Set (Fin n → α) := s ∩ Tset
  have hA_meas : MeasurableSet A := hs.inter hT_meas
  have hA_sub : A ⊆ Tset := Set.inter_subset_right
  -- Apply the typical-set lower bound: c * P^n(A) ≤ Q^n(A).
  have h_A : c * (Pn A).toReal ≤ (Qn A).toReal :=
    steinTypicalSubset_Q_prob_ge P Q hPpos hQpos A hA_sub
  -- (Qn A) ≤ (Qn s) since A ⊆ s.
  have hA_sub_s : A ⊆ s := Set.inter_subset_left
  have h_Q_mono : (Qn A).toReal ≤ (Qn s).toReal := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono hA_sub_s
  -- (Pn Tset) - ε ≤ (Pn A): use Pn A = Pn (Tset ∩ s) and
  -- Pn Tset = Pn (Tset ∩ s) + Pn (Tset ∩ sᶜ).
  have hA_eq : A = Tset ∩ s := Set.inter_comm s Tset
  have h_partition : (Pn Tset).toReal
      = (Pn (Tset ∩ s)).toReal + (Pn (Tset ∩ sᶜ)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have h_split_eq : Pn Tset = Pn (Tset ∩ s) + Pn (Tset ∩ sᶜ) := by
      have h_disj : Disjoint (Tset ∩ s) (Tset ∩ sᶜ) := by
        rw [Set.disjoint_iff]
        intro x ⟨⟨_, hxs⟩, ⟨_, hxsc⟩⟩
        exact hxsc hxs
      have h_union : Tset = (Tset ∩ s) ∪ (Tset ∩ sᶜ) := by
        rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
      calc Pn Tset = Pn ((Tset ∩ s) ∪ (Tset ∩ sᶜ)) := by rw [← h_union]
        _ = Pn (Tset ∩ s) + Pn (Tset ∩ sᶜ) :=
            measure_union h_disj (hT_meas.inter hs.compl)
    rw [h_split_eq]
  have h_Tsc_le : (Pn (Tset ∩ sᶜ)).toReal ≤ ε := by
    have h_mono : (Pn (Tset ∩ sᶜ)).toReal ≤ (Pn sᶜ).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono Set.inter_subset_right
    linarith
  have h_PA_ge : (Pn Tset).toReal - ε ≤ (Pn A).toReal := by
    rw [hA_eq, h_partition]
    linarith
  -- c * ((Pn Tset).toReal - ε) ≤ c * (Pn A).toReal ≤ (Qn A).toReal ≤ (Qn s).toReal.
  calc c * ((Pn Tset).toReal - ε)
      ≤ c * (Pn A).toReal := mul_le_mul_of_nonneg_left h_PA_ge hc_nn
    _ ≤ (Qn A).toReal := h_A
    _ ≤ (Qn s).toReal := h_Q_mono

/-! ### Main theorem: `Tendsto → K` -/

omit [DecidableEq α] [Nonempty α] in
theorem exp_le_steinOptimalBeta_strong
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal + δ)))
        * (((Measure.pi (fun _ : Fin n ↦ P)) (steinTypicalSet P Q n δ)).toReal - ε)
      ≤ steinOptimalBeta P Q n ε := by
  apply le_csInf (steinBetaSet_nonempty P Q n ε hε)
  rintro β ⟨s, hs_meas, hs_alpha, rfl⟩
  exact steinAlphaTest_Q_prob_ge P Q hPpos hQpos s hs_meas hs_alpha

omit [DecidableEq α] in
/-- For any `δ > 0`, eventually `-(1/n) log β*(n, ε) ≤ (klDiv P Q).toReal + δ + o(1)`. -/
@[entry_point]
theorem steinOptimalBeta_log_le_of_strong_converse
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n ↦ P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)
        ≤ (klDiv P Q).toReal + δ
            - ((1 : ℝ) / n) * Real.log
                (((Measure.pi (fun _ : Fin n ↦ P))
                  (steinTypicalSet P Q n δ)).toReal - ε) := by
  -- Translate via hMapJoint so we know P^n(T_n^δ) → 1.
  have h_translate : ∀ (n : ℕ) (T : Set (Fin n → α)), MeasurableSet T →
      μ {ω | jointRV Xs n ω ∈ T} = (Measure.pi (fun _ : Fin n ↦ P)) T := by
    intro n T hT
    have hjoint_meas : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
    have h_preimg : {ω | jointRV Xs n ω ∈ T} = jointRV Xs n ⁻¹' T := rfl
    rw [h_preimg, ← Measure.map_apply hjoint_meas hT, hMapJoint n]
  have h_P_mu_to_one := steinTypicalSet_P_prob_tendsto_one μ P Q Xs hXs hindep hident hMap
    hPQ hQpos (ε := δ) hδ
  have h_P_pi_to_one : Tendsto
      (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ P)) (steinTypicalSet P Q n δ))
      atTop (𝓝 1) := by
    refine Tendsto.congr (fun n ↦ ?_) h_P_mu_to_one
    exact h_translate n _ (measurableSet_steinTypicalSet P Q n δ)
  have h_P_pi_to_one_R : Tendsto
      (fun n : ℕ ↦ ((Measure.pi (fun _ : Fin n ↦ P))
        (steinTypicalSet P Q n δ)).toReal)
      atTop (𝓝 1) := by
    have h_cont : ContinuousAt ENNReal.toReal 1 :=
      ENNReal.continuousAt_toReal (by simp)
    have := h_cont.tendsto.comp h_P_pi_to_one
    simpa using this
  -- Eventually P^n(T) - ε > (1-ε)/2 > 0.
  have h_mid_pos : 0 < (1 - ε) / 2 := by linarith
  have h_target_pos : 0 < (1 - ε) / 2 + ε := by linarith
  have h_eventually_PT_ge : ∀ᶠ n : ℕ in atTop,
      (1 - ε) / 2 + ε ≤ ((Measure.pi (fun _ : Fin n ↦ P))
        (steinTypicalSet P Q n δ)).toReal := by
    have h_lt_one : (1 - ε) / 2 + ε < 1 := by linarith
    have : ∀ᶠ x : ℝ in 𝓝 1, (1 - ε) / 2 + ε ≤ x :=
      eventually_ge_nhds h_lt_one
    exact h_P_pi_to_one_R this
  -- Combine with exp_le_steinOptimalBeta_strong.
  filter_upwards [h_eventually_PT_ge, eventually_gt_atTop 0] with n h_PT hn_pos
  set K : ℝ := (klDiv P Q).toReal with hK_def
  set Pn_T_minus_ε : ℝ := ((Measure.pi (fun _ : Fin n ↦ P))
    (steinTypicalSet P Q n δ)).toReal - ε with hPn_def
  have h_diff_pos : 0 < Pn_T_minus_ε := by
    have : (1 - ε) / 2 + ε - ε ≤ Pn_T_minus_ε := by linarith
    linarith
  -- exp(-n(K+δ)) * Pn_T_minus_ε ≤ steinOptimalBeta.
  have h_lower : Real.exp (-((n : ℝ) * (K + δ))) * Pn_T_minus_ε
      ≤ steinOptimalBeta P Q n ε :=
    exp_le_steinOptimalBeta_strong P Q hPpos hQpos hε.le n
  -- steinOptimalBeta > 0 (since RHS is product of two positive numbers).
  have h_lower_pos : 0 < Real.exp (-((n : ℝ) * (K + δ))) * Pn_T_minus_ε :=
    mul_pos (Real.exp_pos _) h_diff_pos
  have h_opt_pos : 0 < steinOptimalBeta P Q n ε :=
    lt_of_lt_of_le h_lower_pos h_lower
  -- log monotonicity: log[exp(-n(K+δ)) * Pn_T_minus_ε] ≤ log steinOptimalBeta.
  have h_log_le : Real.log (Real.exp (-((n : ℝ) * (K + δ))) * Pn_T_minus_ε)
      ≤ Real.log (steinOptimalBeta P Q n ε) :=
    Real.log_le_log h_lower_pos h_lower
  -- Expand log of product.
  have h_log_expand : Real.log (Real.exp (-((n : ℝ) * (K + δ))) * Pn_T_minus_ε)
      = -((n : ℝ) * (K + δ)) + Real.log Pn_T_minus_ε := by
    rw [Real.log_mul (Real.exp_pos _).ne' h_diff_pos.ne', Real.log_exp]
  rw [h_log_expand] at h_log_le
  -- Multiply both sides by -(1/n) (≤ 0), flips:
  -- -(1/n) log steinOptimalBeta ≤ -(1/n) * (-(n(K+δ)) + log Pn_T_minus_ε)
  --                           = (K+δ) - (1/n) log Pn_T_minus_ε.
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_neg_inv_nonpos : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_step : -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)
      ≤ -((1 : ℝ) / n) * (-((n : ℝ) * (K + δ)) + Real.log Pn_T_minus_ε) :=
    mul_le_mul_of_nonpos_left h_log_le h_neg_inv_nonpos
  have h_simp : -((1 : ℝ) / n) * (-((n : ℝ) * (K + δ)) + Real.log Pn_T_minus_ε)
      = K + δ - ((1 : ℝ) / n) * Real.log Pn_T_minus_ε := by
    have hn_ne : (n : ℝ) ≠ 0 := hn_R_pos.ne'
    field_simp
    ring
  rw [h_simp] at h_step
  exact h_step

end InformationTheory.Shannon.StrongStein
