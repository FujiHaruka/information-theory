import InformationTheory.Draft.Shannon.RateDistortionAchievabilityPhaseE
import InformationTheory.Draft.Shannon.RateDistortionAchievabilityPhaseEDischarge
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ConditionalMethodOfTypes
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseC
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseD
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseEStrong

/-!
# Rate-distortion achievability (strong-typicality variant) — supporting layer

The per-source match-probability and encoder-failure bounds, the
generic-encoder distortion decomposition, the strong lossy-code bundle, the
witness-form and partial-discharge wrappers, `codebookAvgFailureStrong`, and the
`rdAmbient` entropy / block-law bridges.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter Real
open InformationTheory.Shannon.ChannelCoding
  (jointSequence jointSequence_apply measurable_jointSequence jointlyTypicalSet
   measurableSet_jointlyTypicalSet Codebook codebookMeasure
   iidXs iidYs measurable_iidXs measurable_iidYs
   pmfToMeasure pmfToMeasure_isProbabilityMeasure pmfToMeasure_real_singleton)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ## Step A — Per-source-typical match probability lower bound -/

/-- **Step A**: repackage `conditionalStronglyTypicalSlice_mass_ge` for the
random-coding chain. For `x` X-strongly-typical (eventually in `n`), the
probability under the Y-product measure that a random `y` lands in the joint
strong slice at `x` is bounded below by `exp(-n · (H(X) + H(Y) - H(Z) + slack))`. -/
theorem per_source_typical_match_prob_strong_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep_Z_pair : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hident_Z : ∀ i, IdentDistrib (jointSequence Xs Ys i)
                                  (jointSequence Xs Ys 0) μ μ)
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hposX : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    (hposY : ∀ b : β, 0 < (μ.map (Ys 0)).real {b})
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε ε_X δ : ℝ}
    (hε : 0 < ε) (hε_X : 0 ≤ ε_X) (hε_X_lt_ε : ε_X < ε) (hδ : 0 < δ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β, qZ_min ≤ (μ.map (jointSequence Xs Ys 0)).real {p})
    (hδ_dominates_kl :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (x : Fin n → α),
      x ∈ stronglyTypicalSet μ Xs n ε_X →
      Real.exp (-(n : ℝ) *
          (entropy μ (Xs 0) + entropy μ (Ys 0)
            - entropy μ (jointSequence Xs Ys 0)
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs μ Ys
               + ε_X * logSumAbs μ Xs
               + ε_X * logSumAbs μ (jointSequence Xs Ys)
               + δ)))
        ≤ (Measure.pi (fun _ : Fin n => μ.map (Ys 0))).real
              {y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε} := by
  -- This is exactly `conditionalStronglyTypicalSlice_mass_ge`; the conditional slice
  -- unfolds to `{y | (x, y) ∈ jointStronglyTypicalSet ...}`.
  exact conditionalStronglyTypicalSlice_mass_ge μ Xs Ys hXs hYs
    hindep_Z_pair hident_Z hposZ hposX hposY hmarg_X hmarg_Y
    hε hε_X hε_X_lt_ε hδ qZ_min hqZ_min_pos hqZ_min_le hδ_dominates_kl

/-! ## Step B — Encoder failure probability bound (strong version) -/

/-- **Step B**: For `x ∈ stronglyTypicalSet μ Xs n ε_X` (eventually in `n`),
the codebook-averaged probability that *no* codeword is jointly-strongly-typical
with `x` is bounded by `exp(-M · exp(-n(H(X)+H(Y)-H(Z)+slack)))`. Strong analogue
of `encoder_failure_prob_le_exp_neg_M_avg`. -/
theorem encoder_strong_failure_prob_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep_Z_pair : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hident_Z : ∀ i, IdentDistrib (jointSequence Xs Ys i)
                                  (jointSequence Xs Ys 0) μ μ)
    (hposZ : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (hposX : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    (hposY : ∀ b : β, 0 < (μ.map (Ys 0)).real {b})
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {ε ε_X δ : ℝ}
    (hε : 0 < ε) (hε_X : 0 ≤ ε_X) (hε_X_lt_ε : ε_X < ε) (hδ : 0 < δ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β, qZ_min ≤ (μ.map (jointSequence Xs Ys 0)).real {p})
    (hδ_dominates_kl :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ) (x : Fin n → α),
      x ∈ stronglyTypicalSet μ Xs n ε_X →
    (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ.map (Ys 0)))).real
      { c : Fin M → (Fin n → β) |
          ∀ m, (x, c m) ∉ jointStronglyTypicalSet μ Xs Ys n ε }
      ≤ Real.exp (-(M : ℝ) *
            Real.exp (-(n : ℝ) *
              (entropy μ (Xs 0) + entropy μ (Ys 0)
                - entropy μ (jointSequence Xs Ys 0)
                + ((Fintype.card α : ℝ) * ε_X * logSumAbs μ Ys
                   + ε_X * logSumAbs μ Xs
                   + ε_X * logSumAbs μ (jointSequence Xs Ys)
                   + δ)))) := by
  -- Step A + product-measure factorization + `one_sub_pow_le_exp_neg_mul`.
  obtain ⟨N, hN⟩ := per_source_typical_match_prob_strong_ge μ Xs Ys hXs hYs
    hindep_Z_pair hident_Z hposZ hposX hposY hmarg_X hmarg_Y
    hε hε_X hε_X_lt_ε hδ qZ_min hqZ_min_pos hqZ_min_le hδ_dominates_kl
  refine ⟨N, fun n hn M x hx => ?_⟩
  have h_lower := hN n hn x hx
  -- Abbreviate.
  set p : Measure (Fin n → β) := Measure.pi (fun _ : Fin n => μ.map (Ys 0)) with hp_def
  haveI : IsProbabilityMeasure (μ.map (Ys 0)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map (hYs 0).aemeasurable
  haveI : IsProbabilityMeasure p := by rw [hp_def]; infer_instance
  -- Define the "no strong match" event.
  set Smiss : Set (Fin M → (Fin n → β)) :=
    { c | ∀ m, (x, c m) ∉ jointStronglyTypicalSet μ Xs Ys n ε } with hSmiss_def
  -- Factor the product measure: P_pi(Smiss) = (1 - p(slice))^M.
  set q : ℝ := p.real { y | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε } with hq_def
  have hq_nn : 0 ≤ q := measureReal_nonneg
  have hq_le : q ≤ 1 := measureReal_le_one
  -- Equation: (Measure.pi (fun _ => p)).real Smiss = (1 - q)^M.
  have h_set_eq : Smiss = Set.univ.pi
      (fun _ : Fin M => {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε}) := by
    ext c
    simp [hSmiss_def, Set.mem_pi]
  have h_per_missing :
      p.real {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε} = 1 - q := by
    have h_compl :
        {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε}
          = ({y : Fin n → β | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε})ᶜ := by
      ext y; simp
    have h_meas_typ :
        MeasurableSet {y : Fin n → β | (x, y) ∈ jointStronglyTypicalSet μ Xs Ys n ε} :=
      (Set.toFinite _).measurableSet
    rw [h_compl, probReal_compl_eq_one_sub h_meas_typ]
  have h_meas_compl :
      MeasurableSet {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε} :=
    (Set.toFinite _).measurableSet
  have h_pi :
      (Measure.pi (fun _ : Fin M => p))
          (Set.univ.pi
            (fun _ : Fin M => {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε}))
        = ∏ _m : Fin M,
            p {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε} :=
    Measure.pi_pi _ _
  have h_real :
      (Measure.pi (fun _ : Fin M => p)).real Smiss = (1 - q) ^ M := by
    show ((Measure.pi (fun _ : Fin M => p)) Smiss).toReal = _
    rw [h_set_eq, h_pi, ENNReal.toReal_prod]
    have h_pt :
        (p {y : Fin n → β | (x, y) ∉ jointStronglyTypicalSet μ Xs Ys n ε}).toReal = 1 - q := by
      show p.real _ = 1 - q
      exact h_per_missing
    simp_rw [h_pt]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h_real]
  -- Now: (1 - q)^M ≤ exp(-M · q) ≤ exp(-M · lower_bound).
  set target : ℝ := Real.exp (-(n : ℝ) *
          (entropy μ (Xs 0) + entropy μ (Ys 0)
            - entropy μ (jointSequence Xs Ys 0)
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs μ Ys
               + ε_X * logSumAbs μ Xs
               + ε_X * logSumAbs μ (jointSequence Xs Ys)
               + δ)))
    with htarget_def
  have htarget_pos : 0 < target := Real.exp_pos _
  have h_lower_target : target ≤ q := h_lower
  -- (1 - q)^M ≤ exp(-M · q)
  have h_one_sub_pow : (1 - q) ^ M ≤ Real.exp (-(M : ℝ) * q) :=
    one_sub_pow_le_exp_neg_mul M hq_nn hq_le
  -- exp(-M · q) ≤ exp(-M · target) because q ≥ target and (-M) ≤ 0.
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have h_exp_mono : Real.exp (-(M : ℝ) * q) ≤ Real.exp (-(M : ℝ) * target) := by
    refine Real.exp_le_exp.mpr ?_
    have h_neg_M : -(M : ℝ) ≤ 0 := by linarith
    nlinarith [h_lower_target]
  exact le_trans h_one_sub_pow h_exp_mono

/-! ## Generic-encoder distortion decomposition -/

omit [DecidableEq α] [DecidableEq β] in
/-- Generic-encoder distortion decomposition, the analogue of
`source_avg_distortion_le_simpler` with the joint-typical encoder replaced by an
arbitrary encoder function. -/
theorem source_avg_distortion_le_simpler_generic
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) {M n : ℕ} (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (c : Codebook M n β)
    (enc : (Fin n → α) → Fin M)
    (P_X : Measure (Fin n → α)) [IsProbabilityMeasure P_X] :
    ∫ x, blockDistortion d n x (c (enc x)) ∂P_X
      ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ)
        + distortionMax d *
          P_X.real
            { x | (x, c (enc x))
                    ∉ distortionTypicalSet μ Xs Ys d n ε δ } := by
  classical
  set Edδ : ℝ := expectedJointDistortion μ (Xs 0) (Ys 0) d + δ with hEdδ_def
  set dMax : ℝ := distortionMax d with hdMax_def
  set B : Set (Fin n → α) :=
      { x | (x, c (enc x)) ∉ distortionTypicalSet μ Xs Ys d n ε δ } with hB_def
  have h_Ed_nn : 0 ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d :=
    expectedJointDistortion_nonneg μ (Xs 0) (Ys 0) d
  have h_Edδ_nn : 0 ≤ Edδ := by rw [hEdδ_def]; linarith
  have h_dMax_nn : 0 ≤ dMax := distortionMax_nonneg d
  have h_B_meas : MeasurableSet B := (Set.toFinite _).measurableSet
  have h_pointwise : ∀ x : Fin n → α,
      blockDistortion d n x (c (enc x))
        ≤ Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x) := by
    intro x
    by_cases hxB : x ∈ B
    · have h_bd :
          blockDistortion d n x (c (enc x)) ≤ dMax :=
        blockDistortion_le_distortionMax d n x _
      have h_ind : B.indicator (fun _ : Fin n → α => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem hxB _
      calc blockDistortion d n x (c (enc x))
          ≤ dMax := h_bd
        _ = 0 + dMax * 1 := by ring
        _ ≤ Edδ + dMax * 1 := by linarith
        _ = Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x) := by rw [h_ind]
    · have hxB' : (x, c (enc x)) ∈ distortionTypicalSet μ Xs Ys d n ε δ := by
        rw [hB_def, Set.mem_setOf_eq, not_not] at hxB
        exact hxB
      have h_bd :
          blockDistortion d n x (c (enc x)) ≤ Edδ :=
        blockDistortion_le_of_mem_distortionTypicalSet μ Xs Ys d n ε δ hxB'
      have h_ind : B.indicator (fun _ : Fin n → α => (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem hxB _
      calc blockDistortion d n x (c (enc x))
          ≤ Edδ := h_bd
        _ = Edδ + dMax * 0 := by ring
        _ = Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x) := by rw [h_ind]
  have h_meas_f : Measurable (fun x : Fin n → α =>
        blockDistortion d n x (c (enc x))) := measurable_of_finite _
  have h_meas_g : Measurable (fun x : Fin n → α =>
        Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x)) := measurable_of_finite _
  have h_f_le : ∀ x, ‖blockDistortion d n x (c (enc x))‖ ≤ dMax := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (blockDistortion_nonneg d n x _)]
    exact blockDistortion_le_distortionMax d n x _
  have h_int_f : Integrable (fun x : Fin n → α =>
        blockDistortion d n x (c (enc x))) P_X := by
    refine Integrable.mono' (g := fun _ => dMax) (integrable_const dMax)
      h_meas_f.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall h_f_le
  have h_int_g : Integrable (fun x : Fin n → α =>
        Edδ + dMax * (B.indicator (fun _ => (1 : ℝ)) x)) P_X := by
    refine Integrable.mono' (g := fun _ => Edδ + dMax) (integrable_const (Edδ + dMax))
      h_meas_g.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_ind_le : (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ 1 := by
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB]
      · rw [Set.indicator_of_notMem hxB]; linarith
    have h_ind_nn : 0 ≤ (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have h_val_le : Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x)
        ≤ Edδ + dMax := by
      have h_inner : dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ dMax := by
        calc dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x)
            ≤ dMax * 1 := mul_le_mul_of_nonneg_left h_ind_le h_dMax_nn
          _ = dMax := by ring
      linarith
    have h_val_nn : 0 ≤ Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
      add_nonneg h_Edδ_nn (mul_nonneg h_dMax_nn h_ind_nn)
    rw [Real.norm_eq_abs, abs_of_nonneg h_val_nn]
    exact h_val_le
  have h_int_mono :
      ∫ x, blockDistortion d n x (c (enc x)) ∂P_X
        ≤ ∫ x, Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ∂P_X :=
    integral_mono h_int_f h_int_g h_pointwise
  have h_int_const : ∫ _x : Fin n → α, Edδ ∂P_X = Edδ := by
    rw [integral_const]; simp
  have h_int_indicator_const :
      ∫ x : Fin n → α, dMax * (B.indicator (fun _ => (1 : ℝ)) x) ∂P_X
        = dMax * P_X.real B := by
    have h_ind_eq :
        (fun x : Fin n → α => dMax * (B.indicator (fun _ => (1 : ℝ)) x))
          = B.indicator (fun _ : Fin n → α => dMax) := by
      funext x
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB]; ring
      · rw [Set.indicator_of_notMem hxB, Set.indicator_of_notMem hxB]; ring
    rw [h_ind_eq, integral_indicator_const dMax h_B_meas]
    rw [smul_eq_mul]; ring
  have h_int_split :
      ∫ x, Edδ + dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ∂P_X
        = Edδ + dMax * P_X.real B := by
    have h_const_int : Integrable (fun _ : Fin n → α => Edδ) P_X := integrable_const Edδ
    have h_ind_int : Integrable
        (fun x : Fin n → α => dMax * (B.indicator (fun _ => (1 : ℝ)) x)) P_X := by
      have h_meas' : Measurable
          (fun x : Fin n → α => dMax * (B.indicator (fun _ => (1 : ℝ)) x)) :=
        measurable_of_finite _
      refine Integrable.mono' (g := fun _ => dMax) (integrable_const dMax)
        h_meas'.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h_ind_le : (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ 1 := by
        by_cases hxB : x ∈ B
        · rw [Set.indicator_of_mem hxB]
        · rw [Set.indicator_of_notMem hxB]; linarith
      have h_ind_nn : 0 ≤ (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have h_val_nn : 0 ≤ dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) :=
        mul_nonneg h_dMax_nn h_ind_nn
      have h_val_le : dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x) ≤ dMax := by
        calc dMax * (B.indicator (fun _ : Fin n → α => (1 : ℝ)) x)
            ≤ dMax * 1 := mul_le_mul_of_nonneg_left h_ind_le h_dMax_nn
          _ = dMax := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg h_val_nn]
      exact h_val_le
    rw [integral_add h_const_int h_ind_int, h_int_const, h_int_indicator_const]
  rw [h_int_split] at h_int_mono
  exact h_int_mono

/-! ## Strong lossy-code-of-codebook bundle -/

/-- Bundle a codebook + strong-JTS lossy encoder into a `LossyCode`. Strong
analogue of `lossyCodeOfCodebook`. -/
noncomputable def lossyCodeOfCodebookStrong
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    LossyCode M n α β where
  encoder := jointStronglyTypicalLossyEncoder μ Xs Ys hM ε c
  decoder := c

/-! ## Witness-form rate-distortion achievability (strong-encoder variant)

The strong-encoder analogue of `rate_distortion_achievability_witness_form`,
with `jointTypicalLossyEncoder` replaced by `jointStronglyTypicalLossyEncoder`.
The argument composes the per-codebook distortion decomposition (the generic
`source_avg_distortion_le_simpler_generic`), a weighted sum, and pigeonhole. -/
theorem rate_distortion_achievability_witness_form_strong
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε')
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    [IsProbabilityMeasure (μ.map (Xs 0))]
    [IsProbabilityMeasure (μ.map (Ys 0))]
    (h_dist_eq : expectedJointDistortion μ (Xs 0) (Ys 0) d
                  = expectedDistortionPmf d qStar)
    (ε_join ε_dist : ℝ) (δ_typ : ℝ) (hδ_typ : 0 ≤ δ_typ)
    (failure_seq : ℕ → ℝ)
    (h_failure_nn : ∀ n, 0 ≤ failure_seq n)
    (h_failure_tendsto_zero : Filter.Tendsto failure_seq Filter.atTop (𝓝 0))
    (h_codebook_avg_failure : ∀ {n : ℕ} (hn : 0 < n),
        ∑ c : Codebook (Nat.ceil (Real.exp ((n : ℝ) * R))) n β,
            (codebookMeasure (μ.map (Ys 0))
                (Nat.ceil (Real.exp ((n : ℝ) * R))) n).real {c}
              * (Measure.pi (fun _ : Fin n => μ.map (Xs 0))).real
                  { x | (x, c (jointStronglyTypicalLossyEncoder μ Xs Ys
                                  (Nat.ceil_pos.mpr (Real.exp_pos _)) ε_join c x))
                          ∉ distortionTypicalSet μ Xs Ys d n ε_dist δ_typ }
          ≤ failure_seq n)
    (h_slack : expectedDistortionPmf d qStar + δ_typ ≤ D + ε' / 2) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion (μ.map (Xs 0)) d ≤ D + ε' := by
  classical
  set dMax : ℝ := distortionMax d with hdMax_def
  have h_dMax_nn : 0 ≤ dMax := distortionMax_nonneg d
  have h_dMax_p1_pos : 0 < dMax + 1 := by linarith
  set η : ℝ := ε' / (2 * (dMax + 1)) with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_failure_eventually : ∀ᶠ n in Filter.atTop, failure_seq n < η := by
    have := (Metric.tendsto_atTop.mp h_failure_tendsto_zero) η hη_pos
    obtain ⟨N, hN⟩ := this
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    have h_nn := h_failure_nn n
    rw [abs_of_nonneg h_nn] at this
    exact this
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_failure_eventually
  refine ⟨max N 1, fun n hn => ?_⟩
  have hN_le : N ≤ n := le_of_max_le_left hn
  have h_n_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_of_max_le_right hn)
  have h_failure_n_lt : failure_seq n < η := hN n hN_le
  set Mn : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R)) with hMn_def
  have hMn_pos : 0 < Mn := by
    rw [hMn_def]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  set f : Codebook Mn n β → ℝ := fun c =>
    (lossyCodeOfCodebookStrong μ Xs Ys hMn_pos ε_join c).expectedBlockDistortion
      (μ.map (Xs 0)) d with hf_def
  have h_per_codebook : ∀ c : Codebook Mn n β,
      f c ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ)
              + dMax *
                (Measure.pi (fun _ : Fin n => μ.map (Xs 0))).real
                  { x | (x, c (jointStronglyTypicalLossyEncoder μ Xs Ys hMn_pos ε_join c x))
                          ∉ distortionTypicalSet μ Xs Ys d n ε_dist δ_typ } := by
    intro c
    have h := source_avg_distortion_le_simpler_generic (μ := μ) (Xs := Xs) (Ys := Ys)
      (d := d) (ε := ε_dist) (δ := δ_typ) hδ_typ c
      (enc := jointStronglyTypicalLossyEncoder μ Xs Ys hMn_pos ε_join c)
      (P_X := Measure.pi (fun _ : Fin n => μ.map (Xs 0)))
    show (lossyCodeOfCodebookStrong μ Xs Ys hMn_pos ε_join c).expectedBlockDistortion
        (μ.map (Xs 0)) d ≤ _
    unfold LossyCode.expectedBlockDistortion lossyCodeOfCodebookStrong
    exact h
  have h_codebook_meas_isProb :
      IsProbabilityMeasure (codebookMeasure (μ.map (Ys 0)) Mn n) :=
    codebookMeasure.instIsProbabilityMeasure (μ.map (Ys 0)) Mn n
  have h_sum_one :
      ∑ c : Codebook Mn n β, (codebookMeasure (μ.map (Ys 0)) Mn n).real {c} = 1 := by
    haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
    haveI : MeasurableSingletonClass (Codebook Mn n β) := Pi.instMeasurableSingletonClass
    have h_real_univ : (codebookMeasure (μ.map (Ys 0)) Mn n).real
        ((Finset.univ : Finset (Codebook Mn n β)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]
      rfl
    have h_sum_eq :=
      sum_measureReal_singleton (μ := codebookMeasure (μ.map (Ys 0)) Mn n)
        (Finset.univ : Finset (Codebook Mn n β))
    rw [h_sum_eq, h_real_univ]
  have h_avg_bound :
      ∑ c : Codebook Mn n β, (codebookMeasure (μ.map (Ys 0)) Mn n).real {c} * f c
        ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ) + dMax * failure_seq n := by
    set Edδ : ℝ := expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ with hEdδ_def
    set fail : Codebook Mn n β → ℝ := fun c =>
      (Measure.pi (fun _ : Fin n => μ.map (Xs 0))).real
        { x | (x, c (jointStronglyTypicalLossyEncoder μ Xs Ys hMn_pos ε_join c x))
                ∉ distortionTypicalSet μ Xs Ys d n ε_dist δ_typ } with hfail_def
    set W : Codebook Mn n β → ℝ :=
      fun c => (codebookMeasure (μ.map (Ys 0)) Mn n).real {c} with hW_def
    have h_per_codebook' : ∀ c : Codebook Mn n β,
        f c ≤ Edδ + dMax * fail c := h_per_codebook
    have h_w_nn : ∀ c : Codebook Mn n β, 0 ≤ W c := fun _ => measureReal_nonneg
    have h_step1 : ∑ c, W c * f c ≤ ∑ c, W c * (Edδ + dMax * fail c) := by
      refine Finset.sum_le_sum (fun c _ => ?_)
      exact mul_le_mul_of_nonneg_left (h_per_codebook' c) (h_w_nn c)
    have h_step2 : ∑ c, W c * (Edδ + dMax * fail c)
          = Edδ + dMax * ∑ c, W c * fail c := by
      have h_distribute :
          ∑ c, W c * (Edδ + dMax * fail c)
            = (∑ c, W c * Edδ) + ∑ c, W c * (dMax * fail c) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro c _
        ring
      rw [h_distribute]
      have h_sum_Edδ : ∑ c, W c * Edδ = Edδ := by
        rw [show (∑ c, W c * Edδ) = (∑ c, W c) * Edδ from by
              rw [Finset.sum_mul]]
        rw [h_sum_one]; ring
      have h_sum_dMax_fail : ∑ c, W c * (dMax * fail c) = dMax * ∑ c, W c * fail c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro c _
        ring
      rw [h_sum_Edδ, h_sum_dMax_fail]
    have h_step3 : ∑ c, W c * fail c ≤ failure_seq n := by
      have h_app := h_codebook_avg_failure h_n_pos
      convert h_app using 0
    have h_step4 : dMax * ∑ c, W c * fail c ≤ dMax * failure_seq n :=
      mul_le_mul_of_nonneg_left h_step3 h_dMax_nn
    linarith [h_step1, h_step2.le]
  obtain ⟨c₀, hc₀_le⟩ :=
    exists_codebook_low_avg (M := Mn) (n := n) (μ.map (Ys 0)) f h_avg_bound
  refine ⟨Mn, le_refl _, lossyCodeOfCodebookStrong μ Xs Ys hMn_pos ε_join c₀, ?_⟩
  have hf_unfold : f c₀ =
      (lossyCodeOfCodebookStrong μ Xs Ys hMn_pos ε_join c₀).expectedBlockDistortion
        (μ.map (Xs 0)) d := rfl
  have h_failure_bound : dMax * failure_seq n ≤ ε' / 2 := by
    have h_failure_lt : failure_seq n < η := h_failure_n_lt
    have h_failure_le : failure_seq n ≤ η := h_failure_lt.le
    have h_dMax_le : dMax ≤ dMax + 1 := by linarith
    have h_failure_nn_n : 0 ≤ failure_seq n := h_failure_nn n
    calc dMax * failure_seq n
        ≤ (dMax + 1) * failure_seq n :=
          mul_le_mul_of_nonneg_right h_dMax_le h_failure_nn_n
      _ ≤ (dMax + 1) * η := mul_le_mul_of_nonneg_left h_failure_le h_dMax_p1_pos.le
      _ = (dMax + 1) * (ε' / (2 * (dMax + 1))) := by rw [hη_def]
      _ = ε' / 2 := by field_simp
  have h_dist_pmf_eq : expectedJointDistortion μ (Xs 0) (Ys 0) d
                        = expectedDistortionPmf d qStar := h_dist_eq
  show (lossyCodeOfCodebookStrong μ Xs Ys hMn_pos ε_join c₀).expectedBlockDistortion
      (μ.map (Xs 0)) d ≤ D + ε'
  calc (lossyCodeOfCodebookStrong μ Xs Ys hMn_pos ε_join c₀).expectedBlockDistortion
        (μ.map (Xs 0)) d
      = f c₀ := rfl
    _ ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ) + dMax * failure_seq n :=
        hc₀_le
    _ = (expectedDistortionPmf d qStar + δ_typ) + dMax * failure_seq n := by
        rw [h_dist_pmf_eq]
    _ ≤ (D + ε' / 2) + ε' / 2 :=
        add_le_add h_slack h_failure_bound
    _ = D + ε' := by ring

/-! ## Partial-discharge wrapper (strong-encoder variant) -/

/-- **Rate-distortion achievability — partial discharge form (strong-encoder variant).**
The strong-encoder analogue of `rate_distortion_achievability_partial_discharge`,
with `jointStronglyTypicalLossyEncoder` as the encoder. -/
theorem rate_distortion_achievability_partial_discharge_strong
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε')
    (ε_join ε_dist : ℝ) (δ_typ : ℝ) (hδ_typ : 0 ≤ δ_typ)
    (failure_seq : ℕ → ℝ)
    (h_failure_nn : ∀ n, 0 ≤ failure_seq n)
    (h_failure_tendsto_zero : Filter.Tendsto failure_seq Filter.atTop (𝓝 0))
    (h_codebook_avg_failure : ∀ {n : ℕ} (hn : 0 < n),
        ∑ c : Codebook (Nat.ceil (Real.exp ((n : ℝ) * R))) n β,
            (codebookMeasure
                ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0))
                  (Nat.ceil (Real.exp ((n : ℝ) * R))) n).real {c}
              * (Measure.pi (fun _ : Fin n =>
                    (rdAmbient qStar).map (iidXs (α := α) (β := β) 0))).real
                  { x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                                  iidXs iidYs
                                  (Nat.ceil_pos.mpr (Real.exp_pos _)) ε_join c x))
                          ∉ distortionTypicalSet (rdAmbient qStar) iidXs iidYs
                              d n ε_dist δ_typ }
          ≤ failure_seq n)
    (h_slack : expectedDistortionPmf d qStar + δ_typ ≤ D + ε' / 2) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion
            ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) d ≤ D + ε' := by
  have hqStar_simp : qStar ∈ stdSimplex ℝ (α × β) := hqStar_mem.1
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hqStar_simp
  haveI : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hqStar_simp
  haveI : IsProbabilityMeasure
      ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) :=
    rdAmbient_iidXs_isProbabilityMeasure qStar hqStar_simp
  haveI : IsProbabilityMeasure
      ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0)) :=
    rdAmbient_iidYs_isProbabilityMeasure qStar hqStar_simp
  have h_dist_eq :
      expectedJointDistortion (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
          (iidYs (α := α) (β := β) 0) d
        = expectedDistortionPmf d qStar :=
    expectedJointDistortion_rdAmbient qStar hqStar_simp d
  exact rate_distortion_achievability_witness_form_strong
    (P_X_pmf := P_X_pmf) (d := d) (D := D)
    (qStar := qStar) hqStar_mem (R := R) hI_lt_R (ε' := ε') hε'
    (μ := rdAmbient qStar) (Xs := iidXs) (Ys := iidYs)
    (hXs := measurable_iidXs) (hYs := measurable_iidYs)
    (h_dist_eq := h_dist_eq)
    (ε_join := ε_join) (ε_dist := ε_dist) (δ_typ := δ_typ) hδ_typ
    (failure_seq := failure_seq) h_failure_nn h_failure_tendsto_zero
    (h_codebook_avg_failure := h_codebook_avg_failure)
    (h_slack := h_slack)

/-! ## Codebook-averaged source-failure sequence (strong-encoder variant) -/

/-- The codebook-averaged source-failure probability for the **strong** lossy
encoder, at the canonical codebook size `M_n := ⌈exp(n·R)⌉`.

The encoder uses the inner slack `ε_join` for `jointStronglyTypicalSet`; the
failure event tests against `distortionTypicalSet` with outer slack
`ε_dist ≥ widening(ε_join)`. -/
noncomputable def codebookAvgFailureStrong
    (qStar : α × β → ℝ) (d : DistortionFn α β)
    (R : ℝ) (n : ℕ) (ε_join ε_dist δ_typ : ℝ) : ℝ :=
  ∑ c : Codebook (Nat.ceil (Real.exp ((n : ℝ) * R))) n β,
    (codebookMeasure ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0))
        (Nat.ceil (Real.exp ((n : ℝ) * R))) n).real {c}
      * (Measure.pi (fun _ : Fin n =>
            (rdAmbient qStar).map (iidXs (α := α) (β := β) 0))).real
          { x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar) iidXs iidYs
                          (Nat.ceil_pos.mpr (Real.exp_pos _)) ε_join c x))
                  ∉ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d n
                      ε_dist δ_typ }

lemma codebookAvgFailureStrong_nonneg
    (qStar : α × β → ℝ) (d : DistortionFn α β)
    (R : ℝ) (n : ℕ) (ε_join ε_dist δ_typ : ℝ) :
    0 ≤ codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ := by
  unfold codebookAvgFailureStrong
  refine Finset.sum_nonneg fun c _ => ?_
  exact mul_nonneg measureReal_nonneg measureReal_nonneg

/-! ### Entropy ↔ mutualInfoPmf bridge in the `rdAmbient` setting -/

omit [DecidableEq α] [DecidableEq β] in
/-- For `μ := rdAmbient qStar`, the entropy difference
`H(X) + H(Y) − H(Z)` equals `mutualInfoPmf qStar`. -/
lemma rdAmbient_entropy_diff_eq_mutualInfoPmf
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β)) :
    entropy (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
      + entropy (rdAmbient qStar) (iidYs (α := α) (β := β) 0)
      - entropy (rdAmbient qStar)
          (jointSequence (α := α) (β := β) iidXs iidYs 0)
      = mutualInfoPmf qStar := by
  classical
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hqStar_simp
  -- Each entropy is a negMulLog sum over the marginal pmf.
  have h_HX :
      entropy (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
        = ∑ a : α, Real.negMulLog (marginalFst qStar a) := by
    unfold entropy
    rw [rdAmbient_map_iidXs qStar hqStar_simp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pmfToMeasure_map_fst_real_singleton hqStar_simp]
  have h_HY :
      entropy (rdAmbient qStar) (iidYs (α := α) (β := β) 0)
        = ∑ b : β, Real.negMulLog (marginalSnd qStar b) := by
    unfold entropy
    rw [rdAmbient_map_iidYs qStar hqStar_simp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pmfToMeasure_map_snd_real_singleton hqStar_simp]
  have h_HZ :
      entropy (rdAmbient qStar)
          (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = ∑ p : α × β, Real.negMulLog (qStar p) := by
    unfold entropy
    rw [rdAmbient_map_jointSequence qStar hqStar_simp]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact pmfToMeasure_real_singleton hqStar_simp p
  rw [h_HX, h_HY, h_HZ]
  unfold mutualInfoPmf
  ring

/-! ## Block-law identification for `rdAmbient` -/

omit [DecidableEq α] [DecidableEq β] in
/-- The X-block joint law under `rdAmbient qStar` equals the product of the
single-letter X-marginal. Mirrors the private `block_law_X_eq_pi_p` in
`ChannelCodingAchievability`, specialised to `rdAmbient`. -/
lemma rdAmbient_block_law_iidXs
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β)) (n : ℕ) :
    (rdAmbient qStar).map
        (InformationTheory.Shannon.jointRV (iidXs (α := α) (β := β)) n)
      = Measure.pi (fun _ : Fin n =>
          (rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) := by
  classical
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hqStar_simp
  haveI : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hqStar_simp
  -- Restrict the i.i.d. X-sequence to `Fin n`.
  set Xs' : Fin n → (ℕ → α × β) → α := fun i => iidXs (α := α) (β := β) i
    with hXs'_def
  have hXs'_meas : ∀ i : Fin n, AEMeasurable (Xs' i) (rdAmbient qStar) := fun i =>
    (measurable_iidXs i).aemeasurable
  have hindepX_full :
      iIndepFun (fun i : ℕ => iidXs (α := α) (β := β) i) (rdAmbient qStar) :=
    iidAmbientJoint_iIndepFun_iidXs (pmfToMeasure (α := α × β) qStar)
  have hindepX' : iIndepFun Xs' (rdAmbient qStar) :=
    hindepX_full.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
  have h_pi_form :
      (rdAmbient qStar).map (fun ω i => Xs' i ω)
        = Measure.pi (fun i => (rdAmbient qStar).map (Xs' i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map hXs'_meas).mp hindepX'
  have h_jointRV_eq : InformationTheory.Shannon.jointRV
        (iidXs (α := α) (β := β)) n = fun ω (i : Fin n) => Xs' i ω := rfl
  rw [h_jointRV_eq, h_pi_form]
  congr 1
  funext i
  show (rdAmbient qStar).map (iidXs (α := α) (β := β) i)
        = (rdAmbient qStar).map (iidXs (α := α) (β := β) 0)
  exact (iidAmbientJoint_identDistrib_iidXs
    (pmfToMeasure (α := α × β) qStar) i).map_eq

end InformationTheory.Shannon
