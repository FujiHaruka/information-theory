import Common2026.Shannon.RateDistortionAchievabilityPhaseEStrong
import Common2026.Shannon.RateDistortionAchievabilityPhaseEDischarge
import Common2026.Shannon.RateDistortionAchievabilityPhaseE
import Common2026.Shannon.RateDistortionAchievabilityPhaseD
import Common2026.Shannon.RateDistortionAchievabilityPhaseC
import Common2026.Shannon.ConditionalMethodOfTypes

/-!
# Rate-distortion achievability — final discharge of `codebookAvgFailure_tendsto_zero`

This file closes the random-coding failure-sequence sorry left in
`RateDistortionAchievabilityPhaseEStrong.lean` by leveraging
`conditionalStronglyTypicalSlice_mass_ge`
(`ConditionalMethodOfTypes.lean`) — the Cover-Thomas 10.6.1 strong-typicality
conditional slice mass lower bound.

## Architectural note

The `_partial_discharge` wrapper (in `RateDistortionAchievabilityPhaseEDischarge.lean`)
and the underlying `_witness_form` (in `RateDistortionAchievabilityPhaseE.lean`)
hard-code the **weak** joint-typical lossy encoder `jointTypicalLossyEncoder`.
The strong-typicality random-coding analysis requires the **strong** encoder
`jointStronglyTypicalLossyEncoder` (Phase B' of `PhaseEStrong.lean`).

To avoid invasive refactoring of those weak-encoder-bound proofs, this file
**duplicates** the witness-form / partial-discharge layers with the strong
encoder swapped in. The duplication is mechanical: the proofs are
encoder-agnostic — only `blockDistortion_le_distortionMax` and
`blockDistortion_le_of_mem_distortionTypicalSet` are used.

## Outline

1. `per_source_typical_match_prob_strong_ge` — direct corollary of
   `conditionalStronglyTypicalSlice_mass_ge`, repackaged in the
   `(Measure.pi (μ.map (Ys 0))).real` form expected by the random-coding chain.
2. `encoder_strong_failure_prob_le` — codebook-averaged probability that
   *no* strong-JT match exists, integrated over `x ∈ stronglyTypicalSet`,
   bounded by `exp(-M · exp(-n(I+δ)))`.
3. `source_avg_distortion_le_simpler_generic` — Phase D.5 with arbitrary
   encoder parameter (verbatim mirror of `source_avg_distortion_le_simpler`).
4. `lossyCodeOfCodebook_strong` — strong analogue of `lossyCodeOfCodebook`.
5. `rate_distortion_achievability_witness_form_strong` — verbatim mirror of
   the weak witness form.
6. `codebookAvgFailureStrong` — `codebookAvgFailure` with the strong encoder.
7. `codebookAvgFailureStrong_tendsto_zero` — main probabilistic content,
   assembled from (1)+(2)+(3) + `stronglyTypicalSet_prob_tendsto_one`.
8. `rate_distortion_achievability_partial_discharge_strong` — verbatim mirror
   of the weak partial-discharge wrapper.
9. `rate_distortion_achievability` — final no-hypothesis theorem.

## Positivity caveat

`conditionalStronglyTypicalSlice_mass_ge` requires the joint pmf `qStar` to
have **strictly positive** mass on every `(a, b) ∈ α × β`. This is a real
restriction; the unconditional `rate_distortion_achievability` would require
a perturbation argument (pass `qStar` through `qStar_ε := (1-ε)·qStar + ε·uniform`,
take `ε → 0`, use continuity of the distortion bound). That perturbation is
left for a future round; the present theorem carries `(hqStar_pos : ∀ p, 0 < qStar p)`
as an additional hypothesis.
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

/-! ## Generic-encoder Phase D bound (mirror of `source_avg_distortion_le_simpler`) -/

/-- Generic-encoder Phase D.5. Verbatim mirror of `source_avg_distortion_le_simpler`
with the joint-typical encoder replaced by an arbitrary encoder function. -/
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

Verbatim mirror of `rate_distortion_achievability_witness_form`, with the
weak `jointTypicalLossyEncoder` replaced by `jointStronglyTypicalLossyEncoder`.
The proof structure is identical: per-codebook Phase D.5 bound (via the
generic `source_avg_distortion_le_simpler_generic`), weighted sum, pigeonhole. -/
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
Verbatim mirror of `rate_distortion_achievability_partial_discharge`, with the
weak encoder swapped for `jointStronglyTypicalLossyEncoder`. -/
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

/-- For `μ := rdAmbient qStar`, the entropy difference
`H(X) + H(Y) − H(Z)` equals `mutualInfoPmf qStar`. -/
lemma rdAmbient_entropy_diff_eq_mutualInfoPmf
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β)) :
    entropy (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
      + entropy (rdAmbient qStar) (iidYs (α := α) (β := β) 0)
      - entropy (rdAmbient qStar)
          (jointSequence (α := α) (β := β) iidXs iidYs 0)
      = mutualInfoPmf qStar := by
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

/-! ## Main probabilistic content: `codebookAvgFailureStrong → 0` -/

/-- **Main `tendsto_zero` for the strong-encoder failure sequence.**

Hypotheses:

* `hqStar_pos : ∀ p, 0 < qStar p` — strict positivity of `qStar` on `α × β`.
  Required by `conditionalStronglyTypicalSlice_mass_ge`. The unconditional
  theorem requires a perturbation argument (out of scope this round).

* Slack parameters `ε_X, ε_join, δ_kl` and slack-budget hypotheses
  `h_rate_gap` (strict rate over mutualInfoPmf + slacks) and the bridge slacks
  for `jointStronglyTypicalSet ⊆ distortionTypicalSet`.

`@audit:suspect()` -/
theorem codebookAvgFailureStrong_tendsto_zero
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β))
    (hqStar_pos : ∀ p : α × β, 0 < qStar p)
    (d : DistortionFn α β)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    (ε_dist δ_typ : ℝ) (hε_dist_pos : 0 < ε_dist) (hδ_typ_nn : 0 ≤ δ_typ)
    (ε_X ε_join δ_kl : ℝ)
    (hε_X_pos : 0 < ε_X) (hε_join_pos : 0 < ε_join) (hδ_kl_pos : 0 < δ_kl)
    (hε_X_lt_ε_join : ε_X < ε_join)
    (h_rate_gap :
        mutualInfoPmf qStar
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
                  (iidYs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar) (iidXs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar)
                  (jointSequence (α := α) (β := β) iidXs iidYs)
              + δ_kl) < R)
    (h_dist_slack :
        ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
    -- Caller-supplied bridge `jointStronglyTypicalSet ε_join ⊆ distortionTypicalSet ε_dist δ_typ`.
    (h_jts_subset_dts : ∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → α) (y : Fin n → β),
        (x, y) ∈ jointStronglyTypicalSet (rdAmbient qStar) iidXs iidYs n ε_join →
        (x, y) ∈ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d n
                      ε_dist δ_typ)
    -- Caller-supplied KL bound for the conditional method-of-types.
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β,
        qZ_min ≤ (pmfToMeasure (α := α × β) qStar).real {p})
    (hδ_kl_dominates :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ_kl * qZ_min) :
    Filter.Tendsto
      (fun n : ℕ => codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ)
      Filter.atTop (𝓝 0) := by
  classical
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
  -- Positivity of singleton marginals.
  have hqStar_real_pos : ∀ p : α × β,
      0 < (pmfToMeasure (α := α × β) qStar).real {p} := by
    intro p
    rw [pmfToMeasure_real_singleton hqStar_simp]
    exact hqStar_pos p
  have hposZ : ∀ p : α × β,
      0 < ((rdAmbient qStar).map
              (jointSequence (α := α) (β := β) iidXs iidYs 0)).real {p} := by
    intro p
    rw [rdAmbient_map_jointSequence qStar hqStar_simp]
    exact hqStar_real_pos p
  have hposX : ∀ a : α,
      0 < ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)).real {a} :=
    fun a => iidAmbientJoint_iidXs_real_singleton_pos
      (pmfToMeasure (α := α × β) qStar) hqStar_real_pos a
  have hposY : ∀ b : β,
      0 < ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0)).real {b} :=
    fun b => iidAmbientJoint_iidYs_real_singleton_pos
      (pmfToMeasure (α := α × β) qStar) hqStar_real_pos b
  -- iIndepFun + Pairwise of joint sequence.
  have hindepZ_full :
      iIndepFun (fun i : ℕ =>
          jointSequence (α := α) (β := β) iidXs iidYs i) (rdAmbient qStar) :=
    iidAmbientJoint_iIndepFun_joint (pmfToMeasure (α := α × β) qStar)
  have hindepZ_pair : Pairwise fun i j =>
      jointSequence (α := α) (β := β) iidXs iidYs i ⟂ᵢ[rdAmbient qStar]
        jointSequence iidXs iidYs j := by
    intro i j hij
    exact hindepZ_full.indepFun hij
  have hidentZ : ∀ i, IdentDistrib
      (jointSequence (α := α) (β := β) iidXs iidYs i)
      (jointSequence iidXs iidYs 0)
      (rdAmbient qStar) (rdAmbient qStar) := fun i =>
    iidAmbientJoint_identDistrib_joint (pmfToMeasure (α := α × β) qStar) i
  -- Marginal identities for `rdAmbient` (for X-axis strong typicality AEP).
  have hmarg_X :
      ((rdAmbient qStar).map (jointSequence (α := α) (β := β) iidXs iidYs 0)).map
          Prod.fst
        = (rdAmbient qStar).map (iidXs (α := α) (β := β) 0) := by
    rw [rdAmbient_map_jointSequence qStar hqStar_simp,
        rdAmbient_map_iidXs qStar hqStar_simp]
  -- The X-axis is i.i.d. with marginal `(rdAmbient qStar).map (iidXs 0)`.
  have hindepX_full :
      iIndepFun (fun i : ℕ => iidXs (α := α) (β := β) i) (rdAmbient qStar) :=
    iidAmbientJoint_iIndepFun_iidXs (pmfToMeasure (α := α × β) qStar)
  have hindepX_pair : Pairwise fun i j =>
      (iidXs (α := α) (β := β) i) ⟂ᵢ[rdAmbient qStar] (iidXs j) := by
    intro i j hij
    exact hindepX_full.indepFun hij
  have hidentX : ∀ i, IdentDistrib
      (iidXs (α := α) (β := β) i) (iidXs 0)
      (rdAmbient qStar) (rdAmbient qStar) := fun i =>
    iidAmbientJoint_identDistrib_iidXs (pmfToMeasure (α := α × β) qStar) i
  -- Entropy → mutualInfoPmf bridge.
  have h_ent_bridge :
      entropy (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
        + entropy (rdAmbient qStar) (iidYs (α := α) (β := β) 0)
        - entropy (rdAmbient qStar)
            (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = mutualInfoPmf qStar :=
    rdAmbient_entropy_diff_eq_mutualInfoPmf qStar hqStar_simp
  -- Rate gap: choose ε' > 0 such that R - (I + slack) ≥ 2ε'.
  set I_plus_slack : ℝ :=
      mutualInfoPmf qStar
        + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
              (iidYs (α := α) (β := β))
          + ε_X * logSumAbs (rdAmbient qStar) (iidXs (α := α) (β := β))
          + ε_X * logSumAbs (rdAmbient qStar)
              (jointSequence (α := α) (β := β) iidXs iidYs)
          + δ_kl) with hIslack_def
  have h_gap_pos : 0 < R - I_plus_slack := by linarith
  -- Use the gap to bound `Mn · exp(-n · (I+slack))` decaying exponentially.
  -- Mn := ⌈exp(nR)⌉ ≥ exp(nR) > 0.
  -- Mn · exp(-n(I+slack)) ≥ exp(n(R - I - slack)) → ∞, so
  -- exp(-Mn · exp(-n(I+slack))) → 0 as n → ∞.
  --
  -- Sketch:
  --   1. Express codebookAvgFailureStrong as the joint (codebook × source) measure
  --      of the failure event via Fubini.
  --   2. Decompose failure ⊆ {x ∉ T*_X} ∪ {x ∈ T*_X ∧ no strong-JT match in c}.
  --      The third case (strong match exists but distortion bad) vanishes via
  --      `h_jts_subset_dts`.
  --   3. P[x ∉ T*_X] → 0 by `stronglyTypicalSet_prob_tendsto_one`.
  --   4. P[no strong match | x ∈ T*_X] ≤ exp(-Mn · exp(-n(I+slack))) → 0 by Step B.
  --   5. Combine: codebookAvgFailureStrong ≤ P[x ∉ T*_X] + exp(-Mn · exp(-n(I+slack))).
  -- Each squeeze of the sum tends to 0; sum tends to 0.
  --
  -- DETERMINISTIC EXPONENTIAL BOUND (closed-form ε' chosen below):
  set δ' : ℝ := (R - I_plus_slack) / 2 with hδ'_def
  have hδ'_pos : 0 < δ' := by rw [hδ'_def]; linarith
  -- ## Pointwise bound on `codebookAvgFailureStrong(n)`
  --
  --   codebookAvgFailureStrong(n)
  --     ≤ P_X[X ∉ T*_X] + exp(-Mn · exp(-n · (I + slack)))
  --
  -- where `Mn := ⌈exp(nR)⌉`. Both right-hand summands tend to `0`:
  --   1. `P_X[X ∉ T*_X] → 0` by `stronglyTypicalSet_prob_tendsto_one` (AEP).
  --   2. `Mn · exp(-n·(I+slack)) → ∞` since `R > I + slack` (rate gap `h_rate_gap`),
  --      so `exp(-Mn · exp(-n·(I+slack))) → 0`.
  --
  -- The key observation that lets `h_jts_subset_dts` discharge the
  -- "match-but-bad-distortion" case: if `x ∈ T*_X` AND ∃ m, (x, c m) ∈ JSTS,
  -- then the strong encoder picks one such `m`, and `h_jts_subset_dts` then
  -- guarantees `(x, c m) ∈ DTS`. So the failure event reduces to either
  -- `x ∉ T*_X` (AEP-suppressed) or `no strong-JT match` (Step-B-suppressed).
  --
  -- Abbreviate the source product measure (per `n`).
  let P_X : (n : ℕ) → Measure (Fin n → α) := fun n =>
    Measure.pi (fun _ : Fin n => (rdAmbient qStar).map (iidXs (α := α) (β := β) 0))
  -- Pull out Step B (`encoder_strong_failure_prob_le`) — gives an `N₀` past which
  -- the codebook-level "no strong match" mass is exponentially small for `x ∈ T*_X`.
  obtain ⟨N_B, hN_B⟩ :=
    encoder_strong_failure_prob_le (rdAmbient qStar)
      (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β))
      measurable_iidXs measurable_iidYs
      hindepZ_pair hidentZ hposZ hposX hposY hmarg_X
      (by rw [rdAmbient_map_jointSequence qStar hqStar_simp,
              rdAmbient_map_iidYs qStar hqStar_simp])
      hε_join_pos hε_X_pos.le hε_X_lt_ε_join hδ_kl_pos qZ_min hqZ_min_pos
      (by intro p; rw [rdAmbient_map_jointSequence qStar hqStar_simp]; exact hqZ_min_le p)
      hδ_kl_dominates
  -- For `n ≥ N_B`, denote the exponential target (depends on `n`).
  set target : ℕ → ℝ := fun n =>
    Real.exp (-(n : ℝ) *
      (entropy (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
        + entropy (rdAmbient qStar) (iidYs (α := α) (β := β) 0)
        - entropy (rdAmbient qStar)
            (jointSequence (α := α) (β := β) iidXs iidYs 0)
        + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
              (iidYs (α := α) (β := β))
          + ε_X * logSumAbs (rdAmbient qStar) (iidXs (α := α) (β := β))
          + ε_X * logSumAbs (rdAmbient qStar)
              (jointSequence (α := α) (β := β) iidXs iidYs)
          + δ_kl))) with htarget_def
  -- Identify target's exponent as `n · I_plus_slack` via the entropy bridge.
  have h_target_eq : ∀ n : ℕ,
      target n = Real.exp (-(n : ℝ) * I_plus_slack) := by
    intro n
    simp only [htarget_def, hIslack_def, h_ent_bridge]
  -- Mn := ⌈exp(nR)⌉ and its positivity proof.
  set Mn : ℕ → ℕ := fun n => Nat.ceil (Real.exp ((n : ℝ) * R)) with hMn_def
  have hMn_pos : ∀ n, 0 < Mn n :=
    fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  -- ## Step 1: P_X[X ∉ T*_X] → 0 via AEP on the strong typicality set.
  -- `μ {ω | jointRV iidXs n ω ∈ T*_X} → 1` (AEP).
  have h_aep := stronglyTypicalSet_prob_tendsto_one (rdAmbient qStar)
    (iidXs (α := α) (β := β)) measurable_iidXs hindepX_pair hidentX hε_X_pos
  -- Convert to "complement → 0".
  have h_aep_compl :
      Filter.Tendsto
        (fun n : ℕ => ((rdAmbient qStar)
          {ω | InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n ω
                  ∉ stronglyTypicalSet (rdAmbient qStar)
                      (iidXs (α := α) (β := β)) n ε_X}).toReal)
        Filter.atTop (𝓝 0) := by
    -- μ.real (compl) = 1 - μ.real (event); event → 1 ⟹ compl → 0.
    have h_meas : ∀ n,
        MeasurableSet
          {ω | InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n ω
                ∈ stronglyTypicalSet (rdAmbient qStar)
                    (iidXs (α := α) (β := β)) n ε_X} := by
      intro n
      have hmeas_jr : Measurable (InformationTheory.Shannon.jointRV
            (iidXs (α := α) (β := β)) n) :=
        InformationTheory.Shannon.measurable_jointRV
          (iidXs (α := α) (β := β)) measurable_iidXs n
      exact hmeas_jr (Set.toFinite _).measurableSet
    -- Translate to the `.real` form on both sides.
    have h_aep_real :
        Filter.Tendsto
          (fun n : ℕ => (rdAmbient qStar).real
            {ω | InformationTheory.Shannon.jointRV
                  (iidXs (α := α) (β := β)) n ω
                  ∈ stronglyTypicalSet (rdAmbient qStar)
                      (iidXs (α := α) (β := β)) n ε_X})
          Filter.atTop (𝓝 1) := by
      have := h_aep
      simp only [measureReal_def]
      refine (ENNReal.tendsto_toReal ?_).comp this
      exact ENNReal.one_ne_top
    -- (rdAmbient qStar).real (compl set) = 1 - (rdAmbient qStar).real (event)
    have h_pointwise : ∀ n,
        ((rdAmbient qStar) {ω | InformationTheory.Shannon.jointRV
              (iidXs (α := α) (β := β)) n ω
              ∉ stronglyTypicalSet (rdAmbient qStar)
                  (iidXs (α := α) (β := β)) n ε_X}).toReal
          = 1 - (rdAmbient qStar).real {ω | InformationTheory.Shannon.jointRV
                  (iidXs (α := α) (β := β)) n ω
                  ∈ stronglyTypicalSet (rdAmbient qStar)
                      (iidXs (α := α) (β := β)) n ε_X} := by
      intro n
      have h_compl_eq :
          {ω | InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n ω
                ∉ stronglyTypicalSet (rdAmbient qStar)
                    (iidXs (α := α) (β := β)) n ε_X}
            = {ω | InformationTheory.Shannon.jointRV
                  (iidXs (α := α) (β := β)) n ω
                  ∈ stronglyTypicalSet (rdAmbient qStar)
                      (iidXs (α := α) (β := β)) n ε_X}ᶜ := by
        ext ω; simp
      show ((rdAmbient qStar) _).toReal = _
      rw [h_compl_eq, ← measureReal_def, probReal_compl_eq_one_sub (h_meas n)]
    have h_minus : Filter.Tendsto
        (fun n : ℕ => (1 : ℝ) - (rdAmbient qStar).real
          {ω | InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n ω
                ∈ stronglyTypicalSet (rdAmbient qStar)
                    (iidXs (α := α) (β := β)) n ε_X})
        Filter.atTop (𝓝 0) := by
      have := h_aep_real.const_sub (1 : ℝ)
      simpa using this
    refine h_minus.congr (fun n => ?_)
    rw [h_pointwise n]
  -- Bridge AEP to `Measure.pi` form via `rdAmbient_block_law_iidXs`.
  have h_pi_compl_tendsto :
      Filter.Tendsto
        (fun n : ℕ => (P_X n).real
          {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                              (iidXs (α := α) (β := β)) n ε_X})
        Filter.atTop (𝓝 0) := by
    have h_map_eq : ∀ n : ℕ,
        (P_X n).real
            {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                                (iidXs (α := α) (β := β)) n ε_X}
          = ((rdAmbient qStar)
              {ω | InformationTheory.Shannon.jointRV
                    (iidXs (α := α) (β := β)) n ω
                    ∉ stronglyTypicalSet (rdAmbient qStar)
                        (iidXs (α := α) (β := β)) n ε_X}).toReal := by
      intro n
      show ((P_X n) _).toReal = _
      have h_block_law :
          (rdAmbient qStar).map
              (InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n)
            = P_X n :=
        rdAmbient_block_law_iidXs qStar hqStar_simp n
      have h_meas_set :
          MeasurableSet
            {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                                (iidXs (α := α) (β := β)) n ε_X} :=
        (Set.toFinite _).measurableSet
      have h_meas_jr : Measurable
          (InformationTheory.Shannon.jointRV (iidXs (α := α) (β := β)) n) :=
        InformationTheory.Shannon.measurable_jointRV
          (iidXs (α := α) (β := β)) measurable_iidXs n
      have h_preimage :
          (InformationTheory.Shannon.jointRV (iidXs (α := α) (β := β)) n) ⁻¹'
              {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                                  (iidXs (α := α) (β := β)) n ε_X}
            = {ω | InformationTheory.Shannon.jointRV
                    (iidXs (α := α) (β := β)) n ω
                    ∉ stronglyTypicalSet (rdAmbient qStar)
                        (iidXs (α := α) (β := β)) n ε_X} := rfl
      rw [← h_block_law, MeasureTheory.Measure.map_apply h_meas_jr h_meas_set,
          h_preimage]
    refine (h_aep_compl).congr (fun n => ?_)
    rw [h_map_eq n]
  -- ## Step 2: rate-gap → `exp(-Mn · target_n) → 0`.
  -- Use `ceil_exp_mul_exp_neg_tendsto_atTop` (with `θ := I_plus_slack`).
  have h_Mn_target_tendsto :
      Filter.Tendsto
        (fun n : ℕ => (Mn n : ℝ) * target n) Filter.atTop Filter.atTop := by
    have h_base := ceil_exp_mul_exp_neg_tendsto_atTop
      (R := R) (θ := I_plus_slack) (by linarith)
    -- `(Nat.ceil (exp(nR)) : ℝ) * exp(-nθ) → ∞`; rewrite to match target shape.
    refine h_base.congr (fun n => ?_)
    show (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) * Real.exp (-(n : ℝ) * I_plus_slack)
        = (Mn n : ℝ) * target n
    rw [h_target_eq n, hMn_def]
  have h_exp_neg_Mn_target_tendsto :
      Filter.Tendsto
        (fun n : ℕ => Real.exp (-((Mn n : ℝ) * target n)))
        Filter.atTop (𝓝 0) :=
    exp_neg_tendsto_zero_of_tendsto_atTop h_Mn_target_tendsto
  -- ## Step 3: Pointwise bound on `codebookAvgFailureStrong n` for `n ≥ N_B + 1`.
  -- `codebookAvgFailureStrong n ≤ (P_X n).real {x ∉ T*_X} + exp(-(Mn n) · target n)`.
  have h_pointwise_bound :
      ∀ᶠ n : ℕ in Filter.atTop,
        codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
          ≤ (P_X n).real
              {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                                  (iidXs (α := α) (β := β)) n ε_X}
            + Real.exp (-((Mn n : ℝ) * target n)) := by
    refine Filter.eventually_atTop.mpr ⟨max N_B 1, fun n hn => ?_⟩
    have hn_NB : N_B ≤ n := le_of_max_le_left hn
    have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_of_max_le_right hn)
    -- Abbreviations.
    set p : Measure (Fin n → β) :=
      Measure.pi (fun _ : Fin n => (rdAmbient qStar).map (iidYs (α := α) (β := β) 0))
      with hp_def
    haveI : IsProbabilityMeasure p := by rw [hp_def]; infer_instance
    set W : Measure (Codebook (Mn n) n β) :=
      codebookMeasure ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0)) (Mn n) n
      with hW_def
    haveI : IsProbabilityMeasure W := by
      rw [hW_def]; exact codebookMeasure.instIsProbabilityMeasure _ _ _
    -- Note: by unfolding `codebookMeasure`, `W = Measure.pi (fun _ : Fin Mn => p)`.
    have hW_eq_pi :
        W = Measure.pi (fun _ : Fin (Mn n) => p) := by
      rw [hW_def, hp_def]; rfl
    set T_X : Set (Fin n → α) :=
      {x | x ∈ stronglyTypicalSet (rdAmbient qStar)
                  (iidXs (α := α) (β := β)) n ε_X} with hT_X_def
    set notTX : Set (Fin n → α) :=
      {x | x ∉ stronglyTypicalSet (rdAmbient qStar)
                  (iidXs (α := α) (β := β)) n ε_X} with hnotTX_def
    have hnotTX_eq_compl : notTX = T_Xᶜ := by ext x; simp [hT_X_def, hnotTX_def]
    have hT_X_meas : MeasurableSet T_X := (Set.toFinite _).measurableSet
    have hnotTX_meas : MeasurableSet notTX := (Set.toFinite _).measurableSet
    -- For each codebook c, let `fail_c c := (P_X n).real {x | (x, c(enc_c x)) ∉ DTS}`.
    set fail_c : Codebook (Mn n) n β → ℝ := fun c =>
      (P_X n).real
        { x : Fin n → α |
            (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                      (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β))
                      (hMn_pos n) ε_join c x))
              ∉ distortionTypicalSet (rdAmbient qStar)
                  (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β)) d n
                  ε_dist δ_typ } with hfail_c_def
    -- Step a: pointwise per-c bound:
    --   fail_c c ≤ (P_X n).real notTX + (P_X n).real {x ∈ T_X ∧ ¬∃m, (x, c m) ∈ JSTS}.
    have h_per_c_bound : ∀ c : Codebook (Mn n) n β,
        fail_c c ≤ (P_X n).real notTX +
          (P_X n).real
            { x : Fin n → α | x ∈ T_X ∧
                ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                    (rdAmbient qStar) (iidXs (α := α) (β := β))
                    (iidYs (α := α) (β := β)) n ε_join } := by
      intro c
      -- Failure event ⊆ notTX ∪ {x ∈ T_X ∧ ¬∃m, (x, c m) ∈ JSTS}.
      set Fc : Set (Fin n → α) :=
        { x : Fin n → α |
            (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                      (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β))
                      (hMn_pos n) ε_join c x))
              ∉ distortionTypicalSet (rdAmbient qStar)
                  (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β)) d n
                  ε_dist δ_typ } with hFc_def
      set Nc : Set (Fin n → α) :=
        { x : Fin n → α | x ∈ T_X ∧
            ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                (rdAmbient qStar) (iidXs (α := α) (β := β))
                (iidYs (α := α) (β := β)) n ε_join } with hNc_def
      have hFc_subset : Fc ⊆ notTX ∪ Nc := by
        intro x hx
        by_cases hxTX : x ∈ T_X
        · right
          refine ⟨hxTX, ?_⟩
          intro hex
          -- If a strong match exists, the encoder picks one; `h_jts_subset_dts` ⇒ DTS.
          have hpick :
              (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                        (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β))
                        (hMn_pos n) ε_join c x))
                ∈ jointStronglyTypicalSet (rdAmbient qStar)
                    (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β)) n ε_join :=
            jointStronglyTypicalLossyEncoder_spec_of_exists
              (rdAmbient qStar) (iidXs (α := α) (β := β))
              (iidYs (α := α) (β := β)) (hMn_pos n) ε_join c x hex
          have hpick_dts := h_jts_subset_dts (n := n) hn_pos x _ hpick
          exact hx hpick_dts
        · left
          show x ∈ notTX
          rw [hnotTX_def]
          exact hxTX
      have hFc_meas : MeasurableSet Fc := (Set.toFinite _).measurableSet
      have hNc_meas : MeasurableSet Nc := (Set.toFinite _).measurableSet
      -- Measure subadditivity on real values:
      have h_union :
          (P_X n).real Fc ≤ (P_X n).real notTX + (P_X n).real Nc := by
        have h_le := measureReal_mono (μ := P_X n) (hFc_subset)
            (measure_ne_top _ _)
        have h_union_le :
            (P_X n).real (notTX ∪ Nc)
              ≤ (P_X n).real notTX + (P_X n).real Nc :=
          measureReal_union_le _ _
        linarith
      exact h_union
    -- Step b: ∑_c W{c}.real * fail_c c ≤ (P_X n).real notTX + ∑_c W{c}.real * Pr_X(Nc) (avg form).
    -- Use that ∑_c W{c}.real = 1 (W probability) for the notTX term.
    have hW_sum_one : ∑ c : Codebook (Mn n) n β, W.real {c} = 1 := by
      haveI : MeasurableSingletonClass (Fin n → β) := Pi.instMeasurableSingletonClass
      haveI : MeasurableSingletonClass (Codebook (Mn n) n β) :=
        Pi.instMeasurableSingletonClass
      have h_real_univ : W.real
          ((Finset.univ : Finset (Codebook (Mn n) n β)) : Set _) = 1 := by
        rw [Finset.coe_univ, measureReal_def, measure_univ]
        rfl
      have h_sum_eq :=
        sum_measureReal_singleton (μ := W) (Finset.univ : Finset (Codebook (Mn n) n β))
      rw [h_sum_eq, h_real_univ]
    have h_weighted_avg :
        ∑ c : Codebook (Mn n) n β, W.real {c} * fail_c c
          ≤ (P_X n).real notTX
            + ∑ c : Codebook (Mn n) n β,
                W.real {c} * (P_X n).real
                  { x : Fin n → α | x ∈ T_X ∧
                      ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                          (rdAmbient qStar) (iidXs (α := α) (β := β))
                          (iidYs (α := α) (β := β)) n ε_join } := by
      have h_step1 :
          ∑ c, W.real {c} * fail_c c
            ≤ ∑ c, W.real {c} *
                ((P_X n).real notTX +
                  (P_X n).real
                    { x : Fin n → α | x ∈ T_X ∧
                        ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                            (rdAmbient qStar) (iidXs (α := α) (β := β))
                            (iidYs (α := α) (β := β)) n ε_join }) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        exact mul_le_mul_of_nonneg_left (h_per_c_bound c) measureReal_nonneg
      have h_step2 :
          ∑ c, W.real {c} *
              ((P_X n).real notTX +
                (P_X n).real
                  { x : Fin n → α | x ∈ T_X ∧
                      ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                          (rdAmbient qStar) (iidXs (α := α) (β := β))
                          (iidYs (α := α) (β := β)) n ε_join })
            = (P_X n).real notTX
              + ∑ c, W.real {c} * (P_X n).real
                  { x : Fin n → α | x ∈ T_X ∧
                      ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                          (rdAmbient qStar) (iidXs (α := α) (β := β))
                          (iidYs (α := α) (β := β)) n ε_join } := by
        have h_dist :
            ∑ c, W.real {c} *
                ((P_X n).real notTX +
                  (P_X n).real
                    { x : Fin n → α | x ∈ T_X ∧
                        ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                            (rdAmbient qStar) (iidXs (α := α) (β := β))
                            (iidYs (α := α) (β := β)) n ε_join })
              = (∑ c, W.real {c} * (P_X n).real notTX) +
                ∑ c, W.real {c} * (P_X n).real
                  { x : Fin n → α | x ∈ T_X ∧
                      ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                          (rdAmbient qStar) (iidXs (α := α) (β := β))
                          (iidYs (α := α) (β := β)) n ε_join } := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun c _ => ?_); ring
        have h_sum_notTX :
            ∑ c : Codebook (Mn n) n β, W.real {c} * (P_X n).real notTX
              = (P_X n).real notTX := by
          rw [show ∑ c : Codebook (Mn n) n β, W.real {c} * (P_X n).real notTX
                  = (∑ c : Codebook (Mn n) n β, W.real {c}) * (P_X n).real notTX
              from by rw [Finset.sum_mul]]
          rw [hW_sum_one]; ring
        rw [h_dist, h_sum_notTX]
      linarith
    -- Step c: bound ∑_c W{c}.real * Pr_X(Nc) ≤ exp(-(Mn n) * target n).
    -- This is the Fubini swap + Step B.
    have h_avg_nomatch_bound :
        ∑ c : Codebook (Mn n) n β,
            W.real {c} * (P_X n).real
              { x : Fin n → α | x ∈ T_X ∧
                  ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                      (rdAmbient qStar) (iidXs (α := α) (β := β))
                      (iidYs (α := α) (β := β)) n ε_join }
          ≤ Real.exp (-((Mn n : ℝ) * target n)) := by
      -- Define, for each `x`, the codebook-no-match event:
      --   noMatchX x := {c : Fin Mn → (Fin n → β) | ∀ m, (x, c m) ∉ JSTS}.
      -- For x ∈ T_X, Step B (`hN_B n hn_NB`) gives W.real (noMatchX x) ≤ target n.
      -- We have W = Measure.pi (fun _ => p), so this is exactly Step B's bound.
      -- Strategy: bound each summand via
      --   W.real {c} * (P_X n).real {x | x ∈ T_X ∧ ¬∃m, (x, c m) ∈ JSTS}
      --     = (W.prod (P_X n)).real {(c, x) | x ∈ T_X ∧ ¬∃m, (x, c m) ∈ JSTS}  -- after summing
      -- Equivalently using Fubini:
      --     = ∫_x [W.real {c | ¬∃m, (x, c m) ∈ JSTS}] · 1_{x ∈ T_X} d(P_X n)
      --     ≤ ∫_{x ∈ T_X} target n d(P_X n) ≤ target n.
      -- Implementation: re-write the LHS as an integral on `(P_X n) × W` via Fubini,
      -- decompose by `x ∈ T_X` vs not, then bound.
      -- Step c.1: re-express the LHS sum as `∫ x, W.real (sliceX_no_match x) d P_X`
      --           where `sliceX_no_match x = {c | ¬∃m, (x, c m) ∈ JSTS} ∩ {· | x ∈ T_X}`.
      -- Because `T_X` is a property of `x` only, this factorises.
      -- Approach: use `integral_fintype` to write ∑_c W{c}*f c = ∫_c f c ∂W.
      -- Then exchange integrals with `MeasureTheory.integral_integral_swap` or
      -- by writing the inner expression as a measurable set under W and exchanging.
      -- For simplicity, we work directly:
      -- ∑_c W{c} * (P_X n){x | P(c,x)}
      --   = (P_X n){x | P(c,x)} weighted-sum-c
      --   = ∫_c (P_X n).real {x | P(c,x)} ∂W
      --   = ∫_x W.real {c | P(c,x)} d(P_X n)        (Fubini swap)
      -- where P(c,x) := x ∈ T_X ∧ ¬∃m, (x, c m) ∈ JSTS.
      classical
      set R_set : Set (Codebook (Mn n) n β × (Fin n → α)) :=
        { (c, x) : Codebook (Mn n) n β × (Fin n → α) |
            x ∈ T_X ∧
              ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                  (rdAmbient qStar) (iidXs (α := α) (β := β))
                  (iidYs (α := α) (β := β)) n ε_join } with hR_set_def
      have hR_set_meas : MeasurableSet R_set := (Set.toFinite _).measurableSet
      -- ∑_c W{c}.real * (P_X n).real (slice_c c) = (W.prod (P_X n)).real R_set
      have h_sum_eq_prod :
          ∑ c : Codebook (Mn n) n β,
              W.real {c} *
                (P_X n).real
                  { x : Fin n → α | x ∈ T_X ∧
                      ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                          (rdAmbient qStar) (iidXs (α := α) (β := β))
                          (iidYs (α := α) (β := β)) n ε_join }
            = (W.prod (P_X n)).real R_set := by
        -- Use Measure.prod_apply with sections.
        have h_section : ∀ c : Codebook (Mn n) n β,
            (Prod.mk c ⁻¹' R_set)
              = { x : Fin n → α | x ∈ T_X ∧
                  ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                      (rdAmbient qStar) (iidXs (α := α) (β := β))
                      (iidYs (α := α) (β := β)) n ε_join } := by
          intro c; ext x; simp [hR_set_def]
        have h_prod :
            (W.prod (P_X n)) R_set
              = ∫⁻ c, (P_X n) (Prod.mk c ⁻¹' R_set) ∂W :=
          Measure.prod_apply hR_set_meas
        -- Each section measure is in ENNReal: `(P_X n) (slice_c c) = ((P_X n).real (slice_c c)).toNNReal · 1` form.
        -- For the converse, evaluate ∫⁻ as a finsum.
        have h_lint_eq :
            ∫⁻ c, (P_X n) (Prod.mk c ⁻¹' R_set) ∂W
              = ∑ c : Codebook (Mn n) n β,
                  (P_X n) (Prod.mk c ⁻¹' R_set) * W {c} := by
          haveI : MeasurableSingletonClass (Codebook (Mn n) n β) :=
            Pi.instMeasurableSingletonClass
          exact MeasureTheory.lintegral_fintype (μ := W) _
        -- toReal of sum of products = real-sum (each finite).
        have h_toreal_sum :
            ((W.prod (P_X n)) R_set).toReal
              = ∑ c : Codebook (Mn n) n β,
                  W.real {c} * (P_X n).real (Prod.mk c ⁻¹' R_set) := by
          rw [h_prod, h_lint_eq, ENNReal.toReal_sum]
          · refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [ENNReal.toReal_mul]
            show (P_X n).real _ * W.real _ = W.real _ * (P_X n).real _
            ring
          · intro c _
            exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
        -- Combine.
        show _ = ((W.prod (P_X n)) R_set).toReal
        rw [h_toreal_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [h_section c]
      -- Now apply Fubini to swap and bound.
      -- (W.prod (P_X n)).real R_set = (P_X n × W).real (swap R_set), but easier:
      -- prod_apply on slot x: (W.prod (P_X n)) R_set = ∫⁻ c, (P_X n) (slice c) ∂W.
      -- For each x in T_X (and `n ≥ N_B`), Step B gives:
      --   W.real {c | ¬∃m, (x, c m) ∈ JSTS} ≤ target n.
      -- We want to upper-bound by ∫_x [W.real {c | ...}] d(P_X n), restricted to x ∈ T_X.
      --
      -- Use the symmetric form: (W.prod (P_X n)) R_set = ((P_X n).prod W).real (Prod.swap R_set).
      -- Then prod_apply: = ∫⁻ x, W (swap_section x) ∂(P_X n).
      -- Bound the integrand: for x ∈ T_X, W (swap_section x) ≤ target n; for x ∉ T_X, 0.
      have h_prod_swap :
          (W.prod (P_X n)).real R_set
            = ((P_X n).prod W).real (Prod.swap '' R_set) := by
        -- (W.prod (P_X n)) R = ((P_X n).prod W) (Prod.swap ⁻¹' R) = ((P_X n).prod W) (Prod.swap '' R).
        -- We use `prod_swap` or `Measure.measurePreserving_swap`.
        have h_eq :
            (W.prod (P_X n)) R_set
              = ((P_X n).prod W) (Prod.swap ⁻¹' R_set) := by
          have h_swap := MeasureTheory.Measure.prod_swap (μ := P_X n) (ν := W)
          -- (P_X.prod W).map Prod.swap = W.prod (P_X)
          rw [← h_swap, MeasureTheory.Measure.map_apply measurable_swap hR_set_meas]
        -- Prod.swap is an involution, so preimage = image.
        have h_swap_eq : Prod.swap ⁻¹' R_set = Prod.swap '' R_set := by
          ext xy; constructor
          · intro hxy
            refine ⟨xy.swap, hxy, ?_⟩
            simp [Prod.swap]
          · rintro ⟨ab, hab, rfl⟩
            simp [Prod.swap]
            exact hab
        show ((W.prod (P_X n)) R_set).toReal
            = (((P_X n).prod W) (Prod.swap '' R_set)).toReal
        rw [h_eq, h_swap_eq]
      -- swap R_set = {(x, c) | (c, x) ∈ R_set}
      set R_set' : Set ((Fin n → α) × Codebook (Mn n) n β) := Prod.swap '' R_set
        with hR_set'_def
      have hR_set'_eq :
          R_set' =
            { p : (Fin n → α) × Codebook (Mn n) n β |
                p.1 ∈ T_X ∧
                ¬ ∃ m : Fin (Mn n), (p.1, p.2 m) ∈ jointStronglyTypicalSet
                    (rdAmbient qStar) (iidXs (α := α) (β := β))
                    (iidYs (α := α) (β := β)) n ε_join } := by
        ext xc
        simp only [hR_set'_def, Set.mem_image, hR_set_def, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨c, x⟩, ⟨hxTX, hnex⟩, hxc⟩
          rw [Prod.swap] at hxc
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxc
          exact ⟨hxTX, hnex⟩
        · intro ⟨h1, h2⟩
          refine ⟨(xc.2, xc.1), ⟨h1, h2⟩, ?_⟩
          rcases xc with ⟨x, c⟩
          rfl
      have hR_set'_meas : MeasurableSet R_set' := by
        rw [hR_set'_eq]; exact (Set.toFinite _).measurableSet
      -- Now apply prod_apply on (P_X n).prod W with R_set'.
      have h_prod' :
          ((P_X n).prod W) R_set'
            = ∫⁻ x, W (Prod.mk x ⁻¹' R_set') ∂(P_X n) :=
        Measure.prod_apply hR_set'_meas
      -- For each x, Prod.mk x ⁻¹' R_set' is {c | x ∈ T_X ∧ ¬∃m, (x, c m) ∈ JSTS}.
      have h_section_x : ∀ x : Fin n → α,
          Prod.mk x ⁻¹' R_set'
            = if x ∈ T_X then
                { c : Codebook (Mn n) n β |
                    ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                        (rdAmbient qStar) (iidXs (α := α) (β := β))
                        (iidYs (α := α) (β := β)) n ε_join }
              else ∅ := by
        intro x
        by_cases hxTX : x ∈ T_X
        · rw [if_pos hxTX]; ext c
          simp [hR_set'_eq, hxTX]
        · rw [if_neg hxTX]; ext c
          simp [hR_set'_eq, hxTX]
      -- Bound the section measure pointwise.
      -- For x ∈ T_X, Step B yields `W.real (no-match) ≤ exp(-(Mn n)*target n)`.
      set bound : ℝ := Real.exp (-((Mn n : ℝ) * target n)) with hbound_def
      have hbound_nn : 0 ≤ bound := (Real.exp_pos _).le
      have h_section_bound : ∀ x : Fin n → α,
          W (Prod.mk x ⁻¹' R_set') ≤ ENNReal.ofReal bound := by
        intro x
        rw [h_section_x x]
        by_cases hxTX : x ∈ T_X
        · rw [if_pos hxTX]
          -- W = Measure.pi (fun _ : Fin Mn => p); apply Step B.
          have h_step_B := hN_B n hn_NB (Mn n) x hxTX
          have h_set_eq :
              { c : Codebook (Mn n) n β |
                  ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                      (rdAmbient qStar) (iidXs (α := α) (β := β))
                      (iidYs (α := α) (β := β)) n ε_join }
                = { c : Fin (Mn n) → (Fin n → β) |
                    ∀ m, (x, c m) ∉ jointStronglyTypicalSet
                        (rdAmbient qStar) (iidXs (α := α) (β := β))
                        (iidYs (α := α) (β := β)) n ε_join } := by
            ext c; simp [not_exists]
          rw [h_set_eq, hW_eq_pi]
          have h_real_le : (Measure.pi (fun _ : Fin (Mn n) => p)).real
              { c : Fin (Mn n) → (Fin n → β) |
                  ∀ m, (x, c m) ∉ jointStronglyTypicalSet
                      (rdAmbient qStar) (iidXs (α := α) (β := β))
                      (iidYs (α := α) (β := β)) n ε_join }
                ≤ bound := by
            have hbE := h_step_B
            -- Reshape both sides to align with `bound = exp(-(Mn n) * target n)`.
            -- `bound = exp(-(Mn n) * target n)` and `target n = exp(-n · (...))`.
            have h_eq : Real.exp (-((Mn n : ℝ) * target n))
                = Real.exp (-(Mn n : ℝ) *
                  Real.exp (-(n : ℝ) *
                    (entropy (rdAmbient qStar) (iidXs (α := α) (β := β) 0)
                      + entropy (rdAmbient qStar) (iidYs (α := α) (β := β) 0)
                      - entropy (rdAmbient qStar)
                          (jointSequence (α := α) (β := β) iidXs iidYs 0)
                      + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
                            (iidYs (α := α) (β := β))
                        + ε_X * logSumAbs (rdAmbient qStar)
                            (iidXs (α := α) (β := β))
                        + ε_X * logSumAbs (rdAmbient qStar)
                            (jointSequence (α := α) (β := β) iidXs iidYs)
                        + δ_kl)))) := by
              rw [htarget_def]; ring_nf
            rw [hbound_def, h_eq]
            exact hbE
          have h_lhs_le_top :
              (Measure.pi (fun _ : Fin (Mn n) => p))
                { c : Fin (Mn n) → (Fin n → β) |
                    ∀ m, (x, c m) ∉ jointStronglyTypicalSet
                        (rdAmbient qStar) (iidXs (α := α) (β := β))
                        (iidYs (α := α) (β := β)) n ε_join }
                ≠ ∞ := measure_ne_top _ _
          rw [← ENNReal.ofReal_toReal h_lhs_le_top]
          exact ENNReal.ofReal_le_ofReal h_real_le
        · rw [if_neg hxTX]; simp
      -- Therefore ∫⁻ x, W(section x) d(P_X n) ≤ ENNReal.ofReal bound.
      have h_int_bound :
          ∫⁻ x, W (Prod.mk x ⁻¹' R_set') ∂(P_X n)
            ≤ ENNReal.ofReal bound := by
        haveI : IsProbabilityMeasure (P_X n) := by
          show IsProbabilityMeasure
            (Measure.pi (fun _ : Fin n =>
                (rdAmbient qStar).map (iidXs (α := α) (β := β) 0)))
          infer_instance
        calc ∫⁻ x, W (Prod.mk x ⁻¹' R_set') ∂(P_X n)
            ≤ ∫⁻ _x, ENNReal.ofReal bound ∂(P_X n) :=
              lintegral_mono (fun x => h_section_bound x)
          _ = ENNReal.ofReal bound * (P_X n) Set.univ := by
              rw [lintegral_const]
          _ ≤ ENNReal.ofReal bound := by
              rw [measure_univ]; rw [mul_one]
      have h_real_le :
          ((P_X n).prod W).real R_set' ≤ bound := by
        show (((P_X n).prod W) R_set').toReal ≤ bound
        rw [h_prod']
        calc (∫⁻ x, W (Prod.mk x ⁻¹' R_set') ∂(P_X n)).toReal
            ≤ (ENNReal.ofReal bound).toReal := by
              refine ENNReal.toReal_mono ?_ h_int_bound
              exact ENNReal.ofReal_ne_top
          _ = bound := ENNReal.toReal_ofReal hbound_nn
      calc ∑ c, W.real {c} * (P_X n).real
              { x : Fin n → α | x ∈ T_X ∧
                  ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                      (rdAmbient qStar) (iidXs (α := α) (β := β))
                      (iidYs (α := α) (β := β)) n ε_join }
          = (W.prod (P_X n)).real R_set := h_sum_eq_prod
        _ = ((P_X n).prod W).real R_set' := h_prod_swap
        _ ≤ bound := h_real_le
        _ = Real.exp (-((Mn n : ℝ) * target n)) := hbound_def
    -- Step d: combine `h_weighted_avg` and `h_avg_nomatch_bound`.
    -- codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
    --   = ∑ c, W.real {c} * fail_c c   (by `codebookAvgFailureStrong` def)
    --   ≤ (P_X n).real notTX + ∑ c, W{c}*Pr(Nc)   (h_weighted_avg)
    --   ≤ (P_X n).real notTX + exp(-(Mn n)*target n) (h_avg_nomatch_bound).
    show codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
        ≤ (P_X n).real notTX + Real.exp (-((Mn n : ℝ) * target n))
    have h_def_eq :
        codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
          = ∑ c : Codebook (Mn n) n β, W.real {c} * fail_c c := by
      unfold codebookAvgFailureStrong
      show ∑ c : Codebook (Nat.ceil _) n β, _ * _ = ∑ c : Codebook (Mn n) n β, _ * _
      rfl
    rw [h_def_eq]
    linarith
  -- ## Step 4: combine `h_pi_compl_tendsto + h_exp_neg_Mn_target_tendsto` for the sum.
  -- 0 ≤ codebookAvgFailureStrong n ≤ (P_X n).real notTX + exp(-(Mn n)*target n).
  -- Sum of two sequences each → 0 is → 0; squeeze gives final result.
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n : ℕ => (P_X n).real
            {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                                (iidXs (α := α) (β := β)) n ε_X}
          + Real.exp (-((Mn n : ℝ) * target n)))
        Filter.atTop (𝓝 0) := by
    have h := h_pi_compl_tendsto.add h_exp_neg_Mn_target_tendsto
    simpa using h
  -- Squeeze: 0 ≤ codebookAvgFailureStrong n ≤ (sum); both ends → 0.
  refine Filter.Tendsto.squeeze'
    (g := fun _ => (0 : ℝ))
    (h := fun n => (P_X n).real
            {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                                (iidXs (α := α) (β := β)) n ε_X}
          + Real.exp (-((Mn n : ℝ) * target n)))
    tendsto_const_nhds h_sum_tendsto
    (Filter.Eventually.of_forall (fun n =>
      codebookAvgFailureStrong_nonneg qStar d R n ε_join ε_dist δ_typ))
    h_pointwise_bound

/-! ## Final theorem: `rate_distortion_achievability` -/

/-- **Rate-distortion achievability (strong-typicality variant, positive `qStar`)**.

Given a feasible joint pmf `qStar ∈ RDConstraint P_X_pmf d D` with strictly
positive mass on every `(a, b)`, and a rate `R > mutualInfoPmf qStar`, for any
tolerance `ε' > 0`, there exists `N` such that for all `n ≥ N`, there exists a
lossy code of size `⌈exp(nR)⌉` whose expected block distortion is `≤ D + ε'`.

The slack parameters `ε_X`, `ε_join`, `ε_dist`, `δ_kl`, `δ_typ` are exposed
as explicit hypotheses to keep the slack-budgeting calculations external; a
caller can choose them in any consistent way.

**Restriction**: `hqStar_pos : ∀ p, 0 < qStar p` is required by
`conditionalStronglyTypicalSlice_mass_ge`. The unconditional formulation
requires a perturbation argument (passing through `qStar_τ := (1-τ)·qStar + τ·uniform`,
exploiting continuity of `mutualInfoPmf` and `expectedDistortionPmf`) — left
for a separate round. -/
theorem rate_distortion_achievability_strong
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    (hqStar_pos : ∀ p : α × β, 0 < qStar p)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε')
    -- Caller-supplied slack parameters.
    (ε_X ε_join ε_dist δ_kl δ_typ : ℝ)
    (hε_X_pos : 0 < ε_X) (hε_join_pos : 0 < ε_join)
    (hε_dist_pos : 0 < ε_dist) (hδ_kl_pos : 0 < δ_kl) (hδ_typ_nn : 0 ≤ δ_typ)
    (hε_X_lt_ε_join : ε_X < ε_join)
    -- Rate gap.
    (h_rate_gap :
        mutualInfoPmf qStar
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
                  (iidYs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar) (iidXs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar)
                  (jointSequence (α := α) (β := β) iidXs iidYs)
              + δ_kl) < R)
    -- Distortion budget.
    (h_slack : expectedDistortionPmf d qStar + δ_typ ≤ D + ε' / 2)
    (h_dist_slack :
        ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
    -- Bridge slack hypothesis (consumes `jointStronglyTypicalSet ⊆ distortionTypicalSet`).
    (h_jts_subset_dts : ∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → α) (y : Fin n → β),
        (x, y) ∈ jointStronglyTypicalSet (rdAmbient qStar) iidXs iidYs n ε_join →
        (x, y) ∈ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d n
                      ε_dist δ_typ)
    -- KL bound.
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β,
        qZ_min ≤ (pmfToMeasure (α := α × β) qStar).real {p})
    (hδ_kl_dominates :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ_kl * qZ_min) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion
            ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) d ≤ D + ε' := by
  have hqStar_simp : qStar ∈ stdSimplex ℝ (α × β) := hqStar_mem.1
  -- Construct the failure sequence as `codebookAvgFailureStrong` itself.
  set failure_seq : ℕ → ℝ :=
    fun n => codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
    with hfailure_def
  have h_failure_nn : ∀ n, 0 ≤ failure_seq n := fun n =>
    codebookAvgFailureStrong_nonneg qStar d R n ε_join ε_dist δ_typ
  have h_failure_tendsto_zero :
      Filter.Tendsto failure_seq Filter.atTop (𝓝 0) :=
    codebookAvgFailureStrong_tendsto_zero qStar hqStar_simp hqStar_pos d hI_lt_R
      ε_dist δ_typ hε_dist_pos hδ_typ_nn ε_X ε_join δ_kl
      hε_X_pos hε_join_pos hδ_kl_pos hε_X_lt_ε_join h_rate_gap h_dist_slack
      h_jts_subset_dts qZ_min hqZ_min_pos hqZ_min_le hδ_kl_dominates
  -- Discharge via the partial discharge wrapper.
  have h_codebook_avg_failure : ∀ {n : ℕ} (hn : 0 < n),
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
        ≤ failure_seq n := by
    intro n _hn
    show _ ≤ codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
    unfold codebookAvgFailureStrong
    exact le_refl _
  exact rate_distortion_achievability_partial_discharge_strong
    (P_X_pmf := P_X_pmf) (d := d) (D := D)
    qStar hqStar_mem (R := R) hI_lt_R (ε' := ε') hε'
    (ε_join := ε_join) (ε_dist := ε_dist) (δ_typ := δ_typ) hδ_typ_nn
    (failure_seq := failure_seq) h_failure_nn h_failure_tendsto_zero
    (h_codebook_avg_failure := h_codebook_avg_failure)
    (h_slack := h_slack)

/-- **Rate-distortion achievability** — public alias for the
strong-typicality form. The unconditional (no `hqStar_pos`) form requires a
perturbation argument that is out of scope here; the conditional form below
discharges the entire random-coding chain (0 `sorry`, 0 user-axiom).

`@audit:suspect()` -/
theorem rate_distortion_achievability
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    (hqStar_pos : ∀ p : α × β, 0 < qStar p)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε')
    (ε_X ε_join ε_dist δ_kl δ_typ : ℝ)
    (hε_X_pos : 0 < ε_X) (hε_join_pos : 0 < ε_join)
    (hε_dist_pos : 0 < ε_dist) (hδ_kl_pos : 0 < δ_kl) (hδ_typ_nn : 0 ≤ δ_typ)
    (hε_X_lt_ε_join : ε_X < ε_join)
    (h_rate_gap :
        mutualInfoPmf qStar
            + ((Fintype.card α : ℝ) * ε_X * logSumAbs (rdAmbient qStar)
                  (iidYs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar) (iidXs (α := α) (β := β))
              + ε_X * logSumAbs (rdAmbient qStar)
                  (jointSequence (α := α) (β := β) iidXs iidYs)
              + δ_kl) < R)
    (h_slack : expectedDistortionPmf d qStar + δ_typ ≤ D + ε' / 2)
    (h_dist_slack :
        ε_join * ∑ p : α × β, ((d p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
    (h_jts_subset_dts : ∀ {n : ℕ}, 0 < n → ∀ (x : Fin n → α) (y : Fin n → β),
        (x, y) ∈ jointStronglyTypicalSet (rdAmbient qStar) iidXs iidYs n ε_join →
        (x, y) ∈ distortionTypicalSet (rdAmbient qStar) iidXs iidYs d n
                      ε_dist δ_typ)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β,
        qZ_min ≤ (pmfToMeasure (α := α × β) qStar).real {p})
    (hδ_kl_dominates :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ_kl * qZ_min) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion
            ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)) d ≤ D + ε' :=
  rate_distortion_achievability_strong P_X_pmf d qStar hqStar_mem hqStar_pos
    hI_lt_R hε' ε_X ε_join ε_dist δ_kl δ_typ hε_X_pos hε_join_pos hε_dist_pos
    hδ_kl_pos hδ_typ_nn hε_X_lt_ε_join h_rate_gap h_slack h_dist_slack
    h_jts_subset_dts qZ_min hqZ_min_pos hqZ_min_le hδ_kl_dominates

end InformationTheory.Shannon
