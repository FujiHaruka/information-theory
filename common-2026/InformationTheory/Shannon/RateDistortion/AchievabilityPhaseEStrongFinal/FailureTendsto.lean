import InformationTheory.Draft.Shannon.RateDistortionAchievabilityPhaseE
import InformationTheory.Draft.Shannon.RateDistortionAchievabilityPhaseEDischarge
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ConditionalMethodOfTypes
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseC
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseD
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseEStrong
import InformationTheory.Shannon.RateDistortion.AchievabilityPhaseEStrongFinal.Setup

/-!
# Rate-distortion achievability (strong final) — FailureTendsto part

The main probabilistic content `codebookAvgFailureStrong_tendsto_zero`.
Split out from `AchievabilityPhaseEStrongFinal.lean` for the 1500-line-per-file
convention; proof is unchanged.
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

lemma measureReal_prod_eq_measureReal_prod_swap_image
    {γ₁ γ₂ : Type*} [MeasurableSpace γ₁] [MeasurableSpace γ₂]
    (μ : Measure γ₁) (ν : Measure γ₂) [SFinite μ] [SFinite ν]
    {S : Set (γ₁ × γ₂)} (hS : MeasurableSet S) :
    (μ.prod ν).real S = (ν.prod μ).real (Prod.swap '' S) := by
  have h_eq : (μ.prod ν) S = (ν.prod μ) (Prod.swap ⁻¹' S) := by
    have h_swap := MeasureTheory.Measure.prod_swap (μ := ν) (ν := μ)
    rw [← h_swap, MeasureTheory.Measure.map_apply measurable_swap hS]
  have h_swap_eq : Prod.swap ⁻¹' S = Prod.swap '' S := by
    ext xy; constructor
    · intro hxy
      refine ⟨xy.swap, hxy, ?_⟩
      simp [Prod.swap]
    · rintro ⟨ab, hab, rfl⟩
      simp only [Prod.swap, Set.mem_preimage, Prod.mk.eta]
      exact hab
  show ((μ.prod ν) S).toReal = (((ν.prod μ)) (Prod.swap '' S)).toReal
  rw [h_eq, h_swap_eq]

lemma sum_weighted_le_const_add_sum_weighted_of_le_add
    {ι : Type*} [Fintype ι] (w f g : ι → ℝ) (A : ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (h_le : ∀ i, f i ≤ A + g i) :
    ∑ i, w i * f i ≤ A + ∑ i, w i * g i := by
  have h_step1 : ∑ i, w i * f i ≤ ∑ i, w i * (A + g i) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h_le i) (hw_nonneg i))
  have h_step2 : ∑ i, w i * (A + g i) = A + ∑ i, w i * g i := by
    have h_dist : ∑ i, w i * (A + g i)
        = (∑ i, w i * A) + ∑ i, w i * g i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    have h_sum_A : ∑ i, w i * A = A := by
      rw [show ∑ i, w i * A = (∑ i, w i) * A from by rw [Finset.sum_mul]]
      rw [hw_sum]; ring
    rw [h_dist, h_sum_A]
  linarith

lemma measureReal_le_add_measureReal_of_subset_union
    {γ : Type*} [MeasurableSpace γ] (μ : Measure γ) [IsFiniteMeasure μ]
    {S A B : Set γ} (hS : S ⊆ A ∪ B) :
    μ.real S ≤ μ.real A + μ.real B := by
  have h_le := measureReal_mono (μ := μ) hS (measure_ne_top _ _)
  have h_union_le : μ.real (A ∪ B) ≤ μ.real A + μ.real B :=
    measureReal_union_le _ _
  linarith

lemma sum_measureReal_singleton_univ_eq_one
    {ι : Type*} [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι]
    (μ : Measure ι) [IsProbabilityMeasure μ] :
    ∑ i : ι, μ.real {i} = 1 := by
  have h_real_univ : μ.real ((Finset.univ : Finset ι) : Set ι) = 1 := by
    rw [Finset.coe_univ, measureReal_def, measure_univ]
    rfl
  have h_sum_eq := sum_measureReal_singleton (μ := μ) (Finset.univ : Finset ι)
  rw [h_sum_eq, h_real_univ]

lemma measureReal_prod_eq_sum_measureReal_singleton_mul_measureReal_section
    {ι γ : Type*} [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι]
    [MeasurableSpace γ] (μ : Measure ι) (ν : Measure γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {R : Set (ι × γ)} (hR : MeasurableSet R) :
    (μ.prod ν).real R
      = ∑ c : ι, μ.real {c} * ν.real (Prod.mk c ⁻¹' R) := by
  have h_prod : (μ.prod ν) R = ∫⁻ c, ν (Prod.mk c ⁻¹' R) ∂μ :=
    Measure.prod_apply hR
  have h_lint_eq :
      ∫⁻ c, ν (Prod.mk c ⁻¹' R) ∂μ
        = ∑ c : ι, ν (Prod.mk c ⁻¹' R) * μ {c} :=
    MeasureTheory.lintegral_fintype (μ := μ) _
  show ((μ.prod ν) R).toReal = _
  rw [h_prod, h_lint_eq, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [ENNReal.toReal_mul]
    show ν.real _ * μ.real _ = μ.real _ * ν.real _
    ring
  · intro c _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

lemma measureReal_prod_le_of_measure_section_le_ofReal
    {γ₁ γ₂ : Type*} [MeasurableSpace γ₁] [MeasurableSpace γ₂]
    (μ : Measure γ₁) (ν : Measure γ₂) [IsProbabilityMeasure μ] [SFinite ν]
    {R : Set (γ₁ × γ₂)} (hR : MeasurableSet R) (b : ℝ) (hb : 0 ≤ b)
    (h_section : ∀ x, ν (Prod.mk x ⁻¹' R) ≤ ENNReal.ofReal b) :
    (μ.prod ν).real R ≤ b := by
  have h_prod : (μ.prod ν) R = ∫⁻ x, ν (Prod.mk x ⁻¹' R) ∂μ :=
    Measure.prod_apply hR
  have h_int_bound :
      ∫⁻ x, ν (Prod.mk x ⁻¹' R) ∂μ ≤ ENNReal.ofReal b := by
    calc ∫⁻ x, ν (Prod.mk x ⁻¹' R) ∂μ
        ≤ ∫⁻ _x, ENNReal.ofReal b ∂μ := lintegral_mono h_section
      _ = ENNReal.ofReal b * μ Set.univ := by rw [lintegral_const]
      _ ≤ ENNReal.ofReal b := by rw [measure_univ]; rw [mul_one]
  show ((μ.prod ν) R).toReal ≤ b
  rw [h_prod]
  calc (∫⁻ x, ν (Prod.mk x ⁻¹' R) ∂μ).toReal
      ≤ (ENNReal.ofReal b).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h_int_bound
    _ = b := ENNReal.toReal_ofReal hb

lemma tendsto_measureReal_compl_zero_of_tendsto_measure_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (hE_meas : ∀ n, MeasurableSet (E n))
    (hE : Filter.Tendsto (fun n => μ (E n)) Filter.atTop (𝓝 1)) :
    Filter.Tendsto (fun n => (μ (E n)ᶜ).toReal) Filter.atTop (𝓝 0) := by
  have h_aep_real :
      Filter.Tendsto (fun n => μ.real (E n)) Filter.atTop (𝓝 1) := by
    simp only [measureReal_def]
    exact (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hE
  have h_pointwise : ∀ n, (μ (E n)ᶜ).toReal = 1 - μ.real (E n) := by
    intro n
    show (μ (E n)ᶜ).toReal = _
    rw [← measureReal_def, probReal_compl_eq_one_sub (hE_meas n)]
  have h_minus :
      Filter.Tendsto (fun n => (1 : ℝ) - μ.real (E n)) Filter.atTop (𝓝 0) := by
    have := h_aep_real.const_sub (1 : ℝ)
    simpa using this
  refine h_minus.congr (fun n => ?_)
  rw [h_pointwise n]

lemma weightedSum_section_pred_le_of_section_measure_le
    {κ ι : Type*} [MeasurableSpace κ] [Fintype κ] [MeasurableSingletonClass κ]
    [MeasurableSpace ι]
    (W : Measure κ) [IsProbabilityMeasure W]
    (Q : Measure ι) [IsProbabilityMeasure Q]
    (Pred : κ → ι → Prop)
    (hPred_meas_x : ∀ c, MeasurableSet {x : ι | Pred c x})
    (hPred_meas_prod : MeasurableSet {p : κ × ι | Pred p.1 p.2})
    (b : ℝ) (hb : 0 ≤ b)
    (h_section_bound : ∀ x : ι,
        W {c : κ | Pred c x} ≤ ENNReal.ofReal b) :
    ∑ c : κ, W.real {c} * Q.real {x : ι | Pred c x} ≤ b := by
  classical
  set R_set : Set (κ × ι) := {p : κ × ι | Pred p.1 p.2} with hR_set_def
  -- Sum over `c` equals the product-measure of `R_set`.
  have h_sum_eq_prod :
      ∑ c : κ, W.real {c} * Q.real {x : ι | Pred c x}
        = (W.prod Q).real R_set := by
    have h_section : ∀ c : κ, (Prod.mk c ⁻¹' R_set) = {x : ι | Pred c x} := by
      intro c; ext x; simp [hR_set_def]
    rw [measureReal_prod_eq_sum_measureReal_singleton_mul_measureReal_section
          W Q hPred_meas_prod]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [h_section c]
  -- Swap to the `(Q × W)` orientation.
  set R_set' : Set (ι × κ) := Prod.swap '' R_set with hR_set'_def
  have h_prod_swap :
      (W.prod Q).real R_set = (Q.prod W).real R_set' :=
    measureReal_prod_eq_measureReal_prod_swap_image W Q hPred_meas_prod
  have h_section_x : ∀ x : ι, Prod.mk x ⁻¹' R_set' = {c : κ | Pred c x} := by
    intro x; ext c
    simp only [hR_set'_def, Set.mem_preimage, Set.mem_image, hR_set_def,
      Set.mem_setOf_eq, Prod.exists, Prod.swap_prod_mk]
    constructor
    · rintro ⟨a, y, hP, hay⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hay
      exact hP
    · intro hP; exact ⟨c, x, hP, rfl⟩
  have hR_set'_meas : MeasurableSet R_set' := by
    have h_swap_eq : R_set' = Prod.swap ⁻¹' R_set := by
      rw [hR_set'_def, Set.image_swap_eq_preimage_swap]
    rw [h_swap_eq]
    exact measurable_swap hPred_meas_prod
  have h_real_le : (Q.prod W).real R_set' ≤ b :=
    measureReal_prod_le_of_measure_section_le_ofReal Q W hR_set'_meas b hb
      (fun x => by rw [h_section_x x]; exact h_section_bound x)
  rw [h_sum_eq_prod, h_prod_swap]
  exact h_real_le

lemma piMeasure_section_no_match_le_of_typical
    {ιx M : Type*} [MeasurableSpace ιx] [Fintype M]
    {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (p : Measure γ) [IsProbabilityMeasure p]
    (Match : (M → γ) → ιx → Prop) [∀ c, DecidablePred (fun x => Match c x)]
    (T_X : Set ιx) (b : ℝ) (hb : 0 ≤ b)
    (h_typical : ∀ x ∈ T_X,
        (Measure.pi (fun _ : M => p)).real {c : M → γ | ¬ Match c x} ≤ b) :
    ∀ x : ιx,
        (Measure.pi (fun _ : M => p))
            {c : M → γ | x ∈ T_X ∧ ¬ Match c x} ≤ ENNReal.ofReal b := by
  intro x
  by_cases hxTX : x ∈ T_X
  · have h_set_eq : {c : M → γ | x ∈ T_X ∧ ¬ Match c x}
        = {c : M → γ | ¬ Match c x} := by
      ext c; simp [hxTX]
    rw [h_set_eq]
    have h_real_le := h_typical x hxTX
    have h_lhs_le_top : (Measure.pi (fun _ : M => p))
        {c : M → γ | ¬ Match c x} ≠ ∞ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal h_lhs_le_top]
    exact ENNReal.ofReal_le_ofReal h_real_le
  · have h_empty : {c : M → γ | x ∈ T_X ∧ ¬ Match c x} = ∅ := by
      ext c; simp [hxTX]
    rw [h_empty]; simp

lemma encoderFailure_subset_notTypical_union_noMatch
    {ιx ιy : Type*} (T_X : Set ιx) (DTS JSTS : Set (ιx × ιy))
    {M : Type*} (c : M → ιy) (enc : ιx → M)
    (hJTS_subset : ∀ x : ιx, x ∈ T_X →
        ∀ y : ιy, (x, y) ∈ JSTS → (x, y) ∈ DTS)
    (hEnc_spec : ∀ x : ιx, (∃ m : M, (x, c m) ∈ JSTS) → (x, c (enc x)) ∈ JSTS) :
    {x : ιx | (x, c (enc x)) ∉ DTS}
      ⊆ {x : ιx | x ∉ T_X}
        ∪ {x : ιx | x ∈ T_X ∧ ¬ ∃ m : M, (x, c m) ∈ JSTS} := by
  intro x hx
  by_cases hxTX : x ∈ T_X
  · right
    refine ⟨hxTX, ?_⟩
    intro hex
    have hpick : (x, c (enc x)) ∈ JSTS := hEnc_spec x hex
    have hpick_dts := hJTS_subset x hxTX _ hpick
    exact hx hpick_dts
  · left
    exact hxTX

lemma tendsto_measureReal_map_notMem_zero_of_tendsto_prob_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ιx : ℕ → Type*} [∀ n, MeasurableSpace (ιx n)]
    (jr : ∀ n, Ω → ιx n) (hjr : ∀ n, Measurable (jr n))
    (S : ∀ n, Set (ιx n)) (hS : ∀ n, MeasurableSet (S n))
    (Pn : ∀ n, Measure (ιx n)) (hPn : ∀ n, μ.map (jr n) = Pn n)
    (h_aep : Filter.Tendsto
        (fun n => μ {ω | jr n ω ∈ S n}) Filter.atTop (𝓝 1)) :
    Filter.Tendsto
      (fun n : ℕ => (Pn n).real {x : ιx n | x ∉ S n})
      Filter.atTop (𝓝 0) := by
  have h_aep_compl :
      Filter.Tendsto
        (fun n : ℕ => (μ {ω | jr n ω ∉ S n}).toReal)
        Filter.atTop (𝓝 0) := by
    have h_meas : ∀ n, MeasurableSet {ω | jr n ω ∈ S n} :=
      fun n => hjr n (hS n)
    have h_base := tendsto_measureReal_compl_zero_of_tendsto_measure_one
      μ (fun n => {ω | jr n ω ∈ S n}) h_meas h_aep
    refine h_base.congr (fun n => ?_)
    have h_set_eq :
        {ω | jr n ω ∉ S n} = {ω | jr n ω ∈ S n}ᶜ := by ext ω; simp
    rw [h_set_eq]
  have h_map_eq : ∀ n : ℕ,
      (Pn n).real {x : ιx n | x ∉ S n}
        = (μ {ω | jr n ω ∉ S n}).toReal := by
    intro n
    show ((Pn n) _).toReal = _
    have h_preimage : (jr n) ⁻¹' {x : ιx n | x ∉ S n} = {ω | jr n ω ∉ S n} := rfl
    have h_meas_set : MeasurableSet {x : ιx n | x ∉ S n} := (hS n).compl
    rw [← hPn n, MeasureTheory.Measure.map_apply (hjr n) h_meas_set, h_preimage]
  refine h_aep_compl.congr (fun n => ?_)
  rw [h_map_eq n]

lemma weightedSum_fail_le_const_add_of_per_index_and_sum_bound
    {κ : Type*} [MeasurableSpace κ] [Fintype κ] [MeasurableSingletonClass κ]
    (W : Measure κ) [IsProbabilityMeasure W]
    (fail g : κ → ℝ) (A bound : ℝ)
    (h_per : ∀ c, fail c ≤ A + g c)
    (h_sum_g : ∑ c, W.real {c} * g c ≤ bound) :
    ∑ c, W.real {c} * fail c ≤ A + bound := by
  have hW_sum_one : ∑ c : κ, W.real {c} = 1 :=
    sum_measureReal_singleton_univ_eq_one W
  have h_weighted := sum_weighted_le_const_add_sum_weighted_of_le_add
    (fun c => W.real {c}) fail g A (fun _ => measureReal_nonneg) hW_sum_one h_per
  linarith

lemma measureReal_encoderFailure_le_notTypical_add_noMatch
    {ιx ιy : Type*} [MeasurableSpace ιx]
    (Q : Measure ιx) [IsFiniteMeasure Q]
    (T_X : Set ιx) (DTS JSTS : Set (ιx × ιy))
    {M : Type*} (c : M → ιy) (enc : ιx → M)
    (hJTS_subset : ∀ x : ιx, x ∈ T_X →
        ∀ y : ιy, (x, y) ∈ JSTS → (x, y) ∈ DTS)
    (hEnc_spec : ∀ x : ιx, (∃ m : M, (x, c m) ∈ JSTS) → (x, c (enc x)) ∈ JSTS) :
    Q.real {x : ιx | (x, c (enc x)) ∉ DTS}
      ≤ Q.real {x : ιx | x ∉ T_X}
        + Q.real {x : ιx | x ∈ T_X ∧ ¬ ∃ m : M, (x, c m) ∈ JSTS} :=
  measureReal_le_add_measureReal_of_subset_union Q
    (encoderFailure_subset_notTypical_union_noMatch T_X DTS JSTS c enc
      hJTS_subset hEnc_spec)

lemma weightedSum_noMatch_le_of_typical
    {ιx M : Type*} [MeasurableSpace ιx] [Fintype M] [DecidableEq M] [MeasurableSpace M]
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (p : Measure γ) [IsProbabilityMeasure p]
    (Q : Measure ιx) [IsProbabilityMeasure Q]
    (T_X : Set ιx) (Match : (M → γ) → ιx → Prop)
    [∀ c, DecidablePred (fun x => Match c x)]
    (hMeas_x : ∀ c, MeasurableSet {x : ιx | x ∈ T_X ∧ ¬ Match c x})
    (hMeas_prod : MeasurableSet {q : (M → γ) × ιx | q.2 ∈ T_X ∧ ¬ Match q.1 q.2})
    (b : ℝ) (hb : 0 ≤ b)
    (h_typical : ∀ x ∈ T_X,
        (Measure.pi (fun _ : M => p)).real {c : M → γ | ¬ Match c x} ≤ b) :
    ∑ c : (M → γ), (Measure.pi (fun _ : M => p)).real {c}
        * Q.real {x : ιx | x ∈ T_X ∧ ¬ Match c x} ≤ b := by
  classical
  have h_section_bound := piMeasure_section_no_match_le_of_typical
    (M := M) p Match T_X b hb h_typical
  refine weightedSum_section_pred_le_of_section_measure_le
    (Measure.pi (fun _ : M => p)) Q
    (fun c x => x ∈ T_X ∧ ¬ Match c x)
    hMeas_x hMeas_prod b hb
    (fun x => by simpa using h_section_bound x)

lemma encoder_strong_failure_prob_le_rdAmbient
    (qStar : α × β → ℝ) (hqStar_simp : qStar ∈ stdSimplex ℝ (α × β))
    (hqStar_pos : ∀ p : α × β, 0 < qStar p)
    {ε_join ε_X δ_kl : ℝ}
    (hε_join_pos : 0 < ε_join) (hε_X_nn : 0 ≤ ε_X) (hε_X_lt : ε_X < ε_join)
    (hδ_kl_pos : 0 < δ_kl)
    (qZ_min : ℝ) (hqZ_min_pos : 0 < qZ_min)
    (hqZ_min_le : ∀ p : α × β,
        qZ_min ≤ (pmfToMeasure (α := α × β) qStar).real {p})
    (hδ_kl_dominates :
        8 * (Fintype.card α : ℝ) * (Fintype.card β : ℝ) * ε_X ^ 2
          ≤ δ_kl * qZ_min) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (M : ℕ) (x : Fin n → α),
      x ∈ stronglyTypicalSet (rdAmbient qStar) (iidXs (α := α) (β := β)) n ε_X →
    (Measure.pi (fun _ : Fin M =>
        Measure.pi (fun _ : Fin n =>
          (rdAmbient qStar).map (iidYs (α := α) (β := β) 0)))).real
      { c : Fin M → (Fin n → β) |
          ∀ m, (x, c m) ∉ jointStronglyTypicalSet (rdAmbient qStar)
              (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β)) n ε_join }
      ≤ Real.exp (-(M : ℝ) *
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
                  + δ_kl)))) := by
  haveI : IsProbabilityMeasure (pmfToMeasure (α := α × β) qStar) :=
    pmfToMeasure_isProbabilityMeasure hqStar_simp
  haveI : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hqStar_simp
  have hqStar_real_pos : ∀ p : α × β,
      0 < (pmfToMeasure (α := α × β) qStar).real {p} := by
    intro p
    rw [pmfToMeasure_real_singleton hqStar_simp]; exact hqStar_pos p
  have hposZ : ∀ p : α × β,
      0 < ((rdAmbient qStar).map
              (jointSequence (α := α) (β := β) iidXs iidYs 0)).real {p} := by
    intro p
    rw [rdAmbient_map_jointSequence qStar hqStar_simp]; exact hqStar_real_pos p
  have hposX : ∀ a : α,
      0 < ((rdAmbient qStar).map (iidXs (α := α) (β := β) 0)).real {a} :=
    fun a => iidAmbientJoint_iidXs_real_singleton_pos
      (pmfToMeasure (α := α × β) qStar) hqStar_real_pos a
  have hposY : ∀ b : β,
      0 < ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0)).real {b} :=
    fun b => iidAmbientJoint_iidYs_real_singleton_pos
      (pmfToMeasure (α := α × β) qStar) hqStar_real_pos b
  have hindepZ_pair : Pairwise fun i j =>
      jointSequence (α := α) (β := β) iidXs iidYs i ⟂ᵢ[rdAmbient qStar]
        jointSequence iidXs iidYs j := fun i j hij =>
    (iidAmbientJoint_iIndepFun_joint (pmfToMeasure (α := α × β) qStar)).indepFun hij
  have hidentZ : ∀ i, IdentDistrib
      (jointSequence (α := α) (β := β) iidXs iidYs i)
      (jointSequence iidXs iidYs 0) (rdAmbient qStar) (rdAmbient qStar) := fun i =>
    iidAmbientJoint_identDistrib_joint (pmfToMeasure (α := α × β) qStar) i
  have hmarg_X :
      ((rdAmbient qStar).map (jointSequence (α := α) (β := β) iidXs iidYs 0)).map
          Prod.fst
        = (rdAmbient qStar).map (iidXs (α := α) (β := β) 0) := by
    rw [rdAmbient_map_jointSequence qStar hqStar_simp,
        rdAmbient_map_iidXs qStar hqStar_simp]
  exact encoder_strong_failure_prob_le (rdAmbient qStar)
    (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β))
    measurable_iidXs measurable_iidYs hindepZ_pair hidentZ hposZ hposX hposY hmarg_X
    (by rw [rdAmbient_map_jointSequence qStar hqStar_simp,
            rdAmbient_map_iidYs qStar hqStar_simp])
    hε_join_pos hε_X_nn hε_X_lt hδ_kl_pos qZ_min hqZ_min_pos
    (by intro p; rw [rdAmbient_map_jointSequence qStar hqStar_simp]; exact hqZ_min_le p)
    hδ_kl_dominates

lemma weightedSum_encoderFailure_le_notTypical_add_bound
    {ιx M : Type*} [MeasurableSpace ιx] [Fintype M] [DecidableEq M] [MeasurableSpace M]
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (Q : Measure ιx) [IsProbabilityMeasure Q]
    (p : Measure γ) [IsProbabilityMeasure p]
    (T_X : Set ιx) (DTS JSTS : Set (ιx × γ))
    (enc : (M → γ) → ιx → M)
    (b : ℝ) (hb : 0 ≤ b)
    (hMeas_x : ∀ c : M → γ,
        MeasurableSet {x : ιx | x ∈ T_X ∧ ¬ ∃ m : M, (x, c m) ∈ JSTS})
    (hMeas_prod : MeasurableSet
        {q : (M → γ) × ιx | q.2 ∈ T_X ∧ ¬ ∃ m : M, (q.2, q.1 m) ∈ JSTS})
    (hJTS_subset : ∀ x : ιx, x ∈ T_X → ∀ y : γ, (x, y) ∈ JSTS → (x, y) ∈ DTS)
    (hEnc_spec : ∀ (c : M → γ) (x : ιx),
        (∃ m : M, (x, c m) ∈ JSTS) → (x, c (enc c x)) ∈ JSTS)
    (h_typical : ∀ x ∈ T_X,
        (Measure.pi (fun _ : M => p)).real
            {c : M → γ | ¬ ∃ m : M, (x, c m) ∈ JSTS} ≤ b) :
    ∑ c : M → γ, (Measure.pi (fun _ : M => p)).real {c}
        * Q.real {x : ιx | (x, c (enc c x)) ∉ DTS}
      ≤ Q.real {x : ιx | x ∉ T_X} + b := by
  classical
  refine weightedSum_fail_le_const_add_of_per_index_and_sum_bound
    (Measure.pi (fun _ : M => p))
    (fun c => Q.real {x : ιx | (x, c (enc c x)) ∉ DTS})
    (fun c => Q.real {x : ιx | x ∈ T_X ∧ ¬ ∃ m : M, (x, c m) ∈ JSTS})
    (Q.real {x : ιx | x ∉ T_X}) b
    (fun c => measureReal_encoderFailure_le_notTypical_add_noMatch
      Q T_X DTS JSTS c (enc c) hJTS_subset (hEnc_spec c)) ?_
  exact weightedSum_noMatch_le_of_typical p Q T_X
    (fun c x => ∃ m : M, (x, c m) ∈ JSTS) hMeas_x hMeas_prod b hb h_typical

lemma exp_neg_ceilExp_mul_tendsto_zero_of_lt
    (target : ℕ → ℝ) (R θ : ℝ) (hθ_lt : θ < R)
    (h_target_eq : ∀ n : ℕ, target n = Real.exp (-(n : ℝ) * θ)) :
    Filter.Tendsto
      (fun n : ℕ => Real.exp
        (-((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) * target n)))
      Filter.atTop (𝓝 0) := by
  refine exp_neg_tendsto_zero_of_tendsto_atTop ?_
  have h_base := ceil_exp_mul_exp_neg_tendsto_atTop (R := R) (θ := θ) hθ_lt
  refine h_base.congr (fun n => ?_)
  rw [h_target_eq n]

/-! ## Main probabilistic content: `codebookAvgFailureStrong → 0` -/

/-- **Main `tendsto_zero` for the strong-encoder failure sequence.**

Hypotheses:

* `hqStar_pos : ∀ p, 0 < qStar p` — strict positivity of `qStar` on `α × β`,
  required by `conditionalStronglyTypicalSlice_mass_ge`.
* Slack parameters `ε_X, ε_join, δ_kl` and the slack-budget hypotheses
  `h_rate_gap` (strict rate over `mutualInfoPmf` + slacks) and the bridge slacks
  for `jointStronglyTypicalSet ⊆ distortionTypicalSet`.

The proof is a conditional method-of-types AEP combined with joint strong
typicality. -/
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
  -- Sketch: `codebookAvgFailureStrong n ≤ P_X[X ∉ T*_X] + exp(-Mn · target n)`,
  -- where `Mn := ⌈exp(nR)⌉` and `target n := exp(-n·(I+slack))`. The first summand
  -- → 0 by AEP (`stronglyTypicalSet_prob_tendsto_one`); the second → 0 since
  -- `Mn · target n → ∞` (rate gap `h_rate_gap`). The failure event splits into
  -- `x ∉ T*_X` (AEP-suppressed) and `no strong-JT match` (Step B), the
  -- match-but-bad-distortion case being discharged by `h_jts_subset_dts`.
  -- The source product measure (per `n`).
  let P_X : (n : ℕ) → Measure (Fin n → α) := fun n =>
    Measure.pi (fun _ : Fin n => (rdAmbient qStar).map (iidXs (α := α) (β := β) 0))
  -- Step B: an `N₀` past which the codebook-level "no strong match" mass is
  -- exponentially small for `x ∈ T*_X`.
  obtain ⟨N_B, hN_B⟩ :=
    encoder_strong_failure_prob_le_rdAmbient qStar hqStar_simp hqStar_pos
      hε_join_pos hε_X_pos.le hε_X_lt_ε_join hδ_kl_pos qZ_min hqZ_min_pos
      hqZ_min_le hδ_kl_dominates
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
  set Mn : ℕ → ℕ := fun n => Nat.ceil (Real.exp ((n : ℝ) * R))
  have hMn_pos : ∀ n, 0 < Mn n :=
    fun n => Nat.ceil_pos.mpr (Real.exp_pos _)
  -- ## Step 1: P_X[X ∉ T*_X] → 0 via AEP on the strong typicality set.
  -- `μ {ω | jointRV iidXs n ω ∈ T*_X} → 1` (AEP).
  have h_aep := stronglyTypicalSet_prob_tendsto_one (rdAmbient qStar)
    (iidXs (α := α) (β := β)) measurable_iidXs hindepX_pair hidentX hε_X_pos
  -- Bridge AEP to `Measure.pi` form via `rdAmbient_block_law_iidXs`.
  have h_pi_compl_tendsto :
      Filter.Tendsto
        (fun n : ℕ => (P_X n).real
          {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                              (iidXs (α := α) (β := β)) n ε_X})
        Filter.atTop (𝓝 0) :=
    tendsto_measureReal_map_notMem_zero_of_tendsto_prob_one
      (rdAmbient qStar)
      (fun n => InformationTheory.Shannon.jointRV (iidXs (α := α) (β := β)) n)
      (fun n => InformationTheory.Shannon.measurable_jointRV
        (iidXs (α := α) (β := β)) measurable_iidXs n)
      (fun n => stronglyTypicalSet (rdAmbient qStar)
        (iidXs (α := α) (β := β)) n ε_X)
      (fun _ => (Set.toFinite _).measurableSet)
      P_X (fun n => rdAmbient_block_law_iidXs qStar hqStar_simp n)
      h_aep
  -- ## Step 2: rate-gap → `exp(-Mn · target_n) → 0`.
  have h_exp_neg_Mn_target_tendsto :
      Filter.Tendsto
        (fun n : ℕ => Real.exp (-((Mn n : ℝ) * target n)))
        Filter.atTop (𝓝 0) :=
    exp_neg_ceilExp_mul_tendsto_zero_of_lt target R I_plus_slack
      (by linarith) h_target_eq
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
    -- The source-block measure `p` and the codebook measure as a pi-product.
    set p : Measure (Fin n → β) :=
      Measure.pi (fun _ : Fin n => (rdAmbient qStar).map (iidYs (α := α) (β := β) 0))
      with hp_def
    haveI : IsProbabilityMeasure p := by rw [hp_def]; infer_instance
    have hW_eq_pi :
        codebookMeasure ((rdAmbient qStar).map (iidYs (α := α) (β := β) 0)) (Mn n) n
          = Measure.pi (fun _ : Fin (Mn n) => p) := by rw [hp_def]; rfl
    -- Step B reshaped: for `x ∈ T_X` the pi-measure of "no match" is ≤ target.
    have h_typical : ∀ x ∈ {x | x ∈ stronglyTypicalSet (rdAmbient qStar)
            (iidXs (α := α) (β := β)) n ε_X},
        (Measure.pi (fun _ : Fin (Mn n) => p)).real
            { c : Fin (Mn n) → (Fin n → β) |
                ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                    (rdAmbient qStar) (iidXs (α := α) (β := β))
                    (iidYs (α := α) (β := β)) n ε_join }
          ≤ Real.exp (-((Mn n : ℝ) * target n)) := by
      intro x hxTX
      have h_step_B := hN_B n hn_NB (Mn n) x hxTX
      have h_set_eq :
          { c : Fin (Mn n) → (Fin n → β) |
              ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                  (rdAmbient qStar) (iidXs (α := α) (β := β))
                  (iidYs (α := α) (β := β)) n ε_join }
            = { c : Fin (Mn n) → (Fin n → β) |
                ∀ m, (x, c m) ∉ jointStronglyTypicalSet
                    (rdAmbient qStar) (iidXs (α := α) (β := β))
                    (iidYs (α := α) (β := β)) n ε_join } := by
        ext c; simp [not_exists]
      rw [h_set_eq, show -((Mn n : ℝ) * target n) = -(Mn n : ℝ) * target n from by
        ring, htarget_def]
      exact h_step_B
    -- Rewrite the failure to the weighted-sum form, then apply the combined helper.
    show codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ ≤ _ + _
    rw [show codebookAvgFailureStrong qStar d R n ε_join ε_dist δ_typ
          = ∑ c : Codebook (Mn n) n β,
              (Measure.pi (fun _ : Fin (Mn n) => p)).real {c}
                * (P_X n).real {x : Fin n → α |
                    (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                              (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β))
                              (hMn_pos n) ε_join c x))
                      ∉ distortionTypicalSet (rdAmbient qStar)
                          (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β)) d n
                          ε_dist δ_typ}
        from by unfold codebookAvgFailureStrong; rw [hW_eq_pi]]
    exact weightedSum_encoderFailure_le_notTypical_add_bound (P_X n) p
      {x | x ∈ stronglyTypicalSet (rdAmbient qStar)
              (iidXs (α := α) (β := β)) n ε_X}
      (distortionTypicalSet (rdAmbient qStar) (iidXs (α := α) (β := β))
        (iidYs (α := α) (β := β)) d n ε_dist δ_typ)
      (jointStronglyTypicalSet (rdAmbient qStar) (iidXs (α := α) (β := β))
        (iidYs (α := α) (β := β)) n ε_join)
      (fun c => jointStronglyTypicalLossyEncoder (rdAmbient qStar)
        (iidXs (α := α) (β := β)) (iidYs (α := α) (β := β)) (hMn_pos n) ε_join c)
      (Real.exp (-((Mn n : ℝ) * target n))) (Real.exp_pos _).le
      (fun _ => (Set.toFinite _).measurableSet)
      (Set.toFinite _).measurableSet
      (fun x _ y hy => h_jts_subset_dts (n := n) hn_pos x y hy)
      (fun c x hex => jointStronglyTypicalLossyEncoder_spec_of_exists
        (rdAmbient qStar) (iidXs (α := α) (β := β))
        (iidYs (α := α) (β := β)) (hMn_pos n) ε_join c x hex)
      h_typical
  -- ## Step 4: the upper-bound sequence tends to `0`; squeeze gives the result.
  set upper : ℕ → ℝ := fun n => (P_X n).real
      {x : Fin n → α | x ∉ stronglyTypicalSet (rdAmbient qStar)
                          (iidXs (α := α) (β := β)) n ε_X}
    + Real.exp (-((Mn n : ℝ) * target n)) with hupper_def
  have h_sum_tendsto : Filter.Tendsto upper Filter.atTop (𝓝 0) := by
    rw [hupper_def]; simpa using h_pi_compl_tendsto.add h_exp_neg_Mn_target_tendsto
  refine Filter.Tendsto.squeeze' (g := fun _ => (0 : ℝ)) (h := upper)
    tendsto_const_nhds h_sum_tendsto
    (Filter.Eventually.of_forall (fun n =>
      codebookAvgFailureStrong_nonneg qStar d R n ε_join ε_dist δ_typ))
    h_pointwise_bound
end InformationTheory.Shannon
