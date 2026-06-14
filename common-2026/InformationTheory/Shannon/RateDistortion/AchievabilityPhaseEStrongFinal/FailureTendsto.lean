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
    have h_base := tendsto_measureReal_compl_zero_of_tendsto_measure_one
      (rdAmbient qStar)
      (fun n => {ω | InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n ω
                ∈ stronglyTypicalSet (rdAmbient qStar)
                    (iidXs (α := α) (β := β)) n ε_X})
      h_meas h_aep
    refine h_base.congr (fun n => ?_)
    have h_set_eq :
        {ω | InformationTheory.Shannon.jointRV
              (iidXs (α := α) (β := β)) n ω
              ∉ stronglyTypicalSet (rdAmbient qStar)
                  (iidXs (α := α) (β := β)) n ε_X}
          = {ω | InformationTheory.Shannon.jointRV
                (iidXs (α := α) (β := β)) n ω
                ∈ stronglyTypicalSet (rdAmbient qStar)
                    (iidXs (α := α) (β := β)) n ε_X}ᶜ := by
      ext ω; simp
    rw [h_set_eq]
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
      haveI : IsProbabilityMeasure (P_X n) := by
        show IsProbabilityMeasure
          (Measure.pi (fun _ : Fin n =>
              (rdAmbient qStar).map (iidXs (α := α) (β := β) 0)))
        infer_instance
      exact measureReal_le_add_measureReal_of_subset_union (P_X n) hFc_subset
    -- Step b: ∑_c W{c}.real * fail_c c ≤ (P_X n).real notTX + ∑_c W{c}.real * Pr_X(Nc) (avg form).
    -- Use that ∑_c W{c}.real = 1 (W probability) for the notTX term.
    have hW_sum_one : ∑ c : Codebook (Mn n) n β, W.real {c} = 1 := by
      haveI : MeasurableSingletonClass (Codebook (Mn n) n β) :=
        Pi.instMeasurableSingletonClass
      exact sum_measureReal_singleton_univ_eq_one W
    have h_weighted_avg :
        ∑ c : Codebook (Mn n) n β, W.real {c} * fail_c c
          ≤ (P_X n).real notTX
            + ∑ c : Codebook (Mn n) n β,
                W.real {c} * (P_X n).real
                  { x : Fin n → α | x ∈ T_X ∧
                      ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                          (rdAmbient qStar) (iidXs (α := α) (β := β))
                          (iidYs (α := α) (β := β)) n ε_join } :=
      sum_weighted_le_const_add_sum_weighted_of_le_add
        (fun c => W.real {c}) fail_c
        (fun c => (P_X n).real
          { x : Fin n → α | x ∈ T_X ∧
              ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                  (rdAmbient qStar) (iidXs (α := α) (β := β))
                  (iidYs (α := α) (β := β)) n ε_join })
        ((P_X n).real notTX)
        (fun _ => measureReal_nonneg) hW_sum_one h_per_c_bound
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
        haveI : MeasurableSingletonClass (Codebook (Mn n) n β) :=
          Pi.instMeasurableSingletonClass
        have h_section : ∀ c : Codebook (Mn n) n β,
            (Prod.mk c ⁻¹' R_set)
              = { x : Fin n → α | x ∈ T_X ∧
                  ¬ ∃ m : Fin (Mn n), (x, c m) ∈ jointStronglyTypicalSet
                      (rdAmbient qStar) (iidXs (α := α) (β := β))
                      (iidYs (α := α) (β := β)) n ε_join } := by
          intro c; ext x; simp [hR_set_def]
        rw [measureReal_prod_eq_sum_measureReal_singleton_mul_measureReal_section
              W (P_X n) hR_set_meas]
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
            = ((P_X n).prod W).real (Prod.swap '' R_set) :=
        measureReal_prod_eq_measureReal_prod_swap_image W (P_X n) hR_set_meas
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
      haveI : IsProbabilityMeasure (P_X n) := by
        show IsProbabilityMeasure
          (Measure.pi (fun _ : Fin n =>
              (rdAmbient qStar).map (iidXs (α := α) (β := β) 0)))
        infer_instance
      have h_real_le :
          ((P_X n).prod W).real R_set' ≤ bound :=
        measureReal_prod_le_of_measure_section_le_ofReal
          (P_X n) W hR_set'_meas bound hbound_nn h_section_bound
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
end InformationTheory.Shannon
