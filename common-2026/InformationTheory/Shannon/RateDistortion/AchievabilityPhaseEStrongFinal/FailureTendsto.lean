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
            simp only [Prod.swap, Set.mem_preimage, Prod.mk.eta]
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
end InformationTheory.Shannon
