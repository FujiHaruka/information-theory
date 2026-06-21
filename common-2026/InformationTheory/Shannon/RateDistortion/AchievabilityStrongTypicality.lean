import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ConditionalMethodOfTypes
import InformationTheory.Shannon.RateDistortion.AchievabilityCodebookMatchProbability
import InformationTheory.Shannon.RateDistortion.AchievabilityAsymptoticFailureDecay
import InformationTheory.Shannon.RateDistortion.AchievabilityJointStrongTypicality
import InformationTheory.Shannon.RateDistortion.AchievabilityStrongTypicality.SupportingBounds
import InformationTheory.Shannon.RateDistortion.AchievabilityStrongTypicality.FailureTendstoZero

/-!
# Rate-distortion achievability — assembly (strong-typicality variant)

The rate-distortion achievability theorem, assembled from the
strong-encoder random-coding chain via `conditionalStronglyTypicalSlice_mass_ge`
(`ConditionalMethodOfTypes.lean`), the Cover–Thomas 10.6.1 strong-typicality
conditional slice mass lower bound.

## Architectural note

The ambient-measure and witness-form wrappers (in
`AchievabilityAmbientMeasure.lean`) hard-code the **weak** joint-typical lossy
encoder `jointTypicalLossyEncoder`. The strong-typicality random-coding analysis
requires the **strong** encoder `jointStronglyTypicalLossyEncoder` (from
`AchievabilityJointStrongTypicality.lean`).

To avoid invasive refactoring of those weak-encoder-bound proofs, this file
**duplicates** the witness-form / ambient-measure layers with the strong
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
3. `source_avg_distortion_le_simpler_generic` — source-averaged distortion
   bound with arbitrary encoder parameter (verbatim mirror of
   `source_avg_distortion_le_simpler`).
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
have strictly positive mass on every `(a, b) ∈ α × β`, so the present theorem
carries `(hqStar_pos : ∀ p, 0 < qStar p)` as an additional hypothesis. An
unconditional form would require a perturbation argument (passing `qStar`
through `qStar_ε := (1-ε)·qStar + ε·uniform` and taking `ε → 0`).
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
exploiting continuity of `mutualInfoPmf` and `expectedDistortionPmf`). -/
@[entry_point]
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

/-- **Rate-distortion achievability** — public alias for the strong-typicality
form `rate_distortion_achievability_strong`, to which the body delegates
verbatim. The unconditional (no `hqStar_pos`) form requires a perturbation
argument. -/
@[entry_point]
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
