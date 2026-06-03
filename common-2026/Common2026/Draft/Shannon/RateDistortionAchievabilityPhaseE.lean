import Common2026.Meta.EntryPoint
import Common2026.Shannon.RateDistortionAchievabilityPhaseD

/-!
# Rate-distortion achievability — Phase E MVP (main theorem, witness form)

[`docs/shannon/rate-distortion-achievability-plan.md`](../../../docs/shannon/rate-distortion-achievability-plan.md)

Phase E composes Phases B, C, D into the rate-distortion achievability main
theorem in **witness form**: the statement is parameterised by a feasible joint
pmf `qStar ∈ RDConstraint P_X_pmf d D` and a rate `R > mutualInfoPmf qStar`, instead
of the abstract `R(D) < R` form. This avoids the substantial infrastructure
needed for the entropy ↔ pmf bridge (`(HZ - HX - HY) = -mutualInfoPmf qStar`),
which is deferred.

Several other hypotheses are pass-through to avoid building the ambient
construction here:

* `μ, Xs, Ys` and their measurability / i.i.d. / identDistrib hypotheses.
* The entropy bridge `(HZ - HX - HY) = -mutualInfoPmf qStar` is *not* asserted
  here; instead we hypothesise the AEP bound directly in the form needed by
  Phase B-(c) `jointlyTypicalSet_indep_prob_ge`.
* The codebook-averaged source failure sequence tendsto zero is also a
  hypothesis (retreat D). The Phase D / C random-coding apparatus shows
  this for the canonical iid construction; we pass it through to keep the
  MVP file small.

## Statement shape

```lean
∃ N, ∀ n ≥ N, ∃ (M : ℕ) (_ : ⌈exp(nR)⌉ ≤ M) (c : LossyCode M n α β),
  c.expectedBlockDistortion (μ.map (Xs 0)) d ≤ D + ε'
```

with `ε' > 0` an arbitrary tolerance. Concretely we set `ε' = δ + bound`,
where `δ` is the distortion slack inside `distortionTypicalSet` and `bound` is
`distortionMax d · (codebook-averaged failure)` at large enough `n`.

## Proof structure

1. Choose `δ := ε' / 2` (so `δ > 0`).
2. Use the hypothesis `h_failure_tendsto_zero` to extract `N` such that for
   `n ≥ N` the codebook-averaged failure sequence is `≤ ε' / (2 · (distortionMax d + 1))`.
3. For each such `n`, apply Phase D.5 `source_avg_distortion_le_simpler`
   pointwise in `c`, then average over `codebookMeasure`. This gives a
   codebook-averaged distortion bound `≤ (𝔼d + δ) + distortionMax · failure_seq n`.
4. Apply Phase C.3 `exists_codebook_low_avg` (pigeonhole): there exists a
   deterministic codebook `c₀ : Codebook M_n n β` with the same bound.
5. Bundle `c₀` into a `LossyCode` via `lossyCodeOfCodebook`. Use the
   `𝔼d ≤ expectedDistortionPmf d qStar ≤ D` chain (via `h_dist_eq` +
   `qStar ∈ RDConstraint`) to conclude `≤ D + δ + dMax · (small) ≤ D + ε'`.
-/

namespace InformationTheory.Shannon

open Filter Topology MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding (Codebook codebookMeasure jointSequence
  jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ## Helper lemma — encoder-side failure event measurability is finite

(Already discharged inside `source_avg_distortion_le_simpler`; reproduced as a
named lemma for downstream reuse.) -/

/-- **Phase E (witness form, MVP).**

Given a feasible joint pmf `qStar ∈ RDConstraint P_X_pmf d D`, a rate
`R > mutualInfoPmf qStar`, and an ambient i.i.d. construction with the appropriate
random-coding failure decay, we produce for every sufficiently large `n` a
deterministic lossy code of size `⌈exp(nR)⌉` whose expected block distortion
is within `ε'` of `D`.

This is the witness-form variant of Cover-Thomas Theorem 10.2.1
(achievability half of the rate-distortion theorem). The full
`R > R(D) ⟹ achievability` form requires the entropy-pmf bridge and
ambient construction infrastructure, deferred to a later session.

Migration note (Phase 2.RD.3 of `ratedistortion-pgpc-sorry-migration-plan`):
The load-bearing hypotheses `h_codebook_avg_failure` (Phase C-style Fubini
bridge) and the random-coding failure sequence bundle (`failure_seq` +
`h_failure_nn` + `h_failure_tendsto_zero`) have been removed; they are the
mathematical core of random-coding achievability and must be closed by the
Phase E strong plan, not absorbed as preconditions. The passive ambient /
distortion-compatibility / slack hypotheses remain. Body retreated to `sorry`.

`@residual(plan:rate-distortion-achievability-phase-e-strong-plan)`

-/
@[entry_point]
theorem rate_distortion_achievability_witness_form
    -- Source distribution and witness on the pmf side.
    (P_X_pmf : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    (qStar : α × β → ℝ) (hqStar_mem : qStar ∈ RDConstraint P_X_pmf d D)
    {R : ℝ} (hI_lt_R : mutualInfoPmf qStar < R)
    {ε' : ℝ} (hε' : 0 < ε')
    -- Ambient probability space (pass-through).
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    -- Marginal compatibility: `μ.map (Xs 0)` is a probability measure on `α`.
    [IsProbabilityMeasure (μ.map (Xs 0))]
    [IsProbabilityMeasure (μ.map (Ys 0))]
    -- Distortion compatibility (pmf form ↔ measure form).
    (h_dist_eq : expectedJointDistortion μ (Xs 0) (Ys 0) d
                  = expectedDistortionPmf d qStar)
    (ε : ℝ) (δ_typ : ℝ) (hδ_typ : 0 ≤ δ_typ)
    -- Distortion slack: `δ_typ + expectedDistortionPmf d qStar ≤ D + ε' / 2`.
    (h_slack : expectedDistortionPmf d qStar + δ_typ ≤ D + ε' / 2) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion (μ.map (Xs 0)) d ≤ D + ε' := by
  sorry

/-
Original body (before Phase 2.RD.3 retreat) preserved for reference by the
closure plan `rate-distortion-achievability-phase-e-strong-plan`. The two
load-bearing hypotheses now retreated to `sorry` were:
  * `failure_seq` + `h_failure_nn` + `h_failure_tendsto_zero`
  * `h_codebook_avg_failure` (Phase C-style Fubini bridge)

  classical
  -- Notation.
  set dMax : ℝ := distortionMax d with hdMax_def
  have h_dMax_nn : 0 ≤ dMax := distortionMax_nonneg d
  -- Step 1: choose threshold so dMax · failure_seq n ≤ ε' / 2 for n ≥ N₀.
  have h_dMax_p1_pos : 0 < dMax + 1 := by linarith
  set η : ℝ := ε' / (2 * (dMax + 1)) with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  -- failure_seq → 0 means eventually < η.
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
  -- Use max(N, 1) to ensure 0 < n.
  refine ⟨max N 1, fun n hn => ?_⟩
  have hN_le : N ≤ n := le_of_max_le_left hn
  have h_n_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_of_max_le_right hn)
  have h_failure_n_lt : failure_seq n < η := hN n hN_le
  -- Step 2: choose M_n := ⌈exp(nR)⌉, which is ≥ 1.
  set Mn : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R)) with hMn_def
  have hMn_pos : 0 < Mn := by
    rw [hMn_def]
    have h_exp_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    exact Nat.ceil_pos.mpr h_exp_pos
  -- Step 3: apply Phase D.5 + Fubini to get codebook-averaged distortion bound.
  -- The codebook-averaged distortion bound is:
  --   ∑ c, w(c) * c.expectedBlockDistortion P_X^n d
  --     ≤ (expectedJointDistortion μ X Y d + δ_typ) + dMax * failure_seq n
  -- where w(c) = codebookMeasure (μ.map (Ys 0)) Mn n.
  -- Define the codebook-functional we'll pigeon-hole.
  set f : Codebook Mn n β → ℝ := fun c =>
    (lossyCodeOfCodebook μ Xs Ys hMn_pos ε c).expectedBlockDistortion
      (μ.map (Xs 0)) d with hf_def
  -- The pointwise (per-codebook) bound from Phase D.5.
  have h_per_codebook : ∀ c : Codebook Mn n β,
      f c ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ)
              + dMax *
                (Measure.pi (fun _ : Fin n => μ.map (Xs 0))).real
                  { x | (x, c (jointTypicalLossyEncoder μ Xs Ys hMn_pos ε c x))
                          ∉ distortionTypicalSet μ Xs Ys d n ε δ_typ } := by
    intro c
    have h := source_avg_distortion_le_simpler (μ := μ) (Xs := Xs) (Ys := Ys)
      (d := d) (hM := hMn_pos) (ε := ε) (δ := δ_typ) hδ_typ c
      (P_X := Measure.pi (fun _ : Fin n => μ.map (Xs 0)))
    -- Unfold f.
    show (lossyCodeOfCodebook μ Xs Ys hMn_pos ε c).expectedBlockDistortion
        (μ.map (Xs 0)) d ≤ _
    -- The expectedBlockDistortion of `lossyCodeOfCodebook` is exactly the integral.
    unfold LossyCode.expectedBlockDistortion lossyCodeOfCodebook
    exact h
  -- Sum over codebooks weighted by codebookMeasure.
  have h_codebook_meas_isProb :
      IsProbabilityMeasure (codebookMeasure (μ.map (Ys 0)) Mn n) :=
    codebookMeasure.instIsProbabilityMeasure (μ.map (Ys 0)) Mn n
  -- Sum-of-weights = 1.
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
  -- Apply pointwise bound term-by-term and use h_codebook_avg_failure.
  have h_avg_bound :
      ∑ c : Codebook Mn n β, (codebookMeasure (μ.map (Ys 0)) Mn n).real {c} * f c
        ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ) + dMax * failure_seq n := by
    -- Introduce shorter notation, fold in `h_per_codebook`.
    set Edδ : ℝ := expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ with hEdδ_def
    set fail : Codebook Mn n β → ℝ := fun c =>
      (Measure.pi (fun _ : Fin n => μ.map (Xs 0))).real
        { x | (x, c (jointTypicalLossyEncoder μ Xs Ys hMn_pos ε c x))
                ∉ distortionTypicalSet μ Xs Ys d n ε δ_typ } with hfail_def
    set W : Codebook Mn n β → ℝ :=
      fun c => (codebookMeasure (μ.map (Ys 0)) Mn n).real {c} with hW_def
    -- Fold the per-codebook bound under the new notation.
    have h_per_codebook' : ∀ c : Codebook Mn n β,
        f c ≤ Edδ + dMax * fail c := h_per_codebook
    have h_w_nn : ∀ c : Codebook Mn n β, 0 ≤ W c := fun _ => measureReal_nonneg
    -- Sum the per-codebook bound: weighted sum ≤ weighted (Edδ + dMax * fail).
    have h_step1 : ∑ c, W c * f c ≤ ∑ c, W c * (Edδ + dMax * fail c) := by
      refine Finset.sum_le_sum (fun c _ => ?_)
      exact mul_le_mul_of_nonneg_left (h_per_codebook' c) (h_w_nn c)
    -- Split the rhs sum.
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
    -- Apply Fubini hypothesis (under the new notation).
    have h_step3 : ∑ c, W c * fail c ≤ failure_seq n := by
      have h_app := h_codebook_avg_failure h_n_pos
      -- `h_app` has `Mn := Nat.ceil (Real.exp ((n : ℝ) * R))` baked in;
      -- our local `Mn` matches definitionally.
      convert h_app using 0
    -- Combine: ∑ W c * f c ≤ Edδ + dMax * failure_seq n.
    have h_step4 : dMax * ∑ c, W c * fail c ≤ dMax * failure_seq n :=
      mul_le_mul_of_nonneg_left h_step3 h_dMax_nn
    linarith [h_step1, h_step2.le]
  -- Step 4: pigeonhole — extract a deterministic codebook.
  obtain ⟨c₀, hc₀_le⟩ :=
    exists_codebook_low_avg (M := Mn) (n := n) (μ.map (Ys 0)) f h_avg_bound
  -- Step 5: bundle c₀ and convert the bound.
  refine ⟨Mn, le_refl _, lossyCodeOfCodebook μ Xs Ys hMn_pos ε c₀, ?_⟩
  -- The expectedBlockDistortion of the bundled code = f c₀ ≤ (𝔼d+δ) + dMax * failure_seq n.
  have hf_unfold : f c₀ =
      (lossyCodeOfCodebook μ Xs Ys hMn_pos ε c₀).expectedBlockDistortion
        (μ.map (Xs 0)) d := rfl
  -- We need: (lossyCodeOfCodebook ...).expectedBlockDistortion ≤ D + ε'
  -- Have: f c₀ ≤ (𝔼d+δ) + dMax * failure_seq n
  -- Now bound by D + ε'.
  -- 𝔼d = expectedDistortionPmf d qStar (by h_dist_eq)
  -- δ + 𝔼d ≤ D + ε'/2 (by h_slack)
  -- dMax * failure_seq n ≤ ε'/2 (by failure_seq n < η and choice of η)
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
      _ = ε' / 2 := by
          field_simp
  have h_dist_pmf_eq : expectedJointDistortion μ (Xs 0) (Ys 0) d
                        = expectedDistortionPmf d qStar := h_dist_eq
  -- final calc
  show (lossyCodeOfCodebook μ Xs Ys hMn_pos ε c₀).expectedBlockDistortion
      (μ.map (Xs 0)) d ≤ D + ε'
  calc (lossyCodeOfCodebook μ Xs Ys hMn_pos ε c₀).expectedBlockDistortion
        (μ.map (Xs 0)) d
      = f c₀ := rfl
    _ ≤ (expectedJointDistortion μ (Xs 0) (Ys 0) d + δ_typ) + dMax * failure_seq n :=
        hc₀_le
    _ = (expectedDistortionPmf d qStar + δ_typ) + dMax * failure_seq n := by
        rw [h_dist_pmf_eq]
    _ ≤ (D + ε' / 2) + ε' / 2 :=
        add_le_add h_slack h_failure_bound
    _ = D + ε' := by ring
-/

end InformationTheory.Shannon
