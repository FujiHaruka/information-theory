import Common2026.Meta.EntryPoint
import Common2026.Shannon.ParallelGaussian
import Common2026.Draft.Shannon.ParallelGaussianPerCoord
import Common2026.Draft.Shannon.ContChannelMIDecomp
import Common2026.Draft.Shannon.MultivariateDiffEntropy
import Common2026.Shannon.DifferentialEntropy
import Common2026.Draft.Shannon.AwgnCapacityConverseMaxent
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# ② parallel-gaussian converse closure (correlated input)

[parallel-gaussian-converse-closure-plan.md](../../docs/shannon/parallel-gaussian-converse-closure-plan.md).

This file supplies the genuine converse pieces for
`ParallelGaussianPerCoordRegularity.isParallelGaussianPerCoordRegularity_of_pieces`
(`bddAbove` / `max_ent` fields), lifting the 1-D AWGN converse template
(`awgn_per_input_mi_le_log`, `@audit:ok`) to the `Fin n → ℝ` parallel channel.

Genuine (sorryAx-free): Phase 2 decomposition lift
(`parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub`, with generic
`{α β}` core `mutualInfoOfChannel_toReal_eq_neg_integral_log_sub`); Phase 5
`bddAbove` reduction (`parallel_bddAbove_miImage`, modulo the Phase 3 split).

Remaining (1 `sorry`): Phase 3 `parallel_per_input_mi_le_sum` (per-coord
max-entropy + variance allocation on correlated inputs) carries
`@residual(plan:parallel-gaussian-converse-closure-plan)`. Reclassified from
`wall:multivariate-mi` to `plan:…` per the inventory's self-buildable verdict.

Status: type-check done (tier 2), NOT proof done (1 `sorry`).
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open Common2026.Shannon
open scoped ENNReal NNReal BigOperators

/-! ## M0 — `CountableOrCountablyGenerated` instance check (transient) -/

example {n : ℕ} :
    MeasurableSpace.CountableOrCountablyGenerated (Fin n → ℝ) (Fin n → ℝ) := by
  infer_instance

/-! ## Phase 2 — channel↔RV MI decomposition, generic lift

The 1-D `ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub` is
hardwired to `Measure ℝ` / `differentialEntropy`. We re-derive the same chain over
a generic measurable space `β` (with a `SigmaFinite` reference measure `vol`),
producing the entropy in raw `∫ log(rnDeriv) ∂` form, then specialize to
`β = Fin n → ℝ`, `vol = volume`. Every step uses only generic Mathlib / Common2026
lemmas (`InformationTheory.toReal_klDiv_of_measure_eq`, `rnDeriv_compProd_fibre`,
`integral_log_rnDeriv_self_eq_neg`), so the lift is mechanical. -/

section GenericDecomp

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {p : Measure α} [IsProbabilityMeasure p]
variable {W : Channel α β} [IsMarkovKernel W]
variable {vol : Measure β} [SigmaFinite vol]

/-- **Generic per-measure log-density split** (Bayes step). Mirror of
`ContChannelMIDecomp.log_rnDeriv_split` over an arbitrary measurable space with a
`SigmaFinite` reference measure `vol`. -/
private theorem log_rnDeriv_split_gen
    {ν q : Measure β} [SigmaFinite ν] [SigmaFinite q]
    (hνq : ν ≪ q) (hq_vol : q ≪ vol) :
    (fun y => Real.log ((ν.rnDeriv q y).toReal))
      =ᵐ[ν]
    (fun y => Real.log ((ν.rnDeriv vol y).toReal)
                - Real.log ((q.rnDeriv vol y).toReal)) := by
  have h_chain : (fun y => ν.rnDeriv q y * q.rnDeriv vol y)
      =ᵐ[ν] ν.rnDeriv vol :=
    hνq.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ := ν) (ν := q) (κ := vol) hq_vol)
  have h_pos_νq : ∀ᵐ y ∂ν, 0 < ν.rnDeriv q y := Measure.rnDeriv_pos hνq
  have h_lt_νq : ∀ᵐ y ∂ν, ν.rnDeriv q y < ∞ := hνq.ae_le (Measure.rnDeriv_lt_top ν q)
  have h_pos_q : ∀ᵐ y ∂ν, 0 < q.rnDeriv vol y := hνq.ae_le (Measure.rnDeriv_pos hq_vol)
  have h_lt_q : ∀ᵐ y ∂ν, q.rnDeriv vol y < ∞ :=
    hνq.ae_le (hq_vol.ae_le (Measure.rnDeriv_lt_top q vol))
  filter_upwards [h_chain, h_pos_νq, h_lt_νq, h_pos_q, h_lt_q]
    with y hy hpos1 hlt1 hpos2 hlt2
  have hne1 : ((ν.rnDeriv q y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos1.ne' hlt1.ne).ne'
  have hne2 : ((q.rnDeriv vol y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos2.ne' hlt2.ne).ne'
  rw [← hy, ENNReal.toReal_mul, Real.log_mul hne1 hne2]
  ring

/-- **Generic Bayes density split of the joint llr.** Mirror of
`ContChannelMIDecomp.llr_compProd_prod_split` over `α β` with `vol`. -/
private theorem llr_compProd_prod_split_gen
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (q : Measure β) [IsProbabilityMeasure q]
    (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ vol)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv vol y) =ᵐ[W x] fun y => g (x, y)) :
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log (g z).toReal
                - Real.log (q.rnDeriv vol z.2).toReal) := by
  have h_prod : p.prod q = p ⊗ₘ (Kernel.const α q) := (Measure.compProd_const).symm
  have h_ac' : (p ⊗ₘ W) ≪ p ⊗ₘ (Kernel.const α q) := by rwa [h_prod] at h_joint_ac
  have h1 : (p ⊗ₘ W).rnDeriv (p.prod q)
      =ᵐ[p ⊗ₘ W] fun z => Kernel.rnDeriv W (Kernel.const α q) z.1 z.2 := by
    rw [h_prod]
    exact h_ac'.ae_le (rnDeriv_compProd_fibre h_ac')
  have h_split : (fun z => Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal)
      =ᵐ[p ⊗ₘ W] fun z => Real.log (g z).toReal
                  - Real.log (q.rnDeriv vol z.2).toReal := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const α q)).ennreal_toReal.log
      · exact (hg_meas.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q vol).comp measurable_snd).ennreal_toReal.log)
    · filter_upwards with a
      have hker : (fun b => Kernel.rnDeriv W (Kernel.const α q) a b)
          =ᵐ[W a] fun b => (W a).rnDeriv q b := by
        have := (hWx_q a).ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := W) (η := Kernel.const α q) (a := a))
        simpa only [Kernel.const_apply] using this
      filter_upwards [hker, log_rnDeriv_split_gen (vol := vol) (hWx_q a) hq_vol, hg_ae a]
        with b hb hb_split hg_b
      rw [hb, hb_split, hg_b]
  have h_llr_eq : (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
      fun z => Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal := by
    simp only [llr_def]
    filter_upwards [h1] with z hz1
    rw [hz1]
  exact h_llr_eq.trans h_split

/-- **Generic continuous-channel MI chain rule** (entropy in raw integral form).
`(mutualInfoOfChannel p W).toReal = (−∫_y log(dq/dvol) ∂q) − ∫_x (−∫_y log(d(Wx)/dvol) ∂(Wx)) dp`.
Specialized below to `jointDifferentialEntropyPi` via `integral_log_rnDeriv_self_eq_neg`. -/
private theorem mutualInfoOfChannel_toReal_eq_neg_integral_log_sub
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (hW_ac : ∀ x, W x ≪ vol)
    (hWx_q : ∀ x, W x ≪ outputDistribution p W)
    (hq_ac : outputDistribution p W ≪ vol)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv vol y) =ᵐ[W x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z : α × β => Real.log (g z).toReal) (p ⊗ₘ W))
    (h_int_out : Integrable
        (fun z : α × β => Real.log
            ((outputDistribution p W).rnDeriv vol z.2).toReal) (p ⊗ₘ W)) :
    (mutualInfoOfChannel p W).toReal
      = (-∫ y, Real.log ((outputDistribution p W).rnDeriv vol y).toReal
            ∂(outputDistribution p W))
        - ∫ x, (-∫ y, Real.log ((W x).rnDeriv vol y).toReal ∂(W x)) ∂p := by
  set q := outputDistribution p W with hq_def
  have hq_vol : q ≪ vol := hq_ac
  have h_kl :
      (mutualInfoOfChannel p W).toReal
        = ∫ z, llr (p ⊗ₘ W) (p.prod q) z ∂(p ⊗ₘ W) := by
    rw [mutualInfoOfChannel_def, jointDistribution_def]
    refine InformationTheory.toReal_klDiv_of_measure_eq h_joint_ac ?_
    rw [measure_univ, measure_univ]
  rw [h_kl]
  rw [integral_congr_ae
        (llr_compProd_prod_split_gen (vol := vol) (p := p) (W := W)
          q hWx_q hq_vol h_joint_ac g hg_meas hg_ae)]
  rw [integral_sub h_int_fibre h_int_out]
  -- fibre term: ∫_z log(g z) ∂(p⊗ₘW) = ∫_x (∫_y log(g(x,y)) ∂(Wx)) dp
  --   = ∫_x (∫_y log(d(Wx)/dvol) ∂(Wx)) dp
  have h_fibre :
      (∫ z, Real.log (g z).toReal ∂(p ⊗ₘ W))
        = ∫ x, (∫ y, Real.log ((W x).rnDeriv vol y).toReal ∂(W x)) ∂p := by
    rw [Measure.integral_compProd h_int_fibre]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine integral_congr_ae ?_
    filter_upwards [hg_ae x] with y hy
    rw [hy]
  -- output term: ∫_z log(dq/dvol z.2) ∂(p⊗ₘW) = ∫_y log(dq/dvol y) ∂q
  have h_out :
      (∫ z, Real.log (q.rnDeriv vol z.2).toReal ∂(p ⊗ₘ W))
        = ∫ y, Real.log (q.rnDeriv vol y).toReal ∂q := by
    -- `q = (p ⊗ₘ W).map Prod.snd` definitionally; push the marginal integral back to
    -- the joint via `integral_map`, keeping `q` fixed inside the density.
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    set F : β → ℝ := fun y => Real.log (q.rnDeriv vol y).toReal with hF
    have hF_meas : AEStronglyMeasurable F q :=
      ((Measure.measurable_rnDeriv q vol).ennreal_toReal.log).aestronglyMeasurable
    have hF_meas' : AEStronglyMeasurable F ((p ⊗ₘ W).map Prod.snd) := by
      rw [← h_eq]; exact hF_meas
    calc (∫ z, F z.2 ∂(p ⊗ₘ W))
        = ∫ y, F y ∂((p ⊗ₘ W).map Prod.snd) :=
          (MeasureTheory.integral_map measurable_snd.aemeasurable hF_meas').symm
      _ = ∫ y, F y ∂q := by rw [← h_eq]
  rw [h_fibre, h_out, integral_neg]
  ring

end GenericDecomp

/-- **#1 channel↔RV MI decomposition, `Fin n → ℝ` lift.** (Plan Phase 2 / inventory §B)
Specializes the generic chain rule to `β = Fin n → ℝ`, `vol = volume`, producing the
entropy in `jointDifferentialEntropyPi` form via the generic
`integral_log_rnDeriv_self_eq_neg` bridge. The regularity / integrability
hypotheses (absolute continuity + log-density integrability of the correlated output
law) are genuine preconditions supplied by Phase 1. -/
theorem parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub {n : ℕ}
    (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hW_ac : ∀ x, (parallelGaussianChannel N h_meas h_parallel_meas) x ≪ volume)
    (hWx_q : ∀ x, (parallelGaussianChannel N h_meas h_parallel_meas) x
        ≪ outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
    (hq_ac : outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) ≪ volume)
    (h_joint_ac : (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas))
        ≪ p.prod (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)))
    (g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => ((parallelGaussianChannel N h_meas h_parallel_meas) x).rnDeriv volume y)
        =ᵐ[(parallelGaussianChannel N h_meas h_parallel_meas) x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z => Real.log (g z).toReal)
        (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas)))
    (h_int_out : Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Real.log
            ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).rnDeriv
              volume z.2).toReal)
        (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas))) :
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = jointDifferentialEntropyPi
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
        - ∫ x, jointDifferentialEntropyPi
            ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p := by
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  set q := outputDistribution p W with hq
  have h_raw := mutualInfoOfChannel_toReal_eq_neg_integral_log_sub
    (vol := (volume : Measure (Fin n → ℝ))) (p := p) (W := W)
    hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out
  rw [h_raw]
  -- bridge each raw `−∫ log(rnDeriv) ∂` to `jointDifferentialEntropyPi` via the
  -- generic `∫ log(dμ/dν) ∂μ = −∫ negMulLog(dμ/dν) ∂ν` identity.
  have h_out_bridge :
      (-∫ y, Real.log (q.rnDeriv volume y).toReal ∂q)
        = jointDifferentialEntropyPi q := by
    rw [integral_log_rnDeriv_self_eq_neg hq_ac, neg_neg]
    rfl
  have h_fibre_bridge : ∀ x,
      (-∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x))
        = jointDifferentialEntropyPi (W x) := by
    intro x
    rw [integral_log_rnDeriv_self_eq_neg (hW_ac x), neg_neg]
    rfl
  rw [h_out_bridge]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact h_fibre_bridge x

/-! ## Phase 3 — per-coord max-entropy converse split -/

/-- **#2 per-coord max-entropy converse split (correlated input).** (Plan Phase 3 / inventory §C)
@residual(plan:parallel-gaussian-converse-closure-plan) -/
theorem parallel_per_input_mi_le_sum {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
      (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ)) := by
  sorry

/-! ## Phase 5 — `bddAbove` field (genuine, from the Phase 3 converse split) -/

/-- **#4 `BddAbove (miImage P N …)`** (Plan Phase 5 / inventory §E #4). Every MI value
of a feasible (correlated) input is bounded by the *constant* `p`-independent
water-filling sum `∑ᵢ (1/2) log(1 + P/Nᵢ)`: the Phase 3 split returns a feasible `P'`
with `0 ≤ P'ᵢ` and `∑P'ᵢ ≤ P`, so `P'ᵢ ≤ P` coordinate-wise and `log` monotonicity
caps each term. Genuine modulo the Phase 3 converse split. -/
theorem parallel_bddAbove_miImage {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    BddAbove (miImage P N h_meas h_parallel_meas) := by
  -- constant upper bound: `C := ∑ᵢ (1/2) log(1 + P/Nᵢ)`
  refine ⟨∑ i : Fin n, (1/2) * Real.log (1 + P / (N i : ℝ)), ?_⟩
  rintro y ⟨p, hp_mem, rfl⟩
  -- `p` is a probability measure (set membership)
  have hp_prob : IsProbabilityMeasure p := hp_mem.1
  obtain ⟨P', hP'_nn, hP'_sum, hP'_le⟩ :=
    parallel_per_input_mi_le_sum P N hN h_meas h_parallel_meas p hp_mem
  refine hP'_le.trans ?_
  -- each P'ᵢ ≤ ∑P'ⱼ ≤ P, hence the term-wise log bound
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hNi_pos : (0 : ℝ) < (N i : ℝ) :=
    lt_of_le_of_ne (N i).coe_nonneg (Ne.symm (hN i))
  have hP'i_le_P : P' i ≤ P :=
    le_trans (Finset.single_le_sum (fun j _ => hP'_nn j) (Finset.mem_univ i)) hP'_sum
  have h_arg_pos : (0 : ℝ) < 1 + P' i / (N i : ℝ) := by
    have : (0 : ℝ) ≤ P' i / (N i : ℝ) := div_nonneg (hP'_nn i) hNi_pos.le
    linarith
  have h_arg_le : 1 + P' i / (N i : ℝ) ≤ 1 + P / (N i : ℝ) := by
    gcongr
  have h_log_le : Real.log (1 + P' i / (N i : ℝ)) ≤ Real.log (1 + P / (N i : ℝ)) :=
    Real.log_le_log h_arg_pos h_arg_le
  linarith [h_log_le]

end InformationTheory.Shannon.ParallelGaussian
