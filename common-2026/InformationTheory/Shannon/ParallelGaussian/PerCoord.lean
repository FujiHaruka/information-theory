import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.Basic
import InformationTheory.Shannon.ParallelGaussian.KKT
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp
import InformationTheory.Shannon.AWGN.MIClosedForm
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.ChannelCoding.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Parallel Gaussian capacity equals the water-filling sum

The per-coordinate water-filling reduction: the parallel Gaussian information capacity
`parallelGaussianCapacity P N` equals the per-coordinate water-filling sum, evaluated as a
sup-sandwich mirroring the single-coordinate `AWGN.awgnCapacity_eq`.

## Main definitions

* `miImage P N` — the mutual-information image whose `sSup` is the capacity.
* `gaussianProductInput Q` — the independent-Gaussian product input with per-coordinate
  power `Q i`, used as the achiever.
* `IsParallelGaussianPerCoordRegularity P N Q` — the analytic regularity bundle the
  sup-sandwich consumes (boundedness, achiever MI value, correlated-input max-entropy
  bound), mirroring the residual hypotheses of the 1-D `awgnCapacity_eq`.

## Main statements

* `parallel_gaussian_capacity_formula` — the capacity equals the water-filling sum
  (Cover–Thomas, Theorem 9.4.1), derived as `le_antisymm` of the achiever lower bound
  `parallelGaussianCapacity_ge_sum` and the max-entropy upper bound
  `parallelGaussianCapacity_le_sum`.
* `parallelGaussianCapacity_achiever_mi` — the product-Gaussian achiever attains the
  per-coordinate sum, via the per-channel mutual-information decomposition
  `parallelGaussian_achiever_mi_eq_sum_perChannel` and the per-coordinate AWGN closed form.
* `lintegral_fin_nat_prod_eq_prod` — the `ℝ≥0∞` analogue of `n`-variate Fubini.

## Implementation notes

The capacity is an information capacity (a `sSup` of mutual information), so it is evaluated
directly by `le_antisymm`: the achiever lower bound uses `le_csSup`, the upper bound uses
`csSup_le`. The achiever MI decomposition rests on the `compProd`-of-`Measure.pi`
factorization `gaussianProductInput_compProd_parallelGaussianChannel_eq_pi`, self-built via
`Measure.pi_eq` and the multivariate Tonelli lemma `lintegral_fin_nat_prod_eq_prod`.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

/-- The MI image whose `sSup` defines `parallelGaussianCapacity`. -/
noncomputable def miImage {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) : Set ℝ :=
  (fun p : Measure (Fin n → ℝ) =>
        (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal) ''
      parallelGaussianPowerConstraintSet P

lemma parallelGaussianCapacity_eq_sSup_miImage {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = sSup (miImage P N h_meas h_parallel_meas) := rfl

/-! ## Achiever: the independent Gaussian product input -/

/-- The independent-Gaussian product input with per-coordinate power `Q i`. -/
noncomputable def gaussianProductInput {n : ℕ} (Q : Fin n → ℝ≥0) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal 0 (Q i))

instance gaussianProductInput.instIsProbabilityMeasure {n : ℕ} (Q : Fin n → ℝ≥0) :
    IsProbabilityMeasure (gaussianProductInput Q) := by
  unfold gaussianProductInput; infer_instance

/-- The achiever's per-coordinate second moment: `∫ xᵢ² ∂(gaussianProductInput Q) = Q i`. -/
lemma integral_sq_gaussianProductInput {n : ℕ} (Q : Fin n → ℝ≥0) (i : Fin n) :
    ∫ x : Fin n → ℝ, (x i)^2 ∂(gaussianProductInput Q) = (Q i : ℝ) := by
  unfold gaussianProductInput
  -- reduce to the i-th Gaussian factor via `integral_eval`
  have h_sq_meas : AEStronglyMeasurable (fun y : ℝ => y ^ 2)
      (gaussianReal 0 (Q i)) := (measurable_id.pow_const 2).aestronglyMeasurable
  have h_eval :
      ∫ x : Fin n → ℝ, (fun y : ℝ => y ^ 2) (x i) ∂(Measure.pi fun j => gaussianReal 0 (Q j))
        = ∫ y, (fun y : ℝ => y ^ 2) y ∂(gaussianReal 0 (Q i)) :=
    MeasureTheory.integral_comp_eval
      (μ := fun j => gaussianReal 0 (Q j)) (i := i) (f := fun y : ℝ => y ^ 2) h_sq_meas
  rw [show (∫ x : Fin n → ℝ, (x i) ^ 2 ∂(Measure.pi fun j => gaussianReal 0 (Q j)))
        = ∫ x : Fin n → ℝ, (fun y : ℝ => y ^ 2) (x i)
            ∂(Measure.pi fun j => gaussianReal 0 (Q j)) from rfl, h_eval]
  simp only []
  -- ∫ y² ∂(gaussianReal 0 (Q i)) = Var = Q i
  have h_var : (Var[fun x : ℝ => x; gaussianReal 0 (Q i)] : ℝ) = (Q i : ℝ) :=
    variance_fun_id_gaussianReal
  have h_var_eq :
      (∫ x, (x - (0 : ℝ)) ^ 2 ∂(gaussianReal 0 (Q i)))
        = (Var[fun x : ℝ => x; gaussianReal 0 (Q i)] : ℝ) := by
    rw [variance_eq_integral measurable_id'.aemeasurable]
    congr 1
    rw [integral_id_gaussianReal]
  calc ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 (Q i))
      = ∫ x, (x - (0 : ℝ)) ^ 2 ∂(gaussianReal 0 (Q i)) := by simp
    _ = (Q i : ℝ) := by rw [h_var_eq, h_var]

/-- Achiever feasibility: if `∑ᵢ Q i ≤ P` then the product Gaussian input lies in
`parallelGaussianPowerConstraintSet P`.

@audit:ok -/
lemma gaussianProductInput_mem_constraintSet {n : ℕ} (P : ℝ) (Q : Fin n → ℝ≥0)
    (hQ : ∑ i : Fin n, (Q i : ℝ) ≤ P) :
    (gaussianProductInput Q) ∈ parallelGaussianPowerConstraintSet P := by
  refine ⟨inferInstance, ?_⟩
  -- per-coordinate integrability of (x i)² against the product Gaussian
  have h_int : ∀ i : Fin n,
      Integrable (fun x : Fin n → ℝ => (x i) ^ 2) (gaussianProductInput Q) := by
    intro i
    have h_int_i : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 (Q i)) :=
      (memLp_id_gaussianReal (μ := 0) (v := Q i) 2).integrable_sq
    -- `gaussianProductInput Q = Measure.pi (fun j => gaussianReal 0 (Q j))`
    show Integrable (fun x : Fin n → ℝ => (x i) ^ 2)
      (Measure.pi (fun j => gaussianReal 0 (Q j)))
    exact MeasureTheory.integrable_comp_eval (μ := fun j => gaussianReal 0 (Q j))
      (i := i) (f := fun y : ℝ => y ^ 2) h_int_i
  -- per-coordinate lintegral = ofReal (Q i)
  have h_nonneg : ∀ i : Fin n, 0 ≤ᵐ[gaussianProductInput Q] fun x : Fin n → ℝ => (x i) ^ 2 :=
    fun i => Filter.Eventually.of_forall (fun x => sq_nonneg (x i))
  have h_lint_each : ∀ i : Fin n,
      (∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂(gaussianProductInput Q))
        = ENNReal.ofReal (Q i : ℝ) := by
    intro i
    rw [← ofReal_integral_eq_lintegral_ofReal (h_int i) (h_nonneg i),
      integral_sq_gaussianProductInput Q i]
  -- ∑ ∫⁻ = ∑ ofReal(Q i) = ofReal(∑ Q i) ≤ ofReal P
  calc ∑ i : Fin n, ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂(gaussianProductInput Q)
      = ∑ i : Fin n, ENNReal.ofReal (Q i : ℝ) := Finset.sum_congr rfl (fun i _ => h_lint_each i)
    _ = ENNReal.ofReal (∑ i : Fin n, (Q i : ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ => (Q i).coe_nonneg)).symm
    _ ≤ ENNReal.ofReal P := ENNReal.ofReal_le_ofReal hQ

/-! ## Regularity bundle -/

/-- The analytic regularity bundle the sup-sandwich consumes, parameterized by the
achiever power split `Q`, mirroring the single-coordinate `AWGN.awgnCapacity_eq`
residuals. -/
structure IsParallelGaussianPerCoordRegularity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (Q : Fin n → ℝ≥0) :
    Prop where
  /-- The MI image is bounded above (needed for `le_csSup`). -/
  bddAbove : BddAbove (miImage P N h_meas h_parallel_meas)
  /-- The achiever MI value: the independent Gaussian input attains the per-coordinate
  sum `∑ᵢ (1/2) log(1 + Q i / Nᵢ)`. -/
  achiever_mi :
    (mutualInfoOfChannel (gaussianProductInput Q)
        (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = ∑ i : Fin n, (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ))
  /-- The correlated-input max-entropy upper bound: every constrained input has MI
  bounded by the per-coordinate sum evaluated at some feasible split `P'`. -/
  max_ent :
    ∀ p ∈ parallelGaussianPowerConstraintSet P,
      ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
        (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
          ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))

/-! ## Sup-sandwich -/

/-- **Lower bound (achiever).** The independent Gaussian product input is feasible and
achieves the per-coordinate sum, so the capacity is at least that sum (modulo the
`bddAbove` and `achiever_mi` fields of the regularity bundle). -/
theorem parallelGaussianCapacity_ge_sum {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (Q : Fin n → ℝ≥0) (hQ : ∑ i : Fin n, (Q i : ℝ) ≤ P)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q) :
    (∑ i : Fin n, (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)))
      ≤ parallelGaussianCapacity P N h_meas h_parallel_meas := by
  rw [parallelGaussianCapacity_eq_sSup_miImage]
  -- the achiever is feasible and its MI value is the per-coord sum
  have h_mem := gaussianProductInput_mem_constraintSet P Q hQ
  rw [← h_reg.achiever_mi]
  refine le_csSup h_reg.bddAbove ?_
  exact ⟨gaussianProductInput Q, h_mem, rfl⟩

/-- **Upper bound (max-entropy and water-filling).** Every constrained input has MI bounded
by the water-filling sum, via the per-coordinate max-entropy bound (`max_ent` field)
followed by water-filling optimality (`h_opt`). -/
theorem parallelGaussianCapacity_le_sum {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (Q : Fin n → ℝ≥0) (hQ : ∑ i : Fin n, (Q i : ℝ) ≤ P)
    (ν : ℝ) (h_opt : IsWaterFillingOptimal P N ν)
    (h_Q_eq : ∀ i, (Q i : ℝ) = waterFillingPower ν N i)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas Q) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      ≤ ∑ i : Fin n, (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)) := by
  -- the water-filling sum, expressed via Q
  set RHS := ∑ i : Fin n, (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)) with hRHS
  have h_RHS_wf : RHS
      = ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
    rw [hRHS]; exact Finset.sum_congr rfl (fun i _ => by rw [h_Q_eq i])
  rw [parallelGaussianCapacity_eq_sSup_miImage]
  refine csSup_le ?_ ?_
  · -- image nonempty: the achiever is feasible
    exact ⟨_, gaussianProductInput Q, gaussianProductInput_mem_constraintSet P Q hQ, rfl⟩
  · -- every element ≤ RHS: max-entropy bound + water-filling optimality
    rintro y ⟨p, hp_mem, rfl⟩
    obtain ⟨P', hP'_nn, hP'_sum, hP'_le⟩ := h_reg.max_ent p hp_mem
    refine hP'_le.trans ?_
    rw [h_RHS_wf]
    exact h_opt P' hP'_nn hP'_sum

/-! ## `max_ent` via output-entropy subadditivity -/

open InformationTheory.Shannon in
/-- **`max_ent` from subadditivity.** With the channel MI written as `h(Yⁿ) - condTerm`
(`h_decomp`), output-entropy subadditivity `h(Yⁿ) ≤ ∑ h(Yᵢ)`
(`jointDifferentialEntropyPi_le_sum`) and the per-coordinate water-filling allocation
bound `h_perCoord` give `I ≤ ∑ᵢ (1/2) log(1 + P'ᵢ/Nᵢ)`. -/
theorem parallelGaussian_max_ent_le_of_subadditivity {n : ℕ}
    (μY : Measure (Fin n → ℝ)) [IsProbabilityMeasure μY]
    [∀ i, IsProbabilityMeasure (μY.map (fun z => z i))]
    (miReal condTerm : ℝ) (P' : Fin n → ℝ) (N : Fin n → ℝ≥0)
    -- (honest) channel↔RV multivariate MI decomposition  I = h(Yⁿ) − condTerm
    (h_decomp : miReal = jointDifferentialEntropyPi μY - condTerm)
    -- (genuine) subadditivity hypotheses for the output law
    (h_marg_ac : ∀ i, (μY.map (fun z => z i)) ≪ volume)
    (hμ_ac : μY ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μY ≪ Measure.pi (fun i => μY.map (fun z => z i)))
    (h_int_marg : ∀ i,
      Integrable (fun z => Real.log (((μY.map (fun z => z i)).rnDeriv volume (z i)).toReal)) μY)
    (h_int_joint :
      Integrable (fun z => Real.log ((μY.rnDeriv volume z).toReal)) μY)
    -- (honest) per-coord max-entropy + variance allocation:
    --   ∑ᵢ h(Yᵢ) − condTerm ≤ ∑ᵢ (1/2) log(1 + P'ᵢ/Nᵢ)
    (h_perCoord :
      (∑ i, differentialEntropy (μY.map (fun z => z i))) - condTerm
        ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))) :
    miReal ≤ ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ)) := by
  -- output-entropy subadditivity: h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)
  have h_subadd : jointDifferentialEntropyPi μY
      ≤ ∑ i, differentialEntropy (μY.map (fun z => z i)) :=
    jointDifferentialEntropyPi_le_sum h_marg_ac hμ_ac h_joint_ac h_int_joint h_int_marg
  -- I = h(Yⁿ) − condTerm ≤ ∑ h(Yᵢ) − condTerm ≤ ∑ (1/2) log(1 + P'ᵢ/Nᵢ)
  rw [h_decomp]
  refine le_trans ?_ h_perCoord
  linarith [h_subadd]

/-! ## Per-coordinate reduction -/

/-- The capacity equals the per-coordinate water-filling sum (the analytic regularity
hypotheses bundled in `IsParallelGaussianPerCoordRegularity`), as a `le_antisymm`
sup-sandwich. Inhabits `IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν`. -/
theorem isParallelGaussianPerCoordReduction_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas
              (fun i => (waterFillingPower ν N i).toNNReal)) :
    IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν := by
  -- water-filling optimality, derived from the KKT water level
  have h_opt : IsWaterFillingOptimal P N ν := isWaterFillingOptimal_of_kkt P hP N hN ν h_kkt
  set Q : Fin (n + 1) → ℝ≥0 := fun i => (waterFillingPower ν N i).toNNReal with hQ_def
  -- `(Q i : ℝ) = waterFillingPower ν N i` since the power is nonnegative
  have h_Q_eq : ∀ i, (Q i : ℝ) = waterFillingPower ν N i := fun i => by
    rw [hQ_def]; exact Real.coe_toNNReal _ (waterFillingPower_nonneg ν N i)
  -- the power budget is met (KKT: the water-filling sum equals P)
  have hQ_sum : ∑ i : Fin (n + 1), (Q i : ℝ) ≤ P := by
    have : ∑ i : Fin (n + 1), (Q i : ℝ)
        = ∑ i : Fin (n + 1), waterFillingPower ν N i :=
      Finset.sum_congr rfl (fun i _ => h_Q_eq i)
    rw [this, h_kkt]
  -- assemble the sup-sandwich
  unfold IsParallelGaussianPerCoordReduction
  have h_target_eq :
      (∑ i : Fin (n + 1), (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)))
        = ∑ i : Fin (n + 1), (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => by rw [h_Q_eq i])
  rw [h_target_eq]
  refine le_antisymm ?_ ?_
  · exact parallelGaussianCapacity_le_sum P N h_meas h_parallel_meas Q hQ_sum ν h_opt
      h_Q_eq h_reg
  · exact parallelGaussianCapacity_ge_sum P N h_meas h_parallel_meas Q hQ_sum h_reg

/-! ## Headline capacity formula -/

/-- **Parallel Gaussian capacity formula** (Cover–Thomas, Theorem 9.4.1). For parallel AWGN
channels `Y_i = X_i + Z_i`, `Z_i ∼ 𝒩(0, N_i)` (`i : Fin (n+1)`) under the total power
constraint `∑_i E[X_i²] ≤ P`, the information capacity equals the water-filling sum

`C = ∑_i (1/2) log(1 + max(0, ν - N_i) / N_i)`

at the KKT water level `ν`. The equality is derived via
`isParallelGaussianPerCoordReduction_discharged` (a `le_antisymm` sup-sandwich); the
hypotheses are the KKT budget condition `h_kkt` and the analytic regularity bundle
`h_reg`. Water-filling optimality is obtained internally from `h_kkt` rather than assumed. -/
theorem parallel_gaussian_capacity_formula {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas
              (fun i => (waterFillingPower ν N i).toNNReal)) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) :=
  isParallelGaussianPerCoordReduction_discharged P hP N hN h_meas h_parallel_meas
    ν h_kkt h_reg

/-! ## Achiever mutual-information decomposition -/

/-- The `ℝ≥0∞` analogue of `n`-variate Fubini: for a product measure `Measure.pi μ` over
`Fin n`, the integral of a product of single-coordinate functions equals the product of the
per-coordinate integrals (the `ℝ≥0∞` form of
`MeasureTheory.integral_fin_nat_prod_eq_prod`).

@audit:ok -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      have hg : Measurable (fun y : (i : Fin n) → E (Fin.succ i) =>
          ∏ i : Fin n, f (Fin.succ i) (y i)) :=
        Finset.measurable_prod _ (fun i _ => (hf _).comp (measurable_pi_apply i))
      calc
        ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
            = ∫⁻ z : E 0 × ((i : Fin n) → E (Fin.succ i)),
                f 0 z.1 * ∏ i : Fin n, f (Fin.succ i) (z.2 i)
                ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
              rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
                (MeasurableEquiv.measurableEmbedding _)]
              simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
                Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
                Fin.zero_succAbove, cast_eq, Fin.cons_zero]
              rfl
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∫⁻ y, (∏ i : Fin n, f (Fin.succ i) (y i)) ∂(Measure.pi (fun i ↦ μ i.succ)) :=
              lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i ↦ μ i.succ))
                (f := fun x => f 0 x)
                (g := fun y => ∏ i : Fin n, f (Fin.succ i) (y i))
                (hf 0).aemeasurable hg.aemeasurable
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
              rw [n_ih (fun i ↦ μ i.succ) (fun i ↦ f i.succ) (fun i ↦ hf _)]
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

open InformationTheory.Shannon InformationTheory.Shannon.AWGN in
/-- **compProd-of-`Measure.pi` factorization.** The channel joint
`gaussianProductInput Q ⊗ₘ parallelGaussianChannel N` factors as the `Measure.pi` of the
per-coordinate joints `gaussianReal 0 (Qᵢ) ⊗ₘ awgnChannel Nᵢ`, reshaped by
`arrowProdEquivProdArrow`.

@audit:ok -/
theorem gaussianProductInput_compProd_parallelGaussianChannel_eq_pi {n : ℕ}
    (Q : Fin n → ℝ≥0) (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    (gaussianProductInput Q) ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas)
      = (Measure.pi
          (fun i => (gaussianReal 0 (Q i)) ⊗ₘ (awgnChannel (N i) (h_meas i)))).map
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  set joints := fun i => (gaussianReal 0 (Q i)) ⊗ₘ (awgnChannel (N i) (h_meas i)) with hjoints
  -- It suffices to show `(compProd).map e.symm = Measure.pi joints`, transported by `e`.
  have hkey : ((gaussianProductInput Q) ⊗ₘ W).map e.symm = Measure.pi joints := by
    -- Characterize `Measure.pi joints` by its values on product boxes via `pi_eq`.
    refine (Measure.pi_eq (fun s hs => ?_)).symm
    -- LHS box value:
    -- `((compProd).map e.symm) (Set.pi univ s) = (compProd) (e.symm ⁻¹' (Set.pi univ s))`.
    have hbox_meas : MeasurableSet (Set.pi (Set.univ : Set (Fin n)) s) :=
      MeasurableSet.univ_pi hs
    rw [Measure.map_apply e.symm.measurable hbox_meas]
    -- The preimage is `{ω | ∀ i, (ω.1 i, ω.2 i) ∈ s i}`.
    have hpre : e.symm ⁻¹' (Set.pi Set.univ s)
        = {ω : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i, (ω.1 i, ω.2 i) ∈ s i} := by
      ext ω
      have hsymm : ∀ i, e.symm ω i = (ω.1 i, ω.2 i) := by
        intro i
        rw [he]
        rfl
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
        Set.mem_setOf_eq, hsymm]
    have hpre_meas : MeasurableSet
        {ω : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i, (ω.1 i, ω.2 i) ∈ s i} := by
      rw [← hpre]; exact e.symm.measurable hbox_meas
    rw [hpre]
    -- Apply general `compProd_apply`.
    rw [Measure.compProd_apply hpre_meas]
    -- The kernel fibre value:
    -- `W x (Prod.mk x ⁻¹' preimage) = ∏ i, gaussianReal (x i) (N i) (slice i)`.
    have hslice : ∀ x : Fin n → ℝ,
        (W x) (Prod.mk x ⁻¹' {ω : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i, (ω.1 i, ω.2 i) ∈ s i})
          = ∏ i, (gaussianReal (x i) (N i)) (Prod.mk (x i) ⁻¹' s i) := by
      intro x
      have hset : (Prod.mk x ⁻¹' {ω : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i, (ω.1 i, ω.2 i) ∈ s i})
          = Set.pi Set.univ (fun i => Prod.mk (x i) ⁻¹' s i) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
          forall_const]
      rw [hW, parallelGaussianChannel_apply, hset]
      exact Measure.pi_pi _ _
    simp_rw [hslice]
    -- Multivariate Tonelli over the product input.
    rw [show gaussianProductInput Q = Measure.pi (fun i => gaussianReal 0 (Q i)) from rfl]
    rw [lintegral_fin_nat_prod_eq_prod (fun i => gaussianReal 0 (Q i))
        (fun i y => (gaussianReal (y) (N i)) (Prod.mk y ⁻¹' s i)) ?_]
    swap
    · intro i
      have hm := ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
        (κ := awgnChannel (N i) (h_meas i)) (hs i)
      simp_rw [awgnChannel_apply] at hm
      exact hm
    -- Each factor equals the per-coordinate joint box value.
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hjoints]
    have : ((gaussianReal 0 (Q i)) ⊗ₘ (awgnChannel (N i) (h_meas i))) (s i)
        = ∫⁻ y, (awgnChannel (N i) (h_meas i)) y (Prod.mk y ⁻¹' s i)
            ∂(gaussianReal 0 (Q i)) :=
      Measure.compProd_apply (hs i)
    rw [this]
    refine lintegral_congr (fun y => ?_)
    rw [awgnChannel_apply]
  -- Transport `hkey` back through `e`.
  rw [← hkey, Measure.map_map e.measurable e.symm.measurable]
  simp

open InformationTheory.Shannon InformationTheory.Shannon.AWGN in
/-- **Per-channel MI decomposition of the product achiever.** The channel mutual
information of the independent-Gaussian product input through the parallel Gaussian channel
equals the sum of the per-coordinate single-channel mutual informations.

@audit:ok -/
theorem parallelGaussian_achiever_mi_eq_sum_perChannel_enn {n : ℕ}
    (Q : Fin n → ℝ≥0) (N : Fin n → ℝ≥0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    mutualInfoOfChannel (gaussianProductInput Q)
        (parallelGaussianChannel N h_meas h_parallel_meas)
      = ∑ i : Fin n,
          mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i)) := by
  classical
  set p := gaussianProductInput Q with hp
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  set joints := fun i => (gaussianReal 0 (Q i)) ⊗ₘ (awgnChannel (N i) (h_meas i)) with hjoints
  -- Move to the RV form on `Ω := (Fin n → ℝ) × (Fin n → ℝ)`.
  rw [mutualInfoOfChannel_eq_mutualInfo_prod p W]
  -- RV family: i-th input / output coordinate.
  set μ := jointDistribution p W with hμ
  set Xs : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun i ω => ω.1 i with hXs
  set Ys : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun i ω => ω.2 i with hYs
  have hXmeas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have hYmeas : ∀ i, Measurable (Ys i) := fun i =>
    (measurable_pi_apply i).comp measurable_snd
  -- `Prod.fst = fun ω i => Xs i ω` and `Prod.snd = fun ω i => Ys i ω`.
  have hfst : (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
      = fun ω i => Xs i ω := rfl
  have hsnd : (Prod.snd : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
      = fun ω i => Ys i ω := rfl
  rw [hfst, hsnd]
  -- The factorization: `μ = (Measure.pi joints).map e`.
  have hfac : μ = (Measure.pi joints).map
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) := by
    rw [hμ, jointDistribution_def, hp, hW, hjoints]
    exact gaussianProductInput_compProd_parallelGaussianChannel_eq_pi Q N h_meas h_parallel_meas
  haveI : ∀ i, IsProbabilityMeasure (joints i) := by
    rw [hjoints]; intro i; infer_instance
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he
  -- `(fun ω => (Xs i ω, Ys i ω)) ∘ e = Function.eval i` on `Fin n → ℝ × ℝ`.
  have hpair_eval : ∀ i, (fun ω : (Fin n → ℝ) × (Fin n → ℝ) => (Xs i ω, Ys i ω)) ∘ e
      = Function.eval i := by
    intro i; funext h; rfl
  -- Per-coordinate map facts under `μ`.
  have hmap_pair : ∀ i, μ.map (fun ω => (Xs i ω, Ys i ω)) = joints i := by
    intro i
    rw [hfac, Measure.map_map ((hXmeas i).prodMk (hYmeas i)) e.measurable, hpair_eval i]
    exact (measurePreserving_eval joints i).map_eq
  have hmap_X : ∀ i, μ.map (Xs i) = (joints i).map Prod.fst := by
    intro i
    rw [hfac, Measure.map_map (hXmeas i) e.measurable]
    have : (Xs i) ∘ e = Prod.fst ∘ Function.eval i := by funext h; rfl
    rw [this, ← Measure.map_map measurable_fst (measurable_pi_apply i),
      (measurePreserving_eval joints i).map_eq]
  have hmap_Y : ∀ i, μ.map (Ys i) = (joints i).map Prod.snd := by
    intro i
    rw [hfac, Measure.map_map (hYmeas i) e.measurable]
    have : (Ys i) ∘ e = Prod.snd ∘ Function.eval i := by funext h; rfl
    rw [this, ← Measure.map_map measurable_snd (measurable_pi_apply i),
      (measurePreserving_eval joints i).map_eq]
  -- The three i.i.d. factorization hypotheses, via `pi_map_pi` on the factorization.
  have h_iid_joint : μ.map (fun ω (i : Fin n) => (Xs i ω, Ys i ω))
      = Measure.pi (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))) := by
    rw [show (fun i => μ.map (fun ω => (Xs i ω, Ys i ω))) = joints from
      funext (fun i => hmap_pair i)]
    rw [hfac, Measure.map_map
        (measurable_pi_iff.mpr fun i => (hXmeas i).prodMk (hYmeas i)) e.measurable]
    rw [show ((fun ω (i : Fin n) => (Xs i ω, Ys i ω)) ∘ e)
          = (fun (h : Fin n → ℝ × ℝ) i => id (h i)) from rfl]
    rw [Measure.pi_map_pi (fun i => measurable_id.aemeasurable)]
    congr 1; funext i
    rw [Measure.map_id]
  have h_iid_X : μ.map (fun ω (i : Fin n) => Xs i ω)
      = Measure.pi (fun i => μ.map (Xs i)) := by
    rw [show (fun i => μ.map (Xs i)) = (fun i => (joints i).map Prod.fst) from
      funext (fun i => hmap_X i)]
    rw [hfac, Measure.map_map (measurable_pi_iff.mpr hXmeas) e.measurable]
    rw [show ((fun ω (i : Fin n) => Xs i ω) ∘ e)
          = (fun (h : Fin n → ℝ × ℝ) i => Prod.fst (h i)) from rfl]
    rw [Measure.pi_map_pi (fun i => measurable_fst.aemeasurable)]
  have h_iid_Y : μ.map (fun ω (i : Fin n) => Ys i ω)
      = Measure.pi (fun i => μ.map (Ys i)) := by
    rw [show (fun i => μ.map (Ys i)) = (fun i => (joints i).map Prod.snd) from
      funext (fun i => hmap_Y i)]
    rw [hfac, Measure.map_map (measurable_pi_iff.mpr hYmeas) e.measurable]
    rw [show ((fun ω (i : Fin n) => Ys i ω) ∘ e)
          = (fun (h : Fin n → ℝ × ℝ) i => Prod.snd (h i)) from rfl]
    rw [Measure.pi_map_pi (fun i => measurable_snd.aemeasurable)]
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  -- Apply the genuine RV-form additivity.
  rw [mutualInfo_pi_eq_sum μ Xs Ys hXmeas hYmeas h_iid_joint h_iid_X h_iid_Y]
  -- Identify each summand with the per-coordinate channel MI.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mutualInfoOfChannel_eq_mutualInfo_prod (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))]
  -- Both sides are `mutualInfo` of the same joint law and marginals.
  unfold InformationTheory.Shannon.mutualInfo
  rw [hmap_pair i, hmap_X i, hmap_Y i]
  congr 1
  · rw [hjoints, jointDistribution_def]
    have : (fun z : ℝ × ℝ => (z.1, z.2)) = id := by funext z; rfl
    rw [this, Measure.map_id]

open InformationTheory.Shannon InformationTheory.Shannon.AWGN in
/-- **AWGN single-channel mutual information is finite.** The channel MI of the Gaussian
input through a single AWGN channel is a finite `ENNReal` (`≠ ⊤`), via `klDiv_ne_top`
applied to the joint `gaussianReal 0 P ⊗ₘ awgnChannel N` against the product of its
marginals (joint absolute continuity plus llr integrability via the Bayes split).

The `N ≠ 0` hypothesis is required: for `N = 0` the channel is deterministic
(`W x = dirac x`), the joint lives on the diagonal graph (`p.prod q`-null for a continuous
input `P ≠ 0`), and `klDiv = ⊤` — the claim is false there. -/
theorem awgn_mutualInfoOfChannel_ne_top (N : ℝ≥0) (hN : N ≠ 0)
    (h_meas : InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable N) (P : ℝ≥0) :
    mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N h_meas) ≠ ⊤ := by
  classical
  -- Reduce to `klDiv_ne_top` via the AWGN density facts already discharged in
  -- `ContChannelMIDecomp` (same assembly as `isContChannelMIDecompHyp_awgn`, but
  -- feeding `klDiv_ne_top` instead of the `.toReal` chain rule).
  -- Cast `P : ℝ≥0` to the `P.toNNReal` shape used by the supporting lemmas.
  have hP_cast : ((P : ℝ)).toNNReal = P := Real.toNNReal_coe
  rw [show (P : ℝ≥0) = ((P : ℝ)).toNNReal from hP_cast.symm]
  set Pr : ℝ := (P : ℝ) with hPr
  have hPN : Pr.toNNReal + N ≠ 0 := by
    rw [hPr, hP_cast]
    exact fun h => hN (by simpa using (add_eq_zero.mp h).2)
  set p := gaussianReal 0 Pr.toNNReal with hp_def
  set W := awgnChannel N h_meas with hW_def
  set q := outputDistribution p W with hq_def
  -- output Gaussian fact `q = gaussianReal 0 (P+N)`, discharged unconditionally.
  have h_out : InformationTheory.Shannon.AWGN.IsAwgnOutputGaussian Pr N h_meas :=
    InformationTheory.Shannon.AWGN.awgn_output_gaussian_of_bind_eq_conv Pr N h_meas
      (InformationTheory.Shannon.AWGN.isAwgnBindEqConv_discharged Pr N h_meas)
  -- measurable PDF proxy `g := gaussianPDF` for the fibre volume-density (Route B)
  set g : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF z.1 N z.2 with hg_def
  have hg_meas : Measurable g :=
    InformationTheory.Shannon.AWGN.measurable_gaussianPDF_uncurry N
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
    intro x
    rw [hW_def, awgnChannel_apply]
    exact (gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)
  have hq_prob : IsProbabilityMeasure q := by rw [hq_def, h_out]; infer_instance
  have hWx_q : ∀ x, W x ≪ q :=
    InformationTheory.Shannon.AWGN.awgnChannel_apply_absolutelyContinuous_output
      Pr N hN hPN h_meas h_out
  have hq_vol : q ≪ volume :=
    InformationTheory.Shannon.AWGN.awgn_output_absolutelyContinuous_of_outputGaussian
      Pr N hPN h_meas h_out
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod q := by
    rw [show p.prod q = p ⊗ₘ (Kernel.const ℝ q) from (Measure.compProd_const).symm]
    exact Measure.absolutelyContinuous_compProd_right_iff.mpr
      (Filter.Eventually.of_forall (fun x => by simpa only [Kernel.const_apply] using hWx_q x))
  -- llr split + fibre/output log-density integrabilities (analytic core, all existing)
  have h_llr_split := llr_compProd_prod_split (p := p) (W := W) q hWx_q hq_vol
    h_joint_ac g hg_meas hg_ae
  have h_int_fibre_joint :
      Integrable (fun z => Real.log (g z).toReal) (p ⊗ₘ W) :=
    integrable_log_proxy_fibre_compProd Pr N hN h_meas
  have h_int_out_marg :
      Integrable (fun y => Real.log (q.rnDeriv volume y).toReal) q := by
    rw [hq_def, h_out]
    exact integrable_log_rnDeriv_gaussianReal 0 hPN
  have h_int_out_joint :
      Integrable (fun z => Real.log (q.rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    have hg_aesm :
        AEStronglyMeasurable (fun y => Real.log (q.rnDeriv volume y).toReal) q :=
      h_int_out_marg.aestronglyMeasurable
    rw [show (fun z : ℝ × ℝ => Real.log (q.rnDeriv volume z.2).toReal)
          = (fun y => Real.log (q.rnDeriv volume y).toReal) ∘ Prod.snd from rfl]
    refine (integrable_map_measure ?_ measurable_snd.aemeasurable).mp ?_
    · rw [← h_eq]; exact hg_aesm
    · rw [← h_eq]; exact h_int_out_marg
  -- assemble `klDiv_ne_top`: AC + llr integrability (split into fibre − output).
  rw [mutualInfoOfChannel_def, jointDistribution_def]
  refine klDiv_ne_top h_joint_ac ?_
  refine (h_int_fibre_joint.sub h_int_out_joint).congr ?_
  exact (h_llr_split).symm

open InformationTheory.Shannon InformationTheory.Shannon.AWGN in
/-- Per-channel MI decomposition of the product achiever, in `.toReal` form. The
per-coordinate finiteness used for the `.toReal`/`∑` exchange comes from
`awgn_mutualInfoOfChannel_ne_top`, which needs `N i ≠ 0`. -/
theorem parallelGaussian_achiever_mi_eq_sum_perChannel {n : ℕ}
    (Q : Fin n → ℝ≥0) (N : Fin n → ℝ≥0) (hN : ∀ i, N i ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    (mutualInfoOfChannel (gaussianProductInput Q)
        (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = ∑ i : Fin n,
          (mutualInfoOfChannel (gaussianReal 0 (Q i)) (awgnChannel (N i) (h_meas i))).toReal := by
  rw [parallelGaussian_achiever_mi_eq_sum_perChannel_enn Q N h_meas h_parallel_meas]
  rw [ENNReal.toReal_sum (fun i _ => awgn_mutualInfoOfChannel_ne_top (N i) (hN i) (h_meas i) (Q i))]

open InformationTheory.Shannon InformationTheory.Shannon.AWGN in
/-- **Per-coordinate AWGN MI closed form** (all variances). For a single AWGN sub-channel,
the Gaussian-input mutual information equals `(1/2)·log(1 + Q/N)`, with no positivity
hypothesis on the input variance `Q`. The `Q = 0` branch (deterministic input
`gaussianReal 0 0 = dirac 0`) gives MI `= 0 = (1/2)·log 1` via `klDiv_self`. -/
theorem awgn_perCoord_mi_closed_form (Q N : ℝ≥0) (hN : N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    (mutualInfoOfChannel (gaussianReal 0 Q) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + (Q : ℝ) / (N : ℝ)) := by
  by_cases hQ : Q = 0
  · -- deterministic input: gaussianReal 0 0 = dirac 0, joint = product ⇒ MI = 0.
    subst hQ
    rw [NNReal.coe_zero, zero_div, add_zero, Real.log_one, mul_zero]
    -- MI = klDiv (dirac 0 ⊗ₘ W) ((dirac 0) ×ₘ output) = klDiv_self = 0.
    have h_joint_eq :
        jointDistribution (gaussianReal 0 0) (awgnChannel N h_meas)
          = (gaussianReal 0 0).prod
              (outputDistribution (gaussianReal 0 0) (awgnChannel N h_meas)) := by
      rw [ProbabilityTheory.gaussianReal_zero_var]
      -- LHS: dirac 0 ⊗ₘ W = (W 0).map (Prod.mk 0); RHS: dirac.prod = map (Prod.mk 0) ∘ snd.
      have hW : awgnChannel N h_meas 0 = gaussianReal 0 N := rfl
      rw [jointDistribution, outputDistribution, jointDistribution]
      rw [Measure.dirac_prod]
      -- both sides are `(W 0).map (Prod.mk 0)`.
      have h_compProd :
          (Measure.dirac (0 : ℝ)) ⊗ₘ (awgnChannel N h_meas)
            = ((awgnChannel N h_meas) 0).map (Prod.mk 0) := by
        ext s hs
        rw [MeasureTheory.Measure.dirac_compProd_apply hs,
          Measure.map_apply measurable_prodMk_left hs]
      rw [h_compProd,
        show (Prod.mk (0 : ℝ)) = (fun y : ℝ => ((fun _ : ℝ => (0 : ℝ)) y, id y)) from rfl,
        Measure.snd_map_prodMk (measurable_const), Measure.map_id]
    rw [mutualInfoOfChannel_def, h_joint_eq, InformationTheory.klDiv_self,
      ENNReal.toReal_zero]
  · -- Q ≠ 0: the hypothesis-free closed form with P := (Q : ℝ) > 0.
    have hQpos : (0 : ℝ) < (Q : ℝ) := by
      rw [NNReal.coe_pos]; exact pos_iff_ne_zero.mpr hQ
    have hN' : (N : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hN
    have hQ_cast : ((Q : ℝ)).toNNReal = Q := Real.toNNReal_coe
    have h := AWGN.mutualInfoOfChannel_gaussianInput_closed_form' (Q : ℝ) hQpos N hN' h_meas
    rw [hQ_cast] at h
    exact h

open InformationTheory.Shannon InformationTheory.Shannon.AWGN in
/-- The achiever MI value equals the per-coordinate water-filling sum, from the per-channel
decomposition `parallelGaussian_achiever_mi_eq_sum_perChannel` and the per-coordinate AWGN
closed form `awgn_perCoord_mi_closed_form`. Inhabits the `achiever_mi` field of
`IsParallelGaussianPerCoordRegularity`. -/
theorem parallelGaussianCapacity_achiever_mi {n : ℕ}
    (Q : Fin n → ℝ≥0) (N : Fin n → ℝ≥0) (hN : ∀ i, N i ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    (mutualInfoOfChannel (gaussianProductInput Q)
        (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = ∑ i : Fin n, (1/2) * Real.log (1 + (Q i : ℝ) / (N i : ℝ)) := by
  rw [parallelGaussian_achiever_mi_eq_sum_perChannel Q N hN h_meas h_parallel_meas]
  exact Finset.sum_congr rfl
    (fun i _ => awgn_perCoord_mi_closed_form (Q i) (N i) (hN i) (h_meas i))

/-- Deprecated alias for `parallel_gaussian_capacity_formula`. -/
@[entry_point, deprecated parallel_gaussian_capacity_formula (since := "2026-05-21")]
theorem parallel_gaussian_capacity_formula_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν)
    (h_reg : IsParallelGaussianPerCoordRegularity P N h_meas h_parallel_meas
              (fun i => (waterFillingPower ν N i).toNNReal)) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin (n + 1), (1/2) *
          Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) :=
  parallel_gaussian_capacity_formula P hP N hN h_meas h_parallel_meas
    ν h_kkt h_reg

end InformationTheory.Shannon.ParallelGaussian
