import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.Basic
import InformationTheory.Shannon.ParallelGaussian.PerCoord
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.CapacityConverseMaxent
import Mathlib.MeasureTheory.Constructions.Pi
import InformationTheory.Shannon.ParallelGaussian.Converse.Core
import InformationTheory.Shannon.ParallelGaussian.Converse.Regularity

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

section Phase1Regularity

variable {n : ℕ} (N : Fin n → ℝ≥0)
variable (h_meas : IsParallelAwgnChannelMeasurable N)
variable (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
variable (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]


/-! ## Joint mixture output density -/

/-- The **joint mixture output density** `f_Y(z) := ∫⁻ x, ∏ᵢ gaussianPDF (x i) (N i) (z i) ∂p`,
the `Fin n → ℝ` analogue of the 1-D output mixture density. -/
noncomputable def parallelOutputMixtureDensity (z : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Fin n → ℝ, piGaussProxy N (x, z) ∂p

/-- Unfolded form of `parallelOutputMixtureDensity`.

@audit:ok -/
theorem parallelOutputMixtureDensity_eq (z : Fin n → ℝ) :
    parallelOutputMixtureDensity N p z
      = ∫⁻ x : Fin n → ℝ, ∏ i, gaussianPDF (x i) (N i) (z i) ∂p := rfl

/-- The joint mixture density is measurable in `z`.

@audit:ok -/
theorem measurable_parallelOutputMixtureDensity :
    Measurable (parallelOutputMixtureDensity N p) := by
  unfold parallelOutputMixtureDensity
  exact Measurable.lintegral_prod_left' (piGaussProxy_measurable N)

/-- The correlated output `μY` equals `volume.withDensity (parallelOutputMixtureDensity)`
(the noise fibre is a `withDensity` of the Gaussian-PDF product, with Tonelli moving the `∂p`
average outside).

@audit:ok -/
theorem parallelOutput_eq_withDensity_mixture (hN : ∀ i, (N i : ℝ) ≠ 0) :
    outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)
      = volume.withDensity (parallelOutputMixtureDensity N p) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have hN' : ∀ i, N i ≠ 0 := fun i h => hN i (by rw [h]; norm_num)
  have h_mix_meas : Measurable (parallelOutputMixtureDensity N p) :=
    measurable_parallelOutputMixtureDensity N p
  -- the fibre `W x` is `volume.withDensity (z ↦ piGaussProxy N (x, z))`
  have h_fibre_wd : ∀ x : Fin n → ℝ,
      W x = volume.withDensity (fun z => piGaussProxy N (x, z)) := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    have h_each : ∀ i, gaussianReal (x i) (N i)
        = (volume : Measure ℝ).withDensity (gaussianPDF (x i) (N i)) :=
      fun i => gaussianReal_of_var_ne_zero (x i) (hN' i)
    rw [show (fun i => gaussianReal (x i) (N i))
        = (fun i => (volume : Measure ℝ).withDensity (gaussianPDF (x i) (N i))) from
        funext h_each]
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF (x i) (N i))) := by
      intro i; rw [← h_each i]; infer_instance
    rw [pi_withDensity_fin (fun _ => (volume : Measure ℝ))
      (fun i => measurable_gaussianPDF (x i) (N i)), ← volume_pi]
    rfl
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  -- LHS = ∫⁻ x, ∫⁻ z, f z · piGaussProxy N (x,z) ∂volume ∂p
  have hfi_meas : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f z.2) :=
    hf.comp measurable_snd
  have hLHS : ∫⁻ a, f a ∂(outputDistribution p W)
      = ∫⁻ x, ∫⁻ z, f z * piGaussProxy N (x, z) ∂volume ∂p := by
    calc ∫⁻ a, f a ∂(outputDistribution p W)
        = ∫⁻ z, f z.2 ∂(p ⊗ₘ W) := by
            rw [outputDistribution, jointDistribution_def, Measure.snd]
            exact lintegral_map hf measurable_snd
      _ = ∫⁻ x, ∫⁻ y, f y ∂(W x) ∂p := Measure.lintegral_compProd hfi_meas
      _ = ∫⁻ x, ∫⁻ z, f z * piGaussProxy N (x, z) ∂volume ∂p := by
            refine lintegral_congr (fun x => ?_)
            have h_slice : Measurable (fun z : Fin n → ℝ => piGaussProxy N (x, z)) :=
              (piGaussProxy_measurable N).comp (measurable_const.prodMk measurable_id)
            rw [h_fibre_wd x,
              lintegral_withDensity_eq_lintegral_mul _ h_slice hf]
            refine lintegral_congr (fun z => ?_)
            rw [Pi.mul_apply, mul_comm]
  -- swap order via Fubini-Tonelli
  have h_swap_meas : Measurable
      (Function.uncurry fun x z : Fin n → ℝ => f z * piGaussProxy N (x, z)) := by
    refine (hf.comp measurable_snd).mul ?_
    exact (piGaussProxy_measurable N).comp (measurable_fst.prodMk measurable_snd)
  rw [hLHS]
  calc ∫⁻ x, ∫⁻ z, f z * piGaussProxy N (x, z) ∂volume ∂p
      = ∫⁻ z, ∫⁻ x, f z * piGaussProxy N (x, z) ∂p ∂volume :=
        lintegral_lintegral_swap h_swap_meas.aemeasurable
    _ = ∫⁻ z, f z * parallelOutputMixtureDensity N p z ∂volume := by
        refine lintegral_congr (fun z => ?_)
        have h_slice : Measurable (fun x : Fin n → ℝ => piGaussProxy N (x, z)) :=
          (piGaussProxy_measurable N).comp (measurable_id.prodMk measurable_const)
        rw [parallelOutputMixtureDensity, ← lintegral_const_mul (f z) h_slice]
    _ = ∫⁻ z, f z ∂(volume.withDensity (parallelOutputMixtureDensity N p)) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ h_mix_meas hf]
        refine lintegral_congr (fun z => ?_)
        rw [Pi.mul_apply, mul_comm]

/-- The output rnDeriv is a.e. equal to the joint mixture density.

@audit:ok -/
theorem parallelOutput_rnDeriv_ae_mixture (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).rnDeriv volume
      =ᵐ[volume] parallelOutputMixtureDensity N p := by
  rw [parallelOutput_eq_withDensity_mixture N h_meas h_parallel_meas p hN]
  exact Measure.rnDeriv_withDensity volume (measurable_parallelOutputMixtureDensity N p)

/-- The joint mixture density is bounded above by `∏ᵢ (√(2π Nᵢ))⁻¹`.

@audit:ok -/
theorem parallelOutputMixtureDensity_le_sup (z : Fin n → ℝ) :
    parallelOutputMixtureDensity N p z
      ≤ ENNReal.ofReal (∏ i, (Real.sqrt (2 * Real.pi * N i))⁻¹) := by
  rw [parallelOutputMixtureDensity_eq,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  calc ∫⁻ x, ∏ i, gaussianPDF (x i) (N i) (z i) ∂p
      ≤ ∫⁻ _x, ∏ i, ENNReal.ofReal (Real.sqrt (2 * Real.pi * N i))⁻¹ ∂p := by
        refine lintegral_mono (fun x => ?_)
        refine Finset.prod_le_prod' (fun i _ => ?_)
        rw [gaussianPDF]
        exact ENNReal.ofReal_le_ofReal (AWGN.gaussianPDFReal_le_sup (x i) (N i) (z i))
    _ = ∏ i, ENNReal.ofReal (Real.sqrt (2 * Real.pi * N i))⁻¹ := by
        rw [lintegral_const, measure_univ, mul_one]

/-- **Coordinate-box concentration.** There is a box `S = {x | ∀ i, |x i| ≤ Rᵢ}` carrying
`≥ 1/2` of the mass of `p`, via a per-coordinate Chebyshev bound and a union bound over
`Fin n`.

@audit:ok -/
theorem parallel_concentration_box (P : ℝ) (hP : 0 ≤ P)
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ R : Fin n → ℝ, (∀ i, 0 < R i) ∧
      (1 : ℝ≥0∞) / 2 ≤ p {x : Fin n → ℝ | ∀ i, |x i| ≤ R i} := by
  classical
  obtain ⟨hp_prob, hp_lint⟩ := hp
  -- per-coordinate second-moment lintegral, finite
  set M : Fin n → ℝ≥0∞ := fun i => ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p with hM_def
  have hM_lt_top : ∀ i, M i < ∞ := by
    intro i
    have h_single_le : M i ≤ ∑ j : Fin n, M j :=
      Finset.single_le_sum (f := M) (fun j _ => bot_le) (Finset.mem_univ i)
    exact lt_of_le_of_lt (h_single_le.trans hp_lint) ENNReal.ofReal_lt_top
  -- choose `Rᵢ := √(2n·(M i).toReal + 1)`, so `Rᵢ² = 2n·(M i).toReal + 1`
  set R : Fin n → ℝ := fun i => Real.sqrt (2 * n * (M i).toReal + 1) with hR_def
  have hR_pos : ∀ i, 0 < R i := fun i => Real.sqrt_pos.mpr (by positivity)
  have hR_sq : ∀ i, R i ^ 2 = 2 * n * (M i).toReal + 1 :=
    fun i => Real.sq_sqrt (by positivity)
  refine ⟨R, hR_pos, ?_⟩
  -- the box is the complement of `⋃ i, {Rᵢ < |xᵢ|}`
  set S : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i, |x i| ≤ R i} with hS_def
  set T : Fin n → Set (Fin n → ℝ) := fun i => {x : Fin n → ℝ | R i < |x i|} with hT_def
  have hSc_eq : Sᶜ = ⋃ i, T i := by
    ext x
    simp only [hS_def, hT_def, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, not_forall,
      not_le]
  -- per-coordinate Markov bound `p (T i) ≤ 1/(2n)`
  have h_per : ∀ i, p (T i) ≤ ENNReal.ofReal (1 / (2 * n)) := by
    intro i
    have hn_pos' : (0 : ℝ) < 2 * n := by
      have : 0 < n := i.pos
      positivity
    have h_subset : T i ⊆
        {x : Fin n → ℝ | ENNReal.ofReal (R i ^ 2) ≤ ENNReal.ofReal ((x i) ^ 2)} := by
      intro x hx
      simp only [hT_def, Set.mem_setOf_eq] at hx
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [abs_nonneg (x i), sq_abs (x i), (hR_pos i).le]
    have hRsq_pos : (0 : ℝ) < R i ^ 2 := by rw [hR_sq i]; positivity
    have h_markov : p {x : Fin n → ℝ | ENNReal.ofReal (R i ^ 2) ≤ ENNReal.ofReal ((x i) ^ 2)}
        ≤ M i / ENNReal.ofReal (R i ^ 2) :=
      meas_ge_le_lintegral_div
        (((measurable_pi_apply i).pow_const 2).ennreal_ofReal.aemeasurable)
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hRsq_pos)
        ENNReal.ofReal_ne_top
    refine le_trans (measure_mono h_subset) (le_trans h_markov ?_)
    -- `M i / ofReal(Rᵢ²) ≤ ofReal(1/(2n))`
    rw [show M i = ENNReal.ofReal (M i).toReal from (ENNReal.ofReal_toReal (hM_lt_top i).ne).symm,
      ← ENNReal.ofReal_div_of_pos hRsq_pos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hR_sq i, div_le_div_iff₀ (by positivity) hn_pos']
    have hM_nonneg : 0 ≤ (M i).toReal := ENNReal.toReal_nonneg
    nlinarith [hM_nonneg]
  -- union bound: `p Sᶜ ≤ ∑ i, 1/(2n) = 1/2` (n > 0); n = 0 ⇒ box is univ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : S = Set.univ := by
      rw [hS_def]; ext x; simp
    rw [this, measure_univ]; norm_num
  · have h_union : p Sᶜ ≤ 1 / 2 := by
      rw [hSc_eq]
      refine le_trans (measure_iUnion_fintype_le p T) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ => h_per i)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn_pos : (0 : ℝ) < 2 * n := by positivity
      rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from (ENNReal.ofReal_natCast n).symm,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
        show (1:ℝ≥0∞)/2 = ENNReal.ofReal (1/2) by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_one_div, div_le_div_iff₀ hn_pos (by norm_num : (0:ℝ) < 2)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h_compl : p Sᶜ + p S = 1 := by
      rw [← measure_univ (μ := p), ← Set.compl_union_self S]
      have hS_meas : MeasurableSet S := by
        rw [hS_def, show {x : Fin n → ℝ | ∀ i, |x i| ≤ R i}
            = ⋂ i, {x : Fin n → ℝ | |x i| ≤ R i} by ext x; simp]
        exact MeasurableSet.iInter (fun i =>
          measurableSet_le ((measurable_pi_apply i).abs) measurable_const)
      exact (measure_union (disjoint_compl_left) hS_meas).symm
    have h1 : (1 : ℝ≥0∞) / 2 + p Sᶜ ≤ p Sᶜ + p S := by
      rw [h_compl]
      calc (1:ℝ≥0∞)/2 + p Sᶜ ≤ 1/2 + 1/2 := by gcongr
        _ = 1 := ENNReal.add_halves 1
    rw [add_comm (p Sᶜ)] at h1
    exact ENNReal.le_of_add_le_add_right
      (ne_of_lt (lt_of_le_of_lt h_union (by norm_num))) h1

set_option maxHeartbeats 1000000 in
/-- **Quadratic `-log` upper bound on the mixture density:** `∃ a b, 0 ≤ a ∧ ∀ z,
-log (f_Y z).toReal ≤ a · ∑ᵢ (zᵢ)² + b`. On the concentration box each coordinate Gaussian
has a tail lower bound, giving `f_Y(z) ≥ (1/2)·∏ᵢ Krᵢ(zᵢ)`, quadratic in each `zᵢ`.

@audit:ok -/
theorem parallelOutput_logDensity_lower_bound (P : ℝ) (hP : 0 ≤ P)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∀ z : Fin n → ℝ,
      -Real.log ((parallelOutputMixtureDensity N p z).toReal)
        ≤ a * (∑ i, (z i) ^ 2) + b := by
  classical
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  have hN_pos : ∀ i, (0 : ℝ) < N i :=
    fun i => lt_of_le_of_ne (N i).coe_nonneg (fun h => hN i h.symm)
  -- coordinate-box concentration
  obtain ⟨R, hR_pos, hS_ge⟩ := parallel_concentration_box p P hP hp
  set S : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i, |x i| ≤ R i} with hS_def
  -- per-coordinate Gaussian-tail lower constant `Krᵢ(zᵢ)`
  set Kr : Fin n → ℝ → ℝ := fun i zi =>
    (Real.sqrt (2 * Real.pi * (N i : ℝ)))⁻¹
      * Real.exp (-(2 * zi ^ 2 + 2 * R i ^ 2) / (2 * (N i : ℝ)))
    with hKr_def
  have hKr_pos : ∀ i zi, 0 < Kr i zi := fun i zi => by
    rw [hKr_def]; have := hN_pos i; positivity
  -- on `S`, the product of coordinate pdfs dominates `∏ᵢ ofReal (Krᵢ zᵢ)`
  have h_prod_ge : ∀ z : Fin n → ℝ, ∀ x ∈ S,
      ENNReal.ofReal (∏ i, Kr i (z i)) ≤ ∏ i, gaussianPDF (x i) (N i) (z i) := by
    intro z x hx
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hKr_pos i (z i)).le)]
    refine Finset.prod_le_prod' (fun i _ => ?_)
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [gaussianPDFReal, hKr_def]
    have hxi : |x i| ≤ R i := hx i
    have hxi_sq : (x i) ^ 2 ≤ R i ^ 2 := by
      nlinarith [abs_nonneg (x i), sq_abs (x i), (hR_pos i).le]
    have hNi := hN_pos i
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    rw [neg_div, neg_div, neg_le_neg_iff,
      div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * (N i : ℝ))]
    nlinarith [sq_nonneg (z i + x i), hxi_sq]
  -- `f_Y(z) ≥ ofReal (∏ᵢ Krᵢ zᵢ) · (1/2)`
  have h_fY_ge : ∀ z : Fin n → ℝ,
      ENNReal.ofReal (∏ i, Kr i (z i)) * (1 / 2) ≤ parallelOutputMixtureDensity N p z := by
    intro z
    rw [parallelOutputMixtureDensity_eq]
    have hS_meas : MeasurableSet S := by
      rw [hS_def, show {x : Fin n → ℝ | ∀ i, |x i| ≤ R i}
          = ⋂ i, {x : Fin n → ℝ | |x i| ≤ R i} by ext x; simp]
      exact MeasurableSet.iInter (fun i =>
        measurableSet_le ((measurable_pi_apply i).abs) measurable_const)
    have h_prod_meas : Measurable
        (fun x : Fin n → ℝ => ∏ i, gaussianPDF (x i) (N i) (z i)) := by
      have := (piGaussProxy_measurable N).comp
        (measurable_id.prodMk (measurable_const : Measurable fun _ : Fin n → ℝ => z))
      simpa [piGaussProxy] using this
    calc ENNReal.ofReal (∏ i, Kr i (z i)) * (1 / 2)
        ≤ ENNReal.ofReal (∏ i, Kr i (z i)) * p S := by gcongr
      _ = ∫⁻ _x in S, ENNReal.ofReal (∏ i, Kr i (z i)) ∂p := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x in S, ∏ i, gaussianPDF (x i) (N i) (z i) ∂p :=
          setLIntegral_mono h_prod_meas (fun x hx => h_prod_ge z x hx)
      _ ≤ ∫⁻ x, ∏ i, gaussianPDF (x i) (N i) (z i) ∂p := setLIntegral_le_lintegral S _
  -- pick `a := ∑ᵢ 1/Nᵢ`, `b := ∑ᵢ (Rᵢ²/Nᵢ + log(√(2π Nᵢ))) + log 2`
  refine ⟨∑ i, (1 / (N i : ℝ)),
    ∑ i, (R i ^ 2 / (N i : ℝ) + Real.log (Real.sqrt (2 * Real.pi * (N i : ℝ))))
    + Real.log 2, ?_, fun z => ?_⟩
  · refine Finset.sum_nonneg (fun i _ => ?_); have := hN_pos i; positivity
  -- bound `f_Y(z).toReal` below by `(∏ Krᵢ)·(1/2)`
  have h_ne_top : parallelOutputMixtureDensity N p z ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (parallelOutputMixtureDensity_le_sup N p z)
  have h_lb_real : (∏ i, Kr i (z i)) * (1 / 2)
      ≤ (parallelOutputMixtureDensity N p z).toReal := by
    have := ENNReal.toReal_mono h_ne_top (h_fY_ge z)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      show ((1:ℝ≥0∞)/2).toReal = 1/2 by simp] at this
  rw [neg_le]
  -- exact value: `log ((∏ Krᵢ)·(1/2)) = -(∑ᵢ zᵢ²/Nᵢ + b)`
  have h_log_eq : Real.log ((∏ i, Kr i (z i)) * (1 / 2))
      = -((∑ i, (z i) ^ 2 / (N i : ℝ))
          + (∑ i, (R i ^ 2 / (N i : ℝ)
              + Real.log (Real.sqrt (2 * Real.pi * (N i : ℝ)))) + Real.log 2)) := by
    have h_prod_pos : 0 < ∏ i, Kr i (z i) :=
      Finset.prod_pos (fun i _ => hKr_pos i (z i))
    rw [Real.log_mul h_prod_pos.ne' (by norm_num)]
    have h_log_prod : Real.log (∏ i, Kr i (z i)) = ∑ i, Real.log (Kr i (z i)) :=
      Real.log_prod (fun i _ => (hKr_pos i (z i)).ne')
    rw [h_log_prod]
    have h_log_Kr : ∀ i, Real.log (Kr i (z i))
        = -((z i) ^ 2 / (N i : ℝ)
          + (R i ^ 2 / (N i : ℝ) + Real.log (Real.sqrt (2 * Real.pi * (N i : ℝ))))) := by
      intro i
      have hNi : (N i : ℝ) ≠ 0 := hN i
      have hNpos := hN_pos i
      rw [hKr_def, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun i _ => h_log_Kr i)]
    rw [show (1:ℝ)/2 = ((2:ℝ))⁻¹ by norm_num, Real.log_inv,
      Finset.sum_neg_distrib, Finset.sum_add_distrib]
    ring
  -- bound `∑ᵢ zᵢ²/Nᵢ ≤ (∑ᵢ 1/Nᵢ)·∑zᵢ²`
  have h_quad : (∑ i, (z i) ^ 2 / (N i : ℝ))
      ≤ (∑ i, (1 / (N i : ℝ))) * (∑ i, (z i) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h_single : (1 / (N i : ℝ)) ≤ ∑ j, (1 / (N j : ℝ)) :=
      Finset.single_le_sum (f := fun j => (1 : ℝ) / (N j : ℝ))
        (fun j _ => by have := hN_pos j; positivity) (Finset.mem_univ i)
    rw [div_eq_mul_one_div, mul_comm ((z i) ^ 2)]
    exact mul_le_mul_of_nonneg_right h_single (sq_nonneg (z i))
  have h_prod_pos : 0 < ∏ i, Kr i (z i) :=
    Finset.prod_pos (fun i _ => hKr_pos i (z i))
  calc Real.log ((parallelOutputMixtureDensity N p z).toReal)
      ≥ Real.log ((∏ i, Kr i (z i)) * (1 / 2)) :=
        Real.log_le_log (by positivity) h_lb_real
    _ = -((∑ i, (z i) ^ 2 / (N i : ℝ))
          + (∑ i, (R i ^ 2 / (N i : ℝ)
              + Real.log (Real.sqrt (2 * Real.pi * (N i : ℝ)))) + Real.log 2)) :=
        h_log_eq
    _ ≥ -((∑ i, (1 / (N i : ℝ))) * (∑ i, (z i) ^ 2)
          + (∑ i, (R i ^ 2 / (N i : ℝ)
              + Real.log (Real.sqrt (2 * Real.pi * (N i : ℝ)))) + Real.log 2)) := by
        gcongr

/-- **Quadratic bound on `|log f_Y|`:** `∃ c₀ c₁, 0 ≤ c₁ ∧ ∀ z, |log (f_Y z).toReal| ≤ c₀ +
c₁ ∑ᵢ (zᵢ)²`, combining the constant upper bound with the quadratic lower bound.

@audit:ok -/
theorem parallelOutputMixtureDensity_log_abs_le (P : ℝ) (hP : 0 ≤ P)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ z : Fin n → ℝ,
      |Real.log ((parallelOutputMixtureDensity N p z).toReal)| ≤ c₀ + c₁ * ∑ i, (z i) ^ 2 := by
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  set M : ℝ := ∏ i, (Real.sqrt (2 * Real.pi * N i))⁻¹ with hM_def
  have hM_nonneg : 0 ≤ M := by rw [hM_def]; positivity
  -- upper bound on log f_Y(z) from the sup bound: `f_Y(z).toReal ≤ M`
  have h_up : ∀ z : Fin n → ℝ,
      Real.log ((parallelOutputMixtureDensity N p z).toReal) ≤ max (Real.log M) 0 := by
    intro z
    have h_le : (parallelOutputMixtureDensity N p z).toReal ≤ M := by
      have h := parallelOutputMixtureDensity_le_sup N p z
      rw [← hM_def] at h
      calc (parallelOutputMixtureDensity N p z).toReal
          ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        _ = M := ENNReal.toReal_ofReal hM_nonneg
    rcases le_or_gt (parallelOutputMixtureDensity N p z).toReal 0 with h0 | h0
    · have : (parallelOutputMixtureDensity N p z).toReal = 0 :=
        le_antisymm h0 ENNReal.toReal_nonneg
      rw [this, Real.log_zero]; exact le_max_right _ _
    · exact le_trans (Real.log_le_log h0 h_le) (le_max_left _ _)
  -- quadratic lower bound: `-log f_Y(z) ≤ a·∑zᵢ² + b`
  obtain ⟨a, b, ha, h_low⟩ := parallelOutput_logDensity_lower_bound N p P hP hN hp
  refine ⟨max (Real.log M) 0 + max b 0, a, ha, fun z => ?_⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := h_low z
    have hb : b ≤ max b 0 := le_max_left _ _
    nlinarith [le_max_right (Real.log M) (0 : ℝ), Finset.sum_nonneg
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg (z i)),
      mul_nonneg ha (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (z i)))]
  · have := h_up z
    nlinarith [le_max_right b (0 : ℝ), mul_nonneg ha
      (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (z i)))]

/-- Joint log-density integrability for the correlated output law: `log ((μY.rnDeriv volume
z).toReal)` is integrable against `μY`.

@audit:ok -/
theorem parallelOutput_joint_logDensity_integrable (P : ℝ) (hP : 0 ≤ P)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    Integrable
      (fun z => Real.log
        ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).rnDeriv
          volume z).toReal)
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) := by
  classical
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  set q := outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) with hq_def
  set fY := parallelOutputMixtureDensity N p with hfY_def
  -- `q ≪ volume` and `q.rnDeriv vol =ᵐ[q] fY`
  have hq_ac : q ≪ (volume : Measure (Fin n → ℝ)) :=
    parallelOutput_absolutelyContinuous_volume N h_meas h_parallel_meas p hN
  have h_rn_ae_q : q.rnDeriv volume =ᵐ[q] fY :=
    hq_ac.ae_le (parallelOutput_rnDeriv_ae_mixture N h_meas h_parallel_meas p hN)
  -- quadratic abs bound on `log fY`
  obtain ⟨c₀, c₁, hc₁, h_abs⟩ := parallelOutputMixtureDensity_log_abs_le N p P hP hN hp
  -- each coordinate second moment is integrable against `q`
  have h_q_coord_sq : ∀ i, Integrable (fun z : Fin n → ℝ => (z i) ^ 2) q := by
    intro i
    have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
    -- push to the marginal `q.map (· i)`, which has finite second moment
    have h_marg_sq : Integrable (fun y : ℝ => y ^ 2) (q.map (fun z => z i)) := by
      -- finite-second-moment ⇒ integrable on the marginal (1-D AWGN output law)
      rw [hq_def, parallelOutput_marginal_eq_awgn_output N h_meas h_parallel_meas p i]
      have h_mem : p.map (fun z => z i) ∈ AWGN.awgnPowerConstraintSet P :=
        parallelMarginal_mem_awgnPowerConstraintSet p P hp i
      haveI : IsProbabilityMeasure (p.map (fun z => z i)) :=
        Measure.isProbabilityMeasure_map hmeas_i.aemeasurable
      obtain ⟨hp_int, _⟩ := AWGN.awgnPowerConstraintSet_mem_iff_integrable P hP _ h_mem
      have h_pi_sq : Integrable (fun y : ℝ => y ^ 2) (p.map (fun z => z i)) := hp_int
      have h_sq0 := InformationTheory.Shannon.AWGN.output_sq_sub_integrable
        (AWGN.isAwgnChannelMeasurable (N i)) (by exact_mod_cast hN i)
        (p.map (fun z => z i)) h_pi_sq 0
      refine h_sq0.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp
    rw [show (fun z : Fin n → ℝ => (z i) ^ 2) = (fun y : ℝ => y ^ 2) ∘ (fun z => z i) from rfl,
      ← integrable_map_measure (by fun_prop) hmeas_i.aemeasurable]
    exact h_marg_sq
  -- the quadratic `c₀ + c₁·∑ᵢ zᵢ²` is integrable against `q`
  have h_sum_sq : Integrable (fun z : Fin n → ℝ => ∑ i, (z i) ^ 2) q :=
    integrable_finsetSum _ (fun i _ => h_q_coord_sq i)
  have h_dom_q : Integrable (fun z : Fin n → ℝ => c₀ + c₁ * ∑ i, (z i) ^ 2) q :=
    (integrable_const c₀).add (h_sum_sq.const_mul c₁)
  -- dominate `log (rnDeriv)` by `c₀ + c₁·∑zᵢ²`
  refine Integrable.mono' h_dom_q ?_ ?_
  · have h_rn_meas : Measurable (fun z => (q.rnDeriv volume z).toReal) :=
      (Measure.measurable_rnDeriv q volume).ennreal_toReal
    exact (Real.measurable_log.comp h_rn_meas).aestronglyMeasurable
  · filter_upwards [h_rn_ae_q] with z hz
    rw [Real.norm_eq_abs, hz, hfY_def]
    exact h_abs z

/-- **Fibre product-entropy identity.** Each fibre is a coordinate product of Gaussians, so
the conditional term is the constant `∑ᵢ (1/2)log(2πe Nᵢ)`.

@audit:ok -/
theorem parallel_condTerm_eq_sum_noise_entropy (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (∫ x, jointDifferentialEntropyPi
        ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p)
      = ∑ i : Fin n, (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) := by
  have hN' : ∀ i, N i ≠ 0 := fun i h => hN i (by rw [h]; norm_num)
  -- the integrand is the constant noise-entropy sum (mean-independent)
  have h_const : ∀ x : Fin n → ℝ,
      jointDifferentialEntropyPi ((parallelGaussianChannel N h_meas h_parallel_meas) x)
        = ∑ i : Fin n, (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) := by
    intro x
    rw [parallelGaussianChannel_apply]
    rw [jointDifferentialEntropyPi_pi_eq_sum (fun i => gaussianReal (x i) (N i))
      (fun i => gaussianReal_absolutelyContinuous (x i) (hN' i))
      (fun i => gaussianReal_logRnDeriv_integrable (x i) (hN' i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [differentialEntropy_gaussianReal (x i) (hN' i)]
  -- integrate the constant over the probability measure `p`
  rw [integral_congr_ae (Filter.Eventually.of_forall h_const), integral_const]
  simp

/-- The **output marginal mean** `mᵢ := ∫ y, y ∂(μY.map (· i))`. -/
noncomputable def parallelOutputMean (i : Fin n) : ℝ :=
  ∫ y, y ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
    (fun z => z i))

/-- **Marginal centered-second-moment (noise additivity).** With `m` the marginal mean,
`∫ (y − m)² ∂(μY.map (· i)) = (∫ (xᵢ − m)² ∂p) + Nᵢ`, via the convolution identity for the
marginal and the Gaussian fibre second moment.

@audit:ok -/
theorem parallelOutput_centered_secondMoment_eq (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P)
    (c : ℝ) :
    ∫ y, (y - c) ^ 2
        ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i))
      = (∫ x : Fin n → ℝ, ((x i) - c) ^ 2 ∂p) + (N i : ℝ) := by
  have hN_NN : N i ≠ 0 := fun h => hN (by rw [h]; norm_num)
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  set pi := p.map (fun z => z i) with hpi
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  haveI hpi_prob : IsProbabilityMeasure pi :=
    Measure.isProbabilityMeasure_map hmeas_i.aemeasurable
  -- `(x i)²` integrable from membership
  obtain ⟨hp_int, _⟩ := parallelGaussianPowerConstraintSet_mem_iff_integrable P hP p hp
  have h_xi_sq : Integrable (fun x : Fin n → ℝ => (x i) ^ 2) p := hp_int i
  -- `y²` integrable over the marginal `pi`
  have h_pi_sq : Integrable (fun y : ℝ => y ^ 2) pi := by
    rw [hpi, integrable_map_measure (by fun_prop) hmeas_i.aemeasurable]
    exact h_xi_sq
  -- the marginal is the 1-D AWGN output law of `pi`
  have h_out_eq := parallelOutput_marginal_eq_awgn_output N h_meas h_parallel_meas p i
  rw [h_out_eq, ← hpi]
  -- `∫ ((x i) − c)² ∂p = ∫ (y − c)² ∂pi` (push-forward)
  have h_marg_eq : (∫ x : Fin n → ℝ, ((x i) - c) ^ 2 ∂p)
      = ∫ y : ℝ, (y - c) ^ 2 ∂pi := by
    rw [hpi, integral_map hmeas_i.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => (y - c) ^ 2) (p.map (fun z => z i)))]
  rw [h_marg_eq]
  -- the 1-D output second moment:
  -- `∫ (y − c)² ∂(outputDistribution pi (awgn (N i))) = ∫ (x − c)² ∂pi + N i`
  rw [InformationTheory.Shannon.AWGN.outputDistribution_awgn_eq_conv,
    MeasureTheory.integral_conv (by
      rw [← InformationTheory.Shannon.AWGN.outputDistribution_awgn_eq_conv
        (h_meas := AWGN.isAwgnChannelMeasurable (N i))]
      exact InformationTheory.Shannon.AWGN.output_sq_sub_integrable
        (AWGN.isAwgnChannelMeasurable (N i)) hN_NN pi h_pi_sq c)]
  -- fibre: `∫ z, (x + z − c)² ∂𝒩(0, N i) = N i + (x − c)²`
  have h_fibre : (fun x : ℝ => ∫ z, (x + z - c) ^ 2 ∂(gaussianReal 0 (N i)))
      = fun x => (N i : ℝ) + (x - c) ^ 2 := by
    funext x
    have h_rw : (fun z => (x + z - c) ^ 2) = fun z => (z - (c - x)) ^ 2 := by funext z; ring
    rw [h_rw, InformationTheory.Shannon.AWGN.integral_sub_sq_gaussianReal (N i) hN_NN (c - x)]
    ring
  rw [h_fibre]
  -- `∫ x, (N i + (x − c)²) ∂pi = N i + ∫ (x − c)² ∂pi`
  have h_xc_sq_pi : Integrable (fun x : ℝ => (x - c) ^ 2) pi := by
    have h_expand : (fun x : ℝ => (x - c) ^ 2)
        = fun x => x ^ 2 + ((-(2 * c)) * x + c ^ 2) := by funext x; ring
    rw [h_expand]
    have h_id : Integrable (fun x : ℝ => x) pi := by
      refine (h_pi_sq.add (integrable_const (1 : ℝ))).mono' (by fun_prop) ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have h1 : (0 : ℝ) ≤ (|y| - 1) ^ 2 := sq_nonneg _
      have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
      nlinarith [abs_nonneg y, h1, h2]
    exact h_pi_sq.add ((h_id.const_mul _).add (integrable_const _))
  rw [integral_add (integrable_const _) h_xc_sq_pi, integral_const]
  simp [add_comm]

/-- **Output marginal mean equals input marginal mean:** `mᵢ = ∫ (xᵢ) ∂p` (the noise mean is
`0`).

@audit:ok -/
theorem parallelOutputMean_eq (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    parallelOutputMean N h_meas h_parallel_meas p i = ∫ x : Fin n → ℝ, (x i) ∂p := by
  have hN_NN : N i ≠ 0 := fun h => hN (by rw [h]; norm_num)
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  set pi := p.map (fun z => z i) with hpi
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  haveI hpi_prob : IsProbabilityMeasure pi :=
    Measure.isProbabilityMeasure_map hmeas_i.aemeasurable
  obtain ⟨hp_int, _⟩ := parallelGaussianPowerConstraintSet_mem_iff_integrable P hP p hp
  have h_xi_sq : Integrable (fun x : Fin n → ℝ => (x i) ^ 2) p := hp_int i
  have h_pi_sq : Integrable (fun y : ℝ => y ^ 2) pi := by
    rw [hpi, integrable_map_measure (by fun_prop) hmeas_i.aemeasurable]; exact h_xi_sq
  have h_pi_id : Integrable (fun x : ℝ => x) pi := by
    refine (h_pi_sq.add (integrable_const (1 : ℝ))).mono' (by fun_prop) ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have h1 : (0 : ℝ) ≤ (|y| - 1) ^ 2 := sq_nonneg _
    have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [abs_nonneg y, h1, h2]
  -- `Integrable id` over the conv output (from finite second moment)
  have h_out_id : Integrable (fun y : ℝ => y) (pi ∗ gaussianReal 0 (N i)) := by
    have h_out_sq : Integrable (fun y : ℝ => y ^ 2) (pi ∗ gaussianReal 0 (N i)) := by
      rw [← InformationTheory.Shannon.AWGN.outputDistribution_awgn_eq_conv
        (h_meas := AWGN.isAwgnChannelMeasurable (N i))]
      exact (InformationTheory.Shannon.AWGN.output_sq_sub_integrable
        (AWGN.isAwgnChannelMeasurable (N i)) hN_NN pi h_pi_sq 0).congr
        (Filter.Eventually.of_forall (fun y => by ring))
    refine (h_out_sq.add (integrable_const (1 : ℝ))).mono' (by fun_prop) ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have h1 : (0 : ℝ) ≤ (|y| - 1) ^ 2 := sq_nonneg _
    have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [abs_nonneg y, h1, h2]
  rw [parallelOutputMean, parallelOutput_marginal_eq_awgn_output N h_meas h_parallel_meas p i,
    ← hpi, InformationTheory.Shannon.AWGN.outputDistribution_awgn_eq_conv,
    MeasureTheory.integral_conv h_out_id]
  -- fibre mean: `∫ z, (x + z) ∂𝒩(0,Nᵢ) = x`
  have h_fibre : (fun x : ℝ => ∫ z, (x + z) ∂(gaussianReal 0 (N i))) = fun x => x := by
    funext x
    have h_id_g : Integrable (fun z : ℝ => z) (gaussianReal 0 (N i)) := by
      have := (memLp_id_gaussianReal (μ := 0) (v := N i) 1).integrable (by norm_num)
      simpa using this
    rw [integral_add (integrable_const _) h_id_g, integral_const,
      ProbabilityTheory.integral_id_gaussianReal]
    simp
  rw [h_fibre]
  -- `∫ x ∂pi = ∫ (x i) ∂p`
  rw [hpi, integral_map hmeas_i.aemeasurable
    (f := fun x : ℝ => x) (measurable_id).aestronglyMeasurable]

/-- **Output marginal variance bound:** `Var(Yᵢ) ≤ E[Xᵢ²] + Nᵢ`, from noise additivity
`Var(Yᵢ) = Var(Xᵢ) + Nᵢ` and `Var(Xᵢ) ≤ E[Xᵢ²]`.

@audit:ok -/
theorem parallelOutput_variance_le (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∫ y, (y - parallelOutputMean N h_meas h_parallel_meas p i) ^ 2
        ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i))
      ≤ (∫ x : Fin n → ℝ, (x i) ^ 2 ∂p) + (N i : ℝ) := by
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  obtain ⟨hp_int, _⟩ := parallelGaussianPowerConstraintSet_mem_iff_integrable P hP p hp
  have h_xi_sq : Integrable (fun x : Fin n → ℝ => (x i) ^ 2 ) p := hp_int i
  have h_xi_id : Integrable (fun x : Fin n → ℝ => (x i)) p := by
    refine (h_xi_sq.add (integrable_const (1 : ℝ))).mono'
      (measurable_pi_apply i).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have h1 : (0 : ℝ) ≤ (|x i| - 1) ^ 2 := sq_nonneg _
    have h2 : |x i| ^ 2 = (x i) ^ 2 := sq_abs (x i)
    nlinarith [abs_nonneg (x i), h1, h2]
  set m := parallelOutputMean N h_meas h_parallel_meas p i with hm
  have hm_eq : m = ∫ x : Fin n → ℝ, (x i) ∂p :=
    parallelOutputMean_eq N h_meas h_parallel_meas p P hP i hN hp
  rw [parallelOutput_centered_secondMoment_eq N h_meas h_parallel_meas p P hP i hN hp m]
  -- `∫ ((x i) − m)² ∂p ≤ ∫ (x i)² ∂p` with `m = ∫ (x i) ∂p` (variance ≤ second moment)
  have key : ∫ x : Fin n → ℝ, ((x i) - m) ^ 2 ∂p ≤ ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p := by
    have h_expand : ∫ x : Fin n → ℝ, ((x i) - m) ^ 2 ∂p
        = (∫ x : Fin n → ℝ, (x i) ^ 2 ∂p) - m ^ 2 := by
      have h_int2 : Integrable (fun x : Fin n → ℝ => (-(2 * m)) * (x i) + m ^ 2) p :=
        (h_xi_id.const_mul _).add (integrable_const _)
      have h_rw : ∫ x : Fin n → ℝ, ((x i) - m) ^ 2 ∂p
          = ∫ x : Fin n → ℝ, ((x i) ^ 2 + ((-(2 * m)) * (x i) + m ^ 2)) ∂p :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      rw [h_rw, integral_add h_xi_sq h_int2]
      have h_lin : ∫ x : Fin n → ℝ, ((-(2 * m)) * (x i) + m ^ 2) ∂p = -(m ^ 2) := by
        rw [integral_add (h_xi_id.const_mul _) (integrable_const _),
          integral_const_mul, integral_const, ← hm_eq, probReal_univ]
        ring
      rw [h_lin]; ring
    rw [h_expand]
    nlinarith [sq_nonneg m]
  linarith [key]

/-- **Output marginal variance lower bound:** `Var(Yᵢ) ≥ Nᵢ`, since the independent noise of
variance `Nᵢ` adds to the nonnegative input variance.

@audit:ok -/
theorem parallelOutput_variance_ge_noise (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    (N i : ℝ)
      ≤ ∫ y, (y - parallelOutputMean N h_meas h_parallel_meas p i) ^ 2
          ∂((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
            (fun z => z i)) := by
  set m := parallelOutputMean N h_meas h_parallel_meas p i with hm
  rw [parallelOutput_centered_secondMoment_eq N h_meas h_parallel_meas p P hP i hN hp m]
  have h_nonneg : (0 : ℝ) ≤ ∫ x : Fin n → ℝ, ((x i) - m) ^ 2 ∂p :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

/-- **Output marginal variance integrability.** The centered square `(yᵢ − mᵢ)²` is
integrable against the marginal.

@audit:ok -/
theorem parallelOutput_variance_integrable (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    Integrable (fun y => (y - parallelOutputMean N h_meas h_parallel_meas p i) ^ 2)
      ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)) := by
  have hN_NN : N i ≠ 0 := fun h => hN (by rw [h]; norm_num)
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  set pi := p.map (fun z => z i) with hpi
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  haveI hpi_prob : IsProbabilityMeasure pi :=
    Measure.isProbabilityMeasure_map hmeas_i.aemeasurable
  obtain ⟨hp_int, _⟩ := parallelGaussianPowerConstraintSet_mem_iff_integrable P hP p hp
  have h_pi_sq : Integrable (fun y : ℝ => y ^ 2) pi := by
    rw [hpi, integrable_map_measure (by fun_prop) hmeas_i.aemeasurable]; exact hp_int i
  rw [parallelOutput_marginal_eq_awgn_output N h_meas h_parallel_meas p i, ← hpi]
  exact InformationTheory.Shannon.AWGN.output_sq_sub_integrable
    (AWGN.isAwgnChannelMeasurable (N i)) hN_NN pi h_pi_sq _

set_option maxHeartbeats 1000000 in
/-- **Output marginal entropy-integrand volume integrability** (for
`differentialEntropy_le_gaussian_of_variance_le`), via the 1-D AWGN output of the input
marginal and its inherited power constraint.

@audit:ok -/
theorem parallelOutput_marginal_entropy_integrable (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    Integrable
      (fun y => Real.negMulLog
        (((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i)).rnDeriv volume y).toReal)
      (volume : Measure ℝ) := by
  have hN_NN : N i ≠ 0 := fun h => hN (by rw [h]; norm_num)
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  have h_mem : p.map (fun z => z i) ∈ AWGN.awgnPowerConstraintSet P :=
    parallelMarginal_mem_awgnPowerConstraintSet p P hp i
  rw [parallelOutput_marginal_eq_awgn_output N h_meas h_parallel_meas p i]
  haveI : IsProbabilityMeasure (p.map (fun z => z i)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  exact InformationTheory.Shannon.AWGN.outputDistribution_logDensity_integrable
    hP hN_NN (AWGN.isAwgnChannelMeasurable (N i)) (p.map (fun z => z i)) h_mem

/-- **Fibre ≪ output:** `W x ≪ μY`, via `W x ≪ volume ≪ μY`.

@audit:ok -/
theorem parallelChannel_fibre_absolutelyContinuous_output (hN : ∀ i, (N i : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    (parallelGaussianChannel N h_meas h_parallel_meas) x
      ≪ outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) := by
  exact (parallelChannel_fibre_absolutelyContinuous_volume N hN h_meas h_parallel_meas x).trans
    (volume_absolutelyContinuous_parallelOutput N h_meas h_parallel_meas p hN)

/-- **Fibre rnDeriv as Gaussian-PDF-product proxy:** `(W x).rnDeriv volume =ᵐ[W x]
fun y => ∏ᵢ gaussianPDF (x i) (N i) (y i)`.

@audit:ok -/
theorem parallelFibre_rnDeriv_ae_proxy (hN : ∀ i, (N i : ℝ) ≠ 0) (x : Fin n → ℝ) :
    (fun y => ((parallelGaussianChannel N h_meas h_parallel_meas) x).rnDeriv volume y)
      =ᵐ[(parallelGaussianChannel N h_meas h_parallel_meas) x]
    fun y => ∏ i, gaussianPDF (x i) (N i) (y i) := by
  classical
  have hN' : ∀ i, N i ≠ 0 := fun i h => hN i (by rw [h]; norm_num)
  rw [parallelGaussianChannel_apply]
  set f : Fin n → ℝ → ℝ≥0∞ := fun i => gaussianPDF (x i) (N i) with hf
  have hf_meas : ∀ i, Measurable (f i) := fun i => measurable_gaussianPDF _ _
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = gaussianReal (x i) (N i) :=
    fun i => (gaussianReal_of_var_ne_zero (x i) (hN' i)).symm
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  have h_prod_meas : Measurable (fun y : Fin n → ℝ => ∏ i, f i (y i)) :=
    Finset.measurable_prod _ (fun i _ => (hf_meas i).comp (measurable_pi_apply i))
  have h_pi_wd : Measure.pi (fun i => gaussianReal (x i) (N i))
      = (volume : Measure (Fin n → ℝ)).withDensity (fun y => ∏ i, f i (y i)) := by
    rw [← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (f i))
        = fun i => gaussianReal (x i) (N i))]
    rw [pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) hf_meas, volume_pi]
  have h_ac : Measure.pi (fun i => gaussianReal (x i) (N i)) ≪ (volume : Measure (Fin n → ℝ)) :=
    pi_absolutelyContinuous _
      (fun i => gaussianReal_absolutelyContinuous (x i) (by exact_mod_cast hN i))
  refine h_ac.ae_le ?_
  have h_rn : (Measure.pi (fun i => gaussianReal (x i) (N i))).rnDeriv volume
      =ᵐ[volume] fun y => ∏ i, f i (y i) := by
    rw [h_pi_wd]; exact Measure.rnDeriv_withDensity volume h_prod_meas
  exact h_rn

set_option maxHeartbeats 800000 in
/-- **Fibre log-proxy integrability over the joint:** `log (∏ gaussianPDF)` is integrable
against `p ⊗ₘ W`. The log of the Gaussian-PDF product is the coordinate sum
`∑ᵢ (cᵢ + c'ᵢ (yᵢ − xᵢ)²)`, each quadratic summand integrable.

@audit:ok -/
theorem parallelFibre_logProxy_integrable_compProd (P : ℝ) (hP : 0 ≤ P)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        Real.log (∏ i, gaussianPDF (z.1 i) (N i) (z.2 i)).toReal)
      (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas)) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW_def
  have hN' : ∀ i, N i ≠ 0 := fun i h => hN i (by rw [h]; norm_num)
  -- per-coordinate affine constants
  set c₀ : Fin n → ℝ := fun i => -(1 / 2) * Real.log (2 * Real.pi * (N i : ℝ)) with hc₀
  set c₁ : Fin n → ℝ := fun i => -(1 / (2 * (N i : ℝ))) with hc₁
  -- STEP 1: rewrite the log-of-product integrand as the coordinate sum
  -- `∑ᵢ (c₀ᵢ + c₁ᵢ (z.2 i − z.1 i)²)`
  have h_eq : (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        Real.log (∏ i, gaussianPDF (z.1 i) (N i) (z.2 i)).toReal)
      = fun z => ∑ i, (c₀ i + c₁ i * (z.2 i - z.1 i) ^ 2) := by
    funext z
    rw [ENNReal.toReal_prod]
    have h_pos : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (gaussianPDF (z.1 i) (N i) (z.2 i)).toReal ≠ 0 := by
      intro i _
      rw [toReal_gaussianPDF]
      exact (gaussianPDFReal_pos (z.1 i) (N i) (z.2 i) (hN' i)).ne'
    rw [Real.log_prod h_pos]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [toReal_gaussianPDF, log_gaussianPDFReal_eq (z.1 i) (hN' i) (z.2 i), hc₀, hc₁]
    ring
  rw [h_eq]
  -- STEP 2: each summand is integrable; sum over `Fin n` is integrable
  refine integrable_finsetSum _ (fun i _ => ?_)
  -- `(z.2 i − z.1 i)²` integrable against `p ⊗ₘ W`
  have h_sq : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.2 i - z.1 i) ^ 2)
      (p ⊗ₘ W) := by
    have h_aesm : AEStronglyMeasurable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.2 i - z.1 i) ^ 2) (p ⊗ₘ W) :=
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).pow_const 2 |>.aestronglyMeasurable
    rw [Measure.integrable_compProd_iff h_aesm]
    constructor
    · -- per-fibre: `∫ y, (y i − x i)² ∂(W x)` integrable (Gaussian `i`-marginal 2nd moment)
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [hW_def, parallelGaussianChannel_apply]
      have hfib : Integrable (fun yi : ℝ => (yi - x i) ^ 2) (gaussianReal (x i) (N i)) :=
        InformationTheory.Shannon.AWGN.integrable_sq_sub_gaussianReal (x i) (x i) (N i)
      exact integrable_comp_eval (μ := fun j => gaussianReal (x j) (N j)) (i := i) hfib
    · -- L¹ norm of the fibre is the constant `N i`
      have h_norm : (fun x : Fin n → ℝ => ∫ y, ‖(y i - x i) ^ 2‖ ∂(W x))
          = fun _ => (N i : ℝ) := by
        funext x
        have hnn : (fun y : Fin n → ℝ => ‖(y i - x i) ^ 2‖)
            = fun y => (fun yi : ℝ => (yi - x i) ^ 2) (y i) := by
          funext y; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [hnn, hW_def, parallelGaussianChannel_apply]
        rw [integral_comp_eval (μ := fun j => gaussianReal (x j) (N j)) (i := i)
          (f := fun yi : ℝ => (yi - x i) ^ 2)
          (InformationTheory.Shannon.AWGN.integrable_sq_sub_gaussianReal
            (x i) (x i) (N i)).aestronglyMeasurable]
        exact InformationTheory.Shannon.AWGN.integral_sq_sub_self_gaussianReal (x i) (N i)
      rw [h_norm]
      exact integrable_const _
  exact (integrable_const (c₀ i)).add (h_sq.const_mul (c₁ i))

set_option maxHeartbeats 1600000 in
/-- **Channel↔RV MI decomposition value** for the correlated input:
`I = jointDifferentialEntropyPi(μY) − ∫ jointDifferentialEntropyPi(W x) ∂p`, a reduction to
the decomposition lift `parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub` with all
preconditions supplied.

@audit:ok -/
theorem parallel_mi_decomp_value (P : ℝ) (hP : 0 ≤ P) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
      = jointDifferentialEntropyPi
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas))
        - ∫ x, jointDifferentialEntropyPi
            ((parallelGaussianChannel N h_meas h_parallel_meas) x) ∂p := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW_def
  set q := outputDistribution p W with hq_def
  -- regularity preconditions
  have hW_ac : ∀ x, W x ≪ (volume : Measure (Fin n → ℝ)) :=
    fun x => parallelChannel_fibre_absolutelyContinuous_volume N hN h_meas h_parallel_meas x
  have hWx_q : ∀ x, W x ≪ q :=
    fun x => parallelChannel_fibre_absolutelyContinuous_output N h_meas h_parallel_meas p hN x
  have hq_ac : q ≪ (volume : Measure (Fin n → ℝ)) :=
    parallelOutput_absolutelyContinuous_volume N h_meas h_parallel_meas p hN
  -- joint AC `p ⊗ₘ W ≪ p.prod q`
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod q := by
    rw [show p.prod q = p ⊗ₘ (Kernel.const (Fin n → ℝ) q) from (Measure.compProd_const).symm]
    exact Measure.absolutelyContinuous_compProd_right_iff.mpr
      (Filter.Eventually.of_forall
        (fun x => by simpa only [Kernel.const_apply] using hWx_q x))
  -- proxy density `g z = ∏ᵢ gaussianPDF (z.1 i) (N i) (z.2 i)`, kept atomic for the lift
  let g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞ := piGaussProxy N
  have hg_prod : ∀ z, g z = ∏ i, gaussianPDF (z.1 i) (N i) (z.2 i) := fun z => rfl
  have hg_meas : Measurable g := piGaussProxy_measurable N
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
    intro x
    refine (parallelFibre_rnDeriv_ae_proxy N h_meas h_parallel_meas hN x).trans ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [hg_prod (x, y)]
  -- fibre log-proxy joint integrability
  have h_int_fibre : Integrable (fun z => Real.log (g z).toReal) (p ⊗ₘ W) := by
    have hbase := parallelFibre_logProxy_integrable_compProd N h_meas h_parallel_meas p P hP hN hp
    refine hbase.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hg_prod z]
  -- output log-density joint integrability: push the output-law integrability up via snd
  have h_int_out : Integrable
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        Real.log (q.rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    have h5 := parallelOutput_joint_logDensity_integrable N h_meas h_parallel_meas p P hP hN hp
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    have hF_meas : AEStronglyMeasurable
        (fun y => Real.log (q.rnDeriv volume y).toReal) q :=
      ((Measure.measurable_rnDeriv q volume).ennreal_toReal.log).aestronglyMeasurable
    have hF_meas' : AEStronglyMeasurable
        (fun y => Real.log (q.rnDeriv volume y).toReal) ((p ⊗ₘ W).map Prod.snd) := by
      rw [← h_eq]; exact hF_meas
    have := (integrable_map_measure hF_meas' measurable_snd.aemeasurable).mp
      (by rw [← h_eq]; exact h5)
    simpa [Function.comp] using this
  have h_lift := parallel_mutualInfoOfChannel_toReal_eq_diffEntropyPi_sub N h_meas h_parallel_meas p
    hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out
  exact h_lift

end Phase1Regularity

/-- **Per-coordinate max-entropy converse split** (correlated input). For `0 ≤ P`, every
feasible input admits a split `P'` (with `0 ≤ P'ᵢ`, `∑ P'ᵢ ≤ P`) whose per-coordinate sum
bounds the MI. Assembled from the MI decomposition, output-entropy subadditivity, per-coord
Gaussian max-entropy, and the variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ`.

The `0 ≤ P` precondition is necessary: for `P < 0` the constraint set is non-empty (it
contains the Dirac at 0) yet `∑ P'ᵢ ≤ P < 0` with `P'ᵢ ≥ 0` is unsatisfiable, so the
statement would be false. -/
theorem parallel_per_input_mi_le_sum {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (p : Measure (Fin n → ℝ)) [IsProbabilityMeasure p]
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    ∃ P' : Fin n → ℝ, (∀ i, 0 ≤ P' i) ∧ (∑ i : Fin n, P' i ≤ P) ∧
      (mutualInfoOfChannel p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal
        ≤ ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ)) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW_def
  set μY := outputDistribution p W with hμY_def
  -- per-coordinate noise positivity
  have hN_pos : ∀ i, (0 : ℝ) < (N i : ℝ) :=
    fun i => lt_of_le_of_ne (N i).coe_nonneg (Ne.symm (hN i))
  -- integrability + Bochner second-moment bound from membership
  obtain ⟨hp_2mom_int, hp_2mom⟩ :=
    parallelGaussianPowerConstraintSet_mem_iff_integrable P hP p hp
  -- output law + marginals are probability measures
  haveI hμY_prob : IsProbabilityMeasure μY := by rw [hμY_def]; infer_instance
  haveI hμY_marg_prob : ∀ i, IsProbabilityMeasure (μY.map (fun z => z i)) := by
    intro i; rw [hμY_def, hW_def]; infer_instance
  -- per-coord output mean / variance
  set m : Fin n → ℝ := fun i => parallelOutputMean N h_meas h_parallel_meas p i with hm_def
  set varY : Fin n → ℝ := fun i =>
    ∫ y, (y - m i) ^ 2 ∂(μY.map (fun z => z i)) with hvarY_def
  -- variance allocation `P'ᵢ := Var(Yᵢ) − Nᵢ`
  refine ⟨fun i => varY i - (N i : ℝ), ?_, ?_, ?_⟩
  · -- `0 ≤ P'ᵢ`: noise additivity `Var(Yᵢ) ≥ Nᵢ`
    intro i
    have h := parallelOutput_variance_ge_noise N h_meas h_parallel_meas p P hP i (hN i) hp
    simp only [hvarY_def, hm_def]
    linarith [h]
  · -- `∑ P'ᵢ ≤ P`: `∑ (Var(Yᵢ) − Nᵢ) ≤ ∑ E[Xᵢ²] ≤ P`
    have h_each : ∀ i : Fin n, varY i - (N i : ℝ) ≤ ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p := by
      intro i
      have h := parallelOutput_variance_le N h_meas h_parallel_meas p P hP i (hN i) hp
      simp only [hvarY_def, hm_def]
      linarith [h]
    calc ∑ i : Fin n, (varY i - (N i : ℝ))
        ≤ ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p :=
          Finset.sum_le_sum (fun i _ => h_each i)
      _ ≤ P := hp_2mom
  · -- the converse chain: MI decomp + subadditivity + per-coord max-entropy + log-algebra
    -- assembled via `parallelGaussian_max_ent_le_of_subadditivity`.
    set condTerm : ℝ := ∫ x, jointDifferentialEntropyPi (W x) ∂p with hcond_def
    -- decomposition value: I = h(Yⁿ) − condTerm
    have h_decomp :
        (mutualInfoOfChannel p W).toReal = jointDifferentialEntropyPi μY - condTerm := by
      rw [hμY_def, hcond_def, hW_def]
      exact parallel_mi_decomp_value N h_meas h_parallel_meas p P hP hN hp
    -- condTerm is the constant noise-entropy sum
    have h_cond_eq : condTerm =
        ∑ i : Fin n, (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) := by
      rw [hcond_def]
      exact parallel_condTerm_eq_sum_noise_entropy N h_meas h_parallel_meas p hN
    -- per-coord max-entropy bound: h(Yᵢ) ≤ (1/2)log(2πe·Var(Yᵢ)) and Var(Yᵢ) = P'ᵢ + Nᵢ
    have h_perCoord :
        (∑ i, differentialEntropy (μY.map (fun z => z i))) - condTerm
          ≤ ∑ i, (1/2) * Real.log (1 + (varY i - (N i : ℝ)) / (N i : ℝ)) := by
      rw [h_cond_eq, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      -- variance value `v := Var(Yᵢ).toNNReal` and `(v : ℝ) = Var(Yᵢ)`
      have h_var_nonneg : (0 : ℝ) < varY i := by
        have h := parallelOutput_variance_ge_noise N h_meas h_parallel_meas p P hP i (hN i) hp
        simp only [hvarY_def, hm_def] at h ⊢
        linarith [hN_pos i]
      set v : ℝ≥0 := varY i |>.toNNReal with hv_def
      have hv_coe : (v : ℝ) = varY i := by rw [hv_def, Real.coe_toNNReal _ h_var_nonneg.le]
      have hv_ne : v ≠ 0 := by rw [hv_def]; exact (Real.toNNReal_pos.mpr h_var_nonneg).ne'
      -- max-entropy on the marginal
      have h_maxent :
          differentialEntropy (μY.map (fun z => z i))
            ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by
        have hμac :=
          parallelOutput_marginal_absolutelyContinuous_volume N h_meas h_parallel_meas p hN i
        have hvar_int :=
          parallelOutput_variance_integrable N h_meas h_parallel_meas p P hP i (hN i) hp
        have hent_int :=
          parallelOutput_marginal_entropy_integrable N h_meas h_parallel_meas p P hP i (hN i) hp
        rw [← hW_def, ← hμY_def] at hμac hvar_int hent_int
        refine differentialEntropy_le_gaussian_of_variance_le hμac (m i) hv_ne rfl ?_ ?_ ?_
        · rw [hv_coe]
        · simpa only [hm_def] using hvar_int
        · simpa only using hent_int
      -- log algebra: (1/2)log(2πe·v) − (1/2)log(2πe·Nᵢ) = (1/2)log(1 + (v−Nᵢ)/Nᵢ)
      have h_log_alg :
          (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
              - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ))
            = (1/2) * Real.log (1 + (varY i - (N i : ℝ)) / (N i : ℝ)) := by
        have h_num : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (v : ℝ) := by
          rw [hv_coe]
          have h2 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
          exact mul_pos h2 h_var_nonneg
        have h_den : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N i : ℝ) :=
          mul_pos (by positivity) (hN_pos i)
        rw [← mul_sub, ← Real.log_div h_num.ne' h_den.ne']
        have h_arg :
            (2 * Real.pi * Real.exp 1 * (v : ℝ)) / (2 * Real.pi * Real.exp 1 * (N i : ℝ))
              = 1 + (varY i - (N i : ℝ)) / (N i : ℝ) := by
          rw [hv_coe]
          rw [mul_div_mul_left _ _ (show (2 * Real.pi * Real.exp 1 : ℝ) ≠ 0 by positivity)]
          rw [add_div' _ _ _ (hN_pos i).ne']
          ring_nf
        rw [h_arg]
      calc differentialEntropy (μY.map (fun z => z i))
            - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ))
          ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
              - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N i : ℝ)) :=
            sub_le_sub_right h_maxent _
        _ = (1/2) * Real.log (1 + (varY i - (N i : ℝ)) / (N i : ℝ)) := h_log_alg
    -- assemble via the genuine subadditivity wrapper
    have h_marg_ac := fun i =>
      parallelOutput_marginal_absolutelyContinuous_volume N h_meas h_parallel_meas p hN i
    have hμ_ac := parallelOutput_absolutelyContinuous_volume N h_meas h_parallel_meas p hN
    have h_joint_ac :=
      parallelOutput_absolutelyContinuous_pi_marginals N h_meas h_parallel_meas p hN
    have h_int_marg : ∀ i, Integrable (fun z => Real.log
        (((μY.map (fun z => z i)).rnDeriv volume (z i)).toReal)) μY := by
      intro i
      have :=
        parallelOutput_marginal_logDensity_integrable N h_meas h_parallel_meas p P hP i (hN i) hp
      rwa [← hW_def, ← hμY_def] at this
    have h_int_joint :=
      parallelOutput_joint_logDensity_integrable N h_meas h_parallel_meas p P hP hN hp
    rw [← hW_def, ← hμY_def] at h_marg_ac hμ_ac h_joint_ac h_int_joint
    exact parallelGaussian_max_ent_le_of_subadditivity μY
      (mutualInfoOfChannel p W).toReal condTerm (fun i => varY i - (N i : ℝ)) N
      h_decomp h_marg_ac hμ_ac h_joint_ac h_int_marg h_int_joint h_perCoord

/-! ## Boundedness of the MI image -/

/-- **`BddAbove (miImage P N …)`.** Every MI value of a feasible input is bounded by the
constant `∑ᵢ (1/2) log(1 + P/Nᵢ)`: the per-input split returns a feasible `P'` with
`P'ᵢ ≤ P` coordinate-wise, and `log` monotonicity caps each term. -/
theorem parallel_bddAbove_miImage {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    BddAbove (miImage P N h_meas h_parallel_meas) := by
  -- constant upper bound: `C := ∑ᵢ (1/2) log(1 + P/Nᵢ)`
  refine ⟨∑ i : Fin n, (1/2) * Real.log (1 + P / (N i : ℝ)), ?_⟩
  rintro y ⟨p, hp_mem, rfl⟩
  -- `p` is a probability measure (set membership)
  have hp_prob : IsProbabilityMeasure p := hp_mem.1
  obtain ⟨P', hP'_nn, hP'_sum, hP'_le⟩ :=
    parallel_per_input_mi_le_sum P hP N hN h_meas h_parallel_meas p hp_mem
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
