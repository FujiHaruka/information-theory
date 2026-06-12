import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.Basic
import InformationTheory.Shannon.ParallelGaussian.PerCoord
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.CapacityConverseMaxent
import Mathlib.MeasureTheory.Constructions.Pi
import InformationTheory.Shannon.ParallelGaussian.Converse.Core

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

/-- Coordinate marginals of the correlated output law are probability measures. -/
instance parallelOutput_marginal_isProbabilityMeasure (i : Fin n) :
    IsProbabilityMeasure
      ((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)) := by
  have : IsProbabilityMeasure
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) :=
    inferInstance
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

/-- **Parallel-output marginal as 1-D AWGN convolution** (Wave 3 linchpin).
The `i`-th coordinate marginal of the correlated output law is the 1-D AWGN output law
of the `i`-input marginal smoothed by the noise `gaussianReal 0 (N i)`:
`μY.map (· i) = (p.map (· i)) ∗ gaussianReal 0 (N i)`.

Built by identifying `μY.map (· i)` with the 1-D AWGN output law of the input marginal,
`outputDistribution (p.map (· i)) (awgnChannel (N i) …)`, which equals the convolution by
`outputDistribution_awgn_eq_conv`. The identification is a `lintegral`-level equality
(`Measure.ext_of_lintegral`): on the joint `p ⊗ₘ W`, `∫⁻ f((y) i) ∂(W x) = ∫⁻ yi, f yi
∂(gaussianReal (x i) (N i))` (the `i`-marginal of the Gaussian product fibre, via
`Measure.pi_map_eval`), which matches the 1-D AWGN fibre `(awgnChannel (N i)) (x i)`.
@audit:ok -/
theorem parallelOutput_marginal_eq_conv (i : Fin n) :
    (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)
      = (p.map (fun z => z i)) ∗ gaussianReal 0 (N i) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  -- the 1-D AWGN channel for coordinate `i`
  set Wi := AWGN.awgnChannel (N i) (AWGN.isAwgnChannelMeasurable (N i)) with hWi
  -- STEP 1: identify the parallel-output marginal with the 1-D AWGN output law of `p.map (· i)`
  have h_id : (outputDistribution p W).map (fun z => z i)
      = ChannelCoding.outputDistribution (p.map (fun z => z i)) Wi := by
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    -- LHS = ∫⁻ z, f (z i) ∂μY = ∫⁻ x, (∫⁻ y, f (y i) ∂(W x)) ∂p
    -- fibre identity: ∫⁻ y, f (y i) ∂(W x) = ∫⁻ t, f ((x i) + t) ∂𝒩(0, N i)
    have h_fibre : ∀ x : Fin n → ℝ, ∫⁻ y, f (y i) ∂(W x)
        = ∫⁻ t, f ((x i) + t) ∂(gaussianReal 0 (N i)) := by
      intro x
      -- `i`-marginal of the Gaussian product fibre is `gaussianReal (x i) (N i)`
      have h_eval := Measure.pi_map_eval (μ := fun j => gaussianReal (x j) (N j)) i
      have h_one : (∏ j ∈ Finset.univ.erase i, (gaussianReal (x j) (N j)) Set.univ) = 1 :=
        Finset.prod_eq_one (fun j _ => measure_univ)
      have h_marg : (Measure.pi (fun j => gaussianReal (x j) (N j))).map (fun y : Fin n → ℝ => y i)
          = gaussianReal (x i) (N i) := by
        rw [show (fun y : Fin n → ℝ => y i) = Function.eval i from rfl, h_eval, h_one, one_smul]
      calc ∫⁻ y, f (y i) ∂(W x)
          = ∫⁻ y, f (y i) ∂(Measure.pi (fun j => gaussianReal (x j) (N j))) := by
              rw [hW, parallelGaussianChannel_apply]
        _ = ∫⁻ yi, f yi ∂((Measure.pi (fun j => gaussianReal (x j) (N j))).map
              (fun y : Fin n → ℝ => y i)) := (lintegral_map hf hmeas_i).symm
        _ = ∫⁻ yi, f yi ∂(gaussianReal (x i) (N i)) := by rw [h_marg]
        _ = ∫⁻ t, f ((x i) + t) ∂(gaussianReal 0 (N i)) := by
              rw [InformationTheory.Shannon.AWGN.gaussianReal_eq_map_const_add (N i) (x i),
                lintegral_map hf (measurable_const_add (x i))]
    have hfi_meas : Measurable (fun z : Fin n → ℝ => f (z i)) := hf.comp hmeas_i
    have hLHS : ∫⁻ a, f a ∂((outputDistribution p W).map (fun z => z i))
        = ∫⁻ x, (∫⁻ t, f ((x i) + t) ∂(gaussianReal 0 (N i))) ∂p := by
      calc ∫⁻ a, f a ∂((outputDistribution p W).map (fun z => z i))
          = ∫⁻ y, f (y i) ∂(outputDistribution p W) := lintegral_map hf hmeas_i
        _ = ∫⁻ z, f (z.2 i) ∂(p ⊗ₘ W) := by
              rw [outputDistribution, jointDistribution_def, Measure.snd]
              exact lintegral_map hfi_meas measurable_snd
        _ = ∫⁻ x, (∫⁻ y, f (y i) ∂(W x)) ∂p :=
              Measure.lintegral_compProd (hfi_meas.comp measurable_snd)
        _ = ∫⁻ x, (∫⁻ t, f ((x i) + t) ∂(gaussianReal 0 (N i))) ∂p :=
              lintegral_congr (fun x => h_fibre x)
    -- RHS = ∫⁻ a, f a ∂(Wi-output of p.map(·i)) = ∫⁻ x', (∫⁻ t, f (x' + t) ∂𝒩) ∂(p.map(·i))
    have hRHS : ∫⁻ a, f a ∂(ChannelCoding.outputDistribution (p.map (fun z => z i)) Wi)
        = ∫⁻ x, (∫⁻ t, f ((x i) + t) ∂(gaussianReal 0 (N i))) ∂p := by
      have h_inner : ∀ x' : ℝ, ∫⁻ y, f y ∂(Wi x')
          = ∫⁻ t, f (x' + t) ∂(gaussianReal 0 (N i)) := by
        intro x'
        rw [hWi, AWGN.awgnChannel_apply,
          InformationTheory.Shannon.AWGN.gaussianReal_eq_map_const_add (N i) x',
          lintegral_map hf (measurable_const_add x')]
      calc ∫⁻ a, f a ∂(ChannelCoding.outputDistribution (p.map (fun z => z i)) Wi)
          = ∫⁻ z, f z.2 ∂((p.map (fun z => z i)) ⊗ₘ Wi) := by
              rw [ChannelCoding.outputDistribution, jointDistribution_def, Measure.snd]
              exact lintegral_map hf measurable_snd
        _ = ∫⁻ x', (∫⁻ y, f y ∂(Wi x')) ∂(p.map (fun z => z i)) :=
              Measure.lintegral_compProd (hf.comp measurable_snd)
        _ = ∫⁻ x', (∫⁻ t, f (x' + t) ∂(gaussianReal 0 (N i))) ∂(p.map (fun z => z i)) :=
              lintegral_congr (fun x' => h_inner x')
        _ = ∫⁻ x, (∫⁻ t, f ((x i) + t) ∂(gaussianReal 0 (N i))) ∂p := by
              have h_meas_inner : Measurable
                  (fun x' : ℝ => ∫⁻ t, f (x' + t) ∂(gaussianReal 0 (N i))) := by
                have := Measurable.lintegral_kernel_prod_right' (κ := Wi) (f := fun z => f z.2)
                  (hf.comp measurable_snd)
                simpa only [funext h_inner] using this
              exact lintegral_map h_meas_inner hmeas_i
    rw [hLHS, hRHS]
  rw [h_id, InformationTheory.Shannon.AWGN.outputDistribution_awgn_eq_conv]

/-- **Parallel-output marginal as 1-D AWGN output law.** A repackaging of
`parallelOutput_marginal_eq_conv`: the `i`-marginal of the correlated output equals the
1-D AWGN output law `outputDistribution (p.map (· i)) (awgnChannel (N i))`. This lets all
1-D AWGN Phase 6 lemmas (variance / log-density integrability) apply verbatim.
@audit:ok -/
theorem parallelOutput_marginal_eq_awgn_output (i : Fin n) :
    (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)
      = ChannelCoding.outputDistribution (p.map (fun z => z i))
          (AWGN.awgnChannel (N i) (AWGN.isAwgnChannelMeasurable (N i))) := by
  rw [parallelOutput_marginal_eq_conv N h_meas h_parallel_meas p i,
    InformationTheory.Shannon.AWGN.outputDistribution_awgn_eq_conv]

/-- **`i`-marginal inherits the 1-D AWGN power constraint.** The total constraint
`∑ⱼ ∫⁻ (xⱼ)² ∂p ≤ P` dominates the single coordinate `∫⁻ (xᵢ)² ∂p`, and the marginal
push-forward sends `∫⁻ y² ∂(p.map (· i)) = ∫⁻ (xᵢ)² ∂p`, so `p.map (· i) ∈
awgnPowerConstraintSet P`.
@audit:ok -/
theorem parallelMarginal_mem_awgnPowerConstraintSet (P : ℝ)
    (hp : p ∈ parallelGaussianPowerConstraintSet P) (i : Fin n) :
    p.map (fun z => z i) ∈ AWGN.awgnPowerConstraintSet P := by
  obtain ⟨hp_prob, hp_lint⟩ := hp
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  refine ⟨Measure.isProbabilityMeasure_map hmeas_i.aemeasurable, ?_⟩
  -- `∫⁻ y² ∂(p.map (· i)) = ∫⁻ (x i)² ∂p`
  rw [lintegral_map (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (y ^ 2))) hmeas_i]
  -- single coordinate ≤ total ≤ ofReal P
  refine le_trans ?_ hp_lint
  exact Finset.single_le_sum
    (f := fun j => ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x j) ^ 2) ∂p)
    (fun j _ => bot_le) (Finset.mem_univ i)

/-- Output law joint absolute continuity `μY ≪ volume` (Gaussian-smoothed full support).
The output is the fibre mixture `μY s = ∫⁻ x, (W x) s ∂p`; each fibre
`W x = Measure.pi (gaussianReal (x i) (N i)) ≪ volume` (Step A + `gaussianReal_absolutelyContinuous`,
needs `hN`), so the mixture is `≪ volume`.
@audit:ok -/
theorem parallelOutput_absolutelyContinuous_volume (hN : ∀ i, (N i : ℝ) ≠ 0) :
    outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)
      ≪ (volume : Measure (Fin n → ℝ)) := by
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have h_fibre_ac : ∀ x, W x ≪ (volume : Measure (Fin n → ℝ)) :=
    fun x => parallelChannel_fibre_absolutelyContinuous_volume N hN h_meas h_parallel_meas x
  -- `μY = (p ⊗ₘ W).map Prod.snd`; show `volume s = 0 → μY s = 0`.
  refine Measure.AbsolutelyContinuous.mk (fun s hs hvol => ?_)
  show (outputDistribution p W) s = 0
  rw [outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs)]
  rw [lintegral_eq_zero_iff (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd hs))]
  filter_upwards with x
  -- each fibre contributes 0
  show (W x) (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s)) = 0
  have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s)) = s := by
    ext y; simp
  rw [hpre]
  exact h_fibre_ac x hvol

/-- Each coordinate marginal `μY.map (· i) ≪ volume`.
The marginal is `μY.map (· i)`; the fibre's `i`-marginal `gaussianReal (x i) (N i) ≪ volume`,
so the mixture `i`-marginal is `≪ volume`.
@audit:ok -/
theorem parallelOutput_marginal_absolutelyContinuous_volume (hN : ∀ i, (N i : ℝ) ≠ 0)
    (i : Fin n) :
    (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
        (fun z => z i)
      ≪ (volume : Measure ℝ) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  -- fibre `i`-marginal: `(W x).map (· i) = gaussianReal (x i) (N i) ≪ volume`
  have h_fibre_marg_ac : ∀ x : Fin n → ℝ, (W x).map (fun z => z i) ≪ (volume : Measure ℝ) := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    have h_eval := Measure.pi_map_eval (μ := fun j => gaussianReal (x j) (N j)) i
    have h_one : (∏ j ∈ Finset.univ.erase i, (gaussianReal (x j) (N j)) Set.univ) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      exact measure_univ
    have h_eq : (Measure.pi (fun j => gaussianReal (x j) (N j))).map (fun z => z i)
        = gaussianReal (x i) (N i) := by
      rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, h_eval, h_one, one_smul]
    rw [h_eq]
    exact gaussianReal_absolutelyContinuous (x i) (by exact_mod_cast hN i)
  -- `(μY.map (· i)) s = ∫⁻ x, (W x).map (· i) s ∂p`, each fibre marginal AC.
  refine Measure.AbsolutelyContinuous.mk (fun s hs hvol => ?_)
  rw [Measure.map_apply hmeas_i hs, outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd (hmeas_i hs),
    Measure.compProd_apply (measurable_snd (hmeas_i hs))]
  rw [lintegral_eq_zero_iff
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd (hmeas_i hs)))]
  filter_upwards with x
  show (W x) (Prod.mk x ⁻¹' (Prod.snd ⁻¹' ((fun z : Fin n → ℝ => z i) ⁻¹' s))) = 0
  have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' ((fun z : Fin n → ℝ => z i) ⁻¹' s)))
      = (fun z : Fin n → ℝ => z i) ⁻¹' s := by
    ext y; simp
  rw [hpre, ← Measure.map_apply hmeas_i hs]
  exact h_fibre_marg_ac x hvol

/-- **Reverse full-support AC of each output coordinate marginal** `volume ≪ μY.map (· i)`.
Mirror of `parallelOutput_marginal_absolutelyContinuous_volume` with the fibre marginal
reverse AC `volume ≪ gaussianReal (x i) (N i)` (`gaussianReal_absolutelyContinuous'`).
@audit:ok -/
theorem volume_absolutelyContinuous_parallelOutput_marginal (hN : ∀ i, (N i : ℝ) ≠ 0)
    (i : Fin n) :
    (volume : Measure ℝ)
      ≪ (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i) := by
  classical
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  -- fibre `i`-marginal reverse AC: `volume ≪ (W x).map (· i) = gaussianReal (x i) (N i)`
  have h_fibre_marg_rev : ∀ x : Fin n → ℝ,
      (volume : Measure ℝ) ≪ (W x).map (fun z => z i) := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    have h_eval := Measure.pi_map_eval (μ := fun j => gaussianReal (x j) (N j)) i
    have h_one : (∏ j ∈ Finset.univ.erase i, (gaussianReal (x j) (N j)) Set.univ) = 1 :=
      Finset.prod_eq_one (fun j _ => measure_univ)
    have h_eq : (Measure.pi (fun j => gaussianReal (x j) (N j))).map (fun z => z i)
        = gaussianReal (x i) (N i) := by
      rw [show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl, h_eval, h_one, one_smul]
    rw [h_eq]
    exact gaussianReal_absolutelyContinuous' (x i) (by exact_mod_cast hN i)
  refine Measure.AbsolutelyContinuous.mk (fun s hs hmargs => ?_)
  rw [Measure.map_apply hmeas_i hs, outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd (hmeas_i hs),
    Measure.compProd_apply (measurable_snd (hmeas_i hs))] at hmargs
  rw [lintegral_eq_zero_iff
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd (hmeas_i hs)))]
    at hmargs
  have h_ae : ∀ᵐ x ∂p, (W x).map (fun z => z i) s = 0 := by
    filter_upwards [hmargs] with x hx
    have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' ((fun z : Fin n → ℝ => z i) ⁻¹' s)))
        = (fun z : Fin n → ℝ => z i) ⁻¹' s := by ext y; simp
    rw [hpre, ← Measure.map_apply hmeas_i hs] at hx
    exact hx
  obtain ⟨x, hx⟩ := h_ae.exists
  exact h_fibre_marg_rev x hx

/-- **Reverse full-support AC of the correlated output law** `volume ≪ μY`.
The output mixture `μY s = ∫⁻ x, (W x) s ∂p`; from `μY s = 0` the `p`-integral of the
nonnegative `x ↦ (W x) s` vanishes, so `(W x) s = 0` for `p`-a.e. `x` (in particular some
`x`, as `p` is a probability measure), whence `volume s = 0` by the reverse Gaussian-product
AC `volume ≪ W x` (`volume_absolutelyContinuous_pi_gaussian`, needs `hN`).
@audit:ok -/
theorem volume_absolutelyContinuous_parallelOutput (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (volume : Measure (Fin n → ℝ))
      ≪ outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) := by
  set W := parallelGaussianChannel N h_meas h_parallel_meas with hW
  -- reverse AC of each fibre
  have h_fibre_rev : ∀ x : Fin n → ℝ, (volume : Measure (Fin n → ℝ)) ≪ W x := by
    intro x
    rw [hW, parallelGaussianChannel_apply]
    exact volume_absolutelyContinuous_pi_gaussian x N hN
  refine Measure.AbsolutelyContinuous.mk (fun s hs hμYs => ?_)
  -- expand `μY s = ∫⁻ x, (W x) s ∂p` and conclude `(W x) s = 0` p-a.e.
  rw [outputDistribution, jointDistribution_def, Measure.snd,
    Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs)] at hμYs
  rw [lintegral_eq_zero_iff
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := W) (measurable_snd hs))]
    at hμYs
  -- `hμYs : (fun x => W x (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s))) =ᵐ[p] 0`; pick a point
  have h_ae : ∀ᵐ x ∂p, (W x) s = 0 := by
    filter_upwards [hμYs] with x hx
    have hpre : (Prod.mk x ⁻¹' (Prod.snd ⁻¹' s)) = s := by ext y; simp
    rwa [hpre] at hx
  -- a.e. nonempty under a probability measure
  obtain ⟨x, hx⟩ := h_ae.exists
  exact h_fibre_rev x hx

/-- Joint vs. product-of-marginals absolute continuity for the output law.
`μY ≪ volume` (`parallelOutput_absolutelyContinuous_volume`, Wave 1) composed with the
reverse `volume ≪ Measure.pi (μY.map (· i))` from `pi_absolutelyContinuous_reverse`, whose
componentwise mutual-AC hypotheses are the forward marginal AC
(`parallelOutput_marginal_absolutelyContinuous_volume`) and the reverse marginal AC
(`volume_absolutelyContinuous_parallelOutput_marginal`); all need `hN`.
@audit:ok -/
theorem parallelOutput_absolutelyContinuous_pi_marginals (hN : ∀ i, (N i : ℝ) ≠ 0) :
    outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)
      ≪ Measure.pi (fun i =>
          (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
            (fun z => z i)) := by
  refine (parallelOutput_absolutelyContinuous_volume N h_meas h_parallel_meas p hN).trans ?_
  exact pi_absolutelyContinuous_reverse _
    (fun i => parallelOutput_marginal_absolutelyContinuous_volume N h_meas h_parallel_meas p hN i)
    (fun i => volume_absolutelyContinuous_parallelOutput_marginal N h_meas h_parallel_meas p hN i)

/-- **1-D AWGN output log-density integrability over the output law itself.** The integrand
`log ((q.rnDeriv volume y).toReal)` is integrable against `q = outputDistribution p₁ (awgn N₁)`.
Derived from the joint form `outputDistribution_logDensity_integrable_joint` by the
snd-marginal pushforward (`q = (p₁ ⊗ₘ W).snd`).
@audit:ok -/
private theorem awgnOutput_logDensity_integrable_self (P : ℝ) (hP : 0 ≤ P)
    (Ni : ℝ≥0) (hNi : (Ni : ℝ) ≠ 0) (p₁ : Measure ℝ) [IsProbabilityMeasure p₁]
    (hp₁ : p₁ ∈ AWGN.awgnPowerConstraintSet P) :
    Integrable
      (fun y => Real.log
        ((ChannelCoding.outputDistribution p₁ (AWGN.awgnChannel Ni
          (AWGN.isAwgnChannelMeasurable Ni))).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p₁ (AWGN.awgnChannel Ni
        (AWGN.isAwgnChannelMeasurable Ni))) := by
  have hNi_NN : Ni ≠ 0 := fun h => hNi (by rw [h]; norm_num)
  set Wi := AWGN.awgnChannel Ni (AWGN.isAwgnChannelMeasurable Ni) with hWi
  set q := ChannelCoding.outputDistribution p₁ Wi with hq
  have h_joint := InformationTheory.Shannon.AWGN.outputDistribution_logDensity_integrable_joint
    hP hNi_NN (AWGN.isAwgnChannelMeasurable Ni) p₁ hp₁
  -- `q = (p₁ ⊗ₘ Wi).snd = (p₁ ⊗ₘ Wi).map Prod.snd`, integrand = (log(rnDeriv q vol ·)) ∘ snd
  have h_map : q = (p₁ ⊗ₘ Wi).map Prod.snd := by rw [hq]; rfl
  set g : ℝ → ℝ := fun y => Real.log ((q.rnDeriv volume y).toReal) with hg
  have hg_aesm : AEStronglyMeasurable g q :=
    ((Measure.measurable_rnDeriv q volume).ennreal_toReal.log).aestronglyMeasurable
  have hg_aesm' : AEStronglyMeasurable g ((p₁ ⊗ₘ Wi).map Prod.snd) := by rw [← h_map]; exact hg_aesm
  rw [show (fun z : ℝ × ℝ => Real.log ((q.rnDeriv volume z.2).toReal)) = g ∘ Prod.snd from rfl,
    ← integrable_map_measure hg_aesm' measurable_snd.aemeasurable, ← h_map] at h_joint
  exact h_joint

/-- Marginal log-density joint integrability. The integrand depends only on the `i`-th
coordinate; pushing forward to the marginal `μY.map(·i) = q` (1-D AWGN output), it reduces
to `awgnOutput_logDensity_integrable_self`.
@audit:ok -/
theorem parallelOutput_marginal_logDensity_integrable (P : ℝ) (hP : 0 ≤ P) (i : Fin n)
    (hN : (N i : ℝ) ≠ 0) (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    Integrable
      (fun z => Real.log
        (((outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)).map
          (fun z => z i)).rnDeriv volume (z i)).toReal)
      (outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas)) := by
  haveI hp_prob : IsProbabilityMeasure p := hp.1
  have hmeas_i : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  set μY := outputDistribution p (parallelGaussianChannel N h_meas h_parallel_meas) with hμY
  haveI : IsProbabilityMeasure μY := by rw [hμY]; infer_instance
  haveI : IsProbabilityMeasure (μY.map (fun z => z i)) :=
    Measure.isProbabilityMeasure_map hmeas_i.aemeasurable
  set g : ℝ → ℝ := fun y => Real.log (((μY.map (fun z => z i)).rnDeriv volume y).toReal) with hg
  -- integrand = g ∘ (·i); push to marginal
  have hg_aesm : AEStronglyMeasurable g (μY.map (fun z => z i)) :=
    ((Measure.measurable_rnDeriv _ volume).ennreal_toReal.log).aestronglyMeasurable
  rw [show (fun z : Fin n → ℝ => Real.log
      (((μY.map (fun z => z i)).rnDeriv volume (z i)).toReal)) = g ∘ (fun z => z i) from rfl,
    ← integrable_map_measure hg_aesm hmeas_i.aemeasurable]
  -- the marginal is the 1-D AWGN output; apply the self-integrability fact
  have h_mem : p.map (fun z => z i) ∈ AWGN.awgnPowerConstraintSet P :=
    parallelMarginal_mem_awgnPowerConstraintSet p P hp i
  rw [hμY, parallelOutput_marginal_eq_awgn_output N h_meas h_parallel_meas p i] at hg ⊢
  rw [hg]
  haveI : IsProbabilityMeasure (p.map (fun z => z i)) :=
    Measure.isProbabilityMeasure_map hmeas_i.aemeasurable
  exact awgnOutput_logDensity_integrable_self P hP (N i) hN (p.map (fun z => z i)) h_mem

end Phase1Regularity

end InformationTheory.Shannon.ParallelGaussian
