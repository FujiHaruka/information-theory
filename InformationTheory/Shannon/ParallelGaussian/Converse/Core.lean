import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.Basic
import InformationTheory.Shannon.ParallelGaussian.PerCoord
import InformationTheory.Shannon.AWGN.ContChannelMIDecomp
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.CapacityConverseMaxent
import Mathlib.MeasureTheory.Constructions.Pi

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding
open InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

example {n : ℕ} :
    MeasurableSpace.CountableOrCountablyGenerated (Fin n → ℝ) (Fin n → ℝ) := by
  infer_instance

/-! ## Product-measure absolute continuity -/

/-- `Measure.pi` preserves absolute continuity w.r.t. `volume`. If every factor
`μ i ≪ volume` (each a probability measure), then `Measure.pi μ ≪ volume`.

@audit:ok -/
theorem pi_absolutelyContinuous {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (h : ∀ i, μ i ≪ (volume : Measure ℝ)) :
    Measure.pi μ ≪ (volume : Measure (Fin n → ℝ)) := by
  classical
  -- write each factor as `volume.withDensity (rnDeriv (μ i) volume)`
  set f : Fin n → ℝ → ℝ≥0∞ := fun i ↦ (μ i).rnDeriv volume with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i ↦ Measure.measurable_rnDeriv (μ i) volume
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = μ i :=
    fun i ↦ Measure.withDensity_rnDeriv_eq (μ i) volume (h i)
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  -- `Measure.pi μ = (Measure.pi (fun _ => volume)).withDensity (∏ ...)`
  have h_pi_eq : Measure.pi μ
      = (Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
          (fun z ↦ ∏ i, f i (z i)) := by
    have h_factor : (fun i ↦ (volume : Measure ℝ).withDensity (f i)) = μ := funext h_eq
    rw [← h_factor]
    exact pi_withDensity_fin (fun _ : Fin n ↦ (volume : Measure ℝ)) hf_meas
  -- `volume : Measure (Fin n → ℝ) = Measure.pi (fun _ => volume)`
  rw [h_pi_eq, volume_pi]
  exact withDensity_absolutelyContinuous _ _

/-- Reverse `Measure.pi` absolute continuity from componentwise mutual AC. If every factor
is mutually absolutely continuous with `volume` (`ν i ≪ volume` and `volume ≪ ν i`), then
`volume ≪ Measure.pi ν`.

@audit:ok -/
theorem pi_absolutelyContinuous_reverse {n : ℕ} (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (h_ac : ∀ i, ν i ≪ (volume : Measure ℝ))
    (h_rev : ∀ i, (volume : Measure ℝ) ≪ ν i) :
    (volume : Measure (Fin n → ℝ)) ≪ Measure.pi ν := by
  classical
  set f : Fin n → ℝ → ℝ≥0∞ := fun i ↦ (ν i).rnDeriv volume with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i ↦ Measure.measurable_rnDeriv (ν i) volume
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = ν i :=
    fun i ↦ Measure.withDensity_rnDeriv_eq (ν i) volume (h_ac i)
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  have h_pi_eq : Measure.pi ν
      = (Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
          (fun z ↦ ∏ i, f i (z i)) := by
    have h_factor : (fun i ↦ (volume : Measure ℝ).withDensity (f i)) = ν := funext h_eq
    rw [← h_factor]
    exact pi_withDensity_fin (fun _ : Fin n ↦ (volume : Measure ℝ)) hf_meas
  rw [h_pi_eq, ← volume_pi]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (Finset.measurable_prod _
      (fun i _ ↦ (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
  · -- each `rnDeriv (ν i) volume` is a.e.-positive on `volume` (reverse AC)
    have h_pos : ∀ i, ∀ᵐ z ∂(volume : Measure ℝ), f i z ≠ 0 := by
      intro i
      filter_upwards [Measure.rnDeriv_pos' (h_rev i)] with z hz
      exact hz.ne'
    -- transfer each coordinate's a.e. to the product measure, then take the product
    have h_pos_pi : ∀ i, ∀ᵐ z ∂(volume : Measure (Fin n → ℝ)), f i (z i) ≠ 0 := by
      intro i
      rw [volume_pi]
      exact (Measure.quasiMeasurePreserving_eval
        (μ := fun _ : Fin n ↦ (volume : Measure ℝ)) i).ae (h_pos i)
    filter_upwards [eventually_countable_forall.mpr h_pos_pi] with z hz
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hz i)

/-- Reverse full-support AC for a Gaussian product fibre.
`volume ≪ Measure.pi (gaussianReal (x i) (N i))` whenever every `N i ≠ 0`, since the product
of everywhere-positive Gaussian densities gives the reverse AC.

@audit:ok -/
theorem volume_absolutelyContinuous_pi_gaussian {n : ℕ}
    (x : Fin n → ℝ) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0) :
    (volume : Measure (Fin n → ℝ)) ≪ Measure.pi (fun i ↦ gaussianReal (x i) (N i)) := by
  classical
  have hN' : ∀ i, (N i) ≠ 0 := fun i ↦ by
    intro h; exact hN i (by rw [h]; norm_num)
  set f : Fin n → ℝ → ℝ≥0∞ := fun i ↦ gaussianPDF (x i) (N i) with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i ↦ measurable_gaussianPDF _ _
  -- each factor as `volume.withDensity (gaussianPDF ...)`
  have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = gaussianReal (x i) (N i) :=
    fun i ↦ (gaussianReal_of_var_ne_zero (x i) (hN' i)).symm
  haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
    intro i; rw [h_eq i]; infer_instance
  -- `Measure.pi (gaussianReal ...) = (Measure.pi volume).withDensity (∏ f)`
  have h_pi_eq : Measure.pi (fun i ↦ gaussianReal (x i) (N i))
      = (Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
          (fun z ↦ ∏ i, f i (z i)) := by
    have h_factor : (fun i ↦ (volume : Measure ℝ).withDensity (f i))
        = fun i ↦ gaussianReal (x i) (N i) := funext h_eq
    rw [← h_factor]
    exact pi_withDensity_fin (fun _ : Fin n ↦ (volume : Measure ℝ)) hf_meas
  rw [h_pi_eq, ← volume_pi]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (Finset.measurable_prod _
      (fun i _ ↦ (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
  · -- the product density is everywhere `≠ 0` since each Gaussian pdf is positive
    refine Filter.Eventually.of_forall (fun z ↦ ?_)
    refine Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ?_)
    simp only [hf_def, gaussianPDF_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact gaussianPDFReal_pos (x i) (N i) (z i) (hN' i)

/-- Product → sum differential entropy identity. For a product of probability measures
`μ i ≪ volume` on `ℝ`, the joint differential entropy of `Measure.pi μ` is the coordinate sum
of the 1-D entropies, `jointDifferentialEntropyPi (Measure.pi μ) = ∑ i, differentialEntropy
(μ i)`. The per-component log-density integrability `h_int` is a regularity precondition
(satisfied by Gaussians).

@audit:ok -/
theorem jointDifferentialEntropyPi_pi_eq_sum {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (h_ac : ∀ i, μ i ≪ (volume : Measure ℝ))
    (h_int : ∀ i, Integrable (fun y ↦ Real.log ((μ i).rnDeriv volume y).toReal) (μ i)) :
    jointDifferentialEntropyPi (Measure.pi μ) = ∑ i, differentialEntropy (μ i) := by
  classical
  set P := Measure.pi μ with hP
  have hP_ac : P ≪ (volume : Measure (Fin n → ℝ)) := pi_absolutelyContinuous μ h_ac
  set a : Fin n → ℝ → ℝ≥0∞ := fun i ↦ (μ i).rnDeriv volume with ha_def
  have ha_meas : ∀ i, Measurable (a i) := fun i ↦ Measure.measurable_rnDeriv (μ i) volume
  -- (1) `jointDifferentialEntropyPi P = -∫ log(P.rnDeriv volume z).toReal ∂P`
  have h_step1 : jointDifferentialEntropyPi P
      = -∫ z, Real.log ((P.rnDeriv volume z).toReal) ∂P := by
    rw [integral_log_rnDeriv_self_eq_neg hP_ac, neg_neg]; rfl
  -- (2) rnDeriv-of-pi = product of component rnDerivs, a.e. P
  have h_rn_pi : (P.rnDeriv volume) =ᵐ[P] fun z ↦ ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i ↦ Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : P = (volume : Measure (Fin n → ℝ)).withDensity (fun z ↦ ∏ i, a i (z i)) := by
      rw [hP, ← (funext h_eq : (fun i ↦ (volume : Measure ℝ).withDensity (a i)) = μ)]
      rw [pi_withDensity_fin (fun _ : Fin n ↦ (volume : Measure ℝ)) ha_meas, volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ ↦ ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ ↦ (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (P.rnDeriv volume) =ᵐ[volume] fun z ↦ ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hP_ac.ae_le h_rn_vol
  -- (3) each component rnDeriv is a.e. positive + finite on P (so log of product splits)
  have h_pos : ∀ i, ∀ᵐ z ∂P, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), 0 < a i y := Measure.rnDeriv_pos (h_ac i)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂P, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), a i y < ∞ := (h_ac i).ae_le (Measure.rnDeriv_lt_top (μ i) volume)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  -- (4) `log((∏ aᵢ).toReal) =ᵐ[P] ∑ log(aᵢ.toReal)`
  have h_log_split : (fun z ↦ Real.log ((P.rnDeriv volume z).toReal))
      =ᵐ[P] fun z ↦ ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz]
    rw [ENNReal.toReal_prod, Real.log_prod]
    intro i _
    have : (0 : ℝ) < (a i (z i)).toReal := ENNReal.toReal_pos (hpos i).ne' (hlt i).ne
    exact this.ne'
  -- (5) per-component log-density is integrable over P (transfer from μ i)
  have h_int_P : ∀ i, Integrable (fun z ↦ Real.log ((a i (z i)).toReal)) P := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) P (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hcomp : (fun z : Fin n → ℝ ↦ Real.log ((a i (z i)).toReal))
        = (fun y ↦ Real.log ((a i y).toReal)) ∘ (Function.eval i) := rfl
    rw [hcomp]
    exact (hmp.integrable_comp
      ((((ha_meas i).ennreal_toReal.log).aestronglyMeasurable))).mpr (h_int i)
  -- (6) marginal projection: `∫ log(aⱼ(zⱼ)) ∂P = ∫ log(aⱼ) ∂(μ j) = -differentialEntropy(μ j)`
  have h_marg : ∀ i, (∫ z, Real.log ((a i (z i)).toReal) ∂P) = -differentialEntropy (μ i) := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) P (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hGmeas : AEStronglyMeasurable (fun y ↦ Real.log ((a i y).toReal)) (μ i) :=
      ((ha_meas i).ennreal_toReal.log).aestronglyMeasurable
    -- `∫ (G ∘ eval i) ∂P = ∫ G ∂((P.map (eval i))) = ∫ G ∂(μ i)`
    have h_map : (∫ z, Real.log ((a i (z i)).toReal) ∂P)
        = ∫ y, Real.log ((a i y).toReal) ∂(μ i) := by
      rw [← hmp.map_eq]
      exact (MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
        (by rw [hmp.map_eq]; exact hGmeas)).symm
    rw [h_map, ha_def, integral_log_rnDeriv_self_eq_neg (h_ac i)]
    rfl
  -- assemble
  rw [h_step1, integral_congr_ae h_log_split, integral_finsetSum _ (fun i _ ↦ h_int_P i)]
  rw [show (∑ i, ∫ z, Real.log ((a i (z i)).toReal) ∂P) = ∑ i, -differentialEntropy (μ i) from
    Finset.sum_congr rfl (fun i _ ↦ h_marg i)]
  rw [Finset.sum_neg_distrib, neg_neg]

/-- Per-Gaussian log-density integrability. For `v ≠ 0`,
`log ((gaussianReal m v).rnDeriv volume y).toReal` is integrable against `gaussianReal m v`;
it is the affine-in-`(y-m)²` function `-(1/2)log(2πv) - (y-m)²/(2v)`.

@audit:ok -/
theorem gaussianReal_logRnDeriv_integrable (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y ↦ Real.log ((gaussianReal m v).rnDeriv volume y).toReal)
      (gaussianReal m v) := by
  have hv_pos : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg
    (Ne.symm (by exact_mod_cast hv))
  -- `(y - m)²` is integrable: `id - const` is MemLp 2
  have h_memLp : MemLp (fun y : ℝ ↦ y - m) 2 (gaussianReal m v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const m)
  have h_sq_int : Integrable (fun y ↦ (y - m) ^ 2) (gaussianReal m v) := h_memLp.integrable_sq
  -- rewrite the log-rnDeriv as the affine-in-`(y-m)²` function
  have h_rn : ∀ᵐ y ∂(gaussianReal m v),
      Real.log ((gaussianReal m v).rnDeriv volume y).toReal
        = -(1/2) * Real.log (2 * Real.pi * v) - (y - m) ^ 2 / (2 * v) := by
    have h_ac : gaussianReal m v ≪ volume := gaussianReal_absolutelyContinuous m hv
    filter_upwards [h_ac.ae_le (rnDeriv_gaussianReal m v)] with y hy
    rw [hy, toReal_gaussianPDF, log_gaussianPDFReal_eq m hv y]
  have h_affine_int : Integrable
      (fun y ↦ -(1/2) * Real.log (2 * Real.pi * v) - (y - m) ^ 2 / (2 * v))
      (gaussianReal m v) :=
    (integrable_const _).sub (h_sq_int.div_const (2 * v))
  refine h_affine_int.congr ?_
  filter_upwards [h_rn] with y hy
  exact hy.symm

/-! ## Channel↔RV MI decomposition, generic lift

The single-coordinate decomposition is hardwired to `Measure ℝ` / `differentialEntropy`.
The same chain is re-derived over a generic measurable space `β` with a `SigmaFinite`
reference measure `vol`, producing the entropy in raw `∫ log(rnDeriv) ∂` form, then
specialized to `β = Fin n → ℝ`, `vol = volume`. -/

section GenericDecomp

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {p : Measure α} [IsProbabilityMeasure p]
variable {W : Channel α β} [IsMarkovKernel W]
variable {vol : Measure β} [SigmaFinite vol]

/-- Generic per-measure log-density split (Bayes step). Mirror of
`ContChannelMIDecomp.log_rnDeriv_split` over an arbitrary measurable space with a
`SigmaFinite` reference measure `vol`. -/
private theorem log_rnDeriv_split_gen
    {ν q : Measure β} [SigmaFinite ν] [SigmaFinite q]
    (hνq : ν ≪ q) (hq_vol : q ≪ vol) :
    (fun y ↦ Real.log ((ν.rnDeriv q y).toReal))
      =ᵐ[ν]
    (fun y ↦ Real.log ((ν.rnDeriv vol y).toReal)
                - Real.log ((q.rnDeriv vol y).toReal)) := by
  have h_chain : (fun y ↦ ν.rnDeriv q y * q.rnDeriv vol y)
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

/-- Generic Bayes density split of the joint llr. Mirror of
`ContChannelMIDecomp.llr_compProd_prod_split` over `α β` with `vol`. -/
private theorem llr_compProd_prod_split_gen
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (q : Measure β) [IsProbabilityMeasure q]
    (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ vol)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y ↦ (W x).rnDeriv vol y) =ᵐ[W x] fun y ↦ g (x, y)) :
    (fun z ↦ llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z ↦ Real.log (g z).toReal
                - Real.log (q.rnDeriv vol z.2).toReal) := by
  have h_prod : p.prod q = p ⊗ₘ (Kernel.const α q) := (Measure.compProd_const).symm
  have h_ac' : (p ⊗ₘ W) ≪ p ⊗ₘ (Kernel.const α q) := by rwa [h_prod] at h_joint_ac
  have h1 : (p ⊗ₘ W).rnDeriv (p.prod q)
      =ᵐ[p ⊗ₘ W] fun z ↦ Kernel.rnDeriv W (Kernel.const α q) z.1 z.2 := by
    rw [h_prod]
    exact h_ac'.ae_le (rnDeriv_compProd_fibre h_ac')
  have h_split : (fun z ↦ Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal)
      =ᵐ[p ⊗ₘ W] fun z ↦ Real.log (g z).toReal
                  - Real.log (q.rnDeriv vol z.2).toReal := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const α q)).ennreal_toReal.log
      · exact (hg_meas.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q vol).comp measurable_snd).ennreal_toReal.log)
    · filter_upwards with a
      have hker : (fun b ↦ Kernel.rnDeriv W (Kernel.const α q) a b)
          =ᵐ[W a] fun b ↦ (W a).rnDeriv q b := by
        have := (hWx_q a).ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := W) (η := Kernel.const α q) (a := a))
        exact this
      filter_upwards [hker, log_rnDeriv_split_gen (vol := vol) (hWx_q a) hq_vol, hg_ae a]
        with b hb hb_split hg_b
      rw [hb, hb_split, hg_b]
  have h_llr_eq : (fun z ↦ llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
      fun z ↦ Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal := by
    simp only [llr_def]
    filter_upwards [h1] with z hz1
    rw [hz1]
  exact h_llr_eq.trans h_split

/-- Generic continuous-channel MI chain rule (entropy in raw integral form).
`(mutualInfoOfChannel p W).toReal = (−∫_y log(dq/dvol) ∂q) − ∫_x (−∫_y log(d(Wx)/dvol) ∂(Wx)) dp`.
Specialized below to `jointDifferentialEntropyPi` via `integral_log_rnDeriv_self_eq_neg`.
@audit:ok -/
private theorem mutualInfoOfChannel_toReal_eq_neg_integral_log_sub
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (hW_ac : ∀ x, W x ≪ vol)
    (hWx_q : ∀ x, W x ≪ outputDistribution p W)
    (hq_ac : outputDistribution p W ≪ vol)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y ↦ (W x).rnDeriv vol y) =ᵐ[W x] fun y ↦ g (x, y))
    (h_int_fibre : Integrable (fun z : α × β ↦ Real.log (g z).toReal) (p ⊗ₘ W))
    (h_int_out : Integrable
        (fun z : α × β ↦ Real.log
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
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ ?_))
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
    set F : β → ℝ := fun y ↦ Real.log (q.rnDeriv vol y).toReal with hF
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

/-- Channel↔RV MI decomposition, `Fin n → ℝ` lift. Specializes the generic chain rule to
`β = Fin n → ℝ`, `vol = volume`, producing the entropy in `jointDifferentialEntropyPi` form.
The absolute-continuity / log-density-integrability hypotheses are regularity preconditions.

@audit:ok -/
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
    (hg_ae : ∀ x, (fun y ↦ ((parallelGaussianChannel N h_meas h_parallel_meas) x).rnDeriv volume y)
        =ᵐ[(parallelGaussianChannel N h_meas h_parallel_meas) x] fun y ↦ g (x, y))
    (h_int_fibre : Integrable (fun z ↦ Real.log (g z).toReal)
        (p ⊗ₘ (parallelGaussianChannel N h_meas h_parallel_meas)))
    (h_int_out : Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ Real.log
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
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ ?_))
  exact h_fibre_bridge x

/-! ## Correlated-output regularity preconditions

The decomposition and the subadditivity step both consume regularity preconditions of the
correlated output law `μY := outputDistribution p (parallelGaussianChannel N …)`: absolute
continuity of the joint and of every coordinate marginal w.r.t. Lebesgue measure, the
joint-vs-product absolute continuity, and the log-density integrabilities. These follow from
Gaussian smoothing (each fibre is a full-support product, so the output is
volume-equivalent), supplied here for an arbitrary correlated input as named lemmas. -/

/-- Each fibre is absolutely continuous w.r.t. volume. Each component
`gaussianReal (x i) (N i) ≪ volume`, so the product fibre is `≪ volume`.

@audit:ok -/
theorem parallelChannel_fibre_absolutelyContinuous_volume {n : ℕ} (N : Fin n → ℝ≥0)
    (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (x : Fin n → ℝ) :
    (parallelGaussianChannel N h_meas h_parallel_meas) x ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [parallelGaussianChannel_apply]
  refine pi_absolutelyContinuous (fun i ↦ gaussianReal (x i) (N i)) (fun i ↦ ?_)
  exact gaussianReal_absolutelyContinuous (x i) (by exact_mod_cast hN i)

/-- Gaussian-PDF-product proxy density `z ↦ ∏ᵢ gaussianPDF (z.1 i) (N i) (z.2 i)` for the
`Fin n → ℝ` fibre, named so the decomposition lift receives a single atomic `g` argument
rather than a `∏ gaussianPDF` lambda that the unifier repeatedly expands.

@audit:ok -/
noncomputable def piGaussProxy {n : ℕ} (N : Fin n → ℝ≥0)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ≥0∞ :=
  ∏ i, gaussianPDF (z.1 i) (N i) (z.2 i)

set_option maxHeartbeats 1000000 in
theorem piGaussProxy_measurable {n : ℕ} (N : Fin n → ℝ≥0) :
    Measurable (piGaussProxy N) := by
  unfold piGaussProxy
  refine Finset.measurable_prod _ (fun i _ ↦ ?_)
  -- unwrap `gaussianPDF = ENNReal.ofReal ∘ gaussianPDFReal` first to avoid an `isDefEq`
  -- whnf-loop on the `ofReal` wrapper: go through the ℝ-valued uncurry, then re-wrap.
  simp only [gaussianPDF]
  apply Measurable.ennreal_ofReal
  exact (InformationTheory.Shannon.AWGN.measurable_gaussianPDFReal_uncurry (N i)).comp
    (Measurable.prodMk ((measurable_pi_apply i).comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd))

end InformationTheory.Shannon.ParallelGaussian
