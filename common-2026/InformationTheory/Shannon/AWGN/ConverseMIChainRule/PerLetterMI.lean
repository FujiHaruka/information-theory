import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityAEP
import InformationTheory.Shannon.BlockwiseChannel.Definition
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.MultivariateDiffEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import InformationTheory.Shannon.AWGN.ConverseMIChainRule.PerLetterIntegrability
import InformationTheory.Shannon.AWGN.ConverseMIChainRule.BlockMI

/-! # Per-letter MI decomposition and continuous MI chain rule -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-- Joint measurability of `(x, y) ↦ gaussianPDF x N y` (mean × point). -/
private lemma gaussianPDF_joint_measurable (N : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ ↦ gaussianPDF p.1 N p.2) := by
  unfold gaussianPDF
  refine ENNReal.measurable_ofReal.comp ?_
  unfold gaussianPDFReal
  refine Measurable.mul measurable_const ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.div ?_ measurable_const
  refine (Measurable.pow ?_ measurable_const).neg
  exact (measurable_snd.sub measurable_fst)

/-- Per-letter input law `μ.map (encoder · i)` (discrete, real-valued). -/
private noncomputable def perLetterInputLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (converseJointInline h_meas c).map (fun ω ↦ c.encoder ω.1 i)

instance perLetterInputLaw_isProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    IsProbabilityMeasure (perLetterInputLaw h_meas c i) := by
  rw [perLetterInputLaw]
  exact Measure.isProbabilityMeasure_map
    (((measurable_of_countable (fun m : Fin M ↦ c.encoder m i)).comp measurable_fst).aemeasurable)

/-- `perLetterInputLaw_i = (1/M) • ∑ₘ δ_{encoder m i}` (mixture-of-diracs form). -/
private lemma perLetterInputLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterInputLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
  classical
  unfold perLetterInputLaw converseJointInline
  have henc_i : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1 i) :=
    (measurable_of_countable (fun m : Fin M ↦ c.encoder m i)).comp measurable_fst
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j))))
      henc_i.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  -- `((δ_m).prod ν).map (fun ω => encoder ω.1 i) = (δ_m).map (encoder · i) = δ_{encoder m i}`
  rw [show (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1 i)
        = (fun a : Fin M ↦ c.encoder a i) ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_of_countable _) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul,
    MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]

/-- **Per-letter X-input factorization** (mixture-of-diracs, holds with collisions):
`μ.map (fun ω => (encoder ω.1 i, ω.2 i)) = perLetterInputLaw_i ⊗ₘ awgnChannel`. -/
private lemma perLetter_map_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω : Fin M × (Fin n → ℝ) ↦ (c.encoder ω.1 i, ω.2 i))
      = perLetterInputLaw h_meas c i ⊗ₘ awgnChannel N h_meas := by
  classical
  -- RHS: explicit mixture of diracs ⊗ₘ awgnChannel = (1/M) ∑ₘ δ_{encoder m i} ⊗ awgn
  rw [perLetterInputLaw_eq_mixture h_meas c i, Measure.compProd_smul_left]
  rw [← Measure.sum_fintype (fun m : Fin M ↦ Measure.dirac (c.encoder m i)),
    Measure.compProd_sum_left, Measure.sum_fintype, Fintype.card_fin]
  -- LHS: distribute the map over the mixture
  unfold converseJointInline
  have hmap_fn : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun m : Fin M ↦ c.encoder m i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j))))
      hmap_fn.aemeasurable]
  have h_per : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j)))).map
            (fun ω : Fin M × (Fin n → ℝ) ↦ (c.encoder ω.1 i, ω.2 i))
        = (Measure.dirac (c.encoder m i)) ⊗ₘ awgnChannel N h_meas := by
    intro m
    -- per-message: `((δ_m).prod (pi gaussian)).map (encoder·i, ·.2 i) = δ_{encoder m i} ⊗ₘ awgn`
    rw [show (Measure.dirac (c.encoder m i)) ⊗ₘ awgnChannel N h_meas
          = (Measure.dirac (c.encoder m i)).prod (awgnChannel N h_meas (c.encoder m i)) by
        ext s hs
        rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
          Measure.map_apply measurable_prodMk_left hs]]
    -- LHS per-message
    rw [show (fun ω : Fin M × (Fin n → ℝ) ↦ (c.encoder ω.1 i, ω.2 i))
          = Prod.map (fun a : Fin M ↦ c.encoder a i) (fun y : Fin n → ℝ ↦ y i) from rfl]
    rw [← Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_pi_apply i)]
    rw [MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]
    congr 1
    -- `(pi (gaussian (encoder m j))).map (·i) = gaussian (encoder m i) = awgnChannel (encoder m i)`
    rw [Measure.pi_map_eval]
    have h_prod_one : (∏ j ∈ Finset.univ.erase i,
        (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
      refine Finset.prod_eq_one (fun j _ ↦ ?_)
      rw [awgnChannel_apply]; exact measure_univ
    rw [h_prod_one, one_smul, awgnChannel_apply]
  rw [Finset.sum_congr rfl (fun m _ ↦ h_per m), Fintype.card_fin]

/-- Positivity of the per-letter mixture density (single full-support component suffices). -/
private lemma perLetterMixtureDensity_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (i : Fin n) (y : ℝ) :
    0 < (perLetterMixtureDensity N c i y).toReal := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM_pos y)
  rw [ENNReal.toReal_pos_iff]
  refine ⟨?_, lt_of_le_of_ne le_top h_ne_top⟩
  unfold perLetterMixtureDensity
  refine ENNReal.mul_pos ?_ ?_
  · simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top M
  · -- `∑ₘ gaussianPDF ... ≠ 0` (single component positive)
    have h_comp_pos : 0 < gaussianPDF (c.encoder m₀ i) N y := by
      rw [gaussianPDF, ENNReal.ofReal_pos]
      exact gaussianPDFReal_pos (c.encoder m₀ i) N y hN
    refine (lt_of_lt_of_le h_comp_pos (Finset.single_le_sum
      (f := fun m ↦ gaussianPDF (c.encoder m i) N y) (fun m _ ↦ zero_le')
      (Finset.mem_univ m₀))).ne'

/-- `perLetterYLaw_i ≪ volume` (mixture of full-support Gaussians). -/
private lemma perLetterLaw_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) ≪ (volume : Measure ℝ) := by
  rw [perLetterLaw_withDensity h_meas c i (Nat.pos_of_ne_zero (NeZero.ne M)) hN]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- `volume ≪ perLetterYLaw_i` (mixture density everywhere positive). -/
private lemma volume_ac_perLetterLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (volume : Measure ℝ) ≪ (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) := by
  rw [perLetterLaw_withDensity h_meas c i (Nat.pos_of_ne_zero (NeZero.ne M)) hN]
  refine withDensity_absolutelyContinuous'
    (perLetterMixtureDensity_measurable N c i).aemeasurable ?_
  refine Filter.Eventually.of_forall (fun y ↦ ?_)
  have := perLetterMixtureDensity_pos hN c i y
  simp only [ne_eq]
  intro h0
  rw [h0] at this; simp at this

/-- **Marginal identification**: `blockYLawInline.map (· i) = (converseJointInline).map (·.2 i)`
= the per-letter law `Y_i`. -/
private lemma blockYLawInline_map_eval
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (blockYLawInline h_meas c).map (fun y ↦ y i)
      = (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) := by
  show ((converseJointInline h_meas c).map Prod.snd).map (fun y ↦ y i)
      = (converseJointInline h_meas c).map (fun ω ↦ ω.2 i)
  rw [Measure.map_map (measurable_pi_apply i) measurable_snd]
  rfl

/-- Per-letter MI = channel MI: `mutualInfo μ X_i Y_i = mutualInfoOfChannel inputLaw_i awgn`. -/
private lemma perLetterMI_eq_channel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    mutualInfo (converseJointInline h_meas c)
        (fun ω ↦ c.encoder ω.1 i) (fun ω ↦ ω.2 i)
      = ChannelCoding.mutualInfoOfChannel (perLetterInputLaw h_meas c i)
          (awgnChannel N h_meas) := by
  classical
  set μ := converseJointInline h_meas c with hμ
  set p := perLetterInputLaw h_meas c i with hp
  set W := awgnChannel N h_meas with hW
  have hX_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1 i) :=
    (measurable_of_countable (fun m : Fin M ↦ c.encoder m i)).comp measurable_fst
  have hY_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hpair_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ (c.encoder ω.1 i, ω.2 i)) :=
    hX_meas.prodMk hY_meas
  -- `mutualInfoOfChannel = klDiv (p ⊗ₘ W) (p.prod (outputDistribution p W))`
  rw [ChannelCoding.mutualInfoOfChannel_def, ChannelCoding.jointDistribution_def]
  -- `mutualInfo μ X_i Y_i = klDiv (μ.map (X_i,Y_i)) ((μ.map X_i).prod (μ.map Y_i))`
  unfold mutualInfo
  -- joint: `μ.map (X_i,Y_i) = p ⊗ₘ W`
  have h_joint : μ.map (fun ω ↦ (c.encoder ω.1 i, ω.2 i)) = p ⊗ₘ W := by
    rw [hμ, hp, hW]; exact perLetter_map_eq_compProd h_meas c i
  -- input marginal: `μ.map X_i = p`
  have h_in : μ.map (fun ω ↦ c.encoder ω.1 i) = p := by rw [hp, perLetterInputLaw]
  -- output marginal: `μ.map Y_i = outputDistribution p W`
  have h_out : μ.map (fun ω ↦ ω.2 i) = ChannelCoding.outputDistribution p W := by
    show μ.map (fun ω ↦ ω.2 i) = (p ⊗ₘ W).map Prod.snd
    rw [← h_joint, Measure.map_map measurable_snd hpair_meas]
    rfl
  rw [h_joint, h_in, h_out]

/-- Any measurable real function is integrable against the finite-support `perLetterInputLaw`
(a `(1/M)`-weighted sum of `M` Diracs). -/
private lemma integrable_of_perLetterInputLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (perLetterInputLaw h_meas c i) := by
  classical
  rw [perLetterInputLaw_eq_mixture h_meas c i]
  have hM_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ ↦ ?_)
  exact integrable_dirac (enorm_lt_top)

/-- Per-fibre output log-density integrability (1-D): `log (rnDeriv perLetterYLaw_i vol)`
integrable against each Gaussian fibre `gaussian x N`. -/
private lemma integrable_log_perLetterLaw_on_fibre
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (x : ℝ) :
    Integrable
      (fun y ↦ Real.log
        (((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)).rnDeriv volume y).toReal)
      (gaussianReal x N) := by
  classical
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set q := (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) with hq
  set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
  have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
  have hq_wd : q = volume.withDensity f := by
    rw [hq, hf_def]; exact perLetterLaw_withDensity h_meas c i hM_pos hN
  have hgx_ac : gaussianReal x N ≪ (volume : Measure ℝ) := gaussianReal_absolutelyContinuous x hN
  have h_rn_vol : q.rnDeriv volume =ᵐ[volume] f := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
  have h_log_ae : (fun y ↦ Real.log (q.rnDeriv volume y).toReal)
      =ᵐ[gaussianReal x N] (fun y ↦ Real.log ((perLetterMixtureDensity N c i y).toReal)) := by
    filter_upwards [hgx_ac.ae_le h_rn_vol] with y hy
    rw [hy]
  refine (Integrable.congr ?_ h_log_ae.symm)
  obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM_pos hN
  have h_sq_int : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal x N) :=
    (memLp_id_gaussianReal (μ := x) (v := N) 2).integrable_sq
  have h_dom : Integrable (fun y : ℝ ↦ c₀ + c₁ * y ^ 2) (gaussianReal x N) :=
    (integrable_const c₀).add (h_sq_int.const_mul c₁)
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp
      (perLetterMixtureDensity_measurable N c i).ennreal_toReal).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs]
    exact h_abs y

/-- **Per-letter MI decomposition**: `I(X_i;Y_i).toReal = h(Y_i) − h(noise)`. -/
private lemma perLetterMI_decomp
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω ↦ c.encoder ω.1 i) (fun ω ↦ ω.2 i)).toReal
      = InformationTheory.Shannon.differentialEntropy
          ((converseJointInline h_meas c).map (fun ω ↦ ω.2 i))
        - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  classical
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set p := perLetterInputLaw h_meas c i with hp
  set W := awgnChannel N h_meas with hW
  have hpair_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun m : Fin M ↦ c.encoder m i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  -- output distribution `q = perLetterYLaw_i`
  have hq_eq : ChannelCoding.outputDistribution p W
      = (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) := by
    show ((p ⊗ₘ W).map Prod.snd) = _
    rw [hp, hW, ← perLetter_map_eq_compProd h_meas c i]
    rw [Measure.map_map measurable_snd hpair_meas]
    rfl
  -- regularity
  have hW_ac : ∀ x, W x ≪ (volume : Measure ℝ) := by
    intro x; rw [hW, awgnChannel_apply]; exact gaussianReal_absolutelyContinuous x hN
  have hq_ac : ChannelCoding.outputDistribution p W ≪ (volume : Measure ℝ) := by
    rw [hq_eq]; exact perLetterLaw_ac_volume hN h_meas c i
  have hvol_ac_q : (volume : Measure ℝ) ≪ ChannelCoding.outputDistribution p W := by
    rw [hq_eq]; exact volume_ac_perLetterLaw hN h_meas c i
  have hWx_q : ∀ x, W x ≪ ChannelCoding.outputDistribution p W :=
    fun x ↦ (hW_ac x).trans hvol_ac_q
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod (ChannelCoding.outputDistribution p W) := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    exact Filter.Eventually.of_forall (fun x ↦ by
      simpa only [Kernel.const_apply] using hWx_q x)
  -- proxy `g (x, y) := gaussianPDF x N y`
  set g : ℝ × ℝ → ℝ≥0∞ := fun z ↦ gaussianPDF z.1 N z.2 with hg
  have hg_meas : Measurable g := gaussianPDF_joint_measurable N
  have hg_ae : ∀ x, (fun y ↦ (W x).rnDeriv volume y) =ᵐ[W x] fun y ↦ g (x, y) := by
    intro x
    rw [hW, awgnChannel_apply]
    filter_upwards [(gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)]
      with y hy
    rw [hy]
  -- per-fibre log-density integrability against `W x = gaussian x N`
  have h_int_fibre_self : ∀ x, Integrable (fun y ↦ Real.log (g (x, y)).toReal) (W x) := by
    intro x
    have hint := gaussianReal_logRnDeriv_integrable_inline x hN
    have hWx : W x = gaussianReal x N := by rw [hW, awgnChannel_apply]
    rw [hWx]
    refine hint.congr ?_
    filter_upwards [(gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)]
      with y hy
    rw [hg]; simp only; rw [hy]
  -- `h_fibre_self` (proxy integral = rnDeriv integral, per fibre)
  have h_fibre_self : ∀ x, ∫ y, Real.log (g (x, y)).toReal ∂(W x)
      = ∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x) := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hg_ae x] with y hy
    rw [← hy]
  -- output log-density integrability against q (= perLetterYLaw_i)
  have h_out_self : Integrable
      (fun y ↦ Real.log ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p W) := by
    rw [hq_eq]
    set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) with hν
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν]
      exact Measure.isProbabilityMeasure_map
        (((measurable_pi_apply i).comp measurable_snd).aemeasurable)
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν, hf_def]; exact perLetterLaw_withDensity h_meas c i hM_pos hN
    have hν_ac : ν ≪ (volume : Measure ℝ) := by
      rw [hν_wd]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have h_rn_vol : ν.rnDeriv volume =ᵐ[volume] f := by
      conv_lhs => rw [hν_wd]
      exact Measure.rnDeriv_withDensity volume hf_meas
    have h_log_ae : (fun y ↦ Real.log (ν.rnDeriv volume y).toReal)
        =ᵐ[ν] (fun y ↦ Real.log ((perLetterMixtureDensity N c i y).toReal)) := by
      filter_upwards [hν_ac.ae_le h_rn_vol] with y hy
      rw [hy]
    refine (Integrable.congr ?_ h_log_ae.symm)
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM_pos hN
    have h_dom : Integrable (fun y : ℝ ↦ c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add (((by
            rw [hν]; exact perLetterLaw_sq_integrable h_meas c i hM_pos hN)
        : Integrable (fun y : ℝ ↦ y ^ 2) ν).const_mul c₁)
    refine Integrable.mono' h_dom ?_ ?_
    · exact (Real.measurable_log.comp
        (perLetterMixtureDensity_measurable N c i).ennreal_toReal).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs]
      exact h_abs y
  -- compProd-level integrabilities (the `p`-norm-integrability is free: `p` is finite-support)
  have h_int_fibre : Integrable (fun z : ℝ × ℝ ↦ Real.log (g z).toReal) (p ⊗ₘ W) := by
    rw [Measure.integrable_compProd_iff
      ((hg_meas.ennreal_toReal.log).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun x ↦ h_int_fibre_self x), ?_⟩
    rw [hp]
    refine integrable_of_perLetterInputLaw h_meas c i ?_
    -- measurability of `x ↦ ∫ y, ‖log g(x,y)‖ ∂(W x)`
    have : StronglyMeasurable
        (fun x ↦ ∫ y, ‖Real.log (g (x, y)).toReal‖ ∂(W x)) :=
      (StronglyMeasurable.integral_kernel_prod_right' (κ := W)
        (f := fun z : ℝ × ℝ ↦ ‖Real.log (g z).toReal‖)
        (hg_meas.ennreal_toReal.log.norm.stronglyMeasurable))
    exact this.measurable
  have h_int_out : Integrable
      (fun z : ℝ × ℝ ↦ Real.log
          ((ChannelCoding.outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    rw [hq_eq]
    set ψ : ℝ → ℝ := fun y ↦ Real.log
      (((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)).rnDeriv volume y).toReal with hψ
    have hψ_meas : Measurable ψ :=
      (Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    show Integrable (fun z : ℝ × ℝ ↦ ψ z.2) (p ⊗ₘ W)
    rw [Measure.integrable_compProd_iff
      (f := fun z : ℝ × ℝ ↦ ψ z.2) ((hψ_meas.comp measurable_snd).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun x ↦ ?_), ?_⟩
    · -- per-fibre: `ψ` integrable against `W x = gaussian x N`
      have hWx : W x = gaussianReal x N := by rw [hW, awgnChannel_apply]
      rw [hWx]
      exact integrable_log_perLetterLaw_on_fibre hN h_meas c i x
    · -- `p`-norm-integrability (finite support)
      rw [hp]
      refine integrable_of_perLetterInputLaw h_meas c i ?_
      have : StronglyMeasurable (fun x ↦ ∫ y, ‖ψ y‖ ∂(W x)) :=
        (StronglyMeasurable.integral_kernel_prod_right' (κ := W)
          (f := fun z : ℝ × ℝ ↦ ‖ψ z.2‖)
          ((hψ_meas.comp measurable_snd).norm.stronglyMeasurable))
      exact this.measurable
  -- apply the generic 1-D decomposition
  rw [perLetterMI_eq_channel h_meas c i]
  rw [ChannelCoding.mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out]
  rw [hq_eq]
  -- fibre term: `∫ x, h(W x) ∂p = ∫ x, h(gaussian 0 N) ∂p = h(gaussian 0 N)`
  have h_fibre_ent : ∀ x, InformationTheory.Shannon.differentialEntropy (W x)
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro x
    rw [hW, awgnChannel_apply,
      InformationTheory.Shannon.differentialEntropy_gaussianReal x hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_fibre_ent), integral_const,
    probReal_univ, one_smul]

/-- `log(blockYLaw.rnDeriv vol)` integrable against `blockYLaw` itself (mixture of components). -/
private lemma integrable_log_blockYLawInline_self
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    Integrable
      (fun y ↦ Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal)
      (blockYLawInline h_meas c) := by
  classical
  set F : (Fin n → ℝ) → ℝ :=
    fun y ↦ Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal with hF
  rw [blockYLawInline_eq_mixture h_meas c]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ ↦ ?_)
  exact integrable_log_blockYLawInline_on_component hN h_meas c m

/-- `log(perLetterYLaw_i.rnDeriv vol (y i))` integrable against `blockYLaw` (per-coord marginal
log-density against the joint). -/
private lemma integrable_log_marg_on_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    Integrable
      (fun y ↦ Real.log
        ((((converseJointInline h_meas c).map (fun ω ↦ ω.2 i))).rnDeriv volume (y i)).toReal)
      (blockYLawInline h_meas c) := by
  classical
  set F : (Fin n → ℝ) → ℝ := fun y ↦ Real.log
      ((((converseJointInline h_meas c).map (fun ω ↦ ω.2 i))).rnDeriv volume (y i)).toReal with hF
  rw [blockYLawInline_eq_mixture h_meas c]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ ↦ ?_)
  -- `F y = (ψ ∘ eval i) y` where `ψ = log(perLetterYLaw_i.rnDeriv vol)`, integrable against the
  -- i-th 1-D Gaussian factor via `integrable_comp_eval`
  rw [hF]
  show Integrable (fun y : Fin n → ℝ ↦ Real.log
      (((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)).rnDeriv volume (y i)).toReal)
    (Measure.pi (fun j : Fin n ↦ gaussianReal (c.encoder m j) N))
  exact integrable_comp_eval (μ := fun j : Fin n ↦ gaussianReal (c.encoder m j) N) (i := i)
    (integrable_log_perLetterLaw_on_fibre hN h_meas c i (c.encoder m i))

/-- **n-D subadditivity for the block output law**: `h(Y^n) ≤ ∑ᵢ h(Y_i)`. -/
private lemma jointDifferentialEntropyPi_blockYLawInline_le_sum
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
      ≤ ∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
          ((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)) := by
  classical
  set q := blockYLawInline h_meas c with hq
  haveI : IsProbabilityMeasure q := by rw [hq]; infer_instance
  -- marginal identification: `q.map (·i) = perLetterYLaw_i`
  have h_marg_eq : ∀ i,
      q.map (fun y ↦ y i) = (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) :=
    fun i ↦ blockYLawInline_map_eval h_meas c i
  haveI : ∀ i, IsProbabilityMeasure (q.map (fun z ↦ z i)) := by
    intro i; rw [h_marg_eq i]
    exact Measure.isProbabilityMeasure_map
      (((measurable_pi_apply i).comp measurable_snd).aemeasurable)
  have h_marg_ac : ∀ i, (q.map (fun z ↦ z i)) ≪ (volume : Measure ℝ) := by
    intro i; rw [h_marg_eq i]; exact perLetterLaw_ac_volume hN h_meas c i
  have hμ_ac : q ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hq]; exact blockYLawInline_ac_volume hN h_meas c
  -- `q ≪ pi(marginals)` via `q ≪ vol` and `vol ≪ pi(marginals)`
  have hvol_ac_pi : (volume : Measure (Fin n → ℝ)) ≪
      Measure.pi (fun i ↦ q.map (fun z ↦ z i)) := by
    have h_rev : ∀ i, (volume : Measure ℝ) ≪ q.map (fun z ↦ z i) := by
      intro i; rw [h_marg_eq i]; exact volume_ac_perLetterLaw hN h_meas c i
    -- mirror of `pi_absolutelyContinuous_reverse`
    set f : Fin n → ℝ → ℝ≥0∞ := fun i ↦ (q.map (fun z ↦ z i)).rnDeriv volume with hf_def
    have hf_meas : ∀ i, Measurable (f i) := fun i ↦ Measure.measurable_rnDeriv _ _
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = q.map (fun z ↦ z i) :=
      fun i ↦ Measure.withDensity_rnDeriv_eq _ volume (h_marg_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_eq : Measure.pi (fun i ↦ q.map (fun z ↦ z i))
        = (Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
            (fun z ↦ ∏ i, f i (z i)) := by
      rw [← (funext h_eq : (fun i ↦ (volume : Measure ℝ).withDensity (f i))
          = fun i ↦ q.map (fun z ↦ z i))]
      exact InformationTheory.Shannon.pi_withDensity_fin
        (fun _ : Fin n ↦ (volume : Measure ℝ)) hf_meas
    rw [h_pi_eq, ← volume_pi]
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (Finset.measurable_prod _
        (fun i _ ↦ (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
    · -- each `f i (z i)` a.e.-positive on `volume` (from `volume ≪ q.map(·i)`)
      have h_pos : ∀ i, ∀ᵐ y ∂(volume : Measure ℝ), f i y ≠ 0 := by
        intro i
        have := Measure.rnDeriv_pos' (h_rev i)
        filter_upwards [this] with y hy using hy.ne'
      filter_upwards [eventually_countable_forall.mpr
        (fun i ↦ (Measure.quasiMeasurePreserving_eval
          (μ := fun _ : Fin n ↦ (volume : Measure ℝ)) i).ae (h_pos i))] with z hz
      simp only [ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and]
      intro i _
      exact hz i
  have h_joint_ac : q ≪ Measure.pi (fun i ↦ q.map (fun z ↦ z i)) := hμ_ac.trans hvol_ac_pi
  -- integrability
  have h_int_joint : Integrable (fun z ↦ Real.log ((q.rnDeriv volume z).toReal)) q := by
    rw [hq]; exact integrable_log_blockYLawInline_self hN h_meas c
  have h_int_marg : ∀ i, Integrable
      (fun z ↦ Real.log (((q.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal)) q := by
    intro i
    have h_eq : (fun z : Fin n → ℝ ↦
          Real.log (((q.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal))
        = (fun z ↦ Real.log
            ((((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)).rnDeriv volume
              (z i)).toReal)) := by
      funext z; rw [h_marg_eq i]
    rw [h_eq, hq]
    exact integrable_log_marg_on_blockYLawInline hN h_meas c i
  -- apply the n-D subadditivity bridge, then rewrite marginals
  have h_sub := InformationTheory.Shannon.jointDifferentialEntropyPi_le_sum
    (μ := q) h_marg_ac hμ_ac h_joint_ac h_int_joint h_int_marg
  rw [Finset.sum_congr rfl (fun i _ ↦ congrArg InformationTheory.Shannon.differentialEntropy
    (h_marg_eq i))] at h_sub
  exact h_sub

/-- Memoryless AWGN continuous MI chain rule.

`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)` on the inlined joint. The route:
`I(X^n;Y^n) ≤ I(W;Y^n)` (deterministic DPI) `= h(Y^n) − n·h(noise) ≤ ∑ h(Y_i) − n·h(noise)
= ∑ I(X_i;Y_i)`, combining `mutualInfo_encoder_le_fst`, `blockMI_decomp`,
`jointDifferentialEntropyPi_blockYLawInline_le_sum`, and `perLetterMI_decomp`.
Consumer-side `unfold jointMIXnYn perLetterMI awgnConverseJoint` gives defeq.

`[NeZero M]` (`M ≥ 1`, so the uniform message law is a probability measure) and `hN : N ≠ 0`
(full-support Gaussian fibres ⇒ blockYLaw absolutely continuous) are regularity
preconditions, both supplied by the converse consumer. They are not load-bearing: the MI
inequality is proved from the entropy chain, not encoded in the hypotheses (at the
degenerate boundary `N = 0` the Gaussian fibres collapse to Diracs, breaking only the
density route, while the MI inequality itself stays true since it is KL≥0-backed).
@audit:ok -/
@[entry_point]
theorem awgnContinuousMIChainRule_holds
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω ↦ c.encoder ω.1) Prod.snd).toReal
      ≤ ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω ↦ c.encoder ω.1 i) (fun ω ↦ ω.2 i)).toReal := by
  classical
  set h := InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) with hh
  -- LHS ≤ I(W;Y^n).toReal via deterministic DPI + finiteness.
  have h_dpi := mutualInfo_encoder_le_fst h_meas c
  have h_fin := mutualInfo_fst_snd_ne_top hN h_meas c
  have h_lhs_le :
      (mutualInfo (converseJointInline h_meas c) (fun ω ↦ c.encoder ω.1) Prod.snd).toReal
        ≤ (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal :=
    ENNReal.toReal_mono h_fin h_dpi
  -- I(W;Y^n).toReal = h(Y^n) − n·h(noise).
  have h_block := blockMI_decomp hN h_meas c
  -- h(Y^n) ≤ ∑ᵢ h(Y_i).
  have h_sub := jointDifferentialEntropyPi_blockYLawInline_le_sum hN h_meas c
  -- ∑ᵢ I(X_i;Y_i).toReal = (∑ᵢ h(Y_i)) − n·h(noise).
  have h_sum_perletter :
      ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω ↦ c.encoder ω.1 i) (fun ω ↦ ω.2 i)).toReal
        = (∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
              ((converseJointInline h_meas c).map (fun ω ↦ ω.2 i))) - (n : ℝ) * h := by
    rw [Finset.sum_congr rfl (fun i _ ↦ perLetterMI_decomp hN h_meas c i)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Combine.
  rw [h_sum_perletter]
  calc
    (mutualInfo (converseJointInline h_meas c) (fun ω ↦ c.encoder ω.1) Prod.snd).toReal
        ≤ (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal := h_lhs_le
    _ = InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
          - (n : ℝ) * h := h_block
    _ ≤ (∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
            ((converseJointInline h_meas c).map (fun ω ↦ ω.2 i))) - (n : ℝ) * h := by
        gcongr

end InformationTheory.Shannon.AWGN
