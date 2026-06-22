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

/-! # Memoryless MI chain rule: block MI decomposition -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ### Memoryless MI chain rule

The chain rule `I(X^n;Y^n) ≤ ∑ᵢ I(X_i;Y_i)` is the textbook argument
`I(W;Y^n) = h(Y^n) − n·h(noise) ≤ ∑ h(Y_i) − n·h(noise) = ∑ I(X_i;Y_i)`, combined with the
deterministic data-processing inequality `I(X^n;Y^n) ≤ I(W;Y^n)` (since `X^n = encoder ∘ W`
is a measurable post-processing of `W`, via `mutualInfo_le_of_postprocess` — no Markov-chain
machinery needed). The `I(W;Y^n)` decomposition uses the discrete-input block kernel
`blockKernelInline : Channel (Fin M) (Fin n → ℝ)` whose measurability is free
(`measurable_of_countable`, input `Fin M`), so the parallel-Gaussian kernel-measurability
gap (X-input route) is sidestepped. Pieces:

* the generic n-D continuous-channel MI decomposition
  `ChannelCoding.mutualInfoOfChannel_toReal_eq_log_density_sub` (the gateway atom, output
  type `β := Fin n → ℝ`, reference `volume`; genuine, no wall), giving
  `I(W;Y^n).toReal = h(Y^n) − n·h(noise)`;
* the n-D subadditivity `Shannon.jointDifferentialEntropyPi_le_sum` (genuine);
* the per-letter 1-D decomposition `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (genuine),
  giving `I(X_i;Y_i).toReal = h(Y_i) − h(noise)`.

The block regularity machinery mirrors the per-letter Wall-4 closure above and the
`ConverseMutualInfoFiniteness.lean` block infrastructure. -/

/-- Discrete-input block kernel `K m := pi (gaussianReal (encoder m i) N)` (`Fin M → Y^n`).
Measurability is free (`measurable_of_countable`, input `Fin M`). -/
private noncomputable def blockKernelInline
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    ChannelCoding.Channel (Fin M) (Fin n → ℝ) :=
  { toFun := fun m ↦ Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
    measurable' := measurable_of_countable _ }

instance blockKernelInline_isMarkov
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    ProbabilityTheory.IsMarkovKernel (blockKernelInline N c) :=
  ⟨fun m ↦ by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N))
    infer_instance⟩

/-- Uniform message law `msgLawInline := (M⁻¹ : ℝ≥0∞) • count` on `Fin M`. -/
private noncomputable def msgLawInline (M : ℕ) : Measure (Fin M) :=
  (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count

instance msgLawInline_isProb (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (msgLawInline M) := by
  refine ⟨?_⟩
  rw [msgLawInline, Measure.smul_apply, smul_eq_mul, Fintype.card_fin]
  have h_count : (Measure.count : Measure (Fin M)) Set.univ = (M : ℝ≥0∞) := by
    rw [Measure.count_apply_finite _ (Set.finite_univ)]
    simp [Fintype.card_fin]
  rw [h_count, ENNReal.inv_mul_cancel (by exact_mod_cast (NeZero.ne M))
    (ENNReal.natCast_ne_top M)]

/-- Block output law `Y^n` = `(converseJointInline).map snd` (= mixture of product
Gaussians). This is `outputDistribution msgLawInline blockKernelInline`. -/
noncomputable def blockYLawInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : Measure (Fin n → ℝ) :=
  (converseJointInline h_meas c).map Prod.snd

/-- Real-valued block mixture density `M⁻¹ ∑ₘ ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private noncomputable def blockRealDensityInline
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (y : Fin n → ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)

/-- `blockYLawInline = M⁻¹ • ∑ₘ pi (gaussianReal (encoder m i) N)` (closed mixture form). -/
lemma blockYLawInline_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) := by
  classical
  unfold blockYLawInline converseJointInline
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j))))
      h_meas_snd.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine congrArg (Measure.pi) ?_
  funext i
  rw [awgnChannel_apply]

private lemma blockRealDensityInline_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    0 < blockRealDensityInline N c y := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  unfold blockRealDensityInline
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos (fun m _ ↦ Finset.prod_pos (fun i _ ↦ gaussianPDFReal_pos _ _ _ hN)) ?_
  exact ⟨m₀, Finset.mem_univ m₀⟩

private lemma blockRealDensityInline_measurable
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockRealDensityInline N c) := by
  unfold blockRealDensityInline
  refine measurable_const.mul ?_
  refine Finset.measurable_sum _ (fun m _ ↦ ?_)
  exact Finset.measurable_prod _ (fun i _ ↦
    (measurable_gaussianPDFReal (c.encoder m i) N).comp (measurable_pi_apply i))

private lemma blockComponentInline_withDensity
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
  have h_each : ∀ i, gaussianReal (c.encoder m i) N
      = (MeasureTheory.volume : Measure ℝ).withDensity (gaussianPDF (c.encoder m i) N) :=
    fun i ↦ gaussianReal_of_var_ne_zero (c.encoder m i) hN
  haveI : ∀ i, SigmaFinite ((MeasureTheory.volume : Measure ℝ).withDensity
      (gaussianPDF (c.encoder m i) N)) := by
    intro i; rw [← h_each i]; infer_instance
  rw [show (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
        = (fun i ↦ (MeasureTheory.volume : Measure ℝ).withDensity
            (gaussianPDF (c.encoder m i) N)) from funext h_each,
    InformationTheory.Shannon.pi_withDensity_fin (fun _ ↦ (MeasureTheory.volume : Measure ℝ))
      (fun i ↦ measurable_gaussianPDF (c.encoder m i) N), ← volume_pi]

private lemma blockYLawInline_withDensity_real
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y ↦ ENNReal.ofReal (blockRealDensityInline N c y)) := by
  classical
  rw [blockYLawInline_eq_mixture h_meas c]
  have h_comp := fun m : Fin M ↦ blockComponentInline_withDensity hN c m
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N))
        = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
            (fun y ↦ ∑ m ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert m s hms ih =>
        have h_density_eq :
            (fun y : Fin n → ℝ ↦ ∑ m' ∈ insert m s,
              ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))
              = (fun y : Fin n → ℝ ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
                + (fun y : Fin n → ℝ ↦ ∑ m' ∈ s,
                  ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i)) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert hms]
        rw [Finset.sum_insert hms, ih, h_comp m, h_density_eq]
        rw [withDensity_add_left
            (μ := (MeasureTheory.volume : Measure (Fin n → ℝ)))
            (f := fun y : Fin n → ℝ ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
            (Finset.measurable_prod _ (fun i _ ↦
              (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i)))
            (fun y : Fin n → ℝ ↦ ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))]
  rw [h_sum Finset.univ]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  rw [← withDensity_smul' _ _ hM_inv_ne_top]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, blockRealDensityInline, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)),
      ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_sum_of_nonneg
          (fun m _ ↦ Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun m _ ↦ ?_)
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _)]
    refine Finset.prod_congr rfl (fun i _ ↦ ?_)
    rw [gaussianPDF]

lemma blockYLawInline_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
  rw [blockYLawInline_withDensity_real hN h_meas c]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

private lemma volume_ac_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (MeasureTheory.volume : Measure (Fin n → ℝ)) ≪ blockYLawInline h_meas c := by
  rw [blockYLawInline_withDensity_real hN h_meas c]
  refine withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp (blockRealDensityInline_measurable c)).aemeasurable ?_
  refine Filter.Eventually.of_forall (fun y ↦ ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact blockRealDensityInline_pos hN c y

instance blockYLawInline_isProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (blockYLawInline h_meas c) := by
  rw [blockYLawInline]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- The block component `pi (gaussianReal (encoder m i) N) ≪ blockYLawInline`
(`νₘ ≪ vol ≪ blockYLaw`). -/
private lemma blockComponentInline_ac_blockYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c := by
  have h1 : Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
      ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  exact h1.trans (volume_ac_blockYLawInline hN h_meas c)

/-- Per-component lower bound:
`blockRealDensityInline y ≥ M⁻¹ · ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private lemma blockRealDensityInline_ge_component
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) (y : Fin n → ℝ) :
    (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensityInline N c y := by
  unfold blockRealDensityInline
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.single_le_sum
    (f := fun m ↦ ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
    (fun m _ ↦ Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg _ _ _))
    (Finset.mem_univ m)

/-- Sup upper bound: `blockRealDensityInline y ≤ ∏ᵢ (√(2πN))⁻¹`. -/
private lemma blockRealDensityInline_le_sup
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    blockRealDensityInline N c y ≤ ∏ _i : Fin n, (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  classical
  unfold blockRealDensityInline
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_nonneg : (0 : ℝ) ≤ Bpeak := by rw [hBpeak]; positivity
  have h_comp_le : ∀ (a x : ℝ), gaussianPDFReal a N x ≤ Bpeak := by
    intro a x
    rw [gaussianPDFReal, hBpeak]
    have h_exp_le_one : Real.exp (-(x - a) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (x - a) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one (by positivity)
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  have h_prod_le : ∀ m : Fin M,
      (∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) ≤ ∏ _i : Fin n, Bpeak := by
    intro m
    refine Finset.prod_le_prod (fun i _ ↦ gaussianPDFReal_nonneg _ _ _) (fun i _ ↦ ?_)
    exact h_comp_le (c.encoder m i) (y i)
  calc (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ (1 / (M : ℝ)) * ∑ _m : Fin M, ∏ _i : Fin n, Bpeak := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun m _ ↦ h_prod_le m)
    _ = (1 / (M : ℝ)) * ((M : ℝ) * ∏ _i : Fin n, Bpeak) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∏ _i : Fin n, Bpeak := by
        have : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
        field_simp

/-- Per-component output log-density integrability (n-dim) against the m-th product-Gaussian
fibre `pi (gaussianReal (encoder m i) N)`. Mirror of
`ConverseMutualInfoFiniteness.integrable_log_blockYLaw_on_component`. -/
lemma integrable_log_blockYLawInline_on_component
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y ↦ Real.log ((blockYLawInline h_meas c).rnDeriv MeasureTheory.volume y).toReal)
      (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)) := by
  classical
  set q := blockYLawInline h_meas c with hq_def
  set νm := Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) with hνm_def
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i ↦ inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm_def]; infer_instance
  have hq_wd : q = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
      (fun y ↦ ENNReal.ofReal (blockRealDensityInline N c y)) := by
    rw [hq_def]; exact blockYLawInline_withDensity_real hN h_meas c
  have hDR_meas : Measurable (fun y ↦ ENNReal.ofReal (blockRealDensityInline N c y)) :=
    ENNReal.measurable_ofReal.comp (blockRealDensityInline_measurable c)
  have hνm_ac : νm ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hνm_def, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_vol : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y ↦ ENNReal.ofReal (blockRealDensityInline N c y)) := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity _ hDR_meas
  have h_rn_νm : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[νm] (fun y ↦ ENNReal.ofReal (blockRealDensityInline N c y)) :=
    hνm_ac.ae_le h_rn_vol
  have h_log_ae : (fun y ↦ Real.log (q.rnDeriv MeasureTheory.volume y).toReal)
      =ᵐ[νm] (fun y ↦ Real.log (blockRealDensityInline N c y)) := by
    filter_upwards [h_rn_νm] with y hy
    rw [hy, ENNReal.toReal_ofReal (blockRealDensityInline_pos hN c y).le]
  refine (Integrable.congr ?_ h_log_ae.symm)
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_pos : 0 < Bpeak := by rw [hBpeak]; positivity
  have hD_le : ∀ y, blockRealDensityInline N c y ≤ ∏ _i : Fin n, Bpeak :=
    blockRealDensityInline_le_sup c
  have hD_ge : ∀ y, (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensityInline N c y := fun y ↦ blockRealDensityInline_ge_component c m y
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  set Aconst : ℝ := |Real.log (∏ _i : Fin n, Bpeak)|
      + |Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀| with hAconst
  set Bcoef : ℝ := |c₁| with hBcoef
  have h_dom : Integrable
      (fun y : Fin n → ℝ ↦ Aconst + Bcoef * ∑ i : Fin n, (y i - c.encoder m i) ^ 2) νm := by
    refine (integrable_const Aconst).add (Integrable.const_mul ?_ Bcoef)
    rw [hνm_def]
    refine integrable_finsetSum _ (fun i _ ↦ ?_)
    have h_1d : Integrable (fun y : ℝ ↦ (y - c.encoder m i) ^ 2)
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ ↦ y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ ↦ (y - c.encoder m i) ^ 2)
          = fun y ↦ y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2 := by funext y; ring
      rw [hrw]
      exact ((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2)))
    exact integrable_comp_eval (μ := fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
      (i := i) h_1d
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp (blockRealDensityInline_measurable c)).aestronglyMeasurable
  · filter_upwards with y
    have hDy_pos : 0 < blockRealDensityInline N c y := blockRealDensityInline_pos hN c y
    set S : ℝ := ∑ i : Fin n, (y i - c.encoder m i) ^ 2 with hS
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
    have hc₁_nonpos : c₁ ≤ 0 := by rw [hc₁]; simp only [neg_nonpos]; positivity
    have h_upper : Real.log (blockRealDensityInline N c y) ≤ Real.log (∏ _i : Fin n, Bpeak) :=
      Real.log_le_log hDy_pos (hD_le y)
    have h_lower : Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
        ≤ Real.log (blockRealDensityInline N c y) := by
      have hMinv_pos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hprod_pos : (0 : ℝ) < ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i) :=
        Finset.prod_pos (fun i _ ↦ gaussianPDFReal_pos _ _ _ hN)
      have h_log_prod : Real.log ((1 / (M : ℝ)) *
            ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
          = Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [Real.log_mul hMinv_pos.ne' hprod_pos.ne', Real.log_prod (fun i _ ↦
          (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
        have h_each : ∀ i : Fin n, Real.log (gaussianPDFReal (c.encoder m i) N (y i))
            = c₀ + c₁ * (y i - c.encoder m i) ^ 2 := by
          intro i
          rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i), hc₀, hc₁]
          ring
        rw [Finset.sum_congr rfl (fun i _ ↦ h_each i), hS, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      calc Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
          = Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) :=
            h_log_prod.symm
        _ ≤ Real.log (blockRealDensityInline N c y) :=
            Real.log_le_log (mul_pos hMinv_pos hprod_pos) (hD_ge y)
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have hc₁S : c₁ * S = -(Bcoef * S) := by rw [hBcoef, abs_of_nonpos hc₁_nonpos]; ring
      have hlb : -(Aconst + Bcoef * S)
          ≤ Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [hAconst, hc₁S]
        have h1 := neg_abs_le (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h2 := abs_nonneg (Real.log (∏ _i : Fin n, Bpeak))
        linarith
      exact le_trans hlb h_lower
    · have hub : Real.log (∏ _i : Fin n, Bpeak) ≤ Aconst + Bcoef * S := by
        rw [hAconst]
        have h1 := le_abs_self (Real.log (∏ _i : Fin n, Bpeak))
        have h2 := abs_nonneg (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h3 : 0 ≤ Bcoef * S := mul_nonneg (abs_nonneg _) hS_nonneg
        linarith
      exact le_trans h_upper hub

/-- The proxy density `g z := ∏ᵢ gaussianPDF (encoder z.1 i) N (z.2 i)`, jointly measurable. -/
private noncomputable def blockProxy
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P)
    (z : (Fin M) × (Fin n → ℝ)) : ℝ≥0∞ :=
  ∏ i : Fin n, gaussianPDF (c.encoder z.1 i) N (z.2 i)

private lemma blockProxy_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockProxy N c) := by
  -- `Fin M` (input) is countable: measurability reduces to measurability in `y` for each `m`.
  refine measurable_from_prod_countable_right (fun m ↦ ?_)
  show Measurable (fun y : Fin n → ℝ ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
  exact Finset.measurable_prod _ (fun i _ ↦
    (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))

/-- Per-fibre a.e. agreement: `(blockKernelInline m).rnDeriv volume =ᵐ blockProxy (m, ·)`. -/
private lemma blockProxy_ae
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    (fun y ↦ ((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y)
      =ᵐ[(blockKernelInline N c) m] fun y ↦ blockProxy N c (m, y) := by
  -- `blockKernelInline m = vol.withDensity (∏ᵢ gaussianPDF (encoder m i)(·i))`, so its
  -- rnDeriv =ᵐ[vol] that density; transport to `=ᵐ[blockKernelInline m]` since fibre ≪ vol.
  have hfibre_eq : (blockKernelInline N c) m
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    show Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) = _
    exact blockComponentInline_withDensity hN c m
  have h_dens_meas : Measurable (fun y : Fin n → ℝ ↦
      ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) :=
    Finset.measurable_prod _ (fun i _ ↦
      (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))
  have h_fibre_ac : (blockKernelInline N c) m ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hfibre_eq]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_vol : ((blockKernelInline N c) m).rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y ↦ ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    conv_lhs => rw [hfibre_eq]
    exact Measure.rnDeriv_withDensity _ h_dens_meas
  filter_upwards [h_fibre_ac.ae_le h_rn_vol] with y hy
  simpa [blockProxy] using hy

/-- Fibre log-density integral identity: the proxy log-density integrates the same as the
rnDeriv log-density against the m-th fibre (used to feed `h_fibre_self`). -/
private lemma fibre_log_proxy_integral
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    ∫ y, Real.log (blockProxy N c (m, y)).toReal ∂((blockKernelInline N c) m)
      = ∫ y, Real.log
          (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal
          ∂((blockKernelInline N c) m) := by
  refine integral_congr_ae ?_
  filter_upwards [blockProxy_ae hN c m] with y hy
  rw [hy]

/-- Per-Gaussian log-density integrability (mirror of
`ParallelGaussian.gaussianReal_logRnDeriv_integrable`, inaccessible downstream). -/
lemma gaussianReal_logRnDeriv_integrable_inline (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y ↦ Real.log ((gaussianReal m v).rnDeriv volume y).toReal)
      (gaussianReal m v) := by
  have h_memLp : MemLp (fun y : ℝ ↦ y - m) 2 (gaussianReal m v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const m)
  have h_sq_int : Integrable (fun y ↦ (y - m) ^ 2) (gaussianReal m v) := h_memLp.integrable_sq
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

/-- Per-fibre log-density integrability: `log (rnDeriv (blockKernelInline m) vol)` is
integrable against the m-th product-Gaussian fibre `blockKernelInline m`. -/
private lemma integrable_log_fibre_rnDeriv
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y ↦ Real.log (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal)
      ((blockKernelInline N c) m) := by
  classical
  set νp := Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) with hνp
  have hfibre : (blockKernelInline N c) m = νp := rfl
  rw [hfibre]
  haveI : IsProbabilityMeasure νp := by rw [hνp]; infer_instance
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i ↦ inferInstance
  -- `log (rnDeriv νp vol) =ᵐ[νp] ∑ᵢ log gaussianPDFReal (encoder m i) (·i)`
  set a : Fin n → ℝ → ℝ≥0∞ := fun i ↦ (gaussianReal (c.encoder m i) N).rnDeriv volume with ha
  have ha_meas : ∀ i, Measurable (a i) := fun i ↦ Measure.measurable_rnDeriv _ _
  have hac : ∀ i, gaussianReal (c.encoder m i) N ≪ (volume : Measure ℝ) :=
    fun i ↦ gaussianReal_absolutelyContinuous (c.encoder m i) hN
  have hνp_ac : νp ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνp, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_pi : (νp.rnDeriv volume) =ᵐ[νp] fun z ↦ ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = gaussianReal (c.encoder m i) N :=
      fun i ↦ Measure.withDensity_rnDeriv_eq _ volume (hac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : νp = (volume : Measure (Fin n → ℝ)).withDensity (fun z ↦ ∏ i, a i (z i)) := by
      rw [hνp, ← (funext h_eq : (fun i ↦ (volume : Measure ℝ).withDensity (a i))
          = fun i ↦ gaussianReal (c.encoder m i) N)]
      rw [InformationTheory.Shannon.pi_withDensity_fin
          (fun _ : Fin n ↦ (volume : Measure ℝ)) ha_meas,
        volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ ↦ ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ ↦ (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (νp.rnDeriv volume) =ᵐ[volume] fun z ↦ ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hνp_ac.ae_le h_rn_vol
  have h_pos : ∀ i, ∀ᵐ z ∂νp, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(gaussianReal (c.encoder m i) N), 0 < a i y := Measure.rnDeriv_pos (hac i)
    exact (Measure.quasiMeasurePreserving_eval
      (μ := fun i ↦ gaussianReal (c.encoder m i) N) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂νp, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(gaussianReal (c.encoder m i) N), a i y < ∞ :=
      (hac i).ae_le (Measure.rnDeriv_lt_top _ volume)
    exact (Measure.quasiMeasurePreserving_eval
      (μ := fun i ↦ gaussianReal (c.encoder m i) N) i).ae h1d
  have h_log_split : (fun z ↦ Real.log ((νp.rnDeriv volume z).toReal))
      =ᵐ[νp] fun z ↦ ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    exact (ENNReal.toReal_pos (hpos i).ne' (hlt i).ne).ne'
  refine (Integrable.congr ?_ h_log_split.symm)
  refine integrable_finsetSum _ (fun i _ ↦ ?_)
  -- each `log (a i (z i))` integrable against νp = pi gaussian via `integrable_comp_eval`
  have h_1d : Integrable (fun y ↦ Real.log ((a i y).toReal)) (gaussianReal (c.encoder m i) N) :=
    gaussianReal_logRnDeriv_integrable_inline (c.encoder m i) hN
  rw [hνp]
  exact integrable_comp_eval (μ := fun i : Fin n ↦ gaussianReal (c.encoder m i) N) (i := i) h_1d

/-- Product entropy additivity (mirror of `ParallelGaussian.jointDifferentialEntropyPi_pi_eq_sum`,
inaccessible downstream): `h(∏ᵢ νᵢ) = ∑ᵢ h(νᵢ)` for component-`≪ volume`, log-density-integrable
factors. -/
private lemma jointDifferentialEntropyPi_pi_eq_sum_inline {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (h_ac : ∀ i, μ i ≪ (volume : Measure ℝ))
    (h_int : ∀ i, Integrable (fun y ↦ Real.log ((μ i).rnDeriv volume y).toReal) (μ i)) :
    InformationTheory.Shannon.jointDifferentialEntropyPi (Measure.pi μ)
      = ∑ i, InformationTheory.Shannon.differentialEntropy (μ i) := by
  classical
  set Pm := Measure.pi μ with hP
  set a : Fin n → ℝ → ℝ≥0∞ := fun i ↦ (μ i).rnDeriv volume with ha_def
  have ha_meas : ∀ i, Measurable (a i) := fun i ↦ Measure.measurable_rnDeriv (μ i) volume
  have hP_ac : Pm ≪ (volume : Measure (Fin n → ℝ)) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i ↦ Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_eq : Measure.pi μ
        = (Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ))).withDensity
            (fun z ↦ ∏ i, a i (z i)) := by
      rw [← (funext h_eq : (fun i ↦ (volume : Measure ℝ).withDensity (a i)) = μ)]
      exact InformationTheory.Shannon.pi_withDensity_fin
        (fun _ : Fin n ↦ (volume : Measure ℝ)) ha_meas
    rw [hP, h_pi_eq, volume_pi]
    exact withDensity_absolutelyContinuous _ _
  have h_step1 : InformationTheory.Shannon.jointDifferentialEntropyPi Pm
      = -∫ z, Real.log ((Pm.rnDeriv volume z).toReal) ∂Pm := by
    rw [InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg hP_ac, neg_neg]; rfl
  have h_rn_pi : (Pm.rnDeriv volume) =ᵐ[Pm] fun z ↦ ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i ↦ Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : Pm = (volume : Measure (Fin n → ℝ)).withDensity (fun z ↦ ∏ i, a i (z i)) := by
      rw [hP, ← (funext h_eq : (fun i ↦ (volume : Measure ℝ).withDensity (a i)) = μ)]
      rw [InformationTheory.Shannon.pi_withDensity_fin
          (fun _ : Fin n ↦ (volume : Measure ℝ)) ha_meas,
        volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ ↦ ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ ↦ (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (Pm.rnDeriv volume) =ᵐ[volume] fun z ↦ ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hP_ac.ae_le h_rn_vol
  have h_pos : ∀ i, ∀ᵐ z ∂Pm, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), 0 < a i y := Measure.rnDeriv_pos (h_ac i)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂Pm, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), a i y < ∞ := (h_ac i).ae_le (Measure.rnDeriv_lt_top (μ i) volume)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_log_split : (fun z ↦ Real.log ((Pm.rnDeriv volume z).toReal))
      =ᵐ[Pm] fun z ↦ ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    have : (0 : ℝ) < (a i (z i)).toReal := ENNReal.toReal_pos (hpos i).ne' (hlt i).ne
    exact this.ne'
  have h_int_P : ∀ i, Integrable (fun z ↦ Real.log ((a i (z i)).toReal)) Pm := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) Pm (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hcomp : (fun z : Fin n → ℝ ↦ Real.log ((a i (z i)).toReal))
        = (fun y ↦ Real.log ((a i y).toReal)) ∘ (Function.eval i) := rfl
    rw [hcomp]
    exact (hmp.integrable_comp
      ((((ha_meas i).ennreal_toReal.log).aestronglyMeasurable))).mpr (h_int i)
  have h_marg : ∀ i, (∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
      = -InformationTheory.Shannon.differentialEntropy (μ i) := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) Pm (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hGmeas : AEStronglyMeasurable (fun y ↦ Real.log ((a i y).toReal)) (μ i) :=
      ((ha_meas i).ennreal_toReal.log).aestronglyMeasurable
    have h_map : (∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
        = ∫ y, Real.log ((a i y).toReal) ∂(μ i) := by
      rw [← hmp.map_eq]
      exact (MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
        (by rw [hmp.map_eq]; exact hGmeas)).symm
    rw [h_map, ha_def, InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg (h_ac i)]
    rfl
  rw [h_step1, integral_congr_ae h_log_split, integral_finsetSum _ (fun i _ ↦ h_int_P i)]
  rw [show (∑ i, ∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
        = ∑ i, -InformationTheory.Shannon.differentialEntropy (μ i) from
    Finset.sum_congr rfl (fun i _ ↦ h_marg i)]
  rw [Finset.sum_neg_distrib, neg_neg]

/-- Fibre neg-entropy value: `∫ y, log (rnDeriv (blockKernelInline m) vol) ∂(blockKernelInline m)
= -n·h(gaussianReal 0 N)`. -/
private lemma fibre_neg_entropy
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    ∫ y, Real.log
        (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal
        ∂((blockKernelInline N c) m)
      = -((n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) := by
  -- the m-th fibre is the product Gaussian `pi (gaussianReal (encoder m i) N)`
  have hfibre : (blockKernelInline N c) m
      = Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) := rfl
  rw [hfibre]
  set νp := Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) with hνp
  haveI : IsProbabilityMeasure νp := by rw [hνp]; infer_instance
  have h_ac : νp ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνp, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `jointDifferentialEntropyPi νp = ∑ᵢ h(gaussian (encoder m i) N) = n·h(gaussian 0 N)`
  have h_sum : InformationTheory.Shannon.jointDifferentialEntropyPi νp
      = ∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
          (gaussianReal (c.encoder m i) N) := by
    rw [hνp]
    exact jointDifferentialEntropyPi_pi_eq_sum_inline
      (fun i ↦ gaussianReal (c.encoder m i) N)
      (fun i ↦ gaussianReal_absolutelyContinuous (c.encoder m i) hN)
      (fun i ↦ gaussianReal_logRnDeriv_integrable_inline (c.encoder m i) hN)
  have h_inv : ∀ i : Fin n,
      InformationTheory.Shannon.differentialEntropy (gaussianReal (c.encoder m i) N)
        = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro i
    rw [InformationTheory.Shannon.differentialEntropy_gaussianReal (c.encoder m i) hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [show (∫ y, Real.log (νp.rnDeriv volume y).toReal ∂νp)
        = -InformationTheory.Shannon.jointDifferentialEntropyPi νp from by
    rw [InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg h_ac]; rfl]
  rw [h_sum, Finset.sum_congr rfl (fun i _ ↦ h_inv i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- `count = ∑ₐ dirac a` on a `Fintype` (mirror of `count_eq_finset_sum_dirac`). -/
private lemma count_eq_finset_sum_dirac_inline (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.count : Measure α) = ∑ a : α, Measure.dirac a := by
  have h_one : ∀ a : α, (Measure.count : Measure α) {a} = 1 := fun a ↦
    Measure.count_singleton a
  have h_sum : Measure.sum (fun a : α ↦ Measure.dirac a)
      = (Measure.count : Measure α) := by
    have h := Measure.sum_smul_dirac (μ := (Measure.count : Measure α))
    simp_rw [h_one, one_smul] at h
    exact h
  rw [← h_sum, Measure.sum_fintype]

/-- Elementary discrete-input factorization (mixture-of-diracs):
`converseJointInline = msgLawInline ⊗ₘ blockKernelInline`. -/
private lemma converseJointInline_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    converseJointInline h_meas c = msgLawInline M ⊗ₘ blockKernelInline N c := by
  classical
  unfold converseJointInline msgLawInline
  rw [Measure.compProd_smul_left]
  congr 1
  rw [count_eq_finset_sum_dirac_inline (Fin M), ← Measure.sum_fintype
        (fun a : Fin M ↦ Measure.dirac a),
    Measure.compProd_sum_left, Measure.sum_fintype]
  symm
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  rw [show (Measure.dirac m) ⊗ₘ blockKernelInline N c
        = (Measure.dirac m).prod (blockKernelInline N c m) by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left hs]]
  refine congrArg ((Measure.dirac m).prod) ?_
  show Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))
      = Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)
  refine congrArg Measure.pi ?_
  funext i
  rw [awgnChannel_apply]

/-- Output law identification: `outputDistribution msgLawInline blockKernelInline
= blockYLawInline`. -/
private lemma outputDistribution_msgLawInline_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ChannelCoding.outputDistribution (msgLawInline M) (blockKernelInline N c)
      = blockYLawInline h_meas c := by
  -- `outputDistribution p W = (p ⊗ₘ W).snd = (p ⊗ₘ W).map snd`
  show (msgLawInline M ⊗ₘ blockKernelInline N c).map Prod.snd = blockYLawInline h_meas c
  rw [← converseJointInline_eq_compProd h_meas c]
  rfl

/-- `mutualInfo μ fst snd = mutualInfoOfChannel msgLawInline blockKernelInline`. -/
private lemma mutualInfo_fst_snd_eq_channel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd
      = ChannelCoding.mutualInfoOfChannel (msgLawInline M) (blockKernelInline N c) := by
  rw [ChannelCoding.mutualInfoOfChannel_eq_mutualInfo_prod]
  -- `jointDistribution msgLaw blockKernel = msgLaw ⊗ₘ blockKernel = converseJointInline`
  congr 1
  rw [ChannelCoding.jointDistribution_def, ← converseJointInline_eq_compProd h_meas c]

/-- Deterministic DPI: `I(X^n;Y^n) ≤ I(W;Y^n)` (`X^n = encoder ∘ fst` is a
post-processing of `W = fst`). -/
lemma mutualInfo_encoder_le_fst
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) (fun ω ↦ c.encoder ω.1) Prod.snd
      ≤ mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd := by
  set μ := converseJointInline h_meas c with hμ
  have hfst : Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := measurable_fst
  have hsnd : Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  have henc : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1) :=
    (measurable_of_countable c.encoder).comp measurable_fst
  -- `encoder ∘ fst = encoder ∘ (id) ∘ fst`; post-process the FIRST argument via comm + 2nd DPI.
  rw [mutualInfo_comm μ (fun ω ↦ c.encoder ω.1) Prod.snd henc hsnd,
    mutualInfo_comm μ Prod.fst Prod.snd hfst hsnd]
  -- now: `I(Y; encoder∘fst) ≤ I(Y; fst)`; `encoder∘fst = encoder ∘ fst`
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1)
      = c.encoder ∘ (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := rfl
  rw [h_comp]
  exact mutualInfo_le_of_postprocess μ Prod.snd Prod.fst hsnd hfst
    (measurable_of_countable c.encoder)

/-- `converseJointInline.map fst = msgLawInline` (uniform message marginal). -/
private lemma converseJointInline_map_fst_eq_msgLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (converseJointInline h_meas c).map (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      = msgLawInline M := by
  classical
  unfold converseJointInline msgLawInline
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j))))
      measurable_fst.aemeasurable]
  rw [count_eq_finset_sum_dirac_inline (Fin M)]
  congr 1
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Marginals product `(μ.map fst).prod (μ.map snd) = msgLaw ⊗ₘ const blockYLaw`. -/
private lemma converseJointInline_prod_marginals_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ((converseJointInline h_meas c).map Prod.fst).prod ((converseJointInline h_meas c).map Prod.snd)
      = msgLawInline M ⊗ₘ Kernel.const (Fin M) (blockYLawInline h_meas c) := by
  rw [converseJointInline_map_fst_eq_msgLaw h_meas c,
    show (converseJointInline h_meas c).map Prod.snd = blockYLawInline h_meas c from rfl,
    Measure.compProd_const]

/-- Per-fibre log-likelihood-ratio integrability:
`log (νₘ.rnDeriv blockYLaw)` integrable against the m-th block component `νₘ`. -/
private lemma integrable_log_component_rnDeriv_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y ↦ Real.log
        ((Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)).rnDeriv
          (blockYLawInline h_meas c) y).toReal)
      (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)) := by
  classical
  set νm := Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) with hνm
  set q := blockYLawInline h_meas c with hq
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i ↦ inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm]; infer_instance
  haveI hq_prob : IsProbabilityMeasure q := by rw [hq]; infer_instance
  have hνm_q : νm ≪ q := by rw [hνm, hq]; exact blockComponentInline_ac_blockYLaw hN h_meas c m
  have hq_vol : q ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hq]; exact blockYLawInline_ac_volume hN h_meas c
  have hνm_vol : νm ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνm, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `log(νₘ/q) =ᵐ[νₘ] log(νₘ/vol) − log(q/vol)`; both terms integrable.
  have h_split : (fun y ↦ Real.log ((νm.rnDeriv q y).toReal))
      =ᵐ[νm] (fun y ↦ Real.log ((νm.rnDeriv volume y).toReal)
                - Real.log ((q.rnDeriv volume y).toReal)) :=
    ChannelCoding.log_rnDeriv_split_gen hνm_q hq_vol
  refine Integrable.congr ?_ h_split.symm
  -- term A: `log(νₘ.rnDeriv vol)` integrable against νₘ (product-Gaussian log-density)
  have hA : Integrable (fun y ↦ Real.log ((νm.rnDeriv volume y).toReal)) νm := by
    rw [hνm]; exact integrable_log_fibre_rnDeriv hN c m
  -- term B: `log(q.rnDeriv vol)` integrable against νₘ (= component output log-density)
  have hB : Integrable (fun y ↦ Real.log ((q.rnDeriv volume y).toReal)) νm := by
    rw [hνm, hq]; exact integrable_log_blockYLawInline_on_component hN h_meas c m
  exact hA.sub hB

/-- `I(W;Y^n) ≠ ∞` (finiteness, so `.toReal` is monotone). -/
lemma mutualInfo_fst_snd_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd ≠ ∞ := by
  classical
  rw [mutualInfo]
  have h_joint : (converseJointInline h_meas c).map
      (fun ω : Fin M × (Fin n → ℝ) ↦ (ω.1, ω.2)) = msgLawInline M ⊗ₘ blockKernelInline N c := by
    rw [show (fun ω : Fin M × (Fin n → ℝ) ↦ (ω.1, ω.2)) = id from rfl, Measure.map_id]
    exact converseJointInline_eq_compProd h_meas c
  rw [h_joint, converseJointInline_prod_marginals_eq h_meas c]
  refine klDiv_ne_top ?_ ?_
  · -- AC: msgLaw ⊗ₘ K ≪ msgLaw ⊗ₘ const blockY
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards with m
    show blockKernelInline N c m ≪ (Kernel.const (Fin M) (blockYLawInline h_meas c)) m
    rw [Kernel.const_apply]
    show Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
    exact blockComponentInline_ac_blockYLaw hN h_meas c m
  · -- integrable llr
    set K := blockKernelInline N c with hK
    set ηc := Kernel.const (Fin M) (blockYLawInline h_meas c) with hηc
    have h_ac : msgLawInline M ⊗ₘ K ≪ msgLawInline M ⊗ₘ ηc := by
      refine Measure.AbsolutelyContinuous.compProd_right ?_
      filter_upwards with m
      rw [hηc, Kernel.const_apply]
      show Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
      exact blockComponentInline_ac_blockYLaw hN h_meas c m
    have h_llr_ae : (fun p ↦ llr (msgLawInline M ⊗ₘ K) (msgLawInline M ⊗ₘ ηc) p)
        =ᵐ[msgLawInline M ⊗ₘ K]
        (fun p : Fin M × (Fin n → ℝ) ↦ Real.log ((K.rnDeriv ηc p.1 p.2)).toReal) := by
      have h1 : (msgLawInline M ⊗ₘ K).rnDeriv (msgLawInline M ⊗ₘ ηc)
          =ᵐ[msgLawInline M ⊗ₘ K] fun p ↦ K.rnDeriv ηc p.1 p.2 :=
        h_ac.ae_le (ChannelCoding.rnDeriv_compProd_fibre h_ac)
      simp only [llr_def]
      filter_upwards [h1] with p hp1
      rw [hp1]
    refine Integrable.congr ?_ h_llr_ae.symm
    refine (Measure.integrable_compProd_iff ?_).mpr ⟨?_, ?_⟩
    · exact ((Kernel.measurable_rnDeriv K ηc).ennreal_toReal.log).aestronglyMeasurable
    · filter_upwards with m
      have h_fibre_ae : (fun y ↦ Real.log ((K.rnDeriv ηc m y)).toReal)
          =ᵐ[K m] (fun y ↦ Real.log (((K m).rnDeriv (blockYLawInline h_meas c) y)).toReal) := by
        have hKm_blockY : K m ≪ blockYLawInline h_meas c := by
          rw [hK]
          show Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) ≪
            blockYLawInline h_meas c
          exact blockComponentInline_ac_blockYLaw hN h_meas c m
        have h_meas_eq : K m ≪ ηc m := by rw [hηc, Kernel.const_apply]; exact hKm_blockY
        filter_upwards [h_meas_eq.ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := ηc) (a := m))] with y hy
        rw [hy]; simp only [hηc, Kernel.const_apply]
      refine Integrable.congr ?_ h_fibre_ae.symm
      show Integrable
        (fun y ↦ Real.log
          ((Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N)).rnDeriv
            (blockYLawInline h_meas c) y).toReal)
        (Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N))
      exact integrable_log_component_rnDeriv_blockYLawInline hN h_meas c m
    · exact Integrable.of_finite

/-- Block MI decomposition: `I(W;Y^n).toReal = h(Y^n) − n·h(noise)`. -/
lemma blockMI_decomp
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal
      = InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
        - (n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  classical
  set p := msgLawInline M with hp
  set W := blockKernelInline N c with hW
  -- output distribution identification
  have hq_eq : ChannelCoding.outputDistribution p W = blockYLawInline h_meas c :=
    outputDistribution_msgLawInline_eq h_meas c
  -- regularity (in the generic decomp's `outputDistribution` form)
  have hWx_q : ∀ m, W m ≪ ChannelCoding.outputDistribution p W := by
    intro m; rw [hq_eq]
    exact blockComponentInline_ac_blockYLaw hN h_meas c m
  have hq_ref : ChannelCoding.outputDistribution p W ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hq_eq]; exact blockYLawInline_ac_volume hN h_meas c
  haveI : (ChannelCoding.outputDistribution p W).HaveLebesgueDecomposition
      (volume : Measure (Fin n → ℝ)) := by infer_instance
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod (ChannelCoding.outputDistribution p W) := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    exact Filter.Eventually.of_forall (fun m ↦ by
      simpa only [Kernel.const_apply] using hWx_q m)
  -- proxy
  set g : (Fin M) × (Fin n → ℝ) → ℝ≥0∞ := blockProxy N c with hg
  have hg_meas : Measurable g := blockProxy_measurable N c
  have hg_ae : ∀ m, (fun y ↦ (W m).rnDeriv volume y) =ᵐ[W m] fun y ↦ g (m, y) :=
    fun m ↦ blockProxy_ae hN c m
  -- compProd-level integrabilities (msgLaw is finite-support → norm-integrability free)
  have h_int_fibre_self : ∀ m, Integrable (fun y ↦ Real.log (g (m, y)).toReal) (W m) := by
    intro m
    refine (integrable_log_fibre_rnDeriv hN c m).congr ?_
    filter_upwards [hg_ae m] with y hy
    rw [hy]
  have h_int_fibre :
      Integrable (fun z : (Fin M) × (Fin n → ℝ) ↦ Real.log (g z).toReal) (p ⊗ₘ W) := by
    rw [Measure.integrable_compProd_iff ((hg_meas.ennreal_toReal.log).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun m ↦ h_int_fibre_self m), ?_⟩
    -- `p = msgLaw` is a finite measure on the finite type `Fin M` → integrable for free
    exact Integrable.of_finite
  have h_out_self : Integrable
      (fun y ↦ Real.log ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p W) := by
    rw [hq_eq]
    -- integrate the fixed function against the mixture measure (rewrite only the measure)
    set F : (Fin n → ℝ) → ℝ :=
      fun y ↦ Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal with hF
    have h_mix : blockYLawInline h_meas c
        = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
            ∑ m : Fin M, Measure.pi (fun i : Fin n ↦ gaussianReal (c.encoder m i) N) :=
      blockYLawInline_eq_mixture h_meas c
    rw [h_mix]
    have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
      rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
    refine Integrable.smul_measure ?_ hM_inv_ne_top
    refine integrable_finsetSum_measure.mpr (fun m _ ↦ ?_)
    exact integrable_log_blockYLawInline_on_component hN h_meas c m
  have h_int_out : Integrable
      (fun z : (Fin M) × (Fin n → ℝ) ↦ Real.log
          ((ChannelCoding.outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    set ψ : (Fin n → ℝ) → ℝ := fun y ↦ Real.log
      ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal with hψ
    have hψ_meas : Measurable ψ :=
      (Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    show Integrable (fun z : (Fin M) × (Fin n → ℝ) ↦ ψ z.2) (p ⊗ₘ W)
    rw [Measure.integrable_compProd_iff
      (f := fun z : (Fin M) × (Fin n → ℝ) ↦ ψ z.2)
      ((hψ_meas.comp measurable_snd).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun m ↦ ?_), ?_⟩
    · -- per-fibre: `ψ` integrable against `W m = pi gaussian`; via output id + on-component
      have : Integrable
          (fun y ↦ Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal) (W m) :=
        integrable_log_blockYLawInline_on_component hN h_meas c m
      refine this.congr ?_
      filter_upwards with y; rw [hψ, hq_eq]
    · exact Integrable.of_finite
  have h_fibre_self : ∀ m, ∫ y, Real.log (g (m, y)).toReal ∂(W m)
      = ∫ y, Real.log ((W m).rnDeriv volume y).toReal ∂(W m) :=
        fun m ↦ fibre_log_proxy_integral hN c m
  -- apply the generic decomposition
  rw [mutualInfo_fst_snd_eq_channel h_meas c]
  rw [ChannelCoding.mutualInfoOfChannel_toReal_eq_log_density_sub
    (volume : Measure (Fin n → ℝ)) hWx_q hq_ref h_joint_ac g hg_meas hg_ae
    h_int_fibre h_int_out h_fibre_self h_out_self]
  -- fibre term: `∫ m, (∫ y, log(rnDeriv (W m) vol) ∂(W m)) ∂msgLaw = -n·h(noise)`
  have h_fibre_val : (∫ m, (∫ y, Real.log ((W m).rnDeriv volume y).toReal ∂(W m)) ∂p)
      = -((n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun m ↦ fibre_neg_entropy hN c m)),
      integral_const, probReal_univ, one_smul]
  -- output term: `∫ y, log(rnDeriv blockYLaw vol) ∂blockYLaw = -jointDiff`
  have h_out_val : (∫ y, Real.log
        ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal
        ∂(ChannelCoding.outputDistribution p W))
      = -InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c) := by
    rw [hq_eq, InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg
      (blockYLawInline_ac_volume hN h_meas c)]
    rfl
  rw [h_fibre_val, h_out_val]
  ring

end InformationTheory.Shannon.AWGN
