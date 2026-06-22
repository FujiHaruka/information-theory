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
import InformationTheory.Shannon.AWGN.ConverseMIChainRule.PerLetterMI

/-! # Deterministic-encoder Markov factorization -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ### Markov factorization -/

private theorem converseMarkov_marginalA
    {N : ℝ≥0} {h_meas : IsAwgnChannelMeasurable N} {M n : ℕ} [NeZero M] {P : ℝ}
    {c : AwgnCode M n P}
    (Wg : Kernel (Fin M) (Fin n → ℝ))
    (hWg_def : Wg = (ChannelCoding.Channel.toBlock (awgnChannel N h_meas) n).comap c.encoder
      (Measurable.of_discrete))
    (h_map_Xs : (converseJointInline h_meas c).map (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac m)) :
    converseJointInline h_meas c
      = ((converseJointInline h_meas c).map (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)) ⊗ₘ Wg := by
  haveI : IsMarkovKernel Wg := by rw [hWg_def]; infer_instance
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_compProd hf, h_map_Xs, lintegral_smul_measure,
    lintegral_finsetSum_measure]
  have hRHS_summand : ∀ m : Fin M,
      ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, f (a, y) ∂(Wg a) ∂(Measure.dirac m)
        = ∫⁻ y : Fin n → ℝ, f (m, y)
            ∂(Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))) := by
    intro m
    rw [lintegral_dirac, hWg_def]
    rfl
  simp_rw [hRHS_summand]
  rw [converseJointInline, lintegral_smul_measure, lintegral_finsetSum_measure]
  have hLHS_summand : ∀ m : Fin M,
      ∫⁻ ω : Fin M × (Fin n → ℝ), f ω
          ∂((Measure.dirac m).prod
            (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))))
        = ∫⁻ y : Fin n → ℝ, f (m, y)
            ∂(Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))) := by
    intro m
    rw [lintegral_prod _ hf.aemeasurable, lintegral_dirac]
  simp_rw [hLHS_summand]

private theorem converseMarkov_pairLaw
    {N : ℝ≥0} {h_meas : IsAwgnChannelMeasurable N} {M n : ℕ} [NeZero M] {P : ℝ}
    {c : AwgnCode M n P}
    (Zc : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) (hZc_def : Zc = fun ω ↦ c.encoder ω.1)
    (hZc_meas : Measurable Zc)
    (Yo : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) (hYo_def : Yo = Prod.snd)
    (hYo_meas : Measurable Yo)
    (W : Kernel (Fin n → ℝ) (Fin n → ℝ))
    (hW_def : W = ChannelCoding.Channel.toBlock (awgnChannel N h_meas) n)
    (h_map_Zc : (converseJointInline h_meas c).map Zc
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac (c.encoder m))) :
    (converseJointInline h_meas c).map (fun ω ↦ (Zc ω, Yo ω))
      = ((converseJointInline h_meas c).map Zc) ⊗ₘ W := by
  haveI : IsMarkovKernel W := by rw [hW_def]; infer_instance
  haveI : IsProbabilityMeasure ((converseJointInline h_meas c).map Zc) :=
    Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_compProd hf, h_map_Zc, lintegral_smul_measure,
    lintegral_finsetSum_measure]
  have hRHS_summand : ∀ m : Fin M,
      ∫⁻ z : Fin n → ℝ, ∫⁻ y : Fin n → ℝ, f (z, y) ∂(W z) ∂(Measure.dirac (c.encoder m))
        = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
            ∂(Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))) := by
    intro m
    rw [lintegral_dirac' _
      (Measurable.lintegral_kernel_prod_right' (κ := W) hf), hW_def]
    rfl
  simp_rw [hRHS_summand]
  rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), converseJointInline,
    lintegral_smul_measure, lintegral_finsetSum_measure]
  have hLHS_summand : ∀ m : Fin M,
      ∫⁻ ω : Fin M × (Fin n → ℝ), f (Zc ω, Yo ω)
          ∂((Measure.dirac m).prod
            (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))))
        = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
            ∂(Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))) := by
    intro m
    rw [lintegral_prod (fun ω : Fin M × (Fin n → ℝ) ↦ f (Zc ω, Yo ω))
      (hf.comp (hZc_meas.prodMk hYo_meas)).aemeasurable, hZc_def, hYo_def, lintegral_dirac]
  simp_rw [hLHS_summand]

/-- Markov chain `W → encoder ∘ W → Y^n` factorization.

`IsMarkovChain (converseJointInline h_meas c) Prod.fst (encoder ∘ fst) Prod.snd`, the
joint factorization.

The argument starts from the identity `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` (with `μ` the
message-space marginal and `W := Channel.toBlock (awgnChannel N) n` the noise block kernel),
established on the mixture-of-diracs via `ext_of_lintegral` (`h_marginalA`). From it,
`condDistrib Yo Zc μ =ᵐ W` (`condDistrib_ae_eq_of_measure_eq_compProd`); then `condDistrib Xs Zc μ`
is absorbed via `compProd_map_condDistrib`, and the triple-joint factorization is verified by
`ext_of_lintegral` + the `h_marginalA` reduction (precedent:
`BlockwiseChannel.isMarkovChain_per_letter_input`).
@audit:ok -/
@[entry_point]
theorem awgnConverseMarkov_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsMarkovChain (converseJointInline h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (fun ω : Fin M × (Fin n → ℝ) ↦ c.encoder ω.1)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := by
  set μ : Measure (Fin M × (Fin n → ℝ)) := converseJointInline h_meas c with hμ_def
  -- The three RVs.
  set Xs : Fin M × (Fin n → ℝ) → Fin M := Prod.fst with hXs_def
  set Zc : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := fun ω ↦ c.encoder ω.1 with hZc_def
  set Yo : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := Prod.snd with hYo_def
  -- The noise block kernel `W^{⊗n}` of the AWGN channel.
  set W : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
    ChannelCoding.Channel.toBlock (awgnChannel N h_meas) n with hW_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Measurability of the three RVs.
  have hXs_meas : Measurable Xs := measurable_fst
  have hZc_meas : Measurable Zc := by
    rw [hZc_def]; exact (Measurable.of_discrete).comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  have hg_meas : Measurable c.encoder := Measurable.of_discrete
  -- `W.comap encoder`: the channel kernel reindexed from message to codeword.
  set Wg : Kernel (Fin M) (Fin n → ℝ) := W.comap c.encoder hg_meas with hWg_def
  -- **Fundamental message-space marginal (A)**: `μ = (μ.map Xs) ⊗ₘ (W.comap encoder)`.
  -- Since `(Xs ω, Yo ω) = ω`, this says the converse joint factors as
  -- `uniform(W) ⊗ₘ (∏ᵢ awgnChannel (encoder · i))`. Proved by `ext_of_lintegral` on the
  -- mixture-of-diracs.
  -- `μ.map Xs = (1/M) • ∑ₘ δ_m` (uniform message law).
  have h_map_Xs : μ.map Xs
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac m) := by
    rw [hμ_def, hXs_def, converseJointInline]
    rw [Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum (measurable_fst.aemeasurable)]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Measure.map_fst_prod]
    simp
  have h_marginalA : μ = (μ.map Xs) ⊗ₘ Wg := by
    rw [hμ_def, hXs_def]
    exact converseMarkov_marginalA Wg hWg_def (by rw [← hμ_def, ← hXs_def]; exact h_map_Xs)
  -- `μ.map Zc = (1/M) • ∑ₘ δ_(encoder m)` (codeword law).
  have h_map_Zc : μ.map Zc
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac (c.encoder m)) := by
    have hZc_comp : Zc = c.encoder ∘ Xs := rfl
    rw [hZc_comp, ← Measure.map_map Measurable.of_discrete hXs_meas, h_map_Xs,
      Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum' Measurable.of_discrete.aemeasurable]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [Measure.map_dirac' Measurable.of_discrete]
  -- Linchpin marginal: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ W`.
  have h_pair_eq : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ W := by
    rw [hμ_def]
    exact converseMarkov_pairLaw Zc hZc_def hZc_meas Yo hYo_def hYo_meas W hW_def
      (by rw [← hμ_def]; exact h_map_Zc)
  -- Identify `condDistrib Yo Zc μ =ᵐ[μ.map Zc] W`.
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] W :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  -- Unfold IsMarkovChain and substitute condDistrib Yo Zc → W on the RHS.
  unfold IsMarkovChain
  set K_X : Kernel (Fin n → ℝ) (Fin M) := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Triple-joint factorization via ext_of_lintegral.
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  -- `compProd_map_condDistrib`: fold K_X back into `μ.map (Zc, Xs)`.
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω ↦ (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  -- LHS: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ.
  rw [lintegral_map hf h_LHS_meas]
  -- RHS: unfold the outer compProd over (μ.map Zc), then the inner product kernel.
  rw [Measure.lintegral_compProd hf]
  -- RHS inner: ∫⁻ p ∂((K_X ×ₖ W) z), f (z, p.1, p.2)
  --          = ∫⁻ x ∂(K_X z), ∫⁻ y ∂(W z), f (z, x, y).
  have h_inner_split : ∀ z : Fin n → ℝ,
      ∫⁻ p : Fin M × (Fin n → ℝ), f (z, p.1, p.2) ∂((K_X ×ₖ W) z)
        = ∫⁻ x : Fin M, ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply]
    rw [lintegral_prod (fun p : Fin M × (Fin n → ℝ) ↦ f (z, p.1, p.2))
      (hf.comp (measurable_const.prodMk
        (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  -- Define G (z, x) := ∫⁻ y ∂(W z), f (z, x, y),
  -- so RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x).
  set G : (Fin n → ℝ) × Fin M → ℝ≥0∞ :=
    fun p ↦ ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel ((Fin n → ℝ) × Fin M) (Fin n → ℝ) :=
      W.comap (Prod.fst : (Fin n → ℝ) × Fin M → (Fin n → ℝ)) measurable_fst
    have h_eq_K' : G = fun p : (Fin n → ℝ) × Fin M ↦
        ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : ((Fin n → ℝ) × Fin M) × (Fin n → ℝ) ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Fin n → ℝ, ∀ x : Fin M,
      ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) = G (z, x) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  -- RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x) = ∫⁻ p ∂((μ.map Zc) ⊗ₘ K_X), G p.
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold]
  -- RHS = ∫⁻ p ∂(μ.map (Zc, Xs)), G p = ∫⁻ ω ∂μ, G (Zc ω, Xs ω).
  rw [lintegral_map hG_meas (hZc_meas.prodMk hXs_meas)]
  -- Now goal: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ = ∫⁻ ω, G (Zc ω, Xs ω) ∂μ.
  rw [← hμ_def]
  -- Reduce any `∫⁻ ω, H ω ∂μ` through message-space marginal (A).
  have h_reduce : ∀ H : Fin M × (Fin n → ℝ) → ℝ≥0∞, Measurable H →
      ∫⁻ ω, H ω ∂μ
        = ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, H (a, y) ∂(Wg a) ∂(μ.map Xs) := by
    intro H hH
    conv_lhs => rw [h_marginalA]
    rw [Measure.lintegral_compProd hH]
  rw [h_reduce (fun ω ↦ f (Zc ω, Xs ω, Yo ω)) (hf.comp h_LHS_meas),
    h_reduce (fun ω ↦ G (Zc ω, Xs ω)) (hG_meas.comp (hZc_meas.prodMk hXs_meas))]
  -- Both inner integrals over `Wg a`. For each message `a`:
  refine lintegral_congr fun a ↦ ?_
  have hWg_eq : Wg a = W (c.encoder a) := by rw [hWg_def, Kernel.comap_apply]
  haveI : IsProbabilityMeasure (Wg a) := by rw [hWg_eq]; infer_instance
  -- LHS inner: ∫⁻ y ∂(Wg a), f (encoder a, a, y).
  --   `(Zc (a,y), Xs (a,y), Yo (a,y)) = (encoder a, a, y)`.
  -- RHS inner: ∫⁻ y ∂(Wg a), G (encoder a, a), constant in y,
  --   value `∫⁻ y' ∂(W (encoder a)), f (encoder a, a, y')`.
  have hRHS_eval : (fun y : Fin n → ℝ ↦ G (Zc (a, y), Xs (a, y)))
      = (fun _ : Fin n → ℝ ↦ ∫⁻ y' : Fin n → ℝ, f (c.encoder a, a, y') ∂(Wg a)) := by
    funext y
    show G (c.encoder a, a) = _
    rw [hG_def, hWg_eq]
  rw [hRHS_eval, lintegral_const, measure_univ, mul_one]

end InformationTheory.Shannon.AWGN
