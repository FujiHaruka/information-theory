import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.ConverseMutualInfoFiniteness
import InformationTheory.Shannon.AWGN.ConverseCapacityBound
import InformationTheory.Shannon.ChannelCoding.MIDecomp

/-!
# AWGN channel coding theorem: the converse

The converse half of the AWGN channel coding theorem (Cover–Thomas, Chapter 9.1.2):
for every power-constrained block code, the rate is bounded by the channel capacity
plus the Fano error terms.

The proof follows the standard route:
1. Fano: `log M ≤ I(W; Ŵ) + binEntropy(Pe) + Pe·log(M-1)`.
2. Data processing: `I(W; Ŵ) ≤ I(Xⁿ; Yⁿ)` from the functionality of encoder/decoder.
3. Chain rule and memorylessness: `I(Xⁿ; Yⁿ) ≤ ∑ I(Xᵢ; Yᵢ)`.
4. Per-letter max-entropy: `I(Xᵢ; Yᵢ) ≤ (1/2) log(1 + P/N)`.
5. Summation: `log M ≤ n·(1/2) log(1 + P/N) + binEntropy(Pe) + Pe·log(M-1)`.

## Main statements

* `awgn_per_letter_mi_bridge_genuine` — the per-letter mutual information equals the
  output differential entropy minus the input-independent noise entropy.
* `awgn_converse` — the converse rate bound for any code with `M ≥ 2` messages.

## Implementation notes

* The per-letter input marginal `perLetterXLaw` is a mixture of Diracs over the
  encoder coordinates, and the per-letter joint `(Xᵢ, Yᵢ)` law factors as
  `perLetterXLaw ⊗ₘ awgnChannel`. The bridge is then obtained from the generic
  continuous-channel mutual-information chain rule
  (`ChannelCoding.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`) together with the
  translation invariance of the AWGN fibre entropy.
* The mixture output law `perLetterYLaw` has a real density bounded above by the
  Gaussian peak and below by a single component, which gives the quadratic envelope
  used to prove integrability of its log-density.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
  InformationTheory.Shannon InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

/-! ## The per-letter mutual-information bridge -/

/-- The per-letter input marginal of `Xᵢ = c.encoder ω.1 i`: the mixture of Diracs
`(1/M) ∑ₘ δ(c.encoder m i)`, i.e. the law of the `i`-th encoder coordinate under a
uniform message. -/
noncomputable def perLetterXLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (awgnConverseJoint h_meas c).map (fun ω => c.encoder ω.1 i)

private lemma perLetterXLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterXLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
  classical
  unfold perLetterXLaw awgnConverseJoint
  have h_meas_eval :
      Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i) :=
    (measurable_of_countable (fun a : Fin M => c.encoder a i)).comp measurable_fst
  rw [Measure.map_smul]
  rw [Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      h_meas_eval.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  -- `((dirac m).prod ν).map (fun ω => c.encoder ω.1 i) = dirac (c.encoder m i)`
  -- via `(fun ω => c.encoder ω.1 i) = (fun a => c.encoder a i) ∘ Prod.fst`.
  have h_decomp : (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i)
      = (fun a : Fin M => c.encoder a i) ∘ Prod.fst := rfl
  rw [h_decomp,
    ← Measure.map_map (measurable_of_countable (fun a : Fin M => c.encoder a i)) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul,
    Measure.map_dirac' (measurable_of_countable (fun a : Fin M => c.encoder a i)) m]

private instance perLetterXLaw_isProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    IsProbabilityMeasure (perLetterXLaw h_meas c i) := by
  unfold perLetterXLaw
  exact Measure.isProbabilityMeasure_map
    ((measurable_of_countable (fun a : Fin M => c.encoder a i)).comp measurable_fst).aemeasurable

/-- The per-letter pair law factors as `perLetterXLaw ⊗ₘ awgnChannel`. -/
private lemma awgnConverseJoint_map_pair_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (awgnConverseJoint h_meas c).map (fun ω => (c.encoder ω.1 i, ω.2 i))
      = perLetterXLaw h_meas c i ⊗ₘ (awgnChannel N h_meas) := by
  classical
  -- Common target form: `M⁻¹ • ∑ₘ (δ(encoder m i)).prod (gaussianReal (encoder m i) N)`.
  -- Per-summand `δ_a ⊗ₘ awgnChannel = (δ_a).prod (awgnChannel a)`.
  have h_dirac_compProd : ∀ a : ℝ,
      (Measure.dirac a) ⊗ₘ (awgnChannel N h_meas)
        = (Measure.dirac a).prod (awgnChannel N h_meas a) := by
    intro a
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left hs]
  -- ===== RHS: perLetterXLaw ⊗ₘ awgnChannel =====
  have h_rhs : perLetterXLaw h_meas c i ⊗ₘ (awgnChannel N h_meas)
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M,
            (Measure.dirac (c.encoder m i)).prod (awgnChannel N h_meas (c.encoder m i)) := by
    rw [perLetterXLaw_eq_mixture h_meas c i]
    -- distribute compProd over `smul` and the finset sum
    rw [← Measure.sum_fintype (fun m : Fin M => Measure.dirac (c.encoder m i)),
      Measure.compProd_smul_left, Measure.compProd_sum_left, Measure.sum_fintype]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    exact h_dirac_compProd (c.encoder m i)
  -- ===== LHS: (awgnConverseJoint).map (X_i, Y_i) =====
  have h_lhs : (awgnConverseJoint h_meas c).map (fun ω => (c.encoder ω.1 i, ω.2 i))
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M,
            (Measure.dirac (c.encoder m i)).prod (awgnChannel N h_meas (c.encoder m i)) := by
    unfold awgnConverseJoint
    have hf_meas :
        Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
      ((measurable_of_countable (fun a : Fin M => c.encoder a i)).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    rw [Measure.map_smul,
      Measure.map_finset_sum (s := Finset.univ)
        (m := fun m => (Measure.dirac m).prod
          (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
        hf_meas.aemeasurable]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    -- map of `(δ_m).prod (pi μ_m)` under `ω ↦ (encoder m i, ω.2 i)`
    -- equals `(δ(encoder m i)).prod (gaussianReal (encoder m i) N)`.
    rw [Measure.dirac_prod, Measure.map_map hf_meas measurable_prodMk_left]
    -- `(fun ω => (encoder ω.1 i, ω.2 i)) ∘ (Prod.mk m)` on `pi μ_m`
    have h_comp : (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
          ∘ (Prod.mk m : (Fin n → ℝ) → Fin M × (Fin n → ℝ))
        = fun y : Fin n → ℝ => (c.encoder m i, y i) := rfl
    rw [h_comp]
    -- `(pi μ_m).map (fun y => (encoder m i, y i))`
    -- `= ((pi μ_m).map (Function.eval i)).map (fun z => (encoder m i, z))`.
    have h_pair : (fun y : Fin n → ℝ => (c.encoder m i, y i))
        = (fun z : ℝ => (c.encoder m i, z)) ∘ (Function.eval i : (Fin n → ℝ) → ℝ) := rfl
    have h_eval_meas : Measurable (Function.eval i : (Fin n → ℝ) → ℝ) :=
      measurable_pi_apply i
    have h_outer_meas : Measurable (fun z : ℝ => (c.encoder m i, z)) := by fun_prop
    rw [h_pair, ← Measure.map_map h_outer_meas h_eval_meas, Measure.pi_map_eval]
    -- `∏ j ∈ erase i, (awgnChannel ...) univ = 1`
    have h_prod_one : (∏ j ∈ Finset.univ.erase i,
        (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      rw [awgnChannel_apply]; exact measure_univ
    rw [h_prod_one, one_smul]
    -- `(awgnChannel (encoder m i)).map (fun z => (encoder m i, z)) = (δ).prod (awgnChannel ...)`
    rw [Measure.dirac_prod]
  rw [h_lhs, h_rhs]

private lemma outputDistribution_eq_perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    outputDistribution (perLetterXLaw h_meas c i) (awgnChannel N h_meas)
      = perLetterYLaw h_meas c i := by
  -- `outputDistribution p W = (p ⊗ₘ W).snd = (p ⊗ₘ W).map Prod.snd`.
  rw [show outputDistribution (perLetterXLaw h_meas c i) (awgnChannel N h_meas)
        = (perLetterXLaw h_meas c i ⊗ₘ (awgnChannel N h_meas)).map Prod.snd from rfl]
  rw [← awgnConverseJoint_map_pair_eq_compProd h_meas c i]
  have hf_meas :
      Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun a : Fin M => c.encoder a i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  rw [Measure.map_map measurable_snd hf_meas]
  rfl

private lemma perLetterMI_eq_mutualInfoOfChannel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterMI h_meas c i
      = mutualInfoOfChannel (perLetterXLaw h_meas c i) (awgnChannel N h_meas) := by
  -- Both are `klDiv joint product`. Match joint via the factorization, and the two
  -- product factors via the marginal identities.
  unfold perLetterMI mutualInfo
  rw [mutualInfoOfChannel_def, jointDistribution_def]
  -- joint: `μ.map (X_i, Y_i) = perLetterXLaw ⊗ₘ awgnChannel`.
  rw [awgnConverseJoint_map_pair_eq_compProd h_meas c i]
  congr 1
  -- product: `(μ.map X_i).prod (μ.map Y_i) = perLetterXLaw.prod (outputDistribution ...)`.
  -- `μ.map X_i = perLetterXLaw` (def), `μ.map Y_i = perLetterYLaw = outputDistribution`.
  rw [show (awgnConverseJoint h_meas c).map (fun ω => c.encoder ω.1 i)
        = perLetterXLaw h_meas c i from rfl,
    show (awgnConverseJoint h_meas c).map (fun ω => ω.2 i)
        = perLetterYLaw h_meas c i from rfl,
    outputDistribution_eq_perLetterYLaw h_meas c i]

private lemma integral_diffEntropy_awgnChannel_eq_noise
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (∫ x, InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
        ∂(perLetterXLaw h_meas c i))
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  -- integrand is the constant `h(𝒩(0,N))` (mean translation invariance of fibre entropy)
  have h_const : ∀ x,
      InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
        = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro x
    rw [awgnChannel_apply,
      InformationTheory.Shannon.differentialEntropy_gaussianReal x hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => h_const x))]
  simp

private lemma perLetterYLaw_eq_mixture_local
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  unfold perLetterYLaw awgnConverseJoint
  have h_meas_eval : Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      h_meas_eval.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) => ω.2 i)
      = (Function.eval i : (Fin n → ℝ) → ℝ) ∘ (Prod.snd : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) := rfl
  rw [h_comp, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul, Measure.pi_map_eval]
  have h_prod_one : (∏ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
    refine Finset.prod_eq_one (fun j _ => ?_)
    rw [awgnChannel_apply]; exact measure_univ
  rw [h_prod_one, one_smul, awgnChannel_apply]

private lemma perLetterYLaw_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i ≪ MeasureTheory.volume := by
  classical
  rw [perLetterYLaw_eq_mixture_local h_meas c i]
  refine Measure.AbsolutelyContinuous.smul_left ?_ _
  rw [← Measure.sum_fintype]
  exact Measure.absolutelyContinuous_sum_left fun m =>
    gaussianReal_absolutelyContinuous _ hN

private lemma volume_ac_perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (MeasureTheory.volume : Measure ℝ) ≪ perLetterYLaw h_meas c i := by
  classical
  -- pick the component `m₀` (NeZero M ⇒ Fin M nonempty): volume ≪ 𝒩(encoder m₀ i, N)
  -- ≪ M⁻¹ • ∑ₘ 𝒩(...) = perLetterYLaw.
  rw [perLetterYLaw_eq_mixture_local h_meas c i]
  obtain ⟨m₀⟩ : Nonempty (Fin M) := by
    have : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M); exact ⟨⟨0, this⟩⟩
  have hM_inv_ne_zero : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ 0 := by
    rw [Fintype.card_fin]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
  -- volume ≪ 𝒩(encoder m₀ i, N)
  have h1 : (MeasureTheory.volume : Measure ℝ) ≪ gaussianReal (c.encoder m₀ i) N :=
    gaussianReal_absolutelyContinuous' _ hN
  -- 𝒩(encoder m₀ i, N) ≪ ∑ₘ 𝒩(encoder m i, N)
  have h2 : gaussianReal (c.encoder m₀ i) N
      ≪ ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
    rw [← Measure.sum_fintype]
    exact Measure.absolutelyContinuous_sum_right m₀ (Measure.AbsolutelyContinuous.refl _)
  -- ∑ₘ ≪ M⁻¹ • ∑ₘ
  have h3 : (∑ m : Fin M, gaussianReal (c.encoder m i) N)
      ≪ (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • ∑ m : Fin M, gaussianReal (c.encoder m i) N :=
    (Measure.absolutelyContinuous_smul hM_inv_ne_zero)
  exact (h1.trans h2).trans h3

private lemma awgnChannel_ac_perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (x : ℝ) :
    (awgnChannel N h_meas) x ≪ perLetterYLaw h_meas c i := by
  rw [awgnChannel_apply]
  exact (gaussianReal_absolutelyContinuous x hN).trans (volume_ac_perLetterYLaw hN h_meas c i)

/-- The real-valued per-letter mixture density `M⁻¹ · ∑ₘ gaussianPDFReal (encoder m i) N y`. -/
private noncomputable def perLetterRealDensity
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (y : ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, gaussianPDFReal (c.encoder m i) N y

private lemma perLetterYLaw_withDensity_real
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i
      = MeasureTheory.volume.withDensity
          (fun y => ENNReal.ofReal (perLetterRealDensity N c i y)) := by
  classical
  rw [perLetterYLaw_eq_mixture_local h_meas c i]
  -- each component `gaussianReal a N = volume.withDensity (gaussianPDF a N)`
  have h_comp : ∀ m : Fin M,
      gaussianReal (c.encoder m i) N
        = MeasureTheory.volume.withDensity (gaussianPDF (c.encoder m i) N) :=
    fun m => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, gaussianReal (c.encoder m i) N)
        = MeasureTheory.volume.withDensity (∑ m ∈ s, gaussianPDF (c.encoder m i) N) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [withDensity_zero]
    | insert m s hms ih =>
        rw [Finset.sum_insert hms, Finset.sum_insert hms, ih, h_comp m,
          withDensity_add_left (measurable_gaussianPDF _ _)]
  rw [h_sum Finset.univ]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  rw [← withDensity_smul' _ _ hM_inv_ne_top]
  congr 1
  funext y
  -- `M⁻¹ • (∑ₘ gaussianPDF) y = ofReal (M⁻¹ · ∑ₘ gaussianPDFReal)`
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, perLetterRealDensity,
    Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)),
      ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => (gaussianPDFReal_nonneg _ _ y))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [gaussianPDF]

private lemma perLetterYLaw_sq_sub_integrable
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (a₀ : ℝ) :
    Integrable (fun y : ℝ => (y - a₀) ^ 2) (perLetterYLaw h_meas c i) := by
  classical
  rw [perLetterYLaw_eq_mixture_local h_meas c i]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  rw [integrable_finsetSum_measure]
  intro m _
  -- `(y − a₀)²` integrable against each `gaussianReal (encoder m i) N`
  have h_id : Integrable (fun y : ℝ => y) (gaussianReal (c.encoder m i) N) := by
    simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
  have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) :=
    (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
  have hrw : (fun y : ℝ => (y - a₀) ^ 2) = fun y => y ^ 2 - 2 * a₀ * y + a₀ ^ 2 := by
    funext y; ring
  rw [hrw]
  exact ((h_sq.sub (h_id.const_mul (2 * a₀))).add (integrable_const (a₀ ^ 2)))

private lemma integrable_log_rnDeriv_perLetterYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    Integrable
      (fun y => Real.log ((perLetterYLaw h_meas c i).rnDeriv MeasureTheory.volume y).toReal)
      (perLetterYLaw h_meas c i) := by
  classical
  set q := perLetterYLaw h_meas c i with hq_def
  haveI hq_prob : IsProbabilityMeasure q := by
    rw [hq_def]; unfold perLetterYLaw
    exact Measure.isProbabilityMeasure_map
      ((measurable_pi_apply i).comp measurable_snd).aemeasurable
  set D : ℝ → ℝ := perLetterRealDensity N c i with hD_def
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  -- density form
  have hq_wd : q = MeasureTheory.volume.withDensity (fun y => ENNReal.ofReal (D y)) := by
    rw [hq_def, hD_def]; exact perLetterYLaw_withDensity_real hN h_meas c i
  have hD_meas : Measurable (fun y => ENNReal.ofReal (D y)) := by
    rw [hD_def]; unfold perLetterRealDensity
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul (Finset.measurable_sum _
      (fun m _ => (measurable_gaussianPDFReal (c.encoder m i) N))))
  -- `q.rnDeriv vol =ᵐ[vol] ofReal ∘ D`, transport to `=ᵐ[q]` (q ≪ vol)
  have hq_ac : q ≪ MeasureTheory.volume := by rw [hq_def]; exact perLetterYLaw_ac_volume hN h_meas c i
  have h_rn_vol : q.rnDeriv MeasureTheory.volume =ᵐ[MeasureTheory.volume]
      (fun y => ENNReal.ofReal (D y)) := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity MeasureTheory.volume hD_meas
  have h_rn_q : q.rnDeriv MeasureTheory.volume =ᵐ[q] (fun y => ENNReal.ofReal (D y)) :=
    hq_ac.ae_le h_rn_vol
  -- positivity of D: bounded below by a single component (m₀)
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
  have hD_pos : ∀ y, 0 < D y := by
    intro y
    rw [hD_def]; unfold perLetterRealDensity
    refine mul_pos (by positivity) ?_
    refine Finset.sum_pos (fun m _ => gaussianPDFReal_pos _ _ y hN) ?_
    exact ⟨m₀, Finset.mem_univ m₀⟩
  -- the target integrand agrees a.e. with `log (D y)`
  have h_log_ae : (fun y => Real.log (q.rnDeriv MeasureTheory.volume y).toReal)
      =ᵐ[q] (fun y => Real.log (D y)) := by
    filter_upwards [h_rn_q] with y hy
    rw [hy, ENNReal.toReal_ofReal (hD_pos y).le]
  refine (Integrable.congr ?_ h_log_ae.symm)
  -- dominate `|log (D y)|` by `A + B·(y - a₀)²`
  -- upper bound: `D y ≤ (√(2πN))⁻¹` ⇒ `log (D y) ≤ log ((√(2πN))⁻¹)`
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_pos : 0 < Bpeak := by
    rw [hBpeak]; positivity
  have hD_le : ∀ y, D y ≤ Bpeak := by
    intro y
    rw [hD_def]; unfold perLetterRealDensity
    have h_comp_le : ∀ m : Fin M, gaussianPDFReal (c.encoder m i) N y ≤ Bpeak := by
      intro m
      rw [gaussianPDFReal, hBpeak]
      have h_const_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ := by positivity
      have h_exp_le_one : Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_div]
        have : 0 ≤ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)) := by positivity
        linarith
      calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N))
          ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left h_exp_le_one h_const_nonneg
        _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
    calc (1 / (M : ℝ)) * ∑ m : Fin M, gaussianPDFReal (c.encoder m i) N y
        ≤ (1 / (M : ℝ)) * ∑ _m : Fin M, Bpeak := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun m _ => h_comp_le m)
      _ = (1 / (M : ℝ)) * ((M : ℝ) * Bpeak) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = Bpeak := by field_simp
  -- lower bound: `D y ≥ M⁻¹ · gaussianPDFReal(a₀) y`
  set a₀ : ℝ := c.encoder m₀ i with ha₀
  have hD_ge : ∀ y, (1 / (M : ℝ)) * gaussianPDFReal a₀ N y ≤ D y := by
    intro y
    rw [hD_def]; unfold perLetterRealDensity
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.single_le_sum (f := fun m => gaussianPDFReal (c.encoder m i) N y)
      (fun m _ => gaussianPDFReal_nonneg _ _ y) (Finset.mem_univ m₀)
  -- assemble the quadratic envelope on `|log (D y)|`
  -- upper: log D ≤ log Bpeak; lower: log D ≥ log(M⁻¹) + c₀ + c₁(y-a₀)²
  set c₀ : ℝ := -(1/2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  -- dominating function `g y := |log Bpeak| + |log (M⁻¹) + c₀| + |c₁|·(y-a₀)²`
  set A : ℝ := |Real.log Bpeak| + |Real.log (1 / (M : ℝ)) + c₀| with hA
  set Bcoef : ℝ := |c₁| with hBcoef
  have h_dom : Integrable (fun y : ℝ => A + Bcoef * (y - a₀) ^ 2) q := by
    refine (integrable_const A).add ?_
    rw [hq_def]
    exact (perLetterYLaw_sq_sub_integrable hN h_meas c i a₀).const_mul Bcoef
  refine Integrable.mono' h_dom ?_ ?_
  · -- `log D` is measurable (D is a measurable real function, positive)
    have hD_meas_real : Measurable D := by
      rw [hD_def]; unfold perLetterRealDensity
      exact measurable_const.mul (Finset.measurable_sum _
        (fun m _ => measurable_gaussianPDFReal (c.encoder m i) N))
    exact (Real.measurable_log.comp hD_meas_real).aestronglyMeasurable
  · filter_upwards with y
    -- `|log (D y)| ≤ A + Bcoef·(y-a₀)²`
    have hDy_pos : 0 < D y := hD_pos y
    have h_upper : Real.log (D y) ≤ Real.log Bpeak :=
      Real.log_le_log hDy_pos (hD_le y)
    have h_lower : Real.log (1 / (M : ℝ)) + c₀ + c₁ * (y - a₀) ^ 2 ≤ Real.log (D y) := by
      have h_ge := hD_ge y
      have hMinv_pos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hga_pos : 0 < gaussianPDFReal a₀ N y := gaussianPDFReal_pos _ _ y hN
      have h_log_prod : Real.log ((1 / (M : ℝ)) * gaussianPDFReal a₀ N y)
          = Real.log (1 / (M : ℝ)) + c₀ + c₁ * (y - a₀) ^ 2 := by
        rw [Real.log_mul hMinv_pos.ne' hga_pos.ne',
          log_gaussianPDFReal_eq a₀ hN y, hc₀, hc₁]
        ring
      calc Real.log (1 / (M : ℝ)) + c₀ + c₁ * (y - a₀) ^ 2
          = Real.log ((1 / (M : ℝ)) * gaussianPDFReal a₀ N y) := h_log_prod.symm
        _ ≤ Real.log (D y) := Real.log_le_log (mul_pos hMinv_pos hga_pos) h_ge
    -- combine
    rw [Real.norm_eq_abs, abs_le]
    have hsq_nonneg : 0 ≤ (y - a₀) ^ 2 := sq_nonneg _
    have hc₁_nonpos : c₁ ≤ 0 := by
      rw [hc₁]; simp only [neg_nonpos]; positivity
    constructor
    · -- lower: `-(A + Bcoef·sq) ≤ log (D y)`
      have h1 : -(A + Bcoef * (y - a₀) ^ 2) ≤ Real.log (1 / (M : ℝ)) + c₀ + c₁ * (y - a₀) ^ 2 := by
        rw [hA, hBcoef]
        have hc₁_abs : c₁ * (y - a₀) ^ 2 = -(|c₁| * (y - a₀) ^ 2) := by
          rw [abs_of_nonpos hc₁_nonpos]; ring
        have hlb1 : -(|Real.log Bpeak| + |Real.log (1 / (M : ℝ)) + c₀|)
            ≤ Real.log (1 / (M : ℝ)) + c₀ := by
          have := neg_abs_le (Real.log (1 / (M : ℝ)) + c₀)
          have h2 := abs_nonneg (Real.log Bpeak)
          linarith
        rw [hc₁_abs]; linarith
      exact le_trans h1 h_lower
    · -- upper: `log (D y) ≤ A + Bcoef·sq`
      have h2 : Real.log Bpeak ≤ A + Bcoef * (y - a₀) ^ 2 := by
        rw [hA, hBcoef]
        have := le_abs_self (Real.log Bpeak)
        have h3 : 0 ≤ |Real.log (1 / (M : ℝ)) + c₀| := abs_nonneg _
        have h4 : 0 ≤ |c₁| * (y - a₀) ^ 2 := mul_nonneg (abs_nonneg _) hsq_nonneg
        linarith
      exact le_trans h_upper h2

/-- The per-letter mutual information equals the output differential entropy minus the
input-independent noise entropy: `I(Xᵢ; Yᵢ).toReal = h(Yᵢ) − h(𝒩(0, N))`, via the
generic continuous-channel mutual-information chain rule and the AWGN
translation invariance of the fibre entropy.
@audit:ok -/
theorem awgn_per_letter_mi_bridge_genuine
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (perLetterMI h_meas c i).toReal
      = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
        - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  have hN_NN : N ≠ 0 := fun h => hN (by exact_mod_cast h)
  set p := perLetterXLaw h_meas c i with hp_def
  set W := awgnChannel N h_meas with hW_def
  set q := outputDistribution p W with hq_def
  have hq_eq : q = perLetterYLaw h_meas c i := outputDistribution_eq_perLetterYLaw h_meas c i
  -- measurable PDF proxy `g := gaussianPDF` (Route B)
  set g : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF z.1 N z.2 with hg_def
  have hg_meas : Measurable g := by
    rw [hg_def]; simp only [gaussianPDF, gaussianPDFReal]; fun_prop
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
    intro x
    rw [hW_def, awgnChannel_apply]
    exact (gaussianReal_absolutelyContinuous x hN_NN).ae_le (rnDeriv_gaussianReal x N)
  -- fibre / output / joint absolute continuities for the mixture input
  have hW_ac : ∀ x, W x ≪ volume := by
    intro x; rw [hW_def, awgnChannel_apply]; exact gaussianReal_absolutelyContinuous x hN_NN
  have hWx_q : ∀ x, W x ≪ q := by
    intro x; rw [hq_eq, hW_def]; exact awgnChannel_ac_perLetterYLaw hN_NN h_meas c i x
  have hq_ac : q ≪ volume := by rw [hq_eq]; exact perLetterYLaw_ac_volume hN_NN h_meas c i
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod q := by
    rw [show p.prod q = p ⊗ₘ (Kernel.const ℝ q) from (Measure.compProd_const).symm]
    exact Measure.absolutelyContinuous_compProd_right_iff.mpr
      (Filter.Eventually.of_forall (fun x => by simpa only [Kernel.const_apply] using hWx_q x))
  -- ★ fibre log-density integrability against the joint (proxy form, mixture input)
  have h_int_fibre :
      Integrable (fun z : ℝ × ℝ => Real.log (g z).toReal) (p ⊗ₘ W) := by
    -- the joint integrand decomposes everywhere as `c₀ + c₁·(z.2 − z.1)²`
    set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
    set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
    have h_eq : (fun z : ℝ × ℝ => Real.log (g z).toReal)
        = fun z => c₀ + c₁ * (z.2 - z.1) ^ 2 := by
      funext z
      rw [hg_def, toReal_gaussianPDF,
        InformationTheory.Shannon.log_gaussianPDFReal_eq z.1 hN_NN z.2, hc₀, hc₁]
      ring
    rw [h_eq]
    have h_sq : Integrable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W) := by
      have h_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W) :=
        ((measurable_snd.sub measurable_fst).pow_const 2).aestronglyMeasurable
      rw [Measure.integrable_compProd_iff h_aesm]
      refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
      · -- per-fibre `Integrable (fun y => (y − x)²) (W x = gaussianReal x N)`
        have h_id : Integrable (fun y : ℝ => y) (gaussianReal x N) := by
          simpa using (memLp_id_gaussianReal (μ := x) (v := N) 1).integrable (by norm_num)
        have h_sq2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal x N) :=
          (memLp_id_gaussianReal (μ := x) (v := N) 2).integrable_sq
        have hrw : (fun y : ℝ => (y - x) ^ 2) = fun y => y ^ 2 - 2 * x * y + x ^ 2 := by
          funext y; ring
        rw [hW_def, awgnChannel_apply, hrw]
        exact ((h_sq2.sub (h_id.const_mul (2 * x))).add (integrable_const (x ^ 2)))
      · -- per-fibre L¹-norm integral is the constant `N` (nonneg integrand, second moment)
        have h_norm : (fun x => ∫ y, ‖(y - x) ^ 2‖ ∂(W x)) = fun _ => (N : ℝ) := by
          funext x
          have hnn : (fun y => ‖(y - x) ^ 2‖) = fun y => (y - x) ^ 2 := by
            funext y; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          rw [hnn, hW_def, awgnChannel_apply]
          have hvar := variance_fun_id_gaussianReal (μ := x) (v := N)
          rw [variance_eq_integral (by fun_prop)] at hvar
          simpa only [id_eq, integral_id_gaussianReal] using hvar
        rw [h_norm]; exact integrable_const _
    exact (integrable_const c₀).add (h_sq.const_mul c₁)
  -- ★ output log-density integrability against the joint (depends only on z.2)
  have h_int_out :
      Integrable (fun z : ℝ × ℝ => Real.log (q.rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    have hp_prob : IsProbabilityMeasure p := by rw [hp_def]; infer_instance
    have h_int_marg :
        Integrable (fun y => Real.log (q.rnDeriv volume y).toReal) q := by
      rw [hq_eq]; exact integrable_log_rnDeriv_perLetterYLaw hN_NN h_meas c i
    -- `q = (p ⊗ₘ W).snd`, so `g ∘ snd` integrable against joint iff `g` against `q`.
    have h_snd : q = (p ⊗ₘ W).map Prod.snd := rfl
    rw [show (fun z : ℝ × ℝ => Real.log (q.rnDeriv volume z.2).toReal)
          = (fun y => Real.log (q.rnDeriv volume y).toReal) ∘ Prod.snd from rfl]
    refine (integrable_map_measure ?_ measurable_snd.aemeasurable).mp ?_
    · exact ((Measure.measurable_rnDeriv q volume).ennreal_toReal.log).aestronglyMeasurable
    · rw [← h_snd]; exact h_int_marg
  -- apply the generic chain-rule asset
  have h_decomp :=
    mutualInfoOfChannel_toReal_eq_diffEntropy_sub (p := p) (W := W)
      hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out
  -- rewrite `perLetterMI` to the channel form, then identify the two entropy terms.
  rw [perLetterMI_eq_mutualInfoOfChannel h_meas c i, ← hp_def, ← hW_def, h_decomp,
    ← hq_def, hq_eq, integral_diffEntropy_awgnChannel_eq_noise hN_NN h_meas c i]

/-! ## The converse rate bound -/

/-- **AWGN converse theorem** (Cover–Thomas, Theorem 9.1.2). For every code with
`M ≥ 2` messages, block length `n`, output-power constraint `P` and average error
probability `Pe`, the rate satisfies

`log M ≤ n·(1/2) log(1 + P/N) + binEntropy(Pe) + Pe·log(M - 1)`.

The per-letter mutual-information bridge is supplied by
`awgn_per_letter_mi_bridge_genuine`, and the rate bound is assembled by
`awgn_converse_F3_discharged`. -/
@[entry_point]
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  -- per-letter MI bridge (`I(X_i; Y_i) = h(Y_i) - h(Z)`), now genuinely closed by
  -- `awgn_per_letter_mi_bridge_genuine` (mixture→compProd factorization + the generic
  -- continuous-channel MI chain rule asset).
  have h_mi_bridge_per_letter :
      ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
        (perLetterMI h_meas c i).toReal
          = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - InformationTheory.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N) :=
    fun {M n} _ _ c i => awgn_per_letter_mi_bridge_genuine hN h_meas c i
  exact awgn_converse_F3_discharged P hP N hN h_meas
    h_mi_bridge_per_letter hM hn_pos c Pe hPe

end InformationTheory.Shannon.AWGN
