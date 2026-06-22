import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import InformationTheory.Shannon.MultivariateDiffEntropy
import InformationTheory.Shannon.AWGN.ConverseMutualInfoFiniteness

/-! # AWGN channel-coding converse — Gaussian capacity bound and assembly

Builds the capacity-bound layer of the AWGN channel-coding converse (Cover–Thomas, 9.1.2):
the per-letter input second moment, the per-letter Gaussian maximum-entropy bound, Jensen's
inequality, the sum-form capacity bound `∑ᵢ I(Xᵢ; Yᵢ) ≤ n · (1/2) log(1 + P/N)`, and the
final assembly into `log M ≤ n · (1/2) log(1 + P/N) + binEntropy(Pe) + Pe · log(M − 1)`.

## Main definitions

* `perLetterInputSecondMoment` — the per-letter input second moment under a uniform message.

## Main statements

* `awgn_per_letter_mi_le_log_var` — the per-letter Gaussian maximum-entropy bound.
* `awgn_sum_per_letter_mi_le_n_capacity` — `∑ᵢ I(Xᵢ; Yᵢ) ≤ n · (1/2) log(1 + P/N)`.
* `isAwgnConverseFeasible_discharger` / `awgn_converse_F3_discharged` — the assembled
  converse inequality.

## Implementation notes

* The capacity bound is built from a sum form (per-letter second moment, per-letter
  Gaussian maximum-entropy, and Jensen) rather than a per-letter power constraint, because
  the per-message power constraint does not yield a per-letter `E[Xᵢ²] ≤ P`.
* `h_mi_bridge_per_letter` carries the bridge `I(Xᵢ; Yᵢ) = h(Yᵢ) − h(Z)` as an explicit
  hypothesis; it is discharged elsewhere. -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
  InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

/-! ## Per-letter input second moment, Jensen, and the sum-form capacity bound

The capacity bound `∑ᵢ I(Xᵢ; Yᵢ) ≤ n · (1/2) log(1 + P/N)` is established in sum form via the
per-letter Gaussian maximum-entropy bound and Jensen's inequality, rather than from a
per-letter power constraint (which does not follow from the per-message power constraint). -/

/-- Per-letter input second moment `E[Xᵢ² | W ∼ Uniform(Fin M)] = (1/M) ∑ₘ (c.encoder m i)²`,
the second moment of the input letter `Xᵢ = c.encoder W i` under a uniform message. -/
@[entry_point]
noncomputable def perLetterInputSecondMoment
    {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) (i : Fin n) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, (c.encoder m i) ^ 2

/-- The average of the per-letter input second moments is bounded by `P`:
`(1/n) ∑ᵢ E[Xᵢ²] ≤ P`, from the per-message power constraint by a Fubini swap. -/
@[entry_point]
theorem awgn_per_letter_input_power_avg
    {M n : ℕ} (hM_pos : 0 < M) (hn_pos : 0 < n) {P : ℝ}
    (c : AwgnCode M n P) :
    (1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i ≤ P := by
  -- Unfold the per-letter second-moment definition.
  unfold perLetterInputSecondMoment
  -- Bring the `(1/M)` constant out of `∑ i`.
  have h_pull_M :
      (∑ i : Fin n, (1 / (M : ℝ)) * ∑ m : Fin M, (c.encoder m i) ^ 2)
        = (1 / (M : ℝ)) * ∑ i : Fin n, ∑ m : Fin M, (c.encoder m i) ^ 2 := by
    rw [← Finset.mul_sum]
  rw [h_pull_M]
  -- Fubini swap: `∑ i ∑ m = ∑ m ∑ i`.
  rw [Finset.sum_comm]
  -- Apply `power_constraint` term-by-term inside the inner sum.
  have h_power_each : ∀ m : Fin M, (∑ i : Fin n, (c.encoder m i) ^ 2) ≤ (n : ℝ) * P :=
    c.power_constraint
  -- Bound the inner double sum by `M · (n · P)`.
  have h_sum_bound :
      (∑ m : Fin M, ∑ i : Fin n, (c.encoder m i) ^ 2)
        ≤ ∑ _m : Fin M, (n : ℝ) * P := by
    apply Finset.sum_le_sum
    intro m _
    exact h_power_each m
  have h_const_sum :
      (∑ _m : Fin M, (n : ℝ) * P) = (M : ℝ) * ((n : ℝ) * P) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [h_const_sum] at h_sum_bound
  -- Now: (1/n) * ((1/M) * (something ≤ M·n·P)) ≤ P.
  have hM_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  -- Step: pull `(1/n)` past `(1/M) * ...`.
  have h_combine :
      (1 / (n : ℝ)) * ((1 / (M : ℝ)) *
          (∑ m : Fin M, ∑ i : Fin n, (c.encoder m i) ^ 2))
        ≤ (1 / (n : ℝ)) * ((1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * P))) := by
    have h_inner : (1 / (M : ℝ)) *
          (∑ m : Fin M, ∑ i : Fin n, (c.encoder m i) ^ 2)
        ≤ (1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * P)) := by
      apply mul_le_mul_of_nonneg_left h_sum_bound
      positivity
    apply mul_le_mul_of_nonneg_left h_inner
    positivity
  -- Simplify the RHS to `P`.
  have h_rhs : (1 / (n : ℝ)) * ((1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * P))) = P := by
    field_simp
  rw [h_rhs] at h_combine
  exact h_combine

/-! ### Helpers for the per-letter maximum-entropy bound -/

/-- Closed form of `perLetterYLaw`: mixture of Gaussians
`(M⁻¹ : ℝ≥0∞) • ∑ₘ gaussianReal (c.encoder m i) N`. -/
private lemma perLetterYLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  unfold perLetterYLaw awgnConverseJoint
  -- map distributes over smul and finset sum.
  have h_meas_eval :
      Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  rw [Measure.map_smul]
  rw [Measure.map_finset_sum (s := Finset.univ)
      (m := fun m ↦ (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n ↦ awgnChannel N h_meas (c.encoder m j))))
      h_meas_eval.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  -- ((dirac m).prod ν).map (fun ω => ω.2 i)
  --   = (ν.map (fun y => y i))                 -- via map_snd_prod ∘ map_eval composition
  --   = gaussianReal (c.encoder m i) N
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  have h_meas_eval_i :
      Measurable (Function.eval i : (Fin n → ℝ) → ℝ) := measurable_pi_apply i
  have h_decomp : (fun ω : Fin M × (Fin n → ℝ) ↦ ω.2 i)
      = (Function.eval i) ∘ Prod.snd := rfl
  rw [h_decomp]
  rw [← Measure.map_map h_meas_eval_i h_meas_snd]
  -- Map of `Prod.snd` first.
  rw [Measure.map_snd_prod]
  -- dirac univ = 1, so `(dirac m univ) • Measure.pi ν = Measure.pi ν`.
  have h_dirac_univ : (Measure.dirac m : Measure (Fin M)) Set.univ = 1 := by
    simp
  rw [h_dirac_univ, one_smul]
  -- Now: `(Measure.pi ν).map (Function.eval i) = gaussianReal (c.encoder m i) N`.
  rw [Measure.pi_map_eval]
  -- Each `μ j Set.univ = 1` because `gaussianReal` is a probability measure.
  have h_other : ∀ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ = 1 := by
    intro j _
    rw [awgnChannel_apply]
    exact measure_univ
  rw [Finset.prod_congr rfl h_other, Finset.prod_const_one, one_smul]
  rw [awgnChannel_apply]

/-- Probability measure structure of `perLetterYLaw`. -/
private lemma perLetterYLaw_isProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    IsProbabilityMeasure (perLetterYLaw h_meas c i) := by
  unfold perLetterYLaw
  have h_meas_eval :
      Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact Measure.isProbabilityMeasure_map h_meas_eval.aemeasurable

/-- Absolute continuity of `perLetterYLaw` w.r.t. Lebesgue volume,
needed for `differentialEntropy_le_gaussian_of_variance_le`. -/
private lemma perLetterYLaw_absolutelyContinuous
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterYLaw h_meas c i ≪ MeasureTheory.volume := by
  classical
  have hN_ne : N ≠ 0 := by
    intro h; apply hN; exact_mod_cast h
  rw [perLetterYLaw_eq_mixture h_meas c i]
  -- each `gaussianReal (c.encoder m i) N ≪ volume`, finset sum AC ⇒ smul AC.
  refine Measure.AbsolutelyContinuous.smul_left ?_ _
  -- Convert finset sum to `Measure.sum` to apply `absolutelyContinuous_sum_left`.
  rw [← Measure.sum_fintype]
  exact Measure.absolutelyContinuous_sum_left fun m ↦
    gaussianReal_absolutelyContinuous _ hN_ne

/-- Integral against `perLetterYLaw`: linearity over the mixture. -/
private lemma perLetterYLaw_integral
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n)
    {f : ℝ → ℝ} (hf : ∀ m : Fin M, Integrable f (gaussianReal (c.encoder m i) N)) :
    ∫ x, f x ∂(perLetterYLaw h_meas c i)
      = (1 / (M : ℝ)) * ∑ m : Fin M, ∫ x, f x ∂(gaussianReal (c.encoder m i) N) := by
  classical
  rw [perLetterYLaw_eq_mixture h_meas c i]
  rw [integral_smul_measure]
  -- Now goal: (M⁻¹ : ℝ≥0∞).toReal • ∫ f ∂(∑ m, gaussianReal ...) = (1/M) * ∑ m, ∫ ...
  rw [integral_finsetSum_measure (fun m _ ↦ hf m)]
  rw [Fintype.card_fin]
  -- `(M⁻¹ : ℝ≥0∞).toReal = 1/M` and scalar smul on ℝ is just mul.
  have h_inv : ((M : ℝ≥0∞)⁻¹).toReal = 1 / (M : ℝ) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  rw [h_inv]
  show (1 / (M : ℝ)) • (∑ m : Fin M, ∫ x, f x ∂(gaussianReal (c.encoder m i) N))
      = (1 / (M : ℝ)) * (∑ m : Fin M, ∫ x, f x ∂(gaussianReal (c.encoder m i) N))
  rw [smul_eq_mul]

/-- The per-letter mean of `Y_i`: equals the average of encoder values. -/
private lemma perLetterYLaw_mean
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    ∫ x, x ∂(perLetterYLaw h_meas c i)
      = (1 / (M : ℝ)) * ∑ m : Fin M, c.encoder m i := by
  have h_int : ∀ m : Fin M, Integrable (fun x : ℝ ↦ x) (gaussianReal (c.encoder m i) N) := by
    intro m
    have : MemLp (id : ℝ → ℝ) 1 (gaussianReal (c.encoder m i) N) :=
      memLp_id_gaussianReal' 1 ENNReal.one_ne_top
    exact (memLp_one_iff_integrable.mp this)
  rw [perLetterYLaw_integral h_meas c i h_int]
  simp_rw [integral_id_gaussianReal]

/-- Per-letter integrability of `(x - m)²` against each mixture component. -/
private lemma gaussianReal_integrable_sub_sq (a : ℝ) {N : ℝ≥0} (m : ℝ) :
    Integrable (fun x : ℝ ↦ (x - m) ^ 2) (gaussianReal a N) := by
  -- `id - const m` is `MemLp 2` via `memLp_id_gaussianReal 2` minus a constant.
  have h_id : MemLp (id : ℝ → ℝ) 2 (gaussianReal a N) :=
    memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
  have h_sub : MemLp (fun x : ℝ ↦ x - m) 2 (gaussianReal a N) := by
    have := h_id.sub (memLp_const m)
    simpa using this
  exact h_sub.integrable_sq

/-- Integrability of `(x - m)²` against `perLetterYLaw`. -/
private lemma perLetterYLaw_var_integrable
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (m : ℝ) :
    Integrable (fun x : ℝ ↦ (x - m) ^ 2) (perLetterYLaw h_meas c i) := by
  classical
  rw [perLetterYLaw_eq_mixture h_meas c i]
  -- Goal: Integrable f (M⁻¹ • ∑ k, gaussianReal (c.encoder k i) N)
  have hM_ne_zero : (Fintype.card (Fin M) : ℝ≥0∞) ≠ 0 := by
    rw [Fintype.card_fin]
    exact_mod_cast (NeZero.ne M)
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hM_ne_zero
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  -- Goal: Integrable f (∑ k, gaussianReal (c.encoder k i) N)
  rw [integrable_finsetSum_measure]
  intro k _
  exact gaussianReal_integrable_sub_sq (c.encoder k i) m

/-- Second moment around an arbitrary point `m_avg` for a real Gaussian:
`∫ (x - m_avg)² ∂(gaussianReal a N) = (a - m_avg)² + N`. -/
private lemma gaussianReal_integral_sub_sq
    (a : ℝ) {N : ℝ≥0} (m_avg : ℝ) :
    ∫ x, (x - m_avg) ^ 2 ∂(gaussianReal a N)
      = (a - m_avg) ^ 2 + (N : ℝ) := by
  -- Define f x := (x - m_avg)² and rewrite the integral via the decomposition
  -- (x - m_avg)² = (x - a)² + 2(x - a)(a - m_avg) + (a - m_avg)².
  have h_int_id : Integrable (fun x : ℝ ↦ x) (gaussianReal a N) := by
    have : MemLp (id : ℝ → ℝ) 1 (gaussianReal a N) :=
      memLp_id_gaussianReal' 1 ENNReal.one_ne_top
    exact (memLp_one_iff_integrable.mp this)
  have h_int1 : Integrable (fun x : ℝ ↦ (x - a) ^ 2) (gaussianReal a N) :=
    gaussianReal_integrable_sub_sq a a
  have h_int_xa : Integrable (fun x : ℝ ↦ x - a) (gaussianReal a N) :=
    h_int_id.sub (integrable_const a)
  -- Rewrite integrand pointwise via `integral_congr`.
  have h_eq_fun :
      (fun x : ℝ ↦ (x - m_avg) ^ 2)
        = (fun x : ℝ ↦ (x - a) ^ 2 + 2 * (x - a) * (a - m_avg) + (a - m_avg) ^ 2) := by
    funext x; ring
  rw [h_eq_fun]
  have h_int2 : Integrable (fun x : ℝ ↦ 2 * (x - a) * (a - m_avg)) (gaussianReal a N) := by
    have h_lin : Integrable (fun x : ℝ ↦ 2 * (x - a)) (gaussianReal a N) := by
      simpa [mul_comm] using h_int_xa.const_mul 2
    simpa [mul_assoc] using h_lin.mul_const (a - m_avg)
  have h_int3 : Integrable (fun _ : ℝ ↦ (a - m_avg) ^ 2) (gaussianReal a N) :=
    integrable_const _
  -- Split integral by linearity.
  have h_sum_step1 :
      ∫ x, ((x - a) ^ 2 + 2 * (x - a) * (a - m_avg)) + (a - m_avg) ^ 2 ∂(gaussianReal a N)
        = ∫ x, ((x - a) ^ 2 + 2 * (x - a) * (a - m_avg)) ∂(gaussianReal a N)
          + ∫ _, (a - m_avg) ^ 2 ∂(gaussianReal a N) :=
    integral_add (h_int1.add h_int2) h_int3
  have h_sum_step2 :
      ∫ x, (x - a) ^ 2 + 2 * (x - a) * (a - m_avg) ∂(gaussianReal a N)
        = ∫ x, (x - a) ^ 2 ∂(gaussianReal a N)
          + ∫ x, 2 * (x - a) * (a - m_avg) ∂(gaussianReal a N) :=
    integral_add h_int1 h_int2
  rw [h_sum_step1, h_sum_step2]
  -- 1) ∫ (x - a)² ∂(gaussianReal a N) = N via `variance_fun_id_gaussianReal`.
  have h_var_eq : ∫ x, (x - a) ^ 2 ∂(gaussianReal a N) = (N : ℝ) := by
    have h_var := variance_fun_id_gaussianReal (μ := a) (v := N)
    rw [variance_eq_integral measurable_id'.aemeasurable] at h_var
    simp only [integral_id_gaussianReal] at h_var
    exact h_var
  -- 2) ∫ 2(x - a)(a - m_avg) ∂(gaussianReal a N) = 0 since mean = a.
  have h_lin_zero : ∫ x, 2 * (x - a) * (a - m_avg) ∂(gaussianReal a N) = 0 := by
    have h_factor : (fun x : ℝ ↦ 2 * (x - a) * (a - m_avg))
        = (fun x : ℝ ↦ (2 * (a - m_avg)) * (x - a)) := by
      funext x; ring
    rw [h_factor, integral_const_mul]
    have h_mean_zero : ∫ x, (x - a) ∂(gaussianReal a N) = 0 := by
      rw [integral_sub h_int_id (integrable_const a)]
      rw [integral_id_gaussianReal, integral_const]
      simp
    rw [h_mean_zero, mul_zero]
  -- 3) ∫ (a - m_avg)² ∂(prob) = (a - m_avg)² since gaussianReal is a probability measure.
  have h_const_eq : ∫ _, (a - m_avg) ^ 2 ∂(gaussianReal a N) = (a - m_avg) ^ 2 := by
    rw [integral_const]; simp
  rw [h_var_eq, h_lin_zero, h_const_eq]
  ring

/-- Variance bound for `perLetterYLaw`: `∫ (x - m_avg)² ∂μ ≤ E[X_i²] + N`. -/
private lemma perLetterYLaw_variance_le
    {P : ℝ} {N : ℝ≥0} (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    ∫ x, (x - ((1 / (M : ℝ)) * ∑ m : Fin M, c.encoder m i)) ^ 2
        ∂(perLetterYLaw h_meas c i)
      ≤ perLetterInputSecondMoment c i + (N : ℝ) := by
  classical
  set m_avg : ℝ := (1 / (M : ℝ)) * ∑ k : Fin M, c.encoder k i with hm_avg_def
  -- Step 1: distribute integral via mixture.
  have h_int_mix :
      ∫ x, (x - m_avg) ^ 2 ∂(perLetterYLaw h_meas c i)
        = (1 / (M : ℝ)) * ∑ k : Fin M,
            ∫ x, (x - m_avg) ^ 2 ∂(gaussianReal (c.encoder k i) N) :=
    perLetterYLaw_integral h_meas c i (fun k ↦
      gaussianReal_integrable_sub_sq (c.encoder k i) m_avg)
  rw [h_int_mix]
  -- Step 2: each summand simplifies to `(c.encoder k i - m_avg)² + N`.
  have h_each : ∀ k : Fin M,
      ∫ x, (x - m_avg) ^ 2 ∂(gaussianReal (c.encoder k i) N)
        = (c.encoder k i - m_avg) ^ 2 + (N : ℝ) := fun k ↦
    gaussianReal_integral_sub_sq (c.encoder k i) m_avg
  simp_rw [h_each]
  -- Step 3: split sum = ∑ (...)² + ∑ N = (∑ (...)²) + M·N.
  rw [Finset.sum_add_distrib]
  -- Constant sum.
  have h_const_sum : (∑ _k : Fin M, (N : ℝ)) = (M : ℝ) * (N : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [h_const_sum]
  -- Goal: (1/M) · (∑ (encoder k - m_avg)² + M·N) ≤ S² + N
  -- = (1/M) · ∑ (encoder k - m_avg)² + (1/M) · M · N
  -- = (1/M) · ∑ (encoder k - m_avg)² + N   (since M > 0)
  -- We must show (1/M) · ∑ (encoder k - m_avg)² ≤ S².
  -- Expand: ∑ (x_k - m_avg)² = ∑ x_k² - 2 m_avg ∑ x_k + M·m_avg²
  -- (1/M)·∑ (...)² = S² - 2 m_avg² + m_avg² = S² - m_avg² ≤ S².
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_real
  -- RHS algebra: (1/M) · (A + M·N) = (1/M)·A + N.
  have h_split :
      (1 / (M : ℝ)) *
          ((∑ k : Fin M, (c.encoder k i - m_avg) ^ 2) + (M : ℝ) * (N : ℝ))
        = (1 / (M : ℝ)) * (∑ k : Fin M, (c.encoder k i - m_avg) ^ 2)
          + (N : ℝ) := by
    field_simp
  rw [h_split]
  -- Suffices: (1/M) · ∑ (c.encoder k i - m_avg)² ≤ perLetterInputSecondMoment c i.
  -- Expand the sum.
  have h_sum_expand :
      (∑ k : Fin M, (c.encoder k i - m_avg) ^ 2)
        = (∑ k : Fin M, (c.encoder k i) ^ 2)
          - 2 * m_avg * (∑ k : Fin M, c.encoder k i)
          + (M : ℝ) * m_avg ^ 2 := by
    have : ∀ k : Fin M,
        (c.encoder k i - m_avg) ^ 2
          = (c.encoder k i) ^ 2 - 2 * m_avg * c.encoder k i + m_avg ^ 2 := by
      intro k; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  rw [h_sum_expand]
  -- ∑ c.encoder k i = M · m_avg.
  have h_sum_eq : (∑ k : Fin M, c.encoder k i) = (M : ℝ) * m_avg := by
    rw [hm_avg_def]
    field_simp
  rw [h_sum_eq]
  -- Now: (1/M) · ((∑ (encoder k)²) - 2 m_avg · M m_avg + M m_avg²)
  --     = (1/M) · ∑ (encoder k)² - 2 m_avg² + m_avg² = S² - m_avg².
  have h_simplify :
      (1 / (M : ℝ)) * ((∑ k : Fin M, (c.encoder k i) ^ 2)
            - 2 * m_avg * ((M : ℝ) * m_avg) + (M : ℝ) * m_avg ^ 2)
        = perLetterInputSecondMoment c i - m_avg ^ 2 := by
    unfold perLetterInputSecondMoment
    field_simp
    ring
  rw [h_simplify]
  -- Conclude: S² - m_avg² + N ≤ S² + N since m_avg² ≥ 0.
  have hm_sq_nn : 0 ≤ m_avg ^ 2 := sq_nonneg _
  linarith

/-- Per-letter mutual-information bound via the per-letter input variance:
`I(Xᵢ; Yᵢ) ≤ (1/2) log(1 + perLetterInputSecondMoment c i / N)`, derived from the Gaussian
maximum-entropy bound `differentialEntropy_le_gaussian_of_variance_le`. The variance of `Yᵢ`
is at most `E[Xᵢ²] + N` since the input and the noise are independent, giving
```
I(Xᵢ; Yᵢ) = h(Yᵢ) − h(gaussianReal 0 N)              -- bridge hypothesis
          ≤ (1/2) log(2πe·v_Y) − (1/2) log(2πe·N)    -- Gaussian maximum entropy
          = (1/2) log(v_Y / N) ≤ (1/2) log((S² + N)/N)
          = (1/2) log(1 + S²/N)
```
with `v_Y := (perLetterInputSecondMoment c i + N).toNNReal`. -/
@[entry_point]
theorem awgn_per_letter_mi_le_log_var
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - InformationTheory.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N))
    (i : Fin n) :
    (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
  -- Positivity.
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_ne N.coe_nonneg (Ne.symm hN)
  have hN_ne_nnreal : N ≠ 0 := by
    intro h; apply hN; exact_mod_cast h
  -- Mean of `X_i` under uniform `W`: `m := (1/M) ∑ₘ c.encoder m i`.
  set m : ℝ := (1 / (M : ℝ)) * ∑ k : Fin M, c.encoder k i with hm_def
  -- `S² := perLetterInputSecondMoment c i`, non-negative.
  set S2 : ℝ := perLetterInputSecondMoment c i with hS2_def
  have hS2_nn : (0 : ℝ) ≤ S2 := by
    rw [hS2_def]; unfold perLetterInputSecondMoment
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  -- `v_Y := (S² + N).toNNReal`. Positivity from N > 0.
  set v : ℝ≥0 := (S2 + (N : ℝ)).toNNReal with hv_def
  have h_v_eq : (v : ℝ) = S2 + (N : ℝ) := by
    rw [hv_def]
    have : (0 : ℝ) ≤ S2 + (N : ℝ) := by linarith
    rw [Real.coe_toNNReal _ this]
  have hv_ne : v ≠ 0 := by
    intro hv_eq
    have : (v : ℝ) = 0 := by exact_mod_cast hv_eq
    rw [h_v_eq] at this
    linarith
  have hv_pos : (0 : ℝ) < (v : ℝ) := by rw [h_v_eq]; linarith
  -- Probability measure structure on per-letter Y.
  haveI : IsProbabilityMeasure (perLetterYLaw h_meas c i) :=
    perLetterYLaw_isProbabilityMeasure h_meas c i
  -- 4 hyp for `differentialEntropy_le_gaussian_of_variance_le`.
  have h_mu_ac : perLetterYLaw h_meas c i ≪ MeasureTheory.volume :=
    perLetterYLaw_absolutelyContinuous hN h_meas c i
  have h_mean : ∫ x, x ∂(perLetterYLaw h_meas c i) = m :=
    perLetterYLaw_mean hN h_meas c i
  have h_var : ∫ x, (x - m) ^ 2 ∂(perLetterYLaw h_meas c i) ≤ (v : ℝ) := by
    rw [h_v_eq]
    exact perLetterYLaw_variance_le hN h_meas c i
  have h_var_int :
      Integrable (fun x : ℝ ↦ (x - m) ^ 2) (perLetterYLaw h_meas c i) :=
    perLetterYLaw_var_integrable hN h_meas c i m
  -- Per-letter log-density integrability via `awgnPerLetterIntegrability_holds`
  -- (`AwgnWalls.lean`); `perLetterYLaw h_meas c i` matches by definitional equality.
  have h_ent_int :
      Integrable (fun y : ℝ ↦
          Real.negMulLog
            ((perLetterYLaw h_meas c i).rnDeriv MeasureTheory.volume y).toReal)
        MeasureTheory.volume := awgnPerLetterIntegrability_holds h_meas c i
  -- Apply Gaussian max-entropy upper bound.
  have h_max_ent :
      InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
        ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) :=
    InformationTheory.Shannon.differentialEntropy_le_gaussian_of_variance_le
      h_mu_ac m hv_ne h_mean h_var h_var_int h_ent_int
  -- `h(gaussianReal 0 N) = (1/2) log(2πe N)`.
  have h_gauss_ent :
      InformationTheory.Shannon.differentialEntropy (ProbabilityTheory.gaussianReal 0 N)
        = (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) :=
    InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN_ne_nnreal
  -- Combine via bridge.
  rw [h_mi_bridge_per_letter i, h_gauss_ent]
  -- Goal: h(Y) - (1/2) log(2πeN) ≤ (1/2) log(1 + S²/N).
  -- (1/2) log(2πe·v) - (1/2) log(2πe·N) = (1/2) log(v/N).
  have h2πe_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by
    have := Real.pi_pos
    have := Real.exp_pos 1
    positivity
  have h2πev_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (v : ℝ) := by positivity
  have h2πeN_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N : ℝ) := by positivity
  have h_log_diff :
      (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
        - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
        = (1 / 2) * Real.log ((v : ℝ) / (N : ℝ)) := by
    rw [← mul_sub, ← Real.log_div h2πev_pos.ne' h2πeN_pos.ne']
    congr 2
    field_simp
  -- v / N = 1 + S² / N.
  have h_v_div : (v : ℝ) / (N : ℝ) = 1 + S2 / (N : ℝ) := by
    rw [h_v_eq, add_div, div_self hN]
    linarith
  -- Chain: h(Y) - h(Z) ≤ (1/2) log(2πe·v) - (1/2) log(2πe·N)
  --       = (1/2) log(v/N) = (1/2) log(1 + S²/N).
  calc InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
        - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
      ≤ (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
        - (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) := by linarith
    _ = (1 / 2) * Real.log ((v : ℝ) / (N : ℝ)) := h_log_diff
    _ = (1 / 2) * Real.log (1 + S2 / (N : ℝ)) := by rw [h_v_div]

/-- Jensen's inequality for the concave map `log(1 + ·/N)`:
`∑ᵢ (1/2) log(1 + xᵢ/N) ≤ n · (1/2) log(1 + (∑ᵢ xᵢ / n) / N)` for `xᵢ ≥ 0`.

`Real.log` is concave on `Ioi 0` (`Mathlib.Analysis.Convex.SpecificFunctions.Basic.
strictConcaveOn_log_Ioi`) ⇒ `fun x => Real.log (1 + x/N)` concave on `Ici 0` (composition
with affine increasing map, packaged as `concaveOn_log_one_add_div` in
`DifferentialEntropy.lean`). Apply `ConcaveOn.le_map_sum` with uniform weights
`wᵢ := 1/n`. -/
@[entry_point]
theorem sum_log_one_add_le_n_log_one_add_avg
    {n : ℕ} (hn_pos : 0 < n)
    (N : ℝ) (hN_pos : 0 < N)
    (xs : Fin n → ℝ) (hxs_nn : ∀ i, 0 ≤ xs i) :
    ∑ i : Fin n, (1 / 2) * Real.log (1 + xs i / N)
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, xs i) / N)) := by
  -- `f x := log(1 + x/N)` is concave on `Ici 0`.
  set f : ℝ → ℝ := fun x ↦ Real.log (1 + x / N) with hf_def
  have hf_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) f :=
    InformationTheory.Shannon.concaveOn_log_one_add_div hN_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- Uniform weights `wᵢ := 1/n`.
  set w : Fin n → ℝ := fun _ ↦ (1 : ℝ) / (n : ℝ) with hw_def
  have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := by
    intro i _; simp only [hw_def]; positivity
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
    simp [hw_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hxs_mem : ∀ i ∈ (Finset.univ : Finset (Fin n)), xs i ∈ Set.Ici (0 : ℝ) := by
    intro i _; exact hxs_nn i
  -- Apply Jensen.
  have h_jensen :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i • f (xs i))
        ≤ f (∑ i ∈ (Finset.univ : Finset (Fin n)), w i • xs i) :=
    hf_concave.le_map_sum hw_nn hw_sum hxs_mem
  -- Convert `smul` to `mul` on `ℝ`.
  simp only [smul_eq_mul, hw_def] at h_jensen
  -- `h_jensen : ∑ i, (1/n) * log(1 + xs i / N) ≤ log(1 + ((1/n) * ∑ i, xs i)/N)`
  -- after factoring `(1/n)` out of `∑ i, (1/n) * xs i`.
  rw [show (∑ i : Fin n, (1 : ℝ) / (n : ℝ) * xs i) = (1 / (n : ℝ)) * ∑ i : Fin n, xs i from
    (Finset.mul_sum Finset.univ xs ((1 : ℝ) / (n : ℝ))).symm] at h_jensen
  -- Multiply both sides by `(n : ℝ) > 0` and then by `(1/2) ≥ 0`.
  -- LHS goal: ∑ (1/2) * log(1 + xᵢ/N) = (n : ℝ) * (1/2) * ((1/n) * ∑ log(1 + xᵢ/N)).
  have h_lhs_rewrite :
      ∑ i : Fin n, (1 / 2 : ℝ) * Real.log (1 + xs i / N)
        = (n : ℝ) * ((1 / 2) * ((1 / (n : ℝ)) *
            ∑ i : Fin n, Real.log (1 + xs i / N))) := by
    rw [show (∑ i : Fin n, (1 / 2 : ℝ) * Real.log (1 + xs i / N))
      = (1 / 2 : ℝ) * ∑ i : Fin n, Real.log (1 + xs i / N) from
      (Finset.mul_sum Finset.univ (fun i ↦ Real.log (1 + xs i / N)) (1 / 2 : ℝ)).symm]
    field_simp
  rw [h_lhs_rewrite]
  -- Now goal: (n) * ((1/2) * ((1/n) * ∑ log(1+xᵢ/N))) ≤ (n) * ((1/2) * log(1+avg/N)).
  -- Apply monotonicity twice (factor (n) ≥ 0, then (1/2) ≥ 0).
  have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  apply mul_le_mul_of_nonneg_left _ hn_real_pos.le
  apply mul_le_mul_of_nonneg_left _ h_half_nn
  -- Goal: (1/n) * ∑ log(1+xᵢ/N) ≤ log(1 + ((1/n) * ∑ xᵢ)/N).
  -- This is exactly `h_jensen` after rewriting `∑ (1/n) * log(...) = (1/n) * ∑ log(...)`.
  have h_sum_factor :
      ∑ i : Fin n, (1 / (n : ℝ)) * Real.log (1 + xs i / N)
        = (1 / (n : ℝ)) * ∑ i : Fin n, Real.log (1 + xs i / N) :=
    (Finset.mul_sum Finset.univ (fun i ↦ Real.log (1 + xs i / N)) (1 / (n : ℝ))).symm
  rw [← h_sum_factor]
  -- `f (xs i) = log(1 + xs i / N)` and `f (∑ ...) = log(1 + (...)/N)`.
  exact h_jensen

/-- The sum of per-letter mutual informations is bounded by `n · (1/2) log(1 + P/N)`,
combining the per-letter maximum-entropy bound, the average input-power bound, and Jensen's
inequality for the concavity of `log(1 + ·/N)`. -/
@[entry_point]
theorem awgn_sum_per_letter_mi_le_n_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (hn_pos : 0 < n) (c : AwgnCode M n P)
    (h_mi_bridge_per_letter :
        ∀ i : Fin n, (perLetterMI h_meas c i).toReal
          = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
            - InformationTheory.Shannon.differentialEntropy
                (ProbabilityTheory.gaussianReal 0 N)) :
    ∑ i : Fin n, (perLetterMI h_meas c i).toReal
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) := by
  -- Step 1: per-letter bound via `awgn_per_letter_mi_le_log_var` for each `i`.
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_per_letter_bound : ∀ i : Fin n, (perLetterMI h_meas c i).toReal
      ≤ (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) := by
    intro i
    exact awgn_per_letter_mi_le_log_var P hP N hN h_meas c
      h_mi_bridge_per_letter i
  -- Step 2: sum the per-letter bound.
  have h_sum_le_sum :
      (∑ i : Fin n, (perLetterMI h_meas c i).toReal)
        ≤ ∑ i : Fin n, (1 / 2) * Real.log (1 + perLetterInputSecondMoment c i / (N : ℝ)) :=
    Finset.sum_le_sum (fun i _ ↦ h_per_letter_bound i)
  -- Step 3: non-negativity of `perLetterInputSecondMoment c i` (squares are ≥ 0).
  have h_nn : ∀ i : Fin n, 0 ≤ perLetterInputSecondMoment c i := by
    intro i
    unfold perLetterInputSecondMoment
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intros m _
      positivity
  -- Step 4: Jensen / concavity bound (C-1c) yields
  --   `∑ᵢ (1/2) log(1 + xᵢ/N) ≤ n · (1/2) log(1 + (∑ᵢ xᵢ / n) / N)`.
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    refine lt_of_le_of_ne N.coe_nonneg ?_
    exact (Ne.symm hN)
  have h_jensen := sum_log_one_add_le_n_log_one_add_avg (n := n) hn_pos
    (N : ℝ) hN_pos (fun i ↦ perLetterInputSecondMoment c i) h_nn
  -- Step 5: monotonicity of `log` to push down `avg ≤ P` (C-1a) into the RHS.
  -- `avg := (1/n) ∑ᵢ perLetterInputSecondMoment c i ≤ P` (awgn_per_letter_input_power_avg).
  have h_avg_le : (1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i ≤ P :=
    awgn_per_letter_input_power_avg hM_pos hn_pos c
  -- `1 + avg / N ≤ 1 + P / N`.
  have h_one_add_mono :
      1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ)
        ≤ 1 + P / (N : ℝ) := by
    have : ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ)
        ≤ P / (N : ℝ) := by
      apply div_le_div_of_nonneg_right h_avg_le hN_pos.le
    linarith
  -- `log` monotone on positives.
  have h_pos_avg :
      0 < 1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ) := by
    have h_avg_nn :
        (0 : ℝ) ≤ (1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i := by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun i _ ↦ h_nn i)
    have : (0 : ℝ) ≤ ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ) := by
      exact div_nonneg h_avg_nn hN_pos.le
    linarith
  have h_log_mono :
      Real.log
          (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ))
        ≤ Real.log (1 + P / (N : ℝ)) :=
    Real.log_le_log h_pos_avg h_one_add_mono
  -- Multiply by `n · (1/2) > 0` and chain.
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have h_jensen_chained :
      (n : ℝ) * ((1 / 2) * Real.log
          (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ)))
        ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) := by
    have h_scaled : (1 / 2) * Real.log
          (1 + ((1 / (n : ℝ)) * ∑ i : Fin n, perLetterInputSecondMoment c i) / (N : ℝ))
        ≤ (1 / 2) * Real.log (1 + P / (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h_log_mono
      norm_num
    apply mul_le_mul_of_nonneg_left h_scaled
    exact le_of_lt hn_real
  -- Chain: sum ≤ ∑ log ≤ n · log_avg ≤ n · log_P.
  exact h_sum_le_sum.trans (h_jensen.trans h_jensen_chained)

/-! ## Converse assembly -/

/-- Converse discharger: the assembled chain
```
log M ≤ I(W; Yⁿ).toReal + binEntropy(Pe) + Pe·log(M − 1)     (Fano)
      ≤ I(Xⁿ; Yⁿ).toReal + binEntropy(Pe) + Pe·log(M − 1)    (data-processing)
      ≤ ∑ I(Xᵢ; Yᵢ).toReal + binEntropy(Pe) + Pe·log(M − 1)  (chain rule)
      ≤ n · (1/2) log(1 + P/N) + binEntropy(Pe) + Pe·log(M − 1)  (capacity bound)
```
The bridge `h_mi_bridge_per_letter` (per-letter `I(Xᵢ; Yᵢ) = h(Yᵢ) − h(Z)`) is taken as a
hypothesis and discharged elsewhere. -/
@[entry_point]
theorem isAwgnConverseFeasible_discharger
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - InformationTheory.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} [NeZero M] (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  have hN_nnreal : N ≠ 0 := by intro h; exact hN (by rw [h]; norm_num)
  -- Fano: `log M ≤ I(W; Y^n).toReal + binEntropy(Pe) + Pe · log(M-1)`.
  have h_fano := awgn_converse_single_shot_call P N hN_nnreal h_meas hM c Pe hPe
  -- Data-processing: `I(W; Y^n).toReal ≤ I(X^n; Y^n).toReal` (Markov factorization).
  have h_dpi := awgn_dpi P N hN_nnreal h_meas c
  -- Chain rule: `I(X^n; Y^n).toReal ≤ ∑ᵢ I(X_i; Y_i).toReal`.
  have h_chain_le := awgn_chain_rule P N hN_nnreal h_meas c
  -- Capacity bound: `∑ᵢ I(X_i; Y_i).toReal ≤ n · (1/2) log(1+P/N)`.
  have h_sum := awgn_sum_per_letter_mi_le_n_capacity P hP N hN h_meas hn_pos c
    (h_mi_bridge_per_letter (M := M) (n := n) hM c)
  -- Assemble: transitive `≤` chain on the first summand.
  have h_lhs_chain : (jointMIWYn h_meas c).toReal
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) :=
    (h_dpi.trans h_chain_le).trans h_sum
  -- Add `binEntropy(Pe) + Pe · log(M-1)` (constants on both sides).
  linarith [h_fano, h_lhs_chain]

/-- Thin wrapper over `isAwgnConverseFeasible_discharger`: derives the `NeZero M` instance
from `2 ≤ M` and delegates. The bridge `h_mi_bridge_per_letter` is taken as a hypothesis. -/
@[entry_point]
theorem awgn_converse_F3_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - InformationTheory.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  haveI : NeZero M := ⟨by omega⟩
  exact isAwgnConverseFeasible_discharger P hP N hN h_meas
    h_mi_bridge_per_letter hM hn_pos c Pe hPe


end InformationTheory.Shannon.AWGN
