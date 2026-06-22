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

/-! # Converse-side per-letter log-density integrability -/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Converse-side shared lemmas

The converse-side analytic facts: per-letter log-density integrability, the memoryless
MI chain rule, and the deterministic-encoder Markov factorization.

The old predicate bodies referenced `awgnConverseJoint` / `perLetterYLaw` / `perLetterMI`
/ `jointMIXnYn`, all defined in `ConverseMutualInfoFiniteness.lean`. Referencing those named defs
from this file directly would create the import cycle
`ConverseMIChainRule → ConverseMutualInfoFiniteness → ConverseMIChainRule`, so the body of
`awgnConverseJoint` is inlined here as
the private mirror def `converseJointInline`. The two defs share the same RHS, so they are
definitionally equal: on the consumer side `unfold awgnConverseJoint perLetterYLaw …`
reduces the goal to the inline form here, where the shared lemmas apply. -/

/-- Mirror of the `awgnConverseJoint` body, inlined here to break the would-be import
cycle. Defeq to `awgnConverseJoint h_meas c` (both `def`s share the same RHS, so
consumer-side `unfold awgnConverseJoint` reduces to this form). -/
noncomputable def converseJointInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) •
    ∑ m : Fin M,
      (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i)))

/-- `converseJointInline` is a probability measure for `M ≥ 1` (mixture with weights
`1/M` summing to 1). Mirror of `awgnConverseJoint.instIsProbabilityMeasure`
(`ConverseMutualInfoFiniteness.lean:74`); needed so `IsMarkovChain`'s `[IsFiniteMeasure μ]`
prerequisite resolves on the inlined joint. -/
instance converseJointInline.instIsProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (converseJointInline h_meas c) := by
  refine ⟨?_⟩
  unfold converseJointInline
  rw [Measure.smul_apply, Measure.finsetSum_apply _ _ Set.univ]
  have h_summand : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n ↦ awgnChannel N h_meas (c.encoder m i))))
            Set.univ = 1 := fun _ ↦ measure_univ
  simp only [h_summand, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

/-! ### Per-letter log-density integrability

The goal is a 1-dimensional integrability against `volume` on `ℝ`. The per-letter output
law `Y_i` is a finite mixture of shifted 1-D Gaussians `(1/M) ∑ₘ 𝒩(encoder m i, N)`, so
its `rnDeriv volume` is the finite Gaussian-mixture density
`(1/M) ∑ₘ gaussianPDF (encoder m i) N`. `negMulLog` of that density is dominated by a
Gaussian moment integrand — pure 1-D measure-theoretic domination. The proof mirrors the
continuous-input analogue `AwgnCapacityConverseMaxent.outputDistribution_logDensity_integrable`
(not importable here, due to the import cycle), but is simpler: the finite mixture needs no
Chebyshev concentration (the lower bound comes from a single component). -/

/-- The finite per-letter Gaussian-mixture density at coordinate `i`:
`(1/M) ∑ₘ gaussianPDF (encoder m i) N y` (`ℝ≥0∞`-valued). For `M ≥ 1` and `N ≠ 0` this is
the `rnDeriv volume` of the per-letter output law `(converseJointInline h_meas c).map (·.2 i)`. -/
noncomputable def perLetterMixtureDensity
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (y : ℝ) : ℝ≥0∞ :=
  ((M : ℝ≥0∞))⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y

lemma perLetterMixtureDensity_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    Measurable (perLetterMixtureDensity N c i) := by
  unfold perLetterMixtureDensity
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ (fun m _ ↦ measurable_gaussianPDF (c.encoder m i) N)

/-- The per-letter output law equals the explicit finite Gaussian mixture
`(1/M) • ∑ₘ 𝒩(encoder m i, N)` (the decisive atom: pushforward of the inlined joint
mixture-of-diracs⊗pi through `ω ↦ ω.2 i`, marginalizing the `pi` to its `i`-th factor). -/
private lemma perLetterLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω ↦ ω.2 i)
      = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  have hf_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  unfold converseJointInline
  rw [Measure.map_smul, Measure.map_finset_sum hf_meas.aemeasurable]
  simp only [Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl (fun m _ ↦ ?_)
  -- `((dirac m).prod (pi μ_m)).map (·.2 i) = gaussianReal (encoder m i) N`
  -- via `map ((eval i) ∘ snd) = (map snd).map (eval i)`.
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) ↦ ω.2 i)
      = (Function.eval i) ∘ (Prod.snd : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) := rfl
  rw [h_comp, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul,
    Measure.pi_map_eval]
  -- `∏ j ∈ erase i, (awgnChannel N (encoder m j)) univ = 1` (each fibre is a prob measure)
  have h_prod_one : (∏ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
    refine Finset.prod_eq_one (fun j _ ↦ ?_)
    rw [awgnChannel_apply]; exact measure_univ
  rw [h_prod_one, one_smul, awgnChannel_apply]

/-- For `M ≥ 1` and `N ≠ 0`, the per-letter output law is
`volume.withDensity (perLetterMixtureDensity c i)`. -/
lemma perLetterLaw_withDensity
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    (converseJointInline h_meas c).map (fun ω ↦ ω.2 i)
      = volume.withDensity (perLetterMixtureDensity N c i) := by
  classical
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- Each component: `gaussianReal μ N = volume.withDensity (gaussianPDF μ N)`.
  have h_comp : ∀ m : Fin M,
      gaussianReal (c.encoder m i) N
        = volume.withDensity (gaussianPDF (c.encoder m i) N) :=
    fun m ↦ gaussianReal_of_var_ne_zero (c.encoder m i) hN
  -- Sum of withDensity = withDensity of sum (finset induction).
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, gaussianReal (c.encoder m i) N)
        = volume.withDensity (∑ m ∈ s, gaussianPDF (c.encoder m i) N) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [withDensity_zero]
    | insert m s hms ih =>
        rw [Finset.sum_insert hms, Finset.sum_insert hms, ih, h_comp m,
          withDensity_add_left (measurable_gaussianPDF _ _)]
  rw [h_sum Finset.univ]
  -- `M⁻¹ • volume.withDensity g = volume.withDensity (M⁻¹ • g)`.
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hM)
  rw [← withDensity_smul' _ _ hM_ne_top]
  -- `M⁻¹ • (∑ₘ gaussianPDF ...) = perLetterMixtureDensity N c i` (pointwise = M⁻¹ * ∑).
  congr 1
  funext y
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, perLetterMixtureDensity]

/-- The mixture density is bounded above by `(√(2πN))⁻¹` (each component is, and the
weights `1/M` sum to ≤ 1). -/
lemma perLetterMixtureDensity_le_sup
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (y : ℝ) :
    perLetterMixtureDensity N c i y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  -- each Gaussian component pdf is `≤ ofReal (√(2πN))⁻¹`
  have h_comp : ∀ m : Fin M,
      gaussianPDF (c.encoder m i) N y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
    intro m
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    -- `gaussianPDFReal μ N y ≤ (√(2πN))⁻¹` (exp factor ≤ 1)
    rw [gaussianPDFReal]
    have h_const_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ := by positivity
    have h_exp_le_one : Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one h_const_nonneg
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  unfold perLetterMixtureDensity
  -- `M⁻¹ * ∑ₘ (≤ B) ≤ M⁻¹ * (M • B) = M⁻¹ * (M * B) = B`
  calc (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ _m : Fin M, ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        gcongr with m _
        exact h_comp m
    _ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hM))
          (ENNReal.natCast_ne_top M), one_mul]

/-- Lower bound on `log` of the mixture density (no Chebyshev needed — a single component
suffices): there are `c₀ c₁` with `|log (f y).toReal| ≤ c₀ + c₁ y²`. -/
lemma perLetterMixtureDensity_log_abs_le
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ y : ℝ,
      |Real.log ((perLetterMixtureDensity N c i y).toReal)| ≤ c₀ + c₁ * y ^ 2 := by
  classical
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (fun h ↦ hN (by exact_mod_cast h.symm))
  set sup : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hsup_def
  have hsup_nonneg : 0 ≤ sup := by rw [hsup_def]; positivity
  -- a fixed representative message `m₀`
  set m₀ : Fin M := ⟨0, hM⟩ with hm₀_def
  set μ₀ : ℝ := c.encoder m₀ i with hμ₀_def
  -- The mixture density never exceeds `sup` (real form via `le_sup`).
  have h_up_real : ∀ y, (perLetterMixtureDensity N c i y).toReal ≤ sup := by
    intro y
    have h := perLetterMixtureDensity_le_sup N c i hM y
    rw [← hsup_def] at h
    calc (perLetterMixtureDensity N c i y).toReal
        ≤ (ENNReal.ofReal sup).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = sup := ENNReal.toReal_ofReal hsup_nonneg
  -- upper bound on `log f(y)`: `≤ max (log sup) 0`.
  have h_up : ∀ y, Real.log ((perLetterMixtureDensity N c i y).toReal) ≤ max (Real.log sup) 0 := by
    intro y
    rcases le_or_gt (perLetterMixtureDensity N c i y).toReal 0 with h0 | h0
    · have : (perLetterMixtureDensity N c i y).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
      rw [this, Real.log_zero]; exact le_max_right _ _
    · exact le_trans (Real.log_le_log h0 (h_up_real y)) (le_max_left _ _)
  -- single-component lower bound: `f(y).toReal ≥ M⁻¹ * gaussianPDFReal μ₀ N y`.
  have h_low_real : ∀ y, ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
      ≤ (perLetterMixtureDensity N c i y).toReal := by
    intro y
    -- `f y = M⁻¹ * ∑ₘ ofReal (gaussianPDFReal · ) ≥ M⁻¹ * ofReal (gaussianPDFReal μ₀)`
    have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM y)
    have h_ge : ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ perLetterMixtureDensity N c i y := by
      unfold perLetterMixtureDensity
      rw [ENNReal.ofReal_mul (by positivity)]
      have h_inv : ENNReal.ofReal ((M : ℝ)⁻¹) = (M : ℝ≥0∞)⁻¹ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hM)]
      rw [h_inv]
      gcongr
      -- `ofReal (gaussianPDFReal μ₀ N y) = gaussianPDF μ₀ N y ≤ ∑ₘ gaussianPDF · `
      rw [← gaussianPDF]
      exact Finset.single_le_sum (f := fun m ↦ gaussianPDF (c.encoder m i) N y)
        (fun m _ ↦ zero_le') (Finset.mem_univ m₀)
    calc ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
        = (ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)).toReal := by
          rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (gaussianPDFReal_nonneg μ₀ N y))]
      _ ≤ (perLetterMixtureDensity N c i y).toReal := ENNReal.toReal_mono h_ne_top h_ge
  -- lower bound on `log f(y)`: `-log f(y) ≤ (1/N) y² + b` from the single-component bound.
  -- `M⁻¹ · gaussianPDFReal μ₀ N y = M⁻¹ · sup · exp(-(y-μ₀)²/(2N))`, so
  -- `-log(M⁻¹ gaussianPDFReal) = log M - log sup + (y-μ₀)²/(2N) ≤ a y² + b`.
  have hgpos : ∀ y, 0 < gaussianPDFReal μ₀ N y := fun y ↦ gaussianPDFReal_pos μ₀ N y hN
  set bLow : ℝ := Real.log M - Real.log sup + μ₀ ^ 2 / (N : ℝ) with hbLow_def
  refine ⟨max (Real.log sup) 0 + max bLow 0, 1 / (N : ℝ), by positivity, fun y ↦ ?_⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-(c₀ + c₁ y²) ≤ log f(y)`: use single-component lower bound + log algebra.
    have h_low := h_low_real y
    have hlow_pos : 0 < (M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y :=
      mul_pos (by positivity) (hgpos y)
    have h_log_low : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ Real.log ((perLetterMixtureDensity N c i y).toReal) :=
      Real.log_le_log hlow_pos h_low
    -- compute `log (M⁻¹ gaussianPDFReal μ₀ N y)`
    have h_log_eq : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        = -Real.log M + (Real.log sup - (y - μ₀) ^ 2 / (2 * N)) := by
      rw [Real.log_mul (by positivity) (hgpos y).ne', Real.log_inv, gaussianPDFReal,
        Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, ← hsup_def, neg_div]
      ring
    rw [h_log_eq] at h_log_low
    -- `(y-μ₀)²/(2N) ≤ (y²+μ₀²)/N` (cleared division)
    have h_quad : (y - μ₀) ^ 2 / (2 * (N : ℝ)) ≤ (y ^ 2 + μ₀ ^ 2) / (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hN_pos]
      nlinarith [sq_nonneg (y + μ₀), hN_pos]
    have h_split : (y ^ 2 + μ₀ ^ 2) / (N : ℝ) = y ^ 2 / (N : ℝ) + μ₀ ^ 2 / (N : ℝ) := by
      rw [add_div]
    have h_max1 : (0 : ℝ) ≤ max (Real.log sup) 0 := le_max_right _ _
    have h_max2 : bLow ≤ max bLow 0 := le_max_left _ _
    have h_c1 : 1 / (N : ℝ) * y ^ 2 = y ^ 2 / (N : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
    rw [h_c1]
    -- unfold `bLow` so linarith sees the same atom `μ₀²/N`
    simp only [hbLow_def] at *
    linarith [h_log_low, h_quad, h_split, h_max1, h_max2]
  · -- `log f(y) ≤ c₀ + c₁ y²`: from the upper bound.
    have h := h_up y
    have h_sq : (0 : ℝ) ≤ 1 / (N : ℝ) * y ^ 2 := by positivity
    have h_max2 : (0 : ℝ) ≤ max bLow 0 := le_max_right _ _
    linarith [h, h_sq, h_max2]

/-- `y²` is integrable against the per-letter output law (finite mixture of Gaussians,
each with finite second moment). -/
lemma perLetterLaw_sq_integrable
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    Integrable (fun y : ℝ ↦ y ^ 2)
      ((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)) := by
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- each component Gaussian has integrable `y²`
  have h_comp : ∀ m : Fin M, Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal (c.encoder m i) N) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
    simpa using h
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
    exact Nat.pos_iff_ne_zero.mp hM
  refine Integrable.smul_measure ?_ hM_ne_top
  exact integrable_finsetSum_measure.mpr (fun m _ ↦ h_comp m)

/-- Per-letter `Y_i` log-density integrability.

For every coordinate `i`, the per-letter output law `Y_i` (here the pushforward of the
inlined joint along `ω ↦ ω.2 i`) has Lebesgue-integrable `negMulLog (rnDeriv · vol)`.
Consumer-side `unfold perLetterYLaw awgnConverseJoint` reduces `perLetterYLaw h_meas c i`
to `(converseJointInline h_meas c).map (fun ω => ω.2 i)` (defeq).

The per-letter law is a finite Gaussian mixture; `negMulLog` of its `rnDeriv` is
dominated by a Gaussian-moment integrand (`perLetterMixtureDensity_log_abs_le` +
`perLetterLaw_sq_integrable`). The degenerate `M = 0` / `N = 0` cases give a singular
law (`rnDeriv = 0` a.e., `negMulLog 0 = 0`, constant, integrable), so the boundary is
discharged by a genuine singular-law argument rather than a vacuity exploit.
@audit:ok -/
@[entry_point]
theorem awgnPerLetterIntegrability_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    ∀ i : Fin n,
      MeasureTheory.Integrable (fun y : ℝ ↦
          Real.negMulLog
            (((converseJointInline h_meas c).map (fun ω ↦ ω.2 i)).rnDeriv
                MeasureTheory.volume y).toReal)
        MeasureTheory.volume := by
  classical
  intro i
  set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω ↦ ω.2 i) with hν_def
  -- Degenerate cases (`M = 0` or `N = 0`): `ν ⟂ volume`, so `rnDeriv =ᵐ 0` and the
  -- integrand is a.e. `negMulLog 0 = 0`, hence integrable.
  by_cases hMN : 0 < M ∧ N ≠ 0
  · obtain ⟨hM, hN⟩ := hMN
    haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩
    -- `ν` is a probability measure (pushforward of the probability mixture)
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν_def]
      exact Measure.isProbabilityMeasure_map
        ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    -- main case: `ν = volume.withDensity f`, `f := perLetterMixtureDensity N c i`.
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν_def, hf_def]; exact perLetterLaw_withDensity h_meas c i hM hN
    -- `ν.rnDeriv volume =ᵐ[volume] f`
    have h_rn_ae : ν.rnDeriv volume =ᵐ[volume] f := by
      rw [hν_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
    -- `f y < ∞` a.e. (bounded above)
    have hf_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), f y < ∞ :=
      Filter.Eventually.of_forall (fun y ↦
        lt_of_le_of_lt (perLetterMixtureDensity_le_sup N c i hM y) ENNReal.ofReal_lt_top)
    -- quadratic abs bound on `log f`
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM hN
    -- `c₀ + c₁ y²` integrable against ν, transport to `(f y).toReal • (c₀+c₁y²)` on volume
    have h_dom_ν : Integrable (fun y : ℝ ↦ c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add ((perLetterLaw_sq_integrable h_meas c i hM hN).const_mul c₁)
    have h_dom_vol : Integrable (fun y : ℝ ↦ (f y).toReal • (c₀ + c₁ * y ^ 2)) volume :=
      (integrable_withDensity_iff_integrable_smul' hf_meas hf_lt_top).mp
        (by rw [← hν_wd]; exact h_dom_ν)
    -- dominate `negMulLog (rnDeriv)` by `(f y).toReal · (c₀ + c₁ y²)`
    refine Integrable.mono' h_dom_vol ?_ ?_
    · have h_rn_meas : Measurable (fun y ↦ (ν.rnDeriv volume y).toReal) :=
        (Measure.measurable_rnDeriv ν volume).ennreal_toReal
      exact (Real.continuous_negMulLog.measurable.comp h_rn_meas).aestronglyMeasurable
    · filter_upwards [h_rn_ae] with y hy
      rw [hy, smul_eq_mul, Real.norm_eq_abs]
      set t : ℝ := (f y).toReal with ht_def
      have ht_nonneg : 0 ≤ t := ENNReal.toReal_nonneg
      rw [Real.negMulLog_def, abs_mul, abs_neg, abs_of_nonneg ht_nonneg]
      exact mul_le_mul_of_nonneg_left (h_abs y) ht_nonneg
  · -- degenerate: `ν ⟂ volume`, so `rnDeriv =ᵐ 0`; integrand a.e. `0`.
    have h_rn_zero : ν.rnDeriv volume =ᵐ[volume] 0 := by
      rcases not_and_or.mp hMN with hM0 | hN0
      · -- `M = 0`: `ν = 0` measure
        have hM_eq : M = 0 := Nat.le_zero.mp (Nat.not_lt.mp hM0)
        have hν_zero : ν = 0 := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hM_eq
          simp
        rw [hν_zero]; exact Measure.rnDeriv_zero volume
      · -- `N = 0`: `ν` is a finite sum of Diracs, mutually singular with volume
        have hN_eq : N = 0 := not_not.mp hN0
        have hν_dirac : ν = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hN_eq
          simp only [gaussianReal_zero_var]
        have h_sum_sing : ∀ s : Finset (Fin M),
            (∑ m ∈ s, Measure.dirac (c.encoder m i)) ⟂ₘ (volume : Measure ℝ) := by
          intro s
          induction s using Finset.induction with
          | empty => simp [Measure.MutuallySingular.zero_left]
          | insert m s hms ih =>
              rw [Finset.sum_insert hms]
              exact (mutuallySingular_dirac (c.encoder m i) volume).add_left ih
        have h_sing : ν ⟂ₘ volume := by
          rw [hν_dirac]
          exact (h_sum_sing Finset.univ).smul _
        exact h_sing.rnDeriv_ae_eq_zero
    -- integrand a.e. equals `negMulLog 0 = 0`
    refine (integrable_zero ℝ ℝ volume).congr ?_
    filter_upwards [h_rn_zero] with y hy
    rw [hy]; simp

end InformationTheory.Shannon.AWGN
