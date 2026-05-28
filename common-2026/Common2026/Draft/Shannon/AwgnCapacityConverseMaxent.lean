import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.LConvolution
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNBindConvBody
import Common2026.Draft.Shannon.ContChannelMIDecomp

/-!
# AWGN single-letter capacity converse (Gaussian max-entropy wall)

[awgn-capacity-converse-maxent-plan.md](../../../docs/shannon/awgn-capacity-converse-maxent-plan.md).

Discharges the single-letter capacity converse `h_max_ent` of
`ContChannelMIDecomp.awgn_capacity_closed_form_of_out` (`:692`): for any input law
`p : Measure ℝ` with second moment `≤ P`,
`(mutualInfoOfChannel p (awgnChannel N)).toReal ≤ (1/2) log(1 + P/N)`.

## Approach (Cover-Thomas 9.1 converse)

`I(X;Y) = h(Y) − h(Y|X)` (in-tree chain rule
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`) combined with the Gaussian
max-entropy bound `differentialEntropy_le_gaussian_of_variance_le`:

1. `MI = h(Y) − h(Y|X)` (chain rule, proxy form, 9 args).
2. `h(Y|X) = ∫ h(𝒩(x,N)) dp = (1/2) log(2πeN)` (fibre entropy constant).
3. `h(Y) ≤ (1/2) log(2πe·Var(Y))` (max-entropy, `m := E[Y]`).
4. `Var(Y) ≤ E[X²] + N ≤ P + N`.
5. arithmetic `(1/2)log(2πe(P+N)) − (1/2)log(2πeN) = (1/2)log(1+P/N)`.

The output law is `q := outputDistribution p W = p ∗ 𝒩(0,N)` (Phase 2). The dominant
Mathlib gap is the mixture-output log-density integrability (`h_int_out` / `h_ent_int`),
which is isolated in `outputDistribution_logDensity_integrable` (Phase 6, hard).

## Residual status

Phases 1–5 are genuinely discharged. Phase 6
(`outputDistribution_logDensity_integrable`, the dominant analytic wall) and Phase 7
(final assembly `awgn_per_input_mi_le_log`) are stubs marked
`@residual(wall:awgn-capacity-converse-maxent)`, scheduled for a follow-up dispatch.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

variable {P : ℝ} {N : ℝ≥0}

/-! ## Phase 1 — Gaussian pdf sup upper bound -/

/-- (#5) Gaussian pdf sup upper bound `gaussianPDFReal m v y ≤ (√(2πv))⁻¹`.
The exponential factor `rexp (-(y-m)²/(2v))` is `≤ 1` (nonpositive exponent), so the
pdf is bounded above by its normalization constant. Material for Phase 6a (upper
bound `log f_q ≤ const`). -/
theorem gaussianPDFReal_le_sup (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal m v y ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal]
  have h_const_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  have h_exp_le_one : Real.exp (-(y - m) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (y - m) ^ 2 / (2 * (v : ℝ)) := by positivity
    rw [neg_div]
    linarith
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(y - m) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h_exp_le_one h_const_nonneg
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-! ## Phase 2 — output law is the noise convolution -/

/-- (#1) For any SFinite input `p`, the AWGN output is the convolution with the noise
law: `outputDistribution p (awgnChannel N h_meas) = p ∗ gaussianReal 0 N`.
Via `outputDistribution = (p⊗ₘW).snd = W ∘ₘ p` (`snd_compProd`) and the in-tree
translation-kernel ↔ convolution bridge `bind_eq_conv_of_translation_kernel`. -/
theorem outputDistribution_awgn_eq_conv
    (h_meas : IsAwgnChannelMeasurable N) (p : Measure ℝ) [SFinite p] :
    ChannelCoding.outputDistribution p (awgnChannel N h_meas)
      = p ∗ gaussianReal 0 N := by
  -- `outputDistribution = (p ⊗ₘ W).snd = W ∘ₘ p`
  show ((p ⊗ₘ (awgnChannel N h_meas)).snd) = p ∗ gaussianReal 0 N
  rw [Measure.snd_compProd p (awgnChannel N h_meas)]
  -- `W ∘ₘ p = p ∗ 𝒩(0,N)` via the translation-kernel bridge
  refine bind_eq_conv_of_translation_kernel
    (awgnChannel N h_meas) p (gaussianReal 0 N) ?_
  intro x
  rw [awgnChannel_apply]
  exact gaussianReal_eq_map_const_add N x

/-! ## Phase 3 — log algebra -/

/-- (#6) The capacity log-algebra step:
`(1/2)log(2πe(P+N)) − (1/2)log(2πeN) = (1/2)log(1+P/N)`.
Follows the in-tree `mutualInfoOfChannel_gaussianInput_closed_form` algebra
(`AWGN.lean:176-191`). -/
theorem capacity_log_diff (hP : 0 < P) (hN : (N : ℝ) ≠ 0) :
    (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (P + (N : ℝ)))
        - (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (Ne.symm hN)
  have hPN_pos : (0 : ℝ) < P + (N : ℝ) := by linarith
  have h_num : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (P + (N : ℝ)) := by positivity
  have h_den : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N : ℝ) := by positivity
  rw [← mul_sub, ← Real.log_div h_num.ne' h_den.ne']
  congr 1
  congr 1
  rw [show (2 * Real.pi * Real.exp 1 * (P + (N : ℝ))) / (2 * Real.pi * Real.exp 1 * (N : ℝ))
        = (P + (N : ℝ)) / (N : ℝ) by field_simp]
  field_simp
  ring

/-! ## Phase 4 — output second moment / variance bound -/

/-- Second moment of a shifted real Gaussian: `∫ z, (z − c)² ∂𝒩(0,N) = N + c²`.
From `Var[id; 𝒩(0,N)] = N`, `∫ z ∂𝒩(0,N) = 0` and the expansion
`(z−c)² = z² − 2cz + c²`. -/
theorem integral_sub_sq_gaussianReal (N : ℝ≥0) (hN : N ≠ 0) (c : ℝ) :
    ∫ z, (z - c) ^ 2 ∂(gaussianReal 0 N) = (N : ℝ) + c ^ 2 := by
  have h_id : Integrable (fun z : ℝ => z) (gaussianReal 0 N) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := N) 1).integrable (by norm_num)
    simpa using this
  have h_sq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 N) :=
    (memLp_id_gaussianReal (μ := 0) (v := N) 2).integrable_sq
  -- `∫ z² ∂𝒩(0,N) = Var[id] + (∫ z)² = N + 0`
  have h_var : ∫ z, z ^ 2 ∂(gaussianReal 0 N) = (N : ℝ) := by
    have hv : Var[fun z : ℝ => z; gaussianReal 0 N] = (N : ℝ) := variance_fun_id_gaussianReal
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
    simpa using hv
  -- expand `(z - c)² = z² - 2cz + c²` and integrate termwise
  have h_int1 : Integrable (fun z : ℝ => -(2 * c) * z) (gaussianReal 0 N) :=
    h_id.const_mul _
  calc ∫ z, (z - c) ^ 2 ∂(gaussianReal 0 N)
      = ∫ z, (z ^ 2 + (-(2 * c) * z + c ^ 2)) ∂(gaussianReal 0 N) := by
        refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
    _ = (∫ z, z ^ 2 ∂(gaussianReal 0 N))
          + ∫ z, (-(2 * c) * z + c ^ 2) ∂(gaussianReal 0 N) :=
        integral_add h_sq (h_int1.add (integrable_const _))
    _ = (∫ z, z ^ 2 ∂(gaussianReal 0 N))
          + ((∫ z, -(2 * c) * z ∂(gaussianReal 0 N)) + ∫ _z, c ^ 2 ∂(gaussianReal 0 N)) := by
        rw [integral_add h_int1 (integrable_const _)]
    _ = (N : ℝ) + c ^ 2 := by
        rw [h_var, integral_const_mul, integral_id_gaussianReal, integral_const]
        simp

/-- (#2, integrability piece) `(y − m)²` is integrable against the mixture output law
`p ∗ 𝒩(0,N)` (for any `m`). With the input second moment integrable (`hp_2mom_int`),
the output has finite second moment, so the quadratic is integrable. Supplies
`h_var_int` for the max-entropy lemma.

`hp_2mom_int : Integrable (fun x => x²) p` is a *regularity* precondition: the bare
constraint `∫ x² ∂p ≤ P` does not imply integrability (a non-integrable `x²` gives the
degenerate `∫ x² ∂p = 0 ≤ P`). -/
theorem output_sq_sub_integrable
    (h_meas : IsAwgnChannelMeasurable N) (hN : N ≠ 0)
    (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp_2mom_int : Integrable (fun x => x ^ 2) p) (m : ℝ) :
    Integrable (fun y => (y - m) ^ 2)
      (ChannelCoding.outputDistribution p (awgnChannel N h_meas)) := by
  rw [outputDistribution_awgn_eq_conv h_meas p]
  -- Use `integrable_conv_iff`: fibre integrability + outer integrability of fibre norm.
  refine (integrable_conv_iff (by fun_prop)).mpr ⟨?_, ?_⟩
  · -- fibre: `(x + z - m)²` integrable against `𝒩(0,N)`.
    refine ae_of_all _ (fun x => ?_)
    have : (fun z => (x + z - m) ^ 2) = (fun z => (z - (m - x)) ^ 2) := by
      funext z; ring_nf
    rw [this]
    exact integrable_sq_sub_gaussianReal (m - x) 0 N
  · -- outer: `∫ z, ‖(x + z - m)²‖ ∂𝒩` is integrable against `p`.
    -- `‖(x+z-m)²‖ = (x+z-m)²` and `∫ z, (x+z-m)² ∂𝒩 = (x-m)² + N` (Gaussian variance N).
    have h_eq : (fun x => ∫ z, ‖(x + z - m) ^ 2‖ ∂(gaussianReal 0 N))
        = fun x => (N : ℝ) + (m - x) ^ 2 := by
      funext x
      have hnorm : (fun z => ‖(x + z - m) ^ 2‖) = fun z => (z - (m - x)) ^ 2 := by
        funext z
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring
      rw [hnorm, integral_sub_sq_gaussianReal N hN (m - x)]
    rw [h_eq]
    -- `(N : ℝ) + (m - x)² = (N + m²) - 2mx + x²` integrable against `p`.
    have h_poly : (fun x => (N : ℝ) + (m - x) ^ 2)
        = fun x => x ^ 2 - (2 * m) * x + ((N : ℝ) + m ^ 2) := by funext x; ring
    rw [h_poly]
    -- `id` is integrable against the finite `p`: `‖x‖ ≤ 1 + x²`.
    have h_id : Integrable (fun x : ℝ => x) p := by
      refine ((integrable_const (1 : ℝ)).add hp_2mom_int).mono' (by fun_prop)
        (ae_of_all _ (fun x => ?_))
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rcases le_or_gt |x| 1 with h | h
      · nlinarith [sq_nonneg x]
      · nlinarith [sq_nonneg x, abs_nonneg x, sq_abs x]
    exact (hp_2mom_int.sub (h_id.const_mul (2 * m))).add (integrable_const _)

/-- Second moment of the mixture output: `∫ y² ∂(p ∗ 𝒩(0,N)) = ∫ x² ∂p + N`.
Via `integral_conv` (the output is `(p.prod 𝒩).map (·+·)`) and the fibre identity
`∫ z, (x + z)² ∂𝒩(0,N) = x² + N`. -/
theorem output_secondMoment_eq
    (h_meas : IsAwgnChannelMeasurable N) (hN : N ≠ 0)
    (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp_2mom_int : Integrable (fun x => x ^ 2) p) :
    ∫ y, y ^ 2 ∂(ChannelCoding.outputDistribution p (awgnChannel N h_meas))
      = (∫ x, x ^ 2 ∂p) + (N : ℝ) := by
  have h_int : Integrable (fun y => y ^ 2)
      (ChannelCoding.outputDistribution p (awgnChannel N h_meas)) := by
    have := output_sq_sub_integrable h_meas hN p hp_2mom_int 0
    simpa using this
  rw [outputDistribution_awgn_eq_conv h_meas p] at h_int ⊢
  rw [integral_conv h_int]
  -- fibre: `∫ z, (x + z)² ∂𝒩(0,N) = x² + N`
  have h_fibre : (fun x => ∫ z, (x + z) ^ 2 ∂(gaussianReal 0 N))
      = fun x => x ^ 2 + (N : ℝ) := by
    funext x
    have : (fun z => (x + z) ^ 2) = fun z => (z - (-x)) ^ 2 := by funext z; ring
    rw [this, integral_sub_sq_gaussianReal N hN (-x)]
    ring
  rw [h_fibre, integral_add hp_2mom_int (integrable_const _), integral_const]
  simp

/-- (#2, variance piece) The mixture output law `q = p ∗ 𝒩(0,N)` has variance at most
`P + N`: `Var(Y) ≤ E[Y²] = E[X²] + N ≤ P + N`. With `m := ∫ y ∂q` the true mean,
`∫ (y − m)² ∂q = Var(Y) ≤ P + N`. Supplies `h_var`.

`hp_2mom_int` is a regularity precondition (see `output_sq_sub_integrable`). -/
theorem output_variance_le
    (h_meas : IsAwgnChannelMeasurable N) (hN : N ≠ 0)
    (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp_2mom_int : Integrable (fun x => x ^ 2) p) (hp_2mom : ∫ x, x ^ 2 ∂p ≤ P) :
    ∫ y, (y - (∫ z, z ∂(ChannelCoding.outputDistribution p (awgnChannel N h_meas)))) ^ 2
        ∂(ChannelCoding.outputDistribution p (awgnChannel N h_meas))
      ≤ P + (N : ℝ) := by
  set q := ChannelCoding.outputDistribution p (awgnChannel N h_meas) with hq_def
  -- `∫ (y - E[Y])² ∂q = Var[id; q] ≤ q[id²] = ∫ y² ∂q`.
  have h_var_eq : ∫ y, (y - (∫ z, z ∂q)) ^ 2 ∂q = Var[fun y : ℝ => y; q] :=
    (variance_eq_integral measurable_id'.aemeasurable).symm
  have h_var_le : Var[fun y : ℝ => y; q] ≤ q[fun y : ℝ => y ^ 2] :=
    variance_le_expectation_sq measurable_id'.aestronglyMeasurable
  rw [h_var_eq]
  refine h_var_le.trans ?_
  -- `q[id²] = ∫ y² ∂q = ∫ x² ∂p + N ≤ P + N`.
  show ∫ y, y ^ 2 ∂q ≤ P + (N : ℝ)
  rw [hq_def, output_secondMoment_eq h_meas hN p hp_2mom_int]
  linarith

/-! ## Phase 5 — fibre absolute continuity w.r.t. output -/

/-- (#4) Each AWGN fibre is absolutely continuous w.r.t. the (mixture) output law:
`∀ x, awgnChannel N h_meas x ≪ outputDistribution p (awgnChannel N h_meas)`.
The output `q = p ∗ 𝒩(0,N)` is full-support (positive density everywhere) since
`𝒩(0,N) ≪ volume`, so each `𝒩(x,N) ≪ q`. The in-tree
`awgnChannel_apply_absolutelyContinuous_output` is Gaussian-input-only and not
reusable here. Supplies `hWx_q`. -/
theorem fibre_absolutelyContinuous_output_general
    (h_meas : IsAwgnChannelMeasurable N) (hN : N ≠ 0)
    (p : Measure ℝ) [IsProbabilityMeasure p] (x : ℝ) :
    (awgnChannel N h_meas) x
      ≪ ChannelCoding.outputDistribution p (awgnChannel N h_meas) := by
  rw [awgnChannel_apply, outputDistribution_awgn_eq_conv h_meas p]
  -- It suffices that `volume ≪ q`, then chain `𝒩(x,N) ≪ volume ≪ q`.
  refine (gaussianReal_absolutelyContinuous x hN).trans ?_
  -- `volume ≪ p ∗ 𝒩(0,N)`: if `q(s) = 0` then `volume(s) = 0`.
  refine Measure.AbsolutelyContinuous.mk (fun s hs h ↦ ?_)
  -- Expand `q(s) = ∫⁻ a, 𝒩(0,N)((-a + ·) ⁻¹' s) ∂p` and conclude each fibre is 0.
  rw [← lintegral_indicator_one hs, Measure.lintegral_conv (by measurability)] at h
  -- For `p`-a.e. `a`, the inner Gaussian integral vanishes.
  have h_inner_zero : ∀ᵐ a ∂p, ∫⁻ y, s.indicator 1 (a + y) ∂(gaussianReal 0 N) = 0 :=
    (lintegral_eq_zero_iff (by measurability)).mp h
  -- Pick any such `a` (p is a probability measure, so the ae set is nonempty).
  obtain ⟨a, ha⟩ := h_inner_zero.exists
  -- The inner vanishing means `𝒩(0,N)((a + ·) ⁻¹' s) = 0`, hence `volume(...) = 0`.
  have h_indic : (fun y => s.indicator (1 : ℝ → ℝ≥0∞) (a + y))
      = ((fun y => a + y) ⁻¹' s).indicator 1 := by
    ext y
    by_cases hy : a + y ∈ s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_preimage.mpr hy),
        Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (by simpa using hy)]
  rw [h_indic, lintegral_indicator_one (by apply MeasurableSet.preimage hs (by fun_prop))] at ha
  have h_gauss_pre : (gaussianReal 0 N) ((fun y => a + y) ⁻¹' s) = 0 := ha
  -- `volume ≪ 𝒩(0,N)`, so the preimage has volume 0; volume is translation invariant.
  have h_vol_pre : volume ((fun y => a + y) ⁻¹' s) = 0 :=
    (gaussianReal_absolutelyContinuous' 0 hN) h_gauss_pre
  rwa [← (measurePreserving_add_left volume a).measure_preimage hs.nullMeasurableSet]

/-- (fibre side, genuine) Proxy-form joint integrability of the AWGN fibre
log-density for an **arbitrary** probability-measure input `p`. The fibre log-density
in measurable-proxy form `fun z => Real.log (gaussianPDF z.1 N z.2).toReal` is
integrable against the joint `p ⊗ₘ awgnChannel N`. The integrand decomposes everywhere
as `c₀ + c₁·(z.2 − z.1)²`, and the `(z.2 − z.1)²` term is integrable against the joint
via `Measure.integrable_compProd_iff` (per-fibre integrability + constant L¹-norm `N`).
The proof never uses that `p` is Gaussian, only that it is a probability measure — so
it is the general-`p` counterpart of the in-tree
`ContChannelMIDecomp.integrable_log_proxy_fibre_compProd` (Gaussian-input only). Supplies
`h_int_fibre` for the chain rule with a general input. -/
theorem integrable_log_proxy_fibre_compProd_general
    (h_meas : IsAwgnChannelMeasurable N) (hN : N ≠ 0)
    (p : Measure ℝ) [IsProbabilityMeasure p] :
    Integrable
      (fun z : ℝ × ℝ => Real.log (gaussianPDF z.1 N z.2).toReal)
      (p ⊗ₘ (awgnChannel N h_meas)) := by
  set W := awgnChannel N h_meas with hW_def
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  have h_eq : (fun z : ℝ × ℝ => Real.log (gaussianPDF z.1 N z.2).toReal)
      = fun z => c₀ + c₁ * (z.2 - z.1) ^ 2 := by
    funext z
    rw [toReal_gaussianPDF, Common2026.Shannon.log_gaussianPDFReal_eq z.1 hN z.2, hc₀, hc₁]
    ring
  rw [h_eq]
  have h_sq : Integrable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W) := by
    have h_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W) :=
      ((measurable_snd.sub measurable_fst).pow_const 2).aestronglyMeasurable
    rw [Measure.integrable_compProd_iff h_aesm]
    refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
    · simpa only [hW_def, awgnChannel_apply] using integrable_sq_sub_gaussianReal x x N
    · have h_norm : (fun x => ∫ y, ‖(y - x) ^ 2‖ ∂(W x)) = fun _ => (N : ℝ) := by
        funext x
        have : (fun y => ‖(y - x) ^ 2‖) = fun y => (y - x) ^ 2 := by
          funext y; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [this, hW_def, awgnChannel_apply]
        exact integral_sq_sub_self_gaussianReal x N
      rw [h_norm]
      exact integrable_const _
  exact (integrable_const c₀).add (h_sq.const_mul c₁)

/-! ## Phase 6 — ★ mixture output log-density integrability (hard, dominant wall) -/

/-- (#3, ★ dominant wall, OUT OF SCOPE for this dispatch) the continuous mixture
output `q = p ∗ 𝒩(0,N)` has integrable log-density: `negMulLog ((q.rnDeriv vol ·).toReal)`
is `volume`-integrable. The output density is bounded above by `(√(2πN))⁻¹` and below
by `c·exp(−a·y²)`, so `|log f_q(y)| ≤ c₀ + c₁·y²`, integrable against the finite
second moment of `q`. This is the only true Mathlib gap (loogle: 0 matches).

The input `p` is constrained by membership in `awgnPowerConstraintSet P` (lintegral
second moment `≤ P`), which carries the genuine integrability of `x²` via
`awgnPowerConstraintSet_mem_iff_integrable` — exactly the regularity Phases 1–5 use.
This rules out the heavy-tailed inputs (Cauchy etc.) that would break the statement, so
the residual is now a genuine analytic wall (mixture-of-Gaussians log-density
integrability), not a false statement.

@residual(wall:awgn-capacity-converse-maxent) -/
theorem outputDistribution_logDensity_integrable
    (hP : 0 ≤ P) (h_meas : IsAwgnChannelMeasurable N) (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp : p ∈ awgnPowerConstraintSet P) :
    Integrable (fun y : ℝ =>
        Real.negMulLog
          ((ChannelCoding.outputDistribution p (awgnChannel N h_meas)).rnDeriv
            volume y).toReal)
      volume := by
  sorry  -- @residual(wall:awgn-capacity-converse-maxent)

/-- (#3, ★ dominant wall, joint form, OUT OF SCOPE for this dispatch) the chain-rule
`h_int_out`: `log ((q.rnDeriv vol ·).toReal) ∘ snd` is integrable against the joint
`p ⊗ₘ W`. Lift of `outputDistribution_logDensity_integrable` along the snd-marginal.

@residual(wall:awgn-capacity-converse-maxent) -/
theorem outputDistribution_logDensity_integrable_joint
    (hP : 0 ≤ P) (h_meas : IsAwgnChannelMeasurable N) (p : Measure ℝ) [IsProbabilityMeasure p]
    (hp : p ∈ awgnPowerConstraintSet P) :
    Integrable (fun z : ℝ × ℝ =>
        Real.log
          ((ChannelCoding.outputDistribution p (awgnChannel N h_meas)).rnDeriv
            volume z.2).toReal)
      (p ⊗ₘ (awgnChannel N h_meas)) := by
  sorry  -- @residual(wall:awgn-capacity-converse-maxent)

/-! ## Phase 7 — final assembly (OUT OF SCOPE for this dispatch) -/

/-- Final converse conclusion (supplies the `h_max_ent` of
`awgn_capacity_closed_form_of_out`). For any input law `p ∈ awgnPowerConstraintSet P`
(lintegral second moment `≤ P`),
`(mutualInfoOfChannel p (awgnChannel N)).toReal ≤ (1/2) log(1 + P/N)`.

OUT OF SCOPE for this dispatch (assembly of Phases 1–6).

The constraint is now membership in `awgnPowerConstraintSet P` (lintegral form), which
carries the genuine integrability of `x²` (`awgnPowerConstraintSet_mem_iff_integrable`),
ruling out the heavy-tailed inputs (Cauchy etc.) that made the old Bochner-only signature
false. The remaining `sorry` is therefore a genuine analytic wall — the assembly of
Phases 1–6, gated by the mixture-output log-density integrability
(`outputDistribution_logDensity_integrable`, loogle 0 matches), not a false statement.

The single remaining `sorry` is the output log-density integrability
(`outputDistribution_logDensity_integrable` / `_joint`, Phase 6), reached via the
ordinary lemma calls below — no load-bearing hypothesis is introduced.

@residual(wall:awgn-capacity-converse-maxent) -/
theorem awgn_per_input_mi_le_log
    (hP : 0 < P) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (p : Measure ℝ) [IsProbabilityMeasure p] (hp : p ∈ awgnPowerConstraintSet P) :
    (ChannelCoding.mutualInfoOfChannel p (awgnChannel N h_meas)).toReal
      ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
  classical
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (Ne.symm hN)
  have hN_NN : N ≠ 0 := fun h => hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h))
  -- regularity from membership: genuine `x²` integrability + Bochner second-moment bound
  obtain ⟨hp_2mom_int, hp_2mom⟩ := awgnPowerConstraintSet_mem_iff_integrable P hP.le p hp
  set W := awgnChannel N h_meas with hW_def
  set q := ChannelCoding.outputDistribution p W with hq_def
  -- output law is the noise convolution `q = p ∗ 𝒩(0,N)` (Phase 2)
  have hq_conv : q = p ∗ gaussianReal 0 N := by
    rw [hq_def, hW_def, outputDistribution_awgn_eq_conv h_meas p]
  -- `q` is a probability measure (convolution of two probability measures)
  have hq_prob : IsProbabilityMeasure q := by
    rw [hq_conv]; infer_instance
  -- `q ≪ volume` via convolution absolute continuity (★ general-p, NEW)
  have hq_vol : q ≪ volume := by
    rw [hq_conv]
    exact Measure.conv_absolutelyContinuous (gaussianReal_absolutelyContinuous 0 hN_NN)
  -- proxy `g := gaussianPDF` for the fibre volume-density (Route B)
  set g : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF z.1 N z.2 with hg_def
  have hg_meas : Measurable g := measurable_gaussianPDF_uncurry N
  -- per-fibre rnDeriv↔proxy bridge `(W x).rnDeriv vol =ᵐ[W x] g(x,·)`
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
    intro x
    rw [hW_def, awgnChannel_apply]
    exact (gaussianReal_absolutelyContinuous x hN_NN).ae_le (rnDeriv_gaussianReal x N)
  -- fibre-vs-output absolute continuity `hWx_q` (Phase 5)
  have hWx_q : ∀ x, W x ≪ q :=
    fun x => fibre_absolutelyContinuous_output_general h_meas hN_NN p x
  -- fibre ≪ volume (each fibre is a full-support Gaussian)
  have hW_ac : ∀ x, W x ≪ volume := by
    intro x; rw [hW_def, awgnChannel_apply]; exact gaussianReal_absolutelyContinuous x hN_NN
  -- joint absolute continuity `p ⊗ₘ W ≪ p.prod q` (★ general-p, in-tree手筋)
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod q := by
    rw [show p.prod q = p ⊗ₘ (Kernel.const ℝ q) from (Measure.compProd_const).symm]
    exact Measure.absolutelyContinuous_compProd_right_iff.mpr
      (Filter.Eventually.of_forall (fun x => by simpa only [Kernel.const_apply] using hWx_q x))
  -- fibre log-density joint integrability `h_int_fibre` (proxy form, in-tree)
  have h_int_fibre :
      Integrable (fun z : ℝ × ℝ => Real.log (g z).toReal) (p ⊗ₘ W) :=
    integrable_log_proxy_fibre_compProd_general h_meas hN_NN p
  -- ★ output log-density joint integrability `h_int_out` (Phase 6 stub, joint form)
  have h_int_out :
      Integrable (fun z : ℝ × ℝ =>
          Real.log (q.rnDeriv volume z.2).toReal) (p ⊗ₘ W) :=
    outputDistribution_logDensity_integrable_joint hP.le h_meas p hp
  -- STEP 1: chain rule `MI.toReal = h(q) − ∫ h(W x) ∂p`
  have h_chain :
      (ChannelCoding.mutualInfoOfChannel p W).toReal
        = Common2026.Shannon.differentialEntropy q
          - ∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p :=
    ChannelCoding.mutualInfoOfChannel_toReal_eq_diffEntropy_sub
      hW_ac hWx_q hq_vol h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out
  -- STEP 2: fibre entropy is the constant `(1/2) log(2πeN)`
  have h_fibre_ent :
      ∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p
        = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) := by
    have h_const : (fun x => Common2026.Shannon.differentialEntropy (W x))
        = fun _ => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) := by
      funext x
      rw [hW_def, awgnChannel_apply, Common2026.Shannon.differentialEntropy_gaussianReal x hN_NN]
    rw [h_const, integral_const, probReal_univ]
    simp
  -- STEP 3: max-entropy bound on `h(q)` with `m := ∫ y ∂q`, `v := (P+N).toNNReal`
  set m : ℝ := ∫ y, y ∂q with hm_def
  set v : ℝ≥0 := (P + (N : ℝ)).toNNReal with hv_def
  have hPN_pos : (0 : ℝ) < P + (N : ℝ) := by positivity
  have hv_ne : v ≠ 0 := by
    rw [hv_def]; exact (Real.toNNReal_pos.mpr hPN_pos).ne'
  have hv_coe : (v : ℝ) = P + (N : ℝ) := by rw [hv_def, Real.coe_toNNReal _ hPN_pos.le]
  have h_var_int : Integrable (fun y => (y - m) ^ 2) q := by
    rw [hq_def]; exact output_sq_sub_integrable h_meas hN_NN p hp_2mom_int m
  have h_var : ∫ y, (y - m) ^ 2 ∂q ≤ (v : ℝ) := by
    rw [hv_coe, hm_def, hq_def]
    exact output_variance_le h_meas hN_NN p hp_2mom_int hp_2mom
  -- ★ output log-density volume-integrability `h_ent_int` (Phase 6 stub, volume form)
  have h_ent_int :
      Integrable (fun y => Real.negMulLog ((q.rnDeriv volume y).toReal)) volume := by
    rw [hq_def]; exact outputDistribution_logDensity_integrable hP.le h_meas p hp
  have h_maxent :
      Common2026.Shannon.differentialEntropy q
        ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) :=
    Common2026.Shannon.differentialEntropy_le_gaussian_of_variance_le
      hq_vol m hv_ne rfl h_var h_var_int h_ent_int
  -- STEP 4+5: assemble `MI ≤ (1/2)log(2πe(P+N)) − (1/2)log(2πeN) = (1/2)log(1+P/N)`.
  rw [h_chain, h_fibre_ent]
  have h_arith :
      (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (P + (N : ℝ)))
          - (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
        = (1/2) * Real.log (1 + P / (N : ℝ)) :=
    capacity_log_diff hP hN
  calc Common2026.Shannon.differentialEntropy q
        - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
      ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
          - (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ)) := by
        exact sub_le_sub_right h_maxent _
    _ = (1/2) * Real.log (1 + P / (N : ℝ)) := by rw [hv_coe]; exact h_arith

/-! ## Phase 7b — genuine capacity closed form (supersedes the `_of_out` wrapper) -/

open InformationTheory.Shannon.ChannelCoding in
/-- **AWGN capacity closed form (Cover-Thomas 9.1), genuine assembly.**

`awgnCapacity P N = (1/2) log(1 + P/N)`. This supersedes
`ContChannelMIDecomp.awgn_capacity_closed_form_of_out`: there the converse
max-entropy bound `h_max_ent` was a body `sorry`; here it is supplied genuinely by
`awgn_per_input_mi_le_log` (whose only residual is the Phase-6 output-log-density
integrability wall). The achievability bridge (`awgn_mi_gaussian_closed_form_of_out`),
the MI decomposition (`isAwgnMIDecomp_of_densitySplit`) and the bind/conv
output-Gaussian fact are all genuinely wired upstream.

Residual status: the only `sorry` reachable from this theorem is the Phase-6 mixture
output log-density integrability (`outputDistribution_logDensity_integrable` /
`_joint`), threaded transitively through `awgn_per_input_mi_le_log`.
@residual(wall:awgn-capacity-converse-maxent) -/
theorem awgn_capacity_closed_form_genuine
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have hN_NN : N ≠ 0 :=
    fun h => hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h))
  have hP_toNN_pos : (0 : ℝ≥0) < P.toNNReal := Real.toNNReal_pos.mpr hP
  have hPN : P.toNNReal + N ≠ 0 :=
    (add_pos_of_pos_of_nonneg hP_toNN_pos (zero_le' (a := N))).ne'
  -- Output-Gaussian fact, genuine via the translation-kernel bind/conv bridge.
  have h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N) :=
    awgn_output_gaussian_of_bind_eq_conv P N (isAwgnChannelMeasurable N)
      (isAwgnBindEqConv_discharged P N (isAwgnChannelMeasurable N))
  -- MI decomposition, genuine via Route B (the continuous-channel MI chain rule).
  have h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N) :=
    isAwgnMIDecomp_of_densitySplit P N hN_NN hPN (isAwgnChannelMeasurable N) h_out
  -- ★ Converse single-letter Gaussian max-entropy bound — genuine via Phase 7 assembly.
  have h_max_ent :
      ∀ p ∈ awgnPowerConstraintSet P,
        (mutualInfoOfChannel p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
    intro p hp
    have hp_prob : IsProbabilityMeasure p := hp.1
    exact awgn_per_input_mi_le_log hP hN (isAwgnChannelMeasurable N) p hp
  -- Bounded-above follows from the converse bound.
  have h_bdd :
      BddAbove ((fun p : Measure ℝ =>
          (mutualInfoOfChannel p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
        awgnPowerConstraintSet P) :=
    ⟨(1/2) * Real.log (1 + P / (N : ℝ)), by
      rintro y ⟨p, hp, rfl⟩; exact h_max_ent p hp⟩
  exact awgn_capacity_closed_form_of_maxent_bindconv_discharged
    P hP N hN h_decomp h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
