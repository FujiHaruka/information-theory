import Common2026.Shannon.EPIConvDensity

/-!
# Differential-entropy-finiteness wall: integrability of log-factor × derivative integrands

Shared honest-`sorry` lemmas for the **differential-entropy-finiteness** Mathlib gap.
This is the same-family wall as Fisher-finiteness (`FisherConvBound.lean` /
`convDensityAdd_fisher_integrable`): for the Gaussian convolution density
`p_t = convDensityAdd pX g_t` (`g_t = gaussianPDFReal 0 ⟨t,_⟩`, `t > 0`) the
differential entropy `h(X + √t·Z) = -∫ negMulLog p_t` is finite for any probability
density `pX`, and the associated log-factor integrands `(- log p_t - 1)·∂_x p_t` and
`(- log p_t - 1)·∂²_x p_t` are integrable. Mathlib has no convolution
differential-entropy finiteness result (loogle `negMulLog ∘ conv` / `differentialEntropy
(conv ...)` = absent); the repo's Stam / Fisher machinery covers `J(p_t) < ∞` but not the
`log`-factor integrands themselves.

## honest-sorry, NOT load-bearing

Each lemma's conclusion is an `Integrable (...)` statement (a regularity output), with
`pX` non-negativity / measurability / integrability as honest preconditions. The
conclusion does **not** bundle the de Bruijn / Fisher core: it is the integrability of a
concrete integrand, supplied as a precondition to `debruijn_ibp_step`. No proof core is
hidden in a hypothesis predicate; the `sorry` is the genuine Mathlib gap (differential
entropy finiteness of a Gaussian convolution density), classified `wall:entropy-finiteness`.
-/

namespace InformationTheory.Shannon.EntropyConvFinite

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

/-- **Entropy-finiteness wall (log-factor × 2nd-derivative integrability).**
For the Gaussian convolution density `p_t = convDensityAdd pX g_t` (`t > 0`), the
integrand `(- log p_t - 1)·∂²_x p_t` of the de Bruijn IBP step is integrable.

This is the `Integrable (u * v')` precondition of `debruijn_ibp_step` with
`u = - log p_t - 1`, `v' = ∂²_x p_t`. Differential-entropy finiteness of a Gaussian
convolution density (Mathlib absent, same family as `convDensityAdd_fisher_integrable`'s
Fisher-finiteness wall). The conclusion is integrability of a concrete integrand
(regularity output), NOT a bundled de Bruijn / Fisher conclusion.

@residual(wall:entropy-finiteness) -/
theorem convDensityAdd_logFactor_deriv2_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))) x) volume := by
  sorry -- @residual(wall:entropy-finiteness)

/-- **Entropy-finiteness wall (log-factor × 1st-derivative integrability).**
For the Gaussian convolution density `p_t = convDensityAdd pX g_t` (`t > 0`), the
integrand `(- log p_t - 1)·∂_x p_t` is integrable.

This is the `Integrable (u * v)` precondition of `debruijn_ibp_step` with
`u = - log p_t - 1`, `v = ∂_x p_t`. Differential-entropy finiteness of a Gaussian
convolution density (Mathlib absent, same family as the Fisher-finiteness wall). The
conclusion is integrability of a concrete integrand (regularity output), NOT a bundled
conclusion.

@residual(wall:entropy-finiteness) -/
theorem convDensityAdd_logFactor_deriv_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
        * deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x) volume := by
  sorry -- @residual(wall:entropy-finiteness)

/-- **Entropy-finiteness wall (negMulLog integrability, forward supply).**
For the Gaussian convolution density `p_t = convDensityAdd pX g_t` (`t > 0`), the
differential-entropy integrand `negMulLog p_t = - p_t · log p_t` is integrable, hence
`h(X + √t·Z) = -∫ negMulLog p_t` is finite.

Forward supply for the entropy-derivative chain (`_chain_parametric` / `_chain_entDeriv`
parametric-diff body, Wave 2). Differential-entropy finiteness of a Gaussian convolution
density (Mathlib absent). The conclusion is integrability of a concrete integrand
(regularity output), NOT a bundled conclusion.

@residual(wall:entropy-finiteness) -/
theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume := by
  sorry -- @residual(wall:entropy-finiteness)

end InformationTheory.Shannon.EntropyConvFinite
