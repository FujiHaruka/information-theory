import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensityGaussianGateway
import InformationTheory.Shannon.EPIBlachmanGaussianWitness
import InformationTheory.Shannon.FisherInfoV2
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# EPI Case-1 producer measurability bricks (Layer C closure, C-b route)

This file supplies the `t`-parameter measurability needed by the `integrable_deriv`
field of `isDeBruijnRegularityHyp_of_methodX_unitnoise`
(`EPICase1RatioLimit.lean:2041`), the sole remaining `sorryAx` leaf of the EPI
moonshot.

## Route — C-b (closed-form score, no `measurable_deriv_with_param`)

`measurable_deriv_with_param` requires global `Continuous f.uncurry`, which fails
at `t ≤ 0` (`gaussianPDFReal 0 0 = 0` plus prefactor blow-up). We bypass it: the
score `logDeriv (convDensityAdd pX g_t) z = (∫ x, pX x · deriv g_t (z - x)) /
(convDensityAdd pX g_t) z` (`convDensityAdd_logDeriv`) is built from jointly
measurable pieces — `StronglyMeasurable.integral_prod_right` for the numerator,
Layer-A joint measurability for the denominator, then `Measurable.div`.

All hypotheses are pure regularity (`Measurable pX` etc.); no de Bruijn / Fisher
core is threaded as a load-bearing hypothesis (CLAUDE.md「検証の誠実性」).
-/

namespace InformationTheory.Shannon.EPICase1ProducerMeasurability

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

/-- **Layer A brick**: the Gaussian pdf is jointly measurable in `(variance, point)`.
The in-tree port `measurable_gaussianPDFReal_uncurry` is on the *mean* axis; this is
the *variance* axis (`v = p.1.toNNReal`). -/
theorem measurable_gaussianPDFReal_var_uncurry :
    Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 p.1.toNNReal p.2) := by
  have hv : Measurable (fun p : ℝ × ℝ => ((p.1.toNNReal : ℝ≥0) : ℝ)) := by
    exact (continuous_real_toNNReal.measurable.comp measurable_fst).coe_nnreal_real
  simp only [gaussianPDFReal]
  apply Measurable.mul
  · -- prefactor `(√(2π·v))⁻¹`
    exact ((((measurable_const.mul hv).sqrt).inv))
  · -- `exp(-(x)²/(2v))`
    apply Measurable.exp
    apply Measurable.div
    · exact ((measurable_snd.sub measurable_const).pow_const 2).neg
    · exact measurable_const.mul hv

/-- **Layer A brick**: the convolution density is jointly measurable in `(t, z)`. -/
theorem measurable_convDensityAdd_gaussian_uncurry
    {pX : ℝ → ℝ} (hpX : Measurable pX) :
    Measurable (fun p : ℝ × ℝ =>
      EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal) p.2) := by
  -- `convDensityAdd pX g_t z = ∫ x, pX x * g_t (z - x)`; apply `integral_prod_right`.
  have hint : (fun p : ℝ × ℝ =>
      EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal) p.2)
      = fun p : ℝ × ℝ =>
        ∫ x, (fun (q : ℝ × ℝ) (x : ℝ) =>
          pX x * gaussianPDFReal 0 q.1.toNNReal (q.2 - x)) p x ∂volume := by
    funext p
    rfl
  rw [hint]
  -- joint strong measurability of the integrand `(p, x) ↦ pX x · g_{p.1}(p.2 - x)`.
  have hmeas_g : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      gaussianPDFReal 0 q.1.1.toNNReal (q.1.2 - q.2)) :=
    measurable_gaussianPDFReal_var_uncurry.comp
      (Measurable.prodMk (measurable_fst.comp measurable_fst)
        ((measurable_snd.comp measurable_fst).sub measurable_snd))
  have hmeas_F : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      pX q.2 * gaussianPDFReal 0 q.1.1.toNNReal (q.1.2 - q.2)) :=
    (hpX.comp measurable_snd).mul hmeas_g
  have hsm : StronglyMeasurable (Function.uncurry (fun (p : ℝ × ℝ) (x : ℝ) =>
      pX x * gaussianPDFReal 0 p.1.toNNReal (p.2 - x))) := by
    simpa [Function.uncurry] using hmeas_F.stronglyMeasurable
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right hsm).measurable

/-- The Gaussian spatial-derivative closed form `deriv (gaussianPDFReal 0 v) w =
-(w)/v · gaussianPDFReal 0 v w`, valid for **all** `v` (including `v = 0`, where both
sides vanish: `gaussianPDFReal 0 0 = 0` and `-(w)/0 = 0`). -/
theorem deriv_gaussianPDFReal_zero_mean_all (v : ℝ≥0) (w : ℝ) :
    deriv (gaussianPDFReal 0 v) w = -(w) / (v : ℝ) * gaussianPDFReal 0 v w := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianPDFReal_zero_var]
  · have := InformationTheory.Shannon.deriv_gaussianPDFReal (m := 0) (v := v) hv w
    simpa using this

/-- **Layer A brick**: the score-form numerator `(t, z) ↦ ∫ x, pX x · deriv g_t (z - x)`
is jointly measurable. Uses the closed form `deriv (gaussianPDFReal 0 v) w =
-(w)/v · gaussianPDFReal 0 v w` so the integrand is jointly measurable. -/
theorem measurable_scoreNum_gaussian_uncurry
    {pX : ℝ → ℝ} (hpX : Measurable pX) :
    Measurable (fun p : ℝ × ℝ =>
      ∫ x, pX x * deriv (gaussianPDFReal 0 p.1.toNNReal) (p.2 - x) ∂volume) := by
  -- Rewrite the integrand via the global closed form.
  have hrw : (fun p : ℝ × ℝ =>
      ∫ x, pX x * deriv (gaussianPDFReal 0 p.1.toNNReal) (p.2 - x) ∂volume)
      = fun p : ℝ × ℝ => ∫ x, (fun (q : ℝ × ℝ) (x : ℝ) =>
          pX x * (-(q.2 - x) / (q.1.toNNReal : ℝ)
            * gaussianPDFReal 0 q.1.toNNReal (q.2 - x))) p x ∂volume := by
    funext p
    congr 1
    funext x
    rw [deriv_gaussianPDFReal_zero_mean_all]
  rw [hrw]
  -- joint measurability of the integrand.
  have hmeas_g : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      gaussianPDFReal 0 q.1.1.toNNReal (q.1.2 - q.2)) :=
    measurable_gaussianPDFReal_var_uncurry.comp
      (Measurable.prodMk (measurable_fst.comp measurable_fst)
        ((measurable_snd.comp measurable_fst).sub measurable_snd))
  have hv : Measurable (fun q : (ℝ × ℝ) × ℝ => ((q.1.1.toNNReal : ℝ≥0) : ℝ)) :=
    (continuous_real_toNNReal.measurable.comp
      (measurable_fst.comp measurable_fst)).coe_nnreal_real
  have hmeas_F : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      pX q.2 * (-(q.1.2 - q.2) / (q.1.1.toNNReal : ℝ)
        * gaussianPDFReal 0 q.1.1.toNNReal (q.1.2 - q.2))) :=
    (hpX.comp measurable_snd).mul
      ((((measurable_snd.comp measurable_fst).sub measurable_snd).neg.div hv).mul hmeas_g)
  have hsm : StronglyMeasurable (Function.uncurry (fun (p : ℝ × ℝ) (x : ℝ) =>
      pX x * (-(p.2 - x) / (p.1.toNNReal : ℝ)
        * gaussianPDFReal 0 p.1.toNNReal (p.2 - x)))) := by
    simpa [Function.uncurry] using hmeas_F.stronglyMeasurable
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right hsm).measurable

/-- **C-b key identity**: `deriv (convDensityAdd pX g_t) z = ∫ x, pX x · deriv g_t (z - x)`
for **all** `t, z` (the differentiation-under-the-integral score form). For `t > 0`
this is `convDensityAdd_hasDerivAt_of_integrable_smoothKernel.deriv`; for `t ≤ 0` both
sides vanish (`g_0 = 0` ⇒ `conv = 0` ⇒ `deriv = 0`, and `deriv g_0 = 0` ⇒ integrand `0`).

`hpX_int` is a pure regularity precondition (`pX` is an integrable density). -/
theorem deriv_convDensityAdd_gaussian_eq_scoreNum
    {pX : ℝ → ℝ} (hpX_int : Integrable pX volume) (t z : ℝ) :
    deriv (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal)) z
      = ∫ x, pX x * deriv (gaussianPDFReal 0 t.toNNReal) (z - x) ∂volume := by
  by_cases ht : 0 < t
  · -- t > 0: the Gaussian kernel is regular; differentiation under the integral fires.
    have hv_ne : t.toNNReal ≠ 0 := by
      simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact ht
    have hregY := EPIBlachmanGaussianWitness.isRegularDensityV2_gaussianPDFReal
      (m := 0) hv_ne
    have hY_bdd := EPIBlachmanGaussianWitness.bdd_gaussianPDFReal 0 t.toNNReal
    have hY'_bdd := EPIBlachmanGaussianWitness.bdd_deriv_gaussianPDFReal (m := 0) hv_ne
    have hderiv := EPIConvDensityGaussianGateway.convDensityAdd_hasDerivAt_of_integrable_smoothKernel
      pX (gaussianPDFReal 0 t.toNNReal) z hpX_int hregY hY_bdd hY'_bdd
    rw [hderiv.deriv]
    rfl
  · -- t ≤ 0: variance is 0, the kernel is identically 0, both sides vanish.
    have ht0 : t.toNNReal = 0 := by
      simp only [Real.toNNReal_eq_zero]; exact le_of_not_gt ht
    rw [ht0]
    have hconv0 : EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 0)
        = fun _ => (0 : ℝ) := by
      funext w
      simp only [EPIConvDensity.convDensityAdd, gaussianPDFReal_zero_var,
        Pi.zero_apply, mul_zero, integral_zero]
    rw [hconv0]
    simp [gaussianPDFReal_zero_var]

/-- **Layer C brick (C-b core)**: `logDeriv (convDensityAdd pX g_t)` is jointly
measurable in `(t, z)`. By `logDeriv = deriv / conv` and the C-b key identity
`deriv (conv_t) = scoreNum t`, this is `scoreNum / conv`, both jointly measurable.

`hpX_int` is a pure regularity precondition, not the de Bruijn core. -/
theorem measurable_logDeriv_convDensityAdd_gaussian_uncurry
    {pX : ℝ → ℝ} (hpX : Measurable pX) (hpX_int : Integrable pX volume) :
    Measurable (fun p : ℝ × ℝ =>
      logDeriv (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal)) p.2) := by
  have hrw : (fun p : ℝ × ℝ =>
      logDeriv (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal)) p.2)
      = fun p : ℝ × ℝ =>
        (∫ x, pX x * deriv (gaussianPDFReal 0 p.1.toNNReal) (p.2 - x) ∂volume)
          / EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 p.1.toNNReal) p.2 := by
    funext p
    rw [logDeriv_apply, deriv_convDensityAdd_gaussian_eq_scoreNum hpX_int]
  rw [hrw]
  exact (measurable_scoreNum_gaussian_uncurry hpX).div
    (measurable_convDensityAdd_gaussian_uncurry hpX)

/-- **Final brick**: the `t`-side measurability the producer's `integrable_deriv`
field needs, in the exact `Measure.integrableOn_of_bounded` shape (over `volume`).

`hpX_int` is a pure regularity precondition (integrable probability density). -/
theorem aestronglyMeasurable_fisherInfo_t
    {pX : ℝ → ℝ} (hpX : Measurable pX) (hpX_int : Integrable pX volume) :
    AEStronglyMeasurable (fun t : ℝ =>
      (1 / 2) * (FisherInfoV2.fisherInfoOfDensity
        (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal))).toReal)
      volume := by
  -- Unfold `fisherInfoOfDensity` into its lintegral and apply parameter measurability.
  -- integrand `(t, x) ↦ ofReal((logDeriv conv_t x)²) * ofReal(conv_t x)` jointly measurable.
  have hlogDeriv := measurable_logDeriv_convDensityAdd_gaussian_uncurry hpX hpX_int
  have hconv := measurable_convDensityAdd_gaussian_uncurry hpX
  have hintegrand : Measurable (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
      ENNReal.ofReal ((logDeriv (EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 t.toNNReal)) x) ^ 2)
        * ENNReal.ofReal (EPIConvDensity.convDensityAdd pX
            (gaussianPDFReal 0 t.toNNReal) x))) := by
    have h1 : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((logDeriv (EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 p.1.toNNReal)) p.2) ^ 2)) :=
      (hlogDeriv.pow_const 2).ennreal_ofReal
    have h2 : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 p.1.toNNReal) p.2)) :=
      hconv.ennreal_ofReal
    simpa [Function.uncurry] using h1.mul h2
  -- `t ↦ J(conv_t) = ∫⁻ x, integrand t x` is measurable.
  have hlint : Measurable (fun t : ℝ =>
      FisherInfoV2.fisherInfoOfDensity
        (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal))) := by
    simp only [FisherInfoV2.fisherInfoOfDensity]
    exact Measurable.lintegral_prod_right hintegrand
  exact (((hlint.ennreal_toReal).const_mul (1 / 2))).aestronglyMeasurable

end InformationTheory.Shannon.EPICase1ProducerMeasurability
