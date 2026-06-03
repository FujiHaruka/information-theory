import Common2026.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.LConvolution
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoGaussian
import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.EPIBlachmanDensity

/-!
# Gaussian witness for `IsBlachmanConvReady` / `IsRegularDensityV2`

Density-route non-vacuousness closure (`epi-wall-reattack-plan`, Phase 3e):
a **proven inhabitant** of `IsBlachmanConvReady (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)`
and `IsRegularDensityV2 (gaussianPDFReal m v)`, built from the existing Gaussian
Fisher-information lemmas plus the measure-level convolution closed form.

The linchpin `convDensityAdd_gaussian_closed_form` shows the pointwise density
convolution closed form `convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)
= gaussianPDFReal (mX+mY) (vX+vY)`, which the `int_fisherZ` field needs.
-/

namespace Common2026.Shannon.EPIBlachmanGaussianWitness

open MeasureTheory Real ProbabilityTheory
open Common2026.Shannon.FisherInfoV2
open InformationTheory.Shannon.EPIConvDensity
open InformationTheory.Shannon.EPIBlachmanDensity
open scoped ENNReal NNReal

/-! ## Helpers -/

/-- Uniform sup bound `gaussianPDFReal μ v x ≤ (√(2πv))⁻¹` (attained at `x = μ`),
from `exp(-(x-μ)²/(2v)) ≤ 1`.
@audit:ok — independent honesty audit (2026-05-31): 0-sorry genuine, sorryAx-free
(`#print axioms` → [propext, Classical.choice, Quot.sound]). -/
@[entry_point]
theorem gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  have hc : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply Real.exp_le_one_iff.mpr
        apply div_nonpos_of_nonpos_of_nonneg
        · simp only [neg_nonpos]; positivity
        · positivity
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-- Boundedness of `gaussianPDFReal μ v`.
@audit:ok — independent honesty audit (2026-05-31): 0-sorry genuine, sorryAx-free. -/
@[entry_point]
theorem bdd_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    ∃ M : ℝ, ∀ w, |gaussianPDFReal μ v w| ≤ M :=
  ⟨(Real.sqrt (2 * Real.pi * v))⁻¹, fun w => by
    rw [abs_of_nonneg (gaussianPDFReal_nonneg μ v w)]
    exact gaussianPDFReal_le μ v w⟩

/-- Elementary bound `s * exp(-s²/(2v)) ≤ √v` for `s ≥ 0`, `v > 0`.
Proof: with `u = s/√v ≥ 0`, the claim is `u ≤ exp(u²/2)`, which follows from
`u ≤ 1 + u²/2 ≤ exp(u²/2)`.
@audit:ok — independent honesty audit (2026-05-31): elementary bound genuine
(`u ≤ 1+u²/2` via `(u-1)²≥0`, `1+t ≤ exp t` via `add_one_le_exp`); sorryAx-free. -/
@[entry_point]
theorem mul_exp_neg_sq_le {v : ℝ} (hv : 0 < v) {s : ℝ} (hs : 0 ≤ s) :
    s * Real.exp (-s ^ 2 / (2 * v)) ≤ Real.sqrt v := by
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  set u : ℝ := s / Real.sqrt v with hu_def
  have hu0 : 0 ≤ u := div_nonneg hs hsv.le
  have hsu : s = u * Real.sqrt v := by
    rw [hu_def, div_mul_cancel₀ _ hsv.ne']
  -- key: u ≤ exp (u^2 / 2)
  have hkey : u ≤ Real.exp (u ^ 2 / 2) := by
    calc u ≤ 1 + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
      _ ≤ Real.exp (u ^ 2 / 2) := by
          have := Real.add_one_le_exp (u ^ 2 / 2)
          linarith
  -- exponent rewrite: -s²/(2v) = -(u²/2)
  have hexp : -s ^ 2 / (2 * v) = -(u ^ 2 / 2) := by
    rw [hsu]
    have hsq : (u * Real.sqrt v) ^ 2 = u ^ 2 * v := by
      rw [mul_pow, Real.sq_sqrt hv.le]
    rw [hsq]
    field_simp
  rw [hexp, hsu]
  rw [Real.exp_neg]
  rw [mul_assoc, mul_comm (Real.sqrt v), ← mul_assoc]
  calc u * (Real.exp (u ^ 2 / 2))⁻¹ * Real.sqrt v
      ≤ 1 * Real.sqrt v := by
        apply mul_le_mul_of_nonneg_right _ hsv.le
        rw [mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
        exact hkey
    _ = Real.sqrt v := one_mul _

/-- Continuity of `deriv (gaussianPDFReal m v)` via its closed form
`-(x-m)/v · gaussianPDFReal m v x`.
@audit:ok — independent honesty audit (2026-05-31): 0-sorry genuine, sorryAx-free. -/
@[entry_point]
theorem continuous_deriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Continuous (deriv (gaussianPDFReal m v)) := by
  have heq : deriv (gaussianPDFReal m v)
      = fun x => -(x - m) / (v : ℝ) * gaussianPDFReal m v x := by
    funext x; exact Common2026.Shannon.deriv_gaussianPDFReal hv x
  rw [heq]
  have h1 : Continuous (fun x : ℝ => -(x - m) / (v : ℝ)) := by fun_prop
  exact h1.mul (Common2026.Shannon.differentiable_gaussianPDFReal m v).continuous

/-- Boundedness of `deriv (gaussianPDFReal m v)`.
`deriv f w = -(w-m)/v · f w`, and `|w-m| · exp(-(w-m)²/(2v)) ≤ √v`
(by `mul_exp_neg_sq_le`), so the derivative is uniformly bounded.
@audit:ok — independent honesty audit (2026-05-31): 0-sorry genuine, sorryAx-free. -/
@[entry_point]
theorem bdd_deriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ M : ℝ, ∀ w, |deriv (gaussianPDFReal m v) w| ≤ M := by
  have hv_pos : (0 : ℝ) < v := by
    have := (NNReal.coe_pos).mpr (pos_of_ne_zero hv)
    simpa using this
  refine ⟨(v : ℝ)⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.sqrt v, fun w => ?_⟩
  rw [Common2026.Shannon.deriv_gaussianPDFReal hv, gaussianPDFReal_def]
  have habs : |(-(w - m) / (v : ℝ)) *
      ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(w - m) ^ 2 / (2 * v)))|
      = ((v : ℝ)⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹)
        * (|w - m| * Real.exp (-(w - m) ^ 2 / (2 * v))) := by
    simp only [abs_mul]
    rw [abs_of_nonneg (le_of_lt (Real.exp_pos _)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (2 * Real.pi * v))⁻¹)]
    rw [neg_div, abs_neg, abs_div, abs_of_nonneg hv_pos.le]
    ring
  rw [habs]
  have hsup : |w - m| * Real.exp (-(w - m) ^ 2 / (2 * v)) ≤ Real.sqrt v := by
    have := mul_exp_neg_sq_le hv_pos (s := |w - m|) (abs_nonneg _)
    rwa [sq_abs] at this
  calc ((v : ℝ)⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹)
        * (|w - m| * Real.exp (-(w - m) ^ 2 / (2 * v)))
      ≤ ((v : ℝ)⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹) * Real.sqrt v :=
        mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = (v : ℝ)⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.sqrt v := by ring

/-- `Integrable (fun x => logDeriv (gaussianPDFReal m v) x * gaussianPDFReal m v x)`.
Since `logDeriv f · f = -(x-m)/v · f`, this is `-(1/v)` times
`integrable_sub_mul_gaussianPDFReal`.
@audit:ok — independent honesty audit (2026-05-31): 0-sorry genuine, sorryAx-free. -/
@[entry_point]
theorem integrable_logDeriv_mul_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => logDeriv (gaussianPDFReal m v) x * gaussianPDFReal m v x) volume := by
  refine ((Common2026.Shannon.integrable_sub_mul_gaussianPDFReal m hv).const_mul
    (-(v : ℝ)⁻¹)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hv]
  ring

/-! ## 段0 — linchpin: density-level Gaussian convolution closed form -/

/-- **Linchpin**: the pointwise density convolution closed form for Gaussians.

`convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z
   = gaussianPDFReal (mX+mY) (vX+vY) z` for every `z`.

Built via the measure-level route
`gaussianReal_conv_gaussianReal` + `gaussianReal_of_var_ne_zero`
+ `mconv_withDensity_eq_mlconvolution₀`, then ENNReal↔Real bridge and an
a.e.→pointwise upgrade using continuity of both sides.

@audit:ok — independent honesty audit (2026-05-31): genuine core-reconstruction.
The 5-step measure-level route (lconvolution pointwise value → withDensity equality
via `gaussianReal_conv_gaussianReal` + `conv_withDensity_eq_mlconvolution₀` →
a.e. density equality via `withDensity_eq_iff_of_sigmaFinite` → ENNReal↔Real bridge →
a.e.→pointwise via `Continuous.ae_eq_iff_eq`) reconstructs the stated pointwise
closed form; no field is the conclusion-as-hypothesis. All cited Mathlib lemmas
verified present (loogle/rg). `#print axioms` → [propext, Classical.choice, Quot.sound]
(sorryAx-free, transitive 0 sorry). -/
@[entry_point]
theorem convDensityAdd_gaussian_closed_form
    {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) :
    convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)
      = gaussianPDFReal (mX + mY) (vX + vY) := by
  have hvXY : vX + vY ≠ 0 := by
    intro h
    apply hvX
    have := (add_eq_zero.mp h).1
    exact this
  -- Pointwise ENNReal value of the additive lconvolution of the two `gaussianPDF`s.
  -- `(gaussianPDF mX vX ⋆ₗ gaussianPDF mY vY) z = ENNReal.ofReal (convDensityAdd … z)`.
  have h_lconv_pt : ∀ z,
      (gaussianPDF mX vX ⋆ₗ gaussianPDF mY vY) z
        = ENNReal.ofReal (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z) := by
    intro z
    -- Integrability of `x ↦ gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)`.
    have hint : Integrable
        (fun x => gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)) volume := by
      obtain ⟨C, hC⟩ := bdd_gaussianPDFReal mY vY
      refine (integrable_gaussianPDFReal mX vX).mul_bdd (c := C) ?_ ?_
      · exact ((measurable_gaussianPDFReal mY vY).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC (z - x)
    have hnn : 0 ≤ᵐ[volume]
        (fun x => gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)) :=
      Filter.Eventually.of_forall fun x =>
        mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
    rw [lconvolution_def, convDensityAdd,
      ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine lintegral_congr fun y => ?_
    rw [gaussianPDF, gaussianPDF,
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 2
    ring
  -- a.e. equality of densities from the measure-level convolution closed form.
  have h_ae : (gaussianPDF mX vX ⋆ₗ gaussianPDF mY vY)
      =ᵐ[volume] gaussianPDF (mX + mY) (vX + vY) := by
    have hmeas : volume.withDensity (gaussianPDF mX vX ⋆ₗ gaussianPDF mY vY)
        = volume.withDensity (gaussianPDF (mX + mY) (vX + vY)) := by
      rw [← conv_withDensity_eq_mlconvolution₀
            (measurable_gaussianPDF mX vX).aemeasurable
            (measurable_gaussianPDF mY vY).aemeasurable,
          ← gaussianReal_of_var_ne_zero mX hvX,
          ← gaussianReal_of_var_ne_zero mY hvY,
          gaussianReal_conv_gaussianReal,
          gaussianReal_of_var_ne_zero _ hvXY]
    refine (withDensity_eq_iff_of_sigmaFinite ?_
      (measurable_gaussianPDF (mX + mY) (vX + vY)).aemeasurable).mp hmeas
    exact aemeasurable_lconvolution
      (measurable_gaussianPDF mX vX).aemeasurable
      (measurable_gaussianPDF mY vY).aemeasurable
  -- Combine: `convDensityAdd … =ᵐ gaussianPDFReal (sum)`.
  have h_ae_real : convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)
      =ᵐ[volume] gaussianPDFReal (mX + mY) (vX + vY) := by
    have h_ofReal : (fun z => ENNReal.ofReal
        (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z))
          =ᵐ[volume] gaussianPDF (mX + mY) (vX + vY) := by
      refine (Filter.EventuallyEq.symm ?_).symm
      calc (fun z => ENNReal.ofReal
            (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z))
          = (gaussianPDF mX vX ⋆ₗ gaussianPDF mY vY) := by
              funext z; exact (h_lconv_pt z).symm
        _ =ᵐ[volume] gaussianPDF (mX + mY) (vX + vY) := h_ae
    refine h_ofReal.mono fun z hz => ?_
    have hnn_z : 0 ≤ convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z := by
      apply integral_nonneg
      intro x
      exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
    have := congrArg ENNReal.toReal hz
    rwa [ENNReal.toReal_ofReal hnn_z, toReal_gaussianPDF] at this
  -- Upgrade to pointwise via continuity of both sides.
  obtain ⟨C, hC⟩ := bdd_gaussianPDFReal mY vY
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have h_cont_conv : Continuous
      (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)) := by
    refine continuous_of_dominated
      (bound := fun a => C * gaussianPDFReal mX vX a)
      (fun z => ?_) (fun z => Filter.Eventually.of_forall fun a => ?_)
      ((integrable_gaussianPDFReal mX vX).const_mul C)
      (Filter.Eventually.of_forall fun a => ?_)
    · exact (Common2026.Shannon.differentiable_gaussianPDFReal mX vX).continuous.aestronglyMeasurable.mul
        (((Common2026.Shannon.differentiable_gaussianPDFReal mY vY).continuous.comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · -- ‖fX a * fY (z - a)‖ ≤ C * fX a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
      have : |gaussianPDFReal mY vY (z - a)| ≤ C := hC (z - a)
      calc gaussianPDFReal mX vX a * |gaussianPDFReal mY vY (z - a)|
          ≤ gaussianPDFReal mX vX a * C :=
            mul_le_mul_of_nonneg_left this (gaussianPDFReal_nonneg _ _ _)
        _ = C * gaussianPDFReal mX vX a := by ring
    · -- continuity in z of a ↦ fX a * fY (z - a)
      exact continuous_const.mul
        ((Common2026.Shannon.differentiable_gaussianPDFReal mY vY).continuous.comp
          (continuous_id.sub continuous_const))
  exact (h_cont_conv.ae_eq_iff_eq volume
    (Common2026.Shannon.differentiable_gaussianPDFReal (mX + mY) (vX + vY)).continuous).mp h_ae_real

/-! ## 段1 — `IsRegularDensityV2 (gaussianPDFReal m v)` (6 fields, all direct) -/

/-- `IsRegularDensityV2 (gaussianPDFReal m v)` — all six fields discharged from the
existing Gaussian regularity lemmas in `FisherInfoGaussian`.

@audit:ok — independent honesty audit (2026-05-31): all 6 fields (`diff`/`pos`/
`tail_bot`/`tail_top`/`integrable_deriv`/`integral_deriv_eq_zero`) are pure regularity
claims discharged by existing Gaussian lemmas, no core bundled. `#print axioms` →
[propext, Classical.choice, Quot.sound] (sorryAx-free). -/
@[entry_point]
theorem isRegularDensityV2_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    IsRegularDensityV2 (gaussianPDFReal m v) where
  diff := Common2026.Shannon.differentiable_gaussianPDFReal m v
  pos := fun x => gaussianPDFReal_pos m v x hv
  tail_bot := Common2026.Shannon.tendsto_gaussianPDFReal_atBot m hv
  tail_top := Common2026.Shannon.tendsto_gaussianPDFReal_atTop m hv
  integrable_deriv := Common2026.Shannon.integrable_deriv_gaussianPDFReal m hv
  integral_deriv_eq_zero := Common2026.Shannon.integral_deriv_gaussianPDFReal_eq_zero m hv

/-! ## 段2/段3 — `IsBlachmanConvReady` Gaussian witness (19 fields) -/

/-- **Gaussian witness** for `IsBlachmanConvReady` — density-route non-vacuousness.

The structure literal supplies each of the 19 fields from the existing Gaussian
lemmas (and the linchpin for `int_fisherZ`). **All 19 fields are now genuine
(0 sorry).** The previously-residual 5 — `int_Wsq`, `int_inner` (quadratic-score
integrability) and `int_prod1/2/3` (non-separable 2D Tonelli terms) — are closed
WITHOUT a Mathlib wall: `int_Wsq` by the 3-term `(a+b)²` expansion (each term
integrable × bounded, then `/pZ`); `int_prod1/2/3` by the shear change of variables
`measurePreserving_prod_sub_swap` (`(z,x) ↦ (x, z-x)`) turning the non-separable
`fY(z-x)` into a separable `g(x)·h(z-x)` to which `Integrable.mul_prod` applies;
`int_inner` by reducing to those product-measure integrabilities via the Tonelli
marginal `Integrable.integral_prod_left` plus the `condDensityX · pZ = fX·fY(z-·)`
cancellation.

WITNESS STATUS: proof done — `#print axioms isBlachmanConvReady_gaussianPDFReal`
yields `[propext, Classical.choice, Quot.sound]` (sorryAx-free, transitive 0 sorry),
so a **proven inhabitant** of `IsBlachmanConvReady (gaussianPDFReal mX vX)
(gaussianPDFReal mY vY)` exists. The Phase 3d non-vacuousness caveat is thereby
machine-confirmed for the density route.

Structurally GENUINE — the witness is a plain `structure` literal `{mX mY vX vY}
(hvX hvY)`; `IsBlachmanConvReady` carries ONLY `Integrable`/boundedness/positivity
fields (no inequality/equality/value core), so this is not a load-bearing bundle.
The Z-side `pos_pZ`/`int_fisherZ` route through the sorryAx-free linchpin
`convDensityAdd_gaussian_closed_form`; `int_fisher{X,Y}` via the public
`integrable_logDeriv_sq_mul_gaussianPDFReal`.

@audit:ok — independent honesty audit (2026-05-31, commit `6e65535`): witness is
proof done. `#print axioms isBlachmanConvReady_gaussianPDFReal` →
[propext, Classical.choice, Quot.sound] (sorryAx-free, transitive 0 sorry,
machine-verified after olean refresh of `EPIBlachmanDensity`). STRUCTURAL: plain
`structure` literal taking only `hvX hvY : v ≠ 0`; `IsBlachmanConvReady` carries ONLY
Integrable / boundedness / positivity fields (no inequality / equality / value core),
so no load-bearing bundle — genuine inhabitant. The 5 newly-genuine fields
(`int_Wsq` / `int_inner` / `int_prod1/2/3`) RECONSTRUCT `Integrable (…)` (not
hypothesis-handed): `int_prod1/2/3` via the shear `measurePreserving_prod_sub_swap`
(Mathlib `Group/Prod.lean:373`, additive form of `measurePreserving_prod_div_swap`,
`(z,x) ↦ (x, z-x)`, `μ×ν → ν×μ` — direction + type verified) + `Integrable.mul_prod`
(`Integral/Prod.lean:346`) + `MeasurePreserving.integrable_comp_of_integrable`;
`int_inner` via `Integrable.integral_prod_left` (`Integral/Prod.lean:380`) marginal +
`condDensityX·pZ = fX·fY(z-·)` cancellation; `int_Wsq` via 3-term `(a+b)²` expansion.
All cited Mathlib lemmas verified present with correct signatures. NON-VACUOUSNESS
SCOPE: this confirms a proven inhabitant of `IsBlachmanConvReady (gaussian)(gaussian)`,
**now operationally consumed** by `convex_fisher_bound_gaussian_via_density_route`
(this file, 段4) — the density-route convex Fisher bound `J(Z) ≤ λ² J(X) + (1-λ)² J(Y)`
genuinely fires end-to-end on Gaussian densities through this witness (the witness is no
longer an isolated existence proof). The upstream density-route predicates
(`IsStamCauchySchwarzOptimal` / `IsStamCondExpCSHyp`) do not yet have a wired Gaussian
inhabitant lemma — that remains the final density-route closure step. -/
@[entry_point]
theorem isBlachmanConvReady_gaussianPDFReal
    {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0) :
    IsBlachmanConvReady (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) where
  int_fX := integrable_gaussianPDFReal mX vX
  int_fY := integrable_gaussianPDFReal mY vY
  bdd_fX := bdd_gaussianPDFReal mX vX
  bdd_fX' := bdd_deriv_gaussianPDFReal hvX
  bdd_fY := bdd_gaussianPDFReal mY vY
  bdd_fY' := bdd_deriv_gaussianPDFReal hvY
  pos_pZ := by
    intro z
    have hvXY : vX + vY ≠ 0 := fun h => hvX (add_eq_zero.mp h).1
    rw [convDensityAdd_gaussian_closed_form hvX hvY]
    exact gaussianPDFReal_pos _ _ z hvXY
  int_X := by
    intro z
    obtain ⟨M, hM⟩ := bdd_deriv_gaussianPDFReal (m := mX) hvX
    have hg : Integrable (fun x => gaussianPDFReal mY vY (z - x)) volume :=
      (integrable_gaussianPDFReal mY vY).comp_sub_left z
    refine hg.bdd_mul ?_ (c := M) ?_
    · exact (continuous_deriv_gaussianPDFReal hvX).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hM x
  int_Y := by
    intro z
    obtain ⟨M, hM⟩ := bdd_deriv_gaussianPDFReal (m := mY) hvY
    have hg : Integrable (fun x => gaussianPDFReal mX vX x) volume :=
      integrable_gaussianPDFReal mX vX
    refine hg.mul_bdd ?_ (c := M) ?_
    · exact ((continuous_deriv_gaussianPDFReal hvY).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hM (z - x)
  cond_int := by
    intro z
    have hvXY : vX + vY ≠ 0 := fun h => hvX (add_eq_zero.mp h).1
    have hpZ : convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z ≠ 0 := by
      rw [convDensityAdd_gaussian_closed_form hvX hvY]
      exact (gaussianPDFReal_pos _ _ z hvXY).ne'
    have hbase : Integrable
        (fun x => gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)) volume := by
      obtain ⟨C, hC⟩ := bdd_gaussianPDFReal mY vY
      refine (integrable_gaussianPDFReal mX vX).mul_bdd (c := C) ?_ ?_
      · exact ((measurable_gaussianPDFReal mY vY).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hC (z - x)
    refine (hbase.div_const
      (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [condDensityX]
  int_W := by
    intro lam _ _ z
    -- scoreWeight·condDensityX = (1/pZ)·(scoreWeight·(fX·fY(z-·)))
    obtain ⟨CfX, hCfX⟩ := bdd_gaussianPDFReal mX vX
    obtain ⟨CfY, hCfY⟩ := bdd_gaussianPDFReal mY vY
    -- term A: logDeriv fX · fX (integrable) × fY(z-·) (bounded)
    have hA : Integrable (fun x =>
        logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
          * gaussianPDFReal mY vY (z - x)) volume :=
      (integrable_logDeriv_mul_gaussianPDFReal hvX).mul_bdd
        ((measurable_gaussianPDFReal mY vY).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable (c := CfY)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCfY (z - x))
    -- term B: fX (bounded) × logDeriv fY(z-·)·fY(z-·) (integrable shift)
    have hBbase : Integrable (fun x =>
        logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)) volume :=
      (integrable_logDeriv_mul_gaussianPDFReal hvY).comp_sub_left z
    have hB : Integrable (fun x =>
        gaussianPDFReal mX vX x
          * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x))) volume :=
      hBbase.bdd_mul (measurable_gaussianPDFReal mX vX).aestronglyMeasurable (c := CfX)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCfX x)
    -- combine: lam·A + (1-lam)·B, then divide by pZ
    have hcomb := ((hA.const_mul lam).add (hB.const_mul (1 - lam))).div_const
      (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z)
    refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [scoreWeight, condDensityX, Pi.add_apply]
    ring
  int_Wsq := by
    intro lam _ _ z
    obtain ⟨CfX, hCfX⟩ := bdd_gaussianPDFReal mX vX
    obtain ⟨CfY, hCfY⟩ := bdd_gaussianPDFReal mY vY
    obtain ⟨CfX', hCfX'⟩ := bdd_deriv_gaussianPDFReal (m := mX) hvX
    obtain ⟨CfY', hCfY'⟩ := bdd_deriv_gaussianPDFReal (m := mY) hvY
    -- term 1: lam² · (logDeriv fX x)²·fX x · fY(z-x)  = [int_fisherX] × [bounded fY(z-·)]
    have hT1base : Integrable (fun x =>
        (logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x) volume := by
      refine (integrable_logDeriv_sq_mul_gaussianPDFReal mX hvX).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvX, neg_div]; ring
    have hT1 : Integrable (fun x =>
        (logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x
          * gaussianPDFReal mY vY (z - x)) volume :=
      hT1base.mul_bdd ((measurable_gaussianPDFReal mY vY).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable (c := CfY)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCfY (z - x))
    -- term 2: cross  logDeriv fX·fX (int) × logDeriv fY(z-·)·fY(z-·) (= deriv fY(z-·), bounded)
    have hderivY_eq : ∀ w, logDeriv (gaussianPDFReal mY vY) w * gaussianPDFReal mY vY w
        = deriv (gaussianPDFReal mY vY) w := by
      intro w
      rw [Common2026.Shannon.logDeriv_gaussianPDFReal hvY,
        Common2026.Shannon.deriv_gaussianPDFReal hvY]
    have hT2meas : AEStronglyMeasurable
        (fun x => logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x))
        volume := by
      have hcont : Continuous
          (fun x => logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)) := by
        have heq : (fun x => logDeriv (gaussianPDFReal mY vY) (z - x)
            * gaussianPDFReal mY vY (z - x))
            = (fun x => deriv (gaussianPDFReal mY vY) (z - x)) := by
          funext x; exact hderivY_eq (z - x)
        rw [heq]
        exact (continuous_deriv_gaussianPDFReal hvY).comp (continuous_const.sub continuous_id)
      exact hcont.aestronglyMeasurable
    have hT2 : Integrable (fun x =>
        logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
          * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x))) volume :=
      (integrable_logDeriv_mul_gaussianPDFReal hvX).mul_bdd hT2meas (c := CfY')
        (Filter.Eventually.of_forall fun x => by
          rw [hderivY_eq (z - x)]; simpa [Real.norm_eq_abs] using hCfY' (z - x))
    -- term 3: (1-lam)² · (logDeriv fY(z-·))²·fY(z-·) (int shift) × fX (bounded)
    have hT3pre : Integrable (fun w =>
        (logDeriv (gaussianPDFReal mY vY) w) ^ 2 * gaussianPDFReal mY vY w) volume := by
      refine (integrable_logDeriv_sq_mul_gaussianPDFReal mY hvY).congr
        (Filter.Eventually.of_forall fun w => ?_)
      simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvY, neg_div]; ring
    have hT3base : Integrable (fun x =>
        (logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2 * gaussianPDFReal mY vY (z - x)) volume :=
      hT3pre.comp_sub_left z
    have hT3 : Integrable (fun x =>
        gaussianPDFReal mX vX x
          * ((logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2 * gaussianPDFReal mY vY (z - x)))
          volume :=
      hT3base.bdd_mul (measurable_gaussianPDFReal mX vX).aestronglyMeasurable (c := CfX)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCfX x)
    -- combine: lam²·T1 + 2·lam·(1-lam)·T2 + (1-lam)²·T3, then divide by pZ
    have hcomb := ((((hT1.const_mul (lam ^ 2)).add
      (hT2.const_mul (2 * lam * (1 - lam)))).add
      (hT3.const_mul ((1 - lam) ^ 2)))).div_const
      (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z)
    refine hcomb.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [scoreWeight, condDensityX, Pi.add_apply]
    ring
  int_inner := by
    intro lam hlam0 hlam1
    have hvXY : vX + vY ≠ 0 := fun h => hvX (add_eq_zero.mp h).1
    -- product-measure integrability of the three Tonelli terms (= int_prod1/2/3 integrands)
    have hP1 : Integrable
        (Function.uncurry fun z x =>
          (logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x
            * gaussianPDFReal mY vY (z - x)) (volume.prod volume) := by
      have hA : Integrable (fun a =>
          (logDeriv (gaussianPDFReal mX vX) a) ^ 2 * gaussianPDFReal mX vX a) volume := by
        refine (integrable_logDeriv_sq_mul_gaussianPDFReal mX hvX).congr
          (Filter.Eventually.of_forall fun a => ?_)
        simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvX, neg_div]; ring
      have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).integrable_comp_of_integrable
        (hA.mul_prod (integrable_gaussianPDFReal mY vY))
      refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Function.uncurry]
    have hP2 : Integrable
        (Function.uncurry fun z x =>
          (logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2 * gaussianPDFReal mX vX x
            * gaussianPDFReal mY vY (z - x)) (volume.prod volume) := by
      have hB : Integrable (fun b =>
          (logDeriv (gaussianPDFReal mY vY) b) ^ 2 * gaussianPDFReal mY vY b) volume := by
        refine (integrable_logDeriv_sq_mul_gaussianPDFReal mY hvY).congr
          (Filter.Eventually.of_forall fun b => ?_)
        simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvY, neg_div]; ring
      have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).integrable_comp_of_integrable
        ((integrable_gaussianPDFReal mX vX).mul_prod hB)
      refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Function.uncurry]; ring
    have hP3 : Integrable
        (Function.uncurry fun z x =>
          logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
            * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)))
          (volume.prod volume) := by
      have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).integrable_comp_of_integrable
        ((integrable_logDeriv_mul_gaussianPDFReal (m := mX) hvX).mul_prod
          (integrable_logDeriv_mul_gaussianPDFReal (m := mY) hvY))
      refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp, Function.uncurry]
    -- marginal integrability of inner integrals via Tonelli (`integral_prod_left`)
    have hI1 := hP1.integral_prod_left
    have hI2 := hP2.integral_prod_left
    have hI3 := hP3.integral_prod_left
    -- assemble: lam²·I1 + 2lam(1-lam)·I3 + (1-lam)²·I2
    have hcomb := (((hI1.const_mul (lam ^ 2)).add
      (hI3.const_mul (2 * lam * (1 - lam)))).add (hI2.const_mul ((1 - lam) ^ 2)))
    refine hcomb.congr (Filter.Eventually.of_forall fun z => ?_)
    -- pointwise: (∫ scoreWeight²·condDensityX)·pZ = lam²∫g1 + 2lam(1-lam)∫g3 + (1-lam)²∫g2
    have hpZ : convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z ≠ 0 := by
      rw [convDensityAdd_gaussian_closed_form hvX hvY]
      exact (gaussianPDFReal_pos _ _ z hvXY).ne'
    set pZ := convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z with hpZdef
    -- per-z integrability (in x) of the three g-terms
    obtain ⟨CfX, hCfX⟩ := bdd_gaussianPDFReal mX vX
    obtain ⟨CfY, hCfY⟩ := bdd_gaussianPDFReal mY vY
    obtain ⟨CfY', hCfY'⟩ := bdd_deriv_gaussianPDFReal (m := mY) hvY
    have hg1 : Integrable (fun x =>
        (logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x
          * gaussianPDFReal mY vY (z - x)) volume := by
      have hbase : Integrable (fun x =>
          (logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x) volume := by
        refine (integrable_logDeriv_sq_mul_gaussianPDFReal mX hvX).congr
          (Filter.Eventually.of_forall fun a => ?_)
        simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvX, neg_div]; ring
      exact hbase.mul_bdd ((measurable_gaussianPDFReal mY vY).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable (c := CfY)
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCfY (z - x))
    have hderivY_eq : ∀ w, logDeriv (gaussianPDFReal mY vY) w * gaussianPDFReal mY vY w
        = deriv (gaussianPDFReal mY vY) w := fun w => by
      rw [Common2026.Shannon.logDeriv_gaussianPDFReal hvY,
        Common2026.Shannon.deriv_gaussianPDFReal hvY]
    have hg3 : Integrable (fun x =>
        logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
          * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x))) volume := by
      have hmeas : AEStronglyMeasurable
          (fun x => logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x))
          volume := by
        have heq : (fun x => logDeriv (gaussianPDFReal mY vY) (z - x)
            * gaussianPDFReal mY vY (z - x))
            = (fun x => deriv (gaussianPDFReal mY vY) (z - x)) := by
          funext x; exact hderivY_eq (z - x)
        rw [heq]
        exact ((continuous_deriv_gaussianPDFReal hvY).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable
      exact (integrable_logDeriv_mul_gaussianPDFReal hvX).mul_bdd hmeas (c := CfY')
        (Filter.Eventually.of_forall fun x => by
          rw [hderivY_eq (z - x)]; simpa [Real.norm_eq_abs] using hCfY' (z - x))
    have hg2 : Integrable (fun x =>
        (logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2 * gaussianPDFReal mX vX x
          * gaussianPDFReal mY vY (z - x)) volume := by
      have hpre : Integrable (fun w =>
          (logDeriv (gaussianPDFReal mY vY) w) ^ 2 * gaussianPDFReal mY vY w) volume := by
        refine (integrable_logDeriv_sq_mul_gaussianPDFReal mY hvY).congr
          (Filter.Eventually.of_forall fun b => ?_)
        simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvY, neg_div]; ring
      have hbase : Integrable (fun x =>
          (logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2 * gaussianPDFReal mY vY (z - x)) volume :=
        hpre.comp_sub_left z
      refine (hbase.bdd_mul (measurable_gaussianPDFReal mX vX).aestronglyMeasurable (c := CfX)
        (Filter.Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs] using hCfX x)).congr
        (Filter.Eventually.of_forall fun x => ?_)
      ring
    -- step 1+2: pull `pZ` inside and cancel `condDensityX · pZ = fX·fY(z-·)`
    have hstep12 : (∫ x, (scoreWeight (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) lam z x) ^ 2
        * condDensityX (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) z x ∂volume) * pZ
        = ∫ x, (scoreWeight (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) lam z x) ^ 2
            * (gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)) ∂volume := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [condDensityX, ← hpZdef]
      rw [mul_assoc, div_mul_cancel₀ _ hpZ]
    -- step 3: expand the square into the three g-terms and split the integral
    have hexpand : (fun x => (scoreWeight (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) lam z x) ^ 2
        * (gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)))
        = (fun x => lam ^ 2 * ((logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x
              * gaussianPDFReal mY vY (z - x))
          + 2 * lam * (1 - lam) * (logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
              * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)))
          + (1 - lam) ^ 2 * ((logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2 * gaussianPDFReal mX vX x
              * gaussianPDFReal mY vY (z - x))) := by
      funext x; simp only [scoreWeight]; ring
    simp only [Pi.add_apply, Function.uncurry]
    -- split the expanded integral into the three g-integrals
    have hsplit : (∫ x, (scoreWeight (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) lam z x) ^ 2
        * (gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)) ∂volume)
        = lam ^ 2 * (∫ x, (logDeriv (gaussianPDFReal mX vX) x) ^ 2 * gaussianPDFReal mX vX x
              * gaussianPDFReal mY vY (z - x) ∂volume)
          + 2 * lam * (1 - lam) * (∫ x, logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
              * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)) ∂volume)
          + (1 - lam) ^ 2 * (∫ x, (logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2
              * gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x) ∂volume) := by
      rw [hexpand]
      rw [show (fun x => lam ^ 2 * ((logDeriv (gaussianPDFReal mX vX) x) ^ 2
            * gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x))
          + 2 * lam * (1 - lam) * (logDeriv (gaussianPDFReal mX vX) x * gaussianPDFReal mX vX x
              * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)))
          + (1 - lam) ^ 2 * ((logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2
              * gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)))
          = ((fun x => lam ^ 2 * ((logDeriv (gaussianPDFReal mX vX) x) ^ 2
                * gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x)))
              + (fun x => 2 * lam * (1 - lam) * (logDeriv (gaussianPDFReal mX vX) x
                  * gaussianPDFReal mX vX x
                  * (logDeriv (gaussianPDFReal mY vY) (z - x) * gaussianPDFReal mY vY (z - x)))))
            + (fun x => (1 - lam) ^ 2 * ((logDeriv (gaussianPDFReal mY vY) (z - x)) ^ 2
                * gaussianPDFReal mX vX x * gaussianPDFReal mY vY (z - x))) from rfl,
        integral_add' ((hg1.const_mul (lam ^ 2)).add (hg3.const_mul (2 * lam * (1 - lam))))
            (hg2.const_mul ((1 - lam) ^ 2)),
        integral_add' (hg1.const_mul (lam ^ 2)) (hg3.const_mul (2 * lam * (1 - lam))),
        integral_const_mul, integral_const_mul, integral_const_mul]
    rw [hstep12, hsplit]
  int_fisherX := by
    refine (integrable_logDeriv_sq_mul_gaussianPDFReal mX hvX).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvX, neg_div]
    ring
  int_fisherY := by
    refine (integrable_logDeriv_sq_mul_gaussianPDFReal mY hvY).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvY, neg_div]
    ring
  int_fisherZ := by
    have hvXY : vX + vY ≠ 0 := fun h => hvX (add_eq_zero.mp h).1
    rw [convDensityAdd_gaussian_closed_form hvX hvY]
    refine (integrable_logDeriv_sq_mul_gaussianPDFReal (mX + mY) hvXY).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvXY, neg_div]
    ring
  int_prod1 := by
    -- shear `(z,x) ↦ (x, z - x)` separates `fY(z-x)`:
    -- A a = (logDeriv fX a)²·fX a, B b = fY b
    have hA : Integrable (fun a =>
        (logDeriv (gaussianPDFReal mX vX) a) ^ 2 * gaussianPDFReal mX vX a) volume := by
      refine (integrable_logDeriv_sq_mul_gaussianPDFReal mX hvX).congr
        (Filter.Eventually.of_forall fun a => ?_)
      simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvX, neg_div]; ring
    have hB : Integrable (fun b => gaussianPDFReal mY vY b) volume :=
      integrable_gaussianPDFReal mY vY
    have hsep : Integrable
        (fun p : ℝ × ℝ =>
          ((logDeriv (gaussianPDFReal mX vX) p.1) ^ 2 * gaussianPDFReal mX vX p.1)
            * gaussianPDFReal mY vY p.2) (volume.prod volume) :=
      hA.mul_prod hB
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable hsep
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]
  int_prod2 := by
    -- shear `(z,x) ↦ (x, z-x)`: A a = fX a, B b = (logDeriv fY b)²·fY b
    have hA : Integrable (fun a => gaussianPDFReal mX vX a) volume :=
      integrable_gaussianPDFReal mX vX
    have hB : Integrable (fun b =>
        (logDeriv (gaussianPDFReal mY vY) b) ^ 2 * gaussianPDFReal mY vY b) volume := by
      refine (integrable_logDeriv_sq_mul_gaussianPDFReal mY hvY).congr
        (Filter.Eventually.of_forall fun b => ?_)
      simp only [Common2026.Shannon.logDeriv_gaussianPDFReal hvY, neg_div]; ring
    have hsep : Integrable
        (fun p : ℝ × ℝ =>
          gaussianPDFReal mX vX p.1
            * ((logDeriv (gaussianPDFReal mY vY) p.2) ^ 2 * gaussianPDFReal mY vY p.2))
          (volume.prod volume) :=
      hA.mul_prod hB
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable hsep
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]
    ring
  int_prod3 := by
    -- shear `(z,x) ↦ (x, z-x)`: A a = logDeriv fX a·fX a, B b = logDeriv fY b·fY b
    have hA : Integrable (fun a =>
        logDeriv (gaussianPDFReal mX vX) a * gaussianPDFReal mX vX a) volume :=
      integrable_logDeriv_mul_gaussianPDFReal hvX
    have hB : Integrable (fun b =>
        logDeriv (gaussianPDFReal mY vY) b * gaussianPDFReal mY vY b) volume :=
      integrable_logDeriv_mul_gaussianPDFReal hvY
    have hsep : Integrable
        (fun p : ℝ × ℝ =>
          (logDeriv (gaussianPDFReal mX vX) p.1 * gaussianPDFReal mX vX p.1)
            * (logDeriv (gaussianPDFReal mY vY) p.2 * gaussianPDFReal mY vY p.2))
          (volume.prod volume) :=
      hA.mul_prod hB
    have hcomp := (measurePreserving_prod_sub_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).integrable_comp_of_integrable hsep
    refine hcomp.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, Function.uncurry]

/-! ## 段4 — capstone: density-route convex Fisher bound fires on Gaussians

The witness `isBlachmanConvReady_gaussianPDFReal`, `isRegularDensityV2_gaussianPDFReal`
and Gaussian normalization (`integral_gaussianPDFReal_eq_one`) are fed into the
`@audit:ok` density-route core `convex_fisher_bound_of_ready`, turning the isolated
existence proof of an `IsBlachmanConvReady` inhabitant into an **operational** statement:
the convex Fisher bound `J(Z) ≤ λ² J(X) + (1-λ)² J(Y)` genuinely fires for Gaussian
densities through the density route. This is the first in-tree consumer of the witness.
-/

/-- **Density-route convex Fisher bound for Gaussians (capstone).**

The density-route convex Fisher bound `convex_fisher_bound_of_ready` fires end-to-end
on Gaussian densities: feeding the proven `IsBlachmanConvReady` witness +
`IsRegularDensityV2` instances + Gaussian normalization, every precondition is an
existing `@audit:ok` part, so this is genuine 0-sorry. This wires the previously
isolated witness into an actual consumer, upgrading "an inhabitant exists" to "the
density route computes the bound for Gaussians".

WITNESS STATUS: proof done (genuine 0-sorry). Every argument to
`convex_fisher_bound_of_ready` is an `@audit:ok` part:
`isBlachmanConvReady_gaussianPDFReal` / `isRegularDensityV2_gaussianPDFReal` (this file)
and `integral_gaussianPDFReal_eq_one` (Mathlib).

@audit:ok — independent honesty audit (2026-05-31, commit `de4099b`): single-term
application of the `@audit:ok` core `convex_fisher_bound_of_ready`; the only
hypotheses are regularity (`vX,vY ≠ 0`, `0 ≤ lam ≤ 1`), none carries the inequality
core (structurally bundle-incapable). `#print axioms` →
[propext, Classical.choice, Quot.sound] (sorryAx-free, transitive 0 sorry). -/
@[entry_point]
theorem convex_fisher_bound_gaussian_via_density_route
    (mX mY : ℝ) {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0)
    (lam : ℝ) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    (fisherInfoOfDensity (convDensityAdd (gaussianPDFReal mX vX) (gaussianPDFReal mY vY))).toReal
      ≤ lam ^ 2 * (fisherInfoOfDensity (gaussianPDFReal mX vX)).toReal
        + (1 - lam) ^ 2 * (fisherInfoOfDensity (gaussianPDFReal mY vY)).toReal :=
  convex_fisher_bound_of_ready (gaussianPDFReal mX vX) (gaussianPDFReal mY vY) lam hlo hhi
    (isRegularDensityV2_gaussianPDFReal hvX) (isRegularDensityV2_gaussianPDFReal hvY)
    (integral_gaussianPDFReal_eq_one mX hvX) (integral_gaussianPDFReal_eq_one mY hvY)
    (isBlachmanConvReady_gaussianPDFReal hvX hvY)

/-- **Density-route Gaussian Fisher bound in closed form.**

Specializing `convex_fisher_bound_gaussian_via_density_route` via the Gaussian Fisher
closed form `J(𝒩(m,v)) = 1/v` (`fisherInfoOfDensity_gaussianPDFReal`) and the
convolution closed form `convDensityAdd (gaussian)(gaussian) = gaussian(sum)`, the
density route yields the same `1/(vX+vY) ≤ λ²/vX + (1-λ)²/vY` arithmetic content as the
measure-level closed-form route `stam_convex_fisher_bound_gaussian`. This makes the
agreement of the two routes explicit.

@audit:ok — independent honesty audit (2026-05-31, commit `de4099b`): genuine rewrite
chain (`convDensityAdd_gaussian_closed_form` + `fisherInfoOfDensity_gaussianPDFReal` =
`1/v`, all `@audit:ok`) of the proven density-route bound `hbnd`; no degenerate-equality
exploitation (`1/v` is a genuine positive closed form, `vXY,vX,vY ≠ 0`). The 2-route
agreement claim is accurately scoped — same `1/(vX+vY) ≤ λ²/vX+(1-λ)²/vY` *arithmetic
content* as `stam_convex_fisher_bound_gaussian` (which goes through `stam_fisher_arith`),
not a definitional identity of `fisherInfoOfDensity` vs `fisherInfoOfMeasureV2`.
`#print axioms` → [propext, Classical.choice, Quot.sound] (sorryAx-free). -/
@[entry_point]
theorem convex_fisher_bound_gaussian_via_density_route_closed_form
    (mX mY : ℝ) {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0)
    (lam : ℝ) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) :
    (1 : ℝ) / (vX + vY) ≤ lam ^ 2 * (1 / (vX : ℝ)) + (1 - lam) ^ 2 * (1 / (vY : ℝ)) := by
  have hvXY : vX + vY ≠ 0 := fun h => hvX (add_eq_zero.mp h).1
  have hbnd := convex_fisher_bound_gaussian_via_density_route mX mY hvX hvY lam hlo hhi
  rw [convDensityAdd_gaussian_closed_form hvX hvY,
    fisherInfoOfDensity_gaussianPDFReal _ hvXY,
    fisherInfoOfDensity_gaussianPDFReal _ hvX,
    fisherInfoOfDensity_gaussianPDFReal _ hvY,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity),
    NNReal.coe_add] at hbnd
  exact hbnd

end Common2026.Shannon.EPIBlachmanGaussianWitness
