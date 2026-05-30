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
lemmas (and the linchpin for `int_fisherZ`). 14 of the 19 fields are genuine
(`int_fX/fY`, `bdd_fX/fX'/fY/fY'`, `pos_pZ`, `int_X/Y`, `cond_int`, `int_W`,
`int_fisherX/Y/Z`). The remaining 5 — `int_Wsq`, `int_inner` (quadratic-score
integrability) and `int_prod1/2/3` (non-separable 2D Tonelli terms needing the
shear `measurePreserving_prod_sub`) — are left as `sorry`; see the per-field
`@residual(plan:epi-wall-reattack-plan)` markers.

Independent honesty audit (2026-05-31): structurally GENUINE — the witness is a plain
`structure` literal `{mX mY vX vY} (hvX hvY)`; `IsBlachmanConvReady` carries ONLY
`Integrable`/boundedness/positivity fields (no inequality/equality/value core), so this
is not a load-bearing bundle. The 14 filled fields are genuine (Z-side `pos_pZ`/
`int_fisherZ` route through the sorryAx-free linchpin; `int_fisher{X,Y}` via the public
`integrable_logDeriv_sq_mul_gaussianPDFReal`). The 5 residual fields (`int_Wsq`,
`int_inner`, `int_prod1/2/3`) are all `Integrable (…)` plumbing closable WITHOUT a
Mathlib wall (`measurePreserving_prod_sub` exists; plan §Phase 3c confirms "真壁なし"),
so `@residual(plan:epi-wall-reattack-plan)` is correctly classified (NOT `wall:`).
NON-VACUOUSNESS STATUS: PARTIAL / NOT YET CONFIRMED — because 5 fields remain `sorry`,
this is type-check done but not proof done, so no proven `IsBlachmanConvReady` inhabitant
exists yet. The Phase 3d non-vacuousness caveat is advanced but not discharged; it
resolves only when all 5 residual fields are filled (0 sorry). NOT `@audit:ok`. -/
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
    -- @residual(plan:epi-wall-reattack-plan)
    sorry
  int_inner := by
    -- @residual(plan:epi-wall-reattack-plan)
    sorry
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
    -- @residual(plan:epi-wall-reattack-plan)
    sorry
  int_prod2 := by
    -- @residual(plan:epi-wall-reattack-plan)
    sorry
  int_prod3 := by
    -- @residual(plan:epi-wall-reattack-plan)
    sorry

end Common2026.Shannon.EPIBlachmanGaussianWitness
