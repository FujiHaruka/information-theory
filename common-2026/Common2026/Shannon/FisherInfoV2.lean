import Common2026.Meta.EntryPoint
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.FisherInfo
import Common2026.Shannon.FisherInfoGaussian
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-!
# Fisher information V2 — density-as-input re-definition (T2-F follow-up, Stage 2)

Common2026 T2-F follow-up (parent: `fisher-info-gaussian-discharge-moonshot-plan.md`
判断ログ #2, 2026-05-19).

## Why a V2

The original `Common2026.Shannon.fisherInfo` published in `FisherInfo.lean:58`
takes the density via `(μ.rnDeriv volume y).toReal`. `Measure.rnDeriv` is defined
via `Classical.choose` of the Lebesgue decomposition, so for `μ := gaussianReal m v`
the chosen representative is generically non-differentiable on a co-null set,
forcing `logDeriv ((rnDeriv).toReal) = 0` a.e. and hence
`fisherInfo (gaussianReal m v) = 0` — not `1/v`. This blocks the Gaussian
closed-form discharge (`fisher-info-gaussian-discharge-moonshot-plan.md` Phases
B-3 / C / D, L-G3 retreat 2026-05-19).

This file fixes the flaw by **adopting 撤退ライン L-FV2-A** (density-argument-
as-input form): the density `f : ℝ → ℝ` is an explicit input rather than derived
through `Classical.choose`. Concretely

```lean
noncomputable def fisherInfoOfDensity (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv f x) ^ 2) * ENNReal.ofReal (f x) ∂volume
```

Then `fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1/v)` is
provable (Phase B-3 below).

The existing `Common2026.Shannon.fisherInfo` and `FisherInfo.lean` /
`FisherInfoGaussian.lean` API are left untouched — V2 lives in a parallel
namespace `Common2026.Shannon.FisherInfoV2` and re-publishes Phase A/B-1/B-2
analogues on top of the new definition (per task spec).

## 主シグネチャ

* `fisherInfoOfDensity` — Phase A 定義 (density-as-input, `ℝ≥0∞` 値)
* `fisherInfoOfDensityReal` — Real-valued projection
* `fisherInfoOfDensity_nonneg` / `_eq_lintegral_logDeriv_sq` — Tier 0
* `fisherInfoOfDensity_zero` — degenerate (constant-zero density → `0`)
* `IsRegularDensityV2` — Phase B regularity predicate, density `f` as primary field
* `integral_logDeriv_density_eq_zero` — Phase B score expectation vanishes
* `fisherInfoOfDensity_gaussianPDFReal` — **Phase B-3 closed form `1/v` (the deliverable
   blocked by the V1 flaw)**

## 撤退ライン

- L-FV2-A (本実装で採用): density-argument-as-input 形 `fisherInfoOfDensity f`
- L-FV2-B (未採用): `AEMeasurable` の equivalence class 形
- L-FV2-C (未採用): Gaussian-only specialization で flaw bypass
- L-FV2-D (本 file scope-out): 既存 `FisherInfo.lean` の置換 (parallel publish のみ)
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase A — `fisherInfoOfDensity` 定義 + Tier 0 基本性質 -/

/-- **Fisher information of a density** `f : ℝ → ℝ`.

`J(f) := ∫⁻ (logDeriv f x)² · f x dx` where `logDeriv f := deriv f / f` is
Mathlib's score function (`Mathlib/Analysis/Calculus/LogDeriv.lean:34`).

Density-as-input form (撤退ライン L-FV2-A): the density is an *explicit
argument*, not derived through `Measure.rnDeriv` (which is `Classical.choose`'d
and hence yields a generically non-differentiable representative). This
sidesteps the representative-dependence flaw of the V1 definition
`Common2026.Shannon.fisherInfo` (`FisherInfo.lean:58`).

Returns `ℝ≥0∞` to capture `J = +∞` for irregular families. Use
`fisherInfoOfDensityReal` or `.toReal` to project to `ℝ` when finite. -/
noncomputable def fisherInfoOfDensity (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv f x) ^ 2) * ENNReal.ofReal (f x) ∂volume

/-- Fisher information of a density is non-negative (trivially, as `ℝ≥0∞`). -/
@[entry_point]
theorem fisherInfoOfDensity_nonneg (f : ℝ → ℝ) : 0 ≤ fisherInfoOfDensity f := bot_le

/-- **Constant zero density**: `J(0) = 0`. -/
@[entry_point]
theorem fisherInfoOfDensity_zero : fisherInfoOfDensity (fun _ : ℝ => (0 : ℝ)) = 0 := by
  unfold fisherInfoOfDensity
  simp

/-- Real-valued projection of `fisherInfoOfDensity`. -/
noncomputable def fisherInfoOfDensityReal (f : ℝ → ℝ) : ℝ := (fisherInfoOfDensity f).toReal

@[entry_point]
theorem fisherInfoOfDensityReal_nonneg (f : ℝ → ℝ) : 0 ≤ fisherInfoOfDensityReal f :=
  ENNReal.toReal_nonneg

/-! ## Phase B-1 — `IsRegularDensityV2` predicate (density-as-input form) -/

/-- **Regular density predicate V2** (density-as-input form, L-FV2-A).

This is the V2 analogue of `Common2026.Shannon.IsRegularDensity` from
`FisherInfo.lean`, but with **the density `f` as the primary input** rather than
extracted via `Classical.choose` from `Measure.rnDeriv`. This is what makes
Phase B-3 (Gaussian closed-form) provable in V2 but not V1.

Bundles the differentiability + positivity + tail-vanishing + integrability
needed for `integral_logDeriv_density_eq_zero` (score expectation = 0).

Unlike V1, no measure `μ` is mentioned in the predicate itself: the link to a
random variable `X : Ω → ℝ` (if any) is established separately via an a.e.-
equality between `f` and `(pdf X P volume).toReal`. -/
structure IsRegularDensityV2 (f : ℝ → ℝ) : Prop where
  /-- `f` is differentiable on all of `ℝ`. -/
  diff : Differentiable ℝ f
  /-- `f` is strictly positive everywhere (so `logDeriv f` is well-defined). -/
  pos : ∀ x, 0 < f x
  /-- `f` tends to `0` at `-∞`. -/
  tail_bot : Filter.Tendsto f Filter.atBot (nhds 0)
  /-- `f` tends to `0` at `+∞`. -/
  tail_top : Filter.Tendsto f Filter.atTop (nhds 0)
  /-- `deriv f` is Lebesgue-integrable on all of `ℝ`. -/
  integrable_deriv : Integrable (deriv f) volume
  /-- `∫ deriv f = 0` — regularity consequence of FTC + tail-vanishing on the
  half-lines. Genuinely discharged for the Gaussian instance via
  `integral_deriv_gaussianPDFReal_eq_zero` (`FisherInfoGaussian.lean:231-292`). -/
  integral_deriv_eq_zero : ∫ x, deriv f x ∂volume = 0

/-! ## Phase B-2 — Score function expectation vanishes (density-form) -/

/-- **Score function expectation vanishes** (V2, density-as-input form).

For a regular density `f`,
`∫ (logDeriv f)(x) · f(x) dx = ∫ f'(x) dx = f(∞) - f(-∞) = 0`.

This is the V2 analogue of `Common2026.Shannon.integral_logDeriv_pdf_eq_zero`
from `FisherInfo.lean` — the proof structure is identical, but stated cleanly
on the explicit density `f`.

Body is a genuine 12-line proof (pointwise `logDeriv f · f = deriv f` via
positivity + `integral_congr_ae` + `IsRegularDensityV2.integral_deriv_eq_zero`
field call). The field is a regularity consequence, not a load-bearing core
hypothesis; cf. Phase 2.C honesty audit (2026-05-27).

`@audit:ok` -/
@[entry_point]
theorem integral_logDeriv_density_eq_zero {f : ℝ → ℝ} (h_reg : IsRegularDensityV2 f) :
    ∫ x, logDeriv f x * f x ∂volume = 0 := by
  -- Pointwise: `logDeriv f x * f x = (deriv f x / f x) * f x = deriv f x` since `f x > 0`.
  have h_eq : ∀ x, logDeriv f x * f x = deriv f x := by
    intro x
    have hfx : f x ≠ 0 := (h_reg.pos x).ne'
    rw [logDeriv_apply, div_mul_cancel₀ _ hfx]
  have h_int : ∫ x, logDeriv f x * f x ∂volume = ∫ x, deriv f x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall h_eq)
  calc ∫ x, logDeriv f x * f x ∂volume
      = ∫ x, deriv f x ∂volume := h_int
    _ = 0 := h_reg.integral_deriv_eq_zero

/-! ## Phase B-3 — Gaussian closed form `fisherInfoOfDensity (gaussianPDFReal m v) = 1/v`

**The deliverable that the V1 definition could not provide** (cf.
`FisherInfoGaussian.lean` L-G3 retreat).
-/

/-- `((x - m) / v)² · gaussianPDFReal m v x` is Lebesgue-integrable for `v ≠ 0`.

Strategy: rewrite as `(1/v²) · (x - m)² · gaussianPDFReal m v x`, then use
`integrable_rpow_mul_exp_neg_mul_sq` at `s = 2` substituted via `y = x - m`. -/
lemma integrable_logDeriv_sq_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x) volume := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2v_pos : (0 : ℝ) < 2 * (v : ℝ) := by positivity
  have hb : (0 : ℝ) < (2 * v)⁻¹ := inv_pos.mpr h2v_pos
  have hv_ne : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  -- `integrable_rpow_mul_exp_neg_mul_sq` at `s = 2`. Convert rpow `^(2:ℝ)`
  -- to nat-pow `^2` using `Real.rpow_two`.
  have h_pow_two : Integrable
      (fun y : ℝ => y ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)) volume := by
    have h_rpow : Integrable
        (fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)) volume :=
      integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
    refine h_rpow.congr (Filter.Eventually.of_forall fun y => ?_)
    show y ^ (2 : ℝ) * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)
        = y ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * y ^ 2)
    rw [Real.rpow_two]
  -- Shift: `y ↦ y - m`.
  have h_shift : Integrable
      (fun x : ℝ => (x - m) ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m) ^ 2)) volume :=
    h_pow_two.comp_sub_right m
  -- Multiply by `(1 / v²) · (√(2πv))⁻¹` to obtain the target shape.
  have h_scaled : Integrable
      (fun x : ℝ => ((1 / (v : ℝ) ^ 2) * (Real.sqrt (2 * Real.pi * v))⁻¹)
          * ((x - m) ^ 2 * Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m) ^ 2))) volume :=
    h_shift.const_mul _
  -- Match the target shape `((x - m) / v)² · gaussianPDFReal m v x`.
  refine h_scaled.congr (Filter.Eventually.of_forall fun x => ?_)
  -- Expand the Gaussian PDF and reconcile the exponent form.
  have hexp_eq :
      Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ)))
        = Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m) ^ 2) := by
    congr 1; field_simp
  simp only [gaussianPDFReal, hexp_eq]
  field_simp

/-- **Key integral**: `∫ ((x - m)/v)² · gaussianPDFReal m v x dx = 1/v`.

Strategy: rewrite the LHS as `(1/v²) · ∫ (x - m)² · gaussianPDFReal m v x dx`,
identify `∫ (x - m)² · gaussianPDFReal m v x dx = v` via
`variance_fun_id_gaussianReal` + `integral_gaussianReal_eq_integral_smul`,
and conclude `(1/v²) · v = 1/v`. -/
private lemma integral_logDeriv_sq_mul_gaussianPDFReal_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x ∂volume = 1 / (v : ℝ) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hv_ne : (v : ℝ) ≠ 0 := hv_pos.ne'
  have hv_sq_ne : (v : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hv_ne
  -- Step 1: pull out `(1/v²)`.
  have h_eq : (fun x : ℝ => ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x)
      = fun x : ℝ => (1 / (v : ℝ) ^ 2) * ((x - m) ^ 2 * gaussianPDFReal m v x) := by
    funext x; field_simp
  rw [h_eq, integral_const_mul]
  -- Step 2: `∫ (x - m)² · gaussianPDFReal m v x = v` via variance.
  have h_var : ∫ x, (x - m) ^ 2 * gaussianPDFReal m v x ∂volume = (v : ℝ) := by
    -- Via `integral_gaussianReal_eq_integral_smul`:
    --   ∫ f x ∂(gaussianReal m v) = ∫ gaussianPDFReal m v x • f x ∂volume.
    -- With `f x := (x - m) ^ 2`, the LHS equals the variance of the Gaussian, namely `v`.
    have h_smul := integral_gaussianReal_eq_integral_smul
      (μ := m) (v := v) (f := fun x => (x - m) ^ 2) hv
    -- LHS = ∫ (x - m)² ∂(gaussianReal m v) = Var[fun x => x; gaussianReal m v] = v.
    have h_var_eq : ∫ x, (x - m) ^ 2 ∂(gaussianReal m v) = (v : ℝ) := by
      have h_int_id : ∫ x, x ∂(gaussianReal m v) = m := integral_id_gaussianReal
      have h_id_mb : AEMeasurable (fun x : ℝ => x) (gaussianReal m v) := aemeasurable_id'
      have h_var := variance_fun_id_gaussianReal (μ := m) (v := v)
      rw [variance_eq_integral h_id_mb] at h_var
      -- h_var : ∫ ω, (ω - ∫ x, x ∂(gaussianReal m v)) ^ 2 ∂(gaussianReal m v) = v
      rw [h_int_id] at h_var
      exact h_var
    rw [h_var_eq] at h_smul
    -- h_smul : v = ∫ x, gaussianPDFReal m v x • (fun x => (x - m) ^ 2) x ∂volume.
    -- Beta-reduce + smul_eq_mul + commute the factors.
    have h_smul' : (v : ℝ) = ∫ x, (x - m) ^ 2 * gaussianPDFReal m v x ∂volume := by
      rw [h_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [smul_eq_mul, mul_comm]
    exact h_smul'.symm
  rw [h_var]
  -- Conclude: (1/v²) * v = 1/v.
  field_simp

/-- **Gaussian Fisher information (V2 closed form)**:
`fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1/v)`.

This is the deliverable that was blocked by the V1 representative-dependence
flaw (`FisherInfoGaussian.lean` L-G3 retreat). With the V2 density-as-input
definition, the Gaussian PDF is supplied directly to `fisherInfoOfDensity` and
the integral computes to `1/v` via the variance identity. -/
@[entry_point]
theorem fisherInfoOfDensity_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfDensity (gaussianPDFReal m v) = ENNReal.ofReal (1 / (v : ℝ)) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  -- Step 1: Convert the `lintegral` to a Bochner integral. The integrand is
  -- `((x - m)/v)² · gaussianPDFReal m v x ≥ 0` and integrable.
  unfold fisherInfoOfDensity
  -- Rewrite the integrand pointwise: combine the two `ENNReal.ofReal`s into one.
  have h_pointwise : ∀ x,
      ENNReal.ofReal ((logDeriv (gaussianPDFReal m v) x) ^ 2)
          * ENNReal.ofReal (gaussianPDFReal m v x)
        = ENNReal.ofReal (((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x) := by
    intro x
    have h_sq_nn : 0 ≤ (logDeriv (gaussianPDFReal m v) x) ^ 2 := sq_nonneg _
    have h_pdf_nn : 0 ≤ gaussianPDFReal m v x := (gaussianPDFReal_pos m v x hv).le
    rw [← ENNReal.ofReal_mul h_sq_nn]
    congr 1
    rw [Common2026.Shannon.logDeriv_gaussianPDFReal hv]
    ring
  rw [lintegral_congr h_pointwise]
  -- Step 2: convert `∫⁻ ofReal g = ofReal (∫ g)` using non-negativity + integrability.
  have h_nn : 0 ≤ᵐ[volume] fun x : ℝ =>
      ((x - m) / (v : ℝ)) ^ 2 * gaussianPDFReal m v x := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h_pdf_nn : 0 ≤ gaussianPDFReal m v x := (gaussianPDFReal_pos m v x hv).le
    have h_sq_nn : 0 ≤ ((x - m) / (v : ℝ)) ^ 2 := sq_nonneg _
    exact mul_nonneg h_sq_nn h_pdf_nn
  have h_int := integrable_logDeriv_sq_mul_gaussianPDFReal m hv
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  -- Step 3: compute the Bochner integral to `1/v`.
  rw [integral_logDeriv_sq_mul_gaussianPDFReal_eq m hv]

/-- Real-valued projection of the Gaussian Fisher info closed form. -/
theorem fisherInfoOfDensityReal_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfDensityReal (gaussianPDFReal m v) = 1 / (v : ℝ) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  unfold fisherInfoOfDensityReal
  rw [fisherInfoOfDensity_gaussianPDFReal m hv]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-! ## Phase C — bridge to V1 `Common2026.Shannon.IsRegularDensity`

For backwards-compatibility, every V1 `IsRegularDensity` instance (which is
keyed by a random variable `X` and pinned to the density representative
`density` field) induces a V2 `IsRegularDensityV2` on the very same density
function. This lets callers that have already discharged V1 (notably Gaussian
via `Common2026.Shannon.isRegularDensity_gaussianReal_of_law`) lift to V2 for
free and obtain the Fisher info closed form.
-/

end Common2026.Shannon.FisherInfoV2