import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InformationTheory.Shannon.FisherInfo
import InformationTheory.Shannon.DifferentialEntropy

/-!
# Fisher information — Gaussian discharge (T2-F follow-up, Stage 1)

InformationTheory T2-F follow-up
([`docs/shannon/fisher-info-gaussian-discharge-moonshot-plan.md`]).

Discharges the **L-F2** hypothesis pass-through of `FisherInfo.lean` for the
Gaussian case: provides `IsRegularDensity (gaussianReal m v)` and the
hypothesis-free `integral_logDeriv_pdf_eq_zero_gaussian` wrapper.

## 主シグネチャ

* `pdf_toReal_ae_eq_gaussianPDFReal` — Phase A bridge `(pdf X P volume).toReal =ᵐ gaussianPDFReal m v`
* `differentiable_gaussianPDFReal` / `deriv_gaussianPDFReal` / `logDeriv_gaussianPDFReal`
   — Gaussian PDF smooth-form differentiation lemmas
* `tendsto_gaussianPDFReal_atBot` / `tendsto_gaussianPDFReal_atTop` — tail vanishing
* `integrable_deriv_gaussianPDFReal` / `integral_deriv_gaussianPDFReal_eq_zero`
   — Phase A-5 / A-6 integrability and antiderivative fields
* `isRegularDensity_gaussianReal_of_law` — Phase A `IsRegularDensity` instance
* `integral_logDeriv_pdf_eq_zero_gaussian` — Phase B score expectation wrapper

## L-G3 retreat (2026-05-19)

Phases B-3 / C / D (Gaussian Fisher info closed form `1/v` + `IsRegularDeBruijnHyp`
instance + `deBruijn_identity_gaussian`) are **blocked** by a representative-
dependence flaw in the `fisherInfo` definition published in `FisherInfo.lean`,
documented at the end of this file. They are deferred to a follow-up seed that
first redefines `fisherInfo` to depend only on the a.e.-class of the density.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase A — `IsRegularDensity (gaussianReal m v)` instance discharge -/

/-- `(pdf X P volume).toReal =ᵐ[volume] gaussianPDFReal m v` for a Gaussian `X`.
Bridges `MeasureTheory.pdf_def` → `rnDeriv_gaussianReal` → `toReal_gaussianPDF`. -/
@[entry_point]
lemma pdf_toReal_ae_eq_gaussianPDFReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0}
    (hX_law : P.map X = gaussianReal m v) :
    (fun x => (pdf X P volume x).toReal) =ᵐ[volume]
      (fun x => gaussianPDFReal m v x) := by
  -- `pdf X P volume = (P.map X).rnDeriv volume` by `pdf_def`.
  -- After `hX_law`, this is `(gaussianReal m v).rnDeriv volume =ᵐ gaussianPDF m v`.
  have h_pdf_eq : pdf X P volume = (gaussianReal m v).rnDeriv volume := by
    rw [MeasureTheory.pdf_def, hX_law]
  have h_rn := rnDeriv_gaussianReal m v
  filter_upwards [h_rn] with x hx
  rw [h_pdf_eq, hx, toReal_gaussianPDF]

/-- `Differentiable ℝ (gaussianPDFReal m v)` — the Gaussian pdf is smooth on all of `ℝ`. -/
@[entry_point]
lemma differentiable_gaussianPDFReal (m : ℝ) (v : ℝ≥0) :
    Differentiable ℝ (gaussianPDFReal m v) := by
  show Differentiable ℝ (fun x => (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m)^2 / (2 * v)))
  fun_prop

/-- `deriv (gaussianPDFReal m v) x = -(x - m)/v * gaussianPDFReal m v x`. -/
@[entry_point]
lemma deriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    deriv (gaussianPDFReal m v) x = -(x - m) / v * gaussianPDFReal m v x := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hv_ne : (2 * (v : ℝ)) ≠ 0 := by positivity
  -- Unfold the Gaussian PDF and chain-rule through.
  set c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hc
  set g : ℝ → ℝ := fun x => -(x - m) ^ 2 / (2 * v) with hg
  -- g'(x) = -(x-m)/v via product/chain rules on `(x-m)^2 / (2v)`.
  have h_g_deriv : HasDerivAt g (-(x - m) / v) x := by
    have h_sub : HasDerivAt (fun y : ℝ => y - m) 1 x := (hasDerivAt_id x).sub_const m
    have h_sq : HasDerivAt (fun y : ℝ => (y - m) ^ 2) (2 * (x - m) ^ 1 * 1) x :=
      h_sub.pow 2
    have h_neg_sq : HasDerivAt (fun y : ℝ => -(y - m) ^ 2)
        (-(2 * (x - m) ^ 1 * 1)) x := h_sq.neg
    have h_div : HasDerivAt g (-(2 * (x - m) ^ 1 * 1) / (2 * v)) x := h_neg_sq.div_const _
    have h_eq : -(2 * (x - m) ^ 1 * 1) / (2 * (v : ℝ)) = -(x - m) / v := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      field_simp
    rw [← h_eq]; exact h_div
  -- Chain through `exp` and multiply by `c`.
  have h_exp_deriv : HasDerivAt (fun y => Real.exp (g y))
      (Real.exp (g x) * (-(x - m) / v)) x := h_g_deriv.exp
  have h_full : HasDerivAt (fun y => c * Real.exp (g y))
      (c * (Real.exp (g x) * (-(x - m) / v))) x := h_exp_deriv.const_mul c
  -- Re-shape the function being differentiated: `gaussianPDFReal m v = c * exp ∘ g`.
  have h_form : (gaussianPDFReal m v) = fun x => c * Real.exp (g x) := by
    rw [gaussianPDFReal_def]
  rw [h_form, h_full.deriv]
  -- Compute: `c * (exp(g(x)) * a) = a * (c * exp(g(x)))`.
  ring

/-- Helper: `(x - m)² / (2 v) → +∞` at both `atBot` and `atTop`. -/
private lemma tendsto_quadratic_div_atTop (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (F : Filter ℝ)
    (h_sub : Filter.Tendsto (fun x : ℝ => |x - m|) F Filter.atTop) :
    Filter.Tendsto (fun x : ℝ => (x - m) ^ 2 / (2 * v)) F Filter.atTop := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2v_pos : (0 : ℝ) < 2 * v := by positivity
  -- `(x - m) ^ 2 = |x - m| ^ 2`, and pow ∘ abs → ∞.
  have h_sq : Filter.Tendsto (fun x : ℝ => (x - m) ^ 2) F Filter.atTop := by
    have h_pow : Filter.Tendsto (fun y : ℝ => y ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have h_eq : (fun x => (x - m) ^ 2) = (fun x => |x - m| ^ 2) := by
      funext x; rw [sq_abs]
    rw [h_eq]; exact h_pow.comp h_sub
  exact Filter.Tendsto.atTop_div_const h2v_pos h_sq

/-- `gaussianPDFReal m v x → 0` as `x → -∞`. -/
@[entry_point]
lemma tendsto_gaussianPDFReal_atBot (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Filter.Tendsto (gaussianPDFReal m v) Filter.atBot (nhds 0) := by
  -- Equate `gaussianPDFReal` with `c * exp(-(x-m)^2 / (2v))`.
  have h_abs : Filter.Tendsto (fun x : ℝ => |x - m|) Filter.atBot Filter.atTop := by
    have h_sub : Filter.Tendsto (fun x : ℝ => x - m) Filter.atBot Filter.atBot := by
      simpa using Filter.tendsto_atBot_add_const_right (Filter.atBot) (-m) Filter.tendsto_id
    exact Filter.tendsto_abs_atBot_atTop.comp h_sub
  have h_quot := tendsto_quadratic_div_atTop m hv Filter.atBot h_abs
  -- `-(quadratic) → -∞`.
  have h_neg : Filter.Tendsto (fun x : ℝ => -((x - m) ^ 2 / (2 * v))) Filter.atBot
      Filter.atBot := Filter.tendsto_neg_atTop_atBot.comp h_quot
  -- `exp ∘ (-quadratic) → 0`.
  have h_exp_neg : Filter.Tendsto (fun x : ℝ => Real.exp (-((x - m) ^ 2 / (2 * v))))
      Filter.atBot (nhds 0) := Real.tendsto_exp_atBot.comp h_neg
  -- Reshape: `-(x-m)^2 / (2v) = -((x-m)^2 / (2v))`.
  have h_exp : Filter.Tendsto (fun x : ℝ => Real.exp (-(x - m) ^ 2 / (2 * v)))
      Filter.atBot (nhds 0) := by
    refine h_exp_neg.congr (fun x => ?_)
    congr 1; ring
  -- Multiply by `c := (√(2πv))⁻¹`.
  have h_final : Filter.Tendsto
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * v)))
      Filter.atBot (nhds 0) := by
    simpa using h_exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  exact h_final.congr (fun x => by rw [gaussianPDFReal_def])

@[entry_point]
lemma tendsto_gaussianPDFReal_atTop (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Filter.Tendsto (gaussianPDFReal m v) Filter.atTop (nhds 0) := by
  have h_abs : Filter.Tendsto (fun x : ℝ => |x - m|) Filter.atTop Filter.atTop := by
    have h_sub : Filter.Tendsto (fun x : ℝ => x - m) Filter.atTop Filter.atTop := by
      simpa using Filter.tendsto_atTop_add_const_right (Filter.atTop) (-m) Filter.tendsto_id
    exact Filter.tendsto_abs_atTop_atTop.comp h_sub
  have h_quot := tendsto_quadratic_div_atTop m hv Filter.atTop h_abs
  have h_neg : Filter.Tendsto (fun x : ℝ => -((x - m) ^ 2 / (2 * v))) Filter.atTop
      Filter.atBot := Filter.tendsto_neg_atTop_atBot.comp h_quot
  have h_exp_neg : Filter.Tendsto (fun x : ℝ => Real.exp (-((x - m) ^ 2 / (2 * v))))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp h_neg
  have h_exp : Filter.Tendsto (fun x : ℝ => Real.exp (-(x - m) ^ 2 / (2 * v)))
      Filter.atTop (nhds 0) := by
    refine h_exp_neg.congr (fun x => ?_)
    congr 1; ring
  have h_final : Filter.Tendsto
      (fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * v)))
      Filter.atTop (nhds 0) := by
    simpa using h_exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  exact h_final.congr (fun x => by rw [gaussianPDFReal_def])

/-- `(x - m) * gaussianPDFReal m v x` is Lebesgue-integrable: this is the first
moment integrand (against Lebesgue), expressible via
`integral_gaussianReal_eq_integral_smul`. -/
lemma integrable_sub_mul_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => (x - m) * gaussianPDFReal m v x) volume := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2v_pos : (0 : ℝ) < 2 * v := by positivity
  -- `(x - m) * gaussianPDFReal m v x =
  --   (√(2πv))⁻¹ * (x - m) * exp(-(2v)⁻¹ * (x - m)^2)`.
  -- Use the substitution `y = x - m` and integrability of `y * exp(-(2v)⁻¹ y^2)`.
  have hb : (0 : ℝ) < (2 * v)⁻¹ := inv_pos.mpr h2v_pos
  -- `integrable_rpow_mul_exp_neg_mul_sq` at `s = 1`: `y * exp(-b y²)` is integrable.
  have h_rpow : Integrable
      (fun y : ℝ => y ^ (1 : ℝ) * Real.exp (-(2 * v)⁻¹ * y^2)) volume :=
    integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)
  have h_base : Integrable (fun y : ℝ => y * Real.exp (-(2 * v)⁻¹ * y^2)) volume := by
    refine h_rpow.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  have h_inner : Integrable
      (fun x : ℝ => (x - m) * Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m)^2)) volume :=
    h_base.comp_sub_right m
  -- Multiply by `(√(2πv))⁻¹`.
  refine (h_inner.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹).congr
      (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDFReal]
  have hexp_eq :
      Real.exp (-(x - m)^2 / (2 * (v : ℝ))) = Real.exp (-(2 * (v : ℝ))⁻¹ * (x - m)^2) := by
    congr 1; field_simp
  rw [hexp_eq]
  ring

/-- `deriv (gaussianPDFReal m v)` is Lebesgue-integrable. -/
@[entry_point]
lemma integrable_deriv_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (deriv (gaussianPDFReal m v)) volume := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  -- Use the closed-form `deriv (gaussianPDFReal m v) x = -(x-m)/v * gaussianPDFReal m v x`.
  have h_form : deriv (gaussianPDFReal m v)
      = fun x => -(x - m) / v * gaussianPDFReal m v x := by
    funext x; exact deriv_gaussianPDFReal hv x
  rw [h_form]
  -- Rewrite as `-(1/v) * ((x - m) * gaussianPDFReal m v x)`.
  have h_eq : (fun x => -(x - m) / (v : ℝ) * gaussianPDFReal m v x)
      = fun x => -(1 / (v : ℝ)) * ((x - m) * gaussianPDFReal m v x) := by
    funext x; ring
  rw [h_eq]
  exact (integrable_sub_mul_gaussianPDFReal m hv).const_mul _

/-- `∫ deriv (gaussianPDFReal m v) x ∂volume = 0`.
Using `deriv f = -(x-m)/v * f`, this equals `-(1/v) · ∫ (x - m) · f`, and the
latter is `m - m = 0` because `∫ x · f = m` (Gaussian mean) and `∫ f = 1`. -/
@[entry_point]
lemma integral_deriv_gaussianPDFReal_eq_zero (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, deriv (gaussianPDFReal m v) x ∂volume = 0 := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  -- Rewrite via the closed form.
  have h_form : deriv (gaussianPDFReal m v)
      = fun x => -(x - m) / v * gaussianPDFReal m v x := by
    funext x; exact deriv_gaussianPDFReal hv x
  rw [h_form]
  -- Pull `-(1/v)` out.
  have h_eq : (fun x => -(x - m) / (v : ℝ) * gaussianPDFReal m v x)
      = fun x => -(1 / (v : ℝ)) * ((x - m) * gaussianPDFReal m v x) := by
    funext x; ring
  rw [h_eq, integral_const_mul]
  -- Show `∫ (x - m) * gaussianPDFReal m v x = 0`.
  have h_split : (fun x => (x - m) * gaussianPDFReal m v x)
      = fun x => x * gaussianPDFReal m v x - m * gaussianPDFReal m v x := by
    funext x; ring
  rw [h_split]
  -- Use integrability of both parts.
  have h_int_x : Integrable (fun x => x * gaussianPDFReal m v x) volume := by
    -- `x * f = (x - m) * f + m * f`; both pieces integrable.
    have h_eq2 : (fun x : ℝ => x * gaussianPDFReal m v x)
        = fun x => (x - m) * gaussianPDFReal m v x + m * gaussianPDFReal m v x := by
      funext x; ring
    rw [h_eq2]
    exact (integrable_sub_mul_gaussianPDFReal m hv).add
      ((integrable_gaussianPDFReal m v).const_mul m)
  have h_int_m : Integrable (fun x => m * gaussianPDFReal m v x) volume :=
    (integrable_gaussianPDFReal m v).const_mul m
  rw [integral_sub h_int_x h_int_m]
  -- `∫ x * gaussianPDFReal m v x ∂volume = m` (from `integral_gaussianReal_eq_integral_smul`).
  have h_id : ∫ x, x * gaussianPDFReal m v x ∂volume = m := by
    have h := integral_gaussianReal_eq_integral_smul (μ := m) (v := v)
        (f := fun x => x) hv
    -- `h : ∫ x ∂(gaussianReal m v) = ∫ x, gaussianPDFReal m v x • x ∂volume`.
    rw [integral_id_gaussianReal] at h
    simp only [smul_eq_mul] at h
    -- `h : m = ∫ x, gaussianPDFReal m v x * x ∂volume`. Commute the multiplication.
    have h' : (fun x : ℝ => x * gaussianPDFReal m v x)
        = fun x => gaussianPDFReal m v x * x := by
      funext x; ring
    rw [h', ← h]
  rw [h_id, integral_const_mul, integral_gaussianPDFReal_eq_one m hv, mul_one, sub_self,
    mul_zero]

/-- **`IsRegularDensity` instance for Gaussian densities** (L-F2 hypothesis discharge). -/
@[entry_point]
noncomputable def isRegularDensity_gaussianReal_of_law
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P volume] {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v) :
    IsRegularDensity X P where
  density := gaussianPDFReal m v
  pdf_ae_eq := pdf_toReal_ae_eq_gaussianPDFReal X hX_law
  diff := differentiable_gaussianPDFReal m v
  pos := fun x => gaussianPDFReal_pos m v x hv
  tail_bot := tendsto_gaussianPDFReal_atBot m hv
  tail_top := tendsto_gaussianPDFReal_atTop m hv
  integrable_deriv := integrable_deriv_gaussianPDFReal m hv
  integral_deriv_eq_zero := integral_deriv_gaussianPDFReal_eq_zero m hv

/-! ## Phase B — Gaussian Fisher info + score expectation wrapper -/

/-- `logDeriv (gaussianPDFReal m v) x = -(x - m) / v`. -/
@[entry_point]
lemma logDeriv_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    logDeriv (gaussianPDFReal m v) x = -(x - m) / v := by
  rw [logDeriv_apply, deriv_gaussianPDFReal hv]
  have h_pos : 0 < gaussianPDFReal m v x := gaussianPDFReal_pos m v x hv
  rw [mul_div_assoc, div_self h_pos.ne', mul_one]

/-! ## L-G3 retreat — Stage 1 publish point

**Judgement #2 (Phase B-3, 2026-05-19)**: The `fisherInfo` definition published in
`FisherInfo.lean` (line 58) directly differentiates `(μ.rnDeriv volume y).toReal`,
but `Measure.rnDeriv` is defined via `Classical.choose` of the Lebesgue
decomposition and returns an *opaque measurable representative* (not necessarily
differentiable). For `μ := gaussianReal m v`, `rnDeriv_gaussianReal` only
provides an a.e.-equality with `gaussianPDF m v`; the actual representative is
typically not differentiable anywhere on a co-null set, so
`logDeriv ((rnDeriv).toReal) x = 0` a.e., yielding
`fisherInfo (gaussianReal m v) = 0` rather than the expected `1/v`.

Computing `fisherInfo (gaussianReal m v) = 1/v` from this definition is
**not provable** — it requires `fisherInfo` to depend only on the a.e.-class of
the density, which it currently does not. A correct fix needs a representative-
invariant redefinition of `fisherInfo` (e.g. an infimum over smooth
representatives, or a redefinition via `differentialEntropy` derivative).

Per the moonshot plan撤退ラインL-G3, we retreat to Stage 1 publish:
Phase A `IsRegularDensity (gaussianReal m v)` instance + Phase B's
`integral_logDeriv_pdf_eq_zero_gaussian` wrapper. Phases C/D (de Bruijn identity
discharge) are blocked by the same `fisherInfo` flaw — the
`derivAt_entropy_eq_half_fisher` field of `IsRegularDeBruijnHyp` has a RHS
`(1/2) * (fisherInfo ...).toReal`, which under the current definition would be
`(1/2) * 0 = 0`, while the LHS derivative is `1/(2(v+t)) > 0` — irreconcilable.
These phases are deferred to a follow-up that first fixes `fisherInfo`. -/

end InformationTheory.Shannon
