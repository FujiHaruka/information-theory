import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Donsker–Varadhan variational lower bound (easy direction)

EPI G2 一般形サンドイッチ moonshot (`docs/shannon/epi-g2-general-sandwich-moonshot-plan.md`)
の sub-Phase 2a。相対エントロピー `klDiv` の **変分下界 (Donsker–Varadhan の easy direction)**

  `KL(μ ‖ ν) ≥ ∫ g dμ − log (∫ exp(g) dν)`   (∀ 有界可測 `g`)

を genuine に立てる。Phase 2b (hard direction, sup 到達) は別 task で park 中であり本 file は
**触らない** (easy direction 1 本のみ)。

## 主シグネチャ

* `integral_exp_sub_llr_le` — change-of-measure 補題: `∫ exp(g − llr μ ν) ∂μ ≤ ∫ exp(g) ∂ν`。
* `klDiv_variational_lower_bound` — 主定理: `∫ g dμ − log (∫ exp(g) dν) ≤ (klDiv μ ν).toReal`。

## 証明骨子 (Jensen + 測度変換)

`μ, ν` を確率測度, `μ ≪ ν` とする。`h := fun x => g x − llr μ ν x` に対し凸関数 `exp` の Jensen
(`ConvexOn.map_integral_le`) で `exp (∫ h ∂μ) ≤ ∫ exp h ∂μ`。change-of-measure
(`integral_toReal_rnDeriv_mul` + `rnDeriv_pos`) で `∫ exp h ∂μ ≤ ∫ exp g ∂ν`。よって
`exp (∫ g ∂μ − KL) ≤ ∫ exp g ∂ν`、両辺 log で `∫ g ∂μ − KL ≤ log (∫ exp g ∂ν)`。
`KL = ∫ llr ∂μ` (確率測度, `toReal_klDiv_of_measure_eq`) を使い結論を得る。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real
open scoped ENNReal NNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- change-of-measure 補題: `μ ≪ ν` のとき有界可測 `g` に対し
`∫ exp (g x − llr μ ν x) ∂μ ≤ ∫ exp (g x) ∂ν`。
`llr = log (rnDeriv).toReal`, `rnDeriv > 0` μ-a.e. ゆえ被積分関数は μ-a.e.
`exp (g x) · (rnDeriv μ ν x).toReal⁻¹` に等しく、`integral_toReal_rnDeriv_mul` で
`ν` 上の積分に移すと `exp (g x) · 𝟙 {rnDeriv ≠ 0}` となり、`exp ≥ 0` で `∫ exp g ∂ν` に押さえられる。 -/
theorem integral_exp_sub_llr_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {g : α → ℝ} (hg_meas : Measurable g) {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) :
    ∫ x, Real.exp (g x - llr μ ν x) ∂μ ≤ ∫ x, Real.exp (g x) ∂ν := by
  set r : α → ℝ := fun x => (μ.rnDeriv ν x).toReal with hr
  -- `exp g` is bounded by `exp C`, hence `Real.exp (g ·)` is integrable wrt any probability measure.
  have hexpg_meas : Measurable (fun x => Real.exp (g x)) := Real.measurable_exp.comp hg_meas
  have hbound_exp : ∀ x, ‖Real.exp (g x)‖ ≤ Real.exp C := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((abs_le.mp (hg_bdd x)).2)
  have hint_expg_ν : Integrable (fun x => Real.exp (g x)) ν :=
    Integrable.of_bound hexpg_meas.aestronglyMeasurable (Real.exp C)
      (Filter.Eventually.of_forall hbound_exp)
  -- Step 1: rewrite `exp (g − llr) =ᵐ[μ] exp g · r⁻¹`.
  have hr_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := μ.rnDeriv_pos hμν
  have hr_ne_top : ∀ᵐ x ∂μ, μ.rnDeriv ν x ≠ ∞ := hμν.ae_le (μ.rnDeriv_ne_top ν)
  have hstep1 : ∫ x, Real.exp (g x - llr μ ν x) ∂μ = ∫ x, Real.exp (g x) * (r x)⁻¹ ∂μ := by
    apply integral_congr_ae
    filter_upwards [hr_pos, hr_ne_top] with x hx hx_top
    have hrx : 0 < r x := ENNReal.toReal_pos hx.ne' hx_top
    rw [llr, sub_eq_add_neg, Real.exp_add, ← Real.log_inv, Real.exp_log (by positivity)]
  -- Step 2: change of measure to ν via `integral_toReal_rnDeriv_mul`.
  have hstep2 : ∫ x, Real.exp (g x) * (r x)⁻¹ ∂μ = ∫ x, r x * (Real.exp (g x) * (r x)⁻¹) ∂ν :=
    (integral_toReal_rnDeriv_mul hμν).symm
  -- Step 3: the ν-integrand `r · exp g · r⁻¹ = exp g · (r·r⁻¹)` is ≤ `exp g` pointwise (ν-a.e.).
  have hstep3 : ∫ x, r x * (Real.exp (g x) * (r x)⁻¹) ∂ν ≤ ∫ x, Real.exp (g x) ∂ν := by
    apply integral_mono_ae _ hint_expg_ν
    · filter_upwards with x
      rcases eq_or_ne (r x) 0 with hr0 | hr0
      · simp [hr0, (Real.exp_pos _).le]
      · rw [show r x * (Real.exp (g x) * (r x)⁻¹) = Real.exp (g x) * (r x * (r x)⁻¹) by ring,
          mul_inv_cancel₀ hr0, mul_one]
    · -- integrability of `r · exp g · r⁻¹` wrt ν: bounded by `exp C`.
      apply Integrable.of_bound
        ((((μ.measurable_rnDeriv ν).ennreal_toReal).mul
          (hexpg_meas.mul ((μ.measurable_rnDeriv ν).ennreal_toReal.inv))).aestronglyMeasurable)
        (Real.exp C)
      filter_upwards with x
      have hfactor : (μ.rnDeriv ν x).toReal * (Real.exp (g x) * (μ.rnDeriv ν x).toReal⁻¹)
          = Real.exp (g x) * ((μ.rnDeriv ν x).toReal * (μ.rnDeriv ν x).toReal⁻¹) := by ring
      rw [hfactor]
      rcases eq_or_ne (μ.rnDeriv ν x).toReal 0 with hr0 | hr0
      · rw [hr0, zero_mul, mul_zero, norm_zero]; positivity
      · rw [mul_inv_cancel₀ hr0, mul_one]; exact hbound_exp x
  rw [hstep1, hstep2]
  exact hstep3

/-- **Donsker–Varadhan の easy direction**: `μ, ν` 確率測度, `μ ≪ ν`, `Integrable (llr μ ν) μ`
のとき有界可測 `g` に対し
`∫ g ∂μ − log (∫ exp g ∂ν) ≤ (klDiv μ ν).toReal`。

これは Donsker–Varadhan 変分公式 `KL = sup_g (∫g dμ − log∫exp g dν)` の **easy direction**
(各 `g` で下界、sup は取らない)。Phase 2b の hard direction (sup 到達) は
`docs/shannon/epi-g2-general-sandwich-moonshot-plan.md` §2b で `wall:kl-lower-semicontinuous`
として park 中であり本 file の射程外。-/
theorem klDiv_variational_lower_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    {g : α → ℝ} (hg_meas : Measurable g) {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) :
    (∫ x, g x ∂μ) - Real.log (∫ x, Real.exp (g x) ∂ν) ≤ (klDiv μ ν).toReal := by
  set r : α → ℝ := fun x => (μ.rnDeriv ν x).toReal with hr
  have hexpg_meas : Measurable (fun x => Real.exp (g x)) := Real.measurable_exp.comp hg_meas
  have hbound_exp : ∀ x, ‖Real.exp (g x)‖ ≤ Real.exp C := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((abs_le.mp (hg_bdd x)).2)
  -- `g` and `llr` are integrable wrt the probability measure μ.
  have hint_g_μ : Integrable g μ :=
    Integrable.of_bound hg_meas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hg_bdd x))
  have hint_sub : Integrable (fun x => g x - llr μ ν x) μ := hint_g_μ.sub h_int
  -- `exp (g − llr)` is integrable wrt μ (via change of measure: bounded after pushing to ν).
  have hr_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := μ.rnDeriv_pos hμν
  have hr_ne_top : ∀ᵐ x ∂μ, μ.rnDeriv ν x ≠ ∞ := hμν.ae_le (μ.rnDeriv_ne_top ν)
  have hexp_sub_eq : (fun x => Real.exp (g x - llr μ ν x)) =ᵐ[μ] fun x => Real.exp (g x) * (r x)⁻¹ := by
    filter_upwards [hr_pos, hr_ne_top] with x hx hx_top
    have hrx : 0 < r x := ENNReal.toReal_pos hx.ne' hx_top
    rw [llr, sub_eq_add_neg, Real.exp_add, ← Real.log_inv, Real.exp_log (by positivity)]
  have hint_expsub_μ : Integrable (fun x => Real.exp (g x - llr μ ν x)) μ := by
    rw [integrable_congr hexp_sub_eq]
    rw [← integrable_toReal_rnDeriv_mul_iff hμν (f := fun x => Real.exp (g x) * (r x)⁻¹)]
    apply Integrable.of_bound
      ((((μ.measurable_rnDeriv ν).ennreal_toReal).mul
        (hexpg_meas.mul ((μ.measurable_rnDeriv ν).ennreal_toReal.inv))).aestronglyMeasurable)
      (Real.exp C)
    filter_upwards with x
    have hfactor : (μ.rnDeriv ν x).toReal * (Real.exp (g x) * (μ.rnDeriv ν x).toReal⁻¹)
        = Real.exp (g x) * ((μ.rnDeriv ν x).toReal * (μ.rnDeriv ν x).toReal⁻¹) := by ring
    rw [hfactor]
    rcases eq_or_ne (μ.rnDeriv ν x).toReal 0 with hr0 | hr0
    · rw [hr0, zero_mul, mul_zero, norm_zero]; positivity
    · rw [mul_inv_cancel₀ hr0, mul_one]; exact hbound_exp x
  -- Jensen for the convex `exp`: `exp (∫ (g − llr) ∂μ) ≤ ∫ exp (g − llr) ∂μ`.
  have hjensen : Real.exp (∫ x, (g x - llr μ ν x) ∂μ)
      ≤ ∫ x, Real.exp (g x - llr μ ν x) ∂μ := by
    have := convexOn_exp.map_integral_le (μ := μ) (f := fun x => g x - llr μ ν x)
      (continuousOn_exp.mono (Set.subset_univ _)) isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hint_sub hint_expsub_μ
    simpa using this
  -- Combine with the change-of-measure bound.
  have hcombine : Real.exp (∫ x, (g x - llr μ ν x) ∂μ) ≤ ∫ x, Real.exp (g x) ∂ν :=
    hjensen.trans (integral_exp_sub_llr_le hμν hg_meas hg_bdd)
  -- Take logs.
  have hlog : (∫ x, (g x - llr μ ν x) ∂μ) ≤ Real.log (∫ x, Real.exp (g x) ∂ν) := by
    rw [← Real.log_exp (∫ x, (g x - llr μ ν x) ∂μ)]
    exact Real.log_le_log (Real.exp_pos _) hcombine
  -- `∫ (g − llr) ∂μ = ∫ g ∂μ − KL`.
  rw [integral_sub hint_g_μ h_int] at hlog
  have hKL : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ :=
    toReal_klDiv_of_measure_eq hμν (by rw [measure_univ, measure_univ])
  rw [hKL]
  linarith

end InformationTheory.Shannon
