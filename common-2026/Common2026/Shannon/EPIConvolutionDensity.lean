import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.LConvolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Common2026.Shannon.FisherInfoV2

/-!
# EPI convolution-density foundational brick

A clean, standalone, reusable brick toward the Entropy Power Inequality
(Blachman/Stam route). It introduces the **pointwise real convolution density**
of two densities and exposes its derivative and `logDeriv` (score), the shapes
that `Common2026.Shannon.FisherInfoV2.fisherInfoOfDensity` consumes.

## Why a generic real convolution

Mathlib's density-of-sum result `IndepFun.pdf_add_eq_lconvolution_pdf`
(`Mathlib/Probability/Density.lean:356`) concludes with an a.e. equality whose
RHS is the **Lebesgue convolution** `⋆ₗ` (`MeasureTheory.lconvolution`,
`ℝ≥0∞`-valued), which has **no differentiability lemmas** in Mathlib. The EPI
consumer instead needs a pointwise-differentiable real density so that
`logDeriv` / `deriv` apply directly.

The strategy splits the problem in two:

* **(A) generic `(f, g)` calculus** — define `convDensityReal f g z = ∫ y, f (z - y) * g y`
  as a real Bochner integral and prove differentiability + score quotient with
  pure `hasDerivAt_integral_of_dominated_loc_of_deriv_le` / `logDeriv_apply`. This
  never touches `lconvolution` and is unconditional (modulo honest analytic
  hypotheses). [`convDensityReal`, `hasDerivAt_convDensityReal`,
  `logDeriv_convDensityReal`]
* **(B) the lconvolution↔real bridge** — identify the `.toReal` of the
  pdf-of-sum with `convDensityReal` of the two real densities
  [`pdf_add_toReal_ae_eq_convDensityReal`]. This is the only place `⋆ₗ` is
  touched. When the convolution-product integrability step walls, the retreat
  line **L-Conv-2** localizes it to the named hypothesis `IsPdfAddConvDensityHyp`.

## 撤退ライン

* L-Conv-1 (採用): 微分・score を generic `(f, g)` で立て、`lconvolution` 不接触。
* L-Conv-2 (Phase 2 wall 時): pdf-of-sum 同定を `IsPdfAddConvDensityHyp` に外出し。
-/

namespace InformationTheory.Shannon.EPIConvolutionDensity

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

/-! ## Phase 1 — `convDensityReal` 定義 + helper -/

/-- **Pointwise real convolution of two densities.**
`convDensityReal f g z = ∫ y, f (z - y) * g y dy`. Real-valued so that
`logDeriv` / `deriv` / `HasDerivAt` apply directly (shape-driven for the EPI
consumer `fisherInfoOfDensity`). -/
noncomputable def convDensityReal (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ y, f (z - y) * g y ∂volume

/-- Unfold lemma for `convDensityReal`. -/
theorem convDensityReal_def (f g : ℝ → ℝ) (z : ℝ) :
    convDensityReal f g z = ∫ y, f (z - y) * g y ∂volume := rfl

/-- Positivity of `convDensityReal` carried directly from a positivity assumption
on the underlying integral (honest hypothesis; not proved for general densities).

`@audit:suspect(epi-convolution-density-plan)` -/
theorem convDensityReal_pos {f g : ℝ → ℝ} (z : ℝ)
    (h_pos : 0 < ∫ y, f (z - y) * g y ∂volume) :
    0 < convDensityReal f g z := by
  rw [convDensityReal_def]
  exact h_pos

/-! ## Phase 3 — `hasDerivAt_convDensityReal` (differentiation under the integral) -/

/-- **Derivative of `convDensityReal` under the integral sign.**
Under honest local-domination regularity hypotheses, the derivative of
`convDensityReal f g` at `z₀` is `∫ y, deriv f (z₀ - y) * g y dy`. Pure Mathlib
calculus via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; never touches
`lconvolution`. -/
theorem hasDerivAt_convDensityReal {f g : ℝ → ℝ} (z₀ : ℝ)
    (hf_diff : ∀ x, DifferentiableAt ℝ f x)
    (hF_meas : ∀ᶠ z in nhds z₀,
      AEStronglyMeasurable (fun y => f (z - y) * g y) volume)
    (hF_int : Integrable (fun y => f (z₀ - y) * g y) volume)
    (hF'_meas : AEStronglyMeasurable (fun y => deriv f (z₀ - y) * g y) volume)
    (bound : ℝ → ℝ) (hbound_int : Integrable bound volume)
    (h_bound : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      ‖deriv f (z - y) * g y‖ ≤ bound y) :
    HasDerivAt (convDensityReal f g)
      (∫ y, deriv f (z₀ - y) * g y ∂volume) z₀ := by
  have hball : Metric.ball z₀ 1 ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  have h_diff : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z => f (z - y) * g y) (deriv f (z - y) * g y) z := by
    refine Filter.Eventually.of_forall (fun y z _ => ?_)
    have hfz : HasDerivAt f (deriv f (z - y)) (z - y) := (hf_diff (z - y)).hasDerivAt
    exact (hfz.comp_sub_const z y).mul_const (g y)
  have key :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun z y => f (z - y) * g y)
      (F' := fun z y => deriv f (z - y) * g y) (bound := bound)
      hball hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact key.2

/-! ## Phase 4 — `logDeriv_convDensityReal` (score quotient form) -/

/-- **Score (`logDeriv`) of `convDensityReal`.**
Given the derivative from Phase 3 as a hypothesis and a positive denominator,
the score is the quotient `(∫ deriv f (z₀-y) g y) / (∫ f (z₀-y) g y)`. Pure
calculus via `logDeriv_apply`. -/
theorem logDeriv_convDensityReal {f g : ℝ → ℝ} (z₀ : ℝ)
    (h_deriv : HasDerivAt (convDensityReal f g)
      (∫ y, deriv f (z₀ - y) * g y ∂volume) z₀)
    (_h_pos : 0 < convDensityReal f g z₀) :
    logDeriv (convDensityReal f g) z₀
      = (∫ y, deriv f (z₀ - y) * g y ∂volume)
          / (∫ y, f (z₀ - y) * g y ∂volume) := by
  rw [logDeriv_apply, h_deriv.deriv, convDensityReal_def]

/-! ## Phase 2 — lconvolution↔real bridge -/

/-- **[L-Conv-2 named retreat hypothesis].**
The density of `X + Y` agrees a.e. with the `convDensityReal` of the two real
densities. The full identification is discharged unconditionally below
(`pdf_add_toReal_ae_eq_convDensityReal`); this predicate is published as a
convenient named form for callers that prefer to pass it as a hypothesis. -/
def IsPdfAddConvDensityHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  (fun z => (pdf (X + Y) P volume z).toReal)
    =ᵐ[volume] convDensityReal
      (fun x => (pdf X P volume x).toReal)
      (fun y => (pdf Y P volume y).toReal)

/-- **Pointwise lconvolution↔real identity.**
For each `z`, the real Bochner convolution of the two real densities equals the
`.toReal` of the Lebesgue convolution of the (`ℝ≥0∞`-valued) densities.

Crucially this uses `integral_toReal` (which needs only `AEMeasurable` of the
`ℝ≥0∞` integrand plus a.e.-pointwise finiteness), **not**
`ofReal_integral_eq_lintegral_ofReal` (which would demand Bochner integrability
of the convolution product). That sidesteps the convolution-integrability wall
flagged in the plan's 落とし穴 (b). -/
theorem convDensityReal_toReal_pdf_eq_lconvolution
    {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (P : Measure Ω)
    [IsFiniteMeasure P] [HasPDF X P volume] [HasPDF Y P volume] (z : ℝ) :
    convDensityReal (fun x => (pdf X P volume x).toReal)
        (fun y => (pdf Y P volume y).toReal) z
      = ((pdf X P volume ⋆ₗ[volume] pdf Y P volume) z).toReal := by
  rw [convDensityReal_def]
  have hprod : (fun y => (pdf X P volume (z - y)).toReal * (pdf Y P volume y).toReal)
      = fun y => (pdf X P volume (z - y) * pdf Y P volume y).toReal := by
    funext y; rw [ENNReal.toReal_mul]
  rw [hprod]
  have hmeasX : Measurable (pdf X P volume) := measurable_pdf X P volume
  have hmeasY : Measurable (pdf Y P volume) := measurable_pdf Y P volume
  have hmeas : AEMeasurable (fun y => pdf X P volume (z - y) * pdf Y P volume y) volume := by
    apply AEMeasurable.mul
    · exact (hmeasX.comp (measurable_const.sub measurable_id)).aemeasurable
    · exact hmeasY.aemeasurable
  have hYfin : ∀ᵐ y ∂volume, pdf Y P volume y < ∞ :=
    ae_lt_top hmeasY (by rw [pdf.lintegral_eq_measure_univ]; exact measure_ne_top P _)
  have hXfin0 : ∀ᵐ x ∂volume, pdf X P volume x < ∞ :=
    ae_lt_top hmeasX (by rw [pdf.lintegral_eq_measure_univ]; exact measure_ne_top P _)
  have hmp : MeasurePreserving (fun t => z - t) volume volume :=
    Measure.measurePreserving_sub_left volume z
  have hXfin : ∀ᵐ y ∂volume, pdf X P volume (z - y) < ∞ :=
    hmp.quasiMeasurePreserving.ae hXfin0
  have hfin : ∀ᵐ y ∂volume, (pdf X P volume (z - y) * pdf Y P volume y) < ∞ := by
    filter_upwards [hXfin, hYfin] with y hx hy using ENNReal.mul_lt_top hx hy
  rw [integral_toReal hmeas hfin]
  congr 1
  rw [lconvolution_def, ← lintegral_sub_left_eq_self
    (fun y => pdf X P volume y * pdf Y P volume (-y + z)) z]
  apply lintegral_congr
  intro y
  have hz : -(z - y) + z = y := by ring
  rw [hz]

/-- **The lconvolution↔real bridge (unconditional).**
The `.toReal` of the density of an `IndepFun` sum agrees a.e. with the
`convDensityReal` of the two real densities. Starting point:
`IndepFun.pdf_add_eq_lconvolution_pdf`. -/
theorem pdf_add_toReal_ae_eq_convDensityReal
    {Ω : Type*} [MeasurableSpace Ω] {X Y : Ω → ℝ} {P : Measure Ω}
    [IsFiniteMeasure P] [HasPDF X P volume] [HasPDF Y P volume]
    (hXY : IndepFun X Y P) :
    (fun z => (pdf (X + Y) P volume z).toReal)
      =ᵐ[volume] convDensityReal
        (fun x => (pdf X P volume x).toReal)
        (fun y => (pdf Y P volume y).toReal) := by
  have h_lconv := hXY.pdf_add_eq_lconvolution_pdf (μ := volume)
  filter_upwards [h_lconv] with z hz
  rw [hz, convDensityReal_toReal_pdf_eq_lconvolution X Y P z]

/-- The named retreat predicate `IsPdfAddConvDensityHyp` is discharged
unconditionally for `IndepFun` summands with densities. -/
theorem isPdfAddConvDensityHyp_of_indepFun
    {Ω : Type*} [MeasurableSpace Ω] {X Y : Ω → ℝ} {P : Measure Ω}
    [IsFiniteMeasure P] [HasPDF X P volume] [HasPDF Y P volume]
    (hXY : IndepFun X Y P) :
    IsPdfAddConvDensityHyp X Y P :=
  pdf_add_toReal_ae_eq_convDensityReal hXY

end InformationTheory.Shannon.EPIConvolutionDensity
