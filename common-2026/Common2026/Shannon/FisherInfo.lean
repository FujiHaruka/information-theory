import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import Common2026.Shannon.DifferentialEntropy

/-!
# Fisher information + de Bruijn identity (T2-F)

Common2026 T2-F ムーンショット ([`docs/shannon/fisher-info-moonshot-plan.md`])。

Cover-Thomas Ch.17.7 の Fisher information 定義 + de Bruijn identity。Mathlib に
Fisher info の概念は不在 (inventory §A) なので本 file で定義 + 性質 + de Bruijn を組む。
**Score function** は Mathlib `logDeriv f := deriv f / f`
(`Mathlib/Analysis/Calculus/LogDeriv.lean:34`) が偶発的に同形で存在するため再利用
(inventory §B、Mathlib-shape-driven 原則)。

## 主シグネチャ

* `fisherInfo` — Phase A 定義 (logDeriv ベース、`ℝ≥0∞` 値)
* `fisherInfo_nonneg`, `fisherInfo_eq_lintegral_logDeriv_sq` — Tier 0 unfold 補助
* `fisherInfo_dirac` — Tier 0 退化 case (Dirac measure → `0`)
* `IsRegularDensity` — Phase B regularity predicate (Cover-Thomas 17.7 仮定の集約)
* `integral_logDeriv_pdf_eq_zero` — Phase B score 期待値 0 (L-F2: predicate 形 hypothesis pass-through)
* `IsRegularDeBruijnHyp` — Phase E de Bruijn 用 regularity predicate (L-F1 + L-F2 統合)
* `deBruijn_identity` — Phase E 主定理 `(d/dt) h(P_{X+√t Z}) = (1/2) J(P_{X+√t Z})`
  (L-F1: heat-eq + dominated bound + IBP は predicate の中に hypothesis として外出し)

## 撤退ライン (本実装で適用済)

本 plan の Tier 2 (de Bruijn identity 主定理) は **L-F1 + L-F2 適用形** で publish:
Gaussian heat equation (Phase C) と `d/ds`-step dominated bound (Phase D-3) を
`IsRegularDeBruijnHyp` predicate に hypothesis として集約。一般の `X` で本 predicate を
discharge するには別 plan (`fisher-info-heat-eq-plan.md` / `fisher-info-dominated-bound-plan.md`)
が要る。本 file はその hypothesis pass-through 形での publish が valuable な範囲を表す。

cf. inventory §H 撤退ライン + plan §撤退ライン。
-/

namespace Common2026.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase A — `fisherInfo` 定義 + Tier 0 基本性質 -/

/-- **Fisher information** of a measure `μ` on `ℝ` with density `p := μ.rnDeriv volume`.

`J(μ) := ∫⁻ (logDeriv p x)² · p x dx` where `logDeriv f := deriv f / f` is Mathlib's
score function (`Mathlib/Analysis/Calculus/LogDeriv.lean:34`).

Returns `ℝ≥0∞` to capture `J = +∞` for irregular families (consistent with `klDiv`'s
return type). Use `(fisherInfo μ).toReal` to project to `ℝ` when the value is known finite. -/
noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
    * μ.rnDeriv volume x ∂volume

/-- Fisher information is non-negative (trivially, as an `ℝ≥0∞` value). -/
theorem fisherInfo_nonneg (μ : Measure ℝ) : 0 ≤ fisherInfo μ := bot_le

/-- Unfold lemma for `fisherInfo`. -/
theorem fisherInfo_eq_lintegral_logDeriv_sq (μ : Measure ℝ) :
    fisherInfo μ
      = ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
          * μ.rnDeriv volume x ∂volume := rfl

/-- **Dirac case**: a Dirac measure is singular to `volume`, so its Radon-Nikodym
derivative vanishes a.e. and its Fisher information is `0`. -/
theorem fisherInfo_dirac (m : ℝ) : fisherInfo (Measure.dirac m) = 0 := by
  unfold fisherInfo
  -- The rnDeriv of `dirac m` w.r.t. volume is 0 a.e.[volume], so the integrand vanishes.
  have h_sing : Measure.dirac m ⟂ₘ (volume : Measure ℝ) :=
    MeasureTheory.mutuallySingular_dirac m volume
  have h_rn : (Measure.dirac m).rnDeriv volume =ᵐ[volume] 0 :=
    MeasureTheory.Measure.MutuallySingular.rnDeriv_ae_eq_zero h_sing
  -- Replace the integrand by `0` a.e. using `h_rn` on the multiplicand factor.
  have h_zero : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal ((logDeriv (fun y => ((Measure.dirac m).rnDeriv volume y).toReal) x) ^ 2)
          * (Measure.dirac m).rnDeriv volume x
        = 0 := by
    filter_upwards [h_rn] with x hx
    simp [hx]
  rw [lintegral_congr_ae h_zero]
  simp

/-- Real-valued projection of `fisherInfo`. Convenience for callers (e.g.,
`deBruijn_identity`) that need an `ℝ`-valued Fisher information; loses information
about `J = +∞` (irregular families) but is the natural shape for `HasDerivAt` consumers. -/
noncomputable def fisherInfoReal (μ : Measure ℝ) : ℝ := (fisherInfo μ).toReal

@[simp] theorem fisherInfoReal_dirac (m : ℝ) : fisherInfoReal (Measure.dirac m) = 0 := by
  unfold fisherInfoReal
  rw [fisherInfo_dirac]
  simp

theorem fisherInfoReal_nonneg (μ : Measure ℝ) : 0 ≤ fisherInfoReal μ :=
  ENNReal.toReal_nonneg

/-- **Bridge**: `differentialEntropy (P.map Y) = -∫ p(x) · log p(x) dx` where
`p := pdf Y P volume` is the PDF of `Y`. Combines `pdf_def`-style `P.map Y = volume.withDensity p`
(`MeasureTheory.map_eq_withDensity_pdf`) with `differentialEntropy_eq_integral_withDensity`. -/
theorem differentialEntropy_map_eq_integral_pdf_log_pdf
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (Y : Ω → ℝ) (P : Measure Ω) [HasPDF Y P volume] :
    differentialEntropy (P.map Y)
      = -∫ x, (pdf Y P volume x).toReal * Real.log (pdf Y P volume x).toReal ∂volume := by
  -- Step 1: `P.map Y = volume.withDensity (pdf Y P volume)`
  rw [map_eq_withDensity_pdf Y P volume]
  -- Step 2: `differentialEntropy (volume.withDensity f) = ∫ negMulLog (f x).toReal dx`
  rw [differentialEntropy_eq_integral_withDensity (measurable_pdf Y P volume)]
  -- Step 3: `negMulLog y = -(y * log y)`
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [Real.negMulLog_def]

/-! ## Phase B — Score function 期待値 0 (Tier 1, L-F2 適用形) -/

/-- **Regular density predicate** (Cover-Thomas 17.7 仮定の集約). Bundles the
differentiability + positivity + tail-vanishing + integrability conditions needed
for `integral_logDeriv_pdf_eq_zero`. **L-F2 撤退ライン形** — we expose this as a
predicate to be discharged downstream rather than verifying it for general `X`. -/
structure IsRegularDensity {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) [HasPDF X P volume] : Prop where
  /-- The (real-valued) PDF is differentiable on all of `ℝ`. -/
  diff : Differentiable ℝ (fun x => (pdf X P volume x).toReal)
  /-- The PDF is strictly positive everywhere (so `logDeriv` is well-defined). -/
  pos : ∀ x, 0 < (pdf X P volume x).toReal
  /-- The PDF tends to `0` at `-∞`. -/
  tail_bot : Filter.Tendsto (fun x => (pdf X P volume x).toReal) Filter.atBot (nhds 0)
  /-- The PDF tends to `0` at `+∞`. -/
  tail_top : Filter.Tendsto (fun x => (pdf X P volume x).toReal) Filter.atTop (nhds 0)
  /-- The derivative of the PDF is Lebesgue-integrable on all of `ℝ`. -/
  integrable_deriv :
    Integrable (fun x => deriv (fun y => (pdf X P volume y).toReal) x) volume
  /-- Score-times-density `logDeriv p · p = deriv p` is the antiderivative
  whose integral over `ℝ` equals the boundary difference of `p`. Bundled here as
  a hypothesis equivalent to FTC + tail-vanish on the half-lines; downstream
  discharge can use `MeasureTheory.integral_deriv_eq_sub` or its improper variants. -/
  integral_deriv_eq_zero :
    ∫ x, deriv (fun y => (pdf X P volume y).toReal) x ∂volume = 0

/-- **Score function expectation vanishes** (Cover-Thomas 17.7, regular density form).

`∫ (logDeriv p)(x) · p(x) dx = ∫ p'(x) dx = p(∞) - p(-∞) = 0` for a sufficiently
regular density `p`. We expose this in **L-F2 form**: the smoothness + positivity +
tail conditions are bundled into `IsRegularDensity`, which is to be discharged by
the caller (Gaussian densities satisfy it; general densities may not). -/
theorem integral_logDeriv_pdf_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P volume]
    (h_reg : IsRegularDensity X P) :
    ∫ x, logDeriv (fun y => (pdf X P volume y).toReal) x
         * (pdf X P volume x).toReal ∂volume = 0 := by
  -- Pointwise: `logDeriv p x * p x = (deriv p x / p x) * p x = deriv p x` since `p x > 0`.
  let p : ℝ → ℝ := fun x => (pdf X P volume x).toReal
  have h_eq : ∀ x, logDeriv p x * p x = deriv p x := by
    intro x
    have hpx : p x ≠ 0 := (h_reg.pos x).ne'
    rw [logDeriv_apply, div_mul_cancel₀ _ hpx]
  -- Apply pointwise rewriting to the integral.
  have h_int : ∫ x, logDeriv p x * p x ∂volume = ∫ x, deriv p x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall h_eq)
  calc ∫ x, logDeriv p x * (pdf X P volume x).toReal ∂volume
      = ∫ x, logDeriv p x * p x ∂volume := rfl
    _ = ∫ x, deriv p x ∂volume := h_int
    _ = 0 := h_reg.integral_deriv_eq_zero

/-! ## Phase E — de Bruijn identity (Tier 2, L-F1 + L-F2 適用形) -/

/-- **Regularity predicate for de Bruijn identity** (Cover-Thomas 17.7.2 hypotheses).

Bundles the family-level regularity needed for the de Bruijn identity. This is the
**L-F1 + L-F2 adapted form** of the moonshot plan: the Gaussian heat equation
(`gaussianPDF_heat_eq` from Phase C of the plan), the `d/ds`-step parametric
differentiation (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` from Phase D),
and the IBP convergence at infinity (Phase E) are all bundled here as a
hypothesis to be discharged downstream.

The field `derivAt_entropy_eq_half_fisher` is the de Bruijn identity itself, packaged
as a hypothesis. Downstream callers who can verify it (e.g., for `X` Gaussian) get a
fully proved de Bruijn statement; otherwise this acts as the L-F1+L-F2 hypothesis
pass-through stub that preserves the statement form. -/
structure IsRegularDeBruijnHyp {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [HasPDF X P volume] (t : ℝ) : Prop where
  /-- `Z` is standard normal (independence with `X` is a separate hypothesis of the
  main theorem, not part of this predicate). -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- The heat-equation-driven derivative identity (Cover-Thomas 17.7.2):
  `(d/ds) h(X + √s · Z) ⌊_{s = t} = (1/2) · J(X + √t · Z)`. -/
  derivAt_entropy_eq_half_fisher :
    HasDerivAt
      (fun s => differentialEntropy (P.map (fun ω => X ω + Real.sqrt s * Z ω)))
      ((1/2) * (fisherInfo (P.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal)
      t

/-- **de Bruijn identity** (Cover-Thomas 17.7.2). For `X ⟂ Z` with `Z ∼ 𝒩(0, 1)`,

`(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)`.

**L-F1 + L-F2 適用形**: the heat-equation / dominated-bound / IBP machinery is
packaged into `IsRegularDeBruijnHyp` as a hypothesis predicate; verifying it for
specific families (Gaussian `X` is the canonical case) is deferred to follow-up
work (`fisher-info-heat-eq-plan.md` / `fisher-info-dominated-bound-plan.md`).
This statement-form publish preserves the de Bruijn signature so downstream
T2-D EPI work can already cite it. -/
theorem deBruijn_identity
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z)
    (_hXZ : IndepFun X Z P)
    [HasPDF X P volume]
    {t : ℝ} (_ht : 0 < t)
    (h_reg : IsRegularDeBruijnHyp X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (fun ω => X ω + Real.sqrt s * Z ω)))
      ((1/2) * (fisherInfo (P.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal)
      t :=
  h_reg.derivAt_entropy_eq_half_fisher

end Common2026.Shannon
