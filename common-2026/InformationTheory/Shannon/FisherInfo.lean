import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Dirac
import InformationTheory.Shannon.DifferentialEntropy

/-!
# Fisher information density helpers (T2-F)

InformationTheory T2-F ムーンショット ([`docs/shannon/fisher-info-moonshot-plan.md`])。

**V1 `fisherInfo` was DELETED on 2026-05-20** (representative-dependence flaw:
returned `0` for Gaussians). The correct Fisher information lives in
`FisherInfoV2.lean` (`fisherInfoOfDensity`) and `FisherInfoV2DeBruijn.lean`
(`fisherInfoOfMeasureV2` + V2 de Bruijn identity); the EPI/Stam scaffolding was
migrated to those. This file retains only the **density-based, `fisherInfo`-free**
helpers below.

**Score function** は Mathlib `logDeriv f := deriv f / f`
(`Mathlib/Analysis/Calculus/LogDeriv.lean:34`) が偶発的に同形で存在するため再利用
(inventory §B、Mathlib-shape-driven 原則)。

## 主シグネチャ (retained, density-based)

* `IsRegularDensity` — Phase B regularity predicate (Cover-Thomas 17.7 仮定の集約)
* `integral_logDeriv_pdf_eq_zero` — Phase B score 期待値 0 (L-F2: predicate 形 hypothesis pass-through)
* `differentialEntropy_map_eq_integral_pdf_log_pdf` — pdf-log-pdf bridge

## DELETED 2026-05-20 (V1 `fisherInfo` flaw)

`fisherInfo`, `fisherInfo_nonneg`, `fisherInfo_eq_lintegral_logDeriv_sq`,
`fisherInfo_dirac`, `fisherInfoReal`, `fisherInfoReal_dirac`,
`fisherInfoReal_nonneg`, `IsRegularDeBruijnHyp`, `deBruijn_identity` — all keyed on
the buggy V1 `fisherInfo`. Replaced by `FisherInfoV2` / `FisherInfoV2DeBruijn`.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase A — V1 `fisherInfo` (DELETED 2026-05-20)

The V1 `fisherInfo (μ : Measure ℝ) : ℝ≥0∞` definition and its companions
(`fisherInfo_nonneg`, `fisherInfo_eq_lintegral_logDeriv_sq`, `fisherInfo_dirac`,
`fisherInfoReal`, `fisherInfoReal_dirac`, `fisherInfoReal_nonneg`) were **deleted**
on 2026-05-20. They reasoned about the `Classical.choose` Lebesgue-decomposition
representative of `μ.rnDeriv volume`, which is non-differentiable a.e., so
`logDeriv` collapsed to `0` a.e. — giving the wrong value `fisherInfo (gaussianReal
m v) = 0` instead of `1/v` (representative-dependence flaw, see
`FisherInfoGaussian.lean` Judgement #2). The correct, a.e.-class-invariant version
is `InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity` (gives `1/v` for
Gaussians), with the measure-keyed wrapper
`InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2` in `FisherInfoV2DeBruijn.lean`.
The EPI/Stam scaffolding predicates were migrated to `fisherInfoOfMeasureV2`. -/

/-! ## Phase B — Score function 期待値 0 (Tier 1, L-F2 適用形) -/

/-- **Regular density predicate** (Cover-Thomas 17.7 仮定の集約). Bundles the
differentiability + positivity + tail-vanishing + integrability conditions needed
for `integral_logDeriv_pdf_eq_zero`. **L-F2 撤退ライン形** — we expose this as a
predicate to be discharged downstream rather than verifying it for general `X`.

**a.e.-representative form** (back-ported 2026-05-19 for Gaussian discharge):
since `pdf X P volume` is only defined up to a.e. equivalence (`MeasureTheory.pdf`
returns a specific representative of an a.e. class), pointwise smoothness /
positivity conditions cannot be discharged for general `X` even when a smooth
representative exists. The structure exposes a chosen smooth representative
`density : ℝ → ℝ` together with an a.e.-equality `pdf_ae_eq` and lifts the
pointwise regularity conditions to `density`. Downstream discharge (e.g. Gaussian
in `FisherInfoGaussian.lean`) provides `density := gaussianPDFReal m v`. -/
structure IsRegularDensity {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) [HasPDF X P volume] where
  /-- A smooth representative of the PDF (`(pdf X P volume x).toReal` is a.e.-equal
  to this representative, see `pdf_ae_eq`). -/
  density : ℝ → ℝ
  /-- `(pdf X P volume).toReal` equals the smooth representative `density` a.e. -/
  pdf_ae_eq : (fun x => (pdf X P volume x).toReal) =ᵐ[volume] density
  /-- The representative is differentiable on all of `ℝ`. -/
  diff : Differentiable ℝ density
  /-- The representative is strictly positive everywhere (so `logDeriv` is well-defined). -/
  pos : ∀ x, 0 < density x
  /-- The representative tends to `0` at `-∞`. -/
  tail_bot : Filter.Tendsto density Filter.atBot (nhds 0)
  /-- The representative tends to `0` at `+∞`. -/
  tail_top : Filter.Tendsto density Filter.atTop (nhds 0)
  /-- The derivative of the representative is Lebesgue-integrable on all of `ℝ`. -/
  integrable_deriv : Integrable (deriv density) volume
  /-- Score-times-density `logDeriv p · p = deriv p` is the antiderivative
  whose integral over `ℝ` equals the boundary difference of `p`. Bundled here as
  a regularity consequence equivalent to FTC + tail-vanish on the half-lines;
  downstream discharge can use `MeasureTheory.integral_deriv_eq_sub` or its
  improper variants. Genuinely discharged for the Gaussian instance at
  `FisherInfoGaussian.lean:284-292` via the closed-form lemma
  `integral_deriv_gaussianPDFReal_eq_zero` (~45 lines). -/
  integral_deriv_eq_zero : ∫ x, deriv density x ∂volume = 0

/-- **Score function expectation vanishes** (Cover-Thomas 17.7, regular density form).

For the smooth representative `density` provided by `IsRegularDensity`,
`∫ (logDeriv density)(x) · density(x) dx = ∫ density'(x) dx = density(∞) - density(-∞) = 0`.

We expose this in **L-F2 form**: the smoothness + positivity + tail conditions are
bundled into `IsRegularDensity`, which is to be discharged by the caller (Gaussian
densities satisfy it; general densities may not). Stated on the smooth
representative `h_reg.density`; combine with `h_reg.pdf_ae_eq` if needed to
re-cast in terms of `(pdf X P volume).toReal` via an a.e.-integral congruence.

Body is a genuine 13-line proof (pointwise `logDeriv f · f = deriv f` via positivity
+ `integral_congr_ae` + `IsRegularDensity.integral_deriv_eq_zero` field call). The
field itself is a regularity consequence (FTC + tail-vanishing on the half-lines),
not a load-bearing core hypothesis; cf. Phase 2.C honesty audit (2026-05-27).

`@audit:ok` -/
@[entry_point]
theorem integral_logDeriv_pdf_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P volume]
    (h_reg : IsRegularDensity X P) :
    ∫ x, logDeriv h_reg.density x * h_reg.density x ∂volume = 0 := by
  -- Pointwise: `logDeriv g x * g x = (deriv g x / g x) * g x = deriv g x` since `g x > 0`.
  set g : ℝ → ℝ := h_reg.density with hg
  have h_eq : ∀ x, logDeriv g x * g x = deriv g x := by
    intro x
    have hgx : g x ≠ 0 := (h_reg.pos x).ne'
    rw [logDeriv_apply, div_mul_cancel₀ _ hgx]
  -- Apply pointwise rewriting to the integral.
  have h_int : ∫ x, logDeriv g x * g x ∂volume = ∫ x, deriv g x ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall h_eq)
  calc ∫ x, logDeriv g x * g x ∂volume
      = ∫ x, deriv g x ∂volume := h_int
    _ = 0 := h_reg.integral_deriv_eq_zero

/-! ## Phase E — V1 de Bruijn identity (DELETED 2026-05-20)

The V1 `IsRegularDeBruijnHyp` predicate and `deBruijn_identity` theorem were
**deleted** on 2026-05-20: their RHS used the (deleted, buggy) V1 `fisherInfo`,
which evaluates to `0` for Gaussians. The correct V2 equivalents
`InformationTheory.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2` and
`InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2` (RHS keyed on
`fisherInfoOfDensityReal`, evaluating to `1/v` for Gaussians) live in
`FisherInfoV2DeBruijn.lean`, together with the hypothesis-free Gaussian discharge
`deBruijn_identity_v2_gaussian`. -/

end InformationTheory.Shannon