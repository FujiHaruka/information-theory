import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# per-time de Bruijn identity — density-route analytic core (atoms)

`debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean`,
`@residual(plan:epi-debruijn-pertime-closure)`) を一般 `X` で genuine 化するための
解析核を atom 分解して提供する scaffolding file。

Phase 0 (false→true signature pivot) は親 file `FisherInfoV2DeBruijn.lean` で完了済
(`IsRegularDeBruijnHypV2` に density-pin field `density_t_eq` 追加、
`debruijnIdentityV2_holds` に `_hX/_hZ/_hXZ` args + `wall:`→`plan:` 再分類)。

本 file は plan `epi-debruijn-pertime-closure-plan.md` の Phase 1-5 atom を提供:

* **Phase 1a** `gaussianConvolution_law_conv` — **genuine**: 法 (law) の畳み込み分解
  `P.map (X + √s·Z) = (P.map X) ∗ gaussianReal 0 ⟨s, _⟩` (`IndepFun.map_add_eq_map_conv_map`
  + `gaussianConvolution_law_of_gaussian` と同型の `√s·Z` law 計算)。density witness 不要、
  全 `X` で成立。
* **Phase 1b** `pPath_eq_convDensityAdd` — density 同定 (`sorry`, L-PT-β):
  `(P.map (X+√s·Z)).rnDeriv volume =ᵐ convDensityAdd p_X (gaussianPDFReal 0 √s)`。
  Phase 1a + `gaussianReal_of_var_ne_zero` + `conv_withDensity_eq_lconvolution` まで
  Mathlib 直結だが、`∫⁻` (lconvolution, ENNReal) → `∫` (convDensityAdd, Bochner Real) の
  shape 橋渡しが ~60 行超 (L-PT-β 撤退、honest sorry)。
* **Phase 2** `heatFlow_density_heat_equation` — heat eq per-density (`sorry`, L-PT-α、最大コスト)
* **Phase 3** `entropy_hasDerivAt_via_parametric` — entropy parametric diff (`sorry`, L-PT-γ)
* **Phase 4a** `debruijn_ibp_step` — 無限区間 IBP (**genuine** `@audit:ok`:
  `integral_mul_deriv_eq_deriv_mul_of_integrable` と同形、`exact` 一発)
* **Phase 4b** `fisher_from_logDeriv` — logDeriv→Fisher congr (`sorry`)

Phase 5 (capstone) は本 file では着手しない — wall lemma `debruijnIdentityV2_holds` は
親 file 側にあり、本 file は atom 群を供給するだけ (plan §Phase 5 参照)。
-/

namespace Common2026.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-! ## Phase 1a — law factorization (genuine) -/

/-- **Phase 1a (genuine)**: the law of the heat-flow path `X + √s·Z` factors as the
convolution of the law of `X` with the Gaussian `𝒩(0, s)`.

`P.map (gaussianConvolution X Z s) = (P.map X) ∗ gaussianReal 0 ⟨s, hs⟩`.

This is the foundational measure-level step of the density identification (Phase 1b):
the density of the LHS is the convolution of `p_X` with the `𝒩(0, s)` density. Holds
for **arbitrary** `X` (no density witness needed) — only `Z ∼ 𝒩(0, 1)` is used.

Proof mirrors `gaussianConvolution_law_of_gaussian` (`FisherInfoV2DeBruijn.lean:131`)
for the `√s·Z` law computation, then `IndepFun.map_add_eq_map_conv_map`.

@audit:ok -/
theorem gaussianConvolution_law_conv
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {s : ℝ} (hs : 0 ≤ s) :
    P.map (gaussianConvolution X Z s)
      = (P.map X) ∗ gaussianReal 0 ⟨s, hs⟩ := by
  -- Step 1: law of `√s · Z` is `𝒩(0, s)` (mirrors `gaussianConvolution_law_of_gaussian`).
  have h_sqrt_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs
  have h_sqrtZ_map : Measure.map (fun ω => Real.sqrt s * Z ω) P = gaussianReal 0 ⟨s, hs⟩ := by
    have h_compose : Measure.map (fun ω => Real.sqrt s * Z ω) P
        = (P.map Z).map (fun y => Real.sqrt s * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt s * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hZ
      simpa [Function.comp] using this.symm
    rw [h_compose, hZ_law, gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]; apply NNReal.eq; exact h_sqrt_sq
  -- Step 2: independence `X ⊥ (√s · Z)`.
  have h_indep_X_sqrtZ : IndepFun X (fun ω => Real.sqrt s * Z ω) P :=
    hXZ.comp measurable_id (measurable_const.mul measurable_id)
  -- Step 3: `gaussianConvolution X Z s = X + (√s · Z)` pointwise, then conv factorization.
  have h_meas_sqrtZ : Measurable (fun ω => Real.sqrt s * Z ω) :=
    measurable_const.mul hZ
  have h_funext : gaussianConvolution X Z s = X + (fun ω => Real.sqrt s * Z ω) := by
    funext ω; rfl
  rw [h_funext,
    IndepFun.map_add_eq_map_conv_map hX h_meas_sqrtZ h_indep_X_sqrtZ, h_sqrtZ_map]

/-! ## Phase 1b — density identification (L-PT-β honest sorry) -/

/-- **Phase 1b (L-PT-β honest sorry)**: when `P.map X` has a Real density witness `pX`
(`P.map X = volume.withDensity (ENNReal.ofReal ∘ pX)`), the density of the heat-flow
path `X + √s·Z` is a.e. equal to `convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩)`.

Foundation chain (all Mathlib-direct): Phase 1a (`gaussianConvolution_law_conv`) +
`gaussianReal_of_var_ne_zero` (`𝒩(0,s) = volume.withDensity (gaussianPDF 0 ⟨s,_⟩)`) +
`conv_withDensity_eq_lconvolution` (conv of two `withDensity` = `withDensity` of the
lconvolution `∫⁻`). The residual gap is the `∫⁻` (ENNReal lconvolution) → `∫` (Bochner
Real `convDensityAdd`) bridge: `ENNReal.ofReal`/`.toReal` round-trip + integrability +
nonnegativity, estimated ~60 lines (L-PT-β retreat per plan §Phase 1).

`@residual(plan:epi-debruijn-pertime-closure)` -/
theorem pPath_eq_convDensityAdd
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {s : ℝ} (hs : 0 < s) :
    (P.map (gaussianConvolution X Z s)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) z) := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure) — L-PT-β: ∫⁻→∫ bridge

/-! ## Phase 2 — heat equation per-density (L-PT-α honest sorry, max cost) -/

/-- **Phase 2 (L-PT-α honest sorry)**: the heat-flow density satisfies the heat
equation per density: `∂_σ pPath σ x = (1/2) ∂²_x pPath σ x` at `σ = s`.

`pPath : ℝ → ℝ → ℝ` is the heat-flow density path, **pinned** by `hpPath` to be the
heat-flow density `pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ,_⟩)` on the
positive `σ`-range (Phase-5 instantiation). `pathDeriv1` / `pathDeriv2` are **pinned**
by `hpathDeriv1` / `hpathDeriv2` to be the first / second `x`-(spatial) derivatives of
`pPath`. The conclusion is the `σ`-`HasDerivAt` of `pPath · x` equal to `(1/2)` times
that spatial second derivative — the heat equation.

**Honesty (avoids Phase-0-type false statement)**: an earlier draft took `pathDeriv2`
as a *free* function unrelated to `pPath`, making the statement universally FALSE
(counterexample `pPath := fun σ _ => σ`, `pathDeriv2 := 0` forces `HasDerivAt id 0 s`,
a `1 = 0` contradiction — the same false-statement shape that judgment #17 fixed for
`IsRegularDeBruijnHypV2.density_t_eq`). The fix pins `pathDeriv2` (and `pPath` itself)
**definitionally**: `pathDeriv1`/`pathDeriv2` are *identified* as the genuine spatial
derivatives of `pPath`, and `pPath` is *identified* as the heat-flow convolution. These
are regularity / definitional bindings (which function `pathDeriv2` *is*), NOT the heat
equation. The heat-equation equality `∂_σ pPath = (1/2) ∂²_x pPath` is the **conclusion**
to be proven (body `sorry`) and is deliberately NOT supplied as a hypothesis — doing so
would be load-bearing (bundling the proof core into a hypothesis), which is forbidden.

**Independent audit (commit `69478a4`, re-audit of prior `b37b9ae` false_statement)**:
signature confirmed a TRUE statement, NOT load-bearing. The Phase-0 false-statement
defect is fully resolved — the old counterexample `pPath := fun σ _ => σ` now violates
`hpPath` (a Gaussian-convolution density cannot be a nonzero constant in `x`), and the
remaining free symbols `pX` / `pathDeriv1` parametrize true instances (the pins force
`pathDeriv1`/`pathDeriv2` to be the unique spatial derivatives, and the conclusion's
σ↔x heat-equation link is supplied by NONE of the three pins — it stays in the body).
Verdict: honest_residual (body `sorry` retained, `@residual` kept).

Mathlib has no Gaussian heat semigroup closed-form (`"heat"`/`"Mehler"`/
`"OrnsteinUhlenbeck"`/`"FokkerPlanck"` all `Found 0`); this is the largest atom
(~80-120 lines, plan §Phase 2). The route is density-side: differentiate the
Gaussian factor `gaussianPDFReal 0 ⟨σ,_⟩` in `σ` (chain rule) and connect to the
`x`-second-derivative `pathDeriv2` via `convDensityAddDeriv`.

`@residual(plan:epi-debruijn-pertime-closure)` -/
theorem heatFlow_density_heat_equation
    (pX : ℝ → ℝ)
    (pPath pathDeriv1 pathDeriv2 : ℝ → ℝ → ℝ)
    -- definitional pin: `pPath` IS the heat-flow convolution density
    (hpPath : ∀ (σ : ℝ) (hσ : 0 < σ),
      pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))
    -- definitional pin: `pathDeriv1` IS the spatial first derivative of `pPath`
    (hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pPath σ ξ) (pathDeriv1 σ y) y)
    -- definitional pin: `pathDeriv2` IS the spatial second derivative of `pPath`
    (hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pathDeriv1 σ ξ) (pathDeriv2 σ y) y)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt
      (fun σ : ℝ => pPath σ x)
      ((1/2) * pathDeriv2 s x) s := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure) — heat eq per-density, density-route self-build

/-! ## Phase 3 — entropy parametric diff (L-PT-γ honest sorry) -/

/-- **Phase 3 (L-PT-γ honest sorry)**: differentiation under the integral sign for the
entropy along the heat-flow path:
`(d/ds) ∫ x, negMulLog (pPath s x) ∂volume = ∫ x, (d/ds) negMulLog (pPath s x) ∂volume`
at `s = t`.

Core lemma: `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`ParametricIntegral.lean:289`, `𝕜 := ℝ`). The Gaussian-tail dominating function
`bound`'s `Integrable bound volume` is a load-bearing-free regularity precondition
(supplied here as a hypothesis). Stated against an abstract entropy-integrand
derivative `entDeriv` and dominating `bound` to keep the parametric-diff shape.

`@residual(plan:epi-debruijn-pertime-closure)` -/
theorem entropy_hasDerivAt_via_parametric
    (pPath : ℝ → ℝ → ℝ) (entDeriv : ℝ → ℝ → ℝ) (bound : ℝ → ℝ) {t : ℝ}
    (hbound_int : Integrable bound volume)
    (hmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable (fun x => negMulLog (pPath s x)) volume)
    (hint : Integrable (fun x => negMulLog (pPath t x)) volume)
    (hderiv_meas : AEStronglyMeasurable (entDeriv t) volume)
    (hb : ∀ᵐ x ∂volume, ∀ s ∈ Set.univ, ‖entDeriv s x‖ ≤ bound x)
    (hdiff : ∀ᵐ x ∂volume, ∀ s ∈ Set.univ,
      HasDerivAt (fun s => negMulLog (pPath s x)) (entDeriv s x) s) :
    HasDerivAt (fun s => ∫ x, negMulLog (pPath s x) ∂volume)
      (∫ x, entDeriv t x ∂volume) t := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure) — parametric integral diff plumbing

/-! ## Phase 4a — infinite-interval IBP (L-PT-δ honest sorry) -/

/-- **Phase 4a (L-PT-δ honest sorry)**: the de Bruijn integration-by-parts step on the
whole line, `∫ x, negMulLog'(p x) · (∂_s p) x = - ∫ x, ∂_x (negMulLog' ∘ p) x · (∂_s p) x`
(boundary terms vanish by Gaussian-tail decay).

Core lemma: `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`
(`IntegralEqImproper.lean:1318`, `A := ℝ`). The signature is exactly the Mathlib
lemma's shape (`A := ℝ` is a `NormedRing`/`NormedAlgebra ℝ`): the support-wide
`HasDerivAt` (`tsupport`) and the three integrability hyps are its preconditions; the
boundary-term vanishing (tail decay) is discharged internally by the `_of_integrable`
variant (no separate `Tendsto` hyp needed). Genuine, `exact`-closed (no residual).

@audit:ok -/
theorem debruijn_ibp_step
    (u v u' v' : ℝ → ℝ)
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ x, u x * v' x = - ∫ x, u' x * v x :=
  MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv

/-! ## Phase 4b — logDeriv → Fisher congr -/

/-- **Phase 4b honest sorry**: shape congruence connecting the IBP output
`∫ (∂_x p)²/p` to the V2 Fisher info `fisherInfoOfDensityReal p`:
`∫ x, (logDeriv p x)^2 * p x ∂volume = fisherInfoOfDensityReal p` (under
integrability / finiteness so the `ℝ≥0∞`↔`ℝ` `.toReal` round-trip holds).

Uses `convDensityAdd_logDeriv` (`EPIConvDensity.lean:113`, `@audit:ok`) for the
`logDeriv p = (∫ pX·pY')/p` identification + `fisherInfoOfDensity` unfold
(`FisherInfoV2.lean:89`). Stated against a density `p` with an integrability
precondition.

`@residual(plan:epi-debruijn-pertime-closure)` -/
theorem fisher_from_logDeriv
    (p : ℝ → ℝ) (hp_nn : ∀ x, 0 ≤ p x)
    (hint : Integrable (fun x => (logDeriv p x)^2 * p x) volume) :
    ∫ x, (logDeriv p x)^2 * p x ∂volume = fisherInfoOfDensityReal p := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure) — logDeriv→Fisher shape congr

end Common2026.Shannon.FisherInfoV2
