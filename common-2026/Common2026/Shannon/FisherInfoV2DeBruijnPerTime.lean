import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt              -- HasDerivAt.sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv          -- HasDerivAt.exp

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
* **Phase 1b** `pPath_eq_convDensityAdd` — density 同定 (**genuine** `@audit:ok`, L-PT-β closed):
  `(P.map (X+√s·Z)).rnDeriv volume =ᵐ convDensityAdd p_X (gaussianPDFReal 0 √s)`。
  Phase 1a + `gaussianReal_of_var_ne_zero` + `conv_withDensity_eq_lconvolution` +
  bridge `pPath_eq_convDensityAdd_lconvolution_bridge` (`∫⁻ → ofReal ∫`)。bridge の per-z
  可積分性は `Integrable.mul_bdd` (pX 可積分 × Gaussian 有界 `gaussianPDFReal_le_prefactor`)、
  density witness 可測性は `hpX_meas.ennreal_ofReal` で genuine 化 (regularity hyp
  `hpX_meas : Measurable pX` 追加)。
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

/-- **Closed-form Gaussian pdf bound (genuine)**: the Gaussian density is bounded above by
the normalizing prefactor `(√(2πv))⁻¹` (since `exp` of a nonpositive exponent is `≤ 1`).
Mathlib has `gaussianPDFReal_nonneg` / `_pos` but no upper bound; supplied here for the
`Integrable.mul_bdd` domination in the L-PT-β bridge. Genuine, no `sorry`.

**Independent audit (commit `6f675ca`)**: genuine non-degenerate upper bound
(`exp` of a nonpositive exponent `≤ 1`, prefactor finite positive). `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free), 0 sorry / 0 residual.
@audit:ok -/
private theorem gaussianPDFReal_le_prefactor (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal]
  have hpref_nn : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  have hexp_le : Real.exp (-(x - μ) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (x - μ) ^ 2 / (2 * v) := by positivity
    linarith [neg_div (2 * (v : ℝ)) ((x - μ) ^ 2)]
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hexp_le hpref_nn
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-- **L-PT-β bridge (genuine)**: the ENNReal lconvolution density of the two
`withDensity` factors equals `ENNReal.ofReal` of the Bochner-`∫` convolution density
`convDensityAdd pX (gaussianPDFReal 0 v)`, pointwise (so a.e.).

`lconvolution_def`: `((ofReal∘pX) ⋆ₗ gaussianPDF 0 v) z = ∫⁻ y, ofReal (pX y) * ofReal (gpdfReal 0 v (-y+z)) ∂volume`.
`convDensityAdd pX g z = ∫ y, pX y * g (z-y) ∂volume`. With `z - y = -y + z` and
`ofReal (a*b) = ofReal a * ofReal b` (`0 ≤ pX y`), the `∫⁻` equals `ofReal (∫ ...)` by
`ofReal_integral_eq_lintegral_ofReal`, whose per-`z` integrability precondition
`Integrable (fun y => pX y * gpdfReal 0 v (z-y))` is discharged genuinely:
`pX` is integrable (probability density, regularity hyp `hpX_int`) and the Gaussian factor
is bounded by its prefactor `(√(2πv))⁻¹` (`gaussianPDFReal_le_prefactor`), so
`Integrable.mul_bdd` closes it. `hpX_int` is a pure regularity precondition (NOT
load-bearing), supplied by the caller from `P.map X = withDensity (ofReal∘pX)` with `P`
a probability measure.

**Independent audit (this session)**: closes the former L-PT-β residual. No `sorry`, no
load-bearing hypothesis (`hpX_int` / `hpX_nn` are regularity preconditions).
@audit:ok -/
private theorem pPath_eq_convDensityAdd_lconvolution_bridge
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (s : ℝ) (hs : 0 ≤ s)
    (_hv_ne : (⟨s, hs⟩ : ℝ≥0) ≠ 0) :
    ((fun x => ENNReal.ofReal (pX x)) ⋆ₗ gaussianPDF 0 (⟨s, hs⟩ : ℝ≥0))
      =ᵐ[volume] fun z => ENNReal.ofReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs⟩) z) := by
  refine Filter.Eventually.of_forall (fun z => ?_)
  -- unfold lconvolution: `∫⁻ y, ofReal (pX y) * gaussianPDF 0 v (-y + z)`
  rw [MeasureTheory.lconvolution_def]
  simp only [gaussianPDF]
  -- fold the product of `ofReal`s into `ofReal` of the product (uses `0 ≤ pX y`)
  have hofReal_mul : ∀ y : ℝ,
      ENNReal.ofReal (pX y) * ENNReal.ofReal (gaussianPDFReal 0 ⟨s, hs⟩ (-y + z))
        = ENNReal.ofReal (pX y * gaussianPDFReal 0 ⟨s, hs⟩ (-y + z)) :=
    fun y => (ENNReal.ofReal_mul (hpX_nn y)).symm
  simp only [hofReal_mul]
  -- rewrite `-y + z` to the `convDensityAdd` shape `z - y`
  have hsub : ∀ y : ℝ, (-y + z) = z - y := fun y => by ring
  simp only [hsub]
  -- `∫⁻ ofReal f = ofReal (∫ f)` needs integrability of `fun y => pX y * gpdfReal 0 v (z-y)`
  -- (per-`z` analytic precondition — L-PT-β residual).
  have hint : Integrable (fun y => pX y * gaussianPDFReal 0 ⟨s, hs⟩ (z - y)) volume := by
    -- `pX` integrable × Gaussian factor bounded by its prefactor ⇒ `Integrable.mul_bdd`.
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * (⟨s, hs⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (z - y))]
      exact gaussianPDFReal_le_prefactor 0 ⟨s, hs⟩ (z - y)
  have hnn : 0 ≤ᵐ[volume] fun y => pX y * gaussianPDFReal 0 ⟨s, hs⟩ (z - y) :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ (z - y))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  rfl

/-- **Phase 1b (genuine, L-PT-β closed)**: when `P.map X` has a Real density witness `pX`
(`P.map X = volume.withDensity (ENNReal.ofReal ∘ pX)`), the density of the heat-flow
path `X + √s·Z` is a.e. equal to `convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩)`.

Foundation chain (all Mathlib-direct): Phase 1a (`gaussianConvolution_law_conv`) +
`gaussianReal_of_var_ne_zero` (`𝒩(0,s) = volume.withDensity (gaussianPDF 0 ⟨s,_⟩)`) +
`conv_withDensity_eq_lconvolution` (conv of two `withDensity` = `withDensity` of the
lconvolution `∫⁻`) + the `∫⁻ → ofReal ∫` bridge `pPath_eq_convDensityAdd_lconvolution_bridge`.

Both former residuals are now genuine: `hf_meas` is `hpX_meas.ennreal_ofReal` (regularity hyp
`hpX_meas : Measurable pX`), and the bridge's per-`z` integrability is discharged by
`Integrable pX volume`, derived here from `hpX_law` + `P` probability (`∫⁻ ofReal(pX) =
(P.map X) univ = 1 < ∞`). `hpX_meas` is a pure regularity precondition (NOT load-bearing).
@audit:ok -/
theorem pPath_eq_convDensityAdd
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {s : ℝ} (hs : 0 < s) :
    (P.map (gaussianConvolution X Z s)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) z) := by
  -- variance witness `⟨s, hs.le⟩ : ℝ≥0` is nonzero (so the Gaussian is volume-AC).
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact hs.ne' (congrArg NNReal.toReal h)
  -- `pX` is a genuine probability density ⇒ `Integrable pX volume` (used by the bridge).
  --   `∫⁻ ofReal(pX) = (volume.withDensity (ofReal∘pX)) univ = (P.map X) univ = P univ = 1`.
  have hpX_int : Integrable pX volume := by
    rw [Integrable, hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpX_nn)]
    refine ⟨hpX_meas.aestronglyMeasurable, ?_⟩
    have hlint : ∫⁻ x, ENNReal.ofReal (pX x) ∂volume = (P.map X) Set.univ := by
      rw [hpX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
    exact ENNReal.one_lt_top
  -- Step 1 (Phase 1a): law of `X + √s·Z` is the convolution `(P.map X) ∗ 𝒩(0,s)`.
  rw [gaussianConvolution_law_conv X Z hX hZ hXZ hZ_law hs.le]
  -- Step 2: write both factors as `volume.withDensity _`.
  --   `P.map X = volume.withDensity (ofReal ∘ pX)`  (hyp)
  --   `𝒩(0,s) = volume.withDensity (gaussianPDF 0 ⟨s,_⟩)`  (gaussianReal_of_var_ne_zero)
  rw [hpX_law, gaussianReal_of_var_ne_zero 0 hv_ne]
  -- Step 3: conv of two `withDensity` = `withDensity` of the lconvolution `∫⁻`.
  have hf_meas : Measurable (fun x => ENNReal.ofReal (pX x)) := hpX_meas.ennreal_ofReal
  have hg_meas : Measurable (gaussianPDF 0 (⟨s, hs.le⟩ : ℝ≥0)) := measurable_gaussianPDF 0 _
  rw [MeasureTheory.conv_withDensity_eq_lconvolution hf_meas hg_meas]
  -- Step 4: `rnDeriv (withDensity h) =ᵐ h`, then identify the lconvolution density with
  --   `ofReal ∘ convDensityAdd` via the `∫⁻ → ofReal ∫` bridge (L-PT-β).
  refine (Measure.rnDeriv_withDensity volume
    (MeasureTheory.measurable_lconvolution volume hf_meas hg_meas)).trans ?_
  exact pPath_eq_convDensityAdd_lconvolution_bridge pX hpX_nn hpX_int s hs.le hv_ne

/-! ## Phase 2 — heat equation per-density (L-PT-α honest sorry, max cost) -/

-- Genuine kernel-level helpers (heat-flow Gaussian kernel `g_σ(u) = gaussianPDFReal 0 ⟨σ,_⟩ u`).
-- These are the analytic core of the heat equation at the kernel level (plan §Phase 2,
-- L-PT-α partial progress). The body `heatFlow_density_heat_equation` consumes them.

/-- Explicit `ℝ`-parameterized heat kernel `g(σ, u) = (√(2πσ))⁻¹ · exp(-u²/(2σ))`, with `σ`
ranging over `ℝ` (not `ℝ≥0`). Agrees with `gaussianPDFReal 0 ⟨σ,_⟩` for `σ > 0`; needed so
the `σ`-derivative can be taken over a real neighborhood (the `NNReal` coercion `⟨σ,_⟩` cannot
be formed for `σ < 0`). `def` — no proof obligation, agreement with `gaussianPDFReal`
established by `heatFlow_density_heat_equation_kernel_eq`. -/
noncomputable def heatFlow_density_heat_equation_kernel (σ u : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-u ^ 2 / (2 * σ))

/-- The explicit `ℝ`-kernel agrees with `gaussianPDFReal 0 ⟨σ,_⟩` for `σ > 0`.

**Independent audit (commit `6f675ca`)**: genuine definitional agreement (`rfl` after
`sub_zero`). sorryAx-free, 0 sorry / 0 residual.
@audit:ok -/
theorem heatFlow_density_heat_equation_kernel_eq
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    heatFlow_density_heat_equation_kernel σ u = gaussianPDFReal 0 ⟨σ, hσ.le⟩ u := by
  unfold heatFlow_density_heat_equation_kernel
  rw [gaussianPDFReal]
  simp only [sub_zero]
  rfl

/-- **Kernel spatial 1st derivative (genuine)**: for the Gaussian heat kernel with mean `0`
and variance `σ > 0`, `g_σ(u) = (√(2πσ))⁻¹ · exp(-u²/(2σ))`,
`∂_u g_σ(u) = g_σ(u) · (-(u/σ))`.

**Independent audit (commit `6f675ca`)**: genuine chain-rule computation, non-degenerate
closed form (`-(u/σ)` factor). sorryAx-free, 0 sorry / 0 residual.
@audit:ok -/
theorem heatFlow_density_heat_equation_kernel_x_deriv1
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun ξ : ℝ => heatFlow_density_heat_equation_kernel σ ξ)
      (heatFlow_density_heat_equation_kernel σ u * (-(u / σ))) u := by
  unfold heatFlow_density_heat_equation_kernel
  have he : HasDerivAt (fun ξ : ℝ => -ξ ^ 2 / (2 * σ)) (-(u / σ)) u := by
    have h1 : HasDerivAt (fun ξ : ℝ => -ξ ^ 2) (-(2 * u)) u := by
      simpa using ((hasDerivAt_pow 2 u).const_mul (-1 : ℝ))
    have := h1.div_const (2 * σ)
    convert this using 1
    field_simp
  have hexp := he.exp
  have hcm := hexp.const_mul (Real.sqrt (2 * Real.pi * σ))⁻¹
  convert hcm using 1
  ring

/-- **Kernel spatial 2nd derivative (genuine)**: `∂²_u g_σ(u) = g_σ(u) · (u²/σ² - 1/σ)`.

**Independent audit (commit `6f675ca`)**: genuine product-rule computation, non-degenerate
closed form (`u²/σ² - 1/σ` factor, `≠ 0` e.g. at `u = 0`). sorryAx-free, 0 sorry / 0 residual.
@audit:ok -/
theorem heatFlow_density_heat_equation_kernel_x_deriv2
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt
      (fun ξ : ℝ => heatFlow_density_heat_equation_kernel σ ξ * (-(ξ / σ)))
      (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ)) u := by
  have hg := heatFlow_density_heat_equation_kernel_x_deriv1 hσ u
  have hlin : HasDerivAt (fun ξ : ℝ => -(ξ / σ)) (-(1 / σ)) u := by
    have := (hasDerivAt_id u).div_const σ
    simpa using this.neg
  have hprod := hg.mul hlin
  convert hprod using 1
  field_simp
  ring

/-- **Kernel σ-derivative (genuine)**: differentiating the kernel in its variance `σ`,
`∂_σ g_σ(u) = (1/2) · g_σ(u) · (u²/σ² - 1/σ)`.

**Independent audit (commit `6f675ca`)**: genuine — differentiates both the prefactor
`(√(2πσ))⁻¹` and the exponent in `σ`, closes via `√(2πσ)² = 2πσ`. Non-degenerate closed
form. sorryAx-free, 0 sorry / 0 residual.
@audit:ok -/
theorem heatFlow_density_heat_equation_kernel_sigma_deriv
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun τ : ℝ => heatFlow_density_heat_equation_kernel τ u)
      ((1/2) * (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ))) σ := by
  unfold heatFlow_density_heat_equation_kernel
  have hpos2pi : (2 * Real.pi * σ) ≠ 0 := by positivity
  have hpos2pi' : (0:ℝ) ≤ 2 * Real.pi * σ := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi * σ) ≠ 0 := by rw [Real.sqrt_ne_zero']; positivity
  -- ∂_τ √(2πτ)
  have hsqrtcomp : HasDerivAt (fun τ : ℝ => Real.sqrt (2 * Real.pi * τ))
      (1 / (2 * Real.sqrt (2 * Real.pi * σ)) * (2 * Real.pi)) σ := by
    have hinner : HasDerivAt (fun τ : ℝ => 2 * Real.pi * τ) (2 * Real.pi) σ := by
      simpa using (hasDerivAt_id σ).const_mul (2 * Real.pi)
    exact (hasDerivAt_sqrt hpos2pi).comp σ hinner
  have hinv := hsqrtcomp.inv hsqrt_ne
  -- ∂_τ exp(-u²/(2τ))
  have hexp_inner : HasDerivAt (fun τ : ℝ => -u ^ 2 / (2 * τ)) (u ^ 2 / (2 * σ ^ 2)) σ := by
    have hinv2 : HasDerivAt (fun τ : ℝ => τ⁻¹) (-1 / σ ^ 2) σ := by
      simpa using (hasDerivAt_id σ).inv hσ.ne'
    have hcm := hinv2.const_mul (-u ^ 2 / 2)
    have heq : (fun τ : ℝ => (-u ^ 2 / 2) * τ⁻¹) = (fun τ : ℝ => -u ^ 2 / (2 * τ)) := by
      funext τ
      rcases eq_or_ne τ 0 with h | h
      · simp [h]
      · field_simp
    rw [heq] at hcm
    convert hcm using 1
    field_simp
  have hexp := hexp_inner.exp
  -- product rule, then close the algebra (uses √(2πσ)² = 2πσ)
  have hprod := hinv.mul hexp
  convert hprod using 1
  simp only [Pi.inv_apply]
  rw [Real.sq_sqrt hpos2pi']
  field_simp
  ring

/-- **Kernel heat equation (genuine)**: the Gaussian heat kernel solves the heat equation,
`∂_σ g_σ(u) = (1/2) · ∂²_u g_σ(u)`. Both sides equal `(1/2) · g_σ(u) · (u²/σ² - 1/σ)`.

**Independent audit (commit `6f675ca`)**: genuine, NON-degenerate. The two `HasDerivAt`
conjuncts are not vacuously-equal: σ-side derivative is `(1/2)·g·(u²/σ²-1/σ)`, x-2nd
derivative is `g·(u²/σ²-1/σ)`, both non-trivially nonzero (e.g. `-1/σ ≠ 0` at `u = 0`), so
the heat-equation link `∂_σ = (1/2)∂²_u` is a real identity (not both ≡ 0). Assembled from
the two genuine kernel-derivative lemmas. sorryAx-free, 0 sorry / 0 residual.
@audit:ok -/
theorem heatFlow_density_heat_equation_kernel_heat_eq
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun τ : ℝ => heatFlow_density_heat_equation_kernel τ u)
      ((1/2) * (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ))) σ
    ∧ HasDerivAt
        (fun ξ : ℝ => heatFlow_density_heat_equation_kernel σ ξ * (-(ξ / σ)))
        (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ)) u :=
  ⟨heatFlow_density_heat_equation_kernel_sigma_deriv hσ u,
   heatFlow_density_heat_equation_kernel_x_deriv2 hσ u⟩

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

**Partial progress (L-PT-α retreat, body `sorry` retained)**: the kernel-level heat
equation is now genuine (`sorryAx`-free): the four helpers above
(`heatFlow_density_heat_equation_kernel_{x_deriv1,x_deriv2,sigma_deriv,heat_eq}`)
establish `∂_σ g_σ(u) = (1/2) ∂²_u g_σ(u)`, both sides `= (1/2) g_σ(u)(u²/σ² - 1/σ)`,
discharging the "differentiate the Gaussian factor in σ (chain rule)" step. What
remains in this body is the two differentiation-under-the-integral-sign steps that
lift the kernel identity through `convDensityAdd`: (i) `∂_σ pPath x = ∫ pX·∂_σ g_σ`
and (ii) identifying the pinned `pathDeriv2 s x` with `∫ pX·∂²_x g_σ`, each requiring
a Gaussian-tail domination-bound `Integrable` construction (~80+ lines, PR-level,
plan §Phase 2 L-PT-α). These stay `sorry` per the explicit retreat line.

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

**Independent audit (commit `127319f`)**: genuine. Hypotheses are all regularity /
parametric-diff preconditions — `hdiff` is the *per-x integrand* `HasDerivAt`, NOT the
integral-level conclusion (which `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
produces from them). No load-bearing hyp, no circular `:= h`. Body genuinely plumbs the
hyps into the gateway lemma and extracts `.2`. `#print axioms` = `[propext,
Classical.choice, Quot.sound]` (sorryAx-free), 0 sorry / 0 residual.
@audit:ok -/
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
  have hgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x => negMulLog (pPath s x))
      (F' := fun s x => entDeriv s x)
      (bound := bound) (Filter.univ_mem) hmeas hint hderiv_meas hb hbound_int hdiff
  simpa only using hgate.2

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

**Independent audit (commit `127319f`)**: genuine. `hp_nn` (nonnegativity) and `hint`
(integrability) are regularity preconditions, not the claim. Body genuinely performs the
`∫ ↔ (∫⁻ ofReal).toReal` round-trip via `ofReal_integral_eq_lintegral_ofReal` (uses
`hint` + a.e. nonnegativity) and `ENNReal.toReal_ofReal` (uses `integral_nonneg`); both
directions of the `.toReal` round-trip discharge their nonneg / integrability side-goals
from the hyps. `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free),
0 sorry / 0 residual.
@audit:ok -/
theorem fisher_from_logDeriv
    (p : ℝ → ℝ) (hp_nn : ∀ x, 0 ≤ p x)
    (hint : Integrable (fun x => (logDeriv p x)^2 * p x) volume) :
    ∫ x, (logDeriv p x)^2 * p x ∂volume = fisherInfoOfDensityReal p := by
  -- non-negativity of the integrand `g x = (logDeriv p x)^2 * p x`
  have hg_nn : 0 ≤ᵐ[volume] fun x => (logDeriv p x)^2 * p x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hp_nn x)
  -- RHS unfolds to the `.toReal` of a lintegral; match the lintegrands
  unfold fisherInfoOfDensityReal fisherInfoOfDensity
  have hlint :
      (∫⁻ x, ENNReal.ofReal ((logDeriv p x) ^ 2) * ENNReal.ofReal (p x) ∂volume)
        = ∫⁻ x, ENNReal.ofReal ((logDeriv p x)^2 * p x) ∂volume := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hlint, ← ofReal_integral_eq_lintegral_ofReal hint hg_nn,
    ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hp_nn x))]

end Common2026.Shannon.FisherInfoV2
