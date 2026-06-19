import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Per-time de Bruijn identity — analytic-core atoms

The analytic-core atoms of the per-time de Bruijn identity for a general `X`, decomposed for the
assembly `debruijnIdentityV2_holds_assembled` in `FisherInfoV2DeBruijnAssembly.lean`.

## Main statements

* `gaussianConvolution_law_conv` — the law of `X + √s · Z` factors as the convolution of the law
  of `X` with `𝒩(0, s · v_Z)` when `Z ∼ 𝒩(0, v_Z)`.
* `pPath_eq_convDensityAdd` — the density of `X + √s · Z` is `convDensityAdd pX (g_{s·v_Z})`.
* `heatFlow_density_heat_equation` — the heat-flow density solves the heat equation
  `∂_s p = (1/2) ∂²_x p`.
* `entropy_hasDerivAt_via_parametric` — differentiation under the integral sign for the entropy
  along the path.
* `debruijn_ibp_step` — the infinite-interval integration-by-parts step.
* `fisher_from_logDeriv` — the shape congruence connecting the IBP output to the Fisher
  information.
-/

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-! ## Law factorization -/

/-- The law of the heat-flow path `X + √s · Z` factors as the convolution of the law of `X` with
`𝒩(0, s · v_Z)` when `Z ∼ 𝒩(0, v_Z)`:
`P.map (gaussianConvolution X Z s) = (P.map X) ∗ gaussianReal 0 ⟨s · v_Z, _⟩`. Holds for arbitrary
`X` (no density witness needed). Via `√s · Z ∼ 𝒩(0, s · v_Z)` (`gaussianReal_map_const_mul`) and
`IndepFun.map_add_eq_map_conv_map`.

@audit:ok -/
theorem gaussianConvolution_law_conv
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (v_Z : ℝ≥0) (hZ_law : P.map Z = gaussianReal 0 v_Z)
    {s : ℝ} (hs : 0 ≤ s) :
    P.map (gaussianConvolution X Z s)
      = (P.map X) ∗ gaussianReal 0 ⟨s * v_Z, by positivity⟩ := by
  -- Step 1: law of `√s · Z` is `𝒩(0, s·v_Z)` (mirrors `gaussianConvolution_law_of_gaussian`).
  have h_sqrt_sq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs
  have h_sqrtZ_map : Measure.map (fun ω => Real.sqrt s * Z ω) P
      = gaussianReal 0 ⟨s * v_Z, by positivity⟩ := by
    have h_compose : Measure.map (fun ω => Real.sqrt s * Z ω) P
        = (P.map Z).map (fun y => Real.sqrt s * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt s * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hZ
      simpa [Function.comp] using this.symm
    rw [h_compose, hZ_law, gaussianReal_map_const_mul]
    congr 1
    · ring
    · -- `⟨(√s)², _⟩ * v_Z = ⟨s·v_Z, _⟩` in `ℝ≥0`.
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_mk]
      rw [h_sqrt_sq]
      rfl
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

/-! ## Density identification -/

/-- The Gaussian density is bounded above by the normalizing prefactor `(√(2πv))⁻¹`.

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

/-- The ENNReal lconvolution density of the two `withDensity` factors equals `ENNReal.ofReal`
of the Bochner convolution density `convDensityAdd pX (gaussianPDFReal 0 v)`, pointwise. The
`∫⁻ → ofReal ∫` step is `ofReal_integral_eq_lintegral_ofReal`, whose per-`z` integrability comes
from `pX` integrable times the Gaussian factor bounded by its prefactor.

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
  -- `∫⁻ ofReal f = ofReal (∫ f)` needs integrability of `fun y => pX y * gpdfReal 0 v (z-y)`.
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

/-- When `P.map X` has a real density witness `pX` and `Z ∼ 𝒩(0, v_Z)` with `v_Z > 0`, the
density of the heat-flow path `X + √s · Z` is a.e. equal to
`convDensityAdd pX (gaussianPDFReal 0 ⟨s · v_Z, _⟩)`. The chain composes
`gaussianConvolution_law_conv` (law factorization), `gaussianReal_of_var_ne_zero`,
`conv_withDensity_eq_lconvolution`, and the bridge `pPath_eq_convDensityAdd_lconvolution_bridge`.
The general `v_Z` is needed for the sum instance `(X+Y, Z_X+Z_Y)`, whose noise has variance `2`.

@audit:ok -/
theorem pPath_eq_convDensityAdd
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (v_Z : ℝ≥0) (hv_Z_pos : 0 < v_Z) (hZ_law : P.map Z = gaussianReal 0 v_Z)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {s : ℝ} (hs : 0 < s) :
    (P.map (gaussianConvolution X Z s)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨s * v_Z, by positivity⟩) z) := by
  -- variance witness `⟨s·v_Z, _⟩ : ℝ≥0` is nonzero (so the Gaussian is volume-AC).
  have hsv_pos : 0 < s * v_Z := mul_pos hs hv_Z_pos
  have hv_ne : (⟨s * v_Z, by positivity⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact hsv_pos.ne' (congrArg NNReal.toReal h)
  -- `pX` is a genuine probability density ⇒ `Integrable pX volume` (used by the bridge).
  --   `∫⁻ ofReal(pX) = (volume.withDensity (ofReal∘pX)) univ = (P.map X) univ = P univ = 1`.
  have hpX_int : Integrable pX volume := by
    rw [Integrable, hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpX_nn)]
    refine ⟨hpX_meas.aestronglyMeasurable, ?_⟩
    have hlint : ∫⁻ x, ENNReal.ofReal (pX x) ∂volume = (P.map X) Set.univ := by
      rw [hpX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
    exact ENNReal.one_lt_top
  -- Step 1 (law factorization): law of `X + √s·Z` is the convolution `(P.map X) ∗ 𝒩(0, s·v_Z)`.
  rw [gaussianConvolution_law_conv X Z hX hZ hXZ v_Z hZ_law hs.le]
  -- Step 2: write both factors as `volume.withDensity _`.
  --   `P.map X = volume.withDensity (ofReal ∘ pX)`  (hyp)
  --   `𝒩(0, s·v_Z) = volume.withDensity (gaussianPDF 0 ⟨s·v_Z,_⟩)`  (gaussianReal_of_var_ne_zero)
  rw [hpX_law, gaussianReal_of_var_ne_zero 0 hv_ne]
  -- Step 3: conv of two `withDensity` = `withDensity` of the lconvolution `∫⁻`.
  have hf_meas : Measurable (fun x => ENNReal.ofReal (pX x)) := hpX_meas.ennreal_ofReal
  have hg_meas : Measurable (gaussianPDF 0 (⟨s * v_Z, by positivity⟩ : ℝ≥0)) :=
    measurable_gaussianPDF 0 _
  rw [MeasureTheory.conv_withDensity_eq_lconvolution hf_meas hg_meas]
  -- Step 4: `rnDeriv (withDensity h) =ᵐ h`, then identify the lconvolution density with
  --   `ofReal ∘ convDensityAdd` via the `∫⁻ → ofReal ∫` bridge, instantiated at
  --   variance `s·v_Z` (the bridge is generic in its variance argument).
  refine (Measure.rnDeriv_withDensity volume
    (MeasureTheory.measurable_lconvolution volume hf_meas hg_meas)).trans ?_
  exact pPath_eq_convDensityAdd_lconvolution_bridge pX hpX_nn hpX_int (s * v_Z)
    (by positivity) hv_ne

/-! ## Heat equation per density -/

-- Kernel-level helpers for the heat-flow Gaussian kernel `g_σ(u) = gaussianPDFReal 0 ⟨σ,_⟩ u`,
-- consumed by `heatFlow_density_heat_equation`.

/-- The heat kernel `g(σ, u) = (√(2πσ))⁻¹ · exp(-u²/(2σ))` with `σ` ranging over `ℝ`. Used so the
`σ`-derivative can be taken over a real neighborhood (the coercion `⟨σ, _⟩ : ℝ≥0` cannot be formed
for `σ < 0`); it agrees with `gaussianPDFReal 0 ⟨σ, _⟩` for `σ > 0`
(`heatFlow_density_heat_equation_kernel_eq`). -/
noncomputable def heatFlow_density_heat_equation_kernel (σ u : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-u ^ 2 / (2 * σ))

/-- The kernel agrees with `gaussianPDFReal 0 ⟨σ, _⟩` for `σ > 0`.

@audit:ok -/
theorem heatFlow_density_heat_equation_kernel_eq
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    heatFlow_density_heat_equation_kernel σ u = gaussianPDFReal 0 ⟨σ, hσ.le⟩ u := by
  unfold heatFlow_density_heat_equation_kernel
  rw [gaussianPDFReal]
  simp only [sub_zero]
  rfl

/-- The spatial first derivative of the Gaussian heat kernel:
`∂_u g_σ(u) = g_σ(u) · (-(u/σ))` for `σ > 0`.

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

/-- The spatial second derivative of the Gaussian heat kernel:
`∂²_u g_σ(u) = g_σ(u) · (u²/σ² - 1/σ)`.

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

/-- The σ-derivative of the Gaussian heat kernel:
`∂_σ g_σ(u) = (1/2) · g_σ(u) · (u²/σ² - 1/σ)`.

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

/-- The Gaussian heat kernel solves the heat equation `∂_σ g_σ(u) = (1/2) · ∂²_u g_σ(u)`; both
sides equal `(1/2) · g_σ(u) · (u²/σ² - 1/σ)`.

@audit:ok -/
@[entry_point]
theorem heatFlow_density_heat_equation_kernel_heat_eq
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun τ : ℝ => heatFlow_density_heat_equation_kernel τ u)
      ((1/2) * (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ))) σ
    ∧ HasDerivAt
        (fun ξ : ℝ => heatFlow_density_heat_equation_kernel σ ξ * (-(ξ / σ)))
        (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ)) u :=
  ⟨heatFlow_density_heat_equation_kernel_sigma_deriv hσ u,
   heatFlow_density_heat_equation_kernel_x_deriv2 hσ u⟩

-- STEP D of `heatFlow_density_heat_equation`: identify the pinned `pathDeriv2 s x` with the
-- spatial-second-derivative integral `∫ y, pX y · ∂²_x kernel`, using the `pathDeriv1` / `pathDeriv2`
-- pins and the spatial-direction domination hypotheses.
private theorem heatFlow_pathDeriv2_eq_integral
    (pX : ℝ → ℝ)
    (pPath pathDeriv1 pathDeriv2 : ℝ → ℝ → ℝ)
    (hpPath : ∀ (σ : ℝ) (hσ : 0 < σ),
      pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))
    (hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pPath σ ξ) (pathDeriv1 σ y) y)
    (hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pathDeriv1 σ ξ) (pathDeriv2 σ y) y)
    {s : ℝ} (hs : 0 < s) (x : ℝ)
    (boundξ1 : ℝ → ℝ) (hboundξ1_int : Integrable boundξ1 volume)
    (hFξ1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hFξ1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hFξ1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-(((ξ - y)) / s)))) volume)
    (hbξ1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-((ξ - y) / s)))‖ ≤ boundξ1 y)
    (boundξ2 : ℝ → ℝ) (hboundξ2_int : Integrable boundξ2 volume)
    (hFξ2_int : Integrable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y) * (-((x - y) / s)))) volume)
    (hFξ2'_meas : AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) volume)
    (hbξ2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))‖ ≤ boundξ2 y) :
    pathDeriv2 s x
      = ∫ y, pX y * (heatFlow_density_heat_equation_kernel s (x - y)
          * ((x - y) ^ 2 / s ^ 2 - 1 / s)) ∂volume := by
  classical
  -- Global agreement `pPath s = fun ξ => ∫ y, pX y · kernel s (ξ-y)` (s > 0, all ξ).
  have hpPaths : (fun ξ : ℝ => pPath s ξ)
      = (fun ξ : ℝ => ∫ y, pX y * heatFlow_density_heat_equation_kernel s (ξ - y) ∂volume) := by
    funext ξ
    rw [hpPath s hs]
    unfold convDensityAdd
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq hs (ξ - y)]
  -- per-y spatial 1st-derivative HasDerivAt (kernel `_x_deriv1` chained through `ξ ↦ ξ - y`).
  have hD1diff : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ => pX y * heatFlow_density_heat_equation_kernel s (ξ - y))
        (pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-((ξ - y) / s)))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv1 hs (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ => ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  -- D1: identify `pathDeriv1 s` (spatial 1st deriv) with the integral, at every ξ.
  have hpathDeriv1_eq : (fun ξ : ℝ => pathDeriv1 s ξ)
      = (fun ξ : ℝ => ∫ y, pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
          * (-((ξ - y) / s))) ∂volume) := by
    funext ξ
    have hgξ :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun ζ y => pX y * heatFlow_density_heat_equation_kernel s (ζ - y))
        (F' := fun ζ y => pX y * (heatFlow_density_heat_equation_kernel s (ζ - y)
          * (-((ζ - y) / s))))
        (bound := boundξ1) (Filter.univ_mem)
        (Filter.Eventually.of_forall hFξ1_meas) (hFξ1_int ξ) (hFξ1'_meas ξ)
        hbξ1 hboundξ1_int hD1diff
    have hpath : HasDerivAt (fun ξ : ℝ => pPath s ξ)
        (∫ y, pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-((ξ - y) / s))) ∂volume) ξ := by
      rw [hpPaths]; exact hgξ.2
    exact (hpathDeriv1 s ξ).unique hpath
  -- D2: identify `pathDeriv2 s x` (spatial 2nd deriv) with `∫ y, pX y · ∂²_x kernel`.
  -- per-y spatial 2nd-derivative HasDerivAt (kernel `_x_deriv2` chained through `ξ ↦ ξ - y`).
  have hD2diff : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
          * (-((ξ - y) / s))))
        (pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
          * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv2 hs (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ => ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  have hD2gate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ξ y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s))))
      (F' := fun ξ y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s)))
      (bound := boundξ2) (Filter.univ_mem)
      (Filter.Eventually.of_forall (fun ξ => hFξ1'_meas ξ)) hFξ2_int hFξ2'_meas
      hbξ2 hboundξ2_int hD2diff
  -- `pathDeriv1 s` IS the integral function (hpathDeriv1_eq), so differentiating it at x gives
  -- `∫ y, pX y · ∂²_x kernel`; uniqueness with the pin `hpathDeriv2 s x` identifies the value.
  have hpath2 : HasDerivAt (fun ξ : ℝ => pathDeriv1 s ξ)
      (∫ y, pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s)) ∂volume) x := by
    rw [hpathDeriv1_eq]; exact hD2gate.2
  exact (hpathDeriv2 s x).unique hpath2

/-- The heat-flow density satisfies the heat equation: `∂_σ pPath σ x = (1/2) ∂²_x pPath σ x` at
`σ = s`. Here `hpPath` pins `pPath σ` to the heat-flow convolution
`convDensityAdd pX (gaussianPDFReal 0 ⟨σ, _⟩)` on the positive `σ`-range, and
`hpathDeriv1` / `hpathDeriv2` identify `pathDeriv1` / `pathDeriv2` as its spatial first and
second derivatives. These pins fix which functions the arguments are; the heat-equation equality
is the conclusion, derived from the kernel-level heat equation, not a hypothesis. The remaining
arguments are per-`y` integrand domination preconditions in the shape consumed by
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

@audit:ok -/
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
    {s : ℝ} (hs : 0 < s) (x : ℝ)
    -- σ-direction domination: per-`y` integrand `pX y · g_σ(x-y)` and its σ-derivative
    -- `pX y · ∂_σ g_σ(x-y)` are bounded/integrable on the compact σ-neighborhood
    -- `Set.Ioo (s/2) (2s)`.
    (boundσ : ℝ → ℝ) (hboundσ_int : Integrable boundσ volume)
    (hFσ_meas : ∀ᶠ σ in nhds s,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel σ (x - y)) volume)
    (hFσ_int : Integrable
      (fun y => pX y * heatFlow_density_heat_equation_kernel s (x - y)) volume)
    (hFσ'_meas : AEStronglyMeasurable
      (fun y => pX y * ((1/2) * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s)))) volume)
    (hbσ : ∀ᵐ y ∂volume, ∀ σ ∈ Set.Ioo (s/2) (2*s),
      ‖pX y * ((1/2) * (heatFlow_density_heat_equation_kernel σ (x - y)
        * ((x - y) ^ 2 / σ ^ 2 - 1 / σ)))‖ ≤ boundσ y)
    -- spatial-direction domination (pathDeriv2 identification): the spatial 1st and
    -- 2nd derivative integrands of `pX y · g_s(x-y)` are bounded/integrable.
    (boundξ1 : ℝ → ℝ) (hboundξ1_int : Integrable boundξ1 volume)
    (hFξ1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hFξ1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hFξ1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-(((ξ - y)) / s)))) volume)
    (hbξ1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-((ξ - y) / s)))‖ ≤ boundξ1 y)
    (boundξ2 : ℝ → ℝ) (hboundξ2_int : Integrable boundξ2 volume)
    (hFξ2_int : Integrable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y) * (-((x - y) / s)))) volume)
    (hFξ2'_meas : AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) volume)
    (hbξ2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))‖ ≤ boundξ2 y) :
    HasDerivAt
      (fun σ : ℝ => pPath σ x)
      ((1/2) * pathDeriv2 s x) s := by
  classical
  -- σ-neighborhood (compact, keeps σ > 0; avoids the σ→0 blow-up of `(u²/σ²-1/σ)`).
  set sset : Set ℝ := Set.Ioo (s/2) (2*s) with hsset
  have hs_nhds : sset ∈ nhds s := by
    rw [hsset]
    refine Ioo_mem_nhds ?_ ?_
    · linarith
    · linarith
  -- positivity of σ on the neighborhood
  have hσ_pos : ∀ σ ∈ sset, 0 < σ := by
    intro σ hσ
    rw [hsset] at hσ
    have : s/2 < σ := hσ.1
    linarith
  -- =========================================================================
  -- STEP A (σ-direction): differentiate `∫ y, pX y · kernel σ (x-y)` in σ.
  -- =========================================================================
  -- per-y σ-derivative HasDerivAt (from kernel σ-deriv scaled by `pX y`).
  have hAdiff : ∀ᵐ y ∂volume, ∀ σ ∈ sset,
      HasDerivAt (fun σ => pX y * heatFlow_density_heat_equation_kernel σ (x - y))
        (pX y * ((1/2) * (heatFlow_density_heat_equation_kernel σ (x - y)
          * ((x - y) ^ 2 / σ ^ 2 - 1 / σ)))) σ := by
    filter_upwards with y
    intro σ hσ
    exact (heatFlow_density_heat_equation_kernel_sigma_deriv (hσ_pos σ hσ) (x - y)).const_mul (pX y)
  have hAgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun σ y => pX y * heatFlow_density_heat_equation_kernel σ (x - y))
      (F' := fun σ y => pX y * ((1/2) * (heatFlow_density_heat_equation_kernel σ (x - y)
        * ((x - y) ^ 2 / σ ^ 2 - 1 / σ))))
      (bound := boundσ) hs_nhds hFσ_meas hFσ_int hFσ'_meas hbσ hboundσ_int hAdiff
  -- hAgate.2 : HasDerivAt (fun σ => ∫ y, pX y · kernel σ (x-y))
  --              (∫ y, pX y · (1/2)(kernel s (x-y)(…))) s
  have hA : HasDerivAt (fun σ : ℝ => ∫ y, pX y * heatFlow_density_heat_equation_kernel σ (x - y) ∂volume)
      (∫ y, pX y * ((1/2) * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) ∂volume) s := hAgate.2
  -- =========================================================================
  -- STEP B: transfer `hA` to `fun σ => pPath σ x` (they agree on `sset ∈ 𝓝 s`).
  -- =========================================================================
  have hEq : (fun σ : ℝ => pPath σ x)
      =ᶠ[nhds s] (fun σ : ℝ => ∫ y, pX y * heatFlow_density_heat_equation_kernel σ (x - y) ∂volume) := by
    filter_upwards [hs_nhds] with σ hσ
    have hσpos : 0 < σ := hσ_pos σ hσ
    rw [hpPath σ hσpos]
    unfold convDensityAdd
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq hσpos (x - y)]
  have hB : HasDerivAt (fun σ : ℝ => pPath σ x)
      (∫ y, pX y * ((1/2) * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) ∂volume) s :=
    hA.congr_of_eventuallyEq hEq
  -- =========================================================================
  -- STEP C: pull out the `1/2` from the σ-derivative integral.
  --   ∫ y, pX y · (1/2)·K(y) = (1/2) · ∫ y, pX y · K(y),
  --   with K(y) = kernel s (x-y) · ((x-y)²/s² - 1/s).
  -- =========================================================================
  have hC : (∫ y, pX y * ((1/2) * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) ∂volume)
      = (1/2) * ∫ y, pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s)) ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with y
    ring
  rw [hC] at hB
  -- hB : HasDerivAt (fun σ => pPath σ x)
  --        ((1/2) · ∫ y, pX y · (kernel s (x-y) · ((x-y)²/s² - 1/s))) s
  -- =========================================================================
  -- STEP D: identify the pinned `pathDeriv2 s x` with `∫ y, pX y · ∂²_x kernel`
  --   (extracted as `heatFlow_pathDeriv2_eq_integral`).
  -- =========================================================================
  have hpathDeriv2_eq : pathDeriv2 s x
      = ∫ y, pX y * (heatFlow_density_heat_equation_kernel s (x - y)
          * ((x - y) ^ 2 / s ^ 2 - 1 / s)) ∂volume :=
    heatFlow_pathDeriv2_eq_integral pX pPath pathDeriv1 pathDeriv2 hpPath hpathDeriv1 hpathDeriv2
      hs x boundξ1 hboundξ1_int hFξ1_meas hFξ1_int hFξ1'_meas hbξ1
      boundξ2 hboundξ2_int hFξ2_int hFξ2'_meas hbξ2
  -- =========================================================================
  -- STEP E: conclude. `hB` gives `(1/2)·∫ pX·∂²_x kernel`; rewrite via `hpathDeriv2_eq`.
  -- =========================================================================
  rw [hpathDeriv2_eq]
  exact hB

/-! ## Entropy parametric differentiation -/

/-- Differentiation under the integral sign for the entropy along the heat-flow path:
`(d/ds) ∫ x, negMulLog (pPath s x) ∂volume = ∫ x, entDeriv t x ∂volume` at `s = t`, via the
gateway `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The domination and per-`x` derivative
hypotheses are quantified over the neighborhood `Set.Ioo (t/2) (2*t)` (all the gateway needs); a
universal form would be un-instantiable since the integrand diverges as `s → 0⁺` and `s → ∞`.

@audit:ok -/
theorem entropy_hasDerivAt_via_parametric
    (pPath : ℝ → ℝ → ℝ) (entDeriv : ℝ → ℝ → ℝ) (bound : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hbound_int : Integrable bound volume)
    (hmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable (fun x => negMulLog (pPath s x)) volume)
    (hint : Integrable (fun x => negMulLog (pPath t x)) volume)
    (hderiv_meas : AEStronglyMeasurable (entDeriv t) volume)
    (hb : ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioo (t/2) (2*t), ‖entDeriv s x‖ ≤ bound x)
    (hdiff : ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioo (t/2) (2*t),
      HasDerivAt (fun s => negMulLog (pPath s x)) (entDeriv s x) s) :
    HasDerivAt (fun s => ∫ x, negMulLog (pPath s x) ∂volume)
      (∫ x, entDeriv t x ∂volume) t := by
  have hnhds : Set.Ioo (t/2) (2*t) ∈ nhds t :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x => negMulLog (pPath s x))
      (F' := fun s x => entDeriv s x)
      (bound := bound) hnhds hmeas hint hderiv_meas hb hbound_int hdiff
  simpa only using hgate.2

/-! ## Infinite-interval integration by parts -/

/-- The de Bruijn integration-by-parts step on the whole line:
`∫ x, u x · v' x = - ∫ x, u' x · v x`, where the boundary terms vanish by tail decay. A direct
application of `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`.

@audit:ok -/
theorem debruijn_ibp_step
    (u v u' v' : ℝ → ℝ)
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ x, u x * v' x = - ∫ x, u' x * v x :=
  MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv

/-! ## logDeriv to Fisher congruence -/

/-- Shape congruence connecting the IBP output to the V2 Fisher information:
`∫ x, (logDeriv p x)² · p x ∂volume = fisherInfoOfDensityReal p`, under nonnegativity and
integrability so the `ℝ≥0∞ ↔ ℝ` round-trip holds.

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

/-! ## Convolution-density positivity and Gaussian lower bound

The Gaussian convolution density `convDensityAdd pX g_s` is everywhere strictly positive and
bounded below by a shifted Gaussian, so its support is all of `ℝ`. -/

/-- `fun y => pX y * gaussianPDFReal 0 v (x - y)` is integrable.

@audit:ok -/
private theorem convDensityAdd_integrand_integrable
    (pX : ℝ → ℝ) (hpX_int : Integrable pX volume) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun y => pX y * gaussianPDFReal 0 v (x - y)) volume := by
  refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * v))⁻¹) ?_ ?_
  · exact ((measurable_gaussianPDFReal 0 v).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
    exact gaussianPDFReal_le_prefactor 0 v (x - y)

/-- When `pX` is a nonnegative integrable density with positive mass (`0 < ∫ pX`), the Gaussian
convolution density is strictly positive at every `x`. The integrand `y ↦ pX y · g_s(x-y)` is
nonnegative and integrable with support equal to that of `pX` (the Gaussian factor never
vanishes), and `0 < ∫ pX` gives positive-measure support, hence a positive integral.

@audit:ok -/
theorem convDensityAdd_pos
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (hpX_mass : 0 < ∫ y, pX y ∂volume)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x := by
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact hs.ne' (congrArg NNReal.toReal h)
  -- variance witness for `gaussianPDFReal_pos`
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  -- integrand `F y := pX y * g (x - y)`, nonnegative + integrable
  set F : ℝ → ℝ := fun y => pX y * g (x - y) with hF_def
  have hF_nn : 0 ≤ F := fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ (x - y))
  have hF_int : Integrable F volume :=
    convDensityAdd_integrand_integrable pX hpX_int ⟨s, hs.le⟩ x
  -- support of F equals support of pX (the Gaussian factor never vanishes)
  have hsupp : Function.support F = Function.support pX := by
    ext y
    simp only [Function.mem_support, hF_def, ne_eq, mul_eq_zero, not_or]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, (gaussianPDFReal_pos 0 _ (x - y) hv_ne).ne'⟩
  -- positive mass ⇒ positive-measure support of pX
  have hpX_supp : 0 < volume (Function.support pX) :=
    (integral_pos_iff_support_of_nonneg hpX_nn hpX_int).mp hpX_mass
  -- hence positive-measure support of F ⇒ positive integral
  have : 0 < ∫ y, F y ∂volume :=
    (integral_pos_iff_support_of_nonneg hF_nn hF_int).mpr (hsupp ▸ hpX_supp)
  simpa only [convDensityAdd, hF_def, hg_def] using this

/-- Monotonicity of the centered Gaussian pdf in `|·|`: if `|u| ≤ |w|` then `g_v(w) ≤ g_v(u)`.

@audit:ok -/
private theorem gaussianPDFReal_antitone_abs
    (v : ℝ≥0) {u w : ℝ} (huw : |u| ≤ |w|) :
    gaussianPDFReal 0 v w ≤ gaussianPDFReal 0 v u := by
  simp only [gaussianPDFReal, sub_zero]
  have hpref_nn : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpref_nn
  rw [Real.exp_le_exp]
  have hsq : u ^ 2 ≤ w ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg u) huw 2
    rwa [sq_abs, sq_abs] at this
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ 2 * v from by positivity) with hv0 | hvpos
  · rw [← hv0]; simp
  · rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr

/-- The Gaussian convolution density is bounded below by a `(1/2)`-scaled shifted Gaussian:
there is a radius `R > 0` with `(1/2) · g_s (|x| + R) ≤ convDensityAdd pX g_s x` for every `x`.
The proof picks `R` so that `∫_{[-R,R]} pX ≥ 1/2` (tightness), drops the integral to that box,
and uses the monotonicity of `g_s` in `|·|`.

@audit:ok -/
@[entry_point]
theorem convDensityAdd_lower_bound_gaussian
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ,
      (1/2) * gaussianPDFReal 0 ⟨s, hs.le⟩ (|x| + R)
        ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x := by
  classical
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  -- STEP 1 (tightness): `∃ R > 0, ∫ y in Icc (-R) R, pX y ≥ 1/2`.
  obtain ⟨R, hR_pos, hR_mass⟩ :
      ∃ R : ℝ, 0 < R ∧ (1:ℝ)/2 ≤ ∫ y in Set.Icc (-R) R, pX y ∂volume := by
    -- exhausting boxes `sN n := Icc (-n) n`, monotone, `⋃ = univ`.
    set sN : ℕ → Set ℝ := fun n => Set.Icc (-(n:ℝ)) (n:ℝ) with hsN_def
    have hsN_meas : ∀ n, MeasurableSet (sN n) := fun n => measurableSet_Icc
    have hsN_mono : Monotone sN := by
      intro m n hmn
      apply Set.Icc_subset_Icc
      · exact neg_le_neg (by exact_mod_cast hmn)
      · exact_mod_cast hmn
    have hsN_union : (⋃ n, sN n) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      obtain ⟨n, hn⟩ := exists_nat_ge |y|
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      rw [hsN_def]
      simp only [Set.mem_Icc]
      have hy : |y| ≤ (n:ℝ) := hn
      rw [abs_le] at hy
      exact ⟨hy.1, hy.2⟩
    -- integrability on `⋃ = univ`, and `∫ in univ pX = ∫ pX = 1`.
    have hfi : IntegrableOn pX (⋃ n, sN n) volume := by
      rw [hsN_union]; exact hpX_int.integrableOn
    have htends := tendsto_setIntegral_of_monotone hsN_meas hsN_mono hfi
    rw [hsN_union, setIntegral_univ, hpX_mass] at htends
    -- eventually `∫ in sN n, pX > 1/2`; extract a large enough box.
    have hev : ∀ᶠ n in Filter.atTop, (1:ℝ)/2 < ∫ y in sN n, pX y ∂volume := by
      have h12 : (1:ℝ)/2 < 1 := by norm_num
      exact htends.eventually (eventually_gt_nhds h12)
    obtain ⟨N, hN⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
    refine ⟨(N:ℝ), by exact_mod_cast hN.2, ?_⟩
    rw [hsN_def] at hN
    exact hN.1.le
  refine ⟨R, hR_pos, fun x => ?_⟩
  -- Integrand `F y := pX y * g (x - y)` is nonnegative + integrable.
  set F : ℝ → ℝ := fun y => pX y * g (x - y) with hF_def
  have hF_nn : ∀ y, 0 ≤ F y := fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ (x - y))
  have hF_int : Integrable F volume :=
    convDensityAdd_integrand_integrable pX hpX_int ⟨s, hs.le⟩ x
  -- STEP 2: drop the integral down to the box `Icc (-R) R`.
  have hbox_le : (∫ y in Set.Icc (-R) R, F y ∂volume) ≤ ∫ y, F y ∂volume := by
    apply setIntegral_le_integral hF_int
    exact Filter.Eventually.of_forall hF_nn
  -- STEP 3: on the box, `g (x-y) ≥ g (|x| + R)`, so
  --   `∫_box F ≥ g(|x|+R) · ∫_box pX ≥ g(|x|+R) · (1/2)`.
  have hbox_lb : (1/2) * g (|x| + R) ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := by
    -- on the box, `g (|x| + R) ≤ g (x - y) = g (x - y)` (monotonicity in `|·|`).
    have hxR_nn : 0 ≤ |x| + R := add_nonneg (abs_nonneg x) hR_pos.le
    -- pointwise lower bound of the integrand on the box: `pX y · g(|x|+R) ≤ F y`.
    have hpt : ∀ y ∈ Set.Icc (-R) R, pX y * g (|x| + R) ≤ F y := by
      intro y hy
      have hy_abs : |x - y| ≤ |x| + R := by
        have h1 : |x - y| ≤ |x| + |y| := abs_sub _ _
        have h2 : |y| ≤ R := abs_le.mpr ⟨hy.1, hy.2⟩
        linarith
      have hmono : g (|x| + R) ≤ g (x - y) := by
        rw [hg_def]
        refine gaussianPDFReal_antitone_abs ⟨s, hs.le⟩ ?_
        rwa [abs_of_nonneg hxR_nn]
      exact mul_le_mul_of_nonneg_left hmono (hpX_nn y)
    -- integrate the pointwise bound over the box.
    have hpX_int_box : IntegrableOn pX (Set.Icc (-R) R) volume := hpX_int.integrableOn
    have hlb_int : IntegrableOn (fun y => pX y * g (|x| + R)) (Set.Icc (-R) R) volume :=
      hpX_int_box.mul_const _
    have hF_int_box : IntegrableOn F (Set.Icc (-R) R) volume := hF_int.integrableOn
    have hstep : (∫ y in Set.Icc (-R) R, pX y * g (|x| + R) ∂volume)
        ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := by
      apply setIntegral_mono_on hlb_int hF_int_box measurableSet_Icc
      exact hpt
    -- pull `g(|x|+R)` out of the box integral.
    rw [integral_mul_const] at hstep
    -- `∫_box pX ≥ 1/2`, `g ≥ 0`, so `g(|x|+R)·(1/2) ≤ g(|x|+R)·∫_box pX ≤ ∫_box F`.
    have hg_nn : 0 ≤ g (|x| + R) := by rw [hg_def]; exact gaussianPDFReal_nonneg 0 _ _
    have hhalf : g (|x| + R) * (1/2) ≤ g (|x| + R) * ∫ y in Set.Icc (-R) R, pX y ∂volume :=
      mul_le_mul_of_nonneg_left hR_mass hg_nn
    calc (1/2) * g (|x| + R)
        = g (|x| + R) * (1/2) := by ring
      _ ≤ g (|x| + R) * ∫ y in Set.Icc (-R) R, pX y ∂volume := hhalf
      _ = (∫ y in Set.Icc (-R) R, pX y ∂volume) * g (|x| + R) := by rw [mul_comm]
      _ ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := hstep
  calc (1/2) * g (|x| + R)
      ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := hbox_lb
    _ ≤ ∫ y, F y ∂volume := hbox_le
    _ = convDensityAdd pX g x := rfl

end InformationTheory.Shannon.FisherInfoV2
