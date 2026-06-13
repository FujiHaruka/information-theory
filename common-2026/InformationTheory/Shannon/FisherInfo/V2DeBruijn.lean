import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.EPI.Conv.Density
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Fisher information V2 — measure-keyed wrapper and de Bruijn identity

Builds on the density-as-input Fisher information of `FisherInfoV2.lean` to define a
measure-keyed wrapper, the heat-flow convolution path `X + √t · Z`, the V2 de Bruijn
regularity predicate, and the Gaussian discharge of the de Bruijn identity.

## Main definitions

* `fisherInfoOfMeasureV2` — the Fisher information of a measure carrying an explicit smooth
  density witness.
* `gaussianConvolution` — the heat-flow path `X + √t · Z`.
* `IsRegularDeBruijnHypV2` — the V2 de Bruijn regularity predicate, whose right-hand side
  uses the V2 Fisher information.
* `IsDeBruijnPathRegular` — the path-regularity bundle for the integrated de Bruijn
  identity.

## Main statements

* `fisherInfoOfMeasureV2_gaussianReal` — the Gaussian closed form `1 / v`.
* `gaussianConvolution_law_of_gaussian` — the law of `X + √t · Z` is `𝒩(m, v + t)` when `X`
  is Gaussian and `X ⊥ Z`.
* `deBruijn_identity_v2_gaussian` — the de Bruijn identity for a Gaussian `X`,
  `(d/dt) h(X + √t · Z) = 1 / (2(v + t))`.
-/

namespace InformationTheory.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open scoped ENNReal NNReal Real

/-! ## Measure-keyed wrapper -/

/-- The Fisher information of a measure `μ` carrying an explicit smooth density witness
`f`, computed as `fisherInfoOfDensity f`. The witness is syntactically unrelated to
`μ.rnDeriv volume`; the caller is responsible for the relevant a.e.-equality. -/
noncomputable def fisherInfoOfMeasureV2 (_μ : Measure ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  fisherInfoOfDensity f

/-- Real-valued projection of `fisherInfoOfMeasureV2`. -/
noncomputable def fisherInfoOfMeasureV2Real (_μ : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  fisherInfoOfDensityReal f

/-- Unfold lemma. -/
@[entry_point]
theorem fisherInfoOfMeasureV2_def (μ : Measure ℝ) (f : ℝ → ℝ) :
    fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f := rfl

@[entry_point]
theorem fisherInfoOfMeasureV2Real_def (μ : Measure ℝ) (f : ℝ → ℝ) :
    fisherInfoOfMeasureV2Real μ f = fisherInfoOfDensityReal f := rfl

/-- The Gaussian Fisher information in measure-keyed form:
`fisherInfoOfMeasureV2 (gaussianReal m v) (gaussianPDFReal m v) = ENNReal.ofReal (1 / v)`. -/
@[entry_point]
theorem fisherInfoOfMeasureV2_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfMeasureV2 (gaussianReal m v) (gaussianPDFReal m v)
      = ENNReal.ofReal (1 / (v : ℝ)) := by
  unfold fisherInfoOfMeasureV2
  exact fisherInfoOfDensity_gaussianPDFReal m hv

/-- Real-valued Gaussian Fisher info via V2. -/
@[entry_point]
theorem fisherInfoOfMeasureV2Real_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfMeasureV2Real (gaussianReal m v) (gaussianPDFReal m v) = 1 / (v : ℝ) := by
  unfold fisherInfoOfMeasureV2Real
  exact fisherInfoOfDensityReal_gaussianPDFReal m hv

/-! ## Heat-flow path -/

/-- The heat-flow convolution path `X + √t · Z`, the `t`-parametrised family underlying the
de Bruijn identity (Cover–Thomas 17.7.2). For `Z ∼ 𝒩(0, 1)` and `X ⊥ Z`, the law
`P.map (gaussianConvolution X Z t)` is the convolution of `P.map X` with `𝒩(0, t)`. -/
noncomputable def gaussianConvolution {α : Type*} (X Z : α → ℝ) (t : ℝ) : α → ℝ :=
  fun ω => X ω + Real.sqrt t * Z ω

/-- The law of `X + √t · Z` is `𝒩(m, v + t)` when `X ∼ 𝒩(m, v)`, `Z ∼ 𝒩(0, 1)`, and
`X ⊥ Z`. -/
@[entry_point]
theorem gaussianConvolution_law_of_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) :
    P.map (gaussianConvolution X Z t)
      = gaussianReal m (v + ⟨t, ht⟩) := by
  -- Step 1: law of `√t · Z` is `𝒩(0, t)`.
  have h_sqrt_nn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h_sqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  -- `P.map (fun ω => √t · Z ω) = gaussianReal (√t · 0) ((√t)² · 1) = gaussianReal 0 t`.
  have h_sqrtZ_map : Measure.map (fun ω => Real.sqrt t * Z ω) P
      = gaussianReal 0 ⟨t, ht⟩ := by
    -- `P.map (c · Z) = (P.map Z).map (c · ·)`.
    have h_compose : Measure.map (fun ω => Real.sqrt t * Z ω) P
        = (P.map Z).map (fun y => Real.sqrt t * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt t * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hZ
      -- `(P.map Z).map (fun y => √t * y) = P.map ((fun y => √t * y) ∘ Z)`.
      -- The RHS is `P.map (fun ω => √t * Z ω)`.
      simpa [Function.comp] using this.symm
    rw [h_compose, hZ_law, gaussianReal_map_const_mul]
    -- Need: `gaussianReal (√t · 0) (⟨(√t)², _⟩ * 1) = gaussianReal 0 ⟨t, ht⟩`.
    congr 1
    · ring
    · -- `⟨(√t)², _⟩ * 1 = ⟨t, ht⟩` as `ℝ≥0`.
      rw [mul_one]
      apply NNReal.eq
      exact h_sqrt_sq
  -- Step 2: independence `X ⊥ (√t · Z)`.
  have hX_aem : AEMeasurable X P := hX.aemeasurable
  have hZ_aem : AEMeasurable Z P := hZ.aemeasurable
  have h_indep_X_sqrtZ : IndepFun X (fun ω => Real.sqrt t * Z ω) P :=
    hXZ.comp measurable_id (measurable_const.mul measurable_id)
  -- Step 3: sum of independent Gaussians.
  have h_sum := gaussianReal_add_gaussianReal_of_indepFun (P := P)
    (X := X) (Y := fun ω => Real.sqrt t * Z ω)
    (m₁ := m) (m₂ := 0) (v₁ := v) (v₂ := ⟨t, ht⟩)
    h_indep_X_sqrtZ hX_law h_sqrtZ_map
  -- Step 4: `X + (√t · Z) = gaussianConvolution X Z t` pointwise.
  unfold gaussianConvolution
  have h_funext : (fun ω => X ω + Real.sqrt t * Z ω) = X + (fun ω => Real.sqrt t * Z ω) := by
    funext ω; rfl
  rw [h_funext, h_sum]
  congr 1
  · ring

/-! ## The de Bruijn regularity predicate -/

/-- The V2 de Bruijn regularity predicate. It carries a smooth density witness
`density_t : ℝ → ℝ` for the law of `X + √t · Z`, together with regularity preconditions on
`X`. The Fisher information on the right-hand side of the de Bruijn identity uses
`fisherInfoOfDensity` of an explicit density witness, so the Gaussian case evaluates to
`1 / v`. The de Bruijn identity itself is not a field of this predicate; it is proved
separately in `debruijnIdentityV2_holds_assembled`. -/
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (t : ℝ) where
  /-- `Z` is standard normal. -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- Smooth density witness for `P.map (X + √t · Z)`. -/
  density_t : ℝ → ℝ
  /-- A real density witness for `X` itself: the law of `X + √s · Z` is the convolution of
  `P.map X` with a Gaussian, expressed via `convDensityAdd pX g_σ`. Declared before
  `density_t_eq` so the latter's right-hand side can reference `pX`. -/
  pX : ℝ → ℝ
  /-- The density witness `pX` is nonnegative. -/
  pX_nn : ∀ x, 0 ≤ pX x
  /-- The density witness `pX` is measurable. -/
  pX_meas : Measurable pX
  /-- `X` has Lebesgue density `pX`. -/
  pX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  /-- The density witness `density_t` equals the smooth representative
  `convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)` — the convolution of `pX` with the
  time-`t` Gaussian heat kernel, which is the genuine density of `P.map (X + √t · Z)`.
  Pinning to this smooth convolution (rather than to the `Measure.rnDeriv` representative,
  which is generically non-differentiable) keeps `logDeriv` and hence
  `fisherInfoOfDensity density_t` nonzero. The positivity `0 < t` is taken as an argument
  since the structure does not carry it. -/
  density_t_eq : ∀ (ht : 0 < t) (x : ℝ),
    density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x
  /-- `X` has a finite second moment: `y ↦ y² · pX y` is volume-integrable. -/
  pX_mom : Integrable (fun y => y ^ 2 * pX y) volume

/-- The path-regularity bundle for the integrated de Bruijn identity, packaging the FTC
ingredients needed to integrate the per-time `debruijnIdentityV2_holds_assembled` derivative
along the heat-flow path `(0, T)`.

* `fPath` — the density witness path: `fPath t` is the density of
  `P.map (gaussianConvolution X Z t)`.
* `reg_t` — per-time V2 de Bruijn regularity at each interior `t ∈ (0, T)`, with
  `density_t = fPath t` so the per-time derivative value matches the integrand.
* `cont` — continuity of the heat-flow entropy on `[0, T]`.
* `integrable` — interval-integrability of the path integrand `(1/2) · J(X + √t · Z)` on
  `(0, T)`.

@audit:ok -/
structure IsDeBruijnPathRegular {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) where
  /-- Density witness path. -/
  fPath : ℝ → ℝ → ℝ
  /-- Per-time V2 de Bruijn regularity at each interior time, with the density
  witness pinned to `fPath t`. -/
  reg_t : ∀ t ∈ Set.Ioo (0 : ℝ) T,
    ∃ h_reg : IsRegularDeBruijnHypV2 X Z P t, h_reg.density_t = fPath t
  /-- Continuity of the heat-flow entropy on `[0, T]`. -/
  cont : ContinuousOn
    (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
    (Set.Icc 0 T)
  /-- The path integrand is interval-integrable. -/
  integrable : IntervalIntegrable
    (fun t => (1/2) * fisherInfoOfDensityReal (fPath t)) volume 0 T

/-! ## Gaussian discharge -/

/-- `(1/2) · log (2π e (v + s))` has derivative `1 / (2(v + s))` at `s` when `v + s > 0`. -/
@[entry_point]
theorem hasDerivAt_half_log_gaussian_entropy
    {v : ℝ≥0} (s : ℝ) (hvs : 0 < (v : ℝ) + s) :
    HasDerivAt
      (fun s' : ℝ => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s')))
      (1 / (2 * ((v : ℝ) + s))) s := by
  -- Inner derivative: `s' ↦ 2π e (v + s')` has derivative `2π e` at any point.
  have h_inner : HasDerivAt (fun s' : ℝ => 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s'))
      (2 * Real.pi * Real.exp 1) s := by
    have h_const : HasDerivAt (fun _ : ℝ => (v : ℝ)) 0 s := hasDerivAt_const s (v : ℝ)
    have h_id' : HasDerivAt (fun s' : ℝ => s') 1 s := hasDerivAt_id s
    have h_add : HasDerivAt (fun s' : ℝ => (v : ℝ) + s') (0 + 1) s := h_const.add h_id'
    have h_add' : HasDerivAt (fun s' : ℝ => (v : ℝ) + s') 1 s := by
      convert h_add using 1; ring
    have h_mul := h_add'.const_mul (2 * Real.pi * Real.exp 1)
    -- `h_mul : HasDerivAt _ (2πe * 1) s`. Rewrite to `2πe`.
    convert h_mul using 1; ring
  -- Apply log chain rule. Need `2π e (v + s) ≠ 0`.
  have h2πe_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have h_prod_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s) :=
    mul_pos h2πe_pos hvs
  have h_prod_ne : (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s)) ≠ 0 := h_prod_pos.ne'
  -- `Real.log ∘ inner` has derivative `(2πe) / (2π e (v + s)) = 1/(v + s)`.
  have h_log := h_inner.log h_prod_ne
  -- Simplify the derivative `(2π e) / (2π e (v + s)) = 1/(v + s)`.
  have h2πe_ne : (2 * Real.pi * Real.exp 1) ≠ 0 := h2πe_pos.ne'
  have h_vs_ne : ((v : ℝ) + s) ≠ 0 := hvs.ne'
  have h_simp : (2 * Real.pi * Real.exp 1) / (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))
      = 1 / ((v : ℝ) + s) := by
    field_simp
  rw [h_simp] at h_log
  -- Multiply by `1/2`.
  have h_half := h_log.const_mul (1/2 : ℝ)
  -- `h_half : HasDerivAt (fun s' => (1/2) * Real.log (2π e (v + s'))) ((1/2) * (1/(v + s))) s`.
  -- Rewrite `(1/2) * (1/(v + s)) = 1 / (2 * (v + s))`.
  have h_rewrite : (1/2 : ℝ) * (1 / ((v : ℝ) + s)) = 1 / (2 * ((v : ℝ) + s)) := by
    field_simp
  rw [h_rewrite] at h_half
  exact h_half

/-- The differential entropy of `gaussianReal m (v + s)` along the heat-flow path equals
`(1/2) · log (2π e (v + s))` for `s ≥ 0`. -/
@[entry_point]
theorem differentialEntropy_gaussianReal_heat_path
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    differentialEntropy (gaussianReal m (v + ⟨s, hs⟩))
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s)) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hvs_nn : v + ⟨s, hs⟩ ≠ 0 := by
    intro h
    have h_coe : ((v + ⟨s, hs⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; simp
    rw [NNReal.coe_add] at h_coe
    show False
    have : (v : ℝ) + s = 0 := by
      convert h_coe using 1
    linarith
  rw [InformationTheory.Shannon.differentialEntropy_gaussianReal m hvs_nn]
  -- The `(v + ⟨s, hs⟩ : ℝ≥0).toReal = (v : ℝ) + s` step.
  rw [show ((v + ⟨s, hs⟩ : ℝ≥0) : ℝ) = (v : ℝ) + s from NNReal.coe_add v ⟨s, hs⟩]

/-- The de Bruijn identity for a Gaussian `X` (hypothesis-free): for `X ∼ 𝒩(m, v)`,
`Z ∼ 𝒩(0, 1)`, `X ⊥ Z`, and `t > 0`,
`(d/dt) h(X + √t · Z) = (1/2) · J(𝒩(m, v + t)) = 1 / (2(v + t))`. -/
@[entry_point]
theorem deBruijn_identity_v2_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfMeasureV2Real (P.map (gaussianConvolution X Z t))
          (gaussianPDFReal m (v + ⟨t, ht.le⟩)))
      t := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hvs_pos : (0 : ℝ) < (v : ℝ) + t := by linarith
  -- Step 1: rewrite the LHS via the Gaussian heat-path entropy form.
  -- For each `s` on a neighbourhood of `t` (in fact for `s ≥ 0`), the law of
  -- `X + √s · Z` is `𝒩(m, v + s)` so the entropy is `(1/2) log (2π e (v + s))`.
  -- We use `HasDerivAt.congr_of_eventuallyEq` against this rewrite, restricted to `s > 0`
  -- (which holds on a neighbourhood of `t > 0`).
  have h_pos_nbhd : ∀ᶠ s in nhds t, (0 : ℝ) < s := eventually_gt_nhds ht
  -- The entropy along the heat path equals `(1/2) log (2π e (v + s))` for `s ≥ 0`.
  have h_entropy_eq : ∀ s : ℝ, 0 ≤ s →
      differentialEntropy (P.map (gaussianConvolution X Z s))
        = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s)) := by
    intro s hs
    have h_law := gaussianConvolution_law_of_gaussian hX hZ hXZ hX_law hZ_law hs
    rw [h_law]
    exact differentialEntropy_gaussianReal_heat_path m hv hs
  -- Reformulate as eventually-equality at `nhds t`.
  have h_eventually : (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      =ᶠ[nhds t] (fun s => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))) := by
    refine h_pos_nbhd.mono fun s hs => ?_
    exact h_entropy_eq s hs.le
  -- Step 2: apply `hasDerivAt_half_log_gaussian_entropy`.
  have h_deriv := hasDerivAt_half_log_gaussian_entropy (v := v) (s := t) hvs_pos
  -- Step 3: transfer via `HasDerivAt.congr_of_eventuallyEq`.
  have h_deriv' : HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      (1 / (2 * ((v : ℝ) + t))) t := by
    refine h_deriv.congr_of_eventuallyEq ?_
    exact h_eventually
  -- Step 4: identify the RHS `(1/2) * fisherInfoOfMeasureV2Real ... = 1/(2(v + t))`.
  have h_law_t := gaussianConvolution_law_of_gaussian hX hZ hXZ hX_law hZ_law ht.le
  have hvs_nn : v + ⟨t, ht.le⟩ ≠ 0 := by
    intro h
    have h_coe : ((v + ⟨t, ht.le⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; simp
    rw [NNReal.coe_add] at h_coe
    have : (v : ℝ) + t = 0 := by convert h_coe using 1
    linarith [v.coe_nonneg]
  have h_fisher : fisherInfoOfMeasureV2Real (P.map (gaussianConvolution X Z t))
      (gaussianPDFReal m (v + ⟨t, ht.le⟩))
        = 1 / ((v : ℝ) + t) := by
    unfold fisherInfoOfMeasureV2Real
    rw [fisherInfoOfDensityReal_gaussianPDFReal m hvs_nn]
    rw [show ((v + ⟨t, ht.le⟩ : ℝ≥0) : ℝ) = (v : ℝ) + t from NNReal.coe_add v ⟨t, ht.le⟩]
  rw [h_fisher]
  -- Now: `HasDerivAt ... ((1/2) * (1/(v + t))) t`. Match with `1/(2(v + t))`.
  have h_eq_rhs : (1/2 : ℝ) * (1 / ((v : ℝ) + t)) = 1 / (2 * ((v : ℝ) + t)) := by
    field_simp
  rw [h_eq_rhs]
  exact h_deriv'

end InformationTheory.Shannon.FisherInfoV2
