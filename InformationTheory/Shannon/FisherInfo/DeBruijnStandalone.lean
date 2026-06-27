import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijn
import InformationTheory.Shannon.FisherInfo.DeBruijnGeneral
import InformationTheory.Shannon.FisherInfo.DeBruijnHeatFlow
import InformationTheory.Shannon.FisherInfo.OfDensity
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# de Bruijn identity — standalone headlines (Cover–Thomas Theorem 17.7.2)

This file assembles the genuine, sorry-free parts already present in the project into clean,
self-contained statements of the **de Bruijn identity** along the Gaussian heat flow:

* the per-time identity `(d/dt) h(X + √t·Z) = (1/2)·J(X + √t·Z)`, and
* its integrated form `h(X + √T·Z) − h(X) = ∫₀ᵀ (1/2)·J(X + √t·Z) dt`.

The per-time analytic core is the existing genuine assembly `debruijnIdentityV2_holds_assembled`
(routed through `deBruijn_identity_v2`); the integrated form is the existing FTC assembly
`debruijnIntegrationIdentity_holds`. The genuine content of this file is the **non-vacuity**
witness: `IsDeBruijnPathRegular` previously had no inhabitant, so the integrated identity was
vacuity-risk. We construct the Gaussian inhabitant (gateway atom) genuinely, and a general
absolutely-continuous producer in which only the path-integrand interval-integrability remains a
localized residual.

## Main statements

* `debruijn_identity_per_time` — the per-time de Bruijn identity for a general probability
  density `pX`, with the V2 Fisher information on the right.
* `isDeBruijnPathRegular_gaussian` — the Gaussian inhabitant of `IsDeBruijnPathRegular` (gateway
  atom, fully genuine).
* `debruijn_identity_integrated_gaussian` — the integrated de Bruijn identity for a Gaussian `X`
  (fully genuine).
* `isDeBruijnPathRegular_of_heat_flow` — the general a.c. producer (`reg_t`/`cont` genuine; the
  interval-integrability field is a localized residual).
* `debruijn_identity_integrated` — the integrated de Bruijn identity for a general a.c. `X`.

## References

[CoverThomas2006] Theorem 17.7.2.
-/

namespace InformationTheory.Shannon.FisherInfo

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open InformationTheory.Shannon.EPIL3Integration
open scoped ENNReal NNReal Real

/-! ## Density-supplied de Bruijn regularity -/

/-- The V2 de Bruijn regularity bundle from an explicit Lebesgue density `pX` of `X`:
a probability density (nonnegative, measurable) carrying the `withDensity` law `pX_law` and a
finite second moment `hpX_mom`, together with the standard-normal law of `Z`. The density witness
`density_t` is pinned to the smooth convolution `convDensityAdd pX g_t`, so `density_t_eq` is
`rfl`.

@audit:ok -/
noncomputable def isRegularDeBruijnHypV2_of_density
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    IsRegularDeBruijnHypV2 X Z P t where
  Z_law := hZ_law
  density_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)
  density_t_eq := fun _ _ ↦ rfl
  pX := pX
  pX_nn := hpX_nn
  pX_meas := hpX_meas
  pX_law := hpX_law
  pX_mom := hpX_mom

/-! ## Phase 3 — de Bruijn per-time standalone -/

/-- **de Bruijn identity (per-time, density form, Cover–Thomas Theorem 17.7.2).**

For `X ⊥ Z` with `Z ∼ 𝒩(0, 1)` and an explicit Lebesgue density `pX` of `X` (a probability
density with finite second moment), the heat-flow entropy `h(X + √s·Z)` has, at every time
`t > 0`, derivative `(1/2)·J(X + √t·Z)` with the V2 Fisher information of the smooth convolution
density `pX ∗ g_t`.

The class is non-vacuous: Gaussian `X ∼ 𝒩(m, v)` instantiates it with
`pX = gaussianPDFReal m v` (see `isDeBruijnPathRegular_gaussian`), and every
absolutely-continuous `X` with finite second
moment supplies `pX = (P.map X).rnDeriv volume` (see `isDeBruijnPathRegular_of_heat_flow`).

References: [CoverThomas2006] Theorem 17.7.2.

@audit:ok -/
@[entry_point]
theorem debruijn_identity_per_time
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1 / 2) * fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := by
  exact deBruijn_identity_v2 X Z hX hZ hXZ ht
    (isRegularDeBruijnHypV2_of_density hZ_law pX hpX_nn hpX_meas hpX_law hpX_mom ht)

/-! ## Phase 4 — gateway atom: Gaussian path-regularity -/

/-- **Gateway atom (gaussian).** The Gaussian inhabitant of `IsDeBruijnPathRegular`: for
`X ∼ 𝒩(m, v)` (`v ≠ 0`), `Z ∼ 𝒩(0, 1)`, `X ⊥ Z`, the heat-flow path is regular on `[0, T]`.
The density witness path is `fPath t = gaussianPDFReal m (v + t)`, whose Fisher information is the
bounded continuous closed form `1 / (v + t)`, so the path integrand is interval-integrable; the
heat-flow entropy is the closed form `(1/2)·log(2π e (v + s))`, continuous on `[0, T]`.

This witness shows `IsDeBruijnPathRegular` (and hence `debruijnIntegrationIdentity_holds`) is
non-vacuous.

@audit:ok -/
noncomputable def isDeBruijnPathRegular_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1)
    (T : ℝ) :
    IsDeBruijnPathRegular X Z P T where
  fPath := fun t ↦ gaussianPDFReal m (v + Real.toNNReal t)
  reg_t := by
    intro t ht
    refine ⟨isRegularDeBruijnHypV2_family_of_gaussian X Z hX hZ hXZ hv hX_law hZ_law t ht.1, ?_⟩
    have htn : (⟨t, ht.1.le⟩ : ℝ≥0) = Real.toNNReal t := by
      apply NNReal.coe_injective
      change t = (Real.toNNReal t : ℝ)
      rw [Real.coe_toNNReal _ ht.1.le]
    change gaussianPDFReal m (v + ⟨t, ht.1.le⟩) = gaussianPDFReal m (v + Real.toNNReal t)
    rw [htn]
  cont := by
    have hvpos : (0 : ℝ) < v := by
      have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
    have hG : ContinuousOn (fun s ↦ (1 / 2 : ℝ)
        * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))) (Set.Icc 0 T) := by
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.log ?_ ?_
      · fun_prop
      · intro s hs
        have hpos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s) := by
          have : (0 : ℝ) < (v : ℝ) + s := by linarith [hs.1]
          positivity
        exact hpos.ne'
    refine hG.congr ?_
    intro s hs
    exact differentialEntropy_gaussianConvolution_of_gaussian hX hZ hXZ hv hX_law hZ_law hs.1
  integrable := by
    have hne : ∀ t : ℝ, (v + Real.toNNReal t) ≠ 0 := by
      intro t h
      exact hv (add_eq_zero.mp h).1
    have hrw : (fun t : ℝ ↦ (1 / 2 : ℝ)
          * fisherInfoOfDensityReal (gaussianPDFReal m (v + Real.toNNReal t)))
        = (fun t : ℝ ↦ (1 / 2 : ℝ) * (1 / ((v : ℝ) + max t 0))) := by
      funext t
      rw [fisherInfoOfDensityReal_gaussianPDFReal m (hne t), NNReal.coe_add, Real.coe_toNNReal']
    change IntervalIntegrable (fun t ↦ (1 / 2 : ℝ)
        * fisherInfoOfDensityReal (gaussianPDFReal m (v + Real.toNNReal t))) volume 0 T
    rw [hrw]
    have hvpos : (0 : ℝ) < v := by
      have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
    apply Continuous.intervalIntegrable
    refine Continuous.mul continuous_const ?_
    refine Continuous.div continuous_const ?_ ?_
    · exact continuous_const.add (continuous_id'.max continuous_const)
    · intro x
      have : (0 : ℝ) < (v : ℝ) + max x 0 := by
        have : (0 : ℝ) ≤ max x 0 := le_max_right _ _
        linarith
      exact this.ne'

/-- **Integrated de Bruijn identity (gaussian, Cover–Thomas Theorem 17.7.2).** The integrated
form `h(X + √T·Z) − h(X) = ∫₀ᵀ (1/2)·J(X + √t·Z) dt` for a Gaussian `X ∼ 𝒩(m, v)`,
obtained by
applying `debruijnIntegrationIdentity_holds` to the Gaussian path-regularity witness.

References: [CoverThomas2006] Theorem 17.7.2.

@audit:ok -/
@[entry_point]
theorem debruijn_identity_integrated_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ (fPath : ℝ → ℝ → ℝ),
      ∀ (h_X h_target : ℝ),
        h_X = differentialEntropy (P.map X) →
        h_target = differentialEntropy (P.map (gaussianConvolution X Z T)) →
        h_target - h_X
          = ∫ t in Set.Ioo 0 T, (1 / 2)
            * (fisherInfoOfMeasureV2
                (P.map (gaussianConvolution X Z t)) (fPath t)).toReal ∂volume :=
  debruijnIntegrationIdentity_holds X Z hX hZ hXZ T hT
    (isDeBruijnPathRegular_gaussian X Z hX hZ hXZ hv hX_law hZ_law T)

/-! ## Phase 4 — general absolutely-continuous producer -/

/-- **General a.c. path-regularity producer.** For `X ⊥ Z` with `Z ∼ 𝒩(0, 1)` and an explicit
probability density `pX` of `X` with finite second moment and finite differential entropy
(`hpX_ent`), the heat-flow path is regular on `[0, T]`. The per-time regularity (`reg_t`) is the
density bundle `isRegularDeBruijnHypV2_of_density`; the heat-flow entropy continuity (`cont`)
combines the genuine endpoint continuity
`heatFlowDifferentialEntropy_continuousWithinAt_zero` (at `t = 0⁺`) with the interior continuity
from the per-time de Bruijn `HasDerivAt`.

The interval-integrability of the path integrand `(1/2)·J(X + √t·Z)` near `t = 0⁺` is the
single localized residual: the convolution bound `J(pX ∗ g_t) ≤ 1/t`
(`gaussianConv_fisher_le_inv_var`) diverges at `0`, and an integrable-singularity argument
independent of the de Bruijn identity is
not available in Mathlib (the integral is finite precisely because it equals
`2·(h(X + √T·Z) − h(X))`, which would be circular to invoke here).

@residual(plan:stam-debruijn-standalone-moonshot-plan) -/
noncomputable def isDeBruijnPathRegular_of_heat_flow
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x ↦ Real.negMulLog (pX x)) volume)
    (T : ℝ) :
    IsDeBruijnPathRegular X Z P T where
  fPath := fun t ↦ convDensityAdd pX (heatKernel t)
  reg_t := by
    intro t ht
    refine
      ⟨isRegularDeBruijnHypV2_of_density hZ_law pX hpX_nn hpX_meas hpX_law hpX_mom ht.1, ?_⟩
    change convDensityAdd pX (gaussianPDFReal 0 (⟨t, ht.1.le⟩ : ℝ≥0))
        = convDensityAdd pX (heatKernel t)
    congr 1
    funext x
    exact (heatKernel_def_gaussianPDFReal ht.1 x).symm
  cont := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · -- endpoint `s = 0`: genuine G2 continuity, lifted from `Ioi 0` to `Icc 0 T`.
      have hG2 :
          ContinuousWithinAt
            (fun t : ℝ ↦ differentialEntropy (P.map (fun ω ↦ X ω + Real.sqrt t * Z ω)))
            (Set.Ioi (0 : ℝ)) 0 :=
        heatFlowDifferentialEntropy_continuousWithinAt_zero X Z P hX hZ hXZ
          1 one_pos hZ_law pX hpX_nn hpX_meas hpX_law hpX_int hpX_mass hpX_mom hpX_ent
      have hsub : Set.Icc (0 : ℝ) T ⊆ insert (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
        intro x hx
        rcases eq_or_lt_of_le hx.1 with h | h
        · exact Set.mem_insert_iff.mpr (Or.inl h.symm)
        · exact Set.mem_insert_iff.mpr (Or.inr h)
      have := (hG2.insert').mono hsub
      rw [← h0]
      exact this
    · -- interior `s > 0`: continuity from the per-time de Bruijn `HasDerivAt`.
      have h_reg := isRegularDeBruijnHypV2_of_density hZ_law pX hpX_nn hpX_meas hpX_law hpX_mom hpos
      have hd := deBruijn_identity_v2 X Z hX hZ hXZ hpos h_reg
      exact hd.continuousAt.continuousWithinAt
  integrable := by
    -- @residual(plan:stam-debruijn-standalone-moonshot-plan)
    sorry

/-- **Integrated de Bruijn identity (general a.c., Cover–Thomas Theorem 17.7.2).** The integrated
form `h(X + √T·Z) − h(X) = ∫₀ᵀ (1/2)·J(X + √t·Z) dt` for a general absolutely-continuous
`X`, obtained by applying `debruijnIntegrationIdentity_holds` to the general path-regularity
producer.
Inherits the path-integrand integrability residual of `isDeBruijnPathRegular_of_heat_flow`.

@residual(plan:stam-debruijn-standalone-moonshot-plan)

References: [CoverThomas2006] Theorem 17.7.2. -/
@[entry_point]
theorem debruijn_identity_integrated
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x ↦ Real.negMulLog (pX x)) volume)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ (fPath : ℝ → ℝ → ℝ),
      ∀ (h_X h_target : ℝ),
        h_X = differentialEntropy (P.map X) →
        h_target = differentialEntropy (P.map (gaussianConvolution X Z T)) →
        h_target - h_X
          = ∫ t in Set.Ioo 0 T, (1 / 2)
            * (fisherInfoOfMeasureV2
                (P.map (gaussianConvolution X Z t)) (fPath t)).toReal ∂volume :=
  debruijnIntegrationIdentity_holds X Z hX hZ hXZ T hT
    (isDeBruijnPathRegular_of_heat_flow X Z hX hZ hXZ hZ_law pX hpX_nn hpX_meas hpX_law
      hpX_int hpX_mass hpX_mom hpX_ent T)

end InformationTheory.Shannon.FisherInfo
