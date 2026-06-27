import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijn
import InformationTheory.Shannon.FisherInfo.DeBruijnGeneral
import InformationTheory.Shannon.FisherInfo.DeBruijnHeatFlow
import InformationTheory.Shannon.FisherInfo.OfDensity
import InformationTheory.Shannon.FisherConvBound
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecificLimits.Basic

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

open MeasureTheory Real ProbabilityTheory InformationTheory Filter
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open InformationTheory.Shannon.EPIL3Integration
open scoped ENNReal NNReal Real Topology

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

/-- Interval-integrability of the heat-flow path integrand `(1/2)·J(pX ∗ g_t)` on `[0, T]`.

The integrand is nonnegative and equals the derivative of the heat-flow entropy
`f s = h(X + √s·Z)` at every `t > 0` (per-time de Bruijn). On each `[ε, T]` with `ε > 0` it is
bounded (by `(1/2)/ε` via `gaussianConv_fisher_le_inv_var`) and measurable (it agrees with
`deriv f`), hence interval-integrable; the subinterval integral equals `f T − f ε` by FTC. As
`ε ↓ 0` the endpoint `f ε → f 0` by the genuine G2 continuity, so the subinterval integrals are
bounded uniformly, and the improper-integral criterion
`integrableOn_Ioc_of_intervalIntegral_norm_bounded_left` upgrades to integrability on `(0, T)`.
This routes only through the per-time identity, never the integrated form, so it is non-circular.

@audit:ok -/
private lemma debruijnHeatPath_intervalIntegrable
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x ↦ ENNReal.ofReal (pX x)))
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y ↦ y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x ↦ Real.negMulLog (pX x)) volume)
    (T : ℝ) :
    IntervalIntegrable
      (fun t ↦ (1 / 2 : ℝ) * fisherInfoOfDensityReal (convDensityAdd pX (heatKernel t)))
      volume 0 T := by
  set g : ℝ → ℝ :=
    fun t ↦ (1 / 2 : ℝ) * fisherInfoOfDensityReal (convDensityAdd pX (heatKernel t)) with hg_def
  have hg_nonneg : ∀ t : ℝ, 0 ≤ g t := by
    intro t
    change 0 ≤ (1 / 2 : ℝ) * fisherInfoOfDensityReal (convDensityAdd pX (heatKernel t))
    exact mul_nonneg (by norm_num) (fisherInfoOfDensityReal_nonneg _)
  have hfi0 : fisherInfoOfDensityReal (fun _ : ℝ ↦ (0 : ℝ)) = 0 := by
    unfold fisherInfoOfDensityReal
    rw [fisherInfoOfDensity_zero, ENNReal.toReal_zero]
  have hg0 : ∀ t : ℝ, t ≤ 0 → g t = 0 := by
    intro t ht
    have hconv0 : convDensityAdd pX (heatKernel t) = fun _ ↦ (0 : ℝ) := by
      funext z
      change (∫ x, pX x * heatKernel t (z - x) ∂volume) = 0
      have hz : ∀ x : ℝ, pX x * heatKernel t (z - x) = 0 := by
        intro x
        have hk : heatKernel t (z - x) = 0 := by
          change (if h : 0 < t then gaussianPDFReal 0 ⟨t, h.le⟩ (z - x) else 0) = 0
          rw [dif_neg (not_lt.mpr ht)]
        rw [hk, mul_zero]
      simp [hz]
    change (1 / 2 : ℝ) * fisherInfoOfDensityReal (convDensityAdd pX (heatKernel t)) = 0
    rw [hconv0, hfi0, mul_zero]
  have hJbound : ∀ x : ℝ, 0 < x →
      fisherInfoOfDensityReal (convDensityAdd pX (heatKernel x)) ≤ 1 / x := by
    intro x hx
    have hbound := gaussianConv_fisher_le_inv_var pX hpX_nn hpX_meas hpX_int hpX_mass hx
    have hker : convDensityAdd pX (heatKernel x)
        = convDensityAdd pX (gaussianPDFReal 0 ⟨x, hx.le⟩) := by
      congr 1; funext y; exact heatKernel_def_gaussianPDFReal hx y
    rw [hker]
    change (fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨x, hx.le⟩))).toReal ≤ 1 / x
    calc (fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨x, hx.le⟩))).toReal
        ≤ (ENNReal.ofReal (1 / x)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
      _ = 1 / x := ENNReal.toReal_ofReal (by positivity)
  rcases (lt_or_ge 0 T).symm with hT | hT
  · -- `T ≤ 0`: the integrand is identically zero on `Ι 0 T`.
    refine (intervalIntegrable_congr (f := fun _ : ℝ ↦ (0 : ℝ)) ?_).mp intervalIntegrable_const
    intro x hx
    have hxle : x ≤ 0 := by
      have h2 := hx.2
      rwa [max_eq_left hT] at h2
    exact (hg0 x hxle).symm
  · -- `0 < T`: subinterval FTC plus the improper-integral criterion.
    set f : ℝ → ℝ :=
      fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)) with hf_def
    set a : ℕ → ℝ := fun n ↦ T / ((n : ℝ) + 1) with ha_def
    have han_pos : ∀ n, 0 < a n := fun n ↦ div_pos hT (by positivity)
    have han_le : ∀ n, a n ≤ T := fun n ↦
      div_le_self hT.le (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have ha_tendsto : Tendsto a atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ ↦ T * (1 / ((n : ℝ) + 1))) atTop (𝓝 (T * 0)) :=
        Filter.Tendsto.const_mul T tendsto_one_div_add_atTop_nhds_zero_nat
      rw [mul_zero] at h
      refine h.congr (fun n ↦ ?_)
      change T * (1 / ((n : ℝ) + 1)) = T / ((n : ℝ) + 1)
      rw [← div_eq_mul_one_div]
    have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (g x) x := by
      intro x hx
      have hd := debruijn_identity_per_time X Z hX hZ hXZ hZ_law pX hpX_nn hpX_meas hpX_law hpX_mom
        hx
      have hker : convDensityAdd pX (gaussianPDFReal 0 ⟨x, hx.le⟩)
          = convDensityAdd pX (heatKernel x) := by
        congr 1; funext y; exact (heatKernel_def_gaussianPDFReal hx y).symm
      rw [hker] at hd
      exact hd
    have hII : ∀ n, IntervalIntegrable g volume (a n) T := by
      intro n
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (han_le n)]
      change Integrable g (volume.restrict (Set.Ioc (a n) T))
      refine ⟨?_, ?_⟩
      · refine (measurable_deriv f).aestronglyMeasurable.congr ?_
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
        intro x hx
        exact (hderiv x ((han_pos n).trans hx.1)).deriv
      · refine HasFiniteIntegral.of_bounded (C := (1 / 2 : ℝ) * (1 / a n)) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
        intro x hx
        have hxpos : 0 < x := (han_pos n).trans hx.1
        rw [Real.norm_of_nonneg (hg_nonneg x)]
        change (1 / 2 : ℝ) * fisherInfoOfDensityReal (convDensityAdd pX (heatKernel x))
            ≤ (1 / 2 : ℝ) * (1 / a n)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact le_trans (hJbound x hxpos) (one_div_le_one_div_of_le (han_pos n) hx.1.le)
    have hFTC : ∀ n, (∫ x in Set.Ioc (a n) T, ‖g x‖) = f T - f (a n) := by
      intro n
      have hnorm : (∫ x in Set.Ioc (a n) T, ‖g x‖) = ∫ x in Set.Ioc (a n) T, g x :=
        setIntegral_congr_fun measurableSet_Ioc (fun x _ ↦ Real.norm_of_nonneg (hg_nonneg x))
      rw [hnorm, ← intervalIntegral.integral_of_le (han_le n)]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ ?_) (hII n)
      rw [Set.uIcc_of_le (han_le n)] at hx
      exact hderiv x (lt_of_lt_of_le (han_pos n) hx.1)
    have hcont0 : Tendsto f (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (f 0)) :=
      heatFlowDifferentialEntropy_continuousWithinAt_zero X Z P hX hZ hXZ
        1 one_pos hZ_law pX hpX_nn hpX_meas hpX_law hpX_int hpX_mass hpX_mom hpX_ent
    have ha_within : Tendsto a atTop (𝓝[Set.Ioi (0 : ℝ)] 0) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨ha_tendsto, Filter.Eventually.of_forall (fun n ↦ Set.mem_Ioi.mpr (han_pos n))⟩
    have htendsto_f : Tendsto (fun n ↦ f (a n)) atTop (𝓝 (f 0)) := hcont0.comp ha_within
    have htendsto_sub : Tendsto (fun n ↦ f T - f (a n)) atTop (𝓝 (f T - f 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds htendsto_f
    have htendsto_int :
        Tendsto (fun n ↦ ∫ x in Set.Ioc (a n) T, ‖g x‖) atTop (𝓝 (f T - f 0)) :=
      htendsto_sub.congr (fun n ↦ (hFTC n).symm)
    obtain ⟨I, hI⟩ := htendsto_int.isBoundedUnder_le
    have hfi : ∀ n, IntegrableOn g (Set.Ioc (a n) T) volume := fun n ↦
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (han_le n)).mp (hII n)
    have hres : IntegrableOn g (Set.Ioc 0 T) volume :=
      integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hfi ha_tendsto hI
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact hres

/-- **General a.c. path-regularity producer.** For `X ⊥ Z` with `Z ∼ 𝒩(0, 1)` and an explicit
probability density `pX` of `X` with finite second moment and finite differential entropy
(`hpX_ent`), the heat-flow path is regular on `[0, T]`. The per-time regularity (`reg_t`) is the
density bundle `isRegularDeBruijnHypV2_of_density`; the heat-flow entropy continuity (`cont`)
combines the genuine endpoint continuity
`heatFlowDifferentialEntropy_continuousWithinAt_zero` (at `t = 0⁺`) with the interior continuity
from the per-time de Bruijn `HasDerivAt`.

The interval-integrability of the path integrand `(1/2)·J(X + √t·Z)` (`integrable`) is closed
genuinely by `debruijnHeatPath_intervalIntegrable`: the integrand is nonnegative and, by the
convolution bound `J(pX ∗ g_t) ≤ 1/t` (`gaussianConv_fisher_le_inv_var`), bounded on each
`[ε, T]` (`ε > 0`); there it equals the derivative of the heat-flow entropy, so the FTC gives
`∫_ε^T = h(X + √T·Z) − h(X + √ε·Z)`, and the genuine G2 endpoint continuity (`ε ↓ 0`) bounds
these uniformly, upgrading to integrability on `(0, T)` via
`integrableOn_Ioc_of_intervalIntegral_norm_bounded_left`. This routes only through the per-time
de Bruijn identity, never its integrated form, so it is non-circular.

@audit:ok -/
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
  integrable :=
    debruijnHeatPath_intervalIntegrable X Z hX hZ hXZ hZ_law pX hpX_nn hpX_meas hpX_law
      hpX_int hpX_mass hpX_mom hpX_ent T

/-- **Integrated de Bruijn identity (general a.c., Cover–Thomas Theorem 17.7.2).** The integrated
form `h(X + √T·Z) − h(X) = ∫₀ᵀ (1/2)·J(X + √t·Z) dt` for a general absolutely-continuous
`X`, obtained by applying `debruijnIntegrationIdentity_holds` to the general path-regularity
producer `isDeBruijnPathRegular_of_heat_flow` (now fully genuine).

References: [CoverThomas2006] Theorem 17.7.2.

@audit:ok -/
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
