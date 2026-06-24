import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.FisherInfo.DeBruijnGeneral
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Case1.RatioLimit
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.Monotone.Basic
import InformationTheory.Shannon.EPI.Case1.TwoTime.Core
import InformationTheory.Shannon.EPI.Case1.TwoTime.Paths

/-!
# EPI case-1 two-time object — gap object and its derivative (§2–§3)

The two-time log-ratio gap object `twoTimeLogRatioGap` (formulation (b), `e^t`
closed form), its value at the left endpoint `twoTimeLogRatioGap_at_zero`, the
matched-sum law `matchedSum_law_eq` (the matched-sum perturbation reduces to a
single-noise heat flow of `X + Y`), and the derivative
`twoTimeLogRatioGap_hasDerivAt` / `twoTimeLogRatioGap_deriv_le_zero`. Verbatim
split of `TwoTime.lean` §2–§3; proofs unchanged. Builds on `TwoTimeCore.lean`
(§0) + `TwoTimePaths.lean` (§1). Umbrella: `TwoTime.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace InformationTheory.Shannon.EPICase1TwoTime

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.StamEPIBridge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap)
open InformationTheory.Shannon.EPIStamToBridge (entropyPower_hasDerivAt_of_diffEnt_hasDerivAt)
open InformationTheory.Shannon.EPICase1RatioLimit
  (entropyPower_rescaled_path_tendsto entropyPower_path_scaling IsRescaledPathRegular)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## §2 — Two-time log-ratio object (formulation (b), `e^t` closed form)

`R(t) = log N(s(t), r(t)) − log(N_X(0) + N_Y(0)) − t`, where the sum entropy
power `N(s,r) = entropyPower (P.map (X + √(s)·Z_X + Y + √(r)·Z_Y))` is taken at
the matched times `s = s(t)`, `r = r(t)`.

The third and second terms `log(N_X(0)+N_Y(0))` and `t` are closed forms in `t`
(constant minus `t`), so the only derivative content is `d/dt log N(s(t),r(t))`.
-/

/-- Sum entropy power of the independently-perturbed pair `X + √s·Z_X` and
`Y + √r·Z_Y`. -/
noncomputable def sumHeatFlowEP (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (s r : ℝ) : ℝ :=
  entropyPower (P.map (fun ω ↦ X ω + Real.sqrt s * Z_X ω + (Y ω + Real.sqrt r * Z_Y ω)))

/-- The two-time EPI log-ratio object `twoTimeLogRatioGap`
(formulation (b), `e^t` closed form), parametrized by the matched paths
`s r : ℝ → ℝ`.

`R(t) = log N(s(t),r(t)) − log(N_X(0) + N_Y(0)) − t`.

This is a plain `def` (no `sorry`): the paths `s, r` are inputs (constructed by
`matchedTimePath_exists`), not load-bearing hypotheses. Mirrors the structure of
`csiszarLogRatioGap` (`EPIL3Integration.lean:1380`) with the independent
two-time perturbation and the `e^t` reparametrization. -/
noncomputable def twoTimeLogRatioGap (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    (s r : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (sumHeatFlowEP X Y Z_X Z_Y P (s t) (r t))
    - Real.log (entropyPower (P.map X) + entropyPower (P.map Y))
    - t

/-- At `t = 0` the two-time gap reduces to the EPI bridge
form `log (eP(X+Y)) − log (eP X + eP Y)`.

Uses `s 0 = r 0 = 0` (`IsMatchedTimePath.start_zero`) so the perturbations
vanish (`√0 = 0`), `N(s 0, r 0) = eP(X+Y)`, and the `−t` term is `0`.
@audit:ok -/
theorem twoTimeLogRatioGap_at_zero
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r) :
    twoTimeLogRatioGap X Y Z_X Z_Y P s r 0
      = Real.log (entropyPower (P.map (fun ω ↦ X ω + Y ω)))
        - Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) := by
  unfold twoTimeLogRatioGap sumHeatFlowEP
  rw [h_path_X.start_zero, h_path_Y.start_zero]
  have h_sum_funext :
      (fun ω ↦ X ω + Real.sqrt 0 * Z_X ω + (Y ω + Real.sqrt 0 * Z_Y ω))
        = fun ω ↦ X ω + Y ω := by
    funext ω
    simp [Real.sqrt_zero]
  rw [h_sum_funext, sub_zero]

/-! ## §3 — Derivative of the two-time object

`R'(t) = J_S·(1/J_X + 1/J_Y) − 1` along the matched path, where
`J_S = J(X_s + Y_r)`, via per-component de Bruijn (`deBruijn_identity_v2`) +
chain rule (`HasDerivAt.comp` with `s' = 1/J_X`, `r' = 1/J_Y`). -/

/-- The matched-sum law equals the single-noise heat flow of `X+Y` at `τ = s_t + r_t`.

At a single time the matched-sum perturbation
`X + √(s_t)·Z_X + (Y + √(r_t)·Z_Y)` rearranges to
`(X+Y) + (√(s_t)·Z_X + √(r_t)·Z_Y)`, and the noise
`√(s_t)·Z_X + √(r_t)·Z_Y` — being a sum of independent centered Gaussians of
variances `s_t·v_X` and `r_t·v_Y` — has law `𝒩(0, s_t·v_X + r_t·v_Y)`
independent of `X+Y`. Taking unit-variance noises (`v_X = v_Y = 1`) and
`τ = s_t + r_t`, the matched-sum law equals the law of `(X+Y) + √τ·Z` for a unit
Gaussian `Z` independent of `X+Y`. This is the single-noise heat flow of `X+Y`
at time `τ`, which lets `J_S` be pinned by the existing single-noise
`IsDeBruijnRegularityHyp (X+Y) Z P`.

The hypotheses are regularity preconditions only (measurability, the unit-noise
laws of `Z_X`, `Z_Y`, `Z`, and the relevant independences). The conclusion is a
pure measure equality (an honest math fact); no derivative value or EPI content
is bundled. Body: Gaussian convolution additivity (`gaussianReal` add of the
independent noise variances) + reassociation of the `map`.

Honesty (2026-06-06 independence strengthening). The original `hXY_ZXZY :
IndepFun (X+Y) (Z_X+Z_Y) P` was insufficient: it gives independence of `X+Y`
from the *unscaled* sum `Z_X+Z_Y`, but the matched-sum noise is the *scaled*
combination `√s_t·Z_X + √r_t·Z_Y` (a different linear functional when
`s_t ≠ r_t`), whose independence from `X+Y` does not follow. The honest
precondition is joint independence of `X+Y` from the pair `(Z_X, Z_Y)`
(`hXY_ZXZY_pair`), from which the scaled-noise independence is recovered by
`IndepFun.comp` with the measurable map `(z₁, z₂) ↦ √s_t·z₁ + √r_t·z₂`. This is
a refinement of a regularity precondition, not a bundling of the conclusion.

Proof done (2026-06-06): genuinely closed via `gaussianReal_map_const_mul`
(scaled-noise law `√c·W ∼ 𝒩(0,c)`), `gaussianReal_add_gaussianReal_of_indepFun`
(LHS noise additivity), and `IndepFun.map_add_eq_map_conv_map` (split both sides
as `(P.map (X+Y)) ∗ 𝒩(0, s_t+r_t)`). `#print axioms` = sorryAx-free. -/
theorem matchedSum_law_eq
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (s_t r_t : ℝ) (hst : 0 < s_t) (hrt : 0 < r_t) :
    P.map (fun ω ↦ X ω + Real.sqrt s_t * Z_X ω + (Y ω + Real.sqrt r_t * Z_Y ω))
      = P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (s_t + r_t) * Z ω) := by
  classical
  -- Abbreviations.
  set B : Ω → ℝ := fun ω ↦ X ω + Y ω with hB
  have hB_meas : Measurable B := hX.add hY
  have hst0 : (0:ℝ) ≤ s_t := hst.le
  have hrt0 : (0:ℝ) ≤ r_t := hrt.le
  have hτ0 : (0:ℝ) ≤ s_t + r_t := by positivity
  -- Measurability of the three noise terms.
  have hmul_st : Measurable (fun y : ℝ ↦ Real.sqrt s_t * y) := measurable_const.mul measurable_id
  have hmul_rt : Measurable (fun y : ℝ ↦ Real.sqrt r_t * y) := measurable_const.mul measurable_id
  have hmul_τ : Measurable (fun y : ℝ ↦ Real.sqrt (s_t + r_t) * y) :=
    measurable_const.mul measurable_id
  have hSZX_meas : Measurable (fun ω ↦ Real.sqrt s_t * Z_X ω) := hmul_st.comp hZX
  have hRZY_meas : Measurable (fun ω ↦ Real.sqrt r_t * Z_Y ω) := hmul_rt.comp hZY
  have hτZ_meas : Measurable (fun ω ↦ Real.sqrt (s_t + r_t) * Z ω) := hmul_τ.comp hZ
  -- Law of a single scaled noise `√c·W ∼ 𝒩(0, c)` for `c ≥ 0`, `W ∼ 𝒩(0,1)`.
  have scaled_law : ∀ (W : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c), Measurable W →
      P.map W = gaussianReal 0 1 →
      P.map (fun ω ↦ Real.sqrt c * W ω) = gaussianReal 0 ⟨c, hc⟩ := by
    intro W c hc hW hW_law
    have h_compose : Measure.map (fun ω ↦ Real.sqrt c * W ω) P
        = (P.map W).map (fun y ↦ Real.sqrt c * y) := by
      have hmm := Measure.map_map (μ := P) (g := fun y : ℝ ↦ Real.sqrt c * y) (f := W)
        (measurable_const.mul measurable_id) hW
      simpa [Function.comp] using hmm.symm
    rw [h_compose, hW_law, gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]
      apply NNReal.eq
      exact Real.sq_sqrt hc
  -- Laws of the three scaled noises.
  have hSZX_law : P.map (fun ω ↦ Real.sqrt s_t * Z_X ω) = gaussianReal 0 ⟨s_t, hst0⟩ :=
    scaled_law Z_X s_t hst0 hZX hZX_law
  have hRZY_law : P.map (fun ω ↦ Real.sqrt r_t * Z_Y ω) = gaussianReal 0 ⟨r_t, hrt0⟩ :=
    scaled_law Z_Y r_t hrt0 hZY hZY_law
  have hτZ_law : P.map (fun ω ↦ Real.sqrt (s_t + r_t) * Z ω) = gaussianReal 0 ⟨s_t + r_t, hτ0⟩ :=
    scaled_law Z (s_t + r_t) hτ0 hZ hZ_law
  -- LHS noise law = `𝒩(0, s_t + r_t)`.
  -- Independence of the two scaled noises from `IndepFun Z_X Z_Y`.
  have hSZX_RZY_indep : IndepFun (fun ω ↦ Real.sqrt s_t * Z_X ω)
      (fun ω ↦ Real.sqrt r_t * Z_Y ω) P :=
    hZX_ZY.comp hmul_st hmul_rt
  have hnoiseL_law : P.map (fun ω ↦ Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω)
      = gaussianReal 0 ⟨s_t + r_t, hτ0⟩ := by
    have h_sum := gaussianReal_add_gaussianReal_of_indepFun (P := P)
      (X := fun ω ↦ Real.sqrt s_t * Z_X ω) (Y := fun ω ↦ Real.sqrt r_t * Z_Y ω)
      (m₁ := 0) (m₂ := 0) (v₁ := ⟨s_t, hst0⟩) (v₂ := ⟨r_t, hrt0⟩)
      hSZX_RZY_indep hSZX_law hRZY_law
    have h_funext : (fun ω ↦ Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω)
        = (fun ω ↦ Real.sqrt s_t * Z_X ω) + (fun ω ↦ Real.sqrt r_t * Z_Y ω) := by
      funext ω; rfl
    rw [h_funext, h_sum]
    refine congrArg₂ gaussianReal (by norm_num) ?_
    apply NNReal.eq
    rfl
  -- Measurability + independence of `B` from the LHS scaled noise.
  have hnoiseL_meas : Measurable (fun ω ↦ Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω) :=
    hSZX_meas.add hRZY_meas
  -- `B ⊥ (√s_t·Z_X + √r_t·Z_Y)` from joint independence `B ⊥ (Z_X, Z_Y)`.
  have hB_noiseL_indep : IndepFun B
      (fun ω ↦ Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω) P := by
    have hmap : Measurable (fun p : ℝ × ℝ ↦ Real.sqrt s_t * p.1 + Real.sqrt r_t * p.2) := by
      fun_prop
    have := hXY_ZXZY_pair.comp (measurable_id) hmap
    simpa [Function.comp] using this
  -- `B ⊥ (√τ·Z)` from `B ⊥ Z`.
  have hB_noiseR_indep : IndepFun B (fun ω ↦ Real.sqrt (s_t + r_t) * Z ω) P :=
    hXY_Z.comp measurable_id hmul_τ
  -- Split both sides as `(P.map B) ∗ (noise law)`.
  -- LHS.
  have hLHS_eq : P.map (fun ω ↦ X ω + Real.sqrt s_t * Z_X ω + (Y ω + Real.sqrt r_t * Z_Y ω))
      = (P.map B) ∗ gaussianReal 0 ⟨s_t + r_t, hτ0⟩ := by
    have h_funext : (fun ω ↦ X ω + Real.sqrt s_t * Z_X ω + (Y ω + Real.sqrt r_t * Z_Y ω))
        = B + (fun ω ↦ Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω) := by
      funext ω; simp only [hB, Pi.add_apply]; ring
    rw [h_funext,
      hB_noiseL_indep.map_add_eq_map_conv_map hB_meas hnoiseL_meas, hnoiseL_law]
  -- RHS.
  have hRHS_eq : P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (s_t + r_t) * Z ω)
      = (P.map B) ∗ gaussianReal 0 ⟨s_t + r_t, hτ0⟩ := by
    have h_funext : (fun ω ↦ (X ω + Y ω) + Real.sqrt (s_t + r_t) * Z ω)
        = B + (fun ω ↦ Real.sqrt (s_t + r_t) * Z ω) := by
      funext ω; simp only [hB, Pi.add_apply]
    rw [h_funext,
      hB_noiseR_indep.map_add_eq_map_conv_map hB_meas hτZ_meas, hτZ_law]
  rw [hLHS_eq, hRHS_eq]

/-- The two-time gap has derivative
`J_S·(1/J_X + 1/J_Y) − 1` at `t > 0` along the matched path.

Reuses the per-component de Bruijn building blocks of
`csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:744`, the
`entropyPower(X_s)·J_X` form `hN_X`) composed via the chain rule with the
matched velocities `s'(t) = 1/J_X(s(t))`, `r'(t) = 1/J_Y(r(t))`
(`IsMatchedTimePath.deriv_at`). The bivariate de Bruijn for the sum is
`deBruijn_identity_v2` applied at base `X + Y_r`, noise `Z_X` (and symmetrically),
structurally identical to the existing sum version (no new asset).

The de Bruijn regularity is `IsDeBruijnRegularityHyp` for each component; the
`J_* > 0` positivity is threaded as in `csiszarLogRatioGap_deriv_le_zero`.

Honesty (2026-06-06 STRUCTURAL fix — all three Fisher infos density-pinned, the
old a.e.-pin `J_S` escape is structurally removed). All three Fisher infos in
the conclusion are now pinned to a pointwise-smooth representative, so a skeptic
cannot choose their values:

* `J_X (s t)` / `J_Y (r t)`: density-pinned. `hJX_eq`/`hJY_eq` fix them to
`fisherInfoOfDensityReal ((h_reg_*.reg_at (s t) hst).density_t)`, and that
`density_t` is pointwise pinned to the smooth representative via
`IsRegularDeBruijnHypV2.density_t_eq`, with the real `X`/`Y`-density fixed by
`pX_law` (same mechanism as the honest single-time
`csiszarLogRatioGap_hasDerivAt`).
* `J_S`: directly embedded, no free variable. At the single time `t`, the
matched sum `X_{s t} + Y_{r t} = (X+Y) + (√(s t)·Z_X + √(r t)·Z_Y)`, and the
noise has law `𝒩(0, s t + r t)` independent of `X+Y`, so the matched-sum law
equals that of `(X+Y) + √τ·Z` (`τ = s t + r t`, `Z` unit Gaussian) — a
single-noise heat flow of `X+Y` at time `τ` (proved by `matchedSum_law_eq`).
Hence `J_S` is embedded directly into the conclusion as
`fisherInfoOfDensityReal ((h_reg_sum.reg_at (s t + r t) hτ).density_t)` by
threading the EXISTING single-noise `IsDeBruijnRegularityHyp (X+Y) Z P`. Its
`density_t_eq` supplies the smooth pointwise pin for free, so the old
`withDensity` a.e.-pin (representative-escapable via the documented
`fisherInfoOfDensityReal` pointwise `logDeriv`) is gone. No free Fisher-info
variable remains.
@audit:ok -/
theorem twoTimeLogRatioGap_hasDerivAt
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (hX : Measurable X) (hZX : Measurable Z_X) (_hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (_hYZY : IndepFun Y Z_Y P)
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    -- de Bruijn regularity for the independently-perturbed components
    (h_reg_X : IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : IsDeBruijnRegularityHyp Y Z_Y P)
    -- unit noise `Z` + single-noise heat-flow regularity of the matched sum.
    -- `matchedSum_law_eq` shows `P.map (X_{s t}+Y_{r t}) = P.map ((X+Y)+√τ·Z)`,
    -- so `J_S` is the single-noise sum Fisher info at `τ = s t + r t`; these are
    -- the regularity preconditions for that identification (measurability, the
    -- unit-noise law of `Z`, and independence of `X+Y` from `Z`).
    (hZ : Measurable Z) (hZ_law : P.map Z = gaussianReal 0 1)
    (hXYZ : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    -- unit-noise laws + joint independences for the matched-sum law
    -- (`matchedSum_law_eq` regularity preconditions; honest noise-distribution
    -- facts, not bundled derivative content)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_reg_sum : IsDeBruijnRegularityHyp (fun ω ↦ X ω + Y ω) Z P)
    {t : ℝ} (ht : 0 < t)
    -- matched-time positivity (regularity precondition: `t > 0` + strict-mono
    -- matched path put `s t, r t > 0`; threaded here as a precondition)
    (hst : 0 < s t) (hrt : 0 < r t)
    -- `τ = s t + r t > 0` (derivable from `add_pos hst hrt`, threaded explicitly)
    (hτ : 0 < s t + r t)
    -- `J_X (s t) / J_Y (r t)` density-pinned to the real perturbed-density
    -- Fisher info at the matched time (same pin as the honest single-time
    -- `csiszarLogRatioGap_hasDerivAt`, evaluated at `s t` / `r t`)
    (_hJX_eq : J_X (s t)
        = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_X.reg_at (s t) hst).density_t))
    (_hJY_eq : J_Y (r t)
        = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_Y.reg_at (r t) hrt).density_t))
    (_hJX_pos : 0 < J_X (s t)) (_hJY_pos : 0 < J_Y (r t)) :
    HasDerivAt (fun u : ℝ ↦ twoTimeLogRatioGap X Y Z_X Z_Y P s r u)
      (InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) hτ).density_t)
        * (1 / J_X (s t) + 1 / J_Y (r t)) - 1) t := by
  classical
  set J_S : ℝ := InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
      ((h_reg_sum.reg_at (s t + r t) hτ).density_t) with hJS_def
  -- Step 2: single-noise de Bruijn for `X+Y` at `τ = s t + r t` gives the
  -- entropy-power log-derivative `d/dσ log (heatFlowEP (X+Y) Z P σ) = J_S` at `s t + r t`.
  have h_log_sum :
      HasDerivAt (fun σ : ℝ ↦ Real.log (heatFlowEP (fun ω ↦ X ω + Y ω) Z P σ))
        J_S (s t + r t) := by
    -- Single-noise de Bruijn V2 for `X+Y` perturbed by `Z` at time `τ = s t + r t`.
    have h_dB :
        HasDerivAt
          (fun σ : ℝ ↦ InformationTheory.Shannon.differentialEntropy
            (P.map (InformationTheory.Shannon.FisherInfo.gaussianConvolution
                      (fun ω ↦ X ω + Y ω) Z σ)))
          ((1/2) * J_S) (s t + r t) := by
      have := InformationTheory.Shannon.FisherInfo.deBruijn_identity_v2
        (fun ω ↦ X ω + Y ω) Z (hX.add hY) hZ hXYZ hτ (h_reg_sum.reg_at (s t + r t) hτ)
      simpa only [hJS_def] using this
    -- Lift to entropy-power form.
    have h_eP := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB
    -- Normalize to `heatFlowEP (X+Y) Z P σ · J_S`.
    have hN :
        HasDerivAt (fun σ : ℝ ↦ heatFlowEP (fun ω ↦ X ω + Y ω) Z P σ)
          (heatFlowEP (fun ω ↦ X ω + Y ω) Z P (s t + r t) * J_S) (s t + r t) := by
      have h_val :
          heatFlowEP (fun ω ↦ X ω + Y ω) Z P (s t + r t) * J_S
            = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
                (P.map (InformationTheory.Shannon.FisherInfo.gaussianConvolution
                          (fun ω ↦ X ω + Y ω) Z (s t + r t))))
              * (2 * ((1/2) * J_S)) := by
        unfold heatFlowEP entropyPower InformationTheory.Shannon.FisherInfo.gaussianConvolution
        ring
      rw [h_val]
      exact h_eP
    -- `log` derivative: `(N_S · J_S) / N_S = J_S`.
    have hNpos : 0 < heatFlowEP (fun ω ↦ X ω + Y ω) Z P (s t + r t) := by
      simpa [heatFlowEP] using entropyPower_pos _
    have h := hN.log (ne_of_gt hNpos)
    rwa [mul_comm, mul_div_assoc, div_self (ne_of_gt hNpos), mul_one] at h
  -- Step 3: chain rule with `τ(u) = s u + r u`, `τ'(t) = 1/J_X(s t) + 1/J_Y(r t)`.
  have h_tau_deriv :
      HasDerivAt (fun u : ℝ ↦ s u + r u) (1 / J_X (s t) + 1 / J_Y (r t)) t :=
    (h_path_X.deriv_at t ht).add (h_path_Y.deriv_at t ht)
  have h_log_comp :
      HasDerivAt (fun u : ℝ ↦ Real.log (heatFlowEP (fun ω ↦ X ω + Y ω) Z P (s u + r u)))
        (J_S * (1 / J_X (s t) + 1 / J_Y (r t))) t := by
    -- `comp` of the log-heat-flow (at `s t + r t`) with `τ(u) = s u + r u` (at `t`).
    have hcomp := h_log_sum.comp t h_tau_deriv
    -- `comp` yields value `J_S * τ'(t)`; match by `mul_comm`.
    simpa only [Function.comp, mul_comm] using hcomp
  -- Step 1: rewrite `log (sumHeatFlowEP ... (s u) (r u))` to the single-noise heat flow
  -- on a neighborhood of `t`, via `matchedSum_law_eq` (eventually `s u, r u > 0`).
  have h_log_sumHeat :
      HasDerivAt
        (fun u : ℝ ↦ Real.log (sumHeatFlowEP X Y Z_X Z_Y P (s u) (r u)))
        (J_S * (1 / J_X (s t) + 1 / J_Y (r t))) t := by
    -- `s`, `r` are continuous at `t` (`HasDerivAt → ContinuousAt`), and `s t, r t > 0`,
    -- so `s u, r u > 0` on a neighborhood of `t`.
    have hs_cont : ContinuousAt s t := (h_path_X.deriv_at t ht).continuousAt
    have hr_cont : ContinuousAt r t := (h_path_Y.deriv_at t ht).continuousAt
    have hs_ev : ∀ᶠ u in nhds t, 0 < s u :=
      continuousAt_const.eventually_lt hs_cont hst
    have hr_ev : ∀ᶠ u in nhds t, 0 < r u :=
      continuousAt_const.eventually_lt hr_cont hrt
    -- On that neighborhood the matched-sum law identifies the two heat flows.
    have h_eq : (fun u : ℝ ↦ Real.log (sumHeatFlowEP X Y Z_X Z_Y P (s u) (r u)))
        =ᶠ[nhds t] (fun u : ℝ ↦ Real.log (heatFlowEP (fun ω ↦ X ω + Y ω) Z P (s u + r u))) := by
      filter_upwards [hs_ev, hr_ev] with u hsu hru
      have hmap := matchedSum_law_eq X Y Z_X Z_Y Z P hX hY hZX hZY hZ
        hZX_law hZY_law hZ_law hXY_ZXZY_pair hXYZ hZX_ZY (s u) (r u) hsu hru
      unfold sumHeatFlowEP heatFlowEP
      rw [hmap]
    exact h_log_comp.congr_of_eventuallyEq h_eq
  -- Step 4: assemble. `twoTimeLogRatioGap ... u = log (sumHeatFlowEP ... (s u)(r u)) − const − u`.
  have h_const :
      HasDerivAt
        (fun _ : ℝ ↦ Real.log (entropyPower (P.map X) + entropyPower (P.map Y)))
        0 t := hasDerivAt_const t _
  have h_id : HasDerivAt (fun u : ℝ ↦ u) (1 : ℝ) t := hasDerivAt_id t
  have h_assembled :
      HasDerivAt (fun u : ℝ ↦ twoTimeLogRatioGap X Y Z_X Z_Y P s r u)
        (J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 0 - 1) t := by
    have := (h_log_sumHeat.sub h_const).sub h_id
    simpa only [twoTimeLogRatioGap] using this
  -- Match the stated derivative value.
  have hval : J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 0 - 1
      = J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 1 := by ring
  rw [hval] at h_assembled
  rw [hJS_def] at h_assembled
  exact h_assembled

/-- The two-time gap derivative is `≤ 0` at `t > 0` along the matched path
(the analytic core).

From harmonic Stam `1/J_S ≥ 1/J_X + 1/J_Y` (J_S > 0), the value
`J_S·(1/J_X + 1/J_Y) − 1 ≤ 0` (proof-log §Two-time object `twotime_reduced` /
`twotime_full`, mechanically verified). The harmonic Stam supply is the
existing genuine producer `isStamInequalityHyp_via_step3` /
`isStamInequalityHyp_via_body` (sorryAx-free).

Audit 2026-06-06 (skeleton): signature-honest. Free `J_S`/`J_X`/`J_Y` are here
genuinely OK because `h_stam : 1/J_S ≥ 1/J_X(s t)+1/J_Y(r t)` + `hJS_pos` CONSTRAIN
them — the conclusion is pure abstract arith (`J_S·(1/J_X+1/J_Y) ≤ J_S·(1/J_S) = 1`)
that follows for ANY reals satisfying the hypotheses. Same shape as the honest
`csiszar_ratio_deriv_le_zero_arith`. Contrast `_hasDerivAt` above, where the free
`J_S` has NO constraining hypothesis (false-as-framed).
@audit:ok -/
theorem twoTimeLogRatioGap_deriv_le_zero
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (_h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (_h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    {t : ℝ} (_ht : 0 < t)
    (J_S : ℝ)
    (_hJX_pos : 0 < J_X (s t)) (_hJY_pos : 0 < J_Y (r t)) (hJS_pos : 0 < J_S)
    -- harmonic Stam for the matched-time sum (supplied by the genuine producer)
    (h_stam : 1 / J_S ≥ 1 / J_X (s t) + 1 / J_Y (r t)) :
    J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 1 ≤ 0 := by
  have h : 1 / J_X (s t) + 1 / J_Y (r t) ≤ 1 / J_S := h_stam
  have h2 : J_S * (1 / J_X (s t) + 1 / J_Y (r t)) ≤ J_S * (1 / J_S) :=
    mul_le_mul_of_nonneg_left h (le_of_lt hJS_pos)
  rw [mul_one_div, div_self (ne_of_gt hJS_pos)] at h2
  linarith

end InformationTheory.Shannon.EPICase1TwoTime
