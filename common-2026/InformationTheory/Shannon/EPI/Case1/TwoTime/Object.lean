import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.Discharge
import InformationTheory.Shannon.FisherInfo.V2DeBruijnGenuine
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
# EPI case-1 two-time object — gap object, derivative, EPI bridge (§2–§4)

The two-time log-ratio object `twoTimeLogRatioGap`, its derivative, endpoints /
antitonicity / Gaussian-saturation limit, and the EPI bridge
`entropyPower_add_ge_case1_of_regular_twotime`. Verbatim split of `TwoTime.lean`
§2–§4; proofs unchanged. Builds on `TwoTimeCore.lean` (§0) +
`TwoTimePaths.lean` (§1). Umbrella: `TwoTime.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace InformationTheory.Shannon.EPICase1TwoTime

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
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
  entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω + (Y ω + Real.sqrt r * Z_Y ω)))

/-- **TT-def `twoTimeLogRatioGap`** — the two-time EPI log-ratio object
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

/-- **TT-`_at_zero`** — at `t = 0` the two-time gap reduces to the EPI bridge
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
      = Real.log (entropyPower (P.map (fun ω => X ω + Y ω)))
        - Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) := by
  unfold twoTimeLogRatioGap sumHeatFlowEP
  rw [h_path_X.start_zero, h_path_Y.start_zero]
  have h_sum_funext :
      (fun ω => X ω + Real.sqrt 0 * Z_X ω + (Y ω + Real.sqrt 0 * Z_Y ω))
        = fun ω => X ω + Y ω := by
    funext ω
    simp [Real.sqrt_zero]
  rw [h_sum_funext, sub_zero]

/-! ## §3 — Derivative of the two-time object

`R'(t) = J_S·(1/J_X + 1/J_Y) − 1` along the matched path, where
`J_S = J(X_s + Y_r)`, via per-component de Bruijn (`deBruijn_identity_v2`) +
chain rule (`HasDerivAt.comp` with `s' = 1/J_X`, `r' = 1/J_Y`). -/

/-- **Matched-sum law = single-noise heat flow of `X+Y` at `τ = s_t + r_t`.**

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
IndepFun (X+Y) (Z_X+Z_Y) P` was **insufficient**: it gives independence of `X+Y`
from the *unscaled* sum `Z_X+Z_Y`, but the matched-sum noise is the *scaled*
combination `√s_t·Z_X + √r_t·Z_Y` (a different linear functional when
`s_t ≠ r_t`), whose independence from `X+Y` does **not** follow. The honest
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
    (hXY_ZXZY_pair : IndepFun (fun ω => X ω + Y ω) (fun ω => (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω => X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (s_t r_t : ℝ) (hst : 0 < s_t) (hrt : 0 < r_t) :
    P.map (fun ω => X ω + Real.sqrt s_t * Z_X ω + (Y ω + Real.sqrt r_t * Z_Y ω))
      = P.map (fun ω => (X ω + Y ω) + Real.sqrt (s_t + r_t) * Z ω) := by
  classical
  -- Abbreviations.
  set B : Ω → ℝ := fun ω => X ω + Y ω with hB
  have hB_meas : Measurable B := hX.add hY
  have hst0 : (0:ℝ) ≤ s_t := hst.le
  have hrt0 : (0:ℝ) ≤ r_t := hrt.le
  have hτ0 : (0:ℝ) ≤ s_t + r_t := by positivity
  -- Measurability of the three noise terms.
  have hmul_st : Measurable (fun y : ℝ => Real.sqrt s_t * y) := measurable_const.mul measurable_id
  have hmul_rt : Measurable (fun y : ℝ => Real.sqrt r_t * y) := measurable_const.mul measurable_id
  have hmul_τ : Measurable (fun y : ℝ => Real.sqrt (s_t + r_t) * y) :=
    measurable_const.mul measurable_id
  have hSZX_meas : Measurable (fun ω => Real.sqrt s_t * Z_X ω) := hmul_st.comp hZX
  have hRZY_meas : Measurable (fun ω => Real.sqrt r_t * Z_Y ω) := hmul_rt.comp hZY
  have hτZ_meas : Measurable (fun ω => Real.sqrt (s_t + r_t) * Z ω) := hmul_τ.comp hZ
  -- **Law of a single scaled noise** `√c·W ∼ 𝒩(0, c)` for `c ≥ 0`, `W ∼ 𝒩(0,1)`.
  have scaled_law : ∀ (W : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c), Measurable W →
      P.map W = gaussianReal 0 1 →
      P.map (fun ω => Real.sqrt c * W ω) = gaussianReal 0 ⟨c, hc⟩ := by
    intro W c hc hW hW_law
    have h_compose : Measure.map (fun ω => Real.sqrt c * W ω) P
        = (P.map W).map (fun y => Real.sqrt c * y) := by
      have hmm := Measure.map_map (μ := P) (g := fun y : ℝ => Real.sqrt c * y) (f := W)
        (measurable_const.mul measurable_id) hW
      simpa [Function.comp] using hmm.symm
    rw [h_compose, hW_law, gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one]
      apply NNReal.eq
      exact Real.sq_sqrt hc
  -- Laws of the three scaled noises.
  have hSZX_law : P.map (fun ω => Real.sqrt s_t * Z_X ω) = gaussianReal 0 ⟨s_t, hst0⟩ :=
    scaled_law Z_X s_t hst0 hZX hZX_law
  have hRZY_law : P.map (fun ω => Real.sqrt r_t * Z_Y ω) = gaussianReal 0 ⟨r_t, hrt0⟩ :=
    scaled_law Z_Y r_t hrt0 hZY hZY_law
  have hτZ_law : P.map (fun ω => Real.sqrt (s_t + r_t) * Z ω) = gaussianReal 0 ⟨s_t + r_t, hτ0⟩ :=
    scaled_law Z (s_t + r_t) hτ0 hZ hZ_law
  -- **LHS noise law** = `𝒩(0, s_t + r_t)`.
  -- Independence of the two scaled noises from `IndepFun Z_X Z_Y`.
  have hSZX_RZY_indep : IndepFun (fun ω => Real.sqrt s_t * Z_X ω)
      (fun ω => Real.sqrt r_t * Z_Y ω) P :=
    hZX_ZY.comp hmul_st hmul_rt
  have hnoiseL_law : P.map (fun ω => Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω)
      = gaussianReal 0 ⟨s_t + r_t, hτ0⟩ := by
    have h_sum := gaussianReal_add_gaussianReal_of_indepFun (P := P)
      (X := fun ω => Real.sqrt s_t * Z_X ω) (Y := fun ω => Real.sqrt r_t * Z_Y ω)
      (m₁ := 0) (m₂ := 0) (v₁ := ⟨s_t, hst0⟩) (v₂ := ⟨r_t, hrt0⟩)
      hSZX_RZY_indep hSZX_law hRZY_law
    have h_funext : (fun ω => Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω)
        = (fun ω => Real.sqrt s_t * Z_X ω) + (fun ω => Real.sqrt r_t * Z_Y ω) := by
      funext ω; rfl
    rw [h_funext, h_sum]
    refine congrArg₂ gaussianReal (by norm_num) ?_
    apply NNReal.eq
    rfl
  -- Measurability + independence of `B` from the LHS scaled noise.
  have hnoiseL_meas : Measurable (fun ω => Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω) :=
    hSZX_meas.add hRZY_meas
  -- `B ⊥ (√s_t·Z_X + √r_t·Z_Y)` from joint independence `B ⊥ (Z_X, Z_Y)`.
  have hB_noiseL_indep : IndepFun B
      (fun ω => Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω) P := by
    have hmap : Measurable (fun p : ℝ × ℝ => Real.sqrt s_t * p.1 + Real.sqrt r_t * p.2) := by
      fun_prop
    have := hXY_ZXZY_pair.comp (measurable_id) hmap
    simpa [Function.comp] using this
  -- `B ⊥ (√τ·Z)` from `B ⊥ Z`.
  have hB_noiseR_indep : IndepFun B (fun ω => Real.sqrt (s_t + r_t) * Z ω) P :=
    hXY_Z.comp measurable_id hmul_τ
  -- **Split both sides as `(P.map B) ∗ (noise law)`.**
  -- LHS.
  have hLHS_eq : P.map (fun ω => X ω + Real.sqrt s_t * Z_X ω + (Y ω + Real.sqrt r_t * Z_Y ω))
      = (P.map B) ∗ gaussianReal 0 ⟨s_t + r_t, hτ0⟩ := by
    have h_funext : (fun ω => X ω + Real.sqrt s_t * Z_X ω + (Y ω + Real.sqrt r_t * Z_Y ω))
        = B + (fun ω => Real.sqrt s_t * Z_X ω + Real.sqrt r_t * Z_Y ω) := by
      funext ω; simp only [hB, Pi.add_apply]; ring
    rw [h_funext,
      hB_noiseL_indep.map_add_eq_map_conv_map hB_meas hnoiseL_meas, hnoiseL_law]
  -- RHS.
  have hRHS_eq : P.map (fun ω => (X ω + Y ω) + Real.sqrt (s_t + r_t) * Z ω)
      = (P.map B) ∗ gaussianReal 0 ⟨s_t + r_t, hτ0⟩ := by
    have h_funext : (fun ω => (X ω + Y ω) + Real.sqrt (s_t + r_t) * Z ω)
        = B + (fun ω => Real.sqrt (s_t + r_t) * Z ω) := by
      funext ω; simp only [hB, Pi.add_apply]
    rw [h_funext,
      hB_noiseR_indep.map_add_eq_map_conv_map hB_meas hτZ_meas, hτZ_law]
  rw [hLHS_eq, hRHS_eq]

/-- **TT-`_hasDerivAt`** — the two-time gap has derivative
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
`density_t` is **pointwise** pinned to the smooth representative via
`IsRegularDeBruijnHypV2.density_t_eq`, with the real `X`/`Y`-density fixed by
`pX_law` (same mechanism as the honest single-time
`csiszarLogRatioGap_hasDerivAt`).
* `J_S`: **directly embedded, no free variable.** At the single time `t`, the
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
    (hXYZ : IndepFun (fun ω => X ω + Y ω) Z P)
    -- unit-noise laws + joint independences for the matched-sum law
    -- (`matchedSum_law_eq` regularity preconditions; honest noise-distribution
    -- facts, not bundled derivative content)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω => X ω + Y ω) (fun ω => (Z_X ω, Z_Y ω)) P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_reg_sum : IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) Z P)
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
        = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_X.reg_at (s t) hst).density_t))
    (_hJY_eq : J_Y (r t)
        = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_Y.reg_at (r t) hrt).density_t))
    (_hJX_pos : 0 < J_X (s t)) (_hJY_pos : 0 < J_Y (r t)) :
    HasDerivAt (fun u : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r u)
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) hτ).density_t)
        * (1 / J_X (s t) + 1 / J_Y (r t)) - 1) t := by
  classical
  set J_S : ℝ := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_sum.reg_at (s t + r t) hτ).density_t) with hJS_def
  -- Step 2: single-noise de Bruijn for `X+Y` at `τ = s t + r t` gives the
  -- entropy-power log-derivative `d/dσ log (heatFlowEP (X+Y) Z P σ) = J_S` at `s t + r t`.
  have h_log_sum :
      HasDerivAt (fun σ : ℝ => Real.log (heatFlowEP (fun ω => X ω + Y ω) Z P σ))
        J_S (s t + r t) := by
    -- Single-noise de Bruijn V2 for `X+Y` perturbed by `Z` at time `τ = s t + r t`.
    have h_dB :
        HasDerivAt
          (fun σ : ℝ => InformationTheory.Shannon.differentialEntropy
            (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                      (fun ω => X ω + Y ω) Z σ)))
          ((1/2) * J_S) (s t + r t) := by
      have := InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2
        (fun ω => X ω + Y ω) Z (hX.add hY) hZ hXYZ hτ (h_reg_sum.reg_at (s t + r t) hτ)
      simpa only [hJS_def] using this
    -- Lift to entropy-power form.
    have h_eP := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB
    -- Normalize to `heatFlowEP (X+Y) Z P σ · J_S`.
    have hN :
        HasDerivAt (fun σ : ℝ => heatFlowEP (fun ω => X ω + Y ω) Z P σ)
          (heatFlowEP (fun ω => X ω + Y ω) Z P (s t + r t) * J_S) (s t + r t) := by
      have h_val :
          heatFlowEP (fun ω => X ω + Y ω) Z P (s t + r t) * J_S
            = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
                (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                          (fun ω => X ω + Y ω) Z (s t + r t))))
              * (2 * ((1/2) * J_S)) := by
        unfold heatFlowEP entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
        ring
      rw [h_val]
      exact h_eP
    -- `log` derivative: `(N_S · J_S) / N_S = J_S`.
    have hNpos : 0 < heatFlowEP (fun ω => X ω + Y ω) Z P (s t + r t) := by
      simpa [heatFlowEP] using entropyPower_pos _
    have h := hN.log (ne_of_gt hNpos)
    rwa [mul_comm, mul_div_assoc, div_self (ne_of_gt hNpos), mul_one] at h
  -- Step 3: chain rule with `τ(u) = s u + r u`, `τ'(t) = 1/J_X(s t) + 1/J_Y(r t)`.
  have h_tau_deriv :
      HasDerivAt (fun u : ℝ => s u + r u) (1 / J_X (s t) + 1 / J_Y (r t)) t :=
    (h_path_X.deriv_at t ht).add (h_path_Y.deriv_at t ht)
  have h_log_comp :
      HasDerivAt (fun u : ℝ => Real.log (heatFlowEP (fun ω => X ω + Y ω) Z P (s u + r u)))
        (J_S * (1 / J_X (s t) + 1 / J_Y (r t))) t := by
    -- `comp` of the log-heat-flow (at `s t + r t`) with `τ(u) = s u + r u` (at `t`).
    have hcomp := h_log_sum.comp t h_tau_deriv
    -- `comp` yields value `J_S * τ'(t)`; match by `mul_comm`.
    simpa only [Function.comp, mul_comm] using hcomp
  -- Step 1: rewrite `log (sumHeatFlowEP ... (s u) (r u))` to the single-noise heat flow
  -- on a neighborhood of `t`, via `matchedSum_law_eq` (eventually `s u, r u > 0`).
  have h_log_sumHeat :
      HasDerivAt
        (fun u : ℝ => Real.log (sumHeatFlowEP X Y Z_X Z_Y P (s u) (r u)))
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
    have h_eq : (fun u : ℝ => Real.log (sumHeatFlowEP X Y Z_X Z_Y P (s u) (r u)))
        =ᶠ[nhds t] (fun u : ℝ => Real.log (heatFlowEP (fun ω => X ω + Y ω) Z P (s u + r u))) := by
      filter_upwards [hs_ev, hr_ev] with u hsu hru
      have hmap := matchedSum_law_eq X Y Z_X Z_Y Z P hX hY hZX hZY hZ
        hZX_law hZY_law hZ_law hXY_ZXZY_pair hXYZ hZX_ZY (s u) (r u) hsu hru
      unfold sumHeatFlowEP heatFlowEP
      rw [hmap]
    exact h_log_comp.congr_of_eventuallyEq h_eq
  -- Step 4: assemble. `twoTimeLogRatioGap ... u = log (sumHeatFlowEP ... (s u)(r u)) − const − u`.
  have h_const :
      HasDerivAt
        (fun _ : ℝ => Real.log (entropyPower (P.map X) + entropyPower (P.map Y)))
        0 t := hasDerivAt_const t _
  have h_id : HasDerivAt (fun u : ℝ => u) (1 : ℝ) t := hasDerivAt_id t
  have h_assembled :
      HasDerivAt (fun u : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r u)
        (J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 0 - 1) t := by
    have := (h_log_sumHeat.sub h_const).sub h_id
    simpa only [twoTimeLogRatioGap] using this
  -- Match the stated derivative value.
  have hval : J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 0 - 1
      = J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 1 := by ring
  rw [hval] at h_assembled
  rw [hJS_def] at h_assembled
  exact h_assembled

/-- **TT-`_deriv_le_zero`** (= analytic core, arith gate PASS) — the two-time
gap derivative is `≤ 0` at `t > 0` along the matched path.

From harmonic Stam `1/J_S ≥ 1/J_X + 1/J_Y` (J_S > 0), the value
`J_S·(1/J_X + 1/J_Y) − 1 ≤ 0` (proof-log §Two-time object `twotime_reduced` /
`twotime_full`, mechanically verified). The harmonic Stam supply is the
existing genuine producer `isStamInequalityHyp_via_step3` /
`isStamInequalityHyp_via_body` (sorryAx-free). **No new wall.**

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

/-! ## §4 — Endpoints, antitonicity, EPI bridge -/

/-- **TT-`_continuousWithinAt_zero`** — the two-time gap is continuous at the
left endpoint `t = 0` (within `Ioi 0`).

The `log N(s(t),r(t))` term is continuous via the matched-path continuity
(`IsMatchedTimePath.cont`) + heat-flow endpoint continuity
(`heatFlowEntropyPower_continuousWithinAt_zero`, CLOSED 2026-06-05); the
`−t` term is continuous. Mirrors `csiszarLogRatioGap_continuousWithinAt_zero`
(`EPIStamToBridge.lean:1098`).

Mechanism. On `Set.Ioi 0` (where the matched velocities give `s t, r t > 0`),
`matchedSum_law_eq` rewrites the two-time sum heat flow into the single-noise
heat flow of `X + Y` at `τ = s t + r t`: `sumHeatFlowEP X Y Z_X Z_Y P (s t)(r t) =
heatFlowEP (X+Y) Z P (s t + r t)`. This eventual equality (on a neighborhood of
`0` within `Ioi 0`) lets us transfer the continuity via
`ContinuousWithinAt.congr`. The reduced single-noise heat flow is the composition
of the genuine endpoint atom `heatFlowEntropyPower_continuousWithinAt_zero`
(`wall:heatflow-continuity` CLOSED) with the continuous matched reparameterisation
`τ(t) = s t + r t` (`IsMatchedTimePath.cont`).

Added preconditions are genuine regularity:
* `IsHeatFlowEndpointRegular (X+Y) Z P` — the single-noise endpoint atom's input.
* the `matchedSum_law_eq` preconditions (unit-noise laws of `Z_X`, `Z_Y`, `Z`,
the joint/pairwise independences, measurability) — honest
noise-distribution facts, not bundled EPI/derivative content.
* `h_pos : ∀ t, 0 < t → 0 < s t ∧ 0 < r t` — the matched-path positivity on the
interior (the strict-mono inverse-function path satisfies it), threaded as a
precondition exactly as `_hasDerivAt` threads `hst`/`hrt`.
@audit:ok -/
theorem twoTimeLogRatioGap_continuousWithinAt_zero
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω => X ω + Y ω) (fun ω => (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω => X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_pos : ∀ t : ℝ, 0 < t → 0 < s t ∧ 0 < r t)
    (h_endpt_sum : IsHeatFlowEndpointRegular (fun ω => X ω + Y ω) Z P) :
    ContinuousWithinAt (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
      (Set.Ioi (0 : ℝ)) 0 := by
  -- The single-noise endpoint heat-flow continuity atom (`wall:heatflow-continuity`
  -- CLOSED), continuous within `Ioi 0` at `0`.
  have h_endpt :
      ContinuousWithinAt
        (fun u : ℝ => entropyPower (P.map (fun ω => (X ω + Y ω) + Real.sqrt u * Z ω)))
        (Set.Ioi (0 : ℝ)) 0 :=
    heatFlowEntropyPower_continuousWithinAt_zero
      (fun ω => X ω + Y ω) Z P h_endpt_sum
  -- The matched reparameterisation `τ(t) = s t + r t`, continuous within `Ioi 0`
  -- at `0` (from `IsMatchedTimePath.cont` on `Ici 0`, restricted), with `τ 0 = 0`.
  have hs0 : s 0 = 0 := h_path_X.start_zero
  have hr0 : r 0 = 0 := h_path_Y.start_zero
  have hs_cwa : ContinuousWithinAt s (Set.Ioi (0 : ℝ)) 0 :=
    (h_path_X.cont 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self
  have hr_cwa : ContinuousWithinAt r (Set.Ioi (0 : ℝ)) 0 :=
    (h_path_Y.cont 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self
  have hτ_cwa : ContinuousWithinAt (fun t : ℝ => s t + r t) (Set.Ioi (0 : ℝ)) 0 :=
    hs_cwa.add hr_cwa
  -- `τ` maps `Ioi 0` into `Ioi 0` (matched-path positivity).
  have hτ_maps : Set.MapsTo (fun t : ℝ => s t + r t) (Set.Ioi (0 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    obtain ⟨hst, hrt⟩ := h_pos t ht
    exact add_pos hst hrt
  -- `τ 0 = 0`.
  have hτ0 : (fun t : ℝ => s t + r t) 0 = 0 := by simp [hs0, hr0]
  -- Compose: single-noise heat flow along `τ`, continuous within `Ioi 0` at `0`.
  have h_heat_comp :
      ContinuousWithinAt
        (fun t : ℝ => entropyPower
          (P.map (fun ω => (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω)))
        (Set.Ioi (0 : ℝ)) 0 := by
    have hcomp := h_endpt.comp_of_eq hτ_cwa hτ_maps hτ0
    simpa [Function.comp] using hcomp
  -- `log` of the heat flow, continuous within `Ioi 0` at `0`
  -- (`entropyPower` at `τ 0 = 0` is positive).
  have hpos0 : (0 : ℝ) < entropyPower
      (P.map (fun ω => (X ω + Y ω) + Real.sqrt (s 0 + r 0) * Z ω)) := entropyPower_pos _
  have h_log_comp :
      ContinuousWithinAt
        (fun t : ℝ => Real.log (entropyPower
          (P.map (fun ω => (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω))))
        (Set.Ioi (0 : ℝ)) 0 := by
    refine h_heat_comp.log ?_
    simpa [hs0, hr0] using hpos0.ne'
  -- The `−log(const) − t` tail is continuous.
  have h_const : ContinuousWithinAt
      (fun _ : ℝ => Real.log (entropyPower (P.map X) + entropyPower (P.map Y)))
      (Set.Ioi (0 : ℝ)) 0 := continuousWithinAt_const
  have h_id : ContinuousWithinAt (fun t : ℝ => t) (Set.Ioi (0 : ℝ)) 0 :=
    continuousWithinAt_id
  -- Assemble the reduced (single-noise) continuity.
  have h_reduced :
      ContinuousWithinAt
        (fun t : ℝ => Real.log (entropyPower
            (P.map (fun ω => (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω)))
          - Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) - t)
        (Set.Ioi (0 : ℝ)) 0 :=
    (h_log_comp.sub h_const).sub h_id
  -- Transfer back to the two-time gap via the matched-sum law on `Ioi 0`.
  refine h_reduced.congr ?_ ?_
  · -- equality on `Ioi 0`: `twoTimeLogRatioGap ... t = reduced t`.
    intro t ht
    obtain ⟨hst, hrt⟩ := h_pos t ht
    have hmap := matchedSum_law_eq X Y Z_X Z_Y Z P hX hY hZX hZY hZ
      hZX_law hZY_law hZ_law hXY_ZXZY_pair hXY_Z hZX_ZY (s t) (r t) hst hrt
    show twoTimeLogRatioGap X Y Z_X Z_Y P s r t = _
    unfold twoTimeLogRatioGap sumHeatFlowEP
    rw [hmap]
  · -- value at `0`: `twoTimeLogRatioGap ... 0 = reduced 0`.
    show twoTimeLogRatioGap X Y Z_X Z_Y P s r 0 = _
    unfold twoTimeLogRatioGap sumHeatFlowEP
    have hfun : (fun ω => X ω + Real.sqrt (s 0) * Z_X ω + (Y ω + Real.sqrt (r 0) * Z_Y ω))
        = (fun ω => (X ω + Y ω) + Real.sqrt (s 0 + r 0) * Z ω) := by
      funext ω
      simp [hs0, hr0, Real.sqrt_zero]
    rw [hfun]

/-- **TT-`_antitoneOn_Ici_zero`** — the two-time gap is `AntitoneOn (Set.Ici 0)`.

`antitoneOn_of_deriv_nonpos` (convex `Set.Ici 0`) with continuity
(`twoTimeLogRatioGap_continuousWithinAt_zero`), differentiability + per-`t`
`deriv ≤ 0` (`twoTimeLogRatioGap_hasDerivAt.deriv` + `_deriv_le_zero`).
Mirrors `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1130`).

Surface structure (matched to the single-time model). On the interior `Set.Ioi 0`
`AntitoneOn` is genuine: continuity there is the interior differentiability
(`_hasDerivAt.differentiableAt.differentiableWithinAt`), `interior (Ioi 0) = Ioi 0`,
and per-`t` `deriv ≤ 0` is `(_hasDerivAt ...).deriv` rewritten to the closed-form
derivative `J_S·(1/J_X + 1/J_Y) − 1`, bounded `≤ 0` by `_deriv_le_zero`
instantiated with the free `J_S := J_S_embed(t)` (= the directly-embedded sum
Fisher info) and the per-`t` harmonic Stam supply. The endpoint `0` is then
re-attached via `AntitoneOn.insert_of_continuousWithinAt` + the endpoint
continuity (Task 1).

The added preconditions are all genuine regularity / Stam-supply, **not** a
bundling of the EPI conclusion (the `h_per_t` conjunction supplies positivity,
the density-pin equalities, and the harmonic Stam `1/J_S ≥ 1/J_X + 1/J_Y` — the
same shape as the model's `h_pos_stam`; the harmonic Stam is the genuine
single-noise-sum producer's output, threaded per-`t`).
@audit:ok -/
theorem twoTimeLogRatioGap_antitoneOn_Ici_zero
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hZ : Measurable Z) (hZ_law : P.map Z = gaussianReal 0 1)
    (hXYZ : IndepFun (fun ω => X ω + Y ω) Z P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω => X ω + Y ω) (fun ω => (Z_X ω, Z_Y ω)) P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_reg_X : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) Z P)
    (h_endpt_sum : IsHeatFlowEndpointRegular (fun ω => X ω + Y ω) Z P)
    (h_pos : ∀ t : ℝ, 0 < t → 0 < s t ∧ 0 < r t)
    -- per-`t` regularity + harmonic Stam supply bundle (genuine, not bundled
    -- conclusion): density-pins for `J_X`/`J_Y`, positivity, and harmonic Stam.
    (h_per_t : ∀ (t : ℝ), 0 < t → ∀ (hst : 0 < s t) (hrt : 0 < r t),
      J_X (s t) = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_X.reg_at (s t) hst).density_t) ∧
      J_Y (r t) = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at (r t) hrt).density_t) ∧
      0 < J_X (s t) ∧ 0 < J_Y (r t) ∧
      0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t) ∧
      1 / InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t)
        ≥ 1 / J_X (s t) + 1 / J_Y (r t)) :
    AntitoneOn (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t) (Set.Ici (0 : ℝ)) := by
  set f := fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t with hf_def
  -- Genuine interior differentiability (= continuity) on `Set.Ioi 0`.
  have h_diff_Ioi : DifferentiableOn ℝ f (Set.Ioi 0) := by
    intro t ht
    have ht_pos : (0 : ℝ) < t := ht
    obtain ⟨hst, hrt⟩ := h_pos t ht_pos
    have hτ : 0 < s t + r t := add_pos hst hrt
    obtain ⟨hJX_eq, hJY_eq, hJX_pos, hJY_pos, _, _⟩ := h_per_t t ht_pos hst hrt
    exact ((twoTimeLogRatioGap_hasDerivAt X Y Z_X Z_Y Z P
      hX hZX hXZX hY hZY hYZY h_path_X h_path_Y h_reg_X h_reg_Y
      hZ hZ_law hXYZ hZX_law hZY_law hXY_ZXZY_pair hZX_ZY h_reg_sum
      ht_pos hst hrt hτ hJX_eq hJY_eq hJX_pos hJY_pos).differentiableAt).differentiableWithinAt
  -- `AntitoneOn f (Set.Ioi 0)`, genuine: deriv ≤ 0 from `_hasDerivAt` + `_deriv_le_zero`.
  have h_anti_Ioi : AntitoneOn f (Set.Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) h_diff_Ioi.continuousOn
      (by rw [interior_Ioi]; exact h_diff_Ioi) ?_
    intro t ht
    rw [interior_Ioi] at ht
    have ht_pos : (0 : ℝ) < t := ht
    obtain ⟨hst, hrt⟩ := h_pos t ht_pos
    have hτ : 0 < s t + r t := add_pos hst hrt
    obtain ⟨hJX_eq, hJY_eq, hJX_pos, hJY_pos, hJS_pos, h_stam⟩ := h_per_t t ht_pos hst hrt
    have h_deriv := twoTimeLogRatioGap_hasDerivAt X Y Z_X Z_Y Z P
      hX hZX hXZX hY hZY hYZY h_path_X h_path_Y h_reg_X h_reg_Y
      hZ hZ_law hXYZ hZX_law hZY_law hXY_ZXZY_pair hZX_ZY h_reg_sum
      ht_pos hst hrt hτ hJX_eq hJY_eq hJX_pos hJY_pos
    have h_le := twoTimeLogRatioGap_deriv_le_zero X Y Z_X Z_Y P
      h_path_X h_path_Y ht_pos
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
        ((h_reg_sum.reg_at (s t + r t) hτ).density_t))
      hJX_pos hJY_pos hJS_pos h_stam
    rw [h_deriv.deriv]
    exact h_le
  -- Endpoint `0` is a (left) cluster point of `Set.Ioi 0`.
  have h_cluster : ClusterPt (0 : ℝ) (Filter.principal (Set.Ioi 0)) := by
    rw [← mem_closure_iff_clusterPt, closure_Ioi]
    exact Set.self_mem_Ici
  -- Endpoint continuity (Task 1).
  have h_cont_zero : ContinuousWithinAt f (Set.Ioi 0) 0 :=
    twoTimeLogRatioGap_continuousWithinAt_zero X Y Z_X Z_Y Z P
      hX hY hZX hZY hZ hZX_law hZY_law hZ_law hXY_ZXZY_pair hXYZ hZX_ZY
      h_path_X h_path_Y h_pos h_endpt_sum
  -- Insert the endpoint: `insert 0 (Ioi 0) = Ici 0`.
  have := h_anti_Ioi.insert_of_continuousWithinAt h_cluster h_cont_zero
  rwa [Set.Ioi_insert] at this

/-- **TT-`_tendsto_zero_atTop`** — the two-time gap tends to `0` as `t → ∞`
(Gaussian-saturation limit along the matched paths). Mirrors
`csiszarLogRatioGap_tendsto_zero_atTop` (`EPICase1RatioLimit.lean:1178`).

**§1 (genuine reduction, sorry-free in this body).** Using
`IsMatchedTimePath.matched_growth` (for `t ≥ 0`, `heatFlowEP A B P (s t) =
heatFlowEP A B P 0 · eᵗ`) and `heatFlowEP A B P 0 = entropyPower (P.map A)` (the
`√0 = 0` collapse), the matched-path denominator
`B t = heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t)` equals
`(eP X + eP Y)·eᵗ`, whence `log B t = log (eP X + eP Y) + t`. Therefore the gap
reduces (for `t ≥ 0`) to `R t = log (A t) − log (B t)`, the log of the EPI
saturation ratio `A t / B t` (`A t = sumHeatFlowEP …(s t)(r t)` is the numerator).
The `−t` correction is absorbed by the `eᵗ` growth — established genuinely in the
body via `Real.log_mul`/`Real.log_exp`, no `sorry`.

**§2 (saturation core, genuinely closed 2026-06-06).** The EPI saturation
`A t / B t → 1` as `t → ∞`, isolated into `have h_ratio_tendsto`; from it
`log (A t / B t) → log 1 = 0` (continuity of `log` at `1`) and
`log (A/B) = log A − log B` (both positive) recover `R t → 0`. The saturation is
reduced to a single genuine limit `A t / eᵗ → N(X) + N(Y)`:

* `A t` (the matched-sum numerator) is identified with a single-noise heat flow of
`X+Y` at `τ = s t + r t` via `matchedSum_law_eq` (`@audit:ok`), then split by
`entropyPower_path_scaling` as `A t = τ · NSr(τ)` with `NSr(σ) → ν` and
`ν = N(𝒩(0,1))` the common noise entropy power.
* the component asymptotics `s t / eᵗ → N(X)/ν`, `r t / eᵗ → N(Y)/ν` come from
combining matched growth (`N_X(s t) = N(X)·eᵗ`) with the scaling identity
`N_X(s t) = s t · NXr(s t)` and the §3 envelope limit `NXr(s t) → ν` (composed
with `s, r → ∞`). Hence `τ / eᵗ → (N(X)+N(Y))/ν`, so `A t / eᵗ → (N(X)+N(Y))`
and the `ν` factors cancel.

The §3 saturation machinery (`entropyPower_rescaled_path_tendsto`,
`IsRescaledPathRegular`) is keyed to the single-time rescaling `A/√t + B`; the
matched path uses different times `s t ≠ r t`, so the re-keying is exactly the
`matchedSum_law_eq` reduction above. No EPI/Stam conclusion is bundled; the
added preconditions (noise laws/independences, path divergence `s,r → ∞`, per-σ
scaling regularity, the three `IsRescaledPathRegular` bundles) are genuine
regularity — none of them encodes `A t / B t → 1`.
@audit:ok -/
theorem twoTimeLogRatioGap_tendsto_zero_atTop
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    -- §2 saturation regularity (all genuine; none bundles the ratio→1 conclusion):
    (Z : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω => X ω + Y ω) (fun ω => (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω => X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZ_ac : (P.map Z) ≪ volume)
    -- path divergence (genuine property of the matched path; not the conclusion):
    (hs_atTop : Filter.Tendsto s Filter.atTop Filter.atTop)
    (hr_atTop : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hs_pos : ∀ t : ℝ, 0 < t → 0 < s t) (hr_pos : ∀ t : ℝ, 0 < t → 0 < r t)
    -- per-σ scaling regularity (consumed by `entropyPower_path_scaling`):
    (h_scale_X : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => X ω / Real.sqrt σ + Z_X ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω / Real.sqrt σ + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => Y ω / Real.sqrt σ + Z_Y ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => Y ω / Real.sqrt σ + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => (X ω + Y ω) / Real.sqrt σ + Z ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => (X ω + Y ω) / Real.sqrt σ + Z ω)).rnDeriv volume x).toReal)) volume)
    -- per-path squeeze regularity bundles (方針 X; audited non-load-bearing in §3):
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX 1)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY 1)
    (h_reg_S : IsRescaledPathRegular (fun ω => X ω + Y ω) Z P varS 1) :
    Filter.Tendsto (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Abbreviations: the saturation numerator `A t` and the matched-path
  -- denominator `B t = (eP X + eP Y)·eᵗ`.
  set A := fun t : ℝ => sumHeatFlowEP X Y Z_X Z_Y P (s t) (r t) with hA
  set B := fun t : ℝ =>
    heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t) with hB
  -- (eP X + eP Y) is positive.
  have hXY_pos : (0 : ℝ) < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- `heatFlowEP _ _ _ 0 = entropyPower (P.map _)` (the `√0 = 0` collapse).
  have hX0 : heatFlowEP X Z_X P 0 = entropyPower (P.map X) := by
    unfold heatFlowEP
    have : (fun ω => X ω + Real.sqrt 0 * Z_X ω) = X := by
      funext ω; simp [Real.sqrt_zero]
    rw [this]
  have hY0 : heatFlowEP Y Z_Y P 0 = entropyPower (P.map Y) := by
    unfold heatFlowEP
    have : (fun ω => Y ω + Real.sqrt 0 * Z_Y ω) = Y := by
      funext ω; simp [Real.sqrt_zero]
    rw [this]
  -- §1 (genuine reduction): for `t ≥ 0`, `R t = log (A t) − log (B t)` and
  -- `B t = (eP X + eP Y)·eᵗ`.
  have hB_eq : ∀ t : ℝ, 0 ≤ t →
      B t = (entropyPower (P.map X) + entropyPower (P.map Y)) * Real.exp t := by
    intro t ht
    show heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t) = _
    rw [h_path_X.matched_growth t ht, h_path_Y.matched_growth t ht, hX0, hY0]
    ring
  have h_R_eq : ∀ t : ℝ, 0 ≤ t →
      twoTimeLogRatioGap X Y Z_X Z_Y P s r t = Real.log (A t) - Real.log (B t) := by
    intro t ht
    rw [hB_eq t ht]
    rw [Real.log_mul hXY_pos.ne' (Real.exp_ne_zero t), Real.log_exp]
    show Real.log (A t) - _ - t = _
    rw [hA]
    ring
  -- §2 (saturation core): the EPI ratio `A t / B t → 1` along the matched path.
  have h_ratio_tendsto :
      Filter.Tendsto (fun t : ℝ => A t / B t) Filter.atTop (nhds (1 : ℝ)) := by
    -- Common noise entropy power `ν = N(𝒩(0,1))`; all three noises share it.
    set ν : ℝ := entropyPower (gaussianReal 0 (1 : ℝ≥0)) with hν
    have hν_pos : (0 : ℝ) < ν := entropyPower_pos _
    -- Rescaled-path envelope limits → ν (from §3 `entropyPower_rescaled_path_tendsto`).
    have hNXr_lim : Filter.Tendsto
        (fun σ : ℝ => entropyPower (P.map (fun ω => X ω / Real.sqrt σ + Z_X ω)))
        Filter.atTop (nhds ν) := by
      have h := entropyPower_rescaled_path_tendsto X Z_X P hX hZX (1 : ℝ≥0) one_ne_zero
        hZX_law varX h_varX_nn hZX_ac h_reg_X
      rw [hZX_law, ← hν] at h; exact h
    have hNYr_lim : Filter.Tendsto
        (fun σ : ℝ => entropyPower (P.map (fun ω => Y ω / Real.sqrt σ + Z_Y ω)))
        Filter.atTop (nhds ν) := by
      have h := entropyPower_rescaled_path_tendsto Y Z_Y P hY hZY (1 : ℝ≥0) one_ne_zero
        hZY_law varY h_varY_nn hZY_ac h_reg_Y
      rw [hZY_law, ← hν] at h; exact h
    have hNSr_lim : Filter.Tendsto
        (fun σ : ℝ => entropyPower (P.map (fun ω => (X ω + Y ω) / Real.sqrt σ + Z ω)))
        Filter.atTop (nhds ν) := by
      have h := entropyPower_rescaled_path_tendsto (fun ω => X ω + Y ω) Z P (hX.add hY) hZ
        (1 : ℝ≥0) one_ne_zero hZ_law varS h_varS_nn hZ_ac h_reg_S
      rw [hZ_law, ← hν] at h; exact h
    -- Compose envelope limits with path divergence `s, r, τ = s + r → ∞`.
    have hτ_atTop : Filter.Tendsto (fun t => s t + r t) Filter.atTop Filter.atTop :=
      hs_atTop.atTop_add_atTop hr_atTop
    have hNXr_s : Filter.Tendsto
        (fun t : ℝ => entropyPower (P.map (fun ω => X ω / Real.sqrt (s t) + Z_X ω)))
        Filter.atTop (nhds ν) := hNXr_lim.comp hs_atTop
    have hNYr_r : Filter.Tendsto
        (fun t : ℝ => entropyPower (P.map (fun ω => Y ω / Real.sqrt (r t) + Z_Y ω)))
        Filter.atTop (nhds ν) := hNYr_lim.comp hr_atTop
    have hNSr_τ : Filter.Tendsto
        (fun t : ℝ =>
          entropyPower (P.map (fun ω => (X ω + Y ω) / Real.sqrt (s t + r t) + Z ω)))
        Filter.atTop (nhds ν) := hNSr_lim.comp hτ_atTop
    -- Component asymptotics: `s t / eᵗ → N(X)/ν`, `r t / eᵗ → N(Y)/ν`.
    -- From `N_X(s t) = N(X)·eᵗ` (matched growth) and `N_X(s t) = s t · NXr(s t)` (scaling).
    have h_sX : ∀ t : ℝ, 0 < t →
        s t / Real.exp t
          = entropyPower (P.map X)
              / entropyPower (P.map (fun ω => X ω / Real.sqrt (s t) + Z_X ω)) := by
      intro t ht
      have hgrow : heatFlowEP X Z_X P (s t) = entropyPower (P.map X) * Real.exp t := by
        rw [h_path_X.matched_growth t ht.le, hX0]
      have hsc : heatFlowEP X Z_X P (s t)
          = s t * entropyPower (P.map (fun ω => X ω / Real.sqrt (s t) + Z_X ω)) :=
        entropyPower_path_scaling X Z_X P hX hZX (hs_pos t ht)
          (h_scale_X (s t) (hs_pos t ht)).1 (h_scale_X (s t) (hs_pos t ht)).2
      have hNXr_pos : 0 < entropyPower (P.map (fun ω => X ω / Real.sqrt (s t) + Z_X ω)) :=
        entropyPower_pos _
      rw [div_eq_div_iff (Real.exp_pos t).ne' hNXr_pos.ne', ← hsc, hgrow]
    have h_rY : ∀ t : ℝ, 0 < t →
        r t / Real.exp t
          = entropyPower (P.map Y)
              / entropyPower (P.map (fun ω => Y ω / Real.sqrt (r t) + Z_Y ω)) := by
      intro t ht
      have hgrow : heatFlowEP Y Z_Y P (r t) = entropyPower (P.map Y) * Real.exp t := by
        rw [h_path_Y.matched_growth t ht.le, hY0]
      have hsc : heatFlowEP Y Z_Y P (r t)
          = r t * entropyPower (P.map (fun ω => Y ω / Real.sqrt (r t) + Z_Y ω)) :=
        entropyPower_path_scaling Y Z_Y P hY hZY (hr_pos t ht)
          (h_scale_Y (r t) (hr_pos t ht)).1 (h_scale_Y (r t) (hr_pos t ht)).2
      have hNYr_pos : 0 < entropyPower (P.map (fun ω => Y ω / Real.sqrt (r t) + Z_Y ω)) :=
        entropyPower_pos _
      rw [div_eq_div_iff (Real.exp_pos t).ne' hNYr_pos.ne', ← hsc, hgrow]
    have h_sX_lim : Filter.Tendsto (fun t : ℝ => s t / Real.exp t) Filter.atTop
        (nhds (entropyPower (P.map X) / ν)) := by
      refine (Filter.tendsto_congr' ?_).mp (tendsto_const_nhds.div hNXr_s hν_pos.ne')
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      exact (h_sX t ht).symm
    have h_rY_lim : Filter.Tendsto (fun t : ℝ => r t / Real.exp t) Filter.atTop
        (nhds (entropyPower (P.map Y) / ν)) := by
      refine (Filter.tendsto_congr' ?_).mp (tendsto_const_nhds.div hNYr_r hν_pos.ne')
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      exact (h_rY t ht).symm
    -- `τ t / eᵗ → (N(X) + N(Y))/ν`.
    have h_τ_lim : Filter.Tendsto (fun t : ℝ => (s t + r t) / Real.exp t) Filter.atTop
        (nhds ((entropyPower (P.map X) + entropyPower (P.map Y)) / ν)) := by
      have hadd := h_sX_lim.add h_rY_lim
      have heq : (fun t : ℝ => s t / Real.exp t + r t / Real.exp t)
          = (fun t : ℝ => (s t + r t) / Real.exp t) := by funext t; rw [add_div]
      rw [heq, ← add_div] at hadd
      exact hadd
    -- `A t = τ t · NSr(τ t)` for `t > 0` (matched-sum reduction + scaling).
    have h_A : ∀ t : ℝ, 0 < t →
        A t = (s t + r t)
            * entropyPower (P.map (fun ω => (X ω + Y ω) / Real.sqrt (s t + r t) + Z ω)) := by
      intro t ht
      have hτpos : 0 < s t + r t := by
        have := hs_pos t ht; have := hr_pos t ht; linarith
      have hlaw := matchedSum_law_eq X Y Z_X Z_Y Z P hX hY hZX hZY hZ hZX_law hZY_law hZ_law
        hXY_ZXZY_pair hXY_Z hZX_ZY (s t) (r t) (hs_pos t ht) (hr_pos t ht)
      have hAeq : A t
          = entropyPower (P.map (fun ω => (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω)) := by
        simp only [hA, sumHeatFlowEP]
        exact congrArg entropyPower hlaw
      rw [hAeq]
      exact entropyPower_path_scaling (fun ω => X ω + Y ω) Z P (hX.add hY) hZ hτpos
        (h_scale_sum (s t + r t) hτpos).1 (h_scale_sum (s t + r t) hτpos).2
    -- `A t / eᵗ → N(X) + N(Y)`.
    have h_Ae_lim : Filter.Tendsto (fun t : ℝ => A t / Real.exp t) Filter.atTop
        (nhds (entropyPower (P.map X) + entropyPower (P.map Y))) := by
      have hprod := h_τ_lim.mul hNSr_τ
      have hval : ((entropyPower (P.map X) + entropyPower (P.map Y)) / ν) * ν
          = entropyPower (P.map X) + entropyPower (P.map Y) := by
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self hν_pos.ne', mul_one]
      rw [hval] at hprod
      refine (Filter.tendsto_congr' ?_).mp hprod
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      rw [h_A t ht]; ring
    -- `A t / B t = (A t / eᵗ)·(1/(N(X)+N(Y))) → 1` (eventually, `t ≥ 0`, via `hB_eq`).
    have hfin := h_Ae_lim.mul_const
      (1 / (entropyPower (P.map X) + entropyPower (P.map Y)))
    have hone : (entropyPower (P.map X) + entropyPower (P.map Y))
        * (1 / (entropyPower (P.map X) + entropyPower (P.map Y))) = 1 := by
      rw [mul_one_div, div_self hXY_pos.ne']
    rw [hone] at hfin
    refine (Filter.tendsto_congr' ?_).mp hfin
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hB_eq t ht]
    field_simp
  -- `B t > 0` for `t ≥ 0` (positive entropy powers times `eᵗ`).
  have hB_pos : ∀ t : ℝ, 0 ≤ t → 0 < B t := by
    intro t ht
    rw [hB_eq t ht]; positivity
  have hA_pos : ∀ t : ℝ, 0 < A t := fun t => by rw [hA]; exact entropyPower_pos _
  -- `log (A/B) → log 1 = 0` by continuity of `log` at `1`.
  have h_logratio_tendsto :
      Filter.Tendsto (fun t : ℝ => Real.log (A t / B t)) Filter.atTop (nhds (0 : ℝ)) := by
    have := (Real.continuousAt_log (one_ne_zero)).tendsto.comp h_ratio_tendsto
    simpa using this
  -- `log (A/B) = log A − log B` (both positive, eventually for `t ≥ 0`).
  have h_eventually_eq : ∀ᶠ t in Filter.atTop,
      Real.log (A t / B t) = twoTimeLogRatioGap X Y Z_X Z_Y P s r t := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.log_div (hA_pos t).ne' (hB_pos t ht).ne', ← h_R_eq t ht]
  exact (Filter.tendsto_congr' h_eventually_eq).mp h_logratio_tendsto

/-- **TT-`epi_of_*`** — `R(0) ≥ 0 ⟹ EPI` for the two-time object.

`twoTimeLogRatioGap_at_zero` rewrites `R 0` to the EPI bridge form, so
`R 0 ≥ 0 ⟺ entropyPower (X+Y) ≥ entropyPower X + entropyPower Y`. Mirrors
`epi_of_csiszarLogRatioGap_zero_nonneg` (`EPIStamToBridge.lean:1030`).
@audit:ok -/
theorem epi_of_twoTimeLogRatioGap_zero_nonneg
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_nonneg : 0 ≤ twoTimeLogRatioGap X Y Z_X Z_Y P s r 0) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  rw [twoTimeLogRatioGap_at_zero X Y Z_X Z_Y P h_path_X h_path_Y] at h_nonneg
  -- `0 ≤ log A − log B` ⟺ `log B ≤ log A`.
  have h_log_le : Real.log (entropyPower (P.map X) + entropyPower (P.map Y))
      ≤ Real.log (entropyPower (P.map (fun ω => X ω + Y ω))) := by linarith
  -- Positivity of both `log` arguments.
  have hA_pos : 0 < entropyPower (P.map (fun ω => X ω + Y ω)) := entropyPower_pos _
  have hB_pos : 0 < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- `log B ≤ log A ⟺ B ≤ A` (both positive).
  rw [Real.log_le_log_iff hB_pos hA_pos] at h_log_le
  exact h_log_le

/-- **TT EPI via tendsto** — antitonicity + `R(t) → 0` give `R(0) ≥ 0`, hence EPI.

Order-limit bridge (`le_of_tendsto`) over `twoTimeLogRatioGap_antitoneOn_Ici_zero`
+ `twoTimeLogRatioGap_tendsto_zero_atTop`, then `epi_of_twoTimeLogRatioGap_zero_nonneg`.
Mirrors `epi_of_csiszarLogRatioGap_tendsto` (`EPICase1RatioLimit.lean:103`).
@audit:ok -/
theorem epi_of_twoTimeLogRatioGap_tendsto
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_anti : AntitoneOn (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t) (Set.Ici (0 : ℝ)))
    (h_lim : Filter.Tendsto (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
        Filter.atTop (nhds (0 : ℝ))) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  set R := fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t with hR
  -- `R 0 ≥ R t` for every `t ≥ 0` by antitonicity (`0 ≤ t`).
  have h_tail : ∀ᶠ t in Filter.atTop, R t ≤ R 0 := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact h_anti Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  -- `R t → 0` and `R t ≤ R 0` eventually ⟹ `0 ≤ R 0`.
  have h_zero_le : (0 : ℝ) ≤ R 0 := le_of_tendsto h_lim h_tail
  -- Bridge to EPI.
  exact epi_of_twoTimeLogRatioGap_zero_nonneg X Y Z_X Z_Y P h_path_X h_path_Y h_zero_le

/-- **TT case-1 EPI terminal** (two-time analog of the single-`t`
`entropyPower_add_ge_case1_of_regular`, `EPICase1RatioLimit.lean:1343`).

`N(X+Y) ≥ N(X) + N(Y)`, assembled from the three GENUINE two-time pillars
(`twoTimeLogRatioGap_antitoneOn_Ici_zero`, `twoTimeLogRatioGap_tendsto_zero_atTop`,
`epi_of_twoTimeLogRatioGap_tendsto`) + the path producer `matchedTimePath_exists`.
Unlike the single-`t` route (whose sum derivative is the variance-2 `2·J_sum` that
does NOT close from harmonic Stam), the two-time object perturbs `X`/`Y` at
*independent* matched times `s(t)`/`r(t)` and closes from the genuine harmonic Stam
producer.

**`J_X`/`J_Y` Fisher pin (honesty-load-bearing).** The Fisher infos are NOT free
variables: `J_X`/`J_Y` are defined as the total-domain functions
`fun σ => if 0 < σ then fisherInfoOfDensityReal ((h_reg_*.reg_at σ _).density_t) else 0`.
The same quantity supplies both (a) `matchedTimePath_exists`'s entropy-power
`HasDerivAt` (via `deBruijn_identity_v2` → `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt`)
and (b) Pillar B's per-`t` density-pin (`dif_pos` under `s t > 0`). `density_t` is
pointwise-pinned by `IsRegularDeBruijnHypV2.density_t_eq` (`∀ x`, NOT a.e.), so a
representative escape is structurally impossible — the same honest mechanism as
`twoTimeLogRatioGap_hasDerivAt`.

**Preconditions** are the union of `matchedTimePath_exists` (×2) + Pillar B + Pillar C
regularity, deduplicated. None encode the EPI conclusion (mirrors the single-`t`
terminal's `@audit:ok` union, `EPICase1RatioLimit.lean:1336-1342`):
* `h_endpt_X`/`h_endpt_Y` (path-producer endpoint continuity), `h_endpt_sum` (Pillar B);
* `h_reg_X`/`h_reg_Y`/`h_reg_sum : IsDeBruijnRegularityHyp` (de Bruijn + J pin);
* `h_scale_*` per-σ a.c.+integrability (consumed by `entropyPower_path_scaling`,
used both for the path-producer `hN_tendsto` and Pillar C);
* `h_rescale_*` (`IsRescaledPathRegular`) + `varX`/`varY`/`varS` (Pillar C squeeze
and the path-producer divergence);
* `h_stam_supply` the per-time harmonic-Stam + positivity supply (genuine producer
`isStamInequalityHyp_via_step3`, NOT a bundled conclusion — `1/J_S ≥ 1/J_X+1/J_Y`
is the Fisher form, a different statement from the EPI inequality).

**Proof done (2026-06-06): sorryAx-free.** `#print axioms
entropyPower_add_ge_case1_of_regular_twotime = [propext, Classical.choice,
Quot.sound]`. The body (1) defines `J_X`/`J_Y` by `dif_pos`, (2) assembles the
entropy-power `HasDerivAt` (`hJ_deriv_*`) and the `heatFlowEP` divergence
(`hN_tendsto_*`), (3) constructs `s`/`r` via the strengthened
`matchedTimePath_exists`, (4) discharges Pillar B's `h_per_t` (density-pin by
`dif_pos`, positivity + harmonic Stam from `h_stam_supply`), (5) closes with Pillar
C and `epi_of_twoTimeLogRatioGap_tendsto`.
@audit:ok -/
theorem entropyPower_add_ge_case1_of_regular_twotime
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hXZX : IndepFun X Z_X P) (hYZY : IndepFun Y Z_Y P)
    -- unit-noise laws
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    -- joint independences for the matched-sum law (Pillar B/C)
    (hXYZ : IndepFun (fun ω => X ω + Y ω) Z P)
    (hXY_ZXZY_pair : IndepFun (fun ω => X ω + Y ω) (fun ω => (Z_X ω, Z_Y ω)) P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    -- a.c. of the noises (Pillar C)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZ_ac : (P.map Z) ≪ volume)
    -- de Bruijn regularity (J pin + de Bruijn HasDerivAt source)
    (h_reg_X : IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : IsDeBruijnRegularityHyp Y Z_Y P)
    (h_reg_sum : IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) Z P)
    -- heat-flow endpoint regularity (path-producer endpoint continuity + Pillar B)
    (h_endpt_X : IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : IsHeatFlowEndpointRegular Y Z_Y P)
    (h_endpt_sum : IsHeatFlowEndpointRegular (fun ω => X ω + Y ω) Z P)
    -- per-σ scaling regularity (path-producer `hN_tendsto` + Pillar C)
    (h_scale_X : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => X ω / Real.sqrt σ + Z_X ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω / Real.sqrt σ + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => Y ω / Real.sqrt σ + Z_Y ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => Y ω / Real.sqrt σ + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => (X ω + Y ω) / Real.sqrt σ + Z ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => (X ω + Y ω) / Real.sqrt σ + Z ω)).rnDeriv volume x).toReal)) volume)
    -- per-path squeeze regularity (Pillar C + path-producer divergence)
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_rescale_X : IsRescaledPathRegular X Z_X P varX 1)
    (h_rescale_Y : IsRescaledPathRegular Y Z_Y P varY 1)
    (h_rescale_S : IsRescaledPathRegular (fun ω => X ω + Y ω) Z P varS 1)
    -- harmonic-Stam + positivity supply at independent matched times σ (X side) and
    -- τ (Y side); `J_S` is pinned to the single-noise sum heat flow at `σ + τ`.
    -- This is the GENUINE producer output (`isStamInequalityHyp_via_step3`), the
    -- Fisher form `1/J_S ≥ 1/J_X+1/J_Y` — NOT the EPI conclusion.
    (h_stam_supply : ∀ (σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ),
      0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_X.reg_at σ hσ).density_t) ∧
      0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_Y.reg_at τ hτ).density_t) ∧
      0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (σ + τ) (add_pos hσ hτ)).density_t) ∧
      1 / InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (σ + τ) (add_pos hσ hτ)).density_t)
        ≥ 1 / InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_X.reg_at σ hσ).density_t)
          + 1 / InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_Y.reg_at τ hτ).density_t)) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- ===== Fisher pin: total-domain `J_X`/`J_Y` (probe-5a). =====
  set J_X : ℝ → ℝ := fun σ =>
    if hσ : 0 < σ then
      InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
        ((h_reg_X.reg_at σ hσ).density_t)
    else 0 with hJX_def
  set J_Y : ℝ → ℝ := fun τ =>
    if hτ : 0 < τ then
      InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
        ((h_reg_Y.reg_at τ hτ).density_t)
    else 0 with hJY_def
  have hJX_val : ∀ (σ : ℝ) (hσ : 0 < σ), J_X σ
      = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_X.reg_at σ hσ).density_t) := by
    intro σ hσ; rw [hJX_def]; simp only [dif_pos hσ]
  have hJY_val : ∀ (τ : ℝ) (hτ : 0 < τ), J_Y τ
      = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at τ hτ).density_t) := by
    intro τ hτ; rw [hJY_def]; simp only [dif_pos hτ]
  -- `J_X`/`J_Y` positivity (path-producer `hJ_pos`), from the supply at `σ=τ`.
  have hJX_pos : ∀ σ : ℝ, 0 < σ → 0 < J_X σ := by
    intro σ hσ
    rw [hJX_val σ hσ]; exact (h_stam_supply σ σ hσ hσ).1
  have hJY_pos : ∀ τ : ℝ, 0 < τ → 0 < J_Y τ := by
    intro τ hτ
    rw [hJY_val τ hτ]; exact (h_stam_supply τ τ hτ hτ).2.1
  -- ===== `hJ_deriv` assembly (entropy-power level, probe-5c-i). =====
  have hJ_deriv_X : ∀ σ : ℝ, 0 < σ →
      HasDerivAt (fun u => heatFlowEP X Z_X P u) (heatFlowEP X Z_X P σ * J_X σ) σ := by
    intro σ hσ
    rw [hJX_val σ hσ]
    set J := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_X.reg_at σ hσ).density_t) with hJ_def
    have h_dB : HasDerivAt
        (fun s => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z_X s)))
        ((1/2) * J) σ := by
      have := InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2
        X Z_X hX hZX hXZX hσ (h_reg_X.reg_at σ hσ)
      simpa only [hJ_def] using this
    have h_eP := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB
    have h_val : heatFlowEP X Z_X P σ * J
        = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
            (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z_X σ)))
          * (2 * ((1/2) * J)) := by
      unfold heatFlowEP entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]; exact h_eP
  have hJ_deriv_Y : ∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun u => heatFlowEP Y Z_Y P u) (heatFlowEP Y Z_Y P τ * J_Y τ) τ := by
    intro τ hτ
    rw [hJY_val τ hτ]
    set J := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_Y.reg_at τ hτ).density_t) with hJ_def
    have h_dB : HasDerivAt
        (fun s => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Y Z_Y s)))
        ((1/2) * J) τ := by
      have := InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2
        Y Z_Y hY hZY hYZY hτ (h_reg_Y.reg_at τ hτ)
      simpa only [hJ_def] using this
    have h_eP := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB
    have h_val : heatFlowEP Y Z_Y P τ * J
        = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
            (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Y Z_Y τ)))
          * (2 * ((1/2) * J)) := by
      unfold heatFlowEP entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]; exact h_eP
  -- ===== `hN_tendsto` assembly (heatFlowEP divergence, probe-5d). =====
  have hN_tendsto_X : Filter.Tendsto (fun s => heatFlowEP X Z_X P s) Filter.atTop Filter.atTop := by
    set ν : ℝ := entropyPower (P.map Z_X) with hν
    have hν_pos : (0 : ℝ) < ν := entropyPower_pos _
    have hNr_lim := entropyPower_rescaled_path_tendsto X Z_X P hX hZX (1 : ℝ≥0) one_ne_zero
      hZX_law varX h_varX_nn hZX_ac h_rescale_X
    have h_eq : ∀ᶠ s in Filter.atTop,
        heatFlowEP X Z_X P s = s * entropyPower (P.map (fun ω => X ω / Real.sqrt s + Z_X ω)) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with s hs
      have hsc := entropyPower_path_scaling X Z_X P hX hZX hs (h_scale_X s hs).1 (h_scale_X s hs).2
      simpa only [heatFlowEP] using hsc
    have h_prod : Filter.Tendsto
        (fun s : ℝ => s * entropyPower (P.map (fun ω => X ω / Real.sqrt s + Z_X ω)))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_pos hν_pos Filter.tendsto_id hNr_lim
    exact h_prod.congr' (h_eq.mono (fun s hs => hs.symm))
  have hN_tendsto_Y : Filter.Tendsto (fun s => heatFlowEP Y Z_Y P s) Filter.atTop Filter.atTop := by
    set ν : ℝ := entropyPower (P.map Z_Y) with hν
    have hν_pos : (0 : ℝ) < ν := entropyPower_pos _
    have hNr_lim := entropyPower_rescaled_path_tendsto Y Z_Y P hY hZY (1 : ℝ≥0) one_ne_zero
      hZY_law varY h_varY_nn hZY_ac h_rescale_Y
    have h_eq : ∀ᶠ s in Filter.atTop,
        heatFlowEP Y Z_Y P s = s * entropyPower (P.map (fun ω => Y ω / Real.sqrt s + Z_Y ω)) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with s hs
      have hsc := entropyPower_path_scaling Y Z_Y P hY hZY hs (h_scale_Y s hs).1 (h_scale_Y s hs).2
      simpa only [heatFlowEP] using hsc
    have h_prod : Filter.Tendsto
        (fun s : ℝ => s * entropyPower (P.map (fun ω => Y ω / Real.sqrt s + Z_Y ω)))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_pos hν_pos Filter.tendsto_id hNr_lim
    exact h_prod.congr' (h_eq.mono (fun s hs => hs.symm))
  -- ===== Construct the matched paths `s` / `r` (strengthened `matchedTimePath_exists`). =====
  obtain ⟨s, h_path_X, hs_pos, hs_atTop⟩ :=
    matchedTimePath_exists X Z_X P J_X hX hZX hXZX hJX_pos hJ_deriv_X h_endpt_X hN_tendsto_X
  obtain ⟨r, h_path_Y, hr_pos, hr_atTop⟩ :=
    matchedTimePath_exists Y Z_Y P J_Y hY hZY hYZY hJY_pos hJ_deriv_Y h_endpt_Y hN_tendsto_Y
  -- ===== `h_pos` (Pillar B), built from path positivity. =====
  have h_pos : ∀ t : ℝ, 0 < t → 0 < s t ∧ 0 < r t :=
    fun t ht => ⟨hs_pos t ht, hr_pos t ht⟩
  -- ===== Pillar B `h_per_t`: density-pin (`dif_pos`) + supply at `s t`, `r t`. =====
  have h_per_t : ∀ (t : ℝ), 0 < t → ∀ (hst : 0 < s t) (hrt : 0 < r t),
      J_X (s t) = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_X.reg_at (s t) hst).density_t) ∧
      J_Y (r t) = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at (r t) hrt).density_t) ∧
      0 < J_X (s t) ∧ 0 < J_Y (r t) ∧
      0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t) ∧
      1 / InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t)
        ≥ 1 / J_X (s t) + 1 / J_Y (r t) := by
    intro t ht hst hrt
    obtain ⟨hJXp, hJYp, hJSp, h_stam⟩ := h_stam_supply (s t) (r t) hst hrt
    refine ⟨hJX_val (s t) hst, hJY_val (r t) hrt, hJX_pos (s t) hst, hJY_pos (r t) hrt,
      hJSp, ?_⟩
    rw [hJX_val (s t) hst, hJY_val (r t) hrt]; exact h_stam
  -- ===== Pillar B: antitonicity. =====
  have h_anti := twoTimeLogRatioGap_antitoneOn_Ici_zero X Y Z_X Z_Y Z P
    hX hZX hXZX hY hZY hYZY hZ hZ_law hXYZ hZX_law hZY_law hXY_ZXZY_pair hZX_ZY
    h_path_X h_path_Y h_reg_X h_reg_Y h_reg_sum h_endpt_sum h_pos h_per_t
  -- ===== Pillar C: saturation `R t → 0`. =====
  have h_lim := twoTimeLogRatioGap_tendsto_zero_atTop X Y Z_X Z_Y P
    h_path_X h_path_Y Z hX hY hZX hZY hZ hZX_law hZY_law hZ_law
    hXY_ZXZY_pair hXYZ hZX_ZY hZX_ac hZY_ac hZ_ac hs_atTop hr_atTop hs_pos hr_pos
    h_scale_X h_scale_Y h_scale_sum varX varY varS h_varX_nn h_varY_nn h_varS_nn
    h_rescale_X h_rescale_Y h_rescale_S
  -- ===== Seam: EPI from antitonicity + saturation. =====
  exact epi_of_twoTimeLogRatioGap_tendsto X Y Z_X Z_Y P h_path_X h_path_Y h_anti h_lim

end InformationTheory.Shannon.EPICase1TwoTime
