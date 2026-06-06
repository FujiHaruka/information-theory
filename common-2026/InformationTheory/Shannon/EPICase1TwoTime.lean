import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIStamDischarge
import InformationTheory.Shannon.FisherInfoV2DeBruijnGenuine
import InformationTheory.Shannon.EPIL3Integration
import InformationTheory.Shannon.EPIStamToBridge
import InformationTheory.Shannon.EPICase1RatioLimit
import InformationTheory.Shannon.EPIG2HeatFlowContinuity
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

/-!
# EPI case-1 sum frontier — two-time object skeleton

The single-time log-ratio object `csiszarLogRatioGap` (`EPIL3Integration.lean`)
perturbs `X` and `Y` at the **same** time `t`, forcing `s = r = t`. Its sum
derivative is the variance-2 quantity `2·J_sum`, which does **not** close from
the harmonic Stam inequality (mechanically refuted in the GS-A3' gate, see
`docs/shannon/proof-log-epi-case1-genvar-struct.md` §GS-A3').

The **two-time object** perturbs `X` at time `s` and `Y` at time `r`
**independently**, and follows the FII-matched path `s'(t) = 1/J_X(s)`,
`r'(t) = 1/J_Y(r)`. Along this path the matched-time characterization gives
`N_X(s(t)) = N_X(0)·eᵗ`, `N_Y(r(t)) = N_Y(0)·eᵗ`, so the gap (formulation (b),
entropy-power reparametrization) is

  `R(t) = log N(s(t),r(t)) − log(N_X(0) + N_Y(0)) − t`,

with derivative `R'(t) = J_S·(1/J_X + 1/J_Y) − 1 ≤ 0` from the **existing**
harmonic Stam producer (no new Mathlib wall). The arith core gate is PASS
(proof-log §Two-time object, `twotime_full`); the formulation gate is PASS
(proof-log §Two-time formulation gate, `ProbeF1.lean`, `e^t` characterization +
inverse-function chain rule).

This file is the **Phase 2 declaration skeleton** of
`docs/shannon/epi-case1-twotime-restructure-plan.md`. Every body is `sorry`
with `@residual(plan:epi-case1-twotime-restructure-plan)`. Bodies are filled in
later phases (Phase 3 deriv core / Phase 4 endpoints).

## Honesty notes

* `twoTimeLogRatioGap` is a plain `def` parametrized by the matched paths
  `s r : ℝ → ℝ` (formulation (b) `e^t` closed form). The paths are **not**
  load-bearing hypotheses: they are constructed (existence delivered by
  `matchedTimePath_exists`, a `sorry` lemma whose hypotheses are only the
  regularity preconditions `J_X > 0`, measurability, independence).
* The `IsMatchedTimePath` predicate below records the **output** of the path
  construction (matched `e^t` property + `HasDerivAt`). It is genuinely
  produced by `matchedTimePath_exists`; consumers receive it as a *constructed*
  object, not as a bundled core of the EPI conclusion. The EPI inequality
  itself is never encoded in any hypothesis.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace InformationTheory.Shannon.EPICase1TwoTime

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## §0 — Matched-time path abbreviations

The single-source heat-flow entropy power `N_A(s) = entropyPower (P.map (A + √s·B))`.
The matched path `s(t)` is the inverse of `N_A` solving `N_A(s(t)) = N_A(0)·eᵗ`.
-/

/-- Single-source heat-flow entropy power along the perturbation `A + √s·B`.
`N_A(0) = entropyPower (P.map A)`. -/
noncomputable def heatFlowEP (A B : Ω → ℝ) (P : Measure Ω) (s : ℝ) : ℝ :=
  entropyPower (P.map (fun ω => A ω + Real.sqrt s * B ω))

/-- **Matched-time path predicate** (output of the inverse-function construction).

For a path `s : ℝ → ℝ` along the `A`-perturbation, this records that:
* `s` starts at `0` (`s 0 = 0`);
* the entropy power grows as `eᵗ`: `N_A(s(t)) = N_A(0)·eᵗ` for `t ≥ 0`
  (the matched-time `e^t` characterization, proof-log §formulation gate);
* `s` is continuous on `[0, ∞)`;
* on the interior `t > 0`, `s` has derivative `1/J_A(s(t))` (FII-matched
  velocity), where `J_A` is the Fisher info of the perturbed density.

This is **not** a load-bearing hypothesis on the EPI conclusion: it is the
genuine output of `matchedTimePath_exists` (inverse-function subproject), whose
inputs are only regularity preconditions (`J_A > 0`, measurability, indep). -/
structure IsMatchedTimePath (A B : Ω → ℝ) (P : Measure Ω)
    (J_A : ℝ → ℝ) (s : ℝ → ℝ) : Prop where
  /-- The path starts at time `0`. -/
  start_zero : s 0 = 0
  /-- Matched `e^t` growth of the single-source entropy power. -/
  matched_growth : ∀ t : ℝ, 0 ≤ t → heatFlowEP A B P (s t) = heatFlowEP A B P 0 * Real.exp t
  /-- The path is continuous on `[0, ∞)`. -/
  cont : ContinuousOn s (Set.Ici 0)
  /-- FII-matched velocity on the interior. -/
  deriv_at : ∀ t : ℝ, 0 < t → HasDerivAt s (1 / J_A (s t)) t

/-! ## §1 — Matched-time path existence (inverse-function subproject)

The largest block (Phase 2 ~200-300 lines): construct `s(t) = N_A⁻¹(N_A(0)·eᵗ)`
via strict monotonicity (`J_A > 0`), continuity on `Ici 0`, surjectivity
(`N_A → ∞`), continuous inverse (`StrictMonoOn.orderIso`), and inverse-function
derivative (`HasDerivAt.of_local_left_inverse` + `comp`). The hypotheses are
**only** regularity preconditions; the conclusion (existence of a matched path)
is the genuine output, not bundled.
-/

/-- **TT-path existence** — the matched-time path `s : ℝ → ℝ` exists.

Hypotheses are regularity preconditions only: positivity of the Fisher info
`J_A` along the path (`hJ_pos`, a genuine `0 < fisherInfo` precondition that has
no in-tree theorem, threaded as in `csiszarLogRatioGap_deriv_le_zero`'s
`hJX_pos`), measurability, and independence. The conclusion is `∃ s,
IsMatchedTimePath ...` — the existence of the matched path with its `e^t`
property and FII-matched derivative.

Filled in Phase 2 (inverse-function subproject): strict monotonicity from
`J_A > 0` (`strictMonoOn_of_deriv_pos`), continuity on `Ici 0`
(interior `HasDerivAt` + heat-flow endpoint, CLOSED), surjectivity via
`entropyPower_path_scaling` × `entropyPower_rescaled_path_tendsto`, IVT
(`intermediate_value_Ici`), continuous inverse (`StrictMonoOn.orderIso`),
inverse derivative (`HasDerivAt.of_local_left_inverse` + `HasDerivAt.comp`).

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem matchedTimePath_exists
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (J_A : ℝ → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hAB : IndepFun A B P)
    (hJ_pos : ∀ s : ℝ, 0 < s → 0 < J_A s)
    (hJ_deriv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun u => heatFlowEP A B P u) (heatFlowEP A B P s * J_A s) s) :
    ∃ s : ℝ → ℝ, IsMatchedTimePath A B P J_A s := by
  sorry

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

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem twoTimeLogRatioGap_at_zero
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r) :
    twoTimeLogRatioGap X Y Z_X Z_Y P s r 0
      = Real.log (entropyPower (P.map (fun ω => X ω + Y ω)))
        - Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) := by
  sorry

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

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem twoTimeLogRatioGap_hasDerivAt
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
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
    (hJX_eq : J_X (s t)
        = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_X.reg_at (s t) hst).density_t))
    (hJY_eq : J_Y (r t)
        = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_Y.reg_at (r t) hrt).density_t))
    (hJX_pos : 0 < J_X (s t)) (hJY_pos : 0 < J_Y (r t)) :
    HasDerivAt (fun u : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r u)
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) hτ).density_t)
        * (1 / J_X (s t) + 1 / J_Y (r t)) - 1) t := by
  sorry

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
@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem twoTimeLogRatioGap_deriv_le_zero
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    {t : ℝ} (ht : 0 < t)
    (J_S : ℝ)
    (hJX_pos : 0 < J_X (s t)) (hJY_pos : 0 < J_Y (r t)) (hJS_pos : 0 < J_S)
    -- harmonic Stam for the matched-time sum (supplied by the genuine producer)
    (h_stam : 1 / J_S ≥ 1 / J_X (s t) + 1 / J_Y (r t)) :
    J_S * (1 / J_X (s t) + 1 / J_Y (r t)) - 1 ≤ 0 := by
  sorry

/-! ## §4 — Endpoints, antitonicity, EPI bridge -/

/-- **TT-`_continuousWithinAt_zero`** — the two-time gap is continuous at the
left endpoint `t = 0` (within `Ioi 0`).

The `log N(s(t),r(t))` term is continuous via the matched-path continuity
(`IsMatchedTimePath.cont`) + heat-flow endpoint continuity
(`heatFlowEntropyPower_continuousWithinAt_zero`, CLOSED 2026-06-05); the
`−t` term is continuous. Mirrors `csiszarLogRatioGap_continuousWithinAt_zero`
(`EPIStamToBridge.lean:1098`).

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem twoTimeLogRatioGap_continuousWithinAt_zero
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_endpt_X : IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : IsHeatFlowEndpointRegular Y Z_Y P) :
    ContinuousWithinAt (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
      (Set.Ioi (0 : ℝ)) 0 := by
  sorry

/-- **TT-`_antitoneOn_Ici_zero`** — the two-time gap is `AntitoneOn (Set.Ici 0)`.

`antitoneOn_of_deriv_nonpos` (convex `Set.Ici 0`) with continuity
(`twoTimeLogRatioGap_continuousWithinAt_zero`), differentiability + per-`t`
`deriv ≤ 0` (`twoTimeLogRatioGap_hasDerivAt.deriv` + `_deriv_le_zero`).
Mirrors `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1130`).

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem twoTimeLogRatioGap_antitoneOn_Ici_zero
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r) :
    AntitoneOn (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t) (Set.Ici (0 : ℝ)) := by
  sorry

/-- **TT-`_at_one_eq_zero`** — the two-time gap is `0` at the Gaussian-saturation
endpoint.

Mirrors `csiszarLogRatioGap_at_one_eq_zero` (`EPIL3Integration.lean:1426`,
`entropyPower_gaussian_additivity`): at the saturation time the perturbed
components are independent Gaussians and EPI saturates, so `log A − log A = 0`
(after the `−t` correction is matched by the `e^t` growth — checked in the body).

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem twoTimeLogRatioGap_tendsto_zero_atTop
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r) :
    Filter.Tendsto (fun t : ℝ => twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
      Filter.atTop (nhds (0 : ℝ)) := by
  sorry

/-- **TT-`epi_of_*`** — `R(0) ≥ 0 ⟹ EPI` for the two-time object.

`twoTimeLogRatioGap_at_zero` rewrites `R 0` to the EPI bridge form, so
`R 0 ≥ 0 ⟺ entropyPower (X+Y) ≥ entropyPower X + entropyPower Y`. Mirrors
`epi_of_csiszarLogRatioGap_zero_nonneg` (`EPIStamToBridge.lean:1030`).

@residual(plan:epi-case1-twotime-restructure-plan) -/
theorem epi_of_twoTimeLogRatioGap_zero_nonneg
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_nonneg : 0 ≤ twoTimeLogRatioGap X Y Z_X Z_Y P s r 0) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  sorry

/-- **TT EPI via tendsto** — antitonicity + `R(t) → 0` give `R(0) ≥ 0`, hence EPI.

Order-limit bridge (`le_of_tendsto`) over `twoTimeLogRatioGap_antitoneOn_Ici_zero`
+ `twoTimeLogRatioGap_tendsto_zero_atTop`, then `epi_of_twoTimeLogRatioGap_zero_nonneg`.
Mirrors `epi_of_csiszarLogRatioGap_tendsto` (`EPICase1RatioLimit.lean:103`).

@residual(plan:epi-case1-twotime-restructure-plan) -/
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
  sorry

end InformationTheory.Shannon.EPICase1TwoTime
