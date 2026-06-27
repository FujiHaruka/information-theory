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
import InformationTheory.Shannon.EPI.Case1.TwoTime.GapDerivative

/-!
# EPI case-1 two-time object — endpoints, antitonicity, Gaussian saturation (§4)

The endpoint continuity `twoTimeLogRatioGap_continuousWithinAt_zero`, the
antitonicity `twoTimeLogRatioGap_antitoneOn_Ici_zero`, and the
Gaussian-saturation limit `twoTimeLogRatioGap_tendsto_zero_atTop` (the gap tends
to `0` as `t → ∞` along the matched paths), together with the heat-flow scaling
and rescaled-path saturation machinery feeding the limit. Verbatim split of
`TwoTime.lean` §4 (monotonicity / saturation part); proofs unchanged. Builds on
the gap object and its derivative in `TwoTime.GapDerivative`. Umbrella:
`TwoTime.lean`.
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

/-! ## §4 — Endpoints, antitonicity, EPI bridge -/

/-- TT-`_continuousWithinAt_zero` — the two-time gap is continuous at the
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
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_pos : ∀ t : ℝ, 0 < t → 0 < s t ∧ 0 < r t)
    (h_endpt_sum : IsHeatFlowEndpointRegular (fun ω ↦ X ω + Y ω) Z P) :
    ContinuousWithinAt (fun t : ℝ ↦ twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
      (Set.Ioi (0 : ℝ)) 0 := by
  -- The single-noise endpoint heat-flow continuity atom (`wall:heatflow-continuity`
  -- CLOSED), continuous within `Ioi 0` at `0`.
  have h_endpt :
      ContinuousWithinAt
        (fun u : ℝ ↦ entropyPower (P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt u * Z ω)))
        (Set.Ioi (0 : ℝ)) 0 :=
    heatFlowEntropyPower_continuousWithinAt_zero
      (fun ω ↦ X ω + Y ω) Z P h_endpt_sum
  -- The matched reparameterisation `τ(t) = s t + r t`, continuous within `Ioi 0`
  -- at `0` (from `IsMatchedTimePath.cont` on `Ici 0`, restricted), with `τ 0 = 0`.
  have hs0 : s 0 = 0 := h_path_X.start_zero
  have hr0 : r 0 = 0 := h_path_Y.start_zero
  have hs_cwa : ContinuousWithinAt s (Set.Ioi (0 : ℝ)) 0 :=
    (h_path_X.cont 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self
  have hr_cwa : ContinuousWithinAt r (Set.Ioi (0 : ℝ)) 0 :=
    (h_path_Y.cont 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self
  have hτ_cwa : ContinuousWithinAt (fun t : ℝ ↦ s t + r t) (Set.Ioi (0 : ℝ)) 0 :=
    hs_cwa.add hr_cwa
  -- `τ` maps `Ioi 0` into `Ioi 0` (matched-path positivity).
  have hτ_maps : Set.MapsTo (fun t : ℝ ↦ s t + r t) (Set.Ioi (0 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    obtain ⟨hst, hrt⟩ := h_pos t ht
    exact add_pos hst hrt
  -- `τ 0 = 0`.
  have hτ0 : (fun t : ℝ ↦ s t + r t) 0 = 0 := by simp [hs0, hr0]
  -- Compose: single-noise heat flow along `τ`, continuous within `Ioi 0` at `0`.
  have h_heat_comp :
      ContinuousWithinAt
        (fun t : ℝ ↦ entropyPower
          (P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω)))
        (Set.Ioi (0 : ℝ)) 0 := by
    have hcomp := h_endpt.comp_of_eq hτ_cwa hτ_maps hτ0
    exact hcomp
  -- `log` of the heat flow, continuous within `Ioi 0` at `0`
  -- (`entropyPower` at `τ 0 = 0` is positive).
  have hpos0 : (0 : ℝ) < entropyPower
      (P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (s 0 + r 0) * Z ω)) := entropyPower_pos _
  have h_log_comp :
      ContinuousWithinAt
        (fun t : ℝ ↦ Real.log (entropyPower
          (P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω))))
        (Set.Ioi (0 : ℝ)) 0 := by
    refine h_heat_comp.log ?_
    simpa [hs0, hr0] using hpos0.ne'
  -- The `−log(const) − t` tail is continuous.
  have h_const : ContinuousWithinAt
      (fun _ : ℝ ↦ Real.log (entropyPower (P.map X) + entropyPower (P.map Y)))
      (Set.Ioi (0 : ℝ)) 0 := continuousWithinAt_const
  have h_id : ContinuousWithinAt (fun t : ℝ ↦ t) (Set.Ioi (0 : ℝ)) 0 :=
    continuousWithinAt_id
  -- Assemble the reduced (single-noise) continuity.
  have h_reduced :
      ContinuousWithinAt
        (fun t : ℝ ↦ Real.log (entropyPower
            (P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (s t + r t) * Z ω)))
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
    have hfun : (fun ω ↦ X ω + Real.sqrt (s 0) * Z_X ω + (Y ω + Real.sqrt (r 0) * Z_Y ω))
        = (fun ω ↦ (X ω + Y ω) + Real.sqrt (s 0 + r 0) * Z ω) := by
      funext ω
      simp [hs0, hr0, Real.sqrt_zero]
    rw [hfun]

/-- TT-`_antitoneOn_Ici_zero` — the two-time gap is `AntitoneOn (Set.Ici 0)`.

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

The added preconditions are all genuine regularity / Stam-supply, not a
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
    (hXYZ : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (h_reg_X : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω ↦ X ω + Y ω) Z P)
    (h_endpt_sum : IsHeatFlowEndpointRegular (fun ω ↦ X ω + Y ω) Z P)
    (h_pos : ∀ t : ℝ, 0 < t → 0 < s t ∧ 0 < r t)
    -- per-`t` regularity + harmonic Stam supply bundle (genuine, not bundled
    -- conclusion): density-pins for `J_X`/`J_Y`, positivity, and harmonic Stam.
    (h_per_t : ∀ (t : ℝ), 0 < t → ∀ (hst : 0 < s t) (hrt : 0 < r t),
      J_X (s t) = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_X.reg_at (s t) hst).density_t) ∧
      J_Y (r t) = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at (r t) hrt).density_t) ∧
      0 < J_X (s t) ∧ 0 < J_Y (r t) ∧
      0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t) ∧
      1 / InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t)
        ≥ 1 / J_X (s t) + 1 / J_Y (r t)) :
    AntitoneOn (fun t : ℝ ↦ twoTimeLogRatioGap X Y Z_X Z_Y P s r t) (Set.Ici (0 : ℝ)) := by
  set f := fun t : ℝ ↦ twoTimeLogRatioGap X Y Z_X Z_Y P s r t with hf_def
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
      (InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
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

theorem heatFlowEP_zero (A B : Ω → ℝ) (P : Measure Ω) :
    heatFlowEP A B P 0 = entropyPower (P.map A) := by
  unfold heatFlowEP
  have : (fun ω ↦ A ω + Real.sqrt 0 * B ω) = A := by
    funext ω; simp [Real.sqrt_zero]
  rw [this]

theorem matchedPath_component_div_exp_eq
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_A : ℝ → ℝ} {s : ℝ → ℝ}
    (h_path : IsMatchedTimePath A B P J_A s)
    (hA : Measurable A) (hB : Measurable B)
    (h_scale : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ A ω / Real.sqrt σ + B ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ A ω / Real.sqrt σ + B ω)).rnDeriv volume x).toReal)) volume)
    (hs_pos : ∀ t : ℝ, 0 < t → 0 < s t) :
    ∀ t : ℝ, 0 < t →
      s t / Real.exp t
        = entropyPower (P.map A)
            / entropyPower (P.map (fun ω ↦ A ω / Real.sqrt (s t) + B ω)) := by
  intro t ht
  have hgrow : heatFlowEP A B P (s t) = entropyPower (P.map A) * Real.exp t := by
    rw [h_path.matched_growth t ht.le, heatFlowEP_zero]
  have hsc : heatFlowEP A B P (s t)
      = s t * entropyPower (P.map (fun ω ↦ A ω / Real.sqrt (s t) + B ω)) :=
    entropyPower_path_scaling A B P hA hB (hs_pos t ht)
      (h_scale (s t) (hs_pos t ht)).1 (h_scale (s t) (hs_pos t ht)).2
  have hNr_pos : 0 < entropyPower (P.map (fun ω ↦ A ω / Real.sqrt (s t) + B ω)) :=
    entropyPower_pos _
  rw [div_eq_div_iff (Real.exp_pos t).ne' hNr_pos.ne', ← hsc, hgrow]

theorem sumHeatFlowEP_eq_mul_rescaled
    (X Y Z_X Z_Y Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (h_scale_sum : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)).rnDeriv volume x).toReal)) volume)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    sumHeatFlowEP X Y Z_X Z_Y P σ τ
      = (σ + τ)
          * entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt (σ + τ) + Z ω)) := by
  have hτpos : 0 < σ + τ := add_pos hσ hτ
  have hlaw := matchedSum_law_eq X Y Z_X Z_Y Z P hX hY hZX hZY hZ hZX_law hZY_law hZ_law
    hXY_ZXZY_pair hXY_Z hZX_ZY σ τ hσ hτ
  have hAeq : sumHeatFlowEP X Y Z_X Z_Y P σ τ
      = entropyPower (P.map (fun ω ↦ (X ω + Y ω) + Real.sqrt (σ + τ) * Z ω)) := by
    simp only [sumHeatFlowEP]
    exact congrArg entropyPower hlaw
  rw [hAeq]
  exact entropyPower_path_scaling (fun ω ↦ X ω + Y ω) Z P (hX.add hY) hZ hτpos
    (h_scale_sum (σ + τ) hτpos).1 (h_scale_sum (σ + τ) hτpos).2

theorem tendsto_div_one_of_tendsto_atTop_of_eq_mul_exp
    {A B : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hAe : Filter.Tendsto (fun t : ℝ ↦ A t / Real.exp t) Filter.atTop (nhds c))
    (hB : ∀ᶠ t in Filter.atTop, B t = c * Real.exp t) :
    Filter.Tendsto (fun t : ℝ ↦ A t / B t) Filter.atTop (nhds (1 : ℝ)) := by
  have hfin := hAe.mul_const (1 / c)
  have hone : c * (1 / c) = 1 := by
    rw [mul_one_div, div_self hc.ne']
  rw [hone] at hfin
  refine (Filter.tendsto_congr' ?_).mp hfin
  filter_upwards [hB] with t ht
  rw [ht]
  field_simp

theorem entropyPower_rescaled_path_tendsto_gaussianEP
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    (hB_law : P.map B = gaussianReal 0 1)
    (hB_ac : (P.map B) ≪ volume)
    (var : ℝ) (h_var_nn : 0 ≤ var)
    (h_reg : IsRescaledPathRegular A B P var 1) :
    Filter.Tendsto
      (fun σ : ℝ ↦ entropyPower (P.map (fun ω ↦ A ω / Real.sqrt σ + B ω)))
      Filter.atTop (nhds (entropyPower (gaussianReal 0 (1 : ℝ≥0)))) := by
  have h := entropyPower_rescaled_path_tendsto A B P hA hB (1 : ℝ≥0) one_ne_zero
    hB_law var h_var_nn hB_ac h_reg
  rwa [hB_law] at h

theorem matchedPath_div_exp_tendsto
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_A : ℝ → ℝ} {s : ℝ → ℝ}
    (h_path : IsMatchedTimePath A B P J_A s)
    (hA : Measurable A) (hB : Measurable B)
    (h_scale : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ A ω / Real.sqrt σ + B ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ A ω / Real.sqrt σ + B ω)).rnDeriv volume x).toReal)) volume)
    (hs_pos : ∀ t : ℝ, 0 < t → 0 < s t)
    {ν : ℝ} (hν_pos : 0 < ν)
    (hN : Filter.Tendsto
      (fun t : ℝ ↦ entropyPower (P.map (fun ω ↦ A ω / Real.sqrt (s t) + B ω)))
      Filter.atTop (nhds ν)) :
    Filter.Tendsto (fun t : ℝ ↦ s t / Real.exp t) Filter.atTop
      (nhds (entropyPower (P.map A) / ν)) := by
  have h_comp := matchedPath_component_div_exp_eq A B P h_path hA hB h_scale hs_pos
  refine (Filter.tendsto_congr' ?_).mp (tendsto_const_nhds.div hN hν_pos.ne')
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  exact (h_comp t ht).symm

theorem tendsto_sum_mul_div_exp
    {f g h F : ℝ → ℝ} {a b ν : ℝ}
    (hf : Filter.Tendsto (fun t : ℝ ↦ f t / Real.exp t) Filter.atTop (nhds a))
    (hg : Filter.Tendsto (fun t : ℝ ↦ g t / Real.exp t) Filter.atTop (nhds b))
    (hh : Filter.Tendsto h Filter.atTop (nhds ν))
    (hF : ∀ᶠ t in Filter.atTop, F t = (f t + g t) * h t) :
    Filter.Tendsto (fun t : ℝ ↦ F t / Real.exp t) Filter.atTop (nhds ((a + b) * ν)) := by
  have h_sum : Filter.Tendsto (fun t : ℝ ↦ (f t + g t) / Real.exp t) Filter.atTop
      (nhds (a + b)) := by
    have hadd := hf.add hg
    have heq : (fun t : ℝ ↦ f t / Real.exp t + g t / Real.exp t)
        = (fun t : ℝ ↦ (f t + g t) / Real.exp t) := by funext t; rw [add_div]
    rwa [heq] at hadd
  have hprod := h_sum.mul hh
  refine (Filter.tendsto_congr' ?_).mp hprod
  filter_upwards [hF] with t ht
  rw [ht]; ring

theorem sumHeatFlowEP_div_heatFlowEP_sum_tendsto_one
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    {J_X J_Y : ℝ → ℝ} {s r : ℝ → ℝ}
    (h_path_X : IsMatchedTimePath X Z_X P J_X s)
    (h_path_Y : IsMatchedTimePath Y Z_Y P J_Y r)
    (Z : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y) (hZ : Measurable Z)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZ_ac : (P.map Z) ≪ volume)
    (hs_atTop : Filter.Tendsto s Filter.atTop Filter.atTop)
    (hr_atTop : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hs_pos : ∀ t : ℝ, 0 < t → 0 < s t) (hr_pos : ∀ t : ℝ, 0 < t → 0 < r t)
    (h_scale_X : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ X ω / Real.sqrt σ + Z_X ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ X ω / Real.sqrt σ + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ Y ω / Real.sqrt σ + Z_Y ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ Y ω / Real.sqrt σ + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)).rnDeriv volume x).toReal)) volume)
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX 1)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY 1)
    (h_reg_S : IsRescaledPathRegular (fun ω ↦ X ω + Y ω) Z P varS 1)
    (h_den : ∀ t : ℝ, 0 ≤ t →
      heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t)
        = (entropyPower (P.map X) + entropyPower (P.map Y)) * Real.exp t) :
    Filter.Tendsto
      (fun t : ℝ ↦ sumHeatFlowEP X Y Z_X Z_Y P (s t) (r t)
        / (heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t)))
      Filter.atTop (nhds (1 : ℝ)) := by
  set A := fun t : ℝ ↦ sumHeatFlowEP X Y Z_X Z_Y P (s t) (r t) with hA
  have hXY_pos : (0 : ℝ) < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- Common noise entropy power `ν = N(𝒩(0,1))`; all three noises share it.
  set ν : ℝ := entropyPower (gaussianReal 0 (1 : ℝ≥0)) with hν
  have hν_pos : (0 : ℝ) < ν := entropyPower_pos _
  -- Rescaled-path envelope limits → ν (from §3 `entropyPower_rescaled_path_tendsto`).
  have hNXr_lim : Filter.Tendsto
      (fun σ : ℝ ↦ entropyPower (P.map (fun ω ↦ X ω / Real.sqrt σ + Z_X ω)))
      Filter.atTop (nhds ν) :=
    hν ▸ entropyPower_rescaled_path_tendsto_gaussianEP X Z_X P hX hZX hZX_law hZX_ac
      varX h_varX_nn h_reg_X
  have hNYr_lim : Filter.Tendsto
      (fun σ : ℝ ↦ entropyPower (P.map (fun ω ↦ Y ω / Real.sqrt σ + Z_Y ω)))
      Filter.atTop (nhds ν) :=
    hν ▸ entropyPower_rescaled_path_tendsto_gaussianEP Y Z_Y P hY hZY hZY_law hZY_ac
      varY h_varY_nn h_reg_Y
  have hNSr_lim : Filter.Tendsto
      (fun σ : ℝ ↦ entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)))
      Filter.atTop (nhds ν) :=
    hν ▸ entropyPower_rescaled_path_tendsto_gaussianEP (fun ω ↦ X ω + Y ω) Z P
      (hX.add hY) hZ hZ_law hZ_ac varS h_varS_nn h_reg_S
  -- Compose envelope limits with path divergence `s, r, τ = s + r → ∞`.
  have hτ_atTop : Filter.Tendsto (fun t ↦ s t + r t) Filter.atTop Filter.atTop :=
    hs_atTop.atTop_add_atTop hr_atTop
  have hNXr_s : Filter.Tendsto
      (fun t : ℝ ↦ entropyPower (P.map (fun ω ↦ X ω / Real.sqrt (s t) + Z_X ω)))
      Filter.atTop (nhds ν) := hNXr_lim.comp hs_atTop
  have hNYr_r : Filter.Tendsto
      (fun t : ℝ ↦ entropyPower (P.map (fun ω ↦ Y ω / Real.sqrt (r t) + Z_Y ω)))
      Filter.atTop (nhds ν) := hNYr_lim.comp hr_atTop
  have hNSr_τ : Filter.Tendsto
      (fun t : ℝ ↦
        entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt (s t + r t) + Z ω)))
      Filter.atTop (nhds ν) := hNSr_lim.comp hτ_atTop
  -- Component asymptotics: `s t / eᵗ → N(X)/ν`, `r t / eᵗ → N(Y)/ν`.
  have h_sX_lim := matchedPath_div_exp_tendsto X Z_X P h_path_X hX hZX h_scale_X hs_pos
    hν_pos hNXr_s
  have h_rY_lim := matchedPath_div_exp_tendsto Y Z_Y P h_path_Y hY hZY h_scale_Y hr_pos
    hν_pos hNYr_r
  -- `A t = τ t · NSr(τ t)` for `t > 0` (matched-sum reduction + scaling).
  have h_A : ∀ᶠ t in Filter.atTop,
      A t = (s t + r t)
          * entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt (s t + r t) + Z ω)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hA]
    exact sumHeatFlowEP_eq_mul_rescaled X Y Z_X Z_Y Z P hX hY hZX hZY hZ
      hZX_law hZY_law hZ_law hXY_ZXZY_pair hXY_Z hZX_ZY h_scale_sum
      (hs_pos t ht) (hr_pos t ht)
  -- `A t / eᵗ → N(X) + N(Y)` (the `ν` factors cancel: `(N(X)/ν + N(Y)/ν)·ν`).
  have h_Ae_lim : Filter.Tendsto (fun t : ℝ ↦ A t / Real.exp t) Filter.atTop
      (nhds (entropyPower (P.map X) + entropyPower (P.map Y))) := by
    have h := tendsto_sum_mul_div_exp h_sX_lim h_rY_lim hNSr_τ h_A
    have hval : (entropyPower (P.map X) / ν + entropyPower (P.map Y) / ν) * ν
        = entropyPower (P.map X) + entropyPower (P.map Y) := by
      field_simp
    rwa [hval] at h
  -- `A t / B t → 1` from `A t / eᵗ → N(X)+N(Y)` and `B t = (N(X)+N(Y))·eᵗ`.
  refine tendsto_div_one_of_tendsto_atTop_of_eq_mul_exp hXY_pos h_Ae_lim ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact h_den t ht

/-- TT-`_tendsto_zero_atTop` — the two-time gap tends to `0` as `t → ∞`
(Gaussian-saturation limit along the matched paths). Mirrors
`csiszarLogRatioGap_tendsto_zero_atTop` (`EPICase1RatioLimit.lean:1178`).

§1 (genuine reduction, sorry-free in this body). Using
`IsMatchedTimePath.matched_growth` (for `t ≥ 0`, `heatFlowEP A B P (s t) =
heatFlowEP A B P 0 · eᵗ`) and `heatFlowEP A B P 0 = entropyPower (P.map A)` (the
`√0 = 0` collapse), the matched-path denominator
`B t = heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t)` equals
`(eP X + eP Y)·eᵗ`, whence `log B t = log (eP X + eP Y) + t`. Therefore the gap
reduces (for `t ≥ 0`) to `R t = log (A t) − log (B t)`, the log of the EPI
saturation ratio `A t / B t` (`A t = sumHeatFlowEP …(s t)(r t)` is the numerator).
The `−t` correction is absorbed by the `eᵗ` growth — established genuinely in the
body via `Real.log_mul`/`Real.log_exp`, no `sorry`.

§2 (saturation core, genuinely closed 2026-06-06). The EPI saturation
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
    (hXY_ZXZY_pair : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ (Z_X ω, Z_Y ω)) P)
    (hXY_Z : IndepFun (fun ω ↦ X ω + Y ω) Z P)
    (hZX_ZY : IndepFun Z_X Z_Y P)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZ_ac : (P.map Z) ≪ volume)
    -- path divergence (genuine property of the matched path; not the conclusion):
    (hs_atTop : Filter.Tendsto s Filter.atTop Filter.atTop)
    (hr_atTop : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hs_pos : ∀ t : ℝ, 0 < t → 0 < s t) (hr_pos : ∀ t : ℝ, 0 < t → 0 < r t)
    -- per-σ scaling regularity (consumed by `entropyPower_path_scaling`):
    (h_scale_X : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ X ω / Real.sqrt σ + Z_X ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ X ω / Real.sqrt σ + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ Y ω / Real.sqrt σ + Z_Y ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ Y ω / Real.sqrt σ + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt σ + Z ω)).rnDeriv volume x).toReal)) volume)
    -- per-path squeeze regularity bundles (policy X; audited non-load-bearing in §3):
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX 1)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY 1)
    (h_reg_S : IsRescaledPathRegular (fun ω ↦ X ω + Y ω) Z P varS 1) :
    Filter.Tendsto (fun t : ℝ ↦ twoTimeLogRatioGap X Y Z_X Z_Y P s r t)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Abbreviations: the saturation numerator `A t` and the matched-path
  -- denominator `B t = (eP X + eP Y)·eᵗ`.
  set A := fun t : ℝ ↦ sumHeatFlowEP X Y Z_X Z_Y P (s t) (r t) with hA
  set B := fun t : ℝ ↦
    heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t) with hB
  -- (eP X + eP Y) is positive.
  have hXY_pos : (0 : ℝ) < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- §1 (genuine reduction): for `t ≥ 0`, `R t = log (A t) − log (B t)` and
  -- `B t = (eP X + eP Y)·eᵗ`.
  have hB_eq : ∀ t : ℝ, 0 ≤ t →
      B t = (entropyPower (P.map X) + entropyPower (P.map Y)) * Real.exp t := by
    intro t ht
    show heatFlowEP X Z_X P (s t) + heatFlowEP Y Z_Y P (r t) = _
    rw [h_path_X.matched_growth t ht, h_path_Y.matched_growth t ht,
      heatFlowEP_zero, heatFlowEP_zero]
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
      Filter.Tendsto (fun t : ℝ ↦ A t / B t) Filter.atTop (nhds (1 : ℝ)) := by
    rw [hA, hB]
    exact sumHeatFlowEP_div_heatFlowEP_sum_tendsto_one X Y Z_X Z_Y P h_path_X h_path_Y Z
      hX hY hZX hZY hZ hZX_law hZY_law hZ_law hXY_ZXZY_pair hXY_Z hZX_ZY
      hZX_ac hZY_ac hZ_ac hs_atTop hr_atTop hs_pos hr_pos h_scale_X h_scale_Y h_scale_sum
      varX varY varS h_varX_nn h_varY_nn h_varS_nn h_reg_X h_reg_Y h_reg_S hB_eq
  -- `B t > 0` for `t ≥ 0` (positive entropy powers times `eᵗ`).
  have hB_pos : ∀ t : ℝ, 0 ≤ t → 0 < B t := by
    intro t ht
    rw [hB_eq t ht]; positivity
  have hA_pos : ∀ t : ℝ, 0 < A t := fun t ↦ by rw [hA]; exact entropyPower_pos _
  -- `log (A/B) → log 1 = 0` by continuity of `log` at `1`.
  have h_logratio_tendsto :
      Filter.Tendsto (fun t : ℝ ↦ Real.log (A t / B t)) Filter.atTop (nhds (0 : ℝ)) := by
    have := (Real.continuousAt_log (one_ne_zero)).tendsto.comp h_ratio_tendsto
    simpa [Function.comp_def] using this
  -- `log (A/B) = log A − log B` (both positive, eventually for `t ≥ 0`).
  have h_eventually_eq : ∀ᶠ t in Filter.atTop,
      Real.log (A t / B t) = twoTimeLogRatioGap X Y Z_X Z_Y P s r t := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.log_div (hA_pos t).ne' (hB_pos t ht).ne', ← h_R_eq t ht]
  exact (Filter.tendsto_congr' h_eventually_eq).mp h_logratio_tendsto

end InformationTheory.Shannon.EPICase1TwoTime
