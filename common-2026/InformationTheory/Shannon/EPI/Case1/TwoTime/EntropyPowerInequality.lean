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
import InformationTheory.Shannon.EPI.Case1.TwoTime.MonotonicityAndSaturation

/-!
# EPI case-1 two-time object — entropy power inequality bridge (§4 terminal)

The entropy power inequality bridge for the two-time object:
`epi_of_twoTimeLogRatioGap_zero_nonneg` / `epi_of_twoTimeLogRatioGap_tendsto`
turn the gap's nonnegativity at `0` (delivered by antitonicity plus the
saturation limit) into `N(X + Y) ≥ N(X) + N(Y)`, and the terminal
`entropyPower_add_ge_case1_of_regular_twotime` assembles the matched-path
producer with the three genuine pillars. Verbatim split of `TwoTime.lean` §4
(EPI bridge / terminal part); proofs unchanged. Builds on
`TwoTime.GapDerivative` (gap object) and `TwoTime.MonotonicityAndSaturation`
(antitonicity / saturation). Umbrella: `TwoTime.lean`.
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

theorem heatFlowEP_hasDerivAt_of_regular
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {σ : ℝ} (hσ : 0 < σ)
    (h_reg : InformationTheory.Shannon.FisherInfo.IsRegularDeBruijnHypV2 X Z P σ) :
    HasDerivAt (fun u => heatFlowEP X Z P u)
      (heatFlowEP X Z P σ
        * InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal h_reg.density_t)
      σ := by
  set J := InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
    h_reg.density_t with hJ_def
  have h_dB : HasDerivAt
      (fun s => InformationTheory.Shannon.differentialEntropy
        (P.map (InformationTheory.Shannon.FisherInfo.gaussianConvolution X Z s)))
      ((1/2) * J) σ := by
    have := InformationTheory.Shannon.FisherInfo.deBruijn_identity_v2
      X Z hX hZ hXZ hσ h_reg
    simpa only [hJ_def] using this
  have h_eP := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB
  have h_val : heatFlowEP X Z P σ * J
      = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfo.gaussianConvolution X Z σ)))
        * (2 * ((1/2) * J)) := by
    unfold heatFlowEP entropyPower InformationTheory.Shannon.FisherInfo.gaussianConvolution
    ring
  rw [h_val]; exact h_eP

theorem heatFlowEP_tendsto_atTop
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZ : Measurable Z)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hZ_ac : (P.map Z) ≪ volume)
    (h_scale : ∀ σ : ℝ, 0 < σ →
      (P.map (fun ω => X ω / Real.sqrt σ + Z ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω / Real.sqrt σ + Z ω)).rnDeriv volume x).toReal)) volume)
    (var : ℝ) (h_var_nn : 0 ≤ var)
    (h_rescale : IsRescaledPathRegular X Z P var 1) :
    Filter.Tendsto (fun s => heatFlowEP X Z P s) Filter.atTop Filter.atTop := by
  have hν_pos : (0 : ℝ) < entropyPower (P.map Z) := entropyPower_pos _
  have hNr_lim := entropyPower_rescaled_path_tendsto X Z P hX hZ (1 : ℝ≥0) one_ne_zero
    hZ_law var h_var_nn hZ_ac h_rescale
  have h_eq : ∀ᶠ s in Filter.atTop,
      heatFlowEP X Z P s = s * entropyPower (P.map (fun ω => X ω / Real.sqrt s + Z ω)) := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with s hs
    have hsc := entropyPower_path_scaling X Z P hX hZ hs (h_scale s hs).1 (h_scale s hs).2
    simpa only [heatFlowEP] using hsc
  have h_prod : Filter.Tendsto
      (fun s : ℝ => s * entropyPower (P.map (fun ω => X ω / Real.sqrt s + Z ω)))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_pos hν_pos Filter.tendsto_id hNr_lim
  exact h_prod.congr' (h_eq.mono (fun s hs => hs.symm))

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
      0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_X.reg_at σ hσ).density_t) ∧
      0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_Y.reg_at τ hτ).density_t) ∧
      0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (σ + τ) (add_pos hσ hτ)).density_t) ∧
      1 / InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at (σ + τ) (add_pos hσ hτ)).density_t)
        ≥ 1 / InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_X.reg_at σ hσ).density_t)
          + 1 / InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_Y.reg_at τ hτ).density_t)) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- ===== Fisher pin: total-domain `J_X`/`J_Y` (probe-5a). =====
  set J_X : ℝ → ℝ := fun σ =>
    if hσ : 0 < σ then
      InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
        ((h_reg_X.reg_at σ hσ).density_t)
    else 0 with hJX_def
  set J_Y : ℝ → ℝ := fun τ =>
    if hτ : 0 < τ then
      InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
        ((h_reg_Y.reg_at τ hτ).density_t)
    else 0 with hJY_def
  have hJX_val : ∀ (σ : ℝ) (hσ : 0 < σ), J_X σ
      = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_X.reg_at σ hσ).density_t) := by
    intro σ hσ; rw [hJX_def]; simp only [dif_pos hσ]
  have hJY_val : ∀ (τ : ℝ) (hτ : 0 < τ), J_Y τ
      = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
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
    exact heatFlowEP_hasDerivAt_of_regular X Z_X P hX hZX hXZX hσ (h_reg_X.reg_at σ hσ)
  have hJ_deriv_Y : ∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun u => heatFlowEP Y Z_Y P u) (heatFlowEP Y Z_Y P τ * J_Y τ) τ := by
    intro τ hτ
    rw [hJY_val τ hτ]
    exact heatFlowEP_hasDerivAt_of_regular Y Z_Y P hY hZY hYZY hτ (h_reg_Y.reg_at τ hτ)
  -- ===== `hN_tendsto` assembly (heatFlowEP divergence, probe-5d). =====
  have hN_tendsto_X : Filter.Tendsto (fun s => heatFlowEP X Z_X P s) Filter.atTop Filter.atTop :=
    heatFlowEP_tendsto_atTop X Z_X P hX hZX hZX_law hZX_ac h_scale_X varX h_varX_nn h_rescale_X
  have hN_tendsto_Y : Filter.Tendsto (fun s => heatFlowEP Y Z_Y P s) Filter.atTop Filter.atTop :=
    heatFlowEP_tendsto_atTop Y Z_Y P hY hZY hZY_law hZY_ac h_scale_Y varY h_varY_nn h_rescale_Y
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
      J_X (s t) = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_X.reg_at (s t) hst).density_t) ∧
      J_Y (r t) = InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at (r t) hrt).density_t) ∧
      0 < J_X (s t) ∧ 0 < J_Y (r t) ∧
      0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at (s t + r t) (add_pos hst hrt)).density_t) ∧
      1 / InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
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
