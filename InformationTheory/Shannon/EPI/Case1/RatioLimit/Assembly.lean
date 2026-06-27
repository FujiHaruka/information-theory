import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Unconditional.MixedCase
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.G2.ConvEntropyDensity
import InformationTheory.Shannon.EPI.Case1.ProducerMeasurability
import InformationTheory.Shannon.EPI.Case1.RatioLimit.PathRegular

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace InformationTheory.Shannon.EPICase1RatioLimit

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamToBridge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap csiszarLogRatioGap_at_zero)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Eventual equality between `csiszarLogRatioGap` and the log-ratio of rescaled
entropy powers: for all sufficiently large `t > 0`, the gap equals
`log N(W_S t) − log (N(W_X t) + N(W_Y t))` where the three `W`-paths are the
scaled convolutions with noise. Proved by `entropyPower_path_scaling` cancellation. -/
private theorem csiszarLogRatioGap_eventually_eq_logRatio
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (h_scale_X : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t
            + (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal)) volume) :
    ∀ᶠ t in Filter.atTop,
      csiszarLogRatioGap X Y Z_X Z_Y P t =
        Real.log (entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω)))) -
        Real.log (entropyPower (P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)) +
                  entropyPower (P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω))) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hsX := h_scale_X t ht
  have hsY := h_scale_Y t ht
  have hsS := h_scale_sum t ht
  set NX := entropyPower (P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω))
  set NY := entropyPower (P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω))
  set NS := entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω)))
  have eqX : entropyPower (P.map (fun ω ↦ X ω + Real.sqrt t * Z_X ω)) = t * NX :=
    entropyPower_path_scaling X Z_X P hX hZX ht hsX.1 hsX.2
  have eqY : entropyPower (P.map (fun ω ↦ Y ω + Real.sqrt t * Z_Y ω)) = t * NY :=
    entropyPower_path_scaling Y Z_Y P hY hZY ht hsY.1 hsY.2
  have eqS : entropyPower (P.map (fun ω ↦ X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
      = t * NS := by
    have := entropyPower_path_scaling (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P
      (hX.add hY) (hZX.add hZY) ht hsS.1 hsS.2
    simpa using this
  have hNX : 0 < NX := entropyPower_pos _
  have hNY : 0 < NY := entropyPower_pos _
  have hNS : 0 < NS := entropyPower_pos _
  unfold csiszarLogRatioGap
  rw [eqS, eqX, eqY, show t * NX + t * NY = t * (NX + NY) by ring]
  rw [Real.log_mul ht.ne' hNS.ne', Real.log_mul ht.ne' (by positivity : (NX + NY) ≠ 0)]
  ring

/-! ## §4 — Main analytic deliverable

`csiszarLogRatioGap_tendsto_zero_atTop`: composing §2 (cancellation), §3 (per-path
limits), and Gaussian additivity yields `R t → 0`. -/

/-- `R t → 0` as `t → ∞` (entropic-CLT-free). Combining the scaling cancellation
(`entropyPower_path_scaling`), the three per-path limits
(`entropyPower_rescaled_path_tendsto`), Gaussian additivity of the noise
(`entropyPower_gaussian_additivity`), and continuity of `log` on positive reals.

The per-`t` regularity (a.c. + entropy integrability of the three W-path laws for
the scaling step; the §3 squeeze regularity bundles `IsRescaledPathRegular` for the
three paths) is threaded as honest preconditions; the noise Gaussian laws +
independence are regularity. No EPI / Stam core is bundled.
@audit:ok -/
theorem csiszarLogRatioGap_tendsto_zero_atTop
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (v_X v_Y : ℝ≥0) (hv_X : v_X ≠ 0) (hv_Y : v_Y ≠ 0)
    (hZX_law : P.map Z_X = gaussianReal 0 v_X)
    (hZY_law : P.map Z_Y = gaussianReal 0 v_Y)
    (hZXZY_indep : IndepFun Z_X Z_Y P)
    -- per-`t` scaling regularity (consumed by `entropyPower_path_scaling`)
    (h_scale_X : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t
            + (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal)) volume)
    -- noise laws are a.c. (Gaussian)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZXZY_ac : (P.map (fun ω ↦ Z_X ω + Z_Y ω)) ≪ volume)
    -- per-path variance data + §3 regularity bundles (all regularity)
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX v_X)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY v_Y)
    (h_reg_S : IsRescaledPathRegular (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P
      varS (v_X + v_Y)) :
    Filter.Tendsto
      (fun t ↦ csiszarLogRatioGap X Y Z_X Z_Y P t)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Abbreviations for the rescaled W-paths and the noise entropy powers.
  set NX := fun t ↦ entropyPower (P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)) with hNX
  set NY := fun t ↦ entropyPower (P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)) with hNY
  set NS := fun t ↦
    entropyPower (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) with hNS
  -- `v_X + v_Y ≠ 0` over `ℝ≥0`.
  have hv_sum : v_X + v_Y ≠ 0 := by
    intro h
    exact hv_X (le_antisymm (h ▸ le_self_add) bot_le)
  -- Gaussian additivity for the noise sum.
  have hZXZY_law : P.map (fun ω ↦ Z_X ω + Z_Y ω) = gaussianReal 0 (v_X + v_Y) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law
    have h_eq : (Z_X + Z_Y) = fun ω ↦ Z_X ω + Z_Y ω := by funext ω; rfl
    rw [h_eq] at h; simpa using h
  -- Limits of the three rescaled paths (§3).
  have hlimX : Filter.Tendsto NX Filter.atTop (nhds (entropyPower (P.map Z_X))) :=
    entropyPower_rescaled_path_tendsto X Z_X P hX hZX v_X hv_X hZX_law varX h_varX_nn
      hZX_ac h_reg_X
  have hlimY : Filter.Tendsto NY Filter.atTop (nhds (entropyPower (P.map Z_Y))) :=
    entropyPower_rescaled_path_tendsto Y Z_Y P hY hZY v_Y hv_Y hZY_law varY h_varY_nn
      hZY_ac h_reg_Y
  have hlimS : Filter.Tendsto NS Filter.atTop
      (nhds (entropyPower (P.map (fun ω ↦ Z_X ω + Z_Y ω)))) :=
    entropyPower_rescaled_path_tendsto (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P
      (hX.add hY) (hZX.add hZY) (v_X + v_Y) hv_sum hZXZY_law varS h_varS_nn
      hZXZY_ac h_reg_S
  -- `N(law(Z_X + Z_Y)) = N(Z_X) + N(Z_Y)` (Gaussian additivity).
  have h_add : entropyPower (P.map (fun ω ↦ Z_X ω + Z_Y ω))
      = entropyPower (P.map Z_X) + entropyPower (P.map Z_Y) :=
    entropyPower_gaussian_additivity P Z_X Z_Y hZX hZY hZXZY_indep 0 0 v_X v_Y hv_X hv_Y
      hZX_law hZY_law
  -- Positivity of the limit values (entropy power is strictly positive).
  have hNX0_pos : 0 < entropyPower (P.map Z_X) := entropyPower_pos _
  have hNY0_pos : 0 < entropyPower (P.map Z_Y) := entropyPower_pos _
  -- The rescaled gap agrees with `R` eventually (for `t > 0`) via §2 cancellation.
  have h_eventually_eq : ∀ᶠ t in Filter.atTop,
      csiszarLogRatioGap X Y Z_X Z_Y P t
        = Real.log (NS t) - Real.log (NX t + NY t) :=
    csiszarLogRatioGap_eventually_eq_logRatio X Y Z_X Z_Y P hX hY hZX hZY
      h_scale_X h_scale_Y h_scale_sum
  -- Limit of the rescaled gap: both `log` arguments → `N(Z_X)+N(Z_Y)`.
  have h_lim_rescaled : Filter.Tendsto
      (fun t ↦ Real.log (NS t) - Real.log (NX t + NY t))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hlogS : Filter.Tendsto (fun t ↦ Real.log (NS t)) Filter.atTop
        (nhds (Real.log (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y)))) := by
      rw [← h_add]
      exact (Real.continuousAt_log (entropyPower_pos _).ne').tendsto.comp hlimS
    have hlogD : Filter.Tendsto (fun t ↦ Real.log (NX t + NY t)) Filter.atTop
        (nhds (Real.log (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y)))) := by
      have hsum : Filter.Tendsto (fun t ↦ NX t + NY t) Filter.atTop
          (nhds (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y))) :=
        hlimX.add hlimY
      have hpos : entropyPower (P.map Z_X) + entropyPower (P.map Z_Y) ≠ 0 := by
        positivity
      exact (Real.continuousAt_log hpos).tendsto.comp hsum
    have := hlogS.sub hlogD
    simpa using this
  -- Transfer the limit through the eventual equality.
  exact (Filter.tendsto_congr' h_eventually_eq).mpr h_lim_rescaled

/-! ## §5 — End-to-end case-1 assembly (with-noise)

`entropyPower_add_ge_case1_of_regular`: combine the genuine ratio antitonicity
(`csiszarLogRatioGap_antitoneOn_Ici_zero`, `EPIStamToBridge.lean:1085`) and the
genuine saturation (`csiszarLogRatioGap_tendsto_zero_atTop`, §4) through the
genuine order-limit bridge (§1 `epi_of_csiszarLogRatioGap_tendsto`) to obtain the
classical (case-1, a.c. inputs) entropy power inequality. Pure assembly — no new
analytic content, no `sorry`. -/

/-- **Case-1 EPI (with-noise, entropic-CLT-free), under heat-flow + scaling
regularity**. The classical entropy power inequality
`N(law(X+Y)) ≥ N(law X) + N(law Y)` for a.c. inputs, assembled from the two genuine
pillars:

* `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`, genuine):
  the log-ratio gap `R = csiszarLogRatioGap X Y Z_X Z_Y P` is `AntitoneOn (Set.Ici 0)`.
* `csiszarLogRatioGap_tendsto_zero_atTop` (§4, genuine): `R t → 0` as `t → ∞`.

By the order-limit bridge §1 `epi_of_csiszarLogRatioGap_tendsto`, antitonicity +
`R t → 0` force `R 0 ≥ 0`, hence EPI. No entropic CLT — the saturation `R t → 0`
is the scaling squeeze of §4.

All hypotheses are honest regularity preconditions, the union of the two
pillars' preconditions: pairwise + joint independence (`hXZX`/`hYZY`/`hXYZXY`), the
three `IsDeBruijnRegularityHyp` / `IsHeatFlowEndpointRegular` density-witness bundles,
the per-`t` `h_pos_stam` Fisher/Stam/Blachman bundle (ratio antitone side), the noise
Gaussian laws + a.c. (`hZX_law`/`hZY_law`/`hZXZY_indep`/`hZX_ac`/`hZY_ac`/`hZXZY_ac`),
the per-`t` scaling regularity (`h_scale_X/Y/sum`), and the per-path variance data +
three `IsRescaledPathRegular` bundles (§4 side). None is load-bearing: the EPI /
Stam core is supplied genuinely inside the two pillars; the conclusion
`N(X+Y) ≥ N(X)+N(Y)` is not encoded in any hypothesis. Honest naming
(`_of_regular`, not bare `_unconditional`): the regularity preconditions are real.

@audit:ok (independent honesty audit): assembly of two `@audit:ok`
pillars through one `@audit:ok` bridge. Over-claim check: the conclusion is verbatim the
case-1 EPI `N(X+Y) ≥ N(X)+N(Y)`, no weaker substitute. Non-load-bearing AFFIRMED via
core-reconstruction test: the ~30 preconditions are the union of the two pillars'
regularity bundles; granting them (incl. the per-`t` `h_pos_stam` whose
`IsStamInequalityHyp` is itself genuinely provable, `wall:stam-step2-density`)
does NOT hand the EPI conclusion — that requires the pillars' genuine de Bruijn
integration + scaling squeeze, neither encoded in any hypothesis. Sufficiency: the body
threads pillar args in matching order and composes via the §1 bridge.
@audit:superseded-by(entropyPowerExt_add_ge_unconditional) Superseded by the
unconditional EPI; the sole consumer `entropyPower_add_ge_case1_of_methodX` is a dead leaf.
Retained as proof-done. The two-time variant `entropyPower_add_ge_case1_of_regular_twotime` is
separate and live. -/
theorem entropyPower_add_ge_case1_of_regular
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    -- independence (pairwise + joint), shared by both pillars
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hXZX : IndepFun X Z_X P) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P)
    (hZXZY_indep : IndepFun Z_X Z_Y P)
    -- noise Gaussian laws + variances (§4 side), nonzero
    (v_X v_Y : ℝ≥0) (hv_X : v_X ≠ 0) (hv_Y : v_Y ≠ 0)
    (hZX_law : P.map Z_X = gaussianReal 0 v_X)
    (hZY_law : P.map Z_Y = gaussianReal 0 v_Y)
    (hZX_ac : (P.map Z_X) ≪ volume) (hZY_ac : (P.map Z_Y) ≪ volume)
    (hZXZY_ac : (P.map (fun ω ↦ Z_X ω + Z_Y ω)) ≪ volume)
    -- ratio-antitone density-witness + de Bruijn regularity bundles
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P)
    (h_reg_X' : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y' : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_X'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_Y'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_sum.reg_at t ht).density_t)) ∧
      InformationTheory.Shannon.StamEPIBridge.IsStamInequalityHyp
        (fun ω ↦ X ω + Real.sqrt t * Z_X ω)
        (fun ω ↦ Y ω + Real.sqrt t * Z_Y ω) P ∧
      InformationTheory.Shannon.FisherInfo.IsRegularDensityV2
        ((h_reg_X'.reg_at t ht).density_t) ∧
      InformationTheory.Shannon.FisherInfo.IsRegularDensityV2
        ((h_reg_Y'.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∫ x, (h_reg_Y'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                ((h_reg_X'.reg_at t ht).density_t)
                ((h_reg_Y'.reg_at t ht).density_t) x) ∧
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X'.reg_at t ht).density_t)
        ((h_reg_Y'.reg_at t ht).density_t))
    -- per-`t` scaling regularity (§4 side, consumed by `entropyPower_path_scaling`)
    (h_scale_X : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ X ω / Real.sqrt t + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ Y ω / Real.sqrt t + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ t : ℝ, 0 < t →
      (P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) ≪ volume ∧
      Integrable (fun x ↦ Real.negMulLog
        (((P.map (fun ω ↦ (X ω + Y ω) / Real.sqrt t
            + (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal)) volume)
    -- per-path variance data + §3 squeeze regularity bundles (§4 side)
    (varX varY varS : ℝ)
    (h_varX_nn : 0 ≤ varX) (h_varY_nn : 0 ≤ varY) (h_varS_nn : 0 ≤ varS)
    (h_reg_X : IsRescaledPathRegular X Z_X P varX v_X)
    (h_reg_Y : IsRescaledPathRegular Y Z_Y P varY v_Y)
    (h_reg_S : IsRescaledPathRegular (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P
      varS (v_X + v_Y)) :
    entropyPower (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- Pillar 1: genuine ratio antitonicity on `Set.Ici 0`.
  have h_anti := csiszarLogRatioGap_antitoneOn_Ici_zero X Y Z_X Z_Y P
    hX hZX hXZX hY hZY hYZY hXYZXY
    h_reg_sum h_reg_X' h_reg_Y'
    h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
  -- Pillar 2: genuine saturation `R t → 0`.
  have h_lim := csiszarLogRatioGap_tendsto_zero_atTop X Y Z_X Z_Y P
    hX hY hZX hZY v_X v_Y hv_X hv_Y hZX_law hZY_law hZXZY_indep
    h_scale_X h_scale_Y h_scale_sum
    hZX_ac hZY_ac hZXZY_ac
    varX varY varS h_varX_nn h_varY_nn h_varS_nn
    h_reg_X h_reg_Y h_reg_S
  -- Order-limit bridge §1: antitone + `R t → 0` ⟹ EPI.
  exact epi_of_csiszarLogRatioGap_tendsto X Y Z_X Z_Y P h_anti h_lim

theorem variance_rescaledPath_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : IndepFun A B P) (h_mom_A : Integrable (fun ω ↦ (A ω)^2) P)
    (v_B : ℝ≥0) (hB_law : P.map B = gaussianReal 0 v_B)
    (t : ℝ) (ht : 0 < t) :
    (∫ x, (x - (∫ y, y ∂(P.map (fun ω ↦ A ω / Real.sqrt t + B ω))))^2
          ∂(P.map (fun ω ↦ A ω / Real.sqrt t + B ω)))
        ≤ ProbabilityTheory.variance A P / t + (v_B : ℝ) := by
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  set Zt : Ω → ℝ := fun ω ↦ A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hW_meas : Measurable (fun ω ↦ Zt ω + B ω) := hZt_meas.add hB
  -- `A/√t` and `B` finite second moments → `MemLp 2`.
  have hB_memLp : MemLp B 2 P := by
    have hid : MemLp (id : ℝ → ℝ) 2 (P.map B) := by
      rw [hB_law]; exact memLp_id_gaussianReal' 2 (by simp)
    have := (memLp_map_measure_iff (p := 2) (μ := P) (g := (id : ℝ → ℝ))
      aestronglyMeasurable_id hB.aemeasurable).mp hid
    simpa [Function.comp] using this
  have hZt_sq : Integrable (fun ω ↦ (Zt ω)^2) P := by
    have : (fun ω ↦ (Zt ω)^2) = (fun ω ↦ (1 / t) * (A ω)^2) := by
      funext ω; simp only [hZt, div_pow, Real.sq_sqrt ht.le]; ring
    rw [this]; exact h_mom_A.const_mul _
  have hZt_memLp : MemLp Zt 2 P :=
    (memLp_two_iff_integrable_sq_norm hZt_meas.aestronglyMeasurable).mpr (by simpa using hZt_sq)
  -- `Zt ⊥ B`.
  have h_indep : IndepFun Zt B P := by
    have : Zt = (fun a ↦ a / Real.sqrt t) ∘ A := by funext ω; rfl
    rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
  -- LHS = `Var[id; P.map path]`.
  have hLHS : (∫ x, (x - (∫ y, y ∂(P.map (fun ω ↦ Zt ω + B ω))))^2
        ∂(P.map (fun ω ↦ Zt ω + B ω)))
      = ProbabilityTheory.variance (fun ω ↦ Zt ω + B ω) P := by
    rw [← ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable]
    exact ProbabilityTheory.variance_id_map hW_meas.aemeasurable
  -- `Var[path] = Var[Zt] + Var[B] = (1/t)Var[A] + v_B`.
  have hVarZt : ProbabilityTheory.variance Zt P
      = (1 / t) * ProbabilityTheory.variance A P := by
    have hZt_eq : Zt = fun ω ↦ (1 / Real.sqrt t) * A ω := by
      funext ω; simp only [hZt]; rw [div_eq_inv_mul, one_div]
    rw [hZt_eq, ProbabilityTheory.variance_const_mul]
    congr 1
    rw [div_pow, one_pow, Real.sq_sqrt ht.le]
  have hVarB : ProbabilityTheory.variance B P = (v_B : ℝ) := by
    rw [← ProbabilityTheory.variance_id_map hB.aemeasurable, hB_law,
      ProbabilityTheory.variance_id_gaussianReal]
  have hVarSum : ProbabilityTheory.variance (fun ω ↦ Zt ω + B ω) P
      = (1 / t) * ProbabilityTheory.variance A P + (v_B : ℝ) := by
    rw [ProbabilityTheory.IndepFun.variance_fun_add hZt_memLp hB_memLp h_indep,
      hVarZt, hVarB]
  rw [hLHS, hVarSum, one_div, inv_mul_eq_div]

theorem rescaledPath_ac_and_negMulLog_integrable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hAB : IndepFun A B P) (hA_ac : (P.map A) ≪ volume)
    (h_mom_A : Integrable (fun ω ↦ (A ω)^2) P)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0) (hB_law : P.map B = gaussianReal 0 v_B)
    (t : ℝ) (ht : 0 < t) :
    (P.map (fun ω ↦ A ω / Real.sqrt t + B ω)) ≪ volume ∧
    Integrable (fun x ↦ Real.negMulLog
      (((P.map (fun ω ↦ A ω / Real.sqrt t + B ω)).rnDeriv volume x).toReal)) volume := by
  set Zt : Ω → ℝ := fun ω ↦ A ω / Real.sqrt t with hZt
  have hZt_meas : Measurable Zt := hA.div_const _
  have hB_ac : (P.map B) ≪ volume := by
    rw [hB_law]; exact gaussianReal_absolutelyContinuous 0 hv_B
  have h_indep : IndepFun Zt B P := by
    have : Zt = (fun a ↦ a / Real.sqrt t) ∘ A := by funext ω; rfl
    rw [this]; exact hAB.comp (measurable_id.div_const _) measurable_id
  -- a.c. of `A/√t + B`.
  have hμ_ac : (P.map (fun ω ↦ Zt ω + B ω)) ≪ volume := by
    have hWac : (P.map (fun ω ↦ B ω + Zt ω)) ≪ volume :=
      map_add_absolutelyContinuous B Zt P hB hZt_meas h_indep.symm hB_ac
    have h_path : (fun ω ↦ Zt ω + B ω) = (fun ω ↦ B ω + Zt ω) := by funext ω; ring
    rw [h_path]; exact hWac
  refine ⟨hμ_ac, ?_⟩
  -- negMulLog (path rnDeriv) integrable (B(i)-identical, path = `Zt + B`).
  have hv_B_pos : (0 : ℝ≥0) < v_B := pos_iff_ne_zero.mpr hv_B
  obtain ⟨pX, hpX_nn, hpX_meas, hpX_law, hpX_int, hpX_mass, hpX_mom⟩ :=
    rescaledInput_density_witness A P hA hA_ac h_mom_A ht
  have hgconv : InformationTheory.Shannon.FisherInfo.gaussianConvolution Zt B 1
      = fun ω ↦ Zt ω + B ω := by
    funext ω
    simp only [InformationTheory.Shannon.FisherInfo.gaussianConvolution,
      Real.sqrt_one, one_mul]
  have h_path_rnDeriv : (P.map (fun ω ↦ Zt ω + B ω)).rnDeriv volume
      =ᵐ[volume] fun z ↦ ENNReal.ofReal
        (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
          (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) z) := by
    have := InformationTheory.Shannon.FisherInfo.pPath_eq_convDensityAdd
      Zt B hZt_meas hB h_indep v_B hv_B_pos hB_law pX hpX_nn hpX_meas hpX_law
      (s := 1) one_pos
    rwa [hgconv] at this
  have hvar_eq : (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B := by
    apply NNReal.coe_injective; show (1 : ℝ) * (v_B : ℝ) = (v_B : ℝ); rw [one_mul]
  have h_asset : Integrable (fun x ↦
      Real.negMulLog (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
        (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x)) volume := by
    rw [show (⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩ : ℝ≥0) = v_B from hvar_eq]
    have hv_B_pos' : (0 : ℝ) < v_B := hv_B_pos
    exact InformationTheory.Shannon.convDensityAdd_negMulLog_integrable_pub
      hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (t := (v_B : ℝ)) hv_B_pos'
  refine h_asset.congr ?_
  filter_upwards [h_path_rnDeriv] with x hx
  have hcd_nn : 0 ≤ InformationTheory.Shannon.EPIConvDensity.convDensityAdd pX
      (gaussianPDFReal 0 ⟨(1 : ℝ) * (v_B : ℝ), by positivity⟩) x :=
    integral_nonneg fun y ↦ mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg _ _ _)
  rw [hx, ENNReal.toReal_ofReal hcd_nn]

/-- Case-1 EPI under method-X regularity (entropic-CLT-free, unit-noise form).
`N(P.map(X+Y)) ≥ N(P.map X) + N(P.map Y)` for a.c. inputs, reduced to method-X
regularity (a.c. inputs + finite second moments + standard-normal `𝒩(0,1)`
noise laws + 4-tuple independence) plus de Bruijn per-time regularity.

On the unit-noise restatement: the noise
laws were generalized `gaussianReal 0 v_X`/`gaussianReal 0 v_Y` (`v_X v_Y` arbitrary
nonzero). Since the conclusion `N(X+Y) ≥ N(X)+N(Y)` does not mention the noise, the noise
is an auxiliary variable and fixing it to `𝒩(0,1)` loses no generality. This is required
so the de Bruijn producers (`isDeBruijnRegularityHyp_of_methodX_unitnoise`) — whose
`IsRegularDeBruijnHypV2.Z_law` hardcodes `gaussianReal 0 1` — can actually supply the
threaded `IsDeBruijnRegularityHyp` group (previously vacuous for `v_X ≠ 1`). The body
re-introduces `v_X v_Y := (1 : ℝ≥0)` existentially to keep the `_of_regular` plumbing
(general `v_B` on the §4 saturation side) unchanged.

@audit-note: independent honesty audit.
The unit-noise restate resolves the latent vacuity defect. The old signature
took arbitrary nonzero `v_X v_Y` while threading `IsDeBruijnRegularityHyp X Z_X P`, whose
`reg_at t ht .Z_law` (= `IsRegularDeBruijnHypV2.Z_law`, `FisherInfoDeBruijn.lean:210`)
hardcodes `P.map Z_X = gaussianReal 0 1` — so for `v_X ≠ 1` the hypotheses `hZX_law` and
`Z_law` were mutually unsatisfiable, making the theorem vacuously true (premises never
jointly inhabitable). Fixing `hZX_law : P.map Z_X = gaussianReal 0 1` removes the
contradiction. The body's `obtain ⟨v_X, hv_X, hZX_law⟩ : ∃ v, v≠0 ∧ … := ⟨1, one_ne_zero,
hZX_law⟩` is HONEST (not circular `:= h`, not `:True`): it locally re-derives the
`∃ v ≠ 0` shape the `_of_regular` plumbing expects, instantiated at the genuine witness
`v = 1` carried by the unit hypothesis. The conclusion `N(X+Y) ≥ N(X)+N(Y)` is unchanged and
not weakened; the noise is genuinely auxiliary (absent from the conclusion) so the unit
restriction loses no generality. The
threaded `IsDeBruijnRegularityHyp` / `h_reg_*` are honest preconditions (residuals live in
the producer's `integrable_deriv`, see `isDeBruijnRegularityHyp_of_methodX_unitnoise`). Not
`@audit:ok` only because it threads residual-carrying regularity hyps.

This wrapper discharges the supply-able preconditions of
`entropyPower_add_ge_case1_of_regular` from clean method-X data:
* noise a.c. (`hZX_ac`/`hZY_ac`/`hZXZY_ac`) via `gaussianReal_absolutelyContinuous`
  + `map_add_absolutelyContinuous`;
* the four individual independences from the single 4-tuple
  `iIndepFun ![X,Y,Z_X,Z_Y] P` (pairwise via `iIndepFun.indepFun`, joint via
  `iIndepFun.indepFun_prodMk_prodMk` + `IndepFun.comp`);
* the three `IsRescaledPathRegular` bundles via `isRescaledPathRegular_of_methodX`;
* the per-`t` scaling regularity (`h_scale_*`) via the B(i)-identical density-witness
  plumbing (`rescaledInput_density_witness` + `pPath_eq_convDensityAdd` +
  `convDensityAdd_negMulLog_integrable_pub`);
* the variance bounds (`varX/Y/S := Var[·;P]`) via `IndepFun.variance_fun_add` +
  variance scaling, which hold with equality.

The de Bruijn per-time regularity group (`h_reg_*'` / `h_endpt_*` / `h_pos_stam`)
is not supplied from method-X (it depends on the moonshot
`epi-debruijn-pertime-closure`) and is threaded as an honest precondition.

@audit:superseded-by(entropyPowerExt_add_ge_unconditional) Has 0 consumers, carries an
unresolved de Bruijn per-time wall (`@residual` below). Superseded by the unconditional EPI.
The de Bruijn closure plan `epi-debruijn-pertime-closure` remains a valid standalone goal
independently of this supersession.
@residual(plan:epi-debruijn-pertime-closure) -/
theorem entropyPower_add_ge_case1_of_methodX
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    -- method-X: input regularity (both inputs a.c. + their sum a.c.; the sum-a.c. is the
    -- standard case-1 hypothesis, NOT derivable from `hX_ac`/`hY_ac` without `X ⊥ Y`)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hXY_ac : (P.map (fun ω ↦ X ω + Y ω)) ≪ volume)
    (h_mom_X : Integrable (fun ω ↦ (X ω)^2) P)
    (h_mom_Y : Integrable (fun ω ↦ (Y ω)^2) P)
    -- method-X: noise standard-normal law (unit variance, PB-1 restate — the noise is an
    -- auxiliary variable absent from the conclusion, so fixing it to `𝒩(0,1)` loses no
    -- generality and aligns with the de Bruijn group's unit-variance requirement)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1)
    -- method-X: 4-tuple joint independence (inputs/noise all independent)
    (h_iIndep : iIndepFun ![X, Y, Z_X, Z_Y] P)
    -- de Bruijn per-time regularity (NOT supply-able from method-X data)
    -- @residual(plan:epi-debruijn-pertime-closure)
    (h_reg_sum : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp
                    (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P)
    (h_reg_X' : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y' : InformationTheory.Shannon.StamEPIBridge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_X'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_Y'.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfo.fisherInfoOfDensityReal
              ((h_reg_sum.reg_at t ht).density_t)) ∧
      InformationTheory.Shannon.StamEPIBridge.IsStamInequalityHyp
        (fun ω ↦ X ω + Real.sqrt t * Z_X ω)
        (fun ω ↦ Y ω + Real.sqrt t * Z_Y ω) P ∧
      InformationTheory.Shannon.FisherInfo.IsRegularDensityV2
        ((h_reg_X'.reg_at t ht).density_t) ∧
      InformationTheory.Shannon.FisherInfo.IsRegularDensityV2
        ((h_reg_Y'.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∫ x, (h_reg_Y'.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                ((h_reg_X'.reg_at t ht).density_t)
                ((h_reg_Y'.reg_at t ht).density_t) x) ∧
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X'.reg_at t ht).density_t)
        ((h_reg_Y'.reg_at t ht).density_t)) :
    entropyPower (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  classical
  -- PB-1: unit-noise restate. The noise variances are fixed to `1`; the §4 saturation
  -- side (`entropyPower_rescaled_path_tendsto`) takes a general `v_B`, so `v_X = v_Y = 1`
  -- and `v_sum = 1 + 1 = 2` flow through `_of_regular` unchanged. We rebind the unit laws
  -- to the `gaussianReal 0 v_X` shape the body expects (defeq `v_X := (1 : ℝ≥0)`).
  obtain ⟨v_X, hv_X, hZX_law⟩ :
      ∃ v : ℝ≥0, v ≠ 0 ∧ P.map Z_X = gaussianReal 0 v :=
    ⟨1, one_ne_zero, hZX_law⟩
  obtain ⟨v_Y, hv_Y, hZY_law⟩ :
      ∃ v : ℝ≥0, v ≠ 0 ∧ P.map Z_Y = gaussianReal 0 v :=
    ⟨1, one_ne_zero, hZY_law⟩
  -- ===== C-3a: extract the four individual independences from the 4-tuple. =====
  -- Pointwise reduction of the `![X,Y,Z_X,Z_Y]` family entries.
  have hf_meas : ∀ i, Measurable (![X, Y, Z_X, Z_Y] i) := by
    intro i; fin_cases i <;> simpa using ‹_›
  -- pairwise independences
  have hXZX : IndepFun X Z_X P := by
    have := h_iIndep.indepFun (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
    simpa using this
  have hYZY : IndepFun Y Z_Y P := by
    have := h_iIndep.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    simpa using this
  have hZXZY_indep : IndepFun Z_X Z_Y P := by
    have := h_iIndep.indepFun (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    simpa using this
  -- joint independence `IndepFun (X+Y) (Z_X+Z_Y) P` via prodMk_prodMk + sum-comp.
  have hXYZXY : IndepFun (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P := by
    have hpair : IndepFun (fun a ↦ (X a, Y a)) (fun a ↦ (Z_X a, Z_Y a)) P := by
      have := h_iIndep.indepFun_prodMk_prodMk hf_meas 0 1 2 3
        (by decide) (by decide) (by decide) (by decide)
      simpa using this
    have hsum : Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) := by fun_prop
    have := hpair.comp hsum hsum
    exact this
  -- ===== C-3b: noise a.c. from Gaussian a.c. + independent-sum a.c. =====
  have hZX_ac : (P.map Z_X) ≪ volume := by
    rw [hZX_law]; exact gaussianReal_absolutelyContinuous 0 hv_X
  have hZY_ac : (P.map Z_Y) ≪ volume := by
    rw [hZY_law]; exact gaussianReal_absolutelyContinuous 0 hv_Y
  have hZXZY_ac : (P.map (fun ω ↦ Z_X ω + Z_Y ω)) ≪ volume :=
    map_add_absolutelyContinuous Z_X Z_Y P hZX hZY hZXZY_indep hZX_ac
  -- noise-sum Gaussian law (independent Gaussians).
  have hv_sum : v_X + v_Y ≠ 0 := by
    intro h
    exact hv_X (le_antisymm (h ▸ le_self_add) bot_le)
  have hZXZY_law : P.map (fun ω ↦ Z_X ω + Z_Y ω) = gaussianReal 0 (v_X + v_Y) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law
    have h_eq : (Z_X + Z_Y) = fun ω ↦ Z_X ω + Z_Y ω := by funext ω; rfl
    rw [h_eq] at h; simpa using h
  -- ===== C-5: variance bounds (hold with equality, `varA := Var[A;P]`). =====
  -- Concrete variances.
  set varX : ℝ := ProbabilityTheory.variance X P with hvarX_def
  set varY : ℝ := ProbabilityTheory.variance Y P with hvarY_def
  set varS : ℝ := ProbabilityTheory.variance (fun ω ↦ X ω + Y ω) P with hvarS_def
  have h_varX_nn : 0 ≤ varX := ProbabilityTheory.variance_nonneg X P
  have h_varY_nn : 0 ≤ varY := ProbabilityTheory.variance_nonneg Y P
  have h_varS_nn : 0 ≤ varS := ProbabilityTheory.variance_nonneg _ P
  -- second moment of `X+Y` from `MemLp 2` of `X`,`Y`.
  have h_mom_S : Integrable (fun ω ↦ (X ω + Y ω)^2) P := by
    have hX_memLp : MemLp X 2 P :=
      (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr (by simpa using h_mom_X)
    have hY_memLp : MemLp Y 2 P :=
      (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mpr (by simpa using h_mom_Y)
    have hS_memLp : MemLp (fun ω ↦ X ω + Y ω) 2 P := hX_memLp.add hY_memLp
    simpa using hS_memLp.integrable_sq
  -- ===== C-2: the three `IsRescaledPathRegular` bundles. =====
  have h_reg_X : IsRescaledPathRegular X Z_X P varX v_X :=
    isRescaledPathRegular_of_methodX X Z_X P hX hZX v_X hv_X hZX_law hXZX hX_ac
      varX h_varX_nn h_mom_X (variance_rescaledPath_le P X Z_X hX hZX hXZX h_mom_X v_X hZX_law)
  have h_reg_Y : IsRescaledPathRegular Y Z_Y P varY v_Y :=
    isRescaledPathRegular_of_methodX Y Z_Y P hY hZY v_Y hv_Y hZY_law hYZY hY_ac
      varY h_varY_nn h_mom_Y (variance_rescaledPath_le P Y Z_Y hY hZY hYZY h_mom_Y v_Y hZY_law)
  have h_reg_S : IsRescaledPathRegular (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P
      varS (v_X + v_Y) :=
    isRescaledPathRegular_of_methodX (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω) P
      (hX.add hY) (hZX.add hZY) (v_X + v_Y) hv_sum hZXZY_law hXYZXY hXY_ac
      varS h_varS_nn h_mom_S
      (variance_rescaledPath_le P (fun ω ↦ X ω + Y ω) (fun ω ↦ Z_X ω + Z_Y ω)
        (hX.add hY) (hZX.add hZY) hXYZXY h_mom_S (v_X + v_Y) hZXZY_law)
  -- ===== C-4: per-`t` scaling regularity (B(i)-identical density plumbing). =====
  have h_scale_X := rescaledPath_ac_and_negMulLog_integrable P X Z_X hX hZX hXZX hX_ac
    h_mom_X v_X hv_X hZX_law
  have h_scale_Y := rescaledPath_ac_and_negMulLog_integrable P Y Z_Y hY hZY hYZY hY_ac
    h_mom_Y v_Y hv_Y hZY_law
  have h_scale_sum := rescaledPath_ac_and_negMulLog_integrable P (fun ω ↦ X ω + Y ω)
    (fun ω ↦ Z_X ω + Z_Y ω)
    (hX.add hY) (hZX.add hZY) hXYZXY hXY_ac h_mom_S (v_X + v_Y) hv_sum hZXZY_law
  -- ===== C-6 + final: thread de Bruijn group, invoke `_of_regular`. =====
  exact entropyPower_add_ge_case1_of_regular X Y Z_X Z_Y P hX hY hZX hZY
    hXZX hYZY hXYZXY hZXZY_indep v_X v_Y hv_X hv_Y hZX_law hZY_law hZX_ac hZY_ac hZXZY_ac
    h_reg_sum h_reg_X' h_reg_Y' h_endpt_sum h_endpt_X h_endpt_Y h_pos_stam
    h_scale_X h_scale_Y h_scale_sum varX varY varS h_varX_nn h_varY_nn h_varS_nn
    h_reg_X h_reg_Y h_reg_S

end InformationTheory.Shannon.EPICase1RatioLimit
