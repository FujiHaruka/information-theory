import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIL3Integration
import InformationTheory.Shannon.EPIPlumbing
import InformationTheory.Shannon.EPIStamToBridge
import InformationTheory.Shannon.EPIUncondMixedCase
import InformationTheory.Shannon.DifferentialEntropy

/-!
# EPI case-1 via ratio + scaling squeeze (entropic-CLT-free)

This file lands the **monotone + limit** architecture for the classical (case-1,
a.c. inputs) entropy power inequality, **bypassing the entropic CLT wall**.

## Architecture (advisor-verified, `epi-case1-difference-g3-closure-plan.md` 判断ログ 7/8)

Let `R(t) = csiszarLogRatioGap X Y Z_X Z_Y P t
          = log N(law(X+Y+√t·(Z_X+Z_Y))) − log (N(law(X+√t·Z_X)) + N(law(Y+√t·Z_Y)))`,
the genuine log-ratio gap (`EPIL3Integration.csiszarLogRatioGap`).

* `csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085`, genuine,
  sorryAx-free) gives `AntitoneOn R (Set.Ici 0)`.
* `epi_of_csiszarLogRatioGap_zero_nonneg` (`EPIStamToBridge.lean:985`, genuine)
  gives `0 ≤ R 0 ⟹ EPI`.

So if `R t → 0` as `t → ∞`, then by antitonicity `R 0 ≥ lim_{t→∞} R t = 0`, hence
EPI. **No entropic CLT** is needed: `R t → 0` follows from a *scaling squeeze*.

### Scaling cancellation

`X + √t·Z_X = √t·(X/√t + Z_X)`, so by `entropyPower_map_mul_const`
(`EPIPlumbing.lean:136`, `N(μ.map(·*c)) = c²·N(μ)`, `c = √t`):
`N(law(X+√t·Z_X)) = t · N(law(X/√t + Z_X))`. Applying this to all three paths, the
`t` factor cancels inside the `log`s (`Real.log_mul`, `t > 0`, `N > 0`):
`R t = log N(W_sum t) − log (N(W_X t) + N(W_Y t))`,
`W_X t = X/√t + Z_X`, `W_Y t = Y/√t + Z_Y`, `W_sum t = (X+Y)/√t + (Z_X+Z_Y)`.

### Squeeze

Each `N(W_X t) → N(law Z_X)` as `t → ∞` (input mass shrinks like `1/√t`): the lower
bound is `N(W_X t) = N(Z_X + X/√t) ≥ N(Z_X)` (independent-noise monotonicity,
`differentialEntropy_add_ge_of_indep`); the upper bound is the Gaussian max-entropy
`N(W_X t) ≤ 2πe (Var X / t + 1) → 2πe = N(Z_X)`
(`differentialEntropy_le_gaussian_of_variance_le`). With
`N(law(Z_X)+law(Z_Y)) = N(Z_X) + N(Z_Y)` (`entropyPower_gaussian_additivity`,
standard normals), the two `log`s converge to the same value, so `R t → 0`.

## Honesty

All per-`t` regularity (a.c., finite-entropy integrability of the W-path laws, the
8 fibre-integrability preconditions of `differentialEntropy_add_ge_of_indep`, finite
variance) is threaded as **honest preconditions** in the signatures (方針 X). The
Stam core / EPI core is never bundled as a `*Hypothesis`. The genuine analytic glue
(scaling cancellation, log-continuity composition, Gaussian additivity, order limit)
is the deliverable; preconditions not discharged here remain honest hypotheses.

Status: §1 (`epi_of_csiszarLogRatioGap_tendsto`), §2 (`entropyPower_path_scaling`),
and §4 (`csiszarLogRatioGap_tendsto_zero_atTop`) have `sorry`-free bodies. The single
outstanding `sorry` is §3's per-path squeeze (`entropyPower_rescaled_path_tendsto`),
the relocated W-path regularity wall — see its `@residual` tag.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace InformationTheory.Shannon.EPICase1RatioLimit

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamToBridge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap csiszarLogRatioGap_at_zero)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## §1 — Order-theoretic deliverable (fully genuine)

`epi_of_csiszarLogRatioGap_tendsto`: antitone `R` on `Ici 0` together with
`R t → 0` forces `R 0 ≥ 0`, hence EPI. Pure order-limit argument; no analysis. -/

/-- **Order-limit bridge → EPI**. If the log-ratio gap `R = csiszarLogRatioGap …`
is antitone on `Set.Ici 0` and `R t → 0` as `t → ∞`, then `R 0 ≥ 0`, and therefore
the entropy power inequality holds.

`R 0 ≥ R t` for every `t ≥ 0` (antitonicity); since `R t → 0` and the tail predicate
`R 0 ≥ R t` holds eventually, `ge_of_tendsto` gives `R 0 ≥ 0`. The final EPI step is
`epi_of_csiszarLogRatioGap_zero_nonneg` (genuine bridge).

Genuine — no `sorry`, no load-bearing hypotheses (the antitone carrier and the limit
are honest inputs, both about `R` itself, not the EPI conclusion). -/
theorem epi_of_csiszarLogRatioGap_tendsto
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    (h_anti : AntitoneOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici (0 : ℝ)))
    (h_lim : Filter.Tendsto (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t)
        Filter.atTop (nhds (0 : ℝ))) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  set R := fun t => csiszarLogRatioGap X Y Z_X Z_Y P t with hR
  -- `R 0 ≥ R t` for every `t ≥ 0` by antitonicity (`0 ≤ t`).
  have h_tail : ∀ᶠ t in Filter.atTop, R t ≤ R 0 := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact h_anti Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  -- `R t → 0` and `R t ≤ R 0` eventually ⟹ `0 ≤ R 0`.
  have h_zero_le : (0 : ℝ) ≤ R 0 := le_of_tendsto h_lim h_tail
  -- Bridge to EPI.
  exact epi_of_csiszarLogRatioGap_zero_nonneg X Y Z_X Z_Y P h_zero_le

/-! ## §2 — Scaling cancellation (genuine glue + threaded regularity)

`N(law(X+√t·Z_X)) = t · N(law(X/√t + Z_X))` via `entropyPower_map_mul_const`. -/

/-- **Single-path scaling identity**: for `t > 0`,
`entropyPower (P.map (fun ω => A ω + √t · B ω))
   = t · entropyPower (P.map (fun ω => A ω / √t + B ω))`.

`A + √t·B = √t·(A/√t + B)`, so the law on the left is the law on the right pushed
forward by `(· * √t)`; `entropyPower_map_mul_const` with `c = √t` (squared `= t`)
finishes. The a.c. + entropy-integrability of the *unscaled* W-path law are honest
regularity preconditions (consumed by `entropyPower_map_mul_const`). -/
theorem entropyPower_path_scaling
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    {t : ℝ} (ht : 0 < t)
    (h_ac : (P.map (fun ω => A ω / Real.sqrt t + B ω)) ≪ volume)
    (h_ent_int : Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => A ω / Real.sqrt t + B ω)).rnDeriv volume x).toReal)) volume) :
    entropyPower (P.map (fun ω => A ω + Real.sqrt t * B ω))
      = t * entropyPower (P.map (fun ω => A ω / Real.sqrt t + B ω)) := by
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h_sqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt h_sqrt_pos
  set W : Ω → ℝ := fun ω => A ω / Real.sqrt t + B ω with hW
  have hW_meas : Measurable W := (hA.div_const _).add hB
  have hmul_meas : Measurable (fun x : ℝ => x * Real.sqrt t) :=
    measurable_id.mul_const _
  haveI : IsProbabilityMeasure (P.map W) :=
    Measure.isProbabilityMeasure_map hW_meas.aemeasurable
  -- `A + √t·B = (A/√t + B) * √t = (· * √t) ∘ W` pointwise.
  have h_path_eq : (fun ω => A ω + Real.sqrt t * B ω)
      = (fun x => x * Real.sqrt t) ∘ W := by
    funext ω
    simp only [hW, Function.comp_apply]
    field_simp
  -- Push forward through `map_map`: `P.map ((·*√t) ∘ W) = (P.map W).map (·*√t)`.
  have h_map_eq : P.map (fun ω => A ω + Real.sqrt t * B ω)
      = (P.map W).map (fun x => x * Real.sqrt t) := by
    rw [h_path_eq, Measure.map_map hmul_meas hW_meas]
  rw [h_map_eq]
  -- `entropyPower ((P.map W).map (·*√t)) = (√t)² · entropyPower (P.map W) = t · …`.
  rw [entropyPower_map_mul_const h_ac h_sqrt_ne h_ent_int]
  rw [Real.sq_sqrt ht.le]

/-! ## §3 — Per-path limit (squeeze, regularity threaded)

`N(W_X t) → N(law Z_X)` via the independent-noise lower bound and the Gaussian
max-entropy upper bound. -/

/-- **Per-path entropy-power limit**: as `t → ∞`, the rescaled W-path entropy power
`N(law(A/√t + B))` converges to the noise entropy power `N(law B)` when `B` has a
Gaussian law of nonzero variance.

Squeeze: lower bound `N(B + A/√t) ≥ N(B)` (independent-noise monotonicity,
genuine `differentialEntropy_add_ge_of_indep`), upper bound
`N(A/√t + B) ≤ 2πe (Var A / t + v_B) → 2πe·v_B = N(B)` (Gaussian max-entropy,
`differentialEntropy_le_gaussian_of_variance_le`; variance via
`IndepFun.variance_add` + `variance_smul`), both sandwiching `N(law B)` as
`Var A / t → 0` (`tendsto_of_tendsto_of_tendsto_of_le_of_le`).

The squeeze structure (constant lower envelope + decaying upper envelope → common
limit) is the analytic content; bottoming it out requires the **relocated W-path
regularity wall** (a.c. + finite-entropy integrability of `law(A/√t + B)` per `t`,
the 8 fibre integrabilities of `differentialEntropy_add_ge_of_indep`, finite
variance of `A`). These are regularity preconditions (方針 X, NOT load-bearing): the
conclusion `N(W t) → N(B)` is not encoded in any hypothesis. Threading the full
per-`t` regularity bundle is deferred; the body retreats with `sorry`.

@residual(plan:epi-case1-difference-g3-closure-plan) -/
theorem entropyPower_rescaled_path_tendsto
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : Measurable A) (hB : Measurable B)
    (v_B : ℝ≥0) (hv_B : v_B ≠ 0)
    (hB_law : P.map B = gaussianReal 0 v_B) :
    Filter.Tendsto
      (fun t => entropyPower (P.map (fun ω => A ω / Real.sqrt t + B ω)))
      Filter.atTop (nhds (entropyPower (P.map B))) := by
  sorry

/-! ## §4 — Main analytic deliverable

`csiszarLogRatioGap_tendsto_zero_atTop`: composing §2 (cancellation), §3 (per-path
limits), and Gaussian additivity yields `R t → 0`. -/

/-- **`R t → 0` as `t → ∞`** (entropic-CLT-free). Combining the scaling cancellation
(`entropyPower_path_scaling`), the three per-path limits
(`entropyPower_rescaled_path_tendsto`), Gaussian additivity of the noise
(`entropyPower_gaussian_additivity`), and continuity of `log` on positive reals.

The per-`t` regularity (a.c. + entropy integrability of the three W-path laws) is
threaded as honest preconditions (方針 X); the noise Gaussian laws + independence are
regularity. No EPI / Stam core is bundled.

Genuine analytic glue — **own body is `sorry`-free** (scaling cancellation, `log`
cancellation, composition with the per-path limits, Gaussian additivity, limit
transfer). The only transitive `sorry` is the per-path squeeze
`entropyPower_rescaled_path_tendsto` (§3), tagged separately. -/
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
      (P.map (fun ω => X ω / Real.sqrt t + Z_X ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω / Real.sqrt t + Z_X ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_Y : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)).rnDeriv volume x).toReal)) volume)
    (h_scale_sum : ∀ t : ℝ, 0 < t →
      (P.map (fun ω => (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) ≪ volume ∧
      Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => (X ω + Y ω) / Real.sqrt t
            + (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal)) volume) :
    Filter.Tendsto
      (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Abbreviations for the rescaled W-paths and the noise entropy powers.
  set NX := fun t => entropyPower (P.map (fun ω => X ω / Real.sqrt t + Z_X ω)) with hNX
  set NY := fun t => entropyPower (P.map (fun ω => Y ω / Real.sqrt t + Z_Y ω)) with hNY
  set NS := fun t =>
    entropyPower (P.map (fun ω => (X ω + Y ω) / Real.sqrt t + (Z_X ω + Z_Y ω))) with hNS
  -- `v_X + v_Y ≠ 0` over `ℝ≥0`.
  have hv_sum : v_X + v_Y ≠ 0 := by
    intro h
    exact hv_X (le_antisymm (h ▸ le_self_add) bot_le)
  -- Gaussian additivity for the noise sum.
  have hZXZY_law : P.map (fun ω => Z_X ω + Z_Y ω) = gaussianReal 0 (v_X + v_Y) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law
    have h_eq : (Z_X + Z_Y) = fun ω => Z_X ω + Z_Y ω := by funext ω; rfl
    rw [h_eq] at h; simpa using h
  -- Limits of the three rescaled paths (§3).
  have hlimX : Filter.Tendsto NX Filter.atTop (nhds (entropyPower (P.map Z_X))) :=
    entropyPower_rescaled_path_tendsto X Z_X P hX hZX v_X hv_X hZX_law
  have hlimY : Filter.Tendsto NY Filter.atTop (nhds (entropyPower (P.map Z_Y))) :=
    entropyPower_rescaled_path_tendsto Y Z_Y P hY hZY v_Y hv_Y hZY_law
  have hlimS : Filter.Tendsto NS Filter.atTop
      (nhds (entropyPower (P.map (fun ω => Z_X ω + Z_Y ω)))) :=
    entropyPower_rescaled_path_tendsto (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
      (hX.add hY) (hZX.add hZY) (v_X + v_Y) hv_sum hZXZY_law
  -- `N(law(Z_X + Z_Y)) = N(Z_X) + N(Z_Y)` (Gaussian additivity).
  have h_add : entropyPower (P.map (fun ω => Z_X ω + Z_Y ω))
      = entropyPower (P.map Z_X) + entropyPower (P.map Z_Y) :=
    entropyPower_gaussian_additivity P Z_X Z_Y hZX hZY hZXZY_indep 0 0 v_X v_Y hv_X hv_Y
      hZX_law hZY_law
  -- Positivity of the limit values (entropy power is strictly positive).
  have hNX0_pos : 0 < entropyPower (P.map Z_X) := entropyPower_pos _
  have hNY0_pos : 0 < entropyPower (P.map Z_Y) := entropyPower_pos _
  -- The rescaled gap agrees with `R` eventually (for `t > 0`) via §2 cancellation.
  have h_eventually_eq : ∀ᶠ t in Filter.atTop,
      csiszarLogRatioGap X Y Z_X Z_Y P t
        = Real.log (NS t) - Real.log (NX t + NY t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hsX := h_scale_X t ht
    have hsY := h_scale_Y t ht
    have hsS := h_scale_sum t ht
    -- Scaling identities: `N(path) = t · N(W)`.
    have eqX : entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) = t * NX t :=
      entropyPower_path_scaling X Z_X P hX hZX ht hsX.1 hsX.2
    have eqY : entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) = t * NY t :=
      entropyPower_path_scaling Y Z_Y P hY hZY ht hsY.1 hsY.2
    have eqS : entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
        = t * NS t := by
      have := entropyPower_path_scaling (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P
        (hX.add hY) (hZX.add hZY) ht hsS.1 hsS.2
      simpa using this
    -- Positivity for the `log` cancellation.
    have ht_pos : (0 : ℝ) < t := ht
    have hNXt : 0 < NX t := entropyPower_pos _
    have hNYt : 0 < NY t := entropyPower_pos _
    have hNSt : 0 < NS t := entropyPower_pos _
    unfold csiszarLogRatioGap
    rw [eqS, eqX, eqY]
    -- `log (t·NS) − log (t·NX + t·NY) = log NS − log (NX + NY)`.
    rw [show t * NX t + t * NY t = t * (NX t + NY t) by ring]
    rw [Real.log_mul ht_pos.ne' hNSt.ne',
        Real.log_mul ht_pos.ne' (by positivity : (NX t + NY t) ≠ 0)]
    ring
  -- Limit of the rescaled gap: both `log` arguments → `N(Z_X)+N(Z_Y)`.
  have h_lim_rescaled : Filter.Tendsto
      (fun t => Real.log (NS t) - Real.log (NX t + NY t))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hlogS : Filter.Tendsto (fun t => Real.log (NS t)) Filter.atTop
        (nhds (Real.log (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y)))) := by
      rw [← h_add]
      exact (Real.continuousAt_log (entropyPower_pos _).ne').tendsto.comp hlimS
    have hlogD : Filter.Tendsto (fun t => Real.log (NX t + NY t)) Filter.atTop
        (nhds (Real.log (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y)))) := by
      have hsum : Filter.Tendsto (fun t => NX t + NY t) Filter.atTop
          (nhds (entropyPower (P.map Z_X) + entropyPower (P.map Z_Y))) :=
        hlimX.add hlimY
      have hpos : entropyPower (P.map Z_X) + entropyPower (P.map Z_Y) ≠ 0 := by
        positivity
      exact (Real.continuousAt_log hpos).tendsto.comp hsum
    have := hlogS.sub hlogD
    simpa using this
  -- Transfer the limit through the eventual equality.
  exact (Filter.tendsto_congr' h_eventually_eq).mpr h_lim_rescaled

end InformationTheory.Shannon.EPICase1RatioLimit
