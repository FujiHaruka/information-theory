import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.EPI.Stam.Discharge
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.EPI.Blachman.GaussianWitness
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Entropy Power Inequality — L-EPI3 final integration

This file integrates the building blocks from `EPIPlumbing`, `EPIStamDischarge`,
and `FisherInfoV2DeBruijn` to assemble `IsEPIL3IntegratedPipeline` and derive EPI.

## Main definitions

- `IsEPIL3IntegratedPipeline`: single-field structure carrying `IsStamInequalityHyp`.

## Main statements

- `isEPIL3IntegratedPipeline_of_gaussian`: Gaussian full discharge (§3).
- `entropy_power_inequality_gaussian_full`: Gaussian EPI hypothesis-free (§9).
- `isEPIL3IntegratedPipeline_symm`: symmetry of the integrated pipeline (§6).
- `isEPIL3IntegratedPipeline_of_stam`: pipeline from a Stam residual (§6).
- `integrated_pipeline_roundtrip`: round-trip sanity check (§11).

## Implementation notes

The Stam-to-EPI bridge (Cover-Thomas Lemma 17.7.3, Csiszár-style coupling) is absent
from Mathlib. The current design:
- L-EPI1 (Stam inequality) is received as a genuine `IsStamInequalityHyp X Y P`.
- L-EPI2 (de Bruijn integration) uses `IsDeBruijnIntegrationHyp` and
  `FisherInfoV2DeBruijn.deBruijn_identity_v2_gaussian` for the Gaussian case.
- The Stam → L-EPI3 coupling uses `IsStamToEPIBridgeHyp` pass-through;
  the Gaussian saturation case is fully discharged in §3.
-/

namespace InformationTheory.Shannon.EPIL3Integration

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open InformationTheory.Shannon.EPIBlachmanGaussianWitness (convDensityAdd_gaussian_closed_form)

/-! ## §1 — Integrated pipeline predicate -/

/-- **Integrated L-EPI3 pipeline predicate**.

Carries the genuine Stam inequality (Cover-Thomas Lemma 17.7.2 signature) as its
single field. The Stam-to-EPI *bridge* (Cover-Thomas Lemma 17.7.3 coupling) is no
longer a load-bearing field: consumers now discharge it internally via the shared
sorry lemma `EntropyPowerInequality.stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`) rather than threading a
`bridge : IsStamToEPIBridgeHyp` predicate hypothesis (Cluster C Tier-3 → Tier-2
migration, `epi-stam-cluster-c-sorry-migration-plan`, route L-EPISC-3-α: the
bundle structure is retained but its load-bearing bridge field is removed). -/
@[entry_point]
structure IsEPIL3IntegratedPipeline {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Stam inequality (Cover-Thomas Lemma 17.7.2) genuine signature. -/
  stam : IsStamInequalityHyp X Y P

/-! ## §3 — Gaussian full discharge (hypothesis-free) -/

/-- **Gaussian pipeline witness from an honest Stam hypothesis**.

For independent Gaussians `X, Y` with non-zero variance, the Stam-to-EPI
*bridge* field is discharged hypothesis-free via `isStamToEPIBridgeHyp_of_gaussian`
(which uses `isEntropyPowerInequalityHypothesis_of_gaussian` under the hood,
applying the Gaussian saturation case from `EntropyPowerInequality.lean`). The
*Stam* field is supplied as an **honest `IsStamInequalityHyp X Y P` argument**, not
discharged.

**RESOLVED (2026-05-20):** the former vacuous "Fisher-info-zero" route — which
`exfalso`-ed the `0 < J_X` precondition against the buggy V1 `fisherInfo = 0`
artefact for Gaussians and asserted nothing about Stam — was removed. There is no
vacuous back-door: the Stam half is a genuine non-circular hypothesis here. The
genuine hypothesis-free Gaussian EPI (no Stam claim at all) is
`entropy_power_inequality_gaussian_full`. -/
@[entry_point]
theorem isEPIL3IntegratedPipeline_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂)
    (h_stam : IsStamInequalityHyp X Y P) :
    IsEPIL3IntegratedPipeline X Y P :=
  -- The former `bridge` field (discharged here via `isStamToEPIBridgeHyp_of_gaussian`)
  -- was removed in Cluster C Tier-2 migration; the bridge is now discharged
  -- internally by consumers via `stamToEPIBridge_holds`. The Gaussian-law
  -- arguments are retained as regularity preconditions documenting the setting.
  { stam := h_stam }

-- (deleted, legacy Stam→EPI subtree removal) `entropy_power_inequality_three_arg_integrated`
-- and `entropy_power_inequality_four_arg_integrated` were removed together with the
-- legacy bridge subtree: both delegated through `epi_l3_of_integrated_pipeline`
-- (deleted in §1) into `EntropyPowerInequality.stamToEPIBridge_holds` (the lone EPI-family
-- `sorry`, deleted), so they are transitive consumers of that bridge and could not survive
-- its removal. Both had 0 consumers (dead leaves). NOTE: these two were NOT on the brief's
-- explicit delete list — they are forced co-deletions surfaced by `dep_consumers.sh`
-- (reverse-dependency gap in the brief's ripple estimate; reported to orchestrator).

/-! ## §6 — Pipeline predicate manipulation -/

/-- **Symmetry of integrated pipeline**: `IsEPIL3IntegratedPipeline X Y P`
implies `IsEPIL3IntegratedPipeline Y X P`. -/
@[entry_point]
theorem isEPIL3IntegratedPipeline_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIL3IntegratedPipeline X Y P) :
    IsEPIL3IntegratedPipeline Y X P where
  stam := isStamInequalityHyp_symm h.stam

/-- **Pipeline from a Stam residual directly** (mirrors `epi_via_stam`).

After the Cluster C Tier-2 migration the bundle no longer carries a `bridge`
field, so the pipeline is built from the genuine Stam residual alone; the
Stam→EPI bridge is discharged internally by consumers via
`stamToEPIBridge_holds`. -/
@[entry_point]
theorem isEPIL3IntegratedPipeline_of_stam
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P) :
    IsEPIL3IntegratedPipeline X Y P where
  stam := h_stam

/-! ## §7 — Hypothesis-reduced re-publish of `entropy_power_inequality`

The original `entropy_power_inequality` takes three separate hypotheses
(L-EPI1 `_h_stam`, L-EPI2 `_h_debruijn`, L-EPI3 `h_epi`); the L-EPI1 and L-EPI2
slots are placeholder `True` so any caller can pass `trivial`. We re-publish
under a single, integrated, **non-trivial** hypothesis (the pipeline) — this
is the "hypothesis-reduced form" promised in the parent plan. -/

/-! ## §8 — Composability with `EPIPlumbing` translation invariance -/

/-! ## §9 — Concrete Gaussian EPI (genuine, via saturation)

**RESOLVED (2026-05-20):** the former `isStamInequalityHyp_of_gaussian_v1_zero`
and `isEPIL3IntegratedPipeline_gaussian` discharged the Stam predicate vacuously
through the buggy V1 `fisherInfo = 0` artefact for Gaussians and were removed. The
genuine Gaussian EPI is `entropy_power_inequality_gaussian_full` below (direct from
`entropyPower_gaussian_additivity`); the integrated-pipeline form takes
a real `IsStamInequalityHyp` argument (`entropy_power_inequality_gaussian_via_pipeline`).
-/

/-- **Gaussian EPI hypothesis-free**: combine the Gaussian saturation case
directly (no Stam predicate needed for the inequality itself; the predicate
is only needed for the integrated pipeline form). -/
@[entry_point]
theorem entropy_power_inequality_gaussian_full
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_eq := entropyPower_gaussian_additivity
    P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY
  exact h_eq.ge

/-! ## §10 — Composability with `FisherInfoV2DeBruijn` (V2 de Bruijn identity) -/

/-! ## §11 — Final sanity-check / regression theorems -/

/-- **Round-trip**: building a pipeline from the Stam residual and then
extracting it yields the original. (The bundle no longer carries a `bridge`
field after the Cluster C Tier-2 migration.) -/
@[entry_point]
theorem integrated_pipeline_roundtrip
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P) :
    let h := isEPIL3IntegratedPipeline_of_stam h_stam
    h.stam = h_stam :=
  rfl

/-! ## §12 — `epi-debruijn-integration-plan` Phase B/C/D contributions

This section contributes the **family-level de Bruijn lift** (Phase B) and the
**bounded-T Gaussian FTC application** (Phase C) called for by
`docs/shannon/epi-debruijn-integration-plan.md`. The former load-bearing
predicate `IsHeatFlowFamilyHyp` (and its Gaussian constructor) was **deleted**
in the Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`,
task 3α-3): it had 0 active consumers; the genuine `HasDerivAt` content is
available through `FisherInfoV2.deBruijn_identity_v2_gaussian` directly, and a
non-Gaussian extension should route through the genuine de Bruijn lemma
`debruijnIdentityV2_holds_assembled` (`wall:debruijn-integration` is [CLOSED
2026-06-04]) rather than a load-bearing structure. A second predicate
`IsDeBruijnTailHyp` (intended for the `T → ∞` tail-analysis externalization)
was attempted in the Wave 3 third batch and then **retracted** in the same
batch by the independent honesty audit
(`defect(epi-debruijn-tail-vacuous-and-empty)`; see retraction comment in
the structure-definition area below). Tail-analysis externalization remains
a pending plan-level task (Phase C-5).

### Honesty notes (load-bearing) — read before extending this section.

1. The predicate `IsDeBruijnIntegrationHyp X Z P T`
   (`EPIStamDischarge.lean:198-214`) **was repaired 2026-05-25** (Wave 3 third
   batch): the former `∀ fPath` quantifier (which collapsed via `fPath := 0`
   through `fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f` defeq and
   `fisherInfoOfDensity 0 = 0` (`FisherInfoV2.lean:100`)) is now
   `∃ fPath, ∀ h_X h_target, ...`, so the predicate is satisfiable for
   genuine density witnesses. Its current declaration-level tag is
   `@audit:retract-candidate(load-bearing-predicate)` (Tier 3 bookkeeping,
   `EPIStamDischarge.lean`), and the analytic core is no longer threaded as a
   load-bearing hypothesis: a general witness `isDeBruijnIntegrationHyp_holds`
   produces the predicate by delegating to the genuine (sorryAx-free) lemma
   `debruijnIntegrationIdentity_holds` (`FisherInfoV2DeBruijn.lean`), whose
   per-time core is now `debruijnIdentityV2_holds_assembled`
   (`wall:debruijn-integration` is [CLOSED 2026-06-04]). The standalone
   Gaussian-case statements below (`bounded_T_ftc_gaussian`) still bypass the
   predicate because the genuine bridge from the bounded-T identity to a
   `∃ fPath` witness is sister-plan responsibility
   (`epi-debruijn-integration-plan.md` Phase B/C/D).

2. Similarly, `IsDeBruijnRegularityHyp X Z P` (`EPIStamDischarge.lean:152-172`)
   **was repaired 2026-05-25** (Wave 3 third batch): the former
   `Integrable (… ) (volume.restrict (Set.Ioi 0))` field (which diverged on
   Gaussian `1/(2(v+t))`) is now
   `∀ T : ℝ, 0 < T → IntervalIntegrable (… ) volume 0 T` (bounded-T window),
   so the field is satisfiable for Gaussian density witnesses. The tail
   behavior on `(0, ∞)` was intended to be externalized via `IsDeBruijnTailHyp`
   (§ below), but that predicate was **retracted** in the same batch by
   independent audit; tail-analysis externalization is now a pending
   plan-level task (Phase C-5, awaiting `EReal`-lift refactor). This section
   continues to provide the per-time-point V2 family lift
   (`isRegularDeBruijnHypV2_family_of_gaussian`) as a standalone deliverable;
   constructing `IsDeBruijnRegularityHyp` for Gaussian via the repaired
   signature is sister-plan responsibility.

3. The §1–§11 pipeline wrappers used to thread
   `IsEPIL3IntegratedPipeline`'s `bridge : IsStamToEPIBridgeHyp` field as a
   load-bearing predicate. That field was **removed** in the Cluster C Tier-2
   migration (`epi-stam-cluster-c-sorry-migration-plan`, route L-EPISC-3-α): the
   bundle structure is retained but the bridge is now discharged internally by
   consumers via the shared sorry lemma
   `EntropyPowerInequality.stamToEPIBridge_holds`
   (`@residual(plan:epi-stam-to-conclusion-plan)`). The de Bruijn integration
   identity in this section remains the honest *input* to Csiszár scaling, and
   the pipeline wrappers no longer carry a load-bearing predicate hypothesis.
-/

-- (deleted 2026-05-28, Cluster C Tier-2 migration `epi-stam-cluster-c-sorry-migration-plan`,
-- task 3α-3) The `structure IsHeatFlowFamilyHyp X Z P` (family-level heat-flow
-- regularity bundle) was removed outright: it had **0 active hypothesis-form
-- consumers** (no declaration took `(h : IsHeatFlowFamilyHyp …)` as an
-- argument) and its sole inhabitation source was the hypothesis-free Gaussian
-- constructor `isHeatFlowFamilyHyp_of_gaussian` (also deleted below). This is
-- the `-empty-consumers` pure-delete sister to `34e17bc` / `37284f1`. A
-- non-Gaussian heat-flow regularity extension that re-introduces a load-bearing
-- consumer should be re-introduced via the genuine de Bruijn lemma
-- `debruijnIdentityV2_holds_assembled` (`wall:debruijn-integration` is [CLOSED
-- 2026-06-04]), not a load-bearing structure.

-- (retracted 2026-05-25, Wave 3 third batch independent audit) **De Bruijn
-- tail-analysis hypothesis** `IsDeBruijnTailHyp X Z P`.
--
-- The Wave 3 third batch (`823e150`) attempted to close a `fPath_tail ≡ 0`
-- vacuous bypass by adding a `tail_limit : Tendsto ... atTop (nhds h_inf)`
-- field. The independent honesty audit reopened to DEFECT on two grounds:
--   (1) the structure had no `Z_law : P.map Z = gaussianReal 0 1` field, so
--       `Z := fun _ ↦ 0` yields `gaussianConvolution X Z T = X` and
--       `tail_limit` holds trivially with `h_inf := h(P.map X)` by
--       `tendsto_const_nhds` — the vacuous channel survives;
--   (2) even after adding `Z_law`, `h_inf : ℝ` cannot hold the genuine
--       `T → ∞` heat-flow entropy limit which diverges to `+∞` (Gaussian
--       sub-entropy lower bound `(1/2)log(2πe·T)`), so the predicate is
--       essentially uninhabited and any consumer is vacuously discharged.
--
-- Predicate retracted; consumer count is 0 (Phase D was sister-plan pending).
-- The honest re-introduction path requires `h_inf : EReal` (or `ℝ≥0∞`) and
-- a `Z_law` field; tracked under `docs/shannon/epi-debruijn-integration-plan.md`
-- Phase C-5 with `defect(epi-debruijn-tail-vacuous-and-empty)` rationale.

/-! ### Phase C-5 — De Bruijn tail externalization (honest re-introduction)

Honest re-introduction of `IsDeBruijnTailHyp X Z P` per
`docs/shannon/epi-debruijn-tail-reintroduction-plan.md`. The Wave 3 third
batch retract (commit `823e150`, 2026-05-25) identified two defects:
(i) absence of `Z_law` allowed a `Z := 0` vacuous bypass, and
(ii) `h_inf : ℝ` made the predicate essentially uninhabited because the
Gaussian sub-entropy `(1/2) log (2π e (v+T))` diverges to `+∞` as `T → ∞`.

Both defects are addressed structurally:

* `Z_law : P.map Z = gaussianReal 0 1` is included as a field, closing the
  `Z = 0` bypass channel.
* `h_inf : EReal` accommodates the `+∞` Gaussian limit; coercion to `EReal`
  is provided by `Real.toEReal`, and the convergence
  `Tendsto (Real.toEReal ∘ ·) atTop (𝓝 ⊤) ↔ Tendsto · atTop atTop`
  (`EReal.tendsto_coe_nhds_top_iff`) bridges to the standard real-valued
  divergence statement.

The Gaussian instance `isDeBruijnTailHyp_of_gaussian` uses
`h_inf := ⊤` and routes the existing closed-form
`differentialEntropy_gaussianConvolution_of_gaussian` through
`Real.tendsto_log_atTop` and the standard `atTop`-shift / `atTop`-scaling
chain. -/

/-- **De Bruijn tail-analysis hypothesis** (`IsDeBruijnTailHyp X Z P`, honest
re-introduction 2026-05-25).

Externalizes the `T → ∞` tail-analysis of the heat-flow differential entropy
`T ↦ h(P.map (X + √T · Z))` as a load-bearing hypothesis with EReal lift
`h_inf : EReal` (Gaussian case `h_inf = ⊤`) and a `Z_law` field structurally
closing the `Z := 0` vacuous-bypass channel that retracted the prior
incarnation.

Honest re-introduction conditions (both required, derived from the retract
verdict `defect(epi-debruijn-tail-vacuous-and-empty)`):

1. **`EReal` lift** — `h_inf : EReal` allows divergent (`⊤`) limits.
2. **`Z_law` field** — `Z_law : P.map Z = gaussianReal 0 1` closes the
   `Z = 0` vacuous bypass.

NOT a discharge — load-bearing on `Z_law` + `tail_limit`.

`@audit:ok` — 2026-05-27 independent honesty audit (Phase 1.B follow-up).
Re-verified the past 2026-05-25 audit:PASS verdict (recorded inline below) and
confirmed it remains accurate under current honesty doctrine. Body is a genuine
3-field `Type` structure where each field is a regularity precondition
(`Z_law` rules the vacuous `Z := 0` bypass, `h_inf : EReal` lifts the divergent
Gaussian case, `tail_limit` carries the genuine `Tendsto` content). The
Gaussian instance constructor `isDeBruijnTailHyp_of_gaussian` (`:770`)
exhibits a substantive multi-step `Tendsto` discharge via
`Real.tendsto_log_atTop` + `EReal.tendsto_coe_nhds_top_iff`. No active
consumer yet; the structure exists to externalize the `T → ∞` tail-analysis
as honest data, not as a load-bearing claim.

-- audit:PASS 2026-05-25 by honesty-auditor: Tier 1/2/3 verified.
-- T1 (type ≠ conclusion): 3-field structure ≠ Gaussian-instance signature;
--   discharge is a substantive 5-step Tendsto chain, no circularity.
-- T2 (vacuous-bypass closure): `Z_law : P.map Z = gaussianReal 0 1` rules out
--   `Z := 0` (Dirac ≠ Gaussian), `h_inf : EReal` is forced by limit uniqueness
--   in T2 space, `atTop` is non-trivial — all three channels structurally closed.
-- T3 (semantic non-emptiness): `h_inf : EReal` lift makes `⊤` representable;
--   Gaussian instance `isDeBruijnTailHyp_of_gaussian` exhibits a genuine
--   discharge with `h_inf := ⊤` via `Real.tendsto_log_atTop` + EReal coe lift. -/
structure IsDeBruijnTailHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Type where
  /-- `Z` is the standard normal driving the heat flow (vacuous-bypass closure). -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- The asymptotic value of the heat-flow entropy; EReal-valued to allow
  divergent (`⊤`) limits. -/
  h_inf : EReal
  /-- Heat-flow entropy converges to `h_inf` via coercion through
  `Real.toEReal`. The lambda form is written verbatim (not `Real.toEReal ∘ _`)
  to keep `EReal.tendsto_coe_nhds_top_iff` (`@[simp]`, with
  `omit [TopologicalSpace α]`) discoverable. -/
  tail_limit :
    Tendsto
      (fun T : ℝ => Real.toEReal
        (InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z T))))
      atTop (𝓝 h_inf)

-- (Gaussian discharge `isDeBruijnTailHyp_of_gaussian` is deferred until after
-- `differentialEntropy_gaussianConvolution_of_gaussian` (the closed-form
-- bridge) is in scope below in Phase C-3.)

/-! ### Phase B helpers — `gaussianConvolution` boundary -/

/-- `gaussianConvolution X Z 0 = X` pointwise (uses `Real.sqrt 0 = 0`). -/
@[entry_point]
theorem gaussianConvolution_at_zero {Ω : Type*} (X Z : Ω → ℝ) :
    InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z 0 = X := by
  funext ω
  simp [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution]

/-- `P.map (gaussianConvolution X Z 0) = P.map X`. -/
theorem map_gaussianConvolution_at_zero {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) :
    P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z 0) = P.map X := by
  rw [gaussianConvolution_at_zero]

/-- `differentialEntropy (P.map (gaussianConvolution X Z 0)) =
differentialEntropy (P.map X)`. -/
theorem differentialEntropy_gaussianConvolution_at_zero
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) :
    InformationTheory.Shannon.differentialEntropy
      (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z 0))
      = InformationTheory.Shannon.differentialEntropy (P.map X) := by
  rw [map_gaussianConvolution_at_zero]

/-! ### Phase B-4 — Gaussian per-time-point V2 family lift -/

/-- **Gaussian per-time-point V2 family lift** (Phase B-4, honest, Gaussian
restricted, hypothesis-free).

For independent Gaussian `X ∼ 𝒩(m, v)` (with `v ≠ 0`) and standard normal
`Z ∼ 𝒩(0, 1)`, the V2 de Bruijn regularity `IsRegularDeBruijnHypV2 X Z P t`
holds for every `t > 0`, with explicit density witness
`gaussianPDFReal m (v + ⟨t, ht.le⟩)`.

The witness is constructed by routing
`FisherInfoV2.deBruijn_identity_v2_gaussian` (which gives the `HasDerivAt`
directly) into the structure constructor; no Mathlib-side discharge is needed
because Phase D of `fisher-info-gaussian-discharge-moonshot-plan.md` already
publishes that derivative.

This is the family-level lift promised by Phase B of
`epi-debruijn-integration-plan.md`, restricted to the Gaussian case. The
general non-Gaussian case is externalized via `IsHeatFlowFamilyHyp`.

(Returns `Type`, not `Prop`, because `IsRegularDeBruijnHypV2` carries a
density witness as data; declared `noncomputable def` accordingly.)
@audit:ok -/
@[entry_point]
noncomputable def isRegularDeBruijnHypV2_family_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z)
    (_hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (_hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) :
    ∀ t : ℝ, 0 < t →
      InformationTheory.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t := by
  intro t ht
  -- Phase 2.B step 1 (foundation): `IsRegularDeBruijnHypV2` is now 2-field
  -- (regularity only). The `derivAt_entropy_eq_half_fisher_v2` field used to
  -- be filled here via `deBruijn_identity_v2_gaussian`; that discharge is
  -- now downstream (via the genuine `debruijnIdentityV2_holds_assembled`;
  -- `wall:debruijn-integration` is [CLOSED 2026-06-04]).
  exact
    { Z_law := hZ_law
      density_t := gaussianPDFReal m (v + ⟨t, ht.le⟩)
      -- Conv-pin (Gaussian case, 2026-05-31 plan §5-F): genuine closure.
      -- `density_t = gaussianPDFReal m (v + ⟨t,ht.le⟩)` and the conv-pin RHS is
      -- `convDensityAdd (gaussianPDFReal m v) (gaussianPDFReal 0 ⟨t,ht.le⟩)`, which
      -- equals `gaussianPDFReal (m+0) (v+⟨t,ht.le⟩) = gaussianPDFReal m (v+⟨t,ht.le⟩)`
      -- by `convDensityAdd_gaussian_closed_form` (@audit:ok, sorryAx-free) + `add_zero`.
      density_t_eq := by
        intro ht' x
        have ht_ne : (⟨t, ht.le⟩ : ℝ≥0) ≠ 0 := by
          intro h
          exact ht.ne' (congrArg NNReal.toReal h)
        rw [convDensityAdd_gaussian_closed_form hv ht_ne, add_zero]
      -- §5A `pX`-witness fields (Gaussian case): `X ∼ 𝒩(m, v)` has Lebesgue
      -- density `gaussianPDFReal m v`. All genuine (no new sorry).
      pX := gaussianPDFReal m v
      pX_nn := fun x => gaussianPDFReal_nonneg m v x
      pX_meas := measurable_gaussianPDFReal m v
      pX_law := by
        -- `P.map X = gaussianReal m v = withDensity (gaussianPDF m v)`,
        -- and `gaussianPDF m v = fun x => ofReal (gaussianPDFReal m v x)` (def).
        rw [_hX_law, gaussianReal_of_var_ne_zero m hv, gaussianPDF_def]
      -- Second-moment regularity (genuine, Gaussian case). `X ∼ 𝒩(m,v)` has a finite
      -- second moment: `id ∈ L²(gaussianReal m v)` (`memLp_id_gaussianReal`), so
      -- `x ↦ x²` is `gaussianReal m v`-integrable (`MemLp.integrable_sq`); transport to
      -- `volume` via `gaussianReal = withDensity (gaussianPDF m v)` and
      -- `integrable_withDensity_iff` (giving `x² · (gaussianPDF m v x).toReal`, which is
      -- `x² · gaussianPDFReal m v x`).
      pX_mom := by
        have hsq : Integrable (fun x => x ^ 2) (gaussianReal m v) := by
          have hL2 : MemLp id 2 (gaussianReal m v) := memLp_id_gaussianReal 2
          simpa using hL2.integrable_sq
        rw [gaussianReal_of_var_ne_zero m hv] at hsq
        have hvol : Integrable (fun x => x ^ 2 * (gaussianPDF m v x).toReal) volume :=
          (integrable_withDensity_iff (measurable_gaussianPDF m v)
            (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hsq
        refine hvol.congr ?_
        filter_upwards with x
        rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m v x)] }

-- (deleted 2026-05-28, Cluster C Tier-2 migration, task 3α-3) The Gaussian
-- constructor `isHeatFlowFamilyHyp_of_gaussian` was removed together with the
-- `IsHeatFlowFamilyHyp` structure it inhabited (see the structure-deletion note
-- in §12). It had no consumers; its genuine `HasDerivAt` content is available
-- through `FisherInfoV2.deBruijn_identity_v2_gaussian` directly.

/-! ### Phase C-3 — Gaussian closed-form entropy at the heat-flow boundary -/

/-- **Gaussian heat-flow entropy boundary value at `T`** for `T ≥ 0`. -/
@[entry_point]
theorem differentialEntropy_gaussianConvolution_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {T : ℝ} (hT : 0 ≤ T) :
    InformationTheory.Shannon.differentialEntropy
      (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z T))
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + T)) := by
  rw [InformationTheory.Shannon.FisherInfoV2.gaussianConvolution_law_of_gaussian
        hX hZ hXZ hX_law hZ_law hT]
  exact InformationTheory.Shannon.FisherInfoV2.differentialEntropy_gaussianReal_heat_path
    m hv hT

/-! ### Phase C-5 — Gaussian discharge of `IsDeBruijnTailHyp` (honest)

The Gaussian instance constructor for the re-introduced `IsDeBruijnTailHyp`
predicate (`@audit:ok` per 2026-05-27 audit, defined above near the
retraction notice at `:595-613`). Discharged with `h_inf := ⊤` via
the existing closed-form `differentialEntropy_gaussianConvolution_of_gaussian`
combined with `Real.tendsto_log_atTop` and the standard `atTop`-shift /
`atTop`-scaling chain, lifted to `EReal` by `EReal.tendsto_coe_nhds_top_iff`. -/

/-- **Gaussian instance of `IsDeBruijnTailHyp`** (Phase C-5 honest discharge).

When `P.map X = gaussianReal m v` with `v ≠ 0`, `P.map Z = gaussianReal 0 1`,
and `X ⊥ Z`, the heat-flow entropy diverges to `+∞` (Gaussian sub-entropy
lower bound `(1/2) log (2π e (v + T)) → +∞`), so `h_inf := ⊤` is genuine.

Discharge route (`differentialEntropy_gaussianConvolution_of_gaussian` above
already gives the closed form `(1/2) log (2π e (v + T))`):

* shift `T ↦ (v : ℝ) + T` via `tendsto_atTop_add_const_left`;
* scale by `2 π e > 0` via `Tendsto.const_mul_atTop`;
* apply `Real.tendsto_log_atTop`;
* scale by `(1/2) > 0` via `Tendsto.const_mul_atTop`;
* congr with the closed-form identity on `[0, ∞)` via `Tendsto.congr'`;
* lift to `EReal` via `EReal.tendsto_coe_nhds_top_iff.mpr`. -/
@[entry_point]
noncomputable def isDeBruijnTailHyp_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) :
    IsDeBruijnTailHyp X Z P where
  Z_law := hZ_law
  h_inf := ⊤
  tail_limit := by
    -- Goal: `Tendsto (fun T => Real.toEReal (h(P.map (gaussConv X Z T)))) atTop (𝓝 ⊤)`.
    -- Strategy: build `Tendsto (fun T => (1/2) * log (2πe(v+T))) atTop atTop`,
    -- congr with the closed-form on `[0, ∞)`, then lift to EReal.
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2pie_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := mul_pos h2pi_pos hexp_pos
    have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    -- `Tendsto (fun T : ℝ => (v : ℝ) + T) atTop atTop`.
    have h_shift : Tendsto (fun T : ℝ => (v : ℝ) + T) atTop atTop :=
      tendsto_atTop_add_const_left atTop (v : ℝ) tendsto_id
    -- Scale by `2πe > 0`.
    have h_scale_inner : Tendsto
        (fun T : ℝ => 2 * Real.pi * Real.exp 1 * ((v : ℝ) + T)) atTop atTop :=
      Tendsto.const_mul_atTop h2pie_pos h_shift
    -- Apply log.
    have h_log : Tendsto
        (fun T : ℝ => Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + T))) atTop atTop :=
      Real.tendsto_log_atTop.comp h_scale_inner
    -- Scale by `(1/2) > 0`.
    have h_closed : Tendsto
        (fun T : ℝ => (1 / 2 : ℝ) *
          Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + T))) atTop atTop :=
      Tendsto.const_mul_atTop hhalf_pos h_log
    -- Congr with entropy form on `T ≥ 0`.
    have h_entropy : Tendsto
        (fun T : ℝ => InformationTheory.Shannon.differentialEntropy
            (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z T))) atTop atTop := by
      refine h_closed.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
      exact
        (differentialEntropy_gaussianConvolution_of_gaussian
          hX hZ hXZ hv hX_law hZ_law hT).symm
    -- Lift to EReal.
    exact EReal.tendsto_coe_nhds_top_iff.mpr h_entropy

/-! ### Phase C-1/C-4 — Bounded-T FTC application (Gaussian case)

This is the **honest Gaussian-restricted bounded-T deliverable** of Phase C:
the de Bruijn integration identity holds for Gaussian `X` on `(0, T)` as a
direct consequence of Mathlib's bounded FTC and Phase B-4 above. Stated as a
*standalone* identity (not via `IsDeBruijnIntegrationHyp`, which carries the
honest `∃ fPath` shape post-repair; bridging this standalone equality into a
predicate witness remains sister-plan responsibility — see §12 honesty note 1). -/

/-- **Heat-flow entropy derivative (Gaussian, on `s > 0` neighbourhood)**.

For Gaussian `X` and `s > 0`, the derivative of `s' ↦ differentialEntropy(P.map
(X + √s' · Z))` at `s` equals `1/(2(v+s))`. This is the per-point statement
from `deBruijn_identity_v2_gaussian` rewritten with the Gaussian closed-form
Fisher information value `1/(v+t)`. -/
@[entry_point]
theorem hasDerivAt_differentialEntropy_heat_flow_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun s' => InformationTheory.Shannon.differentialEntropy
                  (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
      (1 / (2 * ((v : ℝ) + s))) s := by
  -- Step 1: re-derive the LHS identification (same approach as
  -- `deBruijn_identity_v2_gaussian`'s proof). We want
  -- `s' ↦ entropy(...) =ᶠ[nhds s] s' ↦ (1/2) log (2π e (v + s'))` so that
  -- `hasDerivAt_half_log_gaussian_entropy` transfers the derivative.
  have hvs_pos : (0 : ℝ) < (v : ℝ) + s := by
    have hv_pos : (0 : ℝ) < v := by
      have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
    linarith
  have h_pos_nbhd : ∀ᶠ s' in nhds s, (0 : ℝ) < s' := eventually_gt_nhds hs
  have h_eventually : (fun s' => InformationTheory.Shannon.differentialEntropy
        (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
        =ᶠ[nhds s] (fun s' => (1/2 : ℝ) * Real.log
            (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s'))) := by
    refine h_pos_nbhd.mono fun s' hs' => ?_
    exact differentialEntropy_gaussianConvolution_of_gaussian
      hX hZ hXZ hv hX_law hZ_law hs'.le
  -- Step 2: derivative of the log form.
  have h_log_deriv :=
    InformationTheory.Shannon.FisherInfoV2.hasDerivAt_half_log_gaussian_entropy
      (v := v) (s := s) hvs_pos
  -- Transfer. `congr_of_eventuallyEq` expects `f_entropy =ᶠ f_log`, which is
  -- our `h_eventually` (no `.symm` needed).
  exact h_log_deriv.congr_of_eventuallyEq h_eventually

/-- **Continuity of `1/(2(v+t))` on `[0, T]`** for `v > 0`, `T ≥ 0`. -/
theorem continuousOn_one_div_two_times_v_plus
    {v : ℝ≥0} (hv : v ≠ 0) (T : ℝ) :
    ContinuousOn (fun t : ℝ => 1 / (2 * ((v : ℝ) + t))) (Set.Icc 0 T) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h_pos : ∀ t ∈ Set.Icc (0 : ℝ) T, 2 * ((v : ℝ) + t) ≠ 0 := by
    intro t ht
    have ht_nn : (0 : ℝ) ≤ t := ht.1
    have hvt : (0 : ℝ) < (v : ℝ) + t := by linarith
    have h2vt : (0 : ℝ) < 2 * ((v : ℝ) + t) := by linarith
    exact h2vt.ne'
  -- `1/(2(v + t)) = (2 * (v + t))⁻¹`; the inner expression is continuous and
  -- non-zero on `[0, T]`, so the reciprocal is continuous.
  refine ContinuousOn.div continuousOn_const ?_ h_pos
  exact (continuous_const.mul (continuous_const.add continuous_id)).continuousOn

/-- **Continuity of `s' ↦ differentialEntropy(P.map (X + √s' · Z))` on `[0, T]`
for Gaussian `X`**. -/
theorem continuousOn_differentialEntropy_heat_flow_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn
      (fun s' => InformationTheory.Shannon.differentialEntropy
                  (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
      (Set.Icc 0 T) := by
  -- For `s' ∈ [0, T]` (so `s' ≥ 0`), the entropy equals the closed form
  -- `(1/2) log (2π e (v + s'))`, which is continuous.
  have h_eq_on : Set.EqOn
      (fun s' => InformationTheory.Shannon.differentialEntropy
        (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
      (fun s' => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s')))
      (Set.Icc 0 T) := by
    intro s' hs'
    exact differentialEntropy_gaussianConvolution_of_gaussian
      hX hZ hXZ hv hX_law hZ_law hs'.1
  refine ContinuousOn.congr ?_ h_eq_on
  -- Continuity of `(1/2) log (2π e (v + s'))` on `[0, T]`.
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have h2πe_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have h_arg_pos : ∀ s' ∈ Set.Icc (0 : ℝ) T,
      0 < 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s') := by
    intro s' hs'
    have hs'_nn : 0 ≤ s' := hs'.1
    have : (0 : ℝ) < (v : ℝ) + s' := by linarith
    exact mul_pos h2πe_pos this
  -- `Real.log` is continuous on positives.
  have h_inner_cont : ContinuousOn
      (fun s' : ℝ => 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s')) (Set.Icc 0 T) :=
    (continuous_const.mul (continuous_const.add continuous_id)).continuousOn
  have h_log_cont : ContinuousOn
      (fun s' : ℝ => Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s')))
      (Set.Icc 0 T) := by
    refine ContinuousOn.log h_inner_cont ?_
    intro s' hs'
    exact (h_arg_pos s' hs').ne'
  exact continuousOn_const.mul h_log_cont

/-- **Bounded-T FTC application (Gaussian case)** — Phase C-1/C-4 main
deliverable.

For Gaussian `X ∼ 𝒩(m, v)` with `v ≠ 0`, the heat-flow entropy gap over
the bounded interval `(0, T)` equals the path integral of `1/(2(v+t))`:

`h(N(m, v+T)) - h(N(m, v))
    = ∫_(0, T) 1/(2(v+t)) dt`,

stated as a direct equality (i.e., bypassing the
`IsDeBruijnIntegrationHyp X Z P T` predicate; the predicate now carries the
honest `∃ fPath` shape post-repair, but bridging from this standalone equality
into the predicate's existential witness remains sister-plan work — see §12
honesty note 1). The integration uses Mathlib `intervalIntegral` and is
converted to `Set.Ioo`-form for downstream consumption.

`@audit:ok` — genuine bounded-T FTC discharge, body 0 sorry. The former
bookkeeping tag (`@audit:retract-candidate(load-bearing-predicate)`) described
the downstream `IsEPIL3IntegratedPipeline.bridge` field this lemma fed into;
that load-bearing field was removed in Cluster C Tier-2 migration
(`epi-stam-cluster-c-sorry-migration-plan`), so the bookkeeping tag no longer
applies. Unbounded `T → ∞` lift remains a pending plan-level task (the
previously intended `IsDeBruijnTailHyp` externalization was retracted by
independent audit; see the §12 honesty notes and the retraction comment in the
structure-definition area). -/
@[entry_point]
theorem bounded_T_ftc_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {T : ℝ} (hT : 0 ≤ T) :
    InformationTheory.Shannon.differentialEntropy
        (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z T))
      - InformationTheory.Shannon.differentialEntropy (P.map X)
      = ∫ t in Set.Ioo 0 T, 1 / (2 * ((v : ℝ) + t)) ∂volume := by
  set f : ℝ → ℝ := fun s => InformationTheory.Shannon.differentialEntropy
    (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z s)) with hf_def
  set f' : ℝ → ℝ := fun s => 1 / (2 * ((v : ℝ) + s)) with hf'_def
  -- Step 1: continuity of `f` on `[0, T]`.
  have h_cont : ContinuousOn f (Set.Icc 0 T) :=
    continuousOn_differentialEntropy_heat_flow_gaussian hX hZ hXZ hv hX_law hZ_law hT
  -- Step 2: `HasDerivAt f (f' s) s` for `s ∈ Ioo 0 T`.
  have h_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (f' s) s := by
    intro s hs
    exact hasDerivAt_differentialEntropy_heat_flow_gaussian
      hX hZ hXZ hv hX_law hZ_law hs.1
  -- Step 3: `IntervalIntegrable f' volume 0 T` (continuity on `[0, T]`).
  have h_cont_f' : ContinuousOn f' (Set.Icc 0 T) :=
    continuousOn_one_div_two_times_v_plus hv T
  have h_int : IntervalIntegrable f' volume 0 T := by
    have h_icc_eq_uicc : Set.Icc (0 : ℝ) T = Set.uIcc 0 T := by
      rw [Set.uIcc_of_le hT]
    rw [h_icc_eq_uicc] at h_cont_f'
    exact h_cont_f'.intervalIntegrable
  -- Step 4: Mathlib FTC `integral_eq_sub_of_hasDerivAt_of_le`.
  have h_ftc :
      ∫ s in (0 : ℝ)..T, f' s = f T - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT h_cont h_deriv h_int
  -- Step 5: `f 0 = differentialEntropy (P.map X)` (boundary).
  have h_f0 : f 0 = InformationTheory.Shannon.differentialEntropy (P.map X) := by
    simp [hf_def, differentialEntropy_gaussianConvolution_at_zero]
  -- Step 6: convert `∫ s in 0..T, f' s` → `∫ s in Set.Ioo 0 T, f' s ∂volume`.
  -- Use `intervalIntegral.integral_of_le` then `integral_Ioc_eq_integral_Ioo`.
  have h_ioc : ∫ s in (0 : ℝ)..T, f' s = ∫ s in Set.Ioc (0 : ℝ) T, f' s ∂volume :=
    intervalIntegral.integral_of_le hT
  have h_ioo_eq_ioc :
      ∫ s in Set.Ioc (0 : ℝ) T, f' s ∂volume
        = ∫ s in Set.Ioo (0 : ℝ) T, f' s ∂volume :=
    MeasureTheory.integral_Ioc_eq_integral_Ioo
  -- Combine.
  rw [← h_f0]
  rw [← h_ftc, h_ioc, h_ioo_eq_ioc]

/-! ### Phase D — Section closure note

Closure update (2026-05-28, Cluster C Tier-2 migration
`epi-stam-cluster-c-sorry-migration-plan`, route L-EPISC-3-α): the
`IsEPIL3IntegratedPipeline` bundle's former load-bearing
`bridge : IsStamToEPIBridgeHyp` field was **removed**. The §1–§11 pipeline
wrappers now take only the single-field Stam-residual bundle and discharge the
Stam→EPI bridge internally via the shared sorry lemma
`EntropyPowerInequality.stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`); they no longer carry a
load-bearing predicate hypothesis and hold no `@residual` of their own (the
Mathlib wall is localized in `stamToEPIBridge_holds`).

Phase D's own contributions (Phase B-4/C-1/C-4 above) remain the de Bruijn-side
honest inputs to the Csiszár scaling argument and are unchanged. -/

/-! ## §13 — 1-source Csiszár log-ratio gap (genuine monotone object)

The genuine ratio object `csiszarLogRatioGap` (and its `t = 0` / `t = 1`
endpoints) used by the live EPI ratio line in `EPIStamToBridge.lean`
(`csiszarLogRatioGap_hasDerivAt` → `csiszarLogRatioGap_antitoneOn_Ici_zero` →
`isStamToEPIScalingHyp_of_*`).

The earlier difference-form Csiszár gap families were deleted as a structurally
orphaned, false-as-framed dead subgraph; the ratio reframe
(`epi-csiszar-ratio-reframe-plan`) is the genuine successor.
-/

/-- **1-source Csiszár log-ratio gap** (genuine monotone object).

`r(t) = log (N_sum t) − log (N_X t + N_Y t)` where
`N_sum = entropyPower (P.map (X+Y+√t·(Z_X+Z_Y)))`,
`N_X = entropyPower (P.map (X+√t·Z_X))`, `N_Y = entropyPower (P.map (Y+√t·Z_Y))`.

This replaces the (deleted) false-as-framed difference gap: the
log-ratio derivative `r'(t) = J_sum − (N_X·J_X + N_Y·J_Y)/(N_X+N_Y) ≤ 0` is
genuinely closable from plain harmonic Stam (see
`epi-csiszar-ratio-reframe-plan`). Both `log` arguments are strictly positive
(`entropyPower_pos`, `add_pos`), so the gap is well-defined. -/
@[entry_point]
noncomputable def csiszarLogRatioGap {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ :=
  Real.log (entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))))
    - Real.log
        (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
          + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))

/-- **Endpoint `t = 0` of the log-ratio gap**: reduces to
`log (eP(X+Y)) − log (eP X + eP Y)`, the form bridging to EPI
(`r(0) ≥ 0 ⟺ entropyPower (X+Y) ≥ entropyPower X + entropyPower Y`). -/
@[entry_point]
theorem csiszarLogRatioGap_at_zero {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
    csiszarLogRatioGap X Y Z_X Z_Y P 0
      = Real.log (entropyPower (P.map (fun ω => X ω + Y ω)))
        - Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) := by
  unfold csiszarLogRatioGap
  have h_sum_funext :
      (fun ω => X ω + Y ω + Real.sqrt 0 * (Z_X ω + Z_Y ω))
        = fun ω => X ω + Y ω := by
    funext ω
    simp [Real.sqrt_zero]
  have h_X_funext :
      (fun ω => X ω + Real.sqrt 0 * Z_X ω) = X := by
    funext ω
    simp [Real.sqrt_zero]
  have h_Y_funext :
      (fun ω => Y ω + Real.sqrt 0 * Z_Y ω) = Y := by
    funext ω
    simp [Real.sqrt_zero]
  rw [h_sum_funext, h_X_funext, h_Y_funext]

/-- **R-4-a — Endpoint `t = 1` of the log-ratio gap is zero (Gaussian saturation)**.

At `t = 1` the 1-source heat-flow paths are `X + Z_X`, `Y + Z_Y`, and their sum
`X + Y + (Z_X + Z_Y) = (X + Z_X) + (Y + Z_Y)`. When the convolved endpoints
`X + Z_X` and `Y + Z_Y` are independent Gaussians of nonzero variance, EPI
saturates: `N_sum(1) = N_X(1) + N_Y(1)` by `entropyPower_gaussian_additivity`.
Hence `r(1) = log N_sum(1) − log (N_X(1) + N_Y(1)) = log A − log A = 0`
(`sub_self`).

This is the genuine endpoint of the monotone log-ratio object: together with
`r'(t) ≤ 0` on `[0, ∞)` and `r(1) = 0`, monotonicity gives `r(0) ≥ 0`, i.e. EPI.
The Gaussian-pair hypotheses are honest preconditions (laws + independence of the
convolved endpoints), not load-bearing bundling. -/
@[entry_point]
theorem csiszarLogRatioGap_at_one_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X Y Z_X Z_Y : Ω → ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (hXZX : Measurable (fun ω => X ω + Z_X ω))
    (hYZY : Measurable (fun ω => Y ω + Z_Y ω))
    (hIndep : IndepFun (fun ω => X ω + Z_X ω) (fun ω => Y ω + Z_Y ω) P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map (fun ω => X ω + Z_X ω) = gaussianReal m₁ v₁)
    (hLawY : P.map (fun ω => Y ω + Z_Y ω) = gaussianReal m₂ v₂) :
    csiszarLogRatioGap X Y Z_X Z_Y P 1 = 0 := by
  unfold csiszarLogRatioGap
  -- At `t = 1`, `√1 = 1`; reduce the three paths to `X+Z_X`, `Y+Z_Y`,
  -- and their sum `(X+Z_X)+(Y+Z_Y)`.
  have h_sum_funext :
      (fun ω => X ω + Y ω + Real.sqrt 1 * (Z_X ω + Z_Y ω))
        = fun ω => (X ω + Z_X ω) + (Y ω + Z_Y ω) := by
    funext ω; rw [Real.sqrt_one]; ring
  have h_X_funext :
      (fun ω => X ω + Real.sqrt 1 * Z_X ω) = fun ω => X ω + Z_X ω := by
    funext ω; rw [Real.sqrt_one]; ring
  have h_Y_funext :
      (fun ω => Y ω + Real.sqrt 1 * Z_Y ω) = fun ω => Y ω + Z_Y ω := by
    funext ω; rw [Real.sqrt_one]; ring
  rw [h_sum_funext, h_X_funext, h_Y_funext]
  -- Gaussian saturation: `eP((X+Z_X)+(Y+Z_Y)) = eP(X+Z_X) + eP(Y+Z_Y)`.
  have h_sat := entropyPower_gaussian_additivity P
    (fun ω => X ω + Z_X ω) (fun ω => Y ω + Z_Y ω)
    hXZX hYZY hIndep m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY
  rw [h_sat]
  -- `log A − log A = 0`.
  exact sub_self _

end InformationTheory.Shannon.EPIL3Integration