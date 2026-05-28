import Common2026.Meta.EntryPoint
import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.EPIPlumbing
import Common2026.Shannon.EPIStamDischarge
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoGaussian
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.HeatFlowPath
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
# T2-D-I: Entropy Power Inequality — L-EPI3 final integration

`Common2026/Shannon/EntropyPowerInequality.lean` (T2-D, 347 行) の主定理
`entropy_power_inequality` は L-EPI1 + L-EPI2 + L-EPI3 三本立て hypothesis
pass-through pattern で publish 済。Wave 5 で

* `Common2026/Shannon/EPIPlumbing.lean` (319 行)
* `Common2026/Shannon/EPIStamDischarge.lean` (755 行)
* `Common2026/Shannon/FisherInfoV2DeBruijn.lean` (452 行)

の三本柱が揃ったので、本 file はこれら building blocks を **integrate** し、
L-EPI3 を取り出す **integrated pipeline** を整える。

## Approach

主 deliverable は **`IsEPIL3IntegratedPipeline X Y Z P`** という構造体形 predicate。
これを与えると `IsEntropyPowerInequalityHypothesis X Y P` (L-EPI3) が導かれ、
さらに主定理 `entropy_power_inequality` を経由して `entropyPower (P.map (X+Y))
≥ entropyPower (P.map X) + entropyPower (P.map Y)` に着地する。

* §1 — **`IsEPIL3IntegratedPipeline`**: Stam (真 signature) の単一 field predicate。
  `IsStamInequalityHyp X Y P` から L-EPI3 を生成。Stam-to-EPI *bridge* は
  load-bearing field ではなくなり (Cluster C Tier-2 migration、
  `epi-stam-cluster-c-sorry-migration-plan` route L-EPISC-3-α)、consumer が
  shared sorry 補題 `stamToEPIBridge_holds` で内部 discharge する。
* §2 — **integrated 主定理**: integrated pipeline → EPI。`Common2026/Shannon/EPIStamDischarge.lean`
  の `epi_via_stam_main` を packaging。
* §3 — **Gaussian EPI**: `X, Y` がともに Gaussian なら EPI は等号で成立
  (`entropyPower_gaussian_additivity` 直行)。integrated pipeline 形は
  `entropy_power_inequality_gaussian_via_pipeline` が真の `IsStamInequalityHyp`
  を引数で受ける (honest pass-through)。
  **RESOLVED (2026-05-20):** 旧 `isStamInequalityHyp_of_gaussian_v1_zero` /
  `isEPIL3IntegratedPipeline_gaussian` は buggy V1 `fisherInfo = 0` artefact で
  `0 < J_X` precondition を `exfalso` するだけの vacuous discharge だったため削除。
* §4 — **variants**: log / exp / normalized form 全部 integrated pipeline 経由。
* §5 — **chain forms**: 3-arg / 4-arg EPI を integrated pipeline 1 本立てで。
* §6 — **predicate manipulation**: symm / refl / pass-through helpers。

## 撤退ライン (本 file で発動)

Cover-Thomas Lemma 17.7.3 の Csiszár-style coupling argument (path-integral
`∫₀^∞ (J(X+√tZ)⁻¹) dt = h(N) - h(X)` 形を使った Stam → EPI 導出) は **Mathlib
不在 + 本 file scope-out**。

* L-EPI1 (Stam inequality) は `EPIStamDischarge.IsStamInequalityHyp` 真
  signature で受ける。
* L-EPI2 (de Bruijn integration) は `EPIStamDischarge.IsDeBruijnIntegrationHyp`
  真 signature + `FisherInfoV2DeBruijn.deBruijn_identity_v2_gaussian` Gaussian
  discharge を引用。
* L-EPI3 → EPI 着地は `EntropyPowerInequality.entropy_power_inequality` に
  そのまま渡す。
* Stam + de Bruijn → L-EPI3 の coupling 部は `IsStamToEPIBridgeHyp` hypothesis
  pass-through、Gaussian saturation case のみ §3 で full discharge。

## 主シグネチャ

* `IsEPIL3IntegratedPipeline` — single-field Stam-residual bundle predicate (§1)
* `epi_l3_of_integrated_pipeline` — L-EPI3 を生成 (§1)
* `entropy_power_inequality_integrated` — integrated 主定理 (§2)
* `isEPIL3IntegratedPipeline_of_gaussian` — Gaussian full discharge (§3)
* `entropy_power_inequality_gaussian_via_pipeline` — Gaussian EPI via pipeline (§3)
* `entropy_power_inequality_log_form_integrated`
   / `entropy_power_inequality_exp_form_integrated`
   / `entropy_power_inequality_normalized_integrated` — variants (§4)
* `entropy_power_inequality_three_arg_integrated`
   / `entropy_power_inequality_four_arg_integrated` — chain forms (§5)
* `isEPIL3IntegratedPipeline_symm` / `isEPIL3IntegratedPipeline_of_epi_only`
   — predicate manipulation (§6)
-/

namespace InformationTheory.Shannon.EPIL3Integration

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge

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
structure IsEPIL3IntegratedPipeline {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Stam inequality (Cover-Thomas Lemma 17.7.2) genuine signature. -/
  stam : IsStamInequalityHyp X Y P

/-- **L-EPI3 from integrated pipeline**. The integrated pipeline discharges
`IsEntropyPowerInequalityHypothesis X Y P` by feeding the genuine Stam residual
(`h.stam`) through the shared sorry lemma
`EntropyPowerInequality.stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`). The former load-bearing
`bridge : IsStamToEPIBridgeHyp` field was removed in Cluster C Tier-2 migration
(`epi-stam-cluster-c-sorry-migration-plan`), so this wrapper no longer threads a
bridge predicate hypothesis; the Mathlib wall is localized in
`stamToEPIBridge_holds`. -/
theorem epi_l3_of_integrated_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIL3IntegratedPipeline X Y P) :
    IsEntropyPowerInequalityHypothesis X Y P :=
  stamToEPIBridge_holds X Y P h.stam

/-! ## §2 — Integrated main theorem (Cover-Thomas Theorem 17.7.3, integrated form) -/

/-- **Integrated EPI main theorem**: the integrated pipeline gives the full
EPI conclusion in one shot (no need for callers to thread through L-EPI1,
L-EPI2, L-EPI3 separately).

The pipeline now carries only the genuine Stam residual (`h_pipeline.stam`); the
former load-bearing `bridge : IsStamToEPIBridgeHyp` field was removed in Cluster C
Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`). The Stam→EPI bridge
is discharged internally via the shared sorry lemma
`EntropyPowerInequality.stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`), threaded through
`entropy_power_inequality`. -/
theorem entropy_power_inequality_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  -- Thread the genuine residual (`stam`) through the non-circular headline;
  -- `IsStamInequalityHyp` is reducibly defeq to `IsStamInequalityResidual`. The
  -- Stam→EPI bridge (formerly a load-bearing `bridge` field, removed in Cluster C
  -- Tier-2 migration) is discharged internally by `entropy_power_inequality` via
  -- the shared sorry lemma `stamToEPIBridge_holds`.
  entropy_power_inequality P X Y hX hY hXY h_pipeline.stam

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

/-- **Gaussian EPI via integrated pipeline** — the canonical Gaussian saturation
case routed through the integrated pipeline. -/
theorem entropy_power_inequality_gaussian_via_pipeline
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂)
    (h_stam : IsStamInequalityHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_pipeline := isEPIL3IntegratedPipeline_of_gaussian
    P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY h_stam
  exact entropy_power_inequality_integrated P X Y hX hY hXY h_pipeline

/-! ## §4 — Variants (log / exp / normalized form via integrated pipeline) -/

/-- **EPI log form via integrated pipeline**.

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_log_form_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω))
      ≥ (1/2) * Real.log
          (entropyPower (P.map X) + entropyPower (P.map Y)) :=
  entropy_power_inequality_log_form P X Y hX hY hXY h_pipeline.stam

/-- **EPI exp form via integrated pipeline** (Cover-Thomas Theorem 17.7.3 露出形).

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_exp_form_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    Real.exp (2 * Common2026.Shannon.differentialEntropy
              (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map X))
        + Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map Y)) :=
  entropy_power_inequality_exp_form P X Y hX hY hXY h_pipeline.stam

/-- **EPI normalized `(2πe)⁻¹` form via integrated pipeline** (Cover-Thomas Ch.17).

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_normalized_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω)) / gaussianEntropyPowerConst
      ≥ entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst :=
  entropy_power_inequality_normalized P X Y hX hY hXY h_pipeline.stam

/-! ## §5 — Chain forms (3-arg / 4-arg) via integrated pipeline -/

/-- **3-arg EPI via integrated pipeline**. Chains two integrated pipelines.

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_three_arg_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ)
    (h_xy : IsEPIL3IntegratedPipeline X Y P)
    (h_xy_z : IsEPIL3IntegratedPipeline (fun ω => X ω + Y ω) Z P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z) := by
  have h_xy_epi := epi_l3_of_integrated_pipeline h_xy
  have h_xy_z_epi := epi_l3_of_integrated_pipeline h_xy_z
  exact entropy_power_inequality_three_arg P X Y Z h_xy_z_epi h_xy_epi

/-- **4-arg EPI via integrated pipeline**. Chains three integrated pipelines.

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_four_arg_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z W : Ω → ℝ)
    (h_xy : IsEPIL3IntegratedPipeline X Y P)
    (h_xy_z : IsEPIL3IntegratedPipeline (fun ω => X ω + Y ω) Z P)
    (h_xyz_w : IsEPIL3IntegratedPipeline (fun ω => X ω + Y ω + Z ω) W P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω + W ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z)
          + entropyPower (P.map W) := by
  have h_xy_epi := epi_l3_of_integrated_pipeline h_xy
  have h_xy_z_epi := epi_l3_of_integrated_pipeline h_xy_z
  have h_xyz_w_epi := epi_l3_of_integrated_pipeline h_xyz_w
  exact entropy_power_inequality_four_arg P X Y Z W h_xyz_w_epi h_xy_z_epi h_xy_epi

/-! ## §6 — Pipeline predicate manipulation -/

/-- **Symmetry of integrated pipeline**: `IsEPIL3IntegratedPipeline X Y P`
implies `IsEPIL3IntegratedPipeline Y X P`. -/
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

/-- **Hypothesis-reduced EPI** (Cover-Thomas Theorem 17.7.3, integrated form).

Single non-trivial hypothesis `IsEPIL3IntegratedPipeline X Y P` (vs the
three-hypothesis form in `EntropyPowerInequality.entropy_power_inequality`).

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_reduced
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  entropy_power_inequality_integrated P X Y hX hY hXY h_pipeline

/-- **Hypothesis-reduced EPI exp form**. Single integrated hypothesis.

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_exp_form_reduced
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    Real.exp (2 * Common2026.Shannon.differentialEntropy
              (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map X))
        + Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map Y)) :=
  entropy_power_inequality_exp_form_integrated P X Y hX hY hXY h_pipeline

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
theorem integrated_pipeline_roundtrip
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P) :
    let h := isEPIL3IntegratedPipeline_of_stam h_stam
    h.stam = h_stam :=
  rfl

/-- **Three forms of EPI are equivalent** (in the presence of the integrated
pipeline + measurability).

Pipeline wrapper; the bundle's former load-bearing `bridge` field was removed in
Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`), and the
Stam→EPI bridge is discharged internally via the shared sorry lemma
`stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`). See the
`entropy_power_inequality_integrated` header. -/
theorem entropy_power_inequality_three_forms_equiv
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    (entropyPower (P.map (fun ω => X ω + Y ω))
        ≥ entropyPower (P.map X) + entropyPower (P.map Y))
    ∧ (Real.exp (2 * Common2026.Shannon.differentialEntropy
                (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map X))
          + Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map Y)))
    ∧ (entropyPower (P.map (fun ω => X ω + Y ω)) / gaussianEntropyPowerConst
        ≥ entropyPower (P.map X) / gaussianEntropyPowerConst
          + entropyPower (P.map Y) / gaussianEntropyPowerConst) :=
  ⟨entropy_power_inequality_reduced P X Y hX hY hXY h_pipeline,
   entropy_power_inequality_exp_form_reduced P X Y hX hY hXY h_pipeline,
   entropy_power_inequality_normalized_integrated P X Y hX hY hXY h_pipeline⟩

/-! ## §12 — `epi-debruijn-integration-plan` Phase B/C/D contributions

This section contributes the **family-level de Bruijn lift** (Phase B) and the
**bounded-T Gaussian FTC application** (Phase C) called for by
`docs/shannon/epi-debruijn-integration-plan.md`. The former load-bearing
predicate `IsHeatFlowFamilyHyp` (and its Gaussian constructor) was **deleted**
in the Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`,
task 3α-3): it had 0 active consumers; the genuine `HasDerivAt` content is
available through `FisherInfoV2.deBruijn_identity_v2_gaussian` directly, and a
non-Gaussian extension should route through `wall:debruijn-integration` rather
than a load-bearing structure. A second predicate
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
   produces the predicate by delegating to the shared sorry lemma
   `debruijnIntegrationIdentity_holds` (`@residual(wall:debruijn-integration)`,
   `FisherInfoV2DeBruijn.lean`). (Stale prose cleanup, honesty audit 2026-05-28:
   the prior wording cited a now-superseded `@audit:staged` tag.) The standalone
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
-- consumer should be re-introduced via `wall:debruijn-integration`
-- (shared sorry lemma `debruijnIdentityV2_holds`), not a load-bearing structure.

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
        (Common2026.Shannon.differentialEntropy
          (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z T))))
      atTop (𝓝 h_inf)

-- (Gaussian discharge `isDeBruijnTailHyp_of_gaussian` is deferred until after
-- `differentialEntropy_gaussianConvolution_of_gaussian` (the closed-form
-- bridge) is in scope below in Phase C-3.)

/-! ### Phase B helpers — `gaussianConvolution` boundary -/

/-- `gaussianConvolution X Z 0 = X` pointwise (uses `Real.sqrt 0 = 0`). -/
@[entry_point]
theorem gaussianConvolution_at_zero {Ω : Type*} (X Z : Ω → ℝ) :
    Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z 0 = X := by
  funext ω
  simp [Common2026.Shannon.FisherInfoV2.gaussianConvolution]

/-- `P.map (gaussianConvolution X Z 0) = P.map X`. -/
theorem map_gaussianConvolution_at_zero {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) :
    P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z 0) = P.map X := by
  rw [gaussianConvolution_at_zero]

/-- `differentialEntropy (P.map (gaussianConvolution X Z 0)) =
differentialEntropy (P.map X)`. -/
theorem differentialEntropy_gaussianConvolution_at_zero
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) :
    Common2026.Shannon.differentialEntropy
      (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z 0))
      = Common2026.Shannon.differentialEntropy (P.map X) := by
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
density witness as data; declared `noncomputable def` accordingly.) -/
noncomputable def isRegularDeBruijnHypV2_family_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z)
    (_hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (_hv : v ≠ 0)
    (_hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) :
    ∀ t : ℝ, 0 < t →
      Common2026.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t := by
  intro t ht
  -- Phase 2.B 段 1 (foundation): `IsRegularDeBruijnHypV2` is now 2-field
  -- (regularity only). The `derivAt_entropy_eq_half_fisher_v2` field used to
  -- be filled here via `deBruijn_identity_v2_gaussian`; that discharge is
  -- now downstream (via `debruijnIdentityV2_holds` / shared wall lemma).
  exact
    { Z_law := hZ_law
      density_t := gaussianPDFReal m (v + ⟨t, ht.le⟩) }

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
    Common2026.Shannon.differentialEntropy
      (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z T))
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + T)) := by
  rw [Common2026.Shannon.FisherInfoV2.gaussianConvolution_law_of_gaussian
        hX hZ hXZ hX_law hZ_law hT]
  exact Common2026.Shannon.FisherInfoV2.differentialEntropy_gaussianReal_heat_path
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
        (fun T : ℝ => Common2026.Shannon.differentialEntropy
            (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z T))) atTop atTop := by
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
      (fun s' => Common2026.Shannon.differentialEntropy
                  (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
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
  have h_eventually : (fun s' => Common2026.Shannon.differentialEntropy
        (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
        =ᶠ[nhds s] (fun s' => (1/2 : ℝ) * Real.log
            (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s'))) := by
    refine h_pos_nbhd.mono fun s' hs' => ?_
    exact differentialEntropy_gaussianConvolution_of_gaussian
      hX hZ hXZ hv hX_law hZ_law hs'.le
  -- Step 2: derivative of the log form.
  have h_log_deriv :=
    Common2026.Shannon.FisherInfoV2.hasDerivAt_half_log_gaussian_entropy
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
      (fun s' => Common2026.Shannon.differentialEntropy
                  (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
      (Set.Icc 0 T) := by
  -- For `s' ∈ [0, T]` (so `s' ≥ 0`), the entropy equals the closed form
  -- `(1/2) log (2π e (v + s'))`, which is continuous.
  have h_eq_on : Set.EqOn
      (fun s' => Common2026.Shannon.differentialEntropy
        (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z s')))
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
    Common2026.Shannon.differentialEntropy
        (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z T))
      - Common2026.Shannon.differentialEntropy (P.map X)
      = ∫ t in Set.Ioo 0 T, 1 / (2 * ((v : ℝ) + t)) ∂volume := by
  set f : ℝ → ℝ := fun s => Common2026.Shannon.differentialEntropy
    (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z s)) with hf_def
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
  have h_f0 : f 0 = Common2026.Shannon.differentialEntropy (P.map X) := by
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

/-! ## §13 — Phase D: `csiszarGap` function + sister entry point

Phase D of `epi-debruijn-integration-phaseD-plan.md`. Defines the
Csiszár scaling gap function `csiszarGap` whose shape verbatim matches
the `AntitoneOn` argument lambda body in
`EPIStamToBridge.IsStamToEPIScalingHyp` (sister
`epi-stam-to-conclusion-plan` Phase A consumer). The `rfl` lemma
`csiszarGap_shape_for_sister` confirms the verbatim shape match.

Scope (per the Phase D mini-plan):

* D-1-1 `csiszarGap` — definition (shape verbatim from sister
  `EPIStamToBridge.lean:210-216`).
* D-1-2 `csiszarGap_at_zero` — endpoint at `s = 0`
  (`heatFlowPath2 _ _ 0 = X`, so gap reduces to the EPI gap of the
  original `X, Y`).
* D-1-3 `csiszarGap_at_one_eq_zero_of_gaussian_pair` — endpoint at
  `s = 1` is zero by Gaussian saturation (`Z_X, Z_Y` independent
  standard normals).
* D-2 (downgraded to strategy γ statement-only after L-DBD-2-α fired
  during D-0 honesty check; see
  `csiszarGap_bounded_T_ftc_bridge_note` below).
* D-4 `csiszarGap_shape_for_sister` — `rfl` lemma exposing
  `csiszarGap` shape for sister consumption.
-/

open Common2026.Shannon (heatFlowPath2 heatFlowPath2_zero heatFlowPath2_one
  measurable_heatFlowPath2)

/-- **Csiszár scaling gap function** (Phase D D-1-1 of
`epi-debruijn-integration-phaseD-plan.md`).

`csiszarGap X Y Z_X Z_Y P s` is the EPI gap at heat-flow path parameter
`s ∈ [0, 1]` along the path `Common2026.Shannon.heatFlowPath2`:

  `gap_s := entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
            − entropyPower (P.map (heatFlowPath2 X Z_X s))
            − entropyPower (P.map (heatFlowPath2 Y Z_Y s))`

**Shape contract**: the body matches verbatim the lambda body of
`Common2026.Shannon.IsStamToEPIScalingHyp`'s `AntitoneOn` argument
(`Common2026/Shannon/EPIStamToBridge.lean:210-216`); the `rfl` lemma
`csiszarGap_shape_for_sister` (D-4) confirms this. Sister
`epi-stam-to-conclusion-plan` Phase A consumes this shape directly
to discharge `IsStamToEPIScalingHyp` honestly.

This is a `noncomputable def` (standard Lean output, not a `Prop`-level
predicate). It is **not** a staged predicate — no honesty audit
required at the predicate level.

`@audit:ok` — Phase A (2026-05-27, `epi-stam-to-conclusion-phaseA-plan`)
consumes this definition transitively via `csiszarGap_eq_one_source_via_rescale`
(A-0'-2, `:1311`, `@audit:ok`), which unfolds `csiszarGap csiszarGap1Source`
inline (`:1478`) and feeds the rescale lift `csiszarGap_antitoneOn_Icc_zero_one`
(`Common2026/Shannon/EPIStamToBridge.lean:912`). The pending `sorry` in
that consumer is a separate sub-plan (A-4-rescale), not a defect in the
definition here. Body is a transparent `entropyPower - entropyPower - entropyPower`
identification, no `Prop`-level claim bundling. -/
noncomputable def csiszarGap {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (s : ℝ) : ℝ :=
  entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
    - entropyPower (P.map (heatFlowPath2 X Z_X s))
    - entropyPower (P.map (heatFlowPath2 Y Z_Y s))

/-- **Endpoint at `s = 0`** (Phase D D-1-2). The Csiszár gap at the path
start reduces to the EPI gap for the original `X, Y` (since
`heatFlowPath2 X Z_X 0 = X` and `heatFlowPath2 Y Z_Y 0 = Y` by
`Common2026.Shannon.heatFlowPath2_zero`).

`@audit:ok` — 2026-05-27 independent honesty audit. Body is a genuine
tactic proof (`unfold csiszarGap` + `funext` + `simp [heatFlowPath2_zero]`
+ `rw`), not a degenerate-definition exploit; the conclusion `=
entropyPower (X+Y) - entropyPower X - entropyPower Y` is the honest
endpoint identification. Structurally identical to the 1-source sister
`csiszarGap1Source_at_zero` (`:1490`, `@audit:ok` per Phase A cleanup). -/
theorem csiszarGap_at_zero {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
    csiszarGap X Y Z_X Z_Y P 0
      = entropyPower (P.map (fun ω => X ω + Y ω))
        - entropyPower (P.map X) - entropyPower (P.map Y) := by
  unfold csiszarGap
  have h_sum_funext :
      (heatFlowPath2 X Z_X 0 + heatFlowPath2 Y Z_Y 0)
        = fun ω => X ω + Y ω := by
    funext ω
    simp [heatFlowPath2_zero]
  rw [h_sum_funext, heatFlowPath2_zero, heatFlowPath2_zero]

/-- **Endpoint at `s = 1` is zero (Gaussian saturation case)** (Phase D
D-1-3). When `Z_X, Z_Y` are independent standard normals, the path-end
gap is zero by `entropyPower_gaussian_additivity` (both
endpoints are standard normal, so the EPI holds with equality).

`@audit:ok` — 2026-05-27 independent honesty audit. Body is a genuine
Gaussian-saturation discharge via
`entropyPower_gaussian_additivity` + `linarith`. The conclusion
`= 0` is **not** a degenerate-definition exploit: it follows from the
genuine equality case of EPI for independent standard normals, with
hypothesis-borne `Z_X, Z_Y ∼ 𝒩(0, 1)` + independence. Referenced by Phase A
A-4-4 (`Common2026/Shannon/EPIStamToBridge.lean:912`, docstring) as the
`s = 1` endpoint connection in the rescale lift; A-4-4's pending `sorry`
is a separate sub-plan, not a defect here. -/
theorem csiszarGap_at_one_eq_zero_of_gaussian_pair
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X Y Z_X Z_Y : Ω → ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hZXZY : IndepFun Z_X Z_Y P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hZY_law : P.map Z_Y = gaussianReal 0 1) :
    csiszarGap X Y Z_X Z_Y P 1 = 0 := by
  unfold csiszarGap
  -- `heatFlowPath2 _ Z _ 1 = Z` for both endpoints.
  have h_sum_funext :
      (heatFlowPath2 X Z_X 1 + heatFlowPath2 Y Z_Y 1)
        = fun ω => Z_X ω + Z_Y ω := by
    funext ω
    simp [heatFlowPath2_one]
  rw [h_sum_funext, heatFlowPath2_one, heatFlowPath2_one]
  -- Gaussian saturation: independent standard normals saturate EPI.
  have h_sat := entropyPower_gaussian_additivity
    P Z_X Z_Y hZX hZY hZXZY 0 0 1 1
    (by norm_num : (1 : ℝ≥0) ≠ 0) (by norm_num : (1 : ℝ≥0) ≠ 0)
    hZX_law hZY_law
  linarith

/-!
### Phase D D-2 — strategy-γ note (statement-only handoff, no Lean theorem)

The original Phase D mini-plan proposed strategy β: an evaluation-point
bridge from `bounded_T_ftc_gaussian` (1-source `gaussianConvolution`
heat-flow path) to `csiszarGap` (2-source `heatFlowPath2` heat-flow path)
via the degeneration `Y := 0`, `Z_Y := 0`. The D-0 honesty check
(`docs/shannon/epi-debruijn-integration-mathlib-inventory.md` §D-0-5)
**rejected strategy β**:

* `Y = 0, Z_Y = 0` makes `heatFlowPath2 0 0 s = 0` pointwise.
* `P.map 0 = Measure.dirac 0`, and
  `entropyPower (Measure.dirac 0) = Real.exp (2 · 0) = 1` (via
  `Common2026/Shannon/DifferentialEntropy.lean:147` `differentialEntropy_dirac`).
* So `csiszarGap X 0 Z_X 0 P s
    = entropyPower (P.map (heatFlowPath2 X Z_X s))
      − entropyPower (P.map (heatFlowPath2 X Z_X s)) − 1
    = -1` (constant in `s`).
* A constant function is **trivially `AntitoneOn`**, so the
  `Y := 0`, `Z_Y := 0` evaluation point of `csiszarGap` carries no
  information about the heat-flow path. This is precisely the
  degenerate-definition-exploitation defect class (CLAUDE.md
  "退化定義の悪用").

Phase D D-2 is therefore downgraded to **strategy γ** (statement-only
handoff): the Phase C-1 output `bounded_T_ftc_gaussian` (1-source
`gaussianConvolution` FTC) is not bridged into the 2-source `csiszarGap`
in this mini-plan. Sister `epi-stam-to-conclusion-plan` Phase A is
expected to construct the 2-source de Bruijn FTC directly along the
`heatFlowPath2` path (using `bounded_T_ftc_gaussian` as a 1-source
reference but not as a literal substitution input). This is a **load-
bearing absence**, not a discharge — recorded as the L-DBD-2-α
retreat-line firing per the mini-plan §"撤退ライン総覧" table.

No Lean theorem is published in this section; this module note is the
entire D-2 deliverable (per the mini-plan §D-2 撤退ライン L-DBD-2-α:
"D-2 statement only"). The D-V verification check confirms no `sorry`
and no `Prop := True` placeholder are introduced (this note is a `/-!
... -/` module-doc block, not a declaration).

`@audit:ok` — 2026-05-27 audit aligned with the D-1 deliverables: this
§D-2 strategy-γ note is an honest module-doc statement (`/-! ... -/`, no
declaration), explicitly retreat-lined to "statement only" per the
mini-plan §D-2 撤退ライン L-DBD-2-α. Sister Phase A's 2-source closure
runs through `csiszarGap_eq_one_source_via_rescale` + the 1-source
`csiszarGap1Source` chain (both `@audit:ok`), bypassing the strategy-β
degenerate-definition exploit that this note documents the rejection of.
-/

/-- **Sister export — Csiszár gap shape contract for `epi-stam-to-conclusion-plan` Phase A**
(Phase D D-4).

The `csiszarGap` (D-1-1) body matches verbatim the lambda body of the
`AntitoneOn` argument of
`Common2026.Shannon.IsStamToEPIScalingHyp`
(`Common2026/Shannon/EPIStamToBridge.lean:210-216`). This `rfl` lemma
exposes that verbatim match so that sister Phase A can `simp` or
`rw [← csiszarGap_shape_for_sister]` to re-express the sister predicate's
internal `AntitoneOn` argument as `csiszarGap`, enabling structural
reasoning about the gap function as a single named entity.

This is a **shape contract only** (`rfl` body); no analytic content. The
sister Phase A is responsible for the actual `AntitoneOn` proof using
Stam + de Bruijn FTC along the heat-flow path.

`@audit:ok` — 2026-05-27 independent honesty audit. Body is `rfl`, a pure
shape contract with no analytic content. Conclusion type is the verbatim
unfolding of `csiszarGap`'s definition — the type ≠ conclusion criterion
holds because the equation `(fun s => csiszarGap …) = (fun s => entropyPower …
- entropyPower … - entropyPower …)` is a definitional witness, not a
`Prop`-level claim about analytic properties. Structurally identical to the
1-source sister `csiszarGap1Source_shape_for_sister` (`:1579`, `@audit:ok`
per Phase A cleanup). -/
theorem csiszarGap_shape_for_sister
    {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
    (fun s : ℝ => csiszarGap X Y Z_X Z_Y P s)
      = (fun s : ℝ =>
          entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
            - entropyPower (P.map (heatFlowPath2 X Z_X s))
            - entropyPower (P.map (heatFlowPath2 Y Z_Y s))) :=
  rfl

/-! ### §13.A-0' — 1-source form alias for `epi-stam-to-conclusion-plan` Phase A

The Phase D 2-source `csiszarGap` body is keyed to `heatFlowPath2 X Z s`
(`s ∈ [0, 1]`, base `√(1-s)·X` is `s`-dependent), which does not align with the
1-source form of de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2`
(`Common2026/Shannon/FisherInfoV2DeBruijn.lean:245`, keyed to
`gaussianConvolution X Z t = X + √t·Z`, base `X` is `t`-independent).
Reparametrizing the 2-source form by `t := s/(1-s)` and pulling out the
scale factor `√(1-s)` yields a 1-source equivalent form whose base is
`t`-independent — the sister Phase A consumes this 1-source form to apply
de Bruijn V2 directly (the per-`t` derivative is now delivered by the
shared lemma `debruijnIdentityV2_holds` carrying
`@residual(wall:debruijn-integration)`; Phase 2.B foundation removed the
inline `derivAt_entropy_eq_half_fisher_v2` field from
`IsRegularDeBruijnHypV2`) without scaling-correction-term cancellation
problems (L-Concl-A-δ avoided at the source).

This subsection is **additive** on top of the Phase D D-1..D-4 deliverables —
none of the existing definitions or theorems above are modified.

Members:

* A-0'-1 `csiszarGap1Source` — 1-source form alias `noncomputable def`,
  body `entropyPower (P.map (X + Y + √t·(Z_X + Z_Y))) − ... − ...`.
* A-0'-2 `csiszarGap_eq_one_source_via_rescale` — equivalence
  `csiszarGap _ s = (1-s) · csiszarGap1Source _ (s/(1-s))` for `s ∈ Set.Ico 0 1`,
  using `entropyPower_map_mul_const` (Phase B-2 lift,
  `Common2026/Shannon/EPIPlumbing.lean:130`). Caller-side absolute continuity
  and entropy-integrand integrability hypotheses are passed as direct lemma
  arguments (honest pass-through, option (b) per the dispatch brief).
* A-0'-3 `csiszarGap1Source_at_zero` — endpoint at `t = 0` reduces to the EPI
  gap for the original `(X, Y)`.
* A-0'-4 `csiszarGap1Source_tendsto_zero_at_infinity_of_gaussian_pair` —
  Gaussian saturation at `t → ∞` (statement-only handoff per mini-plan,
  proof externalized via the named honest hypothesis predicate
  `IsCsiszarGap1SourceTendsToZeroAtInfinity` below; Phase A's closure path
  does not require this lemma in its proof form — the 2-source endpoint
  `s = 1` is discharged by the existing `csiszarGap_at_one_eq_zero_of_gaussian_pair`).
* A-0'-5 `csiszarGap1Source_shape_for_sister` — `rfl` lemma exposing the
  1-source `csiszarGap1Source` body to sister Phase A for structural
  reasoning.
-/

/-- **1-source form alias of the Csiszár scaling gap** (Phase D §13 A-0'-1,
sister `epi-stam-to-conclusion-plan` Phase A consumer).

`csiszarGap1Source X Y Z_X Z_Y P t` is the EPI gap along the 1-source
heat-flow path `Common2026.Shannon.FisherInfoV2.gaussianConvolution _ _ t`
(`= _ + √t · _`, `t ∈ [0, ∞)`):

  `gap_t := entropyPower (P.map (X + Y + √t · (Z_X + Z_Y)))
            − entropyPower (P.map (X + √t · Z_X))
            − entropyPower (P.map (Y + √t · Z_Y))`

The base of each `entropyPower` term is `t`-independent (`X + Y`, `X`, `Y`
respectively), unlike the 2-source `csiszarGap` whose base `√(1-s) · X`
is `s`-dependent. This shape directly matches the conclusion form of
the V2 de Bruijn identity `deBruijn_identity_v2` (Phase 2.B foundation
removed the inline `derivAt_entropy_eq_half_fisher_v2` field, the
identity is now delivered by shared lemma `debruijnIdentityV2_holds`,
`@residual(wall:debruijn-integration)`) keyed to `gaussianConvolution`,
enabling sister Phase A to compute `d/dt gap_t` without
scaling-correction-term cancellation problems (L-Concl-A-δ avoidance).

**Shape contract**: the body matches the conclusion of
`csiszarGap1Source_shape_for_sister` (A-0'-5) verbatim, exposed via `rfl`.

This is a `noncomputable def`, **not** a `Prop`-level staged predicate —
no honesty audit at the predicate level.

`@audit:ok` — Phase A (2026-05-27, `epi-stam-to-conclusion-phaseA-plan`)
completed the sister-side consumption of this alias; A-0' shape contracts
land via `csiszarGap_eq_one_source_via_rescale` (A-0'-2) and the
A-5 chain `isStamToEPIScalingHyp_of_stam_debruijn` in
`Common2026/Shannon/EPIStamToBridge.lean:926`. -/
noncomputable def csiszarGap1Source {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ :=
  entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
    - entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
    - entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))

/-- **Rescale equivalence: 2-source `csiszarGap` ↔ 1-source `csiszarGap1Source`**
(Phase D §13 A-0'-2).

For `s ∈ Set.Ico 0 1`, the 2-source heat-flow path
`heatFlowPath2 X Z s = √(1-s) · X + √s · Z` factors as
`√(1-s) · (X + √(s/(1-s)) · Z) = √(1-s) · gaussianConvolution X Z (s/(1-s))`.
Pulling out the scalar factor `√(1-s)` via `entropyPower_map_mul_const`
(Phase B-2 lift, `Common2026/Shannon/EPIPlumbing.lean:130`,
`entropyPower (μ.map (· * c)) = c² · entropyPower μ`) yields the rescale
equivalence `gap(s) = (1-s) · gap1Source(s/(1-s))`.

**Caller integrability hypothesis (honest pass-through, option (b))**.
`entropyPower_map_mul_const` requires for each `μ ∈ {P.map(X+Y+√t·(Z_X+Z_Y)),
P.map(X+√t·Z_X), P.map(Y+√t·Z_Y)}` (where `t = s/(1-s)`) both
`μ ≪ volume` and `Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume`.
We pass these 6 conditions as direct lemma arguments — honest carrier
hypotheses, no new staged predicate is introduced (per the dispatch brief
A-0'-2 integrability bridge resolution: option (b)).

`@audit:ok` — Phase A A-4 (2026-05-27, `epi-stam-to-conclusion-phaseA-plan`)
completed the consumption of this equivalence in
`csiszarGap_antitoneOn_Icc_zero_one` (`Common2026/Shannon/EPIStamToBridge.lean:893`).
The 6 carrier hypotheses (`h_ac_*`, `h_int_*`) are regularity preconditions,
not load-bearing predicates. -/
theorem csiszarGap_eq_one_source_via_rescale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (h_ac_sum :
      (P.map (fun ω => X ω + Y ω + Real.sqrt (s / (1 - s)) * (Z_X ω + Z_Y ω)))
        ≪ (volume : Measure ℝ))
    (h_ac_X :
      (P.map (fun ω => X ω + Real.sqrt (s / (1 - s)) * Z_X ω))
        ≪ (volume : Measure ℝ))
    (h_ac_Y :
      (P.map (fun ω => Y ω + Real.sqrt (s / (1 - s)) * Z_Y ω))
        ≪ (volume : Measure ℝ))
    (h_int_sum :
      Integrable
        (fun x : ℝ => Real.negMulLog
          (((P.map (fun ω => X ω + Y ω
                + Real.sqrt (s / (1 - s)) * (Z_X ω + Z_Y ω))).rnDeriv volume x).toReal))
        (volume : Measure ℝ))
    (h_int_X :
      Integrable
        (fun x : ℝ => Real.negMulLog
          (((P.map (fun ω => X ω + Real.sqrt (s / (1 - s)) * Z_X ω)).rnDeriv volume x).toReal))
        (volume : Measure ℝ))
    (h_int_Y :
      Integrable
        (fun x : ℝ => Real.negMulLog
          (((P.map (fun ω => Y ω + Real.sqrt (s / (1 - s)) * Z_Y ω)).rnDeriv volume x).toReal))
        (volume : Measure ℝ)) :
    csiszarGap X Y Z_X Z_Y P s
      = (1 - s) * csiszarGap1Source X Y Z_X Z_Y P (s / (1 - s)) := by
  -- Set up the rescale parameter `t = s / (1 - s)` and preliminary facts.
  set t : ℝ := s / (1 - s) with ht_def
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s < 1 := hs.2
  have h_one_sub_s_pos : (0 : ℝ) < 1 - s := by linarith
  have h_one_sub_s_nn : (0 : ℝ) ≤ 1 - s := le_of_lt h_one_sub_s_pos
  have h_one_sub_s_ne : (1 - s : ℝ) ≠ 0 := ne_of_gt h_one_sub_s_pos
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt (1 - s) := Real.sqrt_pos.mpr h_one_sub_s_pos
  have h_sqrt_ne : Real.sqrt (1 - s) ≠ 0 := ne_of_gt h_sqrt_pos
  have h_sqrt_sq : (Real.sqrt (1 - s)) ^ 2 = 1 - s := Real.sq_sqrt h_one_sub_s_nn
  -- The key algebraic identity: `√(1-s) · √t = √s`.
  have ht_nn : (0 : ℝ) ≤ t := by
    rw [ht_def]; exact div_nonneg hs0 h_one_sub_s_nn
  have h_sqrt_mul_t : Real.sqrt (1 - s) * Real.sqrt t = Real.sqrt s := by
    rw [← Real.sqrt_mul h_one_sub_s_nn]
    congr 1
    rw [ht_def]
    field_simp
  -- Helper: for each base function `F : Ω → ℝ` (measurable, X+Y, X, Y),
  -- and noise `N : Ω → ℝ` (measurable, Z_X+Z_Y, Z_X, Z_Y), the rescale identity
  -- `√(1-s)·F + √s·N = √(1-s) · (F + √t·N)` lifts to entropyPower scaling.
  -- We instantiate this 3 times: (X+Y, Z_X+Z_Y), (X, Z_X), (Y, Z_Y).
  have h_meas_XY : Measurable (fun ω => X ω + Y ω) := hX.add hY
  have h_meas_ZXY : Measurable (fun ω => Z_X ω + Z_Y ω) := hZX.add hZY
  have h_meas_fXY : Measurable (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)) :=
    h_meas_XY.add ((measurable_const).mul h_meas_ZXY)
  have h_meas_fX : Measurable (fun ω => X ω + Real.sqrt t * Z_X ω) :=
    hX.add ((measurable_const).mul hZX)
  have h_meas_fY : Measurable (fun ω => Y ω + Real.sqrt t * Z_Y ω) :=
    hY.add ((measurable_const).mul hZY)
  -- The funext rewrites: `heatFlowPath2 _ _ s ω` equals `√(1-s) * (_ + √t * _ ω)`.
  -- Sum branch (the sum-of-paths under `entropyPower`).
  have h_funext_sum :
      (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s)
        = (fun ω => Real.sqrt (1 - s) *
              (X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) := by
    funext ω
    simp only [Pi.add_apply, Common2026.Shannon.heatFlowPath2_apply]
    have h_assoc : Real.sqrt (1 - s) * (Real.sqrt t * (Z_X ω + Z_Y ω))
        = Real.sqrt s * Z_X ω + Real.sqrt s * Z_Y ω := by
      rw [← mul_assoc, h_sqrt_mul_t]; ring
    have h_rhs_expand : Real.sqrt (1 - s) *
            (X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))
          = Real.sqrt (1 - s) * X ω + Real.sqrt (1 - s) * Y ω
              + Real.sqrt (1 - s) * (Real.sqrt t * (Z_X ω + Z_Y ω)) := by ring
    rw [h_rhs_expand, h_assoc]
    ring
  have h_funext_X :
      heatFlowPath2 X Z_X s
        = (fun ω => Real.sqrt (1 - s) * (X ω + Real.sqrt t * Z_X ω)) := by
    funext ω
    simp only [Common2026.Shannon.heatFlowPath2_apply]
    have h_assoc : Real.sqrt (1 - s) * (Real.sqrt t * Z_X ω) = Real.sqrt s * Z_X ω := by
      rw [← mul_assoc, h_sqrt_mul_t]
    have h_rhs_expand : Real.sqrt (1 - s) * (X ω + Real.sqrt t * Z_X ω)
          = Real.sqrt (1 - s) * X ω + Real.sqrt (1 - s) * (Real.sqrt t * Z_X ω) := by ring
    rw [h_rhs_expand, h_assoc]
  have h_funext_Y :
      heatFlowPath2 Y Z_Y s
        = (fun ω => Real.sqrt (1 - s) * (Y ω + Real.sqrt t * Z_Y ω)) := by
    funext ω
    simp only [Common2026.Shannon.heatFlowPath2_apply]
    have h_assoc : Real.sqrt (1 - s) * (Real.sqrt t * Z_Y ω) = Real.sqrt s * Z_Y ω := by
      rw [← mul_assoc, h_sqrt_mul_t]
    have h_rhs_expand : Real.sqrt (1 - s) * (Y ω + Real.sqrt t * Z_Y ω)
          = Real.sqrt (1 - s) * Y ω + Real.sqrt (1 - s) * (Real.sqrt t * Z_Y ω) := by ring
    rw [h_rhs_expand, h_assoc]
  -- Lift each `entropyPower (P.map (heatFlowPath2 _ _ s))` to the 1-source form via
  -- `Measure.map_map` + `entropyPower_map_mul_const`.
  -- The map decomposition: `P.map (fun ω => √(1-s) * f ω) = (P.map f).map (· * √(1-s))`.
  have h_meas_scale : Measurable (fun y : ℝ => y * Real.sqrt (1 - s)) :=
    measurable_id.mul measurable_const
  -- IsProbabilityMeasure instances for the 1-source mapped measures.
  have h_prob_fXY : IsProbabilityMeasure
      (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) :=
    Measure.isProbabilityMeasure_map h_meas_fXY.aemeasurable
  have h_prob_fX : IsProbabilityMeasure
      (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) :=
    Measure.isProbabilityMeasure_map h_meas_fX.aemeasurable
  have h_prob_fY : IsProbabilityMeasure
      (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) :=
    Measure.isProbabilityMeasure_map h_meas_fY.aemeasurable
  -- The key identity per branch: entropyPower scaling.
  -- `P.map (fun ω => √(1-s) * f ω) = (P.map f).map (· * √(1-s))`.
  have h_map_decomp_sum :
      P.map (fun ω => Real.sqrt (1 - s) *
            (X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
        = (P.map (fun ω => X ω + Y ω
            + Real.sqrt t * (Z_X ω + Z_Y ω))).map (fun y => y * Real.sqrt (1 - s)) := by
    have h_comp_eq :
        (fun ω => Real.sqrt (1 - s) *
              (X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
          = (fun y : ℝ => y * Real.sqrt (1 - s)) ∘
              (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)) := by
      funext ω; simp [mul_comm]
    rw [h_comp_eq, ← Measure.map_map h_meas_scale h_meas_fXY]
  have h_map_decomp_X :
      P.map (fun ω => Real.sqrt (1 - s) * (X ω + Real.sqrt t * Z_X ω))
        = (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)).map
            (fun y => y * Real.sqrt (1 - s)) := by
    have h_comp_eq :
        (fun ω => Real.sqrt (1 - s) * (X ω + Real.sqrt t * Z_X ω))
          = (fun y : ℝ => y * Real.sqrt (1 - s)) ∘
              (fun ω => X ω + Real.sqrt t * Z_X ω) := by
      funext ω; simp [mul_comm]
    rw [h_comp_eq, ← Measure.map_map h_meas_scale h_meas_fX]
  have h_map_decomp_Y :
      P.map (fun ω => Real.sqrt (1 - s) * (Y ω + Real.sqrt t * Z_Y ω))
        = (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)).map
            (fun y => y * Real.sqrt (1 - s)) := by
    have h_comp_eq :
        (fun ω => Real.sqrt (1 - s) * (Y ω + Real.sqrt t * Z_Y ω))
          = (fun y : ℝ => y * Real.sqrt (1 - s)) ∘
              (fun ω => Y ω + Real.sqrt t * Z_Y ω) := by
      funext ω; simp [mul_comm]
    rw [h_comp_eq, ← Measure.map_map h_meas_scale h_meas_fY]
  -- Apply `entropyPower_map_mul_const` per branch (`c^2 = (√(1-s))^2 = 1 - s`).
  have h_ep_sum :
      entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
        = (1 - s) * entropyPower
            (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) := by
    rw [h_funext_sum, h_map_decomp_sum,
        entropyPower_map_mul_const h_ac_sum h_sqrt_ne h_int_sum, h_sqrt_sq]
  have h_ep_X :
      entropyPower (P.map (heatFlowPath2 X Z_X s))
        = (1 - s) * entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) := by
    rw [h_funext_X, h_map_decomp_X,
        entropyPower_map_mul_const h_ac_X h_sqrt_ne h_int_X, h_sqrt_sq]
  have h_ep_Y :
      entropyPower (P.map (heatFlowPath2 Y Z_Y s))
        = (1 - s) * entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) := by
    rw [h_funext_Y, h_map_decomp_Y,
        entropyPower_map_mul_const h_ac_Y h_sqrt_ne h_int_Y, h_sqrt_sq]
  -- Combine.
  unfold csiszarGap csiszarGap1Source
  rw [h_ep_sum, h_ep_X, h_ep_Y]
  ring

/-- **Endpoint at `t = 0`** (Phase D §13 A-0'-3). The 1-source Csiszár gap
at the path start reduces to the EPI gap for the original `(X, Y)` (since
`√0 · _ = 0` and `X + 0 = X`).

`@audit:ok` — Phase A (2026-05-27, `epi-stam-to-conclusion-phaseA-plan`)
consumed this endpoint identification in the antitonicity chain
(`Common2026/Shannon/EPIStamToBridge.lean` A-3/A-4); body is a verbatim
`Real.sqrt 0 = 0` reduction. -/
theorem csiszarGap1Source_at_zero {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
    csiszarGap1Source X Y Z_X Z_Y P 0
      = entropyPower (P.map (fun ω => X ω + Y ω))
        - entropyPower (P.map X) - entropyPower (P.map Y) := by
  unfold csiszarGap1Source
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

-- (deleted 2026-05-28, Cluster C Tier-2 migration `epi-stam-cluster-c-sorry-migration-plan`,
-- task 3α-4) The `def IsCsiszarGap1SourceTendsToZeroAtInfinity X Y Z_X Z_Y P`
-- (1-source Csiszár tail bound `… → Tendsto (csiszarGap1Source …) atTop (𝓝 0)`)
-- was removed outright: it had **0 active consumers** (only this declaration +
-- a docstring mention). The sister Phase A closure path uses the rescale route
-- through `csiszarGap_at_one_eq_zero_of_gaussian_pair`, not this `Tendsto … atTop`
-- assertion. If a future direct-1-source-endpoint path is adopted, re-introduce
-- the tail bound as a shared sorry lemma `@residual(wall:csiszar)` rather than a
-- load-bearing predicate. (Former docstring + Cover-Thomas Csiszár tail-bound
-- narrative preserved in git history at this commit's parent.)

/-- **1-source Csiszár gap shape contract for `epi-stam-to-conclusion-plan` Phase A**
(Phase D §13 A-0'-5).

The `csiszarGap1Source` (A-0'-1) body matches verbatim the shape used by
sister Phase A's 1-source derivative computation (sister A-2/A-3). This
`rfl` lemma exposes the verbatim match so that sister Phase A can
`simp only [← csiszarGap1Source_shape_for_sister]` to re-express its
local working term as the named `csiszarGap1Source`.

This is a **shape contract only** (`rfl` body); no analytic content. Sister
Phase A is responsible for the actual `AntitoneOn` proof on the 1-source
form using de Bruijn V2 + Stam inequality, then lifts to the 2-source form
via `csiszarGap_eq_one_source_via_rescale` (A-0'-2).

`@audit:ok` — Phase A (2026-05-27, `epi-stam-to-conclusion-phaseA-plan`)
consumed this shape contract in sister derivative computations
(`Common2026/Shannon/EPIStamToBridge.lean` A-2/A-3); body is `rfl`. -/
theorem csiszarGap1Source_shape_for_sister
    {Ω : Type*} [MeasurableSpace Ω]
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) :
    (fun t : ℝ => csiszarGap1Source X Y Z_X Z_Y P t)
      = (fun t : ℝ =>
          entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)))
            - entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            - entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))) :=
  rfl

end InformationTheory.Shannon.EPIL3Integration
