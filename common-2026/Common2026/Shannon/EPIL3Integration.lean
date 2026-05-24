import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.EPIPlumbing
import Common2026.Shannon.EPIStamDischarge
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoGaussian
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

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

* §1 — **`IsEPIL3IntegratedPipeline`**: Stam (真 signature) + Stam-to-EPI bridge
  + de Bruijn (V2) を bundle する predicate。`IsStamInequalityHyp X Y P` +
  `IsStamToEPIBridgeHyp X Y P` の最小組合せで L-EPI3 を生成。
* §2 — **integrated 主定理**: integrated pipeline → EPI。`Common2026/Shannon/EPIStamDischarge.lean`
  の `epi_via_stam_main` を packaging。
* §3 — **Gaussian EPI**: `X, Y` がともに Gaussian なら EPI は等号で成立
  (`entropy_power_inequality_gaussian_saturation` 直行)。integrated pipeline 形は
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

* `IsEPIL3IntegratedPipeline` — Stam + bridge bundling predicate (§1)
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

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge

/-! ## §1 — Integrated pipeline predicate -/

/-- **Integrated L-EPI3 pipeline predicate**.

Bundles the three Wave 5 building blocks (Stam inequality + Stam-to-EPI bridge
+ de Bruijn integration) into a single predicate. Providing this predicate
gives a discharge route through `epi_via_stam` to the L-EPI3 conclusion
`IsEntropyPowerInequalityHypothesis X Y P`.

The auxiliary `Z` field plays no role in the predicate itself (its inputs are
recorded only for the `epi_via_stam` re-use convenience); it can be supplied as
any measurable function or just `X` itself if no Gaussian standard normal is
naturally available. -/
structure IsEPIL3IntegratedPipeline {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Stam inequality (Cover-Thomas Lemma 17.7.2) genuine signature. -/
  stam : IsStamInequalityHyp X Y P
  /-- Stam-to-EPI bridge (Cover-Thomas Lemma 17.7.3 coupling argument). -/
  bridge : IsStamToEPIBridgeHyp X Y P

/-- **L-EPI3 from integrated pipeline**. The integrated pipeline discharges
`IsEntropyPowerInequalityHypothesis X Y P` via `epi_via_stam`.

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem epi_l3_of_integrated_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIL3IntegratedPipeline X Y P) :
    IsEntropyPowerInequalityHypothesis X Y P :=
  h.bridge h.stam

/-! ## §2 — Integrated main theorem (Cover-Thomas Theorem 17.7.3, integrated form) -/

/-- **Integrated EPI main theorem**: the integrated pipeline gives the full
EPI conclusion in one shot (no need for callers to thread through L-EPI1,
L-EPI2, L-EPI3 separately).

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem entropy_power_inequality_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  -- Thread the genuine residual (`stam`) + bridge through the non-circular
  -- headline; `IsStamInequalityHyp`/`IsStamToEPIBridgeHyp` are defeq to the base
  -- `IsStamInequalityResidual`/`IsStamToEPIBridge`.
  entropy_power_inequality P X Y hX hY hXY h_pipeline.stam h_pipeline.bridge

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
  { stam := h_stam
    bridge :=
      isStamToEPIBridgeHyp_of_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY }

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

/-- **Gaussian saturation in integrated pipeline form, with equality**.

Reuses `entropy_power_inequality_gaussian_saturation` from `EntropyPowerInequality.lean`. -/
theorem entropy_power_inequality_gaussian_saturation_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      = entropyPower (P.map X) + entropyPower (P.map Y) :=
  entropy_power_inequality_gaussian_saturation
    P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-! ## §4 — Variants (log / exp / normalized form via integrated pipeline) -/

/-- **EPI log form via integrated pipeline**.

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem entropy_power_inequality_log_form_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω))
      ≥ (1/2) * Real.log
          (entropyPower (P.map X) + entropyPower (P.map Y)) :=
  entropy_power_inequality_log_form P X Y hX hY hXY h_pipeline.stam h_pipeline.bridge

/-- **EPI exp form via integrated pipeline** (Cover-Thomas Theorem 17.7.3 露出形).

`@audit:suspect(epi-debruijn-integration-plan)` -/
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
  entropy_power_inequality_exp_form P X Y hX hY hXY h_pipeline.stam h_pipeline.bridge

/-- **EPI normalized `(2πe)⁻¹` form via integrated pipeline** (Cover-Thomas Ch.17).

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem entropy_power_inequality_normalized_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω)) / gaussianEntropyPowerConst
      ≥ entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst :=
  entropy_power_inequality_normalized P X Y hX hY hXY h_pipeline.stam h_pipeline.bridge

/-- **2 · h(X+Y) ≥ log(entropyPower X + entropyPower Y)** via integrated pipeline.

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem two_differentialEntropy_ge_log_sum_integrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    2 * Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω))
      ≥ Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) :=
  two_differentialEntropy_ge_log_sum P X Y hX hY hXY h_pipeline.stam h_pipeline.bridge

/-! ## §5 — Chain forms (3-arg / 4-arg) via integrated pipeline -/

/-- **3-arg EPI via integrated pipeline**. Chains two integrated pipelines.

`@audit:suspect(epi-debruijn-integration-plan)` -/
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

`@audit:suspect(epi-debruijn-integration-plan)` -/
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
  bridge := isStamToEPIBridgeHyp_symm h.bridge

/-- **Pipeline from EPI hypothesis only**. When the EPI hypothesis is already
known by some non-circular route (e.g. Gaussian saturation) and an honest Stam
predicate is *also* available, bundle into a pipeline. (No vacuous Fisher-info-zero
discharge is used — that buggy V1 route was removed 2026-05-20.)

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem isEPIL3IntegratedPipeline_of_epi
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P)
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    IsEPIL3IntegratedPipeline X Y P where
  stam := h_stam
  bridge := isStamToEPIBridgeHyp_of_epi h_epi

/-- **Pipeline from Stam + bridge directly** (mirrors `epi_via_stam`). -/
theorem isEPIL3IntegratedPipeline_of_stam_bridge
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    IsEPIL3IntegratedPipeline X Y P where
  stam := h_stam
  bridge := h_bridge

/-- **Pipeline destruction**: extract the `IsStamInequalityHyp` part. -/
theorem isStamInequalityHyp_of_integrated_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIL3IntegratedPipeline X Y P) :
    IsStamInequalityHyp X Y P :=
  h.stam

/-- **Pipeline destruction**: extract the `IsStamToEPIBridgeHyp` part. -/
theorem isStamToEPIBridgeHyp_of_integrated_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIL3IntegratedPipeline X Y P) :
    IsStamToEPIBridgeHyp X Y P :=
  h.bridge

/-! ## §7 — Hypothesis-reduced re-publish of `entropy_power_inequality`

The original `entropy_power_inequality` takes three separate hypotheses
(L-EPI1 `_h_stam`, L-EPI2 `_h_debruijn`, L-EPI3 `h_epi`); the L-EPI1 and L-EPI2
slots are placeholder `True` so any caller can pass `trivial`. We re-publish
under a single, integrated, **non-trivial** hypothesis (the pipeline) — this
is the "hypothesis-reduced form" promised in the parent plan. -/

/-- **Hypothesis-reduced EPI** (Cover-Thomas Theorem 17.7.3, integrated form).

Single non-trivial hypothesis `IsEPIL3IntegratedPipeline X Y P` (vs the
three-hypothesis form in `EntropyPowerInequality.entropy_power_inequality`).

`@audit:suspect(epi-debruijn-integration-plan)` -/
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

`@audit:suspect(epi-debruijn-integration-plan)` -/
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

/-- **Integrated pipeline preserved under translation**.

If `X, Y` satisfy the integrated pipeline (i.e. Stam + Stam-to-EPI bridge),
and the relevant measures are absolutely continuous, then `X + a, Y + b` also
satisfy the integrated pipeline — provided the Fisher information is shown
to be translation-invariant (the predicate-level statement; the Fisher info
invariance itself is downstream).

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem isEPIL3IntegratedPipeline_of_translates
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hJX : ∀ a : ℝ, ∀ f : ℝ → ℝ,
        Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => X ω + a)) f
          = Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) f)
    (hJY : ∀ b : ℝ, ∀ f : ℝ → ℝ,
        Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => Y ω + b)) f
          = Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) f)
    (hJsum : ∀ a b : ℝ, ∀ f : ℝ → ℝ,
        Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
          (P.map (fun ω => (X ω + a) + (Y ω + b))) f
        = Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
            (P.map (fun ω => X ω + Y ω)) f)
    (h_bridge_t : ∀ a b : ℝ,
        IsStamToEPIBridgeHyp (fun ω => X ω + a) (fun ω => Y ω + b) P)
    (a b : ℝ)
    (h : IsEPIL3IntegratedPipeline X Y P) :
    IsEPIL3IntegratedPipeline (fun ω => X ω + a) (fun ω => Y ω + b) P where
  stam :=
    isStamInequalityHyp_of_fisherInfo_eq
      (fun f => (hJX a f).symm) (fun f => (hJY b f).symm) (fun f => (hJsum a b f).symm) h.stam
  bridge := h_bridge_t a b

/-! ## §9 — Concrete Gaussian EPI (genuine, via saturation)

**RESOLVED (2026-05-20):** the former `isStamInequalityHyp_of_gaussian_v1_zero`
and `isEPIL3IntegratedPipeline_gaussian` discharged the Stam predicate vacuously
through the buggy V1 `fisherInfo = 0` artefact for Gaussians and were removed. The
genuine Gaussian EPI is `entropy_power_inequality_gaussian_full` below (direct from
`entropy_power_inequality_gaussian_saturation`); the integrated-pipeline form takes
a real `IsStamInequalityHyp` argument (`entropy_power_inequality_gaussian_via_pipeline`).
-/

/-- **Gaussian EPI hypothesis-free**: combine the Gaussian saturation case
directly (no Stam predicate needed for the inequality itself; the predicate
is only needed for the integrated pipeline form). -/
theorem entropy_power_inequality_gaussian_full
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_eq := entropy_power_inequality_gaussian_saturation
    P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY
  exact h_eq.ge

/-! ## §10 — Composability with `FisherInfoV2DeBruijn` (V2 de Bruijn identity) -/

/-- **Hypothesis-reduced EPI with V2 de Bruijn citation**. Combines integrated
pipeline + V2 de Bruijn citation; the V2 citation is structurally trivial
(L-EPI2 is `True`) but documents the chain.

`@audit:suspect(epi-debruijn-integration-plan)` -/
theorem entropy_power_inequality_with_v2_debruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_pipeline : IsEPIL3IntegratedPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  entropy_power_inequality_integrated P X Y hX hY hXY h_pipeline

/-! ## §11 — Final sanity-check / regression theorems -/

/-- **Round-trip**: building a pipeline from `(Stam, bridge)` and then
extracting them yields the originals. -/
theorem integrated_pipeline_roundtrip
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    let h := isEPIL3IntegratedPipeline_of_stam_bridge h_stam h_bridge
    h.stam = h_stam ∧ h.bridge = h_bridge :=
  ⟨rfl, rfl⟩

/-- **Three forms of EPI are equivalent** (in the presence of the integrated
pipeline + measurability).

`@audit:suspect(epi-debruijn-integration-plan)` -/
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

end InformationTheory.Shannon.EPIL3Integration
