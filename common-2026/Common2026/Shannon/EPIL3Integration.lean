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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

/-! ## §12 — `epi-debruijn-integration-plan` Phase B/C/D contributions

This section contributes the **family-level de Bruijn lift** (Phase B) and the
**bounded-T Gaussian FTC application** (Phase C) called for by
`docs/shannon/epi-debruijn-integration-plan.md`, together with the **honest
load-bearing predicate** `IsHeatFlowFamilyHyp` that externalizes the
regularity facts which Mathlib does not provide. A second predicate
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
   genuine density witnesses. The audit tag is now
   `@audit:staged(epi-debruijn-integration)` (load-bearing honest, not a
   defect). The standalone Gaussian-case statements below
   (`bounded_T_ftc_gaussian`) still bypass the predicate because the genuine
   bridge from the bounded-T identity to a `∃ fPath` witness is sister-plan
   responsibility (`epi-debruijn-integration-plan.md` Phase B/C/D).

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

3. The 14 `@audit:suspect(epi-debruijn-integration-plan)` tags in §1–§11 are
   **not** downgraded by this section. Those tags reflect that the integrated
   pipeline's `bridge : IsStamToEPIBridgeHyp` field is load-bearing (Csiszár
   scaling argument, Cover-Thomas Lemma 17.7.3), and that bridge is sister-plan
   responsibility (`epi-stam-to-conclusion-plan.md`). The de Bruijn integration
   identity is the *input* to Csiszár scaling, not its discharge, so producing
   genuine de Bruijn machinery (this section) does not retire those tags. The
   honest downgrade target for the 14 tags is
   `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` once the bridge is
   genuine; that downgrade is **not performed here** because the bridge is
   still load-bearing as of this commit.

`@audit:suspect(epi-debruijn-integration-plan)` — section header carries the same
plan slug so that grep for the slug surfaces these notes alongside the 14 tags.
-/

/-- **Family-level heat-flow regularity hypothesis** (Phase B-5, honest
load-bearing).

`IsHeatFlowFamilyHyp X Z P` packages, for general (non-Gaussian) `X`, the
per-time-point V2 de Bruijn regularity witness along the heat-flow path
`s ↦ X + √s · Z`, together with a smooth density path. This is a **load-bearing
honest hypothesis** (type ≠ conclusion, no circular discharge); the only
hypothesis-free constructor produced in this file is the Gaussian case
(`isHeatFlowFamilyHyp_of_gaussian`).

For Gaussian `X` the witness is `fun t => gaussianPDFReal m (v + ⟨t, _⟩)`; for
general `X` no Mathlib machinery currently produces the required
`HasDerivAt` family-level statement and so this hypothesis externalizes that
regularity.

`@audit:staged(epi-heat-flow-family-regularity)` — honest load-bearing
hypothesis, not a discharge. -/
structure IsHeatFlowFamilyHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Type where
  /-- `Z` is the standard normal driving the heat flow. -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- Smooth density witness along the heat-flow path (`fPath t` should be the
  density of `P.map (X + √t · Z)`). -/
  fPath : ℝ → ℝ → ℝ
  /-- For each `t > 0` the V2 de Bruijn regularity holds with `density_t = fPath t`. -/
  reg_at : ∀ t : ℝ, 0 < t →
    HasDerivAt
      (fun s => Common2026.Shannon.differentialEntropy
                  (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z s)))
      ((1/2) * Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal (fPath t))
      t

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

/-! ### Phase B helpers — `gaussianConvolution` boundary -/

/-- `gaussianConvolution X Z 0 = X` pointwise (uses `Real.sqrt 0 = 0`). -/
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
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) :
    ∀ t : ℝ, 0 < t →
      Common2026.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t := by
  intro t ht
  refine
    { Z_law := hZ_law
      density_t := gaussianPDFReal m (v + ⟨t, ht.le⟩)
      derivAt_entropy_eq_half_fisher_v2 := ?_ }
  -- The V2 de Bruijn Gaussian discharge gives the derivative with the V2
  -- *measure*-keyed Fisher info; convert to the density-keyed shape required
  -- by `IsRegularDeBruijnHypV2`.
  have h_deriv := Common2026.Shannon.FisherInfoV2.deBruijn_identity_v2_gaussian
    X Z hX hZ hXZ hv hX_law hZ_law ht
  -- `fisherInfoOfMeasureV2Real μ f = fisherInfoOfDensityReal f` by `rfl`.
  -- (The measure argument is purely a labelling device in the V2 API.)
  have h_eq :
      Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2Real
          (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z t))
          (gaussianPDFReal m (v + ⟨t, ht.le⟩))
        = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            (gaussianPDFReal m (v + ⟨t, ht.le⟩)) := rfl
  rw [h_eq] at h_deriv
  exact h_deriv

/-- **Family-level heat-flow regularity from a Gaussian** (Phase B-5,
hypothesis-free Gaussian constructor).

For Gaussian `X` and standard normal `Z` with the usual independence,
`IsHeatFlowFamilyHyp X Z P` admits a hypothesis-free witness, where the
density path is `fun t x => gaussianPDFReal m (v + ⟨t, _⟩) x`. -/
noncomputable def isHeatFlowFamilyHyp_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1) :
    IsHeatFlowFamilyHyp X Z P where
  Z_law := hZ_law
  fPath := fun t => gaussianPDFReal m
            (v + ⟨max t 0, le_max_right _ _⟩)
  reg_at t ht := by
    -- For `t > 0`, `max t 0 = t`.
    have h_max : max t 0 = t := max_eq_left ht.le
    -- The V2 de Bruijn Gaussian discharge gives the derivative.
    have h_deriv := Common2026.Shannon.FisherInfoV2.deBruijn_identity_v2_gaussian
      X Z hX hZ hXZ hv hX_law hZ_law ht
    -- `fisherInfoOfMeasureV2Real μ f = fisherInfoOfDensityReal f` by `rfl`.
    have h_eq :
        Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2Real
            (P.map (Common2026.Shannon.FisherInfoV2.gaussianConvolution X Z t))
            (gaussianPDFReal m (v + ⟨t, ht.le⟩))
          = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              (gaussianPDFReal m (v + ⟨t, ht.le⟩)) := rfl
    rw [h_eq] at h_deriv
    -- Massage `⟨max t 0, ...⟩` to `⟨t, ht.le⟩` using `h_max`.
    have h_subt :
        gaussianPDFReal m
            (v + ⟨max t 0, le_max_right _ _⟩)
        = gaussianPDFReal m (v + ⟨t, ht.le⟩) := by
      congr 2
      exact Subtype.ext h_max
    rw [h_subt]
    exact h_deriv

/-! ### Phase C-3 — Gaussian closed-form entropy at the heat-flow boundary -/

/-- **Gaussian heat-flow entropy boundary value at `T`** for `T ≥ 0`. -/
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

`@audit:suspect(epi-debruijn-integration-plan)` — honest bounded-T discharge,
unbounded `T → ∞` lift is a pending plan-level task (the previously intended
`IsDeBruijnTailHyp` externalization was retracted by independent audit; see
the §12 honesty notes and the retraction comment in the structure-definition
area). -/
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

As discussed in §12 honesty note 3, the 14 `@audit:suspect(epi-debruijn-integration-plan)`
tags in §1–§11 cannot be downgraded by this Phase D — the
`IsStamToEPIBridgeHyp` field of `IsEPIL3IntegratedPipeline` is the sister-plan
discharge target (Csiszár scaling, Cover-Thomas Lemma 17.7.3). This file's
contributions (Phase B-4/B-5/C-1/C-4 above) are the de Bruijn-side honest
inputs to that scaling argument; the bridge itself remains load-bearing as of
this commit.

Honest downgrade plan once `epi-stam-to-conclusion-plan` lands:

  `@audit:suspect(epi-debruijn-integration-plan)`
    → `@audit:closed-by-successor(epi-stam-to-conclusion-plan)`

(See `docs/audit/audit-tags.md` for the `closed-by-successor` semantics.) -/

end InformationTheory.Shannon.EPIL3Integration
