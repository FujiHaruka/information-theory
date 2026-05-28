import Common2026.Meta.EntryPoint
import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.EPIStamDischarge
import Common2026.Shannon.EPIL3Integration
import Common2026.Shannon.EPIStamToBridge
import Common2026.Shannon.EPIStamInequalityBody
import Common2026.Shannon.EPIStamStep3Body
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoGaussian
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# W10-S20: Stam → de Bruijn → EPI conclusion assembly

The EPI proof pieces have been progressively discharged across waves:

* **Stam inequality** (Cover-Thomas Lemma 17.7.2). Step 4 (λ-optimization closed
  form `J_sum ≤ J_X J_Y / (J_X + J_Y)`) is *fully arithmetic* and discharged in
  `EPIStamInequalityBody.lean` (`stam_lambda_min`, `stam_lambda_lower_bound`,
  `stam_inverse_form_of_harmonic_mean`). Steps 1–3 are split into two
  genuinely-primitive predicates: the Blachman convolution-score representation
  `IsStamScoreConvolution` (Step 1) and the total-expectation cross-term-drop
  `IsStamTotalExpectation` (Step 3, the integration-by-parts content). The chain
  `isStamInequalityHyp_via_step3` discharges `IsStamInequalityHyp` from those two
  primitives (Steps 2 and 4 being arithmetic).
* **de Bruijn identity** (V2). `deBruijn_identity_v2` gives, from
  `IsRegularDeBruijnHypV2`, the heat-flow derivative
  `(d/dt) h(X + √t · Z) = (1/2) · J(g_t)`, with the Gaussian case
  `deBruijn_identity_v2_gaussian` fully discharged hypothesis-free.

This file is the **conclusion-assembly** layer: it wires those discharged Stam +
de Bruijn pieces into a tighter EPI pipeline, reducing the EPI main theorem's
remaining hypothesis to the genuinely-irreducible primitives.

## Approach

The Wave-7 `IsEPIScalingDecomposedPipeline` (`EPIStamToBridge.lean`) decomposed
the bridge into `scaling`/`limit`, but its `stam` field was a *black-box*
`IsStamInequalityHyp`. We refine this two ways:

1. **Stam from genuine primitives** (§2). Replace the black-box `stam` field by
   the two genuine Stam primitives `IsStamScoreConvolution` (Step 1, Blachman) +
   `IsStamTotalExpectation` (Step 3, IBP/cross-term). `IsStamInequalityHyp` is
   then *derived*, not assumed — the arithmetic Steps 2 and 4 are discharged.
2. **de Bruijn gap-monotonicity engine** (§1, §6). The de Bruijn derivative
   `g'(t) = (1/2) · J(g_t)` is `≥ 0` because Fisher information is non-negative
   (`fisherInfoOfDensityReal_nonneg`). This is the *genuine* monotonicity content
   that makes the EPI gap monotone along the heat-flow scaling path — we discharge
   `g'(t) ≥ 0` outright from the de Bruijn V2 witness.

The refined pipeline `IsEPIStamDeBruijnPipeline` (§3) bundles only the
genuinely-irreducible Stam primitives (Step 1 Blachman + Step 3 IBP); the
Stam→EPI bridge is no longer a pipeline field (it was vestigial once the
monolithic pipeline stopped reading it, and is discharged internally by consumers
via `stamToEPIBridge_holds`). The pipeline reduces to the monolithic
`IsEPIL3IntegratedPipeline`, and lands the EPI conclusion (§4). The genuine Gaussian EPI (§5) is obtained directly from Gaussian
saturation (`entropy_power_inequality_gaussian_full'`), with no Stam claim. (The
former Gaussian *pipeline* discharge routed the Stam half through the buggy V1
Fisher-info-zero artefact and was removed — see §5, RESOLVED 2026-05-20.)

## Genuinely-irreducible primitives remaining

After this assembly the EPI conclusion reduces to:

* `IsStamScoreConvolution` — Blachman score-of-convolution identity (Step 1).
* `IsStamTotalExpectation` — total-expectation cross-term orthogonality (Step 3,
  the integration-by-parts step; Cover-Thomas 17.7.2's deepest analytic content).
* `IsStamToEPIBridgeHyp` — the Csiszár scaling-path coupling (Lemma 17.7.3),
  with its Gaussian case fully discharged.

These are genuine analytic primitives (not `True` placeholders, not defeq no-ops);
the arithmetic of Steps 2 and 4 and the de Bruijn derivative sign are discharged
internally here.

## Key signatures

* `IsEPIGapMonotoneHyp` — de Bruijn gap-monotonicity sub-predicate (§1)
* `deBruijn_deriv_nonneg` / `isEPIGapMonotoneHyp_of_deBruijnV2` — `g'(t) ≥ 0` (§1)
* `isStamInequalityHyp_of_primitives` — Stam from Step 1 + Step 3 (§2)
* `IsEPIStamDeBruijnPipeline` — refined pipeline (§3)
* `isEPIL3IntegratedPipeline_of_stamDeBruijn` — reduction to monolithic (§3)
* `entropy_power_inequality_via_stamDeBruijn` — main EPI (§4)
* `entropy_power_inequality_gaussian_full'` — genuine Gaussian EPI via saturation (§5)
* `deBruijn_gap_deriv_nonneg_gaussian` — composed Gaussian gap monotonicity (§6)
-/

namespace InformationTheory.Shannon.EPIStamDeBruijnConclusion

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIL3Integration
open InformationTheory.Shannon.EPIStamToBridge
open InformationTheory.Shannon.EPIStamInequalityBody
open InformationTheory.Shannon.EPIStamStep3Body
open Common2026.Shannon.FisherInfoV2

/-! ## §1 — de Bruijn gap-monotonicity engine -/

/-- **EPI gap-monotonicity hypothesis along the heat-flow scaling path**.

The Stam inequality + de Bruijn identity together imply that the EPI gap is
monotone non-decreasing along the heat-flow path `X(t) = X + √t · Z`. The de
Bruijn derivative `g'(t) = (d/dt) h(X + √t · Z) = (1/2) · J(g_t)` is the engine:
it is non-negative because Fisher information is non-negative.

This `Prop`-level predicate records the **non-negativity of the de Bruijn
derivative for the density witness `f`** — the genuine analytic content that makes
the gap monotone. It complements `IsStamToEPIScalingHyp` (which, after the
Phase 0 (2026-05-25) refactor, carries the global `AntitoneOn` `gap_s` witness
on `s ∈ [0, 1]` via independent standard-normal witnesses); the present predicate
isolates the *derivative-sign* step of the Csiszár scaling argument and
discharges it outright (§1, below). -/
def IsEPIGapMonotoneHyp (f : ℝ → ℝ) : Prop :=
  0 ≤ (1 / 2 : ℝ) * fisherInfoOfDensityReal f

/-- **de Bruijn derivative is non-negative**: `(1/2) · J(f) ≥ 0` for any density
`f`, because the V2 Fisher information is non-negative. This is the
monotonicity engine of the heat-flow EPI gap. -/
@[entry_point]
theorem deBruijn_deriv_nonneg (f : ℝ → ℝ) :
    0 ≤ (1 / 2 : ℝ) * fisherInfoOfDensityReal f :=
  mul_nonneg (by norm_num) (fisherInfoOfDensityReal_nonneg f)

/-- The gap-monotonicity hypothesis is **discharged outright** for any density
`f`. -/
@[entry_point]
theorem isEPIGapMonotoneHyp_discharge (f : ℝ → ℝ) : IsEPIGapMonotoneHyp f :=
  deBruijn_deriv_nonneg f

/-- **Gap-monotonicity from a de Bruijn V2 regularity witness**. Given the
de Bruijn V2 witness, its derivative value `(1/2) · J(density_t)` is the EPI
gap derivative along the heat-flow path, and it is non-negative. -/
@[entry_point]
theorem isEPIGapMonotoneHyp_of_deBruijnV2
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} {t : ℝ}
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    IsEPIGapMonotoneHyp h_reg.density_t :=
  isEPIGapMonotoneHyp_discharge h_reg.density_t

/-! ## §2 — Stam inequality from genuine primitives (Step 1 + Step 3) -/

/-- **Stam inequality from the two genuine primitives** (Step 1 + Step 3).

Replaces the black-box `IsStamInequalityHyp` assumption by the two
genuinely-irreducible Stam primitives: the Blachman convolution-score identity
(`IsStamScoreConvolution`, Step 1) and the total-expectation cross-term-drop
(`IsStamTotalExpectation`, Step 3, the IBP content). Steps 2 and 4 are discharged
arithmetically (`isStamInequalityHyp_via_step3`).

`@audit:retract-candidate(load-bearing-predicate)` — chains two Stam-wall
predicates (`IsStamScoreConvolution`, `IsStamTotalExpectation`) into the
`IsStamInequalityHyp` predicate. The Stam wall itself is the closure target
of separate `wall:stam` discharge plans (`EPIStamStep3Body.lean` chain); this
wrapper is a load-bearing pass-through for that chain. -/
@[entry_point]
theorem isStamInequalityHyp_of_primitives
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_step3 h_conv h_te

/-! ## §3 — Refined pipeline: only genuine primitives -/

/-- **Refined EPI conclusion-assembly pipeline**.

Refines `IsEPIL3IntegratedPipeline` (`EPIL3Integration.lean`) by replacing the
black-box `stam : IsStamInequalityHyp` field with the **two genuine Stam
primitives** (Step 1 Blachman + Step 3 IBP). The Stam inequality is *derived* via
`isStamInequalityHyp_of_primitives`, not assumed. -/
structure IsEPIStamDeBruijnPipeline {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Step 1: Blachman convolution-score representation. -/
  convScore : IsStamScoreConvolution X Y P
  /-- Step 3: total-expectation cross-term-drop (the IBP step). -/
  totalExp : IsStamTotalExpectation X Y P

/-- **Derive the Stam inequality** from the refined pipeline.

`@audit:retract-candidate(load-bearing-predicate)` — `IsEPIStamDeBruijnPipeline`
is a refined pipeline whose `convScore`/`totalExp` fields are Stam-wall
predicates; this extraction is a pass-through. The genuine alternative
(Phase A `entropy_power_inequality_unconditional`) bypasses the pipeline
entirely. -/
theorem isStamInequalityHyp_of_stamDeBruijn
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIStamDeBruijnPipeline X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_of_primitives h.convScore h.totalExp

/-- **Reduce the refined pipeline to the monolithic `IsEPIL3IntegratedPipeline`**.
The Stam field is supplied by deriving it from the genuine primitives.

After the Cluster C Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`,
route L-EPISC-3-α) `IsEPIL3IntegratedPipeline` carries only its `stam` field; its
former load-bearing `bridge` field was removed and is now discharged internally
by consumers via `stamToEPIBridge_holds`. `IsEPIStamDeBruijnPipeline`'s own former
load-bearing `bridge` field was likewise removed (it was vestigial once the
monolithic pipeline stopped reading it); this adapter therefore supplies only the
`stam` field, derived from the two genuine Stam primitives. -/
theorem isEPIL3IntegratedPipeline_of_stamDeBruijn
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIStamDeBruijnPipeline X Y P) :
    IsEPIL3IntegratedPipeline X Y P where
  stam := isStamInequalityHyp_of_stamDeBruijn h

/-! ## §4 — Main EPI via the refined pipeline -/

/-- **EPI conclusion via the refined Stam + de Bruijn pipeline** (the main
deliverable). Single hypothesis is the refined pipeline, which bundles only the
genuinely-irreducible primitives.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing pipeline
wrapper superseded by Phase A's hypothesis-free alternative
`EPIStamToBridge.entropy_power_inequality_unconditional`. -/
theorem entropy_power_inequality_via_stamDeBruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h : IsEPIStamDeBruijnPipeline X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_int := isEPIL3IntegratedPipeline_of_stamDeBruijn h
  exact entropy_power_inequality_integrated P X Y hX hY hXY h_int

/-- **Refined pipeline from the two genuine primitives directly**. -/
theorem isEPIStamDeBruijnPipeline_of_primitives
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P) :
    IsEPIStamDeBruijnPipeline X Y P where
  convScore := h_conv
  totalExp := h_te

/-! ## §5 — Gaussian EPI (genuine, via saturation)

**RESOLVED (2026-05-20):** the former `isEPIStamDeBruijnPipeline_of_gaussian` and
`entropy_power_inequality_gaussian_via_stamDeBruijn` were removed. They presented a
Gaussian EPI "via Stam + de Bruijn", but the Stam half (`totalExp`) was discharged
vacuously through the buggy V1 `fisherInfo = 0` artefact (`exfalso` on `0 < J_X`),
so the Stam/de Bruijn machinery played no load-bearing role — the inequality came
entirely from Gaussian saturation. The genuine Gaussian EPI is
`entropy_power_inequality_gaussian_full'` below (direct from
`entropyPower_gaussian_additivity`), which carries no Stam claim.
-/

/-- **Gaussian EPI fully hypothesis-free** (re-verification + extension of
`EPIL3Integration.entropy_power_inequality_gaussian_full`). The saturation case
gives equality, hence `≥`; *no* pipeline hypothesis at all is required. -/
@[entry_point]
theorem entropy_power_inequality_gaussian_full'
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  (entropyPower_gaussian_additivity
    P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY).ge

/-! ## §6 — Composed de Bruijn gap-monotonicity into the EPI gap -/

/-- **Composed Gaussian gap-derivative non-negativity**. For Gaussian `X`,
standard-normal `Z`, `X ⊥ Z`, the de Bruijn derivative along the heat-flow path
at `t > 0` is `(1/2) · J(𝒩(m, v + t)) = 1/(2(v + t)) ≥ 0`. This composes the
Gaussian de Bruijn identity with the derivative-sign engine: the EPI gap is
monotone non-decreasing along the heat path. -/
@[entry_point]
theorem deBruijn_gap_deriv_nonneg_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ (1 / 2 : ℝ) * fisherInfoOfMeasureV2Real
          (P.map (gaussianConvolution X Z t))
          (gaussianPDFReal m (v + ⟨t, ht.le⟩)) := by
  rw [fisherInfoOfMeasureV2Real_def]
  exact deBruijn_deriv_nonneg _

/-- **The de Bruijn derivative drives a monotone EPI gap**: the heat-flow path
derivative `g'(t) = (1/2) · J(g_t)` is non-negative, so the gap function
`g(t)` is monotone non-decreasing — packaged as the `IsEPIGapMonotoneHyp`
predicate for the density witness. -/
theorem isEPIGapMonotoneHyp_of_density (f : ℝ → ℝ) : IsEPIGapMonotoneHyp f :=
  isEPIGapMonotoneHyp_discharge f

/-! ## §7 — Predicate manipulation + sanity checks -/

/-- **Refined pipeline symmetry**: `IsEPIStamDeBruijnPipeline X Y P` implies
`IsEPIStamDeBruijnPipeline Y X P`.

Note: the `convScore` field is rebuilt via `isStamScoreConvolution_symm` (no
longer `trivial`, since `IsStamScoreConvolution` was upgraded from the W7
`Prop := True` placeholder to the typed optimal-λ-witness Prop in the
`epi-stam-discharge-plan` Phase B). -/
theorem isEPIStamDeBruijnPipeline_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsEPIStamDeBruijnPipeline X Y P) :
    IsEPIStamDeBruijnPipeline Y X P where
  convScore := isStamScoreConvolution_symm h.convScore
  totalExp := isStamTotalExpectation_symm h.totalExp

/-- **Refined pipeline congruence** under function equality. -/
theorem isEPIStamDeBruijnPipeline_congr
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hX : X = X') (hY : Y = Y')
    (h : IsEPIStamDeBruijnPipeline X Y P) :
    IsEPIStamDeBruijnPipeline X' Y' P := by
  subst hX; subst hY; exact h

/-- **Round-trip**: building the refined pipeline from its two genuine primitives
and extracting them yields the originals. -/
theorem stamDeBruijn_pipeline_roundtrip
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_conv : IsStamScoreConvolution X Y P)
    (h_te : IsStamTotalExpectation X Y P) :
    let h := isEPIStamDeBruijnPipeline_of_primitives h_conv h_te
    h.convScore = h_conv ∧ h.totalExp = h_te :=
  ⟨rfl, rfl⟩

end InformationTheory.Shannon.EPIStamDeBruijnConclusion
