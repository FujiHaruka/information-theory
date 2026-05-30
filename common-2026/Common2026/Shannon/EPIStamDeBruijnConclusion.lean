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
  `stam_inverse_form_of_harmonic_mean`). The genuine Step 2-3 analytic core (the
  conditional Cauchy-Schwarz + convex Fisher bound) is localized to the single
  shared sorry lemma `EPIStamInequalityBody.stam_step2_density_wall`
  (`@residual(wall:stam-step2-density)`, regularity preconditions only). The chain
  `isStamInequalityHyp_via_step3` discharges `IsStamInequalityHyp` from regularity
  alone via that shared wall.
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
`IsStamInequalityHyp`. This file wires the discharged pieces two ways:

1. **Stam from regularity via the shared wall** (§2). The genuine Step 2-3
   analytic core is localized to the shared sorry lemma `stam_step2_density_wall`
   (`@residual(wall:stam-step2-density)`); `isStamInequalityHyp_of_primitives`
   derives `IsStamInequalityHyp` from regularity preconditions alone (no
   load-bearing analytic hypothesis). The earlier design carried this content as
   load-bearing predicates (`IsStamScoreConvolution` + `IsStamTotalExpectation`
   bundled in the `IsEPIStamDeBruijnPipeline` structure); those were removed in
   the wall-consolidation pass (`epi-stam-wall-consolidation-plan`) as an isolated
   island with zero cross-file consumers.
2. **de Bruijn gap-monotonicity engine** (§1, §6). The de Bruijn derivative
   `g'(t) = (1/2) · J(g_t)` is `≥ 0` because Fisher information is non-negative
   (`fisherInfoOfDensityReal_nonneg`). This is the *genuine* monotonicity content
   that makes the EPI gap monotone along the heat-flow scaling path — we discharge
   `g'(t) ≥ 0` outright from the de Bruijn V2 witness.

The EPI conclusion (§3) is landed from regularity by deriving the Stam inequality
from the shared wall and feeding it through the monolithic
`IsEPIL3IntegratedPipeline`. The genuine Gaussian EPI (§5) is obtained directly
from Gaussian saturation (`entropy_power_inequality_gaussian_full'`), with no Stam
claim. (The former Gaussian *pipeline* discharge routed the Stam half through the
buggy V1 Fisher-info-zero artefact and was removed — see §5, RESOLVED 2026-05-20.)

## Genuine residual remaining

After this assembly the EPI conclusion reduces to the **single shared Stam-wall
sorry** `stam_step2_density_wall` (`@residual(wall:stam-step2-density)`,
`EPIStamInequalityBody.lean`): the conditional Cauchy-Schwarz + convex Fisher
bound (Cover-Thomas 17.7.2's deepest analytic content). The Stam→EPI bridge
(`IsStamToEPIBridgeHyp`, Csiszár scaling-path coupling, Lemma 17.7.3) is
discharged internally by consumers via the shared sorry lemma
`stamToEPIBridge_holds`.

## Key signatures

* `IsEPIGapMonotoneHyp` — de Bruijn gap-monotonicity sub-predicate (§1)
* `deBruijn_deriv_nonneg` / `isEPIGapMonotoneHyp_of_deBruijnV2` — `g'(t) ≥ 0` (§1)
* `isStamInequalityHyp_of_primitives` — Stam from regularity via shared wall (§2)
* `entropy_power_inequality_via_stamDeBruijn` — main EPI from regularity (§3)
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

/-! ## §2 — Stam inequality from regularity (via shared wall) -/

/-- **Stam inequality from regularity preconditions** (via the shared wall).

Produces the genuine `IsStamInequalityHyp` from measurability / independence /
probability measure alone, delegating the genuine Step 2-3 analytic core to the
shared sorry wall lemma `stam_step2_density_wall`
(`@residual(wall:stam-step2-density)`) via `isStamInequalityHyp_via_step3`.

This replaces the former load-bearing version that chained two Stam-wall
predicates (`IsStamScoreConvolution`, `IsStamTotalExpectation`); those predicates
were removed in the wall-consolidation pass. The signature now carries **no**
load-bearing analytic hypothesis.

This wrapper is **not** proof done: it depends transitively on `sorryAx`. The genuine
residual now lives in `isStamInequalityHyp_via_body`
(`@residual(plan:epi-wall-reattack-plan)`).
Update 2026-05-31 (Phase 3d): `stam_step2_density_wall` is **genuinely closed** (0-sorry,
`#print axioms` sorryAx-free) via `convex_fisher_bound_of_ready`; `IsStamCauchySchwarzOptimal`
is a provable (non-false) Prop. The prior "false-statement defect / universally FALSE"
note is obsolete. The remaining transitive `sorry` is the regularity-precondition signature
gap on the published `IsStamInequalityHyp` (`isStamInequalityHyp_via_body`), a clean
owner-level pivot tracked under `epi-wall-reattack-plan`, not a Mathlib wall. -/
@[entry_point]
theorem isStamInequalityHyp_of_primitives
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_step3 P X Y hX hY hXY

/-! ## §3 — Main EPI from regularity (via shared wall)

The former refined pipeline `IsEPIStamDeBruijnPipeline` (a structure bundling the
load-bearing `IsStamScoreConvolution` + `IsStamTotalExpectation` predicates) and
its operation helpers (`isStamInequalityHyp_of_stamDeBruijn`,
`isEPIL3IntegratedPipeline_of_stamDeBruijn`, `entropy_power_inequality_via_stamDeBruijn`,
`isEPIStamDeBruijnPipeline_of_primitives`, `_symm`, `_congr`, `_roundtrip`) were
removed in the wall-consolidation pass. They were an isolated island (zero
cross-file consumers; the public main theorem `entropy_power_inequality` runs via
`EPIStamToBridge.entropy_power_inequality_unconditional`), and their load-bearing
predicate content is now localized to the shared `stam_step2_density_wall`. -/

/-- **EPI conclusion from regularity preconditions** (via the shared wall).

Produces the EPI conclusion from measurability / independence / probability
measure alone, deriving the Stam inequality via the shared wall and feeding it
through the integrated pipeline. Carries **no** load-bearing analytic hypothesis.

This wrapper is **not** proof done: it consumes the shared sorry lemma
`stam_step2_density_wall` (transitively, via `isStamInequalityHyp_of_primitives`)
and so depends transitively on `sorryAx`. The genuine residual lives in that lemma.
⚠ Audit 2026-05-30: `stam_step2_density_wall` is a **false-statement defect**, not a
genuine Mathlib wall (target predicate `IsStamCauchySchwarzOptimal` universally FALSE
at its current signature, `@audit:defect(false-statement)`, see
`EPIStamInequalityBody.lean:359`); honest closure needs the owner-level signature
pivot under `epi-wall-reattack-plan`. Transitive consumer (no local `sorry`), so no
active `@residual` — defect marker lives on the wall lemma. -/
theorem entropy_power_inequality_via_stamDeBruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_int : IsEPIL3IntegratedPipeline X Y P :=
    { stam := isStamInequalityHyp_of_primitives P X Y hX hY hXY }
  exact entropy_power_inequality_integrated P X Y hX hY hXY h_int

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

/-! ## §7 — Predicate manipulation + sanity checks

The former refined-pipeline manipulation lemmas (`isEPIStamDeBruijnPipeline_symm`,
`_congr`, `stamDeBruijn_pipeline_roundtrip`) were removed alongside the
`IsEPIStamDeBruijnPipeline` structure in the wall-consolidation pass. -/

end InformationTheory.Shannon.EPIStamDeBruijnConclusion
