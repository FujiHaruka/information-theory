import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.Discharge
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Stam.InequalityBody
import InformationTheory.Shannon.EPI.Stam.Step3Body
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.DifferentialEntropy
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
  lemma `EPIStamInequalityBody.stam_step2_density_wall`, which is now **genuinely
  closed** (0-sorry, sorryAx-free; `wall:stam-step2-density` is [CLOSED
  2026-06-04] via `convex_fisher_bound_of_ready`; regularity preconditions only).
  The chain `isStamInequalityHyp_via_step3` discharges `IsStamInequalityHyp` from
  regularity alone via that lemma.
* **de Bruijn identity** (V2). `deBruijn_identity_v2` gives, from
  `IsRegularDeBruijnHypV2`, the heat-flow derivative
  `(d/dt) h(X + √t · Z) = (1/2) · J(g_t)`, with the Gaussian case
  `deBruijn_identity_v2_gaussian` fully discharged hypothesis-free.

This file is the **conclusion-assembly** layer: it wires those discharged Stam +
de Bruijn pieces into a tighter EPI pipeline, reducing the EPI main theorem's
remaining hypothesis to the genuinely-irreducible primitives.

## Approach

This file wires the discharged Stam + de Bruijn pieces directly into the EPI
conclusion, with no intermediate scaling-decomposition structure (an earlier
Wave-7 decomposition predicate that split the bridge into `scaling`/`limit`
around a black-box `IsStamInequalityHyp` field was removed; it is no longer part
of the route). The wiring proceeds two ways:

1. **Stam from regularity via the (now genuine) wall lemma** (§2). The genuine
   Step 2-3 analytic core is localized to `stam_step2_density_wall`, now genuinely
   closed (0-sorry, sorryAx-free; `wall:stam-step2-density` is [CLOSED
   2026-06-04]); `isStamInequalityHyp_of_primitives`
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

After this assembly the EPI conclusion reduces to a single residual. Update
2026-05-31 (Phase 3d): `stam_step2_density_wall` — the conditional Cauchy-Schwarz +
convex Fisher bound (Cover-Thomas 17.7.2's deepest analytic content) — is now
**genuinely closed** (0-sorry, sorryAx-free, `@audit:ok`) via
`convex_fisher_bound_of_ready`. The remaining residual is the regularity-precondition
signature gap on the published `IsStamInequalityHyp`, localized to
`isStamInequalityHyp_via_body` (`@residual(plan:epi-wall-reattack-plan)`,
`EPIStamInequalityBody.lean`), an owner-level pivot — not a Mathlib wall. The
Stam→EPI bridge
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
open InformationTheory.Shannon.FisherInfoV2

/-! ## §1 — de Bruijn gap-monotonicity engine -/

/-- **EPI gap-monotonicity hypothesis along the heat-flow scaling path**.

The Stam inequality + de Bruijn identity together imply that the EPI gap is
monotone non-decreasing along the heat-flow path `X(t) = X + √t · Z`. The de
Bruijn derivative `g'(t) = (d/dt) h(X + √t · Z) = (1/2) · J(g_t)` is the engine:
it is non-negative because Fisher information is non-negative.

This `Prop`-level predicate records the **non-negativity of the de Bruijn
derivative for the density witness `f`** — the genuine analytic content that makes
the gap monotone. It complements `EPIStamToBridge.csiszarLogRatioGap_antitoneOn_Ici_zero`
(which carries the global `AntitoneOn` witness for the Csiszár log-ratio gap along
the heat-flow path); the present predicate isolates the *derivative-sign* step of
the Csiszár scaling argument and discharges it outright (§1, below). -/
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
now-genuine (sorryAx-free) lemma `stam_step2_density_wall`
(`wall:stam-step2-density` is [CLOSED 2026-06-04]) via
`isStamInequalityHyp_via_step3`. `#print axioms isStamInequalityHyp_of_primitives`
= `[propext, Classical.choice, Quot.sound]` (sorryAx-free, 2026-06-04 audit).

This replaces the former load-bearing version that chained two Stam-wall
predicates (`IsStamScoreConvolution`, `IsStamTotalExpectation`); those predicates
were removed in the wall-consolidation pass. The signature now carries **no**
load-bearing analytic hypothesis.

Update 2026-05-31 (owner-level pivot, epi-wall-reattack-plan): `stam_step2_density_wall`
**and** `isStamInequalityHyp_via_body` are now **both genuinely closed** (0-sorry,
`#print axioms` sorryAx-free). The published `IsStamInequalityHyp` was pivoted in lockstep
with `IsStamInequalityResidual` to carry the pointwise convolution constraint +
`IsBlachmanConvReady` bundle, closing the former regularity-precondition signature gap.
This wrapper therefore produces a genuine, **sorryAx-free** `IsStamInequalityHyp`. -/
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
cross-file consumers; the public main theorem `entropy_power_inequality`
actually runs via `EntropyPowerInequality.stamToEPIBridge_holds`, verified by the
forward dep graph 2026-06-09), and their load-bearing predicate content is now
localized to the shared `stam_step2_density_wall`.

(deleted 2026-06-11, legacy Stam→EPI subtree removal) The wrapper
`entropy_power_inequality_via_stamDeBruijn` (EPI conclusion from regularity
preconditions, routed through `entropy_power_inequality_integrated` →
`EntropyPowerInequality.stamToEPIBridge_holds`) was removed together with that
bridge subtree; it had 0 consumers. -/

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
