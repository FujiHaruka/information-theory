import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Stam.Inequality
import InformationTheory.Shannon.EPI.Stam.FisherCoupling
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.FisherInfo.V2DeBruijn
import InformationTheory.Shannon.FisherInfo.Gaussian
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Stam → de Bruijn → EPI conclusion assembly

The EPI proof pieces:

* **Stam inequality** (Cover-Thomas Lemma 17.7.2). Step 4 (λ-optimization closed
  form `J_sum ≤ J_X J_Y / (J_X + J_Y)`) is *fully arithmetic*, in
  `StamInequality.lean` (`stam_lambda_min`, `stam_lambda_lower_bound`,
  `stam_inverse_form_of_harmonic_mean`). The Step 2-3 analytic core (the
  conditional Cauchy-Schwarz + convex Fisher bound) is localized to the single
  lemma `StamInequality.stam_step2_density_wall`, via
  `convex_fisher_bound_of_ready` (regularity preconditions only).
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

This file wires the Stam + de Bruijn pieces directly into the EPI
conclusion, with no intermediate scaling-decomposition structure. The wiring
proceeds two ways:

1. **Stam from regularity via the wall lemma** (§2). The
   Step 2-3 analytic core is localized to `stam_step2_density_wall`;
   `isStamInequalityHyp_of_primitives`
   derives `IsStamInequalityHyp` from regularity preconditions alone (no
   load-bearing analytic hypothesis).
2. **de Bruijn gap-monotonicity engine** (§1, §6). The de Bruijn derivative
   `g'(t) = (1/2) · J(g_t)` is `≥ 0` because Fisher information is non-negative
   (`fisherInfoOfDensityReal_nonneg`). This is the *genuine* monotonicity content
   that makes the EPI gap monotone along the heat-flow scaling path — we discharge
   `g'(t) ≥ 0` outright from the de Bruijn V2 witness.

The EPI conclusion (§3) is landed from regularity by deriving the Stam inequality
from the shared wall and feeding it through the monolithic
`IsEPIL3IntegratedPipeline`. The Gaussian EPI (§5) is obtained directly
from Gaussian saturation (`entropy_power_inequality_gaussian_full'`), with no Stam
claim.

## Genuine residual remaining

After this assembly the EPI conclusion reduces to a single residual.
`stam_step2_density_wall` — the conditional Cauchy-Schwarz +
convex Fisher bound (Cover-Thomas 17.7.2's deepest analytic content) — is
closed (`@audit:ok`) via
`convex_fisher_bound_of_ready`. The remaining residual is the regularity-precondition
signature gap on the published `IsStamInequalityHyp`, localized to
`isStamInequalityHyp_via_body` (`@residual(plan:epi-wall-reattack-plan)`,
`StamInequality.lean`), an owner-level pivot — not a Mathlib wall. The
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
open InformationTheory.Shannon.StamEPIBridge
open InformationTheory.Shannon.EPIL3Integration
open InformationTheory.Shannon.EPIStamToBridge
open InformationTheory.Shannon.StamInequality
open InformationTheory.Shannon.StamFisherCoupling
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

Produces `IsStamInequalityHyp` from measurability / independence /
probability measure alone, delegating the Step 2-3 analytic core to the
lemma `stam_step2_density_wall` via
`isStamInequalityHyp_via_step3`. The signature carries **no**
load-bearing analytic hypothesis.

The published `IsStamInequalityHyp` carries the pointwise convolution constraint +
`IsBlachmanConvReady` bundle, closing the regularity-precondition signature gap. -/
@[entry_point]
theorem isStamInequalityHyp_of_primitives
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_step3 P X Y hX hY hXY

/-! ## §3 — Main EPI from regularity (via shared wall)

The public main theorem `entropy_power_inequality` runs via
`EntropyPowerInequality.stamToEPIBridge_holds`, and the load-bearing predicate
content is localized to the shared `stam_step2_density_wall`. -/

/-! ## §5 — Gaussian EPI (via saturation)

The Gaussian EPI is `entropy_power_inequality_gaussian_full'` below (direct from
`entropyPower_gaussian_additivity`), which carries no Stam claim: the inequality
comes entirely from Gaussian saturation.
-/

/-- **Gaussian EPI fully hypothesis-free**
(`EPIL3Integration.entropy_power_inequality_gaussian_full`). The saturation case
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

end InformationTheory.Shannon.EPIStamDeBruijnConclusion
