import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.Discharge
import InformationTheory.Shannon.FisherInfo.V2DeBruijnGenuine
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Plumbing
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Basic

/-!
# T2-D: Stam → EPI — Csiszár ratio path-derivative cluster

This file holds the Csiszár-coupling ratio path-derivative lemmas (the genuine
`AntitoneOn` / continuity chain along the heat-flow path) consumed by the EPI
case-1 closure, plus the standard-normal-pair richness predicate
`IsStamScalingNoiseHyp` whose honest lift-form inhabitant lives in
`EPINoiseExtension`.

The former in-place scaling/noise route through this file
(`IsStamToEPIScalingHyp` / `stamToEPIScaling_holds` /
`isStamToEPIBridgeHyp_of_scaling` / `stamScalingNoise_exists` /
`isStamToEPIBridgeHyp_of_gaussian_via_scaling` /
`IsEPIScalingDecomposedPipeline` / `entropy_power_inequality_unconditional`)
has been **deleted** (2026-06-09, `epi-richness-route-b-plan` B2): the in-place
noise existential `stamScalingNoise_exists` was a `false-statement` defect
(false on atomic measures), and the scaling sub-predicate / headline decls built
on it were dead code (consumer ripple 0). The EPI conclusion is now carried by
the honest successor
`EPINoiseExtension.entropy_power_inequality_via_lift` (sorryAx-free), which
transports EPI from the lift space `Ω × ℝ × ℝ` using `entropyPower`'s law-only
property + `IsStamInequalityResidual`'s carrier-free defeq.

## Surviving members

* `IsStamScalingNoiseHyp X Y P` — the genuine standard-normal-pair existential
  predicate (§2'). Its honest lift-form inhabitant is the live
  `EPINoiseExtension.stamScalingNoise_exists_on_lift`.
* `isStamScalingNoiseHyp_symm` — symmetry of that predicate (§2').
* the Csiszár-cluster ratio path-derivative lemmas
  (`entropyPower_hasDerivAt_of_diffEnt_hasDerivAt`,
  `csiszarLogRatioGap_hasDerivAt`, `csiszarLogRatioGap_deriv_le_zero`,
  `epi_of_csiszarLogRatioGap_zero_nonneg`, and the `AntitoneOn` / continuity
  chain), live-consumed by
  `EPICase1RatioLimit.entropyPower_add_ge_case1_of_regular` (§2''–§4).

## File map

* §2' — Phase A staged predicate: standard normal pair witness on `(Ω, P)`
* §2'' — Phase A A-2: path-derivative of the 1-source gap
* §2''' — Phase A A-3: 1-source Stam reduction `g'(t) ≤ 0`
* §5 — Symmetry, congruence, pass-through helpers
* §6 — 3-arg / 4-arg chain forms via scaling decomposition
* §7 — Round-trip / sanity-check theorems
-/

namespace InformationTheory.Shannon.EPIStamToBridge

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIL3Integration

/-! ## §2' — Phase A staged predicate: standard normal pair witness on `(Ω, P)` -/

/-- **Standard normal pair witness on an arbitrary probability space**
(Phase A A-1 staged honest predicate, sister sub-plan
`epi-stam-to-conclusion-phaseA-plan`).

Cover-Thomas Ch.17 Csiszár scaling argument requires two standard normal
random variables `Z_X, Z_Y : Ω → ℝ` defined on the *same* probability space
`(Ω, P)` as the original `X, Y`, with:

* `P.map Z_X = P.map Z_Y = gaussianReal 0 1` (each is standard normal),
* `IndepFun X Z_X P`, `IndepFun Y Z_Y P` (each `Z_*` is independent of
its paired original variable — needed for the path-law step),
* `IndepFun Z_X Z_Y P` (the noise pair is jointly independent — needed
for the Gaussian saturation endpoint at `s = 1`, where the path-end
reduces to a sum of two independent standard normals).

**Mathlib status (loogle, 2026-05-25)**: there is **no** existing
Mathlib API to extend an arbitrary probability measure `(Ω, P)` with two
fresh independent standard-normal random variables jointly independent
of a pre-existing pair `(X, Y)`. Search results:

* `MeasureTheory.AtomlessProbability` → `unknown identifier`
* `ProbabilityTheory.IsAtomless` → `unknown identifier`
* `ProbabilityTheory.exists_iIndepFun` → `unknown identifier`
* `exists_measurable_indepFun` → `unknown identifier`
* `MeasureTheory.NoAtoms` exists as a class
(`Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean:34`) but the
noise extension constructor is absent.
* The Central Limit Theorem use of `gaussianReal` in
`Mathlib/Probability/CentralLimitTheorem.lean:79` works on a *different*
ambient probability space `P'` and assumes an i.i.d. sequence on `P`,
so it cannot be specialized to construct fresh Gaussians on the original
`P`.

InformationTheory internal search (`rg "exists_indep|standard_normal_pair|
noiseExtension|extendByGaussian"`) likewise returns 0 hits.

**Non-vacuous**: the 7-conjunction body is not trivially dischargeable —
the `P.map _ = gaussianReal 0 1` conjuncts rule out the `Z_* := 0` collapse
(`P.map (fun _ => 0) = Measure.dirac 0 ≠ gaussianReal 0 1`). The genuine content
is the *existence* of such fresh jointly independent standard normals (Cover-Thomas
Ch.17 implicit assumption "carries enough auxiliary randomness"). No Mathlib API
constructs them in place (loogle 0 hits — `ProbabilityTheory.exists_iIndepFun`,
`MeasureTheory.Measure.IsAtomless`, `exists_measurable_indepFun` all `unknown
identifier`); and the predicate is not the EPI conclusion in disguise (it concerns
noise existence, not an entropy-power inequality).

**Honesty status**: this `def` is a *genuine existential richness statement* (no
circular / `:True` / vacuous shape). The **in-place** instantiation on an
arbitrary `(Ω, P)` is **provably false** on atomic measures (e.g. `Ω = Unit`,
`P = Measure.dirac ()`), so the route through this file was deleted (2026-06-09,
`epi-richness-route-b-plan` B2). The honest inhabitant that *does* hold is
`EPINoiseExtension.stamScalingNoise_exists_on_lift` on the lift space
`Ω × ℝ × ℝ` (0 sorry, live), which feeds
`EPINoiseExtension.entropy_power_inequality_via_lift` (the honest EPI successor).
This predicate carries **no** `@residual` / `@audit:*` tag of its own. -/
def IsStamScalingNoiseHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ (Z_X Z_Y : Ω → ℝ),
    Measurable Z_X ∧ Measurable Z_Y ∧
    P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
    IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P

/-- **Symmetry of the standard-normal-pair predicate**: if `(Z_X, Z_Y)`
witnesses `IsStamScalingNoiseHyp X Y P`, then `(Z_Y, Z_X)` witnesses
`IsStamScalingNoiseHyp Y X P` (swap the roles).

`@audit:ok` (trivial existential repackage; no analytic content). -/
theorem isStamScalingNoiseHyp_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamScalingNoiseHyp X Y P) :
    IsStamScalingNoiseHyp Y X P := by
  obtain ⟨Z_X, Z_Y, hZX_meas, hZY_meas, hZX_law, hZY_law,
          hXZX, hYZY, hZXZY⟩ := h
  exact ⟨Z_Y, Z_X, hZY_meas, hZX_meas, hZY_law, hZX_law, hYZY, hXZX,
         hZXZY.symm⟩

/-! ## §2'' — Phase A A-2: path-derivative of the 1-source gap

This subsection provides the entropy-power chain-rule helper used by the
de Bruijn path-derivative computation along `t ∈ Ioi 0`, by direct application of
the V2 de Bruijn identity (`deBruijn_identity_v2`,
`InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:272`; Phase 2.B foundation
removed the inline `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2`
field, the identity is now delivered by the genuine (sorryAx-free)
`debruijnIdentityV2_holds_assembled`; `wall:debruijn-integration` is [CLOSED
2026-06-04]) to the three mapped measures
`P.map (X + √t · Z_X)`, `P.map (Y + √t · Z_Y)`, `P.map ((X+Y) + √t · (Z_X+Z_Y))`,
composed with `Real.exp` via a one-line chain rule helper.

Bases (`X`, `Y`, `X + Y`) are all `t`-independent — no scaling-correction term
appears (1-source design avoids L-Concl-A-δ at the source).

Members:

* `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (A-2-2) — chain-rule helper
  lifting `HasDerivAt h d t` to `HasDerivAt (fun s => Real.exp (2 · h s))
  (Real.exp (2 · h t) · (2 · d)) t`. Single-line wrap of `HasDerivAt.exp`
  composed with `HasDerivAt.const_mul`.

(The difference-version path-derivative A-2-3 was deleted with the dead de Bruijn
difference subgraph; the genuine ratio path-derivative lives in
`csiszarLogRatioGap_hasDerivAt`.)
-/

/-- **A-2-2 chain-rule helper**: if `f` has derivative `d` at `t`, then the
"entropy power" composition `s ↦ Real.exp (2 · f s)` has derivative
`Real.exp (2 · f t) · (2 · d)` at `t`.

Used to lift the V2 de Bruijn identity `HasDerivAt (fun s => h (P.map
(gaussianConvolution X Z s))) ((1/2) · J(X+√t·Z)) t` to the entropy-power
form `HasDerivAt (fun s => entropyPower (P.map (gaussianConvolution X Z s)))
(entropyPower (P.map (gaussianConvolution X Z t)) · (2 · (1/2) · J)) t`.

Proof: `HasDerivAt.const_mul 2` (multiply derivative by `2`), then
`HasDerivAt.exp` (chain with `Real.exp`). `@audit:ok` (trivial chain). -/
@[entry_point]
theorem entropyPower_hasDerivAt_of_diffEnt_hasDerivAt
    {f : ℝ → ℝ} {d t : ℝ} (h : HasDerivAt f d t) :
    HasDerivAt (fun s => Real.exp (2 * f s)) (Real.exp (2 * f t) * (2 * d)) t :=
  (h.const_mul 2).exp

/-! ## §2''' — Phase A A-3: 1-source Stam reduction `g'(t) ≤ 0`

This subsection reduces the A-2-3 derivative expression to `≤ 0` using the
1-source Stam inequality applied to the three convolved random variables
`X + √t · Z_X`, `Y + √t · Z_Y`, `(X+Y) + √t · (Z_X+Z_Y)`.

Concretely we consume `IsStamInequalityHyp (X + √t·Z_X) (Y + √t·Z_Y) P` at the
specific `t > 0` and produce `g'(t) ≤ 0` where `g'(t)` is the right-hand side
of the ratio path-derivative (A-2-3 difference version deleted with the dead
de Bruijn difference subgraph; see `csiszarLogRatioGap_hasDerivAt`).

`InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 _ f` is defined as
`fisherInfoOfDensity f` (a `ℝ≥0∞` value), and `fisherInfoOfDensityReal f`
equals `(fisherInfoOfDensity f).toReal`. The two forms therefore connect:
`(fisherInfoOfMeasureV2 _ f).toReal = fisherInfoOfDensityReal f` (`rfl`).
This is what lets the A-2-3 output (which carries `fisherInfoOfDensityReal`)
plug into the `IsStamInequalityHyp` slot (which requires
`(fisherInfoOfMeasureV2 _ _).toReal`).

Members: the genuine ratio derivative-bound core (the difference-version A-3
`g'(t) ≤ 0` lemma was deleted as false-as-framed; the genuine in-house
arithmetic replacement is the ratio-gap derivative core below).
-/

/-- **Ratio-gap derivative core (pure arithmetic)**. From plain harmonic Stam
`1/J_sum ≥ 1/J_X + 1/J_Y` and positivity of the entropy powers `N_X, N_Y`, the
log-ratio gap derivative `J_sum − (N_X·J_X + N_Y·J_Y)/(N_X+N_Y)` is `≤ 0`,
equivalently `J_sum·(N_X+N_Y) ≤ N_X·J_X + N_Y·J_Y`. This is the genuine in-house
content that replaces the (deleted) false-as-framed difference-gap derivative
lemma; tracked by `epi-csiszar-ratio-reframe-plan`.

Scope note (GS-A3' probe 2026-06-06): this is the **factor-1** abstract arith
(coefficient `1` on `J_sum`). It is a true real-arithmetic inequality over the
free variables (verbatim-reproduced as the probe's `factor1_arith`, compiles
clean). It does NOT assert anything about a variance-2 sum: the analogous
**factor-2** statement `2·J_sum − (…) ≤ 0` is FALSE from plain harmonic Stam +
positivity (probe `factor2_arith_FALSE`, counterexample `J_X=2,J_Y=1,J_sum=2/3,
N_X=1,N_Y=3`). The factor mismatch for the genuine 𝒩(0,2) sum coupling lives in
the de Bruijn lift / `Z_law` precondition, NOT in this lemma; this lemma is
honest as an abstract factor-1 inequality.

@audit:ok — independent honesty audit (2026-06-06, fresh auditor). 4 checks PASS:
(1) non-circular — conclusion is a real inequality, no hypothesis ≡ conclusion;
(2) non-bundled — `h_stam` is plain harmonic Stam over free reals, not a bundled
inequality core; `nlinarith` does the work from `h_stam` + `sq_nonneg`; (3) not
degenerate; (4) sufficiency — `factor1_arith` is provable from the hypotheses (GS-
A3' probe verbatim). `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, mechanically confirmed). -/
theorem csiszar_ratio_deriv_le_zero_arith
    (J_X J_Y J_sum N_X N_Y : ℝ)
    (hJX : 0 < J_X) (hJY : 0 < J_Y) (hJsum : 0 < J_sum)
    (hNX : 0 < N_X) (hNY : 0 < N_Y)
    (h_stam : 1 / J_sum ≥ 1 / J_X + 1 / J_Y) :
    J_sum - (N_X * J_X + N_Y * J_Y) / (N_X + N_Y) ≤ 0 := by
  have hNsum : 0 < N_X + N_Y := add_pos hNX hNY
  -- Clear the harmonic Stam inequality to a polynomial form:
  -- `1/J_sum ≥ 1/J_X + 1/J_Y` ⟺ `J_X*J_Y ≥ J_sum*(J_X+J_Y)`.
  have h_stam_poly : J_sum * (J_X + J_Y) ≤ J_X * J_Y := by
    have h := h_stam
    rw [ge_iff_le, div_add_div _ _ (ne_of_gt hJX) (ne_of_gt hJY)] at h
    rw [div_le_div_iff₀ (by positivity) hJsum] at h
    nlinarith [h]
  -- Goal ⟺ `J_sum*(N_X+N_Y) ≤ N_X*J_X + N_Y*J_Y`.
  rw [sub_nonpos, le_div_iff₀ hNsum]
  -- After clearing `(J_X+J_Y)`: `J_X*J_Y*(N_X+N_Y) ≤ (N_X*J_X+N_Y*J_Y)*(J_X+J_Y)`,
  -- whose difference is `N_X*J_X² + N_Y*J_Y² ≥ 0`.
  nlinarith [mul_nonneg (le_of_lt hNX) (sq_nonneg (J_X - J_Y)),
    mul_nonneg (le_of_lt hNY) (sq_nonneg (J_X - J_Y)),
    mul_pos hJX hJY, mul_pos hNX hJX, mul_pos hNY hJY,
    mul_nonneg (le_of_lt hNsum) (le_of_lt (mul_pos hJX hJY)),
    h_stam_poly, mul_le_mul_of_nonneg_right h_stam_poly (le_of_lt hNsum)]

/-- **R-2 — log-ratio gap derivative**. The genuine monotone object
`csiszarLogRatioGap` (`EPIL3Integration.lean`) has derivative

`(d/dt) csiszarLogRatioGap X Y Z_X Z_Y P t = J_sum − (N_X·J_X + N_Y·J_Y)/(N_X+N_Y)`

at any `t > 0`, where `N_i = entropyPower (P.map path_i t)` and
`J_i = fisherInfoOfDensityReal ((h_reg_i.reg_at t ht).density_t)`.

Built from the three per-term `HasDerivAt (fun s => entropyPower (P.map path_i s))
(N_i · J_i) t` (via `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` over the
de Bruijn V2 identity), then `HasDerivAt.log` for the
two log terms (`log N_sum`: deriv `(N_sum·J_sum)/N_sum = J_sum`; `log(N_X+N_Y)`:
deriv `(N_X·J_X+N_Y·J_Y)/(N_X+N_Y)`), composed by `HasDerivAt.sub`.

Honesty: `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free,
the de Bruijn building block `deBruijn_identity_v2` is genuine); `h_reg_*` are
regularity preconditions, no load-bearing bundling.

GS-A3' scope limitation (probe 2026-06-06, independent audit). This is an
**honest conditional theorem**, but its conclusion is the **factor-1** derivative
`J_sum − (…)` (coefficient `1` on `J_sum`). That value is correct only *under the
hypotheses as stated*: `h_reg_sum.reg_at t ht` carries `IsRegularDeBruijnHypV2`'s
`Z_law` field, which asserts `P.map (Z_X+Z_Y) = gaussianReal 0 1`
(`deBruijn_identity_v2` is "for `Z ∼ 𝒩(0,1)`", yielding factor `(1/2)` → lifted
`J_sum`). For the **genuine** sum coupling where `Z_X,Z_Y ∼ 𝒩(0,1)` are
independent, the true sum law is `gaussianReal 0 2`, so `Z_law(sum)=𝒩(0,1)` is
FALSE and `h_reg_sum` is **uninhabitable** in that setting — and the genuine
variance-2 derivative would be `2·J_sum − (…)`. Hence this factor-1 derivative is
NOT usable to discharge sum-EPI; this is a scope limitation of the single-`t` view,
not a defect of this conditional theorem. As a conditional implication this theorem
is genuinely TRUE (no internal inconsistency in the hypotheses → no vacuous-truth
escape), non-circular, and non-bundled (`Z_law` is a
precondition on the noise distribution, not a bundled derivative value). Honest
closure of the sum line is achieved by the **two-time route**
(`EPICase1TwoTime.lean`, `entropyPower_add_ge_case1_of_regular_twotime`, `@audit:ok`),
which perturbs `X`/`Y` with separate unit-variance noises so the variance-2 view
never arises. The variance-2 `false-statement` defect that this single-`t` view used
to park in the sum producer (`EPICase1SumProducer.lean`) is resolved: that producer
was a structurally dead orphan (0 consumers, superseded by the two-time route) and
has been deleted (2026-06-06), so the `IsRegularDeBruijnHypV2.Z_law` general-variance
refactor is no longer needed. (GS-A3' showed all single-`t` routes are blocked by a
non-local co-monotonicity obligation, not weight tuning.)

@audit:ok — independent honesty audit (2026-06-06, fresh auditor): 4 checks PASS
as a conditional theorem (non-circular / non-bundled — `Z_law` is a noise-law
precondition / not degenerate / sufficiency — factor-1 follows correctly under the
stated `Z_law=𝒩(0,1)` hypothesis). `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free, mechanically confirmed). Tag retained; the sum line is
closed genuinely by the two-time route. -/
theorem csiszarLogRatioGap_hasDerivAt
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P s)
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
            ((h_reg_sum.reg_at t ht).density_t)
        - (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_X.reg_at t ht).density_t)
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_Y.reg_at t ht).density_t))
          / (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))) t := by
  -- Per-term de Bruijn V2 derivatives (same building blocks as the
  -- difference-version path-derivative that was deleted with the dead subgraph).
  have h_dB_X :
      HasDerivAt
        (fun s : ℝ => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z_X s)))
        ((1/2) * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_X.reg_at t ht).density_t)) t :=
    InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2 X Z_X hX hZX hXZX ht
      (h_reg_X.reg_at t ht)
  have h_dB_Y :
      HasDerivAt
        (fun s : ℝ => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Y Z_Y s)))
        ((1/2) * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_Y.reg_at t ht).density_t)) t :=
    InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2 Y Z_Y hY hZY hYZY ht
      (h_reg_Y.reg_at t ht)
  have h_dB_sum :
      HasDerivAt
        (fun s : ℝ => InformationTheory.Shannon.differentialEntropy
          (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) s)))
        ((1/2) * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at t ht).density_t)) t :=
    InformationTheory.Shannon.FisherInfoV2.deBruijn_identity_v2
      (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω)
      (hX.add hY) (hZX.add hZY) hXYZXY ht (h_reg_sum.reg_at t ht)
  -- Lift to entropy-power form via the A-2-2 chain rule.
  have h_eP_X := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB_X
  have h_eP_Y := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB_Y
  have h_eP_sum := entropyPower_hasDerivAt_of_diffEnt_hasDerivAt h_dB_sum
  -- Abbreviations.
  set J_X := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_X.reg_at t ht).density_t) with hJX_def
  set J_Y := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_Y.reg_at t ht).density_t) with hJY_def
  set J_sum := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_sum.reg_at t ht).density_t) with hJsum_def
  -- Normalize each per-term derivative to `entropyPower (P.map path_i) · J_i`.
  -- `entropyPower μ = exp (2 * differentialEntropy μ)` is rfl, and
  -- `gaussianConvolution X Z s = fun ω => X ω + √s · Z ω` is rfl, so the function
  -- bodies already match `entropyPower (P.map (fun ω => ...))`. The derivative
  -- value `exp(2h) * (2 * ((1/2) * J))` simplifies to `entropyPower · J`.
  have hN_X :
      HasDerivAt (fun s : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω)))
        (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X) t := by
    have h_val :
        entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X
          = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z_X t)))
            * (2 * ((1/2) * J_X)) := by
      unfold entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]
    exact h_eP_X
  have hN_Y :
      HasDerivAt (fun s : ℝ => entropyPower (P.map (fun ω => Y ω + Real.sqrt s * Z_Y ω)))
        (entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y) t := by
    have h_val :
        entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y
          = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution Y Z_Y t)))
            * (2 * ((1/2) * J_Y)) := by
      unfold entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]
    exact h_eP_Y
  have hN_sum :
      HasDerivAt (fun s : ℝ => entropyPower
          (P.map (fun ω => X ω + Y ω + Real.sqrt s * (Z_X ω + Z_Y ω))))
        (entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) * J_sum) t := by
    have h_val :
        entropyPower (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) * J_sum
          = Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
                        (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) t)))
            * (2 * ((1/2) * J_sum)) := by
      unfold entropyPower InformationTheory.Shannon.FisherInfoV2.gaussianConvolution
      ring
    rw [h_val]
    exact h_eP_sum
  -- Positivity of the entropy powers (for the `log` side conditions).
  have hNX_pos : 0 < entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) :=
    entropyPower_pos _
  have hNY_pos : 0 < entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) :=
    entropyPower_pos _
  have hNsum_pos : 0 < entropyPower
      (P.map (fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω))) := entropyPower_pos _
  -- `log N_sum` derivative: `(N_sum · J_sum) / N_sum = J_sum`.
  have h_log_sum :
      HasDerivAt (fun s : ℝ => Real.log (entropyPower
          (P.map (fun ω => X ω + Y ω + Real.sqrt s * (Z_X ω + Z_Y ω)))))
        J_sum t := by
    have h := hN_sum.log (ne_of_gt hNsum_pos)
    rwa [mul_comm, mul_div_assoc, div_self (ne_of_gt hNsum_pos), mul_one] at h
  -- `log (N_X + N_Y)` derivative: `(N_X·J_X + N_Y·J_Y)/(N_X+N_Y)`.
  have h_add :
      HasDerivAt (fun s : ℝ =>
          entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt s * Z_Y ω)))
        (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X
          + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y) t :=
    hN_X.add hN_Y
  have h_log_add :
      HasDerivAt (fun s : ℝ => Real.log
          (entropyPower (P.map (fun ω => X ω + Real.sqrt s * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt s * Z_Y ω))))
        ((entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) * J_X
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) * J_Y)
          / (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))) t :=
    h_add.log (ne_of_gt (add_pos hNX_pos hNY_pos))
  -- Combine via `.sub` and match the `csiszarLogRatioGap` body.
  have h_combined := h_log_sum.sub h_log_add
  unfold InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
  exact h_combined

/-- **R-3 — `r'(t) ≤ 0` from 1-source Stam** (genuine successor of the
deleted false-as-framed difference-gap derivative lemma).

The log-ratio gap derivative `J_sum − (N_X·J_X + N_Y·J_Y)/(N_X+N_Y) ≤ 0` follows
from the 1-source Stam inequality (extracted as plain harmonic Stam
`1/J_sum ≥ 1/J_X + 1/J_Y`) plus positivity, via the pure-arithmetic core
`csiszar_ratio_deriv_le_zero_arith`. Unlike the difference-gap form, this RATIO
form IS genuinely closable from plain Stam (weights `α = N_X/(N_X+N_Y)`,
`β = N_Y/(N_X+N_Y)`, `α²≤α`).

`h_stam` is the genuine Stam residual (Mathlib wall, separate `Prop` from EPI),
`h_reg_*` are regularity preconditions — no load-bearing bundling.

**Closure (案 B, R-3‴, 2026-06-01)**: the plain harmonic Stam
`1/J_sum ≥ 1/J_X + 1/J_Y` is now extracted **genuinely** by applying `h_stam`
(the ∀-quantified producer `Prop`) at the three path densities
`f_i = (h_reg_*.reg_at t ht).density_t`. The application requires:
* the three Fisher identifications `J_i = (fisherInfoOfMeasureV2 (P.map _) f_i).toReal`
— `rfl` since `fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f`
(`fisherInfoOfMeasureV2_def`) and `fisherInfoOfDensityReal f = (fisherInfoOfDensity f).toReal`;
* the **caller-supplied regularity preconditions** below: `IsRegularDensityV2`
for the two summand path densities (`h_regdens_X`/`h_regdens_Y`), the
normalizations `∫ = 1` (`h_norm_X`/`h_norm_Y`), the pointwise convolution
identification (`h_conv_id`), and the Blachman-readiness bundle (`h_blachman`).

The core inequality itself lives genuinely in the producer side
(`stam_step2_density_wall` → `isStamInequalityHyp_via_body`, `@audit:ok`
sorryAx-free); the consumer only supplies the regularity inputs to apply it.
None of the new preconditions bundle the inequality core — they are smoothness /
normalization / structural (convolution) / 19-field Blachman regularity. In
particular `h_blachman : IsBlachmanConvReady` is classified `@audit:ok` as a
regularity precondition in `EPIStamDischarge`, NOT a load-bearing core. This is
the honest closure path; the wall (a general-density Blachman producer for the
non-Gaussian path density `convDensityAdd pX gaussian`) is pushed up to the
callers as a `caller-supplied regularity precondition`, not injected here.

@audit:ok — independent honesty audit (2026-06-01, commit `ba4353a`): all 4 checks
PASS, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free,
0-sorry mechanically verified). (1) non-circular: conclusion
`J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0` ≠ any hypothesis type. (2) NOT
load-bearing: `h_stam : IsStamInequalityHyp` is the ∀-quantified genuine Stam
PRODUCER (`@audit:ok`, producible from regularity alone via
`isStamInequalityHyp_via_step3` → `stam_step2_density_wall` →
`convex_fisher_bound_of_ready`, all sorryAx-free); the 6 new preconditions
(`IsRegularDensityV2` smoothness, `∫=1` normalization, pointwise `convDensityAdd`
structural id, 19-field `IsBlachmanConvReady` Integrable/bdd/pos bundle —
`@audit:ok` regularity) are the producer's APPLY antecedents, none carries the
inequality core. Core-reconstruction test: granting all 6 does NOT hand the Stam
bound — `h_stam` is still required. (3) non-degenerate: no `:True`/vacuous shape.
(4) sufficiency: the genuine RATIO form (NOT the false-as-framed difference form
D3, correctly deleted) IS closable from plain harmonic Stam via the genuine
arith core `csiszar_ratio_deriv_le_zero_arith` (`nlinarith`, `α²≤α` weights); the
three Fisher `rfl` identifications hold since `fisherInfoOfMeasureV2` ignores its
measure argument (`FisherInfoV2DeBruijn.lean:81`). -/
@[entry_point]
theorem csiszarLogRatioGap_deriv_le_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    {t : ℝ} (ht : 0 < t)
    (hJX_pos : 0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                      ((h_reg_X.reg_at t ht).density_t))
    (hJY_pos : 0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                      ((h_reg_Y.reg_at t ht).density_t))
    (hJsum_pos : 0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                        ((h_reg_sum.reg_at t ht).density_t))
    (h_stam : InformationTheory.Shannon.EPIStamDischarge.IsStamInequalityHyp
                (fun ω => X ω + Real.sqrt t * Z_X ω)
                (fun ω => Y ω + Real.sqrt t * Z_Y ω) P)
    -- ↓ 案 B (R-3‴): caller-supplied regularity preconditions for applying `h_stam`.
    (h_regdens_X : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
                      ((h_reg_X.reg_at t ht).density_t))
    (h_regdens_Y : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
                      ((h_reg_Y.reg_at t ht).density_t))
    (h_norm_X : ∫ x, (h_reg_X.reg_at t ht).density_t x ∂MeasureTheory.volume = 1)
    (h_norm_Y : ∫ x, (h_reg_Y.reg_at t ht).density_t x ∂MeasureTheory.volume = 1)
    (h_conv_id : ∀ x, (h_reg_sum.reg_at t ht).density_t x
                    = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                        ((h_reg_X.reg_at t ht).density_t)
                        ((h_reg_Y.reg_at t ht).density_t) x)
    (h_blachman : InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
                    ((h_reg_X.reg_at t ht).density_t)
                    ((h_reg_Y.reg_at t ht).density_t)) :
    InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
          ((h_reg_sum.reg_at t ht).density_t)
        - (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_X.reg_at t ht).density_t)
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω))
              * InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
                  ((h_reg_Y.reg_at t ht).density_t))
          / (entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω))
            + entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)))
      ≤ 0 := by
  -- Abbreviations for the three Fisher infos and two entropy powers.
  set J_X := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_X.reg_at t ht).density_t) with hJX_def
  set J_Y := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_Y.reg_at t ht).density_t) with hJY_def
  set J_sum := InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
      ((h_reg_sum.reg_at t ht).density_t) with hJsum_def
  set N_X := entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z_X ω)) with hNX_def
  set N_Y := entropyPower (P.map (fun ω => Y ω + Real.sqrt t * Z_Y ω)) with hNY_def
  -- Positivity of the entropy powers.
  have hNX_pos : 0 < N_X := entropyPower_pos _
  have hNY_pos : 0 < N_Y := entropyPower_pos _
  -- Plain harmonic Stam `1/J_sum ≥ 1/J_X + 1/J_Y` extracted GENUINELY from
  -- `h_stam` (案 B, R-3‴). We apply the ∀-quantified producer `Prop` at the three
  -- path densities `f_i = (h_reg_*.reg_at t ht).density_t`. The Fisher
  -- identifications `J_i = (fisherInfoOfMeasureV2 (P.map _) f_i).toReal` are `rfl`
  -- (`fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f`,
  -- `fisherInfoOfDensityReal f = (fisherInfoOfDensity f).toReal`); the remaining
  -- regularity inputs are the caller-supplied preconditions.
  have h_plain_stam : 1 / J_sum ≥ 1 / J_X + 1 / J_Y := by
    refine h_stam J_X J_Y J_sum
      ((h_reg_X.reg_at t ht).density_t)
      ((h_reg_Y.reg_at t ht).density_t)
      ((h_reg_sum.reg_at t ht).density_t)
      hJX_pos hJY_pos hJsum_pos ?_ ?_ ?_ h_regdens_X h_regdens_Y
      h_norm_X h_norm_Y h_conv_id h_blachman
    · -- `J_X = (fisherInfoOfMeasureV2 (P.map (X+√t·Z_X)) fX).toReal`
      rw [hJX_def]
      rfl
    · -- `J_Y = (fisherInfoOfMeasureV2 (P.map (Y+√t·Z_Y)) fY).toReal`
      rw [hJY_def]
      rfl
    · -- `J_sum = (fisherInfoOfMeasureV2 (P.map ((X+√t·Z_X)+(Y+√t·Z_Y))) fXY).toReal`
      rw [hJsum_def]
      rfl
  -- The genuine arithmetic core closes the goal from plain Stam + positivity.
  exact csiszar_ratio_deriv_le_zero_arith J_X J_Y J_sum N_X N_Y
    hJX_pos hJY_pos hJsum_pos hNX_pos hNY_pos h_plain_stam

/-- **R-4-b — EPI recovery bridge from `r(0) ≥ 0`**.

The log-ratio gap at `t = 0` is `r(0) = log (eP(X+Y)) − log (eP X + eP Y)`
(`csiszarLogRatioGap_at_zero`). Since both `eP(X+Y)` and `eP X + eP Y` are
strictly positive (`entropyPower_pos`, `add_pos`), `0 ≤ r(0)` is equivalent to
`eP X + eP Y ≤ eP(X+Y)` by `Real.log_le_log_iff`, i.e. the entropy power
inequality.

Genuine bridge — no `sorry`, no load-bearing hypotheses. -/
theorem epi_of_csiszarLogRatioGap_zero_nonneg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω)
    (h_nonneg : 0 ≤ InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P 0) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  rw [InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap_at_zero] at h_nonneg
  -- `0 ≤ log A − log B` ⟺ `log B ≤ log A`.
  have h_log_le : Real.log (entropyPower (P.map X) + entropyPower (P.map Y))
      ≤ Real.log (entropyPower (P.map (fun ω => X ω + Y ω))) := by linarith
  -- Positivity of both `log` arguments.
  have hA_pos : 0 < entropyPower (P.map (fun ω => X ω + Y ω)) := entropyPower_pos _
  have hB_pos : 0 < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- `log B ≤ log A ⟺ B ≤ A` (both positive).
  rw [Real.log_le_log_iff hB_pos hA_pos] at h_log_le
  exact h_log_le

/-- **R-5-a — `csiszarLogRatioGap X Y Z_X Z_Y P` is differentiable on the
interior `Set.Ioi 0 = interior (Set.Ici 0)`**, via R-2
(`csiszarLogRatioGap_hasDerivAt`) + `HasDerivAt.differentiableAt`.

Genuine: R-2 is `@audit:ok` (sorryAx-free), so this differentiability is
transparently genuine. (The difference-version differentiability lemma was
deleted with the dead de Bruijn difference subgraph.) -/
theorem csiszarLogRatioGap_differentiableOn_interior
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P) :
    DifferentiableOn ℝ
      (fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P t)
      (interior (Set.Ici (0 : ℝ))) := by
  rw [interior_Ici]
  intro t ht
  have ht_pos : (0 : ℝ) < t := ht
  exact ((csiszarLogRatioGap_hasDerivAt X Y Z_X Z_Y P
    hX hZX hXZX hY hZY hYZY hXYZXY
    h_reg_sum h_reg_X h_reg_Y ht_pos).differentiableAt).differentiableWithinAt

-- **R-5-b (full-ray `ContinuousOn (Set.Ici 0)`) DELETED (surface shrink, 2026-06-04)**:
-- the full-ray continuity consumed the wall atom three times along *every* ray
-- point. After the surface shrink it had no consumer (R-5-c now derives interior
-- `AntitoneOn` from differentiability and re-attaches the endpoint via the
-- endpoint-only `csiszarLogRatioGap_continuousWithinAt_zero` below). Removing it
-- confines the wall to the single endpoint.

/-- **R-5-b' — endpoint continuity `ContinuousWithinAt (Set.Ioi 0) 0` of
`csiszarLogRatioGap X Y Z_X Z_Y P`**.

The endpoint (`t = 0⁺`) version of R-5-b, mirroring the full-ray composition but
using the shrunk shared atom `heatFlowEntropyPower_continuousWithinAt_zero`
(`wall:heatflow-continuity`, endpoint only) three times, then the genuine
`ContinuousWithinAt.log` / `.add` / `.sub` composition (with `entropyPower_pos` /
`add_pos` discharging the `≠ 0` premises).

This consumer carries **no `@residual`**: the only `sorry` lives in the shared
`wall:heatflow-continuity` lemma, now confined to the single endpoint. The
interior `t > 0` continuity is supplied genuinely by R-5-a
(`csiszarLogRatioGap_differentiableOn_interior`, `.continuousOn`) on the consumer
side (R-5-c). -/
theorem csiszarLogRatioGap_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P) :
    ContinuousWithinAt
      (fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P t)
      (Set.Ioi (0 : ℝ)) 0 := by
  have h_sum := heatFlowEntropyPower_continuousWithinAt_zero
    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P h_endpt_sum
  have h_X := heatFlowEntropyPower_continuousWithinAt_zero X Z_X P h_endpt_X
  have h_Y := heatFlowEntropyPower_continuousWithinAt_zero Y Z_Y P h_endpt_Y
  unfold InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
  exact (h_sum.log (entropyPower_pos _).ne').sub
    ((h_X.add h_Y).log (add_pos (entropyPower_pos _) (entropyPower_pos _)).ne')

/-- **R-5-c — `AntitoneOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici 0)`**,
the genuine log-ratio EPI gap is antitone on the heat-flow ray `[0, ∞)`.

Mirrors the (deleted) difference-version antitone lemma:
applies `antitoneOn_of_deriv_nonpos` with the convex domain `Set.Ici 0`
(`convex_Ici`), R-5-b (continuity), R-5-a (differentiability), and the per-`t`
`deriv ≤ 0` from R-2 (`csiszarLogRatioGap_hasDerivAt.deriv`) + R-3
(`csiszarLogRatioGap_deriv_le_zero`).

Genuine assembly: this lemma carries **no new `@residual`**. It transitively
inherits the G2 continuity wall (through R-5-b) and the plain-Stam extraction
gap (through R-3); the assembly itself is genuine, exactly like D6's honesty
structure. -/
theorem csiszarLogRatioGap_antitoneOn_Ici_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hY : Measurable Y) (hZY : Measurable Z_Y) (hYZY : IndepFun Y Z_Y P)
    (hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_sum : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_reg_X : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P)
    (h_reg_Y : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp Y Z_Y P)
    (h_endpt_sum : InformationTheory.Shannon.IsHeatFlowEndpointRegular
                    (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P)
    (h_endpt_X : InformationTheory.Shannon.IsHeatFlowEndpointRegular X Z_X P)
    (h_endpt_Y : InformationTheory.Shannon.IsHeatFlowEndpointRegular Y Z_Y P)
    (h_pos_stam : ∀ (t : ℝ) (ht : 0 < t),
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_X.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_Y.reg_at t ht).density_t)) ∧
      (0 < InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensityReal
              ((h_reg_sum.reg_at t ht).density_t)) ∧
      InformationTheory.Shannon.EPIStamDischarge.IsStamInequalityHyp
        (fun ω => X ω + Real.sqrt t * Z_X ω)
        (fun ω => Y ω + Real.sqrt t * Z_Y ω) P ∧
      -- ↓ 案 B (R-3‴): per-`t` caller-supplied regularity preconditions threaded to R-3.
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_X.reg_at t ht).density_t) ∧
      InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        ((h_reg_Y.reg_at t ht).density_t) ∧
      (∫ x, (h_reg_X.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∫ x, (h_reg_Y.reg_at t ht).density_t x ∂MeasureTheory.volume = 1) ∧
      (∀ x, (h_reg_sum.reg_at t ht).density_t x
            = InformationTheory.Shannon.EPIConvDensity.convDensityAdd
                ((h_reg_X.reg_at t ht).density_t)
                ((h_reg_Y.reg_at t ht).density_t) x) ∧
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        ((h_reg_X.reg_at t ht).density_t)
        ((h_reg_Y.reg_at t ht).density_t)) :
    AntitoneOn
      (fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
        X Y Z_X Z_Y P t)
      (Set.Ici (0 : ℝ)) := by
  -- **Surface shrink (2026-06-04)**: derive `AntitoneOn` on the *interior*
  -- `Set.Ioi 0` genuinely (continuity there is `differentiableOn.continuousOn`,
  -- **no wall**), then re-attach the endpoint `0` via the endpoint-only wall atom
  -- `csiszarLogRatioGap_continuousWithinAt_zero` + `AntitoneOn.insert_of_continuousWithinAt`.
  set f := fun t : ℝ => InformationTheory.Shannon.EPIL3Integration.csiszarLogRatioGap
    X Y Z_X Z_Y P t with hf_def
  -- Genuine interior differentiability (= continuity) on `Set.Ioi 0`.
  have h_diff_Ioi : DifferentiableOn ℝ f (Set.Ioi 0) := by
    have := csiszarLogRatioGap_differentiableOn_interior X Y Z_X Z_Y P
      hX hZX hXZX hY hZY hYZY hXYZXY h_reg_sum h_reg_X h_reg_Y
    rwa [interior_Ici] at this
  -- `AntitoneOn f (Set.Ioi 0)`, genuine (no wall): continuity on `Ioi 0` is the
  -- interior differentiability, `interior (Ioi 0) = Ioi 0`, deriv ≤ 0 from R-2 + R-3.
  have h_anti_Ioi : AntitoneOn f (Set.Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) h_diff_Ioi.continuousOn
      (by rw [interior_Ioi]; exact h_diff_Ioi) ?_
    intro t ht
    rw [interior_Ioi] at ht
    have ht_pos : (0 : ℝ) < t := ht
    obtain ⟨hJX_pos, hJY_pos, hJsum_pos, h_stam, h_regdens_X, h_regdens_Y,
            h_norm_X, h_norm_Y, h_conv_id, h_blachman⟩ := h_pos_stam t ht_pos
    have h_deriv := csiszarLogRatioGap_hasDerivAt X Y Z_X Z_Y P
      hX hZX hXZX hY hZY hYZY hXYZXY
      h_reg_sum h_reg_X h_reg_Y ht_pos
    have h_le := csiszarLogRatioGap_deriv_le_zero X Y Z_X Z_Y P
      h_reg_sum h_reg_X h_reg_Y ht_pos hJX_pos hJY_pos hJsum_pos h_stam
      h_regdens_X h_regdens_Y h_norm_X h_norm_Y h_conv_id h_blachman
    rw [h_deriv.deriv]
    exact h_le
  -- Endpoint `0` is a (left) cluster point of `Set.Ioi 0`.
  have h_cluster : ClusterPt (0 : ℝ) (Filter.principal (Set.Ioi 0)) := by
    rw [← mem_closure_iff_clusterPt, closure_Ioi]
    exact Set.self_mem_Ici
  -- Endpoint continuity from the shrunk wall atom (R-5-b').
  have h_cont_zero : ContinuousWithinAt f (Set.Ioi 0) 0 :=
    csiszarLogRatioGap_continuousWithinAt_zero X Y Z_X Z_Y P
      h_endpt_sum h_endpt_X h_endpt_Y
  -- Insert the endpoint: `insert 0 (Ioi 0) = Ici 0`.
  have := h_anti_Ioi.insert_of_continuousWithinAt h_cluster h_cont_zero
  rwa [Set.Ioi_insert] at this

-- **Difference-gap derivative route DELETED (R-5 rewire 2026-06-01 + dead
-- de Bruijn difference subgraph deletion)**: the false-as-framed difference-gap
-- derivative bound `eP_sum·J_sum ≤ eP_X·J_X + eP_Y·J_Y` does NOT follow from plain
-- harmonic Stam. The genuine successor is the RATIO route R-3
-- (`csiszarLogRatioGap_deriv_le_zero` : `J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0`),
-- closable from plain Stam (ratio weights `α,β` with `α²≤α`).

/-! ## §5 — Predicate manipulation: symmetry, congruence, pass-through -/

/-! ## §6 — Chain forms (3-arg / 4-arg) via scaling decomposition -/

/-! ## §7 — Round-trip / sanity-check theorems -/

end InformationTheory.Shannon.EPIStamToBridge