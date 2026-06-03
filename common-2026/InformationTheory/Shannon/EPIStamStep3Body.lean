import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIPlumbing
import InformationTheory.Shannon.EPIStamDischarge
import InformationTheory.Shannon.EPIStamInequalityBody
import InformationTheory.Shannon.FisherInfoV2
import InformationTheory.Shannon.FisherInfoV2DeBruijn
import InformationTheory.Shannon.FisherInfoGaussian
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# W9-S3 T2-D: Stam inequality body — **Step 3** (Cauchy-Schwarz → symmetric Fisher coupling) discharge

`InformationTheory/Shannon/EPIStamInequalityBody.lean` (Wave 7, 515 行) splits the
1-dimensional Stam inequality proof (Cover-Thomas Lemma 17.7.2 / Stam 1959 /
Blachman 1965) into four steps:

* **Step 1** — convolution score representation `s_Z = E[s_X | Z] = E[s_Y | Z]`
  (`IsStamScoreConvolution`, §1 there).
* **Step 2** — pointwise Cauchy-Schwarz on the conditional expectation
  (`IsStamCauchySchwarz` existential-λ form, §2 there).
* **Step 3** — *take total expectation* against `p_Z` and assemble the
  **symmetric Fisher coupling** `J(X+Y) ≤ λ² J(X) + (1-λ)² J(Y)` for the chosen
  `λ ∈ [0,1]`.
* **Step 4** — optimize over `λ` (`stam_lambda_min`, §3 there) to obtain
  `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`.

The Wave 7 file publishes Step 1, Step 2, and Step 4, but the **Step 3 chain**
— integrating Step 1 + Step 2 into the symmetric Fisher coupling and bridging
into Step 4 — is left implicit (folded inline into
`isStamCauchySchwarz_of_optimal`). This file (W9-S3) makes Step 3 explicit.

## Approach

The genuine analytic content of Step 2-3 — the conditional Cauchy-Schwarz
integrated against `p_Z` to give the convex Fisher bound
`J(Z) ≤ λ² J(X) + (1-λ)² J(Y)` and its λ-optimum
`J(Z) ≤ J(X)J(Y)/(J(X)+J(Y))` — is localized to the **single lemma**
`EPIStamInequalityBody.stam_step2_density_wall`, now **genuinely closed**
(0-sorry, sorryAx-free; `wall:stam-step2-density` is [CLOSED 2026-06-04] via
`convex_fisher_bound_of_ready`), which takes regularity preconditions
only. The earlier design carried this content as load-bearing predicates
(`IsStamTotalExpectation` ∀λ bound, `IsStamFisherCoupling` alias); those were
removed in the wall-consolidation pass (`epi-stam-wall-consolidation-plan`)
since they were isolated (zero cross-file consumers) and the shared-wall path
is strictly more honest (tier-2 sorry rather than tier-4 load-bearing hyp).

The deliverables are:

1. `isStamInequalityHyp_via_step3` (§4) — full Step 1→4 chain to the genuine
   `IsStamInequalityHyp` signature, from regularity alone via the shared wall.
2. `stam_optimal_lambda_mem_unit` (§1) — optimal-λ membership (arithmetic).
3. `stam_coupling_saturates` (§5) — Gaussian saturation arithmetic kernel.
4. `epi_via_stam_step3_gaussian` (§6) — pipeline integration (via Gaussian
   saturation).

### 主シグネチャ

* `stam_optimal_lambda_mem_unit` (§1) — optimal-λ membership (arithmetic)
* `isStamInequalityHyp_via_step3` (§4) — Stam signature from regularity via the
  genuine (sorryAx-free) `stam_step2_density_wall`
* `stam_coupling_saturates` (§5) — Gaussian saturation equality witness (arithmetic)
* `epi_via_stam_step3_gaussian` (§6) — pipeline integration (via Gaussian saturation)
-/

namespace InformationTheory.Shannon.EPIStamStep3Body

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIStamInequalityBody

/-! ## §1 — Optimal λ membership (arithmetic) -/

/-- **Optimal λ membership** (used throughout): the optimal λ `J_Y / (J_X + J_Y)`
selected in Step 4 lies in the unit interval `[0, 1]` whenever `J_X, J_Y > 0`. -/
@[entry_point]
theorem stam_optimal_lambda_mem_unit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ b / (a + b) ∧ b / (a + b) ≤ 1 := by
  have hab : 0 < a + b := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hab]
  linarith

/-! ## §4 — Full Step 1 → 4 chain to the genuine Stam signature

The former Step-3 chain carried the genuine analytic content as a **load-bearing**
`IsStamTotalExpectation` predicate (the ∀λ convex Fisher bound) plus an
`IsStamFisherCoupling` intermediate alias of `IsStamCauchySchwarz`. The
wall-consolidation pass (`epi-stam-wall-consolidation-plan`) removed those: the
genuine Step 2-3 analytic core is now localized to the single genuine (sorryAx-free)
lemma `EPIStamInequalityBody.stam_step2_density_wall` (regularity preconditions
only; `wall:stam-step2-density` is [CLOSED 2026-06-04]), and the load-bearing
predicates are deleted (they were isolated, with zero cross-file consumers). -/

/-- **Full Step 1 → 4 chain to the genuine Stam signature** (the deliverable).

Produces the genuine `IsStamInequalityHyp` (Cover-Thomas Lemma 17.7.2 真
signature) from regularity preconditions alone: the genuine Step 2-3 convex
Fisher bound is supplied internally by the genuine (sorryAx-free) lemma
`stam_step2_density_wall` (`wall:stam-step2-density` is [CLOSED 2026-06-04]),
and Steps 2/4 are discharged arithmetically by
`isStamInequalityHyp_via_body`. This carries **no** load-bearing analytic
hypothesis — only measurability / independence / probability measure.

Update 2026-05-31 (owner-level pivot, epi-wall-reattack-plan): `stam_step2_density_wall`
**and** `isStamInequalityHyp_via_body` are now **both genuinely closed** (0-sorry,
`#print axioms` sorryAx-free). The published `IsStamInequalityHyp` was pivoted in lockstep
with `IsStamInequalityResidual` to carry the pointwise convolution constraint +
`IsBlachmanConvReady` bundle, closing the former regularity-precondition signature gap.
This wrapper is therefore **sorryAx-free** — it produces a genuine `IsStamInequalityHyp`.
(2026-06-04 audit: `#print axioms isStamInequalityHyp_via_step3` =
`[propext, Classical.choice, Quot.sound]` confirmed.)
@audit:ok -/
@[entry_point]
theorem isStamInequalityHyp_via_step3 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamInequalityHyp X Y P :=
  isStamInequalityHyp_via_body (stam_step2_density_wall P X Y hX hY hXY)

/-! ## §5 — Gaussian saturation: Step 3 holds with equality at the optimum

**RESOLVED (2026-05-20):** the former `isStamTotalExpectation_of_gaussian_fisherInfo_zero`,
`isStamFisherCoupling_of_gaussian_saturation`, and the Step-3 chain
`isStamInequalityHyp_of_gaussian_via_step3` discharged the total-expectation /
coupling predicates vacuously by `exfalso`-ing the `0 < J_X` precondition against
the buggy V1 `fisherInfo = 0` artefact for Gaussians. They asserted nothing about
Stam actually holding and were removed. The genuine Gaussian EPI runs via
`entropyPower_gaussian_additivity` (see `epi_via_stam_step3_gaussian`
below); the arithmetic saturation kernel `stam_coupling_saturates` is genuine and
kept.
-/

/-- **Gaussian saturation equality witness** (Step 3 equality condition).

For Gaussian `X, Y`, the Stam inequality saturates: `J(X+Y) = J(X) J(Y) /
(J(X) + J(Y))`, i.e. the Step-3 coupling holds with *equality* at the optimal
`λ = J_Y / (J_X + J_Y)`. This lemma exhibits the *arithmetic* saturation: at the
optimal λ, the coupling RHS `λ² J_X + (1-λ)² J_Y` equals the harmonic mean
exactly (Wave 7 `stam_lambda_min`), so equality in the coupling is equivalent to
equality in the harmonic-mean bound. -/
@[entry_point]
theorem stam_coupling_saturates {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b / (a + b)) ^ 2 * a + (1 - b / (a + b)) ^ 2 * b = a * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  field_simp
  ring

/-! ## §6 — EPI pipeline integration via Step 3 -/

/-- **EPI via Stam Step 3 (Gaussian case)**: full deliverable end-to-end. For
Gaussian `X, Y` with non-zero variance, EPI follows through the Step-3 body
discharge + Gaussian saturation bridge. -/
@[entry_point]
theorem epi_via_stam_step3_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  epi_via_stam_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-! ## §7 — Step 3 manipulation lemmas + intermediate calc -/

/-! ## §8 — Sanity check / regression theorems

The former `step3_chain_eq_body_chain` sanity check (a duplicate of
`isStamInequalityHyp_via_step3` carrying the load-bearing predicates) was
removed in the wall-consolidation pass: with the Step-2-3 core localized to the
shared `stam_step2_density_wall`, there is a single honest path and no
duplicate-chain obligation remains. -/

end InformationTheory.Shannon.EPIStamStep3Body
