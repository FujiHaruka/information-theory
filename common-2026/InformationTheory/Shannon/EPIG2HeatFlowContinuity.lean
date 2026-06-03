import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIStamDischarge

/-!
# G2: heat-flow entropy-power continuity at the endpoint `t = 0⁺`

This file isolates the single analytic atom shared by the two EPI continuity
consumers in `EPIStamToBridge.lean`:

* `csiszarLogRatioGap_continuousOn` (R-5-b, live: feeds `antitoneOn_of_deriv_nonpos`
  in R-5-c), and
* `csiszarGap1Source_continuousOn` (A-4-1, dead difference version).

Both reduce, at the endpoint `t = 0`, to the continuity of a single term
`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` as `t → 0⁺` along the
heat-flow ray. The interior `t > 0` is genuine (already supplied by
`csiszarGap1Source_differentiableOn_interior` / `csiszarLogRatioGap_differentiableOn_interior`).

## GATE verdict (2026-06-03): NO-GO — `wall:heatflow-continuity`

The endpoint continuity hinges on a `t = 0⁺`-uniform integrable pointwise
majorant `g` with `‖negMulLog (f_t x)‖ ≤ g x` for all small `t`, required by
`MeasureTheory.continuousWithinAt_of_dominated`. Such a `g` cannot be built from
the fields available in `IsDeBruijnRegularityHyp`:

* The only smoothed-density envelopes (`convDensityAdd_logFactor_poly_majorant`,
  `_chain_domination`, `gaussGradMaj`, all in `FisherInfoV2DeBruijnAssembly.lean`,
  all `private`) are **fixed-`t`** with constants that **diverge as `t → 0⁺`**
  (`A_up ⊃ (1/2)·log(4πt) + 2R²/t`, slope `B = 2/t`) and are restricted to
  `s ∈ Ioo (t/2, 2t)` — explicitly bounded away from `0`.
* The regularity fields supply only `pX_nn`, `pX_meas`, `pX_law` (an L¹ density)
  and `pX_mom` (finite second moment) — no L^∞ / continuity control on `pX`. For a
  general L¹ + finite-second-moment density `pX`, `negMulLog (pX ∗ g_t)` admits no
  single `t`-uniform integrable pointwise envelope as `t → 0⁺` (e.g. `pX` with an
  integrable singularity).

`entropyPower` / `differentialEntropy` continuity is absent in both Mathlib and
InformationTheory (loogle: 0 declarations). The endpoint atom is therefore parked
as a shared sorry lemma `heatFlowEntropyPower_continuousOn` with
`@residual(wall:heatflow-continuity)`. The DCT machinery
(`continuousWithinAt_of_dominated`) itself is fully present in Mathlib; the wall
is the uniform majorant only.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality

/-- **G2 shared wall lemma** — the single heat-flow entropy-power continuity
atom underlying both EPI continuity consumers.

`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` is `ContinuousOn` the ray
`Set.Ici 0`. Both consumers (`csiszarLogRatioGap_continuousOn`,
`csiszarGap1Source_continuousOn`) reduce to three instances of this single term.

The endpoint `t = 0⁺` is the analytic content. Its proof would go through
`MeasureTheory.continuousWithinAt_of_dominated` on the density integrand
`negMulLog (f_t x)`, whose only missing premise is a `t = 0⁺`-uniform integrable
pointwise majorant. That majorant is not derivable from `IsDeBruijnRegularityHyp`
(see file header GATE verdict, 2026-06-03 NO-GO) and `entropyPower` /
`differentialEntropy` continuity is absent from both Mathlib and InformationTheory
(loogle: 0 declarations). The interior `t > 0` continuity threads through the same
heat-flow density continuity; its genuine single-term assets require measurability
/ independence data not present in this regularity-only signature, so the whole
ray is closed by one wall atom. This is a true continuity claim with body `sorry`;
no continuity conclusion is taken as a hypothesis.

Independent honesty audit 2026-06-04 (fresh subagent): signature honest (true
`ContinuousOn` claim, no conclusion-as-hypothesis, `IsDeBruijnRegularityHyp`
fields are regularity-only — density witness / per-`t` V2 regularity /
interval-integrability, none a continuity claim), non-vacuous (Gaussian
inhabitant), `wall:heatflow-continuity` classification confirmed (loogle: 0
`entropyPower`/`differentialEntropy` × `Continuous` in Mathlib + InformationTheory;
DCT machinery present, uniform-majorant gap genuine). honest_residual.

@residual(wall:heatflow-continuity) -/
theorem heatFlowEntropyPower_continuousOn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) :
    ContinuousOn
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ici (0 : ℝ)) := by
  sorry

end InformationTheory.Shannon
