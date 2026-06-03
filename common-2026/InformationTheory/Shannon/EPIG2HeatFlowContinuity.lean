import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Monotone
import Mathlib.Order.Monotone.Basic
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

## Surface shrink (2026-06-04): full ray → endpoint `t = 0⁺` only

The shared wall is now `heatFlowEntropyPower_continuousWithinAt_zero`, claiming
only `ContinuousWithinAt (Set.Ioi 0) 0` (the single endpoint limit `t → 0⁺`),
not the full-ray `ContinuousOn (Set.Ici 0)`. The interior `t > 0` continuity is
recovered *genuinely* on the consumer side (`EPIStamToBridge.lean`) from
`csiszarLogRatioGap_differentiableOn_interior` (`.continuousOn`, no wall), and the
endpoint is re-attached with the OrderDual mirror
`AntitoneOn.insert_of_continuousWithinAt` (added in this file). Net honesty gain:
the residual shrinks from "continuity along every ray point" to "continuity at the
single endpoint `t = 0⁺`"; the interior is now honest-genuine.

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
as a shared sorry lemma `heatFlowEntropyPower_continuousWithinAt_zero` with
`@residual(wall:heatflow-continuity)`. The DCT machinery
(`continuousWithinAt_of_dominated`) itself is fully present in Mathlib; the wall
is the uniform majorant only.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality

/-- **AntitoneOn endpoint-insert** — the OrderDual mirror of
`MonotoneOn.insert_of_continuousWithinAt`. If `f` is `AntitoneOn s` and
left-continuous-within-`s` at a cluster point `x`, then `f` is `AntitoneOn` the
augmented set `insert x s`. Used to re-attach the endpoint `t = 0` to the genuine
interior `AntitoneOn (Set.Ioi 0)`.

Mathlib has the monotone version only; this is its dual via `OrderDual.toDual`
(an order-reversing homeomorphism on `β`), which sends `AntitoneOn f s` to
`MonotoneOn (toDual ∘ f) s` and preserves `ContinuousWithinAt`.

Independent honesty audit 2026-06-04 (fresh subagent): genuine 0 sorry, sorryAx-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`)、循環なし (body は
Mathlib `MonotoneOn.insert_of_continuousWithinAt` の OrderDual mirror、`:= h` でない)、
型クラス制約 (`OrderClosedTopology β` 等) は monotone 版と整合。
@audit:ok -/
theorem _root_.AntitoneOn.insert_of_continuousWithinAt
    {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [TopologicalSpace β] [LinearOrder β] [OrderClosedTopology β]
    {f : α → β} {s : Set α} {x : α}
    (hf : AntitoneOn f s) (hx : ClusterPt x (Filter.principal s))
    (h'x : ContinuousWithinAt f s x) :
    AntitoneOn f (insert x s) := by
  -- `AntitoneOn f s` is `MonotoneOn (toDual ∘ f) s`; apply the monotone insert.
  have hmono : MonotoneOn (fun a => OrderDual.toDual (f a)) s := hf.dual_right
  have hcont : ContinuousWithinAt (fun a => OrderDual.toDual (f a)) s x :=
    continuous_toDual.continuousWithinAt.comp h'x (Set.mapsTo_univ _ _)
  exact (hmono.insert_of_continuousWithinAt hx hcont).dual_right

/-- **G2 shared wall lemma (endpoint version)** — heat-flow entropy-power
continuity at the single endpoint `t = 0⁺`.

`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` is `ContinuousWithinAt
(Set.Ioi 0) 0` (the limit `t → 0⁺`). The live consumer
(`csiszarLogRatioGap_continuousWithinAt_zero`) reduces to three instances of this
single endpoint term; the interior `t > 0` continuity is supplied separately and
genuinely from `csiszarLogRatioGap_differentiableOn_interior` (`.continuousOn`),
so the wall is confined to the one endpoint atom.

The endpoint `t = 0⁺` is the analytic content. Its proof would go through
`MeasureTheory.continuousWithinAt_of_dominated` on the density integrand
`negMulLog (f_t x)`, whose only missing premise is a `t = 0⁺`-uniform integrable
pointwise majorant. That majorant is not derivable from `IsDeBruijnRegularityHyp`
(see file header GATE verdict, 2026-06-03 NO-GO) and `entropyPower` /
`differentialEntropy` continuity is absent from both Mathlib and InformationTheory
(loogle: 0 declarations). This is a true continuity claim with body `sorry`; no
continuity conclusion is taken as a hypothesis. `IsDeBruijnRegularityHyp` fields
are regularity-only (density witness / per-`t` V2 regularity /
interval-integrability), none a continuity claim.

Surface shrink (2026-06-04): the predecessor `heatFlowEntropyPower_continuousOn`
claimed the full ray `ContinuousOn (Set.Ici 0)`; this version shrinks the residual
to the single endpoint, with the interior recovered genuinely on the consumer side.

Independent honesty audit 2026-06-04 (fresh subagent, post-shrink): 端点
`ContinuousWithinAt (Set.Ioi 0) 0` 縮小後も signature honest (連続性結論を hyp に
bundle せず、`IsDeBruijnRegularityHyp` は density/per-`t` V2 regularity/interval-
integrability の regularity-only) / classification `wall:heatflow-continuity` 確認
(loogle: `entropyPower`/`differentialEntropy` 0 decls in Mathlib、DCT
`continuousWithinAt_of_dominated` は present = 壁は uniform majorant のみ) / 非空虚
(Gaussian inhabitant) / interior `t > 0` は consumer 側 (R-5-c) で
`differentiableOn.continuousOn` genuine。shared sorry 1 件に集約 (consumer
`csiszarLogRatioGap_continuousWithinAt_zero` / `_antitoneOn_Ici_zero` は own
`@residual` 無し、sorryAx は本壁経由の transitive のみ機械確認)。

@residual(wall:heatflow-continuity) -/
theorem heatFlowEntropyPower_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi (0 : ℝ)) 0 := by
  sorry

end InformationTheory.Shannon
