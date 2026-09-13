import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.EPI.Unconditional.Dispatch

/-!
# Discharging the Stam-to-EPI bridge under absolute continuity

The bridge predicate `IsStamToEPIBridgeHyp X Y P` is an implication whose conclusion is the
entropy power inequality itself. This file inhabits it from regularity preconditions alone, by
routing through the absolutely-continuous entropy power inequality
`entropy_power_inequality_of_ac`, which discharges the conclusion without consuming the Stam
antecedent. Together with the Gaussian producer `isStamToEPIBridgeHyp_of_gaussian`, these are
the two classes of pairs for which the bridge is inhabited from regularity alone; for a general
pair `X`, `Y` it stays an assumption.

## Main statements

* `isStamToEPIBridgeHyp_of_ac` — the Stam-to-EPI bridge holds whenever both push-forwards are
  absolutely continuous with finite differential entropy.

## Implementation notes

The producer lives in its own file because `EPI/Stam/EPIBridge.lean` cannot import
`EPI/Unconditional/Dispatch.lean`: the dispatch already depends on `EPI/Stam/EPIBridge.lean`
through the case-1 smoothing-limit chain, so the reverse import would close a cycle.
-/

namespace InformationTheory.Shannon.StamEPIBridge

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality

/-- The Stam-to-EPI bridge holds for independent `X`, `Y` whose push-forwards are absolutely
continuous with finite differential entropy. The conclusion is supplied by the a.c. entropy
power inequality `entropy_power_inequality_of_ac`, so the Stam antecedent is never used; every
hypothesis here is a regularity precondition (measurability, independence, absolute continuity,
finite differential entropy) inherited verbatim from that route.

@audit:ok -/
theorem isStamToEPIBridgeHyp_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x ↦ Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x ↦ Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    IsStamToEPIBridgeHyp X Y P :=
  have h_epi : IsEntropyPowerInequalityHypothesis X Y P :=
    entropy_power_inequality_of_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent
  isStamToEPIBridgeHyp_of_epi h_epi

end InformationTheory.Shannon.StamEPIBridge
