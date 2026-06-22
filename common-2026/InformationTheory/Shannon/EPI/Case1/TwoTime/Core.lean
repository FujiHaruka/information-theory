import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.EPIBridge
import InformationTheory.Shannon.FisherInfo.DeBruijnGeneral
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Case1.RatioLimit
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.Monotone.Basic

/-!
# EPI case-1 two-time object — Core (§0)

Matched-time path abbreviations shared across the two-time object split
(`TwoTimePaths.lean` = §1 path existence, `TwoTimeObject.lean` = §2–§4).
Verbatim split of `TwoTime.lean` §0; proofs unchanged. Umbrella: `TwoTime.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace InformationTheory.Shannon.EPICase1TwoTime

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.StamEPIBridge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap)
open InformationTheory.Shannon.EPIStamToBridge (entropyPower_hasDerivAt_of_diffEnt_hasDerivAt)
open InformationTheory.Shannon.EPICase1RatioLimit
  (entropyPower_rescaled_path_tendsto entropyPower_path_scaling IsRescaledPathRegular)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## §0 — Matched-time path abbreviations

The single-source heat-flow entropy power `N_A(s) = entropyPower (P.map (A + √s·B))`.
The matched path `s(t)` is the inverse of `N_A` solving `N_A(s(t)) = N_A(0)·eᵗ`.
-/

/-- Single-source heat-flow entropy power along the perturbation `A + √s·B`.
`N_A(0) = entropyPower (P.map A)`. -/
noncomputable def heatFlowEP (A B : Ω → ℝ) (P : Measure Ω) (s : ℝ) : ℝ :=
  entropyPower (P.map (fun ω ↦ A ω + Real.sqrt s * B ω))

/-- **Matched-time path predicate** (output of the inverse-function construction).

For a path `s : ℝ → ℝ` along the `A`-perturbation, this records that:
* `s` starts at `0` (`s 0 = 0`);
* the entropy power grows as `eᵗ`: `N_A(s(t)) = N_A(0)·eᵗ` for `t ≥ 0`
(the matched-time `e^t` characterization, proof-log §formulation gate);
* `s` is continuous on `[0, ∞)`;
* on the interior `t > 0`, `s` has derivative `1/J_A(s(t))` (FII-matched
velocity), where `J_A` is the Fisher info of the perturbed density.

This is **not** a load-bearing hypothesis on the EPI conclusion: it is the
genuine output of `matchedTimePath_exists` (inverse-function subproject), whose
inputs are only regularity preconditions (`J_A > 0`, measurability, indep). -/
structure IsMatchedTimePath (A B : Ω → ℝ) (P : Measure Ω)
    (J_A : ℝ → ℝ) (s : ℝ → ℝ) : Prop where
  /-- The path starts at time `0`. -/
  start_zero : s 0 = 0
  /-- Matched `e^t` growth of the single-source entropy power. -/
  matched_growth : ∀ t : ℝ, 0 ≤ t → heatFlowEP A B P (s t) = heatFlowEP A B P 0 * Real.exp t
  /-- The path is continuous on `[0, ∞)`. -/
  cont : ContinuousOn s (Set.Ici 0)
  /-- FII-matched velocity on the interior. -/
  deriv_at : ∀ t : ℝ, 0 < t → HasDerivAt s (1 / J_A (s t)) t


end InformationTheory.Shannon.EPICase1TwoTime
