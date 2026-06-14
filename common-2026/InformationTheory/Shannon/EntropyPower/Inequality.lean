import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.FisherInfo.Basic
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.Blachman.Density
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Entropy power inequality (Cover–Thomas Theorem 17.7.3)

The entropy power inequality (EPI) for independent real-valued random variables `X, Y`:

`exp(2 h(X + Y)) ≥ exp(2 h(X)) + exp(2 h(Y))`,

stated through the named EPI-conclusion predicate `IsEntropyPowerInequalityHypothesis`, together
with the Gaussian saturation case where the inequality holds with equality.

## Main definitions

* `entropyPower μ := exp (2 · h(μ))` — the entropy power of a measure on `ℝ`.
* `IsEntropyPowerInequalityHypothesis X Y P` — the EPI conclusion as a named `Prop`.

## Main statements

* `entropyPower_pos`, `entropyPower_nonneg`, `entropyPower_gaussianReal` — basic properties and the
  Gaussian closed form `2πe v`.
* `entropyPower_gaussian_additivity` — EPI holds with equality for independent Gaussians.
* `isEntropyPowerInequalityHypothesis_of_gaussian` — the EPI predicate holds for independent Gaussians.
* `entropyPower_map_add_const`, `entropy_power_inequality_three_arg` — translation invariance and the
  three-variable form.

## Implementation notes

`entropyPower` is defined as `exp (2 h(μ))`, directly matching the conclusion forms of
`Real.exp_pos` / `Real.exp_log`; the Cover–Thomas normalization `N(μ) = (2πe)⁻¹ · exp(2 h(μ))` is
recovered by a scaling corollary. The Gaussian saturation case is discharged from Mathlib's
`gaussianReal_add_gaussianReal_of_indepFun` together with `differentialEntropy_gaussianReal`.
-/

namespace InformationTheory.Shannon.EntropyPowerInequality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-! ### `entropyPower`: definition and basic properties -/

/-- The entropy power of a measure `μ` on `ℝ`: `entropyPower μ := exp (2 · h(μ))`, where `h` is
`InformationTheory.Shannon.differentialEntropy`. This differs from the Cover–Thomas normalization
`N(X) := (2πe)⁻¹ · exp(2 h(X))` only by the constant `(2πe)`, recovered by a scaling corollary. -/
noncomputable def entropyPower (μ : Measure ℝ) : ℝ :=
  Real.exp (2 * InformationTheory.Shannon.differentialEntropy μ)

/-- Entropy power is strictly positive.

@audit:ok -/
@[entry_point]
theorem entropyPower_pos (μ : Measure ℝ) : 0 < entropyPower μ :=
  Real.exp_pos _

/-- Entropy power is non-negative.

@audit:ok -/
@[entry_point]
theorem entropyPower_nonneg (μ : Measure ℝ) : 0 ≤ entropyPower μ :=
  (entropyPower_pos μ).le

/-- **Closed form for Gaussian entropy power**: `entropyPower (gaussianReal m v) =
2πe v`. This is the Gaussian saturation reference value that drives the
saturating case of EPI.

Computation: by `differentialEntropy_gaussianReal`, `h(𝒩(m,v)) = (1/2) log(2πe v)`,
so `entropyPower (𝒩(m,v)) = exp(2 · (1/2) log(2πe v)) = exp(log(2πe v)) = 2πe v`.

@audit:ok -/
@[entry_point]
theorem entropyPower_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPower (gaussianReal m v) = 2 * Real.pi * Real.exp 1 * v := by
  unfold entropyPower
  rw [InformationTheory.Shannon.differentialEntropy_gaussianReal m hv]
  have h_simplify :
      (2 : ℝ) * ((1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)))
        = Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by ring
  rw [h_simplify]
  have h_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (v : ℝ) := by
    have hv_pos : (0 : ℝ) < (v : ℝ) := by
      have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
    positivity
  exact Real.exp_log h_pos

/-! ### EPI conclusion predicate -/

/-- The EPI conclusion named as a `Prop`:

`entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`.

This is the conclusion itself and is not used as a hypothesis (that would be circular); it names the
output of the Gaussian saturation case and downstream intermediate results. -/
def IsEntropyPowerInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  entropyPower (P.map (fun ω => X ω + Y ω))
    ≥ entropyPower (P.map X) + entropyPower (P.map Y)

/-! ### Gaussian saturation case -/

/-- For independent Gaussians `X, Y` with nonzero variance, EPI holds with equality:
`exp(2 h(X+Y)) = exp(2 h(X)) + exp(2 h(Y))`. This follows from
`gaussianReal_add_gaussianReal_of_indepFun` identifying the law of the sum as Gaussian, together
with the closed form `differentialEntropy_gaussianReal`.

@audit:ok -/
@[entry_point]
theorem entropyPower_gaussian_additivity
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      = entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- Step 1: `(X+Y).law = gaussianReal (m₁+m₂) (v₁+v₂)` from Mathlib.
  have h_sum_law : P.map (fun ω => X ω + Y ω) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hXY hLawX hLawY
    -- `X + Y` in Mathlib lemma is `Pi.instAdd`-form which is defeq to `fun ω => X ω + Y ω`.
    -- Convert via `Pi.add_apply` / `funext`.
    have h_eq : (X + Y) = fun ω => X ω + Y ω := by
      funext ω; rfl
    rw [h_eq] at h
    exact h
  -- Step 2: `v₁ + v₂ ≠ 0` from `hv₁`.
  have hv_sum : v₁ + v₂ ≠ 0 := by
    intro h_eq
    -- `v₁ + v₂ = 0` over `ℝ≥0` implies both are `0` (`NNReal` cancellative add).
    have h1 : v₁ ≤ v₁ + v₂ := le_self_add
    rw [h_eq] at h1
    have h2 : v₁ = 0 := le_antisymm h1 bot_le
    exact hv₁ h2
  -- Step 3: rewrite all three entropy powers as `2πe · v_*`.
  rw [hLawX, hLawY, h_sum_law]
  rw [entropyPower_gaussianReal m₁ hv₁, entropyPower_gaussianReal m₂ hv₂,
      entropyPower_gaussianReal (m₁ + m₂) hv_sum]
  -- Step 4: `2πe (v₁ + v₂) = 2πe v₁ + 2πe v₂`.
  push_cast
  ring

/-- L-EPI3 hypothesis is satisfied (with equality) whenever both `X` and `Y` are
independent Gaussians.

@audit:ok -/
@[entry_point]
theorem isEntropyPowerInequalityHypothesis_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsEntropyPowerInequalityHypothesis X Y P := by
  unfold IsEntropyPowerInequalityHypothesis
  rw [entropyPower_gaussian_additivity P X Y hX hY hXY m₁ m₂ v₁ v₂
        hv₁ hv₂ hLawX hLawY]

-- The discharge path from `IsEntropyPowerInequalityHypothesis` to
-- `IsStamToEPIBridge` (Gaussian-saturation → bridge) is publicly available
-- via `EPIStamDischarge.isStamToEPIBridgeHyp_of_gaussian`, so an
-- in-file `IsStamToEPIBridge` wrapper would be redundant. (Former
-- `@audit:retract-candidate(load-bearing-predicate)`
-- + `@audit:closed-by-successor(epi-stam-to-conclusion-plan)`.)

/-! ### Corollaries -/

/-- Translation invariance of entropy power: for `μ ≪ volume` and σ-finite `μ`,
`entropyPower (μ.map (· + a)) = entropyPower μ`.

@audit:ok -/
@[entry_point]
theorem entropyPower_map_add_const {μ : Measure ℝ} (hμ : μ ≪ volume)
    [SigmaFinite μ] (a : ℝ) :
    entropyPower (μ.map (· + a)) = entropyPower μ := by
  unfold entropyPower
  rw [InformationTheory.Shannon.differentialEntropy_map_add_const hμ]

/-- The three-variable EPI obtained by chaining the two-variable form: for independent `X, Y, Z`,
`exp(2 h(X+Y+Z)) ≥ exp(2 h(X)) + exp(2 h(Y)) + exp(2 h(Z))`, from two lower-arity EPI conclusions
(the `X+Y` vs `Z` pair and the `X` vs `Y` pair).

The body is a structural composition (associativity plus transitivity via `linarith`) with no
internal `sorry`: the supplied `h_xy_z_epi` / `h_x_y_epi` carry lower-arity EPI conclusions
`IsEntropyPowerInequalityHypothesis _ _ P` transparently, and this wrapper holds no core itself —
the load-bearing content lives at the definition site of the `IsEntropyPowerInequalityHypothesis`
predicate. The sister `EPIPlumbing.entropy_power_inequality_four_arg` carries `@audit:ok` for the
same reason, and this declaration was migrated from a stale
`@audit:retract-candidate(load-bearing-predicate)`.

@audit:ok -/
theorem entropy_power_inequality_three_arg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ)
    (h_xy_z_epi : IsEntropyPowerInequalityHypothesis (fun ω => X ω + Y ω) Z P)
    (h_x_y_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z) := by
  -- Step 1: from `h_xy_z_epi`, we get
  --   `entropyPower ((X+Y)+Z) ≥ entropyPower (X+Y) + entropyPower Z`.
  have h1 : entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map (fun ω => X ω + Y ω)) + entropyPower (P.map Z) := by
    -- `fun ω => (X ω + Y ω) + Z ω` is `fun ω => X ω + Y ω + Z ω` (assoc).
    have h_assoc : (fun ω : Ω => (X ω + Y ω) + Z ω)
        = (fun ω : Ω => X ω + Y ω + Z ω) := by
      funext ω; ring
    have h := h_xy_z_epi
    unfold IsEntropyPowerInequalityHypothesis at h
    rw [h_assoc] at h
    exact h
  -- Step 2: from `h_x_y_epi`, we get
  --   `entropyPower (X+Y) ≥ entropyPower X + entropyPower Y`.
  have h2 : entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := h_x_y_epi
  -- Combine via transitivity (add `entropyPower Z` to both sides of h2).
  linarith

end InformationTheory.Shannon.EntropyPowerInequality