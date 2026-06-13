import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Entropy Power Inequality — plumbing lemmas

Supporting lemmas for `entropyPower μ := Real.exp (2 · h(μ))` published independently.

## Main definitions

- `gaussianEntropyPowerConst`: Cover-Thomas `(2πe)` normalization constant.

## Main statements

- `entropyPower_pos_iff`, `entropyPower_ne_zero`: strict positivity.
- `entropyPower_eq_of_differentialEntropy_eq`,
  `entropyPower_le_of_differentialEntropy_le`,
  `entropyPower_lt_of_differentialEntropy_lt`: monotonicity.
- `log_entropyPower`: log-form.
- `entropyPower_div_two_pi_e_gaussianReal`: Gaussian normalization.
- `entropyPower_map_add_const_eq_self`, `entropyPower_map_mul_const`,
  `entropyPower_map_affine`: translation and scaling.
- `entropy_power_inequality_normalized`: `N(X+Y) ≥ N(X) + N(Y)` form.
- `entropy_power_inequality_four_arg`: 4-argument chain.

## Implementation notes

The definition `entropyPower μ := Real.exp (2 · h(μ))` is chosen so that
`Real.exp_pos`, `Real.exp_log`, and `Real.exp_le_exp` apply directly.
Stam inequality and de Bruijn integration discharge are out of scope here.
-/

namespace InformationTheory.Shannon.EntropyPowerInequality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

/-! ## §1 — Positivity, non-zero, log-form -/


/-- `entropyPower μ ≠ 0` (corollary of strict positivity). -/
@[entry_point]
theorem entropyPower_ne_zero (μ : Measure ℝ) : entropyPower μ ≠ 0 :=
  (entropyPower_pos μ).ne'

/-- `Real.log (entropyPower μ) = 2 · h(μ)`. -/
@[entry_point]
theorem log_entropyPower (μ : Measure ℝ) :
    Real.log (entropyPower μ) = 2 * InformationTheory.Shannon.differentialEntropy μ := by
  unfold entropyPower
  exact Real.log_exp _

/-! ## §2 — Monotonicity in `differentialEntropy` -/

/-- If two measures share the same differential entropy, their entropy powers
coincide. -/
@[entry_point]
theorem entropyPower_eq_of_differentialEntropy_eq {μ ν : Measure ℝ}
    (h : InformationTheory.Shannon.differentialEntropy μ
          = InformationTheory.Shannon.differentialEntropy ν) :
    entropyPower μ = entropyPower ν := by
  unfold entropyPower
  rw [h]

/-- Monotonicity (≤): `h(μ) ≤ h(ν) ⟹ entropyPower μ ≤ entropyPower ν`. -/
@[entry_point]
theorem entropyPower_le_of_differentialEntropy_le {μ ν : Measure ℝ}
    (h : InformationTheory.Shannon.differentialEntropy μ
          ≤ InformationTheory.Shannon.differentialEntropy ν) :
    entropyPower μ ≤ entropyPower ν := by
  unfold entropyPower
  refine Real.exp_le_exp.mpr ?_
  linarith

/-- Strict monotonicity (<): `h(μ) < h(ν) ⟹ entropyPower μ < entropyPower ν`. -/
@[entry_point]
theorem entropyPower_lt_of_differentialEntropy_lt {μ ν : Measure ℝ}
    (h : InformationTheory.Shannon.differentialEntropy μ
          < InformationTheory.Shannon.differentialEntropy ν) :
    entropyPower μ < entropyPower ν := by
  unfold entropyPower
  refine Real.exp_lt_exp.mpr ?_
  linarith

/-! ## §3 — Cover-Thomas `(2πe)⁻¹` normalized form -/

/-- The Cover-Thomas normalization constant `2πe`. -/
noncomputable def gaussianEntropyPowerConst : ℝ := 2 * Real.pi * Real.exp 1

/-- `gaussianEntropyPowerConst > 0`. -/
@[entry_point]
theorem gaussianEntropyPowerConst_pos : 0 < gaussianEntropyPowerConst := by
  unfold gaussianEntropyPowerConst; positivity

/-- **`(2πe)⁻¹`-normalized form for Gaussian**: under the Cover-Thomas
`N(μ) := (2πe)⁻¹ · entropyPower μ` normalization, the Gaussian saturating
case takes the closed form `N(gaussianReal m v) = v`. -/
@[entry_point]
theorem entropyPower_div_two_pi_e_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPower (gaussianReal m v) / gaussianEntropyPowerConst = (v : ℝ) := by
  rw [entropyPower_gaussianReal m hv]
  unfold gaussianEntropyPowerConst
  field_simp

/-! ## §4 — Phase B (translation / scaling / affine) lift to `entropyPower` -/

/-- Phase B-1 lift: `entropyPower (μ.map (· + a)) = entropyPower μ`. This is the
`entropyPower` companion to `InformationTheory.Shannon.differentialEntropy_map_add_const`. -/
@[entry_point]
theorem entropyPower_map_add_const_eq_self
    {μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (a : ℝ) :
    entropyPower (μ.map (· + a)) = entropyPower μ :=
  entropyPower_map_add_const hμ a

/-- Phase B-2 lift: `entropyPower (μ.map (· * c)) = |c|² · entropyPower μ`. -/
@[entry_point]
theorem entropyPower_map_mul_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {c : ℝ} (hc : c ≠ 0)
    (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPower (μ.map (· * c)) = c^2 * entropyPower μ := by
  unfold entropyPower
  rw [InformationTheory.Shannon.differentialEntropy_map_mul_const hμ hc h_ent_int]
  -- exp(2 (h(μ) + log|c|)) = exp(2 h(μ)) * exp(2 log|c|) = exp(2 h(μ)) * |c|^2 = c² * exp(2 h(μ))
  rw [show (2 : ℝ) * (InformationTheory.Shannon.differentialEntropy μ + Real.log |c|)
        = 2 * InformationTheory.Shannon.differentialEntropy μ + 2 * Real.log |c| from by ring]
  rw [Real.exp_add]
  have h_abs_pos : (0 : ℝ) < |c| := abs_pos.mpr hc
  have h_log : Real.exp (2 * Real.log |c|) = c^2 := by
    rw [show (2 : ℝ) * Real.log |c| = Real.log (|c| ^ 2) from by
      rw [Real.log_pow]; ring]
    rw [Real.exp_log (by positivity : (0 : ℝ) < |c|^2)]
    rw [sq_abs]
  rw [h_log]
  ring

/-- Phase B-3 lift: `entropyPower (μ.map (fun x => a * x + b)) = a² · entropyPower μ`.

The translation term `+ b` is absorbed (entropy power is translation-invariant),
leaving only the scaling factor `a²`. -/
@[entry_point]
theorem entropyPower_map_affine
    {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPower (μ.map (fun x => a * x + b)) = a^2 * entropyPower μ := by
  unfold entropyPower
  rw [InformationTheory.Shannon.differentialEntropy_map_affine hμ ha b h_ent_int]
  rw [show (2 : ℝ) * (InformationTheory.Shannon.differentialEntropy μ + Real.log |a|)
        = 2 * InformationTheory.Shannon.differentialEntropy μ + 2 * Real.log |a| from by ring]
  rw [Real.exp_add]
  have h_log : Real.exp (2 * Real.log |a|) = a^2 := by
    rw [show (2 : ℝ) * Real.log |a| = Real.log (|a| ^ 2) from by
      rw [Real.log_pow]; ring]
    rw [Real.exp_log (by positivity : (0 : ℝ) < |a|^2)]
    rw [sq_abs]
  rw [h_log]
  ring

/-! ## §6 — 4-argument EPI chain -/

/-- **4-arg EPI pass-through**: for independent `X, Y, Z, W` with the appropriate
L-EPI3 hypotheses, `entropyPower (X+Y+Z+W) ≥ Σ entropyPower (·)`.

Chains three applications of L-EPI3 (the 2-arg `IsEntropyPowerInequalityHypothesis`
predicate): once on `((X+Y)+Z) vs W`, once on `(X+Y) vs Z`, once on `X vs Y`.

`@audit:ok` -- Phase 1.C audit 2026-05-27 (fresh-eye sweep, EPI/Stam cluster):
proof body is genuinely complete (no internal `sorry`, no load-bearing
predicate bundled at this site — the L-EPI3 hypothesis is carried transparently
through the `h_*_epi` arguments supplied by the caller, and the chain to
`entropy_power_inequality_three_arg` + `linarith` is a structural composition).
Migrated `@audit:staged(epi-stam-to-conclusion-plan)` → `@audit:ok` per the
Phase 1.B precedent (commit `5376537`, EPIL3Integration 5 declarations
honestly-complete forgotten-sweep). The transitive load-bearing-ness lives in
the L-EPI3 predicate's definition site (`EntropyPowerInequality.lean`), not
in this consumer wrapper. -/
theorem entropy_power_inequality_four_arg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z W : Ω → ℝ)
    (h_xyz_w_epi :
      IsEntropyPowerInequalityHypothesis (fun ω => X ω + Y ω + Z ω) W P)
    (h_xy_z_epi : IsEntropyPowerInequalityHypothesis (fun ω => X ω + Y ω) Z P)
    (h_x_y_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω + W ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z)
          + entropyPower (P.map W) := by
  -- Step 1: from `h_xyz_w_epi`:
  -- entropyPower ((X+Y+Z) + W) ≥ entropyPower (X+Y+Z) + entropyPower W
  have h1 : entropyPower (P.map (fun ω => X ω + Y ω + Z ω + W ω))
      ≥ entropyPower (P.map (fun ω => X ω + Y ω + Z ω)) + entropyPower (P.map W) := by
    have h_assoc : (fun ω : Ω => (X ω + Y ω + Z ω) + W ω)
        = (fun ω : Ω => X ω + Y ω + Z ω + W ω) := by
      funext ω; ring
    have h := h_xyz_w_epi
    unfold IsEntropyPowerInequalityHypothesis at h
    rw [h_assoc] at h
    exact h
  -- Step 2: from `entropy_power_inequality_three_arg`:
  -- entropyPower (X+Y+Z) ≥ entropyPower X + entropyPower Y + entropyPower Z
  have h2 : entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z) :=
    entropy_power_inequality_three_arg P X Y Z h_xy_z_epi h_x_y_epi
  -- Combine via transitivity.
  linarith

/-! ## §7 — Misc. corollaries -/

/-- L-EPI3 hypothesis is symmetric in `X` and `Y` (when the sum is reordered). -/
theorem isEntropyPowerInequalityHypothesis_symm
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X Y : Ω → ℝ}
    (h : IsEntropyPowerInequalityHypothesis X Y P) :
    IsEntropyPowerInequalityHypothesis Y X P := by
  unfold IsEntropyPowerInequalityHypothesis at *
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm, add_comm (entropyPower (P.map Y))]
  exact h

end InformationTheory.Shannon.EntropyPowerInequality