import InformationTheory.Shannon.EntropyPower.Ext
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic

/-!
# Entropy power inequality — singular and mixed cases

The entropy power inequality for the singular and mixed cases of the absolute-continuity split:
case 3 (both push-forwards singular) and case 2 (`X` a.c., `Y` singular).

## Main statements

* `entropyPowerExt_singular_add_ge` — case 3 (both singular): RHS `= 0`, closed by `zero_le`.
* `map_add_absolutelyContinuous` — `X` a.c. and `X ⊥ Y ⟹ X+Y` a.c. (convolution).
* `differentialEntropy_add_ge_of_indep` — the real core `h(X) ≤ h(X+Y)`.
* `entropyPowerExt_mixed_add_ge` / `_symm` — case 2 lifted to `ℝ≥0∞`.

## Implementation notes

* The integrability hypotheses of the mixed-case lemmas are regularity preconditions (a.c. density
  of `X+Y` and fibre regularity), passed explicitly rather than bundled into a predicate.
* In case 3, `RHS = 0` is the genuine value: the entropy power of a singular measure is `0`.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Case 3 (both singular): if `X` and `Y` are both singular, then `N(X+Y) ≥ N(X) + N(Y) = 0`. The
RHS is `0` (the genuine entropy-power value of a singular measure), so the inequality holds by
`zero_le` regardless of whether `X+Y` is a.c.

@audit:ok -/
theorem entropyPowerExt_singular_add_ge
    (X Y : Ω → ℝ) (P : Measure Ω)
    (hX_sing : ¬ P.map X ≪ volume) (hY_sing : ¬ P.map Y ≪ volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  rw [entropyPowerExt_singular hX_sing, entropyPowerExt_singular hY_sing, add_zero]
  exact zero_le'

/-- Convolution preserves absolute continuity: `X` a.c. and `X ⊥ Y ⟹ X+Y` a.c. The sum law factors
as the convolution `μ.map X ∗ μ.map Y` (independence), and `conv_absolutelyContinuous` propagates
absolute continuity of the a.c. factor.

@audit:ok -/
theorem map_add_absolutelyContinuous
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : P.map X ≪ volume) :
    P.map (fun ω => X ω + Y ω) ≪ volume := by
  rw [show (fun ω => X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map hX hY, Measure.conv_comm]
  exact Measure.conv_absolutelyContinuous hX_ac

/-- The real core of case 2: `h(X) ≤ h(X+Y)`. Combines the fibre identification
`condDifferentialEntropy (X+Y) Y P = h(X)` (`condDifferentialEntropy_indep_add_eq` at `c = 1`) with
the conditioning bound `h(X+Y | Y) ≤ h(X+Y)` (`condDifferentialEntropy_le`). The integrability
hypotheses are regularity preconditions (a.c. density of `X+Y` and fibre regularity).

@audit:ok -/
theorem differentialEntropy_add_ge_of_indep
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume)
    (hW_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume)
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω => X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => X ω + Y ω))) :
    differentialEntropy (P.map X)
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
  set W : Ω → ℝ := fun ω => X ω + Y ω with hW
  have hW_meas : Measurable W := hX.add hY
  -- Fibre identification (c=1): `h(X + 1·Y | Y) = h(X)`, and `1·Y = Y`.
  have h_fibre : condDifferentialEntropy W Y P = differentialEntropy (P.map X) := by
    have h := condDifferentialEntropy_indep_add_eq X Y P 1 hX hY hXY hX_ac
    simpa only [one_mul] using h
  -- Conditioning reduces entropy: `h(W | Y) ≤ h(W)`.
  have h_le : condDifferentialEntropy W Y P ≤ differentialEntropy (P.map W) :=
    condDifferentialEntropy_le W Y P hW_meas hY hW_ac h_ac h_int hκ_v hκ_logp_int
      hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
  rw [← h_fibre]
  exact h_le

/-- Case 2 lifted to `ℝ≥0∞` (`X` a.c., `Y` singular): `N(X+Y) ≥ N(X) + N(Y)`. Since `N(Y) = 0`, the
RHS is `N(X)`; both `X` and `X+Y` are a.c. with finite differential entropy, so
`entropyPowerExt_of_ac_integrable` writes each as `ofReal (exp (2h))`, and the real core
`h(X) ≤ h(X+Y)` lifts via `Real.exp_le_exp`. The integrability and finite-entropy hypotheses are
regularity preconditions.

@audit:superseded-by(entropyPowerExt_add_ge_unconditional) Replaced by the unconditional
`entropyPowerExt_mixed_add_ge_uncond`; retained as a proof-done leaf reachable only from the dead
dispatch skeleton.
@audit:ok -/
theorem entropyPowerExt_mixed_add_ge
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_sing : ¬ P.map Y ≪ volume)
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω => X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => X ω + Y ω)))
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- RHS = N(X) + N(Y) = N(X) + 0 = N(X).
  rw [entropyPowerExt_singular hY_sing, add_zero]
  -- X+Y is a.c. (convolution of an a.c. factor).
  have hW_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  -- Real core: `h(X) ≤ h(X+Y)`.
  have h_real : differentialEntropy (P.map X)
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) :=
    differentialEntropy_add_ge_of_indep X Y P hX hY hXY hX_ac hW_ac h_ac h_int hκ_v
      hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int
  -- Lift to ℝ≥0∞: both endpoints are a.c. with finite differential entropy,
  -- so `N = ofReal (exp (2h))`.
  rw [entropyPowerExt_of_ac_integrable hX_ac hX_ent, entropyPowerExt_of_ac_integrable hW_ac hW_ent]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-- Case 2 symmetric (`Y` a.c., `X` singular): `N(X+Y) ≥ N(X) + N(Y)`. Re-applies
`entropyPowerExt_mixed_add_ge` with `X` and `Y` swapped via `X + Y = Y + X`, passing `hY_ent` /
`hWyx_ent` into the `X`-role positions. The integrability and finite-entropy hypotheses are
regularity preconditions for the `Y+X` path.

@audit:superseded-by(entropyPowerExt_add_ge_unconditional) Replaced by the unconditional
`entropyPowerExt_mixed_add_ge_symm_uncond`; retained as a proof-done leaf reachable only from the
dead dispatch skeleton.
@audit:ok -/
theorem entropyPowerExt_mixed_add_ge_symm
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hY_ac : (P.map Y) ≪ volume) (hX_sing : ¬ P.map X ≪ volume)
    (h_ac : (P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P
        ≪ (P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω)))
    (h_int : Integrable
      (llr ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P)
        ((P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω))))
      ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P))
    (hκ_v : ∀ᵐ z ∂(P.map X),
      condDistrib (fun ω => Y ω + X ω) X P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => Y ω + X ω) X P z)) (P.map X))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) ∂volume) (P.map X))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => Y ω + X ω)))
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hWyx_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- `X + Y = Y + X` pointwise, and `N(X) + N(Y) = N(Y) + N(X)`.
  rw [show (fun ω => X ω + Y ω) = (fun ω => Y ω + X ω) from
        funext fun ω => add_comm _ _, add_comm (entropyPowerExt (P.map X))]
  exact entropyPowerExt_mixed_add_ge Y X P hY hX hXY.symm hY_ac hX_sing h_ac h_int hκ_v
    hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int hY_ent hWyx_ent

end InformationTheory.Shannon
