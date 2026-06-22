import InformationTheory.Shannon.EPI.Unconditional.MixedCase
import InformationTheory.Shannon.EPI.Case1.SmoothingLimit
import InformationTheory.Shannon.EPI.InfiniteVariance.Capstone
import InformationTheory.Meta.EntryPoint

/-!
# Entropy power inequality — case-1 dispatch

The two-a.c. classical entropy power inequality `N(X+Y) ≥ N(X) + N(Y)` (case 1 of the
absolute-continuity case split) together with the four-case dispatch skeleton that combines it
with the mixed and singular cases.

## Main statements

* `entropyPowerExt_add_ge_finite_ac` — case 1 (both push-forwards a.c. with finite differential
  entropy): the extended-real entropy power inequality, split by finiteness of variance.
* `entropy_power_inequality_of_ac` — the real-valued entropy power inequality under absolute
  continuity and finite differential entropy.

## Implementation notes

* This file sits downstream of both `EPIUncondMixedCase` and `EPICase1SmoothingLimit` so that the
  case-1 lemma can delegate to `EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance`.
  Placing the dispatch in either of those files instead would introduce an import cycle, since
  `EPICase1SmoothingLimit` already (transitively) imports `EPIUncondMixedCase`.
* Case 1 is split by whether both inputs have finite variance: the finite-variance branch
  delegates to the smoothing-limit closure, the infinite-variance branch to the conditioning
  truncation (route T) closure. Both branches are `sorryAx`-free.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The classical entropy power inequality `N(X+Y) ≥ N(X) + N(Y)` when both `P.map X` and
`P.map Y` are absolutely continuous and have finite differential entropy. The proof splits on
whether both inputs have finite variance: the finite-variance branch delegates to the
smoothing-limit closure, the infinite-variance branch to the conditioning-truncation (route T)
closure. The hypotheses `hX_ent`/`hY_ent`/`hW_ent` are finite-differential-entropy regularity
preconditions.

@audit:ok -/
theorem entropyPowerExt_add_ge_finite_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x ↦ Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x ↦ Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hfv : Integrable (fun ω ↦ (X ω) ^ 2) P ∧ Integrable (fun ω ↦ (Y ω) ^ 2) P
  · -- Finite variance: delegate to the smoothing-limit closure, threading the finite
    -- differential entropy `hW_ent` of the sum.
    obtain ⟨h_mom_X, h_mom_Y⟩ := hfv
    exact EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance
      P X Y hX hY hXY hX_ac hY_ac h_mom_X h_mom_Y hX_ent hY_ent hW_ent
  · -- Infinite variance: route T (conditioning truncation) closure.
    exact EPIInfiniteVarianceTruncation.entropyPowerExt_add_ge_infinite_variance
      P X Y hX hY hXY hX_ac hY_ac hX_ent hY_ent hfv

/-- Four-case dispatch for the extended-real entropy power inequality, splitting on absolute
continuity of `P.map X` and `P.map Y`: both a.c. delegates to `entropyPowerExt_add_ge_finite_ac`,
the mixed cases to `entropyPowerExt_mixed_add_ge` / `_symm`, and the doubly-singular case to
`entropyPowerExt_singular_add_ge`. The integrability and finite-entropy hypotheses are
path-dependent
regularity preconditions threaded into the mixed-case lemmas.

@audit:superseded-by(entropyPowerExt_add_ge_unconditional) The fully unconditional version
`entropyPowerExt_add_ge_unconditional` (in `EPIUncondDispatchFull`, taking only `hX hY hXY`) is the
canonical headline; this skeleton is retained as a proof-done leaf with no consumers.
@audit:ok -/
theorem entropyPowerExt_add_ge_dispatch_skeleton
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    -- Case 2 (X a.c., Y singular): X+Y-path integrability regularity preconditions.
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω ↦ X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω ↦ X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω ↦ X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω ↦ X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω ↦ X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω ↦ X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x ↦ ((condDistrib (fun ω ↦ X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω ↦ X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x ↦ ((condDistrib (fun ω ↦ X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z ↦ differentialEntropy (condDistrib (fun ω ↦ X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z ↦ ∫ x, ((condDistrib (fun ω ↦ X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x ↦ Real.log (((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω ↦ X ω + Y ω)))
    -- Case 2 symmetric (Y a.c., X singular): Y+X-path integrability regularity preconditions.
    (h_ac_symm : (P.map X) ⊗ₘ condDistrib (fun ω ↦ Y ω + X ω) X P
        ≪ (P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω ↦ Y ω + X ω)))
    (h_int_symm : Integrable
      (llr ((P.map X) ⊗ₘ condDistrib (fun ω ↦ Y ω + X ω) X P)
        ((P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω ↦ Y ω + X ω))))
      ((P.map X) ⊗ₘ condDistrib (fun ω ↦ Y ω + X ω) X P))
    (hκ_v_symm : ∀ᵐ z ∂(P.map X),
      condDistrib (fun ω ↦ Y ω + X ω) X P z ≪ volume)
    (hκ_logp_int_symm : ∀ᵐ z ∂(P.map X), Integrable
      (fun x ↦ ((condDistrib (fun ω ↦ Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω ↦ Y ω + X ω) X P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int_symm : ∀ᵐ z ∂(P.map X), Integrable
      (fun x ↦ ((condDistrib (fun ω ↦ Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω ↦ Y ω + X ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int_symm : Integrable
      (fun z ↦ differentialEntropy (condDistrib (fun ω ↦ Y ω + X ω) X P z)) (P.map X))
    (h_cross_int_symm : Integrable
      (fun z ↦ ∫ x, ((condDistrib (fun ω ↦ Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω ↦ Y ω + X ω)).rnDeriv volume x).toReal) ∂volume) (P.map X))
    (h_logq_int_symm : Integrable
      (fun x ↦ Real.log (((P.map (fun ω ↦ Y ω + X ω)).rnDeriv volume x).toReal))
      (P.map (fun ω ↦ Y ω + X ω)))
    -- Case 1 (both a.c.) and case 2 / symmetric: finite-entropy regularity preconditions.
    (hX_ent : Integrable (fun x ↦ Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x ↦ Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hWyx_ent : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ Y ω + X ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hX_ac : P.map X ≪ volume
  · by_cases hY_ac : P.map Y ≪ volume
    · -- Case 1 (both a.c.): delegate to `entropyPowerExt_add_ge_finite_ac`.
      exact entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent
    · -- Case 2 (X a.c., Y singular).
      exact entropyPowerExt_mixed_add_ge X Y P hX hY hXY hX_ac hY_ac h_ac h_int hκ_v
        hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int hX_ent hW_ent
  · by_cases hY_ac : P.map Y ≪ volume
    · -- Case 2 symmetric (Y a.c., X singular).
      exact entropyPowerExt_mixed_add_ge_symm X Y P hX hY hXY hY_ac hX_ac h_ac_symm h_int_symm
        hκ_v_symm hκ_logp_int_symm hκ_cross_int_symm h_fibreEnt_int_symm h_cross_int_symm
        h_logq_int_symm hY_ent hWyx_ent
    · -- Case 3 (both singular): RHS = 0.
      exact entropyPowerExt_singular_add_ge X Y P hX_ac hY_ac

/-- The real-valued entropy power inequality `N(X+Y) ≥ N(X) + N(Y)` (with `entropyPower μ =
exp (2 · h μ)`) for independent `X`, `Y` whose push-forwards are absolutely continuous with finite
differential entropy. The inequality is supplied by the extended-real version
`entropyPowerExt_add_ge_finite_ac`; this lemma only transports it across `ℝ≥0∞ → ℝ` via
`entropyPowerExt_of_ac_integrable`.

@audit:ok -/
@[entry_point]
theorem entropy_power_inequality_of_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x ↦ Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x ↦ Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPower (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- W = X+Y is a.c. (a.c. of an a.c. factor under independence).
  have hW_ac : (P.map (fun ω ↦ X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  -- The ℝ≥0∞-valued inequality.
  have hineq := entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent
  -- Rewrite each term as `ofReal (exp (2h)) = ofReal (entropyPower)`.
  rw [entropyPowerExt_of_ac_integrable hW_ac hW_ent,
    entropyPowerExt_of_ac_integrable hX_ac hX_ent,
    entropyPowerExt_of_ac_integrable hY_ac hY_ent] at hineq
  -- Combine `ofReal a + ofReal b` into `ofReal (a + b)` on the RHS.
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)] at hineq
  -- Unfold `entropyPower` and match the goal with `hineq` in `ofReal` form.
  rw [ge_iff_le, entropyPower, entropyPower, entropyPower,
    ← ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)]
  exact hineq

end InformationTheory.Shannon
