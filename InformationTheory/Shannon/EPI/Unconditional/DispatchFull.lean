import InformationTheory.Shannon.EPI.Unconditional.Dispatch
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit

/-!
# Entropy power inequality — fully unconditional dispatch

The fully unconditional entropy power inequality `entropyPowerExt_add_ge`, taking only
`(hX hY : Measurable) (hXY : IndepFun X Y P)`, built from the unconditional gateway lemmas.

## Main statements

* `entropyPowerExt_add_ge` — the unconditional `ℝ≥0∞` entropy power inequality.
* `entropyPowerExt_mixed_add_ge` / `_symm` — the mixed cases (one factor a.c., the other
  singular), via gateway monotonicity.
* `entropyPowerExt_add_ge_case1` — case 1 (both a.c.), splitting on `⊤`/`⊥`/finite of the
  three differential entropies and delegating to `entropyPowerExt_add_ge_finite_ac`.

## Implementation notes

* The 21-precondition dispatch `entropyPowerExt_add_ge_dispatch_skeleton` is a separate
  route; this file builds the gateway-based unconditional version independently of it.
* Every declaration delegates to an existing gateway lemma or bridge; the only work is plumbing
  (order lemmas, `EReal.exp` expansion, `add_comm` reshaping).
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `h = ⊥ ⟹ N = 0`: from `differentialEntropyExt μ = ⊥` alone, `entropyPowerExt μ = 0`. Unlike
`entropyPowerExt_singular` (which is for `¬ a.c.`), this covers the a.c. case where `h = ⊥`.

@audit:ok -/
private theorem entropyPowerExt_eq_zero_of_diffEntExt_bot {μ : Measure ℝ}
    (h : differentialEntropyExt μ = ⊥) : entropyPowerExt μ = 0 := by
  unfold entropyPowerExt
  rw [h, EReal.mul_bot_of_pos (by norm_num), EReal.exp_bot]

/-- Case 2 (X a.c., Y singular): since `N(Y) = 0`, the RHS is `N(X)`, and gateway monotonicity gives
`N(X+Y) ≥ N(X)`. The only hypotheses are `hX hY hXY hX_ac hY_sing`.

@audit:ok -/
theorem entropyPowerExt_mixed_add_ge
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_sing : ¬ (P.map Y) ≪ volume) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  rw [entropyPowerExt_singular hY_sing, add_zero]
  exact entropyPowerExt_mono_add X Y P hX hY hXY hX_ac

/-- Case 2 symmetric (Y a.c., X singular): since `N(X) = 0`, the RHS is `N(Y)`, and gateway
monotonicity (`W = Y`, `V = X`) gives `N(Y+X) ≥ N(Y)`, reshaped to `X+Y` by `add_comm`. The only
hypotheses are `hX hY hXY hY_ac hX_sing`.

@audit:ok -/
theorem entropyPowerExt_mixed_add_ge_symm
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hY_ac : (P.map Y) ≪ volume) (hX_sing : ¬ (P.map X) ≪ volume) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  have hcomm : P.map (fun ω ↦ X ω + Y ω) = P.map (fun ω ↦ Y ω + X ω) :=
    congrArg (P.map ·) (funext fun ω ↦ add_comm _ _)
  rw [hcomm, entropyPowerExt_singular hX_sing, zero_add]
  exact entropyPowerExt_mono_add Y X P hY hX hXY.symm hY_ac

/-- Case 1 (both a.c.), with no finite-entropy hypotheses. Splits on `⊤`/`⊥`/finite of `h(X+Y)`,
`h(X)`, `h(Y)`: the `⊤`/`⊥` branches collapse one RHS term via gateway monotonicity, and the
all-finite branch supplies the three integrability hypotheses through the bridge
`differentialEntropyExt_integrable_of_finite` and delegates to `entropyPowerExt_add_ge_finite_ac`.
The only hypotheses are `hX hY hXY hX_ac hY_ac`.

@audit:ok -/
theorem entropyPowerExt_add_ge_case1
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- 1. h(X+Y) = ⊤ ⟹ N(X+Y) = ⊤ ≥ RHS.
  by_cases hWtop : differentialEntropyExt (P.map (fun ω ↦ X ω + Y ω)) = ⊤
  · rw [entropyPowerExt_eq_top_of_diffEntExt_top hWtop]; exact le_top
  -- 2. h(X) = ⊤ ⟹ N(X) = ⊤; gateway monotonicity gives N(X+Y) ≥ N(X) = ⊤, so N(X+Y) = ⊤.
  by_cases hXtop : differentialEntropyExt (P.map X) = ⊤
  · have hNX : entropyPowerExt (P.map X) = ⊤ := entropyPowerExt_eq_top_of_diffEntExt_top hXtop
    have hge : entropyPowerExt (P.map (fun ω ↦ X ω + Y ω)) ≥ entropyPowerExt (P.map X) :=
      entropyPowerExt_mono_add X Y P hX hY hXY hX_ac
    have hWval : entropyPowerExt (P.map (fun ω ↦ X ω + Y ω)) = ⊤ :=
      top_le_iff.mp (hNX ▸ hge)
    rw [hWval]; exact le_top
  -- 3. h(Y) = ⊤ ⟹ as above, by the symmetric gateway.
  by_cases hYtop : differentialEntropyExt (P.map Y) = ⊤
  · have hcomm : P.map (fun ω ↦ X ω + Y ω) = P.map (fun ω ↦ Y ω + X ω) :=
      congrArg (P.map ·) (funext fun ω ↦ add_comm _ _)
    have hNY : entropyPowerExt (P.map Y) = ⊤ := entropyPowerExt_eq_top_of_diffEntExt_top hYtop
    have hge : entropyPowerExt (P.map (fun ω ↦ Y ω + X ω)) ≥ entropyPowerExt (P.map Y) :=
      entropyPowerExt_mono_add Y X P hY hX hXY.symm hY_ac
    have hWval : entropyPowerExt (P.map (fun ω ↦ X ω + Y ω)) = ⊤ := by
      rw [hcomm]; exact top_le_iff.mp (hNY ▸ hge)
    rw [hWval]; exact le_top
  -- 4. h(X) = ⊥ ⟹ N(X) = 0, RHS = N(Y); the symmetric gateway gives N(X+Y) ≥ N(Y).
  by_cases hXbot : differentialEntropyExt (P.map X) = ⊥
  · have hcomm : P.map (fun ω ↦ X ω + Y ω) = P.map (fun ω ↦ Y ω + X ω) :=
      congrArg (P.map ·) (funext fun ω ↦ add_comm _ _)
    rw [entropyPowerExt_eq_zero_of_diffEntExt_bot hXbot, zero_add, hcomm]
    exact entropyPowerExt_mono_add Y X P hY hX hXY.symm hY_ac
  -- 5. h(Y) = ⊥ ⟹ N(Y) = 0, RHS = N(X); the gateway gives N(X+Y) ≥ N(X).
  by_cases hYbot : differentialEntropyExt (P.map Y) = ⊥
  · rw [entropyPowerExt_eq_zero_of_diffEntExt_bot hYbot, add_zero]
    exact entropyPowerExt_mono_add X Y P hX hY hXY hX_ac
  -- 6. Remaining branch (h(X), h(Y), h(X+Y) all finite): supply 3 integrabilities via the bridge.
  · -- h(X+Y) is a.c. (both a.c. + independence preserves convolution).
    have hW_ac : P.map (fun ω ↦ X ω + Y ω) ≪ volume :=
      map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
    -- h(X) ≤ h(X+Y) (gateway monotone); since h(X) ≠ ⊥, also h(X+Y) ≠ ⊥.
    have hmono : differentialEntropyExt (P.map X)
        ≤ differentialEntropyExt (P.map (fun ω ↦ X ω + Y ω)) :=
      differentialEntropyExt_mono_add X Y P hX hY hXY hX_ac
    have hWbot : differentialEntropyExt (P.map (fun ω ↦ X ω + Y ω)) ≠ ⊥ := by
      intro hbot
      exact hXbot (le_bot_iff.mp (hbot ▸ hmono))
    -- Supply the three integrabilities via the bridge.
    have hX_ent := differentialEntropyExt_integrable_of_finite hX_ac hXtop hXbot
    have hY_ent := differentialEntropyExt_integrable_of_finite hY_ac hYtop hYbot
    have hW_ent := differentialEntropyExt_integrable_of_finite hW_ac hWtop hWbot
    exact entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent

/-- The fully unconditional extended-real **entropy power inequality**
`N(X+Y) ≥ N(X) + N(Y)`, taking only `hX hY hXY`. The four-case split on absolute continuity
of `P.map X` and `P.map Y` delegates to `entropyPowerExt_add_ge_case1` (both a.c.),
`entropyPowerExt_mixed_add_ge` / `_symm` (mixed), and `entropyPowerExt_singular_add_ge`
(both singular).

@audit:ok -/
@[entry_point]
theorem entropyPowerExt_add_ge
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hX_ac : (P.map X) ≪ volume
  · by_cases hY_ac : (P.map Y) ≪ volume
    · -- Both a.c. → case 1.
      exact entropyPowerExt_add_ge_case1 X Y P hX hY hXY hX_ac hY_ac
    · -- X a.c., Y singular → case 2.
      exact entropyPowerExt_mixed_add_ge X Y P hX hY hXY hX_ac hY_ac
  · by_cases hY_ac : (P.map Y) ≪ volume
    · -- Y a.c., X singular → case 2 symmetric.
      exact entropyPowerExt_mixed_add_ge_symm X Y P hX hY hXY hY_ac hX_ac
    · -- Both singular → case 3 (RHS = 0).
      exact entropyPowerExt_singular_add_ge X Y P hX_ac hY_ac

end InformationTheory.Shannon
