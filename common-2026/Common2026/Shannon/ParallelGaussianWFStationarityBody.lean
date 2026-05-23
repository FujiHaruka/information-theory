import Common2026.Shannon.ParallelGaussianWFCertBody

/-!
# W10-S2 Water-filling KKT stationarity discharge (common Lagrange multiplier)

`ParallelGaussianWFCertBody.lean` (wave9 G4) proved the per-coordinate tangent
machinery — `concaveOn_wfCost`, the affine tangent bound
`ConcaveOn.le_tangent_of_hasDerivAt`, the Lagrange reduction
`waterFillingCertificate_of_lagrange`, and the **stationarity discharge**
`isWFStationarityHyp_of_pos` (a genuine concave tangent inequality at the common
multiplier `lam = 1/(2ν)`). But its top-level capacity wrapper
`parallel_gaussian_capacity_formula_WFcert_discharged` still *takes* the Lagrange
bundle existence (`h_for_lagrange : ∀ ν, IsWaterFillingKKT P N ν →
∃ lam, IsWFLagrangeBundle P N ν lam`) as an abstract hypothesis.

## What is genuinely discharged here

This file removes that hypothesis by **producing the common Lagrange multiplier
internally** from the water-filling KKT structure:

1. **`waterFillingKKT_pos`** — for `0 < P`, a KKT water level `ν` (i.e.
   `∑_i max(0, ν − N_i) = P`) is strictly positive. *Genuine*: if `ν ≤ 0` then
   every coordinate is inactive (`max(0, ν − N_i) = 0` since `N_i ≥ 0`), forcing
   the sum to `0 ≠ P`.

2. **`isWFComplementarySlacknessHyp_of_KKT`** — at `lam = 1/(2ν)` with `0 < ν`,
   complementary slackness `0 ≤ lam ∧ ∑ P_i^* = P` holds (slackness from `ν > 0`,
   budget from the KKT predicate itself).

3. **`isWFLagrangeBundle_of_KKT`** — combine the stationarity discharge
   (`isWFStationarityHyp_of_pos`, the common-multiplier tangent inequality) with
   slackness to build `IsWFLagrangeBundle P N ν (1/(2ν))`.

4. **`waterFillingCertificate_of_KKT`** — `IsWaterFillingKKT` ⇒
   `WaterFillingOptimalityCertificate` (Phase D applied to the internal bundle).

5. **`parallel_gaussian_capacity_formula_WFstat_discharged`** — the capacity
   formula with the Lagrange-bundle hypothesis fully eliminated. Only the
   chain-rule bundle (L-PG1, a separate plan) remains as a hypothesis.

## Approach

The single shared multiplier `lam = 1/(2ν)` is the active-set derivative of
`wfCost` at the water level: on active coordinates `N_i + P_i^* = ν` so
`wfCost'(P_i^*) = 1/(2ν) = lam` exactly; on inactive coordinates
`wfCost'(0) = 1/(2N_i) ≤ 1/(2ν)` and the slack is absorbed by the nonneg factor
`P'_i − 0`. Both are already encoded in `isWFStationarityHyp_of_pos`. The only
new fact needed is positivity of the KKT water level, which makes that
discharge applicable and makes `lam ≥ 0` hold. No new convex-duality input is
required — the multiplier is exhibited, not assumed.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Positivity of the KKT water level -/

/-- **KKT water level is positive**: if the water-filling allocation uses up a
*positive* total power `P`, the water level `ν` must be strictly positive.

If `ν ≤ 0`, then for every coordinate `ν − N_i ≤ 0` (since `N_i ≥ 0`), so the
allocation `max(0, ν − N_i)` is zero everywhere and the total is `0`, which
contradicts `∑_i P_i^* = P > 0`. -/
theorem waterFillingKKT_pos {n : ℕ} (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0)
    {ν : ℝ} (h_kkt : IsWaterFillingKKT P N ν) :
    0 < ν := by
  by_contra h
  rw [not_lt] at h
  -- ν ≤ 0 ⇒ every coordinate inactive ⇒ sum = 0 ≠ P.
  have h_each : ∀ i : Fin n, waterFillingPower ν N i = 0 := by
    intro i
    have hNi : (0 : ℝ) ≤ (N i : ℝ) := NNReal.coe_nonneg _
    exact waterFillingPower_eq_zero_of_inactive ν N i (le_trans h hNi)
  have h_sum0 : ∑ i : Fin n, waterFillingPower ν N i = 0 :=
    Finset.sum_eq_zero (fun i _ => h_each i)
  -- IsWaterFillingKKT : ∑ ... = P, contradicting 0 = P > 0.
  rw [h_kkt] at h_sum0
  linarith

/-! ## Phase B — Complementary slackness from the KKT predicate -/

/-- **Complementary slackness from KKT**: at the common multiplier
`lam = 1/(2ν)` with positive water level, the slackness pair
`0 ≤ lam ∧ ∑ P_i^* = P` holds. The budget equality is exactly the KKT
predicate; nonnegativity of `lam` follows from `ν > 0`. -/
theorem isWFComplementarySlacknessHyp_of_KKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0)
    {ν : ℝ} (hν : 0 < ν) (h_kkt : IsWaterFillingKKT P N ν) :
    IsWFComplementarySlacknessHyp P N ν (1 / (2 * ν)) := by
  refine ⟨?_, h_kkt⟩
  -- 0 ≤ 1/(2ν) since ν > 0.
  positivity

/-! ## Phase C — Internal Lagrange bundle -/

/-- **Lagrange bundle from KKT** (common-multiplier discharge): a KKT water
level (with positive total power and positive noise floors) admits the Lagrange
bundle `IsWFLagrangeBundle P N ν (1/(2ν))`, i.e. stationarity (the genuine
per-coordinate tangent inequality at the *single shared* multiplier) plus
complementary slackness — both produced internally, neither assumed. -/
theorem isWFLagrangeBundle_of_KKT {n : ℕ} (P : ℝ) (hP : 0 < P)
    (N : Fin n → ℝ≥0) (hN_pos : ∀ i, 0 < (N i : ℝ))
    {ν : ℝ} (h_kkt : IsWaterFillingKKT P N ν) :
    IsWFLagrangeBundle P N ν (1 / (2 * ν)) := by
  have hν : 0 < ν := waterFillingKKT_pos P hP N h_kkt
  exact ⟨isWFStationarityHyp_of_pos N hν hN_pos,
    isWFComplementarySlacknessHyp_of_KKT P N hν h_kkt⟩

/-! ## Phase D — Optimality certificate from KKT -/

/-- **Optimality certificate from KKT**: the water-filling allocation at a KKT
water level is optimality-certified — the per-coordinate cost sum is maximized
there over all feasible allocations. This composes the internal Lagrange bundle
with the Phase D Lagrange reduction (`waterFillingCertificate_of_bundle`). -/
theorem waterFillingCertificate_of_KKT {n : ℕ} (P : ℝ) (hP : 0 < P)
    (N : Fin n → ℝ≥0) (hN_pos : ∀ i, 0 < (N i : ℝ))
    {ν : ℝ} (h_kkt : IsWaterFillingKKT P N ν) :
    WaterFillingOptimalityCertificate P N ν :=
  waterFillingCertificate_of_bundle P N ν (1 / (2 * ν))
    (isWFLagrangeBundle_of_KKT P hP N hN_pos h_kkt)

/-! ## Phase E — Re-publish capacity formula (stationarity discharged) -/

/-- **Parallel Gaussian capacity formula (WF stationarity discharged)**.

Same conclusion as `parallel_gaussian_capacity_formula_WFcert_discharged`, but
the Lagrange-bundle hypothesis `h_for_lagrange` is now **eliminated**: the common
Lagrange multiplier (KKT stationarity + complementary slackness) is produced
internally from the KKT water-level structure.

⚠️ NOT a full discharge: L-PG1 (the per-coordinate water-filling reduction)
remains OPEN — `h_for_bundle` is a conclusion-as-hypothesis (the capacity equality
split into two inequalities). It is the *only* remaining open hypothesis: L-WF1
(KKT existence), L-WF2 (water-filling optimality, now from genuine concavity +
internally-exhibited multiplier) and L-PG0 (kernel measurability) are all
genuinely closed. The genuine L-PG1 reduction needs the memoryless chain rule +
per-coord AWGN capacity (continuous AEP / sphere-shell volume) machinery absent
from Mathlib. -/
theorem parallel_gaussian_capacity_formula_WFstat_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (hN_pos : ∀ i, 0 < (N i : ℝ))
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_for_bundle : ∀ ν : ℝ, IsWaterFillingKKT P N ν →
        ParallelGaussianChainRuleBundle P N h_meas
          (isParallelGaussianKernelMeasurable N) ν) :
    ∃ ν : ℝ, IsWaterFillingKKT P N ν ∧
      parallelGaussianCapacity P N h_meas (isParallelGaussianKernelMeasurable N)
        = ∑ i : Fin (n + 1),
            (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
  -- L-WF1 fully discharged: a KKT water level exists.
  obtain ⟨ν, hν_kkt⟩ := exists_waterFillingKKT_of_pos P hP N
  refine ⟨ν, hν_kkt, ?_⟩
  -- Optimality certificate produced internally from the KKT structure:
  -- common Lagrange multiplier lam = 1/(2ν), no `h_for_lagrange` hypothesis.
  have h_cert : WaterFillingOptimalityCertificate P N ν :=
    waterFillingCertificate_of_KKT P hP N hN_pos hν_kkt
  have h_opt : IsWaterFillingOptimal P N ν :=
    isWaterFillingOptimal_of_certificate P N ν h_cert
  -- Chain rule bundle (L-PG1) → per-coordinate reduction (still load-bearing).
  have h_perCoordReduction_lbh : IsParallelGaussianPerCoordReduction P N h_meas
      (isParallelGaussianKernelMeasurable N) ν :=
    isParallelGaussianPerCoordReduction_of_bundle P N h_meas
      (isParallelGaussianKernelMeasurable N) ν (h_for_bundle ν hν_kkt)
  exact parallel_gaussian_capacity_formula_PG0closed_of_perCoordReduction P hP N hN h_meas ν
    hν_kkt h_opt h_perCoordReduction_lbh

end InformationTheory.Shannon.ParallelGaussian
