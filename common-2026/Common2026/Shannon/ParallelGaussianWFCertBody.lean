import Common2026.Shannon.ParallelGaussianKKT
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# W9-G4 T2-B `WaterFillingOptimalityCertificate` body discharge

wave6 `ParallelGaussianKKT.lean` published the parallel-Gaussian water-filling
optimality as an **abstract certificate** (`WaterFillingOptimalityCertificate`)
plus the chain-rule bundle (`ParallelGaussianChainRuleBundle`), reduced to the
`IsWaterFillingOptimal` / `IsParallelGaussianPerCoordReduction` predicates by
bidirectional definitional unfolding. This file attempts to **discharge the
algebraic core of the certificate body** rather than leave it as a pure
pass-through.

## What is genuinely discharged here

The certificate states that water-filling maximizes the concave per-coordinate
sum `∑ (1/2) log(1 + P_i / N_i)` subject to `P_i ≥ 0, ∑ P_i ≤ P`. The textbook
KKT proof factors into:

1. **Concave tangent-line inequality** (`ConcaveOn.le_tangent_of_hasDerivAt`):
   for `f` concave on `S` with `HasDerivAt f f' x`,
   `f y ≤ f x + f' · (y - x)` for all `x, y ∈ S`. *Fully discharged* from
   Mathlib's slope lemmas via an `x = y / x < y / y < x` trichotomy.

2. **Per-coordinate Lagrange stationarity** (`IsWFStationarityHyp`): each cost
   `g_i(t) = (1/2) log(1 + t / N_i)` admits the tangent bound
   `g_i(P'_i) ≤ g_i(P_i^*) + λ · (P'_i - P_i^*)` at the water-filling point with
   a *common* multiplier `λ`. This is the KKT first-order condition; its
   discharge requires identifying `λ = 1/(2ν)` and the concavity of `g_i`, which
   is encoded as a sub-predicate (Lagrange-multiplier ansatz pass-through, same
   shape as `MaxEntropyConstrainedKKT.KKTSolution.moment_match`).

3. **Complementary slackness** (`IsWFComplementarySlacknessHyp`):
   `λ · (∑ P_i^* - P) = 0` together with `λ ≥ 0`.

4. **Lagrange reduction** (`waterFillingCertificate_of_lagrange`): given (2) + (3)
   + primal feasibility `∑ P_i^* ≤ P`, the certificate holds. *Fully discharged*
   — pure algebra: sum the per-coordinate tangent bounds, then collapse the
   linear remainder using `λ ≥ 0`, `∑ P'_i ≤ P`, and complementary slackness.

## Approach

```
Phase A: Concave tangent-line lemma (Mathlib slope → affine bound)         [internal]
Phase B: Per-coordinate cost concavity + derivative                        [internal]
Phase C: KKT sub-predicate bundle (stationarity / slackness / feasibility) [defs]
Phase D: Lagrange reduction  bundle → WaterFillingOptimalityCertificate    [internal]
Phase E: Stationarity discharge  log-concavity → IsWFStationarityHyp       [internal]
Phase F: Re-publish parallel_gaussian_capacity_formula_WFcert_discharged
```

The deep convex-duality fact "such a `λ` with complementary slackness exists"
remains a hypothesis (the KKT-uniqueness wall the wave6 retreat line names); but
its *use* — turning the multiplier into the optimality certificate — is now an
internal theorem, and the per-coordinate stationarity bound is discharged from
genuine log-concavity.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Concave tangent-line inequality (internal discharge) -/

/-- **Concave tangent-line bound**: a function concave on `S` with a derivative
`f'` at `x` lies below its tangent line at `x`:
`f y ≤ f x + f' · (y - x)` for all `x, y ∈ S`.

This is the affine-bound restatement of Mathlib's slope inequalities
(`ConcaveOn.slope_le_of_hasDerivAt` / `ConcaveOn.le_slope_of_hasDerivAt`),
obtained by an `x = y / x < y / y < x` trichotomy. -/
theorem ConcaveOn.le_tangent_of_hasDerivAt {S : Set ℝ} {f : ℝ → ℝ} {x f' : ℝ}
    (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) {y : ℝ} (hy : y ∈ S)
    (hf' : HasDerivAt f f' x) :
    f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · -- x < y : left-endpoint slope bound `slope f x y ≤ f'`.
    have h_slope : slope f x y ≤ f' :=
      hfc.slope_le_of_hasDerivAt hx hy hxy hf'
    rw [slope_def_field] at h_slope
    have hpos : 0 < y - x := by linarith
    -- (f y - f x) / (y - x) ≤ f'  ⇒  f y - f x ≤ f' * (y - x)
    have := (div_le_iff₀ hpos).mp h_slope
    linarith
  · subst hxy; simp
  · -- y < x : right-endpoint slope bound `f' ≤ slope f y x`.
    have h_slope : f' ≤ slope f y x :=
      hfc.le_slope_of_hasDerivAt hy hx hxy hf'
    rw [slope_def_field] at h_slope
    have hpos : 0 < x - y := by linarith
    -- f' ≤ (f x - f y) / (x - y)  ⇒  f' * (x - y) ≤ f x - f y
    have := (le_div_iff₀ hpos).mp h_slope
    nlinarith [this]

/-! ## Phase B — Per-coordinate cost concavity + derivative -/

/-- Per-coordinate water-filling cost `g_i(t) = (1/2) log(1 + t / N_i)`. -/
noncomputable def wfCost (Ni : ℝ) (t : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + t / Ni)

/-- `wfCost` derivative at `t` (for `Ni > 0`, `t ≥ 0`):
`g_i'(t) = 1 / (2 (Ni + t))`. -/
theorem hasDerivAt_wfCost {Ni : ℝ} (hNi : 0 < Ni) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (wfCost Ni) (1 / (2 * (Ni + t))) t := by
  -- u(t) = 1 + t / Ni, with u'(t) = 1 / Ni and u(t) = (Ni + t)/Ni > 0.
  have hu_pos : (0 : ℝ) < 1 + t / Ni := by
    have : 0 ≤ t / Ni := div_nonneg ht hNi.le
    linarith
  have hu_ne : (1 + t / Ni) ≠ 0 := ne_of_gt hu_pos
  -- HasDerivAt for u: const + id/Ni, with derivative Ni⁻¹.
  have h1 : HasDerivAt (fun s : ℝ => s / Ni) Ni⁻¹ t := by
    simpa using (hasDerivAt_id t).div_const Ni
  have hu : HasDerivAt (fun s : ℝ => 1 + s / Ni) Ni⁻¹ t := by
    have := (hasDerivAt_const t (1 : ℝ)).add h1
    simpa only [zero_add] using this
  -- log ∘ u with derivative (1/u) * u' = (1 + t/Ni)⁻¹ * Ni⁻¹.
  have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s / Ni))
      ((1 + t / Ni)⁻¹ * Ni⁻¹) t := by
    have := (Real.hasDerivAt_log hu_ne).comp t hu
    simpa [Function.comp] using this
  -- scale by 1/2.
  have hscaled : HasDerivAt (wfCost Ni)
      ((1 / 2) * ((1 + t / Ni)⁻¹ * Ni⁻¹)) t := by
    simpa only [wfCost] using hlog.const_mul (1 / 2 : ℝ)
  -- (1/2) * ((1 + t/Ni)⁻¹ * Ni⁻¹) = 1 / (2 (Ni + t)).
  have hval : (1 / 2) * ((1 + t / Ni)⁻¹ * Ni⁻¹) = 1 / (2 * (Ni + t)) := by
    have hNi_ne : Ni ≠ 0 := ne_of_gt hNi
    rw [show (1 : ℝ) + t / Ni = (Ni + t) / Ni by field_simp]
    rw [inv_div]
    field_simp
  rwa [hval] at hscaled

/-- `wfCost Ni` is concave on `[0, ∞)` for `Ni > 0`. Proof via the antitone
first derivative `g_i'(t) = 1/(2(Ni+t))`. -/
theorem concaveOn_wfCost {Ni : ℝ} (hNi : 0 < Ni) :
    ConcaveOn ℝ (Set.Ici 0) (wfCost Ni) := by
  have hint : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
  -- Differentiability everywhere on the interior and the derivative formula.
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (wfCost Ni) (1 / (2 * (Ni + t))) t := by
    intro t ht
    exact hasDerivAt_wfCost hNi (le_of_lt ht)
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) ?_ ?_ ?_
  · -- ContinuousOn over Ici 0: each point has a derivative (hence continuous).
    intro t ht
    have ht0 : 0 ≤ t := ht
    exact (hasDerivAt_wfCost hNi ht0).continuousAt.continuousWithinAt
  · -- DifferentiableOn over interior = Ioi 0.
    rw [hint]
    intro t ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  · -- AntitoneOn (deriv (wfCost Ni)) over Ioi 0.
    rw [hint]
    intro a ha b hb hab
    have hda : deriv (wfCost Ni) a = 1 / (2 * (Ni + a)) := (hderiv a ha).deriv
    have hdb : deriv (wfCost Ni) b = 1 / (2 * (Ni + b)) := (hderiv b hb).deriv
    -- Antitone: a ≤ b ⇒ 1/(2(Ni+b)) ≤ 1/(2(Ni+a)).
    rw [hda, hdb]
    have hpa : 0 < 2 * (Ni + a) := by
      have : 0 < a := ha
      positivity
    have hle : 2 * (Ni + a) ≤ 2 * (Ni + b) := by linarith
    exact one_div_le_one_div_of_le hpa hle

/-! ## Phase C — KKT sub-predicate bundle -/

/-- **WF Lagrange stationarity sub-predicate** (KKT first-order condition).

There is a common Lagrange multiplier `lam ≥ 0` such that each per-coordinate
cost satisfies the tangent bound at the water-filling allocation:
`g_i(P'_i) ≤ g_i(P_i^*) + lam · (P'_i - P_i^*)` for every feasible `P'_i ≥ 0`.

This packages the KKT stationarity `g_i'(P_i^*) = lam` (active) /
`g_i'(P_i^*) ≤ lam` (inactive) into the form actually consumed by the
Lagrange reduction. -/
def IsWFStationarityHyp {n : ℕ} (N : Fin n → ℝ≥0) (ν lam : ℝ) : Prop :=
  ∀ (i : Fin n) (Pi' : ℝ), 0 ≤ Pi' →
    wfCost (N i : ℝ) Pi'
      ≤ wfCost (N i : ℝ) (waterFillingPower ν N i)
        + lam * (Pi' - waterFillingPower ν N i)

/-- **WF complementary slackness sub-predicate**: the multiplier is nonnegative
and the budget binds, `lam ≥ 0 ∧ ∑ P_i^* = P`. -/
def IsWFComplementarySlacknessHyp {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0)
    (ν lam : ℝ) : Prop :=
  0 ≤ lam ∧ ∑ i : Fin n, waterFillingPower ν N i = P

/-! ## Phase D — Lagrange reduction (internal discharge) -/

/-- **Lagrange reduction (certificate body)**: KKT stationarity +
complementary slackness deliver the optimality certificate.

Pure algebra: sum the per-coordinate tangent bounds, then bound the linear
remainder `lam · (∑ P'_i - ∑ P_i^*)` using `lam ≥ 0`, `∑ P'_i ≤ P`, and
`∑ P_i^* = P`. -/
theorem waterFillingCertificate_of_lagrange {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (ν lam : ℝ)
    (h_stat : IsWFStationarityHyp N ν lam)
    (h_slack : IsWFComplementarySlacknessHyp P N ν lam) :
    WaterFillingOptimalityCertificate P N ν := by
  obtain ⟨h_lam_nonneg, h_budget⟩ := h_slack
  intro P' hP'_nonneg hP'_sum
  -- The certificate's summand is exactly `wfCost (N i) (·)`.
  show ∑ i : Fin n, (1 / 2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i : Fin n, (1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
  -- Per-coordinate tangent bound (stationarity), summed.
  have h_each : ∀ i : Fin n,
      (1 / 2) * Real.log (1 + P' i / (N i : ℝ))
        ≤ (1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
          + lam * (P' i - waterFillingPower ν N i) := by
    intro i
    have := h_stat i (P' i) (hP'_nonneg i)
    simpa only [wfCost] using this
  -- Sum the tangent bounds.
  have h_sum_le :
      ∑ i : Fin n, (1 / 2) * Real.log (1 + P' i / (N i : ℝ))
        ≤ ∑ i : Fin n, ((1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
            + lam * (P' i - waterFillingPower ν N i)) :=
    Finset.sum_le_sum (fun i _ => h_each i)
  -- Split the RHS into the optimum value plus the linear remainder.
  have h_split :
      ∑ i : Fin n, ((1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
          + lam * (P' i - waterFillingPower ν N i))
        = (∑ i : Fin n, (1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)))
          + lam * ((∑ i : Fin n, P' i) - ∑ i : Fin n, waterFillingPower ν N i) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  -- The linear remainder is ≤ 0 by `lam ≥ 0`, `∑ P' ≤ P`, `∑ P* = P`.
  have h_rem_nonpos :
      lam * ((∑ i : Fin n, P' i) - ∑ i : Fin n, waterFillingPower ν N i) ≤ 0 := by
    rw [h_budget]
    have h_diff_nonpos : (∑ i : Fin n, P' i) - P ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos h_lam_nonneg h_diff_nonpos
  -- Combine.
  calc ∑ i : Fin n, (1 / 2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i : Fin n, ((1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
          + lam * (P' i - waterFillingPower ν N i)) := h_sum_le
    _ = (∑ i : Fin n, (1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)))
          + lam * ((∑ i : Fin n, P' i) - ∑ i : Fin n, waterFillingPower ν N i) := h_split
    _ ≤ (∑ i : Fin n, (1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)))
          + 0 := by linarith [h_rem_nonpos]
    _ = ∑ i : Fin n, (1 / 2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
        rw [add_zero]

/-! ## Phase E — Stationarity discharge from log-concavity -/

/-- **Stationarity discharge**: for the active coordinates (`N_i < ν`) the
common multiplier `lam = 1/(2ν)` realizes the tangent bound from log-concavity;
for inactive coordinates (`ν ≤ N_i`) the bound holds because `g_i'(0) ≤ 1/(2ν)`.

This discharges `IsWFStationarityHyp` for `lam = 1/(2ν)` *provided* the water
level is positive and dominates the noise floor where active — i.e. for a
genuine KKT water level. -/
theorem isWFStationarityHyp_of_pos {n : ℕ} (N : Fin n → ℝ≥0) {ν : ℝ}
    (hν : 0 < ν) (hN_pos : ∀ i, 0 < (N i : ℝ)) :
    IsWFStationarityHyp N ν (1 / (2 * ν)) := by
  intro i Pi' hPi'
  set Ni : ℝ := (N i : ℝ) with hNi_def
  have hNi : 0 < Ni := hN_pos i
  set Pstar : ℝ := waterFillingPower ν N i with hPstar_def
  have hPstar_nonneg : 0 ≤ Pstar := waterFillingPower_nonneg ν N i
  -- Derivative of wfCost at the water-filling point.
  have hderiv : HasDerivAt (wfCost Ni) (1 / (2 * (Ni + Pstar))) Pstar :=
    hasDerivAt_wfCost hNi hPstar_nonneg
  -- Concave tangent-line bound at Pstar.
  have h_tangent : wfCost Ni Pi'
      ≤ wfCost Ni Pstar + (1 / (2 * (Ni + Pstar))) * (Pi' - Pstar) :=
    InformationTheory.Shannon.ParallelGaussian.ConcaveOn.le_tangent_of_hasDerivAt
      (concaveOn_wfCost hNi)
      (Set.mem_Ici.mpr hPstar_nonneg) (Set.mem_Ici.mpr hPi') hderiv
  -- It suffices to dominate the actual slope by lam = 1/(2ν) on the (Pi' - Pstar) factor.
  refine le_trans h_tangent ?_
  have h_dom : (1 / (2 * (Ni + Pstar))) * (Pi' - Pstar)
      ≤ (1 / (2 * ν)) * (Pi' - Pstar) := by
    by_cases hact : Ni < ν
    · -- Active: Pstar = ν - Ni, so Ni + Pstar = ν, equality of slopes.
      have hP : Pstar = ν - Ni := by
        rw [hPstar_def]; exact waterFillingPower_eq_diff_of_active ν N i hact
      have hsum : Ni + Pstar = ν := by rw [hP]; ring
      rw [hsum]
    · -- Inactive: Pstar = 0, slope 1/(2Ni) ≤ 1/(2ν), factor Pi' - 0 ≥ 0.
      rw [not_lt] at hact
      have hP : Pstar = 0 := by
        rw [hPstar_def]; exact waterFillingPower_eq_zero_of_inactive ν N i hact
      rw [hP, sub_zero, add_zero]
      have h_slope_le : (1 / (2 * Ni)) ≤ (1 / (2 * ν)) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      exact mul_le_mul_of_nonneg_right h_slope_le hPi'
  linarith [h_dom]

/-! ## Phase F — Re-publish certificate-discharged capacity formula -/

/-- **WF-certificate Lagrange sub-predicate bundle**: stationarity + slackness
in one predicate, the structural witness consumed by the discharged formula. -/
def IsWFLagrangeBundle {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν lam : ℝ) : Prop :=
  IsWFStationarityHyp N ν lam ∧ IsWFComplementarySlacknessHyp P N ν lam

/-- The Lagrange bundle yields the optimality certificate (Phase D applied). -/
theorem waterFillingCertificate_of_bundle {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (ν lam : ℝ)
    (h_bundle : IsWFLagrangeBundle P N ν lam) :
    WaterFillingOptimalityCertificate P N ν :=
  waterFillingCertificate_of_lagrange P N ν lam h_bundle.1 h_bundle.2

/-- **Parallel Gaussian capacity formula (WF-certificate body discharged)**.

Same conclusion as `parallel_gaussian_capacity_formula_KKT_discharged`, but the
optimality certificate is now produced *internally* from a Lagrange-multiplier
bundle (KKT stationarity + complementary slackness) instead of taken as an
abstract hypothesis.

⚠️ NOT a full discharge: L-PG1 (the per-coordinate water-filling reduction)
remains OPEN — `h_for_bundle` is a conclusion-as-hypothesis (the capacity equality
split into two inequalities). The Lagrange-bundle *existence* (`h_for_lagrange`,
the convex-duality multiplier) is also still taken as a hypothesis (KKT-uniqueness
wall). Genuinely closed here: the certificate *body* (Lagrange reduction from a
given bundle, via genuine log-concavity), plus upstream L-WF1 and L-PG0. The
genuine L-PG1 reduction needs chain rule + per-coord AWGN capacity (continuous
AEP / sphere-shell volume) machinery absent from Mathlib.

`@audit:suspect(parallel-gaussian-moonshot-plan)` -/
theorem parallel_gaussian_capacity_formula_WFcert_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_for_lagrange : ∀ ν : ℝ, IsWaterFillingKKT P N ν →
        ∃ lam : ℝ, IsWFLagrangeBundle P N ν lam)
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
  -- Optimality certificate from the Lagrange bundle (Phase D body discharge).
  -- Independently derivable; kept here for posture documentation but not
  -- consumed by the final chain (the bundle IS the conclusion equality).
  obtain ⟨lam, h_bundle⟩ := h_for_lagrange ν hν_kkt
  have _h_cert : WaterFillingOptimalityCertificate P N ν :=
    waterFillingCertificate_of_bundle P N ν lam h_bundle
  have _h_opt : IsWaterFillingOptimal P N ν :=
    isWaterFillingOptimal_of_certificate P N ν _h_cert
  -- Chain rule bundle (L-PG1) → conclusion equality (def-unfold of
  -- `IsParallelGaussianPerCoordReduction`; `_of_bundle` runs `le_antisymm`).
  exact isParallelGaussianPerCoordReduction_of_bundle P N h_meas
    (isParallelGaussianKernelMeasurable N) ν (h_for_bundle ν hν_kkt)

end InformationTheory.Shannon.ParallelGaussian
