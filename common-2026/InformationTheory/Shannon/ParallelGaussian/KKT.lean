import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ParallelGaussian.Basic
import InformationTheory.Shannon.ParallelGaussian.L_PG0Discharge
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# T2-B L-WF1 + L-WF2 + L-PG1 discharge: Parallel Gaussian water-filling KKT body

Cover-Thomas Ch.9.4 並列 Gaussian channel の **撤退ライン 3 本** —
L-WF1 (KKT 充足性), L-WF2 (一意性 / 最適性), L-PG1 (active-set ↔ water-filling
同値性) — の body を本 file で discharge する。

## 撤退ラインの位置づけ

親 plan `parallel-gaussian-moonshot-plan.md` の 3 つの hypothesis:

* **L-WF1 (`IsWaterFillingKKT P N ν`)**: `∑ waterFillingPower ν N = P`
  ― ν の存在 (intermediate value theorem) を本 file で discharge。
* **L-WF2 (`IsWaterFillingOptimal P N ν`)**: water-filling が制約付き log-sum 最大化解。
  当初は `WaterFillingOptimalityCertificate` 経由の abstract-certificate retreat predicate で
  reduce する設計だったが、load-bearing bundling + reduction 未配線 + consumer 0 のため orphan
  cleanup で削除 (2026-06-13)。**現在は本 file の `isWaterFillingOptimal_of_kkt` が `IsWaterFillingOptimal`
  を産出する単一の窓口** — body は genuine 証明済 (2026-06-13、共通 KKT 乗数 `λ = 1/(2ν)` での
  per-coord tangent 上界 `waterFillingCost_tangent_le` を足し上げ、相補スラックネス + `λ≥0` で
  線形剰余を潰す Lagrange reduction、`Real.log_le_sub_one_of_pos` 直接ルート)。capacity formula
  family はこの補題で L-WF2 を内部供給 (`h_opt` 仮説を drop)。
* **L-PG1**: chain rule は `parallel-gaussian-chain-rule-plan.md` で discharge 済。

本 file の核心成果は **L-WF1 の完全 discharge** (`exists_waterFillingKKT_of_pos`、genuine) と
**L-WF2 の genuine discharge** (`isWaterFillingOptimal_of_kkt`、sorryAx-free)。

## Approach

```
Phase A: Continuity / monotonicity of g(ν) := ∑ max(0, ν - N_i)
  ──> g is continuous (Continuous.max + continuous_finsetSum)
  ──> g is monotone (waterFillingPower_mono_in_ν + Finset.sum_le_sum)
  ──> g(min N) = 0  (every term is max(0, -nonneg) = 0)
  ──> g(max N + P/n + 1) ≥ P  (each term ≥ ν - max N ≥ P/n, sum ≥ P)

Phase B: IVT on g over [min N, max N + P/n + 1]
  ──> ∃ ν ∈ Icc, g(ν) = P  (intermediate_value_Icc)
  ──> 撤退ライン L-WF1 fully discharged.

(旧 Phase C/D = L-WF2/L-PG1 の abstract-certificate retreat predicate は consumer 0 の
 dead scaffolding として削除済 — 上記 module docstring 参照。)
```
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — `waterFillingPower` sum continuity + monotonicity -/

/-- `waterFillingPower ν N i` is continuous in `ν`. -/
lemma waterFillingPower_continuous_in_ν {n : ℕ} (N : Fin n → ℝ≥0) (i : Fin n) :
    Continuous (fun ν : ℝ => waterFillingPower ν N i) := by
  unfold waterFillingPower
  exact continuous_const.max (continuous_id.sub continuous_const)

/-- The water-filling total sum `∑_i max(0, ν - N_i)` is continuous in `ν`. -/
lemma waterFillingPower_sum_continuous {n : ℕ} (N : Fin n → ℝ≥0) :
    Continuous (fun ν : ℝ => ∑ i : Fin n, waterFillingPower ν N i) := by
  refine continuous_finsetSum _ ?_
  intro i _
  exact waterFillingPower_continuous_in_ν N i


/-- At `ν ≤ min_i N_i`, every coordinate is inactive, so the sum is `0`. -/
lemma waterFillingPower_sum_eq_zero_of_le_min {n : ℕ} (N : Fin n → ℝ≥0)
    {ν : ℝ} (h : ∀ i, ν ≤ (N i : ℝ)) :
    ∑ i : Fin n, waterFillingPower ν N i = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact waterFillingPower_eq_zero_of_inactive ν N i (h i)

/-- For `ν ≥ Nmax + bound`, every coordinate is active and contributes at least
`ν - Nmax` to the sum, giving a sum ≥ `n · (ν - Nmax)`. -/
lemma waterFillingPower_sum_ge_of_all_active {n : ℕ} (N : Fin n → ℝ≥0)
    {Nmax ν : ℝ} (hNmax : ∀ i, (N i : ℝ) ≤ Nmax) (hν : Nmax ≤ ν) :
    (n : ℝ) * (ν - Nmax) ≤ ∑ i : Fin n, waterFillingPower ν N i := by
  -- Each term ≥ ν - Nmax (since N_i ≤ Nmax ⇒ ν - N_i ≥ ν - Nmax ≥ 0).
  have h_pointwise : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ν - Nmax ≤ waterFillingPower ν N i := by
    intro i _
    unfold waterFillingPower
    have h1 : ν - Nmax ≤ ν - (N i : ℝ) := by linarith [hNmax i]
    exact le_max_of_le_right h1
  -- Use `Finset.sum_le_sum` against the constant `ν - Nmax` and `card_univ`.
  have h_sum :
      ∑ _i : Fin n, (ν - Nmax) ≤ ∑ i : Fin n, waterFillingPower ν N i :=
    Finset.sum_le_sum h_pointwise
  -- ∑ _ : Fin n, c = n * c
  have h_const :
      ∑ _i : Fin n, (ν - Nmax) = (n : ℝ) * (ν - Nmax) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  rw [h_const] at h_sum
  exact h_sum

/-! ## Phase B — `exists_waterFillingKKT_of_pos` (L-WF1 discharge via IVT) -/

/-- **L-WF1 discharge (existence of KKT water level)**: For positive total power
`P > 0` and finite noise vector `N : Fin (n+1) → ℝ≥0` (at least one coordinate),
there exists a water level `ν` such that the water-filling allocation exactly
uses up all the power `∑_i max(0, ν - N_i) = P`.

**Strategy**: The function `g(ν) := ∑_i waterFillingPower ν N i` is continuous
and monotone in `ν`. At `ν₀ = min_i N_i` (or any value below), `g(ν₀) = 0 ≤ P`.
At `ν₁ = Nmax + P` (or any value sufficiently large), `g(ν₁) ≥ (n+1)·P ≥ P`.
Intermediate value theorem (`intermediate_value_Icc`) gives `ν ∈ [ν₀, ν₁]` with
`g(ν) = P`. -/
@[entry_point]
theorem exists_waterFillingKKT_of_pos {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) :
    ∃ ν : ℝ, IsWaterFillingKKT P N ν := by
  -- Step 1: Define Nmax as the maximum noise value across coordinates.
  -- Since `Fin (n+1)` is nonempty, `Finset.univ.sup'` is well-defined.
  classical
  -- Use the max over the canonical Fin (n+1) Finset.
  set Nmax : ℝ :=
    (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty (fun i => (N i : ℝ))
    with hNmax_def
  have hNmax_ge : ∀ i, (N i : ℝ) ≤ Nmax :=
    fun i => Finset.le_sup' (fun i => (N i : ℝ)) (Finset.mem_univ i)
  -- Step 2: Build the two endpoints ν₀ = 0, ν₁ = Nmax + P + 1.
  -- Note: we need (n+1)·(ν₁ - Nmax) ≥ P, i.e., (n+1)·(P+1) ≥ P, true for any n.
  set ν₀ : ℝ := min 0 (Finset.univ.inf' Finset.univ_nonempty (fun i => (N i : ℝ)))
    with hν₀_def
  set ν₁ : ℝ := Nmax + P + 1 with hν₁_def
  -- Step 3: At ν₀, the sum is 0 (every coord is inactive).
  have hν₀_le_N : ∀ i, ν₀ ≤ (N i : ℝ) := by
    intro i
    have h_inf : Finset.univ.inf' Finset.univ_nonempty (fun i => (N i : ℝ))
        ≤ (N i : ℝ) :=
      Finset.inf'_le (fun i => (N i : ℝ)) (Finset.mem_univ i)
    exact le_trans (min_le_right _ _) h_inf
  have hg_ν₀ : ∑ i : Fin (n + 1), waterFillingPower ν₀ N i = 0 :=
    waterFillingPower_sum_eq_zero_of_le_min N hν₀_le_N
  -- Step 4: At ν₁, the sum is ≥ P.
  have hν₁_ge : Nmax ≤ ν₁ := by
    show Nmax ≤ Nmax + P + 1; linarith
  have hsum_lb : (((n + 1 : ℕ) : ℝ)) * (ν₁ - Nmax)
      ≤ ∑ i : Fin (n + 1), waterFillingPower ν₁ N i :=
    waterFillingPower_sum_ge_of_all_active N hNmax_ge hν₁_ge
  have hg_ν₁_ge : P ≤ ∑ i : Fin (n + 1), waterFillingPower ν₁ N i := by
    refine le_trans ?_ hsum_lb
    have h_n_pos : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
      exact_mod_cast this
    have h_diff : (1 : ℝ) ≤ ν₁ - Nmax := by
      show (1 : ℝ) ≤ Nmax + P + 1 - Nmax; linarith
    have h_diff_pos : 0 ≤ ν₁ - Nmax := by linarith
    have h_nn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    -- We want P ≤ (n+1)·(ν₁ - Nmax).
    -- (n+1)·(ν₁ - Nmax) = (n+1)·(P + 1) ≥ 1·(P + 1) = P + 1 ≥ P.
    have h_eq : ν₁ - Nmax = P + 1 := by
      show Nmax + P + 1 - Nmax = P + 1; ring
    rw [h_eq]
    calc P ≤ P + 1 := by linarith
      _ = 1 * (P + 1) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * (P + 1) :=
          mul_le_mul_of_nonneg_right h_n_pos (by linarith)
  -- Step 5: ν₀ ≤ ν₁.
  have hν₀_le_ν₁ : ν₀ ≤ ν₁ := by
    have h1 : ν₀ ≤ 0 := min_le_left _ _
    have h2 : (0 : ℝ) ≤ Nmax := by
      -- Nmax = max_i (N i) ≥ (N 0 : ℝ) ≥ 0.
      have h_nn : (0 : ℝ) ≤ (N 0 : ℝ) := NNReal.coe_nonneg _
      exact le_trans h_nn (hNmax_ge 0)
    show ν₀ ≤ Nmax + P + 1; linarith
  -- Step 6: Apply IVT to g on [ν₀, ν₁].
  have hg_cont : ContinuousOn (fun ν => ∑ i : Fin (n + 1), waterFillingPower ν N i)
      (Set.Icc ν₀ ν₁) :=
    (waterFillingPower_sum_continuous N).continuousOn
  have hP_in_Icc : P ∈ Set.Icc
      (∑ i : Fin (n + 1), waterFillingPower ν₀ N i)
      (∑ i : Fin (n + 1), waterFillingPower ν₁ N i) := by
    rw [hg_ν₀]
    exact ⟨le_of_lt hP, hg_ν₁_ge⟩
  obtain ⟨ν, hν_mem, hν_eq⟩ :=
    intermediate_value_Icc hν₀_le_ν₁ hg_cont hP_in_Icc
  exact ⟨ν, hν_eq⟩

/-! ## L-WF2 genuine closure helpers (Cover-Thomas 9.4.1 optimization step) -/

/-- Each noise level is strictly positive (from `(N i : ℝ) ≠ 0` and `0 ≤ (N i : ℝ)`). -/
lemma noise_pos {n : ℕ} (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0) (i : Fin n) :
    0 < (N i : ℝ) :=
  lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm (hN i))

/-- **`ν > 0` from the KKT budget equality.** If `ν ≤ N_i` for every `i`, all
coordinates are inactive and the water-filling sum is `0 = P`, contradicting
`0 < P`. Hence some coordinate is active (`ν > N_i ≥ 0`), forcing `ν > 0`. -/
lemma waterFillingKKT_level_pos {n : ℕ} (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) :
    0 < ν := by
  by_contra h
  rw [not_lt] at h
  -- `ν ≤ 0` ⇒ every coordinate inactive ⇒ sum = 0 = P, contradicting `0 < P`.
  have hsum0 : ∑ i : Fin n, waterFillingPower ν N i = 0 := by
    apply waterFillingPower_sum_eq_zero_of_le_min
    intro i
    have : (0 : ℝ) ≤ (N i : ℝ) := NNReal.coe_nonneg _
    linarith
  rw [IsWaterFillingKKT] at h_kkt
  rw [hsum0] at h_kkt
  linarith

/-- **Per-coordinate tangent (KKT-stationarity) upper bound.** For the common KKT
multiplier `λ = 1/(2ν)`, the per-coordinate cost
`g_i(t) = (1/2) log(1 + t/N_i)` satisfies
`g_i(P'_i) ≤ g_i(P*_i) + λ·(P'_i − P*_i)` where `P*_i = waterFillingPower ν N i`.

Derived directly from the elementary tangent inequality `log u ≤ u − 1`
(`Real.log_le_sub_one_of_pos`) applied to `u = (N_i + P'_i)/(N_i + P*_i) > 0`,
giving `g_i(P'_i) − g_i(P*_i) ≤ (1/2)·(P'_i − P*_i)/(N_i + P*_i)`; then
`N_i + P*_i = ν` (active) or `N_i + P*_i = N_i ≥ ν` (inactive) bounds the slope by
`λ` using `P'_i − P*_i = P'_i ≥ 0` in the inactive case. -/
lemma waterFillingCost_tangent_le {n : ℕ} (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (ν : ℝ) (hν : 0 < ν) (i : Fin n) {P'i : ℝ} (hP'i : 0 ≤ P'i) :
    (1/2) * Real.log (1 + P'i / (N i : ℝ))
      ≤ (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
        + (1 / (2 * ν)) * (P'i - waterFillingPower ν N i) := by
  set a : ℝ := (N i : ℝ) with ha_def
  have ha_pos : 0 < a := noise_pos N hN i
  set Pstar : ℝ := waterFillingPower ν N i with hPstar_def
  have hPstar_nonneg : 0 ≤ Pstar := waterFillingPower_nonneg ν N i
  -- positivity of the two arguments of `log`
  have h1 : 0 < a + P'i := by linarith
  have h2 : 0 < a + Pstar := by linarith
  -- rewrite `1 + t/a = (a + t)/a`
  have heq1 : 1 + P'i / a = (a + P'i) / a := by field_simp
  have heq2 : 1 + Pstar / a = (a + Pstar) / a := by field_simp
  rw [heq1, heq2]
  -- log of ratio
  have hlog1 : Real.log ((a + P'i) / a) = Real.log (a + P'i) - Real.log a := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hlog2 : Real.log ((a + Pstar) / a) = Real.log (a + Pstar) - Real.log a := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [hlog1, hlog2]
  -- tangent inequality: log(a+P'i) - log(a+Pstar) ≤ (P'i - Pstar)/(a + Pstar)
  have h_tangent : Real.log (a + P'i) - Real.log (a + Pstar)
      ≤ (P'i - Pstar) / (a + Pstar) := by
    have hu_pos : 0 < (a + P'i) / (a + Pstar) := div_pos h1 h2
    have h_log_ratio : Real.log ((a + P'i) / (a + Pstar)) ≤ (a + P'i) / (a + Pstar) - 1 :=
      Real.log_le_sub_one_of_pos hu_pos
    rw [Real.log_div (by linarith) (by linarith)] at h_log_ratio
    have h_simp : (a + P'i) / (a + Pstar) - 1 = (P'i - Pstar) / (a + Pstar) := by
      field_simp; ring
    linarith [h_simp ▸ h_log_ratio]
  -- slope bound: (1/2)·(P'i - Pstar)/(a + Pstar) ≤ (1/(2ν))·(P'i - Pstar)
  have h_slope : (1 / 2) * ((P'i - Pstar) / (a + Pstar))
      ≤ (1 / (2 * ν)) * (P'i - Pstar) := by
    by_cases h_inactive : ν ≤ a
    · -- inactive: Pstar = 0, a ≥ ν, slope = (1/2)·P'i/a ≤ (1/2)·P'i/ν
      have hPstar0 : Pstar = 0 := by
        rw [hPstar_def]; exact waterFillingPower_eq_zero_of_inactive ν N i h_inactive
      rw [hPstar0]
      simp only [sub_zero, add_zero]
      -- goal: (1/2) * (P'i / a) ≤ (1/(2ν)) * P'i
      have h_inv : a⁻¹ ≤ ν⁻¹ := by gcongr
      have h_prod : P'i * a⁻¹ ≤ P'i * ν⁻¹ := mul_le_mul_of_nonneg_left h_inv hP'i
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hν_ne : ν ≠ 0 := ne_of_gt hν
      have hlhs : (1/2) * (P'i / a) = (1/2) * (P'i * a⁻¹) := by
        rw [div_eq_mul_inv P'i a]
      have hrhs : (1 / (2 * ν)) * P'i = (1/2) * (P'i * ν⁻¹) := by
        field_simp
      rw [hlhs, hrhs]
      linarith
    · -- active: Pstar = ν - a > 0, a + Pstar = ν
      have h_active : a < ν := not_le.mp h_inactive
      have hPstar_eq : Pstar = ν - a := by
        rw [hPstar_def]; simp only [waterFillingPower_apply]
        exact max_eq_right (by linarith)
      have h_aP : a + Pstar = ν := by rw [hPstar_eq]; ring
      rw [h_aP]
      have hν_ne : ν ≠ 0 := ne_of_gt hν
      -- the two slope expressions with denominator ν are equal
      apply le_of_eq
      field_simp
  -- combine
  calc (1/2) * (Real.log (a + P'i) - Real.log a)
      = (1/2) * (Real.log (a + Pstar) - Real.log a)
        + (1/2) * (Real.log (a + P'i) - Real.log (a + Pstar)) := by ring
    _ ≤ (1/2) * (Real.log (a + Pstar) - Real.log a)
        + (1/2) * ((P'i - Pstar) / (a + Pstar)) := by
          have := mul_le_mul_of_nonneg_left h_tangent (by norm_num : (0:ℝ) ≤ 1/2)
          linarith
    _ ≤ (1/2) * (Real.log (a + Pstar) - Real.log a)
        + (1 / (2 * ν)) * (P'i - Pstar) := by linarith [h_slope]

/-- **L-WF2 (water-filling optimality), genuine discharge.**

Given the KKT water level `ν` (`h_kkt : ∑ max(0, ν - N_i) = P`), the water-filling
allocation `P_i^* = max(0, ν - N_i)` maximizes the concave per-coordinate sum
`∑ (1/2) log(1 + P_i / N_i)` over the feasible set
`{P' : ∀ i, 0 ≤ P'_i ∧ ∑_i P'_i ≤ P}`, i.e. `IsWaterFillingOptimal P N ν`.

This is the genuine convex-optimization core of the water-filling theorem
(Cover-Thomas 9.4.1's optimization step). Proof: the common KKT multiplier
`λ = 1/(2ν)` gives a per-coordinate tangent (stationarity) upper bound
`g_i(P'_i) ≤ g_i(P*_i) + λ·(P'_i − P*_i)` (`waterFillingCost_tangent_le`,
derived from the elementary `log u ≤ u − 1`). Summing over `i`,
`∑ g_i(P'_i) ≤ ∑ g_i(P*_i) + λ·(∑P'_i − ∑P*_i)`. Complementary slackness
`∑P*_i = P` (= `h_kkt`) and feasibility `∑P'_i ≤ P` make the linear remainder
`λ·(∑P'_i − P) ≤ 0` (since `λ ≥ 0` from `ν > 0`, `waterFillingKKT_level_pos`),
yielding `∑ g_i(P'_i) ≤ ∑ g_i(P*_i)`. The `ν ≤ min N_i` degenerate boundary is
killed by `h_kkt + hP` (it would force `∑ = 0 ≠ P`), so `λ = 1/(2ν)` is
well-defined and nonnegative.

Proof done (0 sorry / 0 residual, sorryAx-free `#print axioms` =
`[propext, Classical.choice, Quot.sound]`). No load-bearing hypothesis — only the
budget equality `h_kkt`, `0<P`, `N_i≠0` are taken, all preconditions/regularity;
the optimality conclusion (`∀ feasible P', ∑ cost(P') ≤ ∑ cost(P*)`) is genuinely
derived, not encoded in any hypothesis.

@audit:ok — independent honesty audit 2026-06-13 (commit 3529022): all four
honesty checks PASS. (1) non-circular: body is a genuine intro + per-coord
tangent + sum + complementary-slackness derivation, no hypothesis has type
`IsWaterFillingOptimal`. (2) non-load-bearing: `h_kkt` is the budget equality
pinning `ν` (a precondition, IVT-dischargeable via `exists_waterFillingKKT_of_pos`),
not the optimality conclusion; core-reconstruction test fails to extract the cost
ordering from the hypotheses alone. (3) non-degenerate: `IsWaterFillingOptimal`
is a genuine `∀ feasible P'` inequality (not `:True`). (4) sufficiency: tangent
bound (`log u ≤ u−1`) + active/inactive slope split (active slope `=1/(2ν)`,
inactive `1/(2a)≤1/(2ν)` with `P'_i≥0`) + `λ≥0` from `ν>0` genuinely yields the
conclusion; degenerate boundaries (`P'=P*`, `P'=0`, `n=0`) substituted, no
counterexample. `#print axioms` sorryAx-free machine-confirmed for this lemma and
the helpers `noise_pos` / `waterFillingKKT_level_pos` / `waterFillingCost_tangent_le`. -/
@[entry_point]
theorem isWaterFillingOptimal_of_kkt {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) :
    IsWaterFillingOptimal P N ν := by
  -- `ν > 0` from the KKT budget equality, so `λ = 1/(2ν) ≥ 0`.
  have hν : 0 < ν := waterFillingKKT_level_pos P hP N ν h_kkt
  have hlam_nonneg : 0 ≤ 1 / (2 * ν) := by positivity
  intro P' hP'_nonneg hP'_sum
  -- per-coordinate tangent bound, summed
  have h_pointwise : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (1/2) * Real.log (1 + P' i / (N i : ℝ))
        ≤ (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
          + (1 / (2 * ν)) * (P' i - waterFillingPower ν N i) := by
    intro i _
    exact waterFillingCost_tangent_le N hN ν hν i (hP'_nonneg i)
  have h_sum_le :
      ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))
        ≤ ∑ i : Fin n, ((1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
          + (1 / (2 * ν)) * (P' i - waterFillingPower ν N i)) :=
    Finset.sum_le_sum h_pointwise
  -- split the RHS sum into the optimal-cost sum + the linear remainder
  rw [Finset.sum_add_distrib] at h_sum_le
  -- the linear remainder: λ · (∑P'_i − ∑P*_i) = λ · (∑P'_i − P) ≤ 0
  have h_rem : ∑ i : Fin n, (1 / (2 * ν)) * (P' i - waterFillingPower ν N i) ≤ 0 := by
    rw [← Finset.mul_sum]
    have h_diff_sum : ∑ i : Fin n, (P' i - waterFillingPower ν N i)
        = (∑ i : Fin n, P' i) - P := by
      rw [Finset.sum_sub_distrib]
      rw [IsWaterFillingKKT] at h_kkt
      rw [h_kkt]
    rw [h_diff_sum]
    have h_le_zero : (∑ i : Fin n, P' i) - P ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hlam_nonneg h_le_zero
  linarith

end InformationTheory.Shannon.ParallelGaussian
