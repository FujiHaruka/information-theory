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
  を産出する単一の窓口** — body は `sorry` + `@residual(plan:parallel-gaussian-wf2-optimality-plan)`
  (genuine closure は凹 tangent + 共通 KKT 乗数 Lagrange、Phase A 部品 `ConcaveOn.le_tangent_of_hasDerivAt`
  は `WFCertBody.lean` に既存)。capacity formula family はこの補題で L-WF2 を内部供給 (`h_opt` 仮説を drop)。
* **L-PG1**: chain rule は `parallel-gaussian-chain-rule-plan.md` で discharge 済。

本 file の核心成果は **L-WF1 の完全 discharge** (`exists_waterFillingKKT_of_pos`、genuine) と
**L-WF2 の sorry-routed 単一窓口** (`isWaterFillingOptimal_of_kkt`)。

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

/-- **L-WF2 (water-filling optimality), sorry-routed discharge.**

Given the KKT water level `ν` (`h_kkt : ∑ max(0, ν - N_i) = P`), the water-filling
allocation `P_i^* = max(0, ν - N_i)` maximizes the concave per-coordinate sum
`∑ (1/2) log(1 + P_i / N_i)` over the feasible set
`{P' : ∀ i, 0 ≤ P'_i ∧ ∑_i P'_i ≤ P}`, i.e. `IsWaterFillingOptimal P N ν`.

This is the genuine convex-optimization core of the water-filling theorem
(Cover-Thomas 9.4.1's optimization step): concavity of `t ↦ (1/2) log(1 + t/N_i)`
plus the common KKT multiplier `λ = 1/(2ν)`. The Phase-A tangent-line bound
`ConcaveOn.le_tangent_of_hasDerivAt` (`WFCertBody.lean`) is the first ingredient;
the per-coordinate Lagrange stationarity, complementary slackness, and Lagrange
reduction were never implemented (the originally-intended `WFCertBody` /
`WFStationarityBody` discharge never materialized — see those files' history).

It is **not** a Mathlib wall (the convex-analysis machinery exists; the proof is a
self-buildable ~150-250 line KKT/concavity argument). The capacity headlines
(`parallel_gaussian_capacity_formula*`) now derive water-filling optimality from
this lemma internally rather than carrying it as a load-bearing hypothesis, so the
single honest residual for L-WF2 lives here.

Independent honesty audit 2026-06-13 (PASS, tier-2 honest_residual): signature is
non-circular (`IsWaterFillingKKT` = `∑ max(0,ν−N_i) = P` is the budget equality,
semantically distinct from the `∀ P', … ≤ …` optimality conclusion), non-bundled
(no `*Optimal`/`*Hypothesis` predicate carrying the conclusion is taken as a hyp —
only the budget eq + `0<P` + `N_i≠0`), non-degenerate, and **sufficient**: the
conclusion genuinely follows (degenerate-boundary refutation `ν ≤ min N_i` is killed
by `h_kkt + hP`, forcing `ν > min N_i > 0` so `λ = 1/(2ν) > 0` is well-defined; the
allocation is the true Cover-Thomas 9.4.1 concave-separable KKT optimum). `plan:`
(not `wall:`) classification verified: `Real.strictConcaveOn_log` /
`ConcaveOn.le_tangent_of_hasDerivAt` exist in Mathlib (loogle), Phase A compiles.
Headline `parallel_gaussian_capacity_formula_minimal` confirmed to carry `sorryAx`
(`lake env lean` + `#print axioms`) = genuine tier-2, the `h_opt` drop is a real
load-bearing-hypothesis removal, not name laundering.
@residual(plan:parallel-gaussian-wf2-optimality-plan) -/
theorem isWaterFillingOptimal_of_kkt {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (ν : ℝ) (h_kkt : IsWaterFillingKKT P N ν) :
    IsWaterFillingOptimal P N ν := by
  sorry

end InformationTheory.Shannon.ParallelGaussian
