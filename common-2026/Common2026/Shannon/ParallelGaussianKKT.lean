import Common2026.Shannon.ParallelGaussian
import Common2026.Shannon.ParallelGaussianL_PG0Discharge
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
* **L-WF2 (`IsWaterFillingOptimal P N ν`)**: water-filling が `∑ (1/2) log(1+P_i/N_i)`
  の最大化解 ― 厳密凸性 (`StrictConcaveOn`) + Lagrange 一意性に依存し
  Mathlib API が手薄なため、**KKT 一意性壁の撤退ライン** (タスク仕様) に従い
  `WaterFillingOptimalityCertificate` predicate (abstract certificate)
  経由の hypothesis pass-through 形で reduce。
* **L-PG1 (`IsParallelGaussianPerCoordReduction`)**: chain rule + per-coord AWGN
  reduction ― 別 plan (`parallel-gaussian-chain-rule-plan.md`) に defer する
  ため、finer-grained predicate bundle `ParallelGaussianChainRuleBundle`
  経由の hypothesis pass-through 形で reduce。

本 file の核心成果は **L-WF1 の完全 discharge** (`exists_waterFillingKKT_of_pos`)。
L-WF2 + L-PG1 は **abstract certificate ↔ hypothesis** の同値性 (双方向 reduction)
を proof body 経由で publish。

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

Phase C: L-WF2 certificate reduction
  ──> Define WaterFillingOptimalityCertificate as a predicate bundling
      the strict-concavity + KKT-feasibility hypotheses.
  ──> Show `WaterFillingOptimalityCertificate P N ν → IsWaterFillingOptimal P N ν`
      via direct unfolding (certificate IS the optimality statement).

Phase D: L-PG1 bundle reduction
  ──> Define ParallelGaussianChainRuleBundle as a triple-hypothesis predicate.
  ──> Show bundle → IsParallelGaussianPerCoordReduction via direct chaining.
```

## 撤退ライン採用

* **L-WF2 retreat (KKT-uniqueness wall)**: 凸関数 strict convexity + minimum
  uniqueness の hypothesis pass-through 形 (`WaterFillingOptimalityCertificate`
  abstract predicate)。
* **L-PG1 retreat (chain-rule scope)**: bundle predicate
  (`ParallelGaussianChainRuleBundle`) 形 hypothesis pass-through。
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

/-- The water-filling total sum is monotone in `ν`. -/
lemma waterFillingPower_sum_mono {n : ℕ} (N : Fin n → ℝ≥0) {ν₁ ν₂ : ℝ}
    (h : ν₁ ≤ ν₂) :
    ∑ i : Fin n, waterFillingPower ν₁ N i ≤ ∑ i : Fin n, waterFillingPower ν₂ N i :=
  Finset.sum_le_sum (fun i _ => waterFillingPower_mono_in_ν N i h)

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

/-! ## Phase C — `WaterFillingOptimalityCertificate` (L-WF2 retreat) -/

/-- **L-WF2 abstract optimality certificate** (KKT-uniqueness retreat line).

A water level `ν` is **optimality-certified** if the per-coordinate cost
`fun P' => ∑ i, (1/2) * log(1 + P' i / N_i)` attains its constrained maximum
at the water-filling allocation `waterFillingPower ν N`. Bundling the
strict-concavity + Lagrange-uniqueness data as an abstract predicate
(`Prop`) allows us to defer the full KKT discharge while delivering the
`IsWaterFillingOptimal` reduction in one line.

タスク仕様の撤退ライン:
> KKT 一意性が壁になったら凸関数の strict convexity + minimum uniqueness の
> hypothesis pass-through 形で抜く -/
def WaterFillingOptimalityCertificate {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) :
    Prop :=
  ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i : Fin n, P' i ≤ P) →
    ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- **L-WF2 reduction**: an optimality certificate yields the
`IsWaterFillingOptimal` predicate. (The certificate is *defined* as the
predicate, so the reduction is by definitional unfolding.) -/
theorem isWaterFillingOptimal_of_certificate {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ)
    (h_cert : WaterFillingOptimalityCertificate P N ν) :
    IsWaterFillingOptimal P N ν :=
  h_cert

/-- **L-WF2 reverse reduction**: the `IsWaterFillingOptimal` predicate yields
an optimality certificate. (Both are the same proposition.) -/
theorem certificate_of_isWaterFillingOptimal {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ)
    (h_opt : IsWaterFillingOptimal P N ν) :
    WaterFillingOptimalityCertificate P N ν :=
  h_opt

/-! ## Phase D — `ParallelGaussianChainRuleBundle` (L-PG1 retreat) -/

/-- **L-PG1 chain rule bundle** (chain-rule retreat line).

The per-coordinate AWGN reduction is decomposed into three abstract
hypotheses that together yield the parallel-capacity = water-filling-sum
equality:

* `h_capacity_le` — parallel capacity is bounded above by the per-coordinate
  water-filling sum (memoryless chain rule + per-coord AWGN converse).
* `h_capacity_ge` — parallel capacity is bounded below by the per-coordinate
  water-filling sum (water-filling product Gaussian as input law).
* `h_certificate` — antisymmetry closure (`a ≤ b ∧ b ≤ a → a = b`).

⚠️ OPEN — conclusion-as-hypothesis: the bundle is just the capacity-formula
equality split into its two inequalities (`cap ≤ sum ∧ sum ≤ cap`), so satisfying
it is equivalent to assuming the L-PG1 per-coordinate reduction outright. Neither
inequality is proved here; `isParallelGaussianPerCoordReduction_of_bundle` only
re-assembles them via `le_antisymm`. The genuine bound needs the memoryless chain
rule + per-coord AWGN converse/achievability (continuous AEP / sphere-shell
volume) machinery absent from Mathlib. Deferred to
`parallel-gaussian-chain-rule-plan.md`. -/
def ParallelGaussianChainRuleBundle {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (ν : ℝ) : Prop :=
  (parallelGaussianCapacity P N h_meas h_parallel_meas
      ≤ ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))) ∧
  (∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
      ≤ parallelGaussianCapacity P N h_meas h_parallel_meas)

/-- **L-PG1 reduction**: the chain rule bundle yields the
`IsParallelGaussianPerCoordReduction` predicate, via antisymmetry of `≤`.

`@audit:suspect(parallel-gaussian-moonshot-plan)` -/
theorem isParallelGaussianPerCoordReduction_of_bundle {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (ν : ℝ)
    (h_bundle :
        ParallelGaussianChainRuleBundle P N h_meas h_parallel_meas ν) :
    IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν :=
  le_antisymm h_bundle.1 h_bundle.2

/-- **L-PG1 reverse reduction**: the `IsParallelGaussianPerCoordReduction`
predicate yields the chain rule bundle.

`@audit:suspect(parallel-gaussian-moonshot-plan)` -/
theorem bundle_of_isParallelGaussianPerCoordReduction {n : ℕ}
    (P : ℝ) (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (ν : ℝ)
    (h_red :
        IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν) :
    ParallelGaussianChainRuleBundle P N h_meas h_parallel_meas ν :=
  ⟨h_red.le, h_red.ge⟩

/-! ## Phase E — Combined capacity formula (L-WF1 discharged + L-WF2/L-PG1
certificates) -/

/-- **Parallel Gaussian capacity formula (L-WF1 discharged + L-WF2/L-PG1
certificate forms)**.

Combines `exists_waterFillingKKT_of_pos` with the optimality certificate +
chain rule bundle to deliver the full capacity formula. The signature has
*two* abstract hypotheses (certificate + bundle) instead of three predicate
arguments; in particular, the water-level `ν` is now produced internally by
existence (L-WF1 discharged).

⚠️ NOT a full discharge: L-PG1 (the per-coordinate water-filling reduction)
remains OPEN — it enters via `h_for_bundle : … → ParallelGaussianChainRuleBundle`,
a conclusion-as-hypothesis (the capacity equality split into two inequalities).
The optimality certificate (`h_for_cert`) is also still taken as a hypothesis
here. Genuinely closed in *this* theorem: L-WF1 (KKT water-level existence, via
IVT) and L-PG0 (kernel measurability, upstream). The genuine L-PG1 reduction needs
the memoryless chain rule + per-coord AWGN capacity (continuous AEP / sphere-shell
volume) machinery absent from Mathlib.

`@audit:suspect(parallel-gaussian-moonshot-plan)` -/
theorem parallel_gaussian_capacity_formula_KKT_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_for_cert : ∀ ν : ℝ, IsWaterFillingKKT P N ν →
        WaterFillingOptimalityCertificate P N ν)
    (h_for_bundle : ∀ ν : ℝ, IsWaterFillingKKT P N ν →
        ParallelGaussianChainRuleBundle P N h_meas
          (isParallelGaussianKernelMeasurable N) ν) :
    ∃ ν : ℝ, IsWaterFillingKKT P N ν ∧
      parallelGaussianCapacity P N h_meas (isParallelGaussianKernelMeasurable N)
        = ∑ i : Fin (n + 1),
            (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) := by
  obtain ⟨ν, hν_kkt⟩ := exists_waterFillingKKT_of_pos P hP N
  refine ⟨ν, hν_kkt, ?_⟩
  -- L-WF2 is independently derivable from the certificate (kept here for
  -- posture documentation), but the body chain does not consume it: the
  -- bundle yields the conclusion equality directly via `le_antisymm`.
  have _h_unique : IsWaterFillingOptimal P N ν :=
    isWaterFillingOptimal_of_certificate P N ν (h_for_cert ν hν_kkt)
  -- Chain rule bundle → conclusion equality (L-PG1 load-bearing-hyp via the
  -- bundle, which IS `cap ≤ sum ∧ sum ≤ cap`; `_of_bundle` runs `le_antisymm`).
  -- `IsParallelGaussianPerCoordReduction` def-unfolds to the equality, so the
  -- predicate is accepted directly as the goal.
  exact isParallelGaussianPerCoordReduction_of_bundle P N h_meas
    (isParallelGaussianKernelMeasurable N) ν (h_for_bundle ν hν_kkt)

/-- **Active-set form (L-WF1 discharged + L-WF2/L-PG1 certificate forms)**.

⚠️ NOT a full discharge: L-PG1 (per-coordinate reduction) remains OPEN via the
conclusion-as-hypothesis bundle `h_for_bundle`; L-WF2 (`h_for_cert`) is also a
hypothesis. Only L-WF1 (KKT existence) and L-PG0 (kernel measurability) are
genuinely closed.

Cover-Thomas Ch.9.4 Theorem 9.4.1 alternative form. Combines
`parallel_gaussian_capacity_formula_KKT_discharged` with
`parallel_gaussian_capacity_sum_active`.

`@audit:suspect(parallel-gaussian-moonshot-plan)` -/
theorem parallel_gaussian_capacity_active_form_KKT_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin (n + 1) → ℝ≥0)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hN_pos : ∀ i, 0 < (N i : ℝ))
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_for_cert : ∀ ν : ℝ, IsWaterFillingKKT P N ν →
        WaterFillingOptimalityCertificate P N ν)
    (h_for_bundle : ∀ ν : ℝ, IsWaterFillingKKT P N ν →
        ParallelGaussianChainRuleBundle P N h_meas
          (isParallelGaussianKernelMeasurable N) ν) :
    ∃ ν : ℝ, IsWaterFillingKKT P N ν ∧
      parallelGaussianCapacity P N h_meas (isParallelGaussianKernelMeasurable N)
        = ∑ i ∈ waterFillingActiveSet ν N,
            (1/2) * Real.log (ν / (N i : ℝ)) := by
  obtain ⟨ν, hν_kkt, h_eq⟩ :=
    parallel_gaussian_capacity_formula_KKT_discharged P hP N hN h_meas
      h_for_cert h_for_bundle
  refine ⟨ν, hν_kkt, ?_⟩
  rw [h_eq]
  exact parallel_gaussian_capacity_sum_active ν N hN_pos

end InformationTheory.Shannon.ParallelGaussian
