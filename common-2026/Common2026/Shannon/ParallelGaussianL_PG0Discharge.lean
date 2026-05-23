import Common2026.Shannon.ParallelGaussian

/-!
# T2-B L-PG0 discharge: Parallel Gaussian kernel measurability

Cover-Thomas Ch.9.4 Parallel Gaussian channels の **撤退ライン L-PG0
(parallel kernel measurability) を discharge** した形で
`parallel_gaussian_capacity_formula` および
`parallel_gaussian_capacity_active_form` を再 publish。

## 撤退ラインの位置づけ

親 plan `parallel-gaussian-moonshot-plan.md` の L-PG0 は
`Measurable (fun x : Fin n → ℝ => Measure.pi (fun i => gaussianReal (x i) (N i)))`
の hypothesis pass-through (`IsParallelGaussianKernelMeasurable N`)。

本 file ではこの述語を **Mathlib の `gaussianReal_map_const_add`** と
**`MeasureTheory.Measure.pi_map_pi`** を組合せ、AWGN F-1 と並行な Giry monad
議論で完全証明する (`isParallelGaussianKernelMeasurable`)。

## Approach

```
gaussianReal (x i) (N i)
  = (gaussianReal 0 (N i)).map (x i + ·)                   -- per coord shift
```
を全 `i` に展開すると `pi_map_pi`:
```
Measure.pi (fun i => gaussianReal (x i) (N i))
  = (Measure.pi (fun i => gaussianReal 0 (N i))).map
      (fun y i => x i + y i)
```
パラメータ依存 measure を **固定の** product Gaussian の pushforward に
書き直せる。Map measurability は AWGN F-1 と同じく
`Measure.measurable_of_measurable_coe` + `measurable_measure_prodMk_left`
で finish。

詳細は `docs/shannon/parallel-gaussian-l-pg0-discharge-moonshot-plan.md` 参照。
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — `isParallelGaussianKernelMeasurable` discharge -/

/-- Per-coordinate shift identity:
`gaussianReal (x i) (N i) = (gaussianReal 0 (N i)).map (x i + ·)`.
特殊化 `μ = 0` of `gaussianReal_map_const_add` (`Mathlib`). -/
lemma gaussianReal_eq_zero_map_coord {n : ℕ} (N : Fin n → ℝ≥0)
    (x : Fin n → ℝ) (i : Fin n) :
    gaussianReal (x i) (N i) = (gaussianReal 0 (N i)).map (x i + ·) := by
  rw [gaussianReal_map_const_add (x i), zero_add]

/-- **Product-Gaussian shift identity**: the parameter-dependent product
measure is the pushforward of the fixed centered product Gaussian under the
coordinatewise shift `fun y i => x i + y i`. -/
lemma gaussianReal_pi_eq_zero_map {n : ℕ} (N : Fin n → ℝ≥0)
    (x : Fin n → ℝ) :
    Measure.pi (fun i => gaussianReal (x i) (N i))
      = (Measure.pi (fun i => gaussianReal 0 (N i))).map
          (fun y i => x i + y i) := by
  -- Rewrite each marginal as a shift, then commute pi/map via pi_map_pi.
  have h_fun_eq :
      (fun i => gaussianReal (x i) (N i))
        = (fun i => (gaussianReal 0 (N i)).map (x i + ·)) := by
    funext i; exact gaussianReal_eq_zero_map_coord N x i
  rw [h_fun_eq]
  -- `pi_map_pi` (`Mathlib.MeasureTheory.Constructions.Pi:390`):
  --   `(pi μ).map (fun y i => f i (y i)) = pi (fun i => (μ i).map (f i))`
  -- with `μ i := gaussianReal 0 (N i)` and `f i := (x i + ·)`.
  have h_meas_shift : ∀ i, Measurable ((x i + ·) : ℝ → ℝ) :=
    fun i => measurable_const.add measurable_id
  have h_ae_meas : ∀ i, AEMeasurable ((x i + ·) : ℝ → ℝ)
      (gaussianReal 0 (N i)) :=
    fun i => (h_meas_shift i).aemeasurable
  -- Each pushforward marginal is a Gaussian, hence a probability measure,
  -- hence sigma-finite. Provide instance via the rewrite identity.
  haveI h_sigma : ∀ i, SigmaFinite
      ((gaussianReal 0 (N i)).map ((x i + ·) : ℝ → ℝ)) := by
    intro i
    rw [← gaussianReal_eq_zero_map_coord N x i]
    infer_instance
  exact (Measure.pi_map_pi h_ae_meas).symm

/-- **Parallel Gaussian kernel measurability** (撤退ライン L-PG0 の discharge).

The map `x : Fin n → ℝ ↦ Measure.pi (fun i => gaussianReal (x i) (N i))` is
measurable as a function into `Measure (Fin n → ℝ)` (Giry monad).

Strategy: rewrite the parameter-dependent product Gaussian as the
pushforward of a **fixed** centered product Gaussian under the
coordinatewise shift; then apply Giry monad measurability of pushforward
maps in the parameter (AWGN F-1 pattern lifted from `ℝ` to `Fin n → ℝ`). -/
theorem isParallelGaussianKernelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) :
    IsParallelGaussianKernelMeasurable N := by
  unfold IsParallelGaussianKernelMeasurable
  -- Rewrite the parameter-dependent measure as a pushforward.
  have h_fun_eq :
      (fun x : Fin n → ℝ => Measure.pi (fun i => gaussianReal (x i) (N i)))
        = (fun x : Fin n → ℝ =>
            (Measure.pi (fun i => gaussianReal 0 (N i))).map
              (fun y i => x i + y i)) := by
    funext x; exact gaussianReal_pi_eq_zero_map N x
  rw [h_fun_eq]
  -- Giry monad: ∀ s, ms s → Measurable (fun x ↦ (... .map (shift x)) s).
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  -- The uncurried shift `(p : (Fin n → ℝ) × (Fin n → ℝ)) ↦ fun i => p.1 i + p.2 i`
  -- is measurable: each coordinate is `(fst.eval i).add (snd.eval i)`.
  have h_uncurry_meas :
      Measurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + p.2 i) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).add
      ((measurable_pi_apply i).comp measurable_snd)
  have h_set :
      MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ)
        | (fun i => p.1 i + p.2 i) ∈ s} :=
    h_uncurry_meas hs
  -- Rewrite `(shift x).map s` via `Measure.map_apply`, then identify the
  -- preimage with `Prod.mk x ⁻¹' {p | ...}` (rfl).
  have h_apply_eq :
      (fun x : Fin n → ℝ =>
          ((Measure.pi (fun i => gaussianReal 0 (N i))).map
              (fun y i => x i + y i)) s)
        = (fun x : Fin n → ℝ =>
            (Measure.pi (fun i => gaussianReal 0 (N i)))
              (Prod.mk x ⁻¹' {p : (Fin n → ℝ) × (Fin n → ℝ)
                | (fun i => p.1 i + p.2 i) ∈ s})) := by
    funext x
    have h_shift_meas :
        Measurable (fun y : Fin n → ℝ => fun i => x i + y i) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      exact measurable_const.add (measurable_pi_apply i)
    rw [Measure.map_apply h_shift_meas hs]
    rfl
  rw [h_apply_eq]
  exact measurable_measure_prodMk_left h_set

/-! ## Phase B — `parallel_gaussian_capacity_formula` re-publish (L-PG0 discharge 形) -/

/-- 🟢ʰ **load-bearing hypothesis — NOT a discharge.**
**Parallel Gaussian capacity formula with L-PG0 closed** (Cover-Thomas
Theorem 9.4.1, reduction-from-perCoordReduction form).

ONLY L-PG0 (parallel kernel measurability) is mechanically closed here via the
`isParallelGaussianKernelMeasurable` discharge in this file. The per-coordinate
water-filling reduction (L-PG1, `h_perCoordReduction_lbh`) remains a load-bearing
hypothesis — the predicate `IsParallelGaussianPerCoordReduction` IS the conclusion
equality, so passing it through is intentional pass-through, not a discharge.
L-WF1 (`h_kkt`) and L-WF2 (`h_unique`) likewise remain hypotheses.

The genuine L-PG1 reduction needs water-filling KKT + per-coord AWGN capacity
(continuous AEP / sphere-shell volume) machinery absent from Mathlib; the
hypothesis-free headline is
`ParallelGaussianPerCoord.parallel_gaussian_capacity_formula`.

親定理 `parallel_gaussian_capacity_formula_of_perCoordReduction`
(`ParallelGaussian.lean`) の `h_parallel_meas` を本 file の
`isParallelGaussianKernelMeasurable N` で埋めて再 publish (= L-PG0 closure)。
signature から `h_parallel_meas` が消える。残りの撤退ライン hypothesis
(L-PG1 per-coord reduction / L-WF1 KKT / L-WF2 optimality) はそのまま pass-through。

Renamed from `*_PG0_discharged` (laundering: only L-PG0 closed; full discharge
absent) → `*_PG0closed_of_perCoordReduction` to expose the load-bearing posture. -/
theorem parallel_gaussian_capacity_formula_PG0closed_of_perCoordReduction {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_perCoordReduction_lbh :
        IsParallelGaussianPerCoordReduction P N h_meas
          (isParallelGaussianKernelMeasurable N) ν) :
    parallelGaussianCapacity P N h_meas (isParallelGaussianKernelMeasurable N)
      = ∑ i : Fin n, (1/2) * Real.log
          (1 + waterFillingPower ν N i / (N i : ℝ)) :=
  parallel_gaussian_capacity_formula_of_perCoordReduction P hP N hN h_meas
    (isParallelGaussianKernelMeasurable N) ν h_kkt h_unique h_perCoordReduction_lbh

/-- **Active-set form of the parallel Gaussian capacity formula**
(L-PG0 discharge 形, Cover-Thomas Theorem 9.4.1 restated).

⚠️ ONLY L-PG0 (kernel measurability) is discharged; L-PG1 (`h_per_coord`,
conclusion-as-hypothesis), L-WF1 (`h_kkt`) and L-WF2 (`h_unique`) remain OPEN —
taken as hypotheses.

親 `parallel_gaussian_capacity_active_form` の `h_parallel_meas` を埋めて
再 publish。 -/
theorem parallel_gaussian_capacity_active_form_PG0_discharged {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hN_pos : ∀ i, 0 < (N i : ℝ))
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_per_coord :
        IsParallelGaussianPerCoordReduction P N h_meas
          (isParallelGaussianKernelMeasurable N) ν) :
    parallelGaussianCapacity P N h_meas (isParallelGaussianKernelMeasurable N)
      = ∑ i ∈ waterFillingActiveSet ν N,
          (1/2) * Real.log (ν / (N i : ℝ)) :=
  parallel_gaussian_capacity_active_form_of_perCoordReduction P hP N hN hN_pos h_meas
    (isParallelGaussianKernelMeasurable N) ν h_kkt h_unique h_per_coord

end InformationTheory.Shannon.ParallelGaussian
