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

/-! ## Phase B — legacy PG0-closed wrappers (retracted)

`parallel_gaussian_capacity_formula_PG0closed_of_perCoordReduction` and
`parallel_gaussian_capacity_active_form_PG0_discharged` were re-publishes of the
`*_of_perCoordReduction` reduction wrappers (`ParallelGaussian.lean`) with the
L-PG0 hypothesis filled by `isParallelGaussianKernelMeasurable N`. They added
no derivation beyond that fill; the un-active wrapper itself was a `:= h`
pass-through (`IsParallelGaussianPerCoordReduction` def-unfolds to the goal
equality). Both wrappers, plus their `_of_perCoordReduction` parents, have been
retracted. Callers (`ParallelGaussianKKT.lean`, `ParallelGaussianWFCertBody.lean`,
`ParallelGaussianWFStationarityBody.lean`) now consume
`IsParallelGaussianPerCoordReduction` directly via def-unfolding of the
predicate. The honest hypothesis-free headline lives in
`ParallelGaussianPerCoord.parallel_gaussian_capacity_formula`. -/

end InformationTheory.Shannon.ParallelGaussian
