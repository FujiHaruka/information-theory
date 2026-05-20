import Common2026.Shannon.AWGN
import Common2026.Shannon.AWGNMain
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.DifferentialEntropy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# T2-B: Parallel Gaussian Channels + Water-filling (Cover-Thomas Ch.9.4)

並列 AWGN channels `Y_i = X_i + Z_i`, `Z_i ∼ 𝒩(0, N_i)` (`i : Fin n`) の
総電力制約 `∑_i E[X_i²] ≤ P` 下での容量 + water-filling 解。

## Roadmap (per `docs/shannon/parallel-gaussian-moonshot-plan.md`)

* Phase A — `parallelGaussianChannel` kernel + `waterFillingPower` 定義 + 基本性質
* Phase B — `parallelGaussianCapacity` 定義 + 撤退ライン predicate (L-WF1/L-WF2/L-PG1)
* Phase C — 主定理 `parallel_gaussian_capacity_formula` (L-PG1 適用形)
* Phase D — Corollary (active coord 数, ν-monotonicity, KKT well-defined)

## 撤退ライン (本 file で発動)

* **L-PG0 (parallel kernel measurability)**: `Measurable (fun x : Fin n → ℝ =>
  Measure.pi (fun i => gaussianReal (x i) (N i)))` は Mathlib 不在
  (`Measure.pi` の m-measurability は `measurable_pi_iff` 系で組めるが各 marginal の
  m-measurability を要する)。本 plan では `parallelGaussianChannel` の構築引数として
  `h_meas : IsParallelAwgnChannelMeasurable N` (per-coord T2-A F-4 hypothesis の
  bundle) を渡し、parallel kernel 自身の measurability は補助 hypothesis
  `h_parallel_meas` として `parallelGaussianChannel` 構築時に外出し。
* **L-WF1 (KKT 充足)**: 水位 `ν` が全電力を使い切る (`∑ waterFilling = P`) を
  `IsWaterFillingKKT` predicate に外出し。
* **L-WF2 (水位 一意性 + 最適性)**: water-filling 配分が
  `∑ (1/2) log(1+P_i/N_i)` の最大化解である事実を `IsWaterFillingOptimal`
  predicate に外出し。
* **L-PG1 (per-coordinate AWGN F-* hypothesis bundle)**: parallel capacity =
  per-coord water-filling sum 等号を `IsParallelGaussianPerCoordReduction`
  predicate に外出し。**主定理本体はこの 1 本で `:= h_per_coord` で終わる**。

L-* 撤退ラインの discharge は別 plan (`parallel-gaussian-kkt-plan.md` +
`parallel-gaussian-chain-rule-plan.md`) に defer。

## Mathlib-shape-driven Definitions

* `parallelGaussianChannel N h_meas h_parallel_meas : Channel (Fin n → ℝ) (Fin n → ℝ)`
  は `toFun x := Measure.pi (fun i => gaussianReal (x i) (N i))` で直接定義
  (`Measure.pi_pi` の結論形に直結)。`measurable'` は補助 hypothesis
  `h_parallel_meas` から直接取る (L-PG0 撤退)。
* `waterFillingPower ν N : Fin n → ℝ` は `fun i => max 0 (ν - (N i : ℝ))` で
  Mathlib `max_eq_left` / `max_eq_right` / `le_max_left` の結論形に直結。
* `parallelGaussianCapacity P N h_meas h_parallel_meas : ℝ` は T2-A `awgnCapacity`
  と同じく `sSup` 直書き。
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## D.1 — parallel Gaussian channel kernel

撤退ライン L-PG0 採用: parallel kernel の m-measurability を補助 hypothesis
として外出し。Mathlib `Measure.pi` の m-measurability lemma の整備状況に依らず
本 plan を publish 可能にする。
-/

/-- **AWGN-per-coordinate measurability hypothesis bundled over `Fin n`.**

T2-A の `IsAwgnChannelMeasurable` (`AWGN.lean:63`) を `Fin n` indexed に bundle。
Discharge は T2-A F-4 と同パターン (`awgn-kernel-measurability-plan.md`) の
per-coord 拡張、別 plan に defer。 -/
def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  ∀ i, InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable (N i)

/-- **Parallel kernel measurability hypothesis (L-PG0)**: the map
`x : Fin n → ℝ ↦ Measure.pi (fun i => gaussianReal (x i) (N i))` is measurable.

Discharging this requires lifting per-coord `IsAwgnChannelMeasurable (N i)`
through `Measure.pi`; Mathlib API for this is in
`measurable_pi_iff` form but the `Measure.pi` direction needs custom plumbing
(~50-100 行)。本 plan では別 plan (`parallel-gaussian-kernel-measurability-plan.md`)
に defer。 -/
def IsParallelGaussianKernelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  Measurable (fun x : Fin n → ℝ => Measure.pi (fun i => gaussianReal (x i) (N i)))

/-- **Parallel Gaussian channel kernel**: on input `x : Fin n → ℝ`, output
`y : Fin n → ℝ` with `y i = x i + z i` where `z i ∼ 𝒩(0, N i)` independent
across coordinates. The kernel returns the output law directly as the product
measure `Measure.pi (fun i => gaussianReal (x i) (N i))`.

撤退ライン L-PG0 hypothesis pass-through: `h_parallel_meas` is required to
construct the kernel. -/
noncomputable def parallelGaussianChannel {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    InformationTheory.Shannon.ChannelCoding.Channel (Fin n → ℝ) (Fin n → ℝ) where
  toFun x := Measure.pi (fun i => gaussianReal (x i) (N i))
  measurable' := h_parallel_meas

@[simp] lemma parallelGaussianChannel_apply {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (x : Fin n → ℝ) :
    (parallelGaussianChannel N h_meas h_parallel_meas) x
      = Measure.pi (fun i => gaussianReal (x i) (N i)) := rfl

/-- `parallelGaussianChannel N` is a Markov kernel (each fibre is a product of
probability measures, hence itself a probability measure). -/
instance parallelGaussianChannel.instIsMarkovKernel {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) :
    IsMarkovKernel (parallelGaussianChannel N h_meas h_parallel_meas) where
  isProbabilityMeasure x := by
    show IsProbabilityMeasure (Measure.pi (fun i => gaussianReal (x i) (N i)))
    infer_instance

/-! ## D.2 — Water-filling power allocation

Water-filling solution to the parallel Gaussian capacity optimization
(Cover-Thomas Ch.9.4 Theorem 9.4.1): for water level `ν`, allocate
`P_i^* = max(0, ν - N_i)` to coordinate `i`. -/

/-- **Water-filling power allocation**: for water level `ν : ℝ` and noise
vector `N : Fin n → ℝ≥0`, the power allocated to coordinate `i` is
`max(0, ν - N_i)`.

Cover-Thomas Ch.9.4 Theorem 9.4.1. -/
noncomputable def waterFillingPower {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    Fin n → ℝ :=
  fun i => max 0 (ν - (N i : ℝ))

@[simp] lemma waterFillingPower_apply {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    waterFillingPower ν N i = max 0 (ν - (N i : ℝ)) := rfl

lemma waterFillingPower_nonneg {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    0 ≤ waterFillingPower ν N i := le_max_left _ _

lemma waterFillingPower_sum_nonneg {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    0 ≤ ∑ i, waterFillingPower ν N i :=
  Finset.sum_nonneg (fun i _ => waterFillingPower_nonneg ν N i)

/-- For an **inactive** coordinate (`N_i ≥ ν`), the water-filling allocation
gives zero power. -/
lemma waterFillingPower_eq_zero_of_inactive {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) (h : ν ≤ (N i : ℝ)) :
    waterFillingPower ν N i = 0 := by
  unfold waterFillingPower
  exact max_eq_left (by linarith)

/-- For an **active** coordinate (`N_i < ν`), the water-filling allocation
equals `ν - N_i`. -/
lemma waterFillingPower_eq_diff_of_active {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) (h : (N i : ℝ) < ν) :
    waterFillingPower ν N i = ν - (N i : ℝ) := by
  unfold waterFillingPower
  exact max_eq_right (by linarith)

/-- Water-filling allocation is monotone in the water level `ν`. -/
lemma waterFillingPower_mono_in_ν {n : ℕ} (N : Fin n → ℝ≥0) (i : Fin n)
    {ν₁ ν₂ : ℝ} (h : ν₁ ≤ ν₂) :
    waterFillingPower ν₁ N i ≤ waterFillingPower ν₂ N i := by
  unfold waterFillingPower
  exact max_le_max le_rfl (by linarith)

/-! ## D.3 — Parallel Gaussian capacity definition

Cost-constrained `sSup` of `mutualInfoOfChannel p (parallelGaussianChannel N)`
over input laws `p : Measure (Fin n → ℝ)` satisfying the per-coordinate total
second-moment constraint `∑_i ∫ x_i² ∂p ≤ P`. T2-A `awgnCapacity` の `Fin n`
拡張版。 -/

/-- **Power-constrained parallel Gaussian capacity**. Supremum of `I(p; W_parallel)`
over probability measures `p` on `Fin n → ℝ` with total per-coordinate second
moment `∑_i ∫ x_i² ∂p ≤ P`. -/
noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) : ℝ :=
  sSup ((fun p : Measure (Fin n → ℝ) =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal) ''
        { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
            ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i)^2 ∂p ≤ P })

/-! ## D.4 — 撤退ライン predicates (L-WF1, L-WF2, L-PG1)

T1-B Chernoff `L-S2` / T1-C Cramer `L-C2` / T2-F de Bruijn `L-F1+L-F2` /
T2-A AWGN F-1+F-2+F-3+F-4 と同型 hypothesis pass-through pattern。 -/

/-- **L-WF1 hypothesis** (water-filling KKT condition).

For the unconstrained water-filling problem
`max_{P_i ≥ 0, ∑P_i ≤ P} ∑ (1/2) log(1 + P_i/N_i)`,
`ν` is a KKT-optimal Lagrange multiplier iff the total water-filling power
exactly equals `P`. (For `ν ≤ min N_i`, the sum is `0`; for `ν → ∞`, the sum
diverges; by intermediate value theorem, a unique `ν*` achieves `= P`.)

Discharging this hypothesis (= existence + uniqueness of the KKT water level)
is deferred to `parallel-gaussian-kkt-plan.md`. -/
def IsWaterFillingKKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∑ i : Fin n, waterFillingPower ν N i = P

/-- **L-WF2 hypothesis** (water-filling optimality).

The water-filling allocation `P_i^* = max(0, ν - N_i)` achieves the supremum of
the per-coordinate sum `∑ (1/2) log(1 + P_i/N_i)` subject to
`P_i ≥ 0, ∑ P_i ≤ P`. (Follows from concavity of `log(1+x)` + Lagrange duality.)

Discharging this hypothesis is deferred to `parallel-gaussian-kkt-plan.md`. -/
def IsWaterFillingOptimal {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i : Fin n, P' i ≤ P) →
    ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- **L-PG1 hypothesis** (per-coordinate AWGN F-* bundle).

The parallel Gaussian capacity equals the per-coordinate sum
`∑_i (1/2) log(1 + waterFillingPower ν N i / N_i)` for the (water-filling
optimal) water level `ν`. Bundles in one predicate:

(a) chain rule `I(X^n; Y^n) = ∑_i I(X_i; Y_i)` for memoryless parallel channel
    (Common2026 `MIChainRule` per-coord specialization),
(b) per-coordinate F-2 MI bridge + max-entropy + bddAbove (T2-A
    `awgnCapacity_eq` applied per coordinate),
(c) variance partition feasibility (`∑_i ∫ x_i² ∂p ≤ P` ⇒ allocation exists with
    `∑ Var_i = P_i^*` and `∑ P_i^* ≤ P`).

⚠️ OPEN — conclusion-as-hypothesis: this predicate is *literally* the capacity
formula being claimed (`parallelGaussianCapacity … = ∑ …`). Assuming it and
returning it (as `parallel_gaussian_capacity_formula` does, `:= h_per_coord`) is
NOT a discharge of the per-coordinate water-filling reduction (L-PG1). The genuine
proof needs the memoryless chain rule + per-coord AWGN capacity machinery
(continuous AEP / sphere-shell volume), absent from Mathlib. Deferred to
`parallel-gaussian-chain-rule-plan.md`. -/
def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (ν : ℝ) : Prop :=
  parallelGaussianCapacity P N h_meas h_parallel_meas
    = ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-! ## Main theorem — `parallel_gaussian_capacity_formula`

T2-A awgn_capacity_closed_form の per-coordinate 拡張形。
L-WF1 + L-WF2 + L-PG1 三本立て採用 (Cover-Thomas Theorem 9.4.1 の textbook 完全形
を signature 露出)。本体は L-PG1 (`h_per_coord`) から `:= h_per_coord` で済む。 -/

/-- **Parallel Gaussian capacity formula** (Cover-Thomas Theorem 9.4.1).

For parallel AWGN channels `Y_i = X_i + Z_i`, `Z_i ∼ 𝒩(0, N_i)` (`i : Fin n`)
with total power constraint `∑_i E[X_i²] ≤ P`, the capacity is achieved by
water-filling at level `ν*` satisfying `∑_i max(0, ν* - N_i) = P`:

`C = ∑_i (1/2) log(1 + max(0, ν* - N_i) / N_i)`.

⚠️ NOT a discharge: this is a hypothesis pass-through (`:= h_per_coord`). The
per-coordinate water-filling reduction (L-PG1, `h_per_coord`) is the conclusion
itself, taken as a hypothesis and OPEN; L-WF1/L-WF2 are also taken as hypotheses
here. The genuine reduction needs water-filling KKT + per-coord AWGN capacity
(continuous AEP / sphere-shell volume) machinery absent from Mathlib. Genuine
discharges of the *individual* layers live in the `*_discharged` re-publishes
(L-PG0 kernel measurability, L-WF1 IVT existence, L-WF2 concavity certificate);
L-PG1 stays OPEN throughout.

撤退ライン L-WF1 + L-WF2 + L-PG1 全採用形 (hypothesis pass-through 3 本):
* `h_kkt` (L-WF1): water level `ν` が全電力 `P` を使い切る KKT 条件
* `h_unique` (L-WF2): water-filling が `∑ (1/2) log(1+P_i/N_i)` の最大化解
* `h_per_coord` (L-PG1): parallel capacity = per-coord water-filling sum

L-WF1 + L-WF2 は signature 露出のみで本体では使わない (将来 discharge plan で
L-WF1 + L-WF2 → L-PG1 を導出する想定)。本体は `h_per_coord` 単独で済む。

撤退ライン discharge plans:
* L-WF1 / L-WF2 → `parallel-gaussian-kkt-plan.md`
* L-PG1 → `parallel-gaussian-chain-rule-plan.md`
* L-PG0 (`h_parallel_meas`) → `parallel-gaussian-kernel-measurability-plan.md`
-/
theorem parallel_gaussian_capacity_formula {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_per_coord :
        IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) :=
  h_per_coord

/-! ## Corollaries (Phase D)

Active-set decomposition + per-coord active simplification + log-form
restatement of the main capacity formula. -/

/-- The set of **active** coordinates (those with `N_i < ν`), where the
water-filling allocates positive power. -/
noncomputable def waterFillingActiveSet {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => (N i : ℝ) < ν)

@[simp] lemma mem_waterFillingActiveSet {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) :
    i ∈ waterFillingActiveSet ν N ↔ (N i : ℝ) < ν := by
  unfold waterFillingActiveSet
  simp

/-- For an **inactive** coordinate (`N_i ≥ ν`), the per-coordinate capacity
contribution `(1/2) log(1 + waterFilling/N_i)` is zero (since `log 1 = 0`). -/
lemma waterFilling_log_eq_zero_of_inactive {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) (h : ν ≤ (N i : ℝ)) :
    (1/2 : ℝ) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) = 0 := by
  rw [waterFillingPower_eq_zero_of_inactive ν N i h]
  simp

/-- For an **active** coordinate (`N_i < ν`), the per-coordinate capacity
contribution simplifies to `(1/2) log(ν/N_i)`. -/
lemma waterFilling_log_eq_active {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) (hN_pos : 0 < (N i : ℝ)) (h : (N i : ℝ) < ν) :
    (1/2 : ℝ) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
      = (1/2) * Real.log (ν / (N i : ℝ)) := by
  rw [waterFillingPower_eq_diff_of_active ν N i h]
  congr 1
  have h_eq : (1 : ℝ) + (ν - (N i : ℝ)) / (N i : ℝ) = ν / (N i : ℝ) := by
    rw [eq_div_iff (ne_of_gt hN_pos)]
    field_simp; ring
  rw [h_eq]

/-- Water-filling sum decomposes as a sum over the active set
`∑ i, waterFilling = ∑ i ∈ active, (ν - N_i)`. -/
lemma waterFillingPower_sum_eq_active {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    ∑ i : Fin n, waterFillingPower ν N i
      = ∑ i ∈ waterFillingActiveSet ν N, (ν - (N i : ℝ)) := by
  -- Rewrite each summand using if-then-else based on active/inactive
  rw [show (∑ i : Fin n, waterFillingPower ν N i)
        = ∑ i : Fin n, if (N i : ℝ) < ν then (ν - (N i : ℝ)) else 0 from
        Finset.sum_congr rfl (fun i _ => by
          by_cases h : (N i : ℝ) < ν
          · rw [if_pos h, waterFillingPower_eq_diff_of_active ν N i h]
          · simp only [not_lt] at h
            rw [if_neg (not_lt.mpr h), waterFillingPower_eq_zero_of_inactive ν N i h])]
  -- Now rewrite the if-sum as a sum over the active set
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext i
    simp [waterFillingActiveSet]
  · intros; rfl

/-- The capacity formula restated as a sum only over the **active** coordinates:
`C = ∑_{i ∈ active} (1/2) log(ν/N_i)`. (Cover-Thomas Theorem 9.4.1 alternative
form.) -/
lemma parallel_gaussian_capacity_sum_active {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (hN_pos : ∀ i, 0 < (N i : ℝ)) :
    ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
      = ∑ i ∈ waterFillingActiveSet ν N,
          (1/2) * Real.log (ν / (N i : ℝ)) := by
  -- Rewrite each summand using if-then-else based on active/inactive
  rw [show (∑ i : Fin n, (1/2 : ℝ) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)))
        = ∑ i : Fin n, if (N i : ℝ) < ν
            then (1/2) * Real.log (ν / (N i : ℝ))
            else 0 from
        Finset.sum_congr rfl (fun i _ => by
          by_cases h : (N i : ℝ) < ν
          · rw [if_pos h, waterFilling_log_eq_active ν N i (hN_pos i) h]
          · simp only [not_lt] at h
            rw [if_neg (not_lt.mpr h),
                waterFilling_log_eq_zero_of_inactive ν N i h])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext i
    simp [waterFillingActiveSet]
  · intros; rfl

/-- **Active-set form of the parallel Gaussian capacity formula** (Cover-Thomas
Theorem 9.4.1 restated).

Combining `parallel_gaussian_capacity_formula` with
`parallel_gaussian_capacity_sum_active`. -/
theorem parallel_gaussian_capacity_active_form {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0)
    (hN : ∀ i, (N i : ℝ) ≠ 0) (hN_pos : ∀ i, 0 < (N i : ℝ))
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_per_coord :
        IsParallelGaussianPerCoordReduction P N h_meas h_parallel_meas ν) :
    parallelGaussianCapacity P N h_meas h_parallel_meas
      = ∑ i ∈ waterFillingActiveSet ν N,
          (1/2) * Real.log (ν / (N i : ℝ)) := by
  rw [parallel_gaussian_capacity_formula P hP N hN h_meas h_parallel_meas ν
        h_kkt h_unique h_per_coord]
  exact parallel_gaussian_capacity_sum_active ν N hN_pos

end InformationTheory.Shannon.ParallelGaussian
