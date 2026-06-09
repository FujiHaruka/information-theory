import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.Main
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.DifferentialEntropy
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


/-- For an **inactive** coordinate (`N_i ≥ ν`), the water-filling allocation
gives zero power. -/
lemma waterFillingPower_eq_zero_of_inactive {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) (h : ν ≤ (N i : ℝ)) :
    waterFillingPower ν N i = 0 := by
  unfold waterFillingPower
  exact max_eq_left (by linarith)


/-! ## D.3 — Parallel Gaussian capacity definition

Cost-constrained `sSup` of `mutualInfoOfChannel p (parallelGaussianChannel N)`
over input laws `p : Measure (Fin n → ℝ)` satisfying the per-coordinate total
second-moment constraint `∑_i ∫ x_i² ∂p ≤ P`. T2-A `awgnCapacity` の `Fin n`
拡張版。 -/

/-- **Parallel power constraint set**: probability measures with a (genuine,
lintegral) total per-coordinate second moment `≤ P`. Multivariate analogue of the
single-coordinate `AWGN.awgnPowerConstraintSet`. Using the lower integral
`∑_i ∫⁻ x, ofReal ((x i)²) ∂p ≤ ofReal P` instead of the Bochner
`∑_i ∫ x, (x i)² ∂p ≤ P` matters: Bochner `∫` returns `0` on a non-`p`-integrable
integrand (`MeasureTheory.integral_undef`), so the naive Bochner constraint would
admit heavy-tailed inputs (e.g. wide Cauchy laws) with infinite second moment via
the spurious `∫ (x i)² ∂p = 0 ≤ P`, making the converse bound
`∑_i (1/2)log(1+P_i/N_i)` false. The lintegral form forces each
`∫⁻ ofReal((x i)²) < ∞`, hence genuine integrability of every coordinate `(x i)²`.
`parallelGaussianPowerConstraintSet_mem_iff_integrable` bridges back to the Bochner
moment + the integrability regularity used by the capacity proofs.
@audit:ok -/
def parallelGaussianPowerConstraintSet {n : ℕ} (P : ℝ) : Set (Measure (Fin n → ℝ)) :=
  { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
      ∑ i : Fin n, ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p ≤ ENNReal.ofReal P }

/-- Membership in `parallelGaussianPowerConstraintSet P` (lintegral form) yields both
the genuine per-coordinate integrability of `(x i)²` and the Bochner total
second-moment bound `∑_i ∫ (x i)² ∂p ≤ P`. Multivariate analogue of
`AWGN.awgnPowerConstraintSet_mem_iff_integrable`; the lintegral constraint carries the
regularity (`Integrable (fun x => (x i)²) p`) the Bochner form alone cannot supply.
@audit:ok -/
theorem parallelGaussianPowerConstraintSet_mem_iff_integrable {n : ℕ}
    (P : ℝ) (hP : 0 ≤ P) (p : Measure (Fin n → ℝ))
    (hp : p ∈ parallelGaussianPowerConstraintSet P) :
    (∀ i, Integrable (fun x : Fin n → ℝ => (x i) ^ 2) p) ∧
      ∑ i : Fin n, ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p ≤ P := by
  obtain ⟨hp_prob, hp_lint⟩ := hp
  -- each coordinate's lintegral is ≤ the sum ≤ ofReal P < ∞, hence integrable
  have h_each_nonneg : ∀ i : Fin n, 0 ≤ᵐ[p] fun x : Fin n → ℝ => (x i) ^ 2 :=
    fun i => Filter.Eventually.of_forall (fun x => sq_nonneg (x i))
  have h_each_lt_top : ∀ i : Fin n,
      (∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p) < ∞ := by
    intro i
    have h_single_le :
        (∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p)
          ≤ ∑ j : Fin n, ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x j) ^ 2) ∂p :=
      Finset.single_le_sum (f := fun j => ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x j) ^ 2) ∂p)
        (fun j _ => bot_le) (Finset.mem_univ i)
    exact lt_of_le_of_lt (h_single_le.trans hp_lint) ENNReal.ofReal_lt_top
  have h_int : ∀ i, Integrable (fun x : Fin n → ℝ => (x i) ^ 2) p := by
    intro i
    have h_meas : AEStronglyMeasurable (fun x : Fin n → ℝ => (x i) ^ 2) p :=
      ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
    have h_hfi : HasFiniteIntegral (fun x : Fin n → ℝ => (x i) ^ 2) p :=
      (hasFiniteIntegral_iff_ofReal (h_each_nonneg i)).mpr (h_each_lt_top i)
    exact ⟨h_meas, h_hfi⟩
  refine ⟨h_int, ?_⟩
  -- Bochner sum bound: ofReal (∑ ∫ (x i)²) = ∑ ∫⁻ ofReal((x i)²) ≤ ofReal P, strip.
  have h_ofReal_each : ∀ i : Fin n,
      ENNReal.ofReal (∫ x : Fin n → ℝ, (x i) ^ 2 ∂p)
        = ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p :=
    fun i => ofReal_integral_eq_lintegral_ofReal (h_int i) (h_each_nonneg i)
  have h_int_nonneg : ∀ i : Fin n, 0 ≤ ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p :=
    fun i => integral_nonneg (fun x => sq_nonneg (x i))
  have h_sum_ofReal :
      ENNReal.ofReal (∑ i : Fin n, ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p)
        = ∑ i : Fin n, ∫⁻ x : Fin n → ℝ, ENNReal.ofReal ((x i) ^ 2) ∂p := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => h_int_nonneg i)]
    exact Finset.sum_congr rfl (fun i _ => h_ofReal_each i)
  have h_le : ENNReal.ofReal (∑ i : Fin n, ∫ x : Fin n → ℝ, (x i) ^ 2 ∂p) ≤ ENNReal.ofReal P :=
    h_sum_ofReal ▸ hp_lint
  exact (ENNReal.ofReal_le_ofReal_iff hP).mp h_le

/-- **Power-constrained parallel Gaussian capacity**. Supremum of `I(p; W_parallel)`
over probability measures `p` on `Fin n → ℝ` with total per-coordinate second
moment `∑_i ∫ x_i² ∂p ≤ P` (genuine lintegral form, see
`parallelGaussianPowerConstraintSet`). -/
noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) : ℝ :=
  sSup ((fun p : Measure (Fin n → ℝ) =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal) ''
        parallelGaussianPowerConstraintSet P)

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
    (InformationTheory `MIChainRule` per-coord specialization),
(b) per-coordinate F-2 MI bridge + max-entropy + bddAbove (T2-A
    `awgnCapacity_eq` applied per coordinate),
(c) variance partition feasibility (`∑_i ∫ x_i² ∂p ≤ P` ⇒ allocation exists with
    `∑ Var_i = P_i^*` and `∑ P_i^* ≤ P`).

⚠️ OPEN — conclusion-as-hypothesis: this predicate is *literally* the capacity
formula being claimed (`parallelGaussianCapacity … = ∑ …`). Returning it as a
theorem with `:= h_per_coord` would be a no-op pass-through, NOT a discharge of
the per-coordinate water-filling reduction (L-PG1); historical wrappers of that
shape (`parallel_gaussian_capacity_formula_of_perCoordReduction` and its
PG0-closed / active-form siblings) have been **retracted** — see commit history.
Callers now consume the predicate directly via def-unfolding (the def reduces to
the equality so the predicate inhabits the eq goal). The genuine, non-circular
discharge is `ParallelGaussianPerCoord.isParallelGaussianPerCoordReduction_discharged`,
which *produces* this predicate via a sup-sandwich from the honest regularity
bundle `IsParallelGaussianPerCoordRegularity` (≠ the conclusion). -/
def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (ν : ℝ) : Prop :=
  parallelGaussianCapacity P N h_meas h_parallel_meas
    = ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-! ## Reduction lemma (retracted)

`parallel_gaussian_capacity_formula_of_perCoordReduction` (body `:= h_per_coord`)
was a no-op pass-through wrapper around `IsParallelGaussianPerCoordReduction`
(`h_per_coord : IsParallelGaussianPerCoordReduction …` def-unfolds to the goal
equality). The wrapper added no derivation — it only exposed L-WF1 / L-WF2 in the
signature as decorative load (`hP`, `hN`, `h_kkt`, `h_unique` were never consumed
by the body) — and was retracted alongside its PG0-closed and active-form
siblings. Callers consume `IsParallelGaussianPerCoordReduction` directly via
def-unfolding (see `InformationTheory/Shannon/ParallelGaussianKKT.lean` etc.). The
genuine, hypothesis-free headline lives in
`ParallelGaussianPerCoord.parallel_gaussian_capacity_formula`. -/

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


/-! ## Active-set reduction lemma (retracted)

`parallel_gaussian_capacity_active_form_of_perCoordReduction` was the active-set
counterpart of `parallel_gaussian_capacity_formula_of_perCoordReduction` and
chained the same conclusion-as-hypothesis pattern via the un-active-form
predicate. It is retracted alongside the un-active-form wrapper. The active-set
form is still reachable via
`ParallelGaussianKKT.parallel_gaussian_capacity_active_form_KKT_discharged`,
which derives the active-set sum honestly via `parallel_gaussian_capacity_sum_active`
after consuming the chain rule bundle. -/

end InformationTheory.Shannon.ParallelGaussian
