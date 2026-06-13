import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.Main
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Parallel Gaussian channels and water-filling

The capacity of `n` parallel AWGN channels `Y_i = X_i + Z_i`, `Z_i ∼ 𝒩(0, N_i)`
(`i : Fin n`) under the total power constraint `∑_i E[X_i²] ≤ P`, and its water-filling
solution (Cover–Thomas, Theorem 9.4.1).

## Main definitions

* `parallelGaussianChannel N` — the product Markov kernel on `Fin n → ℝ` whose `i`-th
  output coordinate is `X_i + Z_i` with `Z_i ∼ 𝒩(0, N_i)`, independent across coordinates.
* `waterFillingPower ν N` — the water-filling power allocation `i ↦ max(0, ν - N_i)` for
  water level `ν`.
* `parallelGaussianCapacity P N` — the power-constrained information capacity, the `sSup`
  of the mutual information over inputs in `parallelGaussianPowerConstraintSet P`.
* `parallelGaussianPowerConstraintSet P` — the probability measures with total
  per-coordinate second moment `≤ P`, in lower-integral form.
* `waterFillingActiveSet ν N` — the coordinates `{i | N_i < ν}` allocated positive power.

## Main statements

* `parallelGaussianPowerConstraintSet_mem_iff_integrable` — membership yields genuine
  per-coordinate integrability of `(x i)²` together with the Bochner second-moment bound.

## Implementation notes

* `parallelGaussianChannel` is defined directly as `toFun x := Measure.pi (fun i =>
  gaussianReal (x i) (N i))`, matching the conclusion form of `Measure.pi_pi`; its
  measurability is supplied as the hypothesis `IsParallelGaussianKernelMeasurable N`.
* `waterFillingPower` uses `max 0 (ν - N_i)`, matching `max_eq_left` / `max_eq_right` /
  `le_max_left`.
* The power constraint uses the lower integral `∑_i ∫⁻ ofReal ((x i)²) ∂p ≤ ofReal P`
  rather than the Bochner `∑_i ∫ (x i)² ∂p ≤ P`. Bochner `∫` returns `0` on a
  non-integrable integrand, so the naive Bochner constraint would admit heavy-tailed
  inputs with infinite second moment; the lower integral forces genuine integrability of
  every `(x i)²`.
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Parallel Gaussian channel kernel -/

/-- Per-coordinate AWGN measurability hypothesis, bundled over `Fin n`. -/
def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  ∀ i, InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable (N i)

/-- Measurability of the parallel kernel map `x : Fin n → ℝ ↦ Measure.pi (fun i =>
gaussianReal (x i) (N i))`, supplied as a hypothesis. -/
def IsParallelGaussianKernelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  Measurable (fun x : Fin n → ℝ => Measure.pi (fun i => gaussianReal (x i) (N i)))

/-- The **parallel Gaussian channel kernel**: on input `x : Fin n → ℝ` the output
`y : Fin n → ℝ` has `y i = x i + z i` with `z i ∼ 𝒩(0, N i)` independent across
coordinates. The output law is the product measure `Measure.pi (fun i =>
gaussianReal (x i) (N i))`. -/
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

/-! ## Water-filling power allocation -/

/-- The **water-filling power allocation**: for water level `ν : ℝ` and noise vector
`N : Fin n → ℝ≥0`, coordinate `i` is allocated `max(0, ν - N_i)` (Cover–Thomas,
Theorem 9.4.1). -/
noncomputable def waterFillingPower {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    Fin n → ℝ :=
  fun i => max 0 (ν - (N i : ℝ))

@[simp] lemma waterFillingPower_apply {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    waterFillingPower ν N i = max 0 (ν - (N i : ℝ)) := rfl

lemma waterFillingPower_nonneg {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    0 ≤ waterFillingPower ν N i := le_max_left _ _


/-- An inactive coordinate (`ν ≤ N_i`) is allocated zero power. -/
lemma waterFillingPower_eq_zero_of_inactive {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) (h : ν ≤ (N i : ℝ)) :
    waterFillingPower ν N i = 0 := by
  unfold waterFillingPower
  exact max_eq_left (by linarith)


/-! ## Parallel Gaussian capacity -/

/-- The **parallel power constraint set**: probability measures with total
per-coordinate second moment `≤ P`, in lower-integral form `∑_i ∫⁻ ofReal ((x i)²) ∂p
≤ ofReal P`. Multivariate analogue of `AWGN.awgnPowerConstraintSet`. The lower-integral
form forces each `∫⁻ ofReal ((x i)²) < ∞`, hence genuine integrability of every
coordinate `(x i)²` (a Bochner `∫` constraint would spuriously admit heavy-tailed
inputs with infinite second moment).

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

/-- The **power-constrained parallel Gaussian capacity**: the supremum of the mutual
information `I(p; parallelGaussianChannel N)` over inputs `p` in
`parallelGaussianPowerConstraintSet P`. -/
noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) : ℝ :=
  sSup ((fun p : Measure (Fin n → ℝ) =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (parallelGaussianChannel N h_meas h_parallel_meas)).toReal) ''
        parallelGaussianPowerConstraintSet P)

/-! ## Water-filling KKT, optimality, and per-coordinate reduction predicates -/

/-- The **water-filling KKT condition**: the water level `ν` uses up the total budget,
`∑_i max(0, ν - N_i) = P`. For the unconstrained water-filling problem this characterizes
the KKT-optimal Lagrange multiplier (a unique such `ν` exists by the intermediate value
theorem). -/
def IsWaterFillingKKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∑ i : Fin n, waterFillingPower ν N i = P

/-- **Water-filling optimality**: the water-filling allocation `P_i^* = max(0, ν - N_i)`
maximizes the per-coordinate sum `∑ (1/2) log(1 + P_i/N_i)` subject to `P_i ≥ 0`,
`∑ P_i ≤ P`. -/
def IsWaterFillingOptimal {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i : Fin n, P' i ≤ P) →
    ∑ i : Fin n, (1/2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- The **per-coordinate water-filling reduction**: the parallel Gaussian capacity equals
the per-coordinate water-filling sum `∑_i (1/2) log(1 + max(0, ν - N_i) / N_i)`.

This predicate is the capacity equality itself, so it is intended to be *derived* (not
taken as a hypothesis). The genuine, non-circular producer is
`ParallelGaussianPerCoord.isParallelGaussianPerCoordReduction_discharged`, a sup-sandwich
from the regularity bundle `IsParallelGaussianPerCoordRegularity`. -/
def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N)
    (h_parallel_meas : IsParallelGaussianKernelMeasurable N) (ν : ℝ) : Prop :=
  parallelGaussianCapacity P N h_meas h_parallel_meas
    = ∑ i : Fin n, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-! ## Active set -/

/-- The **active set** of coordinates (those with `N_i < ν`), allocated positive
water-filling power. -/
noncomputable def waterFillingActiveSet {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => (N i : ℝ) < ν)

@[simp] lemma mem_waterFillingActiveSet {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0)
    (i : Fin n) :
    i ∈ waterFillingActiveSet ν N ↔ (N i : ℝ) < ν := by
  unfold waterFillingActiveSet
  simp

end InformationTheory.Shannon.ParallelGaussian
