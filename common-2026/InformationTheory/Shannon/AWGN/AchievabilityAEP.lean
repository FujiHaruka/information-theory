import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# AWGN achievability — continuous AEP engine (Chebyshev concentration)

False-wall overturn for the `awgn-continuous-aep-gaussian` wall slug.  The
continuous AEP mass-concentration sub-bound (i) does **not** require a.s.
convergence (the infinite product measure SLLN that the inventory assumed); a
finite-`n` Chebyshev weak law on the *finite* product measure
`Measure.pi (fun _ : Fin n => μ)` is enough.  Both lemmas below are genuine
(0 sorry, sorryAx-free).

Both lemmas are stated abstractly (general probability measure `μ` + an L²
statistic `φ`), so they can be reused for the AWGN joint law + log-density by
substituting the concrete `φ`.

## Mathlib assets used

* `ProbabilityTheory.variance_sum_pi` — `Var[∑ i, fun ω ↦ X i (ω i); pi μ]
  = ∑ i, Var[X i; μ i]`.
* `ProbabilityTheory.meas_ge_le_variance_div_sq` — Chebyshev.
* `MeasureTheory.measurePreserving_eval` — each coordinate `eval i` is measure
  preserving on `pi μ`, used via `MeasureTheory.integral_map` for `ν[φ∘eval i]
  = μ[φ]` and `MemLp.comp_measurePreserving` for `MemLp (φ∘eval i) 2 ν`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace InformationTheory.Shannon.AWGN

/-- On the product measure `Measure.pi (fun _ : Fin n => μ)`, the empirical mean
`(∑ᵢ φ(xᵢ))/n` of a common L² statistic `φ` deviates from `μ[φ]` by at least
`ε` on a set of mass at most `Var[φ]/(n ε²)`.  Finite-`n` Chebyshev
concentration — no infinite product measure / SLLN.  This is the engine for the
continuous-AEP mass sub-bound (i). -/
theorem pi_empirical_mean_concentration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {φ : α → ℝ} (hφ : MemLp φ 2 μ) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => μ))
        {x : Fin n → α | ε ≤ |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|}
      ≤ ENNReal.ofReal (variance φ μ / ((n : ℝ) * ε ^ 2)) := by
  classical
  set ν : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ) with hν
  -- The empirical sum as a sum of coordinate evaluations.
  set S : (Fin n → α) → ℝ := fun x => ∑ i, φ (x i) with hS
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- Each coordinate evaluation is `φ ∘ eval i`, MemLp 2 under ν.
  have hmemcoord : ∀ i : Fin n, MemLp (fun x : Fin n → α => φ (x i)) 2 ν := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) ν (μ) :=
      measurePreserving_eval (fun _ : Fin n => μ) i
    exact hφ.comp_measurePreserving hmp
  -- `MemLp S 2 ν` as a finite sum of the coordinate functions.
  have hSmem : MemLp S 2 ν := by
    have := memLp_finsetSum (μ := ν) (p := (2 : ℝ≥0∞)) Finset.univ
      (f := fun (i : Fin n) (x : Fin n → α) => φ (x i)) (fun i _ => hmemcoord i)
    simpa [hS] using this
  -- Variance of S = n * variance φ μ.
  have hVarS : variance S ν = (n : ℝ) * variance φ μ := by
    have hpi := variance_sum_pi (ι := Fin n) (Ω := fun _ : Fin n => α)
      (μ := fun _ : Fin n => μ) (X := fun _ : Fin n => φ) (fun i => hφ)
    -- `hpi : Var[∑ i, fun ω ↦ φ (ω i); ν] = ∑ i, Var[φ; μ]`
    rw [hS]
    rw [show (fun x : Fin n → α => ∑ i, φ (x i))
        = (∑ i, fun ω : Fin n → α => φ (ω i)) by
      funext x; simp [Finset.sum_apply]]
    rw [hpi]
    simp [Finset.sum_const, Finset.card_univ]
  -- Mean of S = n * μ[φ].
  have hmeanS : ν[S] = (n : ℝ) * μ[φ] := by
    have hint : ∀ i : Fin n, ν[fun x : Fin n → α => φ (x i)] = μ[φ] := by
      intro i
      have hmp : MeasurePreserving (Function.eval i) ν (μ) :=
        measurePreserving_eval (fun _ : Fin n => μ) i
      calc ν[fun x : Fin n → α => φ (x i)]
          = ∫ x, φ (Function.eval i x) ∂ν := rfl
        _ = ∫ y, φ y ∂(Measure.map (Function.eval i) ν) := by
              rw [integral_map (hmp.measurable.aemeasurable)]
              exact hφ.aestronglyMeasurable.aemeasurable.aestronglyMeasurable.mono_ac
                (by rw [hmp.map_eq])
        _ = ∫ y, φ y ∂μ := by rw [hmp.map_eq]
    rw [hS]
    rw [integral_finsetSum]
    · simp_rw [hint]
      simp [Finset.sum_const, Finset.card_univ]
    · intro i _
      exact (hmemcoord i).integrable (by norm_num)
  -- The pointwise absolute-value identity linking the empirical-mean deviation
  -- and the centred-sum deviation.
  have habs : ∀ x : Fin n → α,
      |S x - ν[S]| = (n : ℝ) * |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]| := by
    intro x
    rw [hmeanS]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    rw [show (n : ℝ) * |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|
          = |(n : ℝ) * ((∑ i, φ (x i)) / (n : ℝ) - μ[φ])| by
        rw [abs_mul, abs_of_pos hnR]]
    congr 1
    simp only [hS]
    field_simp
  -- Rewrite the target deviation set in terms of `S - ν[S]`.
  have hset : {x : Fin n → α | ε ≤ |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|}
      = {x : Fin n → α | (n : ℝ) * ε ≤ |S x - ν[S]|} := by
    ext x
    simp only [Set.mem_setOf_eq, habs x]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h hnR.le
    · intro h; exact le_of_mul_le_mul_left h hnR
  rw [hset]
  -- Apply Chebyshev with X = S, c = n * ε.
  have hcheb := meas_ge_le_variance_div_sq (μ := ν) hSmem
    (c := (n : ℝ) * ε) (by positivity)
  refine hcheb.trans ?_
  -- Simplify the bound: variance S ν / (n*ε)^2 = (n * variance φ μ)/(n² ε²) = variance φ μ/(n ε²).
  apply ENNReal.ofReal_le_ofReal
  rw [hVarS, mul_pow]
  -- The two sides are equal (n>0 cancellation).
  have heq : (n : ℝ) * variance φ μ / ((n : ℝ) ^ 2 * ε ^ 2)
      = variance φ μ / ((n : ℝ) * ε ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hε0 : ε ^ 2 ≠ 0 := by positivity
    field_simp
  rw [heq]

/-- From the concentration bound: for any tolerance `η > 0` there is a threshold
`N₀` such that for `n ≥ N₀` the empirical mean lands within `ε` of `μ[φ]` on a
set of mass `≥ 1 - η`.  The existence form the AEP ultimately consumes. -/
theorem pi_empirical_mean_typical_mass
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {φ : α → ℝ} (hφ : MemLp φ 2 μ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      ENNReal.ofReal (1 - η) ≤
        (Measure.pi (fun _ : Fin n => μ))
          {x : Fin n → α | |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]| < ε} := by
  classical
  -- Choose `N₀` so that `Var[φ]/(N₀ ε²) ≤ η`, i.e. `N₀ ≥ Var[φ]/(η ε²)`.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (variance φ μ / (η * ε ^ 2))
  refine ⟨N₀ + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N₀) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set ν : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => μ) with hν
  -- The "atypical" deviation set and the typical set are complementary.
  set A : Set (Fin n → α) :=
    {x : Fin n → α | ε ≤ |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|} with hA
  set B : Set (Fin n → α) :=
    {x : Fin n → α | |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]| < ε} with hB
  have hBA : B = Aᶜ := by
    rw [hA, hB]; ext x; simp [not_le]
  -- `A` is null-measurable (its defining function is `AEStronglyMeasurable` under ν).
  have hmemcoord : ∀ i : Fin n, MemLp (fun x : Fin n → α => φ (x i)) 2 ν := by
    intro i
    exact hφ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)
  have hSmem : MemLp (fun x : Fin n → α => ∑ i, φ (x i)) 2 ν := by
    have := memLp_finsetSum (μ := ν) (p := (2 : ℝ≥0∞)) Finset.univ
      (f := fun (i : Fin n) (x : Fin n → α) => φ (x i))
      (fun i _ => hmemcoord i)
    simpa using this
  have hS0 : AEMeasurable (fun x : Fin n → α => ∑ i, φ (x i)) ν :=
    (MemLp.aestronglyMeasurable hSmem).aemeasurable
  have hAnull : NullMeasurableSet A ν := by
    -- `A` is the preimage of the measurable target set `{r : ℝ | ε ≤ |r|}`
    -- under the AEMeasurable map `y := (∑ φ(xᵢ))/n - μ[φ]`.
    have hy : AEMeasurable
        (fun x : Fin n → α => (∑ i, φ (x i)) / (n : ℝ) - μ[φ]) ν :=
      (hS0.div_const _).sub_const _
    have hT : MeasurableSet {r : ℝ | ε ≤ |r|} :=
      measurableSet_le measurable_const measurable_norm
    have : NullMeasurableSet
        ((fun x : Fin n → α => (∑ i, φ (x i)) / (n : ℝ) - μ[φ]) ⁻¹' {r : ℝ | ε ≤ |r|}) ν :=
      hy.nullMeasurableSet_preimage hT
    simpa [hA, Set.preimage, Set.mem_setOf_eq] using this
  -- Mass of the typical set via complement.
  have hcompl : ν B = 1 - ν A := by rw [hBA, prob_compl_eq_one_sub₀ hAnull]
  -- Atypical mass bound from theorem 1.
  have hAbound : ν A ≤ ENNReal.ofReal (variance φ μ / ((n : ℝ) * ε ^ 2)) :=
    pi_empirical_mean_concentration μ hφ hε hn0
  -- `Var[φ]/(n ε²) ≤ η`.
  have hηε : (0 : ℝ) < η * ε ^ 2 := by positivity
  have hVarnn : (0 : ℝ) ≤ variance φ μ := variance_nonneg φ μ
  have hNn : variance φ μ / (η * ε ^ 2) < (n : ℝ) := by
    calc variance φ μ / (η * ε ^ 2) < (N₀ : ℝ) := hN₀
      _ ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_succ N₀) hn
  have hbound_le_η : variance φ μ / ((n : ℝ) * ε ^ 2) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hηε] at hNn
    nlinarith [hNn]
  -- Combine: ν B = 1 - ν A ≥ 1 - ofReal η ≥ ofReal (1 - η).
  rw [hcompl]
  have hAη : ν A ≤ ENNReal.ofReal η :=
    hAbound.trans (ENNReal.ofReal_le_ofReal hbound_le_η)
  calc ENNReal.ofReal (1 - η)
      ≤ 1 - ENNReal.ofReal η := by
        rw [ENNReal.ofReal_sub _ hη.le, ENNReal.ofReal_one]
    _ ≤ 1 - ν A := by
        apply tsub_le_tsub_left hAη

end InformationTheory.Shannon.AWGN
