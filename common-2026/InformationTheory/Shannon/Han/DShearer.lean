import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Han.D

/-!
# Han's inequality — Shearer's inequality (integer covering form)

If `S : ι → Finset (Fin n)` covers each `i : Fin n` at least `k` times, then
`k · H(X_{[n]}) ≤ ∑_j H(X_{S_j})`.

## Main statements

* `shearer_inequality` — the integer-covering Shearer inequality. The proof combines the
  subset chain rule `jointEntropySubset_chain_rule`, conditional-entropy monotonicity
  `condEntropy_subset_anti`, and `jointEntropySubset_univ`, then swaps the double sum to
  expose the covering multiplicity `cover i := #{j | i ∈ S j} ≥ k`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [DecidableEq α] in
/-- Shearer's inequality (integer covering form): if `S : ι → Finset (Fin n)` covers each
`i : Fin n` at least `k` times, then `k · H(X_{[n]}) ≤ ∑_j H(X_{S_j})`. -/
@[entry_point]
theorem shearer_inequality
    {ι : Type*} [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : ι → Finset (Fin n))
    {k : ℕ}
    (hk : ∀ i : Fin n,
      k ≤ (Finset.univ.filter (fun j : ι ↦ i ∈ S j)).card) :
    (k : ℝ) * jointEntropy μ Xs
      ≤ ∑ j : ι, jointEntropySubset μ Xs (S j) := by
  classical
  -- f i = H(X_i | X_{<i}) (conditioning over Finset.univ.filter (· < i))
  set f : Fin n → ℝ := fun i ↦
    InformationTheory.MeasureFano.condEntropy μ (Xs i)
      (fun ω (j : ↥(Finset.univ.filter (· < i))) ↦ Xs j.val ω) with hf_def
  -- Step A: ∀ T : Finset (Fin n), ∑ i ∈ T, f i ≤ jointEntropySubset μ Xs T
  have h_subset_lower : ∀ T : Finset (Fin n),
      ∑ i ∈ T, f i ≤ jointEntropySubset μ Xs T := by
    intro T
    rw [jointEntropySubset_chain_rule μ Xs hXs T]
    apply Finset.sum_le_sum
    intro i _
    exact condEntropy_subset_anti μ Xs hXs i
      (Finset.filter_subset_filter (· < i) (Finset.subset_univ T))
  -- Step B: jointEntropy μ Xs = ∑ i, f i (chain rule with S = univ)
  have h_joint_eq : jointEntropy μ Xs = ∑ i, f i := by
    rw [← jointEntropySubset_univ μ Xs hXs]
    rw [jointEntropySubset_chain_rule μ Xs hXs Finset.univ]
  -- Step C: f i ≥ 0 (condEntropy is nonneg)
  have hf_nonneg : ∀ i, 0 ≤ f i := by
    intro i
    show 0 ≤ InformationTheory.MeasureFano.condEntropy μ (Xs i)
        (fun ω (j : ↥(Finset.univ.filter (· < i))) ↦ Xs j.val ω)
    unfold InformationTheory.MeasureFano.condEntropy
    apply integral_nonneg
    intro y
    apply Finset.sum_nonneg
    intro x _
    exact Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one
  -- Step D: swap the double sum
  -- ∑ j : ι, ∑ i ∈ S j, f i = ∑ i, (cover i) * f i
  have h_double : ∑ j : ι, ∑ i ∈ S j, f i
      = ∑ i, ((Finset.univ.filter (fun j : ι ↦ i ∈ S j)).card : ℝ) * f i := by
    have h1 : ∀ j, ∑ i ∈ S j, f i
        = ∑ i : Fin n, if i ∈ S j then f i else 0 := by
      intro j
      conv_lhs =>
        rw [show S j = Finset.univ.filter (fun i ↦ i ∈ S j) from by ext; simp]
      rw [Finset.sum_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Step E: cover i ≥ k and f i ≥ 0 give (k : ℝ) * f i ≤ (cover i) * f i
  have h_cover_ge : ∀ i,
      (k : ℝ) * f i
        ≤ ((Finset.univ.filter (fun j : ι ↦ i ∈ S j)).card : ℝ) * f i := by
    intro i
    apply mul_le_mul_of_nonneg_right _ (hf_nonneg i)
    exact_mod_cast hk i
  -- Final calc
  calc (k : ℝ) * jointEntropy μ Xs
      = (k : ℝ) * ∑ i, f i := by rw [h_joint_eq]
    _ = ∑ i, (k : ℝ) * f i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, ((Finset.univ.filter (fun j : ι ↦ i ∈ S j)).card : ℝ) * f i :=
        Finset.sum_le_sum (fun i _ ↦ h_cover_ge i)
    _ = ∑ j : ι, ∑ i ∈ S j, f i := h_double.symm
    _ ≤ ∑ j : ι, jointEntropySubset μ Xs (S j) :=
        Finset.sum_le_sum (fun j _ ↦ h_subset_lower (S j))

end InformationTheory.Shannon
