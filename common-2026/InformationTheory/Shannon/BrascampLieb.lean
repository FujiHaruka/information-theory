import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.LoomisWhitney

/-!
# Brascamp–Lieb inequality (combinatorial form) and hypercube product projection bound

Generalizes the Loomis–Whitney inequality (`LoomisWhitney.lean`) to an arbitrary cover family
`S : ι → Finset (Fin n)` where each `j : Fin n` is covered at least `k` times:
$$|A|^k \le \prod_{i : \iota} |\pi_{S_i}(A)|.$$

## Main definitions

* `projectionSubset S A` — restriction of `A : Finset (Fin n → α)` to a subset `S : Finset (Fin n)`
  of coordinates, returning a `Finset (↥S → α)`.

## Main statements

* `brascamp_lieb_finset` — Brascamp–Lieb inequality for arbitrary cover families.
* `hypercube_product_projection_bound` — singleton-cover corollary: `|A| ≤ ∏ i, |π_{{i}}(A)|`.

## Implementation notes

The proof routes through `shearer_inequality` from `LoomisWhitney.lean` as the entropic engine,
then peels off the logarithm via `Real.log_le_log_iff`.

Loomis–Whitney (`loomis_whitney`) is the special case `S i := univ.filter (· ≠ i)` (each `j`
covered `n-1` times), but the existing `LoomisWhitney.lean` shape is preserved to avoid
changing `projectionExcept` and `loomis_whitney`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## Projection onto a coordinate subset -/

/-- The image of `A : Finset (Fin n → α)` under restriction to coordinates in
`S : Finset (Fin n)`. -/
def projectionSubset {n : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin n)) (A : Finset (Fin n → α)) :
    Finset (↥S → α) :=
  A.image (fun (x : Fin n → α) (j : ↥S) ↦ x j.val)

/-- For `A` equipped with the uniform measure, the joint entropy over coordinates `S`
is bounded by `log |projectionSubset S A|`. -/
theorem jointEntropySubset_le_log_projectionSubset_card
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) (S : Finset (Fin n)) :
    jointEntropySubset (uniformOn (A : Set (Fin n → α)))
        (fun (i : Fin n) (ω : Fin n → α) ↦ ω i) S
      ≤ Real.log (projectionSubset S A).card := by
  classical
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set (Fin n → α))) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  -- jointEntropySubset μ (fun i ω => ω i) S = entropy μ (fun ω j => ω j.val)
  unfold jointEntropySubset
  -- The function f : (Fin n → α) → (↥S → α), ω ↦ (j ↦ ω j.val).
  set fproj : (Fin n → α) → (↥S → α) := fun (x : Fin n → α) (j : ↥S) ↦ x j.val
    with hfproj_def
  have hfproj_meas : Measurable fproj :=
    measurable_pi_iff.mpr (fun (j : ↥S) ↦ measurable_pi_apply j.val)
  -- Goal after `unfold jointEntropySubset`:
  --   entropy μ (fun ω (i : ↥S) => (fun i ω => ω i) i.val ω) ≤ log (projectionSubset S A).card
  -- which simplifies to entropy μ fproj ≤ log (A.image fproj).card.
  have h_le := entropy_le_log_image_card (β := Fin n → α) (γ := ↥S → α)
    hA fproj hfproj_meas
  -- (A.image fproj) = projectionSubset S A by def.
  show entropy (uniformOn (A : Set (Fin n → α))) fproj
      ≤ Real.log (projectionSubset S A).card
  exact h_le

/-! ## Brascamp–Lieb inequality -/

/-- Brascamp–Lieb inequality (combinatorial form).

If `S : ι → Finset (Fin n)` is a cover family such that each `j : Fin n` is covered
at least `k` times, then for any nonempty finite set `A : Finset (Fin n → α)`:
$$|A|^k \le \prod_{i : \iota} |\pi_{S_i}(A)|.$$

Loomis–Whitney is the special case `S i := univ.filter (· ≠ i)` with `k = n - 1`.
The hypercube product projection bound is the special case `S i := {i}` with `k = 1`. -/
@[entry_point]
theorem brascamp_lieb_finset
    {n k : ℕ} {ι : Type*} [Fintype ι]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty)
    (S : ι → Finset (Fin n))
    (hk : ∀ j : Fin n,
      k ≤ (Finset.univ.filter (fun i : ι ↦ j ∈ S i)).card) :
    A.card ^ k ≤ ∏ i : ι, (projectionSubset (S i) A).card := by
  classical
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set (Fin n → α))) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  set μ : Measure (Fin n → α) := uniformOn (A : Set (Fin n → α)) with hμ_def
  set Xs : Fin n → (Fin n → α) → α := fun i ω ↦ ω i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i ↦ measurable_pi_apply i
  -- Apply Shearer engine
  have h_shearer := shearer_inequality μ Xs hXs_meas S hk
  -- LHS bridge: jointEntropy μ Xs = log #A
  have h_joint_log : jointEntropy μ Xs = Real.log A.card := by
    unfold jointEntropy
    have h_eq : (fun (ω : Fin n → α) (i : Fin n) ↦ Xs i ω) = id := by
      funext ω; funext i; rfl
    rw [h_eq]
    exact entropy_uniformOn_eq_log_card hA
  rw [h_joint_log] at h_shearer
  -- RHS bridge: each summand ≤ log #(projectionSubset (S i) A)
  have h_marginal : ∀ i : ι,
      jointEntropySubset μ Xs (S i)
        ≤ Real.log (projectionSubset (S i) A).card := by
    intro i
    exact jointEntropySubset_le_log_projectionSubset_card hA (S i)
  have h_RHS_le : ∑ i : ι, jointEntropySubset μ Xs (S i)
      ≤ ∑ i : ι, Real.log (projectionSubset (S i) A).card :=
    Finset.sum_le_sum (fun i _ ↦ h_marginal i)
  -- Combine: (k : ℝ) * log #A ≤ ∑ i, log #(projectionSubset (S i) A)
  have h_log :
      (k : ℝ) * Real.log A.card
        ≤ ∑ i : ι, Real.log (projectionSubset (S i) A).card :=
    h_shearer.trans h_RHS_le
  -- Positivity of projection cardinalities
  have h_proj_pos : ∀ i : ι, 0 < (projectionSubset (S i) A).card := by
    intro i
    have : (projectionSubset (S i) A).Nonempty :=
      hA.image (fun (x : Fin n → α) (j : ↥(S i)) ↦ x j.val)
    exact this.card_pos
  have h_proj_ne : ∀ i : ι,
      ((projectionSubset (S i) A).card : ℝ) ≠ 0 := fun i ↦ by
    exact_mod_cast (h_proj_pos i).ne'
  -- Convert ∑ log to log ∏
  have h_sum_log_eq :
      (∑ i : ι, Real.log (projectionSubset (S i) A).card)
        = Real.log (∏ i : ι, ((projectionSubset (S i) A).card : ℝ)) := by
    rw [Real.log_prod (fun i _ ↦ h_proj_ne i)]
  rw [h_sum_log_eq] at h_log
  -- LHS: (k : ℝ) * log #A = log (#A ^ k)
  have h_lhs_eq :
      (k : ℝ) * Real.log A.card = Real.log ((A.card : ℝ) ^ k) := by
    rw [Real.log_pow]
  rw [h_lhs_eq] at h_log
  -- Peel off log via monotonicity
  have h_card_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have h_lhs_pos : (0 : ℝ) < (A.card : ℝ) ^ k := pow_pos h_card_pos _
  have h_rhs_pos : (0 : ℝ) < ∏ i : ι, ((projectionSubset (S i) A).card : ℝ) :=
    Finset.prod_pos (fun i _ ↦ by exact_mod_cast h_proj_pos i)
  have h_pow_le :
      (A.card : ℝ) ^ k
        ≤ ∏ i : ι, ((projectionSubset (S i) A).card : ℝ) :=
    (Real.log_le_log_iff h_lhs_pos h_rhs_pos).mp h_log
  -- Cast to ℕ
  have h_cast :
      ((A.card ^ k : ℕ) : ℝ)
        ≤ (((∏ i : ι, (projectionSubset (S i) A).card) : ℕ) : ℝ) := by
    push_cast
    exact h_pow_le
  exact_mod_cast h_cast

/-! ## Hypercube product projection bound -/

/-- Singleton-cover corollary: for any nonempty `A : Finset (Fin n → α)`,
`|A| ≤ ∏ i, |π_{{i}}(A)|`.

This is `brascamp_lieb_finset` with `S i := {i}` and `k := 1`. Setting `α = Bool` recovers
`|A| ≤ 2^n` since each singleton projection has cardinality at most 2. -/
@[entry_point]
theorem hypercube_product_projection_bound
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) :
    A.card ≤ ∏ i : Fin n, (projectionSubset ({i} : Finset (Fin n)) A).card := by
  classical
  -- Apply BL with S i := {i}, k := 1
  set S : Fin n → Finset (Fin n) := fun i ↦ ({i} : Finset (Fin n)) with hS_def
  have h_cover : ∀ j : Fin n,
      1 ≤ (Finset.univ.filter (fun i : Fin n ↦ j ∈ S i)).card := by
    intro j
    -- {i | j ∈ {i}} = {i | i = j} = {j}, card = 1
    have h_filter_eq : Finset.univ.filter (fun i : Fin n ↦ j ∈ S i)
        = ({j} : Finset (Fin n)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, S]
      exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
    rw [h_filter_eq, Finset.card_singleton]
  have h_BL := brascamp_lieb_finset (k := 1) hA S h_cover
  -- A.card ^ 1 = A.card
  simpa using h_BL

end InformationTheory.Shannon
