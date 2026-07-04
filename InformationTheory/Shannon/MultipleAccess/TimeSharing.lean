import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Achievability
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Multiple access channel — time-sharing achievability (full convex-hull form)

Operational time-sharing for the two-user MAC (Cover–Thomas Theorem 15.3.1, convex-hull
form).  The single-input corner-point achievability `mac_achievability` (proven, `@audit:ok`)
is the input; this file lifts it to the convex hull of the per-input pentagons via block
concatenation.

## Main definitions

* `MACAchievable W R₁ R₂` — the operational achievability predicate for the rate pair
  `(R₁, R₂)`: for every target error `ε' > 0`, eventually (in the block length `n`) there is
  a length-`n` two-user code with at least `⌈exp (n R₁)⌉` / `⌈exp (n R₂)⌉` messages per user
  and average error probability `< ε'`.  This is exactly the conclusion of
  `mac_achievability`, abstracted over `ε'`.
* `macPentagon p₁ p₂ W` — the corner-point pentagon of the independent product input
  `p₁ ⊗ p₂`: rate pairs bounded by `macInfo₁`, `macInfo₂`, `macInfoBoth`.
* `macCapacityRegion W` — the operational capacity region, the topological closure of the
  achievable set.  (The exact-rate achievable set is not closed — boundary Pareto faces
  enter only in the closure — so the region is defined as its closure.)
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open scoped ENNReal NNReal BigOperators Topology

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β]  [DecidableEq β]  [Nonempty β]  [MeasurableSpace β]  [MeasurableSingletonClass β]

/-! ## Operational achievability predicate -/

/-- The operational achievability predicate for the MAC rate pair `(R₁, R₂)`: for every
target error `ε' > 0` there is a block length `N` such that for all `n ≥ N` there is a
length-`n` two-user code with at least `⌈exp (n R₁)⌉` / `⌈exp (n R₂)⌉` messages per user
whose average error probability is `< ε'`.  This is the `∀ ε'`-abstraction of the
conclusion of `mac_achievability`. -/
def MACAchievable (W : MACChannel α₁ α₂ β) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (M₁ M₂ : ℕ) (_ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
      (_ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
      (c : MACCode M₁ M₂ n α₁ α₂ β),
      (c.averageErrorProb W).toReal < ε'

/-- The corner-point pentagon of the independent product input `p₁ ⊗ p₂`: rate pairs with
`0 ≤ R₁`, `0 ≤ R₂`, `R₁ ≤ macInfo₁`, `R₂ ≤ macInfo₂`, `R₁ + R₂ ≤ macInfoBoth`. -/
def macPentagon (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) :
    Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ p₁ p₂ W ∧ p.2 ≤ macInfo₂ p₁ p₂ W
       ∧ p.1 + p.2 ≤ macInfoBoth p₁ p₂ W}

/-- The operational MAC capacity region: the topological closure of the achievable set.
The exact-rate achievable set is not closed (boundary Pareto faces enter only in the
closure), so the capacity region is defined as its closure. -/
def macCapacityRegion (W : MACChannel α₁ α₂ β) : Set (ℝ × ℝ) :=
  closure {p | MACAchievable W p.1 p.2}

/-! ## Monotonicity and the strict-interior wrapper -/

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Achievability is a down-set in the rate pair: a lower rate pair is easier.
@audit:ok -/
theorem mac_achievable_mono {W : MACChannel α₁ α₂ β} {R₁ R₂ R₁' R₂' : ℝ}
    (h : MACAchievable W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) :
    MACAchievable W R₁' R₂' := by
  intro ε' hε'
  obtain ⟨N, hN⟩ := h ε' hε'
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
  have hmul₁ : (n : ℝ) * R₁' ≤ (n : ℝ) * R₁ :=
    mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg n)
  have hmul₂ : (n : ℝ) * R₂' ≤ (n : ℝ) * R₂ :=
    mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg n)
  exact ⟨M₁, M₂,
    le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr hmul₁)) hM₁,
    le_trans (Nat.ceil_mono (Real.exp_le_exp.mpr hmul₂)) hM₂, c, hc⟩

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- The strict interior of a pentagon is achievable: a rate pair strictly inside the
corner-point region of a full-support product input `p₁ ⊗ p₂` is achievable.  This is the
`∀ ε'`-abstraction of `mac_achievability`.
@audit:ok -/
theorem mac_strict_interior_achievable
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hR₁lt : R₁ < macInfo₁ p₁ p₂ W) (hR₂lt : R₂ < macInfo₂ p₁ p₂ W)
    (hRsum : R₁ + R₂ < macInfoBoth p₁ p₂ W) :
    MACAchievable W R₁ R₂ := by
  intro ε' hε'
  exact mac_achievability p₁ p₂ W hp₁ hp₂ hW hR₁ hR₂ hR₁lt hR₂lt hRsum hε'

/-! ## Gateway: time-sharing convexity via block concatenation -/

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Transport a code's average error probability along a block-length equality. -/
theorem MACCode.averageErrorProb_congr_length {M₁ M₂ n n' : ℕ} (h : n = n')
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) :
    (h ▸ c).averageErrorProb W = c.averageErrorProb W := by
  cases h; rfl

/-- Block concatenation of a length-`n₁` code (user counts `Ka₁, Ka₂`) and a length-`n₂`
code (user counts `Kb₁, Kb₂`) into a length-`n₁ + n₂` code with user counts
`Ka₁·Kb₁, Ka₂·Kb₂`.  User messages are paired via `finProdFinEquiv`, codewords are
concatenated with `Fin.append`, and the joint decoder splits the received block at `n₁` and
decodes each half independently. -/
def macConcatCode {Ka₁ Ka₂ Kb₁ Kb₂ n₁ n₂ : ℕ}
    (c₁ : MACCode Ka₁ Ka₂ n₁ α₁ α₂ β) (c₂ : MACCode Kb₁ Kb₂ n₂ α₁ α₂ β) :
    MACCode (Ka₁ * Kb₁) (Ka₂ * Kb₂) (n₁ + n₂) α₁ α₂ β where
  encoder₁ m := Fin.append (c₁.encoder₁ (finProdFinEquiv.symm m).1)
                           (c₂.encoder₁ (finProdFinEquiv.symm m).2)
  encoder₂ m := Fin.append (c₁.encoder₂ (finProdFinEquiv.symm m).1)
                           (c₂.encoder₂ (finProdFinEquiv.symm m).2)
  decoder y :=
    (finProdFinEquiv ((c₁.decoder (fun i => y (Fin.castAdd n₂ i))).1,
                      (c₂.decoder (fun j => y (Fin.natAdd n₁ j))).1),
     finProdFinEquiv ((c₁.decoder (fun i => y (Fin.castAdd n₂ i))).2,
                      (c₂.decoder (fun j => y (Fin.natAdd n₁ j))).2))

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] in
/-- Pointwise error of the concatenated code is bounded by the union bound of the two block
errors: the concatenated block law factors as a product over the split
`Fin (n₁ + n₂) ≃ Fin n₁ ⊕ Fin n₂`, and the joint error event is contained in the union of
the two block error cylinders. -/
theorem macConcatCode_errorProbAt_le (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {Ka₁ Ka₂ Kb₁ Kb₂ n₁ n₂ : ℕ}
    (c₁ : MACCode Ka₁ Ka₂ n₁ α₁ α₂ β) (c₂ : MACCode Kb₁ Kb₂ n₂ α₁ α₂ β)
    (i₁ : Fin Ka₁) (i₂ : Fin Ka₂) (k₁ : Fin Kb₁) (k₂ : Fin Kb₂) :
    (macConcatCode c₁ c₂).errorProbAt W (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂))
      ≤ c₁.errorProbAt W (i₁, i₂) + c₂.errorProbAt W (k₁, k₂) := by
  -- The block-output law family for the concatenated code.
  set ν : Fin (n₁ + n₂) → Measure β :=
    fun t => W ((macConcatCode c₁ c₂).encoder₁ (finProdFinEquiv (i₁, k₁)) t,
                (macConcatCode c₁ c₂).encoder₂ (finProdFinEquiv (i₂, k₂)) t) with hνdef
  haveI hνprob : ∀ t, IsProbabilityMeasure (ν t) := by
    intro t; rw [hνdef]; infer_instance
  -- ν restricted to the two blocks matches the c₁ / c₂ block laws.
  have hleft : ∀ s : Fin n₁, ν (Fin.castAdd n₂ s) = W (c₁.encoder₁ i₁ s, c₁.encoder₂ i₂ s) := by
    intro s; rw [hνdef]; simp only [macConcatCode, Equiv.symm_apply_apply, Fin.append_left]
  have hright : ∀ t : Fin n₂, ν (Fin.natAdd n₁ t) = W (c₂.encoder₁ k₁ t, c₂.encoder₂ k₂ t) := by
    intro t; rw [hνdef]; simp only [macConcatCode, Equiv.symm_apply_apply, Fin.append_right]
  have hfam₁ : (fun s : Fin n₁ => ν (finSumFinEquiv (Sum.inl s)))
      = fun s => W (c₁.encoder₁ i₁ s, c₁.encoder₂ i₂ s) := by
    funext s; rw [finSumFinEquiv_apply_left]; exact hleft s
  have hfam₂ : (fun t : Fin n₂ => ν (finSumFinEquiv (Sum.inr t)))
      = fun t => W (c₂.encoder₁ k₁ t, c₂.encoder₂ k₂ t) := by
    funext t; rw [finSumFinEquiv_apply_right]; exact hright t
  -- Two measure-preserving maps gluing the two blocks into the full block.
  have hmp1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (n₁ + n₂) => β) finSumFinEquiv)
      (Measure.pi (fun j => ν (finSumFinEquiv j))) (Measure.pi ν) :=
    measurePreserving_piCongrLeft (α := fun _ : Fin (n₁ + n₂) => β) (μ := ν) finSumFinEquiv
  have hmp2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n₁ ⊕ Fin n₂ => β)).symm
      ((Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))).prod
        (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))))
      (Measure.pi (fun j => ν (finSumFinEquiv j))) :=
    measurePreserving_sumPiEquivProdPi_symm (fun j => ν (finSumFinEquiv j))
  set T : (Fin n₁ → β) × (Fin n₂ → β) → (Fin (n₁ + n₂) → β) :=
    ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (n₁ + n₂) => β) finSumFinEquiv) ∘
      ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n₁ ⊕ Fin n₂ => β)).symm with hTdef
  have hmp : MeasurePreserving T
      ((Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))).prod
        (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))))
      (Measure.pi ν) := hmp1.comp hmp2
  -- T sends a block pair to the interleaved full block, coordinate-wise.
  have hT_left : ∀ (u : Fin n₁ → β) (v : Fin n₂ → β) (s : Fin n₁),
      T (u, v) (Fin.castAdd n₂ s) = u s := by
    intro u v s
    rw [hTdef]
    simp only [Function.comp_apply]
    rw [← finSumFinEquiv_apply_left s, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  have hT_right : ∀ (u : Fin n₁ → β) (v : Fin n₂ → β) (t : Fin n₂),
      T (u, v) (Fin.natAdd n₁ t) = v t := by
    intro u v t
    rw [hTdef]
    simp only [Function.comp_apply]
    rw [← finSumFinEquiv_apply_right t, MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  -- The joint error event is measurable (finite ambient type).
  have hEmeas : MeasurableSet
      ((macConcatCode c₁ c₂).errorEvent (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂))) :=
    (Set.toFinite _).measurableSet
  -- The error event pulls back into the union of the two block error cylinders.
  have hsub : T ⁻¹' ((macConcatCode c₁ c₂).errorEvent
        (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂)))
      ⊆ (c₁.errorEvent (i₁, i₂)) ×ˢ Set.univ ∪ Set.univ ×ˢ (c₂.errorEvent (k₁, k₂)) := by
    rintro ⟨u, v⟩ hmem
    rw [Set.mem_preimage, MACCode.mem_errorEvent] at hmem
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and,
      MACCode.mem_errorEvent]
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hmem
    have hu : (fun s => T (u, v) (Fin.castAdd n₂ s)) = u := funext (fun s => hT_left u v s)
    have hv : (fun t => T (u, v) (Fin.natAdd n₁ t)) = v := funext (fun t => hT_right u v t)
    change (macConcatCode c₁ c₂).decoder (T (u, v))
        = (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂))
    simp only [macConcatCode]
    rw [hu, hv, h1, h2]
  -- Assemble: transport, union bound, and identify the block errors.
  have hEP : (macConcatCode c₁ c₂).errorProbAt W
        (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂))
      = (Measure.pi ν) ((macConcatCode c₁ c₂).errorEvent
          (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂))) := rfl
  rw [hEP, ← hmp.measure_preimage hEmeas.nullMeasurableSet]
  have hμ₁E : (Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))) (c₁.errorEvent (i₁, i₂))
      = c₁.errorProbAt W (i₁, i₂) := by rw [hfam₁]; rfl
  have hμ₂E : (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))) (c₂.errorEvent (k₁, k₂))
      = c₂.errorProbAt W (k₁, k₂) := by rw [hfam₂]; rfl
  calc ((Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))).prod
          (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))))
        (T ⁻¹' ((macConcatCode c₁ c₂).errorEvent
          (finProdFinEquiv (i₁, k₁), finProdFinEquiv (i₂, k₂))))
      ≤ ((Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))).prod
          (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))))
          ((c₁.errorEvent (i₁, i₂)) ×ˢ Set.univ ∪ Set.univ ×ˢ (c₂.errorEvent (k₁, k₂))) :=
        measure_mono hsub
    _ ≤ ((Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))).prod
          (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))))
          ((c₁.errorEvent (i₁, i₂)) ×ˢ Set.univ)
        + ((Measure.pi (fun s => ν (finSumFinEquiv (Sum.inl s)))).prod
          (Measure.pi (fun t => ν (finSumFinEquiv (Sum.inr t)))))
          (Set.univ ×ˢ (c₂.errorEvent (k₁, k₂))) := measure_union_le _ _
    _ = c₁.errorProbAt W (i₁, i₂) + c₂.errorProbAt W (k₁, k₂) := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul,
          hμ₁E, hμ₂E]

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] in
/-- Average error of the concatenated code is bounded by the sum of the two block averages.
Averaging the pointwise union bound over all message pairs and factoring the product sum. -/
theorem macConcatCode_averageErrorProb_le (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {Ka₁ Ka₂ Kb₁ Kb₂ n₁ n₂ : ℕ}
    (c₁ : MACCode Ka₁ Ka₂ n₁ α₁ α₂ β) (c₂ : MACCode Kb₁ Kb₂ n₂ α₁ α₂ β)
    (hKa₁ : 0 < Ka₁) (hKa₂ : 0 < Ka₂) (hKb₁ : 0 < Kb₁) (hKb₂ : 0 < Kb₂) :
    (macConcatCode c₁ c₂).averageErrorProb W
      ≤ c₁.averageErrorProb W + c₂.averageErrorProb W := by
  have hKaKb : 0 < (Ka₁ * Kb₁) * (Ka₂ * Kb₂) := by positivity
  have hKa : 0 < Ka₁ * Ka₂ := by positivity
  have hKb : 0 < Kb₁ * Kb₂ := by positivity
  simp only [MACCode.averageErrorProb, if_neg hKaKb.ne', if_neg hKa.ne', if_neg hKb.ne']
  set S₁ := ∑ p : Fin Ka₁ × Fin Ka₂, c₁.errorProbAt W p with hS₁def
  set S₂ := ∑ p : Fin Kb₁ × Fin Kb₂, c₂.errorProbAt W p with hS₂def
  -- Step 1: reindex + union bound.
  have step1 : (∑ m : Fin (Ka₁ * Kb₁) × Fin (Ka₂ * Kb₂), (macConcatCode c₁ c₂).errorProbAt W m)
      ≤ ∑ q : (Fin Ka₁ × Fin Kb₁) × (Fin Ka₂ × Fin Kb₂),
          (c₁.errorProbAt W (q.1.1, q.2.1) + c₂.errorProbAt W (q.1.2, q.2.2)) := by
    rw [← Equiv.sum_comp (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
          (fun m => (macConcatCode c₁ c₂).errorProbAt W m)]
    apply Finset.sum_le_sum
    rintro ⟨⟨i₁, k₁⟩, ⟨i₂, k₂⟩⟩ _
    exact macConcatCode_errorProbAt_le W c₁ c₂ i₁ i₂ k₁ k₂
  -- Step 2: factor the reindexed sum.
  have step2 : (∑ q : (Fin Ka₁ × Fin Kb₁) × (Fin Ka₂ × Fin Kb₂),
      (c₁.errorProbAt W (q.1.1, q.2.1) + c₂.errorProbAt W (q.1.2, q.2.2)))
      = (Kb₁ * Kb₂ : ℕ) * S₁ + (Ka₁ * Ka₂ : ℕ) * S₂ := by
    have hre : (∑ q : (Fin Ka₁ × Fin Kb₁) × (Fin Ka₂ × Fin Kb₂),
        (c₁.errorProbAt W (q.1.1, q.2.1) + c₂.errorProbAt W (q.1.2, q.2.2)))
        = ∑ r : (Fin Ka₁ × Fin Ka₂) × (Fin Kb₁ × Fin Kb₂),
            (c₁.errorProbAt W r.1 + c₂.errorProbAt W r.2) := by
      apply Fintype.sum_equiv (Equiv.prodProdProdComm (Fin Ka₁) (Fin Kb₁) (Fin Ka₂) (Fin Kb₂))
      rintro ⟨⟨i₁, k₁⟩, ⟨i₂, k₂⟩⟩
      rfl
    rw [hre, Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← Finset.mul_sum, ← hS₁def]
    · rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← hS₂def]
  -- Step 3: the arithmetic of dividing by the product.
  set A : ℝ≥0∞ := ((Ka₁ * Ka₂ : ℕ) : ℝ≥0∞) with hAdef
  set B : ℝ≥0∞ := ((Kb₁ * Kb₂ : ℕ) : ℝ≥0∞) with hBdef
  have hA0 : A ≠ 0 := by rw [hAdef]; exact_mod_cast hKa.ne'
  have hB0 : B ≠ 0 := by rw [hBdef]; exact_mod_cast hKb.ne'
  have hAt : A ≠ ⊤ := by rw [hAdef]; exact ENNReal.natCast_ne_top _
  have hBt : B ≠ ⊤ := by rw [hBdef]; exact ENNReal.natCast_ne_top _
  have hAB : ((Ka₁ * Kb₁) * (Ka₂ * Kb₂) : ℕ) = A * B := by
    rw [hAdef, hBdef]; push_cast; ring
  have hcancelB : (A * B)⁻¹ * B = A⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_assoc,
      ENNReal.inv_mul_cancel hB0 hBt, mul_one]
  have hcancelA : (A * B)⁻¹ * A = B⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), mul_comm A⁻¹ B⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel hA0 hAt, mul_one]
  rw [hAB]
  calc (A * B)⁻¹ * (∑ m : Fin (Ka₁ * Kb₁) × Fin (Ka₂ * Kb₂),
        (macConcatCode c₁ c₂).errorProbAt W m)
      ≤ (A * B)⁻¹ * (B * S₁ + A * S₂) :=
        mul_le_mul' le_rfl (step1.trans (le_of_eq step2))
    _ = (A * B)⁻¹ * B * S₁ + (A * B)⁻¹ * A * S₂ := by ring
    _ = A⁻¹ * S₁ + B⁻¹ * S₂ := by rw [hcancelB, hcancelA]

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] in
/-- **Time-sharing achievability of the convex hull (gateway, strict-rate form).** Any rate
pair *strictly below* a convex combination of two achievable rate pairs is itself
achievable, realised operationally by concatenating a length-`n₁` code (rate `(a₁, a₂)`) and
a length-`n₂` code (rate `(b₁, b₂)`) with `n₁ = ⌊lam·n⌋`.  The strict gap
`R₁ < lam·a₁ + (1-lam)·b₁` absorbs the `O(1)/n` rounding of the block split, so the
conclusion follows honestly from the hypotheses (unlike the exact-rate form, which is
false-as-framed at boundary points).  This suffices to make `macCapacityRegion` convex via
`closure` of the strict-interior achievable set. -/
theorem mac_timesharing_strict (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {a₁ a₂ b₁ b₂ R₁ R₂ lam : ℝ}
    (ha : MACAchievable W a₁ a₂) (hb : MACAchievable W b₁ b₂)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hR₁ : R₁ < lam * a₁ + (1 - lam) * b₁) (hR₂ : R₂ < lam * a₂ + (1 - lam) * b₂) :
    MACAchievable W R₁ R₂ := by
  rcases eq_or_lt_of_le hlam.1 with h0 | hlam_pos
  · -- lam = 0: the combination is exactly (b₁, b₂), achieved by hb + monotonicity.
    have e₁ : lam * a₁ + (1 - lam) * b₁ = b₁ := by rw [← h0]; ring
    have e₂ : lam * a₂ + (1 - lam) * b₂ = b₂ := by rw [← h0]; ring
    exact mac_achievable_mono hb (hR₁.trans_eq e₁).le (hR₂.trans_eq e₂).le
  · rcases eq_or_lt_of_le hlam.2 with h1 | hlam_lt
    · -- lam = 1: the combination is exactly (a₁, a₂), achieved by ha + monotonicity.
      have e₁ : lam * a₁ + (1 - lam) * b₁ = a₁ := by rw [h1]; ring
      have e₂ : lam * a₂ + (1 - lam) * b₂ = a₂ := by rw [h1]; ring
      exact mac_achievable_mono ha (hR₁.trans_eq e₁).le (hR₂.trans_eq e₂).le
    · -- 0 < lam < 1: block concatenation.
      intro ε' hε'
      obtain ⟨Na, hNa⟩ := ha (ε' / 2) (by linarith)
      obtain ⟨Nb, hNb⟩ := hb (ε' / 2) (by linarith)
      set g₁ : ℝ := lam * a₁ + (1 - lam) * b₁ - R₁ with hg₁def
      set g₂ : ℝ := lam * a₂ + (1 - lam) * b₂ - R₂ with hg₂def
      have hg₁ : 0 < g₁ := by rw [hg₁def]; linarith
      have hg₂ : 0 < g₂ := by rw [hg₂def]; linarith
      have h1lam : (0 : ℝ) < 1 - lam := by linarith
      refine ⟨max (max (Nat.ceil (((Na : ℝ) + 1) / lam)) (Nat.ceil ((Nb : ℝ) / (1 - lam))))
                  (max (Nat.ceil (|a₁ - b₁| / g₁)) (Nat.ceil (|a₂ - b₂| / g₂))),
             fun n hn => ?_⟩
      -- Extract the four size conditions from n ≥ N.
      have hc1 : Nat.ceil (((Na : ℝ) + 1) / lam) ≤ n :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      have hc2 : Nat.ceil ((Nb : ℝ) / (1 - lam)) ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      have hc3 : Nat.ceil (|a₁ - b₁| / g₁) ≤ n :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
      have hc4 : Nat.ceil (|a₂ - b₂| / g₂) ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
      -- Define the split n₁ = ⌊lam·n⌋, n₂ = n - n₁.
      set n₁ : ℕ := Nat.floor (lam * (n : ℝ)) with hn₁def
      have hlamn_nn : 0 ≤ lam * (n : ℝ) := by positivity
      have h_n₁_le_lamn : (n₁ : ℝ) ≤ lam * n := Nat.floor_le hlamn_nn
      have h_lamn_lt : lam * (n : ℝ) < (n₁ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h_n₁_le_n : n₁ ≤ n := by
        have hle : lam * (n : ℝ) ≤ (n : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
        calc n₁ = Nat.floor (lam * (n : ℝ)) := rfl
          _ ≤ Nat.floor ((n : ℝ)) := Nat.floor_mono hle
          _ = n := Nat.floor_natCast n
      set n₂ : ℕ := n - n₁ with hn₂def
      have heq : n₁ + n₂ = n := Nat.add_sub_cancel' h_n₁_le_n
      have h_n₂_real : (n₂ : ℝ) = (n : ℝ) - n₁ := by
        rw [hn₂def]; exact Nat.cast_sub h_n₁_le_n
      -- n₁ ≥ Na and n₂ ≥ Nb.
      have hn₁_ge : Na ≤ n₁ := by
        have h1 : ((Na : ℝ) + 1) / lam ≤ (n : ℝ) := by
          have := Nat.le_ceil (((Na : ℝ) + 1) / lam)
          exact le_trans this (by exact_mod_cast hc1)
        have h2 : (Na : ℝ) + 1 ≤ (n : ℝ) * lam := (div_le_iff₀ hlam_pos).mp h1
        have : (Na : ℝ) < n₁ := by nlinarith [h_lamn_lt, h2]
        exact_mod_cast this.le
      have hn₂_ge : Nb ≤ n₂ := by
        have h1 : (Nb : ℝ) / (1 - lam) ≤ (n : ℝ) := by
          have := Nat.le_ceil ((Nb : ℝ) / (1 - lam))
          exact le_trans this (by exact_mod_cast hc2)
        have h2 : (Nb : ℝ) ≤ (n : ℝ) * (1 - lam) := (div_le_iff₀ h1lam).mp h1
        have : (Nb : ℝ) ≤ n₂ := by rw [h_n₂_real]; nlinarith [h_n₁_le_lamn]
        exact_mod_cast this
      -- Rate conditions.
      have hrate1 : |a₁ - b₁| ≤ (n : ℝ) * g₁ := by
        have h1 : |a₁ - b₁| / g₁ ≤ (n : ℝ) := by
          have := Nat.le_ceil (|a₁ - b₁| / g₁)
          exact le_trans this (by exact_mod_cast hc3)
        calc |a₁ - b₁| = (|a₁ - b₁| / g₁) * g₁ := by field_simp
          _ ≤ (n : ℝ) * g₁ := by nlinarith [h1, hg₁.le]
      have hrate2 : |a₂ - b₂| ≤ (n : ℝ) * g₂ := by
        have h1 : |a₂ - b₂| / g₂ ≤ (n : ℝ) := by
          have := Nat.le_ceil (|a₂ - b₂| / g₂)
          exact le_trans this (by exact_mod_cast hc4)
        calc |a₂ - b₂| = (|a₂ - b₂| / g₂) * g₂ := by field_simp
          _ ≤ (n : ℝ) * g₂ := by nlinarith [h1, hg₂.le]
      -- The rate arithmetic: n·R ≤ n₁·a + n₂·b for each user.
      have key1 : (n : ℝ) * R₁ ≤ (n₁ : ℝ) * a₁ + (n₂ : ℝ) * b₁ := by
        have hident : (n₁ : ℝ) * a₁ + (n₂ : ℝ) * b₁
            = (n : ℝ) * (lam * a₁ + (1 - lam) * b₁) + ((n₁ : ℝ) - n * lam) * (a₁ - b₁) := by
          rw [h_n₂_real]; ring
        have habs : |(n₁ : ℝ) - n * lam| ≤ 1 :=
          abs_le.mpr ⟨by nlinarith [h_lamn_lt], by nlinarith [h_n₁_le_lamn]⟩
        have hprod : -(|a₁ - b₁|) ≤ ((n₁ : ℝ) - n * lam) * (a₁ - b₁) := by
          calc -(|a₁ - b₁|) ≤ -(|((n₁ : ℝ) - n * lam) * (a₁ - b₁)|) := by
                rw [abs_mul]
                have := mul_le_of_le_one_left (abs_nonneg (a₁ - b₁)) habs
                linarith
            _ ≤ ((n₁ : ℝ) - n * lam) * (a₁ - b₁) := neg_abs_le _
        have hgap : (n : ℝ) * (lam * a₁ + (1 - lam) * b₁) = (n : ℝ) * R₁ + n * g₁ := by
          rw [hg₁def]; ring
        linarith [hident, hprod, hrate1, hgap]
      have key2 : (n : ℝ) * R₂ ≤ (n₁ : ℝ) * a₂ + (n₂ : ℝ) * b₂ := by
        have hident : (n₁ : ℝ) * a₂ + (n₂ : ℝ) * b₂
            = (n : ℝ) * (lam * a₂ + (1 - lam) * b₂) + ((n₁ : ℝ) - n * lam) * (a₂ - b₂) := by
          rw [h_n₂_real]; ring
        have habs : |(n₁ : ℝ) - n * lam| ≤ 1 :=
          abs_le.mpr ⟨by nlinarith [h_lamn_lt], by nlinarith [h_n₁_le_lamn]⟩
        have hprod : -(|a₂ - b₂|) ≤ ((n₁ : ℝ) - n * lam) * (a₂ - b₂) := by
          calc -(|a₂ - b₂|) ≤ -(|((n₁ : ℝ) - n * lam) * (a₂ - b₂)|) := by
                rw [abs_mul]
                have := mul_le_of_le_one_left (abs_nonneg (a₂ - b₂)) habs
                linarith
            _ ≤ ((n₁ : ℝ) - n * lam) * (a₂ - b₂) := neg_abs_le _
        have hgap : (n : ℝ) * (lam * a₂ + (1 - lam) * b₂) = (n : ℝ) * R₂ + n * g₂ := by
          rw [hg₂def]; ring
        linarith [hident, hprod, hrate2, hgap]
      -- Obtain the two block codes.
      obtain ⟨Ka₁, Ka₂, hKa₁, hKa₂, c₁, hc₁⟩ := hNa n₁ hn₁_ge
      obtain ⟨Kb₁, Kb₂, hKb₁, hKb₂, c₂, hc₂⟩ := hNb n₂ hn₂_ge
      -- Positivity of all message counts.
      have hpKa₁ : 0 < Ka₁ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hKa₁
      have hpKa₂ : 0 < Ka₂ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hKa₂
      have hpKb₁ : 0 < Kb₁ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hKb₁
      have hpKb₂ : 0 < Kb₂ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hKb₂
      -- Rate bounds for the concatenated code.
      have Hrate₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ Ka₁ * Kb₁ := by
        rw [Nat.ceil_le, Nat.cast_mul]
        have e1 : Real.exp ((n₁ : ℝ) * a₁) ≤ (Ka₁ : ℝ) :=
          le_trans (Nat.le_ceil _) (by exact_mod_cast hKa₁)
        have e2 : Real.exp ((n₂ : ℝ) * b₁) ≤ (Kb₁ : ℝ) :=
          le_trans (Nat.le_ceil _) (by exact_mod_cast hKb₁)
        calc Real.exp ((n : ℝ) * R₁)
            ≤ Real.exp ((n₁ : ℝ) * a₁ + (n₂ : ℝ) * b₁) := Real.exp_le_exp.mpr key1
          _ = Real.exp ((n₁ : ℝ) * a₁) * Real.exp ((n₂ : ℝ) * b₁) := Real.exp_add _ _
          _ ≤ (Ka₁ : ℝ) * (Kb₁ : ℝ) :=
                mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
      have Hrate₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ Ka₂ * Kb₂ := by
        rw [Nat.ceil_le, Nat.cast_mul]
        have e1 : Real.exp ((n₁ : ℝ) * a₂) ≤ (Ka₂ : ℝ) :=
          le_trans (Nat.le_ceil _) (by exact_mod_cast hKa₂)
        have e2 : Real.exp ((n₂ : ℝ) * b₂) ≤ (Kb₂ : ℝ) :=
          le_trans (Nat.le_ceil _) (by exact_mod_cast hKb₂)
        calc Real.exp ((n : ℝ) * R₂)
            ≤ Real.exp ((n₁ : ℝ) * a₂ + (n₂ : ℝ) * b₂) := Real.exp_le_exp.mpr key2
          _ = Real.exp ((n₁ : ℝ) * a₂) * Real.exp ((n₂ : ℝ) * b₂) := Real.exp_add _ _
          _ ≤ (Ka₂ : ℝ) * (Kb₂ : ℝ) :=
                mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
      -- Assemble the concatenated code (transported to block length n).
      refine ⟨Ka₁ * Kb₁, Ka₂ * Kb₂, Hrate₁, Hrate₂, heq ▸ macConcatCode c₁ c₂, ?_⟩
      rw [MACCode.averageErrorProb_congr_length heq (macConcatCode c₁ c₂) W]
      have hle : (macConcatCode c₁ c₂).averageErrorProb W
          ≤ c₁.averageErrorProb W + c₂.averageErrorProb W :=
        macConcatCode_averageErrorProb_le W c₁ c₂ hpKa₁ hpKa₂ hpKb₁ hpKb₂
      have hsum_ne : c₁.averageErrorProb W + c₂.averageErrorProb W ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨c₁.averageErrorProb_ne_top W, c₂.averageErrorProb_ne_top W⟩
      calc ((macConcatCode c₁ c₂).averageErrorProb W).toReal
          ≤ (c₁.averageErrorProb W + c₂.averageErrorProb W).toReal :=
            ENNReal.toReal_mono hsum_ne hle
        _ = (c₁.averageErrorProb W).toReal + (c₂.averageErrorProb W).toReal :=
            ENNReal.toReal_add (c₁.averageErrorProb_ne_top W) (c₂.averageErrorProb_ne_top W)
        _ < ε' := by linarith [hc₁, hc₂]

/-! ## Convexity and closedness of the capacity region -/

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- A rate pair whose strictly-smaller (in both coordinates) perturbations are all
achievable lies in the capacity region.  The perturbed points `(p.1 - ε, p.2 - ε)` form a
sequence in the achievable set converging to `p`, so `p` is in its closure.
@audit:ok -/
theorem mac_mem_closure_of_strictly_below (W : MACChannel α₁ α₂ β) (p : ℝ × ℝ)
    (h : ∀ ε : ℝ, 0 < ε → MACAchievable W (p.1 - ε) (p.2 - ε)) :
    p ∈ closure {q : ℝ × ℝ | MACAchievable W q.1 q.2} := by
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun k => (p.1 - 1 / ((k : ℝ) + 1), p.2 - 1 / ((k : ℝ) + 1)), ?_, ?_⟩
  · intro k
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact h _ hpos
  · have ht : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k : ℕ => p.1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 p.1) := by
      simpa using tendsto_const_nhds.sub ht
    have h2 : Tendsto (fun k : ℕ => p.2 - 1 / ((k : ℝ) + 1)) atTop (𝓝 p.2) := by
      simpa using tendsto_const_nhds.sub ht
    exact h1.prodMk_nhds h2

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- The capacity region is closed (it is defined as a closure).
@audit:ok -/
theorem mac_capacityRegion_isClosed (W : MACChannel α₁ α₂ β) :
    IsClosed (macCapacityRegion W) := isClosed_closure

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] in
/-- The capacity region is convex.  Convexity of the closure follows from time-sharing:
the segment between any two achievable points lies in the closure (via
`mac_timesharing_strict`), and this lifts to closure points by a sequential limit.
@audit:ok -/
theorem mac_capacityRegion_convex (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    Convex ℝ (macCapacityRegion W) := by
  -- The segment between two achievable points lies in the capacity region.
  have seg : ∀ x : ℝ × ℝ, MACAchievable W x.1 x.2 → ∀ y : ℝ × ℝ, MACAchievable W y.1 y.2 →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ macCapacityRegion W := by
    intro x hx y hy a b ha hb hab
    apply mac_mem_closure_of_strictly_below
    intro ε hε
    have hla : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
    have e1 : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp [smul_eq_mul]
    have e2 : (a • x + b • y).2 = a * x.2 + b * y.2 := by simp [smul_eq_mul]
    rw [e1, e2]
    have hb' : b = 1 - a := by linarith
    refine mac_timesharing_strict W hx hy hla ?_ ?_
    · rw [hb']; linarith
    · rw [hb']; linarith
  -- Lift convexity to the closure by a sequential limit.
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp hy
  have hw_mem : ∀ k, a • u k + b • v k ∈ macCapacityRegion W := fun k =>
    seg (u k) (hu_mem k) (v k) (hv_mem k) a b ha hb hab
  have hw_tend : Tendsto (fun k => a • u k + b • v k) atTop (𝓝 (a • x + b • y)) :=
    (hu_tend.const_smul a).add (hv_tend.const_smul b)
  exact (mac_capacityRegion_isClosed W).mem_of_tendsto hw_tend (Eventually.of_forall hw_mem)

/-! ## Each pentagon lies in the capacity region -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- Every rate pair of a full-support product input's pentagon lies in the capacity region.
Strictly-interior points are directly achievable (`mac_strict_interior_achievable`); every
other point is a limit of interior points via a convex combination toward an interior
witness. -/
theorem mac_pentagon_subset_capacityRegion
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b}) :
    macPentagon p₁ p₂ W ⊆ macCapacityRegion W := by
  intro R hR
  obtain ⟨hR1nn, hR2nn, hR1le, hR2le, hRsumle⟩ := hR
  by_cases hpos : 0 < macInfo₁ p₁ p₂ W ∧ 0 < macInfo₂ p₁ p₂ W ∧ 0 < macInfoBoth p₁ p₂ W
  · -- Nonempty interior: approximate `R` by a convex combination toward an interior witness.
    obtain ⟨hI1, hI2, hIb⟩ := hpos
    set c₁ : ℝ := min (macInfo₁ p₁ p₂ W) (macInfoBoth p₁ p₂ W) / 3 with hc₁def
    set c₂ : ℝ := min (macInfo₂ p₁ p₂ W) (macInfoBoth p₁ p₂ W) / 3 with hc₂def
    have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith [lt_min hI1 hIb]
    have hc₂pos : 0 < c₂ := by rw [hc₂def]; linarith [lt_min hI2 hIb]
    have hc₁ltI : c₁ < macInfo₁ p₁ p₂ W := by
      rw [hc₁def]; linarith [min_le_left (macInfo₁ p₁ p₂ W) (macInfoBoth p₁ p₂ W), hI1]
    have hc₂ltI : c₂ < macInfo₂ p₁ p₂ W := by
      rw [hc₂def]; linarith [min_le_left (macInfo₂ p₁ p₂ W) (macInfoBoth p₁ p₂ W), hI2]
    have hcsum : c₁ + c₂ < macInfoBoth p₁ p₂ W := by
      rw [hc₁def, hc₂def]
      linarith [min_le_right (macInfo₁ p₁ p₂ W) (macInfoBoth p₁ p₂ W),
        min_le_right (macInfo₂ p₁ p₂ W) (macInfoBoth p₁ p₂ W), hIb]
    -- Every `t`-combination toward `(c₁, c₂)` (`0 < t ≤ 1`) is strictly interior, hence achievable.
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
        MACAchievable W (R.1 + t * (c₁ - R.1)) (R.2 + t * (c₂ - R.2)) := by
      intro t ht0 ht1
      have h1t : (0 : ℝ) ≤ 1 - t := by linarith
      refine mac_strict_interior_achievable p₁ p₂ W hp₁ hp₂ hW ?_ ?_ ?_ ?_ ?_
      · nlinarith [mul_pos ht0 hc₁pos, mul_nonneg h1t hR1nn]
      · nlinarith [mul_pos ht0 hc₂pos, mul_nonneg h1t hR2nn]
      · nlinarith [mul_le_mul_of_nonneg_left hR1le h1t, mul_lt_mul_of_pos_left hc₁ltI ht0]
      · nlinarith [mul_le_mul_of_nonneg_left hR2le h1t, mul_lt_mul_of_pos_left hc₂ltI ht0]
      · nlinarith [mul_le_mul_of_nonneg_left hRsumle h1t, mul_lt_mul_of_pos_left hcsum ht0]
    -- `R` is the limit of these interior points, hence in the closure.
    refine mem_closure_iff_seq_limit.mpr
      ⟨fun k => R + (1 / ((k : ℝ) + 1)) • (((c₁, c₂) : ℝ × ℝ) - R), ?_, ?_⟩
    · intro k
      have ht0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have ht1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
      have hk := key _ ht0 ht1
      show MACAchievable W (R + (1 / ((k : ℝ) + 1)) • (((c₁, c₂) : ℝ × ℝ) - R)).1
        (R + (1 / ((k : ℝ) + 1)) • (((c₁, c₂) : ℝ × ℝ) - R)).2
      have e1 : (R + (1 / ((k : ℝ) + 1)) • (((c₁, c₂) : ℝ × ℝ) - R)).1
          = R.1 + (1 / ((k : ℝ) + 1)) * (c₁ - R.1) := by simp [smul_eq_mul]
      have e2 : (R + (1 / ((k : ℝ) + 1)) • (((c₁, c₂) : ℝ × ℝ) - R)).2
          = R.2 + (1 / ((k : ℝ) + 1)) * (c₂ - R.2) := by simp [smul_eq_mul]
      rw [e1, e2]; exact hk
    · have ht : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hlim := tendsto_const_nhds (x := R) (f := atTop) |>.add
        (ht.smul_const (((c₁, c₂) : ℝ × ℝ) - R))
      simpa using hlim
  · -- Degenerate pentagon: some `macInfo` is `0`, so the pentagon collapses onto an axis and
    -- the point requires single-user achievability (user 1 or 2 silent), which is not derivable
    -- from `mac_achievability` (it needs both rates strictly positive).
    -- @residual(plan:mac-timesharing-plan)
    sorry

/-! ## Achievability headline: the closed convex hull of the pentagons -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **MAC time-sharing achievability (convex-hull form, Cover–Thomas Theorem 15.3.1).**  The
closed convex hull of the per-input pentagons of full-support product inputs is contained in
the operational capacity region. -/
@[entry_point]
theorem mac_achievability_region (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b}) :
    closedConvexHull ℝ
      (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂) (_ : IsProbabilityMeasure p₁)
         (_ : IsProbabilityMeasure p₂) (_ : ∀ a, 0 < p₁.real {a}) (_ : ∀ a, 0 < p₂.real {a}),
         macPentagon p₁ p₂ W)
      ⊆ macCapacityRegion W := by
  refine closedConvexHull_min ?_ (mac_capacityRegion_convex W) (mac_capacityRegion_isClosed W)
  simp only [Set.iUnion_subset_iff]
  intro p₁ p₂ hp₁inst hp₂inst hp₁ hp₂
  haveI := hp₁inst
  haveI := hp₂inst
  exact mac_pentagon_subset_capacityRegion p₁ p₂ W hp₁ hp₂ hW

end InformationTheory.Shannon.MAC
