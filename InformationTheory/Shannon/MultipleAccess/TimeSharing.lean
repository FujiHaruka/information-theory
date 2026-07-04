import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Achievability
import InformationTheory.Shannon.MultipleAccess.Reconciliation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Probability.Distributions.Uniform
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

omit [Fintype α₁] [DecidableEq α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- The zero rate pair `(0, 0)` is achievable: the trivial single-message code
(`M₁ = M₂ = 1`) never errs, because `Fin 1 × Fin 1` has a unique message pair, so the
decoder is always correct and the average error probability is `0`.
@audit:ok -/
theorem mac_achievable_zero_zero (W : MACChannel α₁ α₂ β) :
    MACAchievable W 0 0 := by
  classical
  intro ε' hε'
  refine ⟨0, fun n _ => ?_⟩
  set c : MACCode 1 1 n α₁ α₂ β :=
    { encoder₁ := fun _ _ => Classical.arbitrary α₁
      encoder₂ := fun _ _ => Classical.arbitrary α₂
      decoder := fun _ => (0, 0) } with hc
  have herr : ∀ m : Fin 1 × Fin 1, c.errorProbAt W m = 0 := by
    intro m
    have hev : c.errorEvent m = (∅ : Set (Fin n → β)) := by
      unfold MACCode.errorEvent MACCode.decodingRegion
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
      exact hy (Subsingleton.elim _ _)
    rw [MACCode.errorProbAt, hev, measure_empty]
  have hzero : c.averageErrorProb W = 0 := by
    rw [MACCode.averageErrorProb]
    simp [herr]
  exact ⟨1, 1, by simp, by simp, c, by rw [hzero]; simpa using hε'⟩

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

/-! ## Single-user axes: M₁ = 1 (resp. M₂ = 1) specialisation of the achievability engine -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **Single-user axis (user 1 silent).**  The rate pair `(0, R₂)` with `R₂ < macInfo₂` is
achievable.  This is the `R₁ = 0` specialisation of the achievability engine: `R₁ = 0`
forces `M₁ = ⌈exp (n·0)⌉ = 1`, so the two alias terms carrying the `(M₁ - 1)` factor (`E1`,
`E3`) collapse to `0` and only the correct-pair atypicality `E0` (AEP) and the user-2 alias
`E2` (controlled by `R₂ < macInfo₂`) remain.  The corner conditions `R₁ < macInfo₁` and
`R₁ + R₂ < macInfoBoth` of `mac_achievability` — vacuous when `macInfo₁ ≤ 0` — are therefore
not needed.
@audit:ok -/
theorem mac_axis1_achievable
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {R₂ : ℝ} (hR₂lt : R₂ < macInfo₂ p₁ p₂ W) :
    MACAchievable W 0 R₂ := by
  classical
  intro ε' hε'
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Rate slack `ε`: a sixth of the single user-2 gap.
  set ε : ℝ := (macInfo₂ p₁ p₂ W - R₂) / 6 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have hgap2 : 0 < macInfo₂ p₁ p₂ W - R₂ - 3 * ε := by rw [hε_def]; linarith
  have hε'2 : 0 < ε' / 2 := by linarith
  -- Measurability of the four coordinate selectors used by the AEP.
  have hm_X2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hm_Y : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  have hm_X1X2 : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm_X1Y : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  -- (N₀) AEP: the correct-pair-typical probability tends to 1.
  have h_aep := macJointlyTypicalSet_prob_tendsto_one μ macX1s macX2s macYs
    measurable_macX1s measurable_macX2s measurable_macYs
    (macAmbient_pairwise_coord p₁ p₂ W Prod.fst measurable_fst)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.fst measurable_fst i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ q.2.1) hm_X2)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.1) hm_X2 i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ q.2.2) hm_Y)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.2) hm_Y i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1)) hm_X1X2)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1)) hm_X1X2 i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2)) hm_X1Y)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2)) hm_X1Y i)
    (macAmbient_pairwise_coord p₁ p₂ W Prod.snd measurable_snd)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.snd measurable_snd i)
    (macAmbient_pairwise_coord p₁ p₂ W id measurable_id)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W id measurable_id i)
    hε_pos
  have h_aep_real : Filter.Tendsto
      (fun n : ℕ ↦ (μ {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
          macJointlyTypicalSet μ macX1s macX2s macYs n ε}).toReal)
      Filter.atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (a := (1 : ℝ≥0∞)) (by simp)).comp h_aep
    simpa [Function.comp_def] using h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (h_aep_real.eventually (eventually_gt_nhds (show (1 : ℝ) - ε' / 2 < 1 by linarith)))
  -- (N₂) exponential decay of the user-2 alias term.
  obtain ⟨N₂, hN₂⟩ := channelCoding_E2_lt_of_rate (I := macInfo₂ p₁ p₂ W) (R := R₂)
    (ε := ε) (ε' := ε' / 2) hgap2 hε'2
  refine ⟨max N₀ N₂, fun n hn ↦ ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  set M₂ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₂)) with hM₂_def
  have hM₂_pos : 0 < M₂ := Nat.ceil_pos.mpr (Real.exp_pos _)
  -- The two-codebook average bound with `M₁ = 1`; the `(M₁ - 1)` alias terms vanish.
  have h_avg_bound := mac_random_codebook_average_le (M₁ := 1) (M₂ := M₂) (n := n)
    p₁ p₂ W hp₁ hp₂ hW Nat.one_pos hM₂_pos hε_pos
  simp only [Nat.cast_one, sub_self, zero_mul, add_zero] at h_avg_bound
  -- Bound the two surviving terms.
  have hE0 : μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
      macJointlyTypicalSet μ macX1s macX2s macYs n ε} ≤ ε' / 2 := by
    have h_meas_good : MeasurableSet
        {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
            macJointlyTypicalSet μ macX1s macX2s macYs n ε} := by
      have h_meas_triple : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
          (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
        (measurable_jointRV (α := α₁) macX1s measurable_macX1s n).prodMk
          ((measurable_jointRV (α := α₂) macX2s measurable_macX2s n).prodMk
            (measurable_jointRV (α := β) macYs measurable_macYs n))
      exact h_meas_triple (measurableSet_macJointlyTypicalSet μ macX1s macX2s macYs n ε)
    exact InformationTheory.Shannon.ChannelCoding.complementProbReal_le_of_one_sub_le
      h_meas_good (le_of_lt (hN₀ n hn0))
  have hE2 : ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)) < ε' / 2 := by
    have := hN₂ n hn2
    rwa [hM₂_def]
  have hRHS_lt :
      μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
            macJointlyTypicalSet μ macX1s macX2s macYs n ε}
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)) < ε' := by
    linarith
  -- Pigeonhole to a deterministic codebook pair, then package the code (a `MACCode 1 M₂ n`).
  obtain ⟨c₁, c₂, hcb⟩ := mac_exists_codebook_le_avg μ macX1s macX2s macYs W p₁ p₂
    Nat.one_pos hM₂_pos _ h_avg_bound
  refine ⟨1, M₂, ?_, le_refl _,
    macCodebookToCode μ macX1s macX2s macYs Nat.one_pos hM₂_pos ε c₁ c₂, ?_⟩
  · rw [mul_zero, Real.exp_zero, Nat.ceil_one]
  · exact lt_of_le_of_lt hcb hRHS_lt

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **Single-user axis (user 2 silent).**  The rate pair `(R₁, 0)` with `R₁ < macInfo₁` is
achievable.  Symmetric to `mac_axis1_achievable`: `R₂ = 0` forces `M₂ = 1`, collapsing the
`(M₂ - 1)`-carrying alias terms (`E2`, `E3`) and leaving only `E0` (AEP) and the user-1 alias
`E1` (controlled by `R₁ < macInfo₁`).
@audit:ok -/
theorem mac_axis2_achievable
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {R₁ : ℝ} (hR₁lt : R₁ < macInfo₁ p₁ p₂ W) :
    MACAchievable W R₁ 0 := by
  classical
  intro ε' hε'
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Rate slack `ε`: a sixth of the single user-1 gap.
  set ε : ℝ := (macInfo₁ p₁ p₂ W - R₁) / 6 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have hgap1 : 0 < macInfo₁ p₁ p₂ W - R₁ - 3 * ε := by rw [hε_def]; linarith
  have hε'2 : 0 < ε' / 2 := by linarith
  -- Measurability of the four coordinate selectors used by the AEP.
  have hm_X2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hm_Y : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  have hm_X1X2 : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm_X1Y : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  -- (N₀) AEP: the correct-pair-typical probability tends to 1.
  have h_aep := macJointlyTypicalSet_prob_tendsto_one μ macX1s macX2s macYs
    measurable_macX1s measurable_macX2s measurable_macYs
    (macAmbient_pairwise_coord p₁ p₂ W Prod.fst measurable_fst)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.fst measurable_fst i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ q.2.1) hm_X2)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.1) hm_X2 i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ q.2.2) hm_Y)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.2) hm_Y i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1)) hm_X1X2)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1)) hm_X1X2 i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2)) hm_X1Y)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2)) hm_X1Y i)
    (macAmbient_pairwise_coord p₁ p₂ W Prod.snd measurable_snd)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.snd measurable_snd i)
    (macAmbient_pairwise_coord p₁ p₂ W id measurable_id)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W id measurable_id i)
    hε_pos
  have h_aep_real : Filter.Tendsto
      (fun n : ℕ ↦ (μ {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
          macJointlyTypicalSet μ macX1s macX2s macYs n ε}).toReal)
      Filter.atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (a := (1 : ℝ≥0∞)) (by simp)).comp h_aep
    simpa [Function.comp_def] using h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (h_aep_real.eventually (eventually_gt_nhds (show (1 : ℝ) - ε' / 2 < 1 by linarith)))
  -- (N₁) exponential decay of the user-1 alias term.
  obtain ⟨N₁, hN₁⟩ := channelCoding_E2_lt_of_rate (I := macInfo₁ p₁ p₂ W) (R := R₁)
    (ε := ε) (ε' := ε' / 2) hgap1 hε'2
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N₁ ≤ n := le_trans (le_max_right _ _) hn
  set M₁ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₁)) with hM₁_def
  have hM₁_pos : 0 < M₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  -- The two-codebook average bound with `M₂ = 1`; the `(M₂ - 1)` alias terms vanish.
  have h_avg_bound := mac_random_codebook_average_le (M₁ := M₁) (M₂ := 1) (n := n)
    p₁ p₂ W hp₁ hp₂ hW hM₁_pos Nat.one_pos hε_pos
  simp only [Nat.cast_one, sub_self, zero_mul, mul_zero, add_zero] at h_avg_bound
  -- Bound the two surviving terms.
  have hE0 : μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
      macJointlyTypicalSet μ macX1s macX2s macYs n ε} ≤ ε' / 2 := by
    have h_meas_good : MeasurableSet
        {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
            macJointlyTypicalSet μ macX1s macX2s macYs n ε} := by
      have h_meas_triple : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
          (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
        (measurable_jointRV (α := α₁) macX1s measurable_macX1s n).prodMk
          ((measurable_jointRV (α := α₂) macX2s measurable_macX2s n).prodMk
            (measurable_jointRV (α := β) macYs measurable_macYs n))
      exact h_meas_triple (measurableSet_macJointlyTypicalSet μ macX1s macX2s macYs n ε)
    exact InformationTheory.Shannon.ChannelCoding.complementProbReal_le_of_one_sub_le
      h_meas_good (le_of_lt (hN₀ n hn0))
  have hE1 : ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)) < ε' / 2 := by
    have := hN₁ n hn1
    rwa [hM₁_def]
  have hRHS_lt :
      μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
            macJointlyTypicalSet μ macX1s macX2s macYs n ε}
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)) < ε' := by
    linarith
  -- Pigeonhole to a deterministic codebook pair, then package the code (a `MACCode M₁ 1 n`).
  obtain ⟨c₁, c₂, hcb⟩ := mac_exists_codebook_le_avg μ macX1s macX2s macYs W p₁ p₂
    hM₁_pos Nat.one_pos _ h_avg_bound
  refine ⟨M₁, 1, le_refl _, ?_,
    macCodebookToCode μ macX1s macX2s macYs hM₁_pos Nat.one_pos ε c₁ c₂, ?_⟩
  · rw [mul_zero, Real.exp_zero, Nat.ceil_one]
  · exact lt_of_le_of_lt hcb hRHS_lt

/-! ## Each pentagon lies in the capacity region -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- Every rate pair of a full-support product input's pentagon lies in the capacity region.
Strictly-interior points are directly achievable (`mac_strict_interior_achievable`); every
other point is a limit of interior points via a convex combination toward an interior
witness.
@audit:ok -/
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
  · -- Degenerate pentagon: some `macInfo ≤ 0`, forcing a rate coordinate to `0`.
    have hcases : macInfo₁ p₁ p₂ W ≤ 0 ∨ macInfo₂ p₁ p₂ W ≤ 0 ∨ macInfoBoth p₁ p₂ W ≤ 0 := by
      by_contra h
      simp only [not_or, not_le] at h
      exact hpos h
    rcases hcases with h1 | h2 | hb
    · -- `macInfo₁ ≤ 0` ⇒ `R.1 = 0`: user 1 is silent and user 2 achieves any rate below
      -- `macInfo₂`.  Although the `R₁ < macInfo₁` corner of `mac_achievability` as-stated is
      -- empty here, the point is achievable via its `M₁ = 1` internal specialisation
      -- (`mac_axis1_achievable`): every strictly-smaller perturbation `(−ε, R.2 − ε)` reduces
      -- to `MACAchievable W 0 (R.2 − ε)` (with `R.2 − ε < macInfo₂`) by monotonicity, so `R`
      -- is a limit of achievable points.
      have hR1zero : R.1 = 0 := le_antisymm (hR1le.trans h1) hR1nn
      refine mac_mem_closure_of_strictly_below W R (fun ε hε => ?_)
      have hax : MACAchievable W 0 (R.2 - ε) :=
        mac_axis1_achievable p₁ p₂ W hp₁ hp₂ hW (by linarith [hR2le])
      exact mac_achievable_mono hax (by rw [hR1zero]; linarith) le_rfl
    · -- `macInfo₂ ≤ 0` ⇒ `R.2 = 0`: symmetric single-user achievability with user 2 silent,
      -- via the `M₂ = 1` internal specialisation `mac_axis2_achievable`.
      have hR2zero : R.2 = 0 := le_antisymm (hR2le.trans h2) hR2nn
      refine mac_mem_closure_of_strictly_below W R (fun ε hε => ?_)
      have hax : MACAchievable W (R.1 - ε) 0 :=
        mac_axis2_achievable p₁ p₂ W hp₁ hp₂ hW (by linarith [hR1le])
      exact mac_achievable_mono hax le_rfl (by rw [hR2zero]; linarith)
    · -- `macInfoBoth ≤ 0` ⇒ `R = (0, 0)`: the trivial single-message code is achievable.
      have hsum0 : R.1 + R.2 ≤ 0 := hRsumle.trans hb
      have hR1zero : R.1 = 0 := le_antisymm (by linarith) hR1nn
      have hR2zero : R.2 = 0 := le_antisymm (by linarith) hR2nn
      have hach : MACAchievable W R.1 R.2 := by
        rw [hR1zero, hR2zero]; exact mac_achievable_zero_zero W
      exact subset_closure hach

/-! ## Achievability headline: the closed convex hull of the pentagons -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **MAC time-sharing achievability (convex-hull form, Cover–Thomas Theorem 15.3.1).**  The
closed convex hull of the per-input pentagons of full-support product inputs is contained in
the operational capacity region.
@audit:ok -/
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

/-! ## All-probability upgrade of achievability

The headline `mac_achievability_region` above only covers the closed convex hull of the
pentagons of *full-support* product inputs.  The converse half exposes per-letter marginals
`μ.map (encoder)` that are probability measures but generally not full-support, so closing the
full time-sharing region requires the achievability side to cover the closed convex hull of the
pentagons of *all* probability inputs.  This is obtained by smoothing an arbitrary probability
input toward a fixed uniform anchor, `p ↦ (1 - ε) • p + ε • uniform`, and passing to the limit
`ε → 0⁺` using continuity of the corner informations in the mixing parameter. -/

/-- The clamped mixing weight `min 1 (max 0 ε) ∈ [0, 1]`, used to keep the smoothed input a
probability measure for every real `ε` while agreeing with `ε` on `[0, 1]`. -/
noncomputable def macMixWeight (ε : ℝ) : ℝ := min 1 (max 0 ε)

lemma macMixWeight_nonneg (ε : ℝ) : 0 ≤ macMixWeight ε :=
  le_min zero_le_one (le_max_left 0 ε)

lemma macMixWeight_le_one (ε : ℝ) : macMixWeight ε ≤ 1 := min_le_left _ _

lemma macMixWeight_zero : macMixWeight 0 = 0 := by simp [macMixWeight]

lemma macMixWeight_pos {ε : ℝ} (hε : 0 < ε) : 0 < macMixWeight ε :=
  lt_min zero_lt_one (lt_of_lt_of_le hε (le_max_right 0 ε))

lemma macMixWeight_continuous : Continuous macMixWeight :=
  continuous_const.min (continuous_const.max continuous_id)

section Perturbation
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The smoothing of a probability input `p` toward a fixed anchor `μ₀`:
`macMix p μ₀ ε = (1 - macMixWeight ε) • p + macMixWeight ε • μ₀`.  For `ε ∈ (0, 1]` and a
full-support anchor `μ₀`, this is a full-support probability measure; at `ε = 0` it is `p`. -/
noncomputable def macMix (p μ₀ : Measure X) (ε : ℝ) : Measure X :=
  ENNReal.ofReal (1 - macMixWeight ε) • p + ENNReal.ofReal (macMixWeight ε) • μ₀

instance macMix.instIsProbabilityMeasure (p μ₀ : Measure X) [IsProbabilityMeasure p]
    [IsProbabilityMeasure μ₀] (ε : ℝ) : IsProbabilityMeasure (macMix p μ₀ ε) := by
  refine ⟨?_⟩
  unfold macMix
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [macMixWeight_le_one ε]) (macMixWeight_nonneg ε),
    show (1 - macMixWeight ε) + macMixWeight ε = 1 by ring, ENNReal.ofReal_one]

omit [MeasurableSingletonClass X] in
lemma macMix_zero (p μ₀ : Measure X) : macMix p μ₀ 0 = p := by
  unfold macMix
  rw [macMixWeight_zero]
  simp

omit [MeasurableSingletonClass X] in
lemma macMix_real_apply (p μ₀ : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure μ₀]
    (ε : ℝ) (a : X) :
    (macMix p μ₀ ε).real {a}
      = (1 - macMixWeight ε) * p.real {a} + macMixWeight ε * μ₀.real {a} := by
  unfold macMix
  rw [measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [macMixWeight_le_one ε]),
    ENNReal.toReal_ofReal (macMixWeight_nonneg ε)]
  rfl

omit [MeasurableSingletonClass X] in
lemma macMix_full_support (p μ₀ : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure μ₀]
    (hμ₀ : ∀ a : X, 0 < μ₀.real {a}) {ε : ℝ} (hε : 0 < ε) (a : X) :
    0 < (macMix p μ₀ ε).real {a} := by
  rw [macMix_real_apply]
  have h1 : 0 ≤ (1 - macMixWeight ε) * p.real {a} :=
    mul_nonneg (by linarith [macMixWeight_le_one ε]) measureReal_nonneg
  have h2 : 0 < macMixWeight ε * μ₀.real {a} := mul_pos (macMixWeight_pos hε) (hμ₀ a)
  linarith

omit [MeasurableSingletonClass X] in
lemma macMix_real_continuous (p μ₀ : Measure X) [IsProbabilityMeasure p] [IsProbabilityMeasure μ₀]
    (a : X) : Continuous (fun ε : ℝ => (macMix p μ₀ ε).real {a}) := by
  have hrw : (fun ε : ℝ => (macMix p μ₀ ε).real {a})
      = (fun ε : ℝ => (1 - macMixWeight ε) * p.real {a} + macMixWeight ε * μ₀.real {a}) := by
    funext ε; exact macMix_real_apply p μ₀ ε a
  rw [hrw]
  exact ((continuous_const.sub macMixWeight_continuous).mul continuous_const).add
    (macMixWeight_continuous.mul continuous_const)

end Perturbation

omit [DecidableEq α₁] [Nonempty α₁] [DecidableEq α₂] [Nonempty α₂] [DecidableEq β] [Nonempty β] in
/-- Singleton mass of a pushforward as a finite fibre sum. -/
lemma map_real_singleton_fiber_sum {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [DecidableEq γ] (μ : Measure (α₁ × α₂ × β)) [SigmaFinite μ]
    (f : α₁ × α₂ × β → γ) (hf : Measurable f) (x : γ) :
    (μ.map f).real {x}
      = ∑ q ∈ Finset.univ.filter (fun q => f q = x), μ.real {q} := by
  rw [map_measureReal_apply hf (measurableSet_singleton x)]
  have hset : f ⁻¹' {x} = ↑(Finset.univ.filter (fun q => f q = x)) := by
    ext q; simp [Set.mem_preimage, Finset.coe_filter]
  rw [hset, sum_measureReal_singleton]

lemma macMixJoint_real_continuous
    (p₁ μ₀₁ : Measure α₁) [IsProbabilityMeasure p₁] [IsProbabilityMeasure μ₀₁]
    (p₂ μ₀₂ : Measure α₂) [IsProbabilityMeasure p₂] [IsProbabilityMeasure μ₀₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (q : α₁ × α₂ × β) :
    Continuous (fun ε : ℝ =>
      (macJointDistribution (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W).real {q}) := by
  obtain ⟨a₁, a₂, b⟩ := q
  have hrw : (fun ε : ℝ =>
      (macJointDistribution (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W).real {(a₁, a₂, b)})
      = (fun ε : ℝ =>
        (macMix p₁ μ₀₁ ε).real {a₁} * (macMix p₂ μ₀₂ ε).real {a₂} * (W (a₁, a₂)).real {b}) := by
    funext ε
    exact macJointDistribution_triple_singleton (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W a₁ a₂ b
  rw [hrw]
  exact ((macMix_real_continuous p₁ μ₀₁ a₁).mul
    (macMix_real_continuous p₂ μ₀₂ a₂)).mul continuous_const

lemma macMixJoint_map_real_continuous {γ : Type*} [Fintype γ] [DecidableEq γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (p₁ μ₀₁ : Measure α₁) [IsProbabilityMeasure p₁] [IsProbabilityMeasure μ₀₁]
    (p₂ μ₀₂ : Measure α₂) [IsProbabilityMeasure p₂] [IsProbabilityMeasure μ₀₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (f : α₁ × α₂ × β → γ) (hf : Measurable f) (x : γ) :
    Continuous (fun ε : ℝ =>
      ((macJointDistribution (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W).map f).real {x}) := by
  have hrw : (fun ε : ℝ =>
      ((macJointDistribution (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W).map f).real {x})
      = (fun ε : ℝ => ∑ q ∈ Finset.univ.filter (fun q => f q = x),
        (macJointDistribution (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W).real {q}) := by
    funext ε
    exact map_real_singleton_fiber_sum _ f hf x
  rw [hrw]
  exact continuous_finsetSum _ (fun q _ => macMixJoint_real_continuous p₁ μ₀₁ p₂ μ₀₂ W q)

lemma macMix_entropy_continuous {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (p₁ μ₀₁ : Measure α₁) [IsProbabilityMeasure p₁] [IsProbabilityMeasure μ₀₁]
    (p₂ μ₀₂ : Measure α₂) [IsProbabilityMeasure p₂] [IsProbabilityMeasure μ₀₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (f : α₁ × α₂ × β → γ) (hf : Measurable f) :
    Continuous (fun ε : ℝ =>
      entropy (macJointDistribution (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W) f) := by
  unfold entropy
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_negMulLog.comp (macMixJoint_map_real_continuous p₁ μ₀₁ p₂ μ₀₂ W f hf x))

lemma macInfo₁_perturb_continuous
    (p₁ μ₀₁ : Measure α₁) [IsProbabilityMeasure p₁] [IsProbabilityMeasure μ₀₁]
    (p₂ μ₀₂ : Measure α₂) [IsProbabilityMeasure p₂] [IsProbabilityMeasure μ₀₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    Continuous (fun ε : ℝ => macInfo₁ (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W) := by
  unfold macInfo₁
  exact ((macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W Prod.fst measurable_fst).add
    (macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W Prod.snd measurable_snd)).sub
    (macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W id measurable_id)

lemma macInfo₂_perturb_continuous
    (p₁ μ₀₁ : Measure α₁) [IsProbabilityMeasure p₁] [IsProbabilityMeasure μ₀₁]
    (p₂ μ₀₂ : Measure α₂) [IsProbabilityMeasure p₂] [IsProbabilityMeasure μ₀₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    Continuous (fun ε : ℝ => macInfo₂ (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W) := by
  unfold macInfo₂
  exact ((macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W (fun q => q.2.1)
      (measurable_fst.comp measurable_snd)).add
    (macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W (fun q => (q.1, q.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).sub
    (macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W id measurable_id)

lemma macInfoBoth_perturb_continuous
    (p₁ μ₀₁ : Measure α₁) [IsProbabilityMeasure p₁] [IsProbabilityMeasure μ₀₁]
    (p₂ μ₀₂ : Measure α₂) [IsProbabilityMeasure p₂] [IsProbabilityMeasure μ₀₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    Continuous (fun ε : ℝ => macInfoBoth (macMix p₁ μ₀₁ ε) (macMix p₂ μ₀₂ ε) W) := by
  unfold macInfoBoth
  exact ((macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W (fun q => (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
    (macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W (fun q => q.2.2)
      (measurable_snd.comp measurable_snd))).sub
    (macMix_entropy_continuous p₁ μ₀₁ p₂ μ₀₂ W id measurable_id)

lemma macInfo₁_nonneg (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    0 ≤ macInfo₁ p₁ p₂ W := by
  rw [macInfo₁_eq_mutualInfo_toReal]; exact ENNReal.toReal_nonneg

lemma macInfo₂_nonneg (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    0 ≤ macInfo₂ p₁ p₂ W := by
  rw [macInfo₂_eq_mutualInfo_toReal]; exact ENNReal.toReal_nonneg

lemma macInfoBoth_nonneg (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    0 ≤ macInfoBoth p₁ p₂ W := by
  rw [macInfoBoth_eq_mutualInfo_toReal]; exact ENNReal.toReal_nonneg

lemma sum_max_shift {x y M δ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 ≤ δ) (hM : x + y ≤ M) :
    max 0 (x - δ) + max 0 (y - δ) ≤ max 0 (M - δ) := by
  have hxle : x ≤ M := by linarith
  have hyle : y ≤ M := by linarith
  rcases le_or_gt (x - δ) 0 with hx' | hx' <;> rcases le_or_gt (y - δ) 0 with hy' | hy'
  · rw [max_eq_left hx', max_eq_left hy', add_zero]; exact le_max_left _ _
  · rw [max_eq_left hx', max_eq_right hy'.le, zero_add]
    exact le_max_of_le_right (by linarith)
  · rw [max_eq_right hx'.le, max_eq_left hy', add_zero]
    exact le_max_of_le_right (by linarith)
  · rw [max_eq_right hx'.le, max_eq_right hy'.le]
    exact le_max_of_le_right (by linarith)

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- Every rate pair of an arbitrary probability product input's pentagon lies in the capacity
region.  The full-support case is `mac_pentagon_subset_capacityRegion`; the general case
smooths the input toward the uniform anchor and passes to the limit. -/
theorem mac_pentagon_subset_capacityRegion_allprob
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b}) :
    macPentagon p₁ p₂ W ⊆ macCapacityRegion W := by
  classical
  intro R hR
  obtain ⟨hR1nn, hR2nn, hR1le, hR2le, hRsumle⟩ := hR
  -- Uniform full-support anchors.
  have hμ₀₁pos : ∀ a : α₁, 0 < ((PMF.uniformOfFintype α₁).toMeasure).real {a} := by
    intro a
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hμ₀₂pos : ∀ a : α₂, 0 < ((PMF.uniformOfFintype α₂).toMeasure).real {a} := by
    intro a
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  set μ₀₁ : Measure α₁ := (PMF.uniformOfFintype α₁).toMeasure with hμ₀₁
  set μ₀₂ : Measure α₂ := (PMF.uniformOfFintype α₂).toMeasure with hμ₀₂
  haveI : IsProbabilityMeasure μ₀₁ := by rw [hμ₀₁]; infer_instance
  haveI : IsProbabilityMeasure μ₀₂ := by rw [hμ₀₂]; infer_instance
  -- Smoothing sequence `εₖ = 1/(k+1) ∈ (0, 1]` tending to `0`.
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε_pos : ∀ k, 0 < ε k := fun k => by rw [hεdef]; positivity
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- Corner informations converge along the smoothing.
  have hAk : Tendsto (fun k => macInfo₁ (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W)
      atTop (𝓝 (macInfo₁ p₁ p₂ W)) := by
    have hc := (macInfo₁_perturb_continuous p₁ μ₀₁ p₂ μ₀₂ W).tendsto 0
    rw [macMix_zero, macMix_zero] at hc
    exact hc.comp hε_tendsto
  have hBk : Tendsto (fun k => macInfo₂ (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W)
      atTop (𝓝 (macInfo₂ p₁ p₂ W)) := by
    have hc := (macInfo₂_perturb_continuous p₁ μ₀₁ p₂ μ₀₂ W).tendsto 0
    rw [macMix_zero, macMix_zero] at hc
    exact hc.comp hε_tendsto
  have hCk : Tendsto (fun k => macInfoBoth (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W)
      atTop (𝓝 (macInfoBoth p₁ p₂ W)) := by
    have hc := (macInfoBoth_perturb_continuous p₁ μ₀₁ p₂ μ₀₂ W).tendsto 0
    rw [macMix_zero, macMix_zero] at hc
    exact hc.comp hε_tendsto
  -- Uniform shrink amount `gapₖ ≥ 0` bounding all three corner losses, tending to `0`.
  set gap : ℕ → ℝ := fun k =>
    max 0 (max (macInfo₁ p₁ p₂ W - macInfo₁ (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W)
      (max (macInfo₂ p₁ p₂ W - macInfo₂ (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W)
        (macInfoBoth p₁ p₂ W - macInfoBoth (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W)))
    with hgapdef
  have hgap_nn : ∀ k, 0 ≤ gap k := fun k => le_max_left _ _
  have hgap_tendsto : Tendsto gap atTop (𝓝 0) := by
    rw [hgapdef]
    have h1 := (tendsto_const_nhds (x := macInfo₁ p₁ p₂ W)).sub hAk
    have h2 := (tendsto_const_nhds (x := macInfo₂ p₁ p₂ W)).sub hBk
    have h3 := (tendsto_const_nhds (x := macInfoBoth p₁ p₂ W)).sub hCk
    simp only [sub_self] at h1 h2 h3
    simpa using (tendsto_const_nhds (x := (0 : ℝ))).max (h1.max (h2.max h3))
  -- Approximating points `Qₖ → R`, each in a full-support pentagon hence in the region.
  set Q : ℕ → ℝ × ℝ := fun k => (max 0 (R.1 - gap k), max 0 (R.2 - gap k)) with hQdef
  have hQmem : ∀ k, Q k ∈ macCapacityRegion W := by
    intro k
    have hgapA : macInfo₁ p₁ p₂ W
        - macInfo₁ (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W ≤ gap k := by
      rw [hgapdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hgapB : macInfo₂ p₁ p₂ W
        - macInfo₂ (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W ≤ gap k := by
      rw [hgapdef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hgapC : macInfoBoth p₁ p₂ W
        - macInfoBoth (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W ≤ gap k := by
      rw [hgapdef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    refine mac_pentagon_subset_capacityRegion (macMix p₁ μ₀₁ (ε k)) (macMix p₂ μ₀₂ (ε k)) W
      (fun a => macMix_full_support p₁ μ₀₁ hμ₀₁pos (hε_pos k) a)
      (fun a => macMix_full_support p₂ μ₀₂ hμ₀₂pos (hε_pos k) a) hW ?_
    refine ⟨le_max_left _ _, le_max_left _ _, ?_, ?_, ?_⟩
    · exact max_le (macInfo₁_nonneg _ _ _) (by linarith)
    · exact max_le (macInfo₂_nonneg _ _ _) (by linarith)
    · exact le_trans (sum_max_shift hR1nn hR2nn (hgap_nn k) hRsumle)
        (max_le (macInfoBoth_nonneg _ _ _) (by linarith))
  have hQ_tendsto : Tendsto Q atTop (𝓝 R) := by
    rw [hQdef]
    have hg1 : Tendsto (fun k => R.1 - gap k) atTop (𝓝 R.1) := by
      simpa using (tendsto_const_nhds (x := R.1)).sub hgap_tendsto
    have hg2 : Tendsto (fun k => R.2 - gap k) atTop (𝓝 R.2) := by
      simpa using (tendsto_const_nhds (x := R.2)).sub hgap_tendsto
    have hm1 : Tendsto (fun k => max 0 (R.1 - gap k)) atTop (𝓝 (max 0 R.1)) :=
      (tendsto_const_nhds (x := (0 : ℝ))).max hg1
    have hm2 : Tendsto (fun k => max 0 (R.2 - gap k)) atTop (𝓝 (max 0 R.2)) :=
      (tendsto_const_nhds (x := (0 : ℝ))).max hg2
    rw [max_eq_right hR1nn] at hm1
    rw [max_eq_right hR2nn] at hm2
    have := hm1.prodMk_nhds hm2
    rwa [Prod.mk.eta] at this
  exact (mac_capacityRegion_isClosed W).mem_of_tendsto hQ_tendsto (Eventually.of_forall hQmem)

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **MAC time-sharing achievability (convex-hull form, all-probability inputs).**  The closed
convex hull of the per-input pentagons of *all* probability product inputs is contained in the
operational capacity region.  Upgrades `mac_achievability_region` from full-support inputs. -/
@[entry_point]
theorem mac_achievability_region_allprob (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b}) :
    closedConvexHull ℝ
      (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂) (_ : IsProbabilityMeasure p₁)
         (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W)
      ⊆ macCapacityRegion W := by
  refine closedConvexHull_min ?_ (mac_capacityRegion_convex W) (mac_capacityRegion_isClosed W)
  simp only [Set.iUnion_subset_iff]
  intro p₁ p₂ hp₁inst hp₂inst
  haveI := hp₁inst
  haveI := hp₂inst
  exact mac_pentagon_subset_capacityRegion_allprob p₁ p₂ W hW

end InformationTheory.Shannon.MAC
