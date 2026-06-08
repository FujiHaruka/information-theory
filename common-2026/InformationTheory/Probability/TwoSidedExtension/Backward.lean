import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Dynamics.Ergodic.Ergodic
import InformationTheory.Probability.TwoSidedExtension.Core

namespace InformationTheory.Shannon.TwoSided

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology symmDiff

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase G — forward filtration of finite past + `pmfLogCond` Levy

The forward filtration is the monotone (in `ℕ`) family of σ-algebras `pastSigma k`
of events depending only on the **finite past** `{coord_i : -k ≤ i ≤ -1}` of length
`k`. As `k → ∞`, the filtration's `⨆`-limit is the σ-algebra
`cylinderEvents {i : ℤ | i ≤ -1}` of the **infinite negative past**.

This is the shape needed by **`MeasureTheory.Integrable.tendsto_ae_condExp`**
(forward Lévy upward convergence): if `g` is `(⨆ k, ℱ k)`-strongly measurable
and integrable, then `μ[g | ℱ k] → g` a.s.

For each `a : α`, the real-valued process
`condProbPast a k := μZ[ (coord0 ⁻¹' {a}).indicator (1 : (ℤ→α)→ℝ) | pastFiltration k ]`
is a martingale (via `martingale_condExp`). The infinite-past conditional
probability `condProbInfty a` is defined directly as the conditional
expectation with respect to `⨆ k, pastFiltration k`; forward Lévy then gives
`condProbPast a k → condProbInfty a` a.s.

The per-step conditional log-likelihood is then
`pmfLogCondPast k ω := -log ( ∑ a, indicator(coord0 ω = a) * condProbPast a k ω )`,
which collapses pointwise to `-log condProbPast (coord0 ω) k ω`.

The terminal integral identity
`∫ pmfLogCondInfty dμZ = entropyRate μ p` is the SMB bridge: it follows from
the per-step identity `∫ pmfLogCondPast k dμZ = conditionalEntropyTail μ p k`
(via the joint-law equality of Phase B's `shiftedMarginal`) and DCT pushed
through forward Lévy + `entropyRate_eq_lim_condEntropy`.
-/

section Backward

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The σ-algebra of events depending only on the finite past
`{coord_i : -k ≤ i ≤ -1}` of length `k`. For `k = 0` this is the trivial
σ-algebra (the set `{i | 0 ≤ i ∧ i ≤ -1}` is empty). -/
@[reducible] def pastSigma (k : ℕ) : MeasurableSpace (∀ _ : ℤ, α) :=
  cylinderEvents (X := fun _ : ℤ => α) {i : ℤ | -(k : ℤ) ≤ i ∧ i ≤ -1}

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- `pastSigma` is monotone in `k` (longer past = larger σ-algebra). -/
lemma pastSigma_mono : Monotone (pastSigma (α := α)) := by
  intro k₁ k₂ hk
  -- `{i | -k₁ ≤ i ∧ i ≤ -1} ⊆ {i | -k₂ ≤ i ∧ i ≤ -1}` because `-k₂ ≤ -k₁`.
  have hsub : {i : ℤ | -(k₁ : ℤ) ≤ i ∧ i ≤ -1} ⊆ {i : ℤ | -(k₂ : ℤ) ≤ i ∧ i ≤ -1} := by
    intro i ⟨h_lo, h_hi⟩
    refine ⟨?_, h_hi⟩
    have h_neg : -(k₂ : ℤ) ≤ -(k₁ : ℤ) :=
      neg_le_neg (by exact_mod_cast hk)
    exact le_trans h_neg h_lo
  exact cylinderEvents_mono (X := fun _ : ℤ => α) hsub

/-- The forward past filtration on `ℕ`: `pastFiltration k` is `pastSigma k`,
the σ-algebra of events depending on the finite past `{coord_i : -k ≤ i ≤ -1}`. -/
@[entry_point]
def pastFiltration : Filtration ℕ
    (MeasurableSpace.pi : MeasurableSpace (∀ _ : ℤ, α)) where
  seq k := pastSigma (α := α) k
  mono' _ _ hij := pastSigma_mono (α := α) hij
  le' _ := cylinderEvents_le_pi

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
@[simp] lemma pastFiltration_apply (k : ℕ) :
    (pastFiltration (α := α)) k = pastSigma (α := α) k := rfl

/-- The σ-algebra of events depending on the **infinite negative past**
`{coord_i : i ≤ -1}`. This is `⨆ k, pastSigma k`. -/
@[reducible] def negPastSigma : MeasurableSpace (∀ _ : ℤ, α) :=
  cylinderEvents (X := fun _ : ℤ => α) {i : ℤ | i ≤ -1}

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The supremum of the forward past filtration is the infinite negative past
σ-algebra.

Unfolds `cylinderEvents` as `⨆ i ∈ Δ, (m i).comap (· i)` and rearranges the
nested `iSup`s: for any `i ≤ -1`, `i ∈ [-k, -1]` for `k := (-i).toNat`. -/
lemma iSup_pastSigma_eq_negPastSigma :
    ⨆ k : ℕ, pastSigma (α := α) k = negPastSigma (α := α) := by
  -- Unfold both sides to the generator iSup form.
  -- LHS = ⨆ k, ⨆ i ∈ [-k,-1], (m_α).comap (· i)
  -- RHS = ⨆ i ≤ -1, (m_α).comap (· i)
  apply le_antisymm
  · -- LHS ⊆ RHS: each `pastSigma k` has indices ⊆ {i ≤ -1}.
    refine iSup_le (fun k => ?_)
    refine cylinderEvents_mono (X := fun _ : ℤ => α) ?_
    rintro i ⟨_, h_hi⟩
    exact h_hi
  · -- RHS ⊆ LHS: each generator at index `i ≤ -1` sits inside `pastSigma ((-i).toNat)`.
    -- Use the `cylinderEvents = ⨆ i ∈ Δ, ...` unfolding.
    show cylinderEvents (X := fun _ : ℤ => α) {i : ℤ | i ≤ -1}
        ≤ ⨆ k : ℕ, cylinderEvents (X := fun _ : ℤ => α)
            {i : ℤ | -(k : ℤ) ≤ i ∧ i ≤ -1}
    refine iSup₂_le (fun i hi => ?_)
    -- Goal: `(m_α).comap (· i) ≤ ⨆ k, pastSigma k`.
    set k : ℕ := (-i).toNat with hk_def
    have hi_neg : i ≤ -1 := hi
    have hi_le0 : i ≤ (0 : ℤ) := le_trans hi (by norm_num)
    have hk_eq : ((k : ℤ)) = -i :=
      Int.toNat_of_nonneg (neg_nonneg.mpr hi_le0)
    have h_lo : -(k : ℤ) ≤ i := by omega
    have h_hi : i ≤ -1 := hi
    -- `(m_α).comap (· i) ≤ pastSigma k` because `i ∈ [-k,-1]`.
    have h_in_pastSigma_k :
        ((inferInstance : MeasurableSpace α).comap (fun x : (∀ _ : ℤ, α) => x i))
          ≤ pastSigma (α := α) k := by
      change ((inferInstance : MeasurableSpace α).comap (fun x : (∀ _ : ℤ, α) => x i))
          ≤ ⨆ j ∈ ({i : ℤ | -(k : ℤ) ≤ i ∧ i ≤ -1} : Set ℤ),
              ((inferInstance : MeasurableSpace α).comap (fun x : (∀ _ : ℤ, α) => x j))
      exact le_iSup₂ (f := fun j _ =>
        ((inferInstance : MeasurableSpace α).comap (fun x : (∀ _ : ℤ, α) => x j))) i ⟨h_lo, h_hi⟩
    exact le_trans h_in_pastSigma_k (le_iSup (fun k : ℕ => pastSigma (α := α) k) k)

/-- The coordinate-0 evaluation. -/
def coord0 : (∀ _ : ℤ, α) → α := fun x => x 0

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The coordinate-0 map is measurable. -/
theorem measurable_coord0 : Measurable (coord0 : (∀ _ : ℤ, α) → α) :=
  measurable_pi_apply 0

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- The indicator of `{coord0 = a}` is bounded by `1`. -/
lemma indicator_coord0_eq_le_one (a : α) (x : (∀ _ : ℤ, α)) :
    ((coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))) x ≤ 1 := by
  by_cases hx : x ∈ (coord0 ⁻¹' {a})
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- The indicator of `{coord0 = a}` is nonneg. -/
lemma indicator_coord0_eq_nonneg (a : α) (x : (∀ _ : ℤ, α)) :
    0 ≤ ((coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))) x := by
  by_cases hx : x ∈ (coord0 ⁻¹' {a})
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

omit [Fintype α] [DecidableEq α] [Nonempty α] [IsProbabilityMeasure μ] in
/-- The set `{coord0 = a}` is measurable. -/
lemma measurableSet_coord0_eq (a : α) :
    MeasurableSet (coord0 ⁻¹' {a} : Set (∀ _ : ℤ, α)) :=
  measurable_coord0 (measurableSet_singleton a)

omit [DecidableEq α] [Nonempty α] in
/-- The indicator function `(coord0 ⁻¹' {a}).indicator 1` is integrable under `μZ`. -/
lemma integrable_indicator_coord0_eq (a : α) :
    Integrable ((coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))) (μZ μ p) := by
  refine (integrable_indicator_iff (measurableSet_coord0_eq (α := α) a)).mpr ?_
  exact integrableOn_const

/-- The real-valued forward conditional probability of `{coord0 = a}` given
the finite past `pastFiltration k`, viewed as a function on `ℤ → α`. -/
@[entry_point]
noncomputable def condProbPast (a : α) (k : ℕ) : (∀ _ : ℤ, α) → ℝ :=
  (μZ μ p)[((coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)))
    | (pastFiltration (α := α)) k]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- For each `a : α`, `condProbPast a` is a (forward) martingale w.r.t. the past
filtration. -/
@[entry_point]
lemma martingale_condProbPast (a : α) :
    Martingale (fun k : ℕ => (μZ μ p)[((coord0 ⁻¹' {a}).indicator
        (fun _ => (1 : ℝ))) | (pastFiltration (α := α)) k])
      (pastFiltration (α := α)) (μZ μ p) :=
  martingale_condExp _ _ _

/-- The infinite-past conditional probability of `{coord0 = a}` given
`⨆ k, pastFiltration k`. -/
@[entry_point]
noncomputable def condProbInfty (a : α) : (∀ _ : ℤ, α) → ℝ :=
  (μZ μ p)[((coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)))
    | ⨆ k : ℕ, (pastFiltration (α := α)) k]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Forward Lévy upward convergence**: `condProbPast a k → condProbInfty a` a.s.
as `k → ∞`. Direct application of
`MeasureTheory.Integrable.tendsto_ae_condExp` (Lévy's upward theorem). -/
@[entry_point]
lemma condProbPast_tendsto_condProbInfty (a : α) :
    ∀ᵐ x ∂(μZ μ p),
      Tendsto (fun k : ℕ => condProbPast μ p a k x) atTop
        (𝓝 (condProbInfty μ p a x)) := by
  -- `tendsto_ae_condExp` gives `μ[g | ℱ k] → μ[g | ⨆ k, ℱ k]` a.s. for any `g`.
  exact MeasureTheory.tendsto_ae_condExp (ℱ := pastFiltration (α := α))
    (μ := μZ μ p) (m0 := MeasurableSpace.pi)
    ((coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `condProbPast a k` is integrable. -/
@[entry_point]
lemma integrable_condProbPast (a : α) (k : ℕ) :
    Integrable (condProbPast μ p a k) (μZ μ p) :=
  integrable_condExp

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `condProbPast a k` is strongly measurable w.r.t. `pastFiltration k`. -/
lemma stronglyMeasurable_condProbPast (a : α) (k : ℕ) :
    StronglyMeasurable[(pastFiltration (α := α)) k]
      (condProbPast μ p a k) :=
  stronglyMeasurable_condExp

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `condProbInfty a` is `⨆ k, pastFiltration k`-strongly measurable. -/
lemma stronglyMeasurable_condProbInfty (a : α) :
    StronglyMeasurable[⨆ n : ℕ, (pastFiltration (α := α)) n]
      (condProbInfty μ p a) :=
  stronglyMeasurable_condExp

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `condProbPast a k ≥ 0` a.s. -/
lemma ae_zero_le_condProbPast (a : α) (k : ℕ) :
    0 ≤ᵐ[μZ μ p] condProbPast μ p a k := by
  refine condExp_nonneg ?_
  filter_upwards with x
  exact indicator_coord0_eq_nonneg a x

omit [DecidableEq α] [Nonempty α] in
/-- `condProbPast a k ≤ 1` a.s. -/
lemma ae_condProbPast_le_one (a : α) (k : ℕ) :
    condProbPast μ p a k ≤ᵐ[μZ μ p] (fun _ => (1 : ℝ)) := by
  have h_mono :
      (μZ μ p)[(coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))
          | (pastFiltration (α := α)) k]
        ≤ᵐ[μZ μ p] (μZ μ p)[(fun _ : (∀ _ : ℤ, α) => (1 : ℝ))
          | (pastFiltration (α := α)) k] := by
    refine condExp_mono (integrable_indicator_coord0_eq μ p a)
      (integrable_const _) ?_
    filter_upwards with x
    exact indicator_coord0_eq_le_one a x
  have h_const_eq :
      (μZ μ p)[(fun _ : (∀ _ : ℤ, α) => (1 : ℝ))
          | (pastFiltration (α := α)) k]
        = fun _ => (1 : ℝ) :=
    condExp_const ((pastFiltration (α := α)).le _) 1
  filter_upwards [h_mono] with x hx
  have := hx
  rw [h_const_eq] at this
  exact this

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `condProbInfty a ≥ 0` a.s. -/
lemma ae_zero_le_condProbInfty (a : α) :
    0 ≤ᵐ[μZ μ p] condProbInfty μ p a := by
  have h_tendsto := condProbPast_tendsto_condProbInfty μ p a
  -- For each x in the AE-set, we have `condProbPast a k x → condProbInfty a x` and each
  -- `condProbPast a k x ≥ 0` a.s. Pick a fixed `k = 0` AE-set and pass to limit.
  have h_nn : ∀ᵐ x ∂(μZ μ p), ∀ k : ℕ, 0 ≤ condProbPast μ p a k x := by
    rw [ae_all_iff]; exact fun k => ae_zero_le_condProbPast μ p a k
  filter_upwards [h_tendsto, h_nn] with x hx_lim hx_nn
  exact ge_of_tendsto' hx_lim hx_nn

omit [DecidableEq α] [Nonempty α] in
/-- `condProbInfty a ≤ 1` a.s. -/
lemma ae_condProbInfty_le_one (a : α) :
    condProbInfty μ p a ≤ᵐ[μZ μ p] (fun _ => (1 : ℝ)) := by
  have h_tendsto := condProbPast_tendsto_condProbInfty μ p a
  have h_le : ∀ᵐ x ∂(μZ μ p), ∀ k : ℕ, condProbPast μ p a k x ≤ 1 := by
    rw [ae_all_iff]; exact fun k => ae_condProbPast_le_one μ p a k
  filter_upwards [h_tendsto, h_le] with x hx_lim hx_le
  exact le_of_tendsto' hx_lim hx_le

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `condProbInfty a` is by definition the conditional expectation of the indicator
`1_{coord0=a}` w.r.t. the σ-algebra `⨆ k, pastFiltration k` of the infinite past. -/
lemma condProbInfty_eq_condExp_tail (a : α) :
    condProbInfty μ p a =ᵐ[μZ μ p]
      (μZ μ p)[(coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))
        | ⨆ n : ℕ, (pastFiltration (α := α)) n] := by
  exact Filter.EventuallyEq.refl _ _

/-- Per-step conditional log-likelihood under `μZ` conditioned on `pastSigma k`.

Defined as `-log (∑ a, indicator(coord0 = a) * condProbPast a k)`. On the
full-measure set where the conditional probability of the actual `coord0` value
is positive, this is `-log condProbPast (coord0 x) k x`. -/
@[entry_point]
noncomputable def pmfLogCondPast (k : ℕ) : (∀ _ : ℤ, α) → ℝ := fun x =>
  -Real.log (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
    * condProbPast μ p a k x)

/-- Limit log-likelihood (conditional on the full backward tail). -/
@[entry_point]
noncomputable def pmfLogCondInfty : (∀ _ : ℤ, α) → ℝ := fun x =>
  -Real.log (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
    * condProbInfty μ p a x)

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- Per-step (and limit) inner sum simplifies to a single conditional probability
of the realized coord-0 value. -/
lemma pmfLogCondPast_inner_eq_self (f : α → ℝ) (x : (∀ _ : ℤ, α)) :
    (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x * f a)
      = f (coord0 x) := by
  classical
  have hmem : (coord0 x) ∈ (Finset.univ : Finset α) := Finset.mem_univ _
  rw [Finset.sum_eq_single (coord0 x)]
  · have hin : x ∈ coord0 ⁻¹' {coord0 x} := rfl
    rw [Set.indicator_of_mem hin]
    ring
  · intro a _ hne
    have hnotmem : x ∉ coord0 ⁻¹' {a} := fun hx => hne hx.symm
    simp [Set.indicator_of_notMem hnotmem]
  · intro hne; exact absurd hmem hne

end Backward

end InformationTheory.Shannon.TwoSided
