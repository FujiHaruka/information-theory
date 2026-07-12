import InformationTheory.Shannon.RateDistortion.AchievabilityUnconditional

/-!
# Rate-distortion achievability — general (arbitrary) source

The unconditional operational achievability theorem
`rate_distortion_achievability_operational` carries a full-support regularity
precondition `hP_supp : ∀ a, 0 < P_X a`. This file removes it: the general
version `rate_distortion_achievability_operational_general` holds for any source
pmf `P_X ∈ stdSimplex ℝ α`.

## Approach

Restrict to the support subtype `α' := {a // 0 < P_X a}`, apply the full-support
theorem there, then lift the resulting lossy code back to the whole alphabet.

* A feasible joint pmf `q ∈ RDConstraint P_X d D` vanishes off the support
  (`marginalFst q = P_X` with `q ≥ 0` forces `q (a, b) = 0` when `P_X a = 0`).
  Hence the restriction/padding maps between joint pmfs on `α × β` and `α' × β`
  are mutually inverse on feasible sets and preserve `mutualInfoPmf`,
  `expectedDistortionPmf`, and `marginalFst` (`negMulLog 0 = 0`).
* Therefore `rateDistortionFunctionPmf` agrees on `α` and `α'`, the hypotheses
  transport, and the full-support theorem produces a code `c'` on `α'`.
* A retraction `r : α → α'` (identity on the support, a fixed default off it)
  lifts `c'` to a code on `α`. The source measure never charges the off-support
  symbols, so the expected block distortion is unchanged.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter Real
open InformationTheory.Shannon.ChannelCoding
  (pmfToMeasure pmfToMeasure_apply_singleton pmfToMeasure_isProbabilityMeasure
   pmfToMeasure_real_singleton)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-! ## Support subtype, restriction, and padding -/

/-- Source pmf restricted to the support subtype. -/
noncomputable abbrev rdSupportPmf (P_X : α → ℝ) : {a // 0 < P_X a} → ℝ :=
  fun a' ↦ P_X a'.val

/-- Distortion function restricted to the support subtype. -/
noncomputable abbrev rdSupportDist (P_X : α → ℝ) (d : DistortionFn α β) :
    DistortionFn {a // 0 < P_X a} β :=
  fun a' b ↦ d a'.val b

/-- Restrict a joint pmf on `α × β` to the support subtype `α' × β`. -/
noncomputable def rdRestrict (P_X : α → ℝ) (q : α × β → ℝ) :
    {a // 0 < P_X a} × β → ℝ :=
  fun p ↦ q (p.1.val, p.2)

/-- Pad a joint pmf on `α' × β` back to `α × β` by zero off the support. -/
noncomputable def rdPad (P_X : α → ℝ) (q' : {a // 0 < P_X a} × β → ℝ) :
    α × β → ℝ :=
  fun p ↦ if h : 0 < P_X p.1 then q' (⟨p.1, h⟩, p.2) else 0

/-- Retraction of the whole alphabet onto the support subtype: the identity on
the support and a fixed default off it. -/
noncomputable def rdRetract (P_X : α → ℝ) (a₀ : {a // 0 < P_X a}) :
    α → {a // 0 < P_X a} :=
  fun a ↦ if h : 0 < P_X a then ⟨a, h⟩ else a₀

/-! ## G0: support-zero -/

/-- A feasible joint pmf vanishes on rows outside the source support. -/
lemma rd_support_row_zero {q : α × β → ℝ} (hq : q ∈ stdSimplex ℝ (α × β))
    {P_X : α → ℝ} (hmarg : marginalFst q = P_X) {a : α} (ha : ¬ 0 < P_X a) (b : β) :
    q (a, b) = 0 := by
  have hnn : ∀ p, 0 ≤ q p := hq.1
  have hsum : ∑ b, q (a, b) = P_X a := congrFun hmarg a
  have hPa_nn : 0 ≤ P_X a := by
    rw [← hsum]; exact Finset.sum_nonneg (fun b _ ↦ hnn (a, b))
  have hPa : P_X a = 0 := le_antisymm (not_lt.mp ha) hPa_nn
  have hsum0 : ∑ b, q (a, b) = 0 := by rw [hsum, hPa]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ hnn (a, b))).mp hsum0 b (Finset.mem_univ b)

/-- There is a symbol in the support of any source pmf. -/
lemma rd_support_nonempty (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α) :
    ∃ a, 0 < P_X a := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hz : ∀ a, P_X a = 0 := fun a ↦ le_antisymm (h a) (hP_pmf.1 a)
  have hsum0 : (∑ a, P_X a) = 0 := Finset.sum_eq_zero (fun a _ ↦ hz a)
  rw [hP_pmf.2] at hsum0
  exact one_ne_zero hsum0

/-! ## G1: finite-sum transfer between `α` and the support subtype -/

/-- Sum transfer: a function vanishing off the support has equal sums over `α`
and over the support subtype. -/
lemma rd_sum_support_transfer (P_X : α → ℝ) (F : α → ℝ)
    (hF : ∀ a, ¬ (0 < P_X a) → F a = 0) :
    ∑ a : α, F a = ∑ a : {a // 0 < P_X a}, F a.val := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a ↦ 0 < P_X a))
        (fun x ↦ by simp) F]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro a _ ha
  exact hF a (by simpa using ha)

/-- Product sum transfer: a function vanishing on off-support rows has equal
sums over `α × β` and over `α' × β`. -/
lemma rd_sum_prod_support_transfer (P_X : α → ℝ) (G : α × β → ℝ)
    (hG : ∀ a b, ¬ (0 < P_X a) → G (a, b) = 0) :
    ∑ p : α × β, G p = ∑ p : {a // 0 < P_X a} × β, G (p.1.val, p.2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  exact rd_sum_support_transfer P_X (fun a ↦ ∑ b, G (a, b))
    (fun a ha ↦ Finset.sum_eq_zero (fun b _ ↦ hG a b ha))

/-- Restriction then padding is the identity on feasible pmfs. -/
lemma rdRestrict_pad (P_X : α → ℝ) (q' : {a // 0 < P_X a} × β → ℝ) :
    rdRestrict P_X (rdPad P_X q') = q' := by
  funext p
  obtain ⟨a', b⟩ := p
  unfold rdRestrict rdPad
  rw [dif_pos a'.property]

/-- The first marginal of a restriction is the restriction of the first
marginal. -/
lemma marginalFst_rdRestrict (P_X : α → ℝ) (q : α × β → ℝ) (a' : {a // 0 < P_X a}) :
    marginalFst (rdRestrict P_X q) a' = marginalFst q a'.val := by
  simp only [marginalFst, rdRestrict]

/-- The second marginal is preserved under restriction of a support-zero pmf. -/
lemma marginalSnd_rdRestrict (P_X : α → ℝ) {q : α × β → ℝ}
    (hq_supp : ∀ a b, ¬ (0 < P_X a) → q (a, b) = 0) (b : β) :
    marginalSnd (rdRestrict P_X q) b = marginalSnd q b := by
  simp only [marginalSnd, rdRestrict]
  exact (rd_sum_support_transfer P_X (fun a ↦ q (a, b)) (fun a ha ↦ hq_supp a b ha)).symm

/-- Mutual information is preserved by restriction of a support-zero pmf. -/
lemma mutualInfoPmf_eq_restrict (P_X : α → ℝ) {q : α × β → ℝ}
    (hq_supp : ∀ a b, ¬ (0 < P_X a) → q (a, b) = 0) :
    mutualInfoPmf q = mutualInfoPmf (rdRestrict P_X q) := by
  have hmarg_zero : ∀ a, ¬ (0 < P_X a) → marginalFst q a = 0 := fun a ha ↦
    Finset.sum_eq_zero (fun b _ ↦ hq_supp a b ha)
  have h1 : (∑ a : α, Real.negMulLog (marginalFst q a))
      = ∑ a' : {a // 0 < P_X a}, Real.negMulLog (marginalFst (rdRestrict P_X q) a') := by
    rw [rd_sum_support_transfer P_X (fun a ↦ Real.negMulLog (marginalFst q a))
        (fun a ha ↦ by rw [hmarg_zero a ha, Real.negMulLog_zero])]
    exact Finset.sum_congr rfl (fun a' _ ↦ by rw [marginalFst_rdRestrict])
  have h2 : (∑ b : β, Real.negMulLog (marginalSnd q b))
      = ∑ b : β, Real.negMulLog (marginalSnd (rdRestrict P_X q) b) :=
    Finset.sum_congr rfl (fun b _ ↦ by rw [marginalSnd_rdRestrict P_X hq_supp])
  have h3 : (∑ p : α × β, Real.negMulLog (q p))
      = ∑ p : {a // 0 < P_X a} × β, Real.negMulLog (rdRestrict P_X q p) := by
    rw [rd_sum_prod_support_transfer P_X (fun p ↦ Real.negMulLog (q p))
        (fun a b ha ↦ by rw [hq_supp a b ha, Real.negMulLog_zero])]
    simp only [rdRestrict]
  simp only [mutualInfoPmf]
  rw [h1, h2, h3]

/-- Expected distortion is preserved by restriction of a support-zero pmf. -/
lemma expectedDistortionPmf_eq_restrict (P_X : α → ℝ) (d : DistortionFn α β)
    {q : α × β → ℝ} (hq_supp : ∀ a b, ¬ (0 < P_X a) → q (a, b) = 0) :
    expectedDistortionPmf d q = expectedDistortionPmf (rdSupportDist P_X d) (rdRestrict P_X q) := by
  simp only [expectedDistortionPmf]
  rw [rd_sum_support_transfer P_X (fun a ↦ ∑ b, q (a, b) * ((d a b : NNReal) : ℝ))
      (fun a ha ↦ Finset.sum_eq_zero (fun b _ ↦ by rw [hq_supp a b ha, zero_mul]))]
  simp only [rdRestrict, rdSupportDist]

/-! ## Membership transport -/

/-- Padding is support-zero by construction. -/
lemma rdPad_support_zero (P_X : α → ℝ) (q' : {a // 0 < P_X a} × β → ℝ)
    (a : α) (b : β) (ha : ¬ 0 < P_X a) : rdPad P_X q' (a, b) = 0 := by
  unfold rdPad
  rw [dif_neg ha]

/-- Restriction lands in the simplex. -/
lemma rdRestrict_mem_stdSimplex (P_X : α → ℝ) {q : α × β → ℝ}
    (hq : q ∈ stdSimplex ℝ (α × β)) (hq_supp : ∀ a b, ¬ (0 < P_X a) → q (a, b) = 0) :
    rdRestrict P_X q ∈ stdSimplex ℝ ({a // 0 < P_X a} × β) := by
  refine ⟨fun p ↦ hq.1 (p.1.val, p.2), ?_⟩
  simp only [rdRestrict]
  rw [← rd_sum_prod_support_transfer P_X q hq_supp]
  exact hq.2

/-- Padding lands in the simplex. -/
lemma rdPad_mem_stdSimplex (P_X : α → ℝ) {q' : {a // 0 < P_X a} × β → ℝ}
    (hq' : q' ∈ stdSimplex ℝ ({a // 0 < P_X a} × β)) :
    rdPad P_X q' ∈ stdSimplex ℝ (α × β) := by
  refine ⟨?_, ?_⟩
  · intro p
    unfold rdPad
    by_cases h : 0 < P_X p.1
    · rw [dif_pos h]; exact hq'.1 _
    · rw [dif_neg h]
  · have hkey : ∀ p' : {a // 0 < P_X a} × β, rdPad P_X q' (p'.1.val, p'.2) = q' p' :=
      fun p' ↦ congrFun (rdRestrict_pad P_X q') p'
    rw [rd_sum_prod_support_transfer P_X (rdPad P_X q')
        (fun a b ha ↦ rdPad_support_zero P_X q' a b ha)]
    rw [Finset.sum_congr rfl (fun p' _ ↦ hkey p')]
    exact hq'.2

/-- The first marginal of a restriction equals the restricted source pmf. -/
lemma marginalFst_rdRestrict_eq (P_X : α → ℝ) {q : α × β → ℝ}
    (hmarg : marginalFst q = P_X) :
    marginalFst (rdRestrict P_X q) = rdSupportPmf P_X := by
  funext a'
  rw [marginalFst_rdRestrict, hmarg]

/-- The first marginal of a padding equals the original source pmf. -/
lemma marginalFst_rdPad_eq (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    {q' : {a // 0 < P_X a} × β → ℝ}
    (hmarg' : marginalFst q' = rdSupportPmf P_X) :
    marginalFst (rdPad P_X q') = P_X := by
  funext a
  by_cases h : 0 < P_X a
  · change (∑ b, rdPad P_X q' (a, b)) = P_X a
    have hval : ∀ b, rdPad P_X q' (a, b) = q' (⟨a, h⟩, b) := fun b ↦ by
      unfold rdPad; rw [dif_pos h]
    rw [Finset.sum_congr rfl (fun b _ ↦ hval b)]
    have hm : marginalFst q' ⟨a, h⟩ = rdSupportPmf P_X ⟨a, h⟩ := congrFun hmarg' ⟨a, h⟩
    simp only [marginalFst] at hm
    rw [hm]
  · change (∑ b, rdPad P_X q' (a, b)) = P_X a
    rw [Finset.sum_congr rfl (fun b _ ↦ rdPad_support_zero P_X q' a b h), Finset.sum_const_zero]
    exact (le_antisymm (not_lt.mp h) (hP_pmf.1 a)).symm

/-- The restricted source pmf lies in the simplex of the support subtype. -/
lemma rdSupportPmf_mem_stdSimplex (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α) :
    rdSupportPmf P_X ∈ stdSimplex ℝ {a // 0 < P_X a} := by
  refine ⟨fun a' ↦ hP_pmf.1 a'.val, ?_⟩
  simp only [rdSupportPmf]
  rw [← rd_sum_support_transfer P_X P_X
    (fun a ha ↦ le_antisymm (not_lt.mp ha) (hP_pmf.1 a))]
  exact hP_pmf.2

/-! ## G2: rate-distortion function invariance -/

/-- Membership transports along restriction. -/
lemma rdRestrict_mem_constraint (P_X : α → ℝ) (d : DistortionFn α β) {D : ℝ}
    {q : α × β → ℝ} (hq : q ∈ RDConstraint P_X d D) :
    rdRestrict P_X q ∈ RDConstraint (rdSupportPmf P_X) (rdSupportDist P_X d) D := by
  obtain ⟨hq_simp, hq_marg, hq_dist⟩ := hq
  have hq_supp : ∀ a b, ¬ (0 < P_X a) → q (a, b) = 0 := fun a b ha ↦
    rd_support_row_zero hq_simp hq_marg ha b
  refine ⟨rdRestrict_mem_stdSimplex P_X hq_simp hq_supp, marginalFst_rdRestrict_eq P_X hq_marg, ?_⟩
  rw [← expectedDistortionPmf_eq_restrict P_X d hq_supp]
  exact hq_dist

/-- Membership transports along padding. -/
lemma rdPad_mem_constraint (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    (d : DistortionFn α β) {D : ℝ}
    {q' : {a // 0 < P_X a} × β → ℝ}
    (hq' : q' ∈ RDConstraint (rdSupportPmf P_X) (rdSupportDist P_X d) D) :
    rdPad P_X q' ∈ RDConstraint P_X d D := by
  obtain ⟨hq'_simp, hq'_marg, hq'_dist⟩ := hq'
  have hpad_supp : ∀ a b, ¬ (0 < P_X a) → rdPad P_X q' (a, b) = 0 := fun a b ha ↦
    rdPad_support_zero P_X q' a b ha
  refine ⟨rdPad_mem_stdSimplex P_X hq'_simp, marginalFst_rdPad_eq P_X hP_pmf hq'_marg, ?_⟩
  rw [expectedDistortionPmf_eq_restrict P_X d hpad_supp, rdRestrict_pad]
  exact hq'_dist

/-- The pmf-direct rate-distortion function is unchanged by support restriction. -/
lemma rd_function_eq (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    (d : DistortionFn α β) (D : ℝ) :
    rateDistortionFunctionPmf P_X d D
      = rateDistortionFunctionPmf (rdSupportPmf P_X) (rdSupportDist P_X d) D := by
  unfold rateDistortionFunctionPmf
  congr 1
  ext v
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨rdRestrict P_X q, rdRestrict_mem_constraint P_X d hq,
      (mutualInfoPmf_eq_restrict P_X (fun a b ha ↦ rd_support_row_zero hq.1 hq.2.1 ha b)).symm⟩
  · rintro ⟨q', hq', rfl⟩
    refine ⟨rdPad P_X q', rdPad_mem_constraint P_X hP_pmf d hq', ?_⟩
    rw [mutualInfoPmf_eq_restrict P_X (fun a b ha ↦ rdPad_support_zero P_X q' a b ha),
      rdRestrict_pad]

/-! ## G4: source measure charges only the support -/

/-- The source measure gives zero mass to the off-support symbols. -/
lemma pmfToMeasure_support_compl_null (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α) :
    pmfToMeasure P_X {a : α | ¬ 0 < P_X a} = 0 := by
  have hS : MeasurableSet {a : α | ¬ 0 < P_X a} := (Set.toFinite _).measurableSet
  unfold pmfToMeasure
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  by_cases ha : a ∈ {a : α | ¬ 0 < P_X a}
  · have hz : P_X a = 0 := le_antisymm (not_lt.mp ha) (hP_pmf.1 a)
    rw [hz, ENNReal.ofReal_zero, zero_mul]
  · rw [Set.indicator_of_notMem ha, mul_zero]

/-- Pushing the source measure through the support retraction yields the
restricted source pmf. -/
lemma pmfToMeasure_map_retract (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    (a₀ : {a // 0 < P_X a}) :
    (pmfToMeasure P_X).map (rdRetract P_X a₀) = pmfToMeasure (rdSupportPmf P_X) := by
  have hr_meas : Measurable (rdRetract P_X a₀) := measurable_of_finite _
  have hnull : pmfToMeasure P_X {a : α | ¬ 0 < P_X a} = 0 :=
    pmfToMeasure_support_compl_null P_X hP_pmf
  refine Measure.ext_of_singleton (fun b ↦ ?_)
  rw [Measure.map_apply hr_meas (measurableSet_singleton b)]
  have h1 : ({b.val} : Set α) ⊆ rdRetract P_X a₀ ⁻¹' {b} := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff, rdRetract]
    rw [dif_pos b.property]
  have h2 : rdRetract P_X a₀ ⁻¹' {b} ⊆ {b.val} ∪ {a : α | ¬ 0 < P_X a} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff, rdRetract] at hx
    by_cases hxs : 0 < P_X x
    · left
      rw [dif_pos hxs] at hx
      simp only [Set.mem_singleton_iff]
      exact congrArg Subtype.val hx
    · exact Or.inr hxs
  have hsq : pmfToMeasure P_X (rdRetract P_X a₀ ⁻¹' {b}) = pmfToMeasure P_X {b.val} := by
    refine le_antisymm ?_ (measure_mono h1)
    calc pmfToMeasure P_X (rdRetract P_X a₀ ⁻¹' {b})
        ≤ pmfToMeasure P_X ({b.val} ∪ {a : α | ¬ 0 < P_X a}) := measure_mono h2
      _ ≤ pmfToMeasure P_X {b.val} + pmfToMeasure P_X {a : α | ¬ 0 < P_X a} := measure_union_le _ _
      _ = pmfToMeasure P_X {b.val} := by rw [hnull, add_zero]
  rw [hsq, pmfToMeasure_apply_singleton P_X b.val,
    pmfToMeasure_apply_singleton (rdSupportPmf P_X) b]

/-- Lift the expected block distortion bound from the support subtype to the
whole alphabet. -/
lemma expectedBlockDistortion_lift_le (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    (d : DistortionFn α β) {M n : ℕ}
    (c' : LossyCode M n {a // 0 < P_X a} β)
    (a₀ : {a // 0 < P_X a}) {v : ℝ}
    (hc' : c'.expectedBlockDistortion (pmfToMeasure (rdSupportPmf P_X)) (rdSupportDist P_X d) ≤ v) :
    (⟨fun x ↦ c'.encoder (fun i ↦ rdRetract P_X a₀ (x i)), c'.decoder⟩ :
        LossyCode M n α β).expectedBlockDistortion (pmfToMeasure P_X) d ≤ v := by
  haveI hμ_prob : IsProbabilityMeasure (pmfToMeasure P_X) :=
    pmfToMeasure_isProbabilityMeasure hP_pmf
  have hr_meas : Measurable (rdRetract P_X a₀) := measurable_of_finite _
  haveI hμ'_map_prob : IsProbabilityMeasure ((pmfToMeasure P_X).map (rdRetract P_X a₀)) :=
    Measure.isProbabilityMeasure_map hr_meas.aemeasurable
  have hmap : (pmfToMeasure P_X).map (rdRetract P_X a₀) = pmfToMeasure (rdSupportPmf P_X) :=
    pmfToMeasure_map_retract P_X hP_pmf a₀
  have hnull : pmfToMeasure P_X {a : α | ¬ 0 < P_X a} = 0 :=
    pmfToMeasure_support_compl_null P_X hP_pmf
  have hS : MeasurableSet {a : α | ¬ 0 < P_X a} := (Set.toFinite _).measurableSet
  set rπ : (Fin n → α) → (Fin n → {a // 0 < P_X a}) :=
    fun x i ↦ rdRetract P_X a₀ (x i) with hrπ
  have hrπ_meas : Measurable rπ := measurable_of_finite _
  -- a.e. every coordinate lands in the support
  have hae : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)), ∀ i, 0 < P_X (x i) := by
    rw [ae_all_iff]
    intro i
    have hmp := measurePreserving_eval (μ := fun _ : Fin n ↦ pmfToMeasure P_X) i
    rw [ae_iff]
    have hpre : {x : Fin n → α | ¬ 0 < P_X (x i)}
        = Function.eval i ⁻¹' {a : α | ¬ 0 < P_X a} := rfl
    rw [hpre, ← Measure.map_apply hmp.measurable hS, hmp.map_eq]
    exact hnull
  -- pointwise congruence of the two integrands on the support-full set
  have hcongr : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)),
      blockDistortion d n x (c'.decoder (c'.encoder (fun i ↦ rdRetract P_X a₀ (x i))))
        = blockDistortion (rdSupportDist P_X d) n (rπ x)
            (c'.decoder (c'.encoder (rπ x))) := by
    filter_upwards [hae] with x hx
    simp only [hrπ]
    unfold blockDistortion
    congr 1
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    have hri : (rdRetract P_X a₀ (x i)).val = x i := by
      simp only [rdRetract]; rw [dif_pos (hx i)]
    simp only [rdSupportDist, hri]
  -- push the source measure through the retraction
  have hmappi : (Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)).map rπ
      = Measure.pi (fun _ : Fin n ↦ pmfToMeasure (rdSupportPmf P_X)) := by
    rw [hrπ, Measure.pi_map_pi (μ := fun _ : Fin n ↦ pmfToMeasure P_X)
        (f := fun _ : Fin n ↦ rdRetract P_X a₀) (fun _ ↦ hr_meas.aemeasurable)]
    simp_rw [hmap]
  -- assemble the change of variables
  refine le_of_eq_of_le ?_ hc'
  calc (⟨fun x ↦ c'.encoder (fun i ↦ rdRetract P_X a₀ (x i)), c'.decoder⟩ :
          LossyCode M n α β).expectedBlockDistortion (pmfToMeasure P_X) d
      = ∫ x, blockDistortion d n x (c'.decoder (c'.encoder (fun i ↦ rdRetract P_X a₀ (x i))))
          ∂(Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)) := rfl
    _ = ∫ x, blockDistortion (rdSupportDist P_X d) n (rπ x)
          (c'.decoder (c'.encoder (rπ x)))
          ∂(Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)) := integral_congr_ae hcongr
    _ = ∫ x', blockDistortion (rdSupportDist P_X d) n x' (c'.decoder (c'.encoder x'))
          ∂((Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)).map rπ) :=
        (integral_map (μ := Measure.pi (fun _ : Fin n ↦ pmfToMeasure P_X)) (φ := rπ)
          (f := fun x' : Fin n → {a // 0 < P_X a} ↦
            blockDistortion (rdSupportDist P_X d) n x' (c'.decoder (c'.encoder x')))
          hrπ_meas.aemeasurable (measurable_of_finite _).aestronglyMeasurable).symm
    _ = ∫ x', blockDistortion (rdSupportDist P_X d) n x' (c'.decoder (c'.encoder x'))
          ∂(Measure.pi (fun _ : Fin n ↦ pmfToMeasure (rdSupportPmf P_X))) := by rw [hmappi]
    _ = c'.expectedBlockDistortion (pmfToMeasure (rdSupportPmf P_X)) (rdSupportDist P_X d) := rfl

/-! ## Wrapper: general-source operational achievability -/

/-- **Rate-distortion theorem** (achievability, general source).

Removes the full-support precondition from
`rate_distortion_achievability_operational`: for any source `P_X ∈ stdSimplex`
with a feasible constraint set and any rate `R > R(D)`, for every `ε > 0` there
is a block length `N` such that every `n ≥ N` admits a rate-`R` lossy code whose
expected block distortion is at most `D + ε`.

@audit:ok -/
@[entry_point]
theorem rate_distortion_achievability_operational_general
    (P_X : α → ℝ) (hP_pmf : P_X ∈ stdSimplex ℝ α)
    (d : DistortionFn α β) {D : ℝ}
    (h_ne : (RDConstraint P_X d D).Nonempty)
    {R : ℝ} (hR : rateDistortionFunctionPmf P_X d D < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (_hM_ub : (M : ℝ) ≤ Real.exp ((n : ℝ) * R) + 1)
        (c : LossyCode M n α β),
        c.expectedBlockDistortion (pmfToMeasure (α := α) P_X) d ≤ D + ε := by
  -- pick a support symbol as the retraction default
  obtain ⟨a₀val, ha₀⟩ := rd_support_nonempty P_X hP_pmf
  set a₀ : {a // 0 < P_X a} := ⟨a₀val, ha₀⟩ with ha₀_def
  haveI : Nonempty {a // 0 < P_X a} := ⟨a₀⟩
  -- transport the hypotheses to the support subtype
  have hP'_pmf : rdSupportPmf P_X ∈ stdSimplex ℝ {a // 0 < P_X a} :=
    rdSupportPmf_mem_stdSimplex P_X hP_pmf
  have hP'_supp : ∀ a' : {a // 0 < P_X a}, 0 < rdSupportPmf P_X a' := fun a' ↦ a'.property
  have h_ne' : (RDConstraint (rdSupportPmf P_X) (rdSupportDist P_X d) D).Nonempty := by
    obtain ⟨q, hq⟩ := h_ne
    exact ⟨rdRestrict P_X q, rdRestrict_mem_constraint P_X d hq⟩
  have hR' : rateDistortionFunctionPmf (rdSupportPmf P_X) (rdSupportDist P_X d) D < R := by
    rwa [rd_function_eq P_X hP_pmf d D] at hR
  -- apply the full-support theorem on the support subtype
  obtain ⟨N, hN⟩ := rate_distortion_achievability_operational
    (rdSupportPmf P_X) hP'_pmf hP'_supp (rdSupportDist P_X d) h_ne' hR' hε
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M, hM_lb, hM_ub, c', hc'⟩ := hN n hn
  -- lift the support-subtype code back to the whole alphabet
  refine ⟨M, hM_lb, hM_ub,
    ⟨fun x ↦ c'.encoder (fun i ↦ rdRetract P_X a₀ (x i)), c'.decoder⟩, ?_⟩
  exact expectedBlockDistortion_lift_le P_X hP_pmf d c' a₀ hc'

end InformationTheory.Shannon
