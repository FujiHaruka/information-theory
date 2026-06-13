import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SlepianWolf.Achievability
import InformationTheory.Shannon.SlepianWolf.Binning
import InformationTheory.Shannon.SlepianWolf.ConditionalTypicalSlice
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.Core
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.AliasBound

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## The strict `swError_EXY` expectation bound under random binning

The "both coordinates differ" sub-event `swError_EXY_strict` admits the bound
`|JTS| / (M_X · M_Y)` via pair-binning collision (`1/M_X · 1/M_Y`) summed over the
joint typical set, which with `jointlyTypicalSet_card_le` gives the target
`exp(n · (H(X,Y) + ε)) / (M_X · M_Y)`. The original `swError_EXY` splits into three
sub-cases by `(p.1 = Xⁿ ?, p.2 = Yⁿ ?)`; the two "loose" cases are absorbed into
`swError_EX` / `swError_EY` via `swError_EXY_subset_union`. -/

/-- The "both coordinates differ" sub-event of `swError_EXY`. -/
private def swError_EXY_strict
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) {M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) : Set Ω :=
  { ω | ∃ p : (Fin n → α) × (Fin n → β),
            p.1 ≠ jointRV Xs n ω
          ∧ p.2 ≠ jointRV Ys n ω
          ∧ f_X p.1 = f_X (jointRV Xs n ω)
          ∧ f_Y p.2 = f_Y (jointRV Ys n ω)
          ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε }

omit [DecidableEq α] [DecidableEq β] in
/-- The full `swError_EXY` event is contained in the union of the two single-axis
events `swError_EX`, `swError_EY` and the strict `swError_EXY_strict`. The loose
cases (only one coordinate of the alias `p` agrees with the truth) are absorbed
into `E_X` or `E_Y` respectively. -/
@[entry_point]
lemma swError_EXY_subset_union
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    swError_EXY μ Xs Ys n ε f_X f_Y
      ⊆ swError_EX μ Xs Ys n ε f_X
        ∪ swError_EY μ Xs Ys n ε f_Y
        ∪ swError_EXY_strict μ Xs Ys n ε f_X f_Y := by
  intro ω hω
  rcases hω with ⟨p, hpne, hfx, hfy, hpJTS⟩
  by_cases hp1 : p.1 = jointRV Xs n ω
  · by_cases hp2 : p.2 = jointRV Ys n ω
    · -- both agree ⇒ contradiction with hpne.
      exfalso
      exact hpne (Prod.ext hp1 hp2)
    · -- p.1 = X^n, p.2 ≠ Y^n ⇒ ω ∈ E_Y (left ∪ right inside left).
      left; right
      show ω ∈ swError_EY μ Xs Ys n ε f_Y
      refine ⟨p.2, hp2, hfy, ?_⟩
      have : (p.1, p.2) ∈ jointlyTypicalSet μ Xs Ys n ε := hpJTS
      rw [hp1] at this
      exact this
  · by_cases hp2 : p.2 = jointRV Ys n ω
    · -- p.1 ≠ X^n, p.2 = Y^n ⇒ ω ∈ E_X.
      left; left
      show ω ∈ swError_EX μ Xs Ys n ε f_X
      refine ⟨p.1, hp1, hfx, ?_⟩
      have : (p.1, p.2) ∈ jointlyTypicalSet μ Xs Ys n ε := hpJTS
      rw [hp2] at this
      exact this
    · -- both differ ⇒ ω ∈ EXY_strict.
      right
      exact ⟨p, hp1, hp2, hfx, hfy, hpJTS⟩

omit [DecidableEq α] [DecidableEq β] in
private lemma measurableSet_swError_EXY_strict
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) {M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    MeasurableSet (swError_EXY_strict μ Xs Ys n ε f_X f_Y) := by
  classical
  have hmeas : Measurable
      (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  let S : Set ((Fin n → α) × (Fin n → β)) :=
    { p | ∃ q : (Fin n → α) × (Fin n → β),
            q.1 ≠ p.1
          ∧ q.2 ≠ p.2
          ∧ f_X q.1 = f_X p.1
          ∧ f_Y q.2 = f_Y p.2
          ∧ q ∈ jointlyTypicalSet μ Xs Ys n ε }
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_eq : swError_EXY_strict μ Xs Ys n ε f_X f_Y
      = (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) ⁻¹' S := by
    ext ω
    rfl
  rw [h_eq]
  exact hmeas hS_meas

omit [DecidableEq α] [DecidableEq β] in
/-- For a finite set `S` of candidate alias pairs, the product binning-measure
probability that some `p ∈ S` has both coordinates differing from the truth and
both hashes colliding is at most `|S| / (M_X · M_Y)` (union bound over the per-pair
product collision probability `1/M_X · 1/M_Y`). -/
private lemma binning_pair_alias_expectation_le_aux
    {n M_X M_Y : ℕ} [NeZero M_X] [NeZero M_Y]
    (truth_x : Fin n → α) (truth_y : Fin n → β)
    (S : Finset ((Fin n → α) × (Fin n → β))) :
    ((binningMeasure α n M_X).prod (binningMeasure β n M_Y)).real
        {fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)
          | ∃ p ∈ S, p.1 ≠ truth_x ∧ p.2 ≠ truth_y
                  ∧ fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y}
      ≤ S.card * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
  classical
  -- Filter to admissible pairs (both coordinates differ from the truth).
  set T : Finset ((Fin n → α) × (Fin n → β)) :=
    S.filter (fun p => p.1 ≠ truth_x ∧ p.2 ≠ truth_y) with hT_def
  set B_X : Measure ((Fin n → α) → Fin M_X) := binningMeasure α n M_X with hB_X_def
  set B_Y : Measure ((Fin n → β) → Fin M_Y) := binningMeasure β n M_Y with hB_Y_def
  set BP : Measure _ := B_X.prod B_Y with hBP_def
  set evt : Set (((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)) :=
      {fg | ∃ p ∈ S, p.1 ≠ truth_x ∧ p.2 ≠ truth_y
              ∧ fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y} with hevt_def
  set unionEvt : Set (((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)) :=
      ⋃ p ∈ T, {fg | fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y}
    with hunionEvt_def
  have h_sub : evt ⊆ unionEvt := by
    intro fg hfg
    rcases hfg with ⟨p, hpS, hp1, hp2, hcoll1, hcoll2⟩
    refine Set.mem_iUnion₂.mpr ⟨p, ?_, hcoll1, hcoll2⟩
    simp [T, hpS, hp1, hp2]
  have h_step1 :
      BP.real evt ≤ BP.real unionEvt :=
    measureReal_mono h_sub (measure_ne_top _ _)
  -- Union bound.
  have h_step2 :
      BP.real unionEvt
        ≤ ∑ p ∈ T, BP.real {fg | fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y} :=
    measureReal_biUnion_finset_le _ _
  -- Per-pair: the collision event factors as a product of single-axis events.
  have h_summand : ∀ p ∈ T,
      BP.real {fg | fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y}
        = ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
    intro p hp
    have hp1 : p.1 ≠ truth_x := ((Finset.mem_filter.mp hp).2).1
    have hp2 : p.2 ≠ truth_y := ((Finset.mem_filter.mp hp).2).2
    -- The set is a product set.
    have h_eq : ({fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)
            | fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y})
          = ({f_X | f_X p.1 = f_X truth_x} : Set ((Fin n → α) → Fin M_X)) ×ˢ
            ({f_Y | f_Y p.2 = f_Y truth_y} : Set ((Fin n → β) → Fin M_Y)) := by
      ext ⟨f_X, f_Y⟩
      simp
    rw [h_eq]
    -- product measure of product set = product of marginal measures.
    rw [measureReal_prod_prod]
    -- Each factor = (M_X)⁻¹ resp. (M_Y)⁻¹ by `binning_collision_prob`.
    rw [binning_collision_prob (M := M_X) hp1, binning_collision_prob (M := M_Y) hp2]
  have h_step3 :
      (∑ p ∈ T, BP.real {fg | fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y})
        = (T.card : ℝ) * (((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := by
    rw [Finset.sum_congr rfl h_summand, Finset.sum_const, nsmul_eq_mul]
  have h_card : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le S _
  have h_mx_nn : (0 : ℝ) ≤ ((M_X : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  have h_my_nn : (0 : ℝ) ≤ ((M_Y : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  have h_prod_nn : (0 : ℝ) ≤ ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ :=
    mul_nonneg h_mx_nn h_my_nn
  calc BP.real evt
      ≤ BP.real unionEvt := h_step1
    _ ≤ ∑ p ∈ T, BP.real {fg | fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y} := h_step2
    _ = (T.card : ℝ) * (((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := h_step3
    _ ≤ (S.card : ℝ) * (((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := by
        exact mul_le_mul_of_nonneg_right h_card h_prod_nn
    _ = (S.card : ℝ) * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by ring

/-! ### The `swError_EXY_strict` expectation bound

The expected `μ`-mass of the strict `E_{XY}` error event (both alias coordinates
differ from the truth) over the product random binning hash
`(f_X, f_Y) ∼ (binningMeasure α n M_X) × (binningMeasure β n M_Y)` is bounded by
`exp(n · (H(X, Y) + ε)) / (M_X · M_Y)`, the joint typical set's cardinality bound
divided by the product bin count. The proof Fubini-swaps `BP := B_X × B_Y` and `μ`,
applies `binning_pair_alias_expectation_le_aux` per `ω`, and closes with
`jointlyTypicalSet_card_le`. -/

omit [DecidableEq α] [DecidableEq β] in
set_option linter.unusedVariables false in
@[entry_point]
theorem swError_EXY_strict_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {n M_X M_Y : ℕ} [NeZero M_X] [NeZero M_Y] {ε : ℝ} (hε : 0 < ε) :
    ∫ f_X, ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)
          ∂(binningMeasure β n M_Y) ∂(binningMeasure α n M_X)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε))
        * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → α) → Fin M_X) :=
    Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass ((Fin n → β) → Fin M_Y) :=
    Pi.instMeasurableSingletonClass
  haveI : Fintype ((Fin n → α) → Fin M_X) := Pi.instFintype
  haveI : Fintype ((Fin n → β) → Fin M_Y) := Pi.instFintype
  -- Notation.
  set B_X : Measure ((Fin n → α) → Fin M_X) := binningMeasure α n M_X with hB_X_def
  set B_Y : Measure ((Fin n → β) → Fin M_Y) := binningMeasure β n M_Y with hB_Y_def
  set BP : Measure (((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)) :=
    B_X.prod B_Y with hBP_def
  set C : ℝ := Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε)) with hC_def
  have hC_pos : 0 < C := Real.exp_pos _
  have hC_nn : 0 ≤ C := hC_pos.le
  have hMxinv_nn : (0 : ℝ) ≤ ((M_X : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  have hMyinv_nn : (0 : ℝ) ≤ ((M_Y : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  have hRHS_nn : 0 ≤ C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ :=
    mul_nonneg (mul_nonneg hC_nn hMxinv_nn) hMyinv_nn
  have hXn : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
  have hYn : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  have h_meas_EXY_strict : ∀ (f_X : (Fin n → α) → Fin M_X)
      (f_Y : (Fin n → β) → Fin M_Y),
      MeasurableSet (swError_EXY_strict μ Xs Ys n ε f_X f_Y) := fun f_X f_Y =>
    measurableSet_swError_EXY_strict hXs hYs μ n ε f_X f_Y
  -- The JTS finset, ω-independent.
  set S : Finset ((Fin n → α) × (Fin n → β)) :=
    (jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset with hS_def
  -- JTS cardinality bound.
  have hS_card_le : (S.card : ℝ) ≤ C := by
    rw [hS_def, hC_def]
    exact jointlyTypicalSet_card_le μ Xs Ys hXs hYs hposZ n hε
  -- Per-ω slice bound on BP.real.
  have h_per_omega : ∀ ω : Ω,
      BP.real {fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)
                | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}
        ≤ C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
    intro ω
    set truth_x : Fin n → α := jointRV Xs n ω
    set truth_y : Fin n → β := jointRV Ys n ω
    -- Rewrite the per-ω set into the binning_pair_alias form.
    have h_set_eq : {fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)
              | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}
          = {fg | ∃ p ∈ S, p.1 ≠ truth_x ∧ p.2 ≠ truth_y
                ∧ fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y} := by
      ext fg
      simp only [Set.mem_setOf_eq, swError_EXY_strict, hS_def, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨p, hp1, hp2, hfx, hfy, hpJTS⟩
        exact ⟨p, hpJTS, hp1, hp2, hfx, hfy⟩
      · rintro ⟨p, hpJTS, hp1, hp2, hfx, hfy⟩
        exact ⟨p, hp1, hp2, hfx, hfy, hpJTS⟩
    rw [h_set_eq]
    have hA : BP.real {fg | ∃ p ∈ S, p.1 ≠ truth_x ∧ p.2 ≠ truth_y
                  ∧ fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y}
        ≤ (S.card : ℝ) * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
      simpa [BP, B_X, B_Y] using
        binning_pair_alias_expectation_le_aux (M_X := M_X) (M_Y := M_Y) truth_x truth_y S
    calc BP.real {fg | ∃ p ∈ S, p.1 ≠ truth_x ∧ p.2 ≠ truth_y
                  ∧ fg.1 p.1 = fg.1 truth_x ∧ fg.2 p.2 = fg.2 truth_y}
        ≤ (S.card : ℝ) * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := hA
      _ ≤ C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
          have hMxinv_my_nn : 0 ≤ ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ :=
            mul_nonneg hMxinv_nn hMyinv_nn
          have := mul_le_mul_of_nonneg_right hS_card_le hMxinv_my_nn
          calc (S.card : ℝ) * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹
              = (S.card : ℝ) * (((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := by ring
            _ ≤ C * (((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := this
            _ = C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by ring
  -- Build the product set E ⊆ (BP-space) × Ω.
  set E : Set ((((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)) × Ω) :=
    {q | q.2 ∈ swError_EXY_strict μ Xs Ys n ε q.1.1 q.1.2} with hE_def
  have hE_meas : MeasurableSet E := by
    -- E = ⋃ (fg : (Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y),
    --       {fg} ×ˢ swError_EXY_strict μ ... fg.1 fg.2.
    have h_decomp : E = ⋃ fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y),
        ({fg} : Set (((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y)))
          ×ˢ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2 := by
      ext ⟨g, ω⟩
      simp [E]
    rw [h_decomp]
    refine MeasurableSet.iUnion (fun fg => ?_)
    exact (measurableSet_singleton _).prod (h_meas_EXY_strict fg.1 fg.2)
  -- Fubini: (BP.prod μ) E rewrites two ways.
  have h_fubini1 :
      (BP.prod μ) E
        = ∫⁻ fg, μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ∂BP := by
    rw [Measure.prod_apply hE_meas]
    congr 1
  have h_fubini2 :
      (BP.prod μ) E
        = ∫⁻ ω, BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2} ∂μ := by
    rw [Measure.prod_apply_symm hE_meas]
    congr 1
  have h_swap :
      ∫⁻ fg, μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ∂BP
        = ∫⁻ ω, BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2} ∂μ := by
    rw [← h_fubini1, h_fubini2]
  -- ENNReal lift of per-ω bound.
  have h_per_omega_ennreal : ∀ ω : Ω,
      BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}
        ≤ ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := by
    intro ω
    have hr := h_per_omega ω
    have hne_top : BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2} ≠ ∞ :=
      measure_ne_top _ _
    rw [show BP.real {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}
          = (BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}).toReal from rfl] at hr
    calc BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}
        = ENNReal.ofReal
            (BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2}).toReal := by
          rw [ENNReal.ofReal_toReal hne_top]
      _ ≤ ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) :=
          ENNReal.ofReal_le_ofReal hr
  have h_lint_le :
      ∫⁻ ω, BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2} ∂μ
        ≤ ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := by
    calc ∫⁻ ω, BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2} ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) ∂μ :=
          lintegral_mono h_per_omega_ennreal
      _ = ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) * μ Set.univ := by
          rw [lintegral_const]
      _ = ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹) := by
          rw [measure_univ, mul_one]
  -- Bochner outer integral over BP — convert to lintegral.
  have h_int_nn : 0 ≤ᵐ[BP] fun fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y) =>
      μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) := by
    refine Filter.Eventually.of_forall (fun fg => ?_)
    exact measureReal_nonneg
  have h_int_meas :
      AEStronglyMeasurable
        (fun fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y) =>
          μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)) BP := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.of_discrete
  -- Bochner integrable on BP.
  have h_integrable_BP : Integrable
      (fun fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y) =>
        μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)) BP := by
    refine ⟨h_int_meas, ?_⟩
    -- HasFiniteIntegral: ∫⁻ ‖·‖ < ∞. Bounded integrand × finite measure.
    refine (hasFiniteIntegral_def _ _).mpr ?_
    have h_bound : ∀ fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y),
        ‖μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)‖₊ ≤ 1 := by
      intro fg
      have h_nn : 0 ≤ μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) :=
        measureReal_nonneg
      have h_le_one : μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ≤ 1 := by
        have := prob_le_one (μ := μ)
            (s := swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)
        unfold Measure.real
        have h_le : (μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)).toReal ≤ 1 := by
          have h_lt_one : μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ≤ 1 := this
          exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr h_lt_one
        exact h_le
      rw [Real.nnnorm_of_nonneg h_nn]
      exact_mod_cast h_le_one
    calc ∫⁻ fg, ‖μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)‖ₑ ∂BP
        ≤ ∫⁻ _, 1 ∂BP := by
          refine lintegral_mono fun fg => ?_
          have hb := h_bound fg
          rw [show ‖μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)‖ₑ
                = ((‖μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)‖₊ : ℝ≥0∞))
                from rfl]
          have : ((‖μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)‖₊ : ℝ≥0∞))
              ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hb
          simpa using this
      _ = BP Set.univ := by rw [lintegral_const, one_mul]
      _ < ∞ := measure_lt_top _ _
  -- Use Bochner Fubini to convert iterated integral to integral over BP.
  rw [show (∫ f_X, ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)
              ∂B_Y ∂B_X)
        = ∫ fg, μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ∂BP from by
    rw [integral_prod _ h_integrable_BP]]
  -- Convert Bochner ∫ over BP to lintegral.
  rw [integral_eq_lintegral_of_nonneg_ae h_int_nn h_int_meas]
  have h_ofReal_eq : ∀ fg : ((Fin n → α) → Fin M_X) × ((Fin n → β) → Fin M_Y),
      ENNReal.ofReal (μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2))
        = μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) := by
    intro fg
    have hne_top : μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ≠ ∞ :=
      measure_ne_top _ _
    rw [show μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)
          = (μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)).toReal from rfl,
        ENNReal.ofReal_toReal hne_top]
  have h_lint_eq :
      ∫⁻ fg, ENNReal.ofReal (μ.real (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2)) ∂BP
        = ∫⁻ fg, μ (swError_EXY_strict μ Xs Ys n ε fg.1 fg.2) ∂BP := by
    refine lintegral_congr (fun fg => ?_)
    exact h_ofReal_eq fg
  rw [h_lint_eq, h_swap]
  calc (∫⁻ ω, BP {fg | ω ∈ swError_EXY_strict μ Xs Ys n ε fg.1 fg.2} ∂μ).toReal
      ≤ (ENNReal.ofReal (C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹)).toReal := by
        apply ENNReal.toReal_mono _ h_lint_le
        exact ENNReal.ofReal_ne_top
    _ = C * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := ENNReal.toReal_ofReal hRHS_nn

/-! ## Pigeonhole and finalize (Cover–Thomas 15.4.1)

Combines the four-event decomposition with the per-term binning bounds, takes a total
bound over the binning expectation, extracts a deterministic encoder pair by
pigeonhole, and derives `error probability → 0` under the rate conditions
`R_X > H(Y|X)`, `R_Y > H(X|Y)`, `R_X + R_Y > H(X, Y)`.

* `entropy_joint_sub_marginal_eq_condEntropy` — the bridge `H(X,Y) - H(X) = H(Y|X)`.
* `swErrorProb_total_expectation_le` — the total binning-expectation bound.
* `exists_pair_le_of_binning_integral_le` — pigeonhole extraction.
* `slepian_wolf_full_rate_region_achievability` — rate region achievability.
-/

section PhaseF

variable {α' β' Ω' : Type*}
  [MeasurableSpace Ω']
  [Fintype α'] [DecidableEq α'] [Nonempty α']
    [MeasurableSpace α'] [MeasurableSingletonClass α']
  [Fintype β'] [DecidableEq β'] [Nonempty β']
    [MeasurableSpace β'] [MeasurableSingletonClass β']

omit [DecidableEq α'] [DecidableEq β'] in
/-- `H(X, Y) - H(X) = H(Y | X)`, a corollary of the chain rule
`entropy_pair_eq_entropy_add_condEntropy`. -/
private lemma entropy_joint_sub_marginal_eq_condEntropy
    (μ : Measure Ω') [IsProbabilityMeasure μ]
    (X : Ω' → α') (Y : Ω' → β') (hX : Measurable X) (hY : Measurable Y) :
    entropy μ (fun ω => (X ω, Y ω)) - entropy μ X
      = InformationTheory.MeasureFano.condEntropy μ Y X := by
  classical
  have h := entropy_pair_eq_entropy_add_condEntropy μ X Y hX hY
  linarith

end PhaseF

omit [DecidableEq α] [DecidableEq β] in
/-- The total binning-expectation bound, combining the four-event decomposition
with the `swError_EXY` subset absorption. The factor `2` absorbs the double count
in `EXY ⊆ EX ∪ EY ∪ EXY_strict`. -/
private theorem swErrorProb_total_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {n M_X M_Y : ℕ} [NeZero M_X] [NeZero M_Y] {ε : ℝ} (hε : 0 < ε) :
    ∫ f_X, ∫ f_Y,
        swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
          (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
      ∂(binningMeasure β n M_Y) ∂(binningMeasure α n M_X)
      ≤ μ.real (swError_E0 μ Xs Ys n ε)
        + 2 * (Real.exp ((n : ℝ) *
            (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
              * ((M_X : ℝ))⁻¹)
        + 2 * (Real.exp ((n : ℝ) *
            (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε))
              * ((M_Y : ℝ))⁻¹)
        + Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε))
            * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → α) → Fin M_X) :=
    Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass ((Fin n → β) → Fin M_Y) :=
    Pi.instMeasurableSingletonClass
  haveI : Fintype ((Fin n → α) → Fin M_X) := Pi.instFintype
  haveI : Fintype ((Fin n → β) → Fin M_Y) := Pi.instFintype
  set B_X : Measure ((Fin n → α) → Fin M_X) := binningMeasure α n M_X with hB_X_def
  set B_Y : Measure ((Fin n → β) → Fin M_Y) := binningMeasure β n M_Y with hB_Y_def
  -- E.2/E.3/E.4 bounds for later use.
  have hE2 :
      ∫ f_X, μ.real (swError_EX μ Xs Ys n ε f_X) ∂B_X
        ≤ Real.exp ((n : ℝ) *
              (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
          * ((M_X : ℝ))⁻¹ :=
    swError_EX_expectation_le μ Xs Ys hXs hYs hindepY_full hidentY
      hindepZ_full hidentZ hposY hposZ hε
  have hE3 :
      ∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y
        ≤ Real.exp ((n : ℝ) *
              (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε))
          * ((M_Y : ℝ))⁻¹ :=
    swError_EY_expectation_le μ Xs Ys hXs hYs hindepX_full hidentX
      hindepZ_full hidentZ hposX hposZ hε
  have hE4 :
      ∫ f_X, ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y ∂B_X
        ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε))
          * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ :=
    swError_EXY_strict_expectation_le μ Xs Ys hXs hYs hposZ hε
  -- Pointwise inequality: the swErrorProb (as a function of f_X, f_Y) is bounded
  -- by the sum of the four μ.real terms (D main decomposition + EXY subset).
  have h_pointwise : ∀ (f_X : (Fin n → α) → Fin M_X)
      (f_Y : (Fin n → β) → Fin M_Y),
      swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
            (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
        ≤ μ.real (swError_E0 μ Xs Ys n ε)
          + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
          + 2 * μ.real (swError_EY μ Xs Ys n ε f_Y)
          + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) := by
    intro f_X f_Y
    have h_D := swErrorProb_le_E0_plus_EX_plus_EY_plus_EXY
      μ Xs Ys hXs hYs ε f_X f_Y
    have h_EXY_subset :
        μ.real (swError_EXY μ Xs Ys n ε f_X f_Y)
          ≤ μ.real (swError_EX μ Xs Ys n ε f_X)
            + μ.real (swError_EY μ Xs Ys n ε f_Y)
            + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) := by
      have h_sub := swError_EXY_subset_union μ Xs Ys ε f_X f_Y
      calc μ.real (swError_EXY μ Xs Ys n ε f_X f_Y)
          ≤ μ.real (swError_EX μ Xs Ys n ε f_X
                ∪ swError_EY μ Xs Ys n ε f_Y
                ∪ swError_EXY_strict μ Xs Ys n ε f_X f_Y) :=
            measureReal_mono h_sub (measure_ne_top _ _)
        _ ≤ μ.real (swError_EX μ Xs Ys n ε f_X
                ∪ swError_EY μ Xs Ys n ε f_Y)
              + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) :=
            measureReal_union_le _ _
        _ ≤ μ.real (swError_EX μ Xs Ys n ε f_X)
              + μ.real (swError_EY μ Xs Ys n ε f_Y)
              + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) := by
            have := measureReal_union_le (μ := μ)
              (swError_EX μ Xs Ys n ε f_X) (swError_EY μ Xs Ys n ε f_Y)
            linarith
    linarith
  -- Integrability template: any `μ.real (...)` integrand is bounded by 1,
  -- discrete (finite domain → measurable), hence integrable.
  -- We will need these for various per-summand sub-integrands.
  have h_meas_inner : ∀ f_X : (Fin n → α) → Fin M_X,
      AEStronglyMeasurable
        (fun f_Y => swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                      (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)) B_Y := fun f_X =>
    Measurable.aestronglyMeasurable Measurable.of_discrete
  have h_meas_outer :
      AEStronglyMeasurable
        (fun f_X => ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                      (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y) B_X :=
    Measurable.aestronglyMeasurable Measurable.of_discrete
  -- Build a generic integrability lemma for "bounded by 1 + discrete" functions
  -- on the product of two probability measures (B_X.prod B_Y) and on each
  -- marginal.
  -- Helper: every nonnegative ≤ 1 discrete function on `B_X` is integrable.
  have hInt_B_X : ∀ g : ((Fin n → α) → Fin M_X) → ℝ,
      (∀ f_X, 0 ≤ g f_X) → (∀ f_X, g f_X ≤ 1) → Integrable g B_X := by
    intro g h_nn h_le
    refine ⟨Measurable.aestronglyMeasurable Measurable.of_discrete, ?_⟩
    refine (hasFiniteIntegral_def _ _).mpr ?_
    have h_bound : ∀ f_X, ‖g f_X‖₊ ≤ 1 := by
      intro f_X
      rw [Real.nnnorm_of_nonneg (h_nn f_X)]
      exact_mod_cast h_le f_X
    calc ∫⁻ f_X, ‖g f_X‖ₑ ∂B_X
        ≤ ∫⁻ _, 1 ∂B_X := by
          refine lintegral_mono fun f_X => ?_
          have hb := h_bound f_X
          rw [show ‖g f_X‖ₑ = ((‖g f_X‖₊ : ℝ≥0∞)) from rfl]
          have : ((‖g f_X‖₊ : ℝ≥0∞)) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hb
          simpa using this
      _ = B_X Set.univ := by rw [lintegral_const, one_mul]
      _ < ∞ := measure_lt_top _ _
  have hInt_B_Y : ∀ g : ((Fin n → β) → Fin M_Y) → ℝ,
      (∀ f_Y, 0 ≤ g f_Y) → (∀ f_Y, g f_Y ≤ 1) → Integrable g B_Y := by
    intro g h_nn h_le
    refine ⟨Measurable.aestronglyMeasurable Measurable.of_discrete, ?_⟩
    refine (hasFiniteIntegral_def _ _).mpr ?_
    have h_bound : ∀ f_Y, ‖g f_Y‖₊ ≤ 1 := by
      intro f_Y
      rw [Real.nnnorm_of_nonneg (h_nn f_Y)]
      exact_mod_cast h_le f_Y
    calc ∫⁻ f_Y, ‖g f_Y‖ₑ ∂B_Y
        ≤ ∫⁻ _, 1 ∂B_Y := by
          refine lintegral_mono fun f_Y => ?_
          have hb := h_bound f_Y
          rw [show ‖g f_Y‖ₑ = ((‖g f_Y‖₊ : ℝ≥0∞)) from rfl]
          have : ((‖g f_Y‖₊ : ℝ≥0∞)) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hb
          simpa using this
      _ = B_Y Set.univ := by rw [lintegral_const, one_mul]
      _ < ∞ := measure_lt_top _ _
  -- swErrorProb is bounded by 1 (it's a probability).
  have h_swErr_le_one : ∀ (f_X : (Fin n → α) → Fin M_X)
      (f_Y : (Fin n → β) → Fin M_Y),
      swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
        (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ≤ 1 := by
    intro f_X f_Y
    unfold swErrorProb
    have h_le : μ {ω | swJointTypicalDecoder μ Xs Ys ε f_X f_Y
                  (f_X (jointRV Xs n ω), f_Y (jointRV Ys n ω))
                  ≠ (jointRV Xs n ω, jointRV Ys n ω)} ≤ 1 :=
      prob_le_one
    unfold Measure.real
    have : (μ {ω | swJointTypicalDecoder μ Xs Ys ε f_X f_Y
            (f_X (jointRV Xs n ω), f_Y (jointRV Ys n ω))
            ≠ (jointRV Xs n ω, jointRV Ys n ω)}).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr h_le
    exact this
  have h_swErr_nn : ∀ (f_X : (Fin n → α) → Fin M_X)
      (f_Y : (Fin n → β) → Fin M_Y),
      0 ≤ swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
        (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) := by
    intro f_X f_Y
    unfold swErrorProb
    exact measureReal_nonneg
  -- Integrability of swErrorProb in f_Y for any f_X.
  have hInt_swErr_inner : ∀ f_X : (Fin n → α) → Fin M_X,
      Integrable (fun f_Y => swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)) B_Y := fun f_X =>
    hInt_B_Y _ (h_swErr_nn f_X) (h_swErr_le_one f_X)
  -- Integrability of μ.real (swError_EX) in f_X (it's f_Y-independent, but we
  -- use this on the B_X axis).
  have hInt_EX : Integrable
      (fun f_X => μ.real (swError_EX μ Xs Ys n ε f_X)) B_X := by
    refine hInt_B_X _ (fun _ => measureReal_nonneg) (fun f_X => ?_)
    have h_le : μ (swError_EX μ Xs Ys n ε f_X) ≤ 1 := prob_le_one
    unfold Measure.real
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr h_le
  have hInt_EY : Integrable
      (fun f_Y => μ.real (swError_EY μ Xs Ys n ε f_Y)) B_Y := by
    refine hInt_B_Y _ (fun _ => measureReal_nonneg) (fun f_Y => ?_)
    have h_le : μ (swError_EY μ Xs Ys n ε f_Y) ≤ 1 := prob_le_one
    unfold Measure.real
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr h_le
  -- Integrability of inner integral over EXY_strict (∫ f_Y, μ.real EXY_strict ∂B_Y)
  -- in f_X. Each inner integral is bounded by 1.
  have h_EXY_strict_nn : ∀ (f_X : (Fin n → α) → Fin M_X)
      (f_Y : (Fin n → β) → Fin M_Y),
      0 ≤ μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) := fun _ _ =>
    measureReal_nonneg
  have h_EXY_strict_le_one : ∀ (f_X : (Fin n → α) → Fin M_X)
      (f_Y : (Fin n → β) → Fin M_Y),
      μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ≤ 1 := by
    intro f_X f_Y
    have h_le : μ (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ≤ 1 := prob_le_one
    unfold Measure.real
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr h_le
  have hInt_EXY_strict_inner : ∀ f_X : (Fin n → α) → Fin M_X,
      Integrable (fun f_Y => μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)) B_Y :=
    fun f_X => hInt_B_Y _ (fun _ => h_EXY_strict_nn f_X _)
      (fun _ => h_EXY_strict_le_one f_X _)
  have hInt_EXY_strict_outer : Integrable
      (fun f_X => ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y) B_X := by
    refine hInt_B_X _ ?_ ?_
    · intro f_X
      refine integral_nonneg (fun f_Y => ?_)
      exact h_EXY_strict_nn f_X f_Y
    · intro f_X
      calc ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y
          ≤ ∫ _ : (Fin n → β) → Fin M_Y, (1 : ℝ) ∂B_Y :=
            integral_mono (hInt_EXY_strict_inner f_X) (integrable_const 1)
              (fun f_Y => h_EXY_strict_le_one f_X f_Y)
        _ = 1 := by rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
  -- Integrability of swErrorProb outer integral (in f_X), bounded by 1.
  have hInt_swErr_outer : Integrable
      (fun f_X => ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                    (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y) B_X := by
    refine hInt_B_X _ ?_ ?_
    · intro f_X
      exact integral_nonneg (fun f_Y => h_swErr_nn f_X f_Y)
    · intro f_X
      calc ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                    (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y
          ≤ ∫ _ : (Fin n → β) → Fin M_Y, (1 : ℝ) ∂B_Y :=
            integral_mono (hInt_swErr_inner f_X) (integrable_const 1)
              (fun f_Y => h_swErr_le_one f_X f_Y)
        _ = 1 := by rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
  -- Inner integral inequality (for each fixed f_X):
  -- ∫ f_Y, swErrorProb ... ∂B_Y ≤ μ.real E0 + 2 μ.real (EX f_X)
  --                              + 2 (∫ f_Y, μ.real (EY f_Y) ∂B_Y)
  --                              + ∫ f_Y, μ.real (EXY_strict f_X f_Y) ∂B_Y.
  have h_inner_ineq : ∀ f_X : (Fin n → α) → Fin M_X,
      ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y
        ≤ μ.real (swError_E0 μ Xs Ys n ε)
          + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
          + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
          + ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y := by
    intro f_X
    -- Build the RHS as an integrand for integral_mono.
    have h_const_E0 : Integrable
        (fun _ : (Fin n → β) → Fin M_Y => μ.real (swError_E0 μ Xs Ys n ε)) B_Y :=
      integrable_const _
    have h_const_EX : Integrable
        (fun _ : (Fin n → β) → Fin M_Y =>
          (2 : ℝ) * μ.real (swError_EX μ Xs Ys n ε f_X)) B_Y :=
      integrable_const _
    have h_2EY : Integrable
        (fun f_Y => (2 : ℝ) * μ.real (swError_EY μ Xs Ys n ε f_Y)) B_Y :=
      hInt_EY.const_mul 2
    have h_EXY_strict_inner_f := hInt_EXY_strict_inner f_X
    -- pointwise summand-by-summand.
    have h_RHS_integrable : Integrable
        (fun f_Y => μ.real (swError_E0 μ Xs Ys n ε)
                  + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                  + 2 * μ.real (swError_EY μ Xs Ys n ε f_Y)
                  + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)) B_Y := by
      have h_sum1 : Integrable
          (fun _ : (Fin n → β) → Fin M_Y =>
            μ.real (swError_E0 μ Xs Ys n ε)
              + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)) B_Y :=
        h_const_E0.add h_const_EX
      have h_sum2 : Integrable
          (fun f_Y =>
            μ.real (swError_E0 μ Xs Ys n ε)
              + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
              + 2 * μ.real (swError_EY μ Xs Ys n ε f_Y)) B_Y :=
        h_sum1.add h_2EY
      exact h_sum2.add h_EXY_strict_inner_f
    have h_mono : ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                      (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y
            ≤ ∫ f_Y, (μ.real (swError_E0 μ Xs Ys n ε)
                  + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                  + 2 * μ.real (swError_EY μ Xs Ys n ε f_Y)
                  + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)) ∂B_Y :=
      integral_mono (hInt_swErr_inner f_X) h_RHS_integrable
        (fun f_Y => h_pointwise f_X f_Y)
    -- Split the integrated RHS into 4 pieces.
    have h_split : ∫ f_Y, (μ.real (swError_E0 μ Xs Ys n ε)
                + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                + 2 * μ.real (swError_EY μ Xs Ys n ε f_Y)
                + μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y)) ∂B_Y
          = μ.real (swError_E0 μ Xs Ys n ε)
            + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
            + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
            + ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y := by
      have h_sum1 : Integrable
          (fun _ : (Fin n → β) → Fin M_Y =>
            μ.real (swError_E0 μ Xs Ys n ε)
              + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)) B_Y :=
        h_const_E0.add h_const_EX
      have h_sum2 : Integrable
          (fun f_Y =>
            μ.real (swError_E0 μ Xs Ys n ε)
              + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
              + 2 * μ.real (swError_EY μ Xs Ys n ε f_Y)) B_Y :=
        h_sum1.add h_2EY
      rw [integral_add h_sum2 h_EXY_strict_inner_f,
          integral_add h_sum1 h_2EY,
          integral_add h_const_E0 h_const_EX]
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [integral_const_mul]
    linarith [h_mono, h_split.le, h_split.ge]
  -- Integrability of the inner-bound (the RHS of h_inner_ineq) over B_X.
  have hInt_RHS_outer : Integrable
      (fun f_X => μ.real (swError_E0 μ Xs Ys n ε)
                + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
                + ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y) B_X := by
    have h_const_E0 : Integrable
        (fun _ : (Fin n → α) → Fin M_X => μ.real (swError_E0 μ Xs Ys n ε)) B_X :=
      integrable_const _
    have h_2EX : Integrable
        (fun f_X => (2 : ℝ) * μ.real (swError_EX μ Xs Ys n ε f_X)) B_X :=
      hInt_EX.const_mul 2
    have h_const_2EY : Integrable
        (fun _ : (Fin n → α) → Fin M_X =>
          (2 : ℝ) * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)) B_X :=
      integrable_const _
    have h_sum1 : Integrable
        (fun f_X => μ.real (swError_E0 μ Xs Ys n ε)
                  + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)) B_X :=
      h_const_E0.add h_2EX
    have h_sum2 : Integrable
        (fun f_X => μ.real (swError_E0 μ Xs Ys n ε)
                  + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                  + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)) B_X :=
      h_sum1.add h_const_2EY
    exact h_sum2.add hInt_EXY_strict_outer
  -- Apply integral_mono on the outer integral.
  have h_outer_mono :
      ∫ f_X, ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                      (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y ∂B_X
        ≤ ∫ f_X, (μ.real (swError_E0 μ Xs Ys n ε)
                + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
                + ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y) ∂B_X :=
    integral_mono hInt_swErr_outer hInt_RHS_outer h_inner_ineq
  -- Split the outer integral into 4 pieces.
  have h_outer_split :
      ∫ f_X, (μ.real (swError_E0 μ Xs Ys n ε)
              + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
              + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
              + ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y) ∂B_X
        = μ.real (swError_E0 μ Xs Ys n ε)
          + 2 * (∫ f_X, μ.real (swError_EX μ Xs Ys n ε f_X) ∂B_X)
          + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
          + ∫ f_X, ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y ∂B_X := by
    have h_const_E0 : Integrable
        (fun _ : (Fin n → α) → Fin M_X => μ.real (swError_E0 μ Xs Ys n ε)) B_X :=
      integrable_const _
    have h_2EX : Integrable
        (fun f_X => (2 : ℝ) * μ.real (swError_EX μ Xs Ys n ε f_X)) B_X :=
      hInt_EX.const_mul 2
    have h_const_2EY : Integrable
        (fun _ : (Fin n → α) → Fin M_X =>
          (2 : ℝ) * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)) B_X :=
      integrable_const _
    have h_sum1 : Integrable
        (fun f_X => μ.real (swError_E0 μ Xs Ys n ε)
                  + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)) B_X :=
      h_const_E0.add h_2EX
    have h_sum2 : Integrable
        (fun f_X => μ.real (swError_E0 μ Xs Ys n ε)
                  + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
                  + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)) B_X :=
      h_sum1.add h_const_2EY
    rw [integral_add h_sum2 hInt_EXY_strict_outer,
        integral_add h_sum1 h_const_2EY,
        integral_add h_const_E0 h_2EX]
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [integral_const_mul]
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- Combine the outer monotone bound with the split + E.2/E.3/E.4.
  calc ∫ f_X, ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                      (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂B_Y ∂B_X
      ≤ ∫ f_X, (μ.real (swError_E0 μ Xs Ys n ε)
              + 2 * μ.real (swError_EX μ Xs Ys n ε f_X)
              + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
              + ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y) ∂B_X :=
        h_outer_mono
    _ = μ.real (swError_E0 μ Xs Ys n ε)
          + 2 * (∫ f_X, μ.real (swError_EX μ Xs Ys n ε f_X) ∂B_X)
          + 2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
          + ∫ f_X, ∫ f_Y, μ.real (swError_EXY_strict μ Xs Ys n ε f_X f_Y) ∂B_Y ∂B_X :=
        h_outer_split
    _ ≤ μ.real (swError_E0 μ Xs Ys n ε)
          + 2 * (Real.exp ((n : ℝ) *
              (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
                * ((M_X : ℝ))⁻¹)
          + 2 * (Real.exp ((n : ℝ) *
              (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε))
                * ((M_Y : ℝ))⁻¹)
          + Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) + ε))
              * ((M_X : ℝ))⁻¹ * ((M_Y : ℝ))⁻¹ := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          have hmono_E2 :
              2 * (∫ f_X, μ.real (swError_EX μ Xs Ys n ε f_X) ∂B_X)
                ≤ 2 * (Real.exp ((n : ℝ) *
                    (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
                  * ((M_X : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left hE2 h2
          have hmono_E3 :
              2 * (∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂B_Y)
                ≤ 2 * (Real.exp ((n : ℝ) *
                    (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε))
                  * ((M_Y : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left hE3 h2
          linarith [hmono_E2, hmono_E3, hE4]

omit [DecidableEq α] [DecidableEq β] in
/-- Pigeonhole: from a double-integral bound `≤ δ`, extract a deterministic encoder
pair `(f_X, f_Y)` with `g f_X f_Y ≤ δ`, by applying the first moment method
(`MeasureTheory.exists_le_integral`) to the outer and inner integrals in turn. -/
private lemma exists_pair_le_of_binning_integral_le
    {n M_X M_Y : ℕ} [NeZero M_X] [NeZero M_Y]
    (g : ((Fin n → α) → Fin M_X) → ((Fin n → β) → Fin M_Y) → ℝ)
    (hg_int_inner : ∀ f_X, Integrable (fun f_Y => g f_X f_Y) (binningMeasure β n M_Y))
    (hg_int_outer :
      Integrable (fun f_X => ∫ f_Y, g f_X f_Y ∂(binningMeasure β n M_Y))
        (binningMeasure α n M_X))
    {δ : ℝ}
    (hδ : ∫ f_X, ∫ f_Y, g f_X f_Y
              ∂(binningMeasure β n M_Y) ∂(binningMeasure α n M_X) ≤ δ) :
    ∃ f_X : (Fin n → α) → Fin M_X, ∃ f_Y : (Fin n → β) → Fin M_Y,
      g f_X f_Y ≤ δ := by
  classical
  -- First moment on the outer integral: ∃ f_X, ∫ f_Y, g f_X f_Y ≤ ∫∫.
  obtain ⟨f_X, hf_X⟩ : ∃ f_X : (Fin n → α) → Fin M_X,
      (∫ f_Y, g f_X f_Y ∂(binningMeasure β n M_Y))
        ≤ ∫ f_X', (∫ f_Y, g f_X' f_Y ∂(binningMeasure β n M_Y))
            ∂(binningMeasure α n M_X) :=
    MeasureTheory.exists_le_integral hg_int_outer
  have hf_X_bound :
      (∫ f_Y, g f_X f_Y ∂(binningMeasure β n M_Y)) ≤ δ :=
    le_trans hf_X hδ
  -- First moment on the inner integral: ∃ f_Y, g f_X f_Y ≤ ∫ f_Y, g f_X f_Y.
  obtain ⟨f_Y, hf_Y⟩ : ∃ f_Y : (Fin n → β) → Fin M_Y,
      g f_X f_Y ≤ ∫ f_Y', g f_X f_Y' ∂(binningMeasure β n M_Y) :=
    MeasureTheory.exists_le_integral (hg_int_inner f_X)
  exact ⟨f_X, f_Y, le_trans hf_Y hf_X_bound⟩

/-! ## Exponential squeeze with rate parametrization

For `M_n := codebookSize R n = ⌈exp(n R)⌉`, the inverse `M_n⁻¹ ≤ exp(-n R)`, so each
expectation bound `exp(n c) · M_n⁻¹` is `≤ exp(n (c - R))`, which tends to `0`
whenever `c < R`. This turns the per-term expectation bounds into `Tendsto (𝓝 0)`. -/

/-- `(codebookSize R n)⁻¹ ≤ exp(-n R)`, from `exp(n R) ≤ ⌈exp(n R)⌉ = codebookSize R n`.
@audit:ok -/
private lemma codebookSize_inv_le_exp_neg (R : ℝ) (n : ℕ) :
    ((codebookSize R n : ℝ))⁻¹ ≤ Real.exp (-(n : ℝ) * R) := by
  have hpos : (0 : ℝ) < Real.exp ((n : ℝ) * R) := Real.exp_pos _
  have hle : Real.exp ((n : ℝ) * R) ≤ (codebookSize R n : ℝ) := by
    unfold codebookSize
    exact Nat.le_ceil _
  calc ((codebookSize R n : ℝ))⁻¹
      ≤ (Real.exp ((n : ℝ) * R))⁻¹ := inv_anti₀ hpos hle
    _ = Real.exp (-(n : ℝ) * R) := by
        rw [← Real.exp_neg]; ring_nf

/-- For `c < R`, `exp(n c) · (codebookSize R n)⁻¹ → 0`.
@audit:ok -/
private lemma tendsto_exp_mul_codebookSize_inv {c R : ℝ} (hcR : c < R) :
    Filter.Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * c) * ((codebookSize R n : ℝ))⁻¹)
      Filter.atTop (𝓝 0) := by
  -- Upper bound by `exp(n (c - R)) = exp(-(n (R - c)))`, which → 0.
  have hub : Filter.Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * (c - R))) Filter.atTop (𝓝 0) := by
    have hRc : 0 < R - c := sub_pos.mpr hcR
    -- `n * (c - R) = -(n * (R - c))`, and `n * (R - c) → ∞`.
    have htend : Filter.Tendsto
        (fun n : ℕ => (n : ℝ) * (R - c)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const hRc tendsto_natCast_atTop_atTop
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp htend
    refine hcomp.congr (fun n => ?_)
    simp only [Function.comp_apply]
    rw [show (n : ℝ) * (c - R) = -((n : ℝ) * (R - c)) by ring]
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hub
  · exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (by positivity))
  · calc Real.exp ((n : ℝ) * c) * ((codebookSize R n : ℝ))⁻¹
        ≤ Real.exp ((n : ℝ) * c) * Real.exp (-(n : ℝ) * R) :=
          mul_le_mul_of_nonneg_left (codebookSize_inv_le_exp_neg R n)
            (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * (c - R)) := by
          rw [← Real.exp_add]; ring_nf

/-- For `c < R_X + R_Y`,
`exp(n c) · (codebookSize R_X n)⁻¹ · (codebookSize R_Y n)⁻¹ → 0`.
@audit:ok -/
private lemma tendsto_exp_mul_codebookSize_inv₂ {c R_X R_Y : ℝ}
    (hcR : c < R_X + R_Y) :
    Filter.Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * c)
          * ((codebookSize R_X n : ℝ))⁻¹ * ((codebookSize R_Y n : ℝ))⁻¹)
      Filter.atTop (𝓝 0) := by
  have hub : Filter.Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) * (c - (R_X + R_Y)))) Filter.atTop (𝓝 0) := by
    have hRc : 0 < (R_X + R_Y) - c := sub_pos.mpr hcR
    have htend : Filter.Tendsto
        (fun n : ℕ => (n : ℝ) * ((R_X + R_Y) - c)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const hRc tendsto_natCast_atTop_atTop
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp htend
    refine hcomp.congr (fun n => ?_)
    simp only [Function.comp_apply]
    rw [show (n : ℝ) * (c - (R_X + R_Y)) = -((n : ℝ) * ((R_X + R_Y) - c)) by ring]
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hub
  · refine mul_nonneg (mul_nonneg (Real.exp_pos _).le ?_) ?_ <;>
      exact inv_nonneg.mpr (by positivity)
  · calc Real.exp ((n : ℝ) * c)
            * ((codebookSize R_X n : ℝ))⁻¹ * ((codebookSize R_Y n : ℝ))⁻¹
        ≤ Real.exp ((n : ℝ) * c)
            * Real.exp (-(n : ℝ) * R_X) * Real.exp (-(n : ℝ) * R_Y) := by
          have h1 : ((codebookSize R_X n : ℝ))⁻¹ ≤ Real.exp (-(n : ℝ) * R_X) :=
            codebookSize_inv_le_exp_neg R_X n
          have h2 : ((codebookSize R_Y n : ℝ))⁻¹ ≤ Real.exp (-(n : ℝ) * R_Y) :=
            codebookSize_inv_le_exp_neg R_Y n
          gcongr
      _ = Real.exp ((n : ℝ) * (c - (R_X + R_Y))) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-! ## Slepian–Wolf full rate region achievability

Assembles the error decomposition, the per-term binning bounds, the total binning
expectation, the pigeonhole extraction, and the exponential squeeze into the
achievability of the full Slepian–Wolf rate region: for any rates strictly above the
conditional entropies `H(X|Y)`, `H(Y|X)` and the joint entropy `H(X,Y)`, there is a
sequence of binning encoders and joint typicality decoders whose error probability
tends to `0`. -/

omit [DecidableEq α] [DecidableEq β] in
/-- **Slepian–Wolf full rate region achievability** (Cover–Thomas 15.4.1). For an
i.i.d. source `(Xⁿ, Yⁿ)` with full support, any rate pair `(R_X, R_Y)` with
`R_X > H(X|Y)`, `R_Y > H(Y|X)`, `R_X + R_Y > H(X,Y)` is achievable: there are
codebook sizes `M_X, M_Y` with the required asymptotic rates and encoders/decoders
whose error probability → 0.
@audit:ok -/
@[entry_point]
theorem slepian_wolf_full_rate_region_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {R_X R_Y : ℝ}
    (hRX : InformationTheory.MeasureFano.condEntropy μ (Xs 0) (Ys 0) < R_X)
    (hRY : InformationTheory.MeasureFano.condEntropy μ (Ys 0) (Xs 0) < R_Y)
    (hRXY : entropy μ (jointSequence Xs Ys 0) < R_X + R_Y) :
    ∃ (M_X M_Y : ℕ → ℕ),
      (∀ n, 0 < M_X n) ∧ (∀ n, 0 < M_Y n) ∧
    ∃ (f_X : ∀ n, (Fin n → α) → Fin (M_X n))
      (f_Y : ∀ n, (Fin n → β) → Fin (M_Y n))
      (d : ∀ n, Fin (M_X n) × Fin (M_Y n) → (Fin n → α) × (Fin n → β)),
      Filter.Tendsto (fun n => Real.log (M_X n : ℝ) / n) Filter.atTop (𝓝 R_X) ∧
      Filter.Tendsto (fun n => Real.log (M_Y n : ℝ) / n) Filter.atTop (𝓝 R_Y) ∧
      Filter.Tendsto (fun n => swErrorProb μ (jointRV Xs n) (jointRV Ys n)
                          (f_X n) (f_Y n) (d n)) Filter.atTop (𝓝 0) := by
  classical
  set cX : ℝ := InformationTheory.MeasureFano.condEntropy μ (Xs 0) (Ys 0) with hcX
  set cY : ℝ := InformationTheory.MeasureFano.condEntropy μ (Ys 0) (Xs 0) with hcY
  set H : ℝ := entropy μ (jointSequence Xs Ys 0) with hH
  -- Rates are positive (conditional entropies are nonnegative).
  have hcX0 : 0 ≤ cX := condEntropy_nonneg μ (Xs 0) (Ys 0)
  have hcY0 : 0 ≤ cY := condEntropy_nonneg μ (Ys 0) (Xs 0)
  have hRX0 : 0 < R_X := lt_of_le_of_lt hcX0 hRX
  have hRY0 : 0 < R_Y := lt_of_le_of_lt hcY0 hRY
  -- Choose ε making all three exponent gaps strictly negative.
  set ε : ℝ := min (min ((R_X - cX) / 3) ((R_Y - cY) / 3)) ((R_X + R_Y - H) / 2)
    with hε_def
  have hε : 0 < ε := by
    refine lt_min (lt_min ?_ ?_) ?_
    · have : 0 < R_X - cX := sub_pos.mpr hRX
      positivity
    · have : 0 < R_Y - cY := sub_pos.mpr hRY
      positivity
    · have : 0 < R_X + R_Y - H := sub_pos.mpr hRXY
      positivity
  -- The three exponent gaps are strictly below the corresponding rate(s).
  have hgapX : cX + 2 * ε < R_X := by
    have h1 : ε ≤ (R_X - cX) / 3 := le_trans (min_le_left _ _) (min_le_left _ _)
    nlinarith [h1, hε]
  have hgapY : cY + 2 * ε < R_Y := by
    have h1 : ε ≤ (R_Y - cY) / 3 := le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith [h1, hε]
  have hgapXY : H + ε < R_X + R_Y := by
    have h1 : ε ≤ (R_X + R_Y - H) / 2 := min_le_right _ _
    nlinarith [h1, hε]
  -- Codebook sizes.
  set M_X : ℕ → ℕ := fun n => codebookSize R_X n with hM_X
  set M_Y : ℕ → ℕ := fun n => codebookSize R_Y n with hM_Y
  -- The total-expectation bound `B n` (RHS of `swErrorProb_total_expectation_le`).
  set B : ℕ → ℝ := fun n =>
      μ.real (swError_E0 μ Xs Ys n ε)
        + 2 * (Real.exp ((n : ℝ) * (H - entropy μ (Ys 0) + 2 * ε))
            * ((M_X n : ℝ))⁻¹)
        + 2 * (Real.exp ((n : ℝ) * (H - entropy μ (Xs 0) + 2 * ε))
            * ((M_Y n : ℝ))⁻¹)
        + Real.exp ((n : ℝ) * (H + ε))
            * ((M_X n : ℝ))⁻¹ * ((M_Y n : ℝ))⁻¹ with hB
  -- Per-n existence of an encoder pair with error ≤ B n.
  have hExists : ∀ n : ℕ, ∃ (f_X : (Fin n → α) → Fin (M_X n))
      (f_Y : (Fin n → β) → Fin (M_Y n)),
      swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
          (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ≤ B n := by
    intro n
    -- Total expectation bound (F.1).
    have htotal := swErrorProb_total_expectation_le (n := n) (M_X := M_X n)
      (M_Y := M_Y n) μ Xs Ys hXs hYs hindepY_full hidentY hindepX_full hidentX
      hindepZ_full hidentZ hposX hposY hposZ hε
    -- Integrability of the swErrorProb integrand (bounded by 1, discrete).
    have hg_nn : ∀ (f_X : (Fin n → α) → Fin (M_X n))
        (f_Y : (Fin n → β) → Fin (M_Y n)),
        0 ≤ swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
              (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) := by
      intro f_X f_Y; unfold swErrorProb; exact measureReal_nonneg
    have hg_le : ∀ (f_X : (Fin n → α) → Fin (M_X n))
        (f_Y : (Fin n → β) → Fin (M_Y n)),
        swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
              (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ≤ 1 := by
      intro f_X f_Y
      unfold swErrorProb Measure.real
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr prob_le_one
    have hInt_inner : ∀ f_X : (Fin n → α) → Fin (M_X n),
        Integrable (fun f_Y => swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                    (swJointTypicalDecoder μ Xs Ys ε f_X f_Y))
          (binningMeasure β n (M_Y n)) := by
      intro f_X
      refine ⟨Measurable.aestronglyMeasurable Measurable.of_discrete, ?_⟩
      refine (hasFiniteIntegral_def _ _).mpr ?_
      calc ∫⁻ f_Y, ‖swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)‖ₑ
              ∂(binningMeasure β n (M_Y n))
          ≤ ∫⁻ _, 1 ∂(binningMeasure β n (M_Y n)) := by
            refine lintegral_mono fun f_Y => ?_
            have hb : ‖swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)‖₊ ≤ 1 := by
              rw [Real.nnnorm_of_nonneg (hg_nn f_X f_Y)]
              exact_mod_cast hg_le f_X f_Y
            rw [show ‖_‖ₑ = ((‖_‖₊ : ℝ≥0∞)) from rfl]
            have : ((‖swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)‖₊ : ℝ≥0∞)) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
              exact_mod_cast hb
            simpa using this
        _ = binningMeasure β n (M_Y n) Set.univ := by rw [lintegral_const, one_mul]
        _ < ∞ := measure_lt_top _ _
    have hInt_outer : Integrable
        (fun f_X => ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                    (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
                    ∂(binningMeasure β n (M_Y n))) (binningMeasure α n (M_X n)) := by
      refine ⟨Measurable.aestronglyMeasurable Measurable.of_discrete, ?_⟩
      refine (hasFiniteIntegral_def _ _).mpr ?_
      calc ∫⁻ f_X, ‖∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
                ∂(binningMeasure β n (M_Y n))‖ₑ ∂(binningMeasure α n (M_X n))
          ≤ ∫⁻ _, 1 ∂(binningMeasure α n (M_X n)) := by
            refine lintegral_mono fun f_X => ?_
            have hnn : 0 ≤ ∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂(binningMeasure β n (M_Y n)) :=
              integral_nonneg (fun f_Y => hg_nn f_X f_Y)
            have hle1 : (∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y) ∂(binningMeasure β n (M_Y n)))
                  ≤ 1 := by
              calc _ ≤ ∫ _ : (Fin n → β) → Fin (M_Y n), (1 : ℝ) ∂(binningMeasure β n (M_Y n)) :=
                    integral_mono (hInt_inner f_X) (integrable_const 1)
                      (fun f_Y => hg_le f_X f_Y)
                _ = 1 := by rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
            have hb : ‖∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
                  ∂(binningMeasure β n (M_Y n))‖₊ ≤ 1 := by
              rw [Real.nnnorm_of_nonneg hnn]
              exact_mod_cast hle1
            rw [show ‖_‖ₑ = ((‖_‖₊ : ℝ≥0∞)) from rfl]
            have : ((‖∫ f_Y, swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
                  (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
                  ∂(binningMeasure β n (M_Y n))‖₊ : ℝ≥0∞)) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
              exact_mod_cast hb
            simpa using this
        _ = binningMeasure α n (M_X n) Set.univ := by rw [lintegral_const, one_mul]
        _ < ∞ := measure_lt_top _ _
    -- Pigeonhole (F.2).
    exact exists_pair_le_of_binning_integral_le _ hInt_inner hInt_outer htotal
  -- Functionalize the choice.
  refine ⟨M_X, M_Y, fun n => codebookSize_pos R_X n, fun n => codebookSize_pos R_Y n,
    fun n => (hExists n).choose, fun n => (hExists n).choose_spec.choose,
    fun n => swJointTypicalDecoder μ Xs Ys ε (hExists n).choose
      (hExists n).choose_spec.choose, ?_, ?_, ?_⟩
  · -- Rate tendsto for R_X.
    exact codebookSize_log_div_tendsto hRX0
  · -- Rate tendsto for R_Y.
    exact codebookSize_log_div_tendsto hRY0
  · -- Error tendsto: 0 ≤ swErrorProb ≤ B n, and B n → 0.
    -- Bridge identities relating the exponent bases to the conditional entropies.
    have hbridgeY : H - entropy μ (Xs 0) = cY := by
      rw [hH, hcY]
      exact entropy_joint_sub_marginal_eq_condEntropy μ (Xs 0) (Ys 0) (hXs 0) (hYs 0)
    have hbridgeX : H - entropy μ (Ys 0) = cX := by
      rw [hH, hcX]
      have hswap :
          entropy μ (jointSequence Xs Ys 0)
            = entropy μ (fun ω => (Ys 0 ω, Xs 0 ω)) := by
        have he := entropy_measurableEquiv_comp (μ := μ)
          (Xs := fun ω => (Xs 0 ω, Ys 0 ω))
          (hXs := (hXs 0).prodMk (hYs 0))
          (MeasurableEquiv.prodComm : (α × β) ≃ᵐ (β × α))
        simpa [jointSequence, MeasurableEquiv.prodComm] using he.symm
      rw [hswap]
      exact entropy_joint_sub_marginal_eq_condEntropy μ (Ys 0) (Xs 0) (hYs 0) (hXs 0)
    -- B n → 0 (sum of four tendsto-to-0 sequences).
    have hE0 : Filter.Tendsto (fun n => μ.real (swError_E0 μ Xs Ys n ε))
        Filter.atTop (𝓝 0) :=
      swError_E0_prob_tendsto_zero μ Xs Ys hXs hYs
        (fun i j hij => hindepX_full.indepFun hij) hidentX
        (fun i j hij => hindepY_full.indepFun hij) hidentY
        (fun i j hij => hindepZ_full.indepFun hij) hidentZ hε
    have hEX : Filter.Tendsto
        (fun n : ℕ => (2 : ℝ) * (Real.exp ((n : ℝ) * (H - entropy μ (Ys 0) + 2 * ε))
            * ((M_X n : ℝ))⁻¹)) Filter.atTop (𝓝 0) := by
      have hc : H - entropy μ (Ys 0) + 2 * ε < R_X := by rw [hbridgeX]; exact hgapX
      have h := (tendsto_exp_mul_codebookSize_inv hc).const_mul (2 : ℝ)
      rw [mul_zero] at h
      exact h
    have hEY : Filter.Tendsto
        (fun n : ℕ => (2 : ℝ) * (Real.exp ((n : ℝ) * (H - entropy μ (Xs 0) + 2 * ε))
            * ((M_Y n : ℝ))⁻¹)) Filter.atTop (𝓝 0) := by
      have hc : H - entropy μ (Xs 0) + 2 * ε < R_Y := by rw [hbridgeY]; exact hgapY
      have h := (tendsto_exp_mul_codebookSize_inv hc).const_mul (2 : ℝ)
      rw [mul_zero] at h
      exact h
    have hEXY : Filter.Tendsto
        (fun n : ℕ => Real.exp ((n : ℝ) * (H + ε))
            * ((M_X n : ℝ))⁻¹ * ((M_Y n : ℝ))⁻¹) Filter.atTop (𝓝 0) := by
      exact tendsto_exp_mul_codebookSize_inv₂ (c := H + ε) (R_X := R_X) (R_Y := R_Y) hgapXY
    have hB : Filter.Tendsto B Filter.atTop (𝓝 0) := by
      have h123 := (hE0.add hEX).add hEY
      have h1234 := h123.add hEXY
      simpa [hB, add_zero] using h1234
    -- Squeeze the actual error between 0 and B n.
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hB
    · unfold swErrorProb; exact measureReal_nonneg
    · exact (hExists n).choose_spec.choose_spec

end InformationTheory.Shannon.ChannelCoding
