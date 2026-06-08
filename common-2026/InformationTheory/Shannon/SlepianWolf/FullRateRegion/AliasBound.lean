import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SlepianWolf.Achievability
import InformationTheory.Shannon.SlepianWolf.Binning
import InformationTheory.Shannon.SlepianWolf.ConditionalTypicalSlice
import InformationTheory.Shannon.SlepianWolf.FullRateRegion.Core

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

/-! ## Phase E common utility — alias expectation bound. -/

/-- **Random-binning alias expectation bound (E.2 / E.3 / E.4 common utility).**

Fixing the source realization, let `S` be a (deterministic) set of candidate alias
sequences `x'`. Then the binning-measure probability that some `x' ∈ S` with
`x' ≠ truth` hashes to the same bin as `truth` is bounded by `|S| / M_X`.

This is the union-bound + collision-probability skeleton shared by all three
non-`E_0` error events: the only thing that varies between them is the choice of
`S` (a conditional-typical fiber size on the `X` axis, on the `Y` axis, or on the
joint axis).

The `truth` may or may not lie in `S`; the constraint `x' ≠ truth` filters it out
of the union, but we coarsely bound the count by `|S|` (not `|S \ {truth}|`) for
downstream cleanliness. -/
private lemma binning_alias_expectation_le_aux
    {n M_X : ℕ} [NeZero M_X]
    (truth : Fin n → α) (S : Finset (Fin n → α)) :
    (binningMeasure α n M_X).real
        {f_X | ∃ x' ∈ S, x' ≠ truth ∧ f_X x' = f_X truth}
      ≤ S.card * ((M_X : ℝ))⁻¹ := by
  classical
  -- Step 1: the event is contained in the union over `x' ∈ S.filter (· ≠ truth)`
  -- of the per-alias collision event `{f | f x' = f truth}`.
  set T : Finset (Fin n → α) := S.filter (· ≠ truth) with hT_def
  set evt : Set ((Fin n → α) → Fin M_X) :=
      {f_X | ∃ x' ∈ S, x' ≠ truth ∧ f_X x' = f_X truth} with hevt_def
  set unionEvt : Set ((Fin n → α) → Fin M_X) :=
      ⋃ x' ∈ T, {f_X | f_X x' = f_X truth} with hunionEvt_def
  have h_sub : evt ⊆ unionEvt := by
    intro f hf
    rcases hf with ⟨x', hxS, hne, hcoll⟩
    refine Set.mem_iUnion₂.mpr ⟨x', ?_, hcoll⟩
    simp [T, hxS, hne]
  -- Step 2: lift to `μ.real` via monotonicity.
  have h_meas_evt : MeasurableSet evt := (Set.toFinite _).measurableSet
  have h_meas_unionEvt : MeasurableSet unionEvt := (Set.toFinite _).measurableSet
  have h_step1 :
      (binningMeasure α n M_X).real evt
        ≤ (binningMeasure α n M_X).real unionEvt :=
    measureReal_mono h_sub (measure_ne_top _ _)
  -- Step 3: `measureReal_biUnion_finset_le` for the union bound.
  have h_step2 :
      (binningMeasure α n M_X).real unionEvt
        ≤ ∑ x' ∈ T, (binningMeasure α n M_X).real {f_X | f_X x' = f_X truth} :=
    measureReal_biUnion_finset_le _ _
  -- Step 4: each summand is exactly `(M_X)⁻¹` since `x' ≠ truth` in the filter.
  have h_summand : ∀ x' ∈ T,
      (binningMeasure α n M_X).real {f_X | f_X x' = f_X truth} = ((M_X : ℝ))⁻¹ := by
    intro x' hx'
    have hne : x' ≠ truth := by
      have := (Finset.mem_filter.mp hx').2
      exact this
    -- `binning_collision_prob` gives `(M_X)⁻¹` for distinct inputs.
    exact binning_collision_prob hne
  have h_step3 :
      (∑ x' ∈ T, (binningMeasure α n M_X).real {f_X | f_X x' = f_X truth})
        = (T.card : ℝ) * ((M_X : ℝ))⁻¹ := by
    rw [Finset.sum_congr rfl h_summand, Finset.sum_const, nsmul_eq_mul]
  -- Step 5: `T.card ≤ S.card`.
  have h_card : (T.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le S _
  -- Combine.
  have h_inv_nn : (0 : ℝ) ≤ ((M_X : ℝ))⁻¹ := by
    have : (0 : ℝ) ≤ (M_X : ℝ) := by exact_mod_cast Nat.zero_le _
    exact inv_nonneg.mpr this
  calc (binningMeasure α n M_X).real evt
      ≤ (binningMeasure α n M_X).real unionEvt := h_step1
    _ ≤ ∑ x' ∈ T, (binningMeasure α n M_X).real {f_X | f_X x' = f_X truth} := h_step2
    _ = (T.card : ℝ) * ((M_X : ℝ))⁻¹ := h_step3
    _ ≤ (S.card : ℝ) * ((M_X : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_right h_card h_inv_nn

/-! ## Phase E.2 — `swError_EX` expectation bound under random binning.

The expected `μ`-mass of the `E_X` error event over the random binning
hash `f_X ∼ binningMeasure α n M_X` is bounded by
`exp(n · (H(X,Y) - H(Y) + 2ε)) / M_X` — the conditional-typical fiber
size on the `X` axis divided by the bin count. This is the heart of the
random-binning achievability argument on the `X`-only error axis.

Strategy (Fubini + per-`ω` slice argument):

1. **Tonelli swap** (Bochner integral form): the outer integral over `f_X`
   of `μ.real (swError_EX ... f_X)` becomes the outer integral over `ω` of
   the inner `(binningMeasure ...).real`-mass of the per-`ω` collision
   event. Concretely we rewrite each set's `Measure.real` as the Bochner
   integral of its indicator and apply
   `MeasureTheory.integral_integral_swap` on the product `μ ⊗ binningMeasure`.

2. **Per-`ω` rewrite**: for fixed `ω`, the slice is exactly
   `{f_X | ∃ x' ∈ conditionalTypicalSlice μ Xs Ys n ε (jointRV Ys n ω),
            x' ≠ jointRV Xs n ω ∧ f_X x' = f_X (jointRV Xs n ω)}`
   by `mem_conditionalTypicalSlice_iff` (definitional).

3. **Apply `binning_alias_expectation_le_aux`** with
   `S := slice.toFinite.toFinset` and `truth := jointRV Xs n ω`. This
   gives the per-`ω` bound `S.card * (M_X)⁻¹`.

4. **Slice cardinality bound (`conditionalTypicalSlice_card_le`)**: the
   slice cardinality is at most `exp(n · (H(X,Y) - H(Y) + 2ε))`, uniformly
   in `ω` (the bound is `y`-independent).

5. **Outer-integral closure**: integrate the uniform `ω`-pointwise bound
   against `μ` (a probability measure) — the integral of a constant equals
   the constant.

`hε : 0 < ε` is kept in the signature as part of the public API (matches
the `conditionalTypicalSlice_card_le` shape and is consumed by downstream
final-rate-region theorems) even though this proof does not branch on it. -/

set_option linter.unusedVariables false in
@[entry_point]
theorem swError_EX_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {n M_X : ℕ} [NeZero M_X] {ε : ℝ} (hε : 0 < ε) :
    ∫ f_X, μ.real (swError_EX μ Xs Ys n ε f_X) ∂(binningMeasure α n M_X)
      ≤ Real.exp ((n : ℝ) *
            (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
        * ((M_X : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → α) → Fin M_X) :=
    Pi.instMeasurableSingletonClass
  haveI : Fintype ((Fin n → α) → Fin M_X) := Pi.instFintype
  -- Notation.
  set B_X : Measure ((Fin n → α) → Fin M_X) := binningMeasure α n M_X with hB_X_def
  set C : ℝ := Real.exp ((n : ℝ) *
      (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε)) with hC_def
  have hC_pos : 0 < C := Real.exp_pos _
  have hC_nn : 0 ≤ C := hC_pos.le
  have hMinv_nn : (0 : ℝ) ≤ ((M_X : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  -- The joint pair-measurable map ω ↦ (jointRV Xs n ω, jointRV Ys n ω).
  have hXn : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
  have hYn : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  -- Each `swError_EX μ ... f_X` is measurable in ω.
  have h_meas_EX : ∀ f_X : (Fin n → α) → Fin M_X,
      MeasurableSet (swError_EX μ Xs Ys n ε f_X) := fun f_X =>
    measurableSet_swError_EX hXs hYs μ n ε f_X
  -- Pointwise bound on each per-`f_X` slice (Step 1, no integration yet):
  -- Per-`ω`-slice in `f_X` (the "set of bad hashes for ω") has B_X-measure
  -- ≤ slice.card * (M_X)⁻¹ via `binning_alias_expectation_le_aux`,
  -- and slice.card ≤ C via `conditionalTypicalSlice_card_le`.
  -- We package this as a pointwise inequality on `ω`.
  have h_per_omega : ∀ ω : Ω,
      B_X.real {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X}
        ≤ C * ((M_X : ℝ))⁻¹ := by
    intro ω
    -- The per-ω set unfolds to the binning-alias-expectation form.
    set y : Fin n → β := jointRV Ys n ω with hy_def
    set truth : Fin n → α := jointRV Xs n ω with htruth_def
    set slice : Set (Fin n → α) := conditionalTypicalSlice μ Xs Ys n ε y with hslice_def
    set S : Finset (Fin n → α) :=
      (conditionalTypicalSlice_finite μ Xs Ys n ε y).toFinset with hS_def
    -- Rewrite the per-ω set as binning_alias form.
    have h_set_eq : {f_X : (Fin n → α) → Fin M_X | ω ∈ swError_EX μ Xs Ys n ε f_X}
        = {f_X | ∃ x' ∈ S, x' ≠ truth ∧ f_X x' = f_X truth} := by
      ext f_X
      simp only [Set.mem_setOf_eq, swError_EX, htruth_def, hy_def, hS_def,
        Set.Finite.mem_toFinset, mem_conditionalTypicalSlice_iff]
      constructor
      · rintro ⟨x', hne, hcoll, hjts⟩
        exact ⟨x', hjts, hne, hcoll⟩
      · rintro ⟨x', hjts, hne, hcoll⟩
        exact ⟨x', hne, hcoll, hjts⟩
    rw [h_set_eq]
    -- Step A: bound by S.card * (M_X)⁻¹.
    have hA : B_X.real {f_X | ∃ x' ∈ S, x' ≠ truth ∧ f_X x' = f_X truth}
        ≤ (S.card : ℝ) * ((M_X : ℝ))⁻¹ :=
      binning_alias_expectation_le_aux (M_X := M_X) truth S
    -- Step B: slice cardinality ≤ C, hence S.card ≤ C.
    have hB : (S.card : ℝ) ≤ C := by
      have := conditionalTypicalSlice_card_le (ε := ε) μ Xs Ys hXs hYs
        hindepY_full hidentY hindepZ_full hidentZ hposY hposZ n y
      rw [hS_def, hC_def]
      exact this
    -- Combine.
    calc B_X.real {f_X | ∃ x' ∈ S, x' ≠ truth ∧ f_X x' = f_X truth}
        ≤ (S.card : ℝ) * ((M_X : ℝ))⁻¹ := hA
      _ ≤ C * ((M_X : ℝ))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hB hMinv_nn
  -- Step 2: Build the product set E ⊆ B_X-space × Ω.
  set E : Set (((Fin n → α) → Fin M_X) × Ω) :=
    {p | p.2 ∈ swError_EX μ Xs Ys n ε p.1} with hE_def
  -- E is measurable: decompose by f_X (finite).
  have hE_meas : MeasurableSet E := by
    -- E = ⋃ f_X, {f_X} ×ˢ swError_EX μ ... f_X.
    have h_decomp : E = ⋃ f_X : (Fin n → α) → Fin M_X,
        ({f_X} : Set ((Fin n → α) → Fin M_X)) ×ˢ swError_EX μ Xs Ys n ε f_X := by
      ext ⟨g, ω⟩
      simp [E]
    rw [h_decomp]
    refine MeasurableSet.iUnion (fun f_X => ?_)
    exact (measurableSet_singleton _).prod (h_meas_EX f_X)
  -- Step 3: Apply Fubini for measures both ways.
  -- (B_X.prod μ) E = ∫⁻ f_X, μ (slice_f_X) ∂B_X = ∫⁻ ω, B_X (slice_ω) ∂μ.
  have h_fubini1 :
      (B_X.prod μ) E = ∫⁻ f_X, μ (swError_EX μ Xs Ys n ε f_X) ∂B_X := by
    rw [Measure.prod_apply hE_meas]
    -- Prod.mk f_X ⁻¹' E = swError_EX μ ... f_X.
    congr 1
  have h_fubini2 :
      (B_X.prod μ) E
        = ∫⁻ ω, B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X} ∂μ := by
    rw [Measure.prod_apply_symm hE_meas]
    congr 1
  -- Combine: ∫⁻ f_X, μ (...) ∂B_X = ∫⁻ ω, B_X (...) ∂μ.
  have h_swap :
      ∫⁻ f_X, μ (swError_EX μ Xs Ys n ε f_X) ∂B_X
        = ∫⁻ ω, B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X} ∂μ := by
    rw [← h_fubini1, h_fubini2]
  -- Step 4: bound the inner B_X-mass uniformly in ω.
  -- Per-ω bound at the ENNReal level: B_X (...) ≤ ENNReal.ofReal (C * (M_X)⁻¹).
  have h_per_omega_ennreal : ∀ ω : Ω,
      B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X}
        ≤ ENNReal.ofReal (C * ((M_X : ℝ))⁻¹) := by
    intro ω
    have hr := h_per_omega ω
    -- B_X.real S = (B_X S).toReal; B_X S < ∞ (probability measure).
    have hne_top : B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X} ≠ ∞ :=
      measure_ne_top _ _
    rw [show B_X.real {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X}
          = (B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X}).toReal from rfl] at hr
    -- ENNReal.ofReal preserves the inequality on toReal ≤ real.
    have h_rhs_nn : 0 ≤ C * ((M_X : ℝ))⁻¹ := mul_nonneg hC_nn hMinv_nn
    calc B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X}
        = ENNReal.ofReal (B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X}).toReal := by
          rw [ENNReal.ofReal_toReal hne_top]
      _ ≤ ENNReal.ofReal (C * ((M_X : ℝ))⁻¹) :=
          ENNReal.ofReal_le_ofReal hr
  -- Integrate the uniform pointwise bound against μ.
  have h_lint_le :
      ∫⁻ ω, B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X} ∂μ
        ≤ ENNReal.ofReal (C * ((M_X : ℝ))⁻¹) := by
    calc ∫⁻ ω, B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X} ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (C * ((M_X : ℝ))⁻¹) ∂μ :=
          lintegral_mono h_per_omega_ennreal
      _ = ENNReal.ofReal (C * ((M_X : ℝ))⁻¹) * μ Set.univ := by
          rw [lintegral_const]
      _ = ENNReal.ofReal (C * ((M_X : ℝ))⁻¹) := by
          rw [measure_univ, mul_one]
  -- Step 5: convert Bochner outer integral to lintegral and conclude.
  -- Outer integrand `f_X ↦ μ.real (swError_EX ... f_X)` is non-negative.
  have h_int_nn : 0 ≤ᵐ[B_X] fun f_X => μ.real (swError_EX μ Xs Ys n ε f_X) := by
    refine Filter.Eventually.of_forall (fun f_X => ?_)
    exact measureReal_nonneg
  -- Strong measurability via Fintype + every-set-is-measurable.
  have h_int_meas :
      AEStronglyMeasurable
        (fun f_X : (Fin n → α) → Fin M_X => μ.real (swError_EX μ Xs Ys n ε f_X)) B_X := by
    -- Domain is finite + every set measurable → every function is measurable.
    apply Measurable.aestronglyMeasurable
    refine Measurable.of_discrete
  rw [integral_eq_lintegral_of_nonneg_ae h_int_nn h_int_meas]
  -- Now goal: (∫⁻ f_X, ENNReal.ofReal (μ.real ...) ∂B_X).toReal ≤ C * (M_X)⁻¹.
  -- ENNReal.ofReal (μ.real S) = μ S (since μ S ≤ 1 < ∞).
  have h_ofReal_eq : ∀ f_X : (Fin n → α) → Fin M_X,
      ENNReal.ofReal (μ.real (swError_EX μ Xs Ys n ε f_X))
        = μ (swError_EX μ Xs Ys n ε f_X) := by
    intro f_X
    have hne_top : μ (swError_EX μ Xs Ys n ε f_X) ≠ ∞ := measure_ne_top _ _
    rw [show μ.real (swError_EX μ Xs Ys n ε f_X)
          = (μ (swError_EX μ Xs Ys n ε f_X)).toReal from rfl,
        ENNReal.ofReal_toReal hne_top]
  -- Substitute into the lintegral.
  have h_lint_eq :
      ∫⁻ f_X, ENNReal.ofReal (μ.real (swError_EX μ Xs Ys n ε f_X)) ∂B_X
        = ∫⁻ f_X, μ (swError_EX μ Xs Ys n ε f_X) ∂B_X := by
    refine lintegral_congr (fun f_X => ?_)
    exact h_ofReal_eq f_X
  rw [h_lint_eq, h_swap]
  -- Goal: (∫⁻ ω, B_X (...) ∂μ).toReal ≤ C * (M_X)⁻¹.
  have h_rhs_nn : 0 ≤ C * ((M_X : ℝ))⁻¹ := mul_nonneg hC_nn hMinv_nn
  calc (∫⁻ ω, B_X {f_X | ω ∈ swError_EX μ Xs Ys n ε f_X} ∂μ).toReal
      ≤ (ENNReal.ofReal (C * ((M_X : ℝ))⁻¹)).toReal := by
        apply ENNReal.toReal_mono _ h_lint_le
        exact ENNReal.ofReal_ne_top
    _ = C * ((M_X : ℝ))⁻¹ := ENNReal.toReal_ofReal h_rhs_nn

/-! ## Phase E.3 — `swError_EY` expectation bound under random binning.

Mirror of Phase E.2 with the `X` and `Y` axes swapped. The expected
`μ`-mass of the `E_Y` error event over the random binning hash
`f_Y ∼ binningMeasure β n M_Y` is bounded by
`exp(n · (H(X,Y) - H(X) + 2ε)) / M_Y` — the conditional-typical
fiber size on the `Y` axis divided by the bin count.

The proof is the exact symmetric counterpart to E.2: we work with the
Y-fiber slice (`{y' | (x, y') ∈ jointlyTypicalSet}`) instead of the
X-fiber. Phase C only published the X-fiber form; the Y-fiber variant
is built locally as a `private` utility below. -/

/-! ### Y-fiber slice utility (mirror of Phase C). -/

/-- The Y-fiber of the jointly typical set at a fixed X-block `x`. Mirror of
`conditionalTypicalSlice` (Phase C) with the two axes swapped. -/
private noncomputable def conditionalTypicalSliceY
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) : Set (Fin n → β) :=
  { y | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε }

private lemma mem_conditionalTypicalSliceY_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) (y : Fin n → β) :
    y ∈ conditionalTypicalSliceY μ Xs Ys n ε x ↔
      (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε := Iff.rfl

private lemma conditionalTypicalSliceY_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    (conditionalTypicalSliceY μ Xs Ys n ε x).Finite :=
  Set.toFinite _

private lemma conditionalTypicalSliceY_empty_of_x_not_typical
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) {x : Fin n → α}
    (hx : x ∉ InformationTheory.Shannon.typicalSet μ Xs n ε) :
    conditionalTypicalSliceY μ Xs Ys n ε x = ∅ := by
  ext y
  constructor
  · intro hy
    exact absurd hy.1 hx
  · intro hy
    exact hy.elim

/-- **Y-fiber slice size bound** (mirror of `conditionalTypicalSlice_card_le`).
For any X-block `x`, the cardinality of the Y-fiber of the jointly typical
set at `x` is at most `exp(n · (H(X, Y) - H(X) + 2ε))`. -/
private theorem conditionalTypicalSliceY_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ}
    (x : Fin n → α) :
    ((conditionalTypicalSliceY μ Xs Ys n ε x).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) *
          (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε)) := by
  classical
  set Zs : ℕ → Ω → α × β := jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  set HZ : ℝ := entropy μ (Zs 0) with hHZ_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set F : Finset (Fin n → β) :=
    (conditionalTypicalSliceY μ Xs Ys n ε x).toFinite.toFinset with hF_def
  by_cases hxT : x ∈ InformationTheory.Shannon.typicalSet μ Xs n ε
  · -- X-typical: full argument.
    -- Embedding `embed : (Fin n → β) → (Fin n → α × β)`, `embed y i := (x i, y i)`.
    let embed : (Fin n → β) → (Fin n → α × β) := fun y i => (x i, y i)
    have hembed_inj : Function.Injective embed := by
      intro y y' hyy
      funext i
      have := congr_fun hyy i
      exact (Prod.mk.injEq _ _ _ _).mp this |>.2
    have hF_embed_typ : ∀ y ∈ F, embed y ∈ InformationTheory.Shannon.typicalSet μ Zs n ε := by
      intro y hy
      have hy_set : y ∈ conditionalTypicalSliceY μ Xs Ys n ε x :=
        (Set.Finite.mem_toFinset _).mp hy
      exact hy_set.2.2
    have hε_pos : 0 < ε := by
      rcases F.eq_empty_or_nonempty with hempty | ⟨y0, hy0⟩
      · rw [mem_typicalSet_iff] at hxT
        exact (abs_nonneg _).trans_lt hxT
      · have h := hF_embed_typ y0 hy0
        rw [mem_typicalSet_iff] at h
        exact (abs_nonneg _).trans_lt h
    have hpoint_ge : ∀ y ∈ F,
        Real.exp (-(n : ℝ) * (HZ + ε)) ≤
            (μ.map (jointRV Zs n)).real {embed y} := by
      intro y hy
      have hyT : embed y ∈ InformationTheory.Shannon.typicalSet μ Zs n ε :=
        hF_embed_typ y hy
      exact typicalSet_prob_ge μ Zs hZs hindepZ_full hidentZ hposZ n (embed y) hyT
    have hsum_ge :
        (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε)) ≤
            ∑ y ∈ F, (μ.map (jointRV Zs n)).real {embed y} := by
      calc (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
          = ∑ _y ∈ F, Real.exp (-(n : ℝ) * (HZ + ε)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ F, (μ.map (jointRV Zs n)).real {embed y} :=
            Finset.sum_le_sum hpoint_ge
    have hMprobZ : IsProbabilityMeasure (μ.map (jointRV Zs n)) :=
      Measure.isProbabilityMeasure_map (measurable_jointRV Zs hZs n).aemeasurable
    have hMprobX : IsProbabilityMeasure (μ.map (jointRV Xs n)) :=
      Measure.isProbabilityMeasure_map (measurable_jointRV Xs hXs n).aemeasurable
    set FimgZ : Finset (Fin n → α × β) := F.image embed with hFimgZ_def
    have hFimg_card : FimgZ.card = F.card :=
      Finset.card_image_of_injective _ hembed_inj
    have hsum_eq :
        (∑ y ∈ F, (μ.map (jointRV Zs n)).real {embed y})
          = ∑ z ∈ FimgZ, (μ.map (jointRV Zs n)).real {z} := by
      symm
      rw [hFimgZ_def]
      apply Finset.sum_image
      intro a _ b _ hab
      exact hembed_inj hab
    have hFimg_measure_eq :
        (∑ z ∈ FimgZ, (μ.map (jointRV Zs n)).real {z})
          = (μ.map (jointRV Zs n)).real (FimgZ : Set (Fin n → α × β)) :=
      sum_measureReal_singleton (μ := μ.map (jointRV Zs n)) FimgZ
    -- Step 4: `FimgZ ⊆ proj_X ⁻¹' {x}`, so its measure ≤ (μ.map (jointRV Xs n)).real {x}.
    let proj_X : (Fin n → α × β) → (Fin n → α) := fun z i => (z i).1
    have hproj_subset :
        (FimgZ : Set (Fin n → α × β)) ⊆ proj_X ⁻¹' ({x} : Set (Fin n → α)) := by
      intro z hz
      rw [Finset.coe_image, Set.mem_image] at hz
      obtain ⟨y, _, hyz⟩ := hz
      show proj_X z = x
      rw [← hyz]
    have hbound_image :
        (μ.map (jointRV Zs n)).real (FimgZ : Set (Fin n → α × β))
          ≤ (μ.map (jointRV Zs n)).real (proj_X ⁻¹' ({x} : Set (Fin n → α))) :=
      measureReal_mono (μ := μ.map (jointRV Zs n)) hproj_subset
    have hbridge :
        (μ.map (jointRV Zs n)).real (proj_X ⁻¹' ({x} : Set (Fin n → α)))
          = (μ.map (jointRV Xs n)).real ({x} : Set (Fin n → α)) := by
      have hproj_meas : Measurable proj_X := by
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i).fst
      have h_meas_x : MeasurableSet ({x} : Set (Fin n → α)) :=
        measurableSet_singleton x
      have h_meas_pre : MeasurableSet (proj_X ⁻¹' ({x} : Set (Fin n → α))) :=
        hproj_meas h_meas_x
      have hZmeas : Measurable (jointRV Zs n) := measurable_jointRV Zs hZs n
      have hXmeas : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
      have hpre_eq :
          jointRV Zs n ⁻¹' (proj_X ⁻¹' ({x} : Set (Fin n → α)))
            = jointRV Xs n ⁻¹' ({x} : Set (Fin n → α)) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hω
          funext i
          have := congr_fun hω i
          exact this
        · intro hω
          funext i
          have := congr_fun hω i
          exact this
      unfold MeasureTheory.Measure.real
      rw [Measure.map_apply hZmeas h_meas_pre]
      rw [Measure.map_apply hXmeas h_meas_x]
      rw [hpre_eq]
    have hXbd : (μ.map (jointRV Xs n)).real ({x} : Set (Fin n → α))
        ≤ Real.exp (-(n : ℝ) * (HX - ε)) :=
      typicalSet_prob_le μ Xs hXs hindepX_full hidentX hposX n x hxT
    have hchain :
        (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
          ≤ Real.exp (-(n : ℝ) * (HX - ε)) := by
      calc (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
          ≤ ∑ y ∈ F, (μ.map (jointRV Zs n)).real {embed y} := hsum_ge
        _ = ∑ z ∈ FimgZ, (μ.map (jointRV Zs n)).real {z} := hsum_eq
        _ = (μ.map (jointRV Zs n)).real (FimgZ : Set (Fin n → α × β)) := hFimg_measure_eq
        _ ≤ (μ.map (jointRV Zs n)).real (proj_X ⁻¹' ({x} : Set (Fin n → α))) :=
            hbound_image
        _ = (μ.map (jointRV Xs n)).real ({x} : Set (Fin n → α)) := hbridge
        _ ≤ Real.exp (-(n : ℝ) * (HX - ε)) := hXbd
    have hexp_pos : 0 < Real.exp ((n : ℝ) * (HZ + ε)) := Real.exp_pos _
    have hexp_cancel :
        Real.exp (-(n : ℝ) * (HZ + ε)) * Real.exp ((n : ℝ) * (HZ + ε)) = 1 := by
      rw [show -(n : ℝ) * (HZ + ε) = -((n : ℝ) * (HZ + ε)) from by ring,
          ← Real.exp_add]
      simp
    have hmul :=
      mul_le_mul_of_nonneg_right hchain hexp_pos.le
    have hlhs :
        (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
            * Real.exp ((n : ℝ) * (HZ + ε)) = (F.card : ℝ) := by
      rw [mul_assoc, hexp_cancel, mul_one]
    have hrhs :
        Real.exp (-(n : ℝ) * (HX - ε)) * Real.exp ((n : ℝ) * (HZ + ε))
          = Real.exp ((n : ℝ) * (HZ - HX + 2 * ε)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hlhs] at hmul
    rw [hrhs] at hmul
    exact hmul
  · -- X not typical: F = ∅, cardinality 0, RHS ≥ 0.
    have hempty :
        conditionalTypicalSliceY μ Xs Ys n ε x = ∅ :=
      conditionalTypicalSliceY_empty_of_x_not_typical μ Xs Ys n ε hxT
    have hF_empty : F = ∅ := by
      rw [hF_def]
      rw [hempty]
      simp
    rw [hF_empty]
    simp
    exact (Real.exp_pos _).le

/-! ### Main statement — `E_Y` expectation bound. -/

set_option linter.unusedVariables false in
@[entry_point]
theorem swError_EY_expectation_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    {n M_Y : ℕ} [NeZero M_Y] {ε : ℝ} (hε : 0 < ε) :
    ∫ f_Y, μ.real (swError_EY μ Xs Ys n ε f_Y) ∂(binningMeasure β n M_Y)
      ≤ Real.exp ((n : ℝ) *
            (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε))
        * ((M_Y : ℝ))⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → β) → Fin M_Y) :=
    Pi.instMeasurableSingletonClass
  haveI : Fintype ((Fin n → β) → Fin M_Y) := Pi.instFintype
  -- Notation.
  set B_Y : Measure ((Fin n → β) → Fin M_Y) := binningMeasure β n M_Y with hB_Y_def
  set C : ℝ := Real.exp ((n : ℝ) *
      (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) + 2 * ε)) with hC_def
  have hC_pos : 0 < C := Real.exp_pos _
  have hC_nn : 0 ≤ C := hC_pos.le
  have hMinv_nn : (0 : ℝ) ≤ ((M_Y : ℝ))⁻¹ :=
    inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)
  have hXn : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
  have hYn : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  have h_meas_EY : ∀ f_Y : (Fin n → β) → Fin M_Y,
      MeasurableSet (swError_EY μ Xs Ys n ε f_Y) := fun f_Y =>
    measurableSet_swError_EY hXs hYs μ n ε f_Y
  -- Per-`ω` slice bound.
  have h_per_omega : ∀ ω : Ω,
      B_Y.real {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}
        ≤ C * ((M_Y : ℝ))⁻¹ := by
    intro ω
    set x : Fin n → α := jointRV Xs n ω with hx_def
    set truth : Fin n → β := jointRV Ys n ω with htruth_def
    set slice : Set (Fin n → β) := conditionalTypicalSliceY μ Xs Ys n ε x with hslice_def
    set S : Finset (Fin n → β) :=
      (conditionalTypicalSliceY_finite μ Xs Ys n ε x).toFinset with hS_def
    have h_set_eq : {f_Y : (Fin n → β) → Fin M_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}
        = {f_Y | ∃ y' ∈ S, y' ≠ truth ∧ f_Y y' = f_Y truth} := by
      ext f_Y
      simp only [Set.mem_setOf_eq, swError_EY, htruth_def, hx_def, hS_def,
        Set.Finite.mem_toFinset, mem_conditionalTypicalSliceY_iff]
      constructor
      · rintro ⟨y', hne, hcoll, hjts⟩
        exact ⟨y', hjts, hne, hcoll⟩
      · rintro ⟨y', hjts, hne, hcoll⟩
        exact ⟨y', hne, hcoll, hjts⟩
    rw [h_set_eq]
    have hA : B_Y.real {f_Y | ∃ y' ∈ S, y' ≠ truth ∧ f_Y y' = f_Y truth}
        ≤ (S.card : ℝ) * ((M_Y : ℝ))⁻¹ :=
      binning_alias_expectation_le_aux (M_X := M_Y) truth S
    have hB : (S.card : ℝ) ≤ C := by
      have := conditionalTypicalSliceY_card_le (ε := ε) μ Xs Ys hXs hYs
        hindepX_full hidentX hindepZ_full hidentZ hposX hposZ n x
      rw [hS_def, hC_def]
      exact this
    calc B_Y.real {f_Y | ∃ y' ∈ S, y' ≠ truth ∧ f_Y y' = f_Y truth}
        ≤ (S.card : ℝ) * ((M_Y : ℝ))⁻¹ := hA
      _ ≤ C * ((M_Y : ℝ))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hB hMinv_nn
  -- Step 2: Build the product set E.
  set E : Set (((Fin n → β) → Fin M_Y) × Ω) :=
    {p | p.2 ∈ swError_EY μ Xs Ys n ε p.1} with hE_def
  have hE_meas : MeasurableSet E := by
    have h_decomp : E = ⋃ f_Y : (Fin n → β) → Fin M_Y,
        ({f_Y} : Set ((Fin n → β) → Fin M_Y)) ×ˢ swError_EY μ Xs Ys n ε f_Y := by
      ext ⟨g, ω⟩
      simp [E]
    rw [h_decomp]
    refine MeasurableSet.iUnion (fun f_Y => ?_)
    exact (measurableSet_singleton _).prod (h_meas_EY f_Y)
  -- Step 3: Fubini.
  have h_fubini1 :
      (B_Y.prod μ) E = ∫⁻ f_Y, μ (swError_EY μ Xs Ys n ε f_Y) ∂B_Y := by
    rw [Measure.prod_apply hE_meas]
    congr 1
  have h_fubini2 :
      (B_Y.prod μ) E
        = ∫⁻ ω, B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y} ∂μ := by
    rw [Measure.prod_apply_symm hE_meas]
    congr 1
  have h_swap :
      ∫⁻ f_Y, μ (swError_EY μ Xs Ys n ε f_Y) ∂B_Y
        = ∫⁻ ω, B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y} ∂μ := by
    rw [← h_fubini1, h_fubini2]
  -- Step 4: ENNReal lift of per-ω bound.
  have h_per_omega_ennreal : ∀ ω : Ω,
      B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}
        ≤ ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹) := by
    intro ω
    have hr := h_per_omega ω
    have hne_top : B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y} ≠ ∞ :=
      measure_ne_top _ _
    rw [show B_Y.real {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}
          = (B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}).toReal from rfl] at hr
    have h_rhs_nn : 0 ≤ C * ((M_Y : ℝ))⁻¹ := mul_nonneg hC_nn hMinv_nn
    calc B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}
        = ENNReal.ofReal (B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y}).toReal := by
          rw [ENNReal.ofReal_toReal hne_top]
      _ ≤ ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹) :=
          ENNReal.ofReal_le_ofReal hr
  have h_lint_le :
      ∫⁻ ω, B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y} ∂μ
        ≤ ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹) := by
    calc ∫⁻ ω, B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y} ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹) ∂μ :=
          lintegral_mono h_per_omega_ennreal
      _ = ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹) * μ Set.univ := by
          rw [lintegral_const]
      _ = ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹) := by
          rw [measure_univ, mul_one]
  -- Step 5: Bochner integral lift.
  have h_int_nn : 0 ≤ᵐ[B_Y] fun f_Y => μ.real (swError_EY μ Xs Ys n ε f_Y) := by
    refine Filter.Eventually.of_forall (fun f_Y => ?_)
    exact measureReal_nonneg
  have h_int_meas :
      AEStronglyMeasurable
        (fun f_Y : (Fin n → β) → Fin M_Y => μ.real (swError_EY μ Xs Ys n ε f_Y)) B_Y := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.of_discrete
  rw [integral_eq_lintegral_of_nonneg_ae h_int_nn h_int_meas]
  have h_ofReal_eq : ∀ f_Y : (Fin n → β) → Fin M_Y,
      ENNReal.ofReal (μ.real (swError_EY μ Xs Ys n ε f_Y))
        = μ (swError_EY μ Xs Ys n ε f_Y) := by
    intro f_Y
    have hne_top : μ (swError_EY μ Xs Ys n ε f_Y) ≠ ∞ := measure_ne_top _ _
    rw [show μ.real (swError_EY μ Xs Ys n ε f_Y)
          = (μ (swError_EY μ Xs Ys n ε f_Y)).toReal from rfl,
        ENNReal.ofReal_toReal hne_top]
  have h_lint_eq :
      ∫⁻ f_Y, ENNReal.ofReal (μ.real (swError_EY μ Xs Ys n ε f_Y)) ∂B_Y
        = ∫⁻ f_Y, μ (swError_EY μ Xs Ys n ε f_Y) ∂B_Y := by
    refine lintegral_congr (fun f_Y => ?_)
    exact h_ofReal_eq f_Y
  rw [h_lint_eq, h_swap]
  have h_rhs_nn : 0 ≤ C * ((M_Y : ℝ))⁻¹ := mul_nonneg hC_nn hMinv_nn
  calc (∫⁻ ω, B_Y {f_Y | ω ∈ swError_EY μ Xs Ys n ε f_Y} ∂μ).toReal
      ≤ (ENNReal.ofReal (C * ((M_Y : ℝ))⁻¹)).toReal := by
        apply ENNReal.toReal_mono _ h_lint_le
        exact ENNReal.ofReal_ne_top
    _ = C * ((M_Y : ℝ))⁻¹ := ENNReal.toReal_ofReal h_rhs_nn

end InformationTheory.Shannon.ChannelCoding
