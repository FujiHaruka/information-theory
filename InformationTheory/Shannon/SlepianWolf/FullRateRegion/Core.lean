import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SlepianWolf.Achievability
import InformationTheory.Shannon.SlepianWolf.Binning
import InformationTheory.Shannon.SlepianWolf.ConditionalTypicalSlice

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

/-! ## Joint typicality decoder -/

/-- Slepian–Wolf joint typicality decoder. Given a bin pair `(i, j)`, returns the
unique source pair `(x, y)` consistent with the bins whose joint sequence is jointly
typical, falling back to an arbitrary source pair if either no such pair exists or
it is not unique. -/
noncomputable def swJointTypicalDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    Fin M_X × Fin M_Y → (Fin n → α) × (Fin n → β) := fun ij ↦
  haveI : Decidable (∃! p : (Fin n → α) × (Fin n → β),
      f_X p.1 = ij.1 ∧ f_Y p.2 = ij.2 ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! p : (Fin n → α) × (Fin n → β),
      f_X p.1 = ij.1 ∧ f_Y p.2 = ij.2 ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else (Classical.arbitrary _, Classical.arbitrary _)

/-! ## The four error events -/

/-- `E_0`: the true source pair is not jointly typical. -/
def swError_E0
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) : Set Ω :=
  { ω | (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε }

/-- `E_X`: there exists an alias `x' ≠ X^n` colliding with `X^n` under `f_X`
such that `(x', Y^n)` is jointly typical. -/
def swError_EX
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) {M_X : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) : Set Ω :=
  { ω | ∃ x' : Fin n → α,
            x' ≠ jointRV Xs n ω
          ∧ f_X x' = f_X (jointRV Xs n ω)
          ∧ (x', jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε }

/-- `E_Y`: there exists an alias `y' ≠ Y^n` colliding with `Y^n` under `f_Y`
such that `(X^n, y')` is jointly typical. -/
def swError_EY
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) {M_Y : ℕ} (ε : ℝ)
    (f_Y : (Fin n → β) → Fin M_Y) : Set Ω :=
  { ω | ∃ y' : Fin n → β,
            y' ≠ jointRV Ys n ω
          ∧ f_Y y' = f_Y (jointRV Ys n ω)
          ∧ (jointRV Xs n ω, y') ∈ jointlyTypicalSet μ Xs Ys n ε }

/-- `E_{XY}`: there exists an alias pair `p ≠ (X^n, Y^n)` colliding with `(X^n, Y^n)`
under `(f_X, f_Y)` on both axes such that `p` is jointly typical. -/
def swError_EXY
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) {M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) : Set Ω :=
  { ω | ∃ p : (Fin n → α) × (Fin n → β),
            p ≠ (jointRV Xs n ω, jointRV Ys n ω)
          ∧ f_X p.1 = f_X (jointRV Xs n ω)
          ∧ f_Y p.2 = f_Y (jointRV Ys n ω)
          ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε }

/-! ## Decoder equation under a unique witness -/

omit [DecidableEq α] [DecidableEq β] in
/-- If `(X^n, Y^n)` is jointly typical and is the unique source pair (across
all source pairs) compatible with its bin pair under joint typicality, then the
joint typical decoder recovers it exactly. -/
lemma swJointTypicalDecoder_eq_of_unique
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y)
    {ω : Ω}
    (htrue : (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε)
    (hunique : ∀ p : (Fin n → α) × (Fin n → β),
        f_X p.1 = f_X (jointRV Xs n ω) →
        f_Y p.2 = f_Y (jointRV Ys n ω) →
        p ∈ jointlyTypicalSet μ Xs Ys n ε →
        p = (jointRV Xs n ω, jointRV Ys n ω)) :
    swJointTypicalDecoder μ Xs Ys ε f_X f_Y
        (f_X (jointRV Xs n ω), f_Y (jointRV Ys n ω))
      = (jointRV Xs n ω, jointRV Ys n ω) := by
  -- The pair `(X^n ω, Y^n ω)` is the unique witness of the `∃!`.
  have hExUnique : ∃! p : (Fin n → α) × (Fin n → β),
      f_X p.1 = f_X (jointRV Xs n ω)
        ∧ f_Y p.2 = f_Y (jointRV Ys n ω)
        ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε := by
    refine ⟨(jointRV Xs n ω, jointRV Ys n ω), ⟨rfl, rfl, htrue⟩, ?_⟩
    intro p hp
    exact hunique p hp.1 hp.2.1 hp.2.2
  -- Unfold the decoder and use `dif_pos`.
  unfold swJointTypicalDecoder
  rw [dif_pos hExUnique]
  -- The chosen witness must equal the unique one.
  have hch_spec :
      f_X (Classical.choose hExUnique.exists).1 = f_X (jointRV Xs n ω)
        ∧ f_Y (Classical.choose hExUnique.exists).2 = f_Y (jointRV Ys n ω)
        ∧ Classical.choose hExUnique.exists ∈ jointlyTypicalSet μ Xs Ys n ε :=
    Classical.choose_spec hExUnique.exists
  exact hunique (Classical.choose hExUnique.exists) hch_spec.1 hch_spec.2.1 hch_spec.2.2

/-! ## Main error decomposition -/

omit [DecidableEq α] [DecidableEq β] in
set_option linter.unusedVariables false in
/-- Main 4-way error decomposition. The Slepian–Wolf error probability under the
joint typicality decoder is bounded above by the sum of probabilities of the four
error events `E_0`, `E_X`, `E_Y`, `E_{XY}`.

`hXs` / `hYs` are kept in the signature as part of the public API (downstream
random-binning average bounds need them) even though this pointwise subset
argument does not consume them. -/
@[entry_point]
theorem swErrorProb_le_E0_plus_EX_plus_EY_plus_EXY
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    swErrorProb μ (jointRV Xs n) (jointRV Ys n) f_X f_Y
        (swJointTypicalDecoder μ Xs Ys ε f_X f_Y)
      ≤ μ.real (swError_E0 μ Xs Ys n ε)
        + μ.real (swError_EX μ Xs Ys n ε f_X)
        + μ.real (swError_EY μ Xs Ys n ε f_Y)
        + μ.real (swError_EXY μ Xs Ys n ε f_X f_Y) := by
  classical
  -- Abbreviate.
  set E0 : Set Ω := swError_E0 μ Xs Ys n ε with hE0_def
  set EX : Set Ω := swError_EX μ Xs Ys n ε f_X with hEX_def
  set EY : Set Ω := swError_EY μ Xs Ys n ε f_Y with hEY_def
  set EXY : Set Ω := swError_EXY μ Xs Ys n ε f_X f_Y with hEXY_def
  -- The SW error event.
  set Eerr : Set Ω :=
    {ω | swJointTypicalDecoder μ Xs Ys ε f_X f_Y
            (f_X (jointRV Xs n ω), f_Y (jointRV Ys n ω))
              ≠ (jointRV Xs n ω, jointRV Ys n ω)} with hEerr_def
  -- Step 1: `Eerr ⊆ E0 ∪ EX ∪ EY ∪ EXY`.
  have h_sub : Eerr ⊆ ((E0 ∪ EX) ∪ EY) ∪ EXY := by
    intro ω hω
    rw [hEerr_def, Set.mem_setOf_eq] at hω
    -- Case on whether the true pair is JTS.
    by_cases hjts : (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε
    · -- True pair JTS. The decoder errs, so the unique-witness hypothesis fails:
      -- some `p ≠ (X^n, Y^n)` with bins matching and `p ∈ JTS`.
      have hnot_unique : ¬ ∀ p : (Fin n → α) × (Fin n → β),
          f_X p.1 = f_X (jointRV Xs n ω) →
          f_Y p.2 = f_Y (jointRV Ys n ω) →
          p ∈ jointlyTypicalSet μ Xs Ys n ε →
          p = (jointRV Xs n ω, jointRV Ys n ω) := by
        intro hunique
        exact hω (swJointTypicalDecoder_eq_of_unique
          μ Xs Ys ε f_X f_Y hjts hunique)
      -- Push the negation in.
      simp only [not_forall] at hnot_unique
      obtain ⟨p, hfx, hfy, hpJTS, hpne⟩ := hnot_unique
      -- Sub-case on which coordinate of `p` differs.
      by_cases hp1 : p.1 = jointRV Xs n ω
      · by_cases hp2 : p.2 = jointRV Ys n ω
        · -- Both coords agree ⇒ contradiction with hpne.
          exfalso
          apply hpne
          exact Prod.ext hp1 hp2
        · -- p.1 = X^n, p.2 ≠ Y^n ⇒ ω ∈ EY (position: left; right).
          left; right
          show ω ∈ EY
          rw [hEY_def]
          refine ⟨p.2, hp2, hfy, ?_⟩
          -- (jointRV Xs n ω, p.2) ∈ JTS via hp1 : p.1 = X^n.
          have hp_in : (p.1, p.2) ∈ jointlyTypicalSet μ Xs Ys n ε := hpJTS
          rw [hp1] at hp_in
          exact hp_in
      · by_cases hp2 : p.2 = jointRV Ys n ω
        · -- p.1 ≠ X^n, p.2 = Y^n ⇒ ω ∈ EX (position: left; left; right).
          left; left; right
          show ω ∈ EX
          rw [hEX_def]
          refine ⟨p.1, hp1, hfx, ?_⟩
          have hp_in : (p.1, p.2) ∈ jointlyTypicalSet μ Xs Ys n ε := hpJTS
          rw [hp2] at hp_in
          exact hp_in
        · -- p.1 ≠ X^n, p.2 ≠ Y^n ⇒ ω ∈ EXY (position: right).
          right
          show ω ∈ EXY
          rw [hEXY_def]
          refine ⟨p, ?_, hfx, hfy, hpJTS⟩
          intro hpe
          exact hp1 (by rw [hpe])
    · -- (X^n, Y^n) ∉ JTS ⇒ ω ∈ E0 (position: left; left; left).
      left; left; left
      show ω ∈ E0
      rw [hE0_def]
      exact hjts
  -- Step 2: lift the subset to `μ.real` via measureReal_mono + union_le.
  unfold swErrorProb
  -- The error event is the swErrorProb integrand set.
  -- It coincides with `Eerr` by defeq.
  show μ.real Eerr ≤ μ.real E0 + μ.real EX + μ.real EY + μ.real EXY
  calc μ.real Eerr
      ≤ μ.real (((E0 ∪ EX) ∪ EY) ∪ EXY) :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ μ.real ((E0 ∪ EX) ∪ EY) + μ.real EXY :=
        measureReal_union_le _ _
    _ ≤ μ.real (E0 ∪ EX) + μ.real EY + μ.real EXY := by
        have := measureReal_union_le (μ := μ) (E0 ∪ EX) EY
        linarith
    _ ≤ μ.real E0 + μ.real EX + μ.real EY + μ.real EXY := by
        have := measureReal_union_le (μ := μ) E0 EX
        linarith

/-! ## Measurability of the four events -/

omit [DecidableEq α] [DecidableEq β] in
lemma measurableSet_swError_EX
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) {M_X : ℕ} (ε : ℝ) (f_X : (Fin n → α) → Fin M_X) :
    MeasurableSet (swError_EX μ Xs Ys n ε f_X) := by
  classical
  -- Write as preimage of a finite set under the measurable map
  -- `ω ↦ (jointRV Xs n ω, jointRV Ys n ω)`.
  have hmeas : Measurable
      (fun ω ↦ (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  -- The target set lives in `(Fin n → α) × (Fin n → β)` (finite ambient).
  let S : Set ((Fin n → α) × (Fin n → β)) :=
    { p | ∃ x' : Fin n → α,
            x' ≠ p.1
          ∧ f_X x' = f_X p.1
          ∧ (x', p.2) ∈ jointlyTypicalSet μ Xs Ys n ε }
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_eq : swError_EX μ Xs Ys n ε f_X
      = (fun ω ↦ (jointRV Xs n ω, jointRV Ys n ω)) ⁻¹' S := by
    ext ω
    rfl
  rw [h_eq]
  exact hmeas hS_meas

omit [DecidableEq α] [DecidableEq β] in
lemma measurableSet_swError_EY
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) {M_Y : ℕ} (ε : ℝ) (f_Y : (Fin n → β) → Fin M_Y) :
    MeasurableSet (swError_EY μ Xs Ys n ε f_Y) := by
  classical
  have hmeas : Measurable
      (fun ω ↦ (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  let S : Set ((Fin n → α) × (Fin n → β)) :=
    { p | ∃ y' : Fin n → β,
            y' ≠ p.2
          ∧ f_Y y' = f_Y p.2
          ∧ (p.1, y') ∈ jointlyTypicalSet μ Xs Ys n ε }
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_eq : swError_EY μ Xs Ys n ε f_Y
      = (fun ω ↦ (jointRV Xs n ω, jointRV Ys n ω)) ⁻¹' S := by
    ext ω
    rfl
  rw [h_eq]
  exact hmeas hS_meas

/-! ## The `E_0` probability tends to zero

The "true source pair is not jointly typical" event has probability tending to `0`
by the joint AEP (`jointlyTypicalSet_prob_tendsto_one`); it is the only one of the
four error-event bounds that does not depend on the random binning measure. -/

omit [DecidableEq α] [DecidableEq β] in
@[entry_point]
theorem swError_E0_prob_tendsto_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j ↦ Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j ↦
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦ μ.real (swError_E0 μ Xs Ys n ε))
      Filter.atTop (𝓝 0) := by
  classical
  -- The "good" event: `(X^n ω, Y^n ω) ∈ jointlyTypicalSet`. Tends-to-1 by AEP.
  have h_good : Filter.Tendsto
      (fun n : ℕ ↦ μ
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε})
      Filter.atTop (𝓝 1) :=
    jointlyTypicalSet_prob_tendsto_one μ Xs Ys hXs hYs
      hindepX hidentX hindepY hidentY hindepZ hidentZ hε
  -- Measurability of the good event.
  have h_meas_good : ∀ n,
      MeasurableSet
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
    intro n
    have h_meas_pair : Measurable
        (fun ω ↦ (jointRV Xs n ω, jointRV Ys n ω)) :=
      (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
    exact h_meas_pair (measurableSet_jointlyTypicalSet _ _ _ _ _)
  -- swError_E0 is the complement of the good event.
  have h_compl_id : ∀ n,
      μ.real (swError_E0 μ Xs Ys n ε)
        = 1 - μ.real
            {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
    intro n
    have h_eq :
        (swError_E0 μ Xs Ys n ε)
          = {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε}ᶜ :=
      rfl
    rw [h_eq, probReal_compl_eq_one_sub (h_meas_good n)]
  -- Lift `μ` tendsto to `μ.real` tendsto.
  have h_good_real : Filter.Tendsto
      (fun n : ℕ ↦ μ.real
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε})
      Filter.atTop (𝓝 1) := by
    have h_step := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp h_good
    simpa [Measure.real] using h_step
  -- 1 - μ.real (good) → 1 - 1 = 0.
  refine Filter.Tendsto.congr (fun n ↦ (h_compl_id n).symm) ?_
  have h_const : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  have := h_const.sub h_good_real
  simpa using this

end InformationTheory.Shannon.ChannelCoding
