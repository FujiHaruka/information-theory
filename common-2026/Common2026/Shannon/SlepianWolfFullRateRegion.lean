import Common2026.Meta.EntryPoint
import Common2026.Shannon.SlepianWolfAchievability
import Common2026.Shannon.SlepianWolfBinning
import Common2026.Shannon.SlepianWolfConditionalTypicalSlice

/-!
# Slepian–Wolf full rate region — Phase D (error event decomposition)

E-5'' Phase D ([`docs/shannon/slepian-wolf-full-rate-region-plan.md`](../../docs/shannon/slepian-wolf-full-rate-region-plan.md)).
Publishes the joint typicality decoder and the 4-way error event decomposition
`E ⊆ E_0 ∪ E_X ∪ E_Y ∪ E_{XY}`.

Encoder-side mirror of `ChannelCodingAchievability.errorProbAt_le_E1_plus_E2`.
-/

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

/-! ## Phase D-1 — Joint typicality decoder -/

/-- Slepian–Wolf joint typicality decoder. Given a bin pair `(i, j)`, returns the
unique source pair `(x, y)` consistent with the bins whose joint sequence is jointly
typical, falling back to an arbitrary source pair if either no such pair exists or
it is not unique. -/
noncomputable def swJointTypicalDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {n M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    Fin M_X × Fin M_Y → (Fin n → α) × (Fin n → β) := fun ij =>
  haveI : Decidable (∃! p : (Fin n → α) × (Fin n → β),
      f_X p.1 = ij.1 ∧ f_Y p.2 = ij.2 ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! p : (Fin n → α) × (Fin n → β),
      f_X p.1 = ij.1 ∧ f_Y p.2 = ij.2 ∧ p ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else (Classical.arbitrary _, Classical.arbitrary _)

/-! ## Phase D-2 — Four error events -/

/-- `E_0`: the **true** source pair is not jointly typical. -/
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

/-! ## Phase D-3 — Decoder equation under unique witness -/

/-- If `(X^n, Y^n)` is jointly typical **and** is the **unique** source pair (across
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

/-! ## Phase D-4 — Main decomposition -/

set_option linter.unusedVariables false in
/-- **Main 4-way error decomposition.** The Slepian–Wolf error probability under the
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

/-! ## Phase D-5 — Measurability of the four events -/

lemma measurableSet_swError_EX
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) {M_X : ℕ} (ε : ℝ) (f_X : (Fin n → α) → Fin M_X) :
    MeasurableSet (swError_EX μ Xs Ys n ε f_X) := by
  classical
  -- Write as preimage of a finite set under the measurable map
  -- `ω ↦ (jointRV Xs n ω, jointRV Ys n ω)`.
  have hmeas : Measurable
      (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  -- The target set lives in `(Fin n → α) × (Fin n → β)` (finite ambient).
  let S : Set ((Fin n → α) × (Fin n → β)) :=
    { p | ∃ x' : Fin n → α,
            x' ≠ p.1
          ∧ f_X x' = f_X p.1
          ∧ (x', p.2) ∈ jointlyTypicalSet μ Xs Ys n ε }
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_eq : swError_EX μ Xs Ys n ε f_X
      = (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) ⁻¹' S := by
    ext ω
    rfl
  rw [h_eq]
  exact hmeas hS_meas

lemma measurableSet_swError_EY
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) {M_Y : ℕ} (ε : ℝ) (f_Y : (Fin n → β) → Fin M_Y) :
    MeasurableSet (swError_EY μ Xs Ys n ε f_Y) := by
  classical
  have hmeas : Measurable
      (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  let S : Set ((Fin n → α) × (Fin n → β)) :=
    { p | ∃ y' : Fin n → β,
            y' ≠ p.2
          ∧ f_Y y' = f_Y p.2
          ∧ (p.1, y') ∈ jointlyTypicalSet μ Xs Ys n ε }
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_eq : swError_EY μ Xs Ys n ε f_Y
      = (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) ⁻¹' S := by
    ext ω
    rfl
  rw [h_eq]
  exact hmeas hS_meas

/-! ## Phase E.1 — `swError_E0` probability tends to zero (AEP).

The "true source pair is not jointly typical" event has probability tending to `0`
by the joint AEP (`jointlyTypicalSet_prob_tendsto_one`). This is the simplest of the
four error-event bounds, and the only one that does **not** depend on the random
binning measure: it is a pure statement about the underlying source process. -/

@[entry_point]
theorem swError_E0_prob_tendsto_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => μ.real (swError_E0 μ Xs Ys n ε))
      Filter.atTop (𝓝 0) := by
  classical
  -- The "good" event: `(X^n ω, Y^n ω) ∈ jointlyTypicalSet`. Tends-to-1 by AEP.
  have h_good : Filter.Tendsto
      (fun n : ℕ => μ
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
        (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) :=
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
      (fun n : ℕ => μ.real
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet μ Xs Ys n ε})
      Filter.atTop (𝓝 1) := by
    have h_step := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp h_good
    simpa [Measure.real] using h_step
  -- 1 - μ.real (good) → 1 - 1 = 0.
  refine Filter.Tendsto.congr (fun n => (h_compl_id n).symm) ?_
  have h_const : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
    tendsto_const_nhds
  have := h_const.sub h_good_real
  simpa using this

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

/-! ## Phase E.4 — `swError_EXY` strict-form expectation bound under random binning.

The "both coordinates differ" sub-event `swError_EXY_strict` admits a clean bound
`|JTS| / (M_X · M_Y)` via pair-binning collision (`1/M_X · 1/M_Y`) summed over the
joint typical set. Combined with `jointlyTypicalSet_card_le`, this gives the
target `exp(n · (H(X,Y) + ε)) / (M_X · M_Y)`.

The original `swError_EXY` (without the strict restriction) splits into three
sub-cases by `(p.1 = X^n ?, p.2 = Y^n ?)`; the two "loose" cases (one coordinate
agrees) are absorbed into `swError_EX` / `swError_EY` via
`swError_EXY_subset_union`. Phase F combines this with the Phase D main
decomposition to obtain the full 5-event union bound. -/

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

/-- The full `swError_EXY` event is contained in the union of the two single-axis
events `swError_EX`, `swError_EY` and the strict `swError_EXY_strict`. The loose
cases (only one coordinate of the alias `p` agrees with the truth) are absorbed
into `E_X` or `E_Y` respectively. -/
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

/-- **Random pair-binning alias expectation bound** (Phase E.4 utility).

For a (deterministic) finite set `S` of candidate alias **pairs**, the product
binning-measure probability that there exists `p ∈ S` with **both coordinates**
differing from the truth and **both hashes** colliding is bounded by
`|S| / (M_X · M_Y)`.

This is the union-bound + product collision-probability skeleton specialised
to the both-axis case: each per-pair collision factors as a product (the two
binning measures are independent), each factor is `(M_X)⁻¹` resp. `(M_Y)⁻¹`
by `binning_collision_prob`, and the cardinality bound trivially upper-bounds
the count of admissible aliases. -/
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

/-! ### Phase E.4 main bound — `swError_EXY_strict` expectation bound.

The expected `μ`-mass of the strict `E_{XY}` error event (both coordinates of
the alias differ from the truth) over the **product** random binning hash
`(f_X, f_Y) ∼ (binningMeasure α n M_X) × (binningMeasure β n M_Y)` is bounded by

`exp(n · (H(X, Y) + ε)) / (M_X · M_Y)`

— the joint typical set's cardinality bound divided by the product bin count.

Strategy: 3-product Tonelli swap on `BP := B_X × B_Y` and ambient `μ`,
followed by a per-`ω` slice bound via `binning_pair_alias_expectation_le_aux`
applied to `S := JTS.toFinite.toFinset` (which is `ω`-independent), and
closing with `jointlyTypicalSet_card_le`. -/

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

/-! ## Phase F — Pigeonhole + finalize (Cover-Thomas 15.4.1 完全形)

Phase D の 4 分解と Phase E.1-E.4 の bound を結合し、 binning expectation 上で
total bound を取って pigeonhole で deterministic な encoder pair を取り出し、
rate condition `R_X > H(Y|X)`, `R_Y > H(X|Y)`, `R_X + R_Y > H(X, Y)` の下で
error probability → 0 を導く。

本セクションは 4 declaration で構成される:

* `entropy_joint_sub_marginal_eq_condEntropy` (bridge): `H(X,Y) - H(X) = H(Y|X)`.
* `swErrorProb_total_expectation_le` (F.1): binning 上の 4 項総和 expectation bound.
* `exists_pair_le_of_binning_integral_le` (F.2): 期待値 → deterministic 取り出し.
* `slepian_wolf_full_rate_region_achievability` (F.3 主定理): rate region achievability.
-/

section PhaseF

variable {α' β' Ω' : Type*}
  [MeasurableSpace Ω']
  [Fintype α'] [DecidableEq α'] [Nonempty α']
    [MeasurableSpace α'] [MeasurableSingletonClass α']
  [Fintype β'] [DecidableEq β'] [Nonempty β']
    [MeasurableSpace β'] [MeasurableSingletonClass β']

/-- **Bridge**: `H(X, Y) - H(X) = H(Y | X)`. Direct corollary of chain rule
`entropy_pair_eq_entropy_add_condEntropy`. -/
private lemma entropy_joint_sub_marginal_eq_condEntropy
    (μ : Measure Ω') [IsProbabilityMeasure μ]
    (X : Ω' → α') (Y : Ω' → β') (hX : Measurable X) (hY : Measurable Y) :
    entropy μ (fun ω => (X ω, Y ω)) - entropy μ X
      = InformationTheory.MeasureFano.condEntropy μ Y X := by
  have h := entropy_pair_eq_entropy_add_condEntropy μ X Y hX hY
  linarith

end PhaseF

/-- **F.1**: Phase D 4 分解 + Phase E.4 subset 吸収を結合した
binning expectation total bound. 係数 2 は `EXY ⊆ EX ∪ EY ∪ EXY_strict` の
2 重カウントを吸収. -/
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

/-- **F.2 pigeonhole**: 期待値 ≤ δ から deterministic 取り出し。
First moment method (`MeasureTheory.exists_le_integral`) を 2 回適用。 -/
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


end InformationTheory.Shannon.ChannelCoding
