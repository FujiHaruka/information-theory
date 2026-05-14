import Common2026.Shannon.SlepianWolfBinning
import Common2026.Shannon.SlepianWolfConditionalTypicalSlice
import Common2026.Shannon.SlepianWolfAchievability

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

lemma measurableSet_swError_E0
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) (ε : ℝ) :
    MeasurableSet (swError_E0 μ Xs Ys n ε) := by
  -- The event is the preimage of `(JTS)ᶜ` under the measurable map
  -- `ω ↦ (jointRV Xs n ω, jointRV Ys n ω)`.
  have hmeas : Measurable
      (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  have hJTSc : MeasurableSet (jointlyTypicalSet μ Xs Ys n ε)ᶜ :=
    (measurableSet_jointlyTypicalSet μ Xs Ys n ε).compl
  exact hmeas hJTSc

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

lemma measurableSet_swError_EXY
    {Xs : ℕ → Ω → α} {Ys : ℕ → Ω → β}
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (μ : Measure Ω) (n : ℕ) {M_X M_Y : ℕ} (ε : ℝ)
    (f_X : (Fin n → α) → Fin M_X) (f_Y : (Fin n → β) → Fin M_Y) :
    MeasurableSet (swError_EXY μ Xs Ys n ε f_X f_Y) := by
  classical
  have hmeas : Measurable
      (fun ω => (jointRV Xs n ω, jointRV Ys n ω)) :=
    (measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n)
  let S : Set ((Fin n → α) × (Fin n → β)) :=
    { p | ∃ q : (Fin n → α) × (Fin n → β),
            q ≠ p
          ∧ f_X q.1 = f_X p.1
          ∧ f_Y q.2 = f_Y p.2
          ∧ q ∈ jointlyTypicalSet μ Xs Ys n ε }
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_eq : swError_EXY μ Xs Ys n ε f_X f_Y
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

end InformationTheory.Shannon.ChannelCoding
