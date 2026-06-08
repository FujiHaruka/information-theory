import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.IIDProductInput.Basic
import InformationTheory.Shannon.AEP.Rate
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Channel coding achievability — Phase 0 / C-(a) / C-(b) / C-(c) core definitions

Part of the longFile split of `Achievability.lean`. This part holds the i.i.d.
input × channel plumbing (Phase 0), the codebook + joint-typical decoder (Phase
C-(a)), the per-codeword error decomposition (Phase C-(b)), and the random
codebook measure (Phase C-(c) definitions). The Fubini swap helpers and the
random-codebook average bound live in `...Achievability.RandomCodebook`; the
pigeonhole and main theorem live in `...Achievability.Main`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Phase 0 — i.i.d. input × channel plumbing -/

section IIDInput

/-- The i.i.d. extension of `(p, W)` to length-`n` blocks: a measure on
`Fin n → α × β` whose `i`-th coordinate has law `jointDistribution p W`. -/
noncomputable def iidJointMeasure
    (p : Measure α) (W : Channel α β) (n : ℕ) : Measure (Fin n → α × β) :=
  Measure.pi (fun _ : Fin n => jointDistribution p W)

instance iidJointMeasure.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsProbabilityMeasure (iidJointMeasure p W n) := by
  unfold iidJointMeasure
  infer_instance

end IIDInput

/-! ### Phase C-(a) — Codebook + joint-typical decoder -/

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- A random codebook is just a function from message indices to length-`n` words. -/
abbrev Codebook (M n : ℕ) (α : Type*) [MeasurableSpace α] :=
  Fin M → (Fin n → α)

/-- **Joint-typical decoder.** Given a received word `y`, returns the unique
message `m` such that `(codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε`, falling
back to `⟨0, hM⟩` if either no such `m` exists or it is not unique. -/
noncomputable def jointTypicalDecoder
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    (Fin n → β) → Fin M := fun y =>
  haveI : Decidable (∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else ⟨0, hM⟩

/-- Bundle a codebook + joint-typical decoder into a `Code`. -/
noncomputable def codebookToCode
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    Code M n α β where
  encoder := codebook
  decoder := jointTypicalDecoder μ Xs Ys hM ε codebook

/-! ### Phase C-(b) — Per-codeword error decomposition -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] [DecidableEq β]
  [Nonempty β] in
/-- **Per-codeword error bound.** The point-wise error probability of message `m`
under the joint-typical decoder is bounded by the (E1) "true codeword not typical"
event plus the (E2) "some alias codeword is typical" union bound. -/
theorem errorProbAt_le_E1_plus_E2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ}
    (codebook : Codebook M n α) (m : Fin M) :
    ((codebookToCode μ Xs Ys hM ε codebook).errorProbAt W m).toReal
      ≤ (Measure.pi (fun i => W (codebook m i))).real
          {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            (Measure.pi (fun i => W (codebook m i))).real
              {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
  classical
  -- Abbreviations.
  set c : Code M n α β := codebookToCode μ Xs Ys hM ε codebook with hc_def
  set ν : Measure (Fin n → β) := Measure.pi (fun i => W (codebook m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by
    rw [hν_def]; infer_instance
  -- Define the (E1) and (E2) sets.
  set E1 : Set (Fin n → β) :=
    {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε} with hE1_def
  set E2_indiv : Fin M → Set (Fin n → β) := fun m' =>
    {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} with hE2_def
  -- Step 1: `c.errorEvent m ⊆ E1 ∪ (⋃ m' ∈ univ.erase m, E2_indiv m')`.
  have h_sub :
      c.errorEvent m ⊆ E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m' := by
    intro y hy
    rw [Code.mem_errorEvent] at hy
    -- `c.decoder y = jointTypicalDecoder μ Xs Ys hM ε codebook y`.
    have hdec : c.decoder y = jointTypicalDecoder μ Xs Ys hM ε codebook y := rfl
    -- Case analyze on whether there is a unique joint-typical `m'`.
    by_cases hu : ∃! m' : Fin M, (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε
    · -- A unique `m'` exists. Decoder returns `Classical.choose hu.exists`.
      have hch : c.decoder y = Classical.choose hu.exists := by
        rw [hdec]
        unfold jointTypicalDecoder
        rw [dif_pos hu]
      set m' := Classical.choose hu.exists with hm'_def
      have hm'_mem : (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε :=
        Classical.choose_spec hu.exists
      have hm'_ne : m' ≠ m := by
        intro hmm
        apply hy
        rw [hch, ← hmm]
      -- Either the true `m` is not typical (E1), or the chosen `m'` ≠ m is typical (E2).
      by_cases hm_typ : (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
      · -- `m` is also typical. Uniqueness ⇒ `m' = m`, contradicting `hm'_ne`.
        have : m' = m := hu.unique hm'_mem hm_typ
        exact absurd this hm'_ne
      · -- `m` is NOT typical: y ∈ E1.
        left
        exact hm_typ
    · -- No unique typical `m'`. Decoder falls back to `⟨0, hM⟩` ≠ … ?
      -- Either NO typical `m'` exists, or multiple do.
      by_cases hexists : ∃ m' : Fin M, (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε
      · -- Multiple typical `m'` exist (because not unique). At least two distinct ones.
        -- We exhibit some `m' ≠ m` that is typical.
        -- Since not unique: either (a) the true `m` is not typical, or
        -- (b) some other typical `m'' ≠ m` exists.
        by_cases hm_typ : (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
        · -- `m` is typical. Since not unique, some `m'' ≠ m` is also typical.
          -- Suppose for contradiction every typical witness equals `m`. Then
          -- `m` is the unique one — contradicting `¬ hu`.
          have h_alias : ∃ m'' : Fin M, (codebook m'', y) ∈ jointlyTypicalSet μ Xs Ys n ε ∧ m'' ≠ m := by
            by_contra h_none
            apply hu
            refine ⟨m, hm_typ, ?_⟩
            intro m'' hm''_typ
            by_contra hne
            exact h_none ⟨m'', hm''_typ, hne⟩
          obtain ⟨m'', hm''_typ, hm''_ne⟩ := h_alias
          right
          refine Set.mem_iUnion.mpr ⟨m'', ?_⟩
          refine Set.mem_iUnion.mpr ⟨?_, hm''_typ⟩
          exact Finset.mem_erase.mpr ⟨hm''_ne, Finset.mem_univ _⟩
        · -- `m` not typical: y ∈ E1.
          left; exact hm_typ
      · -- No typical `m'` at all ⇒ in particular `m` is not typical: y ∈ E1.
        left
        intro hm_typ
        exact hexists ⟨m, hm_typ⟩
  -- Step 2: bound the measure.
  -- First: `c.errorProbAt W m = ν (c.errorEvent m)` (by defeq of `codebookToCode`).
  have h_eq_meas : c.errorProbAt W m = ν (c.errorEvent m) := by
    show (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m) = _
    rfl
  -- The error event is measurable (finite alphabet).
  have h_meas_err : MeasurableSet (c.errorEvent m) :=
    (Set.toFinite _).measurableSet
  -- `ν (c.errorEvent m) ≠ ∞`.
  have h_ne_top : ν (c.errorEvent m) ≠ ∞ := measure_ne_top _ _
  -- Convert to .real.
  have h_real_eq : (c.errorProbAt W m).toReal = ν.real (c.errorEvent m) := by
    rw [h_eq_meas]; rfl
  rw [h_real_eq]
  -- Apply monotonicity and union bound.
  have h_meas_E1 : MeasurableSet E1 := (Set.toFinite _).measurableSet
  have h_meas_union : MeasurableSet (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    (Set.toFinite _).measurableSet
  have h_step1 : ν.real (c.errorEvent m) ≤
      ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    measureReal_mono h_sub (by exact measure_ne_top _ _)
  have h_step2 : ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m')
      ≤ ν.real E1 + ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    measureReal_union_le _ _
  have h_step3 :
      ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m')
      ≤ ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, ν.real (E2_indiv m') := by
    exact measureReal_biUnion_finset_le _ _
  -- Combine.
  calc ν.real (c.errorEvent m)
      ≤ ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') := h_step1
    _ ≤ ν.real E1 + ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') := h_step2
    _ ≤ ν.real E1 + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, ν.real (E2_indiv m') := by
        gcongr

/-! ### Phase C-(c) — Random codebook average bound (probabilistic-method form)

The originally-drafted statement averaged over a **uniform** distribution on
`Codebook M n α := Fin M → (Fin n → α)`. That form is intrinsically inconsistent
with the Phase B-(a) / B-(c) bounds, which speak about a **`p`-i.i.d.** law on
the input alphabet. When `p` is not the uniform on `α`, the uniform-on-codebook
expectation does *not* equal any `p`-derived quantity.

We restate Phase C-(c) in the standard Cover-Thomas form: average over the
product law `p^{Mn}` on `Codebook M n α`. Concretely, the codebook law is
`codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`.
Because `α` is finite, this `Measure.pi` is determined by its values on singletons
`{codebook}`, namely the product `∏ m i, p.real {codebook m i}`; the codebook
average is then a finite weighted sum.

The proof itself remains a placeholder (`sorry`) until the Fubini swap between
"codebook expectation" and "i.i.d. expectation over `(X^n, Y^n)`" is built out.
Both sides of the inequality are well-typed and compile. -/

/-- Product law `p^{Mn}` on the codebook space. -/
noncomputable def codebookMeasure
    (p : Measure α) (M n : ℕ) : Measure (Codebook M n α) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))

instance codebookMeasure.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p] (M n : ℕ) :
    IsProbabilityMeasure (codebookMeasure p M n) := by
  unfold codebookMeasure
  infer_instance
end InformationTheory.Shannon.ChannelCoding
