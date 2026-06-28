import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.AchievabilityCore

/-!
# Multiple access channel — achievability codebook, decoder, and Bonferroni bound

The two-user codebook plumbing for MAC achievability (Cover–Thomas §15.3.1): the
joint-typical pair decoder, the bundle of two codebooks into a `MACCode`, and the
four-event Bonferroni decomposition of the per-pair error probability.  This is the
two-codebook / four-event generalisation of the single-user
`InformationTheory.Shannon.ChannelCoding.errorProbAt_le_E1_plus_E2`.

## Main definitions

* `MACCodebook M n α := Fin M → (Fin n → α)` — a length-`n` codebook for one user.
* `macJointTypicalDecoder` — decodes `y` to the unique pair `(m₁, m₂)` whose codeword
  triple `(c₁ m₁, c₂ m₂, y)` is three-way jointly typical, falling back to
  `(⟨0, hM₁⟩, ⟨0, hM₂⟩)` when none / not-unique.
* `macCodebookToCode` — bundle two codebooks + the joint-typical decoder into a `MACCode`.

## Main results

* `mac_errorProbAt_le_bonferroni4` — the four-event union bound on the per-pair error
  probability: `E0` (the correct pair is not typical) plus the three alias sums
  `E1`/`E2`/`E3` (user 1 alias, user 2 alias, both alias).
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ### Codebook + joint-typical pair decoder -/

/-- A length-`n` codebook for one MAC user: a function from message indices to
length-`n` words.  Two codebooks (one per user) make up a `MACCode`. -/
abbrev MACCodebook (M n : ℕ) (α : Type*) := Fin M → (Fin n → α)

/-- Joint-typical pair decoder.  Given a received word `y`, returns the unique message
pair `(m₁, m₂)` such that `(c₁ m₁, c₂ m₂, y) ∈ macJointlyTypicalSet …`, falling back to
`(⟨0, hM₁⟩, ⟨0, hM₂⟩)` if either no such pair exists or it is not unique. -/
noncomputable def macJointTypicalDecoder
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂) :
    (Fin n → β) → Fin M₁ × Fin M₂ := fun y ↦
  haveI : Decidable (∃! p : Fin M₁ × Fin M₂,
      (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! p : Fin M₁ × Fin M₂,
      (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε
    then Classical.choose h.exists
    else (⟨0, hM₁⟩, ⟨0, hM₂⟩)

/-- Bundle two codebooks + the joint-typical pair decoder into a `MACCode`. -/
noncomputable def macCodebookToCode
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂) :
    MACCode M₁ M₂ n α₁ α₂ β where
  encoder₁ := c₁
  encoder₂ := c₂
  decoder := macJointTypicalDecoder μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂

/-! ### Four-event Bonferroni decomposition -/

omit [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- **Four-event Bonferroni bound.**  When the pair `(m₁, m₂)` is sent, the per-pair error
probability of the joint-typical pair decoder is bounded by the four error events:

* `E0` — the correct codeword triple `(c₁ m₁, c₂ m₂, y)` is not jointly typical;
* `E1` — some user-1 alias `m₁' ≠ m₁` (with user 2 correct) is jointly typical;
* `E2` — some user-2 alias `m₂' ≠ m₂` (with user 1 correct) is jointly typical;
* `E3` — some pair `(m₁', m₂')` with both indices wrong is jointly typical.

The block output law is `ν = Measure.pi (i ↦ W (c₁ m₁ i, c₂ m₂ i))`.  This is the
two-codebook / four-event generalisation of the single-user
`errorProbAt_le_E1_plus_E2`; the two-codebook averaging consumes the four terms term by
term. -/
theorem mac_errorProbAt_le_bonferroni4
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).errorProbAt W (m₁, m₂)).toReal
      ≤ (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
          {y | (c₁ m₁, c₂ m₂, y) ∉ macJointlyTypicalSet μ X1s X2s Ys n ε}
        + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
            (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
              {y | (c₁ m₁', c₂ m₂, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε}
        + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
            (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
              {y | (c₁ m₁, c₂ m₂', y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε}
        + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                  ((Finset.univ : Finset (Fin M₂)).erase m₂),
            (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
              {y | (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε} := by
  classical
  -- Treat the (7-fold) jointly typical set as atomic to keep unification cheap.
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet μ X1s X2s Ys n ε with hJ_def
  -- Index sets for the three alias sums.
  set S1 : Finset (Fin M₁) := (Finset.univ : Finset (Fin M₁)).erase m₁ with hS1_def
  set S2 : Finset (Fin M₂) := (Finset.univ : Finset (Fin M₂)).erase m₂ with hS2_def
  set S3 : Finset (Fin M₁ × Fin M₂) := S1 ×ˢ S2 with hS3_def
  -- The code and the block output law.
  set c : MACCode M₁ M₂ n α₁ α₂ β := macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂ with hc_def
  set ν : Measure (Fin n → β) := Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  -- The four error events: E0 (correct pair atypical), and the three alias families.
  set E0 : Set (Fin n → β) := {y | (c₁ m₁, c₂ m₂, y) ∉ J} with hE0_def
  set E1indiv : Fin M₁ → Set (Fin n → β) :=
    fun a ↦ {y | (c₁ a, c₂ m₂, y) ∈ J} with hE1_def
  set E2indiv : Fin M₂ → Set (Fin n → β) :=
    fun b ↦ {y | (c₁ m₁, c₂ b, y) ∈ J} with hE2_def
  set E3indiv : Fin M₁ × Fin M₂ → Set (Fin n → β) :=
    fun p ↦ {y | (c₁ p.1, c₂ p.2, y) ∈ J} with hE3_def
  -- Step 1: the error event is contained in the union of the four error events.
  have h_sub : c.errorEvent (m₁, m₂) ⊆
      ((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b) ∪ ⋃ p ∈ S3, E3indiv p := by
    intro y hy
    rw [MACCode.mem_errorEvent] at hy
    -- A typical alias pair `p ≠ (m₁, m₂)` lands in one of the three alias unions.
    have place : ∀ p : Fin M₁ × Fin M₂,
        (c₁ p.1, c₂ p.2, y) ∈ J → p ≠ (m₁, m₂) →
        y ∈ ((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b) ∪ ⋃ p ∈ S3, E3indiv p := by
      intro p hp_mem hp_ne
      by_cases ha : p.1 = m₁
      · -- user 1 correct, so user 2 must be wrong (E2).
        have hb : p.2 ≠ m₂ := fun hb ↦ hp_ne (Prod.ext_iff.mpr ⟨ha, hb⟩)
        refine Or.inl (Or.inr ?_)
        refine Set.mem_iUnion.mpr ⟨p.2, ?_⟩
        refine Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩, ?_⟩
        change (c₁ m₁, c₂ p.2, y) ∈ J
        rw [← ha]; exact hp_mem
      · by_cases hb : p.2 = m₂
        · -- user 1 wrong, user 2 correct (E1).
          refine Or.inl (Or.inl (Or.inr ?_))
          refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
          refine Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, ?_⟩
          change (c₁ p.1, c₂ m₂, y) ∈ J
          rw [← hb]; exact hp_mem
        · -- both wrong (E3).
          refine Or.inr ?_
          refine Set.mem_iUnion.mpr ⟨p, ?_⟩
          refine Set.mem_iUnion.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩,
              Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩⟩, ?_⟩
          exact hp_mem
    -- Case analyse on whether the correct pair is typical.
    by_cases hc_typ : (c₁ m₁, c₂ m₂, y) ∈ J
    · -- Correct pair typical: either some alias is also typical (E1/E2/E3), or the correct
      -- pair is the unique typical pair, so the decoder outputs `(m₁, m₂)`, contradicting `hy`.
      by_cases h_alias : ∃ p : Fin M₁ × Fin M₂, (c₁ p.1, c₂ p.2, y) ∈ J ∧ p ≠ (m₁, m₂)
      · obtain ⟨p, hp_mem, hp_ne⟩ := h_alias
        exact place p hp_mem hp_ne
      · exfalso
        apply hy
        -- No alias ⇒ `(m₁, m₂)` is the unique typical pair.
        have huniq : ∃! p : Fin M₁ × Fin M₂,
            (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε := by
          refine ⟨(m₁, m₂), hc_typ, ?_⟩
          intro p hp
          by_contra hne
          exact h_alias ⟨p, hp, hne⟩
        change macJointTypicalDecoder μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂ y = (m₁, m₂)
        unfold macJointTypicalDecoder
        rw [dif_pos huniq]
        exact huniq.unique (Classical.choose_spec huniq.exists) hc_typ
    · -- Correct pair atypical: y ∈ E0.
      exact Or.inl (Or.inl (Or.inl hc_typ))
  -- Step 2: bound the error measure by the union bound over the four events.
  have h_eq_meas : c.errorProbAt W (m₁, m₂) = ν (c.errorEvent (m₁, m₂)) := by
    change (Measure.pi (fun i ↦ W (c.encoder₁ (m₁, m₂).1 i, c.encoder₂ (m₁, m₂).2 i)))
        (c.errorEvent (m₁, m₂)) = _
    rfl
  have h_real_eq : (c.errorProbAt W (m₁, m₂)).toReal = ν.real (c.errorEvent (m₁, m₂)) := by
    rw [h_eq_meas]; rfl
  rw [h_real_eq]
  calc ν.real (c.errorEvent (m₁, m₂))
      ≤ ν.real (((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b) ∪ ⋃ p ∈ S3, E3indiv p) :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ν.real ((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b)
          + ν.real (⋃ p ∈ S3, E3indiv p) := measureReal_union_le _ _
    _ ≤ (ν.real (E0 ∪ ⋃ a ∈ S1, E1indiv a) + ν.real (⋃ b ∈ S2, E2indiv b))
          + ν.real (⋃ p ∈ S3, E3indiv p) := add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ ((ν.real E0 + ν.real (⋃ a ∈ S1, E1indiv a)) + ν.real (⋃ b ∈ S2, E2indiv b))
          + ν.real (⋃ p ∈ S3, E3indiv p) :=
        add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl
    _ ≤ ((ν.real E0 + ∑ a ∈ S1, ν.real (E1indiv a)) + ∑ b ∈ S2, ν.real (E2indiv b))
          + ∑ p ∈ S3, ν.real (E3indiv p) :=
        add_le_add (add_le_add (add_le_add le_rfl (measureReal_biUnion_finset_le _ _))
          (measureReal_biUnion_finset_le _ _)) (measureReal_biUnion_finset_le _ _)

end InformationTheory.Shannon.MAC
