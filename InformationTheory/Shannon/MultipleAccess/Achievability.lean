import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.AchievabilityCore
import InformationTheory.Shannon.MultipleAccess.IIDAmbient
import InformationTheory.Shannon.ChannelCoding.Achievability.Main

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
open scoped ENNReal NNReal BigOperators Topology

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

/-! ### Corner-point information quantities

The three rate corners returned in the entropy-exponent form handed back by the
gateway atoms `macJTS_indep_prob_le_X1`/`_X2`/`_both`: `macInfo₁ = I(X₁; (X₂, Y))`,
`macInfo₂ = I(X₂; (X₁, Y))`, `macInfoBoth = I((X₁, X₂); Y)`, each expressed as a
difference of entropies of marginals of the per-coordinate joint law
`macJointDistribution p₁ p₂ W`.  Under the independent product input `p₁ ⊗ p₂` these
equal the textbook conditional informations `I(X₁; Y | X₂)` / `I(X₂; Y | X₁)` /
`I(X₁, X₂; Y)`. -/

/-- `I(X₁; (X₂, Y)) = H(X₁) + H(X₂, Y) − H(X₁, X₂, Y)` for the per-coordinate joint. -/
noncomputable def macInfo₁
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) : ℝ :=
  entropy (macJointDistribution p₁ p₂ W) Prod.fst
    + entropy (macJointDistribution p₁ p₂ W) Prod.snd
    - entropy (macJointDistribution p₁ p₂ W) id

/-- `I(X₂; (X₁, Y)) = H(X₂) + H(X₁, Y) − H(X₁, X₂, Y)`. -/
noncomputable def macInfo₂
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) : ℝ :=
  entropy (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1)
    + entropy (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.2))
    - entropy (macJointDistribution p₁ p₂ W) id

/-- `I((X₁, X₂); Y) = H(X₁, X₂) + H(Y) − H(X₁, X₂, Y)`. -/
noncomputable def macInfoBoth
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) : ℝ :=
  entropy (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.1))
    + entropy (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2)
    - entropy (macJointDistribution p₁ p₂ W) id

/-! ### Two-codebook averaging -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **Two-codebook random-coding average bound.**  For the i.i.d. MAC ambient measure
`macAmbientMeasure p₁ p₂ W`, averaging the per-pair error probability of the
joint-typical pair decoder over the product of the two codebook laws is bounded by the
four-event sum: the correct-pair atypicality probability `E0`, plus the three
exponential alias terms `E1`/`E2`/`E3` controlled by the gateway atoms
`macJTS_indep_prob_le_X1`/`_X2`/`_both`.

This is the two-codebook generalisation of the single-user
`random_codebook_average_le`; the genuine proof requires re-deriving the single-user
Fubini-swap infrastructure (`codebook_marginal_one`/`_two`) for the three-codeword
marginalisation (true user-1, alias user-1, true user-2) of the paired channel input,
plus the conditional-output fold-in identity and the per-atom reshape.  Left as the
single localized incompleteness of MAC achievability.

@residual(plan:mac-achievability-bonferroni-plan) -/
theorem mac_random_codebook_average_le
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (hε : 0 < ε) :
    ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        ((macCodebookToCode (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
            hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal
      ≤ (macAmbientMeasure p₁ p₂ W).real
          {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
              macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε))
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε))
        + ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) *
            Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) := by
  sorry

/-! ### Random → deterministic (two-codebook pigeonhole) -/

omit [DecidableEq α₁] [Nonempty α₁] [DecidableEq α₂] [Nonempty α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Pigeonhole over the product codebook law: if the two-codebook expectation is `≤ B`,
some deterministic codebook pair achieves `averageErrorProb ≤ B`.
@audit:ok -/
theorem mac_exists_codebook_le_avg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (B : ℝ)
    (h_avg :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal ≤ B) :
    ∃ (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂),
      ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal ≤ B := by
  classical
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- The two codebook laws are probability measures.
  haveI : MeasurableSingletonClass (Fin n → α₁) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → α₂) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (MACCodebook M₁ n α₁) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (MACCodebook M₂ n α₂) := Pi.instMeasurableSingletonClass
  haveI : IsProbabilityMeasure (codebookMeasure p₁ M₁ n) :=
    codebookMeasure.instIsProbabilityMeasure p₁ M₁ n
  haveI : IsProbabilityMeasure (codebookMeasure p₂ M₂ n) :=
    codebookMeasure.instIsProbabilityMeasure p₂ M₂ n
  -- Each codebook law sums to 1 over its (finite) codebook space.
  have h1 : ∑ c₁ : MACCodebook M₁ n α₁, (codebookMeasure p₁ M₁ n).real {c₁} = 1 := by
    have h_real_univ : (codebookMeasure p₁ M₁ n).real
        ((Finset.univ : Finset (MACCodebook M₁ n α₁)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
    rw [sum_measureReal_singleton (μ := codebookMeasure p₁ M₁ n)
      (Finset.univ : Finset (MACCodebook M₁ n α₁)), h_real_univ]
  have h2 : ∑ c₂ : MACCodebook M₂ n α₂, (codebookMeasure p₂ M₂ n).real {c₂} = 1 := by
    have h_real_univ : (codebookMeasure p₂ M₂ n).real
        ((Finset.univ : Finset (MACCodebook M₂ n α₂)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
    rw [sum_measureReal_singleton (μ := codebookMeasure p₂ M₂ n)
      (Finset.univ : Finset (MACCodebook M₂ n α₂)), h_real_univ]
  -- Flatten to a single sum over the product codebook space.
  set weight : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂ → ℝ :=
    fun p ↦ (codebookMeasure p₁ M₁ n).real {p.1} * (codebookMeasure p₂ M₂ n).real {p.2}
    with hweight_def
  set val : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂ → ℝ :=
    fun p ↦ ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε p.1 p.2).averageErrorProb W).toReal
    with hval_def
  have h_w_nn : ∀ p, 0 ≤ weight p := fun p ↦ mul_nonneg measureReal_nonneg measureReal_nonneg
  have h_weight_sum : ∑ p : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂, weight p = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hweight_def]
    rw [← h1]
    refine Finset.sum_congr rfl (fun c₁ _ ↦ ?_)
    rw [← Finset.mul_sum, h2, mul_one]
  -- The flattened expectation is the iterated double sum.
  have h_avg_flat : ∑ p : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂, weight p * val p ≤ B := by
    rw [Fintype.sum_prod_type]
    refine le_trans (le_of_eq ?_) h_avg
    simp only [hweight_def, hval_def]
  -- Some weight is positive (the weights sum to 1 ≠ 0).
  have h_exists_pos : ∃ p, 0 < weight p := by
    by_contra h_np
    simp only [not_exists, not_lt] at h_np
    have h_all_zero : ∀ p, weight p = 0 := fun p ↦ le_antisymm (h_np p) (h_w_nn p)
    have : ∑ p, weight p = 0 := Finset.sum_eq_zero (fun p _ ↦ h_all_zero p)
    rw [this] at h_weight_sum; exact one_ne_zero h_weight_sum.symm
  obtain ⟨p₀, hp₀_pos⟩ := h_exists_pos
  -- Contradiction: B = B·1 < ∑ weight·val ≤ B.
  have h_contra : B < ∑ p, weight p * val p := by
    calc B = B * 1 := (mul_one B).symm
      _ = B * ∑ p, weight p := by rw [h_weight_sum]
      _ = ∑ p, weight p * B := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ < ∑ p, weight p * val p := by
          refine Finset.sum_lt_sum (fun p _ ↦ ?_) ⟨p₀, Finset.mem_univ _, ?_⟩
          · exact mul_le_mul_of_nonneg_left (h_none p.1 p.2).le (h_w_nn p)
          · exact mul_lt_mul_of_pos_left (h_none p₀.1 p₀.2) hp₀_pos
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg_flat h_contra)

/-- Closed-form `N` for the two-user (E3) "both indices wrong" term: with the AEP gap
`Iboth − (R₁ + R₂) − 3ε > 0`, the product `(⌈exp(nR₁)⌉−1)(⌈exp(nR₂)⌉−1)` of the two
codebook sizes times `exp(n(−Iboth+3ε))` falls below any tolerance for large `n`.
@audit:ok -/
theorem mac_E3_lt_of_rate {Iboth R₁ R₂ ε ε' : ℝ}
    (hgap : 0 < Iboth - (R₁ + R₂) - 3 * ε) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N,
      ((Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1) *
        ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-Iboth + 3 * ε)) < ε' := by
  obtain ⟨N, hN⟩ := exp_neg_mul_lt_of_rate hgap hε'
  refine ⟨N, fun n hn ↦ ?_⟩
  have he1 : (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1 ≤ Real.exp ((n : ℝ) * R₁) := by
    have := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R₁)).le; linarith
  have he2 : (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1 ≤ Real.exp ((n : ℝ) * R₂) := by
    have := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R₂)).le; linarith
  have hnn1 : 0 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
    linarith
  have hnn2 : 0 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
    linarith
  calc ((Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1) *
          ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
          Real.exp ((n : ℝ) * (-Iboth + 3 * ε))
      ≤ Real.exp ((n : ℝ) * R₁) * Real.exp ((n : ℝ) * R₂) *
          Real.exp ((n : ℝ) * (-Iboth + 3 * ε)) := by
        gcongr
    _ = Real.exp (-(n : ℝ) * (Iboth - (R₁ + R₂) - 3 * ε)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ < ε' := hN n hn

/-! ### Headline -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **MAC achievability** (Cover–Thomas Theorem 15.3.1, corner-point form).  For an
independent product input `p₁ ⊗ p₂` with full-support marginals and a full-support MAC
channel `W`, any rate pair `(R₁, R₂)` strictly inside the corner-point region
`R₁ < I(X₁; (X₂, Y))`, `R₂ < I(X₂; (X₁, Y))`, `R₁ + R₂ < I((X₁, X₂); Y)` is
achievable: for every target error `ε' > 0` there is `N` such that for all `n ≥ N`
there is a length-`n` two-user code with at least `exp(n R₁)` / `exp(n R₂)` messages per
user whose average error probability is `< ε'`. -/
@[entry_point]
theorem mac_achievability
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {R₁ R₂ : ℝ} (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < macInfo₁ p₁ p₂ W) (hR₂lt : R₂ < macInfo₂ p₁ p₂ W)
    (hRsum : R₁ + R₂ < macInfoBoth p₁ p₂ W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁_lb : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂_lb : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : MACCode M₁ M₂ n α₁ α₂ β),
        (c.averageErrorProb W).toReal < ε' := by
  classical
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Rate slack `ε`: a sixth of the minimum of the three corner gaps.
  set gap : ℝ := min (min (macInfo₁ p₁ p₂ W - R₁) (macInfo₂ p₁ p₂ W - R₂))
      (macInfoBoth p₁ p₂ W - (R₁ + R₂)) with hgap_def
  have hgapA : gap ≤ macInfo₁ p₁ p₂ W - R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hgapB : gap ≤ macInfo₂ p₁ p₂ W - R₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hgapC : gap ≤ macInfoBoth p₁ p₂ W - (R₁ + R₂) := min_le_right _ _
  have hgap_pos : 0 < gap :=
    lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  set ε : ℝ := gap / 6 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have h3ε : 3 * ε = gap / 2 := by rw [hε_def]; ring
  have hgap1 : 0 < macInfo₁ p₁ p₂ W - R₁ - 3 * ε := by linarith
  have hgap2 : 0 < macInfo₂ p₁ p₂ W - R₂ - 3 * ε := by linarith
  have hgap3 : 0 < macInfoBoth p₁ p₂ W - (R₁ + R₂) - 3 * ε := by linarith
  have hε'4 : 0 < ε' / 4 := by linarith
  -- Measurability of the seven coordinate selectors.
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
    (h_aep_real.eventually (eventually_gt_nhds (show (1 : ℝ) - ε' / 4 < 1 by linarith)))
  -- (N₁, N₂, N₃) exponential decay of the three alias terms.
  obtain ⟨N₁, hN₁⟩ := channelCoding_E2_lt_of_rate (I := macInfo₁ p₁ p₂ W) (R := R₁)
    (ε := ε) (ε' := ε' / 4) hgap1 hε'4
  obtain ⟨N₂, hN₂⟩ := channelCoding_E2_lt_of_rate (I := macInfo₂ p₁ p₂ W) (R := R₂)
    (ε := ε) (ε' := ε' / 4) hgap2 hε'4
  obtain ⟨N₃, hN₃⟩ := mac_E3_lt_of_rate (Iboth := macInfoBoth p₁ p₂ W) (R₁ := R₁) (R₂ := R₂)
    (ε := ε) (ε' := ε' / 4) hgap3 hε'4
  refine ⟨max (max N₀ N₁) (max N₂ N₃), fun n hn ↦ ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set M₁ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₁)) with hM₁_def
  set M₂ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₂)) with hM₂_def
  have hM₁_pos : 0 < M₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM₂_pos : 0 < M₂ := Nat.ceil_pos.mpr (Real.exp_pos _)
  -- The two-codebook average bound.
  have h_avg_bound := mac_random_codebook_average_le (M₁ := M₁) (M₂ := M₂) (n := n)
    p₁ p₂ W hp₁ hp₂ hW hM₁_pos hM₂_pos hε_pos
  -- Bound the four terms.
  have hE0 : μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
      macJointlyTypicalSet μ macX1s macX2s macYs n ε} ≤ ε' / 4 := by
    have h_meas_good : MeasurableSet
        {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
            macJointlyTypicalSet μ macX1s macX2s macYs n ε} := by
      have h_meas_triple : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
          (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
        (measurable_jointRV (α := α₁) macX1s measurable_macX1s n).prodMk
          ((measurable_jointRV (α := α₂) macX2s measurable_macX2s n).prodMk
            (measurable_jointRV (α := β) macYs measurable_macYs n))
      exact h_meas_triple (measurableSet_macJointlyTypicalSet μ macX1s macX2s macYs n ε)
    exact complementProbReal_le_of_one_sub_le h_meas_good (le_of_lt (hN₀ n hn0))
  have hE1 : ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)) < ε' / 4 := by
    have := hN₁ n hn1
    rwa [hM₁_def]
  have hE2 : ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)) < ε' / 4 := by
    have := hN₂ n hn2
    rwa [hM₂_def]
  have hE3 : ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) *
      Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) < ε' / 4 := by
    have := hN₃ n hn3
    rwa [hM₁_def, hM₂_def]
  have hRHS_lt :
      μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
            macJointlyTypicalSet μ macX1s macX2s macYs n ε}
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε))
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε))
        + ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) *
            Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) < ε' := by
    linarith
  -- Pigeonhole to a deterministic codebook pair, then package the code.
  obtain ⟨c₁, c₂, hcb⟩ := mac_exists_codebook_le_avg μ macX1s macX2s macYs W p₁ p₂
    hM₁_pos hM₂_pos _ h_avg_bound
  refine ⟨M₁, M₂, le_refl _, le_refl _,
    macCodebookToCode μ macX1s macX2s macYs hM₁_pos hM₂_pos ε c₁ c₂, ?_⟩
  exact lt_of_le_of_lt hcb hRHS_lt

end InformationTheory.Shannon.MAC
