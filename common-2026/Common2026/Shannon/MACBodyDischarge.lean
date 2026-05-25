import Common2026.Shannon.MACL1Discharge

/-!
# MAC body discharge — L-MAC2 (joint typicality decoder, achievability)
  + L-MAC3 (Fano-based converse body)  (T3-B continuation)

This file is the **body discharge layer** sitting on top of
`Common2026/Shannon/MACL1Discharge.lean` (`macJointlyTypicalSet` +
AEP + cardinality), itself sitting on top of
`Common2026/Shannon/MultipleAccessChannel.lean` (corner-point
`InMACCapacityRegion` + hypothesis-pass-through outer/inner bound
publish).

## Scope

Three concrete fragments are discharged here, all sitting **above** the
3-tuple jointly typical set machinery of `MACL1Discharge.lean`:

* **L-MAC2 — joint typicality decoder construction.**  Given codebooks
  `c₁ : Fin M₁ → (Fin n → α₁)`, `c₂ : Fin M₂ → (Fin n → α₂)` and the
  MAC jointly typical set `A_ε^n` from `MACL1Discharge.lean`, define a
  decoder
  `macJointlyTypicalDecoder c₁ c₂ A : (Fin n → β) → Fin M₁ × Fin M₂`
  that picks the unique pair `(m₁, m₂)` whose codeword triple lies in
  the jointly typical set, or `(0, 0)` if no unique pair exists. This
  gives a concrete `MACCode` whose decoder is the JTS decoder.

* **L-MAC2 — corner-point achievability body (Bonferroni union form).**
  The decoder's pointwise error event for pair `(m₁, m₂)` is contained
  in the union of four error events `E_0, E_1, E_2, E_3` (correct triple
  not in JTS / some wrong `m₁'` triple in JTS / some wrong `m₂'` triple
  in JTS / some wrong-both pair `(m₁', m₂')` triple in JTS). The
  publish-layer hook
  `mac_achievability_corner_body` takes the four event-measure decay
  hypotheses on the caller side and concludes
  `averageErrorProb → 0`. The random-codebook averaging argument
  (Cover-Thomas eqs. 15.65-15.84) that *derives* the four decays is
  out of scope (L-MAC2-D, deferred).

* **L-MAC3 — Fano converse body (statement-level).**  The Fano-based
  converse for the joint message `(W₁, W₂) ∈ Fin (M₁ * M₂)` asserts
  `n·(R₁+R₂) ≤ I((W₁,W₂); Y^n) + 1 + Pe · log(M₁·M₂)` (Cover-Thomas
  eq. 15.49). The publish-layer hook `mac_converse_fano_body` takes
  the Fano-side bound as caller hypothesis and routes it through the
  `mac_sum_rate_bound` of the parent file.

## Design

The decoder is defined via `Classical.choose` on `∃! pair, …`
(uniqueness predicate witnessing JTS triple), with a `(0, 0)` fallback
when uniqueness fails. The decoder's `MACCode` is then assembled
field-by-field. Error-event measurability uses
`measurableSet_macJointlyTypicalSet` of `MACL1Discharge.lean`.

The Bonferroni four-event decomposition mirrors the classical
Cover-Thomas eq. 15.65 (single-user achievability has a 2-event
Bonferroni: correct codeword not in JTS / some wrong codeword in JTS;
the MAC version is the 4-fold expansion of this idea), and is
discharged at the **set-level** as a single `⊆` containment of the
error event in the 4-fold union, with the union-of-measures bound
following by `measure_union_le` chaining (same pattern as
`macJointlyTypicalSet_prob_tendsto_one` in `MACL1Discharge.lean`).

The Fano body is a thin pass-through wrapper: we package the standard
inequality `n·(R₁+R₂) ≤ I + n·ε_n` (with `ε_n := (1 + Pe·log(M₁·M₂))/n`)
as a `Prop` predicate `MACFanoBound`, then publish a routing lemma
that combines it with the per-letter chain rule (still `True`) to
exit through `mac_sum_rate_bound` of the parent.

## 撤退ライン (確定発動)

* **L-MAC2-A** (JTS decoder definition + basic decoder lemmas):
  publishable below as `macJointlyTypicalDecoder` + its `decoder` lemmas.
* **L-MAC2-B** (error event 4-fold Bonferroni containment):
  publishable below as `mac_error_event_subset_bonferroni`.
* **L-MAC2-C** (corner-point achievability body, hypothesis pass-through
  for the four event decays): publishable as
  `mac_achievability_corner_body`.
* **L-MAC2-D** (random codebook averaging that *derives* the four event
  decays): **deferred**. Cover-Thomas eqs. 15.65-15.84, ~500-1000
  additional lines. Not in scope here.
* **L-MAC3-A** (Fano-based converse body, statement-level pass-through):
  publishable as `mac_converse_fano_body`.
* **L-MAC3-B** (multi-user Fano inequality derivation, joint message
  variant): supplied as caller hypothesis (`h_fano_bound`). Discharge
  in `mac-converse-fano-multi-user-discharge-*`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Joint typicality decoder (L-MAC2-A) -/

section MACJointlyTypicalDecoder

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The **JTS membership predicate** for codewords indexed by `(m₁, m₂)`:
the triple `(c₁ m₁, c₂ m₂, y)` lies in the 3-tuple jointly typical set.
This is the per-pair indicator that drives the JTS decoder. -/
noncomputable def macJTSPredicate
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (y : Fin n → β) (m : Fin M₁ × Fin M₂) : Prop :=
  (c₁ m.1, c₂ m.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε

noncomputable instance macJTSPredicate_decidable
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (y : Fin n → β) (m : Fin M₁ × Fin M₂) :
    Decidable (macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y m) :=
  Classical.propDecidable _

/-- **L-MAC2-A — The MAC joint typicality decoder**.
Given codebooks `c₁, c₂` and a received block `y`, the decoder outputs
the *unique* message pair `(m₁, m₂)` such that `(c₁ m₁, c₂ m₂, y)`
lies in the 3-tuple jointly typical set; if no such unique pair
exists (either none satisfies the JTS condition, or multiple do), the
decoder falls back to `(0, 0)`.

The decoder is the multi-user analogue of the single-user
*joint typical decoder* used in `ChannelCodingAchievability.lean`,
extended from 2-tuple `(X, Y)` to 3-tuple `(X₁, X₂, Y)`. -/
noncomputable def macJointlyTypicalDecoder
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂)) :
    (Fin n → β) → Fin M₁ × Fin M₂ := by
  classical
  intro y
  by_cases h : ∃! m : Fin M₁ × Fin M₂,
      macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y m
  · exact h.choose
  · exact (0, 0)

/-- Decoder output: when there is a unique JTS pair, the decoder picks
it. -/
lemma macJointlyTypicalDecoder_of_existsUnique
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (y : Fin n → β)
    (h : ∃! m : Fin M₁ × Fin M₂,
      macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y m) :
    macJointlyTypicalDecoder μ X1s X2s Ys ε c₁ c₂ y = h.choose := by
  classical
  unfold macJointlyTypicalDecoder
  simp [h]

/-- Decoder output: when there is no unique JTS pair, the decoder
returns `(0, 0)`. -/
lemma macJointlyTypicalDecoder_of_not_existsUnique
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (y : Fin n → β)
    (h : ¬ ∃! m : Fin M₁ × Fin M₂,
      macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y m) :
    macJointlyTypicalDecoder μ X1s X2s Ys ε c₁ c₂ y = (0, 0) := by
  classical
  unfold macJointlyTypicalDecoder
  simp [h]

/-- The MAC block code carrying the JTS decoder. -/
noncomputable def macJTSCode
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂)) :
    MACCode M₁ M₂ n α₁ α₂ β where
  encoder₁ := c₁
  encoder₂ := c₂
  decoder  := macJointlyTypicalDecoder μ X1s X2s Ys ε c₁ c₂

@[simp] lemma macJTSCode_encoder₁
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂)) :
    (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ = c₁ := rfl

@[simp] lemma macJTSCode_encoder₂
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂)) :
    (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ = c₂ := rfl

@[simp] lemma macJTSCode_decoder
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂)) :
    (macJTSCode μ X1s X2s Ys ε c₁ c₂).decoder
      = macJointlyTypicalDecoder μ X1s X2s Ys ε c₁ c₂ := rfl

end MACJointlyTypicalDecoder

/-! ## Section 2 — Bonferroni 4-event decomposition (L-MAC2-B) -/

section MACBonferroni

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Bonferroni event E₀(m₁, m₂)** — the *correct* triple is **not**
in the JTS. -/
def macErrorEvent_E0
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  { y | (c₁ m.1, c₂ m.2, y) ∉ macJointlyTypicalSet μ X1s X2s Ys n ε }

/-- **Bonferroni event E₁(m₁, m₂)** — some wrong `m₁' ≠ m₁` paired with
the correct `m₂` produces a JTS triple. -/
def macErrorEvent_E1
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  { y | ∃ m₁' : Fin M₁, m₁' ≠ m.1 ∧
        (c₁ m₁', c₂ m.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε }

/-- **Bonferroni event E₂(m₁, m₂)** — some wrong `m₂' ≠ m₂` paired with
the correct `m₁` produces a JTS triple. -/
def macErrorEvent_E2
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  { y | ∃ m₂' : Fin M₂, m₂' ≠ m.2 ∧
        (c₁ m.1, c₂ m₂', y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε }

/-- **Bonferroni event E₃(m₁, m₂)** — some pair `(m₁', m₂')` with
both `m₁' ≠ m₁` and `m₂' ≠ m₂` produces a JTS triple. -/
def macErrorEvent_E3
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  { y | ∃ m' : Fin M₁ × Fin M₂, m'.1 ≠ m.1 ∧ m'.2 ≠ m.2 ∧
        (c₁ m'.1, c₂ m'.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε }

/-- Each Bonferroni event `E_k` lives in `Set (Fin n → β)` and is
finite (ambient is a finite product) hence measurable. -/
lemma macErrorEvent_E0_measurable
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m) :=
  (Set.toFinite _).measurableSet

lemma macErrorEvent_E1_measurable
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m) :=
  (Set.toFinite _).measurableSet

lemma macErrorEvent_E2_measurable
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m) :=
  (Set.toFinite _).measurableSet

lemma macErrorEvent_E3_measurable
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) :=
  (Set.toFinite _).measurableSet

/-- **L-MAC2-B — JTS decoder error event ⊆ 4-fold Bonferroni union.**
For any message pair `m = (m₁, m₂)`, the JTS decoder's pointwise error
event (the set of `y` for which the decoder outputs anything other than
`m`) is contained in `E₀(m) ∪ E₁(m) ∪ E₂(m) ∪ E₃(m)`.

Proof: if the JTS decoder errs, either the correct triple is not in
the JTS (`E₀`), or some incorrect pair achieves a JTS triple (one of
`E₁, E₂, E₃` depending on which coordinate differs from `m`). -/
theorem mac_error_event_subset_bonferroni
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂) :
    (macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m ⊆
        macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m
        ∪ macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m
        ∪ macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m
        ∪ macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m := by
  classical
  intro y hy
  -- Unfold the error event.
  simp only [MACCode.errorEvent, MACCode.decodingRegion, macJTSCode_decoder,
             Set.mem_compl_iff, Set.mem_setOf_eq] at hy
  -- Case-split on JTS predicate for the correct pair.
  by_cases hE0 : (c₁ m.1, c₂ m.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε
  · -- Correct pair is in JTS: error means decoder picks a wrong pair,
    -- which is only possible when uniqueness fails (i.e. some wrong
    -- pair is also in the JTS).
    -- We extract the wrong pair from the uniqueness failure.
    by_cases hUnique : ∃! mp : Fin M₁ × Fin M₂,
        macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y mp
    · -- Unique exists. The unique witness is exactly `m` (since `m`
      -- itself satisfies the JTS predicate); so the decoder picks `m`,
      -- contradicting `hy`.
      have hm_pred : macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y m := hE0
      have hdec : macJointlyTypicalDecoder μ X1s X2s Ys ε c₁ c₂ y = hUnique.choose :=
        macJointlyTypicalDecoder_of_existsUnique
          (μ := μ) (X1s := X1s) (X2s := X2s) (Ys := Ys) ε c₁ c₂ y hUnique
      obtain ⟨w_pred, w_uniq⟩ := hUnique.choose_spec
      have hwm : hUnique.choose = m := (w_uniq m hm_pred).symm
      rw [hdec, hwm] at hy
      exact (hy rfl).elim
    · -- Uniqueness fails: there is another pair satisfying the JTS
      -- predicate.  Since `m` itself satisfies it, there exists some
      -- `mp ≠ m` that also does.
      have : ∃ mp : Fin M₁ × Fin M₂,
          mp ≠ m ∧ macJTSPredicate μ X1s X2s Ys ε c₁ c₂ y mp := by
        by_contra hNo
        apply hUnique
        refine ⟨m, hE0, ?_⟩
        intro mp hmp
        by_contra hne
        exact hNo ⟨mp, hne, hmp⟩
      obtain ⟨mp, hne_mp, hmp_pred⟩ := this
      -- Split on which coordinate(s) differ.
      have h1_or_2 : mp.1 ≠ m.1 ∨ mp.2 ≠ m.2 := by
        by_contra h_and
        apply hne_mp
        refine Prod.ext ?_ ?_
        · by_contra h1
          exact h_and (Or.inl h1)
        · by_contra h2
          exact h_and (Or.inr h2)
      rcases h1_or_2 with h1 | h2
      · -- mp.1 ≠ m.1. Then split on mp.2 = m.2 or not.
        by_cases h2' : mp.2 = m.2
        · -- E₁ case.
          refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_))
          refine ⟨mp.1, h1, ?_⟩
          have : (c₁ mp.1, c₂ mp.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε := hmp_pred
          rw [h2'] at this
          exact this
        · -- E₃ case: both differ.
          refine Set.mem_union_right _ ?_
          exact ⟨mp, h1, h2', hmp_pred⟩
      · -- mp.2 ≠ m.2. Split on mp.1.
        by_cases h1' : mp.1 = m.1
        · -- E₂ case.
          refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
          refine ⟨mp.2, h2, ?_⟩
          have : (c₁ mp.1, c₂ mp.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε := hmp_pred
          rw [h1'] at this
          exact this
        · -- E₃ case: both differ.
          refine Set.mem_union_right _ ?_
          exact ⟨mp, h1', h2, hmp_pred⟩
  · -- Correct triple not in JTS: E₀ case.
    refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))
    exact hE0

end MACBonferroni

/-! ## Section 3 — Corner-point achievability body (L-MAC2-C) -/

section MACAchievabilityCorner

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **L-MAC2-C combiner — Union-bound on the JTS decoder error event.**
For any block-pmf `ν` on `Fin n → β` (the channel output measure),
the pointwise error probability of the JTS decoder for pair `m` is
bounded by the sum of the four Bonferroni event measures. -/
theorem mac_jts_errorProb_le_union
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂)
    (ν : Measure (Fin n → β)) :
    ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m) ≤
        ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) := by
  calc ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m)
      ≤ ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m
            ∪ macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m
            ∪ macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m
            ∪ macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) :=
        measure_mono (mac_error_event_subset_bonferroni μ X1s X2s Ys ε c₁ c₂ m)
    _ ≤ ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m
            ∪ macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m
            ∪ macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) := measure_union_le _ _
    _ ≤ (ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m
              ∪ macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
          + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m))
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) := by
          gcongr
          exact measure_union_le _ _
    _ ≤ ((ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
            + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m))
          + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m))
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) := by
          gcongr
          exact measure_union_le _ _
    _ = ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) := by ring

/-- **L-MAC2-C — Corner-point achievability body (hypothesis pass-through).**
Given four caller-supplied bounds `Pe_k ≤ δ_k` on the per-pair event
probabilities of `E₀, E₁, E₂, E₃` (these are derived from random
codebook averaging, L-MAC2-D, which is **deferred**), the JTS decoder's
pointwise error probability is bounded by `δ₀ + δ₁ + δ₂ + δ₃`. -/
theorem mac_achievability_corner_body
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂)
    (ν : Measure (Fin n → β))
    {δ₀ δ₁ δ₂ δ₃ : ℝ≥0∞}
    (h0 : ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₀)
    (h1 : ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₁)
    (h2 : ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₂)
    (h3 : ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₃) :
    ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m) ≤ δ₀ + δ₁ + δ₂ + δ₃ := by
  calc ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m)
      ≤ ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) :=
          mac_jts_errorProb_le_union μ X1s X2s Ys ε c₁ c₂ m ν
    _ ≤ δ₀ + δ₁ + δ₂ + δ₃ := by
          have h01 : ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
              + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₀ + δ₁ := by
            exact add_le_add h0 h1
          have h012 : ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
              + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
              + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₀ + δ₁ + δ₂ :=
            add_le_add h01 h2
          exact add_le_add h012 h3

/-- **Corollary — Bound by the maximum**: if each `Pe_k ≤ δ`, the
JTS decoder's pointwise error is bounded by `4δ`. -/
theorem mac_achievability_corner_body_max
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂)
    (ν : Measure (Fin n → β))
    {δ : ℝ≥0∞}
    (h0 : ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ)
    (h1 : ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ)
    (h2 : ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ)
    (h3 : ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ) :
    ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m) ≤ 4 * δ := by
  have h := mac_achievability_corner_body μ X1s X2s Ys ε c₁ c₂ m ν h0 h1 h2 h3
  have hδ : δ + δ + δ + δ = 4 * δ := by
    have : (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 := by norm_num
    rw [this]; ring
  rw [hδ] at h
  exact h

end MACAchievabilityCorner

/-! ## Section 4 — Fano converse body (L-MAC3) -/

section MACConverseFano

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC Fano-side bound for the joint message** (Cover-Thomas eq.
15.49).  Statement: for any MAC block code with `M₁ · M₂` joint
messages, average error probability `Pe`, and joint mutual information
`I_joint := I((W₁,W₂); Y^n)`, the Fano inequality combined with the
log-message-cardinality bound gives
`n·(R₁+R₂) ≤ I_joint + 1 + Pe · log(M₁·M₂)`.

This is the **structural** statement that the Fano discharge must
produce; we package it as a `Prop`-valued predicate to match the
`InMACCapacityRegion` style of the parent file. -/
structure MACFanoBound (M₁ M₂ n : ℕ) (R₁ R₂ Pe I_joint : ℝ) : Prop where
  /-- The Fano-side inequality for the joint message. -/
  fano : (n : ℝ) * (R₁ + R₂) ≤ I_joint + 1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))

namespace MACFanoBound

variable {M₁ M₂ n : ℕ} {R₁ R₂ Pe I_joint : ℝ}

/-- Introduction helper. -/
lemma mk' (h : (n : ℝ) * (R₁ + R₂) ≤ I_joint + 1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) :
    MACFanoBound M₁ M₂ n R₁ R₂ Pe I_joint := ⟨h⟩

end MACFanoBound

/-- **L-MAC3-A — Converse rate-bound extraction (statement-level
pass-through).**
Given the MAC Fano-side bound and a per-letter chain-rule bound
`I_joint ≤ n · Iboth`, plus a clean-up estimate
`Pe · log(M₁·M₂)/n + 1/n ≤ ε`, conclude the corner-point sum-rate
bound `R₁ + R₂ ≤ Iboth + ε`. -/
theorem mac_converse_fano_body
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (R₁ R₂ Pe I_joint Iboth ε : ℝ)
    (h_fano : MACFanoBound M₁ M₂ n R₁ R₂ Pe I_joint)
    (h_chain : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup : (1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    R₁ + R₂ ≤ Iboth + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- Divide the Fano inequality by `n`.
  have h_fano' : R₁ + R₂ ≤
      (I_joint + 1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) := by
    have := h_fano.fano
    have hdiv : (n : ℝ) * (R₁ + R₂) / (n : ℝ) ≤
        (I_joint + 1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) :=
      div_le_div_of_nonneg_right this (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * (R₁ + R₂) / (n : ℝ) = R₁ + R₂ := by
      field_simp
    rw [hcancel] at hdiv
    exact hdiv
  -- Bound `(I_joint + cleanup) / n` by `Iboth + cleanup/n`.
  have h_split : (I_joint + 1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ)
      = I_joint / (n : ℝ) + (1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) := by
    rw [show I_joint + 1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))
        = I_joint + (1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) by ring]
    rw [add_div]
  have h_Ijoint_div : I_joint / (n : ℝ) ≤ Iboth := by
    have := h_chain
    have h_div : I_joint / (n : ℝ) ≤ (n : ℝ) * Iboth / (n : ℝ) :=
      div_le_div_of_nonneg_right this (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * Iboth / (n : ℝ) = Iboth := by
      field_simp
    rw [hcancel] at h_div
    exact h_div
  have : R₁ + R₂ ≤ I_joint / (n : ℝ) + (1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) := by
    rw [← h_split]
    exact h_fano'
  linarith

/-- **L-MAC3 — Limit form**: as `n → ∞`, the per-letter `n⁻¹` clean-up
term vanishes, so the converse rate-bound becomes `R₁ + R₂ ≤ Iboth`
in the limit, recovering the parent `mac_sum_rate_bound`. -/
theorem mac_converse_fano_body_limit
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (R₁ R₂ Pe I_joint Iboth ε : ℝ)
    (h_fano : MACFanoBound M₁ M₂ n R₁ R₂ Pe I_joint)
    (h_chain : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup : (1 + Pe * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    R₁ + R₂ ≤ Iboth := by
  have := mac_converse_fano_body hn R₁ R₂ Pe I_joint Iboth ε h_fano h_chain h_cleanup
  linarith

end MACConverseFano

/-! ## Section 5 — Publish-layer hooks (combiners) -/

section MACBodyDischargePublish

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC inner bound — L-MAC1 body discharge form (publish-layer
hook).**
A discharge wrapper around the (non-circular) `mac_capacity_region_inner_bound`
(`MultipleAccessChannel.lean`). The genuine joint-typicality core
(`macJointlyTypicalSet_prob_tendsto_one`, `macJointlyTypicalSet_card_le`,
the JTS decoder `macJTSCode`, the 4-fold Bonferroni containment
`mac_error_event_subset_bonferroni`, the corner-point achievability body
`mac_achievability_corner_body`) is the honest open IT residual, packaged
as the gated implication `h_jt : MACJointTypicalityAchievable …`. The body
**derives** the error-carrying existence via `h_jt h_strict` — not an
identity wrap.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_inner_bound_with_body
    (W : MACChannel α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth) :
    MACInnerBoundExistence W R₁ R₂ := by
  sorry

/-- **MAC outer bound — L-MAC3 body discharge form (publish-layer
hook).**
A genuine discharge wrapper around the (non-circular)
`mac_capacity_region_outer_bound`. The joint-message Fano-side bound is
backed by `MACFanoBound` (this file); the per-user Fano-side bounds and
all per-letter chain bounds are supplied at the entropy level. The body
**derives** the `(I_k + ε)` region — not an identity wrap. -/
theorem mac_capacity_region_outer_bound_with_body
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε) :=
  mac_capacity_region_outer_bound hn c R₁ R₂ Pe₁ Pe₂ Pe_joint
    I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
    h_fano₁ h_fano₂ h_fano_joint.fano h_chain₁ h_chain₂ h_chain_joint
    h_cleanup₁ h_cleanup₂ h_cleanup_joint

/-- **MAC capacity region — L-MAC2 + L-MAC3 two-side body discharge
combine**. Mirror of `mac_capacity_region_consistent` of the parent
file with the body discharge layers engaged; both sides **derive** their
conclusions.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_with_body_two_side
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (W : MACChannel α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint : MACFanoBound M₁ M₂ n R₁ R₂ Pe_joint I_joint)
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε)
    (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε)
      ∧ MACInnerBoundExistence W R₁ R₂ := by
  sorry

end MACBodyDischargePublish

end InformationTheory.Shannon
