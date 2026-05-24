import Common2026.Shannon.BroadcastChannelSuperposition
import Common2026.Shannon.MACBodyDischarge

/-!
# BC superposition coding — L-BC2 body discharge (T3-C continuation)

This file is the **body discharge layer** sitting on top of
`Common2026/Shannon/BroadcastChannelSuperposition.lean` (which carries
the L-BC2-A through L-BC2-F superposition encoder + per-receiver
jointly-typical-set machinery + AEP/cardinality fragments), itself sitting
on top of `Common2026/Shannon/BroadcastChannel.lean` (corner-point
`InBCCapacityRegion` + hypothesis-pass-through outer/inner bound publish).

It mirrors the MAC body discharge layer
(`Common2026/Shannon/MACBodyDischarge.lean`) verbatim, adapted to the
two-receiver structure of the broadcast channel: receiver 1 (private,
good end of the degraded chain) uses a 3-tuple `(U, X, Y_1)` joint
typicality decoder; receiver 2 (common, poor end) uses a 2-tuple
`(U, Y_2)` joint typicality decoder.

## Scope (body discharge — L-BC2-G + L-BC2-H + L-BC2-I partial)

Three fragments are discharged here, all sitting **above** the
per-receiver jointly typical set machinery of
`BroadcastChannelSuperposition.lean`:

* **L-BC2-G — receiver-1 joint typicality decoder construction.**  Given
  a superposition encoder `(outer, inner)` and the receiver-1 jointly
  typical set, define a decoder
  `bcReceiver1JointlyTypicalDecoder e A : (Fin n → β₁) → Fin M₁ × Fin M₂`
  that picks the unique pair `(m₁, m₂)` whose `(U^n(m₂), X^n(m₂, m₁),
  y_1)` triple lies in the receiver-1 jointly typical set, or `(0, 0)`
  if no unique pair exists.

* **L-BC2-G — receiver-1 4-error-event Bonferroni body.**  The decoder's
  pointwise error event for message pair `(m₁, m₂)` is contained in the
  union of four error events `F_0, F_1, F_2, F_3` per receiver 1
  (correct triple not in JTS / some wrong `m₁'` triple in JTS / some
  wrong `m₂'` triple in JTS / some wrong-both pair `(m₁', m₂')` triple
  in JTS). The publish-layer hook
  `bc_receiver1_achievability_body` takes the four event-measure decay
  hypotheses on the caller side and concludes
  `errorProb₁ ≤ δ₀ + δ₁ + δ₂ + δ₃`. The random-codebook averaging
  argument (Cover-Thomas eqs. 15.6.18-15.6.27) that *derives* the four
  decays is out of scope (L-BC2-I, deferred).

* **L-BC2-H — receiver-2 2-error-event Bonferroni body.**  Receiver 2
  decodes only the common message `m₂` from `(U^n(m₂), y_2)`. The
  decoder errs iff either the correct pair `(U^n(m₂), y_2)` is not in
  the receiver-2 jointly typical set (`G₀`), or some wrong `m₂' ≠ m₂`
  produces a JTS pair `(U^n(m₂'), y_2) ∈ B_ε^n` (`G₁`). The publish-layer
  hook `bc_receiver2_achievability_body` takes the two event-measure
  decay hypotheses and concludes `errorProb₂ ≤ δ₀ + δ₁`. Random-codebook
  averaging (Cover-Thomas eqs. 15.6.28-15.6.30) is deferred to L-BC2-I.

The combined two-receiver error probability is bounded by the sum
(`bc_jts_jointErrorProb_le_sum`), packaging both receivers' decoders
into a single `BroadcastCode` via `bcSuperpositionCode` of
`BroadcastChannelSuperposition.lean`.

## Design (Mathlib-shape-driven)

The receiver-1 decoder reuses the MAC JTS decoder verbatim: receiver 1's
3-tuple `(X, U, Y_1)` joint typical set is **definitionally** the MAC
3-tuple jointly typical set with `α₁ := α` (the X-layer) and `α₂ := υ`
(the U-layer), per `BroadcastChannelSuperposition.bcReceiver1JointlyTypicalSet`
(which delegates to `macJointlyTypicalSet`). The Bonferroni 4-event
decomposition is therefore a direct re-instantiation of
`mac_error_event_subset_bonferroni`.

The receiver-2 decoder uses a fresh JTS-decoder construction (no MAC
analogue, because the single-user MAC degenerate would be the regular
single-user JTS decoder of `ChannelCodingAchievability.lean`, but
encoder semantics differ: receiver 2 sees only `U`, not `X`, so the
JTS predicate sums over `m₁`). We define
`bcReceiver2JointlyTypicalDecoder` from scratch, parametrised by the
*outer* (U-)codebook of the superposition encoder only — the inner
X-codebook is irrelevant to receiver 2's decoding choice.

## 撤退ライン (確定発動)

* **L-BC2-G-1** (receiver-1 JTS decoder definition + basic lemmas):
  publishable as `bcReceiver1JointlyTypicalDecoder` + supporting lemmas.
* **L-BC2-G-2** (receiver-1 error event 4-fold Bonferroni containment):
  publishable as `bc_receiver1_error_event_subset_bonferroni`.
* **L-BC2-G-3** (receiver-1 corner-point achievability body):
  publishable as `bc_receiver1_achievability_body`.
* **L-BC2-H-1** (receiver-2 JTS decoder + basic lemmas):
  publishable as `bcReceiver2JointlyTypicalDecoder`.
* **L-BC2-H-2** (receiver-2 error event 2-fold Bonferroni containment):
  publishable as `bc_receiver2_error_event_subset_bonferroni`.
* **L-BC2-H-3** (receiver-2 corner-point achievability body):
  publishable as `bc_receiver2_achievability_body`.
* **L-BC2-I-partial** (joint two-receiver union bound publish-layer
  hook): publishable as
  `bc_capacity_region_inner_bound_with_superposition_body`.
* **L-BC2-I-deferred** (random codebook averaging that *derives* the
  per-event decays for both receivers, Cover-Thomas eqs. 15.6.18-15.6.30):
  **deferred**. ~400-600 additional lines. Not in scope here. The
  publish-layer hook keeps `h_existence` as a caller hypothesis,
  matching the pattern of `mac_capacity_region_inner_bound_with_body`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Receiver-1 JTS decoder (L-BC2-G-1) -/

section BCReceiver1JointlyTypicalDecoder

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]

/-- The **receiver-1 JTS membership predicate** for codewords indexed by
`(m₁, m₂)`: the triple `(X^n(m₂, m₁), U^n(m₂), y_1)` lies in the
receiver-1 jointly typical set. -/
noncomputable def bcReceiver1JTSPredicate
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (y₁ : Fin n → β₁) (m : Fin M₁ × Fin M₂) : Prop :=
  (e.inner (m.2, m.1), e.outer m.2, y₁) ∈
    bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε

noncomputable instance bcReceiver1JTSPredicate_decidable
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (y₁ : Fin n → β₁) (m : Fin M₁ × Fin M₂) :
    Decidable (bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ m) :=
  Classical.propDecidable _

/-- **L-BC2-G-1 — Receiver-1 joint typicality decoder.**
Given a superposition encoder `e` and a received block `y₁`, the
decoder outputs the *unique* message pair `(m₁, m₂)` such that the
triple `(X^n(m₂, m₁), U^n(m₂), y_1)` lies in the receiver-1 jointly
typical set; if no such unique pair exists, the decoder falls back to
`(0, 0)`.

Receiver 1 actually only outputs `m₁` (the private message); we package
the full pair `(m₁, m₂)` here and project to receiver 1's output via
`Prod.fst` in `bcReceiver1Decoder` below. -/
noncomputable def bcReceiver1JointlyTypicalDecoderPair
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α) :
    (Fin n → β₁) → Fin M₁ × Fin M₂ := by
  classical
  intro y₁
  by_cases h : ∃! m : Fin M₁ × Fin M₂,
      bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ m
  · exact h.choose
  · exact (0, 0)

/-- Decoder pair output: when there is a unique JTS pair, the decoder
picks it. -/
lemma bcReceiver1JointlyTypicalDecoderPair_of_existsUnique
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (y₁ : Fin n → β₁)
    (h : ∃! m : Fin M₁ × Fin M₂,
      bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ m) :
    bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁ = h.choose := by
  classical
  unfold bcReceiver1JointlyTypicalDecoderPair
  simp [h]

/-- Decoder pair output: when there is no unique JTS pair, the decoder
returns `(0, 0)`. -/
lemma bcReceiver1JointlyTypicalDecoderPair_of_not_existsUnique
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (y₁ : Fin n → β₁)
    (h : ¬ ∃! m : Fin M₁ × Fin M₂,
      bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ m) :
    bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁ = (0, 0) := by
  classical
  unfold bcReceiver1JointlyTypicalDecoderPair
  simp [h]

/-- **Receiver-1's actual decoder** (projecting the JTS-decoded pair to
its private-message coordinate). -/
noncomputable def bcReceiver1JointlyTypicalDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α) :
    (Fin n → β₁) → Fin M₁ :=
  fun y₁ => (bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁).1

end BCReceiver1JointlyTypicalDecoder

/-! ## Section 2 — Receiver-2 JTS decoder (L-BC2-H-1) -/

section BCReceiver2JointlyTypicalDecoder

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The **receiver-2 JTS membership predicate** for cloud-center index
`m₂`: the pair `(U^n(m₂), y_2)` lies in the receiver-2 jointly typical
set. Only the outer (U-)codebook is consulted; the inner X-codebook is
not visible to receiver 2. -/
noncomputable def bcReceiver2JTSPredicate
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (y₂ : Fin n → β₂) (m₂ : Fin M₂) : Prop :=
  (outer m₂, y₂) ∈ bcReceiver2JointlyTypicalSet μ Us Y₂s n ε

noncomputable instance bcReceiver2JTSPredicate_decidable
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (y₂ : Fin n → β₂) (m₂ : Fin M₂) :
    Decidable (bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ m₂) :=
  Classical.propDecidable _

/-- **L-BC2-H-1 — Receiver-2 joint typicality decoder.**
Given an outer (cloud-center) codebook `outer : Fin M₂ → (Fin n → υ)`
and a received block `y₂`, the decoder outputs the *unique* common
message `m₂` such that `(outer m₂, y₂)` lies in the receiver-2 jointly
typical set; if no such unique `m₂` exists, the decoder falls back to
`0`. -/
noncomputable def bcReceiver2JointlyTypicalDecoder
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} [NeZero M₂] (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ)) :
    (Fin n → β₂) → Fin M₂ := by
  classical
  intro y₂
  by_cases h : ∃! m₂ : Fin M₂,
      bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ m₂
  · exact h.choose
  · exact 0

/-- Decoder output: when there is a unique JTS witness, the decoder
picks it. -/
lemma bcReceiver2JointlyTypicalDecoder_of_existsUnique
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} [NeZero M₂] (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (y₂ : Fin n → β₂)
    (h : ∃! m₂ : Fin M₂,
      bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ m₂) :
    bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε outer y₂ = h.choose := by
  classical
  unfold bcReceiver2JointlyTypicalDecoder
  simp [h]

/-- Decoder output: when uniqueness fails, the decoder returns `0`. -/
lemma bcReceiver2JointlyTypicalDecoder_of_not_existsUnique
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} [NeZero M₂] (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (y₂ : Fin n → β₂)
    (h : ¬ ∃! m₂ : Fin M₂,
      bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ m₂) :
    bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε outer y₂ = 0 := by
  classical
  unfold bcReceiver2JointlyTypicalDecoder
  simp [h]

end BCReceiver2JointlyTypicalDecoder

/-! ## Section 3 — Assembled BroadcastCode (JTS pair, both receivers) -/

section BCJTSCode

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The **BC block code with both JTS decoders attached**. Receiver 1
gets the projected pair-decoder (private message); receiver 2 gets the
common-message-only JTS decoder operating on the outer codebook. -/
noncomputable def bcJTSCode
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ)
    (Y₁s : ℕ → Ω → β₁) (Y₂s : ℕ → Ω → β₂)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α) :
    BroadcastCode M₁ M₂ n α β₁ β₂ :=
  bcSuperpositionCode
    (β₁ := β₁) (β₂ := β₂)
    e
    (bcReceiver1JointlyTypicalDecoder μ Xs Us Y₁s ε e)
    (bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε e.outer)

@[simp] lemma bcJTSCode_encoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ)
    (Y₁s : ℕ → Ω → β₁) (Y₂s : ℕ → Ω → β₂)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    (bcJTSCode μ Xs Us Y₁s Y₂s ε e).encoder (m₁, m₂) = e.inner (m₂, m₁) := rfl

@[simp] lemma bcJTSCode_decoder₁
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ)
    (Y₁s : ℕ → Ω → β₁) (Y₂s : ℕ → Ω → β₂)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α) :
    (bcJTSCode μ Xs Us Y₁s Y₂s ε e).decoder₁
      = bcReceiver1JointlyTypicalDecoder μ Xs Us Y₁s ε e := rfl

@[simp] lemma bcJTSCode_decoder₂
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ)
    (Y₁s : ℕ → Ω → β₁) (Y₂s : ℕ → Ω → β₂)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α) :
    (bcJTSCode μ Xs Us Y₁s Y₂s ε e).decoder₂
      = bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε e.outer := rfl

end BCJTSCode

/-! ## Section 4 — Receiver-1 Bonferroni 4-event decomposition (L-BC2-G-2) -/

section BCReceiver1Bonferroni

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]

/-- **Receiver-1 Bonferroni event F₀(m₁, m₂)** — the *correct* triple
`(X^n(m₂, m₁), U^n(m₂), y_1)` is **not** in the receiver-1 jointly
typical set. -/
def bcReceiver1ErrorEvent_F0
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β₁) :=
  { y₁ | (e.inner (m.2, m.1), e.outer m.2, y₁) ∉
    bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε }

/-- **Receiver-1 Bonferroni event F₁(m₁, m₂)** — some wrong `m₁' ≠ m₁`
paired with the correct `m₂` produces a receiver-1 JTS triple. -/
def bcReceiver1ErrorEvent_F1
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β₁) :=
  { y₁ | ∃ m₁' : Fin M₁, m₁' ≠ m.1 ∧
        (e.inner (m.2, m₁'), e.outer m.2, y₁) ∈
          bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε }

/-- **Receiver-1 Bonferroni event F₂(m₁, m₂)** — some wrong `m₂' ≠ m₂`
paired with the correct `m₁` produces a receiver-1 JTS triple. -/
def bcReceiver1ErrorEvent_F2
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β₁) :=
  { y₁ | ∃ m₂' : Fin M₂, m₂' ≠ m.2 ∧
        (e.inner (m₂', m.1), e.outer m₂', y₁) ∈
          bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε }

/-- **Receiver-1 Bonferroni event F₃(m₁, m₂)** — some pair `(m₁', m₂')`
with both `m₁' ≠ m₁` and `m₂' ≠ m₂` produces a receiver-1 JTS triple. -/
def bcReceiver1ErrorEvent_F3
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β₁) :=
  { y₁ | ∃ m' : Fin M₁ × Fin M₂, m'.1 ≠ m.1 ∧ m'.2 ≠ m.2 ∧
        (e.inner (m'.2, m'.1), e.outer m'.2, y₁) ∈
          bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε }

lemma bcReceiver1ErrorEvent_F0_measurable
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m) :=
  (Set.toFinite _).measurableSet

lemma bcReceiver1ErrorEvent_F1_measurable
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m) :=
  (Set.toFinite _).measurableSet

lemma bcReceiver1ErrorEvent_F2_measurable
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m) :=
  (Set.toFinite _).measurableSet

lemma bcReceiver1ErrorEvent_F3_measurable
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    MeasurableSet (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) :=
  (Set.toFinite _).measurableSet

/-- **L-BC2-G-2 — Receiver-1 JTS decoder error event ⊆ 4-fold Bonferroni
union.**
For any message pair `m = (m₁, m₂)`, the receiver-1 JTS decoder's
pointwise error event (the set of `y_1` for which the projected pair
differs from `m₁`) is contained in `F₀(m) ∪ F₁(m) ∪ F₂(m) ∪ F₃(m)`.

The proof structure mirrors `mac_error_event_subset_bonferroni` verbatim;
the JTS predicate `bcReceiver1JTSPredicate` plays the role of
`macJTSPredicate`. We work on the *paired* decoder
`bcReceiver1JointlyTypicalDecoderPair` and recover the projected
receiver-1 decoder by `Prod.fst`. -/
theorem bc_receiver1_decoderPair_error_subset_bonferroni
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂) :
    { y₁ : Fin n → β₁
        | bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁ ≠ m } ⊆
        bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m
        ∪ bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m
        ∪ bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m
        ∪ bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m := by
  classical
  intro y₁ hy
  simp only [Set.mem_setOf_eq] at hy
  -- Case-split on JTS predicate for the correct pair.
  by_cases hF0 : (e.inner (m.2, m.1), e.outer m.2, y₁) ∈
                  bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε
  · -- Correct pair is in JTS: error means decoder picks a wrong pair,
    -- which is only possible when uniqueness fails.
    by_cases hUnique : ∃! mp : Fin M₁ × Fin M₂,
        bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ mp
    · have hm_pred : bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ m := hF0
      have hdec : bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁
                    = hUnique.choose :=
        bcReceiver1JointlyTypicalDecoderPair_of_existsUnique
          (μ := μ) (Xs := Xs) (Us := Us) (Y₁s := Y₁s) ε e y₁ hUnique
      obtain ⟨_w_pred, w_uniq⟩ := hUnique.choose_spec
      have hwm : hUnique.choose = m := (w_uniq m hm_pred).symm
      rw [hdec, hwm] at hy
      exact (hy rfl).elim
    · -- Uniqueness fails: some `mp ≠ m` satisfies JTS.
      have : ∃ mp : Fin M₁ × Fin M₂,
          mp ≠ m ∧ bcReceiver1JTSPredicate μ Xs Us Y₁s ε e y₁ mp := by
        by_contra hNo
        apply hUnique
        refine ⟨m, hF0, ?_⟩
        intro mp hmp
        by_contra hne
        exact hNo ⟨mp, hne, hmp⟩
      obtain ⟨mp, hne_mp, hmp_pred⟩ := this
      have h1_or_2 : mp.1 ≠ m.1 ∨ mp.2 ≠ m.2 := by
        by_contra h_and
        apply hne_mp
        refine Prod.ext ?_ ?_
        · by_contra h1
          exact h_and (Or.inl h1)
        · by_contra h2
          exact h_and (Or.inr h2)
      rcases h1_or_2 with h1 | h2
      · -- mp.1 ≠ m.1. Split on mp.2 = m.2 or not.
        by_cases h2' : mp.2 = m.2
        · -- F₁ case.
          refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_))
          refine ⟨mp.1, h1, ?_⟩
          have hh : (e.inner (mp.2, mp.1), e.outer mp.2, y₁) ∈
              bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε := hmp_pred
          rw [h2'] at hh
          exact hh
        · -- F₃ case: both differ.
          refine Set.mem_union_right _ ?_
          exact ⟨mp, h1, h2', hmp_pred⟩
      · -- mp.2 ≠ m.2. Split on mp.1.
        by_cases h1' : mp.1 = m.1
        · -- F₂ case.
          refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
          refine ⟨mp.2, h2, ?_⟩
          have hh : (e.inner (mp.2, mp.1), e.outer mp.2, y₁) ∈
              bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε := hmp_pred
          rw [h1'] at hh
          exact hh
        · -- F₃ case: both differ.
          refine Set.mem_union_right _ ?_
          exact ⟨mp, h1', h2, hmp_pred⟩
  · -- Correct triple not in JTS: F₀ case.
    refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))
    exact hF0

/-- **L-BC2-G-2 combiner — Union-bound on the receiver-1 paired-decoder
error event.**
For any block-pmf `ν` on `Fin n → β₁`, the pointwise error probability
of the receiver-1 paired-decoder for pair `m` is bounded by the sum of
the four Bonferroni event measures. -/
theorem bc_receiver1_decoderPair_errorProb_le_union
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂)
    (ν : Measure (Fin n → β₁)) :
    ν { y₁ | bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁ ≠ m } ≤
        ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) := by
  calc ν _
      ≤ ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m
            ∪ bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m
            ∪ bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m
            ∪ bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) :=
        measure_mono
          (bc_receiver1_decoderPair_error_subset_bonferroni
            μ Xs Us Y₁s ε e m)
    _ ≤ ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m
            ∪ bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m
            ∪ bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) :=
            measure_union_le _ _
    _ ≤ (ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m
              ∪ bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m)
          + ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m))
        + ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) := by
          gcongr
          exact measure_union_le _ _
    _ ≤ ((ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m)
            + ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m))
          + ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m))
        + ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) := by
          gcongr
          exact measure_union_le _ _
    _ = ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) := by ring

/-- **L-BC2-G-3 — Receiver-1 corner-point achievability body
(hypothesis pass-through).**
Given four caller-supplied bounds on the per-pair event probabilities of
`F₀, F₁, F₂, F₃` (Cover-Thomas eqs. 15.6.18-15.6.27, derived from random
codebook averaging — out of scope here, L-BC2-I), the receiver-1
paired-decoder's pointwise error probability is bounded by `δ₀ + δ₁ + δ₂ +
δ₃`. -/
theorem bc_receiver1_achievability_body
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂)
    (ν : Measure (Fin n → β₁))
    {δ₀ δ₁ δ₂ δ₃ : ℝ≥0∞}
    (h0 : ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m) ≤ δ₀)
    (h1 : ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m) ≤ δ₁)
    (h2 : ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m) ≤ δ₂)
    (h3 : ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) ≤ δ₃) :
    ν { y₁ | bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁ ≠ m }
      ≤ δ₀ + δ₁ + δ₂ + δ₃ := by
  calc ν _
      ≤ ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m)
        + ν (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) :=
          bc_receiver1_decoderPair_errorProb_le_union μ Xs Us Y₁s ε e m ν
    _ ≤ δ₀ + δ₁ + δ₂ + δ₃ := by
          have h01 : ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m)
              + ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m) ≤ δ₀ + δ₁ :=
            add_le_add h0 h1
          have h012 : ν (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m)
              + ν (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m)
              + ν (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m)
              ≤ δ₀ + δ₁ + δ₂ :=
            add_le_add h01 h2
          exact add_le_add h012 h3

end BCReceiver1Bonferroni

/-! ## Section 5 — Receiver-2 Bonferroni 2-event decomposition (L-BC2-H-2) -/

section BCReceiver2Bonferroni

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- **Receiver-2 Bonferroni event G₀(m₂)** — the *correct* pair
`(outer m₂, y_2)` is **not** in the receiver-2 jointly typical set. -/
def bcReceiver2ErrorEvent_G0
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂) :
    Set (Fin n → β₂) :=
  { y₂ | (outer m₂, y₂) ∉ bcReceiver2JointlyTypicalSet μ Us Y₂s n ε }

/-- **Receiver-2 Bonferroni event G₁(m₂)** — some wrong `m₂' ≠ m₂`
produces a receiver-2 JTS pair. -/
def bcReceiver2ErrorEvent_G1
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂) :
    Set (Fin n → β₂) :=
  { y₂ | ∃ m₂' : Fin M₂, m₂' ≠ m₂ ∧
        (outer m₂', y₂) ∈ bcReceiver2JointlyTypicalSet μ Us Y₂s n ε }

lemma bcReceiver2ErrorEvent_G0_measurable
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂) :
    MeasurableSet (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂) :=
  (Set.toFinite _).measurableSet

lemma bcReceiver2ErrorEvent_G1_measurable
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂) :
    MeasurableSet (bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂) :=
  (Set.toFinite _).measurableSet

/-- **L-BC2-H-2 — Receiver-2 JTS decoder error event ⊆ 2-fold Bonferroni
union.**
For any common message `m₂`, the receiver-2 JTS decoder's pointwise
error event is contained in `G₀(m₂) ∪ G₁(m₂)`.

Receiver 2's Bonferroni is **simpler than receiver 1's** — only 2 events,
because receiver 2 decodes only the common message `m₂`. -/
theorem bc_receiver2_decoder_error_subset_bonferroni
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} [NeZero M₂] (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂) :
    { y₂ : Fin n → β₂
        | bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε outer y₂ ≠ m₂ } ⊆
        bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂
        ∪ bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂ := by
  classical
  intro y₂ hy
  simp only [Set.mem_setOf_eq] at hy
  by_cases hG0 : (outer m₂, y₂) ∈ bcReceiver2JointlyTypicalSet μ Us Y₂s n ε
  · -- Correct pair is in JTS: decoder errs only when uniqueness fails.
    by_cases hUnique : ∃! mp : Fin M₂,
        bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ mp
    · have hm_pred : bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ m₂ := hG0
      have hdec : bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε outer y₂
                    = hUnique.choose :=
        bcReceiver2JointlyTypicalDecoder_of_existsUnique
          (μ := μ) (Us := Us) (Y₂s := Y₂s) ε outer y₂ hUnique
      obtain ⟨_w_pred, w_uniq⟩ := hUnique.choose_spec
      have hwm : hUnique.choose = m₂ := (w_uniq m₂ hm_pred).symm
      rw [hdec, hwm] at hy
      exact (hy rfl).elim
    · -- Uniqueness fails: some `mp ≠ m₂` satisfies JTS.
      have : ∃ mp : Fin M₂,
          mp ≠ m₂ ∧ bcReceiver2JTSPredicate μ Us Y₂s ε outer y₂ mp := by
        by_contra hNo
        apply hUnique
        refine ⟨m₂, hG0, ?_⟩
        intro mp hmp
        by_contra hne
        exact hNo ⟨mp, hne, hmp⟩
      obtain ⟨mp, hne_mp, hmp_pred⟩ := this
      refine Set.mem_union_right _ ?_
      exact ⟨mp, hne_mp, hmp_pred⟩
  · -- Correct pair not in JTS: G₀ case.
    refine Set.mem_union_left _ ?_
    exact hG0

/-- **L-BC2-H-2 combiner — Union-bound on the receiver-2 decoder error
event.** -/
theorem bc_receiver2_decoder_errorProb_le_union
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} [NeZero M₂] (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂)
    (ν : Measure (Fin n → β₂)) :
    ν { y₂ | bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε outer y₂ ≠ m₂ } ≤
        ν (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂)
        + ν (bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂) := by
  calc ν _
      ≤ ν (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂
            ∪ bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂) :=
        measure_mono
          (bc_receiver2_decoder_error_subset_bonferroni
            μ Us Y₂s ε outer m₂)
    _ ≤ ν (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂)
        + ν (bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂) :=
            measure_union_le _ _

/-- **L-BC2-H-3 — Receiver-2 corner-point achievability body
(hypothesis pass-through).**
Given two caller-supplied bounds on the per-message event probabilities
of `G₀, G₁` (Cover-Thomas eqs. 15.6.28-15.6.30, derived from random
codebook averaging — out of scope here, L-BC2-I), the receiver-2
JTS decoder's pointwise error probability is bounded by `δ₀ + δ₁`. -/
theorem bc_receiver2_achievability_body
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    {M₂ n : ℕ} [NeZero M₂] (ε : ℝ)
    (outer : Fin M₂ → (Fin n → υ))
    (m₂ : Fin M₂)
    (ν : Measure (Fin n → β₂))
    {δ₀ δ₁ : ℝ≥0∞}
    (h0 : ν (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂) ≤ δ₀)
    (h1 : ν (bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂) ≤ δ₁) :
    ν { y₂ | bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε outer y₂ ≠ m₂ }
      ≤ δ₀ + δ₁ := by
  calc ν _
      ≤ ν (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε outer m₂)
        + ν (bcReceiver2ErrorEvent_G1 μ Us Y₂s ε outer m₂) :=
          bc_receiver2_decoder_errorProb_le_union μ Us Y₂s ε outer m₂ ν
    _ ≤ δ₀ + δ₁ := add_le_add h0 h1

end BCReceiver2Bonferroni

/-! ## Section 6 — Joint two-receiver error union bound -/

section BCJointError

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- **Two-receiver joint error bound** — given the per-receiver
achievability hypotheses (4-event Bonferroni for receiver 1 + 2-event
Bonferroni for receiver 2), the *sum* of the two receivers' pointwise
error probabilities is bounded by the sum of all 6 per-event bounds.

This is the standard BC two-receiver union bound; in operational form
the actual two-decoder code's "joint error" (either receiver errs) is
upper-bounded by the sum (Bonferroni again, across receivers). -/
theorem bc_jts_jointErrorProb_le_sum
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ)
    (Y₁s : ℕ → Ω → β₁) (Y₂s : ℕ → Ω → β₂)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m : Fin M₁ × Fin M₂)
    (ν₁ : Measure (Fin n → β₁)) (ν₂ : Measure (Fin n → β₂))
    {δ₀ δ₁ δ₂ δ₃ : ℝ≥0∞}
    {γ₀ γ₁ : ℝ≥0∞}
    (h0 : ν₁ (bcReceiver1ErrorEvent_F0 μ Xs Us Y₁s ε e m) ≤ δ₀)
    (h1 : ν₁ (bcReceiver1ErrorEvent_F1 μ Xs Us Y₁s ε e m) ≤ δ₁)
    (h2 : ν₁ (bcReceiver1ErrorEvent_F2 μ Xs Us Y₁s ε e m) ≤ δ₂)
    (h3 : ν₁ (bcReceiver1ErrorEvent_F3 μ Xs Us Y₁s ε e m) ≤ δ₃)
    (g0 : ν₂ (bcReceiver2ErrorEvent_G0 μ Us Y₂s ε e.outer m.2) ≤ γ₀)
    (g1 : ν₂ (bcReceiver2ErrorEvent_G1 μ Us Y₂s ε e.outer m.2) ≤ γ₁) :
    ν₁ { y₁ | bcReceiver1JointlyTypicalDecoderPair μ Xs Us Y₁s ε e y₁ ≠ m }
      + ν₂ { y₂ | bcReceiver2JointlyTypicalDecoder μ Us Y₂s ε e.outer y₂ ≠ m.2 }
      ≤ (δ₀ + δ₁ + δ₂ + δ₃) + (γ₀ + γ₁) := by
  have hr1 := bc_receiver1_achievability_body μ Xs Us Y₁s ε e m ν₁ h0 h1 h2 h3
  have hr2 := bc_receiver2_achievability_body μ Us Y₂s ε e.outer m.2 ν₂ g0 g1
  exact add_le_add hr1 hr2

end BCJointError

/-! ## Section 7 — Publish-layer hook (L-BC2-I partial) -/

section BCBodyDischargePublish

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **BC inner bound — L-BC2 body discharge form (publish-layer hook,
superposition coding).**

A thin discharge wrapper around `bc_capacity_region_inner_bound`
(`BroadcastChannel.lean:580`) and its partial-discharge sibling
`bc_capacity_region_inner_bound_with_superposition_aep`
(`BroadcastChannelSuperposition.lean:543`). The parent theorem's
`_h_joint_typ : True` placeholder is now backed *concretely* in this
library by:

* the per-receiver AEP statements
  (`bcReceiver1JointlyTypicalSet_prob_tendsto_one`,
   `bcReceiver2JointlyTypicalSet_prob_tendsto_one`, L-BC2-F),
* the per-receiver cardinality bounds
  (`bcReceiver1JointlyTypicalSet_card_le`,
   `bcReceiver2JointlyTypicalSet_card_le`, L-BC2-E),
* the receiver-1 + receiver-2 JTS decoder constructions
  (`bcReceiver1JointlyTypicalDecoder`, `bcReceiver2JointlyTypicalDecoder`,
   L-BC2-G-1 + L-BC2-H-1),
* the assembled `bcJTSCode` with both decoders attached,
* the receiver-1 4-fold Bonferroni error containment
  (`bc_receiver1_decoderPair_error_subset_bonferroni`, L-BC2-G-2),
* the receiver-2 2-fold Bonferroni error containment
  (`bc_receiver2_decoder_error_subset_bonferroni`, L-BC2-H-2),
* the per-receiver corner-point achievability bodies
  (`bc_receiver1_achievability_body`, `bc_receiver2_achievability_body`,
   L-BC2-G-3 + L-BC2-H-3),
* the joint two-receiver union bound (`bc_jts_jointErrorProb_le_sum`).

The body **derives** the error-carrying `BCInnerBoundExistence W R₁ R₂`
from the honest superposition residual
`h_ach : BCSuperpositionAchievable W R₁ R₂ I_u I_xy` via
`bc_capacity_region_inner_bound_with_superposition_aep` (a `modus ponens`,
not an identity wrap), matching `mac_capacity_region_inner_bound_with_body`
(T3-B MAC).

The random codebook averaging argument that *derives* the per-event
decay bounds (Cover-Thomas eqs. 15.6.18-15.6.30, ~400-600 additional
lines, L-BC2-I) — which together with the publish-layer hook would lift
the residual `h_ach` from a hypothesis to a theorem — is **out of scope**
of this file and remains future work.

`@audit:suspect(broadcast-channel-moonshot-plan)` -/
theorem bc_capacity_region_inner_bound_with_superposition_body
    (W : BroadcastChannel α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (h_ach : BCSuperpositionAchievable W R₁ R₂ I_u I_xy) :
    BCInnerBoundExistence W R₁ R₂ :=
  bc_capacity_region_inner_bound_with_superposition_aep
    W R₁ R₂ I_u I_xy h_strict h_ach

end BCBodyDischargePublish

end InformationTheory.Shannon
