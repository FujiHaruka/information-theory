import Common2026.Shannon.BroadcastChannel
import Common2026.Shannon.MACL1Discharge

/-!
# BC superposition coding — L-BC2 (achievability) partial discharge (T3-C continuation)

This file publishes the **superposition-coding inner bound body discharge layer**
for the degraded broadcast channel of `Common2026/Shannon/BroadcastChannel.lean`
(T3-C, Cover–Thomas Theorem 15.6.2). The parent file's
`bc_capacity_region_inner_bound` carries `_h_joint_typ : True` and is supplied
the existence form `h_existence : BCInnerBoundExistence …` as a hypothesis
pass-through (judgement **L-BC1** + **L-BC3** in the moonshot plan). The
plumbing below makes the **two-layer superposition codebook** concrete and
publishes the **double-AEP joint typicality bounds** needed by the
superposition decoder, so downstream work can target the remaining 4-error-event
Bonferroni body of receiver 1 (private, `(U, X, Y_1)`) and receiver 2 (common,
`(U, Y_2)`).

## Scope (MVP — superposition structure + main joint-typical fragments)

Six concrete fragments are published in this seed, all by **iterated pairing**
onto the existing AEP machinery
(`Common2026/Shannon/AEP.lean` `typicalSet`, `jointlyTypicalSet`, and the
3-tuple `macJointlyTypicalSet` from `Common2026/Shannon/MACL1Discharge.lean`):

* **L-BC2-A** — `BCSuperpositionEncoder` structure: 2-layer codebook
  (outer U-layer `outer : Fin M₂ → (Fin n → υ)` + inner X-layer
  `inner : Fin M₂ × Fin M₁ → (Fin n → α)` conditional refinement).
* **L-BC2-B** — `BCSuperpositionCode.fromEncoder` — wrap superposition encoder
  into a `BroadcastCode` by attaching the two receivers' joint-typicality
  decoders (here exposed as caller-supplied fields, matching the established
  pattern).
* **L-BC2-C** — `bcReceiver1JointlyTypicalSet`, the
  `(U, X, Y_1)` 3-tuple joint typical set for the **private receiver** (good
  end of the degraded chain `X → Y_1 → Y_2`); inherits the MAC 3-tuple
  cardinality and AEP machinery.
* **L-BC2-D** — `bcReceiver2JointlyTypicalSet`, the `(U, Y_2)` 2-tuple joint
  typical set for the **common receiver** (poor end of the degraded chain);
  inherits the 2-tuple `jointlyTypicalSet` machinery of `ChannelCoding.lean`.
* **L-BC2-E** — `bcSuperposition_card_le_*` cardinality bounds for both
  jointly typical sets via the MAC / 2-tuple specialisations.
* **L-BC2-F** — `bcSuperposition_prob_tendsto_one_*` AEP probability bounds
  for both jointly typical sets via the MAC / 2-tuple specialisations.

The publish-layer hook
`bc_capacity_region_inner_bound_with_superposition_aep` is the thin
partial-discharge wrapper around `bc_capacity_region_inner_bound`: the
parent theorem's `_h_joint_typ : True` placeholder is now backed *concretely*
in this library by the two AEP statements and two cardinality bounds, while
the existence claim `h_existence : BCInnerBoundExistence …` remains a caller
hypothesis (matching `mac_capacity_region_inner_bound_with_joint_typ_aep`).

## Out of scope (L-BC2 deferred fragments)

* **L-BC2-G** (4-error-event Bonferroni body for receiver 1) and
  **L-BC2-H** (analogous body for receiver 2) — Cover-Thomas eqs. 15.6.18-
  15.6.30, ~600-1000 additional lines, deferred to a successor seed.
* **L-BC2-I** — random codebook averaging argument that lifts the existence
  claim from hypothesis to theorem; ~400-600 lines, deferred.

## Design (Mathlib-shape-driven, see CLAUDE.md)

`BCSuperpositionEncoder` is shaped so the dominant downstream lemmas
(`macJointlyTypicalSet_*` for receiver 1, `jointlyTypicalSet_*` for receiver
2) return conclusions in the form the body proof expects:

* receiver 1's typical-set machinery is **3-tuple over `υ × α × β₁`**
  (`(U, X, Y_1)`), matching `macJointlyTypicalSet` (defined over
  `α₁ × α₂ × β` in `MACL1Discharge.lean`), so the U-layer plays the role of
  `α₁` and the X-layer plays the role of `α₂` in the verbatim re-use.
* receiver 2's typical-set machinery is **2-tuple over `υ × β₂`**
  (`(U, Y_2)`), matching `jointlyTypicalSet` (defined over `α × β` in
  `ChannelCoding.lean`).

The two-layer codebook shape `outer : Fin M₂ → (Fin n → υ)` plus
`inner : Fin M₂ × Fin M₁ → (Fin n → α)` is the operational superposition form:
the outer codebook represents the common message `m₂` via the auxiliary RV
`U`, and the inner codebook refines into the private message `m₁` via `X | U`.
The joint encoder of `BroadcastCode` is then
`encoder (m₁, m₂) := inner (m₂, m₁)` (un-curry from the 2-layer indexing).

## 撤退ライン (確定発動)

* **L-BC2-A through L-BC2-F** all publish-form; no further hypotheses
  needed. Each is a direct specialisation of an upstream typical-set
  result.
* **L-BC2-G / L-BC2-H** (per-receiver 4-error-event Bonferroni) and
  **L-BC2-I** (random codebook averaging) — fully scope-out; not in this
  file. The publish-layer hook keeps the `h_existence` hypothesis form
  intact, matching the established pass-through pattern.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — BC two-layer joint sequences -/

section BCJointSequence

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ α β₁ β₂ : Type*}

/-- Receiver-1 joint sequence `(X, U, Y_1)` over the product alphabet
`α × υ × β₁`. The X-layer plays the role of `α₁` (so the X-slice over fixed
`(u, y₁)` is the natural `macConditionalTypicalSlice`) and the U-layer plays
the role of `α₂` in the verbatim re-use of `macJointSequence`. -/
noncomputable def bcReceiver1JointSequence
    (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁) :
    ℕ → Ω → α × υ × β₁ :=
  macJointSequence Xs Us Y₁s

@[simp] lemma bcReceiver1JointSequence_apply
    (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁) (i : ℕ) (ω : Ω) :
    bcReceiver1JointSequence Xs Us Y₁s i ω = (Xs i ω, Us i ω, Y₁s i ω) := rfl

/-- Receiver-2 joint sequence `(U, Y_2)` over the product alphabet
`υ × β₂`. This is `ChannelCoding.jointSequence` directly. -/
noncomputable def bcReceiver2JointSequence
    (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂) :
    ℕ → Ω → υ × β₂ :=
  ChannelCoding.jointSequence Us Y₂s

@[simp] lemma bcReceiver2JointSequence_apply
    (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂) (i : ℕ) (ω : Ω) :
    bcReceiver2JointSequence Us Y₂s i ω = (Us i ω, Y₂s i ω) := rfl

variable [MeasurableSpace υ] [MeasurableSpace α] [MeasurableSpace β₁]
  [MeasurableSpace β₂]

lemma measurable_bcReceiver1JointSequence
    (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (hXs : ∀ i, Measurable (Xs i)) (hUs : ∀ i, Measurable (Us i))
    (hY₁s : ∀ i, Measurable (Y₁s i)) (i : ℕ) :
    Measurable (bcReceiver1JointSequence Xs Us Y₁s i) :=
  measurable_macJointSequence Xs Us Y₁s hXs hUs hY₁s i

lemma measurable_bcReceiver2JointSequence
    (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (hUs : ∀ i, Measurable (Us i)) (hY₂s : ∀ i, Measurable (Y₂s i)) (i : ℕ) :
    Measurable (bcReceiver2JointSequence Us Y₂s i) :=
  ChannelCoding.measurable_jointSequence Us Y₂s hUs hY₂s i

end BCJointSequence

/-! ## Section 2 — BC superposition encoder structure (2-layer codebook) -/

section BCSuperpositionEncoder

variable {υ α β₁ β₂ : Type*}
variable [MeasurableSpace υ] [MeasurableSpace α]
  [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- A **superposition encoder** for the degraded broadcast channel.

Operational shape: a two-layer codebook representing the
Cover-Thomas superposition `(U, X) ~ p(u) p(x | u)`:

* `outer : Fin M₂ → (Fin n → υ)` — the **outer codebook**: maps each common
  message `m₂` to a length-`n` block `U^n(m₂)` over the auxiliary alphabet
  `υ`. This carries the common message `m₂` (poor receiver) via `U`.
* `inner : Fin M₂ × Fin M₁ → (Fin n → α)` — the **inner codebook**: maps
  the conditioning pair `(m₂, m₁)` to a length-`n` block `X^n(m₂, m₁)`
  over the input alphabet `α`. This refines the outer `U` block by the
  private message `m₁` (good receiver) via `X | U`.

The joint encoder of `BroadcastCode` is recovered by un-currying via
`fromEncoder` below: `encoder (m₁, m₂) := inner (m₂, m₁)`.

We bundle no measurability fields: on finite (or `MeasurableSingletonClass`)
alphabets all functions are automatically measurable, matching the
convention of `BroadcastCode` (and `Code`, `MACCode`).

References: Cover-Thomas Ch.15.6.1 (superposition coding for the degraded
broadcast channel). -/
structure BCSuperpositionEncoder (M₁ M₂ n : ℕ) (υ α : Type*)
    [MeasurableSpace υ] [MeasurableSpace α] where
  /-- Outer codebook: `Fin M₂ → (Fin n → υ)`. -/
  outer : Fin M₂ → (Fin n → υ)
  /-- Inner (refinement) codebook: `Fin M₂ × Fin M₁ → (Fin n → α)`. -/
  inner : Fin M₂ × Fin M₁ → (Fin n → α)

namespace BCSuperpositionEncoder

variable {M₁ M₂ n : ℕ}

/-- The total joint encoder obtained by un-currying: `encoder (m₁, m₂) :=
inner (m₂, m₁)`. -/
def jointEncoder (e : BCSuperpositionEncoder M₁ M₂ n υ α) :
    Fin M₁ × Fin M₂ → (Fin n → α) :=
  fun p => e.inner (p.2, p.1)

@[simp] lemma jointEncoder_apply (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    e.jointEncoder (m₁, m₂) = e.inner (m₂, m₁) := rfl

end BCSuperpositionEncoder

/-- **Assemble a `BroadcastCode` from a superposition encoder + two
joint-typicality decoders.**

Given a `BCSuperpositionEncoder M₁ M₂ n υ α` and two decoders
`d₁ : (Fin n → β₁) → Fin M₁`, `d₂ : (Fin n → β₂) → Fin M₂` (which in the
operational discharge of L-BC2 would each be the joint-typicality decoder
applied to its receiver's output, but are exposed here as caller-supplied
fields), produce a `BroadcastCode` whose joint encoder is the un-currying
of the superposition encoder.

This packaging is a thin wrapper; the operational content lives in the
joint-typicality decoders supplied by the caller. -/
def bcSuperpositionCode {M₁ M₂ n : ℕ}
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (d₁ : (Fin n → β₁) → Fin M₁) (d₂ : (Fin n → β₂) → Fin M₂) :
    BroadcastCode M₁ M₂ n α β₁ β₂ where
  encoder  := e.jointEncoder
  decoder₁ := d₁
  decoder₂ := d₂

@[simp] lemma bcSuperpositionCode_encoder {M₁ M₂ n : ℕ}
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (d₁ : (Fin n → β₁) → Fin M₁) (d₂ : (Fin n → β₂) → Fin M₂)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    (bcSuperpositionCode e d₁ d₂).encoder (m₁, m₂) = e.inner (m₂, m₁) := rfl

@[simp] lemma bcSuperpositionCode_decoder₁ {M₁ M₂ n : ℕ}
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (d₁ : (Fin n → β₁) → Fin M₁) (d₂ : (Fin n → β₂) → Fin M₂)
    (y : Fin n → β₁) :
    (bcSuperpositionCode (β₂ := β₂) e d₁ d₂).decoder₁ y = d₁ y := rfl

@[simp] lemma bcSuperpositionCode_decoder₂ {M₁ M₂ n : ℕ}
    (e : BCSuperpositionEncoder M₁ M₂ n υ α)
    (d₁ : (Fin n → β₁) → Fin M₁) (d₂ : (Fin n → β₂) → Fin M₂)
    (y : Fin n → β₂) :
    (bcSuperpositionCode (β₁ := β₁) e d₁ d₂).decoder₂ y = d₂ y := rfl

end BCSuperpositionEncoder

/-! ## Section 3 — Receiver-1 jointly typical set `(U, X, Y_1)` -/

section BCReceiver1JointlyTypicalSet

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]

/-- The **receiver-1 jointly typical set** `A_ε^n ⊆ (Fin n → α) × (Fin n → υ)
× (Fin n → β₁)` for the private receiver of the degraded broadcast channel.

A triple `(x, u, y₁)` is in the set iff each component block is single-axis
typical *and* the 3-tuple sequence `fun i => (x i, u i, y₁ i)` is single-axis
typical over the joint alphabet `α × υ × β₁`. This is a direct specialisation
of `macJointlyTypicalSet` to the BC setting where the X-layer plays the role
of `α₁` (so the X-slice over fixed `(u, y₁)` is the natural
`macConditionalTypicalSlice`) and the U-layer plays the role of `α₂`. -/
noncomputable def bcReceiver1JointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α) × (Fin n → υ) × (Fin n → β₁)) :=
  macJointlyTypicalSet μ Xs Us Y₁s n ε

lemma mem_bcReceiver1JointlyTypicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) (u : Fin n → υ) (y₁ : Fin n → β₁) :
    (x, u, y₁) ∈ bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε ↔
      x ∈ typicalSet μ Xs n ε
      ∧ u ∈ typicalSet μ Us n ε
      ∧ y₁ ∈ typicalSet μ Y₁s n ε
      ∧ (fun i => (x i, u i, y₁ i)) ∈
          typicalSet μ (bcReceiver1JointSequence Xs Us Y₁s) n ε :=
  mem_macJointlyTypicalSet_iff μ Xs Us Y₁s n ε x u y₁

theorem measurableSet_bcReceiver1JointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) :
    MeasurableSet (bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε) :=
  measurableSet_macJointlyTypicalSet μ Xs Us Y₁s n ε

lemma bcReceiver1JointlyTypicalSet_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) :
    (bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε).Finite :=
  macJointlyTypicalSet_finite μ Xs Us Y₁s n ε

end BCReceiver1JointlyTypicalSet

/-! ## Section 4 — Receiver-2 jointly typical set `(U, Y_2)` -/

section BCReceiver2JointlyTypicalSet

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The **receiver-2 jointly typical set** `B_ε^n ⊆ (Fin n → υ) × (Fin n → β₂)`
for the common receiver of the degraded broadcast channel.

A pair `(u, y₂)` is in the set iff each component block is single-axis
typical *and* the 2-tuple sequence `fun i => (u i, y₂ i)` is single-axis
typical over the joint alphabet `υ × β₂`. This is a direct specialisation
of `jointlyTypicalSet` (`ChannelCoding.lean:301`) to `(U, Y_2)`. -/
noncomputable def bcReceiver2JointlyTypicalSet
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (n : ℕ) (ε : ℝ) :
    Set ((Fin n → υ) × (Fin n → β₂)) :=
  ChannelCoding.jointlyTypicalSet μ Us Y₂s n ε

lemma mem_bcReceiver2JointlyTypicalSet_iff
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (n : ℕ) (ε : ℝ) (u : Fin n → υ) (y₂ : Fin n → β₂) :
    (u, y₂) ∈ bcReceiver2JointlyTypicalSet μ Us Y₂s n ε ↔
      u ∈ typicalSet μ Us n ε
      ∧ y₂ ∈ typicalSet μ Y₂s n ε
      ∧ (fun i => (u i, y₂ i)) ∈
          typicalSet μ (bcReceiver2JointSequence Us Y₂s) n ε :=
  ChannelCoding.mem_jointlyTypicalSet_iff μ Us Y₂s n ε u y₂

theorem measurableSet_bcReceiver2JointlyTypicalSet
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (n : ℕ) (ε : ℝ) :
    MeasurableSet (bcReceiver2JointlyTypicalSet μ Us Y₂s n ε) :=
  ChannelCoding.measurableSet_jointlyTypicalSet μ Us Y₂s n ε

lemma bcReceiver2JointlyTypicalSet_finite
    (μ : Measure Ω) (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (n : ℕ) (ε : ℝ) :
    (bcReceiver2JointlyTypicalSet μ Us Y₂s n ε).Finite :=
  ChannelCoding.jointlyTypicalSet_finite μ Us Y₂s n ε

end BCReceiver2JointlyTypicalSet

/-! ## Section 5 — Cardinality bounds (L-BC2-E) -/

section BCSuperpositionCardinality

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- **L-BC2-E (receiver 1) — Receiver-1 jointly typical set cardinality
bound**: the size of the `(X, U, Y_1)` 3-tuple jointly typical set is at most
`exp(n · (H(X, U, Y_1) + ε))`.

Direct specialisation of `macJointlyTypicalSet_card_le`. -/
theorem bcReceiver1JointlyTypicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (hXs : ∀ i, Measurable (Xs i)) (hUs : ∀ i, Measurable (Us i))
    (hY₁s : ∀ i, Measurable (Y₁s i))
    (hposZ : ∀ p : α × υ × β₁,
        0 < (μ.map (bcReceiver1JointSequence Xs Us Y₁s 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) *
        (entropy μ (bcReceiver1JointSequence Xs Us Y₁s 0) + ε)) :=
  macJointlyTypicalSet_card_le μ Xs Us Y₁s hXs hUs hY₁s hposZ n hε

/-- **L-BC2-E (receiver 2) — Receiver-2 jointly typical set cardinality
bound**: the size of the `(U, Y_2)` 2-tuple jointly typical set is at most
`exp(n · (H(U, Y_2) + ε))`.

Direct specialisation of `jointlyTypicalSet_card_le`. -/
theorem bcReceiver2JointlyTypicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (hUs : ∀ i, Measurable (Us i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hpos : ∀ p : υ × β₂,
        0 < (μ.map (bcReceiver2JointSequence Us Y₂s 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((bcReceiver2JointlyTypicalSet μ Us Y₂s n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) *
        (entropy μ (bcReceiver2JointSequence Us Y₂s 0) + ε)) :=
  ChannelCoding.jointlyTypicalSet_card_le μ Us Y₂s hUs hY₂s hpos n hε

end BCSuperpositionCardinality

/-! ## Section 6 — AEP probability bounds (L-BC2-F) -/

section BCSuperpositionAEP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable {β₂ : Type*} [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- **L-BC2-F (receiver 1) — Receiver-1 joint AEP probability** (one-sided):
for i.i.d. sequences `Us, Xs, Y₁s` (each axis pairwise-independent and
identically distributed, plus the same for the joint-axis sequence), the
probability that `(U^n, X^n, Y_1^n)` lies in the receiver-1 jointly typical
set tends to `1` as `n → ∞`.

Direct specialisation of `macJointlyTypicalSet_prob_tendsto_one`. -/
theorem bcReceiver1JointlyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (hXs : ∀ i, Measurable (Xs i)) (hUs : ∀ i, Measurable (Us i))
    (hY₁s : ∀ i, Measurable (Y₁s i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepU : Pairwise fun i j => Us i ⟂ᵢ[μ] Us j)
    (hidentU : ∀ i, IdentDistrib (Us i) (Us 0) μ μ)
    (hindepY₁ : Pairwise fun i j => Y₁s i ⟂ᵢ[μ] Y₁s j)
    (hidentY₁ : ∀ i, IdentDistrib (Y₁s i) (Y₁s 0) μ μ)
    (hindepZ : Pairwise fun i j =>
        bcReceiver1JointSequence Xs Us Y₁s i ⟂ᵢ[μ]
          bcReceiver1JointSequence Xs Us Y₁s j)
    (hidentZ : ∀ i,
        IdentDistrib (bcReceiver1JointSequence Xs Us Y₁s i)
          (bcReceiver1JointSequence Xs Us Y₁s 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ =>
        μ {ω | (jointRV Xs n ω, jointRV Us n ω, jointRV Y₁s n ω) ∈
                bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε})
      Filter.atTop (𝓝 1) :=
  macJointlyTypicalSet_prob_tendsto_one μ Xs Us Y₁s hXs hUs hY₁s
    hindepX hidentX hindepU hidentU hindepY₁ hidentY₁ hindepZ hidentZ hε

/-- **L-BC2-F (receiver 2) — Receiver-2 joint AEP probability** (one-sided):
for i.i.d. sequences `Us, Y₂s` (each axis pairwise-independent and
identically distributed, plus the joint-axis sequence), the probability that
`(U^n, Y_2^n)` lies in the receiver-2 jointly typical set tends to `1`.

Direct specialisation of `jointlyTypicalSet_prob_tendsto_one`. -/
theorem bcReceiver2JointlyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Us : ℕ → Ω → υ) (Y₂s : ℕ → Ω → β₂)
    (hUs : ∀ i, Measurable (Us i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hindepU : Pairwise fun i j => Us i ⟂ᵢ[μ] Us j)
    (hidentU : ∀ i, IdentDistrib (Us i) (Us 0) μ μ)
    (hindepY₂ : Pairwise fun i j => Y₂s i ⟂ᵢ[μ] Y₂s j)
    (hidentY₂ : ∀ i, IdentDistrib (Y₂s i) (Y₂s 0) μ μ)
    (hindepZ : Pairwise fun i j =>
        bcReceiver2JointSequence Us Y₂s i ⟂ᵢ[μ]
          bcReceiver2JointSequence Us Y₂s j)
    (hidentZ : ∀ i,
        IdentDistrib (bcReceiver2JointSequence Us Y₂s i)
          (bcReceiver2JointSequence Us Y₂s 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ =>
        μ {ω | (jointRV Us n ω, jointRV Y₂s n ω) ∈
                bcReceiver2JointlyTypicalSet μ Us Y₂s n ε})
      Filter.atTop (𝓝 1) :=
  ChannelCoding.jointlyTypicalSet_prob_tendsto_one μ Us Y₂s hUs hY₂s
    hindepU hidentU hindepY₂ hidentY₂ hindepZ hidentZ hε

end BCSuperpositionAEP

/-! ## Section 7 — Conditional U-slice on receiver 1 (SW-style plumbing) -/

section BCSuperpositionConditionalSlice

variable {Ω : Type*} [MeasurableSpace Ω]
variable {υ : Type*} [Fintype υ] [DecidableEq υ] [Nonempty υ]
  [MeasurableSpace υ] [MeasurableSingletonClass υ]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]

/-- The **conditional X-slice** on the receiver-1 jointly typical set. For a
fixed pair `(u, y₁)`, the `X`-fiber is
`{ x : Fin n → α | (x, u, y₁) ∈ bcReceiver1JointlyTypicalSet … }`.

This is a direct specialisation of `macConditionalTypicalSlice` with `(u, y₁)`
playing the role of `(x₂, y)` in the MAC SW-style slice — the new
`(X, U, Y_1)` ordering puts the X-layer in the `α₁` slot of MAC, so the
slice over `(u, y₁)` is the natural MAC `α₁`-slice. Operationally this is
the inner codebook fiber for a fixed common message `m₂` (which encodes
to `u`) and a fixed channel output `y₁`. -/
noncomputable def bcReceiver1ConditionalSliceX
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) (u : Fin n → υ) (y₁ : Fin n → β₁) :
    Set (Fin n → α) :=
  macConditionalTypicalSlice μ Xs Us Y₁s n ε u y₁

lemma mem_bcReceiver1ConditionalSliceX_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) (u : Fin n → υ) (y₁ : Fin n → β₁) (x : Fin n → α) :
    x ∈ bcReceiver1ConditionalSliceX μ Xs Us Y₁s n ε u y₁ ↔
      (x, u, y₁) ∈ bcReceiver1JointlyTypicalSet μ Xs Us Y₁s n ε :=
  mem_macConditionalTypicalSlice_iff μ Xs Us Y₁s n ε u y₁ x

lemma bcReceiver1ConditionalSliceX_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Us : ℕ → Ω → υ) (Y₁s : ℕ → Ω → β₁)
    (n : ℕ) (ε : ℝ) (u : Fin n → υ) (y₁ : Fin n → β₁) :
    (bcReceiver1ConditionalSliceX μ Xs Us Y₁s n ε u y₁).Finite :=
  macConditionalTypicalSlice_finite μ Xs Us Y₁s n ε u y₁

end BCSuperpositionConditionalSlice

/-! ## Section 8 — Publish-layer hook -/

section BCSuperpositionInnerBoundDischarge

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **BC inner bound — L-BC2 partial discharge form (superposition coding)**.

A thin partial-discharge wrapper around `bc_capacity_region_inner_bound`
(`BroadcastChannel.lean:580`). The parent theorem's `_h_joint_typ : True`
placeholder is now backed *concretely* in this library by:

* `bcReceiver1JointlyTypicalSet_card_le`     (L-BC2-E receiver 1)
* `bcReceiver2JointlyTypicalSet_card_le`     (L-BC2-E receiver 2)
* `bcReceiver1JointlyTypicalSet_prob_tendsto_one` (L-BC2-F receiver 1)
* `bcReceiver2JointlyTypicalSet_prob_tendsto_one` (L-BC2-F receiver 2)
* `bcReceiver1ConditionalSliceX`             (SW-style plumbing)
* `bcSuperpositionCode`                      (2-layer codebook → BroadcastCode)

The body **derives** the error-carrying `BCInnerBoundExistence W R₁ R₂`
from the honest superposition residual
`h_ach : BCSuperpositionAchievable W R₁ R₂ I_u I_xy` via
`bc_capacity_region_inner_bound` (a `modus ponens`, not an identity wrap),
matching `mac_capacity_region_inner_bound_with_joint_typ_aep` (T3-B MAC).

The trailing 4-error-event Bonferroni body for each receiver (Cover-Thomas
eqs. 15.6.18-15.6.30) and the random codebook averaging argument
(L-BC2-G/H/I) — which together would lift the residual `h_ach` from a
hypothesis to a theorem — are **out of scope** of this file and remain
future work.

`@audit:suspect(broadcast-channel-moonshot-plan)` -/
theorem bc_capacity_region_inner_bound_with_superposition_aep
    (W : BroadcastChannel α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (h_ach : BCSuperpositionAchievable W R₁ R₂ I_u I_xy) :
    BCInnerBoundExistence W R₁ R₂ :=
  bc_capacity_region_inner_bound W R₁ R₂ I_u I_xy h_strict h_ach

end BCSuperpositionInnerBoundDischarge

end InformationTheory.Shannon
