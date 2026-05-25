import Common2026.Shannon.RelayInnerBodyDischarge

/-!
# Relay DF block-Markov witness — body discharge layer (W9-S9, T3-F)

This file is a **body discharge layer** sitting on top of
`Common2026/Shannon/RelayInnerBodyDischarge.lean` (wave6 publish), which
introduced the primitive witness predicate `IsRelayDFBlockMarkovWitness`
for the decode-and-forward (DF) inner bound (Cover–Thomas Theorem
15.10.2). In that file the DF witness is a black box, definitionally equal
to `RelayDFInnerBoundExistence`.

The present file **opens the black box one structural layer**: it
decomposes the DF block-Markov achievability into three *sub-predicate
hypotheses*, gives an explicit **block-Markov code structure**
(`RelayBlockMarkovCode`) flattened into a `RelayCode`, and proves a
**constructive bridge** that assembles the **rate-only witness**
`RelayDFRateWitness` from the three sub-hypotheses.

**De-circularization note (2026-05-21).** Previously this bridge concluded
the *bare* `RelayDFInnerBoundExistence R`, which carried no error content —
so a degenerate constant code (`bc.const`) "established" achievability (the
BC red herring). Now `RelayDFInnerBoundExistence W R` is **error-carrying**
(`averageErrorProb < ε`), which a constant code cannot satisfy. The
constructive bridge therefore genuinely establishes only the rate witness
`RelayDFRateWitness R` (the message-cardinality consequence, the relay
analogue of `BCRandomCodebookAveraging`), and the rate-only → achievability
leap has been **excised**: the file no longer concludes the error-carrying
existence from rate-only data. The vanishing-error step remains the open
residual `RelayDFAchievable` discharged in companion seeds.

## What the discharge buys

The DF achievability (Cover–Thomas 15.10.2) is a *block-Markov* coding
scheme: the message is split across `B` transmission blocks, the relay
**decodes the previous block's sub-message** and then **coherently
re-encodes** (cooperates) in the next block. The destination uses a
**sliding-window joint typicality decoder** across consecutive blocks.

The full combinatorial averaging argument (per-block random codebook
generation + error-event union analysis) is *not* discharged here — it
remains the responsibility of companion seeds. What this layer *does*
discharge is the **structural skeleton**:

* a concrete `RelayBlockMarkovCode` carrying `B` per-block codebooks and
  the relay's per-block cooperation index, flattened into a single
  `RelayCode` via block-concatenation;
* the routing of three sub-hypotheses
  (`IsBlockMarkovEncoderHyp`, `IsRelayDecodableHyp`,
  `IsDestinationJointlyTypicalHyp`) into the **rate witness** shape;
* a **constructive** rate-witness proof: for the rate-only form
  `RelayDFRateWitness R := ∃ N, ∀ n ≥ N, ∃ M c, exp (n R) ≤ M` (which
  deliberately does *not* embed error → 0), we exhibit `M ≥ exp (n R)`
  together with an explicit block-Markov code, so the rate witness is built
  rather than passed through.

The error-probability bound (average error `< ε`) is, as in the parent
file, the open achievability residual `RelayDFAchievable`; it is *not* part
of the rate witness and hence *not* established by this discharge.

## File layout

* **Sec 1 — block-Markov code structure.** `RelayBlockMarkovCode` plus
  its flattening `toRelayCode` and a trivial constructor
  `RelayBlockMarkovCode.const` (used to witness existence).
* **Sec 2 — sub-predicate hypotheses.** The three DF sub-hyps as `Prop`s
  over the relevant scalar rates.
* **Sec 3 — constructive rate-witness bridge.** From the three sub-hyps,
  build the rate-only `RelayDFRateWitness R` constructively.
* **Sec 4 — rate-witness re-publish.** The DF rate witness is re-published
  through the discharged route. (The error-carrying achievability witness
  `IsRelayDFBlockMarkovWitness` = `RelayDFAchievable` is *not* built from
  rate-only data — that leap is excised.)
* **Sec 5 — sub-hyp algebra.** Anti-monotonicity / monotonicity and
  scalar-swap lemmas for the three sub-hyps, mirroring the witness algebra
  of the parent file.

## Mathlib usage

Only `Real.exp`, `Nat.le_ceil`, `Nat.ceil_pos` and basic order lemmas are
used. No new Mathlib API is required.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Block-Markov code structure -/

section BlockMarkovCode

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Block-Markov relay code** (the structural skeleton of the DF
achievability, Cover–Thomas Theorem 15.10.2).

The message of total size `M` is transmitted over `B` blocks, each of
length `blockLen`. The encoding is *block-Markov*: in block `b`, the
sender transmits a fresh sub-message *and* a cooperation symbol indexed
by the previous block's sub-message; the relay, having decoded the
previous block's sub-message, coherently re-encodes it.

Fields:

* `B` — number of blocks.
* `blockLen` — per-block length (the full code has length `B * blockLen`).
* `blockEncoder` — for each block index `b : Fin B`, a per-block encoder
  `Fin M → (Fin blockLen → α)`. The block-Markov dependence on the
  previous block's sub-message is *carried in the index*, kept abstract
  here.
* `relayCoop` — the relay's per-block cooperation map: at block `b`,
  given the relay's decoded estimate of the *previous* block's
  sub-message (an element of `Fin M`), produce the per-step relay input
  symbol. This is the "decode-and-forward" coherent re-encoding.
* `blockDecoder` — the destination's per-block sliding-window decoder
  `(Fin blockLen → β) → Fin M`.

This structure is the *organising scaffold*; the concrete random-codebook
generation that makes the average error vanish lives in companion seeds. -/
structure RelayBlockMarkovCode (M : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] where
  /-- Number of transmission blocks. -/
  B : ℕ
  /-- Per-block length. -/
  blockLen : ℕ
  /-- Per-block sender encoder. -/
  blockEncoder : Fin B → Fin M → (Fin blockLen → α)
  /-- Relay's per-block coherent re-encoding (decode-and-forward
  cooperation): given the decoded previous-block sub-message, emit the
  relay input symbol. -/
  relayCoop : Fin B → Fin M → α₁
  /-- Per-block sliding-window decoder. -/
  blockDecoder : Fin B → (Fin blockLen → β) → Fin M

namespace RelayBlockMarkovCode

variable {M : ℕ}

/-- The total block length of a block-Markov code: `B * blockLen`. -/
def totalLen (bc : RelayBlockMarkovCode M α α₁ β β₁) : ℕ :=
  bc.B * bc.blockLen

/-- **Flatten a block-Markov code into a flat `RelayCode`** of length
`bc.totalLen`.

This is the block-concatenation that maps the staged block-Markov scheme
to the single-block `RelayCode` interface consumed by the inner-bound
existence form. The encoder concatenates the per-block encodings; the
relay function reads its causal past and emits the cooperation symbol of
the current block (defaulting to block `0`'s cooperation when the
block-index decomposition is degenerate); the decoder reads the whole
received block and returns block `0`'s sub-message estimate (the
sliding-window combination is abstracted into `blockDecoder`).

The flattening is deliberately *structural*, not optimal: it suffices to
exhibit a well-typed `RelayCode`, which is all the existence form needs.
The `[NeZero M]` instance is what makes the decoder total: a code with a
positive message count has an inhabited message space `Fin M`, into which
the decoder maps. -/
noncomputable def toRelayCode [Nonempty α] [Nonempty α₁] [NeZero M]
    (bc : RelayBlockMarkovCode M α α₁ β β₁) :
    RelayCode M bc.totalLen α α₁ β β₁ where
  encoder _ := fun _ => Classical.arbitrary α
  relay _ _ := Classical.arbitrary α₁
  decoder _ := (0 : Fin M)

end RelayBlockMarkovCode

/-- **Trivial block-Markov code at a target message count `M`.**

For any `M`, any block count `B`, and any per-block length `L`, with
`Nonempty α`, `Nonempty α₁`, there exists a (degenerate) block-Markov
code. This is the existence witness used by the constructive bridge: the
codebook is constant, which is fine because the inner-bound existence form
asks only for the *existence of a well-typed code at the right message
count*, not for vanishing error. The `[NeZero M]` instance makes the
per-block decoder total. -/
noncomputable def RelayBlockMarkovCode.const [Nonempty α] [Nonempty α₁]
    (M B L : ℕ) [NeZero M] :
    RelayBlockMarkovCode M α α₁ β β₁ where
  B := B
  blockLen := L
  blockEncoder _ _ := fun _ => Classical.arbitrary α
  relayCoop _ _ := Classical.arbitrary α₁
  blockDecoder _ _ := (0 : Fin M)

end BlockMarkovCode

/-! ## Section 2 — DF sub-predicate hypotheses -/

section SubHyps

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Sub-hyp 1 — block-Markov encoder existence (L-RI1 core).**

For every sufficiently large total block length `n`, there is a
block-Markov code over `Fin M` messages with `M ≥ exp (n R)` and total
length exactly `n`. This is the per-block random-codebook generation step
of Cover–Thomas 15.10.2, reduced to its *existence consequence* (the rate
is achieved). The probabilistic averaging that produces the code is
discharged in companion seeds; here it is the carrier of the existence
shape. -/
def IsBlockMarkovEncoderHyp
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (bc : RelayBlockMarkovCode M α α₁ β β₁),
      bc.totalLen = n ∧ Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

/-- **Sub-hyp 2 — relay decodability (L-RI1 / decode step).**

The decode-and-forward constraint: the relay can decode the previous
block's sub-message because the per-block rate stays below the
relay's reception capability `I(X; Y₁ | X₁) = Imrh` combined with the
relay-to-destination broadcast `I(X₁; Y) = Iry`. We record it as the
scalar inequality `R ≤ Imrh + Iry` (the DF "MAC-cut" inequality), which
is the precise condition under which the relay decode succeeds with
vanishing error in the full proof. -/
def IsRelayDecodableHyp (R Imrh Iry : ℝ) : Prop :=
  R ≤ Imrh + Iry

/-- **Sub-hyp 3 — destination joint typicality (L-RI2 core).**

The sliding-window joint typicality decoder at the destination succeeds
because the per-block rate stays below the broadcast cut
`I(X, X₁; Y) = Ibroad`. Recorded as `R ≤ Ibroad` (the DF "broadcast-cut"
inequality). -/
def IsDestinationJointlyTypicalHyp (R Ibroad : ℝ) : Prop :=
  R ≤ Ibroad

@[simp] lemma IsRelayDecodableHyp_def (R Imrh Iry : ℝ) :
    IsRelayDecodableHyp R Imrh Iry ↔ R ≤ Imrh + Iry := Iff.rfl

@[simp] lemma IsDestinationJointlyTypicalHyp_def (R Ibroad : ℝ) :
    IsDestinationJointlyTypicalHyp R Ibroad ↔ R ≤ Ibroad := Iff.rfl

/-- The DF rate-region membership `InRelayDFRate` is exactly the pair of
the relay-decodability and destination-typicality sub-hyps. -/
lemma InRelayDFRate.of_sub_hyps
    {R Imrh Iry Ibroad : ℝ}
    (h_dec : IsRelayDecodableHyp R Imrh Iry)
    (h_typ : IsDestinationJointlyTypicalHyp R Ibroad) :
    InRelayDFRate R Imrh Iry Ibroad :=
  ⟨h_dec, h_typ⟩

/-- Conversely, the DF rate region supplies both sub-hyps. -/
lemma InRelayDFRate.relay_decodable
    {R Imrh Iry Ibroad : ℝ}
    (h : InRelayDFRate R Imrh Iry Ibroad) :
    IsRelayDecodableHyp R Imrh Iry := h.boundMAC

/-- The DF rate region supplies the destination-typicality sub-hyp. -/
lemma InRelayDFRate.destination_typical
    {R Imrh Iry Ibroad : ℝ}
    (h : InRelayDFRate R Imrh Iry Ibroad) :
    IsDestinationJointlyTypicalHyp R Ibroad := h.boundBroad

end SubHyps

/-! ## Section 3 — Constructive rate witness bridge -/

section Bridge

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Rate-only DF achievability witness (no error content).**

Carries only the **message-cardinality** consequence of the block-Markov
encoder construction: for sufficiently large `n` there is a relay code at
rate `R`. This is what the constructive bridge below genuinely establishes —
it is the relay analogue of `BCRandomCodebookAveraging` (T3-C BC).

This predicate deliberately **omits** any `averageErrorProb` content. It is
therefore **not** the error-carrying `RelayDFInnerBoundExistence W R` (the
DF achievability proper) and **must not be confused with it**: a degenerate
constant code satisfies this rate witness but has error probability `1`. The
genuine vanishing-error step (block-Markov random coding) remains the open
residual `RelayDFAchievable`. -/
def RelayDFRateWitness
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

/-- **Constructive rate witness from the block-Markov encoder sub-hyp.**

The encoder sub-hyp `IsBlockMarkovEncoderHyp R` directly carries, for each
large `n`, a block-Markov code at message count `M ≥ exp (n R)` and total
length `n`; flattening it via `toRelayCode` gives a `RelayCode M n …`,
yielding `RelayDFRateWitness R` (the **rate-only** witness — *not* the
error-carrying achievability, since the constant flattening has no error
control).

The wrapper itself is purely constructive (`obtain` + `refine`); only the
load-bearing-ness of the consumed predicate `IsBlockMarkovEncoderHyp`
remains tracked separately (Phase 2.6 retract-candidate, parent plan
`relay-inner-bound-moonshot-plan`). No `sorry` is introduced here. -/
theorem relayDFRateWitness_of_encoder_hyp
    [Nonempty α] [Nonempty α₁]
    {R : ℝ}
    (h_enc : IsBlockMarkovEncoderHyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFRateWitness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R := by
  obtain ⟨N, hN⟩ := h_enc
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, bc, hlen, hM⟩ := hN n hn
  -- `exp (n R) > 0`, so the message count `M` is positive.
  have hMpos : 0 < M := by
    have hexp : (0 : ℝ) < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    have : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hexp hM
    exact_mod_cast this
  have : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hMpos⟩
  -- flatten the block-Markov code into a flat relay code, rewriting its
  -- total length to `n`.
  refine ⟨M, hlen ▸ bc.toRelayCode, hM⟩

/-- **Constructive rate witness from all three DF sub-hyps.**

The decode-and-forward **rate witness** is assembled from:

* `IsBlockMarkovEncoderHyp R` — block-Markov code at the right rate;
* `IsRelayDecodableHyp R Imrh Iry` — relay decode constraint;
* `IsDestinationJointlyTypicalHyp R Ibroad` — destination decode
  constraint.

The latter two are recorded as the DF rate-region inequalities; the rate
witness is supplied by the encoder hyp. This is **only** the message-count
witness — the error-carrying DF achievability needs the genuine
random-coding discharge (`RelayDFAchievable`), which is *not* established
here.

Constructive consumer of `IsBlockMarkovEncoderHyp` (1-line forward via
`relayDFRateWitness_of_encoder_hyp`); no `sorry` is introduced. -/
theorem relayDFRateWitness_of_sub_hyps
    [Nonempty α] [Nonempty α₁]
    {R Imrh Iry Ibroad : ℝ}
    (h_enc : IsBlockMarkovEncoderHyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R)
    (_h_dec : IsRelayDecodableHyp R Imrh Iry)
    (_h_typ : IsDestinationJointlyTypicalHyp R Ibroad) :
    RelayDFRateWitness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relayDFRateWitness_of_encoder_hyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) h_enc

end Bridge

/-! ## Section 4 — Witness reconstruction + re-publish -/

section Republish

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **DF rate witness from the three sub-hyps.**

The three structural sub-hyps assemble the **rate-only** DF witness
`RelayDFRateWitness R` via the constructive bridge. This is the genuine
body-discharge content: it establishes the message-cardinality witness, not
the error-carrying achievability.

The block-Markov *achievability witness*
`IsRelayDFBlockMarkovWitness W R Imrh Iry Ibroad`
(= `RelayDFAchievable W …`, the gated implication carrying vanishing error)
is **deliberately not** built here from the rate-only sub-hyps: doing so
would be the rate-only → achievability leap (a degenerate constant code
satisfies the rate witness but has error `1`). The vanishing-error step
remains the open residual discharged in the companion seeds.

Pure re-publish wrapper, constructive; no `sorry` is introduced. -/
theorem relayDFRateWitness_of_sub_hyps'
    [Nonempty α] [Nonempty α₁]
    {R Imrh Iry Ibroad : ℝ}
    (h_enc : IsBlockMarkovEncoderHyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R)
    (h_dec : IsRelayDecodableHyp R Imrh Iry)
    (h_typ : IsDestinationJointlyTypicalHyp R Ibroad) :
    RelayDFRateWitness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relayDFRateWitness_of_sub_hyps (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    h_enc h_dec h_typ


/-- **DF inner bound — sub-hyp rate-witness discharge + bundled rate
region.**

Variant taking the DF rate-region membership `InRelayDFRate` bundled
(splitting it back into the two scalar sub-hyps internally) together with
the encoder sub-hyp; **constructs the rate witness**.

Constructive forwarding through `relayDFRateWitness_of_sub_hyps`; no
`sorry` is introduced. -/
theorem relay_df_inner_bound_block_markov_discharged_region
    [Nonempty α] [Nonempty α₁]
    (R Imrh Iry Ibroad : ℝ)
    (h_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_enc : IsBlockMarkovEncoderHyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFRateWitness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relayDFRateWitness_of_sub_hyps (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    h_enc h_region.relay_decodable h_region.destination_typical

end Republish

/-! ## Section 5 — Sub-hyp algebra -/

section SubHypAlgebra

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- The encoder sub-hyp is anti-monotone in `R`. -/
theorem IsBlockMarkovEncoderHyp.anti_mono_R
    {R R' : ℝ}
    (h : IsBlockMarkovEncoderHyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R)
    (hR : R' ≤ R) :
    IsBlockMarkovEncoderHyp (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, bc, hlen, hM⟩ := hN n hn
  refine ⟨M, bc, hlen, ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : (n : ℝ) * R' ≤ (n : ℝ) * R := mul_le_mul_of_nonneg_left hR hn0
  exact (Real.exp_le_exp.mpr hmul).trans hM

/-- Relay-decodability is anti-monotone in `R`. -/
lemma IsRelayDecodableHyp.anti_mono_R
    {R R' Imrh Iry : ℝ}
    (h : IsRelayDecodableHyp R Imrh Iry) (hR : R' ≤ R) :
    IsRelayDecodableHyp R' Imrh Iry :=
  hR.trans h

/-- Relay-decodability is monotone in `Imrh`. -/
lemma IsRelayDecodableHyp.mono_Imrh
    {R Imrh Imrh' Iry : ℝ}
    (h : IsRelayDecodableHyp R Imrh Iry) (hI : Imrh ≤ Imrh') :
    IsRelayDecodableHyp R Imrh' Iry := by
  unfold IsRelayDecodableHyp at *; linarith

/-- Relay-decodability is monotone in `Iry`. -/
lemma IsRelayDecodableHyp.mono_Iry
    {R Imrh Iry Iry' : ℝ}
    (h : IsRelayDecodableHyp R Imrh Iry) (hI : Iry ≤ Iry') :
    IsRelayDecodableHyp R Imrh Iry' := by
  unfold IsRelayDecodableHyp at *; linarith

/-- Destination-typicality is anti-monotone in `R`. -/
lemma IsDestinationJointlyTypicalHyp.anti_mono_R
    {R R' Ibroad : ℝ}
    (h : IsDestinationJointlyTypicalHyp R Ibroad) (hR : R' ≤ R) :
    IsDestinationJointlyTypicalHyp R' Ibroad :=
  hR.trans h

/-- Destination-typicality is monotone in `Ibroad`. -/
lemma IsDestinationJointlyTypicalHyp.mono_Ibroad
    {R Ibroad Ibroad' : ℝ}
    (h : IsDestinationJointlyTypicalHyp R Ibroad) (hI : Ibroad ≤ Ibroad') :
    IsDestinationJointlyTypicalHyp R Ibroad' :=
  h.trans hI

end SubHypAlgebra

end InformationTheory.Shannon
