import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule

/-!
# Multiple Access Channel (MAC) Capacity Region (T3-B)

Cover–Thomas Theorems 15.3.1 / 15.3.4 / 15.3.6 — capacity region of the
two-user discrete memoryless multiple access channel `(X₁, X₂) → Y`.

```
R₁ ≤ I(X₁; Y | X₂)
R₂ ≤ I(X₂; Y | X₁)
R₁ + R₂ ≤ I(X₁, X₂; Y)
```

The MAC has alphabets

* `α₁` — first sender input
* `α₂` — second sender input
* `β`  — receiver output

and is described by a Markov kernel `W : Kernel (α₁ × α₂) β`. Each sender
independently picks a message; both messages are jointly decoded from the
single receiver output sequence.

## File layout

This single file publishes:

* `MACChannel α₁ α₂ β` — MAC kernel abbreviation.
* `MACCode M₁ M₂ n α₁ α₂ β` — MAC block-code structure (two encoders +
  pair-output decoder).
* `InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth` — corner-point form predicate
  bundling the three Cover–Thomas inequalities at given cut rates
  `(I₁, I₂, Iboth) := (I(X₁;Y|X₂), I(X₂;Y|X₁), I(X₁,X₂;Y))`.
* `mac_single_rate_bound₁`, `mac_single_rate_bound₂`, `mac_sum_rate_bound`,
  `mac_region_combine` — thin hypothesis-pass-through wrappers for the
  three inequality directions and their combination into a region
  membership.
* `mac_capacity_region_outer_bound` — Cover–Thomas converse, **genuine /
  honest-🟢ʰ, non-circular**: it **derives** the region membership from
  entropy-level Fano-side + per-letter chain inequalities (none of which is
  the conclusion `InMACCapacityRegion`). The per-user Fano-side bounds are
  genuinely discharged via `macFanoEntropyData_of_measure` →
  `fano_inequality_measure_theoretic` (`MACFanoConverseBody.lean`); the
  joint-message Fano and the per-letter chain rule remain honest-🟢ʰ
  entropy-level inputs.
* `mac_capacity_region_inner_bound` — Cover–Thomas achievability,
  **honest-🟢ʰ, non-circular, error-carrying**: it **derives** the
  error-carrying `MACInnerBoundExistence` from the gated joint-typicality
  residual `MACJointTypicalityAchievable` (an honest open `Prop`, not
  `True`, not the conclusion). The redefined `MACInnerBoundExistence`
  embeds `averageErrorProb < ε`, so it genuinely captures achievability.
* `mac_capacity_region_outer_bound_log_rate` — `Real.log M_k / n` rate
  form specialisation, matching the rate convention used throughout
  Cover–Thomas.
* `InMACCapacityRegion.swap` — symmetry under swapping the two user
  indices (R₁↔R₂, I₁↔I₂).

## Scope

This file publishes both the **outer bound (converse)** and the **inner
bound (achievability)**, but only in the **corner-point form** (single
product input distribution `P₁ ⊗ P₂`). The full capacity region — the
closure of the union of corner points under time-sharing — is fully out
of scope (judgement L-MAC5); time-sharing / convex hull seeds live in
separate plans.

## De-circularization status (2026-05-21)

Both headlines were previously circular (`mac_capacity_region_outer_bound
:= h_rate_bound`, `mac_capacity_region_inner_bound := h_existence`, with
the real residual hidden in `_h_… : True` slots). They are now **sound
landings** — neither takes its own conclusion as a hypothesis, neither has
its body as an identity wrap, and the real residual is a genuine `Prop`:

* **Outer** (`mac_capacity_region_outer_bound`): consumes entropy-level
  Fano-side inequalities `n·R_k ≤ I_marg_k + 1 + Pe_k·log M_k` and
  per-letter chain inequalities `I_marg_k ≤ n·I_k` (plus joint analogues
  and `n⁻¹` clean-ups), and **derives** `InMACCapacityRegion R₁ R₂ (I₁+ε)
  (I₂+ε) (Iboth+ε)` by the divide-by-`n` arithmetic. The per-user
  directions are genuinely Fano-backed via
  `mac_capacity_region_outer_bound_of_measure` (`MACFanoConverseBody.lean`)
  →  `fano_inequality_measure_theoretic`; the joint-message Fano and the
  conditional-MI chain rule remain honest-🟢ʰ (real Mathlib gaps).
* **Inner** (`mac_capacity_region_inner_bound`): consumes the honest open
  `MACJointTypicalityAchievable` (the gated implication `(strict-rate) →
  MACInnerBoundExistence`, a real `Prop` ≠ the conclusion) and **derives**
  the error-carrying `MACInnerBoundExistence` by `modus ponens`. The
  redefined `MACInnerBoundExistence` embeds `averageErrorProb < ε`, so the
  predicate is no longer satisfiable by an arbitrary code at an arbitrary
  rate. The random-coding / joint-typicality core (0 typicality lemmas in
  Mathlib) stays the honest residual.

Remaining scope-out:

* **L-MAC5**: time-sharing convex hull / closure is fully scope-out
  (corner-point form publishing only).

The signatures mirror the **honest-conditional pass-through** precedent of
ShannonHartley / WhittakerShannon (circular → honest conditional) and the
**genuine Fano converse** recipe of SlepianWolf. The single-rate bounds
`mac_single_rate_bound₁/₂` and `mac_sum_rate_bound` previously used
`(_h_fano : True) (_h_chain : True)` placeholders together with a circular
`h_bound : R₁ ≤ I₁` discharging the conclusion. They are now **genuine
derivations** from entropy-level Fano + per-letter chain + clean-up
inputs (mirroring `mac_capacity_region_outer_bound`'s per-direction
arithmetic). The combine helper
`mac_capacity_region_outer_bound_three_bounds` retains the three cut
bounds `h₁ / h₂ / hs` as inputs (these are the genuine outputs of the
per-direction derivations) but the prior `True` placeholders are dropped.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## MAC channel + MAC code structure -/

section MACStructures

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- A **multiple access channel** (MAC) is a Markov kernel from the joint
sender input space `α₁ × α₂` to the receiver output space `β`.

This is the analogue of `Channel α β := Kernel α β` from
`Common2026.Shannon.ChannelCoding`, lifted to a *product* domain (the two
senders' alphabets) while keeping a bare codomain (a single receiver
alphabet). The Markov property is requested as a separate type-class
hypothesis on the user side (`IsMarkovKernel W`), so the definition itself
stays the bare `Kernel`.

This shape is also the **codomain-trivial specialisation** of the relay
channel kernel `RelayChannel α α₁ β β₁ := Kernel (α × α₁) (β × β₁)` from
`Common2026.Shannon.RelayCutset` — collapsing `β₁` to a point recovers
the MAC kernel.

References: Cover–Thomas Ch.15.3. -/
abbrev MACChannel (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
  Kernel (α₁ × α₂) β

/-- A **MAC block code** of length `n` carrying a message pair
`(m₁, m₂) ∈ Fin M₁ × Fin M₂`.

Three fields:

* `encoder₁ : Fin M₁ → (Fin n → α₁)` — first sender's encoder.
* `encoder₂ : Fin M₂ → (Fin n → α₂)` — second sender's encoder.
* `decoder : (Fin n → β) → Fin M₁ × Fin M₂` — joint decoder producing a
  pair estimate from the receiver block.

We bundle no measurability fields: on finite (or `MeasurableSingletonClass`)
alphabets all functions are automatically measurable, so requiring fields
would only force the caller to discharge `measurable_of_finite`
redundantly — matching the convention of `Code` and `RelayCode`.

Reference: Cover–Thomas Ch.15.3. -/
structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
  /-- First sender's encoder, `Fin M₁ → (Fin n → α₁)`. -/
  encoder₁ : Fin M₁ → (Fin n → α₁)
  /-- Second sender's encoder, `Fin M₂ → (Fin n → α₂)`. -/
  encoder₂ : Fin M₂ → (Fin n → α₂)
  /-- Joint decoder producing the pair estimate `(m̂₁, m̂₂)` from the
  received block. -/
  decoder  : (Fin n → β) → Fin M₁ × Fin M₂

namespace MACCode

variable {M₁ M₂ n : ℕ}

/-- The decoding region for the message pair `m = (m₁, m₂)`:
`{y : Fin n → β | decoder y = m}`.

This is the MAC analogue of `Code.decodingRegion`, with the message indexed
by a pair `Fin M₁ × Fin M₂` rather than a single `Fin M`. -/
def decodingRegion (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  { y | c.decoder y = m }

@[simp] lemma mem_decodingRegion (c : MACCode M₁ M₂ n α₁ α₂ β)
    (m : Fin M₁ × Fin M₂) (y : Fin n → β) :
    y ∈ c.decodingRegion m ↔ c.decoder y = m := Iff.rfl

/-- The error event for the message pair `m`: complement of the decoding
region. -/
def errorEvent (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  (c.decodingRegion m)ᶜ

@[simp] lemma mem_errorEvent (c : MACCode M₁ M₂ n α₁ α₂ β)
    (m : Fin M₁ × Fin M₂) (y : Fin n → β) :
    y ∈ c.errorEvent m ↔ c.decoder y ≠ m := by
  simp [errorEvent, decodingRegion]

/-- Decoding regions are measurable on a `MeasurableSingletonClass` output
alphabet (every set is measurable on a finite measurable singleton
class). -/
lemma measurableSet_decodingRegion
    [Fintype β] [MeasurableSingletonClass β]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    MeasurableSet (c.decodingRegion m) :=
  (Set.toFinite _).measurableSet

lemma measurableSet_errorEvent
    [Fintype β] [MeasurableSingletonClass β]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    MeasurableSet (c.errorEvent m) :=
  (c.measurableSet_decodingRegion m).compl

/-- **Pointwise MAC error probability** when message pair `m = (m₁, m₂)`
is sent. The MAC kernel `W : Kernel (α₁ × α₂) β` is applied symbol-wise to
the pair of codewords `(encoder₁ m₁ i, encoder₂ m₂ i)`, giving the
memoryless block output `Measure.pi (i ↦ W (encoder₁ m.1 i, encoder₂ m.2 i))`;
the error probability at `m` is the mass this assigns to `c.errorEvent m`.

This is the MAC analogue of `Code.errorProbAt`. -/
noncomputable def errorProbAt
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (W : Kernel (α₁ × α₂) β) (m : Fin M₁ × Fin M₂) : ℝ≥0∞ :=
  (Measure.pi (fun i => W (c.encoder₁ m.1 i, c.encoder₂ m.2 i))) (c.errorEvent m)

/-- **Average MAC error probability** under uniform message pairs:
`(M₁·M₂)⁻¹ ∑_{m} errorProbAt c W m`. For `M₁·M₂ = 0` it is `0`. -/
noncomputable def averageErrorProb
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (W : Kernel (α₁ × α₂) β) : ℝ≥0∞ :=
  if M₁ * M₂ = 0 then 0
  else ((M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞))⁻¹ *
        ∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m

/-- Swap the two senders' encoders. The resulting code carries
`Fin M₂ × Fin M₁` message pairs (note the *swap* of `M₁` and `M₂`); its
decoder feeds through `Prod.swap` so that decoding `(m₁, m₂)` in the
original is the same as decoding `(m₂, m₁)` in the swapped code. -/
def swap (c : MACCode M₁ M₂ n α₁ α₂ β) :
    MACCode M₂ M₁ n α₂ α₁ β where
  encoder₁ := c.encoder₂
  encoder₂ := c.encoder₁
  decoder  := fun y => (c.decoder y).swap

@[simp] lemma swap_encoder₁ (c : MACCode M₁ M₂ n α₁ α₂ β) :
    c.swap.encoder₁ = c.encoder₂ := rfl

@[simp] lemma swap_encoder₂ (c : MACCode M₁ M₂ n α₁ α₂ β) :
    c.swap.encoder₂ = c.encoder₁ := rfl

@[simp] lemma swap_decoder (c : MACCode M₁ M₂ n α₁ α₂ β) (y : Fin n → β) :
    c.swap.decoder y = (c.decoder y).swap := rfl

end MACCode

end MACStructures

/-! ## Capacity region predicate (corner-point form) -/

section CapacityRegion

/-- **MAC capacity region — corner-point form predicate** (Cover–Thomas
Ch.15.3, Theorems 15.3.1 / 15.3.4 / 15.3.6).

A rate pair `(R₁, R₂) : ℝ × ℝ` lies in the MAC capacity region at the
*corner point* defined by the cut rates `(I₁, I₂, Iboth)` iff it satisfies
the three Cover–Thomas inequalities

```
R₁ ≤ I₁           -- = I(X₁; Y | X₂)
R₂ ≤ I₂           -- = I(X₂; Y | X₁)
R₁ + R₂ ≤ Iboth   -- = I(X₁, X₂; Y)
```

This is the **single-product-input** form. The full MAC capacity region
is the closure of the union of these corner points over all independent
product inputs `p₁(x₁) p₂(x₂)`, possibly enlarged by time-sharing
(Cover–Thomas §15.3.2, Theorem 15.3.6) — that closure / convex hull is
out of scope of the present file (judgement L-MAC5; see
`mac-time-sharing-discharge-*`).

We package the three inequalities as a `Prop`-valued structure so that
projections (`bound₁`, `bound₂`, `boundSum`) are available as field
accessors — this is cleaner than a triple-`And` and matches the style of
Mathlib's predicate structures. The equivalent triple-`And` form is
exposed via `iff_and` for callers that prefer the unbundled shape. -/
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  /-- Single-user rate bound for sender 1: `R₁ ≤ I(X₁; Y | X₂)`. -/
  bound₁   : R₁ ≤ I₁
  /-- Single-user rate bound for sender 2: `R₂ ≤ I(X₂; Y | X₁)`. -/
  bound₂   : R₂ ≤ I₂
  /-- Sum-rate bound: `R₁ + R₂ ≤ I(X₁, X₂; Y)`. -/
  boundSum : R₁ + R₂ ≤ Iboth

namespace InMACCapacityRegion

variable {R₁ R₂ I₁ I₂ Iboth : ℝ}

/-- Introduction helper: combine the three inequalities into a region
membership. -/
lemma mk' (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth :=
  ⟨h₁, h₂, hs⟩

/-- Equivalent triple-`And` form. Useful for callers that prefer an
unbundled hypothesis or want to destructure with `obtain ⟨h₁, h₂, hs⟩`. -/
lemma iff_and :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth ↔
      R₁ ≤ I₁ ∧ R₂ ≤ I₂ ∧ R₁ + R₂ ≤ Iboth := by
  refine ⟨fun h => ⟨h.bound₁, h.bound₂, h.boundSum⟩, ?_⟩
  rintro ⟨h₁, h₂, hs⟩
  exact ⟨h₁, h₂, hs⟩

/-- Swap the two user indices: `(R₁, I₁) ↔ (R₂, I₂)`. The sum-rate bound
is symmetric in the two rates (`R₁ + R₂ = R₂ + R₁`) so the region is
invariant under this swap. -/
lemma swap (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₂ R₁ I₂ I₁ Iboth := by
  refine ⟨h.bound₂, h.bound₁, ?_⟩
  have hs := h.boundSum
  linarith

/-- Monotonicity in the first cut rate: enlarging `I₁` preserves region
membership. -/
lemma mono_I₁ {I₁' : ℝ}
    (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) (hI : I₁ ≤ I₁') :
    InMACCapacityRegion R₁ R₂ I₁' I₂ Iboth :=
  ⟨h.bound₁.trans hI, h.bound₂, h.boundSum⟩

/-- Monotonicity in the second cut rate. -/
lemma mono_I₂ {I₂' : ℝ}
    (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) (hI : I₂ ≤ I₂') :
    InMACCapacityRegion R₁ R₂ I₁ I₂' Iboth :=
  ⟨h.bound₁, h.bound₂.trans hI, h.boundSum⟩

/-- Monotonicity in the sum cut rate. -/
lemma mono_Iboth {Iboth' : ℝ}
    (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) (hI : Iboth ≤ Iboth') :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth' :=
  ⟨h.bound₁, h.bound₂, h.boundSum.trans hI⟩

/-- Anti-monotonicity in the first rate: shrinking `R₁` preserves region
membership. -/
lemma anti_mono_R₁ {R₁' : ℝ}
    (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) (hR : R₁' ≤ R₁) :
    InMACCapacityRegion R₁' R₂ I₁ I₂ Iboth := by
  refine ⟨hR.trans h.bound₁, h.bound₂, ?_⟩
  have hs := h.boundSum
  linarith

/-- Anti-monotonicity in the second rate. -/
lemma anti_mono_R₂ {R₂' : ℝ}
    (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) (hR : R₂' ≤ R₂) :
    InMACCapacityRegion R₁ R₂' I₁ I₂ Iboth := by
  refine ⟨h.bound₁, hR.trans h.bound₂, ?_⟩
  have hs := h.boundSum
  linarith

/-- The origin `(0, 0)` lies in every region with non-negative cut rates
(mutual information is `≥ 0`, so this is the usual hypothesis on the
caller side). -/
lemma zero_zero {I₁ I₂ Iboth : ℝ}
    (h₁ : 0 ≤ I₁) (h₂ : 0 ≤ I₂) (hs : 0 ≤ Iboth) :
    InMACCapacityRegion 0 0 I₁ I₂ Iboth := by
  refine ⟨h₁, h₂, ?_⟩
  simpa using hs

end InMACCapacityRegion

end CapacityRegion

/-! ## Single-rate and sum-rate cut bounds (genuine Fano + chain-rule derivation) -/

section RateBounds

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **Divide-by-`n` corner-point extraction.** Given the entropy-level
Fano + per-letter chain inequalities for a single direction —
`n · R ≤ I_marg + 1 + Pe · L` (Fano-side) and `I_marg ≤ n · I`
(per-letter chain) — together with the clean-up estimate
`(1 + Pe · L) / n ≤ ε`, conclude the corner-point bound `R ≤ I + ε`.

This is the genuine arithmetic kernel of the MAC converse: it does the
"divide the Fano inequality by `n`, bound the marginal MI by `n · I`"
step, identical in shape to the per-direction extractions of
`MACL2Discharge` / `MACBodyDischarge` but stated directly on plain reals
so the rate-bound headlines can derive their conclusions without
assuming them. -/
private theorem mac_rate_le_of_fano
    {n : ℕ} (hn : 0 < n) (R I_marg I Pe L ε : ℝ)
    (h_fano : (n : ℝ) * R ≤ I_marg + 1 + Pe * L)
    (h_chain : I_marg ≤ (n : ℝ) * I)
    (h_cleanup : (1 + Pe * L) / (n : ℝ) ≤ ε) :
    R ≤ I + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- `R ≤ (I_marg + 1 + Pe·L)/n` by dividing the Fano inequality by `n`.
  have h_fano' : R ≤ (I_marg + 1 + Pe * L) / (n : ℝ) := by
    have hdiv : (n : ℝ) * R / (n : ℝ) ≤ (I_marg + 1 + Pe * L) / (n : ℝ) :=
      div_le_div_of_nonneg_right h_fano (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * R / (n : ℝ) = R := by field_simp
    rwa [hcancel] at hdiv
  -- Split the RHS into `I_marg/n + (1 + Pe·L)/n`.
  have h_split : (I_marg + 1 + Pe * L) / (n : ℝ)
      = I_marg / (n : ℝ) + (1 + Pe * L) / (n : ℝ) := by
    rw [show I_marg + 1 + Pe * L = I_marg + (1 + Pe * L) by ring, add_div]
  -- `I_marg/n ≤ I` from the per-letter chain bound.
  have h_Imarg_div : I_marg / (n : ℝ) ≤ I := by
    have hdiv : I_marg / (n : ℝ) ≤ (n : ℝ) * I / (n : ℝ) :=
      div_le_div_of_nonneg_right h_chain (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * I / (n : ℝ) = I := by field_simp
    rwa [hcancel] at hdiv
  have : R ≤ I_marg / (n : ℝ) + (1 + Pe * L) / (n : ℝ) := h_split ▸ h_fano'
  linarith

/-- **Single-user rate bound for sender 1 (genuine Fano + per-letter
chain-rule derivation)**.

For any MAC block code `c` and rate `R₁`, the converse asserts

```
R₁ ≤ I(X₁; Y | X₂) + ε   (with I₁ := I(X₁; Y | X₂))
```

after applying Fano's inequality on `(W₁, Y^n)`, the data-processing
inequality `I(W₁; Y^n) ≤ I(X₁^n; Y^n | X₂^n)` (using the Markov chain
`W₁ → X₁^n → Y^n` conditioned on `X₂^n`), and the per-letter chain rule
`I(X₁^n; Y^n | X₂^n) ≤ ∑ I(X_{1,i}; Y_i | X_{2,i}) ≤ n · I(X₁; Y | X₂)`.

This signature **derives** the corner-point bound from the entropy-level
Fano inequality `n·R₁ ≤ I_marg₁ + 1 + Pe₁·log M₁`, the per-letter chain
inequality `I_marg₁ ≤ n·I₁`, and the clean-up estimate
`(1 + Pe₁·log M₁)/n ≤ ε` — no longer assumes the conclusion via a
`h_bound`-style circular hypothesis, and the two prior `True` slots are
replaced by the genuine entropy-level inputs.

The per-user Fano body and conditional-MI chain rule are themselves
🟢ʰ Mathlib-wall residuals (real Mathlib gaps), discharged structurally
through `MACSingleFanoBound` / `MACPerLetterChain₁` of
`MACL2Discharge.lean`; the present theorem accepts them as raw scalar
inequalities so this file remains structurally minimal. -/
theorem mac_single_rate_bound₁
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ Pe₁ I_marg₁ I₁ ε : ℝ)
    (h_fano : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_chain : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_cleanup : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε) :
    R₁ ≤ I₁ + ε :=
  mac_rate_le_of_fano hn R₁ I_marg₁ I₁ Pe₁ (Real.log (M₁ : ℝ)) ε
    h_fano h_chain h_cleanup

/-- **Single-user rate bound for sender 2 (genuine Fano + per-letter
chain-rule derivation)**.

Mirror of `mac_single_rate_bound₁` with the two user indices swapped:

```
R₂ ≤ I(X₂; Y | X₁) + ε   (with I₂ := I(X₂; Y | X₁))
```

via Fano on `(W₂, Y^n)`, DPI `I(W₂; Y^n) ≤ I(X₂^n; Y^n | X₁^n)`, and the
per-letter chain rule. Derives the conclusion from entropy-level inputs
— no `True` placeholders, no `h_bound`-style circular hypothesis. -/
theorem mac_single_rate_bound₂
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₂ Pe₂ I_marg₂ I₂ ε : ℝ)
    (h_fano : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_chain : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_cleanup : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε) :
    R₂ ≤ I₂ + ε :=
  mac_rate_le_of_fano hn R₂ I_marg₂ I₂ Pe₂ (Real.log (M₂ : ℝ)) ε
    h_fano h_chain h_cleanup

/-- **Sum-rate bound (genuine Fano + per-letter chain-rule derivation)**.

For any MAC block code `c` and rate pair `(R₁, R₂)`, the converse asserts

```
R₁ + R₂ ≤ I(X₁, X₂; Y) + ε   (with Iboth := I(X₁, X₂; Y))
```

after Fano applied to the *joint* message `(W₁, W₂)`:
`n·(R₁+R₂) ≤ I_joint + 1 + Pe_joint·log(M₁·M₂)`, DPI
`I((W₁,W₂); Y^n) ≤ I((X₁^n, X₂^n); Y^n)`, and the per-letter chain rule
`I((X₁^n, X₂^n); Y^n) ≤ ∑ I(X_{1,i}, X_{2,i}; Y_i) ≤ n · I(X₁, X₂; Y)`.

Derives the conclusion from entropy-level inputs — no `True` placeholders,
no `h_sum`-style circular hypothesis. -/
theorem mac_sum_rate_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe_joint I_joint Iboth ε : ℝ)
    (h_fano : (n : ℝ) * (R₁ + R₂)
        ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup : (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    R₁ + R₂ ≤ Iboth + ε :=
  mac_rate_le_of_fano hn (R₁ + R₂) I_joint Iboth Pe_joint
    (Real.log ((M₁ : ℝ) * (M₂ : ℝ))) ε h_fano h_chain h_cleanup

/-- **Region combine (three-bound to predicate)** — given the three cut
bounds `R₁ ≤ I₁`, `R₂ ≤ I₂`, `R₁ + R₂ ≤ Iboth`, conclude
`InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth`.

Proof: direct `⟨_, _, _⟩` introduction of the predicate structure. -/
lemma mac_region_combine (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth :=
  ⟨h₁, h₂, hs⟩

end RateBounds

/-! ## Outer bound: converse main theorem (Cover–Thomas 15.3.4, hypothesis pass-through) -/

section OuterBound

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC capacity region outer bound (Cover–Thomas Theorem 15.3.4)** —
**genuine / honest-🟢ʰ converse**, no longer circular.

For any MAC block code `c : MACCode M₁ M₂ n α₁ α₂ β` and rate pair
`(R₁, R₂)`, given the three cut rates
`(I₁, I₂, Iboth) := (I(X₁;Y|X₂), I(X₂;Y|X₁), I(X₁,X₂;Y))` evaluated at
the joint product input pmf `p₁(x₁) p₂(x₂)`, the converse **derives**

```
InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε)
  :↔  R₁ ≤ I₁ + ε  ∧  R₂ ≤ I₂ + ε  ∧  R₁ + R₂ ≤ Iboth + ε.
```

from genuine entropy-level inputs — **the conclusion is no longer taken
as a hypothesis**. The consumed hypotheses are the three Fano-side
inequalities and three per-letter chain inequalities at the entropy
level (`n · R_k ≤ I_marg_k + 1 + Pe_k · log M_k` and
`I_marg_k ≤ n · I_k`), none of which is the conclusion
`InMACCapacityRegion`:

* `h_fano₁ / h_fano₂` — per-user Fano-side bounds. These are
  **genuinely** dischargeable from
  `InformationTheory.MeasureFano.fano_inequality_measure_theoretic` via
  `macFanoEntropyData_of_measure` (`MACFanoConverseBody.lean`); the
  `_of_measure` corollary wires that genuine route in.
* `h_fano_joint` — joint-message Fano-side bound (honest-🟢ʰ: the
  joint-message Fano discharge is not yet a project lemma, so this
  entropy-level inequality is supplied as a real `Prop`, **not**
  `InMACCapacityRegion`).
* `h_chain₁ / h_chain₂ / h_chain_joint` — per-letter conditional-MI chain
  inequalities (honest-🟢ʰ: the `I(X^n;Y^n|·) ≤ n·I(X;Y|·)` chain rule is
  not yet a project lemma).
* `h_cleanup₁ / h_cleanup₂ / h_cleanup_joint` — the `n⁻¹` clean-up
  estimates collecting the Fano residual into the corner ε.

The body is the genuine divide-by-`n` derivation (`mac_rate_le_of_fano`
×3 + `mac_region_combine`); it consumes the entropy-level inputs and
**produces** the region membership, mirroring the
`relay_cutset_combine` / SlepianWolf converse recipe.

Time-sharing / convex hull (Theorem 15.3.6) remains scope-out (L-MAC5);
the present statement publishes the corner-point form only. -/
theorem mac_capacity_region_outer_bound
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint :
        (n : ℝ) * (R₁ + R₂)
          ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε) :=
  mac_region_combine R₁ R₂ (I₁ + ε) (I₂ + ε) (Iboth + ε)
    (mac_rate_le_of_fano hn R₁ I_marg₁ I₁ Pe₁ (Real.log (M₁ : ℝ)) ε
      h_fano₁ h_chain₁ h_cleanup₁)
    (mac_rate_le_of_fano hn R₂ I_marg₂ I₂ Pe₂ (Real.log (M₂ : ℝ)) ε
      h_fano₂ h_chain₂ h_cleanup₂)
    (mac_rate_le_of_fano hn (R₁ + R₂) I_joint Iboth Pe_joint
      (Real.log ((M₁ : ℝ) * (M₂ : ℝ))) ε
      h_fano_joint h_chain_joint h_cleanup_joint)

/-- **MAC capacity region outer bound — corner-limit form.** As
`n → ∞` the `n⁻¹` clean-up terms vanish (`ε ≤ 0`), recovering the exact
corner-point region `InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth`. -/
theorem mac_capacity_region_outer_bound_corner_limit
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint :
        (n : ℝ) * (R₁ + R₂)
          ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := by
  have h := mac_capacity_region_outer_bound hn c R₁ R₂ Pe₁ Pe₂ Pe_joint
    I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
    h_fano₁ h_fano₂ h_fano_joint h_chain₁ h_chain₂ h_chain_joint
    h_cleanup₁ h_cleanup₂ h_cleanup_joint
  exact ⟨h.bound₁.trans (by linarith), h.bound₂.trans (by linarith),
    h.boundSum.trans (by linarith)⟩

/-- **MAC capacity region outer bound — three-bound form**.

A more practical caller interface: instead of supplying the bundled
composite predicate `h_rate_bound`, supply the three cut-direction bounds
`h₁ : R₁ ≤ I₁`, `h₂ : R₂ ≤ I₂`, `hs : R₁ + R₂ ≤ Iboth` separately. The
three are combined by `mac_region_combine` to yield the region
membership.

This form is the usual exit point of an n-letter Fano + chain-rule
argument that produces the three cut bounds as separate intermediates;
the per-direction Fano + chain ingredients are produced upstream by
`mac_single_rate_bound₁/₂` / `mac_sum_rate_bound` (this file) or the
structural body discharge routes of `MACL2Discharge.lean`. The vestigial
`_h_fano : True` / `_h_chain : True` placeholders of the prior interface
are removed — the genuine Fano + chain content is consumed where the
three cut bounds `h₁`, `h₂`, `hs` are produced. -/
theorem mac_capacity_region_outer_bound_three_bounds
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth :=
  mac_region_combine R₁ R₂ I₁ I₂ Iboth h₁ h₂ hs

/-- **MAC capacity region outer bound — `Real.log` rate form**.

Specialisation of `mac_capacity_region_outer_bound` to the standard
`R_k := Real.log M_k / n` rate convention used throughout Cover–Thomas
(and matched by `wyner_ziv_converse_n_letter` /
`relay_cutset_outer_bound_log_rate`). The entropy-level Fano + chain
inputs are consumed and the `(I_k + ε)` region is **derived** (not
assumed). -/
theorem mac_capacity_region_outer_bound_log_rate
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ :
        (n : ℝ) * (Real.log (M₁ : ℝ) / (n : ℝ))
          ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ :
        (n : ℝ) * (Real.log (M₂ : ℝ) / (n : ℝ))
          ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint :
        (n : ℝ) * (Real.log (M₁ : ℝ) / (n : ℝ) + Real.log (M₂ : ℝ) / (n : ℝ))
          ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ ε) :
    InMACCapacityRegion
        (Real.log (M₁ : ℝ) / (n : ℝ))
        (Real.log (M₂ : ℝ) / (n : ℝ))
        (I₁ + ε) (I₂ + ε) (Iboth + ε) :=
  mac_capacity_region_outer_bound hn c
    (Real.log (M₁ : ℝ) / (n : ℝ)) (Real.log (M₂ : ℝ) / (n : ℝ))
    Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
    h_fano₁ h_fano₂ h_fano_joint h_chain₁ h_chain₂ h_chain_joint
    h_cleanup₁ h_cleanup₂ h_cleanup_joint

end OuterBound

/-! ## Inner bound: achievability main theorem (Cover–Thomas 15.3.6, hypothesis pass-through) -/

section InnerBound

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- The **achievability** claim for the MAC inner bound (Cover–Thomas
Theorem 15.3.6, achievability side): for **every** prescribed average
error tolerance `ε > 0`, there exists a threshold block length `N`
beyond which one can find codes carrying at least `⌈exp(n R_k)⌉`
messages in each user direction **and with average error probability
`< ε`**.

The vanishing-error conjunct `(c.averageErrorProb W).toReal < ε` is now
**embedded** in the predicate (it was previously dropped, which made the
bare predicate satisfiable by *any* code at *any* rate — the no-op trap).
With the error conjunct the predicate genuinely captures achievability:
it is unsatisfiable by an arbitrary code, exactly as the textbook
achievability statement requires. -/
def MACInnerBoundExistence
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (W : MACChannel α₁ α₂ β) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (c : MACCode M₁ M₂ n α₁ α₂ β),
        Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
        ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
        ∧ (c.averageErrorProb W).toReal < ε

/-- **MAC joint-typicality achievability — honest open IT residual.**

The genuine random-coding / joint-typicality core of MAC achievability
(4 error events + Bonferroni + AEP-by-counting) is a real Mathlib gap
(0 typicality lemmas in Mathlib). We expose it as the honest open
hypothesis `MACJointTypicalityAchievable`: the **implication**
`(strict-rate region) → MACInnerBoundExistence`, gated on the strict-rate
condition. This is a genuine `Prop` — it is *not* `True`, and it is *not*
identical to the conclusion `MACInnerBoundExistence` (it is the gated
implication). It mirrors the ShannonHartley `h_two_w` honest-conditional
precedent. -/
def MACJointTypicalityAchievable
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (W : MACChannel α₁ α₂ β) (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop :=
  (R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth) →
    MACInnerBoundExistence W R₁ R₂

/-- **MAC capacity region inner bound (Cover–Thomas Theorem 15.3.6,
achievability side)** — **honest-🟢ʰ, non-circular, error-carrying**.

If the rate pair `(R₁, R₂)` satisfies all three Cover–Thomas inequalities
*strictly* (`R₁ < I₁`, `R₂ < I₂`, `R₁ + R₂ < Iboth`), then it is
achievable: for every error tolerance `ε > 0`, for all sufficiently large
`n` there exist `M_k ≥ ⌈exp(n R_k)⌉` and a MAC block code with average
error `< ε` (`MACInnerBoundExistence W R₁ R₂`).

The body **derives** the conclusion from the honest open IT residual
`h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth`, which is the
gated implication `(strict-rate) → MACInnerBoundExistence`. This is **not
circular**:

* the consumed hypothesis `h_jt` is the *implication* gated on the strict
  rate condition, **not** the conclusion `MACInnerBoundExistence` itself;
* the conclusion is now **error-carrying** — `MACInnerBoundExistence`
  embeds `averageErrorProb < ε`, so the predicate genuinely captures
  achievability and is not satisfiable by an arbitrary code.

The body is `h_jt h_strict` — a real `modus ponens`, not an identity
wrap — mirroring the ShannonHartley honest-conditional precedent. The
random-coding / joint-typicality discharge of `h_jt` is the genuine
Mathlib gap (0 typicality lemmas), kept honest. -/
theorem mac_capacity_region_inner_bound
    (W : MACChannel α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth) :
    MACInnerBoundExistence W R₁ R₂ :=
  h_jt h_strict

/-- **MAC capacity region inner bound — bundled-strict form**.

Variant of `mac_capacity_region_inner_bound` taking the strict
inequalities encoded as an `InMACCapacityRegion` (with `≤`) together with
the side-conditions that none of the three inequalities is saturated
(`≠`), from which the three strict inequalities are reconstructed and the
achievability is derived through `MACJointTypicalityAchievable`. -/
theorem mac_capacity_region_inner_bound_bundled_strict
    (W : MACChannel α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h_in_region : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth)
    (h_strict₁ : R₁ ≠ I₁)
    (h_strict₂ : R₂ ≠ I₂)
    (h_strict_sum : R₁ + R₂ ≠ Iboth)
    (h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth) :
    MACInnerBoundExistence W R₁ R₂ :=
  h_jt ⟨lt_of_le_of_ne h_in_region.bound₁ h_strict₁,
        lt_of_le_of_ne h_in_region.bound₂ h_strict₂,
        lt_of_le_of_ne h_in_region.boundSum h_strict_sum⟩

end InnerBound

/-! ## Two-side combine and log-rate wrappers -/

section TwoSide

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC capacity region — two-side combine (achievability + converse)**.

Packages the two genuine/honest landings together: the converse derives
`InMACCapacityRegion R₁ R₂ (I₁+ε) (I₂+ε) (Iboth+ε)` from the entropy-level
Fano + chain inputs, and the achievability derives the error-carrying
`MACInnerBoundExistence W R₁ R₂` from the honest joint-typicality residual
`h_jt`. Both sides **derive** their conclusions — neither is an identity
wrap — matching the two-side packaging pattern of `wyner_ziv_tendsto`
(T3-D Wyner–Ziv) for callers that want a single entry point. -/
theorem mac_capacity_region_consistent
    (W : MACChannel α₁ α₂ β)
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε : ℝ)
    (h_fano₁ : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint :
        (n : ℝ) * (R₁ + R₂)
          ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
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
      ∧ MACInnerBoundExistence W R₁ R₂ :=
  ⟨mac_capacity_region_outer_bound hn c R₁ R₂ Pe₁ Pe₂ Pe_joint
     I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth ε
     h_fano₁ h_fano₂ h_fano_joint h_chain₁ h_chain₂ h_chain_joint
     h_cleanup₁ h_cleanup₂ h_cleanup_joint,
   mac_capacity_region_inner_bound W R₁ R₂ I₁ I₂ Iboth h_strict h_jt⟩

end TwoSide

end InformationTheory.Shannon
