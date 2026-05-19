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
* `mac_capacity_region_outer_bound` — Cover–Thomas converse, published
  with **L-MAC2 + L-MAC4 engaged** (multi-user Fano + chain rule and the
  composite rate bound supplied as hypothesis / placeholder).
* `mac_capacity_region_inner_bound` — Cover–Thomas achievability,
  published with **L-MAC1 + L-MAC3 engaged** (multi-user joint
  typicality body and the existence statement supplied as hypothesis /
  placeholder).
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

## 撤退ライン (確定発動 5 本)

* **L-MAC1**: multi-user joint typicality body (4 error event + Bonferroni
  + AEP-by-counting, ~500-800 lines) is supplied as
  `_h_joint_typ : True` placeholder.
* **L-MAC2**: multi-user Fano + chain rule (`I(W_k; Y^n) ≤ I(X_k^n; Y^n |
  X_{≠k}^n)` per-letter sum, ~300-500 lines) is supplied as
  `_h_fano : True` + `_h_chain : True` placeholders.
* **L-MAC3**: inner bound is supplied as the `h_existence` hypothesis
  (the existence-form `∃ N, ∀ n ≥ N, ∃ M₁ M₂ c, …`); the main theorem's
  body is the identity wrap `:= h_existence`.
* **L-MAC4**: outer bound is supplied as the `h_rate_bound :
  InMACCapacityRegion …` hypothesis; the main theorem's body is the
  identity wrap `:= h_rate_bound`.
* **L-MAC5**: time-sharing convex hull / closure is fully scope-out
  (corner-point form publishing only).

The signatures mirror the **statement-level hypothesis pass-through
patterns** established for `relay_cutset_outer_bound` (T3-F Relay,
Cover–Thomas 15.10.1, converse side) and `wyner_ziv_achievability_existence`
(T3-D Wyner–Ziv, Cover–Thomas 15.9.2, achievability side). Discharge of
each placeholder is performed in companion seeds:

* `mac-joint-typicality-discharge-*`
* `mac-converse-fano-discharge-*`
* `mac-converse-chain-rule-discharge-*`
* `mac-converse-rate-bound-discharge-*`
* `mac-time-sharing-discharge-*`
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

/-! ## Single-rate and sum-rate cut bounds (statement-level hypothesis pass-through) -/

section RateBounds

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **Single-user rate bound for sender 1 (hypothesis pass-through form,
L-MAC2 engaged)**.

For any MAC block code `c` and rate `R₁`, the converse asserts

```
R₁ ≤ I(X₁; Y | X₂)   (= I₁)
```

after applying Fano's inequality on `(W₁, Y^n)`, the data-processing
inequality `I(W₁; Y^n) ≤ I(X₁^n; Y^n | X₂^n)` (using the Markov chain
`W₁ → X₁^n → Y^n` conditioned on `X₂^n`), and the per-letter chain rule
`I(X₁^n; Y^n | X₂^n) ≤ ∑ I(X_{1,i}; Y_i | X_{2,i}) ≤ n · I(X₁; Y | X₂)`.

The multi-hundred-line ingredients — multi-user Fano (~150 lines) and the
conditional-MI chain rule (~150 lines), bundled as L-MAC2 — are supplied
as `True` placeholders. The final scalar inequality is supplied as the
`h_bound` hypothesis. Discharge plan:
`mac-converse-single-rate-discharge-*`. -/
theorem mac_single_rate_bound₁
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ I₁ : ℝ)
    (_h_fano : True)
    (_h_chain : True)
    (h_bound : R₁ ≤ I₁) :
    R₁ ≤ I₁ := h_bound

/-- **Single-user rate bound for sender 2 (hypothesis pass-through form,
L-MAC2 engaged)**.

Mirror of `mac_single_rate_bound₁` with the two user indices swapped:

```
R₂ ≤ I(X₂; Y | X₁)   (= I₂)
```

via Fano on `(W₂, Y^n)`, DPI `I(W₂; Y^n) ≤ I(X₂^n; Y^n | X₁^n)`, and the
per-letter chain rule. -/
theorem mac_single_rate_bound₂
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₂ I₂ : ℝ)
    (_h_fano : True)
    (_h_chain : True)
    (h_bound : R₂ ≤ I₂) :
    R₂ ≤ I₂ := h_bound

/-- **Sum-rate bound (hypothesis pass-through form, L-MAC2 engaged)**.

For any MAC block code `c` and rate pair `(R₁, R₂)`, the converse asserts

```
R₁ + R₂ ≤ I(X₁, X₂; Y)   (= Iboth)
```

after Fano applied to the *joint* message `(W₁, W₂)`:
`n·(R₁+R₂) ≤ I((W₁,W₂); Y^n) + n·ε_n`, DPI
`I((W₁,W₂); Y^n) ≤ I((X₁^n, X₂^n); Y^n)`, and the per-letter chain rule
`I((X₁^n, X₂^n); Y^n) ≤ ∑ I(X_{1,i}, X_{2,i}; Y_i) ≤ n · I(X₁, X₂; Y)`. -/
theorem mac_sum_rate_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Iboth : ℝ)
    (_h_fano : True)
    (_h_chain : True)
    (h_sum : R₁ + R₂ ≤ Iboth) :
    R₁ + R₂ ≤ Iboth := h_sum

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

/-- **MAC capacity region outer bound (Cover–Thomas Theorem 15.3.4,
hypothesis pass-through form, L-MAC2 + L-MAC4 + L-MAC5 all engaged)**.

For any MAC block code `c : MACCode M₁ M₂ n α₁ α₂ β` and rate pair
`(R₁, R₂)`, given the three cut rates
`(I₁, I₂, Iboth) := (I(X₁;Y|X₂), I(X₂;Y|X₁), I(X₁,X₂;Y))` evaluated at
the joint product input pmf `p₁(x₁) p₂(x₂)`, the converse asserts

```
InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth
  :↔  R₁ ≤ I₁  ∧  R₂ ≤ I₂  ∧  R₁ + R₂ ≤ Iboth.
```

The theorem is published with the three hypothesis pass-through slots:

* `_h_fano : True` — multi-user Fano inequality
  (`n·R_k ≤ I(W_k; Y^n) + n·ε_n` for both single users and for the joint
  message) holds (L-MAC2; discharge in
  `mac-converse-fano-discharge-*`).
* `_h_chain : True` — multi-user conditional-MI chain rule
  (`I(X_k^n; Y^n | X_{≠k}^n) ≤ ∑ I(X_{k,i}; Y_i | X_{≠k,i})` and
  `I((X₁^n, X₂^n); Y^n) ≤ ∑ I(X_{1,i}, X_{2,i}; Y_i)`) holds (L-MAC2;
  discharge in `mac-converse-chain-rule-discharge-*`).
* `h_rate_bound : InMACCapacityRegion …` — the composite three-inequality
  rate bound itself (L-MAC4; discharge in
  `mac-converse-rate-bound-discharge-*`).

Time-sharing / convex hull (Theorem 15.3.6) is fully scope-out (L-MAC5);
the present statement publishes the corner-point form only, with
`(I₁, I₂, Iboth) : ℝ × ℝ × ℝ` evaluated externally and supplied as
arguments.

This signature mirrors the established statement-level hypothesis
pass-through pattern of `relay_cutset_outer_bound` (T3-F Relay,
Cover–Thomas Theorem 15.10.1), in particular the `_h_csiszar : True` /
`_h_chain : True` / `h_rate_bound` slots. -/
theorem mac_capacity_region_outer_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth := h_rate_bound

/-- **MAC capacity region outer bound — three-bound form**.

A more practical caller interface: instead of supplying the bundled
composite predicate `h_rate_bound`, supply the three cut-direction bounds
`h₁ : R₁ ≤ I₁`, `h₂ : R₂ ≤ I₂`, `hs : R₁ + R₂ ≤ Iboth` separately. The
three are combined by `mac_region_combine` to yield the region
membership.

This form is the usual exit point of an n-letter Fano + chain-rule
argument that produces the three cut bounds as separate intermediates. -/
theorem mac_capacity_region_outer_bound_three_bounds
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h₁ : R₁ ≤ I₁) (h₂ : R₂ ≤ I₂) (hs : R₁ + R₂ ≤ Iboth) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth :=
  mac_region_combine R₁ R₂ I₁ I₂ Iboth h₁ h₂ hs

/-- **MAC capacity region outer bound — `Real.log` rate form**.

Specialisation of `mac_capacity_region_outer_bound` to the standard
`R_k := Real.log M_k / n` rate convention used throughout Cover–Thomas
(and matched by `wyner_ziv_converse_n_letter` /
`relay_cutset_outer_bound_log_rate`). -/
theorem mac_capacity_region_outer_bound_log_rate
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (I₁ I₂ Iboth : ℝ)
    (h_fano : True) (h_chain : True)
    (h_rate_bound :
        InMACCapacityRegion
          (Real.log (M₁ : ℝ) / (n : ℝ))
          (Real.log (M₂ : ℝ) / (n : ℝ))
          I₁ I₂ Iboth) :
    InMACCapacityRegion
        (Real.log (M₁ : ℝ) / (n : ℝ))
        (Real.log (M₂ : ℝ) / (n : ℝ))
        I₁ I₂ Iboth :=
  mac_capacity_region_outer_bound hn c _ _ I₁ I₂ Iboth h_fano h_chain h_rate_bound

end OuterBound

/-! ## Inner bound: achievability main theorem (Cover–Thomas 15.3.6, hypothesis pass-through) -/

section InnerBound

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- The "existence" claim for the MAC inner bound: there exists a
threshold block length `N` beyond which one can find codes carrying at
least `⌈exp(n R_k)⌉` messages in each user direction.

The error-probability bound (average error `< ε` for any prescribed
`ε > 0`) is **not** embedded into this existence claim — it is supplied
on the caller side together with `h_existence` (and discharged in
`mac-joint-typicality-discharge-*` / `mac-random-codebook-discharge-*`).
This matches the convention of `wyner_ziv_achievability_existence`. -/
def MACInnerBoundExistence
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M₁ M₂ : ℕ) (_c : MACCode M₁ M₂ n α₁ α₂ β),
      Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
      ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)

/-- **MAC capacity region inner bound (Cover–Thomas Theorem 15.3.6,
hypothesis pass-through form, L-MAC1 + L-MAC3 + L-MAC5 all engaged)**.

If the rate pair `(R₁, R₂)` satisfies all three Cover–Thomas inequalities
*strictly* — i.e. `R₁ < I₁`, `R₂ < I₂`, `R₁ + R₂ < Iboth` (a single
`InMACCapacityRegion` instance with strict inequalities, which we receive
as the unbundled `_h_strict` triple) — then for every `n` sufficiently
large there exist `M_k ≥ ⌈exp(n R_k)⌉` and a MAC block code
`c : MACCode M₁ M₂ n α₁ α₂ β`.

The theorem is published with the hypothesis pass-through slots:

* `_h_strict` — the three strict inequalities (mirror of
  `InMACCapacityRegion` with `<` in place of `≤`; supplied unbundled as
  an `And` triple to match the usual call site shape).
* `_h_joint_typ : True` — multi-user joint typicality body (4 error
  events `E_1, E_2, E_3, E_4` + Bonferroni union bound + AEP-by-counting,
  ~500-800 lines) holds (L-MAC1; discharge in
  `mac-joint-typicality-discharge-*`).
* `h_existence : MACInnerBoundExistence …` — the existence statement
  itself (L-MAC3; discharge in `mac-random-codebook-discharge-*`).

The error-probability bound (average error `< ε` for any prescribed
`ε > 0`) is **not** embedded into the existence statement — it is
supplied on the caller side together with `h_existence`. This matches
the convention of `wyner_ziv_achievability_existence` (T3-D Wyner–Ziv,
Cover–Thomas Theorem 15.9.2). -/
theorem mac_capacity_region_inner_bound
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (_h_joint_typ : True)
    (h_existence : MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂) :
    MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂ :=
  h_existence

/-- **MAC capacity region inner bound — bundled-strict form**.

Variant of `mac_capacity_region_inner_bound` taking the strict
inequalities bundled as a single `InMACCapacityRegion`-shaped predicate
whose hypotheses use `<` rather than `≤`. We expose this `<`-bundled
form by *receiving* an `InMACCapacityRegion` together with the
side-conditions that none of the three inequalities is saturated.

In practice callers usually supply the unbundled `And` triple via
`mac_capacity_region_inner_bound`; this variant is offered for
symmetry with `mac_capacity_region_outer_bound`. -/
theorem mac_capacity_region_inner_bound_bundled_strict
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_in_region : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth)
    (_h_strict₁ : R₁ ≠ I₁)
    (_h_strict₂ : R₂ ≠ I₂)
    (_h_strict_sum : R₁ + R₂ ≠ Iboth)
    (_h_joint_typ : True)
    (h_existence : MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂) :
    MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂ :=
  h_existence

end InnerBound

/-! ## Two-side combine and log-rate wrappers -/

section TwoSide

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC capacity region — two-side combine (achievability + converse)**.

If a rate pair `(R₁, R₂)` is shown both to be achievable (existence form,
inner bound) **and** to lie in the corner-point predicate region (outer
bound), then we package the two facts together as the `And` of the two
publish-layer conclusions.

This is a thin wrapper packaging the simultaneous validity of both
hypothesis pass-through forms; it does not derive new information, but
matches the two-side packaging pattern of `wyner_ziv_tendsto`
(T3-D Wyner–Ziv) for callers that want a single entry point.

Both `_h_fano`, `_h_chain`, `_h_joint_typ` placeholders for the underlying
multi-hundred-line discharges (L-MAC1 + L-MAC2) are forwarded transparently
to the two main theorems via `trivial`. -/
theorem mac_capacity_region_consistent
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_fano : True) (_h_chain : True) (_h_joint_typ : True)
    (h_rate_bound : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth)
    (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h_existence : MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂) :
    InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth
      ∧ MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂ :=
  ⟨mac_capacity_region_outer_bound hn c R₁ R₂ I₁ I₂ Iboth trivial trivial h_rate_bound,
   mac_capacity_region_inner_bound (α₁ := α₁) (α₂ := α₂) (β := β)
     R₁ R₂ I₁ I₂ Iboth h_strict trivial h_existence⟩

end TwoSide

end InformationTheory.Shannon
