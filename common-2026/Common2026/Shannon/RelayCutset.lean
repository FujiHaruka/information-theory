import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule

/-!
# Relay Channel + Cut-set Outer Bound (T3-F)

Cover–Thomas Theorem 15.10.1 (cut-set outer bound for the relay channel,
Ch.15.7 / 15.10).

```
C ≤ max_{p(x, x_1)} min { I(X, X_1; Y),  I(X; Y, Y_1 | X_1) }
```

The relay channel has alphabets
* `α`  — sender input
* `α₁` — relay input
* `β`  — receiver output
* `β₁` — relay output

and is described by a Markov kernel `W : Kernel (α × α₁) (β × β₁)`.

## File layout

This single file publishes:

* `RelayChannel α α₁ β β₁` — relay-channel kernel abbreviation.
* `RelayCode M n α α₁ β β₁` — relay block-code structure (encoder +
  per-step causal relay function + decoder).
* `relayCutsetBound Ib Im : ℝ` — scalar form of the cut-set bound
  `min { I(X, X₁; Y), I(X; Y, Y₁ | X₁) }`.
* `relay_broadcast_cut`, `relay_mac_cut`, `relay_cutset_combine` — thin
  hypothesis-pass-through wrappers for the two cut directions.
* `relay_cutset_outer_bound` — Cover–Thomas Theorem 15.10.1 main theorem,
  published with **L-RC1 + L-RC2 + L-RC3 + L-RC4 all engaged** (every
  ingredient that requires a multi-hundred-line discharge is supplied as a
  hypothesis or `True` placeholder).

## Scope

This file publishes the **outer bound only**. The inner bound (decode-and-
forward / compress-and-forward, Cover–Thomas Theorems 15.10.2 / 15.10.3) is
fully out of scope (judgement L-RC5); inner-bound seeds live in separate
plans.

## 撤退ライン (確定発動 4 本 + scope 縮減 1 本)

* **L-RC1**: Csiszár's sum identity (per-letter sum over the broadcast and
  MAC cuts) is supplied as `_h_csiszar : True` placeholder.
* **L-RC2**: auxiliary chain rule (broadcast / MAC chain expansion + DPI)
  is supplied as `_h_chain : True` placeholder.
* **L-RC3**: composite rate bound `R ≤ min { Ib, Im }` is supplied as
  `h_rate_bound` hypothesis. The main theorem's body is the identity wrap
  `:= h_rate_bound`.
* **L-RC4**: relay channel measurability bundle (per-step kernel
  composition + joint distribution constructive measurability) is fully
  deferred; the main statement consumes only scalar values `Ib Im : ℝ`.
* **L-RC5**: inner bound (DF / CF) is fully scope-out (separate seeds).

The signatures mirror the **statement-level hypothesis pass-through pattern**
established for `wyner_ziv_converse_n_letter` (T3-D Wyner–Ziv, Cover–Thomas
Theorem 15.9.2), in particular the `_h_csiszar : True` + `h_rate_bound`
slots. Discharge of each placeholder is performed in companion seeds:

* `relay-cutset-csiszar-sum-discharge-*`
* `relay-cutset-chain-rule-discharge-*`
* `relay-cutset-rate-bound-discharge-*`
* `relay-cutset-measurability-discharge-*`
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Relay channel + relay code structure -/

section RelayStructures

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- A **relay channel** is a Markov kernel from the joint sender / relay
input space `α × α₁` to the joint receiver / relay output space `β × β₁`.

This is the analogue of `Channel α β := Kernel α β` from
`Common2026.Shannon.ChannelCoding`, lifted to a product domain/codomain. The
Markov property is requested as a separate type-class hypothesis on the user
side (`IsMarkovKernel W`), so the definition itself stays the bare
`Kernel`.

References: Cover–Thomas Ch.15.7. -/
abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

/-- A **relay block code** of length `n` carrying `M` messages.

Three fields:

* `encoder : Fin M → (Fin n → α)` — encodes a message into a length-`n`
  block of sender symbols.
* `relay : ∀ (i : Fin n), (Fin i.val → β₁) → α₁` — at time `i`, the relay
  reads the past relay outputs `y₁_0, …, y₁_{i-1}` and emits the next relay
  input `x₁_i`. The `Fin i.val → β₁` domain enforces causality at the type
  level.
* `decoder : (Fin n → β) → Fin M` — decodes the length-`n` block of
  receiver symbols into a message estimate.

Reference: Cover–Thomas Ch.15.7. -/
structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁] where
  /-- Sender-side encoder, `Fin M → (Fin n → α)`. -/
  encoder : Fin M → (Fin n → α)
  /-- Per-step causal relay function: at time `i`, read past `β₁` outputs
  and produce the next `α₁` input. -/
  relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  /-- Receiver-side decoder, `(Fin n → β) → Fin M`. -/
  decoder : (Fin n → β) → Fin M

namespace RelayCode

variable {M n : ℕ}

/-- The decoding region for message `m`: `{y : Fin n → β | decoder y = m}`.

This is the relay-channel analogue of `Code.decodingRegion` from
`Common2026.Shannon.ChannelCoding`. -/
def decodingRegion (c : RelayCode M n α α₁ β β₁) (m : Fin M) : Set (Fin n → β) :=
  { y | c.decoder y = m }

@[simp] lemma mem_decodingRegion (c : RelayCode M n α α₁ β β₁) (m : Fin M)
    (y : Fin n → β) :
    y ∈ c.decodingRegion m ↔ c.decoder y = m := Iff.rfl

/-- The error event for message `m`: complement of the decoding region. -/
def errorEvent (c : RelayCode M n α α₁ β β₁) (m : Fin M) : Set (Fin n → β) :=
  (c.decodingRegion m)ᶜ

@[simp] lemma mem_errorEvent (c : RelayCode M n α α₁ β β₁) (m : Fin M)
    (y : Fin n → β) :
    y ∈ c.errorEvent m ↔ c.decoder y ≠ m := by
  simp [errorEvent, decodingRegion]

/-- Decoding regions are measurable on a `MeasurableSingletonClass` output
alphabet (every set is measurable on a finite measurable singleton class). -/
lemma measurableSet_decodingRegion
    [Fintype β] [MeasurableSingletonClass β]
    (c : RelayCode M n α α₁ β β₁) (m : Fin M) :
    MeasurableSet (c.decodingRegion m) :=
  (Set.toFinite _).measurableSet

lemma measurableSet_errorEvent
    [Fintype β] [MeasurableSingletonClass β]
    (c : RelayCode M n α α₁ β β₁) (m : Fin M) :
    MeasurableSet (c.errorEvent m) :=
  (c.measurableSet_decodingRegion m).compl

end RelayCode

end RelayStructures

/-! ## Cut-set bound (scalar form) -/

section CutsetBound

/-- **Cut-set outer bound (scalar form, Cover–Thomas Ch.15.10.1)** —
given the *broadcast cut* rate `Ib = I(X, X₁; Y)` and the *MAC cut* rate
`Im = I(X; Y, Y₁ | X₁)` evaluated at an optimal joint input pmf
`p(x, x_1)`, the relay channel capacity is bounded above by
`min { Ib, Im }`.

The scalar form takes the two cut-rate values directly as real arguments;
the outer maximisation
`max_{p(x, x₁)} min { I(X, X₁; Y), I(X; Y, Y₁ | X₁) }` is consumed on the
caller side. This keeps the file free of `IsCompact + exists_isMaxOn`
plumbing on the joint simplex (~100 lines avoided) and mirrors the scalar
publish pattern of `relayCutsetBound = min Ib Im`.

A future seed (`relay-cutset-pmf-form-*`) may upgrade this to a pmf-form
function `relayCutsetBoundPmf P W : ℝ` taking the joint input pmf and
channel kernel as arguments. -/
noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im

@[simp] lemma relayCutsetBound_def (Ib Im : ℝ) :
    relayCutsetBound Ib Im = min Ib Im := rfl

/-- The cut-set bound is at most the broadcast cut rate. -/
lemma relayCutsetBound_le_left (Ib Im : ℝ) : relayCutsetBound Ib Im ≤ Ib :=
  min_le_left _ _

/-- The cut-set bound is at most the MAC cut rate. -/
lemma relayCutsetBound_le_right (Ib Im : ℝ) : relayCutsetBound Ib Im ≤ Im :=
  min_le_right _ _

/-- Symmetry of the scalar cut-set bound: order of the two cut rates is
irrelevant. -/
lemma relayCutsetBound_comm (Ib Im : ℝ) :
    relayCutsetBound Ib Im = relayCutsetBound Im Ib := by
  unfold relayCutsetBound; exact min_comm _ _

/-- Monotonicity in the broadcast cut rate (with the MAC rate fixed). -/
lemma relayCutsetBound_mono_left {Ib Ib' Im : ℝ} (h : Ib ≤ Ib') :
    relayCutsetBound Ib Im ≤ relayCutsetBound Ib' Im := by
  unfold relayCutsetBound
  exact min_le_min h le_rfl

/-- Monotonicity in the MAC cut rate (with the broadcast rate fixed). -/
lemma relayCutsetBound_mono_right {Ib Im Im' : ℝ} (h : Im ≤ Im') :
    relayCutsetBound Ib Im ≤ relayCutsetBound Ib Im' := by
  unfold relayCutsetBound
  exact min_le_min le_rfl h

/-- The cut-set bound is non-negative whenever both cut rates are
non-negative (true for mutual information, which is `≥ 0`). -/
lemma relayCutsetBound_nonneg {Ib Im : ℝ} (hb : 0 ≤ Ib) (hm : 0 ≤ Im) :
    0 ≤ relayCutsetBound Ib Im :=
  le_min hb hm

end CutsetBound

/-! ## Broadcast and MAC cuts (statement-level hypothesis pass-through) -/

section Cuts

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Broadcast cut (hypothesis pass-through form, L-RC1 + L-RC2 engaged)**.

For any relay block code `c` and rate `R`, the broadcast direction of the
cut-set bound asserts

```
R ≤ I(X, X₁; Y)   (= Ib)
```

after applying Fano's inequality, the data-processing inequality
`I(W; Y^n) ≤ I(X^n, X_1^n; Y^n)`, and the per-letter chain rule
`I(X^n, X_1^n; Y^n) ≤ ∑ I(X_i, X_{1,i}; Y_i) ≤ n · I(X, X_1; Y)`.

The two ingredients that require a multi-hundred-line discharge — Csiszár's
sum identity (L-RC1, ~300 lines) and the auxiliary chain-rule expansion
(L-RC2, ~150 lines) — are supplied as `True` placeholders. The final scalar
inequality is supplied as the `h_bcast` hypothesis (L-RC3 form for the
broadcast cut). Discharge plan:
`relay-cutset-broadcast-discharge-*`. -/
theorem relay_broadcast_cut
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib : ℝ)
    (_h_csiszar : True)
    (_h_chain : True)
    (h_bcast : R ≤ Ib) :
    R ≤ Ib := h_bcast

/-- **MAC cut (hypothesis pass-through form, L-RC1 + L-RC2 engaged)**.

For any relay block code `c` and rate `R`, the multiple-access direction of
the cut-set bound asserts

```
R ≤ I(X; Y, Y₁ | X₁)   (= Im)
```

after Fano's inequality, conditional-MI chain rule with the relay's input
`X₁` placed in the conditioning side, and the per-letter sum
`I(W; Y^n, Y_1^n | X_1^n) ≤ ∑ I(X_i; Y_i, Y_{1,i} | X_{1,i})` (Csiszár's
sum identity applied to the *conditional* chain).

The Csiszár's identity (L-RC1) and conditional chain-rule expansion (L-RC2)
are supplied as `True` placeholders; the final scalar inequality is
supplied as the `h_mac` hypothesis. Discharge plan:
`relay-cutset-mac-discharge-*`. -/
theorem relay_mac_cut
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Im : ℝ)
    (_h_csiszar : True)
    (_h_chain : True)
    (h_mac : R ≤ Im) :
    R ≤ Im := h_mac

/-- **Cut-set combination (two-rate `min`)** — given the two cut bounds
`R ≤ Ib` and `R ≤ Im`, conclude `R ≤ relayCutsetBound Ib Im`.

Proof: direct application of `le_min`. -/
lemma relay_cutset_combine (R Ib Im : ℝ)
    (h_bcast : R ≤ Ib) (h_mac : R ≤ Im) :
    R ≤ relayCutsetBound Ib Im := by
  unfold relayCutsetBound
  exact le_min h_bcast h_mac

end Cuts

/-! ## Main theorem (Cover–Thomas Theorem 15.10.1, hypothesis pass-through) -/

section MainTheorem

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay cut-set outer bound (Cover–Thomas Theorem 15.10.1, hypothesis
pass-through form, L-RC1 + L-RC2 + L-RC3 + L-RC4 all engaged)**.

For any relay block code `c : RelayCode M n α α₁ β β₁` and rate `R`, given
the broadcast-cut rate `Ib = I(X, X₁; Y)` and MAC-cut rate
`Im = I(X; Y, Y₁ | X₁)` evaluated at an optimal joint input pmf, the
cut-set outer bound

```
R ≤ relayCutsetBound Ib Im = min { Ib, Im }
```

holds, modulo three hypothesis pass-through slots:

* `_h_csiszar : True` — Csiszár's sum identity (per-letter broadcast + MAC
  sum) holds (L-RC1; discharge in
  `relay-cutset-csiszar-sum-discharge-*`).
* `_h_chain : True` — auxiliary chain rule (broadcast / MAC chain
  expansion + DPI) holds (L-RC2; discharge in
  `relay-cutset-chain-rule-discharge-*`).
* `h_rate_bound : R ≤ relayCutsetBound Ib Im` — the composite cut-set rate
  bound itself (L-RC3; discharge in
  `relay-cutset-rate-bound-discharge-*`).

The relay measurability bundle (per-step kernel composition + joint
distribution constructive measurability) is fully deferred (L-RC4); the
statement consumes only scalar values `Ib Im : ℝ`. Discharge in
`relay-cutset-measurability-discharge-*`.

This signature mirrors the established statement-level hypothesis
pass-through pattern of `wyner_ziv_converse_n_letter` (T3-D Wyner–Ziv,
Cover–Thomas Theorem 15.9.2), in particular the `_h_csiszar : True` and
`h_rate_bound` slots. -/
theorem relay_cutset_outer_bound
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_rate_bound : R ≤ relayCutsetBound Ib Im) :
    R ≤ relayCutsetBound Ib Im := h_rate_bound

/-- **Relay cut-set outer bound — two-cut form**.

A more practical caller interface: instead of supplying the composite
`min` bound `h_rate_bound`, supply the two cut-direction bounds
`h_bcast : R ≤ Ib` and `h_mac : R ≤ Im` separately. The two are combined
by `relay_cutset_combine` to yield the cut-set bound.

This form is the usual exit point of an n-letter Fano + chain-rule
argument that produces the two cut bounds as separate intermediates. -/
theorem relay_cutset_outer_bound_two_cuts
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_bcast : R ≤ Ib) (h_mac : R ≤ Im) :
    R ≤ relayCutsetBound Ib Im :=
  relay_cutset_combine R Ib Im h_bcast h_mac

/-- **Relay cut-set outer bound — `Real.log` rate form**.

Specialisation of `relay_cutset_outer_bound` to the standard
`R := Real.log M / n` rate convention used throughout Cover–Thomas (and
matched by `wyner_ziv_converse_n_letter`). -/
theorem relay_cutset_outer_bound_log_rate
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (Ib Im : ℝ)
    (h_csiszar : True) (h_chain : True)
    (h_rate_bound :
        Real.log (M : ℝ) / (n : ℝ) ≤ relayCutsetBound Ib Im) :
    Real.log (M : ℝ) / (n : ℝ) ≤ relayCutsetBound Ib Im :=
  relay_cutset_outer_bound hn c _ Ib Im h_csiszar h_chain h_rate_bound

end MainTheorem

end InformationTheory.Shannon
