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
* `RelayCode.averageErrorProb` — average decoding error probability of a
  relay code under a relay channel (the relay analogue of
  `MACCode.averageErrorProb`); used by the inner-bound existence predicates.
* `RelayBcastCutFano`, `RelayMacCutFano` — entropy-level Fano-side
  inequalities for the two cut directions (non-circular named `Prop`s).
* `relay_broadcast_cut`, `relay_mac_cut` — per-cut bounds
  `R ≤ Ib + ε` / `R ≤ Im + ε`. Currently `sorry` under the sorry-based
  migration: the previous public signature bundled a load-bearing
  per-letter chain hypothesis (Csiszár sum identity wall, L-RC1/L-RC2)
  which has been removed; closure tracked on
  `relay-cutset-moonshot-plan`.
* `relay_cutset_combine` — combines the two cut bounds into the cut-set
  bound via `le_min`.
* `relay_cutset_outer_bound` — Cover–Thomas Theorem 15.10.1 main theorem.
  Currently `sorry` (two load-bearing chain hypotheses removed); closure
  tracked on `relay-cutset-moonshot-plan`.

## Scope

This file publishes the **outer bound only**. The inner bound (decode-and-
forward / compress-and-forward, Cover–Thomas Theorems 15.10.2 / 15.10.3) is
fully out of scope (judgement L-RC5); inner-bound seeds live in separate
plans.

## De-circularization status (2026-05-21) + sorry-based migration (2026-05-25)

The headline `relay_cutset_outer_bound` was previously circular
(`:= h_rate_bound`, with the real residual hidden in `_h_csiszar : True` /
`_h_chain : True` slots). The 2026-05-21 de-circularisation removed the
circular hypothesis and replaced the `True` slots with genuine
entropy-level `Prop`s (Fano-side, per-letter chain, clean-up). The
broadcast-cut Fano direction (single-user `W → Y^n`) is genuinely
Fano-backed; the MAC-cut chain direction relies on the conditional
Csiszár sum identity (Mathlib wall, L-RC1/L-RC2) and was the
load-bearing piece.

The 2026-05-25 sorry-based migration retreats the headline + two cut
wrappers to `sorry`: the load-bearing chain hypotheses have been removed
from the public signatures (so honest open issues are tracked by `sorry`
rather than by `*Hypothesis`-style predicate consumption). Closure
responsibility is `@residual(plan:relay-cutset-moonshot-plan)`.

## 撤退ライン

* **L-RC4**: relay channel measurability bundle (per-step kernel
  composition + joint distribution constructive measurability) is deferred;
  the main statement consumes only scalar values.
* **L-RC5**: inner bound (DF / CF) is fully scope-out (separate seeds).

The converse signature mirrors the **genuine Fano converse** recipe of
SlepianWolf / `mac_capacity_region_outer_bound` (T3-B MAC) /
`bc_capacity_region_outer_bound` (T3-C BC). The `relay_broadcast_cut` /
`relay_mac_cut` helpers were de-circularised (2026-05-23) and then
sorry-migrated (2026-05-25): both signatures previously took a chain
hypothesis `h_chain : I_marg ≤ n · I` which bundled the (conditional)
Csiszár sum identity (L-RC1) + per-letter chain expansion (L-RC2)
Mathlib walls. Those load-bearing hypotheses have been removed and the
wrappers now carry `sorry` + `@residual(plan:relay-cutset-moonshot-plan)`
until L-RC1 / L-RC2 are discharged.
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

/-- The **receiver-marginal error event** of message `m` lifted to the joint
output block `Fin n → β × β₁`: the destination decoder, reading the
receiver marginal `(y i).1`, mis-decodes `m`.

This is the relay analogue of `BroadcastCode.jointErrorEvent`, lifted to the
joint codomain `β × β₁` (the relay kernel `W : Kernel (α × α₁) (β × β₁)`
produces joint outputs; the destination reads its own `β`-marginal). -/
def jointErrorEvent (c : RelayCode M n α α₁ β β₁) (m : Fin M) :
    Set (Fin n → β × β₁) :=
  { y | c.decoder (fun i => (y i).1) ≠ m }

/-- **Pointwise relay error probability** when message `m` is sent. The
relay kernel `W : Kernel (α × α₁) (β × β₁)` is applied symbol-wise to the
pair `(encoder m i, x₁Ref i)` of sender codeword and a reference relay-input
sequence, giving the memoryless block output
`Measure.pi (i ↦ W (encoder m i, x₁Ref i))` on `Fin n → β × β₁`; the error
probability at `m` is the mass this assigns to the receiver-marginal error
event `c.jointErrorEvent m`.

The reference relay-input sequence `x₁Ref` carries the relay's transmitted
symbols; the full causal dependence of `x₁` on past relay outputs (the
operational relay semantics) is consumed on the discharge side, exactly as
`MACCode.errorProbAt` consumes the joint codeword pairing. This is the relay
analogue of `MACCode.errorProbAt` / `BroadcastCode.errorProbAt`. -/
noncomputable def errorProbAt
    (c : RelayCode M n α α₁ β β₁) (W : Kernel (α × α₁) (β × β₁))
    (x₁Ref : Fin n → α₁) (m : Fin M) : ℝ≥0∞ :=
  (Measure.pi (fun i => W (c.encoder m i, x₁Ref i))) (c.jointErrorEvent m)

/-- **Average relay error probability** under uniform messages:
`M⁻¹ ∑_{m} errorProbAt c W x₁Ref m`. For `M = 0` it is `0`.

This is the relay analogue of `MACCode.averageErrorProb` /
`BroadcastCode.averageErrorProb`. -/
noncomputable def averageErrorProb
    (c : RelayCode M n α α₁ β β₁) (W : Kernel (α × α₁) (β × β₁))
    (x₁Ref : Fin n → α₁) : ℝ≥0∞ :=
  if M = 0 then 0
  else (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt W x₁Ref m

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

/-! ## Cut-direction Fano-side hypotheses (entropy-level, non-circular) -/

section CutFano

/-- **Broadcast-cut Fano-side bound (entropy-level, non-circular).**

The entropy-level inequality produced by Fano's inequality applied to the
broadcast cut `W → Y^n` of the relay channel:

```
n · R ≤ I_marg + 1 + Pe · log M
```

where `I_marg = I(W; Y^n)` is the message–output mutual information, `Pe` is
the average error probability and `M` the message count. This is the
**single-user** Fano direction of the cut-set bound: the message `W` is
sent to the destination output `Y^n`, so the same recipe as the MAC per-user
converse (`fano_inequality_measure_theoretic`) discharges it genuinely.

The named `Prop` is **not** the conclusion `R ≤ relayCutsetBound …`; it is
the entropy-level Fano step the headline body consumes and divides by `n`.
-/
def RelayBcastCutFano (M n : ℕ) (R Pe I_marg : ℝ) : Prop :=
  (n : ℝ) * R ≤ I_marg + 1 + Pe * Real.log (M : ℝ)

@[simp] lemma RelayBcastCutFano_def (M n : ℕ) (R Pe I_marg : ℝ) :
    RelayBcastCutFano M n R Pe I_marg ↔
      (n : ℝ) * R ≤ I_marg + 1 + Pe * Real.log (M : ℝ) := Iff.rfl

/-- **MAC-cut Fano-side bound (entropy-level, non-circular).**

The entropy-level inequality produced by Fano's inequality applied to the
MAC cut `W → (Y^n, Y₁^n) | X₁^n` of the relay channel:

```
n · R ≤ I_marg + 1 + Pe · log M
```

where `I_marg = I(W; Y^n, Y₁^n | X₁^n)` is the conditional message–output
mutual information. Unlike the broadcast cut, the per-letter reduction of
this conditional MI requires **Csiszár's sum identity** (not yet a project
lemma); the consumers of this entropy-level `Prop` (`relay_mac_cut` etc.)
now bundle that wall via `sorry` rather than via a load-bearing
`h_chain : I_marg ≤ n · Im` hypothesis. The named `Prop` itself remains an
honest entropy-level statement, **not** `R ≤ relayCutsetBound …`. -/
def RelayMacCutFano (M n : ℕ) (R Pe I_marg : ℝ) : Prop :=
  (n : ℝ) * R ≤ I_marg + 1 + Pe * Real.log (M : ℝ)

@[simp] lemma RelayMacCutFano_def (M n : ℕ) (R Pe I_marg : ℝ) :
    RelayMacCutFano M n R Pe I_marg ↔
      (n : ℝ) * R ≤ I_marg + 1 + Pe * Real.log (M : ℝ) := Iff.rfl

end CutFano

/-! ## Divide-by-`n` cut extraction (shared arithmetic kernel) -/

/-- **Divide-by-`n` cut extraction.** Given the entropy-level Fano +
per-letter chain inequalities for one cut direction —
`n · R ≤ I_marg + 1 + Pe · log M` (Fano-side) and `I_marg ≤ n · I`
(per-letter chain) — together with the clean-up estimate
`(1 + Pe · log M) / n ≤ ε`, conclude the per-cut bound `R ≤ I + ε`.

This is the genuine arithmetic kernel of the cut-set converse: it does the
"divide the Fano inequality by `n`, bound the marginal MI by `n · I`" step,
identical in shape to `mac_rate_le_of_fano` (T3-B MAC) /
`bc_rate_le_of_fano` (T3-C BC) but applied to the two relay cuts (broadcast
and MAC). -/
private theorem relay_cut_rate_le_of_fano
    {M n : ℕ} (hn : 0 < n) (R Pe I_marg I ε : ℝ)
    (h_fano : (n : ℝ) * R ≤ I_marg + 1 + Pe * Real.log (M : ℝ))
    (h_chain : I_marg ≤ (n : ℝ) * I)
    (h_cleanup : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε) :
    R ≤ I + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_fano' : R ≤ (I_marg + 1 + Pe * Real.log (M : ℝ)) / (n : ℝ) := by
    have hdiv : (n : ℝ) * R / (n : ℝ)
        ≤ (I_marg + 1 + Pe * Real.log (M : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right h_fano (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * R / (n : ℝ) = R := by field_simp
    rwa [hcancel] at hdiv
  have h_split : (I_marg + 1 + Pe * Real.log (M : ℝ)) / (n : ℝ)
      = I_marg / (n : ℝ) + (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) := by
    rw [show I_marg + 1 + Pe * Real.log (M : ℝ)
        = I_marg + (1 + Pe * Real.log (M : ℝ)) by ring, add_div]
  have h_Imarg_div : I_marg / (n : ℝ) ≤ I := by
    have hdiv : I_marg / (n : ℝ) ≤ (n : ℝ) * I / (n : ℝ) :=
      div_le_div_of_nonneg_right h_chain (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * I / (n : ℝ) = I := by field_simp
    rwa [hcancel] at hdiv
  have : R ≤ I_marg / (n : ℝ) + (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) :=
    h_split ▸ h_fano'
  linarith

/-! ## Broadcast and MAC cuts (statement-level, honest Fano+chain inputs) -/

section Cuts

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Broadcast cut — `R ≤ Ib + ε`** (load-bearing Csiszár chain wall, sorry).

For any relay block code `c` and rate `R`, the broadcast direction of the
cut-set bound asserts

```
R ≤ Ib + ε
```

from the entropy-level Fano-side input + clean-up estimate:

* `h_fano : RelayBcastCutFano M n R Pe I_marg` — Fano-side bound
  `n · R ≤ I_marg + 1 + Pe · log M` for the broadcast cut `W → Y^n`.
* `h_cleanup : (1 + Pe · log M) / n ≤ ε` — clean-up estimate collecting the
  Fano residual into the corner `ε`.

The previous public signature also took a load-bearing chain hypothesis
`h_chain : I_marg ≤ n · Ib` (the per-letter chain bound
`I(W; Y^n) ≤ n · I(X, X₁; Y)`); that piece bundled the Mathlib-wall
Csiszár sum identity (L-RC1) and per-letter chain expansion (L-RC2) into
the wrapper as a hypothesis. Under the sorry-based migration that
load-bearing predicate has been removed: the wrapper now retreats to
`sorry`, with closure responsibility tracked on the parent moonshot plan.

`@residual(plan:relay-cutset-moonshot-plan)` -/
theorem relay_broadcast_cut
    {M n : ℕ} (hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Pe I_marg Ib ε : ℝ)
    (h_fano : RelayBcastCutFano M n R Pe I_marg)
    (h_cleanup : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε) :
    R ≤ Ib + ε := by
  sorry

/-- **MAC cut — `R ≤ Im + ε`** (load-bearing conditional Csiszár chain wall, sorry).

For any relay block code `c` and rate `R`, the MAC direction of the cut-set
bound asserts

```
R ≤ Im + ε
```

from the entropy-level Fano-side input + clean-up estimate:

* `h_fano : RelayMacCutFano M n R Pe I_marg` — Fano-side bound
  `n · R ≤ I_marg + 1 + Pe · log M` for the MAC cut
  `W → (Y^n, Y₁^n) | X₁^n`.
* `h_cleanup : (1 + Pe · log M) / n ≤ ε` — clean-up estimate.

The previous public signature also took a load-bearing chain hypothesis
`h_chain : I_marg ≤ n · Im` (the conditional per-letter chain bound
`I(W; Y^n, Y₁^n | X₁^n) ≤ n · I(X; Y, Y₁ | X₁)`); that piece bundled the
conditional Csiszár sum identity (L-RC1) + conditional chain-rule
expansion (L-RC2) into the wrapper. Under the sorry-based migration that
load-bearing predicate has been removed; closure responsibility is parked
on the parent moonshot plan.

`@residual(plan:relay-cutset-moonshot-plan)` -/
theorem relay_mac_cut
    {M n : ℕ} (hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Pe I_marg Im ε : ℝ)
    (h_fano : RelayMacCutFano M n R Pe I_marg)
    (h_cleanup : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε) :
    R ≤ Im + ε := by
  sorry

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

/-- **Relay cut-set outer bound (Cover–Thomas Theorem 15.10.1)** —
load-bearing Csiszár chain walls (broadcast + conditional), sorry.

For any relay block code `c : RelayCode M n α α₁ β β₁` and rate `R`, given
the broadcast-cut rate `Ib = I(X, X₁; Y)` and MAC-cut rate
`Im = I(X; Y, Y₁ | X₁)` evaluated at an optimal joint input pmf, the
converse asserts

```
R ≤ relayCutsetBound (Ib + ε) (Im + ε) = min { Ib + ε, Im + ε }
```

from the entropy-level Fano-side inputs and the two clean-up estimates:

* `h_fano_b : RelayBcastCutFano M n R Pe I_marg_b` — broadcast-cut Fano-side
  bound (single-user, Fano on `W → Y^n`).
* `h_fano_m : RelayMacCutFano M n R Pe I_marg_m` — MAC-cut Fano-side bound.
* `h_cleanup_b / h_cleanup_m` — the `n⁻¹` clean-up estimates.

The previous public signature also took two load-bearing chain hypotheses
`h_chain_b : I_marg_b ≤ n · Ib` and `h_chain_m : I_marg_m ≤ n · Im`;
together those bundled the (conditional) Csiszár sum identity (L-RC1) +
per-letter chain expansion (L-RC2) into the wrapper. Under the
sorry-based migration both load-bearing predicates have been removed;
closure responsibility is parked on the parent moonshot plan. The
joint-input maximisation (L-RC4) remains scope-out.

`@residual(plan:relay-cutset-moonshot-plan)` -/
theorem relay_cutset_outer_bound
    {M n : ℕ} (hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)
    (h_fano_m : RelayMacCutFano M n R Pe I_marg_m)
    (h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε) :
    R ≤ relayCutsetBound (Ib + ε) (Im + ε) := by
  sorry

/-- **Relay cut-set outer bound — corner-limit form.** As `n → ∞` the `n⁻¹`
clean-up terms vanish (`ε ≤ 0`), recovering the exact cut-set bound
`R ≤ relayCutsetBound Ib Im`.

Transitive `sorry` via `relay_cutset_outer_bound` (Phase 2.1 retreat). No
`@residual` tag is attached — the closure responsibility belongs to the
upstream declaration's `@residual(plan:relay-cutset-moonshot-plan)`. The
unused `_h_chain_b` / `_h_chain_m` parameters are kept as underscore
placeholders so that callers built against the previous public signature
continue to type-check (extract-only consumer parameterisation; the chain
hypotheses are no longer fed into the upstream body). -/
theorem relay_cutset_outer_bound_corner_limit
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)
    (h_fano_m : RelayMacCutFano M n R Pe I_marg_m)
    (_h_chain_b : I_marg_b ≤ (n : ℝ) * Ib)
    (_h_chain_m : I_marg_m ≤ (n : ℝ) * Im)
    (h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_ε : ε ≤ 0) :
    R ≤ relayCutsetBound Ib Im := by
  have h := relay_cutset_outer_bound hn c R Pe I_marg_b I_marg_m Ib Im ε
    h_fano_b h_fano_m h_cleanup_b h_cleanup_m
  refine le_min ?_ ?_
  · exact h.trans ((relayCutsetBound_le_left _ _).trans (by linarith))
  · exact h.trans ((relayCutsetBound_le_right _ _).trans (by linarith))

/-- **Relay cut-set outer bound — two-cut form**.

A more practical caller interface: instead of supplying the entropy-level
Fano + chain inputs, supply the two already-extracted cut-direction bounds
`h_bcast : R ≤ Ib` and `h_mac : R ≤ Im` separately. The two are combined
by `relay_cutset_combine` to yield the cut-set bound.

This form is the usual exit point of an n-letter Fano + chain-rule argument
that produces the two cut bounds as separate intermediates. -/
theorem relay_cutset_outer_bound_two_cuts
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Ib Im : ℝ)
    (h_bcast : R ≤ Ib) (h_mac : R ≤ Im) :
    R ≤ relayCutsetBound Ib Im :=
  relay_cutset_combine R Ib Im h_bcast h_mac

/-- **Relay cut-set outer bound — `Real.log` rate form**.

Specialisation of `relay_cutset_outer_bound` to the standard
`R := Real.log M / n` rate convention used throughout Cover–Thomas (and
matched by `wyner_ziv_converse_n_letter` /
`mac_capacity_region_outer_bound_log_rate`).

Transitive `sorry` via `relay_cutset_outer_bound` (Phase 2.1 retreat). No
`@residual` tag is attached — the closure responsibility belongs to the
upstream declaration's `@residual(plan:relay-cutset-moonshot-plan)`. The
unused `_h_chain_b` / `_h_chain_m` parameters are kept as underscore
placeholders so that callers built against the previous public signature
continue to type-check. -/
theorem relay_cutset_outer_bound_log_rate
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (h_fano_b :
        RelayBcastCutFano M n (Real.log (M : ℝ) / (n : ℝ)) Pe I_marg_b)
    (h_fano_m :
        RelayMacCutFano M n (Real.log (M : ℝ) / (n : ℝ)) Pe I_marg_m)
    (_h_chain_b : I_marg_b ≤ (n : ℝ) * Ib)
    (_h_chain_m : I_marg_m ≤ (n : ℝ) * Im)
    (h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε) :
    Real.log (M : ℝ) / (n : ℝ) ≤ relayCutsetBound (Ib + ε) (Im + ε) :=
  relay_cutset_outer_bound hn c (Real.log (M : ℝ) / (n : ℝ)) Pe
    I_marg_b I_marg_m Ib Im ε
    h_fano_b h_fano_m h_cleanup_b h_cleanup_m

end MainTheorem

end InformationTheory.Shannon
