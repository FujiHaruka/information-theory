import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.CondMutualInfo
import Common2026.Shannon.MIChainRule

/-!
# Broadcast Channel (degraded) Capacity Region (T3-C)

Cover–Thomas Theorem 15.6.2 — capacity region of the **degraded** two-receiver
broadcast channel `X → (Y₁, Y₂)` with the Markov degradation `X → Y₁ → Y₂`.

```
R₂ ≤ I(U; Y₂)         -- common message (poor receiver)
R₁ ≤ I(X; Y₁ | U)     -- private message (good receiver)
```

where `U` is the auxiliary RV used in superposition coding (`(U, X) ~ p(u) p(x|u)`).
The broadcast channel has alphabets

* `α`  — sender input
* `β₁` — good receiver output (decodes the private message `M₁`)
* `β₂` — poor receiver output (decodes the common message `M₂`)

and is described by a Markov kernel `W : Kernel α (β₁ × β₂)`. A single sender
generates `(U, X)` via superposition coding; the two receivers independently
decode from their respective channel outputs.

## File layout

This single file publishes:

* `BroadcastChannel α β₁ β₂` — BC kernel abbreviation.
* `BroadcastCode M₁ M₂ n α β₁ β₂` — BC block-code structure (one joint
  encoder + two separate per-receiver decoders).
* `InBCCapacityRegion R₁ R₂ I_u I_xy` — corner-point form predicate bundling
  the two Cover–Thomas inequalities at given cut rates
  `(I_u, I_xy) := (I(U;Y₂), I(X;Y₁|U))`.
* `bc_common_rate_bound`, `bc_private_rate_bound`, `bc_region_combine` —
  thin hypothesis-pass-through wrappers for the two inequality directions
  and their combination into a region membership.
* `bc_capacity_region_outer_bound` — Cover–Thomas converse, published with
  **L-BC2 + L-BC4 engaged** (Fano + chain rule and the composite rate bound
  supplied as hypothesis / placeholder).
* `bc_capacity_region_inner_bound` — Cover–Thomas achievability, published
  with **L-BC1 + L-BC3 engaged** (multi-receiver joint typicality body and
  the existence statement supplied as hypothesis / placeholder).
* `bc_capacity_region_outer_bound_log_rate` — `Real.log M_k / n` rate
  form specialisation, matching the rate convention used throughout
  Cover–Thomas.

## Scope

This file publishes both the **outer bound (converse)** and the **inner
bound (achievability)**, but only for the **degraded** broadcast channel
in the **corner-point form** (single auxiliary RV `U` with `(U, X)`
generated via superposition). The general (non-degraded) BC — including
Marton's inner bound and the Körner–Marton outer bound, which require
multiple auxiliary RVs and are partially-open at the time of Cover–Thomas
— is fully out of scope (judgement L-BC5).

## 撤退ライン (確定発動 5 本)

* **L-BC1**: multi-receiver joint typicality body (4 error events per
  receiver + Bonferroni + AEP-by-counting, ~500-800 lines) is supplied as
  `_h_joint_typ : True` placeholder.
* **L-BC2**: multi-user Fano + chain rule (`n·R₂ ≤ I(W₂; Y₂^n) + n·ε_n`,
  `n·R₁ ≤ I(W₁; Y₁^n | W₂) + n·ε_n`, per-letter chain rule, ~300-500 lines)
  is supplied as `_h_fano : True` + `_h_chain : True` placeholders.
* **L-BC3**: inner bound is supplied as the `h_existence` hypothesis
  (the existence-form `∃ N, ∀ n ≥ N, ∃ M₁ M₂ c, …`); the main theorem's
  body is the identity wrap `:= h_existence`.
* **L-BC4**: outer bound is supplied as the `h_rate_bound :
  InBCCapacityRegion …` hypothesis; the main theorem's body is the
  identity wrap `:= h_rate_bound`.
* **L-BC5**: general (non-degraded) BC + Marton inner bound +
  Körner–Marton outer bound are fully scope-out (degraded BC publishing
  only, single auxiliary RV `U` compressed to scalars `I_u, I_xy`).

The signatures mirror the **statement-level hypothesis pass-through
patterns** established for `mac_capacity_region_outer_bound` /
`mac_capacity_region_inner_bound` (T3-B MAC, Cover–Thomas 15.3.4/15.3.6),
in particular the `_h_fano : True` / `_h_chain : True` / `h_rate_bound`
slots on the converse side and the `_h_joint_typ : True` / `h_existence`
slots on the achievability side. Discharge of each placeholder is
performed in companion seeds:

* `bc-joint-typicality-discharge-*`
* `bc-converse-fano-discharge-*`
* `bc-converse-chain-rule-discharge-*`
* `bc-converse-rate-bound-discharge-*`
* `bc-superposition-decoder-discharge-*`
* `bc-general-discharge-*`
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## BC channel + BC code structure -/

section BCStructures

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- A **broadcast channel** (BC) is a Markov kernel from the sender input
space `α` to the *joint* output space `β₁ × β₂` of the two receivers.

This is the analogue of `Channel α β := Kernel α β` from
`Common2026.Shannon.ChannelCoding`, lifted to a *product* codomain (the two
receivers' alphabets) while keeping a bare domain (a single sender
alphabet). The Markov property is requested as a separate type-class
hypothesis on the user side (`IsMarkovKernel W`), so the definition itself
stays the bare `Kernel`.

The joint codomain `β₁ × β₂` (as opposed to a pair of independent kernels
`Kernel α β₁ × Kernel α β₂`) is essential: a broadcast channel is
mathematically a *joint* distribution `p(y₁, y₂ | x)`, not a product. The
**degraded** assumption `X → Y₁ → Y₂` (a Markov chain on the joint
distribution) is *not* embedded in this abbreviation — it surfaces only
inside the L-BC2 discharge (converse argument), so the type stays
shape-faithful to the general BC kernel and the degraded specialisation
appears as a per-theorem hypothesis on the caller side.

This shape is also the **dual** of the MAC kernel
`MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` from
`Common2026.Shannon.MultipleAccessChannel` — swapping domain ↔ codomain
(2-input × 1-output ↔ 1-input × 2-output) yields the BC kernel.

References: Cover–Thomas Ch.15.6. -/
abbrev BroadcastChannel (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] :=
  Kernel α (β₁ × β₂)

/-- A **BC block code** of length `n` carrying a message pair
`(m₁, m₂) ∈ Fin M₁ × Fin M₂`.

Three fields:

* `encoder : Fin M₁ × Fin M₂ → (Fin n → α)` — joint encoder generating the
  channel input sequence from the message pair (un-curry form, matching
  the operational shape of superposition coding `(U, X) ~ p(u) p(x|u)`).
* `decoder₁ : (Fin n → β₁) → Fin M₁` — good receiver's decoder, recovering
  the private message `m₁` from its channel output block.
* `decoder₂ : (Fin n → β₂) → Fin M₂` — poor receiver's decoder, recovering
  the common message `m₂` from its channel output block.

We bundle no measurability fields: on finite (or `MeasurableSingletonClass`)
alphabets all functions are automatically measurable, so requiring fields
would only force the caller to discharge `measurable_of_finite`
redundantly — matching the convention of `Code` and `MACCode`.

The two-separate-decoder shape (as opposed to a single joint decoder
`(Fin n → β₁ × β₂) → Fin M₁ × Fin M₂`) is essential to the operational
meaning of a broadcast channel: the two receivers are *physically
separate* and each decodes from its own channel output without access to
the other's observation. The L-BC1 (joint typicality) and L-BC3
(superposition-decoder existence) discharges both produce two-decoder
codes; threading a joint-decoder shape here would force an
operationally-meaningless coercion at the discharge layer.

Reference: Cover–Thomas Ch.15.6. -/
structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] where
  /-- Joint encoder, `Fin M₁ × Fin M₂ → (Fin n → α)` (un-curry form). -/
  encoder  : Fin M₁ × Fin M₂ → (Fin n → α)
  /-- Good receiver's decoder, recovering the private message `m₁`. -/
  decoder₁ : (Fin n → β₁) → Fin M₁
  /-- Poor receiver's decoder, recovering the common message `m₂`. -/
  decoder₂ : (Fin n → β₂) → Fin M₂

namespace BroadcastCode

variable {M₁ M₂ n : ℕ}

/-- The decoding region of receiver 1 for the private message `m₁`:
`{y : Fin n → β₁ | decoder₁ y = m₁}`. -/
def decodingRegion₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₁ : Fin M₁) :
    Set (Fin n → β₁) :=
  { y | c.decoder₁ y = m₁ }

/-- The decoding region of receiver 2 for the common message `m₂`:
`{y : Fin n → β₂ | decoder₂ y = m₂}`. -/
def decodingRegion₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₂ : Fin M₂) :
    Set (Fin n → β₂) :=
  { y | c.decoder₂ y = m₂ }

@[simp] lemma mem_decodingRegion₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (m₁ : Fin M₁) (y : Fin n → β₁) :
    y ∈ c.decodingRegion₁ m₁ ↔ c.decoder₁ y = m₁ := Iff.rfl

@[simp] lemma mem_decodingRegion₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (m₂ : Fin M₂) (y : Fin n → β₂) :
    y ∈ c.decodingRegion₂ m₂ ↔ c.decoder₂ y = m₂ := Iff.rfl

/-- The error event for receiver 1 at message `m₁`: complement of the
decoding region. -/
def errorEvent₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₁ : Fin M₁) :
    Set (Fin n → β₁) :=
  (c.decodingRegion₁ m₁)ᶜ

/-- The error event for receiver 2 at message `m₂`: complement of the
decoding region. -/
def errorEvent₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₂ : Fin M₂) :
    Set (Fin n → β₂) :=
  (c.decodingRegion₂ m₂)ᶜ

@[simp] lemma mem_errorEvent₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (m₁ : Fin M₁) (y : Fin n → β₁) :
    y ∈ c.errorEvent₁ m₁ ↔ c.decoder₁ y ≠ m₁ := by
  simp [errorEvent₁, decodingRegion₁]

@[simp] lemma mem_errorEvent₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (m₂ : Fin M₂) (y : Fin n → β₂) :
    y ∈ c.errorEvent₂ m₂ ↔ c.decoder₂ y ≠ m₂ := by
  simp [errorEvent₂, decodingRegion₂]

/-- Receiver 1's decoding regions are measurable on a
`MeasurableSingletonClass` output alphabet. -/
lemma measurableSet_decodingRegion₁
    [Fintype β₁] [MeasurableSingletonClass β₁]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₁ : Fin M₁) :
    MeasurableSet (c.decodingRegion₁ m₁) :=
  (Set.toFinite _).measurableSet

/-- Receiver 2's decoding regions are measurable on a
`MeasurableSingletonClass` output alphabet. -/
lemma measurableSet_decodingRegion₂
    [Fintype β₂] [MeasurableSingletonClass β₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₂ : Fin M₂) :
    MeasurableSet (c.decodingRegion₂ m₂) :=
  (Set.toFinite _).measurableSet

lemma measurableSet_errorEvent₁
    [Fintype β₁] [MeasurableSingletonClass β₁]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₁ : Fin M₁) :
    MeasurableSet (c.errorEvent₁ m₁) :=
  (c.measurableSet_decodingRegion₁ m₁).compl

lemma measurableSet_errorEvent₂
    [Fintype β₂] [MeasurableSingletonClass β₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₂ : Fin M₂) :
    MeasurableSet (c.errorEvent₂ m₂) :=
  (c.measurableSet_decodingRegion₂ m₂).compl

end BroadcastCode

end BCStructures

/-! ## Capacity region predicate (corner-point form) -/

section CapacityRegion

/-- **Degraded BC capacity region — corner-point form predicate**
(Cover–Thomas Ch.15.6, Theorem 15.6.2).

A rate pair `(R₁, R₂) : ℝ × ℝ` lies in the degraded BC capacity region
at the *corner point* defined by the cut rates `(I_u, I_xy)` — corresponding
to a choice of auxiliary RV `U` and superposition `(U, X)` — iff it
satisfies the two Cover–Thomas inequalities

```
R₂ ≤ I_u             -- = I(U;  Y₂)        common message  (poor receiver)
R₁ ≤ I_xy            -- = I(X;  Y₁ | U)    private message (good receiver)
```

This is the **single-auxiliary-RV** form. The full degraded BC capacity
region is the closure of the union of these corner points over all
auxiliary RVs `U` and joint pmf `p(u, x)` (Cover–Thomas §15.6.2,
Theorem 15.6.2) — that closure / convex hull is out of scope of the
present file (judgement L-BC5; the general BC requires multiple auxiliary
RVs and is partially open). Marton's inner bound + the Körner–Marton
outer bound for general (non-degraded) BCs are also fully out of scope
(see `bc-general-discharge-*`).

We package the two inequalities as a `Prop`-valued structure so that
projections (`bound_R₂_le_I_u`, `bound_R₁_le_I_xy`) are available as
field accessors — this is cleaner than a paired-`And` and matches the
style of `InMACCapacityRegion`. The equivalent `And` form is exposed via
`iff_and` for callers that prefer the unbundled shape.

Note that, unlike the MAC capacity region, the BC capacity region is
**not symmetric** under swapping the two receivers: receiver 1 is the
"good" receiver (high SNR end of the degraded chain `X → Y₁ → Y₂`) and
decodes `M₁ ⊕ M₂` worth of information, while receiver 2 is the "poor"
receiver and decodes only `M₂`. Accordingly no `swap` lemma is offered. -/
structure InBCCapacityRegion (R₁ R₂ I_u I_xy : ℝ) : Prop where
  /-- Common-message rate bound: `R₂ ≤ I(U; Y₂)`. -/
  bound_R₂_le_I_u  : R₂ ≤ I_u
  /-- Private-message rate bound: `R₁ ≤ I(X; Y₁ | U)`. -/
  bound_R₁_le_I_xy : R₁ ≤ I_xy

namespace InBCCapacityRegion

variable {R₁ R₂ I_u I_xy : ℝ}

/-- Introduction helper: combine the two inequalities into a region
membership. -/
lemma mk' (h₂ : R₂ ≤ I_u) (h₁ : R₁ ≤ I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy :=
  ⟨h₂, h₁⟩

/-- Equivalent paired-`And` form. Useful for callers that prefer an
unbundled hypothesis or want to destructure with `obtain ⟨h₂, h₁⟩`. -/
lemma iff_and :
    InBCCapacityRegion R₁ R₂ I_u I_xy ↔
      R₂ ≤ I_u ∧ R₁ ≤ I_xy := by
  refine ⟨fun h => ⟨h.bound_R₂_le_I_u, h.bound_R₁_le_I_xy⟩, ?_⟩
  rintro ⟨h₂, h₁⟩
  exact ⟨h₂, h₁⟩

/-- Monotonicity in the common-message cut rate: enlarging `I_u`
preserves region membership. -/
lemma mono_I_u {I_u' : ℝ}
    (h : InBCCapacityRegion R₁ R₂ I_u I_xy) (hI : I_u ≤ I_u') :
    InBCCapacityRegion R₁ R₂ I_u' I_xy :=
  ⟨h.bound_R₂_le_I_u.trans hI, h.bound_R₁_le_I_xy⟩

/-- Monotonicity in the private-message cut rate: enlarging `I_xy`
preserves region membership. -/
lemma mono_I_xy {I_xy' : ℝ}
    (h : InBCCapacityRegion R₁ R₂ I_u I_xy) (hI : I_xy ≤ I_xy') :
    InBCCapacityRegion R₁ R₂ I_u I_xy' :=
  ⟨h.bound_R₂_le_I_u, h.bound_R₁_le_I_xy.trans hI⟩

/-- Anti-monotonicity in the private-message rate: shrinking `R₁`
preserves region membership. -/
lemma anti_mono_R₁ {R₁' : ℝ}
    (h : InBCCapacityRegion R₁ R₂ I_u I_xy) (hR : R₁' ≤ R₁) :
    InBCCapacityRegion R₁' R₂ I_u I_xy :=
  ⟨h.bound_R₂_le_I_u, hR.trans h.bound_R₁_le_I_xy⟩

/-- Anti-monotonicity in the common-message rate: shrinking `R₂`
preserves region membership. -/
lemma anti_mono_R₂ {R₂' : ℝ}
    (h : InBCCapacityRegion R₁ R₂ I_u I_xy) (hR : R₂' ≤ R₂) :
    InBCCapacityRegion R₁ R₂' I_u I_xy :=
  ⟨hR.trans h.bound_R₂_le_I_u, h.bound_R₁_le_I_xy⟩

/-- The origin `(0, 0)` lies in every region with non-negative cut rates
(mutual information is `≥ 0`, so this is the usual hypothesis on the
caller side). -/
lemma zero_zero {I_u I_xy : ℝ}
    (h_u : 0 ≤ I_u) (h_xy : 0 ≤ I_xy) :
    InBCCapacityRegion 0 0 I_u I_xy :=
  ⟨h_u, h_xy⟩

end InBCCapacityRegion

end CapacityRegion

/-! ## Single-rate cut bounds (statement-level hypothesis pass-through) -/

section RateBounds

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **Common-message rate bound (hypothesis pass-through form, L-BC2
engaged)**.

For any BC block code `c` and rate `R₂`, the converse asserts

```
R₂ ≤ I(U; Y₂)        (= I_u)
```

after applying Fano's inequality on `(W₂, Y₂^n)`
(`n·R₂ ≤ I(W₂; Y₂^n) + n·ε_n`), the data-processing inequality
`I(W₂; Y₂^n) ≤ I(U^n; Y₂^n)` (after identifying `U := W₂` as the
auxiliary RV in the standard converse), and the per-letter chain rule
`I(U^n; Y₂^n) ≤ n · I(U; Y₂)`.

The multi-hundred-line ingredients — multi-user Fano (~150 lines) and the
per-letter chain rule (~150 lines), bundled as L-BC2 — are supplied as
`True` placeholders. The final scalar inequality is supplied as the
`h_bound` hypothesis. Discharge plan:
`bc-converse-fano-discharge-*`, `bc-converse-chain-rule-discharge-*`. -/
theorem bc_common_rate_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₂ I_u : ℝ)
    (_h_fano : True)
    (_h_chain : True)
    (h_bound : R₂ ≤ I_u) :
    R₂ ≤ I_u := h_bound

/-- **Private-message rate bound (hypothesis pass-through form, L-BC2
engaged)**.

For any BC block code `c` and rate `R₁`, the converse asserts

```
R₁ ≤ I(X; Y₁ | U)    (= I_xy)
```

after applying Fano's inequality on `(W₁, Y₁^n) | W₂`
(`n·R₁ ≤ I(W₁; Y₁^n | W₂) + n·ε_n`), the conditional data-processing
inequality `I(W₁; Y₁^n | W₂) ≤ I(X^n; Y₁^n | U^n)` (using the Markov
chain `W₁ → X^n → Y₁^n` conditioned on `U^n := W₂^n`), and the
per-letter conditional-MI chain rule
`I(X^n; Y₁^n | U^n) ≤ n · I(X; Y₁ | U)`. -/
theorem bc_private_rate_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ I_xy : ℝ)
    (_h_fano : True)
    (_h_chain : True)
    (h_bound : R₁ ≤ I_xy) :
    R₁ ≤ I_xy := h_bound

/-- **Region combine (two-bound to predicate)** — given the two cut bounds
`R₂ ≤ I_u`, `R₁ ≤ I_xy`, conclude
`InBCCapacityRegion R₁ R₂ I_u I_xy`.

Proof: direct `⟨_, _⟩` introduction of the predicate structure. -/
lemma bc_region_combine (R₁ R₂ I_u I_xy : ℝ)
    (h₂ : R₂ ≤ I_u) (h₁ : R₁ ≤ I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy :=
  ⟨h₂, h₁⟩

end RateBounds

/-! ## Outer bound: converse main theorem (Cover–Thomas 15.6.2, hypothesis pass-through) -/

section OuterBound

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **Degraded BC capacity region outer bound (Cover–Thomas Theorem 15.6.2,
converse, hypothesis pass-through form, L-BC2 + L-BC4 + L-BC5 all
engaged)**.

For any BC block code `c : BroadcastCode M₁ M₂ n α β₁ β₂` and rate pair
`(R₁, R₂)`, given the two cut rates `(I_u, I_xy) := (I(U;Y₂), I(X;Y₁|U))`
evaluated at the joint superposition input pmf `p(u) p(x|u)`, the
degraded BC converse asserts

```
InBCCapacityRegion R₁ R₂ I_u I_xy
  :↔  R₂ ≤ I_u  ∧  R₁ ≤ I_xy.
```

The theorem is published with the three hypothesis pass-through slots:

* `_h_fano : True` — multi-user Fano inequality (`n·R₂ ≤ I(W₂; Y₂^n) +
  n·ε_n`, `n·R₁ ≤ I(W₁; Y₁^n | W₂) + n·ε_n`) holds (L-BC2; discharge in
  `bc-converse-fano-discharge-*`).
* `_h_chain : True` — multi-user conditional-MI chain rule
  (`I(U^n; Y₂^n) ≤ ∑ I(U_i; Y_{2,i})` and `I(X^n; Y₁^n | U^n) ≤ ∑
  I(X_i; Y_{1,i} | U_i)`) holds (L-BC2; discharge in
  `bc-converse-chain-rule-discharge-*`).
* `h_rate_bound : InBCCapacityRegion …` — the composite two-inequality
  rate bound itself (L-BC4; discharge in
  `bc-converse-rate-bound-discharge-*`).

The auxiliary-RV closure / convex hull (full degraded BC region) is
fully scope-out (L-BC5); the present statement publishes the
corner-point form only, with `(I_u, I_xy) : ℝ × ℝ` evaluated externally
and supplied as arguments. The degradation assumption `X → Y₁ → Y₂`
(Markov chain on the joint output) is *not* embedded in this signature —
it surfaces only inside the L-BC2 discharge.

This signature mirrors the established statement-level hypothesis
pass-through pattern of `mac_capacity_region_outer_bound` (T3-B MAC,
Cover–Thomas Theorem 15.3.4), specifically the `_h_fano : True` /
`_h_chain : True` / `h_rate_bound` slots, reduced from three to two
inequalities. -/
theorem bc_capacity_region_outer_bound
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h_rate_bound : InBCCapacityRegion R₁ R₂ I_u I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy := h_rate_bound

/-- **Degraded BC capacity region outer bound — two-bound form**.

A more practical caller interface: instead of supplying the bundled
composite predicate `h_rate_bound`, supply the two cut-direction bounds
`h₂ : R₂ ≤ I_u`, `h₁ : R₁ ≤ I_xy` separately. The two are combined by
`bc_region_combine` to yield the region membership.

This form is the usual exit point of an n-letter Fano + chain-rule
argument that produces the two cut bounds as separate intermediates. -/
theorem bc_capacity_region_outer_bound_two_bounds
    {M₁ M₂ n : ℕ} (_hn : 0 < n)
    (_c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True)
    (h₂ : R₂ ≤ I_u) (h₁ : R₁ ≤ I_xy) :
    InBCCapacityRegion R₁ R₂ I_u I_xy :=
  bc_region_combine R₁ R₂ I_u I_xy h₂ h₁

/-- **Degraded BC capacity region outer bound — `Real.log` rate form**.

Specialisation of `bc_capacity_region_outer_bound` to the standard
`R_k := Real.log M_k / n` rate convention used throughout Cover–Thomas
(and matched by `mac_capacity_region_outer_bound_log_rate` /
`relay_cutset_outer_bound_log_rate`). -/
theorem bc_capacity_region_outer_bound_log_rate
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (I_u I_xy : ℝ)
    (h_fano : True) (h_chain : True)
    (h_rate_bound :
        InBCCapacityRegion
          (Real.log (M₁ : ℝ) / (n : ℝ))
          (Real.log (M₂ : ℝ) / (n : ℝ))
          I_u I_xy) :
    InBCCapacityRegion
        (Real.log (M₁ : ℝ) / (n : ℝ))
        (Real.log (M₂ : ℝ) / (n : ℝ))
        I_u I_xy :=
  bc_capacity_region_outer_bound hn c _ _ I_u I_xy h_fano h_chain h_rate_bound

end OuterBound

/-! ## Inner bound: achievability main theorem (Cover–Thomas 15.6.2, hypothesis pass-through) -/

section InnerBound

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- The "existence" claim for the degraded BC inner bound: there exists a
threshold block length `N` beyond which one can find codes carrying at
least `⌈exp(n R_k)⌉` messages in each rate direction.

The error-probability bound (average error `< ε` for any prescribed
`ε > 0`) is **not** embedded into this existence claim — it is supplied
on the caller side together with `h_existence` (and discharged in
`bc-joint-typicality-discharge-*` / `bc-superposition-decoder-discharge-*`).
This matches the convention of `MACInnerBoundExistence` and
`wyner_ziv_achievability_existence`. -/
def BCInnerBoundExistence
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M₁ M₂ : ℕ) (_c : BroadcastCode M₁ M₂ n α β₁ β₂),
      Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
      ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)

/-- **Degraded BC capacity region inner bound (Cover–Thomas Theorem
15.6.2, achievability, hypothesis pass-through form, L-BC1 + L-BC3 +
L-BC5 all engaged)**.

If the rate pair `(R₁, R₂)` satisfies both Cover–Thomas inequalities
*strictly* — i.e. `R₂ < I_u`, `R₁ < I_xy` (an `InBCCapacityRegion`-shaped
predicate with strict inequalities, which we receive as the unbundled
`_h_strict` pair) — then for every `n` sufficiently large there exist
`M_k ≥ ⌈exp(n R_k)⌉` and a BC block code `c : BroadcastCode M₁ M₂ n α β₁
β₂` produced by **superposition coding**: an outer codebook for `U`
(common message) layered with conditional inner codebooks for `X | U`
(private message).

The theorem is published with the hypothesis pass-through slots:

* `_h_strict` — the two strict inequalities (mirror of
  `InBCCapacityRegion` with `<` in place of `≤`; supplied unbundled as
  an `And` pair to match the usual call site shape).
* `_h_joint_typ : True` — multi-receiver joint typicality body (4 error
  events per receiver + Bonferroni union bound + AEP-by-counting,
  ~500-800 lines) holds (L-BC1; discharge in
  `bc-joint-typicality-discharge-*`).
* `h_existence : BCInnerBoundExistence …` — the existence statement
  itself (L-BC3; discharge in
  `bc-superposition-decoder-discharge-*`).

The error-probability bound (average error `< ε` for any prescribed
`ε > 0`) is **not** embedded into the existence statement — it is
supplied on the caller side together with `h_existence`. This matches
the convention of `mac_capacity_region_inner_bound` (T3-B MAC,
Cover–Thomas Theorem 15.3.6) and `wyner_ziv_achievability_existence`
(T3-D Wyner–Ziv, Cover–Thomas Theorem 15.9.2). -/
theorem bc_capacity_region_inner_bound
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (_h_joint_typ : True)
    (h_existence : BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  h_existence

/-- **Degraded BC capacity region inner bound — bundled-strict form**.

Variant of `bc_capacity_region_inner_bound` taking the strict inequalities
bundled as a single `InBCCapacityRegion`-shaped predicate whose
hypotheses use `<` rather than `≤`. We expose this `<`-bundled form by
*receiving* an `InBCCapacityRegion` together with the side-conditions
that neither of the two inequalities is saturated.

In practice callers usually supply the unbundled `And` pair via
`bc_capacity_region_inner_bound`; this variant is offered for symmetry
with `bc_capacity_region_outer_bound`. -/
theorem bc_capacity_region_inner_bound_bundled_strict
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_in_region : InBCCapacityRegion R₁ R₂ I_u I_xy)
    (_h_strict₂ : R₂ ≠ I_u)
    (_h_strict₁ : R₁ ≠ I_xy)
    (_h_joint_typ : True)
    (h_existence : BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  h_existence

end InnerBound

/-! ## Two-side combine and log-rate wrappers -/

section TwoSide

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **Degraded BC capacity region — two-side combine (achievability +
converse)**.

If a rate pair `(R₁, R₂)` is shown both to be achievable (existence form,
inner bound) **and** to lie in the corner-point predicate region (outer
bound), then we package the two facts together as the `And` of the two
publish-layer conclusions.

This is a thin wrapper packaging the simultaneous validity of both
hypothesis pass-through forms; it does not derive new information, but
matches the two-side packaging pattern of `mac_capacity_region_consistent`
(T3-B MAC) for callers that want a single entry point.

Both `_h_fano`, `_h_chain`, `_h_joint_typ` placeholders for the underlying
multi-hundred-line discharges (L-BC1 + L-BC2) are forwarded transparently
to the two main theorems via `trivial`. -/
theorem bc_capacity_region_consistent
    {M₁ M₂ n : ℕ} (hn : 0 < n)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_fano : True) (_h_chain : True) (_h_joint_typ : True)
    (h_rate_bound : InBCCapacityRegion R₁ R₂ I_u I_xy)
    (h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (h_existence : BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    InBCCapacityRegion R₁ R₂ I_u I_xy
      ∧ BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  ⟨bc_capacity_region_outer_bound hn c R₁ R₂ I_u I_xy trivial trivial h_rate_bound,
   bc_capacity_region_inner_bound (α := α) (β₁ := β₁) (β₂ := β₂)
     R₁ R₂ I_u I_xy h_strict trivial h_existence⟩

end TwoSide

end InformationTheory.Shannon
