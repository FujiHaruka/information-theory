import Common2026.Shannon.RelayCutset

/-!
# Relay Channel Inner Bound — Decode-and-Forward / Compress-and-Forward (T3-F)

Cover–Thomas Theorems 15.10.2 (DF) and 15.10.3 (CF) — the two classical
inner bounds for the relay channel introduced in Ch.15.10.

The relay channel `W : Kernel (α × α₁) (β × β₁)` is the one published in
`Common2026.Shannon.RelayCutset` (T3-F outer bound). The companion seed
publishes the cut-set **outer bound**
`min { I(X, X₁; Y), I(X; Y, Y₁ | X₁) }`; the present file publishes the
two main **inner bounds**.

```
[DF inner bound, Cover–Thomas (15.232)]
  R ≤ min { I(X; Y₁ | X₁) + I(X₁; Y),  I(X, X₁; Y) }

[CF inner bound, Cover–Thomas (15.243)]
  R ≤ I(X; Ŷ₁, Y | X₁)
  s.t.  I(X₁; Y) ≥ I(Y₁; Ŷ₁ | X₁, Y)
```

## File layout

This single file publishes:

* `InRelayDFRate R Imrh Iry Ibroad` — decode-and-forward rate region
  predicate, bundling the two DF inequalities at given scalar cut rates
  `(Imrh, Iry, Ibroad) := (I(X; Y₁|X₁), I(X₁; Y), I(X, X₁; Y))`.
* `InRelayCFRate R Idec Ix1y Iy1hy1` — compress-and-forward rate region
  predicate, bundling the CF rate bound and the compression feasibility
  constraint at scalar values `(Idec, Ix1y, Iy1hy1) :=
  (I(X; Ŷ₁, Y | X₁), I(X₁; Y), I(Y₁; Ŷ₁ | X₁, Y))`.
* `RelayDFInnerBoundExistence W R`, `RelayCFInnerBoundExistence W R` —
  achievability existence forms, the single-rate analogues of
  `MACInnerBoundExistence`. **Error-carrying**: each embeds
  `(c.averageErrorProb W x₁Ref).toReal < ε` for every `ε > 0`, so the
  predicate is unsatisfiable by an arbitrary code at an arbitrary rate.
* `RelayDFAchievable`, `RelayCFAchievable` — gated achievability
  implications `(rate-region) → existence`. Retained as the
  bookkeeping predicates documenting which Mathlib walls discharge each
  inner bound; their hypothesis-form consumers below have been
  sorry-migrated (see Phase 2.2 of `relay-sorry-migration-plan`).
* `relay_df_inner_bound` — Cover–Thomas Theorem 15.10.2 main theorem.
  Currently `sorry` (load-bearing achievability hypothesis removed);
  closure tracked on `relay-inner-bound-moonshot-plan` (L-RI1/L-RI2 walls).
* `relay_cf_inner_bound` — Cover–Thomas Theorem 15.10.3 main theorem.
  Currently `sorry` (load-bearing achievability hypothesis removed);
  closure tracked on `relay-inner-bound-moonshot-plan` (L-RI3/L-RI4 walls).

The signatures mirror the **honest-conditional pass-through** of
`mac_capacity_region_inner_bound` (T3-B MAC) /
`bc_capacity_region_inner_bound` (T3-C BC), which are the direct templates
for the present file — the only differences are (a) single rate `R` in place
of the `(R₁, R₂)` pair, (b) `RelayCode` in place of `MACCode`/`BroadcastCode`,
and (c) DF/CF-specific rate region predicates.

## De-circularization status (2026-05-21)

Both inner headlines were previously circular (`relay_df_inner_bound
:= h_existence`, `relay_cf_inner_bound := h_existence`, with the real
residual hidden in `_h_… : True` slots and the existence predicate omitting
any error content — the same red herring as the BC inner pipeline: an
existence claim with no `averageErrorProb` link is satisfiable by *any* code
at *any* rate). They are now **sound landings**:

* the existence predicates are redefined to **carry**
  `(c.averageErrorProb W x₁Ref).toReal < ε` (∀ ε > 0), so they genuinely
  capture achievability;
* the headlines consume the honest open residuals `RelayDFAchievable` /
  `RelayCFAchievable` (gated implications `(rate-region) → existence`, real
  `Prop`s ≠ the conclusion) and **derive** the conclusion by `modus ponens`;
* the downstream rate-only discharge layers
  (`RelayInnerBodyDischarge` / `RelayDFBlockMarkovBody` /
  `RelayCFBinningBody`), which previously *constructed* the bare existence
  from degenerate constant codes (the rate-only → achievability leap), now
  genuinely conclude only the **rate witnesses** they prove and no longer
  leap to the error-carrying achievability.

## Scope

This file publishes both inner bounds in **scalar form** (the three
relevant scalar cut rates for DF and the three for CF are taken as
real arguments; their evaluation from a joint input pmf and channel
kernel is consumed on the caller side). The outer maximisation over the
joint auxiliary distribution `p(x, x₁, ŷ₁)` is consumed on the caller
side; the body of the file is free of `IsCompact + exists_isMaxOn`
plumbing on the joint simplex.

## 撤退ライン (honest open residuals, NOT `True`)

The genuine information-theoretic cores remain real Mathlib gaps, but each
is now an honest open `Prop` (the gated implication `(rate-region) →
error-carrying existence`), **not** a `True` placeholder and **not** the
conclusion:

* **L-RI1 + L-RI2 (DF)**: block-Markov encoding + sliding-window joint
  typicality decoder are bundled into `RelayDFAchievable`.
* **L-RI3 + L-RI4 (CF)**: Wyner–Ziv binning + side-information decoding are
  bundled into `RelayCFAchievable`.

Discharge of each residual is performed in companion seeds:

* `relay-df-block-markov-discharge-*`
* `relay-df-sliding-window-discharge-*`
* `relay-cf-wz-binning-discharge-*`
* `relay-cf-si-decode-discharge-*`
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## DF rate region predicate (Cover–Thomas (15.232) form) -/

section DFRateRegion

/-- **Decode-and-Forward rate region — corner-point predicate**
(Cover–Thomas Ch.15.10, Theorem 15.10.2, eq. (15.232)).

A rate `R : ℝ` lies in the DF rate region at the corner point defined
by the three scalar cut rates `(Imrh, Iry, Ibroad)` iff it satisfies
both DF inequalities

```
R ≤ Imrh + Iry   -- = I(X; Y₁ | X₁) + I(X₁; Y)
R ≤ Ibroad       -- = I(X, X₁; Y)
```

The textbook form

```
R ≤ min { I(X; Y₁ | X₁) + I(X₁; Y),  I(X, X₁; Y) }
```

is recovered by `min_le_iff`: the two field projections combined with
`le_min` are equivalent to the single `min` bound. We bundle the two
inequalities as a `Prop`-valued structure so that the field accessors
`boundMAC`, `boundBroad` are available; the equivalent unbundled `And`
form is exposed via `iff_and`.

This is the single-rate analogue of `InMACCapacityRegion`
(T3-B MAC) — the MAC's three inequalities collapse to DF's two when the
relay channel is reduced to its MAC sub-channel direction.

The full DF inner bound is the closure of the union of these corner
points over all joint input pmfs `p(x, x₁)`; the convex hull /
time-sharing is consumed on the caller side. -/
structure InRelayDFRate (R Imrh Iry Ibroad : ℝ) : Prop where
  /-- DF "MAC-cut" bound: `R ≤ I(X; Y₁ | X₁) + I(X₁; Y)`. -/
  boundMAC   : R ≤ Imrh + Iry
  /-- DF "broadcast-cut" bound: `R ≤ I(X, X₁; Y)`. -/
  boundBroad : R ≤ Ibroad

namespace InRelayDFRate

variable {R Imrh Iry Ibroad : ℝ}

/-- Introduction helper: combine the two DF inequalities into a region
membership. -/
lemma mk' (h₁ : R ≤ Imrh + Iry) (h₂ : R ≤ Ibroad) :
    InRelayDFRate R Imrh Iry Ibroad :=
  ⟨h₁, h₂⟩

/-- Equivalent unbundled `And` form. Useful for callers that prefer to
destructure with `obtain ⟨h₁, h₂⟩`. -/
lemma iff_and :
    InRelayDFRate R Imrh Iry Ibroad ↔
      R ≤ Imrh + Iry ∧ R ≤ Ibroad :=
  ⟨fun h => ⟨h.boundMAC, h.boundBroad⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-- Equivalent `min`-form: `InRelayDFRate` iff `R ≤ min { Imrh + Iry, Ibroad }`.
Bridge to the textbook form `R ≤ min { I(X; Y₁ | X₁) + I(X₁; Y), I(X, X₁; Y) }`. -/
lemma iff_le_min :
    InRelayDFRate R Imrh Iry Ibroad ↔
      R ≤ min (Imrh + Iry) Ibroad := by
  refine ⟨fun h => le_min h.boundMAC h.boundBroad, fun h => ⟨?_, ?_⟩⟩
  · exact h.trans (min_le_left _ _)
  · exact h.trans (min_le_right _ _)

/-- Monotonicity in `Imrh` (enlarging shifts the region outward). -/
lemma mono_Imrh {Imrh' : ℝ}
    (h : InRelayDFRate R Imrh Iry Ibroad) (hI : Imrh ≤ Imrh') :
    InRelayDFRate R Imrh' Iry Ibroad := by
  refine ⟨h.boundMAC.trans ?_, h.boundBroad⟩
  linarith

/-- Monotonicity in `Iry`. -/
lemma mono_Iry {Iry' : ℝ}
    (h : InRelayDFRate R Imrh Iry Ibroad) (hI : Iry ≤ Iry') :
    InRelayDFRate R Imrh Iry' Ibroad := by
  refine ⟨h.boundMAC.trans ?_, h.boundBroad⟩
  linarith

/-- Monotonicity in `Ibroad`. -/
lemma mono_Ibroad {Ibroad' : ℝ}
    (h : InRelayDFRate R Imrh Iry Ibroad) (hI : Ibroad ≤ Ibroad') :
    InRelayDFRate R Imrh Iry Ibroad' :=
  ⟨h.boundMAC, h.boundBroad.trans hI⟩

/-- Anti-monotonicity in the rate `R`: shrinking `R` preserves
membership. -/
lemma anti_mono_R {R' : ℝ}
    (h : InRelayDFRate R Imrh Iry Ibroad) (hR : R' ≤ R) :
    InRelayDFRate R' Imrh Iry Ibroad :=
  ⟨hR.trans h.boundMAC, hR.trans h.boundBroad⟩

/-- The origin `R = 0` lies in every region with non-negative cut rates
(`I(·;·) ≥ 0` is the usual caller-side hypothesis). -/
lemma zero {Imrh Iry Ibroad : ℝ}
    (h₁ : 0 ≤ Imrh + Iry) (h₂ : 0 ≤ Ibroad) :
    InRelayDFRate 0 Imrh Iry Ibroad :=
  ⟨h₁, h₂⟩

end InRelayDFRate

end DFRateRegion

/-! ## CF rate region predicate (Cover–Thomas (15.243) form) -/

section CFRateRegion

/-- **Compress-and-Forward rate region — corner-point predicate**
(Cover–Thomas Ch.15.10, Theorem 15.10.3, eq. (15.243)).

A rate `R : ℝ` lies in the CF rate region at the corner point defined
by the three scalar quantities `(Idec, Ix1y, Iy1hy1)` iff it satisfies
both CF conditions

```
R ≤ Idec            -- = I(X; Ŷ₁, Y | X₁)
Iy1hy1 ≤ Ix1y       -- compression feasibility: I(Y₁; Ŷ₁ | X₁, Y) ≤ I(X₁; Y)
```

Note that the compression-feasibility condition does **not** involve
`R` directly; it is a condition on the auxiliary `Ŷ₁` that has to hold
for the CF scheme to be realisable. We bundle both into the same
predicate because both must hold at the chosen corner point.

The full CF inner bound is the closure of the union of these corner
points over all joint input pmfs `p(x, x₁) p(ŷ₁ | y₁, x₁)`; the convex
hull / time-sharing is consumed on the caller side. -/
structure InRelayCFRate (R Idec Ix1y Iy1hy1 : ℝ) : Prop where
  /-- CF rate bound: `R ≤ I(X; Ŷ₁, Y | X₁)`. -/
  rateBound       : R ≤ Idec
  /-- Compression feasibility: `I(Y₁; Ŷ₁ | X₁, Y) ≤ I(X₁; Y)`. -/
  compressionFeas : Iy1hy1 ≤ Ix1y

namespace InRelayCFRate

variable {R Idec Ix1y Iy1hy1 : ℝ}

/-- Introduction helper. -/
lemma mk' (h₁ : R ≤ Idec) (h₂ : Iy1hy1 ≤ Ix1y) :
    InRelayCFRate R Idec Ix1y Iy1hy1 :=
  ⟨h₁, h₂⟩

/-- Equivalent unbundled `And` form. -/
lemma iff_and :
    InRelayCFRate R Idec Ix1y Iy1hy1 ↔
      R ≤ Idec ∧ Iy1hy1 ≤ Ix1y :=
  ⟨fun h => ⟨h.rateBound, h.compressionFeas⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-- Monotonicity in the decoding mutual information `Idec`. -/
lemma mono_Idec {Idec' : ℝ}
    (h : InRelayCFRate R Idec Ix1y Iy1hy1) (hI : Idec ≤ Idec') :
    InRelayCFRate R Idec' Ix1y Iy1hy1 :=
  ⟨h.rateBound.trans hI, h.compressionFeas⟩

/-- Monotonicity in the channel-to-receiver MI `Ix1y` (enlarging
loosens the compression feasibility). -/
lemma mono_Ix1y {Ix1y' : ℝ}
    (h : InRelayCFRate R Idec Ix1y Iy1hy1) (hI : Ix1y ≤ Ix1y') :
    InRelayCFRate R Idec Ix1y' Iy1hy1 :=
  ⟨h.rateBound, h.compressionFeas.trans hI⟩

/-- Anti-monotonicity in the rate `R`. -/
lemma anti_mono_R {R' : ℝ}
    (h : InRelayCFRate R Idec Ix1y Iy1hy1) (hR : R' ≤ R) :
    InRelayCFRate R' Idec Ix1y Iy1hy1 :=
  ⟨hR.trans h.rateBound, h.compressionFeas⟩

/-- Anti-monotonicity in the compression auxiliary MI `Iy1hy1`
(shrinking makes compression feasibility easier). -/
lemma anti_mono_Iy1hy1 {Iy1hy1' : ℝ}
    (h : InRelayCFRate R Idec Ix1y Iy1hy1) (hI : Iy1hy1' ≤ Iy1hy1) :
    InRelayCFRate R Idec Ix1y Iy1hy1' :=
  ⟨h.rateBound, hI.trans h.compressionFeas⟩

/-- The origin `R = 0` lies in every region with non-negative `Idec`
and a feasible compression auxiliary. -/
lemma zero {Idec Ix1y Iy1hy1 : ℝ}
    (h₁ : 0 ≤ Idec) (h₂ : Iy1hy1 ≤ Ix1y) :
    InRelayCFRate 0 Idec Ix1y Iy1hy1 :=
  ⟨h₁, h₂⟩

end InRelayCFRate

end CFRateRegion

/-! ## Existence forms (single-rate analogue of `MACInnerBoundExistence`) -/

section ExistenceForms

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- The **achievability** claim for the **decode-and-forward** inner bound
(Cover–Thomas Theorem 15.10.2, achievability side): for **every**
prescribed average error tolerance `ε > 0`, there exists a threshold block
length `N` beyond which one can find a relay block code carrying at least
`⌈exp(n R)⌉` messages **and with average error probability `< ε`** (under
the relay channel `W`, with the relay transmitting the reference input
sequence `x₁Ref`).

The vanishing-error conjunct `(c.averageErrorProb W x₁Ref).toReal < ε` is
now **embedded** in the predicate (it was previously dropped, which made the
bare predicate satisfiable by *any* code at *any* rate — the no-op trap, the
same red herring as the BC inner pipeline). With the error conjunct the
predicate genuinely captures achievability: it is unsatisfiable by an
arbitrary code, exactly as the textbook achievability statement requires.
This mirrors the redefined `MACInnerBoundExistence` (T3-B MAC) /
`BCInnerBoundExistence` (T3-C BC). -/
def RelayDFInnerBoundExistence
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (c : RelayCode M n α α₁ β β₁) (x₁Ref : Fin n → α₁),
        Real.exp ((n : ℝ) * R) ≤ (M : ℝ)
        ∧ (c.averageErrorProb W x₁Ref).toReal < ε

/-- The **achievability** claim for the **compress-and-forward** inner bound
(Cover–Thomas Theorem 15.10.3, achievability side). Same shape as
`RelayDFInnerBoundExistence`: it carries the embedded vanishing-error
conjunct `(c.averageErrorProb W x₁Ref).toReal < ε`. The structural
difference between the DF and CF achievability proofs lives entirely in the
discharge of the achievability residual, not in the published existence
form. -/
def RelayCFInnerBoundExistence
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (c : RelayCode M n α α₁ β β₁) (x₁Ref : Fin n → α₁),
        Real.exp ((n : ℝ) * R) ≤ (M : ℝ)
        ∧ (c.averageErrorProb W x₁Ref).toReal < ε

/-- Anti-monotonicity of the DF existence form in the rate: a code that
achieves the larger rate `R` (with the embedded error bound) also achieves
any smaller rate `R' ≤ R`, because `Real.exp (n * R') ≤ Real.exp (n * R) ≤ M`
and the error conjunct is rate-independent so it survives unchanged. -/
lemma RelayDFInnerBoundExistence.anti_mono
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {W : RelayChannel α α₁ β β₁} {R R' : ℝ}
    (h : RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R)
    (hR : R' ≤ R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, x₁Ref, hM, hErr⟩ := hN n hn
  refine ⟨M, c, x₁Ref, ?_, hErr⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : (n : ℝ) * R' ≤ (n : ℝ) * R := mul_le_mul_of_nonneg_left hR hn0
  have hexp : Real.exp ((n : ℝ) * R') ≤ Real.exp ((n : ℝ) * R) :=
    Real.exp_le_exp.mpr hmul
  exact hexp.trans hM

/-- Anti-monotonicity of the CF existence form in the rate (same proof
shape as the DF version). -/
lemma RelayCFInnerBoundExistence.anti_mono
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {W : RelayChannel α α₁ β β₁} {R R' : ℝ}
    (h : RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R)
    (hR : R' ≤ R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, x₁Ref, hM, hErr⟩ := hN n hn
  refine ⟨M, c, x₁Ref, ?_, hErr⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : (n : ℝ) * R' ≤ (n : ℝ) * R := mul_le_mul_of_nonneg_left hR hn0
  have hexp : Real.exp ((n : ℝ) * R') ≤ Real.exp ((n : ℝ) * R) :=
    Real.exp_le_exp.mpr hmul
  exact hexp.trans hM

/-- **DF achievability — load-bearing predicate (retract candidate).**

The genuine block-Markov / random-coding / sliding-window joint-typicality
core of DF achievability (per-block random codebook + staged cooperation +
error-event collapse) is a real Mathlib gap (0 typicality lemmas in
Mathlib). Originally exposed as the honest open hypothesis
`RelayDFAchievable`: the **implication**
`(DF rate-region membership) → RelayDFInnerBoundExistence`, gated on
`InRelayDFRate R Imrh Iry Ibroad`.

All hypothesis-form consumers in this family have been sorry-migrated
(Phase 2.2 + 2.3 + 2.5). The predicate itself is retained for
documentation + for the alias `IsRelayDFBlockMarkovWitness`
(`RelayInnerBodyDischarge.lean:143`); both are deprecation candidates
once the L-RI1 + L-RI2 walls are closed by the companion seeds
`relay-df-block-markov-discharge-*` / `relay-df-sliding-window-discharge-*`.

`@audit:retract-candidate(load-bearing-predicate)` -/
def RelayDFAchievable
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁) (R Imrh Iry Ibroad : ℝ) : Prop :=
  InRelayDFRate R Imrh Iry Ibroad →
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R

/-- **CF achievability — load-bearing predicate (retract candidate).**

The genuine Wyner–Ziv compression binning / side-information decoding core
of CF achievability is a real Mathlib gap. Originally exposed as the
honest open hypothesis `RelayCFAchievable`: the **implication**
`(CF rate-region membership) → RelayCFInnerBoundExistence`, gated on
`InRelayCFRate R Idec Ix1y Iy1hy1`.

All hypothesis-form consumers in this family have been sorry-migrated
(Phase 2.2 + 2.3 + 2.5). The predicate itself is retained for
documentation + for the alias `IsRelayCFBinningWitness`
(`RelayInnerBodyDischarge.lean:333`); both are deprecation candidates
once the L-RI3 + L-RI4 walls are closed by the companion seeds
`relay-cf-wz-binning-discharge-*` / `relay-cf-si-decode-discharge-*`.

`@audit:retract-candidate(load-bearing-predicate)` -/
def RelayCFAchievable
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁) (R Idec Ix1y Iy1hy1 : ℝ) : Prop :=
  InRelayCFRate R Idec Ix1y Iy1hy1 →
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R

end ExistenceForms

/-! ## DF inner bound main theorem (Cover–Thomas Theorem 15.10.2) -/

section DFInnerBound

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay decode-and-forward inner bound (Cover–Thomas Theorem 15.10.2,
achievability side)** — load-bearing block-Markov / typicality wall, sorry.

If a rate `R : ℝ` lies in the DF rate region — i.e. it satisfies the two
Cover–Thomas inequalities

```
R ≤ I(X; Y₁ | X₁) + I(X₁; Y)
R ≤ I(X, X₁; Y)
```

bundled as `InRelayDFRate R Imrh Iry Ibroad` — then it is achievable: for
every error tolerance `ε > 0`, for all sufficiently large `n` there exist
`M ≥ ⌈exp(n R)⌉` and a relay block code with average error `< ε`
(`RelayDFInnerBoundExistence W R`).

The previous public signature also took an honest open IT residual
`h_ach : RelayDFAchievable W R Imrh Iry Ibroad` — the gated implication
`(rate-region) → RelayDFInnerBoundExistence`. That hypothesis bundled the
block-Markov random coding + sliding-window joint typicality decoder
(L-RI1 + L-RI2 Mathlib walls). Under the sorry-based migration that
load-bearing predicate has been removed; closure responsibility is
parked on the parent moonshot plan.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

/-- **DF inner bound — `min`-form variant**.

Variant of `relay_df_inner_bound` taking the rate-region hypothesis in the
**`min`** form

```
R ≤ min { Imrh + Iry,  Ibroad }
```

directly, rather than as a bundled `InRelayDFRate`. The `min` form is the
textbook form (Cover–Thomas (15.232)) and is typically how the inner bound
is stated in the literature.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_min_form
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h_min : R ≤ min (Imrh + Iry) Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

/-- **DF inner bound — unbundled two-inequality form**.

Variant taking the two DF inequalities separately rather than bundled as a
single `InRelayDFRate`. This is the usual exit point of an n-letter joint
typicality argument that produces the two bounds as separate intermediates.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_two_bounds
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h₁ : R ≤ Imrh + Iry) (h₂ : R ≤ Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

/-- **DF inner bound — `Real.log` rate form**.

Specialisation of `relay_df_inner_bound` to the standard
`R := Real.log M / n` rate convention used throughout Cover–Thomas.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_log_rate
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (_hn : 0 < n)
    (Imrh Iry Ibroad : ℝ)
    (h_in_df_region :
        InRelayDFRate (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        W (Real.log (M : ℝ) / (n : ℝ)) := by
  sorry

end DFInnerBound

/-! ## CF inner bound main theorem (Cover–Thomas Theorem 15.10.3) -/

section CFInnerBound

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay compress-and-forward inner bound (Cover–Thomas Theorem 15.10.3,
achievability side)** — load-bearing Wyner–Ziv binning / SI decode wall, sorry.

If a rate `R : ℝ` lies in the CF rate region — i.e. it satisfies the CF rate
bound and the compression feasibility constraint

```
R ≤ I(X; Ŷ₁, Y | X₁)
I(Y₁; Ŷ₁ | X₁, Y) ≤ I(X₁; Y)
```

bundled as `InRelayCFRate R Idec Ix1y Iy1hy1` — then it is achievable: for
every error tolerance `ε > 0`, for all sufficiently large `n` there exist
`M ≥ ⌈exp(n R)⌉` and a relay block code with average error `< ε`
(`RelayCFInnerBoundExistence W R`).

The previous public signature also took an honest open IT residual
`h_ach : RelayCFAchievable W R Idec Ix1y Iy1hy1` — the gated implication
`(rate-region) → RelayCFInnerBoundExistence`. That hypothesis bundled the
Wyner–Ziv binning + side-information decoder (L-RI3 + L-RI4 Mathlib
walls). Under the sorry-based migration that load-bearing predicate has
been removed; closure responsibility is parked on the parent moonshot
plan.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

/-- **CF inner bound — unbundled two-condition form**.

Variant taking the rate bound and the compression feasibility as separate
hypotheses rather than bundled.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_two_conditions
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_rate : R ≤ Idec) (h_feas : Iy1hy1 ≤ Ix1y) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

/-- **CF inner bound — `Real.log` rate form**.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_log_rate
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (_hn : 0 < n)
    (Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region :
        InRelayCFRate (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        W (Real.log (M : ℝ) / (n : ℝ)) := by
  sorry

end CFInnerBound

/-! ## Two-side combine (outer + inner) wrappers -/

section TwoSide

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay channel — DF achievability + cut-set outer bound combined**.

Packages the two landings together: the cut-set outer bound
`R ≤ relayCutsetBound (Ib+ε) (Im+ε)` and the error-carrying
`RelayDFInnerBoundExistence W R`. The previous public signature also
took two load-bearing Csiszár chain hypotheses (`h_chain_b` /
`h_chain_m`) bundling L-RC1/L-RC2 plus an honest DF achievability
residual `h_ach : RelayDFAchievable …` bundling L-RI1/L-RI2; both have
been removed under the sorry-based migration.

The compound conclusion is closed jointly by **two** moonshot plans
(`relay-cutset-moonshot-plan` for the outer-bound conjunct and
`relay-inner-bound-moonshot-plan` for the achievability conjunct); the
single `@residual` tag below names the inner-bound plan as the primary
closure target (consistent with the upstream `relay_df_inner_bound`),
with the outer-bound conjunct closed transitively by
`relay_cutset_outer_bound` (`@residual(plan:relay-cutset-moonshot-plan)`).

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_df_consistent
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Imrh Iry Ibroad Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (_h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)
    (_h_fano_m : RelayMacCutFano M n R Pe I_marg_m)
    (_h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (_h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad) :
    (R ≤ relayCutsetBound (Ib + ε) (Im + ε))
      ∧ RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

/-- **Relay channel — CF achievability + cut-set outer bound combined**.

Package the simultaneous validity of the CF inner bound (error-carrying
existence form) and the cut-set outer bound at the same rate `R`. Same
structural retreat as `relay_df_consistent`: both load-bearing chain
hypotheses (cutset side) and the CF achievability residual `h_ach` have
been removed under the sorry-based migration.

The compound conclusion is closed jointly by **two** moonshot plans
(`relay-cutset-moonshot-plan` for the outer-bound conjunct and
`relay-inner-bound-moonshot-plan` for the achievability conjunct); the
single `@residual` tag below names the inner-bound plan as the primary
closure target, with the outer-bound conjunct closed transitively by
`relay_cutset_outer_bound` (`@residual(plan:relay-cutset-moonshot-plan)`).

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_consistent
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (_hn : 0 < n)
    (_c : RelayCode M n α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (_h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)
    (_h_fano_m : RelayMacCutFano M n R Pe I_marg_m)
    (_h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (_h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1) :
    (R ≤ relayCutsetBound (Ib + ε) (Im + ε))
      ∧ RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

end TwoSide

end InformationTheory.Shannon
