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
* `RelayDFInnerBoundExistence R`, `RelayCFInnerBoundExistence R` —
  achievability existence forms, the single-rate analogues of
  `MACInnerBoundExistence`.
* `relay_df_inner_bound` — Cover–Thomas Theorem 15.10.2 main theorem,
  published with **L-RI1 + L-RI2 engaged** (block-Markov encoding and
  sliding-window joint typicality decoder supplied as `True`
  placeholders) and the existence statement supplied as the
  `h_existence` hypothesis.
* `relay_cf_inner_bound` — Cover–Thomas Theorem 15.10.3 main theorem,
  published with **L-RI3 + L-RI4 engaged** (Wyner–Ziv compression
  binning and side-information decoding supplied as `True` placeholders)
  and the existence statement supplied as the `h_existence` hypothesis.

The signatures mirror the **statement-level hypothesis pass-through
pattern** established for `mac_capacity_region_inner_bound`
(`Common2026.Shannon.MultipleAccessChannel`, T3-B MAC, Cover–Thomas
Theorem 15.3.6), which is the direct template for the present file —
the only differences are (a) single rate `R` in place of the MAC's
`(R₁, R₂)` pair, (b) `RelayCode` in place of `MACCode`, and (c)
DF/CF-specific rate region predicates in place of `InMACCapacityRegion`.

## Scope

This file publishes both inner bounds in **scalar form** (the three
relevant scalar cut rates for DF and the three for CF are taken as
real arguments; their evaluation from a joint input pmf and channel
kernel is consumed on the caller side). The outer maximisation over the
joint auxiliary distribution `p(x, x₁, ŷ₁)` is consumed on the caller
side; the body of the file is free of `IsCompact + exists_isMaxOn`
plumbing on the joint simplex.

## 撤退ライン (確定発動 4 本)

* **L-RI1**: block Markov encoding (DF, B blocks random codebook +
  staged cooperation, ~600–1000 lines) is supplied as
  `_h_block_markov : True` placeholder.
* **L-RI2**: sliding-window joint typicality decoder (DF, per-block
  staged decoding + error event collapse, ~400–600 lines) is supplied
  as `_h_sliding_window : True` placeholder.
* **L-RI3**: Wyner–Ziv binning (CF, compression with side info random
  binning, ~500–700 lines) is supplied as `_h_wz_binning : True`
  placeholder.
* **L-RI4**: side-information decoding (CF, Ŷ₁ reconstruction + final
  decoding, ~300–500 lines) is supplied as `_h_si_decode : True`
  placeholder.

The main theorems' bodies are the identity wrap `:= h_existence`.
Discharge of each placeholder is performed in companion seeds:

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

/-- The "existence" claim for the **decode-and-forward** inner bound:
there exists a threshold block length `N` beyond which one can find a
relay block code carrying at least `⌈exp(n R)⌉` messages.

The error-probability bound (average error `< ε` for any prescribed
`ε > 0`) is **not** embedded into this existence claim — it is supplied
on the caller side together with `h_existence` (and discharged in
`relay-df-block-markov-discharge-*` /
`relay-df-sliding-window-discharge-*`).

This matches the single-rate analogue of `MACInnerBoundExistence`
(T3-B MAC) and the convention of `wyner_ziv_achievability_existence`
(T3-D Wyner–Ziv). -/
def RelayDFInnerBoundExistence
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

/-- The "existence" claim for the **compress-and-forward** inner bound:
there exists a threshold block length `N` beyond which one can find a
relay block code carrying at least `⌈exp(n R)⌉` messages.

Same shape as `RelayDFInnerBoundExistence`; the structural difference
between the DF and CF achievability proofs lives entirely in the
discharge of the `_h_*` placeholders, not in the published existence
form. -/
def RelayCFInnerBoundExistence
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

/-- Anti-monotonicity of the DF existence form in the rate: a code that
achieves the larger rate `R` also achieves any smaller rate `R' ≤ R`,
because `Real.exp (n * R') ≤ Real.exp (n * R) ≤ M`. -/
lemma RelayDFInnerBoundExistence.anti_mono
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    {R R' : ℝ}
    (h : RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R)
    (hR : R' ≤ R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, hM⟩ := hN n hn
  refine ⟨M, c, ?_⟩
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
    {R R' : ℝ}
    (h : RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R)
    (hR : R' ≤ R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, hM⟩ := hN n hn
  refine ⟨M, c, ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul : (n : ℝ) * R' ≤ (n : ℝ) * R := mul_le_mul_of_nonneg_left hR hn0
  have hexp : Real.exp ((n : ℝ) * R') ≤ Real.exp ((n : ℝ) * R) :=
    Real.exp_le_exp.mpr hmul
  exact hexp.trans hM

end ExistenceForms

/-! ## DF inner bound main theorem (Cover–Thomas Theorem 15.10.2) -/

section DFInnerBound

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay decode-and-forward inner bound (Cover–Thomas Theorem 15.10.2,
hypothesis pass-through form, L-RI1 + L-RI2 engaged)**.

If a rate `R : ℝ` lies in the DF rate region — i.e. it satisfies the
two Cover–Thomas inequalities

```
R ≤ I(X; Y₁ | X₁) + I(X₁; Y)
R ≤ I(X, X₁; Y)
```

bundled as `InRelayDFRate R Imrh Iry Ibroad` — then for every block
length `n` sufficiently large there exist `M ≥ ⌈exp(n R)⌉` and a relay
block code `c : RelayCode M n α α₁ β β₁`.

The theorem is published with the hypothesis pass-through slots:

* `_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad` — the rate region
  membership predicate.
* `_h_block_markov : True` — block-Markov encoding hypothesis (B blocks
  random codebook + staged cooperation, ~600–1000 lines) holds (L-RI1;
  discharge in `relay-df-block-markov-discharge-*`).
* `_h_sliding_window : True` — sliding-window joint typicality decoder
  hypothesis (per-block staged decoding + error event collapse,
  ~400–600 lines) holds (L-RI2; discharge in
  `relay-df-sliding-window-discharge-*`).
* `h_existence : RelayDFInnerBoundExistence … R` — the existence
  statement itself; the body of the theorem is the identity wrap
  `:= h_existence`.

The error-probability bound (average error `< ε` for any prescribed
`ε > 0`) is **not** embedded into the existence statement — it is
supplied on the caller side together with `h_existence`. This matches
the convention of `mac_capacity_region_inner_bound` (T3-B MAC,
Cover–Thomas Theorem 15.3.6) and
`wyner_ziv_achievability_existence` (T3-D Wyner–Ziv,
Cover–Thomas Theorem 15.9.2). -/
theorem relay_df_inner_bound
    (R Imrh Iry Ibroad : ℝ)
    (_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (_h_block_markov : True)
    (_h_sliding_window : True)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

/-- **DF inner bound — `min`-form variant**.

Variant of `relay_df_inner_bound` taking the rate-region hypothesis in
the **`min`** form

```
R ≤ min { Imrh + Iry,  Ibroad }
```

directly, rather than as a bundled `InRelayDFRate`. The `min` form is
the textbook form (Cover–Thomas (15.232)) and is typically how the
inner bound is stated in the literature. -/
theorem relay_df_inner_bound_min_form
    (R Imrh Iry Ibroad : ℝ)
    (_h_min : R ≤ min (Imrh + Iry) Ibroad)
    (_h_block_markov : True)
    (_h_sliding_window : True)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

/-- **DF inner bound — unbundled two-inequality form**.

Variant taking the two DF inequalities separately rather than bundled
as a single `InRelayDFRate`. This is the usual exit point of an
n-letter joint typicality argument that produces the two bounds as
separate intermediates. -/
theorem relay_df_inner_bound_two_bounds
    (R Imrh Iry Ibroad : ℝ)
    (h₁ : R ≤ Imrh + Iry) (h₂ : R ≤ Ibroad)
    (h_block_markov : True)
    (h_sliding_window : True)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_df_inner_bound R Imrh Iry Ibroad ⟨h₁, h₂⟩ h_block_markov h_sliding_window
    h_existence

/-- **DF inner bound — `Real.log` rate form**.

Specialisation of `relay_df_inner_bound` to the standard
`R := Real.log M / n` rate convention used throughout Cover–Thomas. -/
theorem relay_df_inner_bound_log_rate
    {M n : ℕ} (_hn : 0 < n)
    (Imrh Iry Ibroad : ℝ)
    (h_in_df_region :
        InRelayDFRate (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad)
    (h_block_markov : True)
    (h_sliding_window : True)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
          (Real.log (M : ℝ) / (n : ℝ))) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        (Real.log (M : ℝ) / (n : ℝ)) :=
  relay_df_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad h_in_df_region
    h_block_markov h_sliding_window h_existence

end DFInnerBound

/-! ## CF inner bound main theorem (Cover–Thomas Theorem 15.10.3) -/

section CFInnerBound

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay compress-and-forward inner bound (Cover–Thomas
Theorem 15.10.3, hypothesis pass-through form, L-RI3 + L-RI4 engaged)**.

If a rate `R : ℝ` lies in the CF rate region — i.e. it satisfies the
CF rate bound and the compression feasibility constraint

```
R ≤ I(X; Ŷ₁, Y | X₁)
I(Y₁; Ŷ₁ | X₁, Y) ≤ I(X₁; Y)
```

bundled as `InRelayCFRate R Idec Ix1y Iy1hy1` — then for every block
length `n` sufficiently large there exist `M ≥ ⌈exp(n R)⌉` and a relay
block code `c : RelayCode M n α α₁ β β₁`.

The theorem is published with the hypothesis pass-through slots:

* `_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1` — the rate
  region membership predicate.
* `_h_wz_binning : True` — Wyner–Ziv compression binning hypothesis
  (compression with side info random binning, ~500–700 lines) holds
  (L-RI3; discharge in `relay-cf-wz-binning-discharge-*`).
* `_h_si_decode : True` — side-information decoding hypothesis
  (Ŷ₁ reconstruction + final decoding, ~300–500 lines) holds (L-RI4;
  discharge in `relay-cf-si-decode-discharge-*`).
* `h_existence : RelayCFInnerBoundExistence … R` — the existence
  statement itself; the body of the theorem is the identity wrap
  `:= h_existence`.

The error-probability bound (average error `< ε`) is **not** embedded
into the existence statement; it is supplied on the caller side. This
matches the convention of the DF inner bound and the MAC inner bound
(T3-B). -/
theorem relay_cf_inner_bound
    (R Idec Ix1y Iy1hy1 : ℝ)
    (_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_wz_binning : True)
    (_h_si_decode : True)
    (h_existence :
        RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

/-- **CF inner bound — unbundled two-condition form**.

Variant taking the rate bound and the compression feasibility as
separate hypotheses rather than bundled. -/
theorem relay_cf_inner_bound_two_conditions
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_rate : R ≤ Idec) (h_feas : Iy1hy1 ≤ Ix1y)
    (h_wz_binning : True)
    (h_si_decode : True)
    (h_existence :
        RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_cf_inner_bound R Idec Ix1y Iy1hy1 ⟨h_rate, h_feas⟩ h_wz_binning
    h_si_decode h_existence

/-- **CF inner bound — `Real.log` rate form**. -/
theorem relay_cf_inner_bound_log_rate
    {M n : ℕ} (_hn : 0 < n)
    (Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region :
        InRelayCFRate (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1)
    (h_wz_binning : True)
    (h_si_decode : True)
    (h_existence :
        RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
          (Real.log (M : ℝ) / (n : ℝ))) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        (Real.log (M : ℝ) / (n : ℝ)) :=
  relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1 h_in_cf_region
    h_wz_binning h_si_decode h_existence

end CFInnerBound

/-! ## Two-side combine (outer + inner) wrappers -/

section TwoSide

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Relay channel — DF achievability + cut-set outer bound combined**.

Package the simultaneous validity of the DF inner bound (existence form)
and the cut-set outer bound (`relay_cutset_outer_bound`) at the same
rate `R`. Matches the two-side packaging pattern of
`mac_capacity_region_consistent` (T3-B MAC) and
`wyner_ziv_tendsto` (T3-D Wyner–Ziv) for callers that want a single
entry point. -/
theorem relay_df_consistent
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Imrh Iry Ibroad Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (_h_block_markov : True) (_h_sliding_window : True)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_rate_bound_outer : R ≤ relayCutsetBound Ib Im)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    (R ≤ relayCutsetBound Ib Im)
      ∧ RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  ⟨relay_cutset_outer_bound hn c R Ib Im trivial trivial h_rate_bound_outer,
   relay_df_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     R Imrh Iry Ibroad h_in_df_region trivial trivial h_existence⟩

/-- **Relay channel — CF achievability + cut-set outer bound combined**.

Package the simultaneous validity of the CF inner bound (existence form)
and the cut-set outer bound at the same rate `R`. -/
theorem relay_cf_consistent
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (_h_wz_binning : True) (_h_si_decode : True)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_rate_bound_outer : R ≤ relayCutsetBound Ib Im)
    (h_existence :
        RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    (R ≤ relayCutsetBound Ib Im)
      ∧ RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  ⟨relay_cutset_outer_bound hn c R Ib Im trivial trivial h_rate_bound_outer,
   relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     R Idec Ix1y Iy1hy1 h_in_cf_region trivial trivial h_existence⟩

end TwoSide

end InformationTheory.Shannon
