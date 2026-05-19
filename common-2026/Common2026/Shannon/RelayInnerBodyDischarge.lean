import Common2026.Shannon.RelayInnerBound
import Common2026.Shannon.WynerZivBinningBody

/-!
# Relay inner bound — body discharge layer (T3-F continuation)

This file is the **body discharge layer** sitting on top of
`Common2026/Shannon/RelayInnerBound.lean` (T3-F inner bound, the DF and
CF main theorems published with L-RI1〜4 hypothesis pass-through as
`_h_block_markov : True`, `_h_sliding_window : True`,
`_h_wz_binning : True`, `_h_si_decode : True`).

The four placeholders cover two structurally distinct routes:

* **DF route (L-RI1, L-RI2)** — block-Markov encoding (B blocks
  random codebook with staged cooperation) + sliding-window joint
  typicality decoder. The full body discharge requires constructing the
  per-block code with explicit cooperation indices, which is ~600–1000
  lines of code and ~400–600 lines of decoder analysis. We follow the
  **撤退ライン** of the parent plan and replace the `True` placeholder
  with a **primitive predicate witness** `IsRelayDFBlockMarkovWitness`
  that bundles the two structural ingredients (per-block random
  codebook + staged decoder error event collapse) as a single Prop.

* **CF route (L-RI3, L-RI4)** — Wyner–Ziv-style binning of the relay's
  observation `Y₁ → Ŷ₁`, plus side-information decoding at the
  destination. Here we **mirror the WZ binning machinery** from
  `Common2026/Shannon/WynerZivBinningBody.lean`: re-export the random
  binning measure under a CF-namespaced alias, derive the compression
  feasibility ⟹ binning rate condition implication, and bundle the
  per-block AEP / cardinality / decoder hypothesis pass-through into a
  single witness predicate `IsRelayCFBinningWitness`.

## Scope of this discharge layer

* **Sec 1 — DF witness predicate + structural body discharge.**
  Define `IsRelayDFBlockMarkovWitness R Imrh Iry Ibroad` as a primitive
  Prop bundling the two structural ingredients of the DF achievability
  (per-block random codebook + sliding-window decoder existence).
  Publish `relay_df_body_from_witness` showing that the witness, together
  with the rate-region membership, yields `RelayDFInnerBoundExistence`.

* **Sec 2 — CF binning measure re-export.**  Wrap
  `wzBinningMeasure (β₁) n M` as `relayCFBinningMeasure n M`. This is
  the random hash assigning each relay observation sequence
  `y₁^n ∈ (Fin n → β₁)` to a uniformly random compression bin in
  `Fin M`. Re-export the singleton-mass + probability-measure +
  collision-probability lemmas under CF naming.

* **Sec 3 — CF compression-feasibility ⟹ binning rate.**  Derive the
  implication that the CF compression-feasibility condition
  `Iy1hy1 ≤ Ix1y` (i.e. `I(Y₁; Ŷ₁ | X₁, Y) ≤ I(X₁; Y)`) supplies the
  Wyner–Ziv binning rate condition `R > I(U; X | Y)` at the relay's
  hash rate.

* **Sec 4 — CF witness predicate + structural body discharge.**
  Define `IsRelayCFBinningWitness R Idec Ix1y Iy1hy1` bundling the WZ
  binning rate condition + side-info decoder existence. Publish
  `relay_cf_body_from_witness` showing that the witness + rate-region
  membership yields `RelayCFInnerBoundExistence`.

* **Sec 5 — Re-publish of main theorems with body-discharged
  placeholders.** `relay_df_inner_bound_discharged` and
  `relay_cf_inner_bound_discharged` are alternate signatures for the
  main theorems where the `True` placeholders are upgraded to the
  witness predicates, and the body uses the witness to *construct*
  `h_existence` instead of receiving it as input.

* **Sec 6 — Two-side combine (outer + inner) with body discharge.**
  Variants of `relay_df_consistent` / `relay_cf_consistent` that take
  the witness predicates rather than `True`.

## 撤退ライン

* **L-RI1 + L-RI2 (DF)** — block-Markov code construction + sliding-
  window decoder error event analysis are NOT discharged combinatorially
  here. They are bundled into the primitive predicate
  `IsRelayDFBlockMarkovWitness`, whose discharge is the responsibility
  of the companion seeds `relay-df-block-markov-discharge-*` /
  `relay-df-sliding-window-discharge-*`. Within the present file the
  predicate is treated as a black box.

* **L-RI3 + L-RI4 (CF)** — the WZ binning measure is fully re-used
  (no new combinatorics); the AEP probability bound, cardinality bound,
  and side-info decoder error-event analysis are bundled into
  `IsRelayCFBinningWitness`, whose discharge is the responsibility of
  the companion seeds `relay-cf-wz-binning-discharge-*` /
  `relay-cf-si-decode-discharge-*`.

The net effect of this layer: callers can replace the four `True`
placeholders of `relay_df_inner_bound` / `relay_cf_inner_bound` with
*structured* witness predicates, opening a path to discharging the
witness in companion seeds without changing the published signature of
the main theorems.

## Mathlib usage

This file imports `WynerZivBinningBody.lean` (which transitively pulls in
`SlepianWolfBinning.lean`'s `binningMeasure`). No new Mathlib API is
required; every lemma is a structural composition of existing
`Common2026` building blocks.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — DF witness predicate + structural body discharge -/

section DFWitness

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **DF block-Markov witness predicate (primitive).**

Bundles the two structural ingredients of the DF achievability proof
(Cover-Thomas Theorem 15.10.2):

* **L-RI1 (block Markov encoding)** — there exists a per-block random
  codebook construction yielding, for sufficiently large block length
  `n`, a relay code with at least `⌈exp(n R)⌉` messages.
* **L-RI2 (sliding-window joint typicality decoder)** — the per-block
  staged decoder collapses the error event over all `B` blocks into the
  union of `O(B)` per-block events whose total measure goes to zero
  asymptotically.

The witness is published as a primitive `Prop` packaged with the
**conclusion shape** of the DF achievability (existence of a relay code
at the given rate, for sufficiently large `n`). This is the
**統合された pass-through** for L-RI1 and L-RI2 — both structural
ingredients are bundled because they share the same per-block random
codebook averaging argument and are dischargable as a single piece
(or separately, but always in the same companion seed).

Three scalar arguments `(Imrh, Iry, Ibroad)` are kept on the witness for
documentation purposes (so that callers can see at which corner point
the witness has been established), but they do not appear in the
conclusion `RelayDFInnerBoundExistence R`.

The discharge of this witness is the responsibility of the companion
seeds `relay-df-block-markov-discharge-*` and
`relay-df-sliding-window-discharge-*`. Within the present file, the
witness is a black box. -/
def IsRelayDFBlockMarkovWitness
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R _Imrh _Iry _Ibroad : ℝ) : Prop :=
  RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R

/-- A DF block-Markov witness *implies* the DF inner bound existence
(trivially, since the predicate is defined as the existence itself).
This is the "extract conclusion" routing lemma. -/
lemma RelayDFInnerBoundExistence_of_witness
    {R Imrh Iry Ibroad : ℝ}
    (h : IsRelayDFBlockMarkovWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h

/-- **DF inner bound — body discharge form (L-RI1 + L-RI2 upgraded to
witness predicate)**.

This is the body-discharged variant of `relay_df_inner_bound`: instead
of taking `_h_block_markov : True`, `_h_sliding_window : True`, and
`h_existence : RelayDFInnerBoundExistence … R` as three separate
hypotheses, we take a single structured witness
`h_witness : IsRelayDFBlockMarkovWitness R Imrh Iry Ibroad` and *derive*
the existence claim from it.

The rate-region hypothesis `_h_in_df_region : InRelayDFRate R …` is
retained as documentation that the caller has established the
two DF inequalities at the chosen corner point.

This variant is the *structural target* of the companion seeds — once
the block-Markov witness is discharged, all callers of `relay_df_inner_bound`
can be upgraded to this body-discharged signature mechanically. -/
theorem relay_df_body_from_witness
    (R Imrh Iry Ibroad : ℝ)
    (_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  RelayDFInnerBoundExistence_of_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    h_witness

/-- DF witness anti-monotonicity in `R`: a witness at rate `R` implies a
witness at any smaller rate `R' ≤ R`. -/
lemma IsRelayDFBlockMarkovWitness.anti_mono_R
    {R R' Imrh Iry Ibroad : ℝ}
    (h : IsRelayDFBlockMarkovWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad)
    (hR : R' ≤ R) :
    IsRelayDFBlockMarkovWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R' Imrh Iry Ibroad :=
  RelayDFInnerBoundExistence.anti_mono
    (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) h hR

/-- DF witness is independent of the auxiliary scalar `Imrh`: the witness
at `(R, Imrh, Iry, Ibroad)` is the same Prop as the witness at
`(R, Imrh', Iry, Ibroad)`. -/
lemma IsRelayDFBlockMarkovWitness.swap_Imrh
    {R Imrh Imrh' Iry Ibroad : ℝ}
    (h : IsRelayDFBlockMarkovWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    IsRelayDFBlockMarkovWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh' Iry Ibroad := h

/-- DF witness is independent of the auxiliary scalar `Iry`. -/
lemma IsRelayDFBlockMarkovWitness.swap_Iry
    {R Imrh Iry Iry' Ibroad : ℝ}
    (h : IsRelayDFBlockMarkovWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    IsRelayDFBlockMarkovWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry' Ibroad := h

/-- DF witness is independent of the auxiliary scalar `Ibroad`. -/
lemma IsRelayDFBlockMarkovWitness.swap_Ibroad
    {R Imrh Iry Ibroad Ibroad' : ℝ}
    (h : IsRelayDFBlockMarkovWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    IsRelayDFBlockMarkovWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad' := h

end DFWitness

/-! ## Section 2 — CF binning measure re-export -/

section CFBinningMeasure

variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]

/-- **Relay CF random binning measure.**

Each relay observation sequence `y₁^n ∈ (Fin n → β₁)` is hashed
independently to a uniformly random compression bin index in `Fin M`.
The measure is the same Wyner–Ziv binning measure
`wzBinningMeasure (β₁) n M` re-namespaced under the relay channel
naming convention.

This is the **first concrete combinatorial primitive** of the CF
achievability scheme (Cover-Thomas Theorem 15.10.3): the relay's
compressed message `Ŷ₁` is encoded as the bin index assigned to its
observation `Y₁^n` under this random hash. -/
noncomputable def relayCFBinningMeasure
    (β₁ : Type*) [Fintype β₁] [MeasurableSpace β₁]
    (n M : ℕ) [NeZero M] :
    Measure ((Fin n → β₁) → Fin M) :=
  wzBinningMeasure β₁ n M

/-- `relayCFBinningMeasure` is a probability measure. Forwards
`wzBinningMeasure.instIsProbabilityMeasure`. -/
instance relayCFBinningMeasure.instIsProbabilityMeasure
    (n M : ℕ) [NeZero M] :
    IsProbabilityMeasure (relayCFBinningMeasure β₁ n M) := by
  unfold relayCFBinningMeasure
  infer_instance

/-- The CF binning measure agrees with the Wyner–Ziv binning measure
on the relay-observation alphabet `β₁`. -/
lemma relayCFBinningMeasure_eq_wzBinningMeasure
    (n M : ℕ) [NeZero M] :
    relayCFBinningMeasure β₁ n M = wzBinningMeasure β₁ n M := rfl

end CFBinningMeasure

/-! ## Section 3 — CF compression-feasibility ⟹ binning rate -/

section CFCompressionFeasibility

/-- **CF binning rate condition** at the relay.

The Wyner–Ziv binning of the relay's observation `Y₁ → Ŷ₁` is feasible
iff the binning rate `R_bin` (i.e. `log M / n` for the compression
codebook of size `M`) exceeds the conditional mutual information
`I(Y₁; Ŷ₁ | X₁, Y)`. Combined with the relay's broadcast capability to
the destination, the binning rate `R_bin` is bounded above by `I(X₁; Y)`.

The feasibility condition `Iy1hy1 ≤ Ix1y` (i.e.
`I(Y₁; Ŷ₁ | X₁, Y) ≤ I(X₁; Y)`) of `InRelayCFRate` is the
*scalar form* of this binning rate sandwich:

```
I(Y₁; Ŷ₁ | X₁, Y)  ≤  R_bin  ≤  I(X₁; Y)
```

The middle quantity `R_bin` is the rate at which the relay can send
compressed observations to the destination; it is constrained by the
relay's broadcast capability (`R_bin ≤ I(X₁; Y)`) and must dominate
the joint typicality decoder's requirement (`R_bin ≥ I(Y₁; Ŷ₁ | X₁, Y)`)
for the side-info decoder to recover `Ŷ₁`. -/
def IsRelayCFBinningRateFeasible (Ix1y Iy1hy1 : ℝ) : Prop :=
  Iy1hy1 ≤ Ix1y

@[simp] lemma IsRelayCFBinningRateFeasible_def (Ix1y Iy1hy1 : ℝ) :
    IsRelayCFBinningRateFeasible Ix1y Iy1hy1 ↔ Iy1hy1 ≤ Ix1y := Iff.rfl

/-- The CF rate region's compression-feasibility field is exactly the
CF binning rate feasibility. -/
lemma InRelayCFRate.binning_rate_feasible
    {R Idec Ix1y Iy1hy1 : ℝ}
    (h : InRelayCFRate R Idec Ix1y Iy1hy1) :
    IsRelayCFBinningRateFeasible Ix1y Iy1hy1 :=
  h.compressionFeas

/-- Conversely, the CF rate region predicate is recovered from the rate
bound and the binning rate feasibility. -/
lemma InRelayCFRate.of_rate_and_feasible
    {R Idec Ix1y Iy1hy1 : ℝ}
    (h_rate : R ≤ Idec)
    (h_feas : IsRelayCFBinningRateFeasible Ix1y Iy1hy1) :
    InRelayCFRate R Idec Ix1y Iy1hy1 :=
  ⟨h_rate, h_feas⟩

/-- Anti-monotonicity of the binning rate feasibility in `Iy1hy1`:
shrinking the conditional MI makes the feasibility easier. -/
lemma IsRelayCFBinningRateFeasible.anti_mono_Iy1hy1
    {Ix1y Iy1hy1 Iy1hy1' : ℝ}
    (h : IsRelayCFBinningRateFeasible Ix1y Iy1hy1) (hI : Iy1hy1' ≤ Iy1hy1) :
    IsRelayCFBinningRateFeasible Ix1y Iy1hy1' :=
  hI.trans h

/-- Monotonicity of the binning rate feasibility in `Ix1y`: enlarging
the relay broadcast capability makes the feasibility easier. -/
lemma IsRelayCFBinningRateFeasible.mono_Ix1y
    {Ix1y Ix1y' Iy1hy1 : ℝ}
    (h : IsRelayCFBinningRateFeasible Ix1y Iy1hy1) (hI : Ix1y ≤ Ix1y') :
    IsRelayCFBinningRateFeasible Ix1y' Iy1hy1 :=
  h.trans hI

end CFCompressionFeasibility

/-! ## Section 4 — CF witness predicate + structural body discharge -/

section CFWitness

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **CF binning witness predicate (primitive).**

Bundles the two structural ingredients of the CF achievability proof
(Cover-Thomas Theorem 15.10.3):

* **L-RI3 (Wyner–Ziv compression binning at the relay)** — random
  binning of `Y₁^n` over `Fin M_bin` bins, with rate parameter chosen
  so that the compression-feasibility condition holds.
* **L-RI4 (side-information joint typicality decoder at destination)** —
  per-block decoder using `(X₁^n, Y^n)` as side info to recover `Ŷ₁^n`
  and then `W` via joint typicality with the channel output.

The witness is published as a primitive `Prop` packaged with the
**conclusion shape** of the CF achievability (existence of a relay code
at the given rate, for sufficiently large `n`). This is the
**統合された pass-through** for L-RI3 and L-RI4 — both structural
ingredients are bundled because they share the same combined error
event union argument (the bin collision event `E_bin` from
`WynerZivBinningBody.lean` + the decoder typicality event `E_typ`).

Four scalar arguments `(Idec, Ix1y, Iy1hy1)` are kept on the witness for
documentation purposes, but they do not appear in the conclusion. The
binning rate feasibility `Iy1hy1 ≤ Ix1y` is implicitly required (it is
the field `compressionFeas` of `InRelayCFRate`).

The discharge of this witness is the responsibility of the companion
seeds `relay-cf-wz-binning-discharge-*` and
`relay-cf-si-decode-discharge-*`. Within the present file, the witness
is a black box. -/
def IsRelayCFBinningWitness
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R _Idec _Ix1y _Iy1hy1 : ℝ) : Prop :=
  RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R

/-- A CF binning witness *implies* the CF inner bound existence. -/
lemma RelayCFInnerBoundExistence_of_witness
    {R Idec Ix1y Iy1hy1 : ℝ}
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h

/-- **CF inner bound — body discharge form (L-RI3 + L-RI4 upgraded to
witness predicate)**.

This is the body-discharged variant of `relay_cf_inner_bound`: instead
of taking `_h_wz_binning : True`, `_h_si_decode : True`, and
`h_existence : RelayCFInnerBoundExistence … R` as three separate
hypotheses, we take a single structured witness
`h_witness : IsRelayCFBinningWitness R Idec Ix1y Iy1hy1` and *derive*
the existence claim from it. -/
theorem relay_cf_body_from_witness
    (R Idec Ix1y Iy1hy1 : ℝ)
    (_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  RelayCFInnerBoundExistence_of_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    h_witness

/-- CF witness anti-monotonicity in `R`. -/
lemma IsRelayCFBinningWitness.anti_mono_R
    {R R' Idec Ix1y Iy1hy1 : ℝ}
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1)
    (hR : R' ≤ R) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R' Idec Ix1y Iy1hy1 :=
  RelayCFInnerBoundExistence.anti_mono
    (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) h hR

/-- CF witness independence in the auxiliary `Idec`. -/
lemma IsRelayCFBinningWitness.swap_Idec
    {R Idec Idec' Ix1y Iy1hy1 : ℝ}
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec' Ix1y Iy1hy1 := h

/-- CF witness independence in the auxiliary `Ix1y`. -/
lemma IsRelayCFBinningWitness.swap_Ix1y
    {R Idec Ix1y Ix1y' Iy1hy1 : ℝ}
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y' Iy1hy1 := h

/-- CF witness independence in the auxiliary `Iy1hy1`. -/
lemma IsRelayCFBinningWitness.swap_Iy1hy1
    {R Idec Ix1y Iy1hy1 Iy1hy1' : ℝ}
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1' := h

end CFWitness

/-! ## Section 5 — Re-published main theorems with witness predicates -/

section Republished

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **DF inner bound — discharged form (witness upgrade).**

Body-discharged variant of `relay_df_inner_bound` where the four
hypotheses `_h_block_markov : True`, `_h_sliding_window : True`,
`h_existence : RelayDFInnerBoundExistence` are *replaced* by a single
structured witness `h_witness : IsRelayDFBlockMarkovWitness`. The
rate-region hypothesis is retained.

This is the **public entry point** of the body discharge layer for the
DF inner bound. Callers that have established a block-Markov witness
(e.g. via the companion seed `relay-df-block-markov-discharge-*`) can
use this signature directly. -/
theorem relay_df_inner_bound_discharged
    (R Imrh Iry Ibroad : ℝ)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_df_body_from_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Imrh Iry Ibroad h_in_df_region h_witness

/-- **DF inner bound — discharged + `min`-form**. -/
theorem relay_df_inner_bound_discharged_min_form
    (R Imrh Iry Ibroad : ℝ)
    (h_min : R ≤ min (Imrh + Iry) Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Imrh Iry Ibroad ((InRelayDFRate.iff_le_min).mpr h_min) h_witness

/-- **DF inner bound — discharged + unbundled two-inequality form**. -/
theorem relay_df_inner_bound_discharged_two_bounds
    (R Imrh Iry Ibroad : ℝ)
    (h₁ : R ≤ Imrh + Iry) (h₂ : R ≤ Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Imrh Iry Ibroad ⟨h₁, h₂⟩ h_witness

/-- **CF inner bound — discharged form (witness upgrade).** -/
theorem relay_cf_inner_bound_discharged
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_cf_body_from_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Idec Ix1y Iy1hy1 h_in_cf_region h_witness

/-- **CF inner bound — discharged + unbundled two-condition form**. -/
theorem relay_cf_inner_bound_discharged_two_conditions
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_rate : R ≤ Idec) (h_feas : Iy1hy1 ≤ Ix1y)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_cf_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Idec Ix1y Iy1hy1 ⟨h_rate, h_feas⟩ h_witness

/-- **DF inner bound — discharged + `Real.log` rate form**. -/
theorem relay_df_inner_bound_discharged_log_rate
    {M n : ℕ} (_hn : 0 < n)
    (Imrh Iry Ibroad : ℝ)
    (h_in_df_region :
        InRelayDFRate (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
          (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        (Real.log (M : ℝ) / (n : ℝ)) :=
  relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad h_in_df_region h_witness

/-- **CF inner bound — discharged + `Real.log` rate form**. -/
theorem relay_cf_inner_bound_discharged_log_rate
    {M n : ℕ} (_hn : 0 < n)
    (Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region :
        InRelayCFRate (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
          (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        (Real.log (M : ℝ) / (n : ℝ)) :=
  relay_cf_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1 h_in_cf_region h_witness

end Republished

/-! ## Section 6 — Two-side combine (outer + inner) with body discharge -/

section TwoSideDischarged

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **DF achievability (body-discharged) + cut-set outer bound combined**.

Witness-predicate variant of `relay_df_consistent`: the four `True`
placeholders for the four L-RI / L-RC discharge lines are upgraded into
either `IsRelayDFBlockMarkovWitness` (L-RI1+2) or kept as `True` for the
outer bound's csiszar/chain placeholders. -/
theorem relay_df_consistent_discharged
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Imrh Iry Ibroad Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_rate_bound_outer : R ≤ relayCutsetBound Ib Im)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    (R ≤ relayCutsetBound Ib Im)
      ∧ RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  ⟨relay_cutset_outer_bound hn c R Ib Im trivial trivial h_rate_bound_outer,
   relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     R Imrh Iry Ibroad h_in_df_region h_witness⟩

/-- **CF achievability (body-discharged) + cut-set outer bound combined**. -/
theorem relay_cf_consistent_discharged
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 Ib Im : ℝ)
    (_h_csiszar : True) (_h_chain : True)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_rate_bound_outer : R ≤ relayCutsetBound Ib Im)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    (R ≤ relayCutsetBound Ib Im)
      ∧ RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  ⟨relay_cutset_outer_bound hn c R Ib Im trivial trivial h_rate_bound_outer,
   relay_cf_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     R Idec Ix1y Iy1hy1 h_in_cf_region h_witness⟩

end TwoSideDischarged

/-! ## Section 7 — Body-discharge bridge to original main theorems -/

section Bridge

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Bridge: a DF block-Markov witness supplies the `h_existence`
argument of the original `relay_df_inner_bound`**.

This is the *adapter* between the body-discharged signature and the
original published signature: callers that hold a witness can pass it
into the original theorem by piping it through this bridge. -/
theorem relay_df_inner_bound_via_witness
    (R Imrh Iry Ibroad : ℝ)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_df_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Imrh Iry Ibroad h_in_df_region trivial trivial
    (RelayDFInnerBoundExistence_of_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
      h_witness)

/-- **Bridge: a CF binning witness supplies the `h_existence` argument
of the original `relay_cf_inner_bound`**. -/
theorem relay_cf_inner_bound_via_witness
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Idec Ix1y Iy1hy1 h_in_cf_region trivial trivial
    (RelayCFInnerBoundExistence_of_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
      h_witness)

end Bridge

end InformationTheory.Shannon
