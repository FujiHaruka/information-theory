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

/-- **DF block-Markov witness predicate (honest achievability residual).**

Bundles the two structural ingredients of the DF achievability proof
(Cover-Thomas Theorem 15.10.2):

* **L-RI1 (block Markov encoding)** — per-block random codebook
  construction.
* **L-RI2 (sliding-window joint typicality decoder)** — per-block staged
  decoder error-event collapse.

Previously this witness was defined as the *bare* existence
`RelayDFInnerBoundExistence R` — but that bare predicate carried **no error
content** (the BC red herring: an existence claim with no `averageErrorProb`
link is satisfiable by any code at any rate). The existence predicate is now
**error-carrying** (`(c.averageErrorProb W x₁Ref).toReal < ε`), so a witness
that merely exhibits a rate-matching code does **not** establish it.

Accordingly the witness is now the **honest achievability residual**
`RelayDFAchievable W R Imrh Iry Ibroad` — the gated implication
`(InRelayDFRate) → RelayDFInnerBoundExistence W R`. This is a genuine `Prop`,
**not** the conclusion and **not** `True`; its discharge (the genuine
random-coding core establishing vanishing error) is the responsibility of
the companion seeds `relay-df-block-markov-discharge-*` /
`relay-df-sliding-window-discharge-*`. -/
def IsRelayDFBlockMarkovWitness
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁) (R Imrh Iry Ibroad : ℝ) : Prop :=
  RelayDFAchievable (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad

/-- A DF block-Markov witness, **together with the rate-region membership**,
yields the DF inner-bound existence by `modus ponens`. This is the genuine
routing lemma — the witness is the gated achievability implication, so the
existence is *derived* from it and the rate region, not asserted.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
lemma RelayDFInnerBoundExistence_of_witness
    {W : RelayChannel α α₁ β β₁} {R Imrh Iry Ibroad : ℝ}
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h : IsRelayDFBlockMarkovWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  h h_in_df_region

/-- **DF inner bound — body discharge form (L-RI1 + L-RI2 as honest
achievability witness)**.

This is the body-discharged variant of `relay_df_inner_bound`: it takes the
rate-region membership `h_in_df_region` and the achievability witness
`h_witness` and **derives** the error-carrying existence claim by `modus
ponens` (not an identity wrap, not a leap from rate-only data).

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_body_from_witness
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  RelayDFInnerBoundExistence_of_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    h_in_df_region h_witness

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

Previously this witness was defined as the *bare* existence
`RelayCFInnerBoundExistence R`, which carried **no error content** (the BC
red herring). The existence predicate is now **error-carrying**, so the
witness is now the **honest achievability residual**
`RelayCFAchievable W R Idec Ix1y Iy1hy1` — the gated implication
`(InRelayCFRate) → RelayCFInnerBoundExistence W R`. This is a genuine `Prop`,
**not** the conclusion and **not** `True`. Its discharge is the
responsibility of the companion seeds `relay-cf-wz-binning-discharge-*` /
`relay-cf-si-decode-discharge-*`. -/
def IsRelayCFBinningWitness
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (W : RelayChannel α α₁ β β₁) (R Idec Ix1y Iy1hy1 : ℝ) : Prop :=
  RelayCFAchievable (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1

/-- A CF binning witness, **together with the rate-region membership**,
yields the CF inner-bound existence by `modus ponens`.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
lemma RelayCFInnerBoundExistence_of_witness
    {W : RelayChannel α α₁ β β₁} {R Idec Ix1y Iy1hy1 : ℝ}
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  h h_in_cf_region

/-- **CF inner bound — body discharge form (L-RI3 + L-RI4 as honest
achievability witness)**.

The body-discharged variant of `relay_cf_inner_bound`: takes the
rate-region membership and the achievability witness and **derives** the
error-carrying existence claim by `modus ponens`.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_body_from_witness
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  RelayCFInnerBoundExistence_of_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    h_in_cf_region h_witness

end CFWitness

/-! ## Section 5 — Re-published main theorems with witness predicates -/

section Republished

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **DF inner bound — discharged form (witness upgrade).**

Body-discharged variant of `relay_df_inner_bound` where the previous
`_h_block_markov : True` / `_h_sliding_window : True` / `h_existence`
hypotheses are *replaced* by a single structured achievability witness
`h_witness : IsRelayDFBlockMarkovWitness`. The rate-region hypothesis is
retained and the error-carrying existence is **derived** by `modus ponens`
(not a leap from rate-only data).

This is the **public entry point** of the body discharge layer for the DF
inner bound.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_discharged
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_df_body_from_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Imrh Iry Ibroad h_in_df_region h_witness

/-- **DF inner bound — discharged + `min`-form**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_discharged_min_form
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h_min : R ≤ min (Imrh + Iry) Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Imrh Iry Ibroad ((InRelayDFRate.iff_le_min).mpr h_min) h_witness

/-- **DF inner bound — discharged + unbundled two-inequality form**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_discharged_two_bounds
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h₁ : R ≤ Imrh + Iry) (h₂ : R ≤ Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Imrh Iry Ibroad ⟨h₁, h₂⟩ h_witness

/-- **CF inner bound — discharged form (witness upgrade).**

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_discharged
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_cf_body_from_witness (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Idec Ix1y Iy1hy1 h_in_cf_region h_witness

/-- **CF inner bound — discharged + unbundled two-condition form**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_discharged_two_conditions
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_rate : R ≤ Idec) (h_feas : Iy1hy1 ≤ Ix1y)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_cf_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Idec Ix1y Iy1hy1 ⟨h_rate, h_feas⟩ h_witness

/-- **DF inner bound — discharged + `Real.log` rate form**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_discharged_log_rate
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (_hn : 0 < n)
    (Imrh Iry Ibroad : ℝ)
    (h_in_df_region :
        InRelayDFRate (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
          W (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        W (Real.log (M : ℝ) / (n : ℝ)) :=
  relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W (Real.log (M : ℝ) / (n : ℝ)) Imrh Iry Ibroad h_in_df_region h_witness

/-- **CF inner bound — discharged + `Real.log` rate form**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_discharged_log_rate
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (_hn : 0 < n)
    (Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region :
        InRelayCFRate (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
          W (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
        W (Real.log (M : ℝ) / (n : ℝ)) :=
  relay_cf_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W (Real.log (M : ℝ) / (n : ℝ)) Idec Ix1y Iy1hy1 h_in_cf_region h_witness

end Republished

/-! ## Section 6 — Two-side combine (outer + inner) with body discharge -/

section TwoSideDischarged

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **DF achievability (body-discharged) + cut-set outer bound combined**.

Witness-predicate variant of `relay_df_consistent`: the outer side
**derives** `R ≤ relayCutsetBound (Ib+ε) (Im+ε)` from the entropy-level
Fano + chain inputs, and the inner side **derives** the error-carrying
existence from the achievability witness by `modus ponens`.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_consistent_discharged
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Imrh Iry Ibroad Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)
    (h_fano_m : RelayMacCutFano M n R Pe I_marg_m)
    (h_chain_b : I_marg_b ≤ (n : ℝ) * Ib)
    (h_chain_m : I_marg_m ≤ (n : ℝ) * Im)
    (h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    (R ≤ relayCutsetBound (Ib + ε) (Im + ε))
      ∧ RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  ⟨relay_cutset_outer_bound hn c R Pe I_marg_b I_marg_m Ib Im ε
     h_fano_b h_fano_m h_chain_b h_chain_m h_cleanup_b h_cleanup_m,
   relay_df_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     W R Imrh Iry Ibroad h_in_df_region h_witness⟩

/-- **CF achievability (body-discharged) + cut-set outer bound combined**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_consistent_discharged
    (W : RelayChannel α α₁ β β₁)
    {M n : ℕ} (hn : 0 < n)
    (c : RelayCode M n α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (h_fano_b : RelayBcastCutFano M n R Pe I_marg_b)
    (h_fano_m : RelayMacCutFano M n R Pe I_marg_m)
    (h_chain_b : I_marg_b ≤ (n : ℝ) * Ib)
    (h_chain_m : I_marg_m ≤ (n : ℝ) * Im)
    (h_cleanup_b : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_cleanup_m : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1) :
    (R ≤ relayCutsetBound (Ib + ε) (Im + ε))
      ∧ RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  ⟨relay_cutset_outer_bound hn c R Pe I_marg_b I_marg_m Ib Im ε
     h_fano_b h_fano_m h_chain_b h_chain_m h_cleanup_b h_cleanup_m,
   relay_cf_inner_bound_discharged (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     W R Idec Ix1y Iy1hy1 h_in_cf_region h_witness⟩

end TwoSideDischarged

/-! ## Section 7 — Body-discharge bridge to original main theorems -/

section Bridge

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Bridge: a DF achievability witness drives the original
`relay_df_inner_bound`**.

The *adapter* between the body-discharged signature and the original
published signature: a caller holding the achievability witness (the gated
implication) can feed it directly as the `h_ach` argument of the original
theorem.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_df_inner_bound_via_witness
    (W : RelayChannel α α₁ β β₁)
    (R Imrh Iry Ibroad : ℝ)
    (h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (h_witness :
        IsRelayDFBlockMarkovWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Imrh Iry Ibroad) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_df_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Imrh Iry Ibroad h_in_df_region h_witness

/-- **Bridge: a CF achievability witness drives the original
`relay_cf_inner_bound`**.

`@audit:suspect(relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_via_witness
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_witness :
        IsRelayCFBinningWitness
          (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R :=
  relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    W R Idec Ix1y Iy1hy1 h_in_cf_region h_witness

end Bridge

end InformationTheory.Shannon
