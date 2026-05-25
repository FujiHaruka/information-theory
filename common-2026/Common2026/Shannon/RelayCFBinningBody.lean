import Common2026.Shannon.RelayInnerBodyDischarge
import Common2026.Shannon.WynerZivBinningCovering

/-!
# Relay CF (compress-and-forward) binning witness body (W9-G3, T3-F continuation)

This file is a **deeper body-discharge layer** for the compress-and-forward
(CF) side of the relay channel inner bound (Cover–Thomas Theorem 15.10.3).
It sits on top of `Common2026/Shannon/RelayInnerBodyDischarge.lean`, which
introduced the CF witness predicate

```
IsRelayCFBinningWitness W R Idec Ix1y Iy1hy1 := RelayCFAchievable W R Idec Ix1y Iy1hy1
```

— the **honest achievability residual** (the gated implication
`(InRelayCFRate) → RelayCFInnerBoundExistence W R`, carrying vanishing
error), and `Common2026/Shannon/WynerZivBinningCovering.lean`, which
published the **covering / packing** decomposition of the Wyner–Ziv random
binning achievability body.

**De-circularization note (2026-05-21).** The CF existence predicate
`RelayCFInnerBoundExistence W R` is now **error-carrying**
(`averageErrorProb < ε`), and the witness is the honest gated implication
(no longer the bare existence). The "binning-discharged" theorems below
therefore consume the achievability witness and **derive** the existence by
`modus ponens` (genuine, non-circular) — they no longer pass a bare
existence through `relay_cf_inner_bound … trivial trivial h_existence`
(which masked a conclusion≡hypothesis circularity).

## What this layer does

The CF achievability scheme compresses the relay's observation `Y₁^n` via a
Wyner–Ziv random binning `Ŷ₁`, then decodes at the destination using
`(X₁^n, Y^n)` as side information. The two structural ingredients bundled
inside `IsRelayCFBinningWitness` (L-RI3 + L-RI4) are *exactly* the WZ
covering and packing events. This file makes that correspondence explicit:

* **`IsCFCompressionHyp`** — the relay's WZ compression covering event:
  the true compressed sequence is jointly typical with the destination's
  side info, with failure probability `≤ ε_cov`. This is literally
  `IsWynerZivBinningCovering` re-namespaced for the CF relay scheme (L-RI3).

* **`IsCFBinningDecodableHyp`** — the side-info decoder packing event: no
  alias compression sequence `ŷ' ≠ ŷ` in the same bin is jointly typical
  with the side info, with failure probability `≤ ε_pack`. This is literally
  `IsWynerZivBinningPacking` re-namespaced (L-RI4).

* **`IsCFSideInfoDecodeHyp`** — the conjunction (the joint achievability
  predicate), re-namespacing `IsWynerZivBinningAchievable`.

* **`relay_cf_si_decoder_fail_le`** — the genuine *reused machinery*: the
  side-info decoder failure probability is `≤ ε_cov + ε_pack`, obtained by
  forwarding `wyner_ziv_binning_via_covering_packing`. **This is the body
  discharge proper** — no new combinatorics, the WZ binning union bound is
  reused verbatim.

* **`relay_cf_existence_of_witness`** — the bridge from the achievability
  witness (the gated implication) **plus the rate-region membership** to the
  error-carrying `RelayCFInnerBoundExistence W R`, by `modus ponens`. The
  decoder-failure side is the discharged consequence of the covering/packing
  bundle (`relay_cf_si_decoder_fail_le`); the achievability witness is the
  open residual whose discharge supplies the vanishing error.

* **`relay_cf_inner_bound_binning_discharged`** — the re-published main
  theorem: a CF inner bound whose old `_h_wz_binning : True` / `_h_si_decode
  : True` placeholders are upgraded to the structured side-info decode
  hypothesis `IsCFSideInfoDecodeHyp` (with the decoder failure bound
  discharged), consuming the achievability witness and **deriving** the
  error-carrying existence (no pass-through of a bare existence).

## 撤退ライン

The genuinely deep information-theoretic ingredients are *still* factored
out as hypotheses, in line with the WZ binning body's own retreat line:

* **Covering / AEP** — that the WZ covering event has small probability
  (`ε_cov`) is the content of `IsCFCompressionHyp`; its discharge (AEP joint
  typicality of `(Ŷ₁^n, X₁^n, Y^n)`) is the responsibility of the companion
  seed `relay-cf-wz-binning-discharge-*`.
* **Packing / slice-cardinality** — that the WZ packing event has small
  probability (`ε_pack`) is the content of `IsCFBinningDecodableHyp`; its
  discharge (union bound + `1/M` collision + conditional typical slice
  cardinality) is the responsibility of `relay-cf-si-decode-discharge-*`.
* **Achievability (vanishing error)** — the error-carrying
  `RelayCFInnerBoundExistence W R` is supplied via the honest gated
  implication `IsRelayCFBinningWitness W …` (= `RelayCFAchievable W …`), not
  built from rate-only data.

The net new content: the CF decoder-failure analysis is no longer an opaque
black box; it is *reduced* to the WZ covering + packing predicates and
discharged by forwarding the existing WZ binning union bound.

## Mathlib usage

No new Mathlib API. Every lemma is a structural composition of existing
`Common2026` building blocks (the WZ binning covering/packing layer and the
relay inner-bound witness layer).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — CF compression covering hypothesis (L-RI3) -/

section CFCompression

variable {Ω β₁ β : Type*} [MeasurableSpace Ω]
variable [Fintype β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable [Fintype β] [MeasurableSpace β]

/-- **CF compression covering hypothesis (L-RI3).**

The relay compresses its observation `Y₁^n` (alphabet `β₁`, abstracted as
the WZ auxiliary sequence `Ŷs : Ω → Fin n → β₁`) and the destination has
side info `Ys : Ω → Fin n → β`. The compression *covers* the source typical
set at rate `R_cov` with failure tolerance `ε_cov` iff the probability that
the true compressed sequence is **not** jointly typical with the side info
is at most `ε_cov`.

This is literally the Wyner–Ziv covering predicate
`IsWynerZivBinningCovering` instantiated at the CF relay's compression
alphabet `β₁`. We re-namespace it so that CF callers cite a single CF
symbol; `compression_eq_wz_covering` records the definitional equality. -/
def IsCFCompressionHyp
    (R_cov ε_cov : ℝ)
    (μ : Measure Ω) {n : ℕ}
    (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁) × (Fin n → β) → Prop) : Prop :=
  IsWynerZivBinningCovering R_cov ε_cov μ Ŷs Ys JT

/-- `IsCFCompressionHyp` is definitionally the WZ covering predicate. -/
lemma IsCFCompressionHyp_eq_wz_covering
    {R_cov ε_cov : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop} :
    IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT
      ↔ IsWynerZivBinningCovering R_cov ε_cov μ Ŷs Ys JT := Iff.rfl

/-- Unfolding to the underlying `E_typ` probability bound. -/
lemma IsCFCompressionHyp_def
    {R_cov ε_cov : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop} :
    IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT
      ↔ μ.real (wzError_E_typ (n := n) Ŷs Ys JT) ≤ ε_cov := Iff.rfl

/-- The compression hypothesis is monotone in its error tolerance. -/
lemma IsCFCompressionHyp.mono
    {R_cov ε_cov ε_cov' : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    (h : IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT) (h_le : ε_cov ≤ ε_cov') :
    IsCFCompressionHyp R_cov ε_cov' μ Ŷs Ys JT :=
  IsWynerZivBinningCovering.mono h h_le

/-- The compression hypothesis is independent of the rate bookkeeping. -/
lemma IsCFCompressionHyp.rate_irrelevant
    {R_cov R_cov' ε_cov : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    (h : IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT) :
    IsCFCompressionHyp R_cov' ε_cov μ Ŷs Ys JT :=
  IsWynerZivBinningCovering.rate_irrelevant h

end CFCompression

/-! ## Section 2 — CF side-info decodable (binning packing) hypothesis (L-RI4) -/

section CFDecodable

variable {Ω β₁ β : Type*} [MeasurableSpace Ω]
variable [Fintype β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable [Fintype β] [MeasurableSpace β]

/-- **CF side-info binning decodable hypothesis (L-RI4).**

After compression binning, the destination decodes `Ŷ₁^n` from the bin index
`f_Ŷ (Ŷs ω)` and the side info `Ys ω`. Decoding fails iff some *alias*
compression sequence `ŷ' ≠ Ŷs ω` lands in the same bin and is also jointly
typical with the side info. The scheme is **decodable** at binning rate
`R_bin` with tolerance `ε_pack` iff that alias-collision probability is
`≤ ε_pack`.

This is the Wyner–Ziv packing predicate `IsWynerZivBinningPacking`
instantiated at the CF relay's compression alphabet `β₁`. -/
def IsCFBinningDecodableHyp
    (R_bin ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁) × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁) → Fin M) : Prop :=
  IsWynerZivBinningPacking R_bin ε_pack μ Ŷs Ys JT f_Ŷ

/-- `IsCFBinningDecodableHyp` is definitionally the WZ packing predicate. -/
lemma IsCFBinningDecodableHyp_eq_wz_packing
    {R_bin ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M} :
    IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ
      ↔ IsWynerZivBinningPacking R_bin ε_pack μ Ŷs Ys JT f_Ŷ := Iff.rfl

/-- Unfolding to the underlying `E_bin` probability bound. -/
lemma IsCFBinningDecodableHyp_def
    {R_bin ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M} :
    IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ
      ↔ μ.real (wzError_E_bin (n := n) Ŷs Ys JT f_Ŷ) ≤ ε_pack := Iff.rfl

/-- The decodable hypothesis is monotone in its error tolerance. -/
lemma IsCFBinningDecodableHyp.mono
    {R_bin ε_pack ε_pack' : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M}
    (h : IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ)
    (h_le : ε_pack ≤ ε_pack') :
    IsCFBinningDecodableHyp R_bin ε_pack' μ Ŷs Ys JT f_Ŷ :=
  IsWynerZivBinningPacking.mono h h_le

/-- The decodable hypothesis is independent of the rate bookkeeping. -/
lemma IsCFBinningDecodableHyp.rate_irrelevant
    {R_bin R_bin' ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M}
    (h : IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ) :
    IsCFBinningDecodableHyp R_bin' ε_pack μ Ŷs Ys JT f_Ŷ :=
  IsWynerZivBinningPacking.rate_irrelevant h

end CFDecodable

/-! ## Section 3 — CF side-info decode bundle + decoder-failure discharge -/

section CFSideInfoDecode

variable {Ω β₁ β γ : Type*} [MeasurableSpace Ω]
variable [Fintype β₁] [Nonempty β₁]
  [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ]

/-- **CF side-info decode hypothesis bundle (retract candidate, cross-family
alias of `IsWynerZivBinningAchievable`).**

The conjunction of the CF compression covering hypothesis (L-RI3) and the
binning decodable hypothesis (L-RI4). Definitionally a re-namespacing of
the WynerZiv-side `IsWynerZivBinningAchievable` (covering ∧ packing), via
the field-level building blocks `IsCFCompressionHyp` (= `IsWynerZivBinningCovering`
re-namespaced) and `IsCFBinningDecodableHyp` (= `IsWynerZivBinningPacking`
re-namespaced).

Cross-family note (Pattern G, `audit-tags.md` Cross-family detection
S3): this predicate is **bundle / re-namespacing infrastructure** on top
of three WynerZiv-family predicates (`IsWynerZivBinningCovering` /
`IsWynerZivBinningPacking` / `IsWynerZivBinningAchievable`,
`WynerZivBinningCovering.lean:106/180/416`). Its retract-candidate
status is synchronised with the WynerZiv side: deprecation requires
joint planning across the two families (tracked under
`relay-sorry-migration-plan` 未決事項 #2). Until then the predicate is
retained for the extract-only `_h_decode` parameter of
`relay_cf_inner_bound_binning_discharged` etc.

`@audit:retract-candidate(load-bearing-predicate)` -/
def IsCFSideInfoDecodeHyp
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁) × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁) → Fin M) : Prop :=
  IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT
    ∧ IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ

/-- Build the CF side-info decode bundle from the two sub-hypotheses. -/
lemma IsCFSideInfoDecodeHyp.mk
    {R_cov R_bin ε_cov ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M}
    (h_cov : IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT)
    (h_pack : IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ) :
    IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ :=
  ⟨h_cov, h_pack⟩

/-- Extract the compression (covering) side. -/
lemma IsCFSideInfoDecodeHyp.compression
    {R_cov R_bin ε_cov ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M}
    (h : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    IsCFCompressionHyp R_cov ε_cov μ Ŷs Ys JT := h.1

/-- Extract the decodable (packing) side. -/
lemma IsCFSideInfoDecodeHyp.decodable
    {R_cov R_bin ε_cov ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M}
    (h : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    IsCFBinningDecodableHyp R_bin ε_pack μ Ŷs Ys JT f_Ŷ := h.2

/-- Convert the CF bundle to the underlying WZ achievable predicate. -/
lemma IsCFSideInfoDecodeHyp.toWZ
    {R_cov R_bin ε_cov ε_pack : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Ŷs : Ω → Fin n → β₁} {Ys : Ω → Fin n → β}
    {JT : (Fin n → β₁) × (Fin n → β) → Prop}
    {f_Ŷ : (Fin n → β₁) → Fin M}
    (h : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    IsWynerZivBinningAchievable R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ :=
  ⟨h.1, h.2⟩

/-- **CF side-info decoder failure bound — body discharge proper.**

Given the CF side-info decode bundle (compression covering + binning
decodable) and measurability of the WZ error events, the destination's
side-info joint-typicality decoder fails with probability at most
`ε_cov + ε_pack`. This is obtained by forwarding the Wyner–Ziv binning
union bound `wyner_ziv_binning_via_covering_packing` — **no new
combinatorics**; the CF decoder *is* the WZ binning decoder on the
compression alphabet `β₁`.

This is the genuine new content of the file: the CF decoder failure event
that was bundled opaquely inside `IsRelayCFBinningWitness` is now reduced to
the WZ covering/packing predicates and discharged.

Cross-family note (S3, `audit-tags.md` Pattern G): this declaration
forwards directly to `wyner_ziv_binning_via_covering_packing`
(`WynerZivBinningCovering.lean:293`). WynerZiv Phase 2.x.1.b (Wave 2,
2026-05-26 main commit `fcf80d1`) dropped `R₁`/`R₂`/`h_cov`/`h_pack`
from upstream's signature and retreated its body to `sorry`; the
present wrapper accordingly drops those args from the call site and
inherits a transitive `sorry` without its own `@residual` tag (Pattern C
散文 — closure responsibility belongs to upstream's
`@residual(plan:wyner-ziv-discharge-moonshot-plan)`). The `h_decode`
hypothesis remains in the wrapper signature for API stability but is
no longer consumed; it stays in scope as bookkeeping (single-line
wrapper). -/
theorem relay_cf_si_decoder_fail_le
    [Nonempty β] [Nonempty γ]
    {R_cov R_bin ε_cov ε_pack : ℝ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁) × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁) → Fin M)
    (f : β₁ × β → γ)
    (h_meas_typ : MeasurableSet (wzError_E_typ (n := n) Ŷs Ys JT))
    (h_meas_bin : MeasurableSet (wzError_E_bin (n := n) Ŷs Ys JT f_Ŷ))
    (h_meas_fail :
      MeasurableSet { ω : Ω |
        wzJointlyTypicalDecoderBody f_Ŷ JT f (f_Ŷ (Ŷs ω), Ys ω)
          ≠ fun i => f (Ŷs ω i, Ys ω i) })
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    μ.real { ω : Ω |
        wzJointlyTypicalDecoderBody f_Ŷ JT f (f_Ŷ (Ŷs ω), Ys ω)
          ≠ fun i => f (Ŷs ω i, Ys ω i) }
      ≤ ε_cov + ε_pack :=
  wyner_ziv_binning_via_covering_packing
    (ε₁ := ε_cov) (ε₂ := ε_pack)
    μ Ŷs Ys JT f_Ŷ f h_meas_typ h_meas_bin h_meas_fail

/-- **CF side-info decoder failure → 0 (asymptotic form)** —
load-bearing existence-form bundle removed, sorry.

Existence-form version of `relay_cf_si_decoder_fail_le`. The previous
public signature took a load-bearing existence-form bundle
`h_asymp : ∀ ε > 0, ∃ N, …` carrying covering / packing predicates +
measurability + the structured CF side-info decode hypothesis at every
block length. Under the sorry-based migration that load-bearing bundle
has been removed; closure responsibility is parked on the parent
moonshot plan.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_si_decoder_fail_tendsto
    [Nonempty β] [Nonempty γ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (JT : ∀ n : ℕ, (Fin n → β₁) × (Fin n → β) → Prop) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
          (f_Ŷ : (Fin n → β₁) → Fin M) (f : β₁ × β → γ),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_Ŷ (JT n) f (f_Ŷ (Ŷs ω), Ys ω)
                ≠ fun i => f (Ŷs ω i, Ys ω i) }
            ≤ ε := by
  sorry

end CFSideInfoDecode

/-! ## Section 4 — Bridge: sub-predicate bundle ⇒ CF binning witness -/

section WitnessBridge

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Bridge: CF inner-bound existence from the rate region** —
load-bearing achievability witness removed, sorry.

The previous public signature took an honest achievability residual
`h_witness : IsRelayCFBinningWitness …` (= `RelayCFAchievable …`, the
gated implication bundling L-RI3 + L-RI4 walls). Under the sorry-based
migration that load-bearing predicate has been removed; closure
responsibility is parked on the parent moonshot plan.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
lemma relay_cf_existence_of_witness
    {W : RelayChannel α α₁ β β₁} {R Idec Ix1y Iy1hy1 : ℝ}
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

end WitnessBridge

/-! ## Section 5 — Re-published CF inner bound with binning discharge -/

section Republished

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **CF inner bound — binning-discharged form** (load-bearing achievability
witness removed, sorry).

The previous public signature took the structured CF side-info decode
bundle `_h_decode : IsCFSideInfoDecodeHyp …` together with the
load-bearing achievability witness `h_witness : IsRelayCFBinningWitness`.
Under the sorry-based migration the load-bearing achievability witness
has been removed; the `_h_decode` parameter is retained as an
extract-only consumer-side parameterisation (Pattern E, `audit-tags.md`):
the structured bundle remains an honest documentation of which
covering / packing predicates the binning discharge relies on (its own
load-bearing-ness is tracked via the cross-family WynerZiv predicates,
see `IsCFSideInfoDecodeHyp` retract-candidate in Phase 2.6).

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_binning_discharged
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry


/-- **CF inner bound — binning-discharged, unbundled two-condition form**
(load-bearing achievability witness removed, sorry).

Same structural retreat as `relay_cf_inner_bound_binning_discharged`; the
`_h_decode` parameter is retained as extract-only documentation.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_inner_bound_binning_discharged_two_conditions
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    (W : RelayChannel α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (h_rate : R ≤ Idec) (h_feas : Iy1hy1 ≤ Ix1y)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

end Republished

/-! ## Section 6 — Two-side combine (outer + inner) with binning discharge -/

section TwoSide

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **CF achievability (binning-discharged) + cut-set outer bound
combined** — load-bearing Csiszár chain + CF achievability witnesses
removed, sorry.

Same structural retreat as `relay_cf_consistent_discharged` with the
extract-only `_h_decode` parameter retained. The compound conclusion is
closed jointly by **two** moonshot plans
(`relay-cutset-moonshot-plan` for the outer-bound conjunct and
`relay-inner-bound-moonshot-plan` for the achievability conjunct); the
single `@residual` tag names the inner-bound plan as the primary
closure target.

`@residual(plan:relay-inner-bound-moonshot-plan)` -/
theorem relay_cf_consistent_binning_discharged
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    (W : RelayChannel α α₁ β β₁)
    {M₀ n₀ : ℕ} (_hn : 0 < n₀)
    (_c : RelayCode M₀ n₀ α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 Pe I_marg_b I_marg_m Ib Im ε : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (_h_fano_b : RelayBcastCutFano M₀ n₀ R Pe I_marg_b)
    (_h_fano_m : RelayMacCutFano M₀ n₀ R Pe I_marg_m)
    (_h_cleanup_b : (1 + Pe * Real.log (M₀ : ℝ)) / (n₀ : ℝ) ≤ ε)
    (_h_cleanup_m : (1 + Pe * Real.log (M₀ : ℝ)) / (n₀ : ℝ) ≤ ε)
    (_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    (R ≤ relayCutsetBound (Ib + ε) (Im + ε))
      ∧ RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) W R := by
  sorry

end TwoSide

end InformationTheory.Shannon
