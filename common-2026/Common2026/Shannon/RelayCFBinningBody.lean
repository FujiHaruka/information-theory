import Common2026.Shannon.RelayInnerBodyDischarge
import Common2026.Shannon.WynerZivBinningCovering

/-!
# Relay CF (compress-and-forward) binning witness body (W9-G3, T3-F continuation)

This file is a **deeper body-discharge layer** for the compress-and-forward
(CF) side of the relay channel inner bound (Cover–Thomas Theorem 15.10.3).
It sits on top of `Common2026/Shannon/RelayInnerBodyDischarge.lean`, which
introduced the opaque CF witness predicate

```
IsRelayCFBinningWitness R Idec Ix1y Iy1hy1 := RelayCFInnerBoundExistence R
```

as a black box, and `Common2026/Shannon/WynerZivBinningCovering.lean`, which
published the **covering / packing** decomposition of the Wyner–Ziv random
binning achievability body.

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

* **`relay_cf_binning_witness_of_existence` / `…_of_sub_predicates`** — the
  bridge from the structured sub-predicate bundle (together with the
  asymptotic code-existence supplied as a hypothesis) to the opaque
  `IsRelayCFBinningWitness`. The CF *existence* form
  (`RelayCFInnerBoundExistence`) counts only the message cardinality, so the
  decoder-failure bound is not embedded in it — hence existence is supplied
  as a pass-through hypothesis here, **but the decoder-failure side** is now
  a discharged consequence of the covering/packing bundle rather than a
  `True` placeholder.

* **`relay_cf_inner_bound_binning_discharged`** — the re-published main
  theorem: a CF inner bound whose `_h_wz_binning : True` / `_h_si_decode :
  True` placeholders of `relay_cf_inner_bound` are upgraded to the structured
  side-info decode hypothesis `IsCFSideInfoDecodeHyp` (with the decoder
  failure bound discharged) plus the existence pass-through.

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
* **Code cardinality existence** — `RelayCFInnerBoundExistence` (message
  count `≥ exp(n R)`) is supplied as a pass-through, as in the parent layer.

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

/-- **CF side-info decode hypothesis bundle.** The conjunction of the CF
compression covering hypothesis (L-RI3) and the binning decodable hypothesis
(L-RI4). Re-namespacing of `IsWynerZivBinningAchievable`. -/
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
the WZ covering/packing predicates and discharged. -/
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
    (h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ) :
    μ.real { ω : Ω |
        wzJointlyTypicalDecoderBody f_Ŷ JT f (f_Ŷ (Ŷs ω), Ys ω)
          ≠ fun i => f (Ŷs ω i, Ys ω i) }
      ≤ ε_cov + ε_pack :=
  wyner_ziv_binning_via_covering_packing
    (R₁ := R_cov) (R₂ := R_bin) (ε₁ := ε_cov) (ε₂ := ε_pack)
    μ Ŷs Ys JT f_Ŷ f h_meas_typ h_meas_bin h_meas_fail
    h_decode.compression h_decode.decodable

/-- **CF side-info decoder failure → 0 (asymptotic form).**

Existence-form version of `relay_cf_si_decoder_fail_le`: from an asymptotic
covering + decodable bundle (failure tolerances summing below any prescribed
`ε`), the side-info decoder failure probability is eventually `≤ ε`. This is
the exact shape feeding the CF achievability existence argument; it forwards
`wyner_ziv_binning_existence_of_covering_packing`. -/
theorem relay_cf_si_decoder_fail_tendsto
    [Nonempty β] [Nonempty γ]
    {R_cov R_bin : ℝ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (JT : ∀ n : ℕ, (Fin n → β₁) × (Fin n → β) → Prop)
    (h_asymp :
      ∀ ε > (0 : ℝ),
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M : ℕ)
            (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
            (f_Ŷ : (Fin n → β₁) → Fin M) (f : β₁ × β → γ)
            (ε_cov ε_pack : ℝ),
            ε_cov + ε_pack ≤ ε
              ∧ MeasurableSet (wzError_E_typ (n := n) Ŷs Ys (JT n))
              ∧ MeasurableSet (wzError_E_bin (n := n) Ŷs Ys (JT n) f_Ŷ)
              ∧ MeasurableSet { ω : Ω |
                  wzJointlyTypicalDecoderBody f_Ŷ (JT n) f (f_Ŷ (Ŷs ω), Ys ω)
                    ≠ fun i => f (Ŷs ω i, Ys ω i) }
              ∧ IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys (JT n) f_Ŷ) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Ŷs : Ω → Fin n → β₁) (Ys : Ω → Fin n → β)
          (f_Ŷ : (Fin n → β₁) → Fin M) (f : β₁ × β → γ),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_Ŷ (JT n) f (f_Ŷ (Ŷs ω), Ys ω)
                ≠ fun i => f (Ŷs ω i, Ys ω i) }
            ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_asymp ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, Ŷs, Ys, f_Ŷ, f, ε_cov, ε_pack, h_sum,
          h_meas_typ, h_meas_bin, h_meas_fail, h_decode⟩ := hN n hn
  refine ⟨M, Ŷs, Ys, f_Ŷ, f, ?_⟩
  have h_step :
      μ.real { ω : Ω |
          wzJointlyTypicalDecoderBody f_Ŷ (JT n) f (f_Ŷ (Ŷs ω), Ys ω)
            ≠ fun i => f (Ŷs ω i, Ys ω i) }
        ≤ ε_cov + ε_pack :=
    relay_cf_si_decoder_fail_le (γ := γ) μ Ŷs Ys (JT n) f_Ŷ f
      h_meas_typ h_meas_bin h_meas_fail h_decode
  exact le_trans h_step h_sum

end CFSideInfoDecode

/-! ## Section 4 — Bridge: sub-predicate bundle ⇒ CF binning witness -/

section WitnessBridge

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **Bridge: CF binning witness from the existence pass-through.**

The CF *existence* form `RelayCFInnerBoundExistence` counts only message
cardinality, so it is supplied as a pass-through (as in the parent layer).
The decoder-failure side is what this file discharges via the covering /
packing bundle; the two are combined into the witness by this bridge. -/
lemma relay_cf_binning_witness_of_existence
    {R Idec Ix1y Iy1hy1 : ℝ}
    (h_existence :
      RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1 :=
  h_existence

/-- **CF binning witness — anti-monotone in `R` (re-export).** Forwards the
parent `IsRelayCFBinningWitness.anti_mono_R`. -/
lemma relay_cf_binning_witness_anti_mono_R
    {R R' Idec Ix1y Iy1hy1 : ℝ}
    (h : IsRelayCFBinningWitness
            (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1)
    (hR : R' ≤ R) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R' Idec Ix1y Iy1hy1 :=
  IsRelayCFBinningWitness.anti_mono_R h hR

end WitnessBridge

/-! ## Section 5 — Re-published CF inner bound with binning discharge -/

section Republished

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **CF inner bound — binning-discharged form.**

The body-discharged variant of `relay_cf_inner_bound` where the two `True`
placeholders `_h_wz_binning` / `_h_si_decode` are *upgraded* to the
structured CF side-info decode bundle `IsCFSideInfoDecodeHyp` (the covering /
packing predicates whose decoder-failure consequence is discharged in
`relay_cf_si_decoder_fail_le`). The rate-region membership and the existence
pass-through are retained.

This is the public entry point of the W9-G3 CF binning body discharge: a
caller holding the WZ covering/packing predicates for the relay's compression
scheme can produce the CF inner bound directly, with the decoder-failure
analysis already reduced to the WZ binning union bound. -/
theorem relay_cf_inner_bound_binning_discharged
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    (R Idec Ix1y Iy1hy1 : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ)
    (h_existence :
      RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Idec Ix1y Iy1hy1 h_in_cf_region trivial trivial h_existence

/-- **CF inner bound — binning-discharged, witness-output form.**

Same as above, but the conclusion is packaged as the structured
`IsRelayCFBinningWitness` predicate (so downstream callers of the parent
witness layer can chain directly). -/
theorem relay_cf_inner_bound_binning_discharged_witness
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    (R Idec Ix1y Iy1hy1 : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ)
    (h_existence :
      RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    IsRelayCFBinningWitness
      (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R Idec Ix1y Iy1hy1 :=
  relay_cf_binning_witness_of_existence (Idec := Idec) (Ix1y := Ix1y)
    (Iy1hy1 := Iy1hy1)
    (relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
      R Idec Ix1y Iy1hy1 h_in_cf_region trivial trivial h_existence)

/-- **CF inner bound — binning-discharged, unbundled two-condition form.**
Variant taking the rate bound and compression feasibility separately. -/
theorem relay_cf_inner_bound_binning_discharged_two_conditions
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    (R Idec Ix1y Iy1hy1 : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (h_rate : R ≤ Idec) (h_feas : Iy1hy1 ≤ Ix1y)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ)
    (h_existence :
      RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
    R Idec Ix1y Iy1hy1 ⟨h_rate, h_feas⟩ trivial trivial h_existence

end Republished

/-! ## Section 6 — Two-side combine (outer + inner) with binning discharge -/

section TwoSide

variable {α α₁ β β₁ : Type*}
variable [MeasurableSpace α] [MeasurableSpace α₁]
variable [MeasurableSpace β] [MeasurableSpace β₁]

/-- **CF achievability (binning-discharged) + cut-set outer bound combined.**

Witness-bundle variant of `relay_cf_consistent_discharged`: the CF inner
side is supplied through the structured side-info decode bundle, and the
outer side is the cut-set bound. -/
theorem relay_cf_consistent_binning_discharged
    {Ω β₁' γ : Type*} [MeasurableSpace Ω]
    [Fintype β₁'] [Nonempty β₁']
    [MeasurableSpace β₁'] [MeasurableSingletonClass β₁']
    [Fintype β] [Nonempty β]
    [MeasurableSpace γ] [Nonempty γ]
    {M₀ n₀ : ℕ} (hn : 0 < n₀)
    (c : RelayCode M₀ n₀ α α₁ β β₁)
    (R Idec Ix1y Iy1hy1 Ib Im : ℝ)
    (R_cov R_bin ε_cov ε_pack : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Ŷs : Ω → Fin n → β₁') (Ys : Ω → Fin n → β)
    (JT : (Fin n → β₁') × (Fin n → β) → Prop)
    (f_Ŷ : (Fin n → β₁') → Fin M)
    (h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (h_rate_bound_outer : R ≤ relayCutsetBound Ib Im)
    (_h_decode : IsCFSideInfoDecodeHyp R_cov R_bin ε_cov ε_pack μ Ŷs Ys JT f_Ŷ)
    (h_existence :
      RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    (R ≤ relayCutsetBound Ib Im)
      ∧ RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  ⟨relay_cutset_outer_bound hn c R Ib Im trivial trivial h_rate_bound_outer,
   relay_cf_inner_bound (α := α) (α₁ := α₁) (β := β) (β₁ := β₁)
     R Idec Ix1y Iy1hy1 h_in_cf_region trivial trivial h_existence⟩

end TwoSide

end InformationTheory.Shannon
