import Common2026.Draft.Shannon.WynerZivCoveringTypicalityBody
import Common2026.Draft.Shannon.WynerZivPackingBody

/-!
# Wyner–Ziv decoder-failure assembly: covering (AEP) + packing (S/M) at aligned μ/ε₀
# (T3-D wave10 S14)

This file **assembles the two halves** of the Wyner–Ziv random-binning
achievability argument into the combined decoder-failure → 0 bound, at a single
aligned joint-typicality predicate `JT = wzAEPCoveringJT μ Xs Ys ε₀`:

* the **covering** half (`ε₁`, AEP joint-typicality failure), discharged in
  `WynerZivCoveringTypicalityBody.lean` via `isCoveringTypicalityHyp_of_aep` and
  consumed by `wzCovering_decoder_fail_aep`;
* the **packing** half (`S/M`, random-binning collision / first-moment method),
  discharged in `WynerZivPackingBody.lean` via `wzPacking_isPacking_of_typicality`.

The covering body left the packing side as an **abstract input**
(`IsPackingExistenceHyp`, in `WynerZivCoveringBody.lean`). This file
**discharges that abstraction** from the genuine packing primitives — slice
cardinality bound `IsPackingTypicalityHyp`, per-hash `E_bin` measurability, and
the `S/M → 0` asymptotics — and then feeds the result into
`wzCovering_decoder_fail_aep`, so the end-to-end decoder-failure → 0 statement
no longer carries an opaque packing hypothesis: its only packing input is the
strictly-more-primitive (genuine, non-`True`) slice-cardinality predicate plus
its quantitative asymptotics.

## Approach

Two layers.

1. **`isPackingExistenceHyp_of_packing_data`** — the genuine discharge of
   `IsPackingExistenceHyp`. For each tolerance `ε > 0`, the `S/M → 0` asymptotic
   supplies `N` beyond which `S n · (M n)⁻¹ ≤ ε`; then for *any* covering pair
   `(Us, Ys)` the first-moment method `wzPacking_isPacking_of_typicality`
   extracts a good hash `f_U` with `IsWynerZivBinningPacking 0 (S n · (M n)⁻¹)`.
   Measurability of `E_bin` (= `IsPackingCollisionBoundHyp`) and of the decoder
   failure set are threaded as the standard finite-`Ω` hypotheses. This is the
   union-bound + collision-probability content, *not* a no-op.
2. **`wzDecoderFail_aep_assembled`** — feed the discharged packing into
   `wzCovering_decoder_fail_aep` at the SAME `μ`/`ε₀` (the covering JT predicate
   `wzAEPCoveringJT μ Xs Ys ε₀` is `μ`-dependent, so both halves must be
   instantiated at identical `μ`, `Xs`, `Ys`, `ε₀`). The result: from the i.i.d.
   random-codebook hypotheses (covering provenance) plus the slice-cardinality
   bound and `S/M → 0` (packing provenance), the WZ decoder failure probability
   tends to `0`.

## 撤退ライン

* **Slice cardinality `IsPackingTypicalityHyp` and the `S/M → 0` asymptotic are
  taken as inputs.** They are the genuine packing-side provenance (the concrete
  `S = exp(n(H(U|Y)+2ε))`, `M = exp(n R₂)`, with `R₂ > I(Y;U)` driving
  `S/M → 0`); their *quantitative* discharge lives in a separate typical-slice /
  rate seed. Here they are threaded exactly as `WynerZivPackingBody`'s
  `wyner_ziv_packing_existence` demands — this *is* the assembly, not a stub.
* **Per-`f_U` `E_bin` and decoder-failure measurability** are taken as input
  (automatic in the concrete finite-`Ω` / decidable-`JT` instantiation; carried
  abstractly to keep the body alphabet-agnostic), matching the hypotheses of the
  covering and packing bodies verbatim.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Discharge of the abstract packing existence hypothesis

`WynerZivCoveringBody.IsPackingExistenceHyp` is the opaque packing input that the
covering body's `wzCovering_decoder_fail_existence` (hence `wzCovering_decoder_fail_aep`)
consumes. Here we *produce* it from the genuine packing primitives via the
first-moment method `wzPacking_isPacking_of_typicality`.
-/

section PackingDischarge

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ] [Nonempty γ]

/-- **Discharge of `IsPackingExistenceHyp` from the packing primitives.**

From a per-block bin count `M n` (nonzero), slice cardinality bound `S n ≥ 0`
with `IsPackingTypicalityHyp (S n) (JT n)`, the per-hash `E_bin` and
decoder-failure measurability data, a reconstruction `f`, and the genuine
`S/M → 0` asymptotic, the abstract packing existence hypothesis
`IsPackingExistenceHyp μ JT` holds.

The body is the first-moment method: for any covering pair `(Us, Ys)`,
`wzPacking_isPacking_of_typicality` produces a good hash `f_U` with
`IsWynerZivBinningPacking 0 (S n · (M n)⁻¹)`, and `S n · (M n)⁻¹ ≤ ε` by the
asymptotic. This is the genuine union-bound + collision content, not a no-op. -/
theorem isPackingExistenceHyp_of_packing_data
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop)
    (M : ℕ → ℕ) (hM : ∀ n, NeZero (M n))
    (S : ℕ → ℝ) (hS_nn : ∀ n, 0 ≤ S n)
    (h_slice : ∀ n, IsPackingTypicalityHyp (n := n) (S n) (JT n))
    (f : U × β → γ)
    (h_meas_bin : ∀ (n : ℕ) (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
        (f_U : (Fin n → U) → Fin (M n)),
        MeasurableSet (wzError_E_bin (n := n) Us Ys (JT n) f_U))
    (h_meas_fail : ∀ (n : ℕ) (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
        (f_U : (Fin n → U) → Fin (M n)),
        MeasurableSet { ω : Ω |
          wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
            ≠ fun i => f (Us ω i, Ys ω i) })
    (h_asymp_SM : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, S n * ((M n : ℝ))⁻¹ ≤ ε) :
    IsPackingExistenceHyp (γ := γ) μ JT := by
  intro ε hε
  -- `S n · (M n)⁻¹ ≤ ε` eventually in `n`.
  obtain ⟨N, hN⟩ := h_asymp_SM ε hε
  refine ⟨N, ?_⟩
  intro n hn Us Ys'
  -- First-moment good hash, with packing tolerance `ε₂ := S n · (M n)⁻¹`.
  haveI : NeZero (M n) := hM n
  obtain ⟨f_U, h_pack⟩ :=
    wzPacking_isPacking_of_typicality (R₂ := (0 : ℝ)) μ Us Ys' (JT n)
      (hS_nn n) (h_slice n)
      (fun f_U => h_meas_bin n Us Ys' f_U)
  refine ⟨M n, f_U, f, S n * ((M n : ℝ))⁻¹, hN n hn, ?_, ?_, h_pack⟩
  · exact h_meas_bin n Us Ys' f_U
  · exact h_meas_fail n Us Ys' f_U

end PackingDischarge

/-! ## Section 2 — End-to-end assembly at aligned μ/ε₀

Feed the discharged packing (Section 1) into the covering body's
`wzCovering_decoder_fail_aep`, both at the *same* `μ`-dependent joint-typicality
predicate `wzAEPCoveringJT μ Xs Ys ε₀`.
-/

section EndToEnd

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [DecidableEq U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]
variable [MeasurableSpace γ] [Nonempty γ]

/-- **Wyner–Ziv decoder failure → 0 — covering (AEP) + packing (S/M) assembled.**

The combined decoder-failure bound, with BOTH halves instantiated at the same
`μ`-dependent joint-typicality predicate `wzAEPCoveringJT μ Xs Ys ε₀`:

* **covering** (`ε₁`) is discharged by the AEP joint-typicality bound
  (`isCoveringTypicalityHyp_of_aep`) from the i.i.d. random-codebook hypotheses;
* **packing** (`S/M`) is discharged by the first-moment method
  (`isPackingExistenceHyp_of_packing_data`) from the slice-cardinality bound and
  the `S/M → 0` asymptotic.

The conclusion is `wzCovering_decoder_fail_aep`'s decoder-failure → 0, but with
its external packing hypothesis `IsPackingExistenceHyp` *eliminated* in favour of
the strictly-more-primitive packing primitives.

Phase 2.x ripple note: this declaration depends transitively on
`wzCovering_decoder_fail_aep`, which transitively depends on the
sorry-migrated `wzCovering_feed_asymp` /
`wyner_ziv_binning_existence_of_covering_packing` /
`wyner_ziv_binning_via_covering_packing`. No `@residual` tag is attached
here — the closure responsibility belongs to the upstream declarations'
`@residual(plan:wyner-ziv-discharge-moonshot-plan)` tags. -/
theorem wzDecoderFail_aep_assembled
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → U) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      ChannelCoding.jointSequence Xs Ys i ⟂ᵢ[μ]
        ChannelCoding.jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
        (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    -- packing primitives, at the SAME `μ`-dependent JT `wzAEPCoveringJT μ Xs Ys ε₀`:
    (M : ℕ → ℕ) (hM : ∀ n, NeZero (M n))
    (Sslice : ℕ → ℝ) (hS_nn : ∀ n, 0 ≤ Sslice n)
    (h_slice : ∀ n,
      IsPackingTypicalityHyp (n := n) (Sslice n) (wzAEPCoveringJT μ Xs Ys ε₀ n))
    (f : U × β → γ)
    (h_meas_bin : ∀ (n : ℕ) (Us : Ω → Fin n → U) (Ys' : Ω → Fin n → β)
        (f_U : (Fin n → U) → Fin (M n)),
        MeasurableSet
          (wzError_E_bin (n := n) Us Ys' (wzAEPCoveringJT μ Xs Ys ε₀ n) f_U))
    (h_meas_fail : ∀ (n : ℕ) (Us : Ω → Fin n → U) (Ys' : Ω → Fin n → β)
        (f_U : (Fin n → U) → Fin (M n)),
        MeasurableSet { ω : Ω |
          wzJointlyTypicalDecoderBody f_U (wzAEPCoveringJT μ Xs Ys ε₀ n) f
              (f_U (Us ω), Ys' ω)
            ≠ fun i => f (Us ω i, Ys' ω i) })
    (h_asymp_SM :
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, Sslice n * ((M n : ℝ))⁻¹ ≤ ε) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M' : ℕ)
          (Us : Ω → Fin n → U) (Ys' : Ω → Fin n → β)
          (f_U : (Fin n → U) → Fin M') (g : U × β → γ),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_U (wzAEPCoveringJT μ Xs Ys ε₀ n) g
                  (f_U (Us ω), Ys' ω)
                ≠ fun i => g (Us ω i, Ys' ω i) }
            ≤ ε := by
  -- Discharge the packing existence hypothesis at the SAME `μ`-dependent JT.
  have h_pack :
      IsPackingExistenceHyp (γ := γ) μ (wzAEPCoveringJT μ Xs Ys ε₀) :=
    isPackingExistenceHyp_of_packing_data μ (wzAEPCoveringJT μ Xs Ys ε₀)
      M hM Sslice hS_nn h_slice f h_meas_bin h_meas_fail h_asymp_SM
  -- Feed it into the AEP-covering decoder-failure existence theorem.
  exact wzCovering_decoder_fail_aep μ Xs Ys hXs hYs
    hindepX hidentX hindepY hidentY hindepZ hidentZ hε₀ h_pack

end EndToEnd

end InformationTheory.Shannon
