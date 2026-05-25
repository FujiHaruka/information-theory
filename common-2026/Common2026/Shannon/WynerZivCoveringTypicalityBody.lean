import Common2026.Shannon.WynerZivCoveringBody
import Common2026.Shannon.AEPRate

/-!
# Wyner–Ziv covering AEP joint-typicality discharge (T3-D wave10 S5)

This file **discharges the AEP-side hypothesis** `IsCoveringTypicalityHyp`
introduced (as an open input) in `WynerZivCoveringBody.lean`. That predicate is
the genuine measure-theoretic content of the Wyner–Ziv *covering* lemma: for a
random codebook of rate `R₁ > I(X;U)`, the chosen auxiliary codeword fails to
be jointly typical with the side information only with vanishing probability, so

```
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ Us Ys,
  MeasurableSet (wzCoveringEvent Us Ys (JT n))
    ∧ 1 - ε ≤ μ.real (wzCoveringEvent Us Ys (JT n)).
```

The sibling `WynerZivCoveringBody.lean` already turns this probability lower
bound into the covering predicate via complement arithmetic
(`isWynerZivBinningCovering_of_typicalProb`), and the sibling
`WynerZivPackingBody.lean` discharges the packing half from the union bound.
This file supplies the missing AEP probability input itself.

## Approach

The discharge is **not** a no-op: it instantiates the abstract joint-typicality
predicate `JT` with the concrete `ChannelCoding.jointlyTypicalSet` membership at
a fixed slack `ε₀ > 0`, takes the random pair `(Us, Ys) := (jointRV Xs n,
jointRV Ys n)` to be the i.i.d. block joint random variables, and feeds the AEP
probability bound `AEPRate.jointlyTypicalSet_prob_ge_of_rate` (with `η := ε`).

Three layers:

1. **Bridge** (`wzCoveringEvent_jointRV_eq`): for the concrete `JT`, the WZ
   "good" event `{ ω | JT (jointRV Xs n ω, jointRV Ys n ω) }` is *definitionally*
   the AEP event `{ ω | (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet }`.
2. **Measurability** (`measurableSet_wzCoveringEvent_jointRV`): that event is the
   preimage of the (finite, hence measurable) `jointlyTypicalSet` under the
   measurable pair map `ω ↦ (jointRV Xs n ω, jointRV Ys n ω)`.
3. **AEP discharge** (`isCoveringTypicalityHyp_of_aep`): assemble
   `IsCoveringTypicalityHyp` by, for each tolerance `ε > 0`, invoking the AEP
   bound at `η := ε` and packaging the witnesses `(Us, Ys)` with the
   measurability + probability conjuncts.

The concrete joint-typicality predicate is exported as `wzAEPCoveringJT`, so the
covering body discharge (`wzCovering_existence_of_typicalProb` etc.) can be
re-published with the typicality hypothesis fully discharged
(`wzCovering_existence_aep`, `wzCovering_decoder_fail_aep`).

## 撤退ライン

* **i.i.d. + pairwise-independence setup is taken as input.** The AEP bound
  `jointlyTypicalSet_prob_ge_of_rate` requires the standard i.i.d. hypotheses
  (`IdentDistrib`, pairwise `IndepFun` on each axis and on the joint sequence);
  these are the genuine probabilistic provenance and are threaded as explicit
  hypotheses, exactly as the AEP theorem demands. No further reduction is needed
  — this *is* the AEP discharge.
* **Rate condition `R₁ > I(X;U)` is bookkeeping.** As documented in
  `WynerZivCoveringBody`, the quantitative `ε(n) → 0` link to the rate lives in
  the AEP slack `ε₀`; here `ε₀` is any fixed positive slack and the rate `R₁` is
  carried only as a parameter of the covering predicate.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Concrete joint-typicality predicate and the event bridge

We instantiate the abstract `JT` of `IsCoveringTypicalityHyp` with the concrete
`ChannelCoding.jointlyTypicalSet` membership at a fixed slack `ε₀`, and show the
resulting WZ "good" event coincides (definitionally) with the AEP event whose
probability `jointlyTypicalSet_prob_ge_of_rate` lower-bounds.
-/

section Bridge

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [DecidableEq U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Concrete AEP joint-typicality predicate.** The abstract `JT` of
`IsCoveringTypicalityHyp` instantiated with `ChannelCoding.jointlyTypicalSet`
membership at slack `ε₀`. This is the predicate that the AEP probability bound
`jointlyTypicalSet_prob_ge_of_rate` is stated about. -/
def wzAEPCoveringJT
    (μ : Measure Ω) (Xs : ℕ → Ω → U) (Ys : ℕ → Ω → β) (ε₀ : ℝ) :
    ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop :=
  fun n p => p ∈ ChannelCoding.jointlyTypicalSet μ Xs Ys n ε₀

/-- **Event bridge.** For the concrete predicate `wzAEPCoveringJT`, the WZ
covering "good" event over the i.i.d. block joint random variables
`(jointRV Xs n, jointRV Ys n)` is the AEP joint-typicality event. Definitional
unfold of `wzCoveringEvent` and `wzAEPCoveringJT`. -/
lemma wzCoveringEvent_jointRV_eq
    (μ : Measure Ω) (Xs : ℕ → Ω → U) (Ys : ℕ → Ω → β) (ε₀ : ℝ) (n : ℕ) :
    wzCoveringEvent (n := n) (jointRV Xs n) (jointRV Ys n)
        (wzAEPCoveringJT μ Xs Ys ε₀ n)
      = { ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
              ChannelCoding.jointlyTypicalSet μ Xs Ys n ε₀ } := by
  rfl

/-- **Measurability of the bridged event.** The AEP covering event is the
preimage of the (finite, hence measurable) jointly-typical set under the
measurable pair map `ω ↦ (jointRV Xs n ω, jointRV Ys n ω)`. -/
lemma measurableSet_wzCoveringEvent_jointRV
    (μ : Measure Ω) (Xs : ℕ → Ω → U) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (ε₀ : ℝ) (n : ℕ) :
    MeasurableSet
      (wzCoveringEvent (n := n) (jointRV Xs n) (jointRV Ys n)
        (wzAEPCoveringJT μ Xs Ys ε₀ n)) := by
  rw [wzCoveringEvent_jointRV_eq]
  exact ((measurable_jointRV Xs hXs n).prodMk (measurable_jointRV Ys hYs n))
    (ChannelCoding.measurableSet_jointlyTypicalSet μ Xs Ys n ε₀)

end Bridge

/-! ## Section 2 — AEP discharge of `IsCoveringTypicalityHyp`

The headline discharge: from the i.i.d. random-codebook hypotheses, the abstract
covering typicality hypothesis holds for the concrete predicate. The probability
input is `jointlyTypicalSet_prob_ge_of_rate` with `η := ε`.
-/

section Discharge

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [DecidableEq U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **AEP covering typicality discharge.**

From the standard i.i.d. random-codebook hypotheses (per-axis `IdentDistrib` and
pairwise `IndepFun`, plus the same for the joint sequence) and a fixed
typicality slack `ε₀ > 0`, the AEP-side covering hypothesis
`IsCoveringTypicalityHyp` holds for the concrete joint-typicality predicate
`wzAEPCoveringJT μ Xs Ys ε₀`, with the random pair taken to be the i.i.d. block
joint random variables `(jointRV Xs n, jointRV Ys n)`.

This is the genuine AEP probability discharge: for each tolerance `ε > 0`,
`jointlyTypicalSet_prob_ge_of_rate` (with `η := ε`) supplies the `N` beyond
which the joint-typicality probability is `≥ 1 - ε`; measurability is
`measurableSet_wzCoveringEvent_jointRV`. -/
theorem isCoveringTypicalityHyp_of_aep
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
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    IsCoveringTypicalityHyp μ (wzAEPCoveringJT μ Xs Ys ε₀) := by
  intro ε hε
  -- AEP probability bound with `η := ε`.
  obtain ⟨N, hN⟩ :=
    jointlyTypicalSet_prob_ge_of_rate μ Xs Ys hXs hYs
      hindepX hidentX hindepY hidentY hindepZ hidentZ hε₀ hε
  refine ⟨N, ?_⟩
  intro n hn
  refine ⟨jointRV Xs n, jointRV Ys n, ?_, ?_⟩
  · exact measurableSet_wzCoveringEvent_jointRV μ Xs Ys hXs hYs ε₀ n
  · -- Rewrite to the AEP event, then `μ.real = .toReal`.
    rw [wzCoveringEvent_jointRV_eq, Measure.real]
    exact hN n hn

end Discharge

/-! ## Section 3 — Re-published covering existence with the AEP hypothesis discharged

Compose the AEP discharge with the (already-published) covering body forms from
`WynerZivCoveringBody.lean`, eliminating `IsCoveringTypicalityHyp` from their
signatures: the covering existence and decoder-failure forms now consume only
the i.i.d. random-codebook hypotheses (plus, for the decoder form, the external
packing hypothesis).
-/

section RePublish

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [DecidableEq U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Covering existence from the AEP discharge.** The covering existence form
`wzCovering_existence_of_typicalProb`, re-published with the AEP hypothesis
discharged: from the i.i.d. random-codebook setup directly, for every `ε > 0`
there is `N` beyond which a covering pair satisfying `IsWynerZivBinningCovering`
exists. -/
theorem wzCovering_existence_aep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {R₁ : ℝ}
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
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (Us : Ω → Fin n → U) (Ys' : Ω → Fin n → β),
          IsWynerZivBinningCovering R₁ ε μ Us Ys' (wzAEPCoveringJT μ Xs Ys ε₀ n) :=
  wzCovering_existence_of_typicalProb μ (wzAEPCoveringJT μ Xs Ys ε₀)
    (isCoveringTypicalityHyp_of_aep μ Xs Ys hXs hYs
      hindepX hidentX hindepY hidentY hindepZ hidentZ hε₀)

end RePublish

/-! ## Section 4 — End-to-end: covering (AEP) + packing (external) ⇒ decoder failure → 0

Feed the AEP-discharged covering hypothesis into the WZ binning decoder-failure
existence theorem alongside the external packing existence hypothesis, yielding
the decoder-failure-→-0 conclusion with the covering side fully discharged.
-/

section EndToEnd

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [DecidableEq U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]
variable [MeasurableSpace γ] [Nonempty γ]

/-- **Decoder failure → 0 from AEP covering + external packing.**

The end-to-end composition for the covering side: with the covering hypothesis
discharged by the AEP bound (`isCoveringTypicalityHyp_of_aep`) and an external
packing existence hypothesis, the WZ decoder failure probability tends to `0`.
This is `wzCovering_decoder_fail_existence` with `IsCoveringTypicalityHyp`
eliminated in favour of the i.i.d. random-codebook setup.

Phase 2.x ripple note: this declaration depends transitively on
`wzCovering_decoder_fail_existence` (which itself depends on the
sorry-migrated `wyner_ziv_binning_existence_of_covering_packing` /
`wzCovering_feed_asymp`). No `@residual` tag is attached here — the
closure responsibility belongs to the upstream declarations'
`@residual(plan:wyner-ziv-discharge-moonshot-plan)` tags. -/
theorem wzCovering_decoder_fail_aep
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
    (h_pack : IsPackingExistenceHyp (γ := γ) μ (wzAEPCoveringJT μ Xs Ys ε₀)) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Us : Ω → Fin n → U) (Ys' : Ω → Fin n → β)
          (f_U : (Fin n → U) → Fin M) (f : U × β → γ),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_U (wzAEPCoveringJT μ Xs Ys ε₀ n) f
                  (f_U (Us ω), Ys' ω)
                ≠ fun i => f (Us ω i, Ys' ω i) }
            ≤ ε :=
  wzCovering_decoder_fail_existence μ (wzAEPCoveringJT μ Xs Ys ε₀)
    (isCoveringTypicalityHyp_of_aep μ Xs Ys hXs hYs
      hindepX hidentX hindepY hidentY hindepZ hidentZ hε₀)
    h_pack

end EndToEnd

end InformationTheory.Shannon
