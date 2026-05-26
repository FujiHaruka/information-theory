import Common2026.Draft.Shannon.BroadcastChannelExistenceBridgeBody

/-!
# BC Bonferroni decay — ℝ≥0∞→ℝ measure reduction + AEP per-event decay (SEED S15)

This file sits on top of `Common2026/Shannon/BroadcastChannelExistenceBridgeBody.lean`
(SEED S7), which discharged the genuine codebook+message double-average swap and
pigeonhole feeding `IsBCRandomCodebookMarkov`, but left the *operational*
predicate `IsBCBonferroniEnsembleDecay` as an explicit retreat line: its slots
carry (a) the `ℝ≥0∞ → ℝ` reduction of the Bonferroni measure terms and (b) the
AEP per-event decay (each of the receiver-1 `F₀..F₃` and receiver-2 `G₀, G₁`
event probabilities tending to `0`).

## What was genuinely open

The bridge body's `IsBCBonferroniEnsembleDecay R₁ R₂` is an *existential* over a
finite codebook ensemble plus a per-event contribution family `contrib`/`δ`,
asserting at every block length `n ≥ N` a sub-`1` averaged total decay
`(Σ_m Σ_k δ k m)/|Msg| < 1`. The bridge body supplied this as a bare caller
hypothesis. The genuine content folded into "supplying the `contrib`/`δ` data"
is exactly the **two retreat steps**:

* **(a) ℝ≥0∞ → ℝ reduction.** The 6 Bonferroni events of
  `BroadcastChannelSuperpositionBody.lean` (receiver-1 `F₀..F₃`, receiver-2
  `G₀, G₁`) have measures living in `ℝ≥0∞`. Their `ENNReal.toReal` images are the
  finite-`ℝ` `contrib`/`δ` family the averaging combinatorics operate on. This
  reduction is `ENNReal.toReal_le_toReal` / `ENNReal.toReal_add` monotonicity,
  given the per-event measures are not `∞` (probability measures).

* **(b) AEP per-event decay.** Each per-event probability tends to `0` as
  `n → ∞` (AEP / joint-typicality). Hence the averaged total — a finite sum of
  `toReal` terms over the 6 events and the message index — tends to `0`, so it is
  eventually `< 1`, which is the operational content of "averaging succeeded".

## Approach

The two retreat steps share a common reusable shape: a *real-valued aggregate
decay sequence* `p : ℕ → ℝ`, `p ≥ 0`, `Tendsto p atTop (𝓝 0)`, that dominates the
averaged total at each `n`. We make this the primitive
`IsBCPerEventAEPDecay R₁ R₂` predicate (strictly more primitive than
`IsBCBonferroniEnsembleDecay`: it exposes the *genuine analytic content* — a
sequence tending to `0` from the AEP — rather than the bare sub-`1` constant). The
main bridge `bc_bonferroni_ensemble_decay_of_perEvent` then performs the genuine
ε-N analysis: `Tendsto p 0 ⇒ ∀ᶠ n, p n < 1`, intersect with the threshold
carrying the codebook ensemble, and discharge `IsBCBonferroniEnsembleDecay`.

The `ℝ≥0∞ → ℝ` reduction (step a) is a standalone reusable lemma
(`bc_measure_term_toReal_le` and its 6-fold aggregate
`bc_bonferroni_avg_toReal_le`): from `ℝ≥0∞` per-event measure bounds it produces
the `ℝ`-level `δ`-bound the averaging combinatorics consume.

## Scope (SEED S15)

* **S15-a — `bc_measure_term_toReal_le` + `bc_bonferroni_avg_toReal_le`**: the
  genuine `ℝ≥0∞ → ℝ` reduction of the Bonferroni measure terms.
* **S15-b — `IsBCPerEventAEPDecay`** (`Prop`): the primitive per-event
  AEP-decay predicate carrying an aggregate decay sequence `p → 0`.
* **S15-c — `bc_bonferroni_ensemble_decay_of_perEvent`**: the genuine ε-N
  bridge `IsBCPerEventAEPDecay → IsBCBonferroniEnsembleDecay`.
* **S15-d — `bc_random_codebook_markov_of_perEvent` +
  `bc_inner_bound_with_perEvent_aep`**: re-publish the random-codebook /
  inner-bound wrappers with the decay discharged from the AEP sequence.

## 撤退ライン

The genuine analytic content (the `ℝ≥0∞ → ℝ` reduction and the `Tendsto → 0 ⇒
eventually < 1` decay) is discharged in full. The *upstream* derivation of the
per-event probability sequences `→ 0` from the AEP machinery
(`macJointlyTypicalSet_prob_tendsto_one`, the receiver-2 JTS AEP) is supplied as
the `Tendsto p atTop (𝓝 0)` slot of `IsBCPerEventAEPDecay` — exactly the genuine
AEP output, packaged as a real sequence rather than re-derived per event here.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — ℝ≥0∞ → ℝ reduction of Bonferroni measure terms (S15-a) -/

section BCMeasureToReal

/-- **S15-a — Per-event `ℝ≥0∞ → ℝ` reduction.**

Given a per-event measure bound `νE ≤ d` in `ℝ≥0∞` with the dominating value `d`
finite (`d ≠ ∞`, e.g. `d ≤ 1` for a probability measure), the `ENNReal.toReal`
image of the event measure is bounded by `d.toReal`. This is the elementary
step that turns the Bonferroni union-bound measures of
`BroadcastChannelSuperpositionBody.lean` (which live in `ℝ≥0∞`) into the
finite-`ℝ` `contrib`/`δ` family the averaging combinatorics of
`BroadcastChannelExistenceBridgeBody.lean` operate on. -/
theorem bc_measure_term_toReal_le {νE d : ℝ≥0∞} (hd : d ≠ ∞) (h : νE ≤ d) :
    νE.toReal ≤ d.toReal :=
  ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hd h) hd |>.mpr h

/-- **S15-a' — Nonnegativity of the reduced term.** The `toReal` of any `ℝ≥0∞`
measure term is nonnegative — the `ℝ`-side `contrib`/`δ` family is automatically
nonnegative, matching the nonnegativity hypotheses of the averaging combinatorics. -/
theorem bc_measure_term_toReal_nonneg (νE : ℝ≥0∞) : 0 ≤ νE.toReal :=
  ENNReal.toReal_nonneg

/-- **S15-a'' — Aggregate `ℝ≥0∞ → ℝ` reduction for the 6-event Bonferroni sum.**

The receiver-1 4-event (`F₀..F₃`) plus receiver-2 2-event (`G₀, G₁`) Bonferroni
union bound `bc_jts_jointErrorProb_le_sum` has the shape
`(δ₀+δ₁+δ₂+δ₃)+(γ₀+γ₁)` in `ℝ≥0∞`. When every dominating term is finite, the
`toReal` of the total is the `ℝ`-sum of the `toReal` terms, and is bounded by the
`ℝ`-sum of the dominating `toReal` values. This is the `ENNReal.toReal_add`-driven
form of the reduction feeding the averaged decay sequence. -/
theorem bc_bonferroni_avg_toReal_le
    {d₀ d₁ d₂ d₃ g₀ g₁ : ℝ≥0∞}
    (h₀ : d₀ ≠ ∞) (h₁ : d₁ ≠ ∞) (h₂ : d₂ ≠ ∞) (h₃ : d₃ ≠ ∞)
    (hg₀ : g₀ ≠ ∞) (hg₁ : g₁ ≠ ∞) :
    ((d₀ + d₁ + d₂ + d₃) + (g₀ + g₁)).toReal
      = ((d₀.toReal + d₁.toReal + d₂.toReal + d₃.toReal)
          + (g₀.toReal + g₁.toReal)) := by
  have hd01 : d₀ + d₁ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨h₀, h₁⟩
  have hd012 : d₀ + d₁ + d₂ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hd01, h₂⟩
  have hd0123 : d₀ + d₁ + d₂ + d₃ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hd012, h₃⟩
  have hg01 : g₀ + g₁ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hg₀, hg₁⟩
  rw [ENNReal.toReal_add hd0123 hg01,
      ENNReal.toReal_add hd012 h₃,
      ENNReal.toReal_add hd01 h₂,
      ENNReal.toReal_add h₀ h₁,
      ENNReal.toReal_add hg₀ hg₁]

end BCMeasureToReal

/-! ## Section 2 — Primitive per-event AEP-decay predicate (S15-b) -/

section BCPerEventAEPDecay

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **S15-b — BC primitive per-event AEP-decay predicate.**

Strictly more primitive than `IsBCBonferroniEnsembleDecay`: instead of asserting
a bare sub-`1` averaged decay constant at every `n`, it exposes the **genuine
analytic content** — a real aggregate decay *sequence* `p : ℕ → ℝ` that

* is nonnegative (`0 ≤ p n`, the `toReal` of measure terms is nonnegative), and
* tends to `0` (`Tendsto p atTop (𝓝 0)`, the AEP per-event decay aggregated over
  the 6 Bonferroni events and the message index) —

together with, beyond a threshold `N`, the rate witness (`M₁, M₂, c` with the
`exp(n Rₖ) ≤ Mₖ` conditions) and the **finite codebook ensemble** with the
per-`(C,m)` Bonferroni decomposition and per-event ensemble decays whose averaged
total is *dominated by* `p n`:

```
(Σ_m Σ_k δ k m)/|Msg| ≤ p n.
```

This is the genuine ensemble-side hypothesis with the analytic decay made
explicit. The `ℝ≥0∞ → ℝ` reduction (S15-a) is what realizes the `δ`/`p` data as
`toReal` of the Bonferroni measures; the AEP supplies `Tendsto p 0`. -/
def IsBCPerEventAEPDecay
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ (p : ℕ → ℝ) (N : ℕ),
    (∀ n, 0 ≤ p n) ∧ Tendsto p atTop (𝓝 0) ∧
    ∀ n ≥ N,
      ∃ (M₁ M₂ : ℕ) (_c : BroadcastCode M₁ M₂ n α β₁ β₂),
        Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
        ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
        ∧ ∃ (Codebook : Type) (_ : Fintype Codebook) (_ : Nonempty Codebook)
            (EventIdx : Type) (_ : Fintype EventIdx)
            (w : Codebook → ℝ)
            (totalPe : Codebook → (Fin M₁ × Fin M₂) → ℝ)
            (contrib : EventIdx → Codebook → (Fin M₁ × Fin M₂) → ℝ)
            (δ : EventIdx → (Fin M₁ × Fin M₂) → ℝ),
          (∀ C, 0 ≤ w C) ∧ (∑ C, w C = 1)
          ∧ IsBCEnsembleErrorDecomp totalPe contrib
          ∧ (∀ k m, ∑ C, w C * contrib k C m ≤ δ k m)
          ∧ (∑ m : Fin M₁ × Fin M₂, ∑ k : EventIdx, δ k m)
              / (Fintype.card (Fin M₁ × Fin M₂) : ℝ) ≤ p n

end BCPerEventAEPDecay

/-! ## Section 3 — Genuine ε-N decay bridge (S15-c) -/

section BCDecayBridge

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **S15-c — Per-event AEP decay → Bonferroni ensemble decay.**

The genuine ε-N bridge: from the primitive per-event AEP-decay predicate
`IsBCPerEventAEPDecay` (carrying the aggregate decay sequence `p → 0` and the
codebook ensemble dominated by `p`), produce `IsBCBonferroniEnsembleDecay`.

The argument: `Tendsto p atTop (𝓝 0)` gives `∀ᶠ n, p n < 1`; intersecting that
`eventually` with the threshold `N` carrying the ensemble data yields a single
threshold beyond which the averaged total decay
`(Σ_m Σ_k δ k m)/|Msg| ≤ p n < 1`. This is the operational content of "the random
codebook averaging succeeded" — derived from the AEP decay, not assumed. -/
theorem bc_bonferroni_ensemble_decay_of_perEvent
    (R₁ R₂ : ℝ)
    (h : IsBCPerEventAEPDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    IsBCBonferroniEnsembleDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := by
  obtain ⟨p, N, hp_nn, hp_tendsto, hN⟩ := h
  -- The genuine ε-N step: `p → 0` so `p n < 1` eventually.
  have h_evt : ∀ᶠ n in atTop, p n < 1 :=
    hp_tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp h_evt
  -- Threshold beyond both the ensemble data and the `< 1` decay.
  refine ⟨max N N', ?_⟩
  intro n hn
  have hn_N : n ≥ N := le_trans (le_max_left N N') hn
  have hn_N' : n ≥ N' := le_trans (le_max_right N N') hn
  obtain ⟨M₁, M₂, c, hM₁, hM₂, Codebook, instFin, instNe, EventIdx, instFinE,
    w, totalPe, contrib, δ, hw_nn, hw_sum, h_decomp, h_event, h_le_p⟩ := hN n hn_N
  refine ⟨M₁, M₂, c, hM₁, hM₂, Codebook, instFin, instNe, EventIdx, instFinE,
    w, totalPe, contrib, δ, hw_nn, hw_sum, h_decomp, h_event, ?_⟩
  -- The averaged total decay is `≤ p n < 1`.
  exact lt_of_le_of_lt h_le_p (hN' n hn_N')

end BCDecayBridge

/-! ## Section 4 — Re-publish wrappers (S15-d) -/

section BCDecayPublish

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **S15-d — Per-event AEP decay → random-codebook Markov.**

Composes the genuine decay bridge (S15-c) with the bridge body's
`bc_random_codebook_markov_of_ensemble` (S7-F): the AEP per-event decay produces
`IsBCRandomCodebookMarkov` with its `errBound` *derived* (no longer a free caller
hypothesis).

Transitive `sorry` via `bc_random_codebook_markov_of_ensemble`
(`@residual(defect:degenerate)`, mac-bc Phase 2.3 retreat). No additional
`@residual` tag attached — closure responsibility is shared with the upstream
declaration's defect marker. -/
theorem bc_random_codebook_markov_of_perEvent
    (R₁ R₂ : ℝ)
    (h : IsBCPerEventAEPDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  bc_random_codebook_markov_of_ensemble
    (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂
    (bc_bonferroni_ensemble_decay_of_perEvent
      (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ h)

/-- **S15-d' — BC random codebook averaging, AEP per-event decay discharge.**

The publish-layer hook closing SEED S15: given the strict rate conditions and the
primitive per-event AEP-decay predicate `IsBCPerEventAEPDecay`, **derive** the
**rate witness** `BCRandomCodebookAveraging`. Composes the decay bridge (S15-c)
with the bridge body's `bc_inner_bound_with_ensemble_averaging` (S7-G).

It deliberately does **not** claim the error-carrying `BCInnerBoundExistence W`:
the rate-only post-averaging witness does not establish `averageErrorProb < ε`
for a specific `W`, so the genuine bridge to achievability is the honest residual
`BCSuperpositionAchievable`, consumed only by the headline
`bc_capacity_region_inner_bound`.

Transitive `sorry` via `bc_inner_bound_with_ensemble_averaging`
(`@residual(plan:mac-bc-sorry-migration-plan)`, Phase 2.2 retreat). No additional
`@residual` tag attached — closure responsibility is shared with the upstream
declaration's `@residual`. -/
theorem bc_inner_bound_with_perEvent_aep
    (R₁ R₂ I_u I_xy : ℝ)
    (h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (h : IsBCPerEventAEPDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  bc_inner_bound_with_ensemble_averaging
    (α := α) (β₁ := β₁) (β₂ := β₂)
    R₁ R₂ I_u I_xy h_strict
    (bc_bonferroni_ensemble_decay_of_perEvent
      (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ h)

/-- **S15-d'' — BC random codebook averaging, AEP per-event decay discharge,
bundled form.**

Variant of `bc_inner_bound_with_perEvent_aep` taking the rate conditions bundled
as the `≤` + `≠` form of `InBCCapacityRegion`, mirroring
`bc_inner_bound_with_ensemble_averaging_bundled` (S7-G').

Transitive `sorry` via `bc_inner_bound_with_ensemble_averaging_bundled`
(`@residual(plan:mac-bc-sorry-migration-plan)`, Phase 2.2 retreat). No additional
`@residual` tag attached — closure responsibility is shared with the upstream
declaration's `@residual`. -/
theorem bc_inner_bound_with_perEvent_aep_bundled
    (R₁ R₂ I_u I_xy : ℝ)
    (h_in_region : InBCCapacityRegion R₁ R₂ I_u I_xy)
    (h_strict₂ : R₂ ≠ I_u)
    (h_strict₁ : R₁ ≠ I_xy)
    (h : IsBCPerEventAEPDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  bc_inner_bound_with_ensemble_averaging_bundled
    (α := α) (β₁ := β₁) (β₂ := β₂)
    R₁ R₂ I_u I_xy h_in_region h_strict₂ h_strict₁
    (bc_bonferroni_ensemble_decay_of_perEvent
      (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ h)

end BCDecayPublish

end InformationTheory.Shannon
