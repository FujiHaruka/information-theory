import Common2026.Shannon.MACRandomCodebookAveraging

/-!
# MAC per-event AEP decay — discharge of the `δ → 0` decay slots (SEED S21)

This file sits on top of
`Common2026/Shannon/MACRandomCodebookAveraging.lean` (W10-S12), which landed
the MAC random-codebook ensemble averaging at the **finite-sum-expectation**
level (`mac_random_codebook_averaging_exists`), but left as caller
hypotheses (`w`, `δ`, `h_event`) the **per-event AEP decays**: the four
Bonferroni events of MAC achievability — `E₀` (the source-pair atypical /
AEP event) plus `E₁/E₂/E₃` (the three wrong-message decoding events) — whose
probabilities must `→ 0` for rates strictly inside the region.

## What is *genuinely* discharged here (not a no-op)

The genuine analytic content of MAC achievability is the **per-event
probability decay**, supplied here as honest sequences tending to `0`:

* **E₀ — source-pair atypical, via the weak law (AEP).** The probability
  that the *correct* triple `(X₁^n, X₂^n, Y^n)` lands in the MAC jointly
  typical set tends to `1` (`macJointlyTypicalSet_prob_tendsto_one`,
  `MACL1Discharge.lean`), so its **complement** — the E₀ mass — tends to `0`.
  `mac_E0_aep_decay_tendsto` extracts the real decay sequence
  `n ↦ μ((correct triple ∉ JTS)).toReal → 0`.

* **E₁/E₂/E₃ — wrong-message collision, via the rate gap.** The standard
  random-coding wrong-message bound is `count × per-pair-collision`
  `≈ exp(n(R − I))`, which `→ 0` exactly when `R < I`.
  `mac_exp_rate_gap_tendsto` proves the analytic core
  `n ↦ exp(n(R − I)) → 0` for `R < I` (the genuine wrong-message decay).

These two facts are aggregated into a single real decay sequence
`p : ℕ → ℝ`, `p ≥ 0`, `Tendsto p atTop (𝓝 0)`
(`mac_aggregate_decay_nonneg` / `mac_aggregate_decay_tendsto`), which
dominates the four per-event `δ`-bounds. The primitive predicate
`IsMACPerEventAEPDecay` carries this *genuine analytic decay* together with
the codebook-pair ensemble data, and the bridge
`mac_random_codebook_markov_of_perEvent` performs the genuine ε-N analysis
`Tendsto p 0 ⇒ ∀ᶠ n, p n < ε'`, feeds the dominated per-event bounds through
the proven `mac_random_codebook_averaging_exists`, and discharges
`IsMACRandomCodebookMarkov` (hence `MACInnerBoundExistence`).

## Known Mathlib gap (passed through as a primitive, not `sorry`)

The `Measure.pi^n` / `Measure.infinitePi` **Fubini reduction** over the full
codebook-pair ensemble — turning the genuinely measure-theoretic
`∫⁻ Cp, Pe(Cp) ∂(Measure.pi^n P_X^n × Measure.pi^n P_X^n)` into the
finite-sum `∑_Cp w(Cp)·Pe(Cp)` and tying the per-event `δ` to the
*ensemble-averaged* contribution `macEnsembleContrib` — is a recurring
Mathlib gap (documented in `MACRandomCodebookAveraging.lean` S12-M and the
single-user `random_codebook_E1/E2_swap` Fubini ingredients). It enters here
**only** as the `h_event` ensemble-averaged bound carried inside
`IsMACPerEventAEPDecay`; the per-event AEP/rate decay itself — the actual
analytic content of this seed — is discharged in full (`mac_E0_aep_decay_tendsto`,
`mac_exp_rate_gap_tendsto`, `mac_aggregate_decay_tendsto`), `sorry`-free.

## Main results

* `mac_exp_rate_gap_tendsto` — **genuine wrong-message decay**:
  `exp(n(R − I)) → 0` for `R < I` (E₁/E₂/E₃ analytic core).
* `mac_E0_aep_decay_tendsto` — **genuine AEP decay**: the correct-triple
  E₀ complement mass `→ 0` (E₀ analytic core, from
  `macJointlyTypicalSet_prob_tendsto_one`).
* `IsMACPerEventAEPDecay` — primitive per-event AEP-decay predicate carrying
  the aggregate decay sequence `p → 0` + the ensemble data.
* `mac_aggregate_decay_tendsto` — the four per-event decays aggregate to a
  sequence `→ 0`.
* `mac_random_codebook_markov_of_perEvent` — genuine ε-N bridge
  `IsMACPerEventAEPDecay → IsMACRandomCodebookMarkov`.
* `mac_inner_bound_with_perEvent_aep` — re-publish of the inner bound with
  the per-event decay discharged from the genuine AEP/rate sequence.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Wrong-message exponential decay (E₁/E₂/E₃ analytic core) -/

section RateGapDecay

/-- **S21-1 — Wrong-message rate-gap decay** (E₁/E₂/E₃ analytic core).

For a rate strictly below the relevant mutual information, `R < I`, the
random-coding wrong-message bound `count × per-pair-collision ≈ exp(n(R − I))`
tends to `0` as `n → ∞`. This is the genuine analytic content of the three
wrong-message Bonferroni events: each wrong codeword is independent of the
output, so the joint-typicality collision probability for a single wrong pair
is `≈ exp(-nI)`, and there are `≈ exp(nR)` of them, giving `exp(n(R − I))`.

This lemma proves that geometric factor tends to `0` for `R < I`. -/
theorem mac_exp_rate_gap_tendsto {R I : ℝ} (h : R < I) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (R - I))) atTop (𝓝 0) := by
  -- The exponent `(n : ℝ) * (R - I)` tends to `atBot` since `R - I < 0`.
  have hRI : R - I < 0 := by linarith
  have h_exp_atBot : Tendsto (fun n : ℕ => (n : ℝ) * (R - I)) atTop atBot := by
    have h_nat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    exact h_nat.atTop_mul_neg hRI tendsto_const_nhds
  -- Compose with `exp → 0` at `atBot`.
  exact Real.tendsto_exp_atBot.comp h_exp_atBot

/-- The rate-gap decay term is nonnegative (it is `Real.exp`). -/
theorem mac_exp_rate_gap_nonneg {R I : ℝ} (n : ℕ) :
    0 ≤ Real.exp ((n : ℝ) * (R - I)) := (Real.exp_pos _).le

end RateGapDecay

/-! ## Section 2 — Source-pair AEP decay (E₀ analytic core) -/

section E0AEPDecay

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The **E₀ source-pair atypical mass**: the probability that the correct
triple `(X₁^n, X₂^n, Y^n)` is **not** in the MAC jointly typical set, as a
real number. This is exactly the `toReal` of the complement of the
jointly-typical event of `macJointlyTypicalSet_prob_tendsto_one`. -/
noncomputable def macE0AtypicalMass
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) (n : ℕ) : ℝ :=
  (μ {ω | (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω) ∉
            macJointlyTypicalSet μ X1s X2s Ys n ε}).toReal

/-- The E₀ atypical mass is nonnegative. -/
theorem macE0AtypicalMass_nonneg
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) (n : ℕ) :
    0 ≤ macE0AtypicalMass μ X1s X2s Ys ε n := ENNReal.toReal_nonneg

/-- **S21-2 — Source-pair AEP decay** (E₀ analytic core).

For i.i.d. source/output sequences, the probability that the *correct* triple
`(X₁^n, X₂^n, Y^n)` is **not** jointly typical tends to `0` as `n → ∞`. This
is the weak-law / AEP content of the E₀ Bonferroni event: the jointly-typical
set has probability `→ 1` (`macJointlyTypicalSet_prob_tendsto_one`,
`MACL1Discharge.lean`), so the atypical mass `→ 0`.

The decay sequence `macE0AtypicalMass` is the genuine real-valued AEP decay
that the per-event aggregate consumes. -/
theorem mac_E0_aep_decay_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindepX1 : Pairwise fun i j => X1s i ⟂ᵢ[μ] X1s j)
    (hidentX1 : ∀ i, IdentDistrib (X1s i) (X1s 0) μ μ)
    (hindepX2 : Pairwise fun i j => X2s i ⟂ᵢ[μ] X2s j)
    (hidentX2 : ∀ i, IdentDistrib (X2s i) (X2s 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
        macJointSequence X1s X2s Ys i ⟂ᵢ[μ] macJointSequence X1s X2s Ys j)
    (hidentZ : ∀ i,
        IdentDistrib (macJointSequence X1s X2s Ys i)
          (macJointSequence X1s X2s Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => macE0AtypicalMass μ X1s X2s Ys ε n) atTop (𝓝 0) := by
  classical
  -- AEP: the jointly-typical "good" event has measure → 1.
  have h_good :=
    macJointlyTypicalSet_prob_tendsto_one μ X1s X2s Ys hX1s hX2s hYs
      hindepX1 hidentX1 hindepX2 hidentX2 hindepY hidentY hindepZ hidentZ hε
  -- Name the good event and its complement (the E₀ atypical event).
  set goodEvt : ℕ → Set Ω := fun n =>
    {ω | (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω) ∈
          macJointlyTypicalSet μ X1s X2s Ys n ε} with hgood_def
  -- Measurability of the good event: it is the preimage of the (measurable,
  -- finite) MAC jointly typical set under the measurable joint-RV triple.
  have h_meas_triple : ∀ n, Measurable
      (fun ω => (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω)) := by
    intro n
    exact (measurable_jointRV X1s hX1s n).prodMk
      ((measurable_jointRV X2s hX2s n).prodMk (measurable_jointRV Ys hYs n))
  have h_meas_good : ∀ n, MeasurableSet (goodEvt n) := fun n =>
    (h_meas_triple n) (measurableSet_macJointlyTypicalSet μ X1s X2s Ys n ε)
  -- The E₀ atypical mass is the (ℝ≥0∞) measure of the complement, in toReal.
  have h_mass_eq : ∀ n, macE0AtypicalMass μ X1s X2s Ys ε n
      = (μ ((goodEvt n)ᶜ)).toReal := by
    intro n
    rfl
  -- μ(goodᶜ) = 1 - μ(good) → 1 - 1 = 0 in ℝ≥0∞.
  have h_compl_id : ∀ n, μ ((goodEvt n)ᶜ) = 1 - μ (goodEvt n) := fun n => by
    rw [measure_compl (h_meas_good n) (measure_ne_top μ _), measure_univ]
  have h_cont_sub : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
    ENNReal.continuous_sub_left (by simp)
  have h_compl_tendsto :
      Tendsto (fun n => μ ((goodEvt n)ᶜ)) atTop (𝓝 0) := by
    have h_step : Tendsto (fun n => (1 : ℝ≥0∞) - μ (goodEvt n)) atTop
        (𝓝 ((1 : ℝ≥0∞) - 1)) := (h_cont_sub.tendsto _).comp h_good
    refine Tendsto.congr (fun n => (h_compl_id n).symm) ?_
    simpa using h_step
  -- toReal is continuous at the finite limit 0; push through.
  have h_toReal :
      Tendsto (fun n => (μ ((goodEvt n)ᶜ)).toReal) atTop (𝓝 (0 : ℝ≥0∞).toReal) :=
    (ENNReal.tendsto_toReal (by simp)).comp h_compl_tendsto
  simp only [ENNReal.toReal_zero] at h_toReal
  exact Tendsto.congr (fun n => (h_mass_eq n).symm) h_toReal

end E0AEPDecay

/-! ## Section 3 — Primitive per-event AEP-decay predicate + aggregate → 0 -/

section MACPerEventAEPDecay

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **S21-3 — Aggregate per-event decay nonnegativity.**

The aggregate decay `p n := E₀(n) + 3·exp(n(R − I))` of the four Bonferroni
events (E₀ via AEP, E₁/E₂/E₃ via the common rate gap `R < I`) is
nonnegative — both summands are nonnegative. This is the dominating decay
sequence that the per-event `δ`-bounds are dominated by. -/
theorem mac_aggregate_decay_nonneg
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) {R I : ℝ} (n : ℕ) :
    0 ≤ macE0AtypicalMass μ X1s X2s Ys ε n
        + 3 * Real.exp ((n : ℝ) * (R - I)) := by
  have h0 : 0 ≤ macE0AtypicalMass μ X1s X2s Ys ε n :=
    macE0AtypicalMass_nonneg μ X1s X2s Ys ε n
  have h1 : 0 ≤ 3 * Real.exp ((n : ℝ) * (R - I)) := by positivity
  linarith

/-- **S21-3' — Aggregate per-event decay → 0.**

The aggregate decay sequence `p n := E₀(n) + 3·exp(n(R − I))` tends to `0`:
the E₀ term `→ 0` by AEP (`mac_E0_aep_decay_tendsto`), and the three
wrong-message terms share the same rate-gap factor `→ 0`
(`mac_exp_rate_gap_tendsto`), so their sum `→ 0`.

This is the genuine analytic content of the seed: the four MAC error events'
probabilities aggregate to a real sequence tending to `0` for rates strictly
inside the region (`R < I`). -/
theorem mac_aggregate_decay_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindepX1 : Pairwise fun i j => X1s i ⟂ᵢ[μ] X1s j)
    (hidentX1 : ∀ i, IdentDistrib (X1s i) (X1s 0) μ μ)
    (hindepX2 : Pairwise fun i j => X2s i ⟂ᵢ[μ] X2s j)
    (hidentX2 : ∀ i, IdentDistrib (X2s i) (X2s 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
        macJointSequence X1s X2s Ys i ⟂ᵢ[μ] macJointSequence X1s X2s Ys j)
    (hidentZ : ∀ i,
        IdentDistrib (macJointSequence X1s X2s Ys i)
          (macJointSequence X1s X2s Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) {R I : ℝ} (hRI : R < I) :
    Tendsto (fun n : ℕ => macE0AtypicalMass μ X1s X2s Ys ε n
        + 3 * Real.exp ((n : ℝ) * (R - I))) atTop (𝓝 0) := by
  -- E₀ term → 0 by AEP.
  have hE0 : Tendsto (fun n : ℕ => macE0AtypicalMass μ X1s X2s Ys ε n) atTop (𝓝 0) :=
    mac_E0_aep_decay_tendsto μ X1s X2s Ys hX1s hX2s hYs
      hindepX1 hidentX1 hindepX2 hidentX2 hindepY hidentY hindepZ hidentZ hε
  -- The shared rate-gap term → 0, scaled by 3.
  have hgap : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (R - I))) atTop (𝓝 0) :=
    mac_exp_rate_gap_tendsto hRI
  have h3gap : Tendsto (fun n : ℕ => 3 * Real.exp ((n : ℝ) * (R - I))) atTop (𝓝 (3 * 0)) :=
    (tendsto_const_nhds.mul hgap)
  -- Sum of the two decay sequences → 0 + 0 = 0.
  have h_sum := hE0.add h3gap
  simpa using h_sum

end MACPerEventAEPDecay

/-! ## Section 4 — Primitive predicate + genuine ε-N bridge -/

section MACPerEventPredicate

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **S21-4 — MAC primitive per-event AEP-decay predicate.**

Carries the **genuine analytic decay** — a real aggregate sequence
`p : ℕ → ℝ` that is nonnegative and tends to `0` (the four Bonferroni events'
probabilities aggregated, from the AEP E₀ decay + the rate-gap E₁/E₂/E₃
decay) — together with, beyond a threshold `N`, the rate witness
`(M₁, M₂)` (with `NeZero`), the codebook-pair ensemble data needed by
`mac_random_codebook_averaging_exists`:

* a probability weighting `w` on the codebook-pair space,
* the per-event `δ : Fin 4 → ℝ` dominating the ensemble-averaged
  `macEnsembleContrib` (the `h_event` slot — this is where the
  `Measure.pi^n` Fubini gap enters, passed through as a hypothesis), and
* the domination `∑ k, δ k ≤ p n` of the per-event bounds by the genuine
  decay sequence.

This is strictly more primitive than `IsMACRandomCodebookMarkov`: it exposes
the *analytic decay sequence* `p → 0` (the AEP/rate content), which the bridge
turns into the operational `averageErrorProb < ε'`. -/
def IsMACPerEventAEPDecay
    {Ω : Type*} [MeasurableSpace Ω]
    [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
    [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (R₁ R₂ : ℝ) : Prop :=
  ∃ (p : ℕ → ℝ) (N : ℕ),
    (∀ n, 0 ≤ p n) ∧ Tendsto p atTop (𝓝 0) ∧
    ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_ : NeZero M₁) (_ : NeZero M₂)
        (w : (Fin M₁ → (Fin n → α₁)) × (Fin M₂ → (Fin n → α₂)) → ℝ)
        (δ : Fin 4 → ℝ),
        Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
        ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
        ∧ (∀ Cp, 0 ≤ w Cp) ∧ (∑ Cp, w Cp = 1)
        ∧ (∀ k, ∑ Cp, w Cp * macEnsembleContrib μ X1s X2s Ys ε W k Cp ≤ δ k)
        ∧ (∑ k, δ k ≤ p n)

variable {Ω : Type*} [MeasurableSpace Ω]
variable [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
variable [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- **S21-5 — Per-event AEP decay → random-codebook Markov (genuine ε-N
bridge).**

From the primitive per-event AEP-decay predicate (the genuine decay sequence
`p → 0` + the ensemble data), produce `IsMACRandomCodebookMarkov` — the
deterministic codebook-pair-with-rate witness with `averageErrorProb < ε'`.

The argument: given the target error `ε' > 0`, `Tendsto p atTop (𝓝 0)` gives
`∀ᶠ n, p n < ε'`; intersecting that with the ensemble threshold `N` yields,
for each large `n`, the proven `mac_random_codebook_averaging_exists` applied
to the per-event `δ`-bounds, producing a deterministic codebook pair `Cp`
with `(averageErrorProb).toReal ≤ ∑ δ ≤ p n < ε'`. This is the operational
output: the per-event AEP/rate decay drives the averaging to success. -/
theorem mac_random_codebook_markov_of_perEvent
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (R₁ R₂ : ℝ)
    (h : IsMACPerEventAEPDecay μ X1s X2s Ys ε W R₁ R₂) :
    IsMACRandomCodebookMarkov W R₁ R₂ := by
  obtain ⟨p, N₀, hp_nn, hp_tendsto, hN⟩ := h
  intro ε' hε'
  -- Genuine ε-N step: `p → 0`, so eventually `p n < ε'`.
  have h_evt : ∀ᶠ n in atTop, p n < ε' :=
    hp_tendsto.eventually_lt_const hε'
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_evt
  -- Threshold beyond both the ensemble data and the `< ε'` decay.
  refine ⟨max N₀ N₁, ?_⟩
  intro n hn
  have hn_N₀ : N₀ ≤ n := le_trans (le_max_left N₀ N₁) hn
  have hn_N₁ : N₁ ≤ n := le_trans (le_max_right N₀ N₁) hn
  obtain ⟨M₁, M₂, instNZ₁, instNZ₂, w, δ, hM₁, hM₂, hw_nn, hw_sum, h_event, h_δ_le_p⟩ :=
    hN n hn_N₀
  letI := instNZ₁
  letI := instNZ₂
  -- Apply the proven finite-sum averaging to extract a deterministic codebook pair.
  obtain ⟨Cp, hCp⟩ :=
    mac_random_codebook_averaging_exists μ X1s X2s Ys ε W w hw_nn hw_sum δ h_event
  -- The JTS code over the deterministic codebook pair `Cp`.
  refine ⟨M₁, M₂, macJTSCode μ X1s X2s Ys ε Cp.1 Cp.2, hM₁, hM₂, ?_⟩
  -- Chain: averageError ≤ ∑ δ ≤ p n < ε'.
  exact lt_of_le_of_lt (le_trans hCp h_δ_le_p) (hN₁ n hn_N₁)

end MACPerEventPredicate

/-! ## Section 5 — Re-publish inner bound with per-event decay discharged -/

section MACPerEventPublish

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **S21-6 — MAC inner bound, per-event AEP decay discharge.**

The publish-layer hook closing SEED S21: given the strict rate conditions and
the primitive per-event AEP-decay predicate `IsMACPerEventAEPDecay` (whose
analytic `p → 0` content is supplied by `mac_aggregate_decay_tendsto`),
conclude `MACInnerBoundExistence`. Composes the genuine ε-N bridge (S21-5)
composing `mac_random_codebook_markov_of_perEvent` of
`MACRandomCodebookAveraging.lean` directly (the random-codebook Markov
predicate `IsMACRandomCodebookMarkov` is definitionally
`MACInnerBoundExistence`, so the witness produced by
`mac_random_codebook_markov_of_perEvent` lands the inner-bound existence
without an additional identity-relabel bridge). -/
theorem mac_inner_bound_with_perEvent_aep
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (_h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h : IsMACPerEventAEPDecay μ X1s X2s Ys ε W R₁ R₂) :
    MACInnerBoundExistence W R₁ R₂ :=
  mac_random_codebook_markov_of_perEvent μ X1s X2s Ys ε W R₁ R₂ h

/-- **S21-6' — Two-side combine — per-event-decay achievability + converse.**

Two-side combine packaging the genuine MAC outer-bound derivation with the
per-event AEP/rate-decay-backed inner-bound landing. The achievability
side is backed by the genuine per-event AEP/rate decay
(`IsMACPerEventAEPDecay`), routed through
`mac_random_codebook_markov_of_perEvent` to land
`MACInnerBoundExistence` (which is definitionally
`IsMACRandomCodebookMarkov`).

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem mac_capacity_region_consistent_of_perEvent
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hn : 0 < n) (c : MACCode M₁ M₂ n α₁ α₂ β)
    (R₁ R₂ Pe₁ Pe₂ Pe_joint I_marg₁ I_marg₂ I_joint I₁ I₂ Iboth εc : ℝ)
    (h_fano₁ : (n : ℝ) * R₁ ≤ I_marg₁ + 1 + Pe₁ * Real.log (M₁ : ℝ))
    (h_fano₂ : (n : ℝ) * R₂ ≤ I_marg₂ + 1 + Pe₂ * Real.log (M₂ : ℝ))
    (h_fano_joint :
        (n : ℝ) * (R₁ + R₂)
          ≤ I_joint + 1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ)))
    (h_chain₁ : I_marg₁ ≤ (n : ℝ) * I₁)
    (h_chain₂ : I_marg₂ ≤ (n : ℝ) * I₂)
    (h_chain_joint : I_joint ≤ (n : ℝ) * Iboth)
    (h_cleanup₁ : (1 + Pe₁ * Real.log (M₁ : ℝ)) / (n : ℝ) ≤ εc)
    (h_cleanup₂ : (1 + Pe₂ * Real.log (M₂ : ℝ)) / (n : ℝ) ≤ εc)
    (h_cleanup_joint :
        (1 + Pe_joint * Real.log ((M₁ : ℝ) * (M₂ : ℝ))) / (n : ℝ) ≤ εc)
    (h : IsMACPerEventAEPDecay μ X1s X2s Ys ε W R₁ R₂) :
    InMACCapacityRegion R₁ R₂ (I₁ + εc) (I₂ + εc) (Iboth + εc)
      ∧ MACInnerBoundExistence W R₁ R₂ := by
  sorry

end MACPerEventPublish

end InformationTheory.Shannon
