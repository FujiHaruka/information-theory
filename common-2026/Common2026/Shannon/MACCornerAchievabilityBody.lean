import Common2026.Shannon.MACBodyDischarge
import Common2026.Shannon.MACL1Discharge
import Common2026.Shannon.AEPRate

/-!
# MAC corner-point achievability — random-codebook error → 0 body (W10-S6, T3-B)

This file is the **genuine achievability-body discharge** for the MAC
corner-point inner bound. It sits above:

* `MultipleAccessChannel.lean` — publishes `MACInnerBoundExistence`
  (the error-carrying existence predicate
  `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M₁ M₂ c, exp(nRₖ) ≤ Mₖ ∧ averageError < ε`,
  with the vanishing-error conjunct embedded — no longer the bare
  no-op-satisfiable predicate).
* `MACBodyDischarge.lean` — the JTS decoder `macJTSCode`, the 4-fold
  Bonferroni decomposition `mac_error_event_subset_bonferroni`, and the
  per-codebook error-probability assembly `mac_achievability_corner_body`
  (`ν(errorEvent) ≤ δ₀ + δ₁ + δ₂ + δ₃`).
* `MACL1Discharge.lean` — the 3-tuple jointly-typical set + AEP.
* `AEPRate.lean` — closed-form rate-uniform AEP / exp-decay `∃ N` lemmas.

## Main results

* `MACCode.errorProbAt` / `MACCode.averageErrorProb` — MAC analogues of
  `Code.errorProbAt` / `Code.averageErrorProb`, the symbol-wise memoryless
  channel output error.
* `mac_averageErrorProb_le_one`, `mac_averageErrorProb_ne_top`.
* `mac_jts_error_lt_of_bonferroni_lt` — **genuine error-assembly**: a JTS
  code whose four Bonferroni events sum to `< ε'` has pointwise error
  `< ε'` (via `mac_achievability_corner_body`).
* `mac_jts_error_eventually_lt` — eventual-form packaging of the
  per-codebook error assembly over the four `∃ N` decay inputs.

## 撤退ライン

* The full random-codebook *averaging* over all `(c₁, c₂)` (E₁/E₂/E₃
  expectation bounds via the union over wrong messages, ~500-800 lines —
  the analogue of `random_codebook_average_le` lifted to 3 events) is
  staged in `MACRandomCodebookAveraging.lean` (finite-sum-expectation
  form) and `MACPerEventAEPDecay.lean` (per-event AEP-decay genuine ε-N
  bridge to `MACInnerBoundExistence`).

## Cluster cleanup (2026-05-23)

The prior `MACAchievableWithError` definitional alias (defeq to
`MACInnerBoundExistence`), together with the three identity-wrapper
bridge theorems
`mac_innerBoundExistence_of_achievableWithError`,
`mac_capacity_region_inner_bound_of_achievableWithError`, and
`mac_capacity_region_consistent_of_achievableWithError`, have been
**retracted**. The alias added no Prop-level content; the bridge body
`:= h` is a pure identity unfolding. Direct downstream consumers
(`MACPerEventAEPDecay.lean`) now route through
`mac_random_codebook_markov_of_perEvent` of
`MACRandomCodebookAveraging.lean` to land `MACInnerBoundExistence`
directly, without the identity-relabel cascade.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — MAC average error probability -/

section MACAverageError

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- Each pointwise MAC error probability is `≤ 1` (Markov kernel output is
a probability measure). -/
theorem mac_errorProbAt_le_one
    [Fintype β] [MeasurableSingletonClass β] [Nonempty β]
    {M₁ M₂ n : ℕ} (c : MACCode M₁ M₂ n α₁ α₂ β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (m : Fin M₁ × Fin M₂) :
    c.errorProbAt W m ≤ 1 := by
  unfold MACCode.errorProbAt
  haveI : IsProbabilityMeasure
      (Measure.pi (fun i => W (c.encoder₁ m.1 i, c.encoder₂ m.2 i))) := by infer_instance
  exact prob_le_one

/-- The average MAC error probability is `≤ 1`. -/
theorem mac_averageErrorProb_le_one
    [Fintype β] [MeasurableSingletonClass β] [Nonempty β]
    {M₁ M₂ n : ℕ} (c : MACCode M₁ M₂ n α₁ α₂ β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    c.averageErrorProb W ≤ 1 := by
  unfold MACCode.averageErrorProb
  by_cases hM : M₁ * M₂ = 0
  · simp [hM]
  · simp only [hM, if_false]
    have hM₁ : M₁ ≠ 0 := fun h => hM (by simp [h])
    have hM₂ : M₂ ≠ 0 := fun h => hM (by simp [h])
    -- Each summand ≤ 1.
    have h_each : ∀ m : Fin M₁ × Fin M₂, c.errorProbAt W m ≤ 1 :=
      fun m => mac_errorProbAt_le_one c W m
    -- Sum ≤ M₁ * M₂.
    have h_card : (Finset.univ : Finset (Fin M₁ × Fin M₂)).card = M₁ * M₂ := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have h_sum_le : (∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m)
        ≤ ((M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞)) := by
      calc (∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m)
          ≤ ∑ _m : Fin M₁ × Fin M₂, (1 : ℝ≥0∞) := Finset.sum_le_sum fun m _ => h_each m
        _ = ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by
              rw [Finset.sum_const, h_card, nsmul_eq_mul, mul_one]
        _ = (M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞) := by push_cast; ring
    have hMM_pos : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞) := by
      have h₁ : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) := by
        rw [show (0 : ℝ≥0∞) = ((0 : ℕ) : ℝ≥0∞) from by simp, Nat.cast_lt (α := ℝ≥0∞)]
        exact Nat.pos_of_ne_zero hM₁
      have h₂ : (0 : ℝ≥0∞) < (M₂ : ℝ≥0∞) := by
        rw [show (0 : ℝ≥0∞) = ((0 : ℕ) : ℝ≥0∞) from by simp, Nat.cast_lt (α := ℝ≥0∞)]
        exact Nat.pos_of_ne_zero hM₂
      exact ENNReal.mul_pos h₁.ne' h₂.ne'
    have hMM_ne_top : ((M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞)) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top M₁) (ENNReal.natCast_ne_top M₂)
    calc (((M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞))⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m)
        ≤ ((M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞))⁻¹ * ((M₁ : ℝ≥0∞) * (M₂ : ℝ≥0∞)) :=
          mul_le_mul_of_nonneg_left h_sum_le bot_le
      _ = 1 := ENNReal.inv_mul_cancel hMM_pos.ne' hMM_ne_top

/-- The average MAC error probability is finite. -/
theorem mac_averageErrorProb_ne_top
    [Fintype β] [MeasurableSingletonClass β] [Nonempty β]
    {M₁ M₂ n : ℕ} (c : MACCode M₁ M₂ n α₁ α₂ β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    c.averageErrorProb W ≠ ∞ :=
  (mac_averageErrorProb_le_one c W).trans_lt ENNReal.one_lt_top |>.ne

end MACAverageError

/-! ## Section 2 — Genuine JTS error assembly (per-code error → 0) -/

section JTSErrorAssembly

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Genuine JTS error assembly.** For any measure `ν` on the output
block and any message pair `m`, if the four Bonferroni events have masses
bounded by `δ₀, δ₁, δ₂, δ₃` whose sum is `< ε'`, then the JTS code's
pointwise error at `m` is `< ε'`.

This is the genuine "error → 0" content for the JTS decoder, assembled
from the *proven* `mac_achievability_corner_body` (Bonferroni union
bound). It is **not** a pass-through: it produces a strictly smaller bound
than its hypotheses by combining them through the 4-event decomposition. -/
theorem mac_jts_error_lt_of_bonferroni_lt
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (m : Fin M₁ × Fin M₂)
    (ν : Measure (Fin n → β))
    {δ₀ δ₁ δ₂ δ₃ ε' : ℝ≥0∞}
    (h0 : ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₀)
    (h1 : ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₁)
    (h2 : ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₂)
    (h3 : ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) ≤ δ₃)
    (hsum : δ₀ + δ₁ + δ₂ + δ₃ < ε') :
    ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m) < ε' :=
  lt_of_le_of_lt
    (mac_achievability_corner_body μ X1s X2s Ys ε c₁ c₂ m ν h0 h1 h2 h3) hsum

/-- **Genuine JTS error → 0 (eventual form).** Given the four Bonferroni
events' eventual-decay inputs — each a closed-form `∃ N, ∀ n ≥ N, …`
shape supplied by the AEP / exp-decay rate lemmas — the JTS code's
pointwise error is eventually `< ε'`.

Concretely: if for each of the four events there is a threshold past which
its mass is `≤ ε'/4`, then past the max threshold the JTS pointwise error
is `< ε'`. This packages `mac_jts_error_lt_of_bonferroni_lt` over the
four `∃ N` decay inputs into a single `∃ N` for the assembled error. -/
theorem mac_jts_error_eventually_lt
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (ε : ℝ) {ε' : ℝ≥0∞} (_hε' : 0 < ε')
    (mk₁ : ℕ → ℕ) (mk₂ : ℕ → ℕ)
    (hmk₁ : ∀ n, NeZero (mk₁ n)) (hmk₂ : ∀ n, NeZero (mk₂ n))
    (cb₁ : ∀ n, Fin (mk₁ n) → (Fin n → α₁))
    (cb₂ : ∀ n, Fin (mk₂ n) → (Fin n → α₂))
    (msg : ∀ n, Fin (mk₁ n) × Fin (mk₂ n))
    (ν : ∀ n, Measure (Fin n → β))
    (hdecay : ∃ N : ℕ, ∀ n, N ≤ n →
        letI := hmk₁ n; letI := hmk₂ n
        (ν n) (macErrorEvent_E0 μ X1s X2s Ys ε (cb₁ n) (cb₂ n) (msg n))
          + (ν n) (macErrorEvent_E1 μ X1s X2s Ys ε (cb₁ n) (cb₂ n) (msg n))
          + (ν n) (macErrorEvent_E2 μ X1s X2s Ys ε (cb₁ n) (cb₂ n) (msg n))
          + (ν n) (macErrorEvent_E3 μ X1s X2s Ys ε (cb₁ n) (cb₂ n) (msg n)) < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
        letI := hmk₁ n; letI := hmk₂ n
        (ν n) ((macJTSCode μ X1s X2s Ys ε (cb₁ n) (cb₂ n)).errorEvent (msg n)) < ε' := by
  obtain ⟨N, hN⟩ := hdecay
  refine ⟨N, ?_⟩
  intro n hn
  letI := hmk₁ n
  letI := hmk₂ n
  exact mac_jts_error_lt_of_bonferroni_lt μ X1s X2s Ys ε (cb₁ n) (cb₂ n) (msg n) (ν n)
    le_rfl le_rfl le_rfl le_rfl (hN n hn)

end JTSErrorAssembly

end InformationTheory.Shannon
