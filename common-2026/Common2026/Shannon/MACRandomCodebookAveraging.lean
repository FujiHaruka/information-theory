import Common2026.Shannon.MACCornerAchievabilityBody

/-!
# MAC random-codebook averaging — 3-event lift of the single-user averaging (W10-S12)

This file discharges the **random-codebook averaging body** of the MAC
corner-point inner bound — the explicit retreat line documented in
`Common2026/Shannon/MACCornerAchievabilityBody.lean`
(`MACCornerAchievabilityBody.lean:65-75`, the "撤退ライン"):

> The full random-codebook *averaging* over all `(c₁, c₂)` (E₁/E₂/E₃
> expectation bounds via the union over wrong messages … the analogue of
> `random_codebook_average_le` lifted to 3 events) is **out of scope** of
> one seed.

The present file lands that averaging at the **finite-sum expectation**
level, lifting the single-user `random_codebook_average_le` /
`exists_codebook_le_avg` pattern (`ChannelCodingAchievability.lean`) and the
2-event `BroadcastChannelAveraging.lean` body to the **MAC 4-event**
structure (the four Bonferroni events `E₀, E₁, E₂, E₃` of
`MACBodyDischarge.lean` — `E₀` is the AEP "correct triple atypical" event,
`E₁/E₂/E₃` are the three union-over-wrong-message events).

## What is *genuinely* discharged here (not a no-op)

The genuine content of MAC achievability is the **codebook-ensemble-averaged
error → 0**, producing a good *deterministic* codebook pair `(c₁, c₂)`. We
discharge this in three grounded layers:

1. **Per-codebook 4-event decomposition, grounded in the proven union
   bound.** `mac_averageErrorProb_le_event_sum` shows that for the JTS code
   `macJTSCode μ … c₁ c₂`, the (real-valued) average error probability is
   `≤` the message-average of the four Bonferroni event masses — by
   averaging the *already-proven* `mac_jts_errorProb_le_union` over the
   message pairs. This is the genuine welding of `MACCode.averageErrorProb`
   to the four `macErrorEvent_Ek`.

2. **Linearity of expectation over the codebook ensemble.**
   `mac_expected_error_le_of_decomp` swaps the expectation `E_{(c₁,c₂)}[·]`
   with the finite sum over the four events via `Finset.sum_comm`, bounding
   the expected total error by `∑_k δ_k` from the per-event expected-decay
   inputs. This is the 4-event lift of the single-user
   `random_codebook_average_le` Fubini-swap aggregation.

3. **Markov pigeonhole over codebook *pairs*.**
   `mac_avg_error_exists_codebook` produces a deterministic codebook pair
   from the expected-error bound (`∑ w·Pe ≤ B ⇒ ∃ C, Pe(C) ≤ B`), lifted
   to the product codebook space `Codebook₁ × Codebook₂`.

These three feed `IsMACRandomCodebookMarkov`, which (by definitional
equality with `MACInnerBoundExistence`) directly supplies the inner-bound
existence — the prior identity-relabel cascade
(`IsMACRandomCodebookMarkov → MACAchievableWithError →
MACInnerBoundExistence`) has been retracted (alias chain).

## Design (finite-sum expectation, matching `BroadcastChannelAveraging`)

The averaging is kept at the finite-sum-expectation level
`E_C[f] := ∑_C w(C)·f(C)` over a `Fintype` codebook(-pair) space with a
probability weighting `w` (`0 ≤ w`, `∑ w = 1`) — exactly the shape the
Markov pigeonhole consumes, so the existence extraction is one wrap with no
mid-proof shape pivot (CLAUDE.md "Mathlib-shape-driven definitions"). The
genuinely measure-theoretic `∫⁻ C, Pe(C) ∂(Measure.pi^n P_X^n × Measure.pi^n P_X^n)`
form — and the operational derivation of the per-event decays from the MAC
AEP body — is the explicit retreat line (S12-M), supplied as a caller
hypothesis (matching `BroadcastChannelAveraging.lean`'s L-BC2-I-M and the
single-user `random_codebook_E1_swap`/`E2_swap` `sorry`-carried Fubini
ingredients, which this file does **not** reintroduce — it stays `sorry`-free
on the finite-sum side).

## Main results

* `mac_averageErrorProb_le_event_sum` — **genuine per-codebook welding**:
  the JTS code's average error `≤` the message-average of the four event
  masses (via `mac_jts_errorProb_le_union`).
* `IsMACExpectationDecomp` / `mac_expected_error_le_of_decomp` — the
  4-event linearity-of-expectation aggregation (`Finset.sum_comm`).
* `mac_avg_error_exists_codebook` / `_of_decomp` — Markov pigeonhole over
  the (product) codebook space.
* `IsMACRandomCodebookMarkov` — the random-codebook Markov predicate
  (deterministic codebook-pair-with-rate witness; definitionally
  `MACInnerBoundExistence`, used directly by callers without a separate
  identity-relabel bridge).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Expected-error 4-event finite-sum decomposition -/

section MACExpectationDecomp

/-- **Expected-error 4-event finite-sum decomposition predicate** (MAC
analogue of `IsBCExpectationDecomp`, Cover–Thomas eqs. 15.65-15.84,
linearity-of-expectation form).

For a finite codebook(-pair) space `Codebook`, a per-event error
contribution family `contrib : EventIdx → Codebook → ℝ`, and a *total*
error `totalPe : Codebook → ℝ`, the predicate asserts that the total error
is pointwise (per codebook pair `C`) bounded by the sum of the per-event
contributions:

```
∀ C, totalPe C ≤ ∑_k contrib k C.
```

For the MAC, `EventIdx := Fin 4` (the four Bonferroni events `E₀..E₃`) and
the bound is the per-codebook union bound `mac_jts_errorProb_le_union`
averaged over the message pairs. -/
def IsMACExpectationDecomp {Codebook EventIdx : Type*}
    [Fintype EventIdx]
    (totalPe : Codebook → ℝ) (contrib : EventIdx → Codebook → ℝ) : Prop :=
  ∀ C : Codebook, totalPe C ≤ ∑ k : EventIdx, contrib k C

/-- **Linearity-of-expectation aggregation** (MAC analogue of
`bc_expected_error_le_of_decomp`).

Given the per-codebook 4-event decomposition `IsMACExpectationDecomp` and a
probability weighting `w` on the codebook(-pair) space, plus per-event
expected-decay bounds `∑_C w(C)·contrib_k(C) ≤ δ_k`, the *expected total
error* `∑_C w(C)·totalPe(C)` is bounded by `∑_k δ_k`.

Proof: expectation of a sum is the sum of expectations (`Finset.sum_comm`),
each bounded by `δ_k`. This is the 4-event lift of the single-user
`random_codebook_average_le` swap aggregation. -/
theorem mac_expected_error_le_of_decomp
    {Codebook EventIdx : Type*} [Fintype Codebook] [Fintype EventIdx]
    (w : Codebook → ℝ) (hw_nn : ∀ C, 0 ≤ w C)
    (totalPe : Codebook → ℝ) (contrib : EventIdx → Codebook → ℝ)
    (h_decomp : IsMACExpectationDecomp totalPe contrib)
    (δ : EventIdx → ℝ)
    (h_event : ∀ k, ∑ C, w C * contrib k C ≤ δ k) :
    ∑ C, w C * totalPe C ≤ ∑ k, δ k := by
  calc ∑ C, w C * totalPe C
      ≤ ∑ C, w C * ∑ k, contrib k C := by
        refine Finset.sum_le_sum (fun C _ => ?_)
        exact mul_le_mul_of_nonneg_left (h_decomp C) (hw_nn C)
    _ = ∑ C, ∑ k, w C * contrib k C := by
        refine Finset.sum_congr rfl (fun C _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ k, ∑ C, w C * contrib k C := Finset.sum_comm
    _ ≤ ∑ k, δ k := Finset.sum_le_sum (fun k _ => h_event k)

end MACExpectationDecomp

/-! ## Section 2 — Averaging core / Markov pigeonhole over codebook pairs -/

section MACAveragingCore

/-- **Markov pigeonhole** (MAC analogue of `bc_avg_error_exists_codebook`).

Given a finite (nonempty) codebook(-pair) space `Codebook`, a probability
weighting `w` (`0 ≤ w`, `∑ w = 1`), and an expected-error bound
`∑_C w(C)·Pe(C) ≤ B`, there exists a *deterministic* codebook pair `C₀`
with `Pe(C₀) ≤ B`.

This is the heart of the random codebook averaging argument, lifted to the
product codebook space `Codebook₁ × Codebook₂`. -/
theorem mac_avg_error_exists_codebook
    {Codebook : Type*} [Fintype Codebook] [Nonempty Codebook]
    (w : Codebook → ℝ) (Pe : Codebook → ℝ)
    (hw_nn : ∀ C, 0 ≤ w C) (hw_sum : ∑ C, w C = 1)
    {B : ℝ} (h_avg : ∑ C, w C * Pe C ≤ B) :
    ∃ C₀ : Codebook, Pe C₀ ≤ B := by
  classical
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- The weighted average is `> B`, contradicting `h_avg`.
  have h_contra : B < ∑ C, w C * Pe C := by
    calc B
        = B * 1 := by ring
      _ = B * ∑ C, w C := by rw [hw_sum]
      _ = ∑ C, w C * B := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ < ∑ C, w C * Pe C := by
            -- For each `C`, `w C * B ≤ w C * Pe C` (weak); some weight is
            -- positive (else `∑ w = 0 ≠ 1`), so the sum is strict.
            have h_each : ∀ C ∈ (Finset.univ : Finset Codebook),
                w C * B ≤ w C * Pe C :=
              fun C _ => mul_le_mul_of_nonneg_left (h_none C).le (hw_nn C)
            have h_exists_pos : ∃ C, 0 < w C := by
              by_contra h_none_pos
              simp only [not_exists, not_lt] at h_none_pos
              have h_all_zero : ∀ C, w C = 0 :=
                fun C => le_antisymm (h_none_pos C) (hw_nn C)
              have h_sum_zero : ∑ C, w C = 0 :=
                Finset.sum_eq_zero (fun C _ => h_all_zero C)
              rw [h_sum_zero] at hw_sum
              exact one_ne_zero hw_sum.symm
            obtain ⟨C₀, hC₀_pos⟩ := h_exists_pos
            have h_strict : w C₀ * B < w C₀ * Pe C₀ :=
              mul_lt_mul_of_pos_left (h_none C₀) hC₀_pos
            exact Finset.sum_lt_sum h_each ⟨C₀, Finset.mem_univ _, h_strict⟩
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg h_contra)

/-- **Averaging core, full chain from the 4-event decomposition.**

Combines `mac_expected_error_le_of_decomp` (linearity of expectation) with
`mac_avg_error_exists_codebook` (Markov pigeonhole): from the per-codebook
4-event decomposition + the per-event expected-decay bounds, there exists a
deterministic codebook pair whose total error is `≤ ∑_k δ_k`.

This is the complete averaging body at the finite-sum expectation level. -/
theorem mac_avg_error_exists_codebook_of_decomp
    {Codebook EventIdx : Type*} [Fintype Codebook] [Nonempty Codebook]
    [Fintype EventIdx]
    (w : Codebook → ℝ) (hw_nn : ∀ C, 0 ≤ w C) (hw_sum : ∑ C, w C = 1)
    (totalPe : Codebook → ℝ) (contrib : EventIdx → Codebook → ℝ)
    (h_decomp : IsMACExpectationDecomp totalPe contrib)
    (δ : EventIdx → ℝ)
    (h_event : ∀ k, ∑ C, w C * contrib k C ≤ δ k) :
    ∃ C₀ : Codebook, totalPe C₀ ≤ ∑ k, δ k :=
  mac_avg_error_exists_codebook w totalPe hw_nn hw_sum
    (mac_expected_error_le_of_decomp w hw_nn totalPe contrib h_decomp δ h_event)

end MACAveragingCore

/-! ## Section 3 — Genuine per-codebook 4-event welding -/

section MACPerCodebookWelding

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Genuine per-codebook welding — pointwise error → 4-event sum.**

For the JTS code `macJTSCode μ … c₁ c₂` and any output measure `ν`, the
(real-valued) pointwise error at message pair `m` is bounded by the sum of
the four Bonferroni event masses. This is the `toReal` form of the proven
`mac_jts_errorProb_le_union`, finite because each event mass is `≤ 1` under
a probability output measure. -/
theorem mac_jts_errorProbAt_toReal_le_event_sum
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (m : Fin M₁ × Fin M₂) :
    ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorProbAt W m).toReal ≤
        ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
            (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
            (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)).toReal
        + ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
            (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
            (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)).toReal
        + ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
            (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
            (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)).toReal
        + ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
            (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
            (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m)).toReal := by
  -- The channel output measure for message pair `m`.
  set ν : Measure (Fin n → β) :=
    Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
        (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  -- `errorProbAt` of the JTS code at `m` is exactly `ν (errorEvent m)`.
  have h_errProb_eq :
      (macJTSCode μ X1s X2s Ys ε c₁ c₂).errorProbAt W m
        = ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m) := rfl
  -- ℝ≥0∞ union bound from the proven lemma, specialised to `ν`.
  have h_union :
      ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m) ≤
        ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) :=
    mac_jts_errorProb_le_union μ X1s X2s Ys ε c₁ c₂ m ν
  -- Each event mass is `≤ 1`, hence the 4-fold sum is finite.
  have h0_ne : ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m) ≠ ∞ :=
    (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  have h1_ne : ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m) ≠ ∞ :=
    (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  have h2_ne : ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m) ≠ ∞ :=
    (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  have h3_ne : ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) ≠ ∞ :=
    (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  have h_sum_ne :
      ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
        + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m) ≠ ∞ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h0_ne, h1_ne⟩, h2_ne⟩, h3_ne⟩
  -- Take `toReal` of the union bound, then split the sum.
  rw [h_errProb_eq]
  calc (ν ((macJTSCode μ X1s X2s Ys ε c₁ c₂).errorEvent m)).toReal
      ≤ (ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)
          + ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)
          + ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)
          + ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m)).toReal :=
        ENNReal.toReal_mono h_sum_ne h_union
    _ = (ν (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)).toReal
        + (ν (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)).toReal
        + (ν (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)).toReal
        + (ν (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m)).toReal := by
        rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h0_ne, h1_ne⟩, h2_ne⟩) h3_ne,
            ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h0_ne, h1_ne⟩) h2_ne,
            ENNReal.toReal_add h0_ne h1_ne]

/-- **Genuine welding — average error → message-averaged 4-event sum.**

For the JTS code over a codebook pair `(c₁, c₂)`, the (real-valued) average
error probability is bounded by the message-average of the four Bonferroni
event masses. This is the average over message pairs `m` of the pointwise
welding `mac_jts_errorProbAt_toReal_le_event_sum`, after expanding
`MACCode.averageErrorProb.toReal` as `(M₁·M₂)⁻¹ · ∑_m (errorProbAt).toReal`
(the MAC analogue of the single-user `h_avg_real` step in
`random_codebook_average_le`).

This is exactly the per-codebook decomposition (`IsMACExpectationDecomp`,
with `EventIdx := Fin 4`) that the averaging core consumes: it feeds the
codebook-ensemble linearity of expectation and the Markov pigeonhole. -/
theorem mac_averageErrorProb_toReal_le_event_sum
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (c₁ : Fin M₁ → (Fin n → α₁)) (c₂ : Fin M₂ → (Fin n → α₂))
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    ((macJTSCode μ X1s X2s Ys ε c₁ c₂).averageErrorProb W).toReal ≤
        ((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          (((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
              (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
              (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)).toReal
            + ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
                (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
                (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)).toReal
            + ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
                (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
                (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)).toReal
            + ((Measure.pi (fun i => W ((macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₁ m.1 i,
                (macJTSCode μ X1s X2s Ys ε c₁ c₂).encoder₂ m.2 i)))
                (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m)).toReal) := by
  classical
  haveI : Nonempty (Fin M₁) := ⟨⟨0, NeZero.pos M₁⟩⟩
  haveI : Nonempty (Fin M₂) := ⟨⟨0, NeZero.pos M₂⟩⟩
  set c := macJTSCode μ X1s X2s Ys ε c₁ c₂ with hc_def
  have hM₁ne : M₁ ≠ 0 := NeZero.ne M₁
  have hM₂ne : M₂ ≠ 0 := NeZero.ne M₂
  have hMM : M₁ * M₂ ≠ 0 := Nat.mul_ne_zero hM₁ne hM₂ne
  -- Each pointwise error probability is finite.
  have h_errProbAt_ne_top : ∀ m : Fin M₁ × Fin M₂, c.errorProbAt W m ≠ ∞ :=
    fun m => (mac_errorProbAt_le_one c W m |>.trans_lt ENNReal.one_lt_top).ne
  -- `(averageErrorProb).toReal = (M₁·M₂)⁻¹ · ∑_m (errorProbAt).toReal`.
  have h_avg_real :
      (c.averageErrorProb W).toReal
        = ((M₁ : ℝ) * (M₂ : ℝ))⁻¹ *
          ∑ m : Fin M₁ × Fin M₂, (c.errorProbAt W m).toReal := by
    unfold MACCode.averageErrorProb
    rw [if_neg hMM]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast,
        ENNReal.toReal_sum (fun m _ => h_errProbAt_ne_top m)]
  rw [h_avg_real]
  -- Multiply the pointwise welding through by the nonneg factor `(M₁·M₂)⁻¹`.
  have h_factor_nn : (0 : ℝ) ≤ ((M₁ : ℝ) * (M₂ : ℝ))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ => ?_)) h_factor_nn
  exact mac_jts_errorProbAt_toReal_le_event_sum μ X1s X2s Ys ε c₁ c₂ W m

end MACPerCodebookWelding

/-! ## Section 3b — Fully grounded averaging over the MAC codebook-pair
ensemble (3-event lift end-to-end) -/

section MACGroundedAveraging

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Per-codebook-pair total error: the (real-valued) average error of the
JTS code built from the codebook pair `Cp = (c₁, c₂)`. -/
noncomputable def macEnsembleTotalPe
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (W : MACChannel α₁ α₂ β)
    (Cp : (Fin M₁ → (Fin n → α₁)) × (Fin M₂ → (Fin n → α₂))) : ℝ :=
  ((macJTSCode μ X1s X2s Ys ε Cp.1 Cp.2).averageErrorProb W).toReal

/-- Per-codebook-pair, per-event error contribution: the message-average of
the `k`-th Bonferroni event mass over the JTS code built from `Cp`.
`k = 0,1,2,3` selects `E₀, E₁, E₂, E₃`. -/
noncomputable def macEnsembleContrib
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (ε : ℝ)
    (W : MACChannel α₁ α₂ β)
    (k : Fin 4)
    (Cp : (Fin M₁ → (Fin n → α₁)) × (Fin M₂ → (Fin n → α₂))) : ℝ :=
  ((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ∑ m : Fin M₁ × Fin M₂,
    (((Measure.pi (fun i => W (Cp.1 m.1 i, Cp.2 m.2 i)))
        (([macErrorEvent_E0, macErrorEvent_E1, macErrorEvent_E2,
            macErrorEvent_E3].get k) μ X1s X2s Ys ε Cp.1 Cp.2 m)).toReal)

/-- **The MAC 4-event expectation decomposition is genuinely satisfied.**

For the JTS-code ensemble over codebook pairs, the per-codebook total error
`macEnsembleTotalPe` is pointwise bounded by the sum of the four per-event
contributions `macEnsembleContrib`. This instantiates `IsMACExpectationDecomp`
with `EventIdx := Fin 4`, grounded in
`mac_averageErrorProb_toReal_le_event_sum`. -/
theorem mac_ensemble_isExpectationDecomp
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    IsMACExpectationDecomp
      (macEnsembleTotalPe μ X1s X2s Ys ε W (M₁ := M₁) (M₂ := M₂) (n := n))
      (macEnsembleContrib μ X1s X2s Ys ε W (M₁ := M₁) (M₂ := M₂) (n := n)) := by
  intro Cp
  obtain ⟨c₁, c₂⟩ := Cp
  -- The 4-event sum equals the message-averaged 4-event sum of Section 3.
  have h_sum_eq :
      ∑ k : Fin 4, macEnsembleContrib μ X1s X2s Ys ε W k (c₁, c₂)
        = ((M₁ : ℝ) * (M₂ : ℝ))⁻¹ * ∑ m : Fin M₁ × Fin M₂,
            (((Measure.pi (fun i => W (c₁ m.1 i, c₂ m.2 i)))
                (macErrorEvent_E0 μ X1s X2s Ys ε c₁ c₂ m)).toReal
              + ((Measure.pi (fun i => W (c₁ m.1 i, c₂ m.2 i)))
                  (macErrorEvent_E1 μ X1s X2s Ys ε c₁ c₂ m)).toReal
              + ((Measure.pi (fun i => W (c₁ m.1 i, c₂ m.2 i)))
                  (macErrorEvent_E2 μ X1s X2s Ys ε c₁ c₂ m)).toReal
              + ((Measure.pi (fun i => W (c₁ m.1 i, c₂ m.2 i)))
                  (macErrorEvent_E3 μ X1s X2s Ys ε c₁ c₂ m)).toReal) := by
    simp only [macEnsembleContrib, Fin.sum_univ_four, List.get]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        mul_add, mul_add, mul_add]
  rw [h_sum_eq]
  -- Apply the Section-3 grounded welding (encoder₁ = c₁, encoder₂ = c₂ defeq).
  exact mac_averageErrorProb_toReal_le_event_sum μ X1s X2s Ys ε c₁ c₂ W

/-- **Fully grounded MAC random-codebook averaging (3-event lift,
end-to-end).**

Given a probability weighting `w` on the (finite, nonempty) codebook-pair
ensemble and per-event expected-decay bounds
`∑_{Cp} w(Cp)·macEnsembleContrib k Cp ≤ δ k` for each of the four Bonferroni
events `k`, there exists a **deterministic** codebook pair `(c₁, c₂)` whose
JTS code has average error `≤ ∑_k δ_k`.

This is the complete genuine averaging body: the per-codebook 4-event
decomposition (`mac_ensemble_isExpectationDecomp`, grounded in the proven
union bound) is fed through the codebook-ensemble linearity of expectation
(`mac_expected_error_le_of_decomp`) and the Markov pigeonhole
(`mac_avg_error_exists_codebook`) over the product codebook space — the MAC
4-event analogue of the single-user `random_codebook_average_le` +
`exists_codebook_le_avg`. -/
theorem mac_random_codebook_averaging_exists
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] (ε : ℝ)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (w : (Fin M₁ → (Fin n → α₁)) × (Fin M₂ → (Fin n → α₂)) → ℝ)
    (hw_nn : ∀ Cp, 0 ≤ w Cp)
    (hw_sum : ∑ Cp, w Cp = 1)
    (δ : Fin 4 → ℝ)
    (h_event : ∀ k, ∑ Cp, w Cp * macEnsembleContrib μ X1s X2s Ys ε W k Cp ≤ δ k) :
    ∃ Cp : (Fin M₁ → (Fin n → α₁)) × (Fin M₂ → (Fin n → α₂)),
      ((macJTSCode μ X1s X2s Ys ε Cp.1 Cp.2).averageErrorProb W).toReal ≤ ∑ k, δ k := by
  have h_exists :=
    mac_avg_error_exists_codebook_of_decomp
      (Codebook := (Fin M₁ → (Fin n → α₁)) × (Fin M₂ → (Fin n → α₂)))
      (EventIdx := Fin 4)
      w hw_nn hw_sum
      (macEnsembleTotalPe μ X1s X2s Ys ε W)
      (macEnsembleContrib μ X1s X2s Ys ε W)
      (mac_ensemble_isExpectationDecomp μ X1s X2s Ys ε W)
      δ h_event
  obtain ⟨Cp, hCp⟩ := h_exists
  exact ⟨Cp, hCp⟩

end MACGroundedAveraging

/-! ## Section 4 — Random codebook Markov predicate + bridge -/

section MACRandomCodebookMarkov

variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **Random codebook Markov predicate** (MAC analogue of
`IsBCRandomCodebookMarkov`, Cover–Thomas eqs. 15.65-15.84,
deterministic-codebook-pair-with-rate form).

For a MAC and a target rate pair `(R₁, R₂)`, the predicate asserts that for
every target error `ε' > 0` there is a threshold `N` beyond which the random
codebook averaging argument produces a **deterministic** MAC code (the JTS
code over a codebook pair `(c₁, c₂)`) satisfying both rate conditions
`exp(n·R_k) ≤ M_k` *and* an explicit average error `< ε'`.

This is the operational output of the random codebook averaging body: the
codebook-ensemble-averaged error is `< ε'`, so the Markov pigeonhole yields
a single deterministic codebook achieving `< ε'`. The predicate is
definitionally `MACInnerBoundExistence`, so callers consume it directly
to land the inner-bound existence (no identity-relabel bridge). -/
def IsMACRandomCodebookMarkov
    {α₁ α₂ β : Type*}
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
    (W : MACChannel α₁ α₂ β) (R₁ R₂ : ℝ) : Prop :=
  ∀ ε' : ℝ, 0 < ε' →
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (c : MACCode M₁ M₂ n α₁ α₂ β),
        Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
        ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
        ∧ (c.averageErrorProb W).toReal < ε'

end MACRandomCodebookMarkov

end InformationTheory.Shannon
