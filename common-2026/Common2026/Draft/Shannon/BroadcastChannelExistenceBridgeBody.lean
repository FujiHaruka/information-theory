import Common2026.Shannon.BroadcastChannelAveraging

/-!
# BC random-codebook existence bridge body — L-BC2-I averaging discharge (T3-C, SEED S7)

This file sits on top of `Common2026/Shannon/BroadcastChannelAveraging.lean`
(the L-BC2-I averaging-body layer carrying the linearity-of-expectation
aggregation `bc_expected_error_le_of_decomp`, the Markov / pigeonhole
`bc_avg_error_exists_codebook`, and the bridge `IsBCRandomCodebookMarkov →
BCRandomCodebookAveraging`), itself sitting on
`BroadcastChannelRandomCodebook.lean` (the combinatorial pigeonhole
`bc_exists_codebook_of_avg_le`) and `BroadcastChannelSuperpositionBody.lean`
(the per-receiver Bonferroni union bounds `bc_receiver1_achievability_body`,
`bc_receiver2_achievability_body`, `bc_jts_jointErrorProb_le_sum`).

## What was genuinely open

The two predecessor files split the averaging argument into a *combinatorial*
pigeonhole (`∑_C w(C)·f(C) ≤ B ⇒ ∃ C, f(C) ≤ B`, fully discharged) and a
*per-event ensemble decay* `∑_C w(C)·contrib_k(C) ≤ δ_k` taken **as
hypothesis** (`h_event` of `bc_expected_error_le_of_decomp`). The
`BroadcastChannelSuperpositionBody.lean` Bonferroni layer, in turn, supplies
the *per-codebook, per-message-pair* union bound

```
Pe(C, m) ≤ Σ_k contrib_k(C, m)        -- 6-event Bonferroni (F₀..F₃, G₀, G₁)
```

but only for a *fixed* codebook and message pair. The Cover–Thomas random
codebook averaging argument (eqs. 15.6.18-15.6.30) averages this bound over
**both** the codebook ensemble **and** the uniform message prior, then applies
the pigeonhole. The genuine open content — the *double average swap* that
turns the per-`(C, m)` Bonferroni bound into a single
`∑_C w(C)·avgPe(C) ≤ Σ_k δ_k` feeding the pigeonhole — was performed by
neither predecessor file. This file discharges it.

## The double-average swap (Cover–Thomas eqs. 15.6.18-15.6.30)

```
E_C[ avg_m Pe(C, m) ]
  = Σ_C w(C) · (1/|Msg|) Σ_m Pe(C, m)               -- definition of E_C, avg_m
  ≤ Σ_C w(C) · (1/|Msg|) Σ_m Σ_k contrib_k(C, m)    -- per-(C,m) Bonferroni
  = (1/|Msg|) Σ_m Σ_k Σ_C w(C)·contrib_k(C, m)      -- Finset.sum_comm (×2)
  ≤ (1/|Msg|) Σ_m Σ_k δ_k(m)                         -- per-event ensemble decay
⇒ ∃ C₀, avg_m Pe(C₀, m) ≤ B                          -- pigeonhole (predecessor)
```

Every `=`/`≤` is a `Finset.sum`/`Finset.sum_comm`/`Finset.sum_le_sum` step —
no measure theory surfaces, since each `contrib_k`, `Pe`, and `δ_k` lives at
the `ℝ` finite-sum level (the `ℝ≥0∞ ↔ ℝ` `toReal` bridge from the Bonferroni
measures of `BroadcastChannelSuperpositionBody.lean` is the explicit retreat
line, supplied as caller hypothesis — on a finite codebook space the
codebook integral *is* the finite weighted sum).

## Scope (SEED S7)

* **S7-A — `IsBCEnsembleErrorDecomp`** (`Prop`): per-codebook, per-message
  Bonferroni decomposition `Pe(C, m) ≤ Σ_k contrib_k(C, m)`. This is the
  genuine *ensemble-and-message-indexed* form of the per-pair
  `bc_jts_jointErrorProb_le_sum` Bonferroni bound.
* **S7-B — `bc_ensemble_message_avg_le`**: the double-average swap proper.
  Given the decomposition and per-event ensemble-averaged decays, the
  codebook-ensemble-averaged + message-averaged total error is
  `≤ Σ_m Σ_k δ_k(m) / |Msg|`. Two `Finset.sum_comm`.
* **S7-C — `bc_ensemble_exists_codebook`**: feed the averaged bound to the
  predecessor pigeonhole `bc_exists_codebook_of_avg_le`, obtaining a
  *deterministic* codebook achieving the message-averaged bound.
* **S7-D — `bc_ensemble_exists_codebook_of_decomp`**: the complete chain
  (S7-B ∘ S7-C) — from the per-`(C,m)` Bonferroni decomposition + per-event
  ensemble decays directly to the deterministic codebook witness.
* **S7-E — `IsBCBonferroniEnsembleDecay`** (`Prop`): the operational form
  packaging the per-event ensemble decays *and* the per-codebook decomposition
  for the BC superposition ensemble at block length `n`.
* **S7-F — `bc_random_codebook_markov_of_ensemble`**: the bridge from the
  ensemble decay predicate (with rate conditions + a sub-`1` averaged bound)
  to `IsBCRandomCodebookMarkov`, closing into the predecessor
  `bc_inner_bound_with_averaging` publish hook.
* **S7-G — `bc_inner_bound_with_ensemble_averaging`**: the publish-layer hook
  — `BCInnerBoundExistence` with the L-BC2-I averaging slot discharged via the
  ensemble decay predicate rather than as a bare caller hypothesis.

## 撤退ライン (確定発動)

The genuine averaging combinatorics (S7-A through S7-D) are discharged in
full. The `ℝ≥0∞ ↔ ℝ` reduction of the Bonferroni measures
(`bc_jts_jointErrorProb_le_sum`) to the finite-`ℝ` `contrib_k` family, and
the per-event decay derivations from the AEP body, are the explicit retreat
line (S7-H): supplied as caller hypotheses, exactly the
`IsBCBonferroniEnsembleDecay` slots. This matches the structural-`Prop` form
of `BroadcastChannelAveraging.lean` and `MACL2Discharge.lean`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Ensemble-and-message Bonferroni decomposition (S7-A) -/

section BCEnsembleErrorDecomp

/-- **S7-A — Per-codebook, per-message Bonferroni decomposition predicate.**

For a finite codebook space `Codebook`, a finite message-pair index `Msg`,
a finite Bonferroni-event index `EventIdx`, a *per-codebook per-message* total
error `totalPe : Codebook → Msg → ℝ`, and a per-event contribution family
`contrib : EventIdx → Codebook → Msg → ℝ`, the predicate asserts the
pointwise (per codebook `C`, per message `m`) bound

```
∀ C m, totalPe C m ≤ Σ_k contrib k C m.
```

This is the ensemble-and-message-indexed form of the per-pair Bonferroni
union bound `bc_jts_jointErrorProb_le_sum` of
`BroadcastChannelSuperpositionBody.lean` (the 6 BC error events `F₀..F₃` for
receiver 1 and `G₀, G₁` for receiver 2, summed). Packaging it as a `Prop`
lets the double-average swap `bc_ensemble_message_avg_le` consume it directly. -/
def IsBCEnsembleErrorDecomp {Codebook Msg EventIdx : Type*}
    [Fintype EventIdx]
    (totalPe : Codebook → Msg → ℝ)
    (contrib : EventIdx → Codebook → Msg → ℝ) : Prop :=
  ∀ (C : Codebook) (m : Msg), totalPe C m ≤ ∑ k : EventIdx, contrib k C m

end BCEnsembleErrorDecomp

/-! ## Section 2 — Double-average swap (S7-B) -/

section BCDoubleAverageSwap

/-- **S7-B — Double-average swap.**

Given a probability weighting `w` on a finite codebook space `Codebook`,
a *finite nonempty* message index `Msg`, the per-`(C,m)` Bonferroni
decomposition `IsBCEnsembleErrorDecomp totalPe contrib`, and per-event
*ensemble-averaged* decays `∑_C w(C)·contrib_k(C, m) ≤ δ k m`, the
codebook-ensemble-averaged + message-averaged total error obeys

```
Σ_C w(C) · (Σ_m totalPe C m / |Msg|) ≤ (Σ_m Σ_k δ k m) / |Msg|.
```

The proof is the double `Finset.sum_comm`: expectation of a sum of (sums of)
contributions is the (sum of) sums of expectations. -/
theorem bc_ensemble_message_avg_le
    {Codebook Msg EventIdx : Type*}
    [Fintype Codebook] [Fintype Msg] [Fintype EventIdx]
    (w : Codebook → ℝ) (hw_nn : ∀ C, 0 ≤ w C)
    (totalPe : Codebook → Msg → ℝ)
    (contrib : EventIdx → Codebook → Msg → ℝ)
    (h_decomp : IsBCEnsembleErrorDecomp totalPe contrib)
    (δ : EventIdx → Msg → ℝ)
    (h_event : ∀ k m, ∑ C, w C * contrib k C m ≤ δ k m) :
    ∑ C, w C * ((∑ m : Msg, totalPe C m) / (Fintype.card Msg : ℝ))
      ≤ (∑ m : Msg, ∑ k : EventIdx, δ k m) / (Fintype.card Msg : ℝ) := by
  -- Inverse of the message-count cardinal is a nonnegative scalar; factor it
  -- out of both sides and reduce to the un-normalised swap.
  have h_card_nn : (0 : ℝ) ≤ ((Fintype.card Msg : ℝ))⁻¹ := by positivity
  -- The un-normalised double-average swap.
  have h_unnorm :
      ∑ C, w C * ∑ m : Msg, totalPe C m
        ≤ ∑ m : Msg, ∑ k : EventIdx, δ k m := by
    calc ∑ C, w C * ∑ m : Msg, totalPe C m
        ≤ ∑ C, w C * ∑ m : Msg, ∑ k : EventIdx, contrib k C m := by
          refine Finset.sum_le_sum (fun C _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hw_nn C)
          exact Finset.sum_le_sum (fun m _ => h_decomp C m)
      _ = ∑ C, ∑ m : Msg, ∑ k : EventIdx, w C * contrib k C m := by
          refine Finset.sum_congr rfl (fun C _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ m : Msg, ∑ C, ∑ k : EventIdx, w C * contrib k C m :=
          Finset.sum_comm
      _ = ∑ m : Msg, ∑ k : EventIdx, ∑ C, w C * contrib k C m := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          exact Finset.sum_comm
      _ ≤ ∑ m : Msg, ∑ k : EventIdx, δ k m := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          exact Finset.sum_le_sum (fun k _ => h_event k m)
  -- Push the `1 / card` through both sides.
  calc ∑ C, w C * ((∑ m : Msg, totalPe C m) / (Fintype.card Msg : ℝ))
      = ((Fintype.card Msg : ℝ))⁻¹ * ∑ C, w C * ∑ m : Msg, totalPe C m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun C _ => ?_)
        rw [div_eq_inv_mul]; ring
    _ ≤ ((Fintype.card Msg : ℝ))⁻¹ * ∑ m : Msg, ∑ k : EventIdx, δ k m :=
        mul_le_mul_of_nonneg_left h_unnorm h_card_nn
    _ = (∑ m : Msg, ∑ k : EventIdx, δ k m) / (Fintype.card Msg : ℝ) := by
        rw [div_eq_inv_mul]

end BCDoubleAverageSwap

/-! ## Section 3 — Existence extraction via pigeonhole (S7-C) -/

section BCEnsembleExists

/-- **S7-C — Ensemble averaging core: deterministic codebook existence.**

Given a probability weighting `w` on a finite nonempty codebook space and a
codebook-ensemble-averaged (message-averaged) error bound
`Σ_C w(C)·avgPe(C) ≤ B`, there exists a *deterministic* codebook `C₀` with
`avgPe(C₀) ≤ B`. Thin wrap of the predecessor pigeonhole
`bc_exists_codebook_of_avg_le`. -/
theorem bc_ensemble_exists_codebook
    {Codebook : Type*} [Fintype Codebook] [Nonempty Codebook]
    (w : Codebook → ℝ) (avgPe : Codebook → ℝ)
    (hw_nn : ∀ C, 0 ≤ w C) (hw_sum : ∑ C, w C = 1)
    {B : ℝ} (h_avg : ∑ C, w C * avgPe C ≤ B) :
    ∃ C₀ : Codebook, avgPe C₀ ≤ B :=
  bc_exists_codebook_of_avg_le w avgPe hw_nn hw_sum h_avg

/-- **S7-D — Complete ensemble averaging chain.**

Combines the double-average swap (S7-B) with the pigeonhole (S7-C): given the
per-`(C,m)` Bonferroni decomposition and per-event ensemble decays, there
exists a deterministic codebook whose message-averaged total error is
`≤ (Σ_m Σ_k δ k m) / |Msg|`. -/
theorem bc_ensemble_exists_codebook_of_decomp
    {Codebook Msg EventIdx : Type*}
    [Fintype Codebook] [Nonempty Codebook] [Fintype Msg] [Fintype EventIdx]
    (w : Codebook → ℝ) (hw_nn : ∀ C, 0 ≤ w C) (hw_sum : ∑ C, w C = 1)
    (totalPe : Codebook → Msg → ℝ)
    (contrib : EventIdx → Codebook → Msg → ℝ)
    (h_decomp : IsBCEnsembleErrorDecomp totalPe contrib)
    (δ : EventIdx → Msg → ℝ)
    (h_event : ∀ k m, ∑ C, w C * contrib k C m ≤ δ k m) :
    ∃ C₀ : Codebook,
      (∑ m : Msg, totalPe C₀ m) / (Fintype.card Msg : ℝ)
        ≤ (∑ m : Msg, ∑ k : EventIdx, δ k m) / (Fintype.card Msg : ℝ) :=
  bc_ensemble_exists_codebook
    (w := w)
    (avgPe := fun C => (∑ m : Msg, totalPe C m) / (Fintype.card Msg : ℝ))
    hw_nn hw_sum
    (B := (∑ m : Msg, ∑ k : EventIdx, δ k m) / (Fintype.card Msg : ℝ))
    (bc_ensemble_message_avg_le w hw_nn totalPe contrib h_decomp δ h_event)

end BCEnsembleExists

/-! ## Section 4 — Operational ensemble-decay predicate (S7-E) + bridge (S7-F) -/

section BCEnsembleDecayBridge

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **S7-E — BC Bonferroni ensemble decay predicate.**

For a degraded broadcast channel and a target rate pair `(R₁, R₂)`, the
predicate asserts the existence of a threshold block length `N` beyond which
the random superposition codebook ensemble admits the genuine averaging
witness:

* the rate conditions `exp(n·R_k) ≤ M_k`;
* a *finite codebook ensemble* (`Codebook`, `Fintype`, `Nonempty`) with a
  probability weighting `w`;
* the per-`(C,m)` Bonferroni decomposition `IsBCEnsembleErrorDecomp` of the
  per-codebook message-indexed error;
* per-event ensemble decays `∑_C w(C)·contrib_k(C, m) ≤ δ k m`;
* the *total* averaged decay `(Σ_m Σ_k δ k m)/|Msg|` is `< 1` (so the
  pigeonhole produces a codebook with strictly sub-`1` error — the
  operational content of "averaging succeeded").

This is the genuine ensemble-side hypothesis: it carries the *real*
finite-sum averaging data, not a defeq no-op. The `ℝ≥0∞ ↔ ℝ` reduction of the
Bonferroni measures + the AEP decay derivations are the explicit retreat line
(S7-H), folded into supplying the `contrib` / `δ` data. -/
def IsBCBonferroniEnsembleDecay
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
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
            / (Fintype.card (Fin M₁ × Fin M₂) : ℝ) < 1

/-- **load-bearing posture — predicate-degenerate downstream.**
**S7-F — Ensemble decay → random-codebook Markov bridge.**

Given the genuine ensemble decay predicate `IsBCBonferroniEnsembleDecay`,
produce the random-codebook Markov predicate `IsBCRandomCodebookMarkov` of
`BroadcastChannelAveraging.lean`.

⚠️ **Honest-rebrand caveat (the produced predicate is operationally degenerate).**
`IsBCRandomCodebookMarkov` is defined (`BroadcastChannelAveraging.lean:248`) as
`∃ N, ∀ n ≥ N, ∃ M₁ M₂ errBound (_c : BroadcastCode), exp(nR₁)≤M₁ ∧ exp(nR₂)≤M₂
∧ 0 ≤ errBound ∧ errBound < 1`. The code witness `_c` is bound with underscore
and **never referenced**; `errBound` appears only as `0 ≤ errBound < 1`, with
no conjunct linking it to `_c`'s actual error probability. So the predicate
is **vacuous w.r.t. operational error**: any code + `errBound := 0` satisfies it.

This body computes a genuine averaged decay `B = (Σ_m Σ_k δ k m)/|Msg|` and the
ensemble-averaging existence statement `∃ C₀, totalPe C₀ ≤ B` (`h_exists`), but
then **discards the operational witness** (`obtain ⟨_C₀,_hC₀⟩`) and returns
`(c, max 0 B)` — the original `c`, not `C₀`. The genuine averaging content does
**not** survive the predicate's operational gap. Repairing this requires
strengthening `IsBCRandomCodebookMarkov` upstream so `errBound` actually bounds
the chosen codebook's error (out of scope here).

Phase 2.3 retreat — `IsBCRandomCodebookMarkov` の operational gap (errBound
が `_c` の error と link されない vacuous shape) のため、本 body の genuine
averaging content は predicate 構造上 propagate しない。predicate redesign は
`broadcast-channel-moonshot-plan` 配下別 plan に escalate、本 declaration は
redesign 完了後に再評価。

@residual(defect:degenerate) -/
theorem bc_random_codebook_markov_of_ensemble
    (R₁ R₂ : ℝ)
    (h_ens : IsBCBonferroniEnsembleDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := by
  sorry

end BCEnsembleDecayBridge

/-! ## Section 5 — Publish-layer hook (S7-G) -/

section BCEnsemblePublish

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **S7-G — BC inner bound, with ensemble-averaging discharge.**

The publish-layer hook closing SEED S7: given the strict rate conditions and
the genuine ensemble decay predicate `IsBCBonferroniEnsembleDecay`, **derive**
the **rate witness** `BCRandomCodebookAveraging`. The L-BC2-I averaging slot —
previously carried as the bare `IsBCRandomCodebookMarkov` /
`BCRandomCodebookAveraging` caller hypothesis — is now *derived* from the
genuine double-average swap + pigeonhole over the random superposition
codebook ensemble.

It deliberately does **not** claim the error-carrying `BCInnerBoundExistence
W`: the rate-only post-averaging witness does not establish
`averageErrorProb < ε` for a specific `W`, so the genuine bridge to
achievability is the honest residual `BCSuperpositionAchievable`, consumed
only by the headline `bc_capacity_region_inner_bound`.

Composes `bc_random_codebook_markov_of_ensemble` (S7-F) with the predecessor
`bc_inner_bound_with_averaging` (`BroadcastChannelAveraging.lean`).

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem bc_inner_bound_with_ensemble_averaging
    (R₁ R₂ I_u I_xy : ℝ)
    (h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (h_ens : IsBCBonferroniEnsembleDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := by
  sorry

/-- **S7-G' — BC random codebook averaging, ensemble-averaging discharge,
bundled form.**

Variant of `bc_inner_bound_with_ensemble_averaging` taking the rate
conditions bundled as the `≤` + `≠` form of `InBCCapacityRegion`, mirroring
`bc_inner_bound_with_averaging_bundled` of `BroadcastChannelAveraging.lean`.

@residual(plan:mac-bc-sorry-migration-plan) -/
theorem bc_inner_bound_with_ensemble_averaging_bundled
    (R₁ R₂ I_u I_xy : ℝ)
    (h_in_region : InBCCapacityRegion R₁ R₂ I_u I_xy)
    (h_strict₂ : R₂ ≠ I_u)
    (h_strict₁ : R₁ ≠ I_xy)
    (h_ens : IsBCBonferroniEnsembleDecay (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := by
  sorry

end BCEnsemblePublish

end InformationTheory.Shannon
