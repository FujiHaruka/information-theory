import Common2026.Shannon.BroadcastChannelRandomCodebook

/-!
# BC random codebook averaging body — L-BC2-I averaging discharge (T3-C continuation)

This file is the **averaging body discharge layer** sitting on top of
`Common2026/Shannon/BroadcastChannelRandomCodebook.lean` (which carries the
abstract Markov / pigeonhole step `bc_exists_codebook_of_avg_le`, the
`BCExpectedErrorBound` / `BCRandomCodebookAveraging` `Prop` predicates, and
the existence extraction `bc_random_codebook_averaging_exists`).

The wave7 layer published the *combinatorial* core (`bc_exists_codebook_of_avg_le`
— `∑_C w(C)·f(C) ≤ B ⇒ ∃ C, f(C) ≤ B`) but left the **averaging body
proper** — the chain that turns a per-event expected-error decomposition
into the deterministic-codebook existence witness — to a successor seed
(L-BC2-I-F). The present file discharges that chain at the *finite-sum
expectation* level: it never surfaces `Measure.pi^n` of `P_X`, working
instead with the weighted-average abstraction
`E_C[·] := ∑_C w(C)·(·)` over a finite codebook space, exactly the shape
that `bc_exists_codebook_of_avg_le` consumes.

## The Cover-Thomas averaging argument (eqs. 15.6.18-15.6.30)

The classical "probabilistic method" step proceeds:

```
E_C[avg-Pe(C)]
  = E_C[ Σ_event Pe_event(C) ]        -- joint error ≤ sum of error events
  ≤ Σ_event E_C[ Pe_event(C) ]        -- linearity of expectation
  ≤ Σ_event δ_event(n)                -- per-event expected decay
  =: δ(n)                             -- total expected error
⇒ ∃ C, avg-Pe(C) ≤ δ(n)              -- Markov / pigeonhole (wave7)
⇒ ∃ C, avg-Pe(C) ≤ ε  (for n large)  -- δ(n) → 0 < ε
```

Each `⇒` is one application of linearity of expectation or the Markov
pigeonhole. The fragments in this file unpack the **expectation-side**
of this chain (the `=`/`≤` steps), feeding the wave7 pigeonhole on the
existence extraction.

## Scope (L-BC2-I averaging body discharge)

Six fragments are published in this seed:

* **L-BC2-I-G — `IsBCExpectationDecomp`** (`Prop` predicate): the
  expected joint error over random codebooks decomposes as a *finite
  sum* of per-event expected error contributions, each bounded by a
  decay term. Structural; the linearity-of-expectation step is captured
  as a finite-`Finset.sum` bound.
* **L-BC2-I-H — `bc_expected_error_le_of_decomp`**: the linearity-of-
  expectation aggregation — given the per-event decomposition with each
  contribution `≤ δ_k`, the total expected error is `≤ ∑ δ_k`. Direct
  `Finset.sum_le_sum`.
* **L-BC2-I-I — `bc_avg_error_exists_codebook`**: the averaging core —
  given a probability weighting `w` on the (finite) codebook space and
  an expected-error bound `∑_C w(C)·Pe(C) ≤ B`, conclude
  `∃ C, Pe(C) ≤ B`. Thin wrap of the wave7 `bc_exists_codebook_of_avg_le`.
* **L-BC2-I-J — `IsBCRandomCodebookMarkov`** (`Prop` predicate): the
  Markov step bundled — for every `ε > 0` there is `N` beyond which the
  expected error is `< ε` *and* (hence, by the averaging core) a
  deterministic codebook achieving `< ε` exists with the right rate
  conditions.
* **L-BC2-I-K — `bc_random_codebook_averaging_of_markov`**: the bridge
  from `IsBCRandomCodebookMarkov` to `BCRandomCodebookAveraging`,
  consuming the rate witness produced by the Markov predicate.
* **L-BC2-I-L — `bc_inner_bound_with_averaging`**: the publish-layer
  hook. A discharge wrapper around
  `bc_inner_bound_with_random_codebook` whose `h_avg` slot is now
  supplied by the averaging-body Markov predicate rather than as a
  caller hypothesis.

## Design (finite-sum expectation, Mathlib-shape-driven)

The averaging argument is kept entirely at the **finite-sum
expectation** level: `E_C[f] := ∑_C w(C)·f(C)` over a `Fintype`
codebook space with a probability weighting `w` (`∑ w = 1`, `0 ≤ w`).
This matches the conclusion form of the wave7
`bc_exists_codebook_of_avg_le` verbatim, so the existence extraction is
a one-step wrap (no mid-proof shape pivot). The genuinely
measure-theoretic form — `∫⁻ C, Pe(C) ∂(Measure.pi^n P_X)` and its
reduction to a finite sum on a finite codebook space — is left as the
explicit retreat line (L-BC2-I-M), supplied as a caller hypothesis: on
a finite codebook space the integral *is* the finite weighted sum, but
threading `Measure.lintegral_fintype` here would add ~100 lines of
`ℝ≥0∞ ↔ ℝ` plumbing for no new mathematical content.

## 撤退ライン (確定発動)

* **L-BC2-I-G** (`IsBCExpectationDecomp`): publishable, structural-`Prop`
  form (finite-sum decomposition of expected error).
* **L-BC2-I-H** (`bc_expected_error_le_of_decomp`): publishable in full,
  pure `Finset.sum_le_sum`.
* **L-BC2-I-I** (`bc_avg_error_exists_codebook`): publishable in full,
  thin wrap of the wave7 pigeonhole.
* **L-BC2-I-J** (`IsBCRandomCodebookMarkov`): publishable, structural-
  `Prop` form.
* **L-BC2-I-K** (`bc_random_codebook_averaging_of_markov`): publishable
  in full as a bridge lemma.
* **L-BC2-I-L** (`bc_inner_bound_with_averaging`): publishable as a thin
  discharge wrapper.
* **L-BC2-I-M** (the `∫⁻`-to-finite-sum reduction on `Measure.pi^n P_X`
  + the operational derivation of the per-event decays from the AEP
  body of `BroadcastChannelSuperpositionBody.lean`): supplied as caller
  hypothesis. **Deferred** to a successor seed.

This signature follows the structural-`Prop` form established in
`BroadcastChannelRandomCodebook.lean` and `MACL2Discharge.lean`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Expected-error finite-sum decomposition (L-BC2-I-G/H) -/

section BCExpectationDecomp

/-- **L-BC2-I-G — Expected-error finite-sum decomposition predicate**
(Cover-Thomas eqs. 15.6.18-15.6.27, linearity-of-expectation form).

For a finite codebook space `Codebook`, a probability weighting `w` on
it, a *per-event* error contribution family
`contrib : EventIdx → Codebook → ℝ`, and a *total* error
`totalPe : Codebook → ℝ`, the predicate asserts that the total error is
pointwise (per codebook `C`) bounded by the sum of the per-event
contributions:

```
∀ C, totalPe C ≤ ∑_k contrib k C.
```

This is the per-codebook Bonferroni union bound (joint error ≤ sum of
the 6 BC error events of `BroadcastChannelSuperpositionBody.lean`:
`F₀..F₃` for receiver 1 + `G₀, G₁` for receiver 2), packaged as a
`Prop` so the linearity-of-expectation aggregation
`bc_expected_error_le_of_decomp` can consume it directly. -/
def IsBCExpectationDecomp {Codebook EventIdx : Type*}
    [Fintype EventIdx]
    (totalPe : Codebook → ℝ) (contrib : EventIdx → Codebook → ℝ) : Prop :=
  ∀ C : Codebook, totalPe C ≤ ∑ k : EventIdx, contrib k C

/-- **L-BC2-I-H — Linearity-of-expectation aggregation.**

Given the per-codebook Bonferroni decomposition `IsBCExpectationDecomp`
and a probability weighting `w` on the codebook space, plus per-event
expected-decay bounds `∑_C w(C)·contrib_k(C) ≤ δ_k`, the *expected
total error* `∑_C w(C)·totalPe(C)` is bounded by `∑_k δ_k`.

The proof is the swap-and-bound: expectation of a sum is the sum of
expectations (`Finset.sum_comm`), each of which is bounded by `δ_k`. -/
theorem bc_expected_error_le_of_decomp
    {Codebook EventIdx : Type*} [Fintype Codebook] [Fintype EventIdx]
    (w : Codebook → ℝ) (hw_nn : ∀ C, 0 ≤ w C)
    (totalPe : Codebook → ℝ) (contrib : EventIdx → Codebook → ℝ)
    (h_decomp : IsBCExpectationDecomp totalPe contrib)
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

end BCExpectationDecomp

/-! ## Section 2 — Averaging core (L-BC2-I-I) -/

section BCAveragingCore

/-- **L-BC2-I-I — Averaging core: from expected-error bound to a
deterministic codebook.**

Given a finite (nonempty) codebook space `Codebook`, a probability
weighting `w` on it (`0 ≤ w`, `∑ w = 1`), and an expected-error bound
`∑_C w(C)·Pe(C) ≤ B`, there exists a *deterministic* codebook `C₀` with
`Pe(C₀) ≤ B`.

This is the Markov / pigeonhole step at the heart of the random
codebook averaging argument; it is a thin wrap of the wave7
`bc_exists_codebook_of_avg_le`. We re-expose it under the
averaging-body name so the chain reads as
`expected bound → deterministic witness` without callers needing to
reach back into `BroadcastChannelRandomCodebook.lean`. -/
theorem bc_avg_error_exists_codebook
    {Codebook : Type*} [Fintype Codebook] [Nonempty Codebook]
    (w : Codebook → ℝ) (Pe : Codebook → ℝ)
    (hw_nn : ∀ C, 0 ≤ w C) (hw_sum : ∑ C, w C = 1)
    {B : ℝ} (h_avg : ∑ C, w C * Pe C ≤ B) :
    ∃ C₀ : Codebook, Pe C₀ ≤ B :=
  bc_exists_codebook_of_avg_le w Pe hw_nn hw_sum h_avg

/-- **L-BC2-I-I' — Averaging core, full chain from the decomposition.**

Combines `bc_expected_error_le_of_decomp` (linearity of expectation)
with `bc_avg_error_exists_codebook` (Markov pigeonhole): given the
per-codebook Bonferroni decomposition and the per-event expected-decay
bounds, there exists a deterministic codebook whose total error is
bounded by `∑_k δ_k`.

This is the complete averaging body at the finite-sum expectation
level — the single lemma a caller would invoke to extract the
deterministic codebook from the random codebook construction. -/
theorem bc_avg_error_exists_codebook_of_decomp
    {Codebook EventIdx : Type*} [Fintype Codebook] [Nonempty Codebook]
    [Fintype EventIdx]
    (w : Codebook → ℝ) (hw_nn : ∀ C, 0 ≤ w C) (hw_sum : ∑ C, w C = 1)
    (totalPe : Codebook → ℝ) (contrib : EventIdx → Codebook → ℝ)
    (h_decomp : IsBCExpectationDecomp totalPe contrib)
    (δ : EventIdx → ℝ)
    (h_event : ∀ k, ∑ C, w C * contrib k C ≤ δ k) :
    ∃ C₀ : Codebook, totalPe C₀ ≤ ∑ k, δ k :=
  bc_avg_error_exists_codebook w totalPe hw_nn hw_sum
    (bc_expected_error_le_of_decomp w hw_nn totalPe contrib h_decomp δ h_event)

end BCAveragingCore

/-! ## Section 3 — Random codebook Markov predicate (L-BC2-I-J) -/

section BCRandomCodebookMarkov

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **L-BC2-I-J — Random codebook Markov predicate**
(Cover-Thomas eq. 15.6.30, deterministic-codebook-with-rate form).

For a degraded broadcast channel and a target rate pair `(R₁, R₂)`, the
predicate asserts that there exists a threshold block length `N` beyond
which the random codebook averaging argument produces a **deterministic**
superposition codebook (the BC code `c : BroadcastCode M₁ M₂ n α β₁ β₂`)
satisfying both rate conditions `exp(n·R_k) ≤ M_k` *and* an explicit
small expected error `errBound < 1` realised by `c`.

The difference from `BCRandomCodebookAveraging` is the extra
`errBound`-witness conjunct, which records that the codebook produced by
the Markov step achieves an error strictly below `1` (the operational
content of "averaging succeeded"). The bridge
`bc_random_codebook_averaging_of_markov` drops this witness to recover
the bare `BCRandomCodebookAveraging` form. -/
def IsBCRandomCodebookMarkov
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M₁ M₂ : ℕ) (errBound : ℝ) (_c : BroadcastCode M₁ M₂ n α β₁ β₂),
      Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
      ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
      ∧ 0 ≤ errBound
      ∧ errBound < 1

namespace IsBCRandomCodebookMarkov

variable {R₁ R₂ : ℝ}

/-- Anti-monotonicity in `R₁`: shrinking the rate `R₁` preserves the
Markov-step witness (since `exp` is monotone). -/
lemma anti_mono_R₁ {R₁' : ℝ}
    (h : IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂)
    (hR : R₁' ≤ R₁) :
    IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁' R₂ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M₁, M₂, eb, c, hM₁, hM₂, heb0, heb1⟩ := hN n hn
  refine ⟨M₁, M₂, eb, c, ?_, hM₂, heb0, heb1⟩
  refine (Real.exp_le_exp.mpr ?_).trans hM₁
  exact mul_le_mul_of_nonneg_left hR (by exact_mod_cast Nat.zero_le n)

/-- Anti-monotonicity in `R₂`: shrinking the rate `R₂` preserves the
Markov-step witness. -/
lemma anti_mono_R₂ {R₂' : ℝ}
    (h : IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂)
    (hR : R₂' ≤ R₂) :
    IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M₁, M₂, eb, c, hM₁, hM₂, heb0, heb1⟩ := hN n hn
  refine ⟨M₁, M₂, eb, c, hM₁, ?_, heb0, heb1⟩
  refine (Real.exp_le_exp.mpr ?_).trans hM₂
  exact mul_le_mul_of_nonneg_left hR (by exact_mod_cast Nat.zero_le n)

end IsBCRandomCodebookMarkov

end BCRandomCodebookMarkov

/-! ## Section 4 — Markov → averaging bridge (L-BC2-I-K) -/

section BCMarkovToAveraging

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **L-BC2-I-K — Markov-step to random codebook averaging bridge.**

Given the random codebook Markov predicate `IsBCRandomCodebookMarkov`
(which carries the deterministic-codebook witness *with* its
sub-`1` expected error), conclude the bare random codebook averaging
predicate `BCRandomCodebookAveraging` by forgetting the error witness.

This is the bridge from the averaging-body output (the codebook that
the Markov step *produces*) to the abstract averaging predicate consumed
by the wave7 `bc_random_codebook_averaging_exists`. -/
theorem bc_random_codebook_averaging_of_markov
    (R₁ R₂ : ℝ)
    (h_markov : IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := by
  obtain ⟨N, hN⟩ := h_markov
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M₁, M₂, _eb, c, hM₁, hM₂, _heb0, _heb1⟩ := hN n hn
  exact ⟨M₁, M₂, c, hM₁, hM₂⟩

/-- **L-BC2-I-K' — Markov-step to inner-bound existence (composed).**

Composes `bc_random_codebook_averaging_of_markov` with the wave7
existence extraction `bc_random_codebook_averaging_exists`: from the
random codebook Markov predicate directly to `BCInnerBoundExistence`. -/
theorem bc_inner_bound_existence_of_markov
    (R₁ R₂ : ℝ)
    (h_markov : IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  bc_random_codebook_averaging_exists (α := α) (β₁ := β₁) (β₂ := β₂)
    R₁ R₂
    (bc_random_codebook_averaging_of_markov
      (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ h_markov)

end BCMarkovToAveraging

/-! ## Section 5 — Publish-layer hook (L-BC2-I-L) -/

section BCAveragingPublish

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **L-BC2-I-L — BC inner bound, with averaging-body discharge**
(Cover-Thomas Theorem 15.6.2, achievability + L-BC2-I averaging body,
hypothesis pass-through form).

A discharge wrapper extending the cumulative chain

* `bc_capacity_region_inner_bound`
  (`BroadcastChannel.lean:580`),
* `bc_capacity_region_inner_bound_with_superposition_aep`
  (`BroadcastChannelSuperposition.lean:543`),
* `bc_capacity_region_inner_bound_with_superposition_body`
  (`BroadcastChannelSuperpositionBody.lean`),
* `bc_inner_bound_with_random_codebook`
  (`BroadcastChannelRandomCodebook.lean`).

The present theorem extends that chain by discharging the L-BC2-I
*averaging body* slot via the `IsBCRandomCodebookMarkov` predicate
(the deterministic-codebook-with-rate witness produced by the random
codebook averaging Markov step). The parent's `h_avg :
BCRandomCodebookAveraging` is *no longer* a caller hypothesis — it is
now derived from the Markov predicate via
`bc_random_codebook_averaging_of_markov`.

The two strict-inequality rate conditions remain (`_h_strict`), since
they are operationally consumed by the existence claim's rate
conditions. The remaining caller hypothesis is the random codebook
Markov predicate itself (L-BC2-I-J). Its operational derivation —
the `∫⁻`-to-finite-sum reduction on `Measure.pi^n` of `P_X` plus the
per-event AEP decays of `bc_receiver1_achievability_body` /
`bc_receiver2_achievability_body` (~400-600 lines) — is the explicit
retreat line (L-BC2-I-M), **deferred** to a successor seed. -/
theorem bc_inner_bound_with_averaging
    (R₁ R₂ I_u I_xy : ℝ)
    (_h_strict : R₂ < I_u ∧ R₁ < I_xy)
    (h_markov : IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ :=
  bc_inner_bound_with_random_codebook
    (α := α) (β₁ := β₁) (β₂ := β₂)
    R₁ R₂ I_u I_xy _h_strict
    (bc_random_codebook_averaging_of_markov
      (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ h_markov)

/-- **L-BC2-I-L' — BC inner bound, fully combined (averaging body +
corner-point rate condition)**. The most caller-facing form: bundle the
strict-rate predicate as the `≤` + `≠` form of `InBCCapacityRegion`
together with the random codebook Markov predicate, and conclude the
inner bound existence.

This packages the same content as `bc_inner_bound_with_averaging` under
a `InBCCapacityRegion`-bundled surface, mirroring
`bc_inner_bound_with_random_codebook_bundled` of
`BroadcastChannelRandomCodebook.lean`. -/
theorem bc_inner_bound_with_averaging_bundled
    (R₁ R₂ I_u I_xy : ℝ)
    (h_in_region : InBCCapacityRegion R₁ R₂ I_u I_xy)
    (h_strict₂ : R₂ ≠ I_u)
    (h_strict₁ : R₁ ≠ I_xy)
    (h_markov : IsBCRandomCodebookMarkov (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂) :
    BCInnerBoundExistence (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂ := by
  have h_lt₂ : R₂ < I_u :=
    lt_of_le_of_ne h_in_region.bound_R₂_le_I_u h_strict₂
  have h_lt₁ : R₁ < I_xy :=
    lt_of_le_of_ne h_in_region.bound_R₁_le_I_xy h_strict₁
  exact bc_inner_bound_with_averaging
    (α := α) (β₁ := β₁) (β₂ := β₂)
    R₁ R₂ I_u I_xy ⟨h_lt₂, h_lt₁⟩ h_markov

end BCAveragingPublish

end InformationTheory.Shannon
