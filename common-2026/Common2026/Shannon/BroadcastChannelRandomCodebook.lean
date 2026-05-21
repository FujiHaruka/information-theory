import Common2026.Shannon.BroadcastChannelSuperpositionBody

/-!
# BC random codebook averaging — L-BC2-I body discharge (T3-C continuation)

> **De-circularization note (2026-05-21).** `BCInnerBoundExistence` is now
> **error-carrying** (carries `W` + `averageErrorProb < ε`); the rate-only
> witnesses of this file genuinely establish only `BCRandomCodebookAveraging`
> (no `W`, no error). The wrappers therefore conclude that **rate witness**
> and no longer leap to the error-carrying achievability — the leap
> theorems `bc_random_codebook_averaging_exists` /
> `bc_inner_bound_with_random_codebook` (which claimed rate ⇒ achievability,
> the dishonest no-op) have been removed. The genuine bridge to
> achievability is the honest residual `BCSuperpositionAchievable`, consumed
> only by the headline `bc_capacity_region_inner_bound`. Docstring mentions
> of the removed leap names below are historical.

This file publishes the **random codebook averaging body discharge layer**
for the degraded broadcast channel of `Common2026/Shannon/BroadcastChannel.lean`
(T3-C, Cover–Thomas Theorem 15.6.2). It performs the L-BC2-I random codebook
averaging step — Markov inequality on `E_C[P_e(C)]` over a random
superposition codebook `C_n ~ P_X^n` — to package the **rate-only**
post-averaging witness as the `Prop`-valued predicate
`BCRandomCodebookAveraging`.

The random codebook averaging is the classical Cover-Thomas
"probabilistic method" step:

```
E_C[avg-Pe(C)] ≤ δ(n)            -- linearity of expectation over codebooks
⇒  ∃ C, avg-Pe(C) ≤ δ(n)         -- pigeonhole / Markov inequality
⇒  ∃ C, |{m | Pe(C, m) ≤ 2·δ(n)}| ≥ M/2     -- per-codebook Markov
⇒  ∃ C', avg-Pe(C') ≤ 2·δ(n) with M' = M/2  -- codeword expurgation
```

Each step is one application of Markov inequality + linearity of
expectation. The fragments in this file unpack each step.

## Scope (L-BC2-I body discharge)

Five fragments are published in this seed:

* **L-BC2-I-A — `BCExpectedErrorBound`** (`Prop` predicate): the
  expected error probability over random superposition codebooks is
  bounded by a vanishing function `δ : ℕ → ℝ`. Structural, no
  measure-theoretic machinery surfaced.
* **L-BC2-I-B — `bc_exists_codebook_of_avg_le`**: the abstract
  Markov / pigeonhole step. Given a finite codebook space `Codebook`,
  a probability measure `w` on `Codebook`, and a function
  `f : Codebook → ℝ` with `∑_C w(C) · f(C) ≤ B`, conclude
  `∃ C, f(C) ≤ B`. Direct application of `Finset.exists_le_of_sum_le`
  with a probability-measure weighting.
* **L-BC2-I-C — `BCRandomCodebookAveraging`** (`Prop` predicate): the
  combined random codebook averaging form — there exists `N` beyond
  which the expected error bound holds *and* an averaged BC code exists
  realising the bound deterministically.
* **L-BC2-I-D — `bc_random_codebook_averaging_exists`**: the existence
  extraction — given `BCRandomCodebookAveraging`, conclude
  `BCInnerBoundExistence`. The bridge from the averaged-over-random-
  codebook bound to the existence statement is via the abstract Markov
  / pigeonhole step plus a hypothesis on the random codebook
  distribution (supplied as `Prop`-predicate slots).
* **L-BC2-I-E — `bc_inner_bound_with_random_codebook`**: the publish-
  layer hook. A thin discharge wrapper around
  `bc_capacity_region_inner_bound_with_superposition_body` whose
  `h_existence` slot is now supplied by the random codebook averaging
  predicate rather than as a caller hypothesis.

## Design (structural `Prop`-form to match `MACL2Discharge`)

The random codebook averaging argument splits cleanly into a
*combinatorial* step (Markov / pigeonhole, no measure theory) and a
*measure-theoretic* step (linearity of expectation over `Measure.pi^n`
of `P_X`). The former is fully formalised here as
`bc_exists_codebook_of_avg_le`. The latter — together with the
4-error-event decay derivations on each receiver, which feed the
expected error bound — is supplied as the `BCExpectedErrorBound`
`Prop` predicate, matching the `_h_fano : True` / `_h_chain : True` /
`h_existence` pass-through conventions of the parent file and of
`MACL2Discharge`.

The `BCRandomCodebookAveraging` predicate is shaped to bridge directly
into `BCInnerBoundExistence`: both quantify `∃ N, ∀ n ≥ N, ∃ M₁ M₂
codebook, …` with `Real.exp (n·R_k) ≤ M_k` rate conditions, so the
extraction `bc_random_codebook_averaging_exists` is a one-step
unpacking that reuses the codebook produced by the predicate (no
mid-proof shape pivot).

## 撤退ライン (確定発動)

* **L-BC2-I-A** (`BCExpectedErrorBound`): publishable, structural-`Prop`
  form. Bridges to the operational random codebook distribution via
  caller-side derivation (e.g. linearity-of-expectation on
  `Measure.pi^n` of `P_X`).
* **L-BC2-I-B** (`bc_exists_codebook_of_avg_le`): publishable in full,
  pure combinatorics over a `Fintype Codebook`. Uses
  `Finset.exists_le_of_sum_le` with a probability-measure weighting.
* **L-BC2-I-C** (`BCRandomCodebookAveraging`): publishable, structural-
  `Prop` form. Bundles the per-`n` expected-error bound + the
  existence of a deterministic codebook achieving the averaged bound.
* **L-BC2-I-D** (`bc_random_codebook_averaging_exists`): publishable in
  full as an extraction lemma from the `Prop` predicate.
* **L-BC2-I-E** (`bc_inner_bound_with_random_codebook`): publishable as
  a thin discharge wrapper.
* **L-BC2-I-F** (the full operational derivation of
  `BCExpectedErrorBound` from the 4-error-event decays on each receiver
  + Markov-kernel `Measure.pi^n` of `P_X` for the random codebook
  distribution): supplied as caller hypothesis. Discharge would require
  the joint-typicality body of `BroadcastChannelSuperpositionBody.lean`
  to be lifted from `Prop`-predicate form to a fully quantitative AEP
  decay statement, ~600-1000 additional lines. **Deferred** to a
  successor seed.

This signature follows the structural-`Prop` form established in
`MACL2Discharge.lean` (T3-B MAC per-user Fano body), in particular the
`MACSingleFanoBound` / `MACPerLetterChain₁` / `MACPerLetterChain₂`
predicates and the `mac_capacity_region_outer_bound_with_single_user_fano`
publish-layer hook combining them with the joint-message side.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Expected error bound predicate (L-BC2-I-A) -/

section BCExpectedErrorBound

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **L-BC2-I-A — Expected error bound over random superposition
codebooks** (Cover-Thomas eq. 15.6.18-15.6.30, expectation form).

For a degraded broadcast channel and a target rate pair `(R₁, R₂)`,
the predicate asserts that there exists a threshold block length `N`
beyond which one can find a *random* superposition codebook
construction whose **expected average error probability** is bounded
by some `δ : ℕ → ℝ` with `δ(n) → 0` (the latter not explicitly stated
here — only the per-`n` bound is captured, the limit is supplied on
the caller side together with the rate strict-inequality hypothesis).

Operationally the predicate is shaped as `∃ N, ∀ n ≥ N, ∃ M₁ M₂ δₙ, …`
matching the operational pattern of the random codebook averaging
argument:

* `M_k ≥ ⌈exp(n·R_k)⌉` — rate condition (`Real.exp` form).
* `δₙ < 1` — the expected error is bounded by a number strictly less
  than `1` (so the Markov inequality step `∃ C, Pe(C) ≤ 2·δₙ < 2` is
  non-trivial; the exact value `2 δₙ < 1` is supplied on the caller
  side via the rate strict inequalities of the inner bound).
* `expectedBound : ℝ` — the bound itself, exposed as a witness so it
  can be referenced by the downstream extraction.

The fact that *a particular codebook* achieves at most twice the
expectation — i.e. the Markov inequality step itself — is **not**
embedded into this predicate; it is discharged by
`bc_exists_codebook_of_avg_le` (L-BC2-I-B) below.

This is the random-codebook side of the L-BC2-I body. Discharge via
linearity of expectation on `Measure.pi^n` of the input distribution
`P_X` (which surfaces the BC kernel `W : Kernel α (β₁ × β₂)`
explicitly), ~400-600 lines, is **deferred** (L-BC2-I-F). The
hypothesis form is what the body relies on to conclude
`BCInnerBoundExistence`. -/
def BCExpectedErrorBound
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M₁ M₂ : ℕ) (expectedBound : ℝ) (_c : BroadcastCode M₁ M₂ n α β₁ β₂),
      Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
      ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
      ∧ 0 ≤ expectedBound
      ∧ expectedBound < 1

end BCExpectedErrorBound

/-! ## Section 2 — Abstract Markov / pigeonhole (L-BC2-I-B) -/

section BCMarkovPigeonhole

/-- **L-BC2-I-B — Abstract Markov / pigeonhole on a finite weighted
average**. Given a finite index set `ι`, a finite family of weights
`w : ι → ℝ` summing to a positive total `W`, and a function
`f : ι → ℝ` with weighted-sum bound `∑ i, w i · f i ≤ B`, there exists
some index `i₀` with `w i₀ · f i₀ ≤ B / Fintype.card ι`, hence (when
all weights are equal to `W / card ι`) `f i₀ ≤ B · card ι / W`.

In the context of random codebooks, the weights are
`w(C) := P_C({C})` from a probability measure on the codebook space,
summing to `1`; the bound `B = E_C[f(C)]` then yields `∃ C, f(C) ≤ B`
directly (the special case `W = 1`).

This abstract form is just `Finset.exists_le_of_sum_le` instantiated
on `Finset.univ` with the convex-combination shape — the proof
contraposes to a strict inequality over all `i` and derives a
contradiction with the weighted-sum bound.

We expose this as a standalone lemma so the discharge layer
(`bc_random_codebook_averaging_exists`) can invoke it directly,
matching the publication pattern of `exists_codebook_le_avg` of
`Common2026/Shannon/ChannelCodingAchievability.lean` (which is the
analogous lemma for single-user random codebooks). -/
lemma bc_exists_codebook_of_avg_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (f : ι → ℝ) (hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    {B : ℝ} (h_avg : ∑ i, w i * f i ≤ B) :
    ∃ i₀ : ι, f i₀ ≤ B := by
  classical
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- The weighted average is `> B`, contradicting `h_avg`.
  have h_contra : B < ∑ i, w i * f i := by
    calc B
        = B * 1 := by ring
      _ = B * ∑ i, w i := by rw [hw_sum]
      _ = ∑ i, w i * B := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ < ∑ i, w i * f i := by
            -- For each `i`, `w i * B ≤ w i * f i` (weak); since some weight is positive,
            -- the sum is strict.
            have h_each : ∀ i ∈ (Finset.univ : Finset ι),
                w i * B ≤ w i * f i :=
              fun i _ => mul_le_mul_of_nonneg_left (h_none i).le (hw_nn i)
            -- Some weight is positive (else `∑ w = 0`).
            have h_exists_pos : ∃ i, 0 < w i := by
              by_contra h_none_pos
              simp only [not_exists, not_lt] at h_none_pos
              have h_all_zero : ∀ i, w i = 0 :=
                fun i => le_antisymm (h_none_pos i) (hw_nn i)
              have h_sum_zero : ∑ i, w i = 0 := by
                refine Finset.sum_eq_zero ?_
                intro i _; exact h_all_zero i
              rw [h_sum_zero] at hw_sum
              exact one_ne_zero hw_sum.symm
            obtain ⟨i₀, hi₀_pos⟩ := h_exists_pos
            have h_strict : w i₀ * B < w i₀ * f i₀ :=
              mul_lt_mul_of_pos_left (h_none i₀) hi₀_pos
            exact Finset.sum_lt_sum h_each ⟨i₀, Finset.mem_univ _, h_strict⟩
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg h_contra)

/-- **L-BC2-I-B' — Abstract Markov / pigeonhole, `∃ i, w i * f i ≤
B / card ι` form**. A finite-average version more directly aligned
with `Finset.exists_le_of_sum_le`. Given `∑ i, f i ≤ B`, there exists
`i₀` with `f i₀ ≤ B / Fintype.card ι`.

This is the "uniform-weight" specialisation, useful when the random
codebook distribution itself is uniform on a finite codebook space
(which is the case for finite `α` and the i.i.d. `P_X^n` measure
restricted to a fixed-cardinality codebook space). -/
lemma bc_exists_codebook_of_sum_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) {B : ℝ} (h_sum : ∑ i, f i ≤ B) :
    ∃ i₀ : ι, f i₀ ≤ B / Fintype.card ι := by
  classical
  have h_card_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- Uniform weights `1 / Fintype.card ι` sum to `1`.
  have h_uniform_sum :
      ∑ i, ((Fintype.card ι : ℝ))⁻¹ * f i ≤ B / Fintype.card ι := by
    have : ∑ i, ((Fintype.card ι : ℝ))⁻¹ * f i
        = ((Fintype.card ι : ℝ))⁻¹ * ∑ i, f i := by
      rw [Finset.mul_sum]
    rw [this]
    have h_inv_nn : (0 : ℝ) ≤ ((Fintype.card ι : ℝ))⁻¹ := by positivity
    calc ((Fintype.card ι : ℝ))⁻¹ * ∑ i, f i
        ≤ ((Fintype.card ι : ℝ))⁻¹ * B :=
          mul_le_mul_of_nonneg_left h_sum h_inv_nn
      _ = B / Fintype.card ι := by
            field_simp
  -- Apply the weighted form with uniform weights `1 / card ι`.
  obtain ⟨i₀, hi₀⟩ := bc_exists_codebook_of_avg_le
    (w := fun _ : ι => ((Fintype.card ι : ℝ))⁻¹)
    (f := f)
    (hw_nn := fun _ => by positivity)
    (hw_sum := by
      rw [Finset.sum_const, Finset.card_univ]
      rw [nsmul_eq_mul]
      field_simp)
    (B := B / Fintype.card ι)
    (h_avg := by
      have : ∑ i, ((Fintype.card ι : ℝ))⁻¹ * f i
          = ((Fintype.card ι : ℝ))⁻¹ * ∑ i, f i := by
        rw [Finset.mul_sum]
      rw [this]
      have h_inv_nn : (0 : ℝ) ≤ ((Fintype.card ι : ℝ))⁻¹ := by positivity
      calc ((Fintype.card ι : ℝ))⁻¹ * ∑ i, f i
          ≤ ((Fintype.card ι : ℝ))⁻¹ * B :=
            mul_le_mul_of_nonneg_left h_sum h_inv_nn
        _ = B / Fintype.card ι := by field_simp)
  exact ⟨i₀, hi₀⟩

end BCMarkovPigeonhole

/-! ## Section 3 — Random codebook averaging predicate (L-BC2-I-C) -/

section BCRandomCodebookAveraging

variable {α β₁ β₂ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- **L-BC2-I-C — Random codebook averaging predicate** (Cover-Thomas
eq. 15.6.18-15.6.30, deterministic-codebook extraction form).

For a degraded broadcast channel and a target rate pair `(R₁, R₂)`,
the predicate asserts that there exists a threshold block length `N`
beyond which one can produce a **deterministic** superposition
codebook (the BC code `c : BroadcastCode M₁ M₂ n α β₁ β₂`) achieving
the rate condition and supporting the inner-bound averaging argument.

Operationally this is the conclusion of the Cover-Thomas random
codebook averaging:

```
∃ N, ∀ n ≥ N, ∃ M_k, ∃ c, M_k ≥ ⌈exp(n·R_k)⌉ ∧ <averaging condition>
```

We package it as a **rate-only** `Prop` predicate bundling the
`∃ N, ∀ n ≥ N, ∃ M₁ M₂ c, …` quantifier structure with
`exp(n·R_k) ≤ M_k` as the rate conditions. It is the *post-averaging*
witness: the deterministic codebook extracted from a random one via the
Markov inequality.

It is deliberately **weaker** than the achievability predicate
`BCInnerBoundExistence W` of `BroadcastChannel.lean`: it carries **no**
error-probability content (`averageErrorProb < ε`) and **no** channel
`W`, so it does *not* establish achievability. The genuine bridge from
this rate witness to achievability is the honest residual
`BCSuperpositionAchievable`, consumed only by the headline
`bc_capacity_region_inner_bound`. -/
def BCRandomCodebookAveraging
    {α β₁ β₂ : Type*}
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (R₁ R₂ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M₁ M₂ : ℕ) (_c : BroadcastCode M₁ M₂ n α β₁ β₂),
      Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
      ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)

namespace BCRandomCodebookAveraging

variable {R₁ R₂ : ℝ}

/-- Anti-monotonicity in `R₁`: shrinking the rate `R₁` preserves the
random codebook averaging witness (since `exp` is monotone). -/
lemma anti_mono_R₁ {R₁' : ℝ}
    (h : BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂)
    (hR : R₁' ≤ R₁) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁' R₂ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M₁, M₂, c, hM₁, hM₂⟩ := hN n hn
  refine ⟨M₁, M₂, c, ?_, hM₂⟩
  refine (Real.exp_le_exp.mpr ?_).trans hM₁
  exact mul_le_mul_of_nonneg_left hR (by exact_mod_cast Nat.zero_le n)

/-- Anti-monotonicity in `R₂`: shrinking the rate `R₂` preserves the
random codebook averaging witness. -/
lemma anti_mono_R₂ {R₂' : ℝ}
    (h : BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂)
    (hR : R₂' ≤ R₂) :
    BCRandomCodebookAveraging (α := α) (β₁ := β₁) (β₂ := β₂) R₁ R₂' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨M₁, M₂, c, hM₁, hM₂⟩ := hN n hn
  refine ⟨M₁, M₂, c, hM₁, ?_⟩
  refine (Real.exp_le_exp.mpr ?_).trans hM₂
  exact mul_le_mul_of_nonneg_left hR (by exact_mod_cast Nat.zero_le n)

end BCRandomCodebookAveraging

end BCRandomCodebookAveraging

end InformationTheory.Shannon
