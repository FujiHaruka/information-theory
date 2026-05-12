import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.IIDProductInput
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Channel coding achievability theorem (B-3'')

[B-3'' Phase C+D plan](../../../docs/shannon/channel-coding-phase-cd-plan.md).

Phase A+B are completed in `Common2026/Shannon/ChannelCoding.lean` (659 行).
This file adds:

* **Phase C** (random codebook + averaging argument): Codebook + joint typical
  decoder definition; per-codeword error decomposition; random-codebook average
  bound; pigeonhole `∃ codebook, P_err ≤ avg`.
* **Phase D** (main theorem): `R < I(p; W) ⟹ ∃ N, ∀ n ≥ N, ∃ M ≥ exp(nR), ∃ code,
  averageErrorProb < ε`.

Skeleton phase: every lemma/theorem body is `:= by sorry` (or `:= sorry` for
non-`Prop` definitions that are sorry-placeheld). The next agent fills.

## Design choices

* Codebook is `Fin M → (Fin n → α)` (abbrev).
* The **codebook average** is taken over the `p`-i.i.d. law
  `codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`
  on the finite space `Codebook M n α`. The earlier-drafted uniform-on-codebook form
  is **inconsistent** with the Phase B bounds unless `p` is uniform on `α`; the
  probabilistic-method form (this file) matches Cover-Thomas Theorem 7.7.3-4.
* Decoder = `Classical.dec`-based "unique joint-typical `m`, else fallback `⟨0, hM⟩`".
* i.i.d. extension `Ω := Fin n → α × β`, `μ := Measure.pi (fun _ => jointDistribution p W)`
  is captured by `iidJointMeasure p W n` below; Phase D-(b) will use the infinite
  version `Measure.infinitePi (jointDistribution p W)` once that plumbing is in.
* Rate slack `ε := (I - R) / 6`; `M := Nat.ceil (Real.exp (n · R))`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### Phase 0 — i.i.d. input × channel plumbing -/

section IIDInput

/-- The i.i.d. extension of `(p, W)` to length-`n` blocks: a measure on
`Fin n → α × β` whose `i`-th coordinate has law `jointDistribution p W`. -/
noncomputable def iidJointMeasure
    (p : Measure α) (W : Channel α β) (n : ℕ) : Measure (Fin n → α × β) :=
  Measure.pi (fun _ : Fin n => jointDistribution p W)

instance iidJointMeasure.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] (n : ℕ) :
    IsProbabilityMeasure (iidJointMeasure p W n) := by
  unfold iidJointMeasure
  infer_instance

end IIDInput

/-! ### Phase C-(a) — Codebook + joint-typical decoder -/

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- A random codebook is just a function from message indices to length-`n` words. -/
abbrev Codebook (M n : ℕ) (α : Type*) [MeasurableSpace α] :=
  Fin M → (Fin n → α)

/-- **Joint-typical decoder.** Given a received word `y`, returns the unique
message `m` such that `(codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε`, falling
back to `⟨0, hM⟩` if either no such `m` exists or it is not unique. -/
noncomputable def jointTypicalDecoder
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    (Fin n → β) → Fin M := fun y =>
  haveI : Decidable (∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! m : Fin M, (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h.exists
    else ⟨0, hM⟩

/-- Bundle a codebook + joint-typical decoder into a `Code`. -/
noncomputable def codebookToCode
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (codebook : Codebook M n α) :
    Code M n α β where
  encoder := codebook
  decoder := jointTypicalDecoder μ Xs Ys hM ε codebook

/-! ### Phase C-(b) — Per-codeword error decomposition -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] [DecidableEq β]
  [Nonempty β] in
/-- **Per-codeword error bound.** The point-wise error probability of message `m`
under the joint-typical decoder is bounded by the (E1) "true codeword not typical"
event plus the (E2) "some alias codeword is typical" union bound. -/
theorem errorProbAt_le_E1_plus_E2
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ}
    (codebook : Codebook M n α) (m : Fin M) :
    ((codebookToCode μ Xs Ys hM ε codebook).errorProbAt W m).toReal
      ≤ (Measure.pi (fun i => W (codebook m i))).real
          {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε}
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            (Measure.pi (fun i => W (codebook m i))).real
              {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} := by
  classical
  -- Abbreviations.
  set c : Code M n α β := codebookToCode μ Xs Ys hM ε codebook with hc_def
  set ν : Measure (Fin n → β) := Measure.pi (fun i => W (codebook m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by
    rw [hν_def]; infer_instance
  -- Define the (E1) and (E2) sets.
  set E1 : Set (Fin n → β) :=
    {y | (codebook m, y) ∉ jointlyTypicalSet μ Xs Ys n ε} with hE1_def
  set E2_indiv : Fin M → Set (Fin n → β) := fun m' =>
    {y | (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε} with hE2_def
  -- Step 1: `c.errorEvent m ⊆ E1 ∪ (⋃ m' ∈ univ.erase m, E2_indiv m')`.
  have h_sub :
      c.errorEvent m ⊆ E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m' := by
    intro y hy
    rw [Code.mem_errorEvent] at hy
    -- `c.decoder y = jointTypicalDecoder μ Xs Ys hM ε codebook y`.
    have hdec : c.decoder y = jointTypicalDecoder μ Xs Ys hM ε codebook y := rfl
    -- Case analyze on whether there is a unique joint-typical `m'`.
    by_cases hu : ∃! m' : Fin M, (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε
    · -- A unique `m'` exists. Decoder returns `Classical.choose hu.exists`.
      have hch : c.decoder y = Classical.choose hu.exists := by
        rw [hdec]
        unfold jointTypicalDecoder
        rw [dif_pos hu]
      set m' := Classical.choose hu.exists with hm'_def
      have hm'_mem : (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε :=
        Classical.choose_spec hu.exists
      have hm'_ne : m' ≠ m := by
        intro hmm
        apply hy
        rw [hch, ← hmm]
      -- Either the true `m` is not typical (E1), or the chosen `m'` ≠ m is typical (E2).
      by_cases hm_typ : (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
      · -- `m` is also typical. Uniqueness ⇒ `m' = m`, contradicting `hm'_ne`.
        have : m' = m := hu.unique hm'_mem hm_typ
        exact absurd this hm'_ne
      · -- `m` is NOT typical: y ∈ E1.
        left
        exact hm_typ
    · -- No unique typical `m'`. Decoder falls back to `⟨0, hM⟩` ≠ … ?
      -- Either NO typical `m'` exists, or multiple do.
      by_cases hexists : ∃ m' : Fin M, (codebook m', y) ∈ jointlyTypicalSet μ Xs Ys n ε
      · -- Multiple typical `m'` exist (because not unique). At least two distinct ones.
        -- We exhibit some `m' ≠ m` that is typical.
        -- Since not unique: either (a) the true `m` is not typical, or
        -- (b) some other typical `m'' ≠ m` exists.
        by_cases hm_typ : (codebook m, y) ∈ jointlyTypicalSet μ Xs Ys n ε
        · -- `m` is typical. Since not unique, some `m'' ≠ m` is also typical.
          -- Suppose for contradiction every typical witness equals `m`. Then
          -- `m` is the unique one — contradicting `¬ hu`.
          have h_alias : ∃ m'' : Fin M, (codebook m'', y) ∈ jointlyTypicalSet μ Xs Ys n ε ∧ m'' ≠ m := by
            by_contra h_none
            apply hu
            refine ⟨m, hm_typ, ?_⟩
            intro m'' hm''_typ
            by_contra hne
            exact h_none ⟨m'', hm''_typ, hne⟩
          obtain ⟨m'', hm''_typ, hm''_ne⟩ := h_alias
          right
          refine Set.mem_iUnion.mpr ⟨m'', ?_⟩
          refine Set.mem_iUnion.mpr ⟨?_, hm''_typ⟩
          exact Finset.mem_erase.mpr ⟨hm''_ne, Finset.mem_univ _⟩
        · -- `m` not typical: y ∈ E1.
          left; exact hm_typ
      · -- No typical `m'` at all ⇒ in particular `m` is not typical: y ∈ E1.
        left
        intro hm_typ
        exact hexists ⟨m, hm_typ⟩
  -- Step 2: bound the measure.
  -- First: `c.errorProbAt W m = ν (c.errorEvent m)` (by defeq of `codebookToCode`).
  have h_eq_meas : c.errorProbAt W m = ν (c.errorEvent m) := by
    show (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m) = _
    rfl
  -- The error event is measurable (finite alphabet).
  have h_meas_err : MeasurableSet (c.errorEvent m) :=
    (Set.toFinite _).measurableSet
  -- `ν (c.errorEvent m) ≠ ∞`.
  have h_ne_top : ν (c.errorEvent m) ≠ ∞ := measure_ne_top _ _
  -- Convert to .real.
  have h_real_eq : (c.errorProbAt W m).toReal = ν.real (c.errorEvent m) := by
    rw [h_eq_meas]; rfl
  rw [h_real_eq]
  -- Apply monotonicity and union bound.
  have h_meas_E1 : MeasurableSet E1 := (Set.toFinite _).measurableSet
  have h_meas_union : MeasurableSet (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    (Set.toFinite _).measurableSet
  have h_step1 : ν.real (c.errorEvent m) ≤
      ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    measureReal_mono h_sub (by exact measure_ne_top _ _)
  have h_step2 : ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m')
      ≤ ν.real E1 + ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') :=
    measureReal_union_le _ _
  have h_step3 :
      ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m')
      ≤ ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, ν.real (E2_indiv m') := by
    exact measureReal_biUnion_finset_le _ _
  -- Combine.
  calc ν.real (c.errorEvent m)
      ≤ ν.real (E1 ∪ ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') := h_step1
    _ ≤ ν.real E1 + ν.real (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2_indiv m') := h_step2
    _ ≤ ν.real E1 + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m, ν.real (E2_indiv m') := by
        gcongr

/-! ### Phase C-(c) — Random codebook average bound (probabilistic-method form)

The originally-drafted statement averaged over a **uniform** distribution on
`Codebook M n α := Fin M → (Fin n → α)`. That form is intrinsically inconsistent
with the Phase B-(a) / B-(c) bounds, which speak about a **`p`-i.i.d.** law on
the input alphabet. When `p` is not the uniform on `α`, the uniform-on-codebook
expectation does *not* equal any `p`-derived quantity.

We restate Phase C-(c) in the standard Cover-Thomas form: average over the
product law `p^{Mn}` on `Codebook M n α`. Concretely, the codebook law is
`codebookMeasure p M n := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`.
Because `α` is finite, this `Measure.pi` is determined by its values on singletons
`{codebook}`, namely the product `∏ m i, p.real {codebook m i}`; the codebook
average is then a finite weighted sum.

The proof itself remains a placeholder (`sorry`) until the Fubini swap between
"codebook expectation" and "i.i.d. expectation over `(X^n, Y^n)`" is built out.
Both sides of the inequality are well-typed and compile. -/

/-- Product law `p^{Mn}` on the codebook space. -/
noncomputable def codebookMeasure
    (p : Measure α) (M n : ℕ) : Measure (Codebook M n α) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))

instance codebookMeasure.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p] (M n : ℕ) :
    IsProbabilityMeasure (codebookMeasure p M n) := by
  unfold codebookMeasure
  infer_instance

/-- **Random codebook average (probabilistic-method form).** With each codeword
drawn i.i.d. from `p^n` (so the codebook law is `codebookMeasure p M n`), the
codebook-average of the (uniform-over-message) error probability decomposes via
Fubini into the Phase B-(a) "joint typical event probability" plus
`(M - 1) ·` the Phase B-(c) independent-pair bound.

The proof is **deferred**: it requires (i) a Fubini-style swap between codebook
average and the `(X^n, Y^n)` distribution under `μ`, (ii) the marginal-matching
hypothesis `μ.map (Xs 0) = p`, and (iii) the chain of equalities relating the
`(Measure.pi (fun i => W (codebook m i)))` channel-output law to the marginal
of `μ` along `Ys`. The statement is checked to type-check; the proof body is
left as `sorry`. -/
theorem random_codebook_average_le
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {q})
    (h_match_X : μ.map (Xs 0) = p) :
    ∑ codebook : Codebook M n α,
        (codebookMeasure p M n).real {codebook} *
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal
    ≤ μ.real
        {ω | (jointRV Xs n ω, jointRV Ys n ω) ∉ jointlyTypicalSet μ Xs Ys n ε}
      + ((M : ℝ) - 1) *
          Real.exp ((n : ℝ) *
            ((entropy μ (jointSequence Xs Ys 0)
              - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3 * ε)) := by
  -- The full proof decomposes via `errorProbAt_le_E1_plus_E2` into per-codeword
  -- E1 / E2 sums averaged over the codebook law `codebookMeasure p M n`, then
  -- a Fubini-style swap between codebook expectation and the `(X^n, Y^n)`
  -- expectation under `μ`. The (E1) term `∑_c w(c) [Wⁿ(cₘ)] (cₘ, y) ∉ A_ε^n`
  -- collapses to `μ.real {(X^n, Y^n) ∉ A_ε^n}` via `h_match_X` and a tight
  -- chain of map / Fubini lemmas; the (E2) term factors over independent codewords
  -- `(cₘ, c_{m'})` to give the (Phase B-(c)) `((μ.map Xⁿ).prod (μ.map Yⁿ))` bound,
  -- which `jointlyTypicalSet_indep_prob_le` bounds by `Real.exp(n(HZ-HX-HY+3ε))`,
  -- summed over `M-1` aliases. This Fubini plumbing (~80-120 lines) is the
  -- one deferred ingredient for the channel-coding achievability moonshot;
  -- the statement is consumer-ready (Phase D-(b) instantiates it on the
  -- concrete i.i.d. ambient and closes the main theorem).
  sorry

/-! ### Phase C-(d) — Pigeonhole (probabilistic-method form)

Restated to match the probabilistic-method shape of Phase C-(c): instead of a
uniform average over `Codebook M n α`, we draw codebooks from
`codebookMeasure p M n`. The pigeonhole is unchanged in spirit — if the
expectation `∑ codebook, μ_codebook · f(codebook) ≤ B`, then some `codebook` in
the support has `f(codebook) ≤ B`. The proof uses the fact that the codebook
measure is a probability measure (mass sums to `1` over the finite space) so the
weighted average is a convex combination. -/

omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
  [MeasurableSingletonClass β] in
/-- **Pigeonhole (probabilistic-method form).** If the codebook expectation is
`≤ B`, then there exists a single codebook with `averageErrorProb ≤ B`. -/
theorem exists_codebook_le_avg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (B : ℝ)
    (h_avg :
      ∑ codebook : Codebook M n α,
        (codebookMeasure p M n).real {codebook} *
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B) :
    ∃ codebook : Codebook M n α,
      ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  -- Strategy: a convex combination `∑ w_i x_i ≤ B` with `w_i ≥ 0` and `∑ w_i = 1`
  -- implies `∃ i, x_i ≤ B`. Otherwise `x_i > B ∀ i`, so `∑ w_i x_i > ∑ w_i B = B`,
  -- contradiction.
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- The codebook measure is a probability measure: `∑ codebook, w(codebook) = 1`.
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Codebook M n α) := Pi.instMeasurableSingletonClass
  have h_sum_one : ∑ codebook : Codebook M n α,
      (codebookMeasure p M n).real {codebook} = 1 := by
    -- `Measure.pi` of probability measures is a probability measure.
    haveI : IsProbabilityMeasure (codebookMeasure p M n) :=
      codebookMeasure.instIsProbabilityMeasure p M n
    -- `sum_measureReal_singleton`: `∑ b ∈ Finset.univ, μ.real {b} = μ.real (Finset.univ : Set _)`.
    have h_real_univ : (codebookMeasure p M n).real
        ((Finset.univ : Finset (Codebook M n α)) : Set _) = 1 := by
      rw [Finset.coe_univ]
      rw [measureReal_def, measure_univ]
      rfl
    have h_sum_eq :=
      sum_measureReal_singleton (μ := codebookMeasure p M n)
        (Finset.univ : Finset (Codebook M n α))
    rw [h_sum_eq, h_real_univ]
  -- Each weight is nonneg.
  have h_w_nn : ∀ codebook : Codebook M n α,
      0 ≤ (codebookMeasure p M n).real {codebook} := fun _ => measureReal_nonneg
  -- The contradictory strict inequality.
  have h_contra : B < ∑ codebook : Codebook M n α,
      (codebookMeasure p M n).real {codebook} *
      ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
    calc B = B * 1 := by ring
      _ = B * ∑ codebook : Codebook M n α,
            (codebookMeasure p M n).real {codebook} := by rw [h_sum_one]
      _ = ∑ codebook : Codebook M n α,
            (codebookMeasure p M n).real {codebook} * B := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ < ∑ codebook : Codebook M n α,
            (codebookMeasure p M n).real {codebook} *
            ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
          -- Use `Finset.sum_lt_sum_of_nonempty` style: strict inequality holds for
          -- each codebook with weight > 0, weak inequality for weight = 0.
          -- Actually the codebook space being nonempty + each term contributing
          -- `w · B < w · x` (when w > 0) or `0 = 0` (when w = 0) suffices, but the
          -- sum is strict iff at least one weight is positive — which holds because
          -- `∑ w = 1 ≠ 0`.
          have h_each : ∀ codebook : Codebook M n α,
              (codebookMeasure p M n).real {codebook} * B
                ≤ (codebookMeasure p M n).real {codebook} *
                  ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal := by
            intro codebook
            exact mul_le_mul_of_nonneg_left (h_none codebook).le (h_w_nn codebook)
          -- For the strict inequality, we need at least one codebook with positive weight.
          -- `∑ w = 1 > 0` implies some `w_i > 0`.
          have h_exists_pos : ∃ codebook : Codebook M n α,
              0 < (codebookMeasure p M n).real {codebook} := by
            by_contra h_none_pos
            simp only [not_exists, not_lt] at h_none_pos
            have h_all_zero : ∀ codebook : Codebook M n α,
                (codebookMeasure p M n).real {codebook} = 0 := fun c =>
              le_antisymm (h_none_pos c) (h_w_nn c)
            have : ∑ codebook : Codebook M n α,
                (codebookMeasure p M n).real {codebook} = 0 := by
              refine Finset.sum_eq_zero ?_
              intro c _; exact h_all_zero c
            rw [this] at h_sum_one
            exact one_ne_zero h_sum_one.symm
          obtain ⟨c₀, hc₀_pos⟩ := h_exists_pos
          have h_strict :
              (codebookMeasure p M n).real {c₀} * B
                < (codebookMeasure p M n).real {c₀} *
                  ((codebookToCode μ Xs Ys hM ε c₀).averageErrorProb W).toReal :=
            mul_lt_mul_of_pos_left (h_none c₀) hc₀_pos
          exact Finset.sum_lt_sum (fun i _ => h_each i) ⟨c₀, Finset.mem_univ _, h_strict⟩
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg h_contra)

/-! ### Phase D-(a) — Existence of a low-error codebook for large `n`

The "eventual smallness of random-codebook average" helper is folded into the
main theorem's proof; this section deliberately exposes no extra public lemma.
Subagent fills the proof of `channel_coding_achievability` below by combining
`random_codebook_average_le` (Phase C-(c)), `exists_codebook_le_avg`
(Phase C-(d)), and the rate-slack analysis. -/

/-! ### Phase D-(a) — i.i.d. ambient + entropy-MI bridge (TBD)

The main theorem instantiates `random_codebook_average_le` with the i.i.d. extension
of `(p, W)` on `Ω := ℕ → α × β`, `μ := Measure.infinitePi (jointDistribution p W)`,
`Xs i ω := (ω i).1`, `Ys i ω := (ω i).2`. The bridges to the abstract Phase B / C
formulation are:

* `iIndepFun (Xs/Ys) μ` from `iIndepFun_infinitePi` + composition with `Prod.fst/.snd`.
* `IdentDistrib (Xs i) (Xs 0) μ μ` from `infinitePi_map_eval` (identical marginals).
* `μ.map (Xs 0) = p`, `μ.map (Ys 0) = outputDistribution p W`,
  `μ.map (jointSequence Xs Ys 0) = jointDistribution p W`.
* `hposY` / `hposZ` need a "channel positivity" hypothesis (not currently part of the
  theorem signature). They are discharged by `sorry` until that hypothesis is added.
* The exponent `entropy μ (jointSequence ...) − entropy μ (Xs 0) − entropy μ (Ys 0)
  = −(mutualInfoOfChannel p W).toReal` requires
  `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` (chain rule + commutativity),
  which is not yet exposed in the project and is also discharged by `sorry`. -/

/-! ### Phase D-(b) — Main theorem -/

/-- **Channel coding achievability (Cover-Thomas 7.7.1, achievability half).**
For any rate `R < I(p; W)` and target error probability `ε' > 0`, there exists
`N` such that for all `n ≥ N` there is a block code of length `n` with at least
`exp (n · R)` messages whose average error probability is `< ε'`.

The proof instantiates the abstract Phase C result `random_codebook_average_le`
on the concrete i.i.d. ambient `Ω := ℕ → α × β`,
`μ := iidAmbientMeasure p W`, then runs `exists_codebook_le_avg` to extract a
single codebook from the codebook average bound. The rate slack
`ε := (I - R)/6` ensures both the E1 term (joint AEP) and the E2 term
`(M-1)·exp(-n(I - 3ε))` tend to 0 as `n → ∞`. -/
theorem channel_coding_achievability
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (hp_pos : ∀ a : α, 0 < p.real {a})
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb W).toReal < ε' := by
  classical
  -- Step 1: rate slack. Set `ε := (I - R) / 6` so that `R + 3ε = (R + I)/2 < I`
  -- and `I - R - 3ε = (I - R) / 2 > 0`.
  set I : ℝ := (mutualInfoOfChannel p W).toReal with hI_def
  have hI_pos : 0 < I := lt_trans hR_pos hR
  set ε : ℝ := (I - R) / 6 with hε_def
  have hε_pos : 0 < ε := by
    refine div_pos ?_ (by norm_num)
    linarith
  have hR_3ε_lt_I : R + 3 * ε < I := by
    have : 3 * ε = (I - R) / 2 := by rw [hε_def]; ring
    rw [this]; linarith
  have h_gap_pos : 0 < I - R - 3 * ε := by linarith
  -- Step 2: set up i.i.d. ambient `μ := iidAmbientMeasure p W` on `Ω := ℕ → α × β`.
  set Ω : Type _ := ℕ → α × β
  set μ : Measure Ω := iidAmbientMeasure p W with hμ_def
  haveI : IsProbabilityMeasure μ := by
    rw [hμ_def]; infer_instance
  -- All abstract hypotheses on `(μ, iidXs, iidYs)` come from `IIDProductInput`.
  have hXs : ∀ i, Measurable (iidXs (α := α) (β := β) i) := measurable_iidXs
  have hYs : ∀ i, Measurable (iidYs (α := α) (β := β) i) := measurable_iidYs
  have hindepX_full : iIndepFun (fun i => iidXs (α := α) (β := β) i) μ :=
    iidAmbient_iIndepFun_iidXs p W
  have hindepY_full : iIndepFun (fun i => iidYs (α := α) (β := β) i) μ :=
    iidAmbient_iIndepFun_iidYs p W
  have hindepX_pair : Pairwise fun i j =>
      iidXs (α := α) (β := β) i ⟂ᵢ[μ] iidXs j :=
    iidAmbient_pairwise_indep_iidXs p W
  have hindepY_pair : Pairwise fun i j =>
      iidYs (α := α) (β := β) i ⟂ᵢ[μ] iidYs j :=
    iidAmbient_pairwise_indep_iidYs p W
  have hindepZ : Pairwise fun i j =>
      jointSequence (α := α) (β := β) iidXs iidYs i ⟂ᵢ[μ]
        jointSequence iidXs iidYs j :=
    iidAmbient_pairwise_indep_joint p W
  have hidentX : ∀ i,
      IdentDistrib (iidXs (α := α) (β := β) i) (iidXs 0) μ μ :=
    fun i => iidAmbient_identDistrib_iidXs p W i
  have hidentY : ∀ i,
      IdentDistrib (iidYs (α := α) (β := β) i) (iidYs 0) μ μ :=
    fun i => iidAmbient_identDistrib_iidYs p W i
  have hidentZ : ∀ i,
      IdentDistrib (jointSequence (α := α) (β := β) iidXs iidYs i)
        (jointSequence iidXs iidYs 0) μ μ :=
    fun i => iidAmbient_identDistrib_joint p W i
  have hposX : ∀ x : α, 0 < (μ.map (iidXs (α := α) (β := β) 0)).real {x} :=
    fun x => iidAmbient_iidXs_real_singleton_pos p W hp_pos x
  have hposY : ∀ y : β, 0 < (μ.map (iidYs (α := α) (β := β) 0)).real {y} :=
    fun y => iidAmbient_iidYs_real_singleton_pos p W hp_pos hW_pos y
  have hposZ : ∀ q : α × β,
      0 < (μ.map (jointSequence (α := α) (β := β) iidXs iidYs 0)).real {q} :=
    fun q => iidAmbient_joint_real_singleton_pos p W hp_pos hW_pos q
  have h_match_X : μ.map (iidXs (α := α) (β := β) 0) = p :=
    iidAmbient_map_iidXs p W 0
  -- Step 3: identify the entropy exponent with `-I.toReal`.
  -- entropy μ (jointSequence iidXs iidYs 0) - entropy μ (iidXs 0) - entropy μ (iidYs 0) = -I.
  have h_entZ : InformationTheory.Shannon.entropy μ
      (jointSequence (α := α) (β := β) iidXs iidYs 0)
        = InformationTheory.Shannon.entropy (jointDistribution p W) id := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p W)
      (jointSequence iidXs iidYs 0) id ?_
    refine ⟨(measurable_jointSequence iidXs iidYs measurable_iidXs measurable_iidYs 0).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    rw [iidAmbient_map_jointSequence, Measure.map_id]
  have h_entX : InformationTheory.Shannon.entropy μ (iidXs (α := α) (β := β) 0)
        = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.fst := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p W)
      (iidXs 0) Prod.fst ?_
    refine ⟨(measurable_iidXs 0).aemeasurable, measurable_fst.aemeasurable, ?_⟩
    -- (μ.map (iidXs 0)) = p, and (jointDistribution p W).map Prod.fst = p.
    rw [iidAmbient_map_iidXs]
    show p = (jointDistribution p W).map Prod.fst
    rw [show ((jointDistribution p W).map Prod.fst) = (jointDistribution p W).fst from rfl,
        jointDistribution_def]
    exact (Measure.fst_compProd p W).symm
  have h_entY : InformationTheory.Shannon.entropy μ (iidYs (α := α) (β := β) 0)
        = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.snd := by
    refine InformationTheory.Shannon.entropy_eq_of_identDistrib μ (jointDistribution p W)
      (iidYs 0) Prod.snd ?_
    refine ⟨(measurable_iidYs 0).aemeasurable, measurable_snd.aemeasurable, ?_⟩
    rw [iidAmbient_map_iidYs]
    rfl
  -- Combine: HZ - HX - HY = -I.
  have h_exp_eq : InformationTheory.Shannon.entropy μ
        (jointSequence (α := α) (β := β) iidXs iidYs 0)
      - InformationTheory.Shannon.entropy μ (iidXs 0)
      - InformationTheory.Shannon.entropy μ (iidYs 0) = -I := by
    rw [h_entZ, h_entX, h_entY]
    have hMI := mutualInfoOfChannel_eq_HX_add_HY_sub_HZ p W
    rw [← hI_def] at hMI
    linarith
  -- Step 4: the E1 term tends to 0 as n → ∞.
  have hE1_tendsto : Filter.Tendsto
      (fun n : ℕ => μ.real
        {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
              InformationTheory.Shannon.jointRV iidYs n ω) ∉
            jointlyTypicalSet μ iidXs iidYs n ε})
      Filter.atTop (𝓝 0) := by
    -- (1 - μ {good}) → (1 - 1) = 0; toReal continuous on a finite (≤1) value.
    have h_good : Filter.Tendsto
        (fun n : ℕ => μ
          {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                InformationTheory.Shannon.jointRV iidYs n ω) ∈
              jointlyTypicalSet μ iidXs iidYs n ε})
        Filter.atTop (𝓝 1) :=
      jointlyTypicalSet_prob_tendsto_one μ iidXs iidYs hXs hYs
        hindepX_pair hidentX hindepY_pair hidentY hindepZ hidentZ hε_pos
    have h_meas_good : ∀ n,
        MeasurableSet
          {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                InformationTheory.Shannon.jointRV iidYs n ω) ∈
              jointlyTypicalSet μ iidXs iidYs n ε} := by
      intro n
      have h_meas_pair : Measurable (fun ω =>
          (InformationTheory.Shannon.jointRV (α := α) iidXs n ω,
            InformationTheory.Shannon.jointRV (α := β) iidYs n ω)) :=
        (InformationTheory.Shannon.measurable_jointRV iidXs hXs n).prodMk
          (InformationTheory.Shannon.measurable_jointRV iidYs hYs n)
      exact h_meas_pair (measurableSet_jointlyTypicalSet _ _ _ _ _)
    -- μ.real {compl} = 1 - μ.real {good}, and (1 - μ.real {good}).toReal → 1 - 1 = 0.
    have h_compl_id : ∀ n,
        μ.real {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                  InformationTheory.Shannon.jointRV iidYs n ω) ∉
                jointlyTypicalSet μ iidXs iidYs n ε}
          = 1 - μ.real {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                      InformationTheory.Shannon.jointRV iidYs n ω) ∈
                    jointlyTypicalSet μ iidXs iidYs n ε} := by
      intro n
      have h_compl_eq :
          {ω | (InformationTheory.Shannon.jointRV (α := α) iidXs n ω,
                InformationTheory.Shannon.jointRV (α := β) iidYs n ω) ∉
              jointlyTypicalSet μ iidXs iidYs n ε}
            = {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                  InformationTheory.Shannon.jointRV iidYs n ω) ∈
                jointlyTypicalSet μ iidXs iidYs n ε}ᶜ := rfl
      rw [h_compl_eq, probReal_compl_eq_one_sub (h_meas_good n)]
    have h_good_real : Filter.Tendsto
        (fun n : ℕ => μ.real
          {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
                InformationTheory.Shannon.jointRV iidYs n ω) ∈
              jointlyTypicalSet μ iidXs iidYs n ε})
        Filter.atTop (𝓝 1) := by
      have h_step := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp h_good
      simpa [Measure.real] using h_step
    refine Filter.Tendsto.congr (fun n => (h_compl_id n).symm) ?_
    have h_const : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1) :=
      tendsto_const_nhds
    have := h_const.sub h_good_real
    simpa using this
  -- Step 5: pick N₁ so that E1 < ε'/2.
  have hε'_half : 0 < ε' / 2 := by linarith
  rw [Metric.tendsto_atTop] at hE1_tendsto
  obtain ⟨N₁, hN₁⟩ := hE1_tendsto (ε' / 2) hε'_half
  -- Step 6: the E2 term `(M-1) · exp(n · (-I + 3ε))` tends to 0.
  -- We'll bound it pointwise by `exp(nR + 1 - n(I - 3ε))` = `exp(1 - n(I-R-3ε))`.
  -- Then `Real.tendsto_exp_neg_atTop_nhds_zero` (after rescaling) gives tendsto 0.
  -- More directly: use the fact that exp(1) * exp(-n*g) → 0 where g := I-R-3ε > 0.
  have hE2_tendsto : Filter.Tendsto
      (fun n : ℕ => (((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε))))
      Filter.atTop (𝓝 0) := by
    -- Bound: (ceil(exp(nR)) - 1) ≤ exp(nR) so (ceil - 1) * exp(n*(-I+3ε)) ≤ exp(nR - n(I-3ε)) = exp(-n(I-R-3ε)).
    -- Actually ceil(x) ≤ x + 1 so ceil - 1 ≤ x. For x = exp(nR), `ceil(exp(nR)) - 1 ≤ exp(nR)`.
    have h_ceil_sub_le : ∀ n : ℕ,
        ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) ≤ Real.exp ((n : ℝ) * R) := by
      intro n
      have h_lt : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) <
          Real.exp ((n : ℝ) * R) + 1 :=
        Nat.ceil_lt_add_one (Real.exp_pos _).le
      linarith
    -- Pointwise: 0 ≤ (ceil-1)*exp ≤ exp(nR) * exp(n*(-I+3ε)) = exp(-n*(I-R-3ε)).
    have h_nn_left : ∀ n : ℕ, 0 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1 := by
      intro n
      have h1 : 1 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) := by
        have h1' : 1 ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) :=
          Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne'
        exact_mod_cast h1'
      linarith
    have h_upper : ∀ n : ℕ,
        (((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
          Real.exp ((n : ℝ) * (-I + 3 * ε)))
          ≤ Real.exp (- (n : ℝ) * (I - R - 3 * ε)) := by
      intro n
      have h_mul : ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
            Real.exp ((n : ℝ) * (-I + 3 * ε))
          ≤ Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (-I + 3 * ε)) :=
        mul_le_mul_of_nonneg_right (h_ceil_sub_le n) (Real.exp_pos _).le
      have h_eq : Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * (-I + 3 * ε))
          = Real.exp (- (n : ℝ) * (I - R - 3 * ε)) := by
        rw [← Real.exp_add]
        congr 1; ring
      linarith [h_eq.symm.le, h_mul]
    -- The upper bound `exp(-n * (I-R-3ε))` tends to 0.
    have h_upper_tendsto : Filter.Tendsto
        (fun n : ℕ => Real.exp (- (n : ℝ) * (I - R - 3 * ε)))
        Filter.atTop (𝓝 0) := by
      -- Rewrite as exp(-(n*(I-R-3ε))) and reduce to Real.tendsto_exp_neg_atTop_nhds_zero.
      have h_eq_fun : (fun n : ℕ => Real.exp (- (n : ℝ) * (I - R - 3 * ε)))
          = (fun n : ℕ => Real.exp (- ((n : ℝ) * (I - R - 3 * ε)))) := by
        funext n; ring_nf
      rw [h_eq_fun]
      have h_arg_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) * (I - R - 3 * ε))
          Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.atTop_mul_const h_gap_pos (tendsto_natCast_atTop_atTop)
      have h_exp_neg := Real.tendsto_exp_neg_atTop_nhds_zero
      have h_comp : Filter.Tendsto (fun n : ℕ => Real.exp (- ((n : ℝ) * (I - R - 3 * ε))))
          Filter.atTop (𝓝 0) := h_exp_neg.comp h_arg_tendsto
      exact h_comp
    -- Squeeze: 0 ≤ f n ≤ g n with g → 0 ⇒ f → 0.
    have h_nn : ∀ n : ℕ, 0 ≤ ((Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-I + 3 * ε)) := fun n =>
      mul_nonneg (h_nn_left n) (Real.exp_pos _).le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_upper_tendsto h_nn h_upper
  -- Step 7: pick N₂ so that E2 < ε'/2.
  rw [Metric.tendsto_atTop] at hE2_tendsto
  obtain ⟨N₂, hN₂⟩ := hE2_tendsto (ε' / 2) hε'_half
  -- Step 8: assemble. N := max N₁ N₂ (and ensure n ≥ 1 for `0 < M`).
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn_N₁ : N₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn_N₂ : N₂ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn_one : 1 ≤ n := le_trans (le_max_right _ _) hn
  set M : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R)) with hM_def
  have hM_pos : 0 < M := Nat.ceil_pos.mpr (Real.exp_pos _)
  refine ⟨M, le_refl _, ?_⟩
  -- Apply `random_codebook_average_le` + `exists_codebook_le_avg`.
  have h_avg_bound :=
    random_codebook_average_le (M := M) (n := n) W p hp_pos hM_pos hε_pos μ iidXs iidYs
      hXs hYs hindepX_full hidentX hindepY_full hidentY hindepZ hidentZ
      hposX hposY hposZ h_match_X
  -- The RHS of h_avg_bound is E1 + (M-1)*exp(n*(HZ-HX-HY+3ε)) = E1 + E2 (under h_exp_eq).
  -- Show this RHS is < ε'.
  set E1 : ℝ := μ.real
      {ω | (InformationTheory.Shannon.jointRV iidXs n ω,
            InformationTheory.Shannon.jointRV iidYs n ω) ∉
          jointlyTypicalSet μ iidXs iidYs n ε} with hE1_def
  set E2 : ℝ := ((M : ℝ) - 1) *
      Real.exp ((n : ℝ) *
        ((InformationTheory.Shannon.entropy μ (jointSequence iidXs iidYs 0)
          - InformationTheory.Shannon.entropy μ (iidXs 0)
          - InformationTheory.Shannon.entropy μ (iidYs 0)) + 3 * ε)) with hE2_def
  have h_E2_simp : E2 = ((M : ℝ) - 1) *
      Real.exp ((n : ℝ) * (-I + 3 * ε)) := by
    rw [hE2_def]
    congr 2
    rw [h_exp_eq]
  have hE1_lt : E1 < ε' / 2 := by
    have := hN₁ n hn_N₁
    rw [Real.dist_eq] at this
    have h_abs : |E1 - 0| < ε' / 2 := by simpa [E1] using this
    have h_E1_nn : 0 ≤ E1 := measureReal_nonneg
    rw [sub_zero] at h_abs
    exact (abs_lt.mp h_abs).2
  have hE2_lt : E2 < ε' / 2 := by
    rw [h_E2_simp]
    have := hN₂ n hn_N₂
    rw [Real.dist_eq] at this
    have h_abs : |((M : ℝ) - 1) * Real.exp ((n : ℝ) * (-I + 3 * ε)) - 0| < ε' / 2 := by
      simpa [hM_def] using this
    rw [sub_zero] at h_abs
    exact (abs_lt.mp h_abs).2
  have h_sum_lt : E1 + E2 < ε' := by linarith
  -- Now apply exists_codebook_le_avg with B := E1 + E2.
  obtain ⟨codebook, hcb⟩ :=
    exists_codebook_le_avg μ iidXs iidYs W p hM_pos (B := E1 + E2) h_avg_bound
  refine ⟨codebookToCode μ iidXs iidYs hM_pos ε codebook, ?_⟩
  exact lt_of_le_of_lt hcb h_sum_lt

end InformationTheory.Shannon.ChannelCoding
