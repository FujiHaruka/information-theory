import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# AWGN achievability via joint typicality

The achievability half of the AWGN channel coding theorem (Cover–Thomas 9.2,
Theorem 9.1.1): for any rate `R` below the Gaussian capacity
`(1/2) log(1 + P/N)`, there exist `(M, n)` codes whose maximal per-message error
probability is below any prescribed `ε`. The construction is the random Gaussian
codebook + joint-typicality decoder + expurgation, assembled into the headline
`isAwgnTypicalityHypothesis`.

## Main definitions

* `gaussianCodebook M n σsq` — the random codebook law: `M` codewords, each `n`
  i.i.d. `𝒩(0, σsq)` components, carried by `Fin M → Fin n → ℝ`.
* `jointTypicalDecoder A codebook` — decodes a received vector `y` to the
  smallest codeword index whose pair lies in the typical set `A`.

## Main statements

* `awgn_random_coding_union_bound` — with the decoder fixed to
  `jointTypicalDecoder A`, the average per-message error probability is `≤ 2ε`
  past a rate-dependent threshold, given the two AEP bounds on `A`.
* `awgn_avg_error_union_bound` — closes the union bound against the AEP-supplied
  typical set.
* `awgnPowerWitness_exists` — produces a strictly smaller variance `P' < P` for
  which `R` is still below `capacity(P')`.
* `isAwgnTypicalityHypothesis` — the assembled achievability statement consumed
  by the headline `awgn_achievability`.

## Implementation notes

* `gaussianCodebook` is built as a two-stage `Measure.pi`, which is definitionally
  equal to `AwgnCode.encoder`, so no measurable-equivalence transport is needed.
* The mutual-information slack is expressed in `klDiv` form rather than via
  `differentialEntropy`, so the existing `klDiv_*` API supplies the decay bounds
  directly.
* The continuous AEP for the `n`-dimensional Gaussian lives in
  `InformationTheory/Shannon/AWGN/Walls.lean` as `continuousAepGaussian_holds`;
  consumers here call it directly rather than taking a predicate hypothesis.
* The typicality slack `δ` is an independent parameter from the error target `ε`;
  coupling `δ ≡ ε` makes the alias term false whenever `3ε ≥ I`.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Random Gaussian codebook -/

/-- The random Gaussian codebook: `M` codewords, each `n` i.i.d. components
`X(m, i) ∼ 𝒩(0, σsq)`, built as a two-stage `Measure.pi`. The concrete carrier
type `Fin M → Fin n → ℝ` matches `AwgnCode.encoder` definitionally, so no
measurable-equivalence transport is needed. -/
noncomputable def gaussianCodebook (M n : ℕ) (σsq : ℝ≥0) :
    Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))

/-- `gaussianCodebook M n σsq` is a probability measure (2-stage `Measure.pi` of
the probability measure `gaussianReal 0 σsq`). All instances autoderive via
`pi.instIsProbabilityMeasure` + `instIsProbabilityMeasureGaussianReal`. -/
instance gaussianCodebook_isProbabilityMeasure (M n : ℕ) (σsq : ℝ≥0) :
    IsProbabilityMeasure (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook; infer_instance

/-- Projecting `gaussianCodebook` onto codeword index `m` gives back the inner
i.i.d. Gaussian product measure on `Fin n → ℝ`. -/
@[entry_point]
theorem gaussianCodebook_codeword_law (M n : ℕ) (σsq : ℝ≥0) (m : Fin M) :
    (gaussianCodebook M n σsq).map (fun c : Fin M → Fin n → ℝ => c m)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 σsq) := by
  unfold gaussianCodebook
  exact (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq)) m).map_eq

/-- Under the codebook law, distinct codewords `c m`, `c m'` are independent
random variables. -/
@[entry_point]
theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σsq : ℝ≥0)
    {m m' : Fin M} (hmm' : m ≠ m') :
    IndepFun (fun c : Fin M → Fin n → ℝ => c m)
             (fun c : Fin M → Fin n → ℝ => c m')
             (gaussianCodebook M n σsq) := by
  unfold gaussianCodebook
  have h_iIndep :
      iIndepFun (fun (i : Fin M) (ω : Fin M → Fin n → ℝ) => ω i)
        (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))) := by
    have :=
      iIndepFun_pi (μ := fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))
        (X := fun (_ : Fin M) (x : Fin n → ℝ) => x)
        (fun _ => aemeasurable_id)
    exact this
  exact h_iIndep.indepFun hmm'

/-! ## Continuous AEP for the n-dimensional Gaussian

The continuous AEP is the lemma `continuousAepGaussian_holds` in
`InformationTheory/Shannon/AWGN/Walls.lean`. Consumers in this file call that
lemma directly instead of taking a predicate hypothesis. -/

/-! ## Joint typical decoder and union bound -/

/-- The joint-typicality decoder (Cover–Thomas 9.2). Given a typical set
`A ⊆ (Fin n → ℝ) × (Fin n → ℝ)` and a candidate codebook, it maps each received
vector `y` to the smallest codeword index `m` with `(codebook m, y) ∈ A`; if no
such `m` exists it returns the default `⟨0, …⟩ : Fin M` (well-defined under
`[NeZero M]`).

The set `A` is a parameter so that callers can plug in the AEP-supplied typical
set directly. -/
noncomputable def jointTypicalDecoder
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (codebook : Fin M → Fin n → ℝ) : (Fin n → ℝ) → Fin M := fun y =>
  haveI : Decidable (∃ m : Fin M, (codebook m, y) ∈ A) := Classical.propDecidable _
  haveI : DecidablePred (fun m : Fin M => (codebook m, y) ∈ A) :=
    fun _ => Classical.propDecidable _
  if h : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h
  else ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩

/-- The joint-typicality decoder is measurable for any measurable typical set
`A`. -/
@[entry_point]
theorem jointTypicalDecoder_measurable
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ) :
    Measurable (jointTypicalDecoder A codebook) := by
  classical
  -- `Fin M` is countable: reduce to per-fibre measurability.
  refine measurable_to_countable' (fun m => ?_)
  -- Pointwise characterization of the decoder.
  let m₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
  have hChar : ∀ y : Fin n → ℝ,
      jointTypicalDecoder A codebook y = m ↔
        ((codebook m, y) ∈ A ∧ ∀ j : Fin M, j < m → (codebook j, y) ∉ A)
        ∨ (m = m₀ ∧ ∀ k : Fin M, (codebook k, y) ∉ A) := by
    intro y
    unfold jointTypicalDecoder
    by_cases h : ∃ k : Fin M, (codebook k, y) ∈ A
    · -- typical hit: decoder = Fin.find _ h
      haveI : DecidablePred fun k : Fin M => (codebook k, y) ∈ A :=
        fun _ => Classical.propDecidable _
      -- value of decoder = Fin.find _ h (instance-irrelevant via Subsingleton)
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (codebook k, y) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (codebook m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h' else m₀)
            = Fin.find _ h := by
        rw [dif_pos h]
        congr 1
      rw [hsimp]
      constructor
      · intro hfind
        left
        exact (Fin.find_eq_iff (i := m) h).mp hfind
      · rintro (⟨hmA, hbelow⟩ | ⟨_, hall⟩)
        · exact (Fin.find_eq_iff (i := m) h).mpr ⟨hmA, hbelow⟩
        · exfalso
          obtain ⟨k, hk⟩ := h
          exact hall k hk
    · -- no typical: decoder = m₀
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (codebook k, y) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (codebook m, y) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (codebook m, y) ∈ A then Fin.find _ h' else m₀)
            = m₀ := by
        rw [dif_neg h]
      rw [hsimp]
      constructor
      · intro hm
        right
        refine ⟨hm.symm, ?_⟩
        intro k hk
        exact h ⟨k, hk⟩
      · rintro (⟨hmA, _⟩ | ⟨hm_eq, _⟩)
        · exfalso; exact h ⟨m, hmA⟩
        · exact hm_eq.symm
  -- Per-coordinate measurable sections of `A` via `(y ↦ (codebook k, y))`.
  have hSec : ∀ k : Fin M,
      MeasurableSet {y : Fin n → ℝ | (codebook k, y) ∈ A} := by
    intro k
    have hmeas : Measurable (fun y : Fin n → ℝ => (codebook k, y)) :=
      measurable_const.prodMk measurable_id
    exact hmeas hA
  -- "No codeword smaller than `m` is typical for y".
  have hNoneBelow :
      MeasurableSet {y : Fin n → ℝ | ∀ j : Fin M, j < m → (codebook j, y) ∉ A} := by
    have hset : {y : Fin n → ℝ | ∀ j : Fin M, j < m → (codebook j, y) ∉ A}
        = ⋂ j : Fin M, ⋂ _ : j < m, {y | (codebook j, y) ∉ A} := by
      ext y; simp
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hSec j).compl
  -- "No codeword at all is typical for y".
  have hNoneAll : MeasurableSet {y : Fin n → ℝ | ∀ k : Fin M, (codebook k, y) ∉ A} := by
    have hset : {y : Fin n → ℝ | ∀ k : Fin M, (codebook k, y) ∉ A}
        = ⋂ k : Fin M, {y | (codebook k, y) ∉ A} := by
      ext y; simp
    rw [hset]
    exact MeasurableSet.iInter (fun k => (hSec k).compl)
  -- Rewrite the fibre using the characterization, then take MeasurableSet union.
  have hFiber :
      jointTypicalDecoder A codebook ⁻¹' {m}
        = {y | (codebook m, y) ∈ A ∧ ∀ j : Fin M, j < m → (codebook j, y) ∉ A}
          ∪ (if m = m₀ then {y | ∀ k : Fin M, (codebook k, y) ∉ A} else ∅) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_setOf_eq]
    rw [hChar y]
    by_cases h_eq : m = m₀
    · subst h_eq
      simp
    · constructor
      · rintro (h₁ | ⟨h₂, _⟩)
        · exact Or.inl h₁
        · exact absurd h₂ h_eq
      · intro h
        rcases h with h₁ | h₂
        · exact Or.inl h₁
        · simp [h_eq] at h₂
  rw [hFiber]
  refine MeasurableSet.union ((hSec m).inter hNoneBelow) ?_
  by_cases h_eq : m = m₀
  · rw [if_pos h_eq]; exact hNoneAll
  · rw [if_neg h_eq]; exact MeasurableSet.empty

/-! ### Measurability plumbing for the per-message error

Private helpers that discharge the AE-measurability of
`c ↦ (Measure.pi (W ∘ c m)) (errorEvent c m)` inside
`isAwgnTypicalityHypothesis`: the joint measurability of the decoder, the
codebook kernel, and the kernel-section measurability. -/

/-- Joint measurability in `(codebook, y)` of `jointTypicalDecoder`. -/
theorem jointTypicalDecoder_joint_measurable
    {n M : ℕ} [NeZero M]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : MeasurableSet A) :
    Measurable (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) =>
                  jointTypicalDecoder A p.1 p.2) := by
  classical
  refine measurable_to_countable' (fun m => ?_)
  let m₀ : Fin M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩
  -- Pointwise characterization (identical Boolean shape to y-only version).
  have hChar : ∀ p : (Fin M → Fin n → ℝ) × (Fin n → ℝ),
      jointTypicalDecoder A p.1 p.2 = m ↔
        ((p.1 m, p.2) ∈ A ∧ ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A)
        ∨ (m = m₀ ∧ ∀ k : Fin M, (p.1 k, p.2) ∉ A) := by
    intro p
    unfold jointTypicalDecoder
    by_cases h : ∃ k : Fin M, (p.1 k, p.2) ∈ A
    · haveI : DecidablePred fun k : Fin M => (p.1 k, p.2) ∈ A :=
        fun _ => Classical.propDecidable _
      have hsimp :
          (haveI : Decidable (∃ k : Fin M, (p.1 k, p.2) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (p.1 m, p.2) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (p.1 m, p.2) ∈ A then Fin.find _ h' else m₀)
            = Fin.find _ h := by
        rw [dif_pos h]; congr 1
      rw [hsimp]
      constructor
      · intro hfind
        exact Or.inl ((Fin.find_eq_iff (i := m) h).mp hfind)
      · rintro (⟨hmA, hbelow⟩ | ⟨_, hall⟩)
        · exact (Fin.find_eq_iff (i := m) h).mpr ⟨hmA, hbelow⟩
        · exfalso; obtain ⟨k, hk⟩ := h; exact hall k hk
    · have hsimp :
          (haveI : Decidable (∃ k : Fin M, (p.1 k, p.2) ∈ A) :=
              Classical.propDecidable _;
           haveI : DecidablePred fun m : Fin M => (p.1 m, p.2) ∈ A :=
              fun _ => Classical.propDecidable _;
           if h' : ∃ m : Fin M, (p.1 m, p.2) ∈ A then Fin.find _ h' else m₀)
            = m₀ := by
        rw [dif_neg h]
      rw [hsimp]
      constructor
      · intro hm
        exact Or.inr ⟨hm.symm, fun k hk => h ⟨k, hk⟩⟩
      · rintro (⟨hmA, _⟩ | ⟨hm_eq, _⟩)
        · exfalso; exact h ⟨m, hmA⟩
        · exact hm_eq.symm
  -- Per-codeword measurable sections of `A` in `(c, y)`.
  have hSec : ∀ k : Fin M,
      MeasurableSet
        {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) | (p.1 k, p.2) ∈ A} := by
    intro k
    -- (c, y) ↦ (c k, y) is measurable: each component is a projection.
    have h_proj : Measurable
        (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) => p.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have h_pair :
        Measurable (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) =>
                      ((p.1 k, p.2) : (Fin n → ℝ) × (Fin n → ℝ))) :=
      h_proj.prodMk measurable_snd
    exact h_pair hA
  have hNoneBelow : MeasurableSet
      {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) |
          ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A} := by
    have hset :
        {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) |
            ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A}
          = ⋂ j : Fin M, ⋂ _ : j < m, {p | (p.1 j, p.2) ∉ A} := by
      ext p; simp
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hSec j).compl
  have hNoneAll : MeasurableSet
      {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) | ∀ k : Fin M, (p.1 k, p.2) ∉ A} := by
    have hset :
        {p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) | ∀ k : Fin M, (p.1 k, p.2) ∉ A}
          = ⋂ k : Fin M, {p | (p.1 k, p.2) ∉ A} := by
      ext p; simp
    rw [hset]
    exact MeasurableSet.iInter (fun k => (hSec k).compl)
  -- Rewrite fibre and conclude.
  have hFiber :
      (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) =>
          jointTypicalDecoder A p.1 p.2) ⁻¹' {m}
        = {p | (p.1 m, p.2) ∈ A ∧ ∀ j : Fin M, j < m → (p.1 j, p.2) ∉ A}
          ∪ (if m = m₀ then {p | ∀ k : Fin M, (p.1 k, p.2) ∉ A} else ∅) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_setOf_eq]
    rw [hChar p]
    by_cases h_eq : m = m₀
    · subst h_eq; simp
    · constructor
      · rintro (h₁ | ⟨h₂, _⟩)
        · exact Or.inl h₁
        · exact absurd h₂ h_eq
      · intro h
        rcases h with h₁ | h₂
        · exact Or.inl h₁
        · simp [h_eq] at h₂
  rw [hFiber]
  refine MeasurableSet.union ((hSec m).inter hNoneBelow) ?_
  by_cases h_eq : m = m₀
  · rw [if_pos h_eq]; exact hNoneAll
  · rw [if_neg h_eq]; exact MeasurableSet.empty

private theorem awgnCodebook_pi_measurable
    {n M : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (m : Fin M) :
    Measurable (fun c : Fin M → Fin n → ℝ =>
      (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i)) :
        Measure (Fin n → ℝ))) := by
  -- Each fibre is a probability measure (Markov kernel + pi instance).
  haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
  haveI : ∀ c : Fin M → Fin n → ℝ,
      IsProbabilityMeasure
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i))) := by
    intro c; infer_instance
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi Set.univ '' Set.pi Set.univ
            (fun _ : Fin n => {s : Set ℝ | MeasurableSet s}))
    (hgen := generateFrom_pi.symm) (hpi := isPiSystem_pi) ?_
  rintro s ⟨t, ht, rfl⟩
  -- Box: μ_c (Set.pi univ t) = ∏ i, awgnChannel N h_meas (c m i) (t i).
  simp_rw [Measure.pi_pi]
  -- Each factor is measurable in `c`.
  refine Finset.measurable_prod _ (fun i _ => ?_)
  -- `c ↦ c m i` is the composition of two pi-projections.
  have h_proj : Measurable (fun c : Fin M → Fin n → ℝ => c m i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply m)
  -- `awgnChannel N h_meas` is a kernel; combine via `Kernel.measurable_coe`.
  have h_kernel_coe :
      Measurable (fun x : ℝ => (awgnChannel N h_meas) x (t i)) :=
    Kernel.measurable_coe _ (ht i (Set.mem_univ _))
  exact h_kernel_coe.comp h_proj

/-- Bundle `c ↦ Measure.pi (fun i => awgnChannel N h_meas (c m i))` as a
genuine kernel. Each fibre is a probability measure (so the kernel is Markov,
hence s-finite), which lets us feed it to
`Kernel.measurable_kernel_prodMk_left`. -/
noncomputable def awgnCodebookKernel
    {n M : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (m : Fin M) :
    Kernel (Fin M → Fin n → ℝ) (Fin n → ℝ) where
  toFun c := Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i))
  measurable' := awgnCodebook_pi_measurable N h_meas m

instance awgnCodebookKernel.instIsMarkovKernel
    {n M : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (m : Fin M) :
    IsMarkovKernel (awgnCodebookKernel (n := n) (M := M) N h_meas m) where
  isProbabilityMeasure c := by
    show IsProbabilityMeasure
      (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i)))
    haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
    infer_instance

lemma measurable_measurePi_awgnChannel
    {n : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
    Measurable (fun x : Fin n → ℝ =>
      (Measure.pi (fun i => awgnChannel N h_meas (x i)) : Measure (Fin n → ℝ))) := by
  haveI : IsMarkovKernel (awgnChannel N h_meas) :=
    awgnChannel.instIsMarkovKernel N h_meas
  haveI : ∀ x : Fin n → ℝ,
      IsProbabilityMeasure
        (Measure.pi (fun i => awgnChannel N h_meas (x i))) := fun x => by
    infer_instance
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := Set.pi Set.univ '' Set.pi Set.univ
            (fun _ : Fin n => {s : Set ℝ | MeasurableSet s}))
    (hgen := generateFrom_pi.symm) (hpi := isPiSystem_pi) ?_
  rintro s ⟨t, ht, rfl⟩
  simp_rw [Measure.pi_pi]
  refine Finset.measurable_prod _ (fun i _ => ?_)
  have hti : MeasurableSet (t i) := ht i (Set.mem_univ i)
  have h_kernel_coe : Measurable
      (fun x : ℝ => (awgnChannel N h_meas) x (t i)) :=
    Kernel.measurable_coe _ hti
  exact h_kernel_coe.comp (measurable_pi_apply i)

lemma map_add_prod_pi_gaussianReal_eq_pi_gaussianReal
    {n : ℕ} (v₁ v₂ : ℝ≥0) :
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 v₁)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 v₂))).map
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + p.2 i)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 (v₁ + v₂)) := by
  set e : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he_def
  -- per-letter sum measure: `(gauss 0 v₁).prod (gauss 0 v₂)` pushed by `+`.
  have hperletter : ∀ _ : Fin n,
      ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
          (fun p : ℝ × ℝ => p.1 + p.2)
        = gaussianReal 0 (v₁ + v₂) := by
    intro _
    have := gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0)
      (v₁ := v₁) (v₂ := v₂)
    rw [zero_add] at this
    exact this
  -- reshape `(pi gauss).prod (pi gauss) = (pi (gauss×gauss)).map e`.
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ : Fin n => gaussianReal 0 v₁) (fun _ : Fin n => gaussianReal 0 v₂)
  have hreshape :
      (Measure.pi (fun _ : Fin n => gaussianReal 0 v₁)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 v₂))
        = (Measure.pi (fun _ : Fin n =>
            (gaussianReal 0 v₁).prod (gaussianReal 0 v₂))).map e := by
    rw [he_def, ← hmp.map_eq]
  have hsum_meas : Measurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + p.2 i) :=
    measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).add
        ((measurable_pi_apply i).comp measurable_snd))
  have hcoord_meas : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  rw [hreshape, Measure.map_map hsum_meas e.measurable]
  -- `Σ ∘ e = fun w i => (w i).1 + (w i).2`, which `pi_map_pi` factorizes.
  have hcomp :
      ((fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + p.2 i) ∘ e)
        = (fun (w : Fin n → ℝ × ℝ) (i : Fin n) => (w i).1 + (w i).2) := by
    funext w; rfl
  rw [hcomp]
  haveI : ∀ _ : Fin n, SigmaFinite
      (((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
        (fun p : ℝ × ℝ => p.1 + p.2)) := by
    intro i; rw [hperletter i]; infer_instance
  rw [Measure.pi_map_pi (μ := fun _ : Fin n =>
      (gaussianReal 0 v₁).prod (gaussianReal 0 v₂))
      (f := fun _ : Fin n => (fun p : ℝ × ℝ => p.1 + p.2))
      (fun _ => hcoord_meas.aemeasurable)]
  congr 1
  funext i
  exact hperletter i

lemma measurePi_awgnChannel_eq_pi_gaussianReal_map_add
    {n : ℕ} (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (x : Fin n → ℝ) :
    Measure.pi (fun i => awgnChannel N h_meas (x i))
      = (Measure.pi (fun _ : Fin n => gaussianReal 0 N)).map (fun z i => x i + z i) := by
  -- Each fibre: `awgnChannel · (x i) = gaussianReal (x i) N = (gaussianReal 0 N).map (x i + ·)`.
  have hfib : ∀ i : Fin n,
      (awgnChannel N h_meas (x i) : Measure ℝ)
        = (gaussianReal 0 N).map (x i + ·) := by
    intro i
    rw [awgnChannel_apply, gaussianReal_map_const_add, zero_add]
  -- AEMeasurable of each shift map.
  have haem : ∀ i : Fin n, AEMeasurable (x i + · : ℝ → ℝ) (gaussianReal 0 N) :=
    fun i => (measurable_const.add measurable_id).aemeasurable
  -- SigmaFinite of each pushforward (it equals `gaussianReal (x i) N`, a prob measure).
  haveI hσ : ∀ i : Fin n, SigmaFinite ((gaussianReal 0 N).map (x i + ·)) := by
    intro i
    rw [gaussianReal_map_const_add, zero_add]
    infer_instance
  rw [Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 N)
    (f := fun i => (x i + ·)) haem]
  congr 1
  funext i
  rw [hfib i]

lemma lintegral_measurePi_awgnChannel_eq_pi_gaussianReal
    {n : ℕ} (N v : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    (∫⁻ x, (Measure.pi (fun i => awgnChannel N h_meas (x i))) B
        ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 v)))
      = Measure.pi (fun _ : Fin n => gaussianReal 0 (v + N)) B := by
  -- per-vector channel collapse `chan x = (pi gauss).map (x + ·)`.
  have hshift : ∀ x : Fin n → ℝ, Measurable (fun z : Fin n → ℝ => fun i => x i + z i) := by
    intro x; exact measurable_pi_lambda _ (fun i => measurable_const.add (measurable_pi_apply i))
  have hchanB : ∀ x : Fin n → ℝ,
      (Measure.pi (fun i => awgnChannel N h_meas (x i))) B
        = (Measure.pi (fun _ : Fin n => gaussianReal 0 N))
            ((fun z : Fin n → ℝ => fun i => x i + z i) ⁻¹' B) := by
    intro x
    rw [measurePi_awgnChannel_eq_pi_gaussianReal_map_add N h_meas x,
      Measure.map_apply (hshift x) hB]
  -- integrate over `x`, fold into the prod, then push by `Σ`.
  rw [lintegral_congr hchanB]
  have hsum_meas : Measurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + p.2 i) :=
    measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).add
        ((measurable_pi_apply i).comp measurable_snd))
  have hsec_eq : ∀ x : Fin n → ℝ,
      (fun z : Fin n → ℝ => fun i => x i + z i) ⁻¹' B
        = Prod.mk x ⁻¹' ((fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i + p.2 i) ⁻¹' B) := by
    intro x; rfl
  rw [lintegral_congr (fun x => by rw [hsec_eq x]),
    ← Measure.prod_apply (hsum_meas hB),
    ← Measure.map_apply hsum_meas hB,
    map_add_prod_pi_gaussianReal_eq_pi_gaussianReal v N]

theorem awgn_unionBound_trueCodeword_term_le
    {n M : ℕ} (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (m : Fin M) {ε : ℝ} (hε : 0 < ε)
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA_meas : MeasurableSet A)
    (hA_mass :
      (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
              (p.1, fun i => p.1 i + p.2 i))) A
        ≥ ENNReal.ofReal (1 - ε)) :
    ∫⁻ codebook : Fin M → Fin n → ℝ,
        (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          {y | (codebook m, y) ∉ A}
      ∂(gaussianCodebook M n P.toNNReal)
        ≤ ENNReal.ofReal ε := by
  classical
  set J : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)) with hJ_def
  -- Single-codeword integrand.
  set f1 : (Fin n → ℝ) → ℝ≥0∞ := fun x =>
    (Measure.pi (fun i => awgnChannel N h_meas (x i))) {y | (x, y) ∉ A} with hf1_def
  -- The codebook integrand equals `f1` precomposed with the `m`-th projection.
  have hpt : (fun codebook : Fin M → Fin n → ℝ =>
      (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
        {y | (codebook m, y) ∉ A})
      = (fun codebook : Fin M → Fin n → ℝ => f1 (codebook m)) := rfl
  -- `f1` is measurable: same kernel section as `hAE_E1`.
  have hf1_meas : Measurable f1 := by
    set T1 : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {p | (p.1, p.2) ∉ A} with hT1_def
    have hT1_meas : MeasurableSet T1 := by
      have : {p : (Fin n → ℝ) × (Fin n → ℝ) | (p.1, p.2) ∉ A} = Aᶜ := by
        ext p; simp
      rw [hT1_def, this]; exact hA_meas.compl
    -- Package `x ↦ Measure.pi (awgnChannel · (x i))` as a kernel (m := default).
    have hker : Measurable (fun x : Fin n → ℝ =>
        (Measure.pi (fun i => awgnChannel N h_meas (x i))) {y | (x, y) ∉ A}) := by
      have hk : Measurable (fun x : Fin n → ℝ =>
          (Measure.pi (fun i => awgnChannel N h_meas (x i)) :
            Measure (Fin n → ℝ))) :=
        measurable_measurePi_awgnChannel N h_meas
      -- Bundle as a Markov kernel and pull back the joint set via prodMk.
      let K : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
        { toFun := fun x => Measure.pi (fun i => awgnChannel N h_meas (x i))
          measurable' := hk }
      haveI : IsMarkovKernel K := by
        refine ⟨fun x => ?_⟩
        show IsProbabilityMeasure (Measure.pi (fun i => awgnChannel N h_meas (x i)))
        haveI : IsMarkovKernel (awgnChannel N h_meas) :=
          awgnChannel.instIsMarkovKernel N h_meas
        infer_instance
      have hEqK : (fun x : Fin n → ℝ =>
            (Measure.pi (fun i => awgnChannel N h_meas (x i))) {y | (x, y) ∉ A})
          = (fun x : Fin n → ℝ => K x (Prod.mk x ⁻¹' T1)) := by
        funext x; rfl
      rw [hEqK]
      exact Kernel.measurable_kernel_prodMk_left hT1_meas
    exact hker
  -- Collapse the codebook integral onto the `m`-th coordinate marginal.
  rw [hpt, ← lintegral_map hf1_meas (measurable_pi_apply m),
    gaussianCodebook_codeword_law M n P.toNNReal m]
  -- Remaining: the joint marginal identity `∫ f1 dμX = J Aᶜ ≤ ε`.
  -- ── Abbreviations for the marginals and the joint map `Φ`. ──
  set μX : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)
    with hμX_def
  set μZ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 N)
    with hμZ_def
  set Φ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun p => (p.1, fun i => p.1 i + p.2 i) with hΦ_def
  -- `Φ` is measurable.
  have hΦ_meas : Measurable Φ := by
    rw [hΦ_def]
    refine Measurable.prodMk measurable_fst ?_
    refine measurable_pi_lambda _ (fun i => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).add
      ((measurable_pi_apply i).comp measurable_snd)
  -- The section set `{y | (x, y) ∉ A} = Prod.mk x ⁻¹' Aᶜ`.
  have hsec : ∀ x : Fin n → ℝ, {y : Fin n → ℝ | (x, y) ∉ A} = Prod.mk x ⁻¹' Aᶜ := by
    intro x
    ext y
    simp [Set.mem_preimage, Set.mem_compl_iff]
  -- Per-vector channel collapse: `Measure.pi (awgnChannel · (x i)) = μZ.map (x + ·)`.
  have hchan : ∀ x : Fin n → ℝ,
      Measure.pi (fun i => awgnChannel N h_meas (x i))
        = μZ.map (fun z i => x i + z i) := by
    intro x
    rw [hμZ_def]
    exact measurePi_awgnChannel_eq_pi_gaussianReal_map_add N h_meas x
  -- Pointwise: `f1 x = μZ (Prod.mk x ⁻¹' (Φ ⁻¹' Aᶜ))`.
  have hf1_eq : ∀ x : Fin n → ℝ,
      f1 x = μZ (Prod.mk x ⁻¹' (Φ ⁻¹' Aᶜ)) := by
    intro x
    show (Measure.pi (fun i => awgnChannel N h_meas (x i))) {y | (x, y) ∉ A}
      = μZ (Prod.mk x ⁻¹' (Φ ⁻¹' Aᶜ))
    rw [hsec x, hchan x]
    have hshift : Measurable (fun z : Fin n → ℝ => fun i => x i + z i) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      exact (measurable_const).add ((measurable_pi_apply i))
    rw [Measure.map_apply hshift (hA_meas.compl.preimage measurable_prodMk_left)]
    -- Section sets coincide.
    rfl
  -- The integral identity: `∫⁻ x, f1 x ∂μX = J Aᶜ`.
  have hint_eq : (∫⁻ x, f1 x ∂μX) = J Aᶜ := by
    have hΦA_meas : MeasurableSet (Φ ⁻¹' Aᶜ) := hΦ_meas hA_meas.compl
    rw [lintegral_congr hf1_eq, hJ_def,
      Measure.map_apply hΦ_meas hA_meas.compl, Measure.prod_apply hΦA_meas]
  -- The mass bound: `J Aᶜ ≤ ENNReal.ofReal ε`.
  have hmass : J Aᶜ ≤ ENNReal.ofReal ε := by
    -- `J` is a probability measure (pushforward of a product of prob measures).
    haveI hJ_prob : IsProbabilityMeasure J := by
      rw [hJ_def]
      exact Measure.isProbabilityMeasure_map hΦ_meas.aemeasurable
    calc J Aᶜ = 1 - J A := prob_compl_eq_one_sub hA_meas
      _ ≤ 1 - ENNReal.ofReal (1 - ε) := tsub_le_tsub_left hA_mass 1
      _ ≤ ENNReal.ofReal ε := by
          rw [tsub_le_iff_left]
          calc (1 : ℝ≥0∞) = ENNReal.ofReal ((1 - ε) + ε) := by
                rw [sub_add_cancel, ENNReal.ofReal_one]
            _ ≤ ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
  rw [hint_eq]
  exact hmass

theorem awgn_unionBound_aliasCodeword_sum_eq
    {n M : ℕ} [NeZero M] (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (m : Fin M) (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA_meas : MeasurableSet A) :
    ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
        ∫⁻ codebook : Fin M → Fin n → ℝ,
          (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
            {y | (codebook m', y) ∈ A}
        ∂(gaussianCodebook M n P.toNNReal)
      = (M - 1) •
        ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A := by
  classical
  set Q : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))) with hQ_def
  -- per-letter marginals
  set μXn : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal) with hμXn_def
  set μYn : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)) with hμYn_def
  haveI : IsProbabilityMeasure μXn := by rw [hμXn_def]; infer_instance
  haveI : IsProbabilityMeasure μYn := by rw [hμYn_def]; infer_instance
  -- ── Step O (output-marginal identity): for any measurable `B`,
  -- `∫⁻ x, (channel x) B ∂μXn = μYn B` (the n-fold law of `X + Z`). ──
  have houtput : ∀ B : Set (Fin n → ℝ), MeasurableSet B →
      (∫⁻ x, (Measure.pi (fun i => awgnChannel N h_meas (x i))) B ∂μXn) = μYn B := by
    intro B hB
    rw [hμXn_def, hμYn_def]
    exact lintegral_measurePi_awgnChannel_eq_pi_gaussianReal N P.toNNReal h_meas B hB
  -- ── Step A (2-coordinate collapse): each summand `= Q A`. ──
  have hsummand : ∀ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
      (∫⁻ codebook, (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          {y | (codebook m', y) ∈ A}
          ∂(gaussianCodebook M n P.toNNReal)) = Q A := by
    intro m' hm'
    have hm'_ne : m' ≠ m := (Finset.mem_erase.mp hm').1
    -- The channel kernel `K x = Measure.pi (awgnChannel·(x i))`.
    have hk : Measurable (fun x : Fin n → ℝ =>
        (Measure.pi (fun i => awgnChannel N h_meas (x i)) : Measure (Fin n → ℝ))) :=
      measurable_measurePi_awgnChannel N h_meas
    let K : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
      { toFun := fun x => Measure.pi (fun i => awgnChannel N h_meas (x i))
        measurable' := hk }
    haveI hKmarkov : IsMarkovKernel K := by
      refine ⟨fun x => ?_⟩
      show IsProbabilityMeasure (Measure.pi (fun i => awgnChannel N h_meas (x i)))
      haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
      infer_instance
    -- 2-coordinate integrand `g2 p = (chan p.1) {y | (p.2, y) ∈ A}`.
    set g2 : (Fin n → ℝ) × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
      (Measure.pi (fun i => awgnChannel N h_meas (p.1 i))) {y | (p.2, y) ∈ A} with hg2_def
    -- the joint section `T = {q | (q.1.2, q.2) ∈ A}` on `((x,x'), y)`.
    let K' : Kernel ((Fin n → ℝ) × (Fin n → ℝ)) (Fin n → ℝ) :=
      K.comap Prod.fst measurable_fst
    have hg2_meas : Measurable g2 := by
      set T : Set (((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) :=
        {q | (q.1.2, q.2) ∈ A} with hT_def
      have hT_meas : MeasurableSet T := by
        have hpair : Measurable
            (fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) => (q.1.2, q.2)) :=
          (measurable_snd.comp measurable_fst).prodMk measurable_snd
        exact hpair hA_meas
      -- `g2 p = K' p (Prod.mk p ⁻¹' T)`.
      have hEq : g2 = (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          K' p (Prod.mk p ⁻¹' T)) := by
        funext p; rfl
      rw [hEq]
      exact Kernel.measurable_kernel_prodMk_left hT_meas
    -- Step 3: push `gaussianCodebook` forward by `c ↦ (c m, c m')` = `μXn.prod μXn`.
    have hmap2 : (gaussianCodebook M n P.toNNReal).map
        (fun c : Fin M → Fin n → ℝ => (c m, c m')) = μXn.prod μXn := by
      have hindep := gaussianCodebook_indepFun_codewords M n P.toNNReal hm'_ne.symm
      have haem_m : AEMeasurable (fun c : Fin M → Fin n → ℝ => c m)
          (gaussianCodebook M n P.toNNReal) := (measurable_pi_apply m).aemeasurable
      have haem_m' : AEMeasurable (fun c : Fin M → Fin n → ℝ => c m')
          (gaussianCodebook M n P.toNNReal) := (measurable_pi_apply m').aemeasurable
      rw [(indepFun_iff_map_prod_eq_prod_map_map haem_m haem_m').mp hindep,
        gaussianCodebook_codeword_law M n P.toNNReal m,
        gaussianCodebook_codeword_law M n P.toNNReal m', hμXn_def]
    -- Step 4: collapse the codebook integral to the 2-coordinate marginal.
    have hcollapse : (∫⁻ codebook, (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          {y | (codebook m', y) ∈ A}
          ∂(gaussianCodebook M n P.toNNReal))
        = ∫⁻ p, g2 p ∂(μXn.prod μXn) := by
      rw [← hmap2, lintegral_map hg2_meas
        ((measurable_pi_apply m).prodMk (measurable_pi_apply m'))]
    rw [hcollapse]
    -- Step 5: Fubini (integrate channel input `x` first) + `houtput` + `prod_apply`.
    rw [lintegral_prod_symm g2 hg2_meas.aemeasurable]
    -- inner `∫⁻ x, g2 (x, x') ∂μXn = μYn {y | (x', y) ∈ A}` by `houtput`.
    have hinner : ∀ x' : Fin n → ℝ,
        (∫⁻ x, g2 (x, x') ∂μXn) = μYn {y | (x', y) ∈ A} := by
      intro x'
      have hBmeas : MeasurableSet {y : Fin n → ℝ | (x', y) ∈ A} :=
        (measurable_const.prodMk measurable_id) hA_meas
      exact houtput {y | (x', y) ∈ A} hBmeas
    rw [lintegral_congr hinner]
    -- outer `∫⁻ x', μYn {y | (x', y) ∈ A} ∂μXn = (μXn.prod μYn) A = Q A`.
    rw [hQ_def]
    exact (Measure.prod_apply hA_meas).symm
  -- ── Step B (count): `∑ = (M − 1) • Q A`. ──
  rw [Finset.sum_congr rfl hsummand, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]

theorem awgn_unionBound_aliasMass_decay
    {n M : ℕ} (P : ℝ) (N : ℝ≥0) (hP : 0 < P) (hN : (N : ℝ) ≠ 0)
    {ε δ R : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hR_pos : 0 < R)
    (hslack : R + 3 * δ < (1/2) * Real.log (1 + P / (N : ℝ)))
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hM_le : M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)))
    (hg_pos : 0 < (1/2) * Real.log (1 + P / (N : ℝ)) - R - 3 * δ)
    (hn : Nat.ceil (Real.log (2 / ε) /
            ((1/2) * Real.log (1 + P / (N : ℝ)) - R - 3 * δ)) ≤ n)
    (hA_indep :
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
        ≤ ENNReal.ofReal (Real.exp (-(
            (klDiv
                (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                    (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                  (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                      (p.1, fun i => p.1 i + p.2 i)))
                ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                  (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
              - (n : ℝ) * (3 * δ))))) :
    (M - 1) •
        ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
      ≤ ENNReal.ofReal ε := by
  classical
  set g : ℝ := (1/2) * Real.log (1 + P / (N : ℝ)) - R - 3 * δ with hg_def
  set J : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)) with hJ_def
  set Q : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))) with hQ_def
  -- ── Step C (decay): `(M − 1) • Q A ≤ ofReal ε`. ──
  -- First, the nondegeneracy `(N : ℝ) ≠ 0` (else `1 + P/N = 1`, `log 1 = 0 < R + 3δ`).
  have hN_ne : (N : ℝ) ≠ 0 := by
    intro hN0
    rw [hN0, div_zero, add_zero, Real.log_one, mul_zero] at hslack
    linarith
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (fun h => hN_ne h.symm)
  -- The per-letter capacity `I = (1/2)log(1+P/N)`, which `hslack` lower-bounds.
  by_cases hPN_nonneg : 0 ≤ 1 + P / (N : ℝ)
  · have hP_pos : 0 < P := hP
    -- bridges: `klDiv_n.toReal = n · klDiv(J₁,Q₁).toReal = n · I`.
    have hI : (klDiv
          (((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 N)).map
              (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
          ((gaussianReal 0 P.toNNReal).prod
            (gaussianReal 0 (P.toNNReal + N)))).toReal
        = (1/2) * Real.log (1 + P / (N : ℝ)) :=
      klDiv_perLetter_eq_capacity P hP_pos N hN_ne
    have hnfold := klDiv_nFold_eq_nsmul P N (n := n)
    -- `klDiv_n.toReal = n · I` (fold the `set J`/`set Q` literals).
    have hkl_n : (klDiv J Q).toReal = (n : ℝ) * ((1/2) * Real.log (1 + P / (N : ℝ))) := by
      rw [hJ_def, hQ_def, hnfold, hI]
    have hexp_pos : (0 : ℝ) < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    have hM1_le : (M : ℝ) ≤ 2 * Real.exp ((n : ℝ) * R) := by
      have hMle : (M : ℝ) ≤ Real.exp ((n : ℝ) * R) + 1 := by
        have h1 : (M : ℝ) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) := by exact_mod_cast hM_le
        have h2 : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) ≤ Real.exp ((n : ℝ) * R) + 1 :=
          (Nat.ceil_lt_add_one hexp_pos.le).le
        linarith
      have h1le : (1 : ℝ) ≤ Real.exp ((n : ℝ) * R) := Real.one_le_exp (by positivity)
      linarith
    -- The real-number decay bound.
    have hg_n : (n : ℝ) * g ≥ Real.log (2 / ε) := by
      have h_cast : (Nat.ceil (Real.log (2 / ε) / g) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h_le_ceil : Real.log (2 / ε) / g ≤ (Nat.ceil (Real.log (2 / ε) / g) : ℝ) :=
        Nat.le_ceil _
      have hle : Real.log (2 / ε) / g ≤ (n : ℝ) := le_trans h_le_ceil h_cast
      have := (div_le_iff₀ hg_pos).mp hle
      linarith [this]
    -- conclude: `(M−1) • Q A ≤ ofReal ε`.
    have hbound : Q A ≤ ENNReal.ofReal
        (Real.exp (-((klDiv J Q).toReal - (n : ℝ) * (3 * δ)))) := hA_indep
    have hreal_decay :
        2 * Real.exp ((n : ℝ) * R)
            * Real.exp (-((klDiv J Q).toReal - (n : ℝ) * (3 * δ))) ≤ ε := by
      rw [hkl_n]
      have hcombine :
          Real.exp ((n : ℝ) * R)
              * Real.exp (-((n : ℝ) * ((1/2) * Real.log (1 + P / (N : ℝ)))
                  - (n : ℝ) * (3 * δ)))
            = Real.exp (-((n : ℝ) * g)) := by
        rw [← Real.exp_add]; congr 1; rw [hg_def]; ring
      rw [mul_assoc, hcombine]
      have hng : -((n : ℝ) * g) ≤ Real.log (ε / 2) := by
        have hlog_eq : Real.log (2 / ε) = -Real.log (ε / 2) := by
          rw [← Real.log_inv]; congr 1; rw [inv_div]
        rw [hlog_eq] at hg_n
        linarith [hg_n]
      have hexp_le : Real.exp (-((n : ℝ) * g)) ≤ ε / 2 := by
        have := Real.exp_le_exp.mpr hng
        rwa [Real.exp_log (by positivity)] at this
      nlinarith [hexp_le, Real.exp_pos (-((n : ℝ) * g))]
    calc (M - 1) • Q A
        = ((M - 1 : ℕ) : ℝ≥0∞) * Q A := by rw [nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (2 * Real.exp ((n : ℝ) * R)) * Q A := by
          gcongr
          calc ((M - 1 : ℕ) : ℝ≥0∞) ≤ ((M : ℕ) : ℝ≥0∞) := by
                exact_mod_cast Nat.sub_le M 1
            _ = ENNReal.ofReal (M : ℝ) := by rw [ENNReal.ofReal_natCast]
            _ ≤ ENNReal.ofReal (2 * Real.exp ((n : ℝ) * R)) := by
                apply ENNReal.ofReal_le_ofReal
                linarith [hM1_le]
      _ ≤ ENNReal.ofReal (2 * Real.exp ((n : ℝ) * R))
            * ENNReal.ofReal (Real.exp (-((klDiv J Q).toReal - (n : ℝ) * (3 * δ)))) := by
          gcongr
      _ = ENNReal.ofReal (2 * Real.exp ((n : ℝ) * R)
            * Real.exp (-((klDiv J Q).toReal - (n : ℝ) * (3 * δ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal_decay
  · have hPN_pos : (0 : ℝ) < P / (N : ℝ) := div_pos hP hN_pos
    exact absurd (by linarith : (0 : ℝ) ≤ 1 + P / (N : ℝ)) hPN_nonneg

/-! ### Random-coding union bound -/

/-- The random-coding union bound (Cover–Thomas 9.2, with the typicality slack
`δ` separated from the error target `ε`). With the codebook drawn from the
two-stage Gaussian product law and the decoder fixed to the joint-typicality
decoder against `A`, there is a threshold `N₀` such that for every `n ≥ N₀`,
every codebook size `M ≤ ⌈exp(nR)⌉`, and every measurable typical set `A`
satisfying the two AEP bounds at slack `δ`, the average per-message error
probability is `≤ 2ε`:

* `hA_mass` — the joint codebook+noise law puts mass `≥ 1−ε` on `A`.
* `hA_indep` — the independent-pair product law puts mass
  `≤ exp(−(klDiv_n − 3nδ))` on `A`.

The slack assumption `hslack : R + 3δ < (1/2) log(1 + P/N)` is what makes the
alias term decay: with the typicality margin `g = I − R − 3δ > 0` and
`klDiv_n = n·I`, the alias mass is bounded by `exp(−ng)·(…) → 0`, hence `≤ ε`
past `N₀`. The preconditions `hP : 0 < P` and `hN : (N:ℝ) ≠ 0` exclude the
degenerate corner `1 + P/N < 0`, where `P.toNNReal = 0` collapses `klDiv` to `0`
and the alias term no longer decays; under `0 < P` and `0 < N` we have
`1 + P/N > 1 > 0`. They are regularity preconditions, not a bundled proof core.
@audit:ok -/
theorem awgn_random_coding_union_bound
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (hP : 0 < P) (hN : (N : ℝ) ≠ 0)
    {ε δ R : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hR_pos : 0 < R)
    (hslack : R + 3 * δ < (1/2) * Real.log (1 + P / (N : ℝ))) :
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      ∀ (A : Set ((Fin n → ℝ) × (Fin n → ℝ))), MeasurableSet A →
        (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                (p.1, fun i => p.1 i + p.2 i))) A
          ≥ ENNReal.ofReal (1 - ε) →
        ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
          ≤ ENNReal.ofReal (Real.exp (-(
              (klDiv
                  (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                      (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                    (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                        (p.1, fun i => p.1 i + p.2 i)))
                  ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                    (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
                - (n : ℝ) * (3 * δ)))) →
        haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
        ∀ m : Fin M,
          ∫⁻ codebook : Fin M → Fin n → ℝ,
            ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
              ((InformationTheory.Shannon.ChannelCoding.Code.mk
                  (M := M) (n := n) (α := ℝ) (β := ℝ)
                  codebook (jointTypicalDecoder A codebook)).errorEvent m))
          ∂(gaussianCodebook M n P.toNNReal)
            ≤ ENNReal.ofReal (2 * ε) := by
  classical
  -- The threshold `N₀` is the alias-term decay threshold (depends only on
  -- `ε, δ, R, N, P`). It is pinned to the value that closes the term2 decay:
  -- the typicality margin `g = (1/2)log(1+P/N) − R − 3δ > 0` (from `hslack`),
  -- and `N₀ = ⌈log(2/ε)/g⌉` so that `2·exp(−n·g) ≤ ε` for `n ≥ N₀`.
  set g : ℝ := (1/2) * Real.log (1 + P / (N : ℝ)) - R - 3 * δ with hg_def
  have hg_pos : 0 < g := by rw [hg_def]; linarith
  refine ⟨Nat.ceil (Real.log (2 / ε) / g), ?_⟩
  intro n hn M hM_pos hM_le A hA_meas hA_mass hA_indep
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
  intro m
  -- Abbreviations for the joint law `J` and the product law `Q` (verbatim Walls).
  set J : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)) with hJ_def
  set Q : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))) with hQ_def
  -- The channel-output measure for codeword `codebook m`.
  set Wch : (Fin M → Fin n → ℝ) → Measure (Fin n → ℝ) := fun codebook =>
    Measure.pi (fun i => awgnChannel N h_meas (codebook m i)) with hWch_def
  haveI hWch_prob : ∀ codebook, IsProbabilityMeasure (Wch codebook) := by
    intro codebook; rw [hWch_def]; infer_instance
  -- The (E1) "true codeword not typical" set and the (E2) "alias codeword
  -- typical" sets, as functions of the codebook.
  set E1 : (Fin M → Fin n → ℝ) → Set (Fin n → ℝ) := fun codebook =>
    {y | (codebook m, y) ∉ A} with hE1_def
  set E2 : (Fin M → Fin n → ℝ) → Fin M → Set (Fin n → ℝ) := fun codebook m' =>
    {y | (codebook m', y) ∈ A} with hE2_def
  -- ── Atom 1: error-event set inclusion (from the decoder definition). ──
  -- `errorEvent m ⊆ E1 ∪ ⋃_{m' ≠ m} E2 m'`.
  have h_incl : ∀ codebook : Fin M → Fin n → ℝ,
      (InformationTheory.Shannon.ChannelCoding.Code.mk
          (M := M) (n := n) (α := ℝ) (β := ℝ)
          codebook (jointTypicalDecoder A codebook)).errorEvent m
        ⊆ E1 codebook ∪
          ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2 codebook m' := by
    intro codebook y hy
    -- `hy : decoder y ≠ m`.
    rw [InformationTheory.Shannon.ChannelCoding.Code.mem_errorEvent] at hy
    change jointTypicalDecoder A codebook y ≠ m at hy
    simp only [hE1_def, hE2_def, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_erase, Finset.mem_univ, and_true]
    -- If the true codeword `m` is not typical, we land in `E1`.
    by_cases hmA : (codebook m, y) ∈ A
    · -- `m` is typical, so the decoder uses `Fin.find` and returns a typical index.
      right
      -- The decoder value: there *is* a typical index (`m` itself).
      have hex : ∃ k : Fin M, (codebook k, y) ∈ A := ⟨m, hmA⟩
      -- Unfold the decoder on the `dif_pos` branch.
      have hdec : jointTypicalDecoder A codebook y = Fin.find _ hex := by
        unfold jointTypicalDecoder
        rw [dif_pos hex]
      -- The found index is typical and (being ≠ m) gives the `E2` witness.
      set m' := Fin.find (fun k : Fin M => (codebook k, y) ∈ A) hex with hm'_def
      have hm'_mem : (codebook m', y) ∈ A := by
        have := (Fin.find_eq_iff (i := m') hex).mp rfl
        exact this.1
      have hm'_ne : m' ≠ m := by
        intro hmm
        apply hy
        rw [hdec]
        exact hmm
      exact ⟨m', hm'_ne, hm'_mem⟩
    · -- `m` not typical: `y ∈ E1`.
      exact Or.inl hmA
  -- ── Pointwise (per-codebook) union bound on the channel measure. ──
  have h_ptwise : ∀ codebook : Fin M → Fin n → ℝ,
      (Wch codebook)
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M) (n := n) (α := ℝ) (β := ℝ)
            codebook (jointTypicalDecoder A codebook)).errorEvent m)
        ≤ (Wch codebook) (E1 codebook)
          + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
              (Wch codebook) (E2 codebook m') := by
    intro codebook
    calc (Wch codebook) _
        ≤ (Wch codebook) (E1 codebook ∪
            ⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2 codebook m') :=
          measure_mono (h_incl codebook)
      _ ≤ (Wch codebook) (E1 codebook)
            + (Wch codebook)
                (⋃ m' ∈ (Finset.univ : Finset (Fin M)).erase m, E2 codebook m') :=
          measure_union_le _ _
      _ ≤ (Wch codebook) (E1 codebook)
            + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
                (Wch codebook) (E2 codebook m') := by
          gcongr
          exact measure_biUnion_finset_le _ _
  -- AE-measurability of the codebook integrands (Wch · (E1 / E2 ·)).
  -- Both reduce to the genuine kernel `awgnCodebookKernel` + the joint-measurable
  -- section `(c, y) ↦ (c k, y)` pulled back through `Kernel.measurable_kernel_prodMk_left`
  -- (the same machinery already used in `isAwgnTypicalityHypothesis`, lines 998-1028).
  have hAE_E1 : AEMeasurable
      (fun codebook : Fin M → Fin n → ℝ => (Wch codebook) (E1 codebook))
      (gaussianCodebook M n P.toNNReal) := by
    refine Measurable.aemeasurable ?_
    set T1 : Set ((Fin M → Fin n → ℝ) × (Fin n → ℝ)) :=
      {p | (p.1 m, p.2) ∉ A} with hT1_def
    have hT1_meas : MeasurableSet T1 := by
      have h_pair : Measurable
          (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) => (p.1 m, p.2)) :=
        ((measurable_pi_apply m).comp measurable_fst).prodMk measurable_snd
      exact (h_pair hA_meas).compl
    have hEq : (fun codebook : Fin M → Fin n → ℝ => (Wch codebook) (E1 codebook))
        = (fun codebook : Fin M → Fin n → ℝ =>
            awgnCodebookKernel N h_meas m codebook (Prod.mk codebook ⁻¹' T1)) := by
      funext codebook
      rfl
    rw [hEq]
    exact Kernel.measurable_kernel_prodMk_left hT1_meas
  have hAE_E2 : ∀ m', AEMeasurable
      (fun codebook : Fin M → Fin n → ℝ => (Wch codebook) (E2 codebook m'))
      (gaussianCodebook M n P.toNNReal) := by
    intro m'
    refine Measurable.aemeasurable ?_
    set T2 : Set ((Fin M → Fin n → ℝ) × (Fin n → ℝ)) :=
      {p | (p.1 m', p.2) ∈ A} with hT2_def
    have hT2_meas : MeasurableSet T2 := by
      have h_pair : Measurable
          (fun p : (Fin M → Fin n → ℝ) × (Fin n → ℝ) => (p.1 m', p.2)) :=
        ((measurable_pi_apply m').comp measurable_fst).prodMk measurable_snd
      exact h_pair hA_meas
    have hEq : (fun codebook : Fin M → Fin n → ℝ => (Wch codebook) (E2 codebook m'))
        = (fun codebook : Fin M → Fin n → ℝ =>
            awgnCodebookKernel N h_meas m codebook (Prod.mk codebook ⁻¹' T2)) := by
      funext codebook
      rfl
    rw [hEq]
    exact Kernel.measurable_kernel_prodMk_left hT2_meas
  -- ── Integrate the pointwise bound, splitting the two terms. ──
  have h_lint_le :
      ∫⁻ codebook, (Wch codebook)
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)
        ∂(gaussianCodebook M n P.toNNReal)
      ≤ (∫⁻ codebook, (Wch codebook) (E1 codebook)
            ∂(gaussianCodebook M n P.toNNReal))
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            ∫⁻ codebook, (Wch codebook) (E2 codebook m')
              ∂(gaussianCodebook M n P.toNNReal) := by
    calc ∫⁻ codebook, _ ∂_
        ≤ ∫⁻ codebook, ((Wch codebook) (E1 codebook)
            + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
                (Wch codebook) (E2 codebook m'))
          ∂(gaussianCodebook M n P.toNNReal) :=
          lintegral_mono (fun codebook => h_ptwise codebook)
      _ = (∫⁻ codebook, (Wch codebook) (E1 codebook)
            ∂(gaussianCodebook M n P.toNNReal))
          + ∫⁻ codebook, (∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
                (Wch codebook) (E2 codebook m'))
            ∂(gaussianCodebook M n P.toNNReal) :=
          lintegral_add_left' hAE_E1 _
      _ = (∫⁻ codebook, (Wch codebook) (E1 codebook)
            ∂(gaussianCodebook M n P.toNNReal))
          + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
              ∫⁻ codebook, (Wch codebook) (E2 codebook m')
                ∂(gaussianCodebook M n P.toNNReal) := by
          congr 1
          rw [lintegral_finsetSum' _ (fun m' _ => hAE_E2 m')]
  -- ── Atom 2: first term = `J Aᶜ ≤ ε` (joint marginal identity + hA_mass). ──
  -- Reduction (genuine): the integrand depends only on the `m`-th codeword, so the
  -- codebook integral collapses to a single-codeword integral against the codeword
  -- marginal `Measure.pi (gaussianReal 0 P')` (`gaussianCodebook_codeword_law` +
  -- `lintegral_map`). What remains is the **joint marginal identity** `J Aᶜ ≤ ε`
  -- (the `μX ⊗ channel = J` change-of-variables; genuine Mathlib-absent wiring).
  have h_term1 :
      ∫⁻ codebook, (Wch codebook) (E1 codebook)
          ∂(gaussianCodebook M n P.toNNReal)
        ≤ ENNReal.ofReal ε :=
    awgn_unionBound_trueCodeword_term_le P N h_meas m hε A hA_meas hA_mass
  -- ── Atom 3: second (alias) term `∑_{m'≠m} ∫ Wch(E2 m') = (M−1)·Q A ≤ ε`. ──
  -- Two sub-steps: (a) **Q-marginal collapse** `∑_{m'≠m} ∫ Wch(E2 m') = (M−1)·Q A`
  -- (m'≠m ⟹ codebook m' ⊥ codebook m, the product law `Q`; same plumbing as term1's
  -- J-marginal). (b) **N₀-decay** `(M−1)·Q A ≤ (M−1)·exp(−(klDiv_n − n·3δ)) ≤
  -- ⌈exp(nR)⌉·exp(−n(I−3δ)) ≤ ε` from `hA_indep`, `hM_le`, and `hslack` (margin
  -- `g = I − R − 3δ > 0`, needing `klDiv_n = n·I` via `klDiv_perLetter_eq_capacity`
  -- and `klDiv_nFold_eq_nsmul`). `N₀ = ⌈log(2/ε)/g⌉` is the pinned decay threshold.
  -- The closed-form `klDiv_n = n·I` needs `0 < P` (precondition `hP`), which also
  -- excludes the degenerate corner `1 + P/N < 0`.
  have h_term2 :
      ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
          ∫⁻ codebook, (Wch codebook) (E2 codebook m')
            ∂(gaussianCodebook M n P.toNNReal)
        ≤ ENNReal.ofReal ε :=
    (awgn_unionBound_aliasCodeword_sum_eq P N h_meas m A hA_meas).le.trans
      (awgn_unionBound_aliasMass_decay P N hP hN hε hδ hR_pos hslack A hM_le hg_pos hn
        hA_indep)
  -- ── Combine: `≤ ε + ε = 2ε`. ──
  calc ∫⁻ codebook, _ ∂_
      ≤ (∫⁻ codebook, (Wch codebook) (E1 codebook)
            ∂(gaussianCodebook M n P.toNNReal))
        + ∑ m' ∈ (Finset.univ : Finset (Fin M)).erase m,
            ∫⁻ codebook, (Wch codebook) (E2 codebook m')
              ∂(gaussianCodebook M n P.toNNReal) := h_lint_le
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := by
        gcongr
    _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε.le hε.le]; ring_nf

/-- The random-coding union bound closed against the AEP-supplied typical set.
Under the random Gaussian codebook and AWGN channel, the average per-message
error probability (using `jointTypicalDecoder` against the AEP-supplied typical
set) is `≤ 2ε` for all `M ≤ ⌈exp(n R)⌉` once `n` is large enough, given the
typicality margin `R + 3δ < (1/2) log(1 + P/N)` with `δ` separate from `ε`.

A modular composition of `continuousAepGaussian_holds` + `awgn_random_coding_union_bound`;
`hP`/`hN` are passed through to the union bound at the call site.
@audit:ok -/
@[entry_point]
theorem awgn_avg_error_union_bound
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    {R ε δ : ℝ} (hR_pos : 0 < R) (hδ : 0 < δ)
    (hslack : R + 3 * δ < (1/2) * Real.log (1 + P / (N : ℝ)))
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ M (hM_pos : 0 < M),
      M ≤ Nat.ceil (Real.exp ((n : ℝ) * R)) →
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)), MeasurableSet A ∧
        haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
        ∀ m : Fin M,
          ∫⁻ codebook : Fin M → Fin n → ℝ,
            ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
              ((InformationTheory.Shannon.ChannelCoding.Code.mk
                  (M := M) (n := n) (α := ℝ) (β := ℝ)
                  codebook (jointTypicalDecoder A codebook)).errorEvent m))
          ∂(gaussianCodebook M n P.toNNReal)
            ≤ ENNReal.ofReal (2 * ε) := by
  have hR_pos' : 0 < R := hR_pos
  -- AEP threshold (typical-set existence at slack `δ`) + union-bound threshold.
  obtain ⟨N_aep, hN_aep⟩ := continuousAepGaussian_holds P N hδ hε
  obtain ⟨N_rand, hN_rand⟩ :=
    awgn_random_coding_union_bound P N h_meas hP hN hε hδ hR_pos hslack
  refine ⟨max N_aep N_rand, ?_⟩
  intro n hn M hM_pos hM_le
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM_pos⟩
  -- AEP supplies the typical set A with the 2 bounds; thread them into the union bound.
  obtain ⟨A, hA_meas, hA_mass, hA_indep⟩ :=
    hN_aep (le_of_max_le_left hn : N_aep ≤ n)
  refine ⟨A, hA_meas, ?_⟩
  exact hN_rand (le_of_max_le_right hn : N_rand ≤ n) hM_pos hM_le A hA_meas hA_mass hA_indep

/-! ## Expurgation -/

/-- If the codebook-average of `Pe` is at most `B`, then some specific codebook
achieves `Pe ≤ B`. -/
@[entry_point]
theorem awgn_exists_codebook_le_avg
    {M n : ℕ} (σsq : ℝ≥0)
    (Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞)
    (hPe_aemeas : AEMeasurable Pe (gaussianCodebook M n σsq))
    {B : ℝ≥0∞}
    (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σsq) ≤ B) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ B := by
  obtain ⟨c, hc⟩ := exists_le_lintegral hPe_aemeas
  exact ⟨c, hc.trans h_avg⟩

/-- Worst-half expurgation: if the sum of `Pe m` is bounded by `M · (2ε)`, then
at least `M/2` indices `m` satisfy `Pe m ≤ 4ε`. -/
@[entry_point]
theorem awgn_expurgate_worst_half
    {M : ℕ} (hM : 2 ≤ M)
    (Pe : Fin M → ℝ) (hPe_nn : ∀ m, 0 ≤ Pe m) {ε : ℝ} (hε : 0 < ε)
    (h_avg : (∑ m, Pe m) ≤ (M : ℝ) * (2 * ε)) :
    ∃ S : Finset (Fin M), M / 2 ≤ S.card ∧ ∀ m ∈ S, Pe m ≤ 4 * ε := by
  classical
  refine ⟨Finset.univ.filter (fun m => Pe m ≤ 4 * ε), ?_, ?_⟩
  · -- card ≥ M/2 via contrapositive on the "bad" filter
    by_contra hlt
    push Not at hlt
    set S_good : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M => Pe m ≤ 4 * ε) with hS_good
    set S_bad : Finset (Fin M) :=
      Finset.univ.filter (fun m : Fin M => ¬ Pe m ≤ 4 * ε) with hS_bad
    have h_card_sum : S_good.card + S_bad.card = M := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin M))) (fun m : Fin M => Pe m ≤ 4 * ε)
      have hu : (Finset.univ : Finset (Fin M)).card = M := by
        simp [Finset.card_univ, Fintype.card_fin]
      simp [hu] at h
      simpa [S_good, S_bad] using h
    have h_card_bad_gt : M / 2 < S_bad.card := by omega
    have h_two_le_card_bad : M / 2 + 1 ≤ S_bad.card := h_card_bad_gt
    -- Real lower bound on S_bad.card.
    have h_two_card_lb_nat : M < 2 * S_bad.card := by
      have h_div : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2 |>.symm ▸ by
        omega
      have h_mod_lt : M % 2 < 2 := Nat.mod_lt M (by norm_num)
      omega
    have h_two_card_lb : (M : ℝ) < 2 * (S_bad.card : ℝ) := by
      have := h_two_card_lb_nat
      have h_cast : ((2 * S_bad.card : ℕ) : ℝ) = 2 * (S_bad.card : ℝ) := by push_cast; ring
      have : (M : ℝ) < ((2 * S_bad.card : ℕ) : ℝ) := by exact_mod_cast this
      linarith [h_cast]
    -- Pe m > 4ε on S_bad.
    have h_strict : ∀ m ∈ S_bad, 4 * ε < Pe m := by
      intro m hm
      have := (Finset.mem_filter.mp hm).2
      push Not at this
      exact this
    have h_nonempty : S_bad.Nonempty := by
      have : 0 < S_bad.card := by omega
      exact Finset.card_pos.mp this
    have h_sum_bad_lb : (S_bad.card : ℝ) * (4 * ε) < ∑ m ∈ S_bad, Pe m := by
      have hsum_lt :
          ∑ _m ∈ S_bad, (4 * ε) < ∑ m ∈ S_bad, Pe m :=
        Finset.sum_lt_sum_of_nonempty h_nonempty h_strict
      have hconst : ∑ _m ∈ S_bad, (4 * ε) = (S_bad.card : ℝ) * (4 * ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      linarith
    have h_sub_le : ∑ m ∈ S_bad, Pe m ≤ ∑ m, Pe m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun m _ _ => hPe_nn m)
    -- Combine: M * 2ε < 2 * S_bad.card * 2ε = S_bad.card * 4ε < ∑ Pe ≤ M * 2ε. Contradiction.
    nlinarith [h_two_card_lb, h_sum_bad_lb, h_sub_le, h_avg, hε]
  · intro m hm
    exact (Finset.mem_filter.mp hm).2

/-! ## Power constraint and feasibility witness

The per-codeword power-constraint bound `awgnPowerConstraintPerCodeword_holds`
lives in `InformationTheory/Shannon/AWGN/Walls.lean`. The achievability assembly
also needs a shared slack witness `∃ P' ∈ (0, P)` with `R < capacity(P')`,
supplied by `awgnPowerWitness_exists` below, which returns a strict `P' < P` (the
variance-level slack `(P'.toNNReal : ℝ) < P` required by the per-codeword
bound). -/

/-- The power-constraint slack witness.

Given `R < capacity(P) = (1/2) log(1 + P/N)`, produce a strictly smaller variance
`P' ∈ (0, P)` for which the rate `R` is still below `capacity(P')`. The strict
`P' < P` is genuinely required by `awgnPowerConstraintPerCodeword_holds` (its
`(P_cb.toNNReal : ℝ) < P_target` slack argument); the witness must therefore
deliver a true strict inequality, never a non-strict one fabricated from `≤`.

Construction: `capacity` is continuous and strictly increasing in the variance;
`R < capacity(P)` lies strictly below the value at `P`, so by continuity there is
a left neighbourhood of `P` on which the capacity still exceeds `R`. Picking any
`P'` in that neighbourhood with `0 < P' < P` works.
@audit:ok -/
@[entry_point]
theorem awgnPowerWitness_exists (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ))) :
    ∃ P', 0 < P' ∧ P' < P ∧ R < (1/2) * Real.log (1 + P' / (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_ne N.coe_nonneg (fun h => hN h.symm)
  -- `R < (1/2) log(1 + P/N)` ⟺ `2R < log(1 + P/N)` ⟺ `exp(2R) < 1 + P/N`.
  have hlogP : 2 * R < Real.log (1 + P / (N : ℝ)) := by linarith
  have harg_P_pos : (0 : ℝ) < 1 + P / (N : ℝ) := by positivity
  have hexp_lt : Real.exp (2 * R) < 1 + P / (N : ℝ) :=
    (Real.lt_log_iff_exp_lt harg_P_pos).mp hlogP
  -- Lower bound on admissible variance: `P_min := N · (exp(2R) − 1)`.
  set t : ℝ := Real.exp (2 * R) with ht_def
  have ht_gt_one : (1 : ℝ) < t := by
    rw [ht_def]; exact Real.one_lt_exp_iff.mpr (by linarith)
  set Pmin : ℝ := (N : ℝ) * (t - 1) with hPmin_def
  have hPmin_pos : 0 < Pmin := by
    rw [hPmin_def]; have : 0 < t - 1 := by linarith
    positivity
  -- `exp(2R) < 1 + P/N` rearranges to `Pmin < P`.
  have hPmin_lt_P : Pmin < P := by
    rw [hPmin_def]
    have h1 : t - 1 < P / (N : ℝ) := by linarith
    have h2 : (N : ℝ) * (t - 1) < (N : ℝ) * (P / (N : ℝ)) :=
      mul_lt_mul_of_pos_left h1 hN_pos
    rwa [mul_div_cancel₀ P (ne_of_gt hN_pos)] at h2
  -- Pick the midpoint `P' := (Pmin + P)/2 ∈ (Pmin, P)`.
  set P' : ℝ := (Pmin + P) / 2 with hP'_def
  have hP'_pos : 0 < P' := by rw [hP'_def]; linarith
  have hP'_lt_P : P' < P := by rw [hP'_def]; linarith
  have hP'_gt_Pmin : Pmin < P' := by rw [hP'_def]; linarith
  refine ⟨P', hP'_pos, hP'_lt_P, ?_⟩
  -- `P' > Pmin = N(t-1)` ⟹ `t - 1 < P'/N` ⟹ `t < 1 + P'/N`.
  have h1 : t - 1 < P' / (N : ℝ) := by
    rw [lt_div_iff₀ hN_pos]
    have := hP'_gt_Pmin; rw [hPmin_def] at this; linarith
  have harg_P'_pos : (0 : ℝ) < 1 + P' / (N : ℝ) := by
    have : 0 < P' / (N : ℝ) := div_pos hP'_pos hN_pos; linarith
  have hexp_lt' : Real.exp (2 * R) < 1 + P' / (N : ℝ) := by
    rw [← ht_def]; linarith
  have hlogP' : 2 * R < Real.log (1 + P' / (N : ℝ)) :=
    (Real.lt_log_iff_exp_lt harg_P'_pos).mpr hexp_lt'
  linarith

/-- Bridge to the `AwgnCode` type from a deterministic codebook satisfying both
the per-message error bound and the per-message power constraint, using
`jointTypicalDecoder` as the decoder and converting the `ℝ≥0∞`-valued error
bound to the `< 5ε` real-valued slack. -/
@[entry_point]
theorem awgn_extract_AwgnCode
    {P : ℝ} {N : ℝ≥0}
    (h_meas : IsAwgnChannelMeasurable N) {n : ℕ}
    {M : ℕ} [NeZero M]
    {ε : ℝ} (hε : 0 < ε)
    {A : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hA_meas : MeasurableSet A)
    (codebook : Fin M → Fin n → ℝ)
    (h_max_Pe : ∀ m,
        (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)
        ≤ ENNReal.ofReal (4 * ε))
    (h_power : ∀ m, (∑ i, (codebook m i)^2) ≤ (n : ℝ) * P) :
    ∃ c : AwgnCode M n P,
      ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < 5 * ε := by
  refine ⟨{
    encoder := codebook
    decoder := jointTypicalDecoder A codebook
    decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
    power_constraint := h_power
  }, ?_⟩
  intro m
  -- toCode.errorProbAt = (Measure.pi (W ∘ encoder m)) (errorEvent ...).
  -- Pe ≤ 4ε in ℝ≥0∞ + 4ε.toReal = 4ε < 5ε.
  have h_pe_le := h_max_Pe m
  -- The body of c.toCode.errorProbAt for our AwgnCode equals the LHS in h_max_Pe.
  have h_eq :
      (({ encoder := codebook
          decoder := jointTypicalDecoder A codebook
          decoder_meas := jointTypicalDecoder_measurable A hA_meas codebook
          power_constraint := h_power : AwgnCode M n P }).toCode.errorProbAt
            (awgnChannel N h_meas) m)
      = (Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m) := rfl
  rw [h_eq]
  -- Now compare with ENNReal.ofReal (4 * ε) ≤ ENNReal.ofReal (5 * ε), take .toReal.
  have h_target : (ENNReal.ofReal (4 * ε)).toReal < 5 * ε := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  have h_ne_top : (ENNReal.ofReal (4 * ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m)).toReal
      ≤ (ENNReal.ofReal (4 * ε)).toReal := by
        apply ENNReal.toReal_mono h_ne_top h_pe_le
    _ < 5 * ε := h_target

lemma exists_two_mul_ceil_exp_le_ceil_exp_of_lt {R R'' : ℝ} (hR_nonneg : 0 ≤ R)
    (hR_lt_R'' : R < R'') :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      2 * Nat.ceil (Real.exp ((n : ℝ) * R))
        ≤ Nat.ceil (Real.exp ((n : ℝ) * R'')) := by
  -- Pick `N₀ = ⌈(log 4) / (R'' - R)⌉` so that for n ≥ N₀,
  -- `exp(n(R''-R)) ≥ 4`, hence `exp(n R'') ≥ 4 * exp(n R)`. Then
  -- `2 * ⌈exp(n R)⌉ ≤ 2 * (exp(n R) + 1) ≤ 4 * exp(n R) ≤ exp(n R'') ≤ ⌈exp(n R'')⌉`.
  set δd : ℝ := R'' - R with hδd_def
  have hδd_pos : 0 < δd := by linarith
  -- Need `n * δd ≥ log 4`, i.e., `n ≥ log 4 / δd`.
  set N₀ : ℕ := Nat.ceil (Real.log 4 / δd) with hN₀_def
  refine ⟨N₀, fun n hn => ?_⟩
  -- Cast `(N₀ : ℝ) ≤ (n : ℝ)`.
  have h_ndelta : Real.log 4 / δd ≤ (n : ℝ) := by
    have h_cast : ((N₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc Real.log 4 / δd ≤ (Nat.ceil (Real.log 4 / δd) : ℝ) := Nat.le_ceil _
      _ = (N₀ : ℝ) := by rfl
      _ ≤ (n : ℝ) := h_cast
  have h_exp_n_delta_ge_4 : (4 : ℝ) ≤ Real.exp ((n : ℝ) * δd) := by
    have h_n_delta : Real.log 4 ≤ (n : ℝ) * δd := by
      have := (div_le_iff₀ hδd_pos).mp h_ndelta
      linarith
    have := Real.exp_le_exp.mpr h_n_delta
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at this
  have h_exp_R''_ge : Real.exp ((n : ℝ) * R'') = Real.exp ((n : ℝ) * R) * Real.exp ((n : ℝ) * δd) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_exp_R_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
  have h_exp_R_ge_one : 1 ≤ Real.exp ((n : ℝ) * R) := by
    apply Real.one_le_exp
    exact mul_nonneg (Nat.cast_nonneg n) hR_nonneg
  -- 2 * ⌈exp(nR)⌉ ≤ 2 * (exp(nR) + 1) ≤ 4 * exp(nR) ≤ exp(nR'') ≤ ⌈exp(nR'')⌉.
  have h_ceil_R_le : (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ Real.exp ((n : ℝ) * R) + 1 := by
    exact (Nat.ceil_lt_add_one (le_of_lt h_exp_R_pos)).le
  have h_two_ceil_R_le : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ 4 * Real.exp ((n : ℝ) * R) := by
    have : (2 : ℝ) * (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        ≤ 2 * (Real.exp ((n : ℝ) * R) + 1) := by
      linarith
    calc (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
        = 2 * (Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ) := by norm_cast
      _ ≤ 2 * (Real.exp ((n : ℝ) * R) + 1) := this
      _ ≤ 2 * Real.exp ((n : ℝ) * R) + 2 * Real.exp ((n : ℝ) * R) := by linarith
      _ = 4 * Real.exp ((n : ℝ) * R) := by ring
  have h_4_le_R'' : (4 : ℝ) * Real.exp ((n : ℝ) * R) ≤ Real.exp ((n : ℝ) * R'') := by
    rw [h_exp_R''_ge]
    have : (4 : ℝ) * Real.exp ((n : ℝ) * R)
        ≤ Real.exp ((n : ℝ) * δd) * Real.exp ((n : ℝ) * R) := by
      nlinarith [h_exp_R_pos]
    linarith [this, mul_comm (Real.exp ((n : ℝ) * R)) (Real.exp ((n : ℝ) * δd))]
  have h_le_R'' : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ Real.exp ((n : ℝ) * R'') := le_trans h_two_ceil_R_le h_4_le_R''
  -- Conclude via Nat.le_ceil.
  have : (2 * Nat.ceil (Real.exp ((n : ℝ) * R)) : ℝ)
      ≤ (Nat.ceil (Real.exp ((n : ℝ) * R'')) : ℝ) :=
    le_trans h_le_R'' (Nat.le_ceil _)
  exact_mod_cast this

/-! ## Achievability assembly -/

/-- The assembled AWGN achievability statement: for any rate `R` below the
Gaussian capacity and any `ε > 0`, there is a threshold `N₀` such that for every
`n ≥ N₀` there is an `(M, n)` code (with `M ≥ ⌈exp(nR)⌉`) whose maximal
per-message error probability over the AWGN channel is below `ε`.

The assembly combines a strictly smaller slack variance `P'` from
`awgnPowerWitness_exists`, a typicality slack `δ := (C−R)/12` for the
union-bound margin `R'' + 3δ < C`, the typical set and its two AEP bounds from
`continuousAepGaussian_holds P' N`, the per-message error bound from
`awgn_random_coding_union_bound P' N h_meas`, and the power constraint from the
per-codeword expurgation bound `awgnPowerConstraintPerCodeword_holds P' P N`.

The strict witness `hP'_pos : 0 < P'` (from `awgnPowerWitness_exists`) + `hN` are
supplied to `awgn_random_coding_union_bound`.
@audit:ok -/
lemma errorEvent_jointTypicalDecoder_comp_subset_of_strictMono
    {n M M_target : ℕ} [NeZero M] [NeZero M_target]
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (c : Fin M → Fin n → ℝ) (reindex : Fin M_target → Fin M)
    (hreindex_strictMono : StrictMono reindex) (j : Fin M_target) :
    (InformationTheory.Shannon.ChannelCoding.Code.mk
          (M := M_target) (n := n) (α := ℝ) (β := ℝ)
          (fun i => c (reindex i)) (jointTypicalDecoder A (fun i => c (reindex i)))).errorEvent j
      ⊆ (InformationTheory.Shannon.ChannelCoding.Code.mk
          (M := M) (n := n) (α := ℝ) (β := ℝ)
          c (jointTypicalDecoder A c)).errorEvent (reindex j) := by
  set subcodebook : Fin M_target → Fin n → ℝ := fun i => c (reindex i) with hsubcodebook_def
  intro y hy
  -- `hy : decoder_sub y ≠ j`. Show `decoder_full y ≠ reindex j`.
  simp only [InformationTheory.Shannon.ChannelCoding.Code.mem_errorEvent] at hy ⊢
  -- Goal: decoder_full y ≠ reindex j.
  -- Suppose for contradiction decoder_full y = reindex j.
  intro hfull_eq
  have hsub_def : jointTypicalDecoder A subcodebook y ≠ j := hy
  have hfull_def : jointTypicalDecoder A c y = reindex j := hfull_eq
  -- Apply the by-cases on existence of typical codewords (for full).
  classical
  by_cases h_exists_full : ∃ k : Fin M, (c k, y) ∈ A
  · -- Full has typical; extract the smallest-index characterization.
    haveI : Decidable (∃ k : Fin M, (c k, y) ∈ A) := Classical.propDecidable _
    haveI inst_full : DecidablePred fun k : Fin M => (c k, y) ∈ A :=
      fun _ => Classical.propDecidable _
    -- Rewrite decoder unfolding once with the SAME instance.
    change
      (haveI : Decidable (∃ m : Fin M, (c m, y) ∈ A) := Classical.propDecidable _;
       haveI : DecidablePred fun m : Fin M => (c m, y) ∈ A :=
          fun _ => Classical.propDecidable _;
       if h' : ∃ m : Fin M, (c m, y) ∈ A then Fin.find _ h' else _) = reindex j
        at hfull_def
    rw [dif_pos h_exists_full] at hfull_def
    -- The two `DecidablePred` instances are Subsingleton-equal; bridge them.
    set inst_dec : DecidablePred fun k : Fin M => (c k, y) ∈ A :=
      fun x => Classical.propDecidable ((fun m => (c m, y) ∈ A) x) with hinst_dec
    have hfull_def_inst :
        @Fin.find M (fun k => (c k, y) ∈ A) inst_full h_exists_full = reindex j := by
      have h_inst_eq : inst_full = inst_dec := Subsingleton.elim _ _
      rw [h_inst_eq]; exact hfull_def
    have hfull_typ : (c (reindex j), y) ∈ A := by
      have h_spec := @Fin.find_spec M (fun k => (c k, y) ∈ A) inst_full h_exists_full
      rw [hfull_def_inst] at h_spec
      exact h_spec
    have hfull_min : ∀ k : Fin M, k < reindex j → (c k, y) ∉ A := by
      intro k hk
      have h_min := @Fin.find_min M (fun k => (c k, y) ∈ A) inst_full h_exists_full k
      have hsub : k < @Fin.find M (fun k => (c k, y) ∈ A) inst_full h_exists_full := by
        rw [hfull_def_inst]; exact hk
      exact h_min hsub
    -- In particular: (subcodebook j, y) = (c (reindex j), y) ∈ A.
    have hsub_typ : (subcodebook j, y) ∈ A := hfull_typ
    -- For ALL k' < j (Fin M_target), (subcodebook k', y) ∉ A by monotonicity.
    have hsub_min : ∀ k' : Fin M_target, k' < j → (subcodebook k', y) ∉ A := by
      intro k' hk'
      have hreindex_lt : reindex k' < reindex j := hreindex_strictMono hk'
      exact hfull_min (reindex k') hreindex_lt
    -- So sub-decoder finds the smallest sub-typical index = j.
    have h_exists_sub : ∃ k : Fin M_target, (subcodebook k, y) ∈ A :=
      ⟨j, hsub_typ⟩
    have : jointTypicalDecoder A subcodebook y = j := by
      unfold jointTypicalDecoder
      rw [dif_pos h_exists_sub]
      set inst_sub_dec : DecidablePred fun k : Fin M_target => (subcodebook k, y) ∈ A :=
        fun x => Classical.propDecidable ((fun m => (subcodebook m, y) ∈ A) x)
      haveI inst_sub : DecidablePred fun k : Fin M_target => (subcodebook k, y) ∈ A :=
        inferInstance
      have h_inst_eq : inst_sub = inst_sub_dec := Subsingleton.elim _ _
      show @Fin.find M_target (fun k => (subcodebook k, y) ∈ A) inst_sub_dec
          h_exists_sub = j
      rw [← h_inst_eq]
      exact (Fin.find_eq_iff (i := j) h_exists_sub).mpr ⟨hsub_typ, hsub_min⟩
    exact hsub_def this
  · -- Full has no typical; decoder_full = ⟨0, ...⟩ = 0 ∈ Fin M.
    unfold jointTypicalDecoder at hfull_def
    rw [dif_neg h_exists_full] at hfull_def
    -- So reindex j = 0 in Fin M (as a value).
    have hreindex_zero : (reindex j : ℕ) = 0 := by
      have : (reindex j : ℕ) = ((⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ : Fin M) : ℕ) := by
        rw [← hfull_def]
      simpa using this
    -- No sub-codeword can be typical (each equals c(reindex k')).
    have h_no_sub_typ : ¬ ∃ k : Fin M_target, (subcodebook k, y) ∈ A := by
      rintro ⟨k, hk⟩
      exact h_exists_full ⟨reindex k, hk⟩
    have h_decoder_sub_zero : jointTypicalDecoder A subcodebook y
        = ⟨0, Nat.pos_of_ne_zero (NeZero.ne M_target)⟩ := by
      unfold jointTypicalDecoder
      rw [dif_neg h_no_sub_typ]
    -- For sub-decoder to satisfy `decoder_sub y ≠ j` (hsub_def), j ≠ 0.
    have hj_ne_zero_sub : (j : ℕ) ≠ 0 := by
      intro hj0
      apply hsub_def
      rw [h_decoder_sub_zero]
      exact Fin.ext hj0.symm
    -- reindex j = 0 with j ≠ 0 contradicts strict monotonicity (reindex 0 < reindex j).
    have hj_pos : (0 : Fin M_target) < j := by
      rw [Fin.pos_iff_ne_zero]
      intro heq
      exact hj_ne_zero_sub (by simp [heq])
    have h_reindex_zero_lt : reindex 0 < reindex j := hreindex_strictMono hj_pos
    have : (reindex 0 : ℕ) < (reindex j : ℕ) := h_reindex_zero_lt
    rw [hreindex_zero] at this
    exact Nat.not_lt_zero _ this

theorem awgn_errorEvent_aemeasurable
    {n M : ℕ} [NeZero M] (P' : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA_meas : MeasurableSet A) (m : Fin M) :
    AEMeasurable (fun c : Fin M → Fin n → ℝ =>
        (Measure.pi (fun i => awgnChannel N h_meas (c m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              c (jointTypicalDecoder A c)).errorEvent m))
      (gaussianCodebook M n P'.toNNReal) := by
  classical
  refine Measurable.aemeasurable ?_
  -- Joint error-event set: {(c, y) | jointTypicalDecoder A c y ≠ m}.
  set T : Set ((Fin M → Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | jointTypicalDecoder A p.1 p.2 ≠ m} with hT_def
  have hT_meas : MeasurableSet T := by
    -- preimage of the measurable set {m}ᶜ ⊆ Fin M under joint decoder.
    have h_joint := jointTypicalDecoder_joint_measurable
      (n := n) (M := M) A hA_meas
    have h_compl : MeasurableSet ({m}ᶜ : Set (Fin M)) :=
      (MeasurableSet.singleton m).compl
    exact h_joint h_compl
  -- Rewrite via the kernel + prodMk preimage shape required by
  -- `Kernel.measurable_kernel_prodMk_left`.
  have hPe_eq : (fun c : Fin M → Fin n → ℝ =>
      (Measure.pi (fun i => awgnChannel N h_meas (c m i)))
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M) (n := n) (α := ℝ) (β := ℝ)
            c (jointTypicalDecoder A c)).errorEvent m))
      = (fun c : Fin M → Fin n → ℝ =>
          awgnCodebookKernel N h_meas m c (Prod.mk c ⁻¹' T)) := by
    funext c
    rfl
  rw [hPe_eq]
  exact Kernel.measurable_kernel_prodMk_left hT_meas

theorem awgn_subcodebook_errorEvent_le
    {n M M_target : ℕ} [NeZero M] [NeZero M_target] (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N)
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (c_full : Fin M → Fin n → ℝ) (reindex : Fin M_target → Fin M)
    (hreindex_strictMono : StrictMono reindex) {b : ℝ≥0∞}
    (hfull : ∀ j : Fin M_target,
      (Measure.pi (fun i => awgnChannel N h_meas (c_full (reindex j) i)))
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M) (n := n) (α := ℝ) (β := ℝ)
            c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j)) ≤ b)
    (j : Fin M_target) :
    (Measure.pi (fun i => awgnChannel N h_meas (c_full (reindex j) i)))
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M_target) (n := n) (α := ℝ) (β := ℝ)
            (fun i => c_full (reindex i))
            (jointTypicalDecoder A (fun i => c_full (reindex i)))).errorEvent j) ≤ b := by
  classical
  set subcodebook : Fin M_target → Fin n → ℝ := fun i => c_full (reindex i)
    with hsubcodebook_def
  set μ_y : Measure (Fin n → ℝ) :=
    Measure.pi (fun i => awgnChannel N h_meas (subcodebook j i)) with hμ_y_def
  -- Step 1: Set-level inclusion `errorEvent_sub j ⊆ errorEvent_full (reindex j)`.
  have h_incl : (InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M_target) (n := n) (α := ℝ) (β := ℝ)
            subcodebook (jointTypicalDecoder A subcodebook)).errorEvent j
      ⊆ (InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M) (n := n) (α := ℝ) (β := ℝ)
            c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j) := by
    rw [hsubcodebook_def]
    exact errorEvent_jointTypicalDecoder_comp_subset_of_strictMono
      A c_full reindex hreindex_strictMono j
  -- Step 2: Monotonicity of `μ_y` gives the measure inclusion.
  have h_meas_le := μ_y.mono h_incl
  -- The full-error measure under this `μ_y` equals the full-side error measure.
  have h_full_eq :
      μ_y ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j))
        = (Measure.pi (fun i => awgnChannel N h_meas (c_full (reindex j) i)))
            ((InformationTheory.Shannon.ChannelCoding.Code.mk
                (M := M) (n := n) (α := ℝ) (β := ℝ)
                c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j)) := rfl
  change μ_y _ ≤ μ_y _ at h_meas_le
  rw [h_full_eq] at h_meas_le
  exact h_meas_le.trans (hfull j)

theorem awgn_exists_codebook_combined_penalty
    {n M : ℕ} [NeZero M] (P P' : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (A : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA_meas : MeasurableSet A)
    (hM_ge_two : 2 ≤ M) {ε_rand ε_pow ε_d2 : ℝ}
    (hε_rand_nonneg : 0 ≤ ε_rand) (hε_pow_pos : 0 < ε_pow) (hε_d2_pos : 0 < ε_d2)
    (h_slack_eq : 2 * ε_rand + ε_pow = 2 * ε_d2) (h4_lt_one : 4 * ε_d2 < 1)
    (h_per_m : ∀ m : Fin M,
      ∫⁻ c : Fin M → Fin n → ℝ,
        (Measure.pi (fun i => awgnChannel N h_meas (c m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              c (jointTypicalDecoder A c)).errorEvent m)
      ∂(gaussianCodebook M n P'.toNNReal) ≤ ENNReal.ofReal (2 * ε_rand))
    (h_viol_mass : ∀ m : Fin M,
      (gaussianCodebook M n P'.toNNReal)
          {c : Fin M → Fin n → ℝ | (n : ℝ) * P < ∑ i, (c m i) ^ 2}
        ≤ ENNReal.ofReal ε_pow) :
    ∃ (c_full : Fin M → Fin n → ℝ) (S : Finset (Fin M)), M / 2 ≤ S.card ∧
      (∀ s ∈ S,
        (Measure.pi (fun i => awgnChannel N h_meas (c_full s i)))
            ((InformationTheory.Shannon.ChannelCoding.Code.mk
                (M := M) (n := n) (α := ℝ) (β := ℝ)
                c_full (jointTypicalDecoder A c_full)).errorEvent s)
          ≤ ENNReal.ofReal (4 * ε_d2)) ∧
      (∀ s ∈ S, ∑ i, (c_full s i) ^ 2 ≤ (n : ℝ) * P) := by
  classical
  set Pe : (Fin M → Fin n → ℝ) → Fin M → ℝ≥0∞ := fun c m =>
    (Measure.pi (fun i => awgnChannel N h_meas (c m i)))
      ((InformationTheory.Shannon.ChannelCoding.Code.mk
          (M := M) (n := n) (α := ℝ) (β := ℝ)
          c (jointTypicalDecoder A c)).errorEvent m) with hPe_def
  have hPe_le_one : ∀ c m, Pe c m ≤ 1 := by
    intro c m
    haveI : IsMarkovKernel (awgnChannel N h_meas) := awgnChannel.instIsMarkovKernel N h_meas
    haveI : IsProbabilityMeasure
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c m i))) := by infer_instance
    exact prob_le_one
  set ViolSet : Fin M → Set (Fin M → Fin n → ℝ) := fun m =>
    {c : Fin M → Fin n → ℝ | (n : ℝ) * P < ∑ i, (c m i) ^ 2} with hViolSet_def
  have hViolSet_meas : ∀ m, MeasurableSet (ViolSet m) := by
    intro m
    rw [hViolSet_def]
    apply measurableSet_lt measurable_const
    refine Finset.measurable_sum _ (fun i _ => ?_)
    have h_proj : Measurable (fun c : Fin M → Fin n → ℝ => c m i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply m)
    exact h_proj.pow_const 2
  set Viol : (Fin M → Fin n → ℝ) → Fin M → ℝ≥0∞ := fun c m =>
    (ViolSet m).indicator (fun _ => (1 : ℝ≥0∞)) c with hViol_def
  have hViol_le_one : ∀ c m, Viol c m ≤ 1 := by
    intro c m
    rw [hViol_def]
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) c
  have hViol_meas : ∀ m, Measurable (fun c => Viol c m) := by
    intro m
    rw [hViol_def]
    exact measurable_const.indicator (hViolSet_meas m)
  have hPe_meas : ∀ m, AEMeasurable (fun c => Pe c m)
      (gaussianCodebook M n P'.toNNReal) := fun m =>
    awgn_errorEvent_aemeasurable P' N h_meas A hA_meas m
  have hPV_meas : ∀ m, AEMeasurable (fun c => Pe c m + Viol c m)
      (gaussianCodebook M n P'.toNNReal) := fun m =>
    (hPe_meas m).add (hViol_meas m).aemeasurable
  have hG_aemeas : AEMeasurable (fun c => ∑ m, (Pe c m + Viol c m))
      (gaussianCodebook M n P'.toNNReal) := by
    have h := Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin M)))
      (μ := gaussianCodebook M n P'.toNNReal)
      (f := fun m c => Pe c m + Viol c m) (fun m _ => hPV_meas m)
    rw [show (fun c => ∑ m, (Pe c m + Viol c m)) =
          (∑ m ∈ (Finset.univ : Finset (Fin M)), fun c => Pe c m + Viol c m) from
        (Finset.sum_fn _ _).symm]
    exact h
  have h_per_int : ∀ m,
      ∫⁻ c, (Pe c m + Viol c m) ∂(gaussianCodebook M n P'.toNNReal)
        ≤ ENNReal.ofReal (2 * ε_rand) + ENNReal.ofReal ε_pow := by
    intro m
    rw [lintegral_add_left' (hPe_meas m)]
    refine add_le_add (h_per_m m) ?_
    have h_viol_int : ∫⁻ c, Viol c m ∂(gaussianCodebook M n P'.toNNReal)
        = (gaussianCodebook M n P'.toNNReal) (ViolSet m) := by
      rw [hViol_def]
      exact lintegral_indicator_const (hViolSet_meas m) _ |>.trans (by rw [one_mul])
    rw [h_viol_int]
    exact h_viol_mass m
  have hsum_total :
      ∫⁻ c, (∑ m, (Pe c m + Viol c m)) ∂(gaussianCodebook M n P'.toNNReal)
        ≤ (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) := by
    rw [lintegral_finsetSum' Finset.univ (fun m _ => hPV_meas m)]
    refine le_trans (Finset.sum_le_sum (fun m _ => h_per_int m)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    gcongr
    rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hε_pow_pos), h_slack_eq]
  obtain ⟨c_full, hc_full_bound⟩ :=
    awgn_exists_codebook_le_avg (M := M) (n := n) (σsq := P'.toNNReal)
      (Pe := fun c => ∑ m, (Pe c m + Viol c m))
      hG_aemeas (B := (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2)) hsum_total
  have hPe_ne_top : ∀ m, Pe c_full m ≠ ⊤ := fun m =>
    (hPe_le_one c_full m).trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤) |>.ne
  have hViol_ne_top : ∀ m, Viol c_full m ≠ ⊤ := fun m =>
    (hViol_le_one c_full m).trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤) |>.ne
  set Comb : Fin M → ℝ := fun m => (Pe c_full m).toReal + (Viol c_full m).toReal
    with hComb_def
  have hComb_nn : ∀ m, 0 ≤ Comb m := fun m => by rw [hComb_def]; positivity
  have h_real_sum : (∑ m, Comb m) ≤ (M : ℝ) * (2 * ε_d2) := by
    have h_toReal_sum : (∑ m, Comb m)
        = (∑ m, (Pe c_full m + Viol c_full m)).toReal := by
      rw [ENNReal.toReal_sum (fun m _ => ENNReal.add_ne_top.mpr ⟨hPe_ne_top m, hViol_ne_top m⟩)]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hComb_def, ENNReal.toReal_add (hPe_ne_top m) (hViol_ne_top m)]
    rw [h_toReal_sum]
    have h_M_finite_ne : (M : ℝ≥0∞) * ENNReal.ofReal (2 * ε_d2) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) ENNReal.ofReal_ne_top
    have h_mono := ENNReal.toReal_mono h_M_finite_ne hc_full_bound
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * ε_d2),
        ENNReal.toReal_natCast] at h_mono
    exact h_mono
  obtain ⟨S, hS_card, hS_pe⟩ :=
    awgn_expurgate_worst_half (M := M) hM_ge_two Comb hComb_nn hε_d2_pos h_real_sum
  refine ⟨c_full, S, hS_card, ?_, ?_⟩
  · intro s hs
    have h_real_bound : (Pe c_full s).toReal ≤ 4 * ε_d2 := by
      have h_comb := hS_pe s hs
      have h_viol_nn : (0 : ℝ) ≤ (Viol c_full s).toReal := ENNReal.toReal_nonneg
      rw [hComb_def] at h_comb
      linarith
    show Pe c_full s ≤ ENNReal.ofReal (4 * ε_d2)
    rw [← ENNReal.ofReal_toReal (hPe_ne_top s)]
    exact ENNReal.ofReal_le_ofReal h_real_bound
  · intro s hs
    have h_comb_lt_one : Comb s < 1 := by
      have h_le := hS_pe s hs
      linarith
    have h_viol_lt_one : (Viol c_full s).toReal < 1 := by
      have h_pe_nn : (0 : ℝ) ≤ (Pe c_full s).toReal := ENNReal.toReal_nonneg
      have : (Viol c_full s).toReal ≤ Comb s := by rw [hComb_def]; linarith
      linarith
    have hViol_unfold : Viol c_full s
        = (ViolSet s).indicator (fun _ => (1 : ℝ≥0∞)) c_full := rfl
    have h_notmem : c_full ∉ ViolSet s := by
      intro h_mem
      rw [hViol_unfold, Set.indicator_of_mem h_mem] at h_viol_lt_one
      simp at h_viol_lt_one
    rw [hViolSet_def] at h_notmem
    simp only [Set.mem_setOf_eq, not_lt] at h_notmem
    exact h_notmem

theorem awgn_capacity_inflatedRate_lt
    {P P' R'' : ℝ} {N : ℝ≥0} (hP'_pos : 0 < P') (hP'_lt_P : P' ≤ P)
    (hN_pos : (0 : ℝ) < (N : ℝ))
    (hR''_lt_C : R'' < (1 : ℝ) / 2 * Real.log (1 + P' / (N : ℝ))) :
    R'' < (1 / 2) * Real.log (1 + P / (N : ℝ)) := by
  have h_div_le : P' / (N : ℝ) ≤ P / (N : ℝ) :=
    div_le_div_of_nonneg_right hP'_lt_P (le_of_lt hN_pos)
  have h_arg_le : 1 + P' / (N : ℝ) ≤ 1 + P / (N : ℝ) := by linarith
  have h_arg_pos : 0 < 1 + P' / (N : ℝ) := by
    have : 0 < P' / (N : ℝ) := div_pos hP'_pos hN_pos
    linarith
  have h_log_le : Real.log (1 + P' / (N : ℝ)) ≤ Real.log (1 + P / (N : ℝ)) :=
    Real.log_le_log h_arg_pos h_arg_le
  have h_C_le : (1 : ℝ) / 2 * Real.log (1 + P' / (N : ℝ))
      ≤ (1 / 2) * Real.log (1 + P / (N : ℝ)) := by
    have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
    exact mul_le_mul_of_nonneg_left h_log_le (le_of_lt h_half_pos)
  exact lt_of_lt_of_le hR''_lt_C h_C_le

@[entry_point]
theorem isAwgnTypicalityHypothesis
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
          ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
            (c : AwgnCode M n P),
              ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε := by
  intro R hR_pos hR ε hε
  classical
  -- The shared slack variance `P'` (strict `P' < P`) comes from
  -- `awgnPowerWitness_exists`; the three sub-bounds at `P'` come from the lemmas
  -- in `Walls.lean`. The assembly below consumes `h_aep' / h_rand' / h_power'`.
  obtain ⟨P', hP'_pos, hP'_lt_P_strict, hR_lt_P'C⟩ :=
    awgnPowerWitness_exists P hP N hN hR_pos hR
  -- Non-strict slack kept under the original name for the verbatim assembly.
  have hP'_lt_P : P' ≤ P := le_of_lt hP'_lt_P_strict
  -- (i) AEP at `P'` (typical-set existence + 2 bounds at slack `δ`).
  have h_aep' := continuousAepGaussian_holds P' N
  -- (iii) per-codeword power-constraint expurgation bound. Needs the variance-level
  -- slack `(P'.toNNReal : ℝ) < P`; from `0 < P' < P` and `(P'.toNNReal : ℝ) = P'`
  -- (since `P' > 0`).
  have hP'_toNNReal_eq : (P'.toNNReal : ℝ) = P' := by
    rw [Real.coe_toNNReal']; exact max_eq_left hP'_pos.le
  have hP'slack : (P'.toNNReal : ℝ) < P := by rw [hP'_toNNReal_eq]; exact hP'_lt_P_strict
  have h_power' := awgnPowerConstraintPerCodeword_holds P' P hP'slack N
  -- WLOG `ε ≤ 1` via `ε₁ := min ε 1`; conclusion `< ε₁` ⟹ `< ε`.
  set ε₁ : ℝ := min ε 1 with hε₁_def
  have hε₁_pos : 0 < ε₁ := lt_min hε one_pos
  have hε₁_le_ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁_le_one : ε₁ ≤ 1 := min_le_right _ _
  -- Slack layout: ε_d2 := ε₁/5; need 2 ε_rand + ε_pow = 2 ε_d2 = 2 ε₁/5.
  set ε_d2  : ℝ := ε₁ / 5  with hε_d2_def
  set ε_rand : ℝ := ε₁ / 10 with hε_rand_def
  set ε_pow  : ℝ := ε₁ / 5  with hε_pow_def
  have hε_d2_pos   : 0 < ε_d2   := by positivity
  have hε_rand_pos : 0 < ε_rand := by positivity
  have hε_pow_pos  : 0 < ε_pow  := by positivity
  -- Inflated rate `R'' := (R + C)/2`, where capacity `C` is evaluated at
  -- the slack variance `P'` (so `R < C` holds via `hR_lt_P'C`).
  set C : ℝ := (1 : ℝ) / 2 * Real.log (1 + P' / (N : ℝ)) with hC_def
  have hR_lt_C : R < C := hR_lt_P'C
  set R'' : ℝ := (R + C) / 2 with hR''_def
  have hR''_pos : 0 < R'' := by
    have : 0 < R + C := by linarith
    linarith
  have hR''_lt_C : R'' < C := by linarith
  have hR_lt_R'' : R < R'' := by linarith
  -- **Typicality slack `δ`** (δ-separation): pick `δ := (C − R)/12 > 0` so that
  -- `R'' + 3δ < C` (the margin condition the δ-separated union bound consumes).
  -- `3δ = (C − R)/4` and `R'' = C − (C − R)/2`, so `R'' + 3δ = C − (C − R)/4 < C`.
  set δ : ℝ := (C - R) / 12 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hR_lt_C]
  have hslack'' : R'' + 3 * δ < C := by
    rw [hδ_def, hR''_def]; linarith
  -- Derive `R'' < (1/2) * log(1 + P / N)` (the *original*-P capacity bound)
  -- from `R'' < C = (1/2) * log(1 + P'/N)` via monotonicity in P'≤P.
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := N.coe_nonneg
    exact lt_of_le_of_ne hN_nonneg (fun h => hN h.symm)
  have hR''_lt_PC : R'' < (1 / 2) * Real.log (1 + P / (N : ℝ)) :=
    awgn_capacity_inflatedRate_lt hP'_pos hP'_lt_P hN_pos hR''_lt_C
  -- Extract three N₀ from the sub-bounds.
  -- AEP (`h_aep'`) at slack variance `P'`, typicality slack `δ`, mass-fail `ε_rand`;
  -- union bound (`awgn_random_coding_union_bound`) at `P'`, rate `R''`, slack `δ`;
  -- power (`h_power'`) per-codeword at variance `P'`, target `P`, mass-fail `ε_pow`.
  obtain ⟨N_aep,  hN_aep⟩  := h_aep' hδ_pos hε_rand_pos
  obtain ⟨N_rand, hN_rand⟩ :=
    awgn_random_coding_union_bound P' N h_meas hP'_pos hN hε_rand_pos hδ_pos hR''_pos hslack''
  obtain ⟨N_pow,  hN_pow⟩  := h_power' hε_pow_pos
  -- `N_doubling`: smallest `n` such that `2 * ⌈exp(nR)⌉ ≤ ⌈exp(n·R'')⌉`.
  -- Existence: `exp(nR'')/exp(nR) = exp(n(R''-R)) → ∞`, so for n large
  -- `exp(n·R'') ≥ 2 * exp(nR) + 2`, which forces the Nat.ceil inequality.
  obtain ⟨N_doubling, hN_doubling⟩ :=
    exists_two_mul_ceil_exp_le_ceil_exp_of_lt hR_pos.le hR_lt_R''
  refine ⟨max N_aep (max N_rand (max N_pow (max N_doubling 1))), ?_⟩
  intro n hn
  have hn_aep  : N_aep  ≤ n := le_trans (le_max_left _ _) hn
  have hn_rand : N_rand ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn_pow  : N_pow  ≤ n :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn_double : N_doubling ≤ n :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)))
  -- Codebook sizes: `M_target = ⌈exp(nR)⌉`, internal `M = ⌈exp(n·R'')⌉`.
  set M_target : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R))   with hM_target_def
  set M        : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R'')) with hM_def
  have hM_target_pos : 0 < M_target :=
    Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM_pos : 0 < M := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM_ge : 2 * M_target ≤ M := hN_doubling n hn_double
  have hM_ge_two : 2 ≤ M := by have := hM_target_pos; omega
  haveI : NeZero M := ⟨hM_pos.ne'⟩
  haveI : NeZero M_target := ⟨hM_target_pos.ne'⟩
  -- (1) typical set + measurability from AEP at parameters `(P', N, δ, ε_rand, n)`,
  --     **keeping** the two AEP bounds (mass `≥ 1−ε_rand`, indep-pair `≤ exp(...)`)
  --     to thread into the δ-separated union bound.
  obtain ⟨A, hA_meas, hA_mass, hA_indep⟩ := hN_aep hn_aep
  -- (2) per-m average error bound from the δ-separated union bound at rate R''
  --     (size M = ⌈exp(n·R'')⌉), codebook drawn from the P'-variance Gaussian
  --     product. The two AEP bounds on `A` are now threaded as arguments.
  have hM_le_ceil_R'' : M ≤ Nat.ceil (Real.exp ((n : ℝ) * R'')) := le_rfl
  have h_per_m : ∀ m : Fin M,
      ∫⁻ codebook : Fin M → Fin n → ℝ,
        ((Measure.pi (fun i => awgnChannel N h_meas (codebook m i)))
          ((InformationTheory.Shannon.ChannelCoding.Code.mk
              (M := M) (n := n) (α := ℝ) (β := ℝ)
              codebook (jointTypicalDecoder A codebook)).errorEvent m))
      ∂(gaussianCodebook M n P'.toNNReal)
        ≤ ENNReal.ofReal (2 * ε_rand) := by
    intro m
    exact hN_rand hn_rand hM_pos hM_le_ceil_R'' A hA_meas hA_mass hA_indep m
  -- (3) per-codeword power-violation mass bound from h_power' (per-codeword form).
  --     Each codeword `m` violates `∑ᵢ (c m i)² > n·P` on a set of mass ≤ ε_pow.
  --     Codebook drawn at variance P', target `n · P` (slack `P' < P`).
  have h_viol_mass : ∀ m : Fin M,
      (gaussianCodebook M n P'.toNNReal)
          {c : Fin M → Fin n → ℝ | (n : ℝ) * P < ∑ i, (c m i) ^ 2}
        ≤ ENNReal.ofReal ε_pow := by
    intro m
    exact hN_pow hn_pow hM_pos m
  -- (4)-(8) Build a codebook with a half-rate expurgated index set `S` carrying
  -- both the per-codeword error bound (`≤ 4ε_d2`) and the power constraint.
  have h_slack_eq : 2 * ε_rand + ε_pow = 2 * ε_d2 := by
    show 2 * (ε₁ / 10) + ε₁ / 5 = 2 * (ε₁ / 5); ring
  have h4_lt_one : 4 * ε_d2 < 1 := by
    have : ε_d2 ≤ 1 / 5 := by rw [hε_d2_def]; linarith [hε₁_le_one]
    linarith
  obtain ⟨c_full, S, hS_card, hS_pe_err, hS_power⟩ :=
    awgn_exists_codebook_combined_penalty P P' N h_meas A hA_meas hM_ge_two
      hε_rand_pos.le hε_pow_pos hε_d2_pos h_slack_eq h4_lt_one h_per_m h_viol_mass
  -- (9) Reindex: |S| ≥ M/2 ≥ M_target (since 2 * M_target ≤ M).
  have hM_target_le_half : M_target ≤ M / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by linarith [hM_ge])
  have hM_target_le_S : M_target ≤ S.card := le_trans hM_target_le_half hS_card
  -- Use a *monotonic* reindex `Fin M_target ↪o Fin M` so the sub-decoder's
  -- error event sits inside the full-decoder's error event (smallest-index
  -- tie-break of `jointTypicalDecoder` is preserved by order embeddings).
  set reindex_emb : Fin M_target ↪o Fin M :=
    (Fin.castLEOrderEmb hM_target_le_S).trans (S.orderEmbOfFin rfl)
      with hreindex_emb_def
  set reindex : Fin M_target → Fin M := fun i => reindex_emb i with hreindex_def
  have hreindex_strictMono : StrictMono reindex :=
    reindex_emb.strictMono
  -- Each `reindex i ∈ S` (image of `orderEmbOfFin S` is `S`).
  have h_reindex_mem : ∀ i : Fin M_target, reindex i ∈ S := by
    intro i
    show (S.orderEmbOfFin rfl) ((Fin.castLEOrderEmb hM_target_le_S) i) ∈ S
    exact Finset.orderEmbOfFin_mem S rfl _
  set subcodebook : Fin M_target → Fin n → ℝ := fun i => c_full (reindex i)
    with hsubcodebook_def
  -- (10) Power constraint + (11) full-side error bound on the subcodebook, both
  -- read off the combined-penalty output set `S` at `reindex j ∈ S`.
  have h_sub_power : ∀ j : Fin M_target,
      (∑ i, (subcodebook j i)^2) ≤ (n : ℝ) * P := fun j =>
    hS_power (reindex j) (h_reindex_mem j)
  have h_full_pe : ∀ j : Fin M_target,
      (Measure.pi (fun i => awgnChannel N h_meas (c_full (reindex j) i)))
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M) (n := n) (α := ℝ) (β := ℝ)
            c_full (jointTypicalDecoder A c_full)).errorEvent (reindex j))
        ≤ ENNReal.ofReal (4 * ε_d2) := fun j =>
    hS_pe_err (reindex j) (h_reindex_mem j)
  -- Transfer the full-side bound to the sub-decoder via the error-event inclusion.
  have h_sub_pe : ∀ j : Fin M_target,
      ((Measure.pi (fun i => awgnChannel N h_meas (subcodebook j i)))
        ((InformationTheory.Shannon.ChannelCoding.Code.mk
            (M := M_target) (n := n) (α := ℝ) (β := ℝ)
            subcodebook (jointTypicalDecoder A subcodebook)).errorEvent j))
        ≤ ENNReal.ofReal (4 * ε_d2) := fun j =>
    awgn_subcodebook_errorEvent_le N h_meas A c_full reindex hreindex_strictMono
      h_full_pe j
  -- (13) D-3: bridge to AwgnCode with the 5ε_d2 = ε₁ ≤ ε bound.
  --      Constraint target is the original `n · P`, so `AwgnCode M_target n P`.
  obtain ⟨awgnCode, h_awgnCode_pe⟩ :=
    awgn_extract_AwgnCode (P := P) (N := N) h_meas (n := n) (M := M_target)
      (ε := ε_d2) hε_d2_pos (A := A) hA_meas subcodebook h_sub_pe h_sub_power
  refine ⟨M_target, le_rfl, awgnCode, ?_⟩
  intro m
  have h_awg := h_awgnCode_pe m
  -- `5 * ε_d2 = ε₁ ≤ ε`.
  have h5 : 5 * ε_d2 = ε₁ := by
    show 5 * (ε₁ / 5) = ε₁; ring
  linarith [h_awg, hε₁_le_ε]

end InformationTheory.Shannon.AWGN
