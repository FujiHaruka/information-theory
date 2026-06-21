import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.AchievabilityCodebook
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Joint-typicality decoder and the random-coding union bound

The decoder side of AWGN achievability (Cover–Thomas 9.2): the joint-typicality
decoder, the measurability plumbing for the per-message error event, and the
random-coding union bound culminating in `awgn_avg_error_union_bound`.

## Main definitions

* `jointTypicalDecoder A codebook` — decodes a received vector to the smallest
  codeword index whose pair lies in the typical set `A`.

## Main statements

* `awgn_random_coding_union_bound` — the codebook-average per-message error
  probability is `≤ 2ε` past a rate-dependent threshold, given the two AEP bounds.
* `awgn_avg_error_union_bound` — closes the union bound against the
  AEP-supplied typical set.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Continuous AEP for the n-dimensional Gaussian

The continuous AEP is the lemma `continuousAepGaussian_holds` in
`InformationTheory/Shannon/AWGN/KLCapacityAndAEP.lean`. Consumers in this file call that
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

end InformationTheory.Shannon.AWGN
