import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

/-!
# Second-moment core of the mutual covering lemma

Marton's mutual covering lemma asserts that among the `M₁ * M₂` pairs formed from two
independently drawn codebooks, at least one pair is jointly typical.  The standard proof
is a second moment argument, and its analytic core does not mention typicality at all:
it only needs a measurable set `S` in the product alphabet and the fact that indicator
variables attached to two pairs sharing no index are independent.

This file develops that core for an abstract `S`, in two strengths.  The crude estimate uses
no information about `S` beyond `p`, and its conclusion needs both `M₁ p` and `M₂ p` to be
large.  The sharpened estimate additionally assumes that every conditional slice of `S` has
mass at most `qbar`, and its conclusion splits into a term needing only the product `M₁ M₂ p`
to be large plus two terms carrying the ratio `qbar / p`.

## Main definitions

* `codebookFamily X Y` — the two codebooks interleaved into one family indexed by
  `Fin M₁ ⊕ Fin M₂`, so that mutual independence of all `M₁ + M₂` codewords is a single
  `iIndepFun` hypothesis.
* `pairIndicator X Y S p` — indicator of "the codeword pair indexed by `p` lands in `S`".
* `pairCount X Y S` — number of codeword pairs landing in `S`.
* `pairProb μX μY S` — probability that one independently drawn pair lands in `S`.
* `sharedFstSet S` / `sharedSndSet S` — the triples of codewords realizing two pairs that
  share one index.

## Main results

* `integral_pairCount` — the first moment `E[A] = M₁ * M₂ * p`.
* `covariance_pairIndicator_eq_zero` — covariance vanishes for pairs sharing no index.
* `variance_pairCount_le` — the resulting variance bound `Var[A] ≤ M₁ M₂ (M₁ + M₂) p`.
* `meas_pairCount_eq_zero_le` — Chebyshev's inequality applied to the above:
  `P(A = 0) ≤ (M₁ + M₂) / (M₁ M₂ p)`.
* `covariance_pairIndicator_shared_le` — under a uniform slice bound `qbar`, the covariance of
  two pairs sharing one index is at most `qbar * p`.
* `variance_pairCount_le'` and `meas_pairCount_eq_zero_le'` — the sharpened variance bound
  `Var[A] ≤ M₁ M₂ p + M₁ M₂ (M₁ + M₂) qbar p` and the estimate it yields,
  `P(A = 0) ≤ 1 / (M₁ M₂ p) + qbar / (M₁ p) + qbar / (M₂ p)`.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [Nonempty α] [Nonempty β]
  {μ : Measure Ω} {μX : Measure α} {μY : Measure β}
  {M₁ M₂ : ℕ} {X : Fin M₁ → Ω → α} {Y : Fin M₂ → Ω → β} {S : Set (α × β)}

/-- The two codebooks interleaved into a single family indexed by `Fin M₁ ⊕ Fin M₂`, each
entry padded by a constant in the unused coordinate so that the whole family shares the
codomain `α × β`.  Padding by a constant leaves the generated σ-algebra unchanged, so
`iIndepFun (codebookFamily X Y) μ` says exactly that the `M₁ + M₂` codewords are mutually
independent. -/
noncomputable def codebookFamily (X : Fin M₁ → Ω → α) (Y : Fin M₂ → Ω → β) :
    Fin M₁ ⊕ Fin M₂ → Ω → α × β :=
  Sum.elim (fun i ω ↦ (X i ω, Classical.arbitrary β))
    (fun j ω ↦ (Classical.arbitrary α, Y j ω))

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] in
@[simp]
lemma codebookFamily_inl (X : Fin M₁ → Ω → α) (Y : Fin M₂ → Ω → β) (i : Fin M₁) :
    codebookFamily X Y (Sum.inl i) = fun ω ↦ (X i ω, Classical.arbitrary β) := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] in
@[simp]
lemma codebookFamily_inr (X : Fin M₁ → Ω → α) (Y : Fin M₂ → Ω → β) (j : Fin M₂) :
    codebookFamily X Y (Sum.inr j) = fun ω ↦ (Classical.arbitrary α, Y j ω) := rfl

/-- Indicator of the event that the codeword pair indexed by `p` lands in `S`. -/
noncomputable def pairIndicator (X : Fin M₁ → Ω → α) (Y : Fin M₂ → Ω → β) (S : Set (α × β))
    (p : Fin M₁ × Fin M₂) (ω : Ω) : ℝ :=
  S.indicator (1 : α × β → ℝ) (X p.1 ω, Y p.2 ω)

/-- Number of codeword pairs landing in `S`. -/
noncomputable def pairCount (X : Fin M₁ → Ω → α) (Y : Fin M₂ → Ω → β) (S : Set (α × β))
    (ω : Ω) : ℝ :=
  ∑ p : Fin M₁ × Fin M₂, pairIndicator X Y S p ω

/-- Probability that one independently drawn codeword pair lands in `S`. -/
noncomputable def pairProb (μX : Measure α) (μY : Measure β) (S : Set (α × β)) : ℝ :=
  ((μX.prod μY) S).toReal

section Regularity

variable (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) (hS : MeasurableSet S)

include hX hY in
lemma measurable_codebookFamily (k : Fin M₁ ⊕ Fin M₂) :
    Measurable (codebookFamily X Y k) := by
  cases k with
  | inl i => exact (hX i).prodMk measurable_const
  | inr j => exact measurable_const.prodMk (hY j)

omit [Nonempty α] [Nonempty β] in
include hX hY hS in
lemma measurable_pairIndicator (p : Fin M₁ × Fin M₂) :
    Measurable (pairIndicator X Y S p) :=
  (measurable_one.indicator hS).comp ((hX p.1).prodMk (hY p.2))

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [Nonempty α] [Nonempty β] in
lemma pairIndicator_nonneg (p : Fin M₁ × Fin M₂) (ω : Ω) : 0 ≤ pairIndicator X Y S p ω :=
  Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [Nonempty α] [Nonempty β] in
lemma pairIndicator_le_one (p : Fin M₁ × Fin M₂) (ω : Ω) : pairIndicator X Y S p ω ≤ 1 := by
  unfold pairIndicator
  by_cases h : (X p.1 ω, Y p.2 ω) ∈ S <;> simp [h]

omit [Nonempty α] [Nonempty β] in
include hX hY hS in
lemma memLp_pairIndicator [IsFiniteMeasure μ] (p : Fin M₁ × Fin M₂) :
    MemLp (pairIndicator X Y S p) 2 μ := by
  refine MemLp.of_bound (measurable_pairIndicator hX hY hS p).aestronglyMeasurable 1 ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pairIndicator_nonneg p ω)]
  exact pairIndicator_le_one p ω

omit [Nonempty α] [Nonempty β] in
include hX hY hS in
lemma memLp_pairCount [IsFiniteMeasure μ] : MemLp (pairCount X Y S) 2 μ := by
  have h : MemLp (∑ p : Fin M₁ × Fin M₂, pairIndicator X Y S p) 2 μ :=
    memLp_finsetSum' _ fun p _ ↦ memLp_pairIndicator hX hY hS p
  convert h using 1
  ext ω
  simp [pairCount, Finset.sum_apply]

end Regularity

section Moments

variable (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) (hS : MeasurableSet S)
  (hIndep : iIndepFun (codebookFamily X Y) μ)

include hX hY hIndep in
lemma indepFun_codewordPair {i i' : Fin M₁} {j j' : Fin M₂} (hi : i ≠ i') (hj : j ≠ j') :
    IndepFun (fun ω ↦ (X i ω, Y j ω)) (fun ω ↦ (X i' ω, Y j' ω)) μ := by
  have h := hIndep.indepFun_prodMk_prodMk (measurable_codebookFamily hX hY)
    (Sum.inl i) (Sum.inr j) (Sum.inl i') (Sum.inr j')
    (by simpa using hi) (by simp) (by simp) (by simpa using hj)
  have hg : Measurable fun q : (α × β) × (α × β) ↦ (q.1.1, q.2.2) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  exact h.comp hg hg

include hX hY hS hIndep in
lemma indepFun_pairIndicator {p q : Fin M₁ × Fin M₂} (hi : p.1 ≠ q.1) (hj : p.2 ≠ q.2) :
    IndepFun (pairIndicator X Y S p) (pairIndicator X Y S q) μ :=
  (indepFun_codewordPair hX hY hIndep hi hj).comp (measurable_one.indicator hS)
    (measurable_one.indicator hS)

include hX hY hS hIndep in
lemma covariance_pairIndicator_eq_zero [IsFiniteMeasure μ] {p q : Fin M₁ × Fin M₂}
    (hi : p.1 ≠ q.1) (hj : p.2 ≠ q.2) :
    cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] = 0 :=
  (indepFun_pairIndicator hX hY hS hIndep hi hj).covariance_eq_zero
    (memLp_pairIndicator hX hY hS p) (memLp_pairIndicator hX hY hS q)

include hIndep in
lemma indepFun_codeword (i : Fin M₁) (j : Fin M₂) : IndepFun (X i) (Y j) μ :=
  (hIndep.indepFun (i := Sum.inl i) (j := Sum.inr j) (by simp)).comp measurable_fst measurable_snd

variable (hXlaw : ∀ i, μ.map (X i) = μX) (hYlaw : ∀ j, μ.map (Y j) = μY)

include hX hY hIndep hXlaw hYlaw in
lemma map_codewordPair [IsFiniteMeasure μ] (i : Fin M₁) (j : Fin M₂) :
    μ.map (fun ω ↦ (X i ω, Y j ω)) = μX.prod μY := by
  rw [(indepFun_codeword hIndep i j).map_prod_eq_prod_map_map (hX i).aemeasurable
    (hY j).aemeasurable, hXlaw i, hYlaw j]

include hX hY hS hIndep hXlaw hYlaw in
lemma integral_pairIndicator [IsProbabilityMeasure μ] (p : Fin M₁ × Fin M₂) :
    μ[pairIndicator X Y S p] = pairProb μX μY S := by
  have hT : Measurable fun ω ↦ (X p.1 ω, Y p.2 ω) := (hX p.1).prodMk (hY p.2)
  have h1 : pairIndicator X Y S p
      = ((fun ω ↦ (X p.1 ω, Y p.2 ω)) ⁻¹' S).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases h : (X p.1 ω, Y p.2 ω) ∈ S <;> simp [pairIndicator, h]
  calc μ[pairIndicator X Y S p]
      = ∫ ω, ((fun ω ↦ (X p.1 ω, Y p.2 ω)) ⁻¹' S).indicator (1 : Ω → ℝ) ω ∂μ := by rw [h1]
    _ = μ.real ((fun ω ↦ (X p.1 ω, Y p.2 ω)) ⁻¹' S) := integral_indicator_one (hT hS)
    _ = pairProb μX μY S := by
        rw [measureReal_def, ← Measure.map_apply hT hS,
          map_codewordPair hX hY hIndep hXlaw hYlaw p.1 p.2, pairProb]

include hX hY hS hIndep hXlaw hYlaw in
lemma integral_pairCount [IsProbabilityMeasure μ] :
    μ[pairCount X Y S] = M₁ * M₂ * pairProb μX μY S := by
  have hint : ∀ p : Fin M₁ × Fin M₂, Integrable (pairIndicator X Y S p) μ :=
    fun p ↦ (memLp_pairIndicator hX hY hS p).integrable (by norm_num)
  simp only [pairCount]
  rw [integral_finsetSum _ fun p _ ↦ hint p]
  simp [integral_pairIndicator hX hY hS hIndep hXlaw hYlaw, Finset.card_univ]

end Moments

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [Nonempty α] [Nonempty β] in
private lemma sum_ite_fst_eq (c : ℝ) (a : Fin M₁) :
    ∑ q : Fin M₁ × Fin M₂, (if q.1 = a then c else 0) = M₂ * c := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : Fin M₁, (∑ _y : Fin M₂, (if x = a then c else 0))
      = (M₂ : ℝ) * (if x = a then c else 0) := by
    intro x; simp [Finset.card_univ]
  rw [Finset.sum_congr rfl fun x _ ↦ hinner x, ← Finset.mul_sum]
  simp

omit [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [Nonempty α] [Nonempty β] in
private lemma sum_ite_snd_eq (c : ℝ) (b : Fin M₂) :
    ∑ q : Fin M₁ × Fin M₂, (if q.2 = b then c else 0) = M₁ * c := by
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', mul_comm]

section Variance

variable (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) (hS : MeasurableSet S)
  (hIndep : iIndepFun (codebookFamily X Y) μ)
  (hXlaw : ∀ i, μ.map (X i) = μX) (hYlaw : ∀ j, μ.map (Y j) = μY)

include hX hY hS hIndep hXlaw hYlaw in
lemma covariance_pairIndicator_le [IsProbabilityMeasure μ] (p q : Fin M₁ × Fin M₂) :
    cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] ≤ pairProb μX μY S := by
  have hp2 : MemLp (pairIndicator X Y S p) 2 μ := memLp_pairIndicator hX hY hS p
  have hq2 : MemLp (pairIndicator X Y S q) 2 μ := memLp_pairIndicator hX hY hS q
  rw [covariance_eq_sub hp2 hq2]
  have h1 : μ[pairIndicator X Y S p * pairIndicator X Y S q] ≤ μ[pairIndicator X Y S p] := by
    refine integral_mono (hp2.integrable_mul hq2) (hp2.integrable (by norm_num)) fun ω ↦ ?_
    simpa using mul_le_of_le_one_right (pairIndicator_nonneg p ω) (pairIndicator_le_one q ω)
  have h2 : 0 ≤ μ[pairIndicator X Y S p] * μ[pairIndicator X Y S q] :=
    mul_nonneg (integral_nonneg fun ω ↦ pairIndicator_nonneg p ω)
      (integral_nonneg fun ω ↦ pairIndicator_nonneg q ω)
  have h3 : μ[pairIndicator X Y S p] = pairProb μX μY S :=
    integral_pairIndicator hX hY hS hIndep hXlaw hYlaw p
  linarith

include hX hY hS hIndep hXlaw hYlaw in
lemma variance_pairCount_le [IsProbabilityMeasure μ] :
    Var[pairCount X Y S; μ] ≤ M₁ * M₂ * (M₁ + M₂) * pairProb μX μY S := by
  have hpnn : 0 ≤ pairProb μX μY S := ENNReal.toReal_nonneg
  have hvar : Var[pairCount X Y S; μ]
      = ∑ p : Fin M₁ × Fin M₂, ∑ q : Fin M₁ × Fin M₂,
          cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] :=
    variance_fun_sum fun p ↦ memLp_pairIndicator hX hY hS p
  have key : ∀ p : Fin M₁ × Fin M₂,
      ∑ q : Fin M₁ × Fin M₂, cov[pairIndicator X Y S p, pairIndicator X Y S q; μ]
        ≤ (M₁ + M₂) * pairProb μX μY S := by
    intro p
    have hbound : ∀ q : Fin M₁ × Fin M₂,
        cov[pairIndicator X Y S p, pairIndicator X Y S q; μ]
          ≤ (if q.1 = p.1 then pairProb μX μY S else 0)
            + (if q.2 = p.2 then pairProb μX μY S else 0) := by
      intro q
      have hle := covariance_pairIndicator_le hX hY hS hIndep hXlaw hYlaw p q
      by_cases h1 : q.1 = p.1 <;> by_cases h2 : q.2 = p.2 <;>
        simp only [h1, h2, if_pos, if_false, add_zero, zero_add] <;> try linarith
      exact le_of_eq (covariance_pairIndicator_eq_zero hX hY hS hIndep (Ne.symm h1) (Ne.symm h2))
    calc ∑ q : Fin M₁ × Fin M₂, cov[pairIndicator X Y S p, pairIndicator X Y S q; μ]
        ≤ ∑ q : Fin M₁ × Fin M₂, ((if q.1 = p.1 then pairProb μX μY S else 0)
            + (if q.2 = p.2 then pairProb μX μY S else 0)) :=
          Finset.sum_le_sum fun q _ ↦ hbound q
      _ = M₂ * pairProb μX μY S + M₁ * pairProb μX μY S := by
          rw [Finset.sum_add_distrib, sum_ite_fst_eq, sum_ite_snd_eq]
      _ = (M₁ + M₂) * pairProb μX μY S := by ring
  calc Var[pairCount X Y S; μ]
      = ∑ p : Fin M₁ × Fin M₂, ∑ q : Fin M₁ × Fin M₂,
          cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] := hvar
    _ ≤ ∑ _p : Fin M₁ × Fin M₂, (M₁ + M₂) * pairProb μX μY S :=
        Finset.sum_le_sum fun p _ ↦ key p
    _ = M₁ * M₂ * (M₁ + M₂) * pairProb μX μY S := by
        simp [Finset.card_univ]
        ring

include hX hY hS hIndep hXlaw hYlaw in
/-- Second-moment estimate behind Marton's mutual covering lemma: the probability that no
codeword pair lands in `S` is at most `(M₁ + M₂) / (M₁ M₂ p)`, where `p` is the probability
that one independently drawn pair lands in `S`. -/
theorem meas_pairCount_eq_zero_le [IsProbabilityMeasure μ]
    (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) (hp : 0 < pairProb μX μY S) :
    μ {ω | pairCount X Y S ω = 0}
      ≤ ENNReal.ofReal ((M₁ + M₂) / (M₁ * M₂ * pairProb μX μY S)) := by
  have hM₁' : (0 : ℝ) < M₁ := by exact_mod_cast Nat.pos_of_ne_zero hM₁
  have hM₂' : (0 : ℝ) < M₂ := by exact_mod_cast Nat.pos_of_ne_zero hM₂
  have hc0 : 0 < (M₁ : ℝ) * M₂ * pairProb μX μY S := by positivity
  have hE : μ[pairCount X Y S] = (M₁ : ℝ) * M₂ * pairProb μX μY S :=
    integral_pairCount hX hY hS hIndep hXlaw hYlaw
  have hsub : {ω | pairCount X Y S ω = 0}
      ⊆ {ω | (M₁ : ℝ) * M₂ * pairProb μX μY S ≤ |pairCount X Y S ω - μ[pairCount X Y S]|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω, hE, zero_sub, abs_neg, abs_of_pos hc0]
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_variance_div_sq (memLp_pairCount hX hY hS) hc0).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hvar : Var[pairCount X Y S; μ]
      ≤ ((M₁ : ℝ) + M₂) * ((M₁ : ℝ) * M₂ * pairProb μX μY S) :=
    calc Var[pairCount X Y S; μ]
        ≤ (M₁ : ℝ) * M₂ * ((M₁ : ℝ) + M₂) * pairProb μX μY S :=
          variance_pairCount_le hX hY hS hIndep hXlaw hYlaw
      _ = ((M₁ : ℝ) + M₂) * ((M₁ : ℝ) * M₂ * pairProb μX μY S) := by ring
  rw [div_le_div_iff₀ (by positivity) hc0]
  nlinarith [hvar, hc0]

end Variance

section SharpVariance

/-! ### Sharpened variance bound under a uniform slice bound

`variance_pairCount_le` bounds the covariance of two pairs sharing one index by the crude
`pairProb μX μY S`.  If instead every conditional slice of `S` has mass at most `qbar`, that
covariance is bounded by `qbar * pairProb μX μY S`, and the resulting Chebyshev estimate
splits into a diagonal term `1 / (M₁ M₂ p)` plus shared-index terms carrying a factor `qbar`.

Two slice bounds are needed, one in each coordinate: the `α`-slices control the pairs sharing
their second index and the `β`-slices control the pairs sharing their first index.  Neither
bound implies the other. -/

/-- Triples `(x, y, y')` whose two pairs `(x, y)` and `(x, y')` both lie in `S`. -/
def sharedFstSet (S : Set (α × β)) : Set (α × β × β) :=
  {r | (r.1, r.2.1) ∈ S ∧ (r.1, r.2.2) ∈ S}

/-- Triples `(y, x, x')` whose two pairs `(x, y)` and `(x', y)` both lie in `S`. -/
def sharedSndSet (S : Set (α × β)) : Set (β × α × α) :=
  {r | (r.2.1, r.1) ∈ S ∧ (r.2.2, r.1) ∈ S}

variable {qbar : ℝ}

omit [Nonempty α] [Nonempty β] in
lemma measurableSet_sharedFstSet (hS : MeasurableSet S) :
    MeasurableSet (sharedFstSet S) := by
  have h1 : Measurable fun r : α × β × β ↦ (r.1, r.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have h2 : Measurable fun r : α × β × β ↦ (r.1, r.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  exact (h1 hS).inter (h2 hS)

omit [Nonempty α] [Nonempty β] in
lemma measurableSet_sharedSndSet (hS : MeasurableSet S) :
    MeasurableSet (sharedSndSet S) := by
  have h1 : Measurable fun r : β × α × α ↦ (r.2.1, r.1) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have h2 : Measurable fun r : β × α × α ↦ (r.2.2, r.1) :=
    (measurable_snd.comp measurable_snd).prodMk measurable_fst
  exact (h1 hS).inter (h2 hS)

omit [Nonempty β] in
lemma prod_sharedFstSet_le [SFinite μX] [IsFiniteMeasure μY] (hS : MeasurableSet S)
    (hsliceY : ∀ x, (μY (Prod.mk x ⁻¹' S)).toReal ≤ qbar) :
    (μX.prod (μY.prod μY)) (sharedFstSet S) ≤ ENNReal.ofReal qbar * (μX.prod μY) S := by
  have hq0 : 0 ≤ qbar := le_trans ENNReal.toReal_nonneg (hsliceY (Classical.arbitrary α))
  have hle : ∀ x, μY (Prod.mk x ⁻¹' S) ≤ ENNReal.ofReal qbar := fun x ↦
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μY _) hq0).2 (hsliceY x)
  have hslice : ∀ x : α, (μY.prod μY) (Prod.mk x ⁻¹' sharedFstSet S)
      = μY (Prod.mk x ⁻¹' S) * μY (Prod.mk x ⁻¹' S) := by
    intro x
    have hset : Prod.mk x ⁻¹' sharedFstSet S = (Prod.mk x ⁻¹' S) ×ˢ (Prod.mk x ⁻¹' S) := by
      ext u; simp [sharedFstSet, Set.mem_prod]
    rw [hset, Measure.prod_prod]
  rw [Measure.prod_apply (measurableSet_sharedFstSet hS)]
  simp_rw [hslice]
  calc ∫⁻ x, μY (Prod.mk x ⁻¹' S) * μY (Prod.mk x ⁻¹' S) ∂μX
      ≤ ∫⁻ x, ENNReal.ofReal qbar * μY (Prod.mk x ⁻¹' S) ∂μX :=
        lintegral_mono fun x ↦ mul_le_mul' (hle x) le_rfl
    _ = ENNReal.ofReal qbar * ∫⁻ x, μY (Prod.mk x ⁻¹' S) ∂μX :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal qbar * (μX.prod μY) S := by rw [Measure.prod_apply hS]

omit [Nonempty α] in
lemma prod_sharedSndSet_le [IsFiniteMeasure μX] [SFinite μY] (hS : MeasurableSet S)
    (hsliceX : ∀ y, (μX ((fun x ↦ (x, y)) ⁻¹' S)).toReal ≤ qbar) :
    (μY.prod (μX.prod μX)) (sharedSndSet S) ≤ ENNReal.ofReal qbar * (μX.prod μY) S := by
  have hq0 : 0 ≤ qbar := le_trans ENNReal.toReal_nonneg (hsliceX (Classical.arbitrary β))
  have hle : ∀ y, μX ((fun x ↦ (x, y)) ⁻¹' S) ≤ ENNReal.ofReal qbar := fun y ↦
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μX _) hq0).2 (hsliceX y)
  have hslice : ∀ y : β, (μX.prod μX) (Prod.mk y ⁻¹' sharedSndSet S)
      = μX ((fun x ↦ (x, y)) ⁻¹' S) * μX ((fun x ↦ (x, y)) ⁻¹' S) := by
    intro y
    have hset : Prod.mk y ⁻¹' sharedSndSet S
        = ((fun x ↦ (x, y)) ⁻¹' S) ×ˢ ((fun x ↦ (x, y)) ⁻¹' S) := by
      ext u; simp [sharedSndSet, Set.mem_prod]
    rw [hset, Measure.prod_prod]
  rw [Measure.prod_apply (measurableSet_sharedSndSet hS)]
  simp_rw [hslice]
  calc ∫⁻ y, μX ((fun x ↦ (x, y)) ⁻¹' S) * μX ((fun x ↦ (x, y)) ⁻¹' S) ∂μY
      ≤ ∫⁻ y, ENNReal.ofReal qbar * μX ((fun x ↦ (x, y)) ⁻¹' S) ∂μY :=
        lintegral_mono fun y ↦ mul_le_mul' (hle y) le_rfl
    _ = ENNReal.ofReal qbar * ∫⁻ y, μX ((fun x ↦ (x, y)) ⁻¹' S) ∂μY :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal qbar * (μX.prod μY) S := by rw [Measure.prod_apply_symm hS]

variable (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j)) (hS : MeasurableSet S)
  (hIndep : iIndepFun (codebookFamily X Y) μ)
  (hXlaw : ∀ i, μ.map (X i) = μX) (hYlaw : ∀ j, μ.map (Y j) = μY)

include hX hY hIndep hXlaw hYlaw in
lemma map_codewordTripleFst [IsProbabilityMeasure μ] (i : Fin M₁) {j j' : Fin M₂} (hj : j ≠ j') :
    μ.map (fun ω ↦ (X i ω, Y j ω, Y j' ω)) = μX.prod (μY.prod μY) := by
  have hmeas := measurable_codebookFamily hX hY
  have hpair : IndepFun (fun ω ↦ (codebookFamily X Y (Sum.inr j) ω,
      codebookFamily X Y (Sum.inr j') ω)) (codebookFamily X Y (Sum.inl i)) μ :=
    hIndep.indepFun_prodMk hmeas (Sum.inr j) (Sum.inr j') (Sum.inl i) (by simp) (by simp)
  have h1 : IndepFun (X i) (fun ω ↦ (Y j ω, Y j' ω)) μ :=
    hpair.symm.comp (φ := fun r : α × β ↦ r.1)
      (ψ := fun r : (α × β) × (α × β) ↦ (r.1.2, r.2.2)) measurable_fst
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  have h2 : μ.map (fun ω ↦ (Y j ω, Y j' ω)) = μY.prod μY := by
    have hind : IndepFun (Y j) (Y j') μ :=
      (hIndep.indepFun (i := Sum.inr j) (j := Sum.inr j') (by simpa using hj)).comp
        measurable_snd measurable_snd
    rw [hind.map_prod_eq_prod_map_map (hY j).aemeasurable (hY j').aemeasurable, hYlaw j, hYlaw j']
  rw [h1.map_prod_eq_prod_map_map (hX i).aemeasurable ((hY j).prodMk (hY j')).aemeasurable,
    hXlaw i, h2]

include hX hY hIndep hXlaw hYlaw in
lemma map_codewordTripleSnd [IsProbabilityMeasure μ] {i i' : Fin M₁} (hi : i ≠ i')
    (j : Fin M₂) :
    μ.map (fun ω ↦ (Y j ω, X i ω, X i' ω)) = μY.prod (μX.prod μX) := by
  have hmeas := measurable_codebookFamily hX hY
  have hpair : IndepFun (fun ω ↦ (codebookFamily X Y (Sum.inl i) ω,
      codebookFamily X Y (Sum.inl i') ω)) (codebookFamily X Y (Sum.inr j)) μ :=
    hIndep.indepFun_prodMk hmeas (Sum.inl i) (Sum.inl i') (Sum.inr j) (by simp) (by simp)
  have h1 : IndepFun (Y j) (fun ω ↦ (X i ω, X i' ω)) μ :=
    hpair.symm.comp (φ := fun r : α × β ↦ r.2)
      (ψ := fun r : (α × β) × (α × β) ↦ (r.1.1, r.2.1)) measurable_snd
      ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  have h2 : μ.map (fun ω ↦ (X i ω, X i' ω)) = μX.prod μX := by
    have hind : IndepFun (X i) (X i') μ :=
      (hIndep.indepFun (i := Sum.inl i) (j := Sum.inl i') (by simpa using hi)).comp
        measurable_fst measurable_fst
    rw [hind.map_prod_eq_prod_map_map (hX i).aemeasurable (hX i').aemeasurable, hXlaw i, hXlaw i']
  rw [h1.map_prod_eq_prod_map_map (hY j).aemeasurable ((hX i).prodMk (hX i')).aemeasurable,
    hYlaw j, h2]

include hX hY hS hIndep hXlaw hYlaw in
lemma integral_pairIndicator_mul_sharedFst_le [IsProbabilityMeasure μ]
    (hsliceY : ∀ x, (μY (Prod.mk x ⁻¹' S)).toReal ≤ qbar)
    (i : Fin M₁) {j j' : Fin M₂} (hj : j ≠ j') :
    μ[pairIndicator X Y S (i, j) * pairIndicator X Y S (i, j')] ≤ qbar * pairProb μX μY S := by
  have hμX : IsProbabilityMeasure μX := by
    rw [← hXlaw i]; exact Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hμY : IsProbabilityMeasure μY := by
    rw [← hYlaw j]; exact Measure.isProbabilityMeasure_map (hY j).aemeasurable
  have hq0 : 0 ≤ qbar := le_trans ENNReal.toReal_nonneg (hsliceY (Classical.arbitrary α))
  have hTmeas : Measurable fun ω ↦ (X i ω, Y j ω, Y j' ω) := (hX i).prodMk ((hY j).prodMk (hY j'))
  have hG : MeasurableSet (sharedFstSet S) := measurableSet_sharedFstSet hS
  have hprod : pairIndicator X Y S (i, j) * pairIndicator X Y S (i, j')
      = ((fun ω ↦ (X i ω, Y j ω, Y j' ω)) ⁻¹' sharedFstSet S).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases h1 : (X i ω, Y j ω) ∈ S <;> by_cases h2 : (X i ω, Y j' ω) ∈ S <;>
      simp [pairIndicator, sharedFstSet, h1, h2]
  rw [hprod, integral_indicator_one (hTmeas hG), measureReal_def,
    ← Measure.map_apply hTmeas hG, map_codewordTripleFst hX hY hIndep hXlaw hYlaw i hj]
  calc ((μX.prod (μY.prod μY)) (sharedFstSet S)).toReal
      ≤ (ENNReal.ofReal qbar * (μX.prod μY) S).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (prod_sharedFstSet_le hS hsliceY)
    _ = qbar * pairProb μX μY S := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0, pairProb]

include hX hY hS hIndep hXlaw hYlaw in
lemma integral_pairIndicator_mul_sharedSnd_le [IsProbabilityMeasure μ]
    (hsliceX : ∀ y, (μX ((fun x ↦ (x, y)) ⁻¹' S)).toReal ≤ qbar)
    {i i' : Fin M₁} (hi : i ≠ i') (j : Fin M₂) :
    μ[pairIndicator X Y S (i, j) * pairIndicator X Y S (i', j)] ≤ qbar * pairProb μX μY S := by
  have hμX : IsProbabilityMeasure μX := by
    rw [← hXlaw i]; exact Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have hμY : IsProbabilityMeasure μY := by
    rw [← hYlaw j]; exact Measure.isProbabilityMeasure_map (hY j).aemeasurable
  have hq0 : 0 ≤ qbar := le_trans ENNReal.toReal_nonneg (hsliceX (Classical.arbitrary β))
  have hTmeas : Measurable fun ω ↦ (Y j ω, X i ω, X i' ω) := (hY j).prodMk ((hX i).prodMk (hX i'))
  have hG : MeasurableSet (sharedSndSet S) := measurableSet_sharedSndSet hS
  have hprod : pairIndicator X Y S (i, j) * pairIndicator X Y S (i', j)
      = ((fun ω ↦ (Y j ω, X i ω, X i' ω)) ⁻¹' sharedSndSet S).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases h1 : (X i ω, Y j ω) ∈ S <;> by_cases h2 : (X i' ω, Y j ω) ∈ S <;>
      simp [pairIndicator, sharedSndSet, h1, h2]
  rw [hprod, integral_indicator_one (hTmeas hG), measureReal_def,
    ← Measure.map_apply hTmeas hG, map_codewordTripleSnd hX hY hIndep hXlaw hYlaw hi j]
  calc ((μY.prod (μX.prod μX)) (sharedSndSet S)).toReal
      ≤ (ENNReal.ofReal qbar * (μX.prod μY) S).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (prod_sharedSndSet_le hS hsliceX)
    _ = qbar * pairProb μX μY S := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0, pairProb]

include hX hY hS hIndep hXlaw hYlaw in
/-- Covariance of two codeword pairs sharing exactly one index, under the two uniform slice
bounds.  Each bound constrains one coordinate of `S` only, so both are needed: the pairs sharing
their first index are governed by the `β`-slices and those sharing their second index by the
`α`-slices.

@audit:ok -/
theorem covariance_pairIndicator_shared_le [IsProbabilityMeasure μ]
    (hsliceY : ∀ x, (μY (Prod.mk x ⁻¹' S)).toReal ≤ qbar)
    (hsliceX : ∀ y, (μX ((fun x ↦ (x, y)) ⁻¹' S)).toReal ≤ qbar)
    {p q : Fin M₁ × Fin M₂}
    (hpq : (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ (p.1 ≠ q.1 ∧ p.2 = q.2)) :
    cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] ≤ qbar * pairProb μX μY S := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  have hp2 : MemLp (pairIndicator X Y S (i, j)) 2 μ := memLp_pairIndicator hX hY hS _
  have hq2 : MemLp (pairIndicator X Y S (i', j')) 2 μ := memLp_pairIndicator hX hY hS _
  have hmul : μ[pairIndicator X Y S (i, j) * pairIndicator X Y S (i', j')]
      ≤ qbar * pairProb μX μY S := by
    rcases hpq with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
    · replace hfst : i = i' := hfst
      replace hsnd : j ≠ j' := hsnd
      subst hfst
      exact integral_pairIndicator_mul_sharedFst_le hX hY hS hIndep hXlaw hYlaw hsliceY i hsnd
    · replace hfst : i ≠ i' := hfst
      replace hsnd : j = j' := hsnd
      subst hsnd
      exact integral_pairIndicator_mul_sharedSnd_le hX hY hS hIndep hXlaw hYlaw hsliceX hfst j
  have hnn : 0 ≤ μ[pairIndicator X Y S (i, j)] * μ[pairIndicator X Y S (i', j')] :=
    mul_nonneg (integral_nonneg fun ω ↦ pairIndicator_nonneg _ ω)
      (integral_nonneg fun ω ↦ pairIndicator_nonneg _ ω)
  rw [covariance_eq_sub hp2 hq2]
  linarith

include hX hY hS hIndep hXlaw hYlaw in
/-- Sharpened variance bound: the diagonal terms contribute `M₁ M₂ p`, and the pairs sharing one
index contribute at most `qbar * p` each.

@audit:ok -/
theorem variance_pairCount_le' [IsProbabilityMeasure μ]
    (hsliceY : ∀ x, (μY (Prod.mk x ⁻¹' S)).toReal ≤ qbar)
    (hsliceX : ∀ y, (μX ((fun x ↦ (x, y)) ⁻¹' S)).toReal ≤ qbar) :
    Var[pairCount X Y S; μ]
      ≤ M₁ * M₂ * pairProb μX μY S
        + M₁ * M₂ * (M₁ + M₂) * (qbar * pairProb μX μY S) := by
  have hpnn : 0 ≤ pairProb μX μY S := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ qbar := le_trans ENNReal.toReal_nonneg (hsliceY (Classical.arbitrary α))
  have hqp : 0 ≤ qbar * pairProb μX μY S := mul_nonneg hq0 hpnn
  have hvar : Var[pairCount X Y S; μ]
      = ∑ p : Fin M₁ × Fin M₂, ∑ q : Fin M₁ × Fin M₂,
          cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] :=
    variance_fun_sum fun p ↦ memLp_pairIndicator hX hY hS p
  have key : ∀ p : Fin M₁ × Fin M₂,
      ∑ q : Fin M₁ × Fin M₂, cov[pairIndicator X Y S p, pairIndicator X Y S q; μ]
        ≤ pairProb μX μY S + (M₁ + M₂) * (qbar * pairProb μX μY S) := by
    intro p
    have hbound : ∀ q : Fin M₁ × Fin M₂,
        cov[pairIndicator X Y S p, pairIndicator X Y S q; μ]
          ≤ (if q = p then pairProb μX μY S else 0)
            + ((if q.1 = p.1 then qbar * pairProb μX μY S else 0)
              + (if q.2 = p.2 then qbar * pairProb μX μY S else 0)) := by
      intro q
      by_cases h1 : q.1 = p.1 <;> by_cases h2 : q.2 = p.2
      · rw [if_pos (Prod.ext h1 h2 : q = p), if_pos h1, if_pos h2]
        have hle := covariance_pairIndicator_le hX hY hS hIndep hXlaw hYlaw p q
        linarith
      · have hne : q ≠ p := fun h ↦ h2 (by rw [h])
        rw [if_neg hne, if_pos h1, if_neg h2]
        have hle := covariance_pairIndicator_shared_le hX hY hS hIndep hXlaw hYlaw hsliceY hsliceX
          (Or.inl ⟨h1.symm, Ne.symm h2⟩)
        linarith
      · have hne : q ≠ p := fun h ↦ h1 (by rw [h])
        rw [if_neg hne, if_neg h1, if_pos h2]
        have hle := covariance_pairIndicator_shared_le hX hY hS hIndep hXlaw hYlaw hsliceY hsliceX
          (Or.inr ⟨Ne.symm h1, h2.symm⟩)
        linarith
      · have hne : q ≠ p := fun h ↦ h1 (by rw [h])
        rw [if_neg hne, if_neg h1, if_neg h2]
        have hzero := covariance_pairIndicator_eq_zero hX hY hS hIndep (Ne.symm h1) (Ne.symm h2)
        linarith
    calc ∑ q : Fin M₁ × Fin M₂, cov[pairIndicator X Y S p, pairIndicator X Y S q; μ]
        ≤ ∑ q : Fin M₁ × Fin M₂, ((if q = p then pairProb μX μY S else 0)
            + ((if q.1 = p.1 then qbar * pairProb μX μY S else 0)
              + (if q.2 = p.2 then qbar * pairProb μX μY S else 0))) :=
          Finset.sum_le_sum fun q _ ↦ hbound q
      _ = pairProb μX μY S
            + (M₂ * (qbar * pairProb μX μY S) + M₁ * (qbar * pairProb μX μY S)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_fst_eq, sum_ite_snd_eq]
          simp
      _ = pairProb μX μY S + (M₁ + M₂) * (qbar * pairProb μX μY S) := by ring
  calc Var[pairCount X Y S; μ]
      = ∑ p : Fin M₁ × Fin M₂, ∑ q : Fin M₁ × Fin M₂,
          cov[pairIndicator X Y S p, pairIndicator X Y S q; μ] := hvar
    _ ≤ ∑ _p : Fin M₁ × Fin M₂,
          (pairProb μX μY S + (M₁ + M₂) * (qbar * pairProb μX μY S)) :=
        Finset.sum_le_sum fun p _ ↦ key p
    _ = M₁ * M₂ * pairProb μX μY S
          + M₁ * M₂ * (M₁ + M₂) * (qbar * pairProb μX μY S) := by
        simp [Finset.card_univ]
        ring

include hX hY hS hIndep hXlaw hYlaw in
/-- Sharpened second-moment estimate behind Marton's mutual covering lemma.  When every
conditional slice of `S` has mass at most `qbar`, the probability that no codeword pair lands
in `S` splits into a term governed by the product `M₁ M₂` and two terms carrying `qbar`.

@audit:ok -/
theorem meas_pairCount_eq_zero_le' [IsProbabilityMeasure μ]
    (hsliceY : ∀ x, (μY (Prod.mk x ⁻¹' S)).toReal ≤ qbar)
    (hsliceX : ∀ y, (μX ((fun x ↦ (x, y)) ⁻¹' S)).toReal ≤ qbar)
    (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) (hp : 0 < pairProb μX μY S) :
    μ {ω | pairCount X Y S ω = 0}
      ≤ ENNReal.ofReal (1 / (M₁ * M₂ * pairProb μX μY S)
          + qbar / (M₁ * pairProb μX μY S) + qbar / (M₂ * pairProb μX μY S)) := by
  have hM₁' : (0 : ℝ) < M₁ := by exact_mod_cast Nat.pos_of_ne_zero hM₁
  have hM₂' : (0 : ℝ) < M₂ := by exact_mod_cast Nat.pos_of_ne_zero hM₂
  have hc0 : 0 < (M₁ : ℝ) * M₂ * pairProb μX μY S := by positivity
  have hE : μ[pairCount X Y S] = (M₁ : ℝ) * M₂ * pairProb μX μY S :=
    integral_pairCount hX hY hS hIndep hXlaw hYlaw
  have hsub : {ω | pairCount X Y S ω = 0}
      ⊆ {ω | (M₁ : ℝ) * M₂ * pairProb μX μY S ≤ |pairCount X Y S ω - μ[pairCount X Y S]|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω, hE, zero_sub, abs_neg, abs_of_pos hc0]
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_variance_div_sq (memLp_pairCount hX hY hS) hc0).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hRHS : 1 / ((M₁ : ℝ) * M₂ * pairProb μX μY S)
        + qbar / ((M₁ : ℝ) * pairProb μX μY S) + qbar / ((M₂ : ℝ) * pairProb μX μY S)
      = ((M₁ : ℝ) * M₂ * pairProb μX μY S
          + (M₁ : ℝ) * M₂ * ((M₁ : ℝ) + M₂) * (qbar * pairProb μX μY S))
        / ((M₁ : ℝ) * M₂ * pairProb μX μY S) ^ 2 := by
    field_simp
    ring
  rw [hRHS]
  gcongr
  exact variance_pairCount_le' hX hY hS hIndep hXlaw hYlaw hsliceY hsliceX

end SharpVariance

section CanonicalAmbient

/-! ### A canonical ambient realizing the hypotheses

`meas_pairCount_eq_zero_le` is stated over an abstract probability space.  This section
exhibits the i.i.d. codebook ambient on which its hypotheses hold, so that the abstract
statement is known to be non-vacuous and downstream users have a template to instantiate. -/

/-- Law of one entry of the interleaved codebook family on the canonical ambient: an
`α`-codeword carries `μX` in its first coordinate and a point mass in the padded one. -/
noncomputable def ambientFactor (μX : Measure α) (μY : Measure β) (M₁ M₂ : ℕ) :
    Fin M₁ ⊕ Fin M₂ → Measure (α × β)
  | Sum.inl _ => μX.prod (Measure.dirac (Classical.arbitrary β))
  | Sum.inr _ => (Measure.dirac (Classical.arbitrary α)).prod μY

instance instIsProbabilityMeasureAmbientFactor [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (k : Fin M₁ ⊕ Fin M₂) : IsProbabilityMeasure (ambientFactor μX μY M₁ M₂ k) := by
  cases k with
  | inl i => exact inferInstanceAs (IsProbabilityMeasure (μX.prod _))
  | inr j => exact inferInstanceAs (IsProbabilityMeasure ((Measure.dirac _).prod μY))

/-- Canonical ambient measure: the `M₁ + M₂` codewords are drawn independently. -/
noncomputable def ambient (μX : Measure α) (μY : Measure β) (M₁ M₂ : ℕ) :
    Measure (Fin M₁ ⊕ Fin M₂ → α × β) :=
  Measure.pi (ambientFactor μX μY M₁ M₂)

instance instIsProbabilityMeasureAmbient [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] :
    IsProbabilityMeasure (ambient μX μY M₁ M₂) := by
  rw [ambient]; infer_instance

/-- First codebook read off the canonical ambient. -/
def ambientX (M₁ M₂ : ℕ) (i : Fin M₁) : (Fin M₁ ⊕ Fin M₂ → α × β) → α := fun ω ↦ (ω (Sum.inl i)).1

/-- Second codebook read off the canonical ambient. -/
def ambientY (M₁ M₂ : ℕ) (j : Fin M₂) : (Fin M₁ ⊕ Fin M₂ → α × β) → β := fun ω ↦ (ω (Sum.inr j)).2

/-- The padding map attached to one index of the interleaved family. -/
noncomputable def ambientPad (M₁ M₂ : ℕ) : Fin M₁ ⊕ Fin M₂ → (α × β) → α × β
  | Sum.inl _ => fun r ↦ (r.1, Classical.arbitrary β)
  | Sum.inr _ => fun r ↦ (Classical.arbitrary α, r.2)

omit [Nonempty α] [Nonempty β] in
lemma measurable_ambientX (i : Fin M₁) : Measurable (ambientX (α := α) (β := β) M₁ M₂ i) :=
  measurable_fst.comp (measurable_pi_apply _)

omit [Nonempty α] [Nonempty β] in
lemma measurable_ambientY (j : Fin M₂) : Measurable (ambientY (α := α) (β := β) M₁ M₂ j) :=
  measurable_snd.comp (measurable_pi_apply _)

lemma measurable_ambientPad (k : Fin M₁ ⊕ Fin M₂) :
    Measurable (ambientPad (α := α) (β := β) M₁ M₂ k) := by
  cases k with
  | inl i => exact measurable_fst.prodMk measurable_const
  | inr j => exact measurable_const.prodMk measurable_snd

lemma iIndepFun_codebookFamily_ambient [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] :
    iIndepFun (codebookFamily (ambientX (α := α) (β := β) M₁ M₂) (ambientY M₁ M₂))
      (ambient μX μY M₁ M₂) := by
  have hpi : iIndepFun (fun (k : Fin M₁ ⊕ Fin M₂) (ω : Fin M₁ ⊕ Fin M₂ → α × β) ↦ ω k)
      (ambient μX μY M₁ M₂) := by
    rw [ambient]
    exact iIndepFun_pi fun _ ↦ aemeasurable_id
  have h := hpi.comp (ambientPad M₁ M₂) measurable_ambientPad
  have hfun : (fun k ↦ ambientPad M₁ M₂ k ∘ fun ω : Fin M₁ ⊕ Fin M₂ → α × β ↦ ω k)
      = codebookFamily (ambientX (α := α) (β := β) M₁ M₂) (ambientY M₁ M₂) := by
    funext k
    cases k <;> rfl
  rwa [hfun] at h

lemma map_ambientX [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] (i : Fin M₁) :
    (ambient μX μY M₁ M₂).map (ambientX (β := β) M₁ M₂ i) = μX := by
  have heval : (ambient μX μY M₁ M₂).map (fun ω ↦ ω (Sum.inl i))
      = μX.prod (Measure.dirac (Classical.arbitrary β)) := by
    rw [ambient]
    exact (measurePreserving_eval (ambientFactor μX μY M₁ M₂) (Sum.inl i)).map_eq
  rw [show ambientX (β := β) M₁ M₂ i = Prod.fst ∘ fun ω ↦ ω (Sum.inl i) from rfl,
    ← Measure.map_map measurable_fst (measurable_pi_apply _), heval, Measure.map_fst_prod]
  simp

lemma map_ambientY [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] (j : Fin M₂) :
    (ambient μX μY M₁ M₂).map (ambientY (α := α) M₁ M₂ j) = μY := by
  have heval : (ambient μX μY M₁ M₂).map (fun ω ↦ ω (Sum.inr j))
      = (Measure.dirac (Classical.arbitrary α)).prod μY := by
    rw [ambient]
    exact (measurePreserving_eval (ambientFactor μX μY M₁ M₂) (Sum.inr j)).map_eq
  rw [show ambientY (α := α) M₁ M₂ j = Prod.snd ∘ fun ω ↦ ω (Sum.inr j) from rfl,
    ← Measure.map_map measurable_snd (measurable_pi_apply _), heval, Measure.map_snd_prod]
  simp

/-- The mutual covering estimate on the canonical i.i.d. codebook ambient. -/
theorem meas_pairCount_ambient_eq_zero_le [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hS : MeasurableSet S) (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) (hp : 0 < pairProb μX μY S) :
    (ambient μX μY M₁ M₂)
        {ω | pairCount (ambientX (β := β) M₁ M₂) (ambientY (α := α) M₁ M₂) S ω = 0}
      ≤ ENNReal.ofReal ((M₁ + M₂) / (M₁ * M₂ * pairProb μX μY S)) :=
  meas_pairCount_eq_zero_le measurable_ambientX measurable_ambientY hS
    iIndepFun_codebookFamily_ambient map_ambientX map_ambientY hM₁ hM₂ hp

end CanonicalAmbient

end InformationTheory.Shannon.BroadcastChannel.Marton
