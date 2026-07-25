import InformationTheory.Shannon.AEP.Rate
import InformationTheory.Shannon.BroadcastChannel.Marton.MutualCovering
import InformationTheory.Shannon.BroadcastChannel.Marton.Setup
import InformationTheory.Shannon.ChannelCoding.Achievability.Core
import InformationTheory.Shannon.RateDistortion.AchievabilityJointTypicalEncoder
import InformationTheory.Shannon.RateDistortion.AchievabilityUnconditional
import InformationTheory.Shannon.SlepianWolf.ConditionalTypicalSlice

/-!
# Marton's mutual covering lemma

The second-moment core of `Marton.MutualCovering` bounds the probability that none of the
`M₁ * M₂` codeword pairs lands in an abstract measurable set `S`, given a uniform bound
`qbar` on the conditional slices of `S`.  This file instantiates that core at the jointly
typical set of a pair of i.i.d. sequences and turns the resulting estimate into the covering
statement used by Marton's inner bound: as soon as the two subcodebook rates add up to more
than `I(V₁; V₂)`, a jointly typical pair exists with probability tending to one.

The same estimate is available at the jointly *strongly* typical set, whose radius has to be
amplified by `coveringBandConst` to reach the weak bands the slice estimates are stated at.  That
reading is the one the encoder's selection rule consumes, because only a strongly typical selected
pair pins the empirical type of the transmitted words.

## Main definitions

* `codebookEmbed` — a pair of codebooks read as one padded family of codewords, exhibiting the
  product of two codebook ensembles as the canonical ambient of `Marton.MutualCovering`.
* `coveringBandConst` and `martonCoveringBandConst` — the Lipschitz factor converting the type
  radius of a jointly strongly typical pair into the weak bands of the two blocks and of their
  joint sequence.

## Main statements

* `mem_jointlyTypicalSet_swap` — the jointly typical set is symmetric in its two blocks.
* `measureReal_jointlyTypicalFiber_le` and `measureReal_jointlyTypicalFiberSnd_le` — both
  families of conditional slices of the jointly typical set have mass at most
  `exp(-n (I - 3ε))`.
* `meas_codebook_no_jointlyTypicalPair_lt` and `meas_codebook_no_jointStronglyTypicalPair_lt` —
  mutual covering for a pair of i.i.d. codebook ensembles, stated over abstract alphabets, at the
  weakly and at the strongly typical set.
* `marton_mutual_covering` and `marton_strong_mutual_covering` — the same statements for the
  auxiliary variables of Marton's inner bound, with the covering threshold read as `I(V₁; V₂)`.
* `meas_marton_codebook_no_jointlyTypicalPair_lt` and
  `meas_marton_codebook_no_jointStronglyTypicalPair_lt` — the same two bounds with the typicality
  parameter left as a hypothesis, so that a consumer may choose one radius meeting the covering
  conditions together with those of the decoding analysis.
* `marton_mutual_covering_of_indepAux` and `marton_strong_mutual_covering_of_indepAux` — the
  degenerate regime of independent auxiliary variables, certifying that the hypotheses of the two
  covering statements are jointly satisfiable.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! ### Symmetry of the jointly typical set -/

section TypicalSwap

variable {Ω : Type*} [MeasurableSpace Ω]
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
  {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B]
    [MeasurableSingletonClass B]

lemma measureReal_map_jointSequence_swap
    (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) (a : A) (b : B) :
    (μ.map (jointSequence Ys Xs 0)).real {(b, a)}
      = (μ.map (jointSequence Xs Ys 0)).real {(a, b)} := by
  have hZ : Measurable (jointSequence Ys Xs 0) := measurable_jointSequence Ys Xs hYs hXs 0
  have hZ' : Measurable (jointSequence Xs Ys 0) := measurable_jointSequence Xs Ys hXs hYs 0
  have hpre : jointSequence Ys Xs 0 ⁻¹' ({(b, a)} : Set (B × A))
      = jointSequence Xs Ys 0 ⁻¹' ({(a, b)} : Set (A × B)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, jointSequence_apply, Prod.mk.injEq]
    exact and_comm
  rw [Measure.real, Measure.real, Measure.map_apply hZ (measurableSet_singleton _),
    Measure.map_apply hZ' (measurableSet_singleton _), hpre]

lemma entropy_jointSequence_swap
    (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) :
    entropy μ (jointSequence Ys Xs 0) = entropy μ (jointSequence Xs Ys 0) := by
  refine Fintype.sum_equiv (Equiv.prodComm B A) _ _ ?_
  rintro ⟨b, a⟩
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [measureReal_map_jointSequence_swap μ Xs Ys hXs hYs a b]

/-- The jointly typical set is symmetric in its two blocks: a pair `(x, y)` is jointly typical for
`(Xs, Ys)` exactly when the swapped pair `(y, x)` is jointly typical for `(Ys, Xs)`.  Both the
per-letter log-likelihood and the joint entropy are invariant under the swap, so the three bands
defining membership are exchanged rather than changed. -/
lemma mem_jointlyTypicalSet_swap
    (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (n : ℕ) (ε : ℝ) (x : Fin n → A) (y : Fin n → B) :
    (y, x) ∈ jointlyTypicalSet μ Ys Xs n ε ↔ (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε := by
  have hjoint : (fun i ↦ (y i, x i)) ∈ typicalSet μ (jointSequence Ys Xs) n ε
      ↔ (fun i ↦ (x i, y i)) ∈ typicalSet μ (jointSequence Xs Ys) n ε := by
    have hterm : ∀ i : Fin n, pmfLog μ (jointSequence Ys Xs) (y i, x i)
        = pmfLog μ (jointSequence Xs Ys) (x i, y i) := by
      intro i
      unfold pmfLog
      rw [measureReal_map_jointSequence_swap μ Xs Ys hXs hYs (x i) (y i)]
    rw [mem_typicalSet_iff, mem_typicalSet_iff, entropy_jointSequence_swap μ Xs Ys hXs hYs,
      Finset.sum_congr rfl fun i _ ↦ hterm i]
  rw [mem_jointlyTypicalSet_iff, mem_jointlyTypicalSet_iff]
  constructor
  · rintro ⟨hy, hx, hz⟩
    exact ⟨hx, hy, hjoint.mp hz⟩
  · rintro ⟨hx, hy, hz⟩
    exact ⟨hy, hx, hjoint.mpr hz⟩

end TypicalSwap

/-! ### Mass of the conditional slices -/

section SliceMass

variable {Ω : Type*} [MeasurableSpace Ω]
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
  {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B]
    [MeasurableSingletonClass B]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
  (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
  (hindepX : iIndepFun (fun i ↦ Xs i) μ) (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
  (hindepY : iIndepFun (fun i ↦ Ys i) μ) (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
  (hindepZ : iIndepFun (fun i ↦ jointSequence Xs Ys i) μ)
  (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
  (hposX : ∀ x : A, 0 < (μ.map (Xs 0)).real {x})
  (hposY : ∀ y : B, 0 < (μ.map (Ys 0)).real {y})
  (hposZ : ∀ p : A × B, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})

include hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ hposX hposY hposZ in
/-- Uniform bound on the conditional slices of the jointly typical set taken along the first
block: whatever the second word `y`, the i.i.d. law of the first sequence gives the set of words
jointly typical with `y` mass at most `exp(-n (I(X; Y) - 3ε))`, where `I(X; Y)` is read as
`H(X) + H(Y) - H(X, Y)`. -/
lemma measureReal_jointlyTypicalFiber_le (n : ℕ) {ε : ℝ} (y : Fin n → B) :
    (μ.map (jointRV Xs n)).real ((fun x ↦ (x, y)) ⁻¹' jointlyTypicalSet μ Xs Ys n ε)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
          - entropy μ (Ys 0) + 3 * ε)) := by
  classical
  have hset : (fun x ↦ (x, y)) ⁻¹' jointlyTypicalSet μ Xs Ys n ε
      = conditionalTypicalSlice μ Xs Ys n ε y := rfl
  set F : Finset (Fin n → A) :=
    (conditionalTypicalSlice μ Xs Ys n ε y).toFinite.toFinset with hF_def
  have hcoe : (F : Set (Fin n → A)) = conditionalTypicalSlice μ Xs Ys n ε y :=
    (Set.toFinite _).coe_toFinset
  have hsum : (μ.map (jointRV Xs n)).real (conditionalTypicalSlice μ Xs Ys n ε y)
      = ∑ x ∈ F, (μ.map (jointRV Xs n)).real {x} := by
    rw [← hcoe, ← sum_measureReal_singleton (μ := μ.map (jointRV Xs n)) F]
  have heach : ∀ x ∈ F,
      (μ.map (jointRV Xs n)).real {x} ≤ Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε)) := by
    intro x hx
    have hxs : x ∈ conditionalTypicalSlice μ Xs Ys n ε y := (Set.Finite.mem_toFinset _).mp hx
    exact typicalSet_prob_le μ Xs hXs hindepX hidentX hposX n x hxs.1
  have hcard : (F.card : ℝ)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε)) :=
    conditionalTypicalSlice_card_le μ Xs Ys hXs hYs hindepY hidentY hindepZ hidentZ hposY hposZ n y
  rw [hset, hsum]
  calc ∑ x ∈ F, (μ.map (jointRV Xs n)).real {x}
      ≤ ∑ _x ∈ F, Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε)) := Finset.sum_le_sum heach
    _ = (F.card : ℝ) * Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε))
          * Real.exp (-(n : ℝ) * (entropy μ (Xs 0) - ε)) := by
        gcongr
    _ = Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
          - entropy μ (Ys 0) + 3 * ε)) := by
        rw [← Real.exp_add]
        ring_nf

include hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ hposX hposY hposZ in
/-- The mirror image of `measureReal_jointlyTypicalFiber_le`, slicing along the second block: the
same exponential bound holds for the mass the i.i.d. law of the second sequence gives to the words
jointly typical with a prescribed first word `x`.  The covering estimate needs both families,
since the second-moment argument controls the two directions of the pair count separately. -/
lemma measureReal_jointlyTypicalFiberSnd_le (n : ℕ) {ε : ℝ} (x : Fin n → A) :
    (μ.map (jointRV Ys n)).real (Prod.mk x ⁻¹' jointlyTypicalSet μ Xs Ys n ε)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
          - entropy μ (Ys 0) + 3 * ε)) := by
  have hindepZ' : iIndepFun (fun i ↦ jointSequence Ys Xs i) μ :=
    hindepZ.comp (fun _ : ℕ ↦ (Prod.swap : A × B → B × A)) fun _ ↦ measurable_swap
  have hidentZ' : ∀ i, IdentDistrib (jointSequence Ys Xs i) (jointSequence Ys Xs 0) μ μ :=
    fun i ↦ (hidentZ i).comp measurable_swap
  have hposZ' : ∀ p : B × A, 0 < (μ.map (jointSequence Ys Xs 0)).real {p} := by
    rintro ⟨b, a⟩
    rw [measureReal_map_jointSequence_swap μ Xs Ys hXs hYs a b]
    exact hposZ (a, b)
  have hset : Prod.mk x ⁻¹' jointlyTypicalSet μ Xs Ys n ε
      = (fun y ↦ (y, x)) ⁻¹' jointlyTypicalSet μ Ys Xs n ε := by
    ext y
    exact (mem_jointlyTypicalSet_swap μ Xs Ys hXs hYs n ε x y).symm
  rw [hset]
  refine (measureReal_jointlyTypicalFiber_le μ Ys Xs hYs hXs hindepY hidentY hindepX hidentX
    hindepZ' hidentZ' hposY hposX hposZ' n x).trans (le_of_eq ?_)
  rw [entropy_jointSequence_swap μ Xs Ys hXs hYs]
  congr 1
  ring

end SliceMass

/-! ### A pair of codebooks as the covering ambient -/

section CodebookAmbient

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
  [Nonempty A] [Nonempty B] {M₁ M₂ : ℕ}

omit [MeasurableSpace A] [MeasurableSpace B] [Nonempty A] [Nonempty B] in
lemma pairCount_eq_zero_iff (X : Fin M₁ → Ω → A) (Y : Fin M₂ → Ω → B) (S : Set (A × B))
    (ω : Ω) :
    pairCount X Y S ω = 0 ↔ ∀ i j, (X i ω, Y j ω) ∉ S := by
  rw [pairCount, Finset.sum_eq_zero_iff_of_nonneg fun p _ ↦ pairIndicator_nonneg p ω]
  constructor
  · intro h i j
    have hij := h (i, j) (Finset.mem_univ _)
    simpa [pairIndicator, Set.indicator_apply_eq_zero] using hij
  · rintro h ⟨i, j⟩ _
    simp [pairIndicator, h i j]

/-- A pair of codebooks read as the single padded family of codewords carried by the canonical
ambient of the second-moment estimate: the `i`-th codeword of the first codebook is padded by a
constant in the second alphabet and vice versa. -/
noncomputable def codebookEmbed (M₁ M₂ : ℕ) :
    ((Fin M₁ → A) × (Fin M₂ → B)) → (Fin M₁ ⊕ Fin M₂ → A × B) := fun c ↦
  Sum.elim (fun i ↦ (c.1 i, Classical.arbitrary B)) (fun j ↦ (Classical.arbitrary A, c.2 j))

lemma measurePreserving_codebookEmbed (μX : Measure A) (μY : Measure B)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] (M₁ M₂ : ℕ) :
    MeasurePreserving (codebookEmbed (A := A) (B := B) M₁ M₂)
      ((Measure.pi fun _ : Fin M₁ ↦ μX).prod (Measure.pi fun _ : Fin M₂ ↦ μY))
      (ambient μX μY M₁ M₂) := by
  have hfst : MeasurePreserving
      (fun c : Fin M₁ → A ↦ fun i ↦ (c i, Classical.arbitrary B))
      (Measure.pi fun _ : Fin M₁ ↦ μX)
      (Measure.pi fun i : Fin M₁ ↦ ambientFactor μX μY M₁ M₂ (Sum.inl i)) :=
    measurePreserving_pi _ _ fun _ ↦
      ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have hsnd : MeasurePreserving
      (fun c : Fin M₂ → B ↦ fun j ↦ (Classical.arbitrary A, c j))
      (Measure.pi fun _ : Fin M₂ ↦ μY)
      (Measure.pi fun j : Fin M₂ ↦ ambientFactor μX μY M₁ M₂ (Sum.inr j)) :=
    measurePreserving_pi _ _ fun _ ↦
      ⟨measurable_const.prodMk measurable_id, (Measure.dirac_prod _).symm⟩
  have hsum := measurePreserving_sumPiEquivProdPi_symm (ambientFactor μX μY M₁ M₂)
  have hcomp := hsum.comp (hfst.prod hsnd)
  have hmeas : Measurable (codebookEmbed (A := A) (B := B) M₁ M₂) := by
    refine measurable_pi_lambda _ fun k ↦ ?_
    cases k with
    | inl i => exact ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_const
    | inr j => exact measurable_const.prodMk ((measurable_pi_apply j).comp measurable_snd)
  unfold ambient
  refine hcomp.congr hmeas (Filter.Eventually.of_forall fun c ↦ ?_)
  funext k
  cases k <;> rfl

/-- The sharpened mutual covering estimate, read on a product of two independent codebook
ensembles. -/
theorem meas_codebook_no_pair_le (μX : Measure A) (μY : Measure B)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] {S : Set (A × B)} (hS : MeasurableSet S)
    {qbar : ℝ}
    (hsliceY : ∀ x, (μY (Prod.mk x ⁻¹' S)).toReal ≤ qbar)
    (hsliceX : ∀ y, (μX ((fun x ↦ (x, y)) ⁻¹' S)).toReal ≤ qbar)
    (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) (hp : 0 < pairProb μX μY S) :
    ((Measure.pi fun _ : Fin M₁ ↦ μX).prod (Measure.pi fun _ : Fin M₂ ↦ μY))
        {c | ∀ i j, (c.1 i, c.2 j) ∉ S}
      ≤ ENNReal.ofReal (1 / (M₁ * M₂ * pairProb μX μY S)
          + qbar / (M₁ * pairProb μX μY S) + qbar / (M₂ * pairProb μX μY S)) := by
  classical
  have hamb := meas_pairCount_eq_zero_le' (μ := ambient μX μY M₁ M₂)
    measurable_ambientX measurable_ambientY hS iIndepFun_codebookFamily_ambient
    map_ambientX map_ambientY hsliceY hsliceX hM₁ hM₂ hp
  have hpc : Measurable
      (pairCount (ambientX (α := A) (β := B) M₁ M₂) (ambientY (α := A) (β := B) M₁ M₂) S) :=
    Finset.measurable_sum _ fun p _ ↦
      measurable_pairIndicator measurable_ambientX measurable_ambientY hS p
  have hT : MeasurableSet
      {ω | pairCount (ambientX (α := A) (β := B) M₁ M₂) (ambientY (α := A) (β := B) M₁ M₂) S ω
        = 0} := hpc (measurableSet_singleton 0)
  have hset : {c : (Fin M₁ → A) × (Fin M₂ → B) | ∀ i j, (c.1 i, c.2 j) ∉ S}
      = codebookEmbed M₁ M₂ ⁻¹'
          {ω | pairCount (ambientX (α := A) (β := B) M₁ M₂)
            (ambientY (α := A) (β := B) M₁ M₂) S ω = 0} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_preimage, pairCount_eq_zero_iff]
    rfl
  rw [hset, (measurePreserving_codebookEmbed μX μY M₁ M₂).measure_preimage hT.nullMeasurableSet]
  exact hamb

end CodebookAmbient

/-! ### The block law of an i.i.d. sequence -/

section BlockLaw

variable {Ω : Type*} [MeasurableSpace Ω]
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A]

lemma map_jointRV_eq_pi (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → A)
    (hXs : ∀ i, Measurable (Xs i)) (hindep : iIndepFun (fun i ↦ Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (n : ℕ) :
    μ.map (jointRV Xs n) = Measure.pi fun _ : Fin n ↦ μ.map (Xs 0) := by
  have hfin : iIndepFun (fun i : Fin n ↦ Xs i.val) μ := hindep.precomp Fin.val_injective
  have hpi : μ.map (jointRV Xs n) = Measure.pi fun i : Fin n ↦ μ.map (Xs i.val) :=
    (iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦ (hXs i.val).aemeasurable).mp hfin
  have hmarg : (fun i : Fin n ↦ μ.map (Xs i.val)) = fun _ : Fin n ↦ μ.map (Xs 0) := by
    funext i
    exact (hident i.val).map_eq
  rw [hpi, hmarg]

end BlockLaw

/-! ### Tail estimates for the three Chebyshev terms -/

section Tail

private lemma exists_forall_mul_exp_lt {c K η : ℝ} (hc : 0 < c) (hK : 0 < K) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * Real.exp (-((n : ℝ) * c)) < η := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((-Real.log (η / K)) / c)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 : (-Real.log (η / K)) / c < (n : ℝ) :=
    lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
  rw [div_lt_iff₀ hc] at h1
  have h3 : -((n : ℝ) * c) < Real.log (η / K) := by linarith
  have h4 : Real.exp (-((n : ℝ) * c)) < η / K :=
    calc Real.exp (-((n : ℝ) * c)) < Real.exp (Real.log (η / K)) := Real.exp_lt_exp.mpr h3
      _ = η / K := Real.exp_log (by positivity)
  rw [mul_comm]
  exact (lt_div_iff₀ hK).mp h4

private lemma exp_div_le_two_mul_exp_sub {u v D : ℝ} (hD : Real.exp v / 2 ≤ D) :
    Real.exp u / D ≤ 2 * Real.exp (u - v) := by
  have h0 : (0 : ℝ) < Real.exp v / 2 := by positivity
  have hstep : Real.exp u / D ≤ Real.exp u / (Real.exp v / 2) := by gcongr
  refine hstep.trans (le_of_eq ?_)
  rw [Real.exp_sub]
  field_simp

/-- The three Chebyshev terms of the second-moment estimate, read at the exponents of a
covering set: `gp` is the exponent of the pair probability and `gq` that of the uniform slice
bound.  The three gaps `hA`, `hB`, `hC` are what the covering rate conditions supply. -/
private lemma codebook_bound_le_six_mul_exp {gp gq R₁' R₂' cgap pv : ℝ} {n m₁ m₂ : ℕ}
    (hm₁ : Real.exp ((n : ℝ) * R₁') ≤ (m₁ : ℝ))
    (hm₂ : Real.exp ((n : ℝ) * R₂') ≤ (m₂ : ℝ))
    (hpge : Real.exp ((n : ℝ) * gp) / 2 ≤ pv)
    (hA : cgap ≤ R₁' + R₂' + gp) (hB : cgap ≤ R₁' + gp - gq) (hC : cgap ≤ R₂' + gp - gq) :
    1 / ((m₁ : ℝ) * (m₂ : ℝ) * pv) + Real.exp ((n : ℝ) * gq) / ((m₁ : ℝ) * pv)
        + Real.exp ((n : ℝ) * gq) / ((m₂ : ℝ) * pv)
      ≤ 6 * Real.exp (-((n : ℝ) * cgap)) := by
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd₁ : Real.exp ((n : ℝ) * (R₁' + R₂' + gp)) / 2 ≤ (m₁ : ℝ) * m₂ * pv := by
    have hexp : Real.exp ((n : ℝ) * (R₁' + R₂' + gp))
        = Real.exp ((n : ℝ) * R₁') * Real.exp ((n : ℝ) * R₂') * Real.exp ((n : ℝ) * gp) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hstep : Real.exp ((n : ℝ) * R₁') * Real.exp ((n : ℝ) * R₂')
        * (Real.exp ((n : ℝ) * gp) / 2) ≤ (m₁ : ℝ) * m₂ * pv := by
      gcongr
    rw [hexp]
    linarith
  have hd₂ : Real.exp ((n : ℝ) * (R₁' + gp)) / 2 ≤ (m₁ : ℝ) * pv := by
    have hexp : Real.exp ((n : ℝ) * (R₁' + gp))
        = Real.exp ((n : ℝ) * R₁') * Real.exp ((n : ℝ) * gp) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hstep : Real.exp ((n : ℝ) * R₁') * (Real.exp ((n : ℝ) * gp) / 2) ≤ (m₁ : ℝ) * pv := by
      gcongr
    rw [hexp]
    linarith
  have hd₃ : Real.exp ((n : ℝ) * (R₂' + gp)) / 2 ≤ (m₂ : ℝ) * pv := by
    have hexp : Real.exp ((n : ℝ) * (R₂' + gp))
        = Real.exp ((n : ℝ) * R₂') * Real.exp ((n : ℝ) * gp) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hstep : Real.exp ((n : ℝ) * R₂') * (Real.exp ((n : ℝ) * gp) / 2) ≤ (m₂ : ℝ) * pv := by
      gcongr
    rw [hexp]
    linarith
  have ht₁ : 1 / ((m₁ : ℝ) * m₂ * pv) ≤ 2 * Real.exp (-((n : ℝ) * cgap)) := by
    have h := exp_div_le_two_mul_exp_sub (u := 0) (v := (n : ℝ) * (R₁' + R₂' + gp)) hd₁
    rw [Real.exp_zero] at h
    refine h.trans ?_
    have hmul : (n : ℝ) * cgap ≤ (n : ℝ) * (R₁' + R₂' + gp) :=
      mul_le_mul_of_nonneg_left hA hnR
    gcongr
    linarith
  have ht₂ : Real.exp ((n : ℝ) * gq) / ((m₁ : ℝ) * pv) ≤ 2 * Real.exp (-((n : ℝ) * cgap)) := by
    have h := exp_div_le_two_mul_exp_sub (u := (n : ℝ) * gq) (v := (n : ℝ) * (R₁' + gp)) hd₂
    refine h.trans ?_
    have hmul : (n : ℝ) * cgap ≤ (n : ℝ) * (R₁' + gp - gq) :=
      mul_le_mul_of_nonneg_left hB hnR
    gcongr
    nlinarith [hmul]
  have ht₃ : Real.exp ((n : ℝ) * gq) / ((m₂ : ℝ) * pv) ≤ 2 * Real.exp (-((n : ℝ) * cgap)) := by
    have h := exp_div_le_two_mul_exp_sub (u := (n : ℝ) * gq) (v := (n : ℝ) * (R₂' + gp)) hd₃
    refine h.trans ?_
    have hmul : (n : ℝ) * cgap ≤ (n : ℝ) * (R₂' + gp - gq) :=
      mul_le_mul_of_nonneg_left hC hnR
    gcongr
    nlinarith [hmul]
  linarith

private lemma codebook_bound_nonneg {gq pv : ℝ} {n m₁ m₂ : ℕ} (hp : 0 ≤ pv) :
    0 ≤ 1 / ((m₁ : ℝ) * (m₂ : ℝ) * pv) + Real.exp ((n : ℝ) * gq) / ((m₁ : ℝ) * pv)
      + Real.exp ((n : ℝ) * gq) / ((m₂ : ℝ) * pv) := by
  have h1 : (0 : ℝ) ≤ (m₁ : ℝ) * m₂ * pv :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp
  have h2 : (0 : ℝ) ≤ (m₁ : ℝ) * pv := mul_nonneg (Nat.cast_nonneg _) hp
  have h3 : (0 : ℝ) ≤ (m₂ : ℝ) * pv := mul_nonneg (Nat.cast_nonneg _) hp
  exact add_nonneg (add_nonneg (div_nonneg zero_le_one h1)
    (div_nonneg (Real.exp_pos _).le h2)) (div_nonneg (Real.exp_pos _).le h3)

end Tail

/-! ### The band constant of the strong radius -/

section StrongRadius

variable {Ω : Type*} [MeasurableSpace Ω]
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
  {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B]
    [MeasurableSingletonClass B]

/-- The Lipschitz factor by which the type radius of a jointly strongly typical pair has to be
amplified to reach the weak bands of the two blocks and of their joint sequence.  It is the
single constant governing both directions the covering estimate needs: the exponential lower
bound on the mass of the strongly typical set, and the slice bound obtained by reading that set
inside a weakly typical set of the widened radius.

@audit:ok -/
noncomputable def coveringBandConst (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B) : ℝ :=
  (Fintype.card B : ℝ) * logSumAbs μ Xs + (Fintype.card A : ℝ) * logSumAbs μ Ys
    + logSumAbs μ (jointSequence Xs Ys)

lemma coveringBandConst_nonneg (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B) :
    0 ≤ coveringBandConst μ Xs Ys := by
  unfold coveringBandConst
  have h₁ : (0 : ℝ) ≤ (Fintype.card B : ℝ) * logSumAbs μ Xs :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₂ : (0 : ℝ) ≤ (Fintype.card A : ℝ) * logSumAbs μ Ys :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₃ : (0 : ℝ) ≤ logSumAbs μ (jointSequence Xs Ys) := logSumAbs_nonneg _ _
  linarith

lemma coveringBandConst_mul (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B) (ε : ℝ) :
    (Fintype.card B : ℝ) * ε * logSumAbs μ Xs + (Fintype.card A : ℝ) * ε * logSumAbs μ Ys
        + ε * logSumAbs μ (jointSequence Xs Ys)
      = ε * coveringBandConst μ Xs Ys := by
  unfold coveringBandConst
  ring

lemma measurableSet_jointStronglyTypicalSet (μ : Measure Ω) (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
    (n : ℕ) (ε : ℝ) : MeasurableSet (jointStronglyTypicalSet μ Xs Ys n ε) :=
  (Set.toFinite _).measurableSet

lemma jointStronglyTypicalSet_subset_jointlyTypicalSet_bandConst
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0))
    (hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0))
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    jointStronglyTypicalSet μ Xs Ys n ε
      ⊆ jointlyTypicalSet μ Xs Ys n (ε * (1 + coveringBandConst μ Xs Ys)) := by
  have h₁ : (0 : ℝ) ≤ (Fintype.card B : ℝ) * logSumAbs μ Xs :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₂ : (0 : ℝ) ≤ (Fintype.card A : ℝ) * logSumAbs μ Ys :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₃ : (0 : ℝ) ≤ logSumAbs μ (jointSequence Xs Ys) := logSumAbs_nonneg _ _
  have hC : coveringBandConst μ Xs Ys
      = (Fintype.card B : ℝ) * logSumAbs μ Xs + (Fintype.card A : ℝ) * logSumAbs μ Ys
        + logSumAbs μ (jointSequence Xs Ys) := rfl
  refine jointStronglyTypicalSet_subset_jointlyTypicalSet μ Xs Ys hXs hYs hmarg_X hmarg_Y hn
    hε.le ?_ ?_ ?_ <;> rw [hC] <;> nlinarith [hε, h₁, h₂, h₃]

end StrongRadius

/-! ### Mutual covering over abstract alphabets -/

section Covering

variable {Ω : Type*} [MeasurableSpace Ω]
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
  {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B]
    [MeasurableSingletonClass B]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → A) (Ys : ℕ → Ω → B)
  (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
  (hindepX : iIndepFun (fun i ↦ Xs i) μ) (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
  (hindepY : iIndepFun (fun i ↦ Ys i) μ) (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
  (hindepZ : iIndepFun (fun i ↦ jointSequence Xs Ys i) μ)
  (hidentZ : ∀ i, IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
  (hposX : ∀ x : A, 0 < (μ.map (Xs 0)).real {x})
  (hposY : ∀ y : B, 0 < (μ.map (Ys 0)).real {y})
  (hposZ : ∀ p : A × B, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})

include hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ hposX hposY hposZ in
/-- Mutual covering for a pair of independent i.i.d. codebook ensembles.  Writing
`I = H(X) + H(Y) - H(X, Y)` for the dependence between the two sequences, if the two
subcodebook rates `R₁'`, `R₂'` add up to more than `I` and `ε` is small enough compared with
both the slack `R₁' + R₂' - I` and the individual rates, then the probability that no pair of
codewords is jointly typical drops below any prescribed `η`. -/
theorem meas_codebook_no_jointlyTypicalPair_lt
    {R₁' R₂' ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hcov : entropy μ (Xs 0) + entropy μ (Ys 0) - entropy μ (jointSequence Xs Ys 0) + 3 * ε
      < R₁' + R₂')
    (hε₁ : 6 * ε < R₁') (hε₂ : 6 * ε < R₂') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure (μ.map (Xs 0)) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure (μ.map (Ys 0)) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉ jointlyTypicalSet μ Xs Ys n ε} < η := by
  classical
  set HX := entropy μ (Xs 0) with hHX
  set HY := entropy μ (Ys 0) with hHY
  set HZ := entropy μ (jointSequence Xs Ys 0) with hHZ
  obtain ⟨cgap, hcgap0, hcgapA, hcgapB, hcgapC⟩ :
      ∃ t : ℝ, 0 < t ∧ t ≤ R₁' + R₂' + (HZ - HX - HY - 3 * ε) ∧ t ≤ R₁' - 6 * ε
        ∧ t ≤ R₂' - 6 * ε :=
    ⟨min (min (R₁' + R₂' + (HZ - HX - HY - 3 * ε)) (R₁' - 6 * ε)) (R₂' - 6 * ε),
      lt_min (lt_min (by linarith) (by linarith)) (by linarith),
      (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨N₀, hN₀⟩ := jointlyTypicalSet_prob_ge_of_rate μ Xs Ys hXs hYs
    (fun i j hij ↦ hindepX.indepFun hij) hidentX
    (fun i j hij ↦ hindepY.indepFun hij) hidentY
    (fun i j hij ↦ hindepZ.indepFun hij) hidentZ hε (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N₁, hN₁⟩ := exists_forall_mul_exp_lt hcgap0 (by norm_num : (0 : ℝ) < 6) hη
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_right _ _) hn
  haveI : IsProbabilityMeasure (μ.map (jointRV Xs n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Xs hXs n).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (jointRV Ys n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Ys hYs n).aemeasurable
  have hpge : (1 - 1 / 2) * Real.exp ((n : ℝ) * (HZ - HX - HY - 3 * ε))
      ≤ pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
          (jointlyTypicalSet μ Xs Ys n ε) :=
    jointlyTypicalSet_indep_prob_ge μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY
      hindepZ hidentZ hposX hposY hposZ n (hN₀ n hn₀)
  have hp : 0 < pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
      (jointlyTypicalSet μ Xs Ys n ε) := by
    have hexp := Real.exp_pos ((n : ℝ) * (HZ - HX - HY - 3 * ε))
    exact lt_of_lt_of_le (by linarith) hpge
  have hqY : ∀ x, ((μ.map (jointRV Ys n))
      (Prod.mk x ⁻¹' jointlyTypicalSet μ Xs Ys n ε)).toReal
      ≤ Real.exp ((n : ℝ) * (HZ - HX - HY + 3 * ε)) := fun x ↦
    measureReal_jointlyTypicalFiberSnd_le μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY
      hindepZ hidentZ hposX hposY hposZ n x
  have hqX : ∀ y, ((μ.map (jointRV Xs n))
      ((fun x ↦ (x, y)) ⁻¹' jointlyTypicalSet μ Xs Ys n ε)).toReal
      ≤ Real.exp ((n : ℝ) * (HZ - HX - HY + 3 * ε)) := fun y ↦
    measureReal_jointlyTypicalFiber_le μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY
      hindepZ hidentZ hposX hposY hposZ n y
  have hbound := meas_codebook_no_pair_le
    (M₁ := ⌈Real.exp ((n : ℝ) * R₁')⌉₊) (M₂ := ⌈Real.exp ((n : ℝ) * R₂')⌉₊)
    (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
    (measurableSet_jointlyTypicalSet μ Xs Ys n ε) hqY hqX
    (Nat.ceil_pos.mpr (Real.exp_pos _)).ne' (Nat.ceil_pos.mpr (Real.exp_pos _)).ne' hp
  set pv := pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
    (jointlyTypicalSet μ Xs Ys n ε) with hpvdef
  set m₁ : ℕ := ⌈Real.exp ((n : ℝ) * R₁')⌉₊ with hm₁def
  set m₂ : ℕ := ⌈Real.exp ((n : ℝ) * R₂')⌉₊ with hm₂def
  have hm₁le : Real.exp ((n : ℝ) * R₁') ≤ (m₁ : ℝ) := Nat.le_ceil _
  have hm₂le : Real.exp ((n : ℝ) * R₂') ≤ (m₂ : ℝ) := Nat.le_ceil _
  have hsum := codebook_bound_le_six_mul_exp (gp := HZ - HX - HY - 3 * ε)
    (gq := HZ - HX - HY + 3 * ε) (cgap := cgap) (pv := pv) (n := n) (m₁ := m₁) (m₂ := m₂)
    hm₁le hm₂le (by linarith) hcgapA (by linarith) (by linarith)
  have hBnn := codebook_bound_nonneg (gq := HZ - HX - HY + 3 * ε) (n := n) (m₁ := m₁) (m₂ := m₂)
    hp.le
  rw [show codebookMeasure (μ.map (Xs 0)) m₁ n
        = Measure.pi (fun _ : Fin m₁ ↦ μ.map (jointRV Xs n)) by
      unfold codebookMeasure
      rw [map_jointRV_eq_pi μ Xs hXs hindepX hidentX n],
    show codebookMeasure (μ.map (Ys 0)) m₂ n
        = Measure.pi (fun _ : Fin m₂ ↦ μ.map (jointRV Ys n)) by
      unfold codebookMeasure
      rw [map_jointRV_eq_pi μ Ys hYs hindepY hidentY n]]
  refine lt_of_le_of_lt ?_ (hN₁ n hn₁)
  rw [measureReal_def]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound) ?_
  rw [ENNReal.toReal_ofReal hBnn]
  linarith

include hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ hposX hposY hposZ in
/-- Mutual covering at a jointly *strongly* typical pair.  The strongly typical set is smaller
than the weakly typical one, so this bound implies the weak reading of `ε`-widened radius; the
price is that the covering rate conditions are stated at the radius amplified by
`coveringBandConst`, which is what converts the strong radius into the weak bands governing
both the mass of the set and its conditional slices.

@audit:ok -/
theorem meas_codebook_no_jointStronglyTypicalPair_lt
    {R₁' R₂' ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hcov : entropy μ (Xs 0) + entropy μ (Ys 0) - entropy μ (jointSequence Xs Ys 0)
        + (coveringBandConst μ Xs Ys + 3) * ε < R₁' + R₂')
    (hε₁ : (4 * coveringBandConst μ Xs Ys + 6) * ε < R₁')
    (hε₂ : (4 * coveringBandConst μ Xs Ys + 6) * ε < R₂') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure (μ.map (Xs 0)) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure (μ.map (Ys 0)) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉ jointStronglyTypicalSet μ Xs Ys n ε} < η := by
  classical
  have hCnn : 0 ≤ coveringBandConst μ Xs Ys := coveringBandConst_nonneg μ Xs Ys
  have hmarg_X : (μ.map (jointSequence Xs Ys 0)).map Prod.fst = μ.map (Xs 0) := by
    rw [Measure.map_map measurable_fst (measurable_jointSequence Xs Ys hXs hYs 0)]
    rfl
  have hmarg_Y : (μ.map (jointSequence Xs Ys 0)).map Prod.snd = μ.map (Ys 0) := by
    rw [Measure.map_map measurable_snd (measurable_jointSequence Xs Ys hXs hYs 0)]
    rfl
  obtain ⟨cgap, hcgap0, hcgapA, hcgapB, hcgapC⟩ :
      ∃ t : ℝ, 0 < t
        ∧ t ≤ R₁' + R₂' + (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
            - entropy μ (Ys 0) - (ε * coveringBandConst μ Xs Ys + 3 * ε))
        ∧ t ≤ R₁' - (4 * coveringBandConst μ Xs Ys + 6) * ε
        ∧ t ≤ R₂' - (4 * coveringBandConst μ Xs Ys + 6) * ε :=
    ⟨min (min (R₁' + R₂' + (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
          - entropy μ (Ys 0) - (ε * coveringBandConst μ Xs Ys + 3 * ε)))
        (R₁' - (4 * coveringBandConst μ Xs Ys + 6) * ε))
        (R₂' - (4 * coveringBandConst μ Xs Ys + 6) * ε),
      lt_min (lt_min (by nlinarith) (by linarith)) (by linarith),
      (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨N₀, hN₀⟩ := jointStronglyTypicalSet_indep_prob_ge μ Xs Ys hXs hYs hindepX hidentX
    hindepY hidentY hindepZ (fun i j hij ↦ hindepZ.indepFun hij) hidentZ hposX hposY hposZ
    hmarg_X hmarg_Y hε hε (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N₁, hN₁⟩ := exists_forall_mul_exp_lt hcgap0 (by norm_num : (0 : ℝ) < 6) hη
  refine ⟨max (max N₀ N₁) 1, fun n hn ↦ ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ 1)) hn
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ 1)) hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ 1) hn)
  haveI : IsProbabilityMeasure (μ.map (jointRV Xs n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Xs hXs n).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (jointRV Ys n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Ys hYs n).aemeasurable
  have hsub : jointStronglyTypicalSet μ Xs Ys n ε
      ⊆ jointlyTypicalSet μ Xs Ys n (ε * (1 + coveringBandConst μ Xs Ys)) :=
    jointStronglyTypicalSet_subset_jointlyTypicalSet_bandConst μ Xs Ys hXs hYs hmarg_X hmarg_Y
      hnpos hε
  have hraw : (1 - 1 / 2) * Real.exp ((n : ℝ) *
        ((entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0))
          - (((Fintype.card B : ℝ) * ε * logSumAbs μ Xs
              + (Fintype.card A : ℝ) * ε * logSumAbs μ Ys
              + ε * logSumAbs μ (jointSequence Xs Ys)) + 3 * ε)))
      ≤ pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
          (jointStronglyTypicalSet μ Xs Ys n ε) := hN₀ n hn₀
  rw [coveringBandConst_mul] at hraw
  have hpge : Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
        - entropy μ (Ys 0) - (ε * coveringBandConst μ Xs Ys + 3 * ε))) / 2
      ≤ pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
          (jointStronglyTypicalSet μ Xs Ys n ε) := by linarith
  have hp : 0 < pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
      (jointStronglyTypicalSet μ Xs Ys n ε) := by
    have hexp := Real.exp_pos ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
      - entropy μ (Ys 0) - (ε * coveringBandConst μ Xs Ys + 3 * ε)))
    linarith
  have hqY : ∀ x, (μ.map (jointRV Ys n)).real
      (Prod.mk x ⁻¹' jointStronglyTypicalSet μ Xs Ys n ε)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
          - entropy μ (Ys 0) + 3 * (ε * (1 + coveringBandConst μ Xs Ys)))) := by
    intro x
    refine le_trans (measureReal_mono (Set.preimage_mono hsub) (measure_ne_top _ _)) ?_
    exact measureReal_jointlyTypicalFiberSnd_le μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY
      hindepZ hidentZ hposX hposY hposZ n x
  have hqX : ∀ y, (μ.map (jointRV Xs n)).real
      ((fun x ↦ (x, y)) ⁻¹' jointStronglyTypicalSet μ Xs Ys n ε)
      ≤ Real.exp ((n : ℝ) * (entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0)
          - entropy μ (Ys 0) + 3 * (ε * (1 + coveringBandConst μ Xs Ys)))) := by
    intro y
    refine le_trans (measureReal_mono (Set.preimage_mono hsub) (measure_ne_top _ _)) ?_
    exact measureReal_jointlyTypicalFiber_le μ Xs Ys hXs hYs hindepX hidentX hindepY hidentY
      hindepZ hidentZ hposX hposY hposZ n y
  have hbound := meas_codebook_no_pair_le
    (M₁ := ⌈Real.exp ((n : ℝ) * R₁')⌉₊) (M₂ := ⌈Real.exp ((n : ℝ) * R₂')⌉₊)
    (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
    (measurableSet_jointStronglyTypicalSet μ Xs Ys n ε) hqY hqX
    (Nat.ceil_pos.mpr (Real.exp_pos _)).ne' (Nat.ceil_pos.mpr (Real.exp_pos _)).ne' hp
  set pv := pairProb (μ.map (jointRV Xs n)) (μ.map (jointRV Ys n))
    (jointStronglyTypicalSet μ Xs Ys n ε) with hpvdef
  set m₁ : ℕ := ⌈Real.exp ((n : ℝ) * R₁')⌉₊ with hm₁def
  set m₂ : ℕ := ⌈Real.exp ((n : ℝ) * R₂')⌉₊ with hm₂def
  have hm₁le : Real.exp ((n : ℝ) * R₁') ≤ (m₁ : ℝ) := Nat.le_ceil _
  have hm₂le : Real.exp ((n : ℝ) * R₂') ≤ (m₂ : ℝ) := Nat.le_ceil _
  have hsum := codebook_bound_le_six_mul_exp
    (gp := entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0)
      - (ε * coveringBandConst μ Xs Ys + 3 * ε))
    (gq := entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0)
      + 3 * (ε * (1 + coveringBandConst μ Xs Ys)))
    (cgap := cgap) (pv := pv) (n := n) (m₁ := m₁) (m₂ := m₂)
    hm₁le hm₂le hpge hcgapA (by nlinarith) (by nlinarith)
  have hBnn := codebook_bound_nonneg
    (gq := entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0)
      + 3 * (ε * (1 + coveringBandConst μ Xs Ys)))
    (n := n) (m₁ := m₁) (m₂ := m₂) hp.le
  rw [show codebookMeasure (μ.map (Xs 0)) m₁ n
        = Measure.pi (fun _ : Fin m₁ ↦ μ.map (jointRV Xs n)) by
      unfold codebookMeasure
      rw [map_jointRV_eq_pi μ Xs hXs hindepX hidentX n],
    show codebookMeasure (μ.map (Ys 0)) m₂ n
        = Measure.pi (fun _ : Fin m₂ ↦ μ.map (jointRV Ys n)) by
      unfold codebookMeasure
      rw [map_jointRV_eq_pi μ Ys hYs hindepY hidentY n]]
  refine lt_of_le_of_lt ?_ (hN₁ n hn₁)
  rw [measureReal_def]
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound) ?_
  rw [ENNReal.toReal_ofReal hBnn]
  linarith

end Covering

/-! ### Marton's auxiliary variables: the weakly typical reading -/

section MartonCovering

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The regularity facts the covering estimate needs of the Marton ambient, read at the pair of
auxiliary coordinates: measurability, independence and identical distribution across blocks, full
support of the three marginals, the reading of the entropy combination as `I(V₁; V₂)`, and the
identification of the two block laws with the marginals of `pV`. -/
private lemma marton_coveringAmbient_facts
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) :
    (∀ i, Measurable (martonV₁s (V₁ := V₁) (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i))
      ∧ (∀ i, Measurable (martonV₂s (V₁ := V₁) (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i))
      ∧ iIndepFun (fun i ↦ martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i)
          (martonAmbientMeasure pV K W)
      ∧ (∀ i, IdentDistrib (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i)
          (martonV₁s 0) (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W))
      ∧ iIndepFun (fun i ↦ martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) i)
          (martonAmbientMeasure pV K W)
      ∧ (∀ i, IdentDistrib (martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) i)
          (martonV₂s 0) (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W))
      ∧ iIndepFun (fun i ↦ jointSequence (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂))
          martonV₂s i) (martonAmbientMeasure pV K W)
      ∧ (∀ i, IdentDistrib (jointSequence (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂))
            martonV₂s i) (jointSequence martonV₁s martonV₂s 0)
          (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W))
      ∧ (∀ v : V₁, 0 < ((martonAmbientMeasure pV K W).map
          (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) 0)).real {v})
      ∧ (∀ v : V₂, 0 < ((martonAmbientMeasure pV K W).map
          (martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) 0)).real {v})
      ∧ (∀ v : V₁ × V₂, 0 < ((martonAmbientMeasure pV K W).map
          (jointSequence martonV₁s martonV₂s 0)).real {v})
      ∧ entropy (martonAmbientMeasure pV K W) (martonV₁s 0)
            + entropy (martonAmbientMeasure pV K W) (martonV₂s 0)
            - entropy (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonV₂s 0)
          = martonInfoV₁V₂ pV K W
      ∧ (martonAmbientMeasure pV K W).map
          (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) 0) = pV.map Prod.fst
      ∧ (martonAmbientMeasure pV K W).map
          (martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) 0) = pV.map Prod.snd := by
  have hV₁ : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hV₂ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hV₁₂ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) := hV₁.prodMk hV₂
  refine ⟨fun i ↦ hV₁.comp (measurable_pi_apply i), fun i ↦ hV₂.comp (measurable_pi_apply i),
    martonAmbient_iIndepFun_coord pV K W Prod.fst hV₁,
    fun i ↦ martonAmbient_identDistrib_coord pV K W Prod.fst hV₁ i,
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ q.2.1) hV₂,
    fun i ↦ martonAmbient_identDistrib_coord pV K W (fun q ↦ q.2.1) hV₂ i,
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ (q.1, q.2.1)) hV₁₂,
    fun i ↦ martonAmbient_identDistrib_coord pV K W (fun q ↦ (q.1, q.2.1)) hV₁₂ i,
    fun v ↦ martonAmbient_coord_marginal_pos pV K W hpV hK hW Prod.fst hV₁ 0 v
      (v, Classical.arbitrary V₂, Classical.arbitrary α, Classical.arbitrary β₁,
        Classical.arbitrary β₂) rfl,
    fun v ↦ martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ q.2.1) hV₂ 0 v
      (Classical.arbitrary V₁, v, Classical.arbitrary α, Classical.arbitrary β₁,
        Classical.arbitrary β₂) rfl,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨v₁, v₂⟩
    exact martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ (q.1, q.2.1)) hV₁₂ 0 _
      (v₁, v₂, Classical.arbitrary α, Classical.arbitrary β₁, Classical.arbitrary β₂) rfl
  · have hEX : entropy (martonAmbientMeasure pV K W) (martonV₁s 0)
        = entropy (martonJointDistribution pV K W) Prod.fst :=
      martonAmbient_entropy_coord pV K W Prod.fst hV₁ 0
    have hEY : entropy (martonAmbientMeasure pV K W) (martonV₂s 0)
        = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1) :=
      martonAmbient_entropy_coord pV K W (fun q ↦ q.2.1) hV₂ 0
    have hEZ : entropy (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonV₂s 0)
        = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.1)) :=
      martonAmbient_entropy_coord pV K W (fun q ↦ (q.1, q.2.1)) hV₁₂ 0
    rw [hEX, hEY, hEZ, martonInfoV₁V₂]
  · have h1 : (martonAmbientMeasure pV K W).map (martonV₁s 0)
        = (martonJointDistribution pV K W).map Prod.fst :=
      martonAmbient_map_coord pV K W Prod.fst hV₁ 0
    have h2 : pV.map (Prod.fst : V₁ × V₂ → V₁)
        = (martonJointDistribution pV K W).map (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := by
      conv_lhs => rw [← martonJointDistribution_map_V pV K W]
      rw [Measure.map_map measurable_fst hV₁₂]
      rfl
    rw [h1, h2]
  · have h1 : (martonAmbientMeasure pV K W).map (martonV₂s 0)
        = (martonJointDistribution pV K W).map (fun q ↦ q.2.1) :=
      martonAmbient_map_coord pV K W (fun q ↦ q.2.1) hV₂ 0
    have h2 : pV.map (Prod.snd : V₁ × V₂ → V₂)
        = (martonJointDistribution pV K W).map (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) := by
      conv_lhs => rw [← martonJointDistribution_map_V pV K W]
      rw [Measure.map_map measurable_snd hV₁₂]
      rfl
    rw [h1, h2]

/-- Mutual covering for Marton's auxiliary codebooks at a prescribed typicality parameter.
The parameter `ε` is a hypothesis rather than an output, so that a consumer may choose one `ε`
meeting the smallness conditions here together with those of the decoding analysis;
`marton_mutual_covering` is the form in which `ε` is chosen.

@audit:ok -/
theorem meas_marton_codebook_no_jointlyTypicalPair_lt
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁' R₂' ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hcov : martonInfoV₁V₂ pV K W + 3 * ε < R₁' + R₂')
    (hε₁ : 6 * ε < R₁') (hε₂ : 6 * ε < R₂') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure (pV.map Prod.fst) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure (pV.map Prod.snd) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε} < η := by
  obtain ⟨hXs, hYs, hindepX, hidentX, hindepY, hidentY, hindepZ, hidentZ, hposX, hposY, hposZ,
    hinfo, hlawX, hlawY⟩ := marton_coveringAmbient_facts pV K W hpV hK hW
  have hcov' : entropy (martonAmbientMeasure pV K W) (martonV₁s 0)
      + entropy (martonAmbientMeasure pV K W) (martonV₂s 0)
      - entropy (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonV₂s 0)
      + 3 * ε < R₁' + R₂' := by
    rw [hinfo]
    exact hcov
  have hmain := meas_codebook_no_jointlyTypicalPair_lt (martonAmbientMeasure pV K W)
    martonV₁s martonV₂s hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ
    hposX hposY hposZ hε hη hcov' hε₁ hε₂
  rw [hlawX, hlawY] at hmain
  exact hmain

/-- Marton's mutual covering lemma.  Two subcodebooks are drawn independently, the first from
the `V₁`-marginal of the auxiliary law and the second from its `V₂`-marginal, at positive rates
`R₁'` and `R₂'` whose sum exceeds the dependence `I(V₁; V₂)` between the auxiliary variables.
Then there is a typicality parameter for which, at every large enough blocklength, the
probability that no pair of codewords is jointly typical is below any prescribed `η`.

The hypotheses `hpV`, `hK`, `hW` are the full-support regularity preconditions shared by every
typicality bound in this development; they are what rules out a deterministic input map
`x = f(v₁, v₂)` and forces the general-kernel formulation.

@audit:ok -/
@[entry_point]
theorem marton_mutual_covering
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁' R₂' η : ℝ} (hR₁' : 0 < R₁') (hR₂' : 0 < R₂')
    (hcov : martonInfoV₁V₂ pV K W < R₁' + R₂') (hη : 0 < η) :
    ∃ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure (pV.map Prod.fst) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure (pV.map Prod.snd) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε} < η := by
  obtain ⟨ε, hε, hεcov, hε₁, hε₂⟩ : ∃ ε : ℝ, 0 < ε
      ∧ martonInfoV₁V₂ pV K W + 3 * ε < R₁' + R₂' ∧ 6 * ε < R₁' ∧ 6 * ε < R₂' := by
    have hA : min (min ((R₁' + R₂' - martonInfoV₁V₂ pV K W) / 6) (R₁' / 12)) (R₂' / 12)
        ≤ (R₁' + R₂' - martonInfoV₁V₂ pV K W) / 6 :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hB : min (min ((R₁' + R₂' - martonInfoV₁V₂ pV K W) / 6) (R₁' / 12)) (R₂' / 12)
        ≤ R₁' / 12 := (min_le_left _ _).trans (min_le_right _ _)
    have hC : min (min ((R₁' + R₂' - martonInfoV₁V₂ pV K W) / 6) (R₁' / 12)) (R₂' / 12)
        ≤ R₂' / 12 := min_le_right _ _
    exact ⟨min (min ((R₁' + R₂' - martonInfoV₁V₂ pV K W) / 6) (R₁' / 12)) (R₂' / 12),
      lt_min (lt_min (by linarith) (by linarith)) (by linarith), by linarith, by linarith,
      by linarith⟩
  exact ⟨ε, hε, meas_marton_codebook_no_jointlyTypicalPair_lt pV K W hpV hK hW hε hη
    hεcov hε₁ hε₂⟩

/-- Mutual covering with independent auxiliary variables, where the covering threshold
`I(V₁; V₂)` vanishes and every pair of positive rates therefore qualifies.  This is the
degenerate regime of Marton's inner bound, and it certifies that the hypotheses of
`marton_mutual_covering` are jointly satisfiable.

@audit:ok -/
theorem marton_mutual_covering_of_indepAux
    (p₁ : Measure V₁) [IsProbabilityMeasure p₁] (p₂ : Measure V₂) [IsProbabilityMeasure p₂]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hp₁ : ∀ v : V₁, 0 < p₁.real {v}) (hp₂ : ∀ v : V₂, 0 < p₂.real {v})
    (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁' R₂' η : ℝ} (hR₁' : 0 < R₁') (hR₂' : 0 < R₂') (hη : 0 < η) :
    ∃ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure ((p₁.prod p₂).map Prod.fst) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure ((p₁.prod p₂).map Prod.snd) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉
          jointlyTypicalSet (martonAmbientMeasure (p₁.prod p₂) K W) martonV₁s martonV₂s n ε}
        < η := by
  have hpV : ∀ v : V₁ × V₂, 0 < (p₁.prod p₂).real {v} := by
    intro v
    have hsingleton : ({v} : Set (V₁ × V₂)) = ({v.1} : Set V₁) ×ˢ ({v.2} : Set V₂) := by
      ext q
      simp [Prod.ext_iff]
    rw [hsingleton, measureReal_prod_prod]
    exact mul_pos (hp₁ v.1) (hp₂ v.2)
  refine marton_mutual_covering (p₁.prod p₂) K W hpV hK hW hR₁' hR₂' ?_ hη
  rw [martonInfoV₁V₂_eq_zero_of_prod]
  linarith

/-! ### The strongly typical reading -/

/-- The Lipschitz factor relating the type radius of a jointly strongly typical auxiliary pair to
the weak bands of the two auxiliary blocks and of their joint sequence.  It is the covering
counterpart of `martonBandConst`, which governs the transmitted `(V₁, X)` pair instead.

@audit:ok -/
noncomputable def martonCoveringBandConst
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ :=
  coveringBandConst (martonAmbientMeasure pV K W) martonV₁s martonV₂s

lemma martonCoveringBandConst_nonneg
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    0 ≤ martonCoveringBandConst pV K W :=
  coveringBandConst_nonneg _ _ _

/-- Mutual covering for Marton's auxiliary codebooks at a prescribed typicality parameter, with
the covering set read as the jointly *strongly* typical one.  This is the form the encoder's
selection rule consumes: a strongly typical selected pair is what pins the empirical type of the
transmitted words, which the receiver-1 conditional AEP needs.

@audit:ok -/
theorem meas_marton_codebook_no_jointStronglyTypicalPair_lt
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁' R₂' ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hcov : martonInfoV₁V₂ pV K W + (martonCoveringBandConst pV K W + 3) * ε < R₁' + R₂')
    (hε₁ : (4 * martonCoveringBandConst pV K W + 6) * ε < R₁')
    (hε₂ : (4 * martonCoveringBandConst pV K W + 6) * ε < R₂') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure (pV.map Prod.fst) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure (pV.map Prod.snd) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε} < η := by
  obtain ⟨hXs, hYs, hindepX, hidentX, hindepY, hidentY, hindepZ, hidentZ, hposX, hposY, hposZ,
    hinfo, hlawX, hlawY⟩ := marton_coveringAmbient_facts pV K W hpV hK hW
  rw [martonCoveringBandConst] at hcov hε₁ hε₂
  have hcov' : entropy (martonAmbientMeasure pV K W) (martonV₁s 0)
      + entropy (martonAmbientMeasure pV K W) (martonV₂s 0)
      - entropy (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonV₂s 0)
      + (coveringBandConst (martonAmbientMeasure pV K W) martonV₁s martonV₂s + 3) * ε
        < R₁' + R₂' := by
    rw [hinfo]
    exact hcov
  have hmain := meas_codebook_no_jointStronglyTypicalPair_lt (martonAmbientMeasure pV K W)
    martonV₁s martonV₂s hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ
    hposX hposY hposZ hε hη hcov' hε₁ hε₂
  rw [hlawX, hlawY] at hmain
  exact hmain

/-- Marton's mutual covering lemma at the strongly typical set.  Two subcodebooks are drawn
independently, the first from the `V₁`-marginal of the auxiliary law and the second from its
`V₂`-marginal, at positive rates `R₁'` and `R₂'` whose sum exceeds the dependence `I(V₁; V₂)`
between the auxiliary variables.  Then there is a typicality parameter for which, at every large
enough blocklength, the probability that no pair of codewords is jointly strongly typical is
below any prescribed `η`.

This is strictly stronger than `marton_mutual_covering`: the strongly typical set is contained in
the weakly typical one of the radius widened by `martonCoveringBandConst`, so the event bounded
here contains the weak one.

The hypotheses `hpV`, `hK`, `hW` are the full-support regularity preconditions shared by every
typicality bound in this development; they are what rules out a deterministic input map
`x = f(v₁, v₂)` and forces the general-kernel formulation.

@audit:ok -/
@[entry_point]
theorem marton_strong_mutual_covering
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁' R₂' η : ℝ} (hR₁' : 0 < R₁') (hR₂' : 0 < R₂')
    (hcov : martonInfoV₁V₂ pV K W < R₁' + R₂') (hη : 0 < η) :
    ∃ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure (pV.map Prod.fst) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure (pV.map Prod.snd) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε} < η := by
  have hCnn : 0 ≤ martonCoveringBandConst pV K W := martonCoveringBandConst_nonneg pV K W
  set D : ℝ := martonCoveringBandConst pV K W + 3 with hD
  set E : ℝ := 4 * martonCoveringBandConst pV K W + 6 with hE
  have hDpos : 0 < D := by rw [hD]; linarith
  have hEpos : 0 < E := by rw [hE]; linarith
  set ε : ℝ := min (min ((R₁' + R₂' - martonInfoV₁V₂ pV K W) / (2 * D)) (R₁' / (2 * E)))
    (R₂' / (2 * E)) with hεdef
  have hεA : ε ≤ (R₁' + R₂' - martonInfoV₁V₂ pV K W) / (2 * D) :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hεB : ε ≤ R₁' / (2 * E) := (min_le_left _ _).trans (min_le_right _ _)
  have hεC : ε ≤ R₂' / (2 * E) := min_le_right _ _
  have hε : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (div_pos (by linarith) (by linarith)) (div_pos hR₁' (by linarith)))
      (div_pos hR₂' (by linarith))
  refine ⟨ε, hε, meas_marton_codebook_no_jointStronglyTypicalPair_lt pV K W hpV hK hW hε hη
    ?_ ?_ ?_⟩
  · have h := mul_le_mul_of_nonneg_left hεA hDpos.le
    rw [show D * ((R₁' + R₂' - martonInfoV₁V₂ pV K W) / (2 * D))
        = (R₁' + R₂' - martonInfoV₁V₂ pV K W) / 2 by field_simp] at h
    linarith
  · have h := mul_le_mul_of_nonneg_left hεB hEpos.le
    rw [show E * (R₁' / (2 * E)) = R₁' / 2 by field_simp] at h
    linarith
  · have h := mul_le_mul_of_nonneg_left hεC hEpos.le
    rw [show E * (R₂' / (2 * E)) = R₂' / 2 by field_simp] at h
    linarith

/-- Strongly typical mutual covering with independent auxiliary variables, where the covering
threshold `I(V₁; V₂)` vanishes and every pair of positive rates therefore qualifies.  This is the
degenerate regime of Marton's inner bound, and it certifies that the hypotheses of
`marton_strong_mutual_covering` are jointly satisfiable.

@audit:ok -/
theorem marton_strong_mutual_covering_of_indepAux
    (p₁ : Measure V₁) [IsProbabilityMeasure p₁] (p₂ : Measure V₂) [IsProbabilityMeasure p₂]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hp₁ : ∀ v : V₁, 0 < p₁.real {v}) (hp₂ : ∀ v : V₂, 0 < p₂.real {v})
    (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {R₁' R₂' η : ℝ} (hR₁' : 0 < R₁') (hR₂' : 0 < R₂') (hη : 0 < η) :
    ∃ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((codebookMeasure ((p₁.prod p₂).map Prod.fst) ⌈Real.exp ((n : ℝ) * R₁')⌉₊ n).prod
          (codebookMeasure ((p₁.prod p₂).map Prod.snd) ⌈Real.exp ((n : ℝ) * R₂')⌉₊ n)).real
        {c | ∀ i j, (c.1 i, c.2 j) ∉
          jointStronglyTypicalSet (martonAmbientMeasure (p₁.prod p₂) K W)
            martonV₁s martonV₂s n ε} < η := by
  have hpV : ∀ v : V₁ × V₂, 0 < (p₁.prod p₂).real {v} := by
    intro v
    have hsingleton : ({v} : Set (V₁ × V₂)) = ({v.1} : Set V₁) ×ˢ ({v.2} : Set V₂) := by
      ext q
      simp [Prod.ext_iff]
    rw [hsingleton, measureReal_prod_prod]
    exact mul_pos (hp₁ v.1) (hp₂ v.2)
  refine marton_strong_mutual_covering (p₁.prod p₂) K W hpV hK hW hR₁' hR₂' ?_ hη
  rw [martonInfoV₁V₂_eq_zero_of_prod]
  linarith

end MartonCovering

end InformationTheory.Shannon.BroadcastChannel.Marton
