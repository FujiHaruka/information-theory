import InformationTheory.Shannon.BroadcastChannel.Marton.MarkovCore.Prelim
import InformationTheory.Shannon.ConditionalAEP

/-!
# Marton's inner bound — the conditional AEP for receiver 2

The receiver-2 mirror of the conditional AEP: for *whatever* auxiliary and input blocks the encoder
ends up transmitting, as long as their empirical type is close to the ambient `(V₂, X)`-law, the
channel output makes the pair `(V₂, Y₂)` weakly jointly typical with probability close to one, and
an input drawn letterwise from a type-pinned auxiliary pair inherits that pin.  The broadcast
channel is not degraded here, so the second receiver is an exact mirror of the first rather than a
second tier.

The two receivers carry separate band constants, because the bands each of them pins are the
entropies of its own output, so the radii they induce are unrelated.  An assembly consuming both
pins its blocks at the minimum of the two radii, which `jointStronglyTypicalSet_mono_radius` turns
back into either pin.

## Main definitions

* `martonBandConst₂` — the Lipschitz factor of the three receiver-2 band pins.
* `martonStrongRadius₂` — the type radius at which the transmitted blocks must be pinned.
* `martonCoveringRadius₂` — the radius at which the selected auxiliary pair must be pinned.

## Main statements

* `marton_condAEP_jointlyTypical₂` — the conditional AEP: the channel output of a type-pinned
  `(V₂, X)`-block is jointly typical with the auxiliary word with probability `≥ 1 - tol`.
* `marton_transmitted_stronglyTypical₂_le` — the input drawn from a type-pinned auxiliary pair
  inherits the pin.
* `marton_condAEP_selected_avg₂_le` — the two combined: the receiver-2 error term of a selected
  auxiliary pair, averaged over the input tier, is below any prescribed tolerance.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Coordinate laws of the Marton ambient measure — receiver 2 -/

private lemma marton_map_Y₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (martonY₂s 0)
      = (martonJointDistribution pV K W).map (fun z ↦ z.2.2.2.2) :=
  martonAmbient_map_coord pV K W (fun z ↦ z.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))) 0

private lemma marton_map_V₂X
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonXs 0)
      = (martonJointDistribution pV K W).map (fun z ↦ (z.2.1, z.2.2.1)) :=
  martonAmbient_map_coord pV K W (fun z ↦ (z.2.1, z.2.2.1))
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))) 0

private lemma marton_map_V₂Y₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonY₂s 0)
      = (martonJointDistribution pV K W).map (fun z ↦ (z.2.1, z.2.2.2.2)) :=
  martonAmbient_map_coord pV K W (fun z ↦ (z.2.1, z.2.2.2.2))
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))) 0

/-! ### The Markov identity `V₂ — X — Y₂` -/

private lemma marton_sum_condMean_eq₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (F : V₂ → β₂ → ℝ) :
    ∑ p : V₂ × α, ((martonJointDistribution pV K W).map (fun z ↦ (z.2.1, z.2.2.1))).real {p}
          * ∑ y : β₁ × β₂, (W p.2).real {y} * F p.1 y.2
      = ∑ r : V₂ × β₂, ((martonJointDistribution pV K W).map
            (fun z ↦ (z.2.1, z.2.2.2.2))).real {r}
          * F r.1 r.2 := by
  classical
  rw [sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ (z.2.1, z.2.2.1))
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      (fun p ↦ ∑ y : β₁ × β₂, (W p.2).real {y} * F p.1 y.2),
    sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ (z.2.1, z.2.2.2.2))
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
      (fun r ↦ F r.1 r.2)]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v₁ _ ↦ Finset.sum_congr rfl fun v₂ _ ↦
    Finset.sum_congr rfl fun x _ ↦ ?_
  have hsing : ∀ (y₁ : β₁) (y₂ : β₂),
      (martonJointDistribution pV K W).real {(v₁, v₂, x, y₁, y₂)}
        = pV.real {(v₁, v₂)} * (K (v₁, v₂)).real {x} * (W x).real {(y₁, y₂)} :=
    fun y₁ y₂ ↦ martonJointDistribution_real_singleton pV K W (v₁, v₂) x (y₁, y₂)
  simp only [hsing]
  set c : ℝ := pV.real {(v₁, v₂)} * (K (v₁, v₂)).real {x} with hc
  set A : ℝ := ∑ b₁ : β₁, ∑ b₂ : β₂, (W x).real {(b₁, b₂)} * F v₂ b₂ with hA
  have hmass : ∑ b₁ : β₁, ∑ b₂ : β₂, (W x).real {(b₁, b₂)} = 1 := by
    have hone : ∑ y : β₁ × β₂, (W x).real {y} = 1 := by
      rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
    rw [← hone, Fintype.sum_prod_type]
  calc ∑ y₁ : β₁, ∑ y₂ : β₂, c * (W x).real {(y₁, y₂)} * A
      = (∑ y₁ : β₁, ∑ y₂ : β₂, c * (W x).real {(y₁, y₂)}) * A := by
        simp only [Finset.sum_mul]
    _ = c * A := by
        simp only [← Finset.mul_sum]
        rw [hmass, mul_one]
    _ = ∑ y₁ : β₁, ∑ y₂ : β₂, c * (W x).real {(y₁, y₂)} * F v₂ y₂ := by
        rw [hA]
        simp only [Finset.mul_sum, ← mul_assoc]

private lemma marton_condMean_sum_eq_entropy_out₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∑ p : V₂ × α, ((martonAmbientMeasure pV K W).map
          (jointSequence martonV₂s martonXs 0)).real {p}
        * ∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2)
      = entropy (martonAmbientMeasure pV K W) (martonY₂s 0) := by
  classical
  have hint : ∀ p : V₂ × α,
      (∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2))
        = ∑ y : β₁ × β₂, (W p.2).real {y}
            * pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 := by
    intro p
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun y _ ↦ smul_eq_mul _ _
  simp only [hint, marton_map_V₂X pV K W]
  rw [marton_sum_condMean_eq₂ pV K W
    (fun _ y₂ ↦ pmfLog (martonAmbientMeasure pV K W) martonY₂s y₂)]
  rw [sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ (z.2.1, z.2.2.2.2))
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    (fun r ↦ pmfLog (martonAmbientMeasure pV K W) martonY₂s r.2)]
  rw [← sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ z.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun b ↦ pmfLog (martonAmbientMeasure pV K W) martonY₂s b)]
  rw [← marton_map_Y₂ pV K W]
  unfold entropy pmfLog
  exact Finset.sum_congr rfl fun b _ ↦ by rw [Real.negMulLog]; ring

private lemma marton_condMean_sum_eq_entropy_joint₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∑ p : V₂ × α, ((martonAmbientMeasure pV K W).map
          (jointSequence martonV₂s martonXs 0)).real {p}
        * ∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W)
            (jointSequence martonV₂s martonY₂s) (p.1, y.2) ∂(W p.2)
      = entropy (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s 0) := by
  classical
  have hint : ∀ p : V₂ × α,
      (∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W)
          (jointSequence martonV₂s martonY₂s) (p.1, y.2) ∂(W p.2))
        = ∑ y : β₁ × β₂, (W p.2).real {y}
            * pmfLog (martonAmbientMeasure pV K W)
                (jointSequence martonV₂s martonY₂s) (p.1, y.2) := by
    intro p
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun y _ ↦ smul_eq_mul _ _
  simp only [hint, marton_map_V₂X pV K W]
  rw [marton_sum_condMean_eq₂ pV K W
    (fun v y₂ ↦ pmfLog (martonAmbientMeasure pV K W)
      (jointSequence martonV₂s martonY₂s) (v, y₂))]
  rw [← marton_map_V₂Y₂ pV K W]
  unfold entropy pmfLog
  exact Finset.sum_congr rfl fun r _ ↦ by rw [Real.negMulLog]; ring

/-! ### The radius separation — receiver 2 -/

/-- The Lipschitz factor relating the type radius of the transmitted `(V₂, X)`-block to the width
of the three entropy bands it has to pin.  It is a separate constant from `martonBandConst`, since
the bands it controls are the entropies of the second output.

@audit:ok -/
noncomputable def martonBandConst₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ :=
  (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s
    + (∑ p : V₂ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2)|)
    + (∑ p : V₂ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)
          ∂(W p.2)|)

/-- The type radius at which the transmitted `(V₂, X)`-block has to be pinned for the second
receiver's output bands to hold at radius `ε`.  Like `martonStrongRadius` it is a computed term of
`ε`, so the signatures downstream carry one radius only.

@audit:ok -/
noncomputable def martonStrongRadius₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) (ε : ℝ) : ℝ :=
  ε / (2 * (1 + martonBandConst₂ pV K W))

private lemma martonBandConst₂_nonneg
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    0 ≤ martonBandConst₂ pV K W := by
  unfold martonBandConst₂
  have h₁ : (0 : ℝ) ≤ (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₂ : (0 : ℝ) ≤ ∑ p : V₂ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have h₃ : (0 : ℝ) ≤ ∑ p : V₂ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)
        ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

lemma martonStrongRadius₂_pos
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε : ℝ}
    (hε : 0 < ε) :
    0 < martonStrongRadius₂ pV K W ε := by
  unfold martonStrongRadius₂
  have hC := martonBandConst₂_nonneg pV K W
  positivity

private lemma martonBandConst₂_mul_strongRadius₂_lt
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε : ℝ}
    (hε : 0 < ε) :
    martonBandConst₂ pV K W * martonStrongRadius₂ pV K W ε < ε / 2 := by
  have hC := martonBandConst₂_nonneg pV K W
  unfold martonStrongRadius₂
  set C := martonBandConst₂ pV K W with hCdef
  have hden : (0 : ℝ) < 2 * (1 + C) := by linarith
  rw [show C * (ε / (2 * (1 + C))) = C * ε / (2 * (1 + C)) from
      (mul_div_assoc C ε (2 * (1 + C))).symm, div_lt_iff₀ hden]
  nlinarith [hε, hC, mul_nonneg hC hε.le]

private lemma marton_term_mul_strongRadius₂_lt
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε t : ℝ}
    (hε : 0 < ε) (hle : t ≤ martonBandConst₂ pV K W) :
    t * martonStrongRadius₂ pV K W ε < ε / 2 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (martonStrongRadius₂_pos pV K W hε).le)
    (martonBandConst₂_mul_strongRadius₂_lt pV K W hε)

private lemma marton_bandTerm_out₂_le
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    (∑ p : V₂ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2)|)
      ≤ martonBandConst₂ pV K W := by
  unfold martonBandConst₂
  have h₁ : (0 : ℝ) ≤ (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₃ : (0 : ℝ) ≤ ∑ p : V₂ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)
        ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

private lemma marton_bandTerm_joint₂_le
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    (∑ p : V₂ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)
          ∂(W p.2)|)
      ≤ martonBandConst₂ pV K W := by
  unfold martonBandConst₂
  have h₁ : (0 : ℝ) ≤ (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₂ : (0 : ℝ) ≤ ∑ p : V₂ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

/-! ### The three bands — receiver 2 -/

private lemma marton_band_aux₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    (v₂ : Fin n → V₂) (x : Fin n → α)
    (hstrong : (fun i ↦ (v₂ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₂s martonXs) n (martonStrongRadius₂ pV K W ε)) :
    v₂ ∈ typicalSet (martonAmbientMeasure pV K W) martonV₂s n ε := by
  have hgV₂ : Measurable (fun z : V₁ × V₂ × α × β₁ × β₂ ↦ z.2.1) :=
    measurable_fst.comp measurable_snd
  have hgX : Measurable (fun z : V₁ × V₂ × α × β₁ × β₂ ↦ z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hmeasV₂ : ∀ i, Measurable (martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ hgV₂.comp (measurable_pi_apply i)
  have hmeasX : ∀ i, Measurable (martonXs (V₁ := V₁) (V₂ := V₂) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ hgX.comp (measurable_pi_apply i)
  have hmarg : ((martonAmbientMeasure pV K W).map
        (jointSequence martonV₂s martonXs 0)).map Prod.fst
      = (martonAmbientMeasure pV K W).map (martonV₂s 0) := by
    rw [Measure.map_map measurable_fst
      (measurable_jointSequence martonV₂s martonXs hmeasV₂ hmeasX 0)]
    rfl
  have hrad_pos := martonStrongRadius₂_pos pV K W hε
  have hstrongV₂ : v₂ ∈ stronglyTypicalSet (martonAmbientMeasure pV K W) martonV₂s n
      ((Fintype.card α : ℝ) * martonStrongRadius₂ pV K W ε) :=
    jointStronglyTypicalSet_implies_X_stronglyTypical (martonAmbientMeasure pV K W)
      martonV₂s martonXs hmeasV₂ hmeasX hmarg hn hrad_pos.le v₂ x hstrong
  refine stronglyTypicalSet_subset_typicalSet (martonAmbientMeasure pV K W) martonV₂s hmeasV₂ hn
    ?_ hstrongV₂
  -- The auxiliary term of `martonBandConst₂` dominates the amplification of this band.
  have hkey := martonBandConst₂_mul_strongRadius₂_lt pV K W hε
  have hterm : (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s
      ≤ martonBandConst₂ pV K W := by
    unfold martonBandConst₂
    have h₂ : (0 : ℝ) ≤ ∑ p : V₂ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2 ∂(W p.2)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have h₃ : (0 : ℝ) ≤ ∑ p : V₂ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)
          ∂(W p.2)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    linarith
  have hmono : ((Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s)
      * martonStrongRadius₂ pV K W ε ≤ martonBandConst₂ pV K W * martonStrongRadius₂ pV K W ε :=
    mul_le_mul_of_nonneg_right hterm hrad_pos.le
  calc (Fintype.card α : ℝ) * martonStrongRadius₂ pV K W ε
        * logSumAbs (martonAmbientMeasure pV K W) martonV₂s
      = ((Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₂s)
          * martonStrongRadius₂ pV K W ε := by ring
    _ ≤ martonBandConst₂ pV K W * martonStrongRadius₂ pV K W ε := hmono
    _ < ε / 2 := hkey
    _ < ε := by linarith

private lemma marton_band_out₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₂ : Fin n → V₂) (x : Fin n → α),
      (fun i ↦ (v₂ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₂s martonXs) n (martonStrongRadius₂ pV K W ε) →
      (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (fun i ↦ (y i).2) ∉
              typicalSet (martonAmbientMeasure pV K W) martonY₂s n ε }
        ≤ tol := by
  classical
  obtain ⟨N, hN⟩ := pi_empiricalMean_deviation_le_of_type_close
    (T := V₂ × α) (β := β₁ × β₂)
    (B := logSumAbs (martonAmbientMeasure pV K W) martonY₂s) hε htol
  refine ⟨N, fun n hn v₂ x hstrong ↦ ?_⟩
  have hB1 : ∀ (_ : V₂ × α) (y : β₁ × β₂),
      |pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2|
        ≤ logSumAbs (martonAmbientMeasure pV K W) martonY₂s := by
    intro _ y
    unfold pmfLog logSumAbs
    rw [abs_neg]
    exact Finset.single_le_sum
      (f := fun b ↦ |Real.log
        (((martonAmbientMeasure pV K W).map (martonY₂s 0)).real {b})|)
      (fun b _ ↦ abs_nonneg _) (Finset.mem_univ y.2)
  have hpin := marton_term_mul_strongRadius₂_lt pV K W hε (marton_bandTerm_out₂_le pV K W)
  have hspec := hN n hn (fun p : V₂ × α ↦ W p.2) (fun _ ↦ inferInstance)
    (fun (_ : V₂ × α) (y : β₁ × β₂) ↦
      pmfLog (martonAmbientMeasure pV K W) martonY₂s y.2) hB1
    (fun p ↦ ((martonAmbientMeasure pV K W).map
      (jointSequence martonV₂s martonXs 0)).real {p})
    (martonStrongRadius₂ pV K W ε) (fun i ↦ (v₂ i, x i)) hstrong hpin
  rw [marton_condMean_sum_eq_entropy_out₂ pV K W] at hspec
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hspec
  intro yb hyb
  simp only [Set.mem_setOf_eq, mem_typicalSet_iff, not_lt] at hyb
  exact hyb

private lemma marton_band_joint₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₂ : Fin n → V₂) (x : Fin n → α),
      (fun i ↦ (v₂ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₂s martonXs) n (martonStrongRadius₂ pV K W ε) →
      (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (fun i ↦ (v₂ i, (y i).2)) ∉
              typicalSet (martonAmbientMeasure pV K W)
                (jointSequence martonV₂s martonY₂s) n ε }
        ≤ tol := by
  classical
  obtain ⟨N, hN⟩ := pi_empiricalMean_deviation_le_of_type_close
    (T := V₂ × α) (β := β₁ × β₂)
    (B := logSumAbs (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s))
    hε htol
  refine ⟨N, fun n hn v₂ x hstrong ↦ ?_⟩
  have hB1 : ∀ (p : V₂ × α) (y : β₁ × β₂),
      |pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)|
        ≤ logSumAbs (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) := by
    intro p y
    unfold pmfLog logSumAbs
    rw [abs_neg]
    exact Finset.single_le_sum
      (f := fun r ↦ |Real.log (((martonAmbientMeasure pV K W).map
        (jointSequence martonV₂s martonY₂s 0)).real {r})|)
      (fun r _ ↦ abs_nonneg _) (Finset.mem_univ (p.1, y.2))
  have hpin := marton_term_mul_strongRadius₂_lt pV K W hε (marton_bandTerm_joint₂_le pV K W)
  have hspec := hN n hn (fun p : V₂ × α ↦ W p.2) (fun _ ↦ inferInstance)
    (fun (p : V₂ × α) (y : β₁ × β₂) ↦
      pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s) (p.1, y.2)) hB1
    (fun p ↦ ((martonAmbientMeasure pV K W).map
      (jointSequence martonV₂s martonXs 0)).real {p})
    (martonStrongRadius₂ pV K W ε) (fun i ↦ (v₂ i, x i)) hstrong hpin
  rw [marton_condMean_sum_eq_entropy_joint₂ pV K W] at hspec
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hspec
  intro yb hyb
  simp only [Set.mem_setOf_eq, mem_typicalSet_iff, not_lt] at hyb
  exact hyb

/-! ### The conditional AEP — receiver 2 -/

/-- Whatever auxiliary word `v₂` and input word `x` the encoder transmits, as long as their
empirical type is pinned to the ambient `(V₂, X)`-law at radius `martonStrongRadius₂`, the channel
output leaves the pair `(v₂, y₂)` outside the weakly jointly typical set with probability at most
`tol`, for every block length past a threshold depending on `ε` and `tol` alone.

This is the receiver-2 mirror of `marton_condAEP_jointlyTypical`; the channel is not degraded, so
the two receivers are related by exchanging the auxiliary and output coordinates alone.

@audit:ok -/
theorem marton_condAEP_jointlyTypical₂
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₂ : Fin n → V₂) (x : Fin n → α),
      (fun i ↦ (v₂ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₂s martonXs) n (martonStrongRadius₂ pV K W ε) →
      (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
              jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
        ≤ tol := by
  classical
  obtain ⟨N₁, hN₁⟩ := marton_band_out₂ pV K W hε (half_pos htol)
  obtain ⟨N₂, hN₂⟩ := marton_band_joint₂ pV K W hε (half_pos htol)
  refine ⟨max (max N₁ N₂) 1, fun n hn v₂ x hstrong ↦ ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right (max N₁ N₂) 1) hn)
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hn
  have hV₂ := marton_band_aux₂ pV K W hε hn1 v₂ x hstrong
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi fun i ↦ W (x i) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set BY : Set (Fin n → β₁ × β₂) :=
    { y | (fun i ↦ (y i).2) ∉ typicalSet (martonAmbientMeasure pV K W) martonY₂s n ε } with hBY
  set BJ : Set (Fin n → β₁ × β₂) :=
    { y | (fun i ↦ (v₂ i, (y i).2)) ∉ typicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₂s martonY₂s) n ε } with hBJ
  have hsub : { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε } ⊆ BY ∪ BJ := by
    intro yb hyb
    simp only [hBY, hBJ, Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    exact hyb ((mem_jointlyTypicalSet_iff (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε
      v₂ (fun i ↦ (yb i).2)).mpr ⟨hV₂, hcon.1, hcon.2⟩)
  calc ν.real { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
      ≤ ν.real (BY ∪ BJ) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ν.real BY + ν.real BJ := measureReal_union_le _ _
    _ ≤ tol / 2 + tol / 2 :=
        add_le_add (hN₁ n hnN₁ v₂ x hstrong) (hN₂ n hnN₂ v₂ x hstrong)
    _ = tol := by ring

/-! ### From a type-pinned auxiliary pair to a type-pinned transmitted pair — receiver 2 -/

/-- The type radius at which the selected auxiliary pair has to be pinned for the transmitted
`(V₂, X)` block to be pinned at `martonStrongRadius₂`.  It mirrors `martonCoveringRadius` with the
receiver-2 band constant; an assembly that needs both pins at once takes the minimum of the two
radii and reopens each of them with `jointStronglyTypicalSet_mono_radius`.

@audit:ok -/
noncomputable def martonCoveringRadius₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) (ε : ℝ) : ℝ :=
  martonStrongRadius₂ pV K W ε / (4 * ((Fintype.card (V₁ × V₂) : ℝ) + 1))

private lemma marton_ambient_V₂X_real_singleton
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (a₂ : V₂) (a : α) :
    ((martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonXs 0)).real {(a₂, a)}
      = ∑ p : V₁ × V₂, pV.real {p} * (if p.2 = a₂ then (K p).real {a} else 0) := by
  classical
  have hg1 : Measurable (fun w : (V₁ × V₂) × α ↦ (w.1.2, w.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hg2 : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ ((q.1, q.2.1), q.2.2.1)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hmapVX : (martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonXs 0)
      = (pV ⊗ₘ K).map (fun w : (V₁ × V₂) × α ↦ (w.1.2, w.2)) := by
    rw [marton_map_V₂X pV K W, ← martonJointDistribution_map_VX pV K W,
      Measure.map_map hg1 hg2]
    rfl
  have hcompProd : ∀ (p : V₁ × V₂) (x : α),
      (pV ⊗ₘ K).real {(p, x)} = pV.real {p} * (K p).real {x} := by
    intro p x
    have h := jointDistribution_singleton pV K p x
    rw [jointDistribution_def] at h
    rw [Measure.real, h, ENNReal.toReal_mul]
    rfl
  have hsum := sum_map_real_singleton_mul (pV ⊗ₘ K) (fun w : (V₁ × V₂) × α ↦ (w.1.2, w.2)) hg1
    (fun c : V₂ × α ↦ if c = (a₂, a) then (1 : ℝ) else 0)
  rw [hmapVX]
  rw [show ((pV ⊗ₘ K).map (fun w : (V₁ × V₂) × α ↦ (w.1.2, w.2))).real {(a₂, a)}
      = ∑ c : V₂ × α, ((pV ⊗ₘ K).map (fun w : (V₁ × V₂) × α ↦ (w.1.2, w.2))).real {c}
          * (if c = (a₂, a) then (1 : ℝ) else 0) by simp]
  rw [hsum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : p.2 = a₂
  · simp [hcompProd p, hp, Prod.ext_iff]
  · simp [hp, Prod.ext_iff]

lemma martonCoveringRadius₂_pos
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε : ℝ}
    (hε : 0 < ε) :
    0 < martonCoveringRadius₂ pV K W ε := by
  unfold martonCoveringRadius₂
  have h := martonStrongRadius₂_pos pV K W hε
  positivity

/-- The transmitted `(V₂, X)` block inherits the type pin of the selected auxiliary pair: drawing
the input word letterwise from `K` applied to a pair whose joint type is pinned at
`martonCoveringRadius₂` leaves the pair `(v₂, x)` outside the strongly typical set of radius
`martonStrongRadius₂` with probability at most `tol`, uniformly in the selected pair.

@audit:ok -/
theorem marton_transmitted_stronglyTypical₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius₂ pV K W ε) →
      (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real
          { x : Fin n → α | (fun i ↦ (v₂ i, x i)) ∉ stronglyTypicalSet
              (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonXs) n
                (martonStrongRadius₂ pV K W ε) }
        ≤ tol := by
  classical
  have hρpos : 0 < martonStrongRadius₂ pV K W ε := martonStrongRadius₂_pos pV K W hε
  have hcardpos : (0 : ℝ) < (Fintype.card (V₂ × α) : ℝ) := by
    have h : 0 < Fintype.card (V₂ × α) := Fintype.card_pos
    exact_mod_cast h
  have hcardnn : (0 : ℝ) ≤ (Fintype.card (V₁ × V₂) : ℝ) := Nat.cast_nonneg _
  have hkey : (Fintype.card (V₁ × V₂) : ℝ) * martonCoveringRadius₂ pV K W ε
      < martonStrongRadius₂ pV K W ε / 2 := by
    unfold martonCoveringRadius₂
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hρpos, hcardnn]
  obtain ⟨N, hN⟩ := pi_empiricalMean_deviation_le_of_type_close (T := V₁ × V₂) (β := α) (B := 1)
    (ε := martonStrongRadius₂ pV K W ε) (tol := tol / (Fintype.card (V₂ × α) : ℝ))
    hρpos (by positivity)
  refine ⟨N, fun n hn v₁ v₂ hpair ↦ ?_⟩
  set zb : Fin n → V₁ × V₂ := fun i ↦ (v₁ i, v₂ i) with hzb
  set q : V₁ × V₂ → ℝ := fun p ↦ pV.real {p} with hq
  have htypeclose : ∀ p, |(typeCount zb p : ℝ) / (n : ℝ) - q p|
      ≤ martonCoveringRadius₂ pV K W ε := by
    have hmem := (mem_jointStronglyTypicalSet_iff (martonAmbientMeasure pV K W) martonV₁s
      martonV₂s n (martonCoveringRadius₂ pV K W ε) v₁ v₂).mp hpair
    rw [mem_stronglyTypicalSet_iff, marton_map_V₁V₂ pV K W] at hmem
    exact hmem
  set Adev : V₂ × α → Set (Fin n → α) := fun c ↦
    { x : Fin n → α | martonStrongRadius₂ pV K W ε ≤
        |(typeCount (fun i ↦ (v₂ i, x i)) c : ℝ) / (n : ℝ)
          - ((martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonXs 0)).real {c}| }
    with hAdev
  have hsub : { x : Fin n → α | (fun i ↦ (v₂ i, x i)) ∉ stronglyTypicalSet
        (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonXs) n
          (martonStrongRadius₂ pV K W ε) }
      ⊆ ⋃ c ∈ (Finset.univ : Finset (V₂ × α)), Adev c := by
    intro x hx
    rw [Set.mem_setOf_eq, mem_stronglyTypicalSet_iff, not_forall] at hx
    obtain ⟨c, hc⟩ := hx
    exact Set.mem_biUnion (Finset.mem_univ c) (le_of_lt (lt_of_not_ge hc))
  have hper : ∀ c : V₂ × α, (Measure.pi fun i ↦ K (zb i)).real (Adev c)
      ≤ tol / (Fintype.card (V₂ × α) : ℝ) := by
    rintro ⟨a₂, a⟩
    set ψ : V₁ × V₂ → α → ℝ := fun p y ↦ if p.2 = a₂ ∧ y = a then (1 : ℝ) else 0 with hψ
    have hψbound : ∀ p y, |ψ p y| ≤ 1 := by
      intro p y
      simp only [hψ]
      split_ifs <;> norm_num
    have hint : ∀ p : V₁ × V₂,
        (∫ y, ψ p y ∂(K p)) = if p.2 = a₂ then (K p).real {a} else 0 := by
      intro p
      by_cases hp : p.2 = a₂
      · rw [if_pos hp, integral_fintype (Integrable.of_finite)]
        simp [hψ, hp]
      · rw [if_neg hp]
        simp [hψ, hp]
    have hmeanEq : (∑ p, q p * ∫ y, ψ p y ∂(K p))
        = ((martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonXs 0)).real {(a₂, a)}
        := by
      rw [marton_ambient_V₂X_real_singleton pV K W a₂ a]
      exact Finset.sum_congr rfl fun p _ ↦ by rw [hint p]
    have hcount : ∀ x : Fin n → α, (∑ i, ψ (zb i) (x i))
        = (typeCount (fun i ↦ (v₂ i, x i)) (a₂, a) : ℝ) := by
      intro x
      rw [typeCount, Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl fun i _ ↦ by simp [hψ, hzb, Prod.ext_iff]
    have hpin : (∑ p, |∫ y, ψ p y ∂(K p)|) * martonCoveringRadius₂ pV K W ε
        < martonStrongRadius₂ pV K W ε / 2 := by
      have hle : (∑ p : V₁ × V₂, |∫ y, ψ p y ∂(K p)|) ≤ (Fintype.card (V₁ × V₂) : ℝ) := by
        calc (∑ p : V₁ × V₂, |∫ y, ψ p y ∂(K p)|) ≤ ∑ _p : V₁ × V₂, (1 : ℝ) := by
              refine Finset.sum_le_sum fun p _ ↦ ?_
              rw [hint p]
              haveI : IsProbabilityMeasure (K p) := inferInstance
              split_ifs
              · rw [abs_of_nonneg measureReal_nonneg]
                exact le_of_le_of_eq (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
                  probReal_univ
              · norm_num
          _ = (Fintype.card (V₁ × V₂) : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hrpos : 0 < martonCoveringRadius₂ pV K W ε := martonCoveringRadius₂_pos pV K W hε
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hrpos.le) hkey
    have hsetEq : Adev (a₂, a)
        = { x : Fin n → α | martonStrongRadius₂ pV K W ε ≤ |(∑ i, ψ (zb i) (x i)) / (n : ℝ)
            - ∑ p, q p * ∫ y, ψ p y ∂(K p)| } := by
      ext x
      simp only [hAdev, Set.mem_setOf_eq, hcount x, hmeanEq]
    rw [hsetEq]
    exact hN n hn K (fun p ↦ inferInstance) ψ hψbound q (martonCoveringRadius₂ pV K W ε) zb
      htypeclose hpin
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  calc ∑ c ∈ (Finset.univ : Finset (V₂ × α)), (Measure.pi fun i ↦ K (zb i)).real (Adev c)
      ≤ ∑ _c ∈ (Finset.univ : Finset (V₂ × α)), tol / (Fintype.card (V₂ × α) : ℝ) :=
        Finset.sum_le_sum fun c _ ↦ hper c
    _ = tol := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- The receiver-2 error term of a selected auxiliary pair, averaged over the input tier: whatever
type-pinned pair the encoder selects, drawing the input word from `K` and passing it through the
channel leaves `(v₂, y₂)` outside the weakly jointly typical set with probability at most `tol`.

This is the form the error decomposition of `Marton.ErrorAnalysis` consumes, since the threshold
is uniform in the selected pair and hence in the code.

@audit:ok -/
theorem marton_condAEP_selected_avg₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius₂ pV K W ε) →
      ∑ x : Fin n → α, (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real {x}
          * (Measure.pi fun i ↦ W (x i)).real
              { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
        ≤ tol := by
  classical
  obtain ⟨N₁, hN₁⟩ := marton_transmitted_stronglyTypical₂_le pV K W hε (half_pos htol)
  obtain ⟨N₂, hN₂⟩ := marton_condAEP_jointlyTypical₂ pV K W hε (half_pos htol)
  refine ⟨max N₁ N₂, fun n hn v₁ v₂ hpair ↦ ?_⟩
  set μX : Measure (Fin n → α) := Measure.pi fun i ↦ K (v₁ i, v₂ i) with hμX
  haveI : IsProbabilityMeasure μX := by rw [hμX]; infer_instance
  set Sbad : Set (Fin n → α) :=
    { x | (fun i ↦ (v₂ i, x i)) ∉ stronglyTypicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₂s martonXs) n (martonStrongRadius₂ pV K W ε) } with hSbad
  set f : (Fin n → α) → ℝ := fun x ↦ (Measure.pi fun i ↦ W (x i)).real
    { y : Fin n → β₁ × β₂ | (v₂, fun i ↦ (y i).2) ∉
        jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε } with hf
  have hf_nonneg : ∀ x, 0 ≤ f x := fun _ ↦ measureReal_nonneg
  have hf_le_one : ∀ x, f x ≤ 1 := by
    intro x
    haveI : IsProbabilityMeasure (Measure.pi fun i ↦ W (x i)) := inferInstance
    refine le_of_le_of_eq (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)) ?_
    exact probReal_univ
  have hbadmass : μX.real Sbad ≤ tol / 2 := hN₁ n (le_trans (le_max_left _ _) hn) v₁ v₂ hpair
  have hgood : ∀ x ∈ Finset.univ.filter (fun x ↦ x ∉ Sbad), f x ≤ tol / 2 := by
    intro x hx
    have hx' : x ∉ Sbad := (Finset.mem_filter.mp hx).2
    have hstrong : (fun i ↦ (v₂ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₂s martonXs) n (martonStrongRadius₂ pV K W ε) := by
      by_contra hcon
      exact hx' hcon
    exact hN₂ n (le_trans (le_max_right _ _) hn) v₂ x hstrong
  have hcoe : ((Finset.univ.filter (fun x ↦ x ∈ Sbad) : Finset (Fin n → α)) : Set (Fin n → α))
      = Sbad := by
    ext x
    simp
  have hsplit : ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ Sbad), μX.real {x} * f x
      + ∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ Sbad), μX.real {x} * f x
      = ∑ x : Fin n → α, μX.real {x} * f x :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hpart₁ : ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ Sbad), μX.real {x} * f x ≤ tol / 2 := by
    calc ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ Sbad), μX.real {x} * f x
        ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ Sbad), μX.real {x} * 1 :=
          Finset.sum_le_sum fun x _ ↦
            mul_le_mul_of_nonneg_left (hf_le_one x) measureReal_nonneg
      _ = μX.real Sbad := by
          simp only [mul_one]
          rw [sum_measureReal_singleton, hcoe]
      _ ≤ tol / 2 := hbadmass
  have hpart₂ : ∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ Sbad), μX.real {x} * f x ≤ tol / 2 := by
    calc ∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ Sbad), μX.real {x} * f x
        ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ Sbad), μX.real {x} * (tol / 2) :=
          Finset.sum_le_sum fun x hx ↦
            mul_le_mul_of_nonneg_left (hgood x hx) measureReal_nonneg
      _ = (∑ x ∈ Finset.univ.filter (fun x ↦ x ∉ Sbad), μX.real {x}) * (tol / 2) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (tol / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          rw [sum_measureReal_singleton]
          exact le_of_le_of_eq (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
            probReal_univ
      _ = tol / 2 := one_mul _
  linarith [hsplit, hpart₁, hpart₂]

end InformationTheory.Shannon.BroadcastChannel.Marton
