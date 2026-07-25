import InformationTheory.Shannon.BroadcastChannel.Marton.Setup
import InformationTheory.Shannon.ConditionalAEP
import InformationTheory.Shannon.RateDistortion.AchievabilityJointStrongTypicality

/-!
# Marton's inner bound — the conditional AEP for the transmitted pair

The receiver-1 error event of the Marton ensemble opens with the transmitted auxiliary word failing
to be jointly typical with the received word.  The selection the encoder performs makes the law of
the transmitted auxiliary word depend on the whole pair of subcodebooks, so the transmitted word is
not distributed as an i.i.d. draw from the ambient and the ordinary AEP does not apply to it.  What
does apply is a conditional statement: for *whatever* auxiliary and input blocks the encoder ends
up transmitting, as long as their empirical type is close to the ambient `(V₁, X)`-law, the channel
output makes the pair `(V₁, Y₁)` weakly jointly typical with probability close to one.

The type closeness has to be at a radius strictly smaller than the band radius `ε`, because pinning
the conditional mean of the log-likelihood costs a Lipschitz factor; `martonStrongRadius` is that
smaller radius and `martonBandConst` the factor.  Weak typicality of the transmitted blocks at
radius `ε` is not enough: it pins an entropy alone, which leaves the conditional means free.

## Main definitions

* `martonBandConst` — the Lipschitz factor of the three band pins.
* `martonStrongRadius` — the type radius at which the transmitted blocks must be pinned.

## Main statements

* `marton_condAEP_jointlyTypical` — the conditional AEP: the channel output of a type-pinned
  `(V₁, X)`-block is jointly typical with the auxiliary word with probability `≥ 1 - tol`.
* `marton_strongRadius_prob_tendsto_one` — the ambient ensemble meets the type pin with
  probability tending to one, so the conditional AEP is not vacuous.
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

/-! ### Sums against a pushed-forward law -/

private lemma sum_map_real_singleton_mul {Ω γ : Type*}
    [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → γ) (hg : Measurable g) (f : γ → ℝ) :
    ∑ c : γ, (P.map g).real {c} * f c = ∑ z : Ω, P.real {z} * f (g z) := by
  haveI : IsFiniteMeasure (P.map g) := Measure.isFiniteMeasure_map P g
  have h1 : ∫ c, f c ∂(P.map g) = ∑ c : γ, (P.map g).real {c} * f c := by
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun c _ ↦ smul_eq_mul _ _
  have h2 : ∫ c, f c ∂(P.map g) = ∫ z, f (g z) ∂P :=
    integral_map hg.aemeasurable (measurable_of_finite f).aestronglyMeasurable
  have h3 : ∫ z, f (g z) ∂P = ∑ z : Ω, P.real {z} * f (g z) := by
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun z _ ↦ smul_eq_mul _ _
  rw [← h1, h2, h3]

/-! ### Coordinate laws of the Marton ambient measure -/

private lemma marton_map_Y₁
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (martonY₁s 0)
      = (martonJointDistribution pV K W).map (fun z ↦ z.2.2.2.1) :=
  martonAmbient_map_coord pV K W (fun z ↦ z.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))) 0

private lemma marton_map_V₁X
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (jointSequence martonV₁s martonXs 0)
      = (martonJointDistribution pV K W).map (fun z ↦ (z.1, z.2.2.1)) :=
  martonAmbient_map_coord pV K W (fun z ↦ (z.1, z.2.2.1))
    (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))) 0

private lemma marton_map_V₁Y₁
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (martonAmbientMeasure pV K W).map (jointSequence martonV₁s martonY₁s 0)
      = (martonJointDistribution pV K W).map (fun z ↦ (z.1, z.2.2.2.1)) :=
  martonAmbient_map_coord pV K W (fun z ↦ (z.1, z.2.2.2.1))
    (measurable_fst.prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))) 0

lemma martonJointDistribution_real_singleton
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (v : V₁ × V₂) (x : α) (y : β₁ × β₂) :
    (martonJointDistribution pV K W).real {(v.1, v.2, x, y.1, y.2)}
      = pV.real {v} * (K v).real {x} * (W x).real {y} := by
  obtain ⟨v₁, v₂⟩ := v
  obtain ⟨y₁, y₂⟩ := y
  unfold martonJointDistribution
  rw [Measure.real, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
  have h_pre₂ : (MeasurableEquiv.prodAssoc ⁻¹'
      ({(v₁, v₂, x, y₁, y₂)} : Set (V₁ × V₂ × α × β₁ × β₂)))
      = ({((v₁, v₂), x, y₁, y₂)} : Set ((V₁ × V₂) × α × β₁ × β₂)) := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  have h_pre₁ : (MeasurableEquiv.prodAssoc ⁻¹'
      ({((v₁, v₂), x, y₁, y₂)} : Set ((V₁ × V₂) × α × β₁ × β₂)))
      = ({(((v₁, v₂), x), y₁, y₂)} : Set (((V₁ × V₂) × α) × β₁ × β₂)) := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre₂, h_pre₁]
  -- Split the outer compProd, then the inner one.
  have houter := jointDistribution_singleton (pV ⊗ₘ K)
    (W.comap Prod.snd measurable_snd : Kernel ((V₁ × V₂) × α) (β₁ × β₂)) ((v₁, v₂), x) (y₁, y₂)
  rw [jointDistribution_def, Kernel.comap_apply] at houter
  have hinner := jointDistribution_singleton pV K (v₁, v₂) x
  rw [jointDistribution_def] at hinner
  rw [houter, hinner, ENNReal.toReal_mul, ENNReal.toReal_mul]
  rfl

/-! ### The Markov identity `V₁ — X — Y₁` -/

/- Averaging a statistic of `(V₁, Y₁)` over the channel against the ambient `(V₁, X)`-law returns
its ambient `(V₁, Y₁)`-average: the output is conditionally independent of the auxiliary pair
given the input.  This is where the compProd structure of the per-coordinate law enters. -/
private lemma marton_sum_condMean_eq
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (F : V₁ → β₁ → ℝ) :
    ∑ p : V₁ × α, ((martonJointDistribution pV K W).map (fun z ↦ (z.1, z.2.2.1))).real {p}
          * ∑ y : β₁ × β₂, (W p.2).real {y} * F p.1 y.1
      = ∑ r : V₁ × β₁, ((martonJointDistribution pV K W).map (fun z ↦ (z.1, z.2.2.2.1))).real {r}
          * F r.1 r.2 := by
  classical
  rw [sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ (z.1, z.2.2.1))
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      (fun p ↦ ∑ y : β₁ × β₂, (W p.2).real {y} * F p.1 y.1),
    sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ (z.1, z.2.2.2.1))
      (measurable_fst.prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
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
  set A : ℝ := ∑ b₁ : β₁, ∑ b₂ : β₂, (W x).real {(b₁, b₂)} * F v₁ b₁ with hA
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
    _ = ∑ y₁ : β₁, ∑ y₂ : β₂, c * (W x).real {(y₁, y₂)} * F v₁ y₁ := by
        rw [hA]
        simp only [Finset.mul_sum, ← mul_assoc]

private lemma marton_condMean_sum_eq_entropy_out
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∑ p : V₁ × α, ((martonAmbientMeasure pV K W).map
          (jointSequence martonV₁s martonXs 0)).real {p}
        * ∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2)
      = entropy (martonAmbientMeasure pV K W) (martonY₁s 0) := by
  classical
  have hint : ∀ p : V₁ × α,
      (∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2))
        = ∑ y : β₁ × β₂, (W p.2).real {y}
            * pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 := by
    intro p
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun y _ ↦ smul_eq_mul _ _
  simp only [hint, marton_map_V₁X pV K W]
  rw [marton_sum_condMean_eq pV K W
    (fun _ y₁ ↦ pmfLog (martonAmbientMeasure pV K W) martonY₁s y₁)]
  rw [sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ (z.1, z.2.2.2.1))
    (measurable_fst.prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    (fun r ↦ pmfLog (martonAmbientMeasure pV K W) martonY₁s r.2)]
  rw [← sum_map_real_singleton_mul (martonJointDistribution pV K W) (fun z ↦ z.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun b ↦ pmfLog (martonAmbientMeasure pV K W) martonY₁s b)]
  rw [← marton_map_Y₁ pV K W]
  unfold entropy pmfLog
  exact Finset.sum_congr rfl fun b _ ↦ by rw [Real.negMulLog]; ring

private lemma marton_condMean_sum_eq_entropy_joint
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    ∑ p : V₁ × α, ((martonAmbientMeasure pV K W).map
          (jointSequence martonV₁s martonXs 0)).real {p}
        * ∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W)
            (jointSequence martonV₁s martonY₁s) (p.1, y.1) ∂(W p.2)
      = entropy (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s 0) := by
  classical
  have hint : ∀ p : V₁ × α,
      (∫ y : β₁ × β₂, pmfLog (martonAmbientMeasure pV K W)
          (jointSequence martonV₁s martonY₁s) (p.1, y.1) ∂(W p.2))
        = ∑ y : β₁ × β₂, (W p.2).real {y}
            * pmfLog (martonAmbientMeasure pV K W)
                (jointSequence martonV₁s martonY₁s) (p.1, y.1) := by
    intro p
    rw [integral_fintype (Integrable.of_finite)]
    exact Finset.sum_congr rfl fun y _ ↦ smul_eq_mul _ _
  simp only [hint, marton_map_V₁X pV K W]
  rw [marton_sum_condMean_eq pV K W
    (fun v y₁ ↦ pmfLog (martonAmbientMeasure pV K W)
      (jointSequence martonV₁s martonY₁s) (v, y₁))]
  rw [← marton_map_V₁Y₁ pV K W]
  unfold entropy pmfLog
  exact Finset.sum_congr rfl fun r _ ↦ by rw [Real.negMulLog]; ring

/-! ### The radius separation -/

/-- The Lipschitz factor relating the type radius of the transmitted `(V₁, X)`-block to the width
of the three entropy bands it has to pin.  The sum runs over the whole alphabet, so letters carrying
no ambient mass are budgeted for as well.

@audit:ok -/
noncomputable def martonBandConst
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ :=
  (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s
    + (∑ p : V₁ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2)|)
    + (∑ p : V₁ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)
          ∂(W p.2)|)

/-- The type radius at which the transmitted `(V₁, X)`-block has to be pinned for the output bands
to hold at radius `ε`.  It is a computed term of `ε` rather than a further parameter, so the
signatures downstream carry one radius only.  It is strictly smaller than `ε`, and its
amplification by `martonBandConst` stays strictly inside `ε/2`, for every ensemble.

@audit:ok -/
noncomputable def martonStrongRadius
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) (ε : ℝ) : ℝ :=
  ε / (2 * (1 + martonBandConst pV K W))

private lemma martonBandConst_nonneg
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    0 ≤ martonBandConst pV K W := by
  unfold martonBandConst
  have h₁ : (0 : ℝ) ≤ (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₂ : (0 : ℝ) ≤ ∑ p : V₁ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have h₃ : (0 : ℝ) ≤ ∑ p : V₁ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)
        ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

lemma martonStrongRadius_pos
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε : ℝ}
    (hε : 0 < ε) :
    0 < martonStrongRadius pV K W ε := by
  unfold martonStrongRadius
  have hC := martonBandConst_nonneg pV K W
  positivity

private lemma martonBandConst_mul_strongRadius_lt
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε : ℝ}
    (hε : 0 < ε) :
    martonBandConst pV K W * martonStrongRadius pV K W ε < ε / 2 := by
  have hC := martonBandConst_nonneg pV K W
  unfold martonStrongRadius
  set C := martonBandConst pV K W with hCdef
  have hden : (0 : ℝ) < 2 * (1 + C) := by linarith
  rw [show C * (ε / (2 * (1 + C))) = C * ε / (2 * (1 + C)) from
      (mul_div_assoc C ε (2 * (1 + C))).symm, div_lt_iff₀ hden]
  nlinarith [hε, hC, mul_nonneg hC hε.le]

private lemma marton_term_mul_strongRadius_lt
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε t : ℝ}
    (hε : 0 < ε) (hle : t ≤ martonBandConst pV K W) :
    t * martonStrongRadius pV K W ε < ε / 2 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (martonStrongRadius_pos pV K W hε).le)
    (martonBandConst_mul_strongRadius_lt pV K W hε)

private lemma marton_bandTerm_out_le
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    (∑ p : V₁ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2)|)
      ≤ martonBandConst pV K W := by
  unfold martonBandConst
  have h₁ : (0 : ℝ) ≤ (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₃ : (0 : ℝ) ≤ ∑ p : V₁ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)
        ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

private lemma marton_bandTerm_joint_le
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) :
    (∑ p : V₁ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)
          ∂(W p.2)|)
      ≤ martonBandConst pV K W := by
  unfold martonBandConst
  have h₁ : (0 : ℝ) ≤ (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s :=
    mul_nonneg (Nat.cast_nonneg _) (logSumAbs_nonneg _ _)
  have h₂ : (0 : ℝ) ≤ ∑ p : V₁ × α, |∫ y : β₁ × β₂,
      pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

/-! ### The three bands -/

private lemma marton_band_aux
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    (v₁ : Fin n → V₁) (x : Fin n → α)
    (hstrong : (fun i ↦ (v₁ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε)) :
    v₁ ∈ typicalSet (martonAmbientMeasure pV K W) martonV₁s n ε := by
  have hgV₁ : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hgX : Measurable (fun z : V₁ × V₂ × α × β₁ × β₂ ↦ z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hmeasV₁ : ∀ i, Measurable (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ hgV₁.comp (measurable_pi_apply i)
  have hmeasX : ∀ i, Measurable (martonXs (V₁ := V₁) (V₂ := V₂) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ hgX.comp (measurable_pi_apply i)
  have hmarg : ((martonAmbientMeasure pV K W).map
        (jointSequence martonV₁s martonXs 0)).map Prod.fst
      = (martonAmbientMeasure pV K W).map (martonV₁s 0) := by
    rw [Measure.map_map measurable_fst
      (measurable_jointSequence martonV₁s martonXs hmeasV₁ hmeasX 0)]
    rfl
  have hrad_pos := martonStrongRadius_pos pV K W hε
  have hstrongV₁ : v₁ ∈ stronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s n
      ((Fintype.card α : ℝ) * martonStrongRadius pV K W ε) :=
    jointStronglyTypicalSet_implies_X_stronglyTypical (martonAmbientMeasure pV K W)
      martonV₁s martonXs hmeasV₁ hmeasX hmarg hn hrad_pos.le v₁ x hstrong
  refine stronglyTypicalSet_subset_typicalSet (martonAmbientMeasure pV K W) martonV₁s hmeasV₁ hn
    ?_ hstrongV₁
  -- The auxiliary term of `martonBandConst` dominates the amplification of this band.
  have hkey := martonBandConst_mul_strongRadius_lt pV K W hε
  have hterm : (Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s
      ≤ martonBandConst pV K W := by
    unfold martonBandConst
    have h₂ : (0 : ℝ) ≤ ∑ p : V₁ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1 ∂(W p.2)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have h₃ : (0 : ℝ) ≤ ∑ p : V₁ × α, |∫ y : β₁ × β₂,
        pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)
          ∂(W p.2)| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    linarith
  have hmono : ((Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s)
      * martonStrongRadius pV K W ε ≤ martonBandConst pV K W * martonStrongRadius pV K W ε :=
    mul_le_mul_of_nonneg_right hterm hrad_pos.le
  calc (Fintype.card α : ℝ) * martonStrongRadius pV K W ε
        * logSumAbs (martonAmbientMeasure pV K W) martonV₁s
      = ((Fintype.card α : ℝ) * logSumAbs (martonAmbientMeasure pV K W) martonV₁s)
          * martonStrongRadius pV K W ε := by ring
    _ ≤ martonBandConst pV K W * martonStrongRadius pV K W ε := hmono
    _ < ε / 2 := hkey
    _ < ε := by linarith

private lemma marton_band_out
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (x : Fin n → α),
      (fun i ↦ (v₁ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) →
      (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (fun i ↦ (y i).1) ∉
              typicalSet (martonAmbientMeasure pV K W) martonY₁s n ε }
        ≤ tol := by
  classical
  obtain ⟨N, hN⟩ := pi_empiricalMean_deviation_le_of_type_close
    (T := V₁ × α) (β := β₁ × β₂)
    (B := logSumAbs (martonAmbientMeasure pV K W) martonY₁s) hε htol
  refine ⟨N, fun n hn v₁ x hstrong ↦ ?_⟩
  have hB1 : ∀ (_ : V₁ × α) (y : β₁ × β₂),
      |pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1|
        ≤ logSumAbs (martonAmbientMeasure pV K W) martonY₁s := by
    intro _ y
    unfold pmfLog logSumAbs
    rw [abs_neg]
    exact Finset.single_le_sum
      (f := fun b ↦ |Real.log
        (((martonAmbientMeasure pV K W).map (martonY₁s 0)).real {b})|)
      (fun b _ ↦ abs_nonneg _) (Finset.mem_univ y.1)
  have hpin := marton_term_mul_strongRadius_lt pV K W hε (marton_bandTerm_out_le pV K W)
  have hspec := hN n hn (fun p : V₁ × α ↦ W p.2) (fun _ ↦ inferInstance)
    (fun (_ : V₁ × α) (y : β₁ × β₂) ↦
      pmfLog (martonAmbientMeasure pV K W) martonY₁s y.1) hB1
    (fun p ↦ ((martonAmbientMeasure pV K W).map
      (jointSequence martonV₁s martonXs 0)).real {p})
    (martonStrongRadius pV K W ε) (fun i ↦ (v₁ i, x i)) hstrong hpin
  rw [marton_condMean_sum_eq_entropy_out pV K W] at hspec
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hspec
  intro yb hyb
  simp only [Set.mem_setOf_eq, mem_typicalSet_iff, not_lt] at hyb
  exact hyb

private lemma marton_band_joint
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (x : Fin n → α),
      (fun i ↦ (v₁ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) →
      (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (fun i ↦ (v₁ i, (y i).1)) ∉
              typicalSet (martonAmbientMeasure pV K W)
                (jointSequence martonV₁s martonY₁s) n ε }
        ≤ tol := by
  classical
  obtain ⟨N, hN⟩ := pi_empiricalMean_deviation_le_of_type_close
    (T := V₁ × α) (β := β₁ × β₂)
    (B := logSumAbs (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s))
    hε htol
  refine ⟨N, fun n hn v₁ x hstrong ↦ ?_⟩
  have hB1 : ∀ (p : V₁ × α) (y : β₁ × β₂),
      |pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)|
        ≤ logSumAbs (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) := by
    intro p y
    unfold pmfLog logSumAbs
    rw [abs_neg]
    exact Finset.single_le_sum
      (f := fun r ↦ |Real.log (((martonAmbientMeasure pV K W).map
        (jointSequence martonV₁s martonY₁s 0)).real {r})|)
      (fun r _ ↦ abs_nonneg _) (Finset.mem_univ (p.1, y.1))
  have hpin := marton_term_mul_strongRadius_lt pV K W hε (marton_bandTerm_joint_le pV K W)
  have hspec := hN n hn (fun p : V₁ × α ↦ W p.2) (fun _ ↦ inferInstance)
    (fun (p : V₁ × α) (y : β₁ × β₂) ↦
      pmfLog (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s) (p.1, y.1)) hB1
    (fun p ↦ ((martonAmbientMeasure pV K W).map
      (jointSequence martonV₁s martonXs 0)).real {p})
    (martonStrongRadius pV K W ε) (fun i ↦ (v₁ i, x i)) hstrong hpin
  rw [marton_condMean_sum_eq_entropy_joint pV K W] at hspec
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hspec
  intro yb hyb
  simp only [Set.mem_setOf_eq, mem_typicalSet_iff, not_lt] at hyb
  exact hyb

/-! ### The conditional AEP -/

/-- Whatever auxiliary word `v₁` and input word `x` the encoder transmits, as long as their
empirical type is pinned to the ambient `(V₁, X)`-law at radius `martonStrongRadius`, the channel
output leaves the pair `(v₁, y₁)` outside the weakly jointly typical set with probability at most
`tol`, for every block length past a threshold depending on `ε` and `tol` alone.

The threshold is uniform in `v₁`, `x` and hence in the code, which is what lets the receiver-1
error decomposition consume it after the encoder's selection has already distorted the law of the
transmitted words.  The hypotheses on `pV`, `K`, `W` are the Markov-kernel regularity of the
ensemble; no full-support assumption is needed.  Both properties a free reference law would have to
assume are structural here: it is a probability law because the ensemble is built from a probability
measure and two Markov kernels, and its `(V₁, X)`- and `(V₁, Y₁)`-marginals are consistent because
both are marginals of the same compProd chain.  A letter of zero ambient mass therefore needs no
separate treatment — it enters the type radius and the band constant like any other.

@audit:ok -/
theorem marton_condAEP_jointlyTypical
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (x : Fin n → α),
      (fun i ↦ (v₁ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) →
      (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
              jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
        ≤ tol := by
  classical
  obtain ⟨N₁, hN₁⟩ := marton_band_out pV K W hε (half_pos htol)
  obtain ⟨N₂, hN₂⟩ := marton_band_joint pV K W hε (half_pos htol)
  refine ⟨max (max N₁ N₂) 1, fun n hn v₁ x hstrong ↦ ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right (max N₁ N₂) 1) hn)
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hn
  have hV₁ := marton_band_aux pV K W hε hn1 v₁ x hstrong
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi fun i ↦ W (x i) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set BY : Set (Fin n → β₁ × β₂) :=
    { y | (fun i ↦ (y i).1) ∉ typicalSet (martonAmbientMeasure pV K W) martonY₁s n ε } with hBY
  set BJ : Set (Fin n → β₁ × β₂) :=
    { y | (fun i ↦ (v₁ i, (y i).1)) ∉ typicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₁s martonY₁s) n ε } with hBJ
  have hsub : { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } ⊆ BY ∪ BJ := by
    intro yb hyb
    simp only [hBY, hBJ, Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    exact hyb ((mem_jointlyTypicalSet_iff (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε
      v₁ (fun i ↦ (yb i).1)).mpr ⟨hV₁, hcon.1, hcon.2⟩)
  calc ν.real { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
      ≤ ν.real (BY ∪ BJ) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ν.real BY + ν.real BJ := measureReal_union_le _ _
    _ ≤ tol / 2 + tol / 2 :=
        add_le_add (hN₁ n hnN₁ v₁ x hstrong) (hN₂ n hnN₂ v₁ x hstrong)
    _ = tol := by ring

/-- The hypothesis of `marton_condAEP_jointlyTypical` is met by the ambient ensemble itself with
probability tending to one: an i.i.d. `(V₁, X)`-block is type-pinned at the strong radius.  This
certifies that the conditional AEP is not vacuous — it is the ambient counterpart of the pinning
the encoder's selection has to preserve.

@audit:ok -/
theorem marton_strongRadius_prob_tendsto_one
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦ (martonAmbientMeasure pV K W)
        { ω | jointRV (jointSequence martonV₁s martonXs) n ω ∈
            stronglyTypicalSet (martonAmbientMeasure pV K W)
              (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) })
      Filter.atTop (nhds 1) := by
  have hg : Measurable (fun z : V₁ × V₂ × α × β₁ × β₂ ↦ (z.1, z.2.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hindep := martonAmbient_iIndepFun_coord pV K W _ hg
  exact stronglyTypicalSet_prob_tendsto_one (martonAmbientMeasure pV K W)
    (jointSequence martonV₁s martonXs) (fun i ↦ hg.comp (measurable_pi_apply i))
    (fun i j hij ↦ hindep.indepFun hij)
    (fun i ↦ martonAmbient_identDistrib_coord pV K W _ hg i)
    (martonStrongRadius_pos pV K W hε)

/-- The complement reading of `marton_condAEP_jointlyTypical`.

@audit:ok -/
theorem marton_condAEP_jointlyTypical_ge
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (x : Fin n → α),
      (fun i ↦ (v₁ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
          (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) →
      1 - tol ≤ (Measure.pi fun i ↦ W (x i)).real
          { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∈
              jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } := by
  classical
  obtain ⟨N, hN⟩ := marton_condAEP_jointlyTypical pV K W hε htol
  refine ⟨N, fun n hn v₁ x hstrong ↦ ?_⟩
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi fun i ↦ W (x i) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set G : Set (Fin n → β₁ × β₂) :=
    { y | (v₁, fun i ↦ (y i).1) ∈
        jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } with hG
  have hsum : ν.real G + ν.real Gᶜ = ν.real Set.univ :=
    measureReal_add_measureReal_compl (Set.toFinite G).measurableSet
  rw [probReal_univ] at hsum
  have hbad : ν.real Gᶜ ≤ tol := hN n hn v₁ x hstrong
  linarith

/-! ### From a type-pinned auxiliary pair to a type-pinned transmitted pair -/

/-- The type radius at which the *selected auxiliary pair* has to be pinned for the transmitted
`(V₁, X)` block to be pinned at `martonStrongRadius`.  The two are separated by the alphabet size
because the conditional mean of a letter statistic of the input is an average of the auxiliary
type against the input kernel, so a type deviation of the pair is amplified by the number of
auxiliary letters before it reaches the input. -/
noncomputable def martonCoveringRadius
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) (ε : ℝ) : ℝ :=
  martonStrongRadius pV K W ε / (4 * ((Fintype.card (V₁ × V₂) : ℝ) + 1))

lemma martonCoveringRadius_pos
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) {ε : ℝ}
    (hε : 0 < ε) :
    0 < martonCoveringRadius pV K W ε := by
  unfold martonCoveringRadius
  have h := martonStrongRadius_pos pV K W hε
  positivity

/-- The transmitted `(V₁, X)` block inherits the type pin of the selected auxiliary pair: drawing
the input word letterwise from `K` applied to a pair whose joint type is pinned at
`martonCoveringRadius` leaves the pair `(v₁, x)` outside the strongly typical set of radius
`martonStrongRadius` with probability at most `tol`, uniformly in the selected pair.

@residual(plan:marton-inner-bound-plan) -/
theorem marton_transmitted_stronglyTypical_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius pV K W ε) →
      (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real
          { x : Fin n → α | (fun i ↦ (v₁ i, x i)) ∉ stronglyTypicalSet
              (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonXs) n
                (martonStrongRadius pV K W ε) }
        ≤ tol := by
  sorry

/-- The receiver-1 error term of a selected auxiliary pair, averaged over the input tier: whatever
type-pinned pair the encoder selects, drawing the input word from `K` and passing it through the
channel leaves `(v₁, y₁)` outside the weakly jointly typical set with probability at most `tol`.

This is the form the error decomposition of `Marton.ErrorAnalysis` consumes, since the threshold
is uniform in the selected pair and hence in the code. -/
theorem marton_condAEP_selected_avg_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (v₁ : Fin n → V₁) (v₂ : Fin n → V₂),
      (v₁, v₂) ∈ jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n
          (martonCoveringRadius pV K W ε) →
      ∑ x : Fin n → α, (Measure.pi fun i ↦ K (v₁ i, v₂ i)).real {x}
          * (Measure.pi fun i ↦ W (x i)).real
              { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
        ≤ tol := by
  classical
  obtain ⟨N₁, hN₁⟩ := marton_transmitted_stronglyTypical_le pV K W hε (half_pos htol)
  obtain ⟨N₂, hN₂⟩ := marton_condAEP_jointlyTypical pV K W hε (half_pos htol)
  refine ⟨max N₁ N₂, fun n hn v₁ v₂ hpair ↦ ?_⟩
  set μX : Measure (Fin n → α) := Measure.pi fun i ↦ K (v₁ i, v₂ i) with hμX
  haveI : IsProbabilityMeasure μX := by rw [hμX]; infer_instance
  set Sbad : Set (Fin n → α) :=
    { x | (fun i ↦ (v₁ i, x i)) ∉ stronglyTypicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) } with hSbad
  set f : (Fin n → α) → ℝ := fun x ↦ (Measure.pi fun i ↦ W (x i)).real
    { y : Fin n → β₁ × β₂ | (v₁, fun i ↦ (y i).1) ∉
        jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } with hf
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
    have hstrong : (fun i ↦ (v₁ i, x i)) ∈ stronglyTypicalSet (martonAmbientMeasure pV K W)
        (jointSequence martonV₁s martonXs) n (martonStrongRadius pV K W ε) := by
      by_contra hcon
      exact hx' hcon
    exact hN₂ n (le_trans (le_max_right _ _) hn) v₁ x hstrong
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
