import InformationTheory.Probability.SingletonMass
import InformationTheory.Shannon.BroadcastChannel.Achievability.ErrorAnalysis
import InformationTheory.Shannon.BroadcastChannel.Marton.Covering
import InformationTheory.Shannon.MultipleAccess.Achievability.Codebook

/-!
# Marton's inner bound — error analysis

Marton's random-coding ensemble has three tiers: one auxiliary subcodebook per receiver, indexed
by a message together with a covering index, and an input codebook drawn letterwise from `K`
applied to the auxiliary pair the encoder selects.  The selection makes the transmitted auxiliary
words depend on the subcodebooks, which is what distinguishes the analysis from the superposition
ensemble of the degraded broadcast channel.

Each receiver decodes its message alone, quantifying the covering index existentially, so a second
typical index inside the transmitted row is not an error.  Its error event splits into the
transmitted pair failing to be jointly typical with the received word, and some codeword of
another message row being jointly typical with it.  The second family is bounded by the fiber
bound of the covering file, which is uniform over received words; that uniformity is what lets
the alias estimate proceed without identifying the law of the received word, which the selection
distorts.  The two receivers are treated symmetrically, the second reading `(V₂, Y₂)` where the
first reads `(V₁, Y₁)`; the ensemble is summed in one fixed order, so at receiver 2 the alias row
sits in the inner subcodebook tier and the outer one is discharged by its total mass.

Two typicality radii run through the file and are independent parameters: the encoder selects a
*strongly* typical auxiliary pair at radius `ε_cov`, while both decoders test *weak* joint
typicality at radius `ε`.  The asymmetry is forced: the alias estimate only needs the weak fiber
bound, whereas the transmitted pair has to have its empirical type pinned for the conditional AEP
of `Marton.MarkovCore` to apply to it.

## Main definitions

* `MartonSubcodebook` and `martonSubcodebookMeasure` — one receiver's auxiliary subcodebook and
  its i.i.d. law, read as a codebook whose alphabet is the set of length-`n` words.
* `martonSelectRow`, `martonAux₁`, `martonAux₂` — the encoder's covering choice and the two
  auxiliary words it transmits.
* `martonInputCodebookMeasure` — the input codebook law conditional on the subcodebooks.
* `martonMessageDecoder₁`, `martonMessageDecoder₂`, `martonCodebookToCode` — the two message
  decoders and the assembled `BroadcastCode`.

## Main statements

* `marton_jointlyTypicalFiber₁_le` and `marton_alias₁_slice_avg_le`, together with
  `marton_jointlyTypicalFiber₂_le` and `marton_alias₂_slice_avg_le` — the alias estimate against
  an arbitrary law of the received word.
* `marton_errorProbAt₁_le_bonferroni` and `marton_averageErrorProb₁_toReal_le`, together with
  `marton_errorProbAt₂_le_bonferroni` and `marton_averageErrorProb₂_toReal_le` — the per-receiver
  error decomposition, pointwise and averaged over message pairs.
* `marton_random_codebook_alias₁_le` and `marton_random_codebook_alias₂_le` — the alias estimate
  over the full three-tier ensemble.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.MAC
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Sums against a slice of a product law -/

private lemma sum_exchange_three {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    (a : A → ℝ) (b : B → ℝ) (c : B → D → ℝ) (d : A → D → ℝ) :
    ∑ v : A, a v * ∑ j : B, b j * ∑ k : D, c j k * d v k
      = ∑ j : B, b j * ∑ k : D, c j k * ∑ v : A, a v * d v k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  ring

private lemma sum_measureReal_slice_le
    {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (P : Measure A) [IsProbabilityMeasure P] (ν : Measure B) [IsProbabilityMeasure ν]
    (J : Set (A × B)) {C : ℝ} (hC : ∀ b : B, P.real {a | (a, b) ∈ J} ≤ C) :
    ∑ a : A, P.real {a} * ν.real {b | (a, b) ∈ J} ≤ C := by
  classical
  set S : Set (B × A) := {q | (q.2, q.1) ∈ J} with hS_def
  have hpre : Prod.swap ⁻¹' S = J := by
    ext p
    simp [hS_def]
  have hswap : (ν.prod P).real S = (P.prod ν).real J := by
    rw [← Measure.prod_swap, Measure.real,
      Measure.map_apply measurable_swap (Set.toFinite S).measurableSet, hpre]
    rfl
  have hsum1 : ∑ b : B, ν.real {b} = 1 := sum_measureReal_singleton_univ_eq_one ν
  rw [← mac_prodReal_eq_slice_sum P ν J, ← hswap, mac_prodReal_eq_slice_sum ν P S]
  calc ∑ b : B, ν.real {b} * P.real {a | (b, a) ∈ S}
      ≤ ∑ b : B, ν.real {b} * C :=
        Finset.sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left (hC b) measureReal_nonneg
    _ = C := by rw [← Finset.sum_mul, hsum1, one_mul]

/-! ### Receiver-1 fiber bound and alias slice -/

/-- Uniform fiber bound for the `(V₁, Y₁)` jointly typical set: whatever the received word,
the `V₁`-block mass of the codewords jointly typical with it is at most
`exp(−n (I(V₁; Y₁) − 3ε))`.

@audit:ok -/
lemma marton_jointlyTypicalFiber₁_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (n : ℕ) {ε : ℝ} (y₁ : Fin n → β₁) :
    (Measure.pi (fun _ : Fin n ↦ pV.map Prod.fst)).real
        { v : Fin n → V₁ |
          (v, y₁) ∈ jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
  classical
  have hgV₁ : Measurable (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := measurable_fst
  have hgY₁ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hgZ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.2.2.1)) := hgV₁.prodMk hgY₁
  have hXs : ∀ i, Measurable (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ hgV₁.comp (measurable_pi_apply i)
  have hYs : ∀ i, Measurable (martonY₁s (V₁ := V₁) (V₂ := V₂) (α := α) (β₂ := β₂) i) :=
    fun i ↦ hgY₁.comp (measurable_pi_apply i)
  have hindepX : iIndepFun (fun i ↦ martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i)
      (martonAmbientMeasure pV K W) := martonAmbient_iIndepFun_coord pV K W Prod.fst hgV₁
  have hindepY : iIndepFun (fun i ↦ martonY₁s (V₁ := V₁) (V₂ := V₂) (α := α) (β₂ := β₂) i)
      (martonAmbientMeasure pV K W) :=
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ q.2.2.2.1) hgY₁
  have hindepZ : iIndepFun (fun i ↦ jointSequence martonV₁s martonY₁s i)
      (martonAmbientMeasure pV K W) :=
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ (q.1, q.2.2.2.1)) hgZ
  have hidentX : ∀ i, IdentDistrib (martonV₁s (V₂ := V₂) (α := α) (β₁ := β₁) (β₂ := β₂) i)
      (martonV₁s 0) (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) := fun i ↦
    martonAmbient_identDistrib_coord pV K W Prod.fst hgV₁ i
  have hidentY : ∀ i, IdentDistrib (martonY₁s (V₁ := V₁) (V₂ := V₂) (α := α) (β₂ := β₂) i)
      (martonY₁s 0) (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) := fun i ↦
    martonAmbient_identDistrib_coord pV K W (fun q ↦ q.2.2.2.1) hgY₁ i
  have hidentZ : ∀ i, IdentDistrib (jointSequence martonV₁s martonY₁s i)
      (jointSequence martonV₁s martonY₁s 0)
      (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) := fun i ↦
    martonAmbient_identDistrib_coord pV K W (fun q ↦ (q.1, q.2.2.2.1)) hgZ i
  have hposX : ∀ v : V₁,
      0 < ((martonAmbientMeasure pV K W).map (martonV₁s 0)).real {v} := fun v ↦
    martonAmbient_coord_marginal_pos pV K W hpV hK hW Prod.fst hgV₁ 0 v
      (v, Classical.arbitrary V₂, Classical.arbitrary α, Classical.arbitrary β₁,
        Classical.arbitrary β₂) rfl
  have hposY : ∀ y : β₁,
      0 < ((martonAmbientMeasure pV K W).map (martonY₁s 0)).real {y} := fun y ↦
    martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ q.2.2.2.1) hgY₁ 0 y
      (Classical.arbitrary V₁, Classical.arbitrary V₂, Classical.arbitrary α, y,
        Classical.arbitrary β₂) rfl
  have hposZ : ∀ p : V₁ × β₁,
      0 < ((martonAmbientMeasure pV K W).map (jointSequence martonV₁s martonY₁s 0)).real {p} := by
    rintro ⟨v, y⟩
    exact martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ (q.1, q.2.2.2.1)) hgZ 0 _
      (v, Classical.arbitrary V₂, Classical.arbitrary α, y, Classical.arbitrary β₂) rfl
  have hlawX : (martonAmbientMeasure pV K W).map (martonV₁s 0) = pV.map Prod.fst := by
    have hV₁₂ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
      hgV₁.prodMk (measurable_fst.comp measurable_snd)
    have h1 : (martonAmbientMeasure pV K W).map (martonV₁s 0)
        = (martonJointDistribution pV K W).map Prod.fst :=
      martonAmbient_map_coord pV K W Prod.fst hgV₁ 0
    have h2 : pV.map (Prod.fst : V₁ × V₂ → V₁)
        = (martonJointDistribution pV K W).map (Prod.fst : V₁ × V₂ × α × β₁ × β₂ → V₁) := by
      conv_lhs => rw [← martonJointDistribution_map_V pV K W]
      rw [Measure.map_map measurable_fst hV₁₂]
      rfl
    rw [h1, h2]
  have hpi : (martonAmbientMeasure pV K W).map (jointRV martonV₁s n)
      = Measure.pi (fun _ : Fin n ↦ pV.map (Prod.fst : V₁ × V₂ → V₁)) := by
    rw [map_jointRV_eq_pi (martonAmbientMeasure pV K W) martonV₁s hXs hindepX hidentX n, hlawX]
  have hmain := measureReal_jointlyTypicalFiber_le (martonAmbientMeasure pV K W)
    martonV₁s martonY₁s hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ
    hposX hposY hposZ n (ε := ε) y₁
  rw [hpi] at hmain
  refine hmain.trans (le_of_eq ?_)
  have hEX : entropy (martonAmbientMeasure pV K W) (martonV₁s 0)
      = entropy (martonJointDistribution pV K W) Prod.fst :=
    martonAmbient_entropy_coord pV K W Prod.fst hgV₁ 0
  have hEY : entropy (martonAmbientMeasure pV K W) (martonY₁s 0)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.1) :=
    martonAmbient_entropy_coord pV K W (fun q ↦ q.2.2.2.1) hgY₁ 0
  have hEZ : entropy (martonAmbientMeasure pV K W) (jointSequence martonV₁s martonY₁s 0)
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.1, q.2.2.2.1)) :=
    martonAmbient_entropy_coord pV K W (fun q ↦ (q.1, q.2.2.2.1)) hgZ 0
  congr 1
  rw [hEX, hEY, hEZ, martonInfo₁]
  ring

/-- Averaged alias bound at receiver 1.  For an arbitrary output law `ν`, drawing the alias
codeword independently of `ν` from the `V₁`-block law makes the probability that it is jointly
typical with the received word at most `exp(−n (I(V₁; Y₁) − 3ε))`.

@audit:ok -/
theorem marton_alias₁_slice_avg_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {n : ℕ} {ε : ℝ}
    (ν : Measure (Fin n → β₁ × β₂)) [IsProbabilityMeasure ν] :
    ∑ v : Fin n → V₁,
        (Measure.pi (fun _ : Fin n ↦ pV.map Prod.fst)).real {v}
          * ν.real { y : Fin n → β₁ × β₂ |
              (v, fun i ↦ (y i).1) ∈
                jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.fst : V₁ × V₂ → V₁)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  exact sum_measureReal_slice_le (Measure.pi fun _ : Fin n ↦ pV.map Prod.fst) ν
    { q : (Fin n → V₁) × (Fin n → β₁ × β₂) |
        (q.1, fun i ↦ (q.2 i).1) ∈
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
    (fun y ↦ marton_jointlyTypicalFiber₁_le pV K W hpV hK hW n (fun i ↦ (y i).1))

/-! ### Receiver-2 fiber bound and alias slice -/

/-- Uniform fiber bound for the `(V₂, Y₂)` jointly typical set: whatever the received word,
the `V₂`-block mass of the codewords jointly typical with it is at most
`exp(−n (I(V₂; Y₂) − 3ε))`.

@audit:ok -/
lemma marton_jointlyTypicalFiber₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (n : ℕ) {ε : ℝ} (y₂ : Fin n → β₂) :
    (Measure.pi (fun _ : Fin n ↦ pV.map Prod.snd)).real
        { v : Fin n → V₂ |
          (v, y₂) ∈ jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
      ≤ Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
  classical
  have hgV₂ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hgY₂ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hgZ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.2.1, q.2.2.2.2)) := hgV₂.prodMk hgY₂
  have hXs : ∀ i, Measurable (martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) i) :=
    fun i ↦ hgV₂.comp (measurable_pi_apply i)
  have hYs : ∀ i, Measurable (martonY₂s (V₁ := V₁) (V₂ := V₂) (α := α) (β₁ := β₁) i) :=
    fun i ↦ hgY₂.comp (measurable_pi_apply i)
  have hindepX : iIndepFun (fun i ↦ martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) i)
      (martonAmbientMeasure pV K W) :=
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ q.2.1) hgV₂
  have hindepY : iIndepFun (fun i ↦ martonY₂s (V₁ := V₁) (V₂ := V₂) (α := α) (β₁ := β₁) i)
      (martonAmbientMeasure pV K W) :=
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ q.2.2.2.2) hgY₂
  have hindepZ : iIndepFun (fun i ↦ jointSequence martonV₂s martonY₂s i)
      (martonAmbientMeasure pV K W) :=
    martonAmbient_iIndepFun_coord pV K W (fun q ↦ (q.2.1, q.2.2.2.2)) hgZ
  have hidentX : ∀ i, IdentDistrib (martonV₂s (V₁ := V₁) (α := α) (β₁ := β₁) (β₂ := β₂) i)
      (martonV₂s 0) (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) := fun i ↦
    martonAmbient_identDistrib_coord pV K W (fun q ↦ q.2.1) hgV₂ i
  have hidentY : ∀ i, IdentDistrib (martonY₂s (V₁ := V₁) (V₂ := V₂) (α := α) (β₁ := β₁) i)
      (martonY₂s 0) (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) := fun i ↦
    martonAmbient_identDistrib_coord pV K W (fun q ↦ q.2.2.2.2) hgY₂ i
  have hidentZ : ∀ i, IdentDistrib (jointSequence martonV₂s martonY₂s i)
      (jointSequence martonV₂s martonY₂s 0)
      (martonAmbientMeasure pV K W) (martonAmbientMeasure pV K W) := fun i ↦
    martonAmbient_identDistrib_coord pV K W (fun q ↦ (q.2.1, q.2.2.2.2)) hgZ i
  have hposX : ∀ v : V₂,
      0 < ((martonAmbientMeasure pV K W).map (martonV₂s 0)).real {v} := fun v ↦
    martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ q.2.1) hgV₂ 0 v
      (Classical.arbitrary V₁, v, Classical.arbitrary α, Classical.arbitrary β₁,
        Classical.arbitrary β₂) rfl
  have hposY : ∀ y : β₂,
      0 < ((martonAmbientMeasure pV K W).map (martonY₂s 0)).real {y} := fun y ↦
    martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ q.2.2.2.2) hgY₂ 0 y
      (Classical.arbitrary V₁, Classical.arbitrary V₂, Classical.arbitrary α,
        Classical.arbitrary β₁, y) rfl
  have hposZ : ∀ p : V₂ × β₂,
      0 < ((martonAmbientMeasure pV K W).map (jointSequence martonV₂s martonY₂s 0)).real {p} := by
    rintro ⟨v, y⟩
    exact martonAmbient_coord_marginal_pos pV K W hpV hK hW (fun q ↦ (q.2.1, q.2.2.2.2)) hgZ 0 _
      (Classical.arbitrary V₁, v, Classical.arbitrary α, Classical.arbitrary β₁, y) rfl
  have hlawX : (martonAmbientMeasure pV K W).map (martonV₂s 0) = pV.map Prod.snd := by
    have hV₁₂ : Measurable (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
      measurable_fst.prodMk hgV₂
    have h1 : (martonAmbientMeasure pV K W).map (martonV₂s 0)
        = (martonJointDistribution pV K W).map (fun q ↦ q.2.1) :=
      martonAmbient_map_coord pV K W (fun q ↦ q.2.1) hgV₂ 0
    have h2 : pV.map (Prod.snd : V₁ × V₂ → V₂)
        = (martonJointDistribution pV K W).map (fun q : V₁ × V₂ × α × β₁ × β₂ ↦ q.2.1) := by
      conv_lhs => rw [← martonJointDistribution_map_V pV K W]
      rw [Measure.map_map measurable_snd hV₁₂]
      rfl
    rw [h1, h2]
  have hpi : (martonAmbientMeasure pV K W).map (jointRV martonV₂s n)
      = Measure.pi (fun _ : Fin n ↦ pV.map (Prod.snd : V₁ × V₂ → V₂)) := by
    rw [map_jointRV_eq_pi (martonAmbientMeasure pV K W) martonV₂s hXs hindepX hidentX n, hlawX]
  have hmain := measureReal_jointlyTypicalFiber_le (martonAmbientMeasure pV K W)
    martonV₂s martonY₂s hXs hYs hindepX hidentX hindepY hidentY hindepZ hidentZ
    hposX hposY hposZ n (ε := ε) y₂
  rw [hpi] at hmain
  refine hmain.trans (le_of_eq ?_)
  have hEX : entropy (martonAmbientMeasure pV K W) (martonV₂s 0)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.1) :=
    martonAmbient_entropy_coord pV K W (fun q ↦ q.2.1) hgV₂ 0
  have hEY : entropy (martonAmbientMeasure pV K W) (martonY₂s 0)
      = entropy (martonJointDistribution pV K W) (fun q ↦ q.2.2.2.2) :=
    martonAmbient_entropy_coord pV K W (fun q ↦ q.2.2.2.2) hgY₂ 0
  have hEZ : entropy (martonAmbientMeasure pV K W) (jointSequence martonV₂s martonY₂s 0)
      = entropy (martonJointDistribution pV K W) (fun q ↦ (q.2.1, q.2.2.2.2)) :=
    martonAmbient_entropy_coord pV K W (fun q ↦ (q.2.1, q.2.2.2.2)) hgZ 0
  congr 1
  rw [hEX, hEY, hEZ, martonInfo₂]
  ring

/-- Averaged alias bound at receiver 2.  For an arbitrary output law `ν`, drawing the alias
codeword independently of `ν` from the `V₂`-block law makes the probability that it is jointly
typical with the received word at most `exp(−n (I(V₂; Y₂) − 3ε))`.

@audit:ok -/
theorem marton_alias₂_slice_avg_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {n : ℕ} {ε : ℝ}
    (ν : Measure (Fin n → β₁ × β₂)) [IsProbabilityMeasure ν] :
    ∑ v : Fin n → V₂,
        (Measure.pi (fun _ : Fin n ↦ pV.map Prod.snd)).real {v}
          * ν.real { y : Fin n → β₁ × β₂ |
              (v, fun i ↦ (y i).2) ∈
                jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
      ≤ Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.snd : V₁ × V₂ → V₂)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact sum_measureReal_slice_le (Measure.pi fun _ : Fin n ↦ pV.map Prod.snd) ν
    { q : (Fin n → V₂) × (Fin n → β₁ × β₂) |
        (q.1, fun i ↦ (q.2 i).2) ∈
          jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
    (fun y ↦ marton_jointlyTypicalFiber₂_le pV K W hpV hK hW n (fun i ↦ (y i).2))

/-! ### The Marton codebook ensemble and the assembled broadcast code -/

section Codebooks

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [MeasurableSpace V]
  [MeasurableSingletonClass V]

/-- A Marton subcodebook: for each message and each covering index one length-`n` auxiliary
codeword.  The covering index is the over-provisioning that lets the encoder pick a jointly
typical pair of auxiliary codewords; unlike the message it is not decoded. -/
abbrev MartonSubcodebook (M M' n : ℕ) (V : Type*) [MeasurableSpace V] :=
  Codebook M M' (Fin n → V)

/-- The subcodebook law: `p`-i.i.d. over all `M · M' · n` auxiliary letters, read as a codebook
whose alphabet is the set of length-`n` words. -/
noncomputable def martonSubcodebookMeasure (p : Measure V) (M M' n : ℕ) :
    Measure (MartonSubcodebook M M' n V) :=
  codebookMeasure (Measure.pi fun _ : Fin n ↦ p) M M'

instance martonSubcodebookMeasure.instIsProbabilityMeasure
    (p : Measure V) [IsProbabilityMeasure p] (M M' n : ℕ) :
    IsProbabilityMeasure (martonSubcodebookMeasure p M M' n) := by
  unfold martonSubcodebookMeasure
  infer_instance

end Codebooks

/-- The encoder's covering choice for one message pair: an index pair whose two auxiliary
codewords are jointly *strongly* typical, falling back to `(0, 0)` when the two subcodebook rows
contain no such pair.  It reads only the two rows addressed by the message pair, which is what
keeps the codewords of every other row independent of the transmission.

Strong typicality — rather than the weak typicality the decoders use — is what pins the empirical
type of the selected pair, and hence, through the input kernel, the empirical type of the
transmitted `(V₁, X)` block that the receiver-1 conditional AEP consumes.  The selection radius
`ε_cov` is therefore a parameter of its own, independent of the decoding radius.

@audit:ok -/
noncomputable def martonSelectRow
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') (ε_cov : ℝ)
    (r₁ : Fin M₁' → (Fin n → V₁)) (r₂ : Fin M₂' → (Fin n → V₂)) : Fin M₁' × Fin M₂' :=
  haveI : Decidable (∃ l : Fin M₁' × Fin M₂', (r₁ l.1, r₂ l.2) ∈
      jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov) :=
    Classical.propDecidable _
  if h : ∃ l : Fin M₁' × Fin M₂', (r₁ l.1, r₂ l.2) ∈
      jointStronglyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonV₂s n ε_cov
    then Classical.choose h
    else (⟨0, hM₁'⟩, ⟨0, hM₂'⟩)

/-- The first auxiliary codeword actually transmitted for the message pair `m`. -/
noncomputable def martonAux₁
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') (ε_cov : ℝ)
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (m : Fin M₁ × Fin M₂) : Fin n → V₁ :=
  c₁ m.1 (martonSelectRow pV K W hM₁' hM₂' ε_cov (c₁ m.1) (c₂ m.2)).1

/-- The second auxiliary codeword actually transmitted for the message pair `m`. -/
noncomputable def martonAux₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') (ε_cov : ℝ)
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (m : Fin M₁ × Fin M₂) : Fin n → V₂ :=
  c₂ m.2 (martonSelectRow pV K W hM₁' hM₂' ε_cov (c₁ m.1) (c₂ m.2)).2

/-- The input codebook law *conditional on* the two subcodebooks: the input word of the message
pair `m` is drawn letterwise from `K` applied to the selected auxiliary pair, independently
across message pairs.  This is where the input randomization of a general kernel `K` is placed,
the deterministic `BroadcastCode.encoder` being fixed only after a pigeonhole step. -/
noncomputable def martonInputCodebookMeasure
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') (ε_cov : ℝ)
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂) :
    Measure (Fin M₁ × Fin M₂ → (Fin n → α)) :=
  Measure.pi fun m : Fin M₁ × Fin M₂ ↦
    Measure.pi fun l : Fin n ↦
      K (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m l,
        martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m l)

instance martonInputCodebookMeasure.instIsProbabilityMeasure
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂)
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') (ε_cov : ℝ)
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂) :
    IsProbabilityMeasure (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂) := by
  unfold martonInputCodebookMeasure
  infer_instance

/-- Receiver-1 decoder: return the unique *message* owning an auxiliary codeword jointly typical
with the received word, falling back to `⟨0, hM₁⟩` when there is none or more than one.  Only the
message is required to be unique — the covering index is quantified existentially, so a second
typical index inside the transmitted row is not an error. -/
noncomputable def martonMessageDecoder₁
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁ M₁' n : ℕ} (hM₁ : 0 < M₁) (ε : ℝ)
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) : (Fin n → β₁) → Fin M₁ := fun y₁ ↦
  haveI : Decidable (∃! w : Fin M₁, ∃ l : Fin M₁', (c₁ w l, y₁) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε) :=
    Classical.propDecidable _
  if h : ∃! w : Fin M₁, ∃ l : Fin M₁', (c₁ w l, y₁) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε
    then Classical.choose h.exists
    else ⟨0, hM₁⟩

/-- Receiver-2 decoder, the mirror image of `martonMessageDecoder₁`. -/
noncomputable def martonMessageDecoder₂
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₂ M₂' n : ℕ} (hM₂ : 0 < M₂) (ε : ℝ)
    (c₂ : MartonSubcodebook M₂ M₂' n V₂) : (Fin n → β₂) → Fin M₂ := fun y₂ ↦
  haveI : Decidable (∃! w : Fin M₂, ∃ l : Fin M₂', (c₂ w l, y₂) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε) :=
    Classical.propDecidable _
  if h : ∃! w : Fin M₂, ∃ l : Fin M₂', (c₂ w l, y₂) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε
    then Classical.choose h.exists
    else ⟨0, hM₂⟩

/-- Bundle two subcodebooks and an input codebook into a `BroadcastCode`: the input codebook is
the encoder, and each receiver runs its own message decoder over its own subcodebook. -/
noncomputable def martonCodebookToCode
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (cX : Fin M₁ × Fin M₂ → (Fin n → α)) :
    BroadcastCode M₁ M₂ n α β₁ β₂ where
  encoder := cX
  decoder₁ := martonMessageDecoder₁ pV K W hM₁ ε c₁
  decoder₂ := martonMessageDecoder₂ pV K W hM₂ ε c₂

/-! ### Receiver-1 error decomposition -/

private lemma martonMessageDecoder₁_eq_of_unique
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₁ M₁' n : ℕ} (hM₁ : 0 < M₁) {ε : ℝ}
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (y₁ : Fin n → β₁) (w : Fin M₁)
    (h : ∃! w : Fin M₁, ∃ l : Fin M₁', (c₁ w l, y₁) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε)
    (hw : ∃ l : Fin M₁', (c₁ w l, y₁) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε) :
    martonMessageDecoder₁ pV K W hM₁ ε c₁ y₁ = w := by
  unfold martonMessageDecoder₁
  rw [dif_pos h]
  exact h.unique (Classical.choose_spec h.exists) hw

/-- Receiver-1 error decomposition at a fixed message pair: the error probability is at most the
probability that the transmitted auxiliary word fails to be jointly typical with the received word,
plus the sum, over the auxiliary codewords of every other message row, of the probability that one
of them is jointly typical with it.  Quantifying the covering index existentially is what keeps a
second typical index inside the transmitted row off the error event, so the alias sum ranges over
the rows of the other messages only.

@audit:ok -/
theorem marton_errorProbAt₁_le_bonferroni
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov : ℝ}
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (cX : Fin M₁ × Fin M₂ → (Fin n → α)) (m : Fin M₁ × Fin M₂) :
    ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₁ W m).toReal
      ≤ (Measure.pi fun i ↦ W (cX m i)).real
          { y : Fin n → β₁ × β₂ |
            (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
              jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
        + ∑ q ∈ ((Finset.univ : Finset (Fin M₁)).erase m.1) ×ˢ (Finset.univ : Finset (Fin M₁')),
            (Measure.pi fun i ↦ W (cX m i)).real
              { y : Fin n → β₁ × β₂ |
                (c₁ q.1 q.2, fun i ↦ (y i).1) ∈
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } := by
  classical
  set J : Set ((Fin n → V₁) × (Fin n → β₁)) :=
    jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε with hJ_def
  set c : BroadcastCode M₁ M₂ n α β₁ β₂ :=
    martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX with hc_def
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi (fun i ↦ W (cX m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  set S : Finset (Fin M₁ × Fin M₁') :=
    ((Finset.univ : Finset (Fin M₁)).erase m.1) ×ˢ (Finset.univ : Finset (Fin M₁')) with hS_def
  set E1 : Set (Fin n → β₁ × β₂) :=
    { y | (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉ J } with hE1_def
  set Ea : Fin M₁ × Fin M₁' → Set (Fin n → β₁ × β₂) :=
    fun q ↦ { y | (c₁ q.1 q.2, fun i ↦ (y i).1) ∈ J } with hEa_def
  have h_sub : c.errorEvent₁ m ⊆ E1 ∪ ⋃ q ∈ S, Ea q := by
    intro y hy
    rw [BroadcastCode.errorEvent₁, Set.mem_setOf_eq] at hy
    set y₁ : Fin n → β₁ := fun i ↦ (y i).1 with hy₁_def
    by_cases htrue : (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, y₁) ∈ J
    · by_cases halias : ∃ q : Fin M₁ × Fin M₁', q.1 ≠ m.1 ∧ (c₁ q.1 q.2, y₁) ∈ J
      · obtain ⟨q, hq_ne, hq_mem⟩ := halias
        refine Or.inr (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨?_, hq_mem⟩⟩)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_erase.mpr ⟨hq_ne, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · exfalso
        apply hy
        have hex : ∃ l : Fin M₁', (c₁ m.1 l, y₁) ∈ J :=
          ⟨(martonSelectRow pV K W hM₁' hM₂' ε_cov (c₁ m.1) (c₂ m.2)).1, htrue⟩
        have huniq : ∃! w : Fin M₁, ∃ l : Fin M₁', (c₁ w l, y₁) ∈ J := by
          refine ⟨m.1, hex, ?_⟩
          intro w hw
          by_contra hne
          obtain ⟨l, hl⟩ := hw
          exact halias ⟨(w, l), hne, hl⟩
        exact martonMessageDecoder₁_eq_of_unique pV K W hM₁ c₁ y₁ m.1 huniq hex
    · exact Or.inl htrue
  have h_real_eq : (c.errorProbAt₁ W m).toReal = ν.real (c.errorEvent₁ m) := rfl
  rw [h_real_eq]
  calc ν.real (c.errorEvent₁ m)
      ≤ ν.real (E1 ∪ ⋃ q ∈ S, Ea q) := measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ν.real E1 + ν.real (⋃ q ∈ S, Ea q) := measureReal_union_le _ _
    _ ≤ ν.real E1 + ∑ q ∈ S, ν.real (Ea q) :=
        add_le_add le_rfl (measureReal_biUnion_finset_le _ _)

/-- The message-averaged form of `marton_errorProbAt₁_le_bonferroni`: averaging the pointwise
decomposition over all message pairs bounds the receiver-1 average error probability by the mean
of the transmitted-pair term and of the alias sum.  The bound holds at every selection radius
`ε_cov`, which is what lets the covering radius be chosen independently of the decoding radius.

@audit:ok -/
theorem marton_averageErrorProb₁_toReal_le
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov : ℝ}
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (cX : Fin M₁ × Fin M₂ → (Fin n → α)) :
    ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁ W).toReal
      ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((Measure.pi fun i ↦ W (cX m i)).real
              { y : Fin n → β₁ × β₂ |
                (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).1) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε }
            + ∑ q ∈ ((Finset.univ : Finset (Fin M₁)).erase m.1) ×ˢ
                      (Finset.univ : Finset (Fin M₁')),
                (Measure.pi fun i ↦ W (cX m i)).real
                  { y : Fin n → β₁ × β₂ |
                    (c₁ q.1 q.2, fun i ↦ (y i).1) ∈
                      jointlyTypicalSet (martonAmbientMeasure pV K W)
                        martonV₁s martonY₁s n ε }) := by
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have h_ne_top : ∀ m : Fin M₁ × Fin M₂,
      (martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₁ W m ≠ ⊤ :=
    fun m ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₁_le_one W m)
  have h_eq : ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₁ W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₁ W m).toReal := by
    unfold BroadcastCode.averageErrorProb₁
    rw [if_neg hMpos.ne', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun m _ ↦
    marton_errorProbAt₁_le_bonferroni pV K W hM₁ hM₂ hM₁' hM₂' c₁ c₂ cX m

/-! ### Receiver-1 alias bound over the random ensemble -/

private lemma sum_codebook_alias_le
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (p : Measure A) [IsProbabilityMeasure p] {M M' n : ℕ}
    (m₁ : Fin M) (q : Fin M × Fin M') (hne : q.1 ≠ m₁)
    (Φ : (Fin M' → (Fin n → A)) → (Fin n → A) → ℝ) {C : ℝ}
    (hΦ_nn : ∀ r v, 0 ≤ Φ r v)
    (hΦ : ∀ r, ∑ v : Fin n → A, (Measure.pi fun _ : Fin n ↦ p).real {v} * Φ r v ≤ C) :
    ∑ c : Codebook M M' (Fin n → A),
        (codebookMeasure (Measure.pi fun _ : Fin n ↦ p) M M').real {c} * Φ (c m₁) (c q.1 q.2)
      ≤ C := by
  classical
  have hrow : ∀ r : Fin M' → (Fin n → A),
      ∑ r' : Fin M' → (Fin n → A), (codebookMeasure p M' n).real {r'} * Φ r (r' q.2) ≤ C := by
    intro r
    rw [codebook_marginal_one p M' n q.2 (Φ r) (hΦ_nn r)]
    exact hΦ r
  rw [codebook_marginal_two (Measure.pi fun _ : Fin n ↦ p) M M' m₁ q.1 (Ne.symm hne)
    (fun r r' ↦ Φ r (r' q.2)) (fun r r' ↦ hΦ_nn r (r' q.2))]
  calc ∑ r : Fin M' → (Fin n → A), ∑ r' : Fin M' → (Fin n → A),
          (codebookMeasure p M' n).real {r} * (codebookMeasure p M' n).real {r'} * Φ r (r' q.2)
      = ∑ r : Fin M' → (Fin n → A), (codebookMeasure p M' n).real {r}
          * ∑ r' : Fin M' → (Fin n → A), (codebookMeasure p M' n).real {r'} * Φ r (r' q.2) := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r' _ ↦ (mul_assoc _ _ _)
    _ ≤ ∑ r : Fin M' → (Fin n → A), (codebookMeasure p M' n).real {r} * C :=
        Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_left (hrow r) measureReal_nonneg
    _ = C := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]

/-- Averaged alias bound over the full three-tier Marton ensemble.  An alias codeword taken from
a *different message row* than the transmitted one is jointly typical with the received word with
probability at most `exp(−n (I(V₁; Y₁) − 3ε))`.  The covering choice reads only the transmitted
rows, so the alias row stays independent of the transmission even though the choice depends on
the codebook; and because the fiber bound behind `marton_alias₁_slice_avg_le` is uniform over
received words, the law of the received word never has to be identified.  The estimate reads the
selection only through the fact that it yields a probability law on input words, so it is
insensitive to the radius and to the typicality notion the selection tests.

@audit:ok -/
theorem marton_random_codebook_alias₁_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') {ε ε_cov : ℝ}
    (m : Fin M₁ × Fin M₂) (q : Fin M₁ × Fin M₁') (hne : q.1 ≠ m.1) :
    ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * (Measure.pi fun i ↦ W (cX m i)).real
                          { y : Fin n → β₁ × β₂ |
                            (c₁ q.1 q.2, fun i ↦ (y i).1) ∈
                              jointlyTypicalSet (martonAmbientMeasure pV K W)
                                martonV₁s martonY₁s n ε }
      ≤ Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.fst : V₁ × V₂ → V₁)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (pV.map (Prod.snd : V₁ × V₂ → V₂)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  -- The transmitted input law, as a function of the two transmitted subcodebook rows.
  set L : (Fin M₁' → (Fin n → V₁)) → (Fin M₂' → (Fin n → V₂)) → Measure (Fin n → α) :=
    fun r s ↦ Measure.pi fun l : Fin n ↦
      K (r (martonSelectRow pV K W hM₁' hM₂' ε_cov r s).1 l,
        s (martonSelectRow pV K W hM₁' hM₂' ε_cov r s).2 l) with hL_def
  have hLprob : ∀ r s, IsProbabilityMeasure (L r s) := by
    intro r s
    rw [hL_def]
    infer_instance
  -- The payoff of one alias codeword against one transmitted input word.
  set G : (Fin n → V₁) → (Fin n → α) → ℝ := fun v x ↦
    (Measure.pi fun i ↦ W (x i)).real
      { y : Fin n → β₁ × β₂ | (v, fun i ↦ (y i).1) ∈
        jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₁s martonY₁s n ε } with hG_def
  -- Step 1: marginalize the input codebook to the transmitted row.
  have step1 : ∀ (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂),
      (∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
          (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
            * G (c₁ q.1 q.2) (cX m))
        = ∑ x : Fin n → α, (L (c₁ m.1) (c₂ m.2)).real {x} * G (c₁ q.1 q.2) x := by
    intro c₁ c₂
    have hmp : (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).map (Function.eval m)
        = L (c₁ m.1) (c₂ m.2) :=
      (measurePreserving_eval (fun m' : Fin M₁ × Fin M₂ ↦
        Measure.pi fun l : Fin n ↦
          K (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m' l,
            martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m' l)) m).map_eq
    have h1 := sum_weighted_map (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂)
      (Function.eval m) (measurable_pi_apply m) (G (c₁ q.1 q.2))
    rw [hmp] at h1
    exact h1
  -- Step 2: fold the input tier away and separate the alias row from the transmitted row.
  have hgoal : (∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * G (c₁ q.1 q.2) (cX m))
      = ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
          (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
            * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
                (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                  * ∑ x : Fin n → α, (L (c₁ m.1) (c₂ m.2)).real {x} * G (c₁ q.1 q.2) x := by
    refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
    congr 1
    refine Finset.sum_congr rfl fun c₂ _ ↦ ?_
    congr 1
    exact step1 c₁ c₂
  rw [hgoal]
  refine sum_codebook_alias_le (pV.map Prod.fst) m.1 q hne
    (fun r v ↦ ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
      (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
        * ∑ x : Fin n → α, (L r (c₂ m.2)).real {x} * G v x) ?_ ?_
  · intro r v
    exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg
      (Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg)
  · intro r
    rw [sum_exchange_three
      (fun v : Fin n → V₁ ↦ (Measure.pi fun _ : Fin n ↦ pV.map (Prod.fst : V₁ × V₂ → V₁)).real {v})
      (fun c₂ : MartonSubcodebook M₂ M₂' n V₂ ↦
        (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂})
      (fun c₂ x ↦ (L r (c₂ m.2)).real {x}) G]
    have hinner : ∀ x : Fin n → α,
        (∑ v : Fin n → V₁,
          (Measure.pi fun _ : Fin n ↦ pV.map (Prod.fst : V₁ × V₂ → V₁)).real {v} * G v x)
          ≤ Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
      intro x
      exact marton_alias₁_slice_avg_le pV K W hpV hK hW (Measure.pi fun i ↦ W (x i))
    calc ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
            (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
              * ∑ x : Fin n → α, (L r (c₂ m.2)).real {x}
                  * ∑ v : Fin n → V₁,
                      (Measure.pi fun _ : Fin n ↦
                        pV.map (Prod.fst : V₁ × V₂ → V₁)).real {v} * G v x
        ≤ ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
            (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
              * ∑ x : Fin n → α, (L r (c₂ m.2)).real {x}
                  * Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
          refine Finset.sum_le_sum fun c₂ _ ↦ mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          exact Finset.sum_le_sum fun x _ ↦
            mul_le_mul_of_nonneg_left (hinner x) measureReal_nonneg
      _ = Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
          have hx : ∀ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (∑ x : Fin n → α, (L r (c₂ m.2)).real {x}
                * Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)))
                = Real.exp (-(n : ℝ) * (martonInfo₁ pV K W - 3 * ε)) := by
            intro c₂
            haveI := hLprob r (c₂ m.2)
            rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]
          simp only [hx]
          rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]

/-! ### Receiver-2 error decomposition -/

private lemma martonMessageDecoder₂_eq_of_unique
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂)
    {M₂ M₂' n : ℕ} (hM₂ : 0 < M₂) {ε : ℝ}
    (c₂ : MartonSubcodebook M₂ M₂' n V₂) (y₂ : Fin n → β₂) (w : Fin M₂)
    (h : ∃! w : Fin M₂, ∃ l : Fin M₂', (c₂ w l, y₂) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε)
    (hw : ∃ l : Fin M₂', (c₂ w l, y₂) ∈
      jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε) :
    martonMessageDecoder₂ pV K W hM₂ ε c₂ y₂ = w := by
  unfold martonMessageDecoder₂
  rw [dif_pos h]
  exact h.unique (Classical.choose_spec h.exists) hw

/-- Receiver-2 error decomposition at a fixed message pair, the mirror image of
`marton_errorProbAt₁_le_bonferroni`: the error probability is at most the probability that the
transmitted auxiliary word fails to be jointly typical with the received word, plus the sum, over
the auxiliary codewords of every other message row, of the probability that one of them is jointly
typical with it.

@audit:ok -/
theorem marton_errorProbAt₂_le_bonferroni
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov : ℝ}
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (cX : Fin M₁ × Fin M₂ → (Fin n → α)) (m : Fin M₁ × Fin M₂) :
    ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₂ W m).toReal
      ≤ (Measure.pi fun i ↦ W (cX m i)).real
          { y : Fin n → β₁ × β₂ |
            (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
              jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
        + ∑ q ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ (Finset.univ : Finset (Fin M₂')),
            (Measure.pi fun i ↦ W (cX m i)).real
              { y : Fin n → β₁ × β₂ |
                (c₂ q.1 q.2, fun i ↦ (y i).2) ∈
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε } := by
  classical
  set J : Set ((Fin n → V₂) × (Fin n → β₂)) :=
    jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε with hJ_def
  set c : BroadcastCode M₁ M₂ n α β₁ β₂ :=
    martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX with hc_def
  set ν : Measure (Fin n → β₁ × β₂) := Measure.pi (fun i ↦ W (cX m i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  set S : Finset (Fin M₂ × Fin M₂') :=
    ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ (Finset.univ : Finset (Fin M₂')) with hS_def
  set E1 : Set (Fin n → β₁ × β₂) :=
    { y | (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉ J } with hE1_def
  set Ea : Fin M₂ × Fin M₂' → Set (Fin n → β₁ × β₂) :=
    fun q ↦ { y | (c₂ q.1 q.2, fun i ↦ (y i).2) ∈ J } with hEa_def
  have h_sub : c.errorEvent₂ m ⊆ E1 ∪ ⋃ q ∈ S, Ea q := by
    intro y hy
    rw [BroadcastCode.errorEvent₂, Set.mem_setOf_eq] at hy
    set y₂ : Fin n → β₂ := fun i ↦ (y i).2 with hy₂_def
    by_cases htrue : (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, y₂) ∈ J
    · by_cases halias : ∃ q : Fin M₂ × Fin M₂', q.1 ≠ m.2 ∧ (c₂ q.1 q.2, y₂) ∈ J
      · obtain ⟨q, hq_ne, hq_mem⟩ := halias
        refine Or.inr (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨?_, hq_mem⟩⟩)
        exact Finset.mem_product.mpr
          ⟨Finset.mem_erase.mpr ⟨hq_ne, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · exfalso
        apply hy
        have hex : ∃ l : Fin M₂', (c₂ m.2 l, y₂) ∈ J :=
          ⟨(martonSelectRow pV K W hM₁' hM₂' ε_cov (c₁ m.1) (c₂ m.2)).2, htrue⟩
        have huniq : ∃! w : Fin M₂, ∃ l : Fin M₂', (c₂ w l, y₂) ∈ J := by
          refine ⟨m.2, hex, ?_⟩
          intro w hw
          by_contra hne
          obtain ⟨l, hl⟩ := hw
          exact halias ⟨(w, l), hne, hl⟩
        exact martonMessageDecoder₂_eq_of_unique pV K W hM₂ c₂ y₂ m.2 huniq hex
    · exact Or.inl htrue
  have h_real_eq : (c.errorProbAt₂ W m).toReal = ν.real (c.errorEvent₂ m) := rfl
  rw [h_real_eq]
  calc ν.real (c.errorEvent₂ m)
      ≤ ν.real (E1 ∪ ⋃ q ∈ S, Ea q) := measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ν.real E1 + ν.real (⋃ q ∈ S, Ea q) := measureReal_union_le _ _
    _ ≤ ν.real E1 + ∑ q ∈ S, ν.real (Ea q) :=
        add_le_add le_rfl (measureReal_biUnion_finset_le _ _)

/-- The message-averaged form of `marton_errorProbAt₂_le_bonferroni`: averaging the pointwise
decomposition over all message pairs bounds the receiver-2 average error probability by the mean
of the transmitted-pair term and of the alias sum.

@audit:ok -/
theorem marton_averageErrorProb₂_toReal_le
    (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂')
    {ε ε_cov : ℝ}
    (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂)
    (cX : Fin M₁ × Fin M₂ → (Fin n → α)) :
    ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂ W).toReal
      ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((Measure.pi fun i ↦ W (cX m i)).real
              { y : Fin n → β₁ × β₂ |
                (martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m, fun i ↦ (y i).2) ∉
                  jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε }
            + ∑ q ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                      (Finset.univ : Finset (Fin M₂')),
                (Measure.pi fun i ↦ W (cX m i)).real
                  { y : Fin n → β₁ × β₂ |
                    (c₂ q.1 q.2, fun i ↦ (y i).2) ∈
                      jointlyTypicalSet (martonAmbientMeasure pV K W)
                        martonV₂s martonY₂s n ε }) := by
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have h_ne_top : ∀ m : Fin M₁ × Fin M₂,
      (martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₂ W m ≠ ⊤ :=
    fun m ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₂_le_one W m)
  have h_eq : ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).averageErrorProb₂ W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((martonCodebookToCode pV K W hM₁ hM₂ ε c₁ c₂ cX).errorProbAt₂ W m).toReal := by
    unfold BroadcastCode.averageErrorProb₂
    rw [if_neg hMpos.ne', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun m _ ↦
    marton_errorProbAt₂_le_bonferroni pV K W hM₁ hM₂ hM₁' hM₂' c₁ c₂ cX m

/-! ### Receiver-2 alias bound over the random ensemble -/

/-- Averaged alias bound over the full three-tier Marton ensemble at receiver 2, the mirror image
of `marton_random_codebook_alias₁_le`.  An alias codeword taken from a *different message row*
than the transmitted one is jointly typical with the received word with probability at most
`exp(−n (I(V₂; Y₂) − 3ε))`.  The ensemble is summed in the same order as at receiver 1, the alias
row now sitting in the inner subcodebook tier.

@audit:ok -/
theorem marton_random_codebook_alias₂_le
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ M₁' M₂' n : ℕ} (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') {ε ε_cov : ℝ}
    (m : Fin M₁ × Fin M₂) (q : Fin M₂ × Fin M₂') (hne : q.1 ≠ m.2) :
    ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * (Measure.pi fun i ↦ W (cX m i)).real
                          { y : Fin n → β₁ × β₂ |
                            (c₂ q.1 q.2, fun i ↦ (y i).2) ∈
                              jointlyTypicalSet (martonAmbientMeasure pV K W)
                                martonV₂s martonY₂s n ε }
      ≤ Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
  classical
  haveI : IsProbabilityMeasure (pV.map (Prod.fst : V₁ × V₂ → V₁)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (pV.map (Prod.snd : V₁ × V₂ → V₂)) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  -- The transmitted input law, as a function of the two transmitted subcodebook rows.
  set L : (Fin M₁' → (Fin n → V₁)) → (Fin M₂' → (Fin n → V₂)) → Measure (Fin n → α) :=
    fun r s ↦ Measure.pi fun l : Fin n ↦
      K (r (martonSelectRow pV K W hM₁' hM₂' ε_cov r s).1 l,
        s (martonSelectRow pV K W hM₁' hM₂' ε_cov r s).2 l) with hL_def
  have hLprob : ∀ r s, IsProbabilityMeasure (L r s) := by
    intro r s
    rw [hL_def]
    infer_instance
  -- The payoff of one alias codeword against one transmitted input word.
  set G : (Fin n → V₂) → (Fin n → α) → ℝ := fun v x ↦
    (Measure.pi fun i ↦ W (x i)).real
      { y : Fin n → β₁ × β₂ | (v, fun i ↦ (y i).2) ∈
        jointlyTypicalSet (martonAmbientMeasure pV K W) martonV₂s martonY₂s n ε } with hG_def
  -- Step 1: marginalize the input codebook to the transmitted row.
  have step1 : ∀ (c₁ : MartonSubcodebook M₁ M₁' n V₁) (c₂ : MartonSubcodebook M₂ M₂' n V₂),
      (∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
          (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
            * G (c₂ q.1 q.2) (cX m))
        = ∑ x : Fin n → α, (L (c₁ m.1) (c₂ m.2)).real {x} * G (c₂ q.1 q.2) x := by
    intro c₁ c₂
    have hmp : (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).map (Function.eval m)
        = L (c₁ m.1) (c₂ m.2) :=
      (measurePreserving_eval (fun m' : Fin M₁ × Fin M₂ ↦
        Measure.pi fun l : Fin n ↦
          K (martonAux₁ pV K W hM₁' hM₂' ε_cov c₁ c₂ m' l,
            martonAux₂ pV K W hM₁' hM₂' ε_cov c₁ c₂ m' l)) m).map_eq
    have h1 := sum_weighted_map (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂)
      (Function.eval m) (measurable_pi_apply m) (G (c₂ q.1 q.2))
    rw [hmp] at h1
    exact h1
  -- Step 2: fold the input tier away, leaving the alias row inside the second subcodebook tier.
  have hgoal : (∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
        (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
          * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
              (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                * ∑ cX : Fin M₁ × Fin M₂ → (Fin n → α),
                    (martonInputCodebookMeasure pV K W hM₁' hM₂' ε_cov c₁ c₂).real {cX}
                      * G (c₂ q.1 q.2) (cX m))
      = ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
          (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
            * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
                (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                  * ∑ x : Fin n → α, (L (c₁ m.1) (c₂ m.2)).real {x} * G (c₂ q.1 q.2) x := by
    refine Finset.sum_congr rfl fun c₁ _ ↦ ?_
    congr 1
    refine Finset.sum_congr rfl fun c₂ _ ↦ ?_
    congr 1
    exact step1 c₁ c₂
  rw [hgoal]
  -- Step 3: at each first-tier codebook, the second tier carries the alias row on its own.
  have hsecond : ∀ c₁ : MartonSubcodebook M₁ M₁' n V₁,
      (∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
          (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
            * ∑ x : Fin n → α, (L (c₁ m.1) (c₂ m.2)).real {x} * G (c₂ q.1 q.2) x)
        ≤ Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
    intro c₁
    refine sum_codebook_alias_le (pV.map Prod.snd) m.2 q hne
      (fun r v ↦ ∑ x : Fin n → α, (L (c₁ m.1) r).real {x} * G v x) ?_ ?_
    · intro r v
      exact Finset.sum_nonneg fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg
    · intro r
      haveI := hLprob (c₁ m.1) r
      have hslice : ∀ x : Fin n → α,
          (∑ v : Fin n → V₂,
            (Measure.pi fun _ : Fin n ↦ pV.map (Prod.snd : V₁ × V₂ → V₂)).real {v} * G v x)
            ≤ Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
        intro x
        exact marton_alias₂_slice_avg_le pV K W hpV hK hW (Measure.pi fun i ↦ W (x i))
      have hswap : (∑ v : Fin n → V₂,
            (Measure.pi fun _ : Fin n ↦ pV.map (Prod.snd : V₁ × V₂ → V₂)).real {v}
              * ∑ x : Fin n → α, (L (c₁ m.1) r).real {x} * G v x)
          = ∑ x : Fin n → α, (L (c₁ m.1) r).real {x}
              * ∑ v : Fin n → V₂,
                  (Measure.pi fun _ : Fin n ↦
                    pV.map (Prod.snd : V₁ × V₂ → V₂)).real {v} * G v x := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ ↦
          Finset.sum_congr rfl fun v _ ↦ by ring
      rw [hswap]
      calc ∑ x : Fin n → α, (L (c₁ m.1) r).real {x}
              * ∑ v : Fin n → V₂,
                  (Measure.pi fun _ : Fin n ↦
                    pV.map (Prod.snd : V₁ × V₂ → V₂)).real {v} * G v x
          ≤ ∑ x : Fin n → α, (L (c₁ m.1) r).real {x}
              * Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) :=
            Finset.sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left (hslice x) measureReal_nonneg
        _ = Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
            rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]
  calc ∑ c₁ : MartonSubcodebook M₁ M₁' n V₁,
          (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {c₁}
            * ∑ c₂ : MartonSubcodebook M₂ M₂' n V₂,
                (martonSubcodebookMeasure (pV.map Prod.snd) M₂ M₂' n).real {c₂}
                  * ∑ x : Fin n → α, (L (c₁ m.1) (c₂ m.2)).real {x} * G (c₂ q.1 q.2) x
      ≤ ∑ _c₁ : MartonSubcodebook M₁ M₁' n V₁,
          (martonSubcodebookMeasure (pV.map Prod.fst) M₁ M₁' n).real {_c₁}
            * Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) :=
        Finset.sum_le_sum fun c₁ _ ↦
          mul_le_mul_of_nonneg_left (hsecond c₁) measureReal_nonneg
    _ = Real.exp (-(n : ℝ) * (martonInfo₂ pV K W - 3 * ε)) := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_univ_eq_one, one_mul]

end InformationTheory.Shannon.BroadcastChannel.Marton

