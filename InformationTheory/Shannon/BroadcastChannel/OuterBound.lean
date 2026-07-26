import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Operational
import InformationTheory.Shannon.ChannelCoding.StrongConverseAsymptotic

/-!
# Broadcast channel — cooperative outer bound

The first outer bound on the operational capacity region of a general two-receiver broadcast
channel.  Each receiver alone, and the two receivers pooling their outputs, form single-user
channels, so the single-user converse applies three times and bounds the two individual rates
and their sum by the corresponding capacities.

The reductions are code transformations: freezing one message index turns a broadcast code into
a single-user code for the other receiver over the marginal channel, and pairing the two message
indices turns it into a single-user code over the channel with the output pair as its output.

## Main definitions

* `BroadcastCode.restrict₁` / `BroadcastCode.restrict₂` — the single-user code obtained by
  freezing the message of the other receiver.
* `BroadcastCode.coop` — the single-user code for the cooperative receiver that sees both
  outputs and decodes the message pair.
* `bcOuterRegionCoop W` — the cooperative outer region, the intersection of the three half
  planes cut out by the capacities of the two marginal channels and of the channel itself.

## Main statements

* `bc_capacity_subset_coop` — the operational capacity region is contained in the cooperative
  outer region.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

namespace BroadcastCode

section Reduction

variable {M₁ M₂ n : ℕ} {α β₁ β₂ : Type*}
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The single-user code for receiver 1 obtained from a broadcast code by freezing the message
of receiver 2: the encoder sends the receiver-1 message paired with the frozen index, and the
decoder is the receiver-1 decoder. -/
def restrict₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₂ : Fin M₂) : Code M₁ n α β₁ where
  encoder m₁ := c.encoder (m₁, m₂)
  decoder := c.decoder₁

/-- The single-user code for receiver 2 obtained from a broadcast code by freezing the message
of receiver 1. -/
def restrict₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m₁ : Fin M₁) : Code M₂ n α β₂ where
  encoder m₂ := c.encoder (m₁, m₂)
  decoder := c.decoder₂

/-- The single-user code for the cooperative receiver: one message for the pair, and a decoder
that runs both broadcast decoders on their own output coordinate and pairs the answers. -/
def coop (c : BroadcastCode M₁ M₂ n α β₁ β₂) : Code (M₁ * M₂) n α (β₁ × β₂) where
  encoder m := c.encoder (finProdFinEquiv.symm m)
  decoder y := finProdFinEquiv (c.decoder₁ fun i ↦ (y i).1, c.decoder₂ fun i ↦ (y i).2)

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₂] [MeasurableSingletonClass β₂] in
lemma errorProbAt_restrict₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (m₁ : Fin M₁) (m₂ : Fin M₂) :
    (c.restrict₁ m₂).errorProbAt (Kernel.fst W) m₁ = c.errorProbAt₁ W (m₁, m₂) := by
  classical
  have hproj : Measurable fun (y : Fin n → β₁ × β₂) (i : Fin n) ↦ (y i).1 :=
    measurable_pi_lambda _ fun i ↦ measurable_fst.comp (measurable_pi_apply i)
  have hE : MeasurableSet ((c.restrict₁ m₂).errorEvent m₁) := (Set.toFinite _).measurableSet
  haveI : ∀ i : Fin n, IsProbabilityMeasure ((W (c.encoder (m₁, m₂) i)).map Prod.fst) :=
    fun _ ↦ Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hpi : (Measure.pi fun i : Fin n ↦ W (c.encoder (m₁, m₂) i)).map
      (fun (y : Fin n → β₁ × β₂) (i : Fin n) ↦ (y i).1)
      = Measure.pi fun i : Fin n ↦ (W (c.encoder (m₁, m₂) i)).map Prod.fst :=
    Measure.pi_map_pi fun _ ↦ measurable_fst.aemeasurable
  have hset : c.errorEvent₁ (m₁, m₂)
      = (fun (y : Fin n → β₁ × β₂) (i : Fin n) ↦ (y i).1) ⁻¹'
        ((c.restrict₁ m₂).errorEvent m₁) := rfl
  unfold Code.errorProbAt errorProbAt₁ blockOutputLaw
  rw [hset, ← Measure.map_apply hproj hE, hpi]
  simp only [Kernel.fst_apply]
  rfl

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₁] [MeasurableSingletonClass β₁] in
lemma errorProbAt_restrict₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] (m₁ : Fin M₁) (m₂ : Fin M₂) :
    (c.restrict₂ m₁).errorProbAt (Kernel.snd W) m₂ = c.errorProbAt₂ W (m₁, m₂) := by
  classical
  have hproj : Measurable fun (y : Fin n → β₁ × β₂) (i : Fin n) ↦ (y i).2 :=
    measurable_pi_lambda _ fun i ↦ measurable_snd.comp (measurable_pi_apply i)
  have hE : MeasurableSet ((c.restrict₂ m₁).errorEvent m₂) := (Set.toFinite _).measurableSet
  haveI : ∀ i : Fin n, IsProbabilityMeasure ((W (c.encoder (m₁, m₂) i)).map Prod.snd) :=
    fun _ ↦ Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hpi : (Measure.pi fun i : Fin n ↦ W (c.encoder (m₁, m₂) i)).map
      (fun (y : Fin n → β₁ × β₂) (i : Fin n) ↦ (y i).2)
      = Measure.pi fun i : Fin n ↦ (W (c.encoder (m₁, m₂) i)).map Prod.snd :=
    Measure.pi_map_pi fun _ ↦ measurable_snd.aemeasurable
  have hset : c.errorEvent₂ (m₁, m₂)
      = (fun (y : Fin n → β₁ × β₂) (i : Fin n) ↦ (y i).2) ⁻¹'
        ((c.restrict₂ m₁).errorEvent m₂) := rfl
  unfold Code.errorProbAt errorProbAt₂ blockOutputLaw
  rw [hset, ← Measure.map_apply hproj hE, hpi]
  simp only [Kernel.snd_apply]
  rfl

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSingletonClass β₂] in
lemma errorProbAt_coop_le (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    (m : Fin (M₁ * M₂)) :
    c.coop.errorProbAt W m
      ≤ c.errorProbAt₁ W (finProdFinEquiv.symm m) + c.errorProbAt₂ W (finProdFinEquiv.symm m) := by
  classical
  have hsub : c.coop.errorEvent m
      ⊆ c.errorEvent₁ (finProdFinEquiv.symm m) ∪ c.errorEvent₂ (finProdFinEquiv.symm m) := by
    intro y hy
    simp only [Code.errorEvent, Code.decodingRegion, Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    by_contra hcon
    simp only [Set.mem_union, not_or, errorEvent₁, errorEvent₂, Set.mem_setOf_eq,
      not_not] at hcon
    refine hy ?_
    show finProdFinEquiv (c.decoder₁ fun i ↦ (y i).1, c.decoder₂ fun i ↦ (y i).2) = m
    have hpair : ((c.decoder₁ fun i ↦ (y i).1), (c.decoder₂ fun i ↦ (y i).2))
        = finProdFinEquiv.symm m := Prod.ext hcon.1 hcon.2
    rw [hpair, Equiv.apply_symm_apply]
  calc c.coop.errorProbAt W m
      ≤ (Measure.pi fun i ↦ W (c.encoder (finProdFinEquiv.symm m) i))
        (c.errorEvent₁ (finProdFinEquiv.symm m) ∪ c.errorEvent₂ (finProdFinEquiv.symm m)) :=
        measure_mono hsub
    _ ≤ _ := measure_union_le _ _

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSingletonClass β₂] in
lemma averageErrorProb₁_le_one (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] : c.averageErrorProb₁ W ≤ 1 := by
  unfold averageErrorProb₁
  by_cases hM : M₁ * M₂ = 0
  · simp [hM]
  · simp only [hM, if_false]
    have hsum : (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m) ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by
      calc (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m)
          ≤ ∑ _m : Fin M₁ × Fin M₂, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun m _ ↦ c.errorProbAt₁_le_one W m
        _ = ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by simp
    calc ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m
        ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ((M₁ * M₂ : ℕ) : ℝ≥0∞) := mul_le_mul_right hsum _
      _ = 1 := ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSingletonClass β₂] in
lemma averageErrorProb₂_le_one (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] : c.averageErrorProb₂ W ≤ 1 := by
  unfold averageErrorProb₂
  by_cases hM : M₁ * M₂ = 0
  · simp [hM]
  · simp only [hM, if_false]
    have hsum : (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₂ W m) ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by
      calc (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₂ W m)
          ≤ ∑ _m : Fin M₁ × Fin M₂, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun m _ ↦ c.errorProbAt₂_le_one W m
        _ = ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by simp
    calc ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt₂ W m
        ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ((M₁ * M₂ : ℕ) : ℝ≥0∞) := mul_le_mul_right hsum _
      _ = 1 := ENNReal.inv_mul_cancel (by exact_mod_cast hM) (ENNReal.natCast_ne_top _)

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₂] [MeasurableSingletonClass β₂] in
lemma exists_averageErrorProb_restrict₁_le (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    ∃ m₂ : Fin M₂,
      (c.restrict₁ m₂).averageErrorProb (Kernel.fst W) ≤ c.averageErrorProb₁ W := by
  classical
  haveI : Nonempty (Fin M₂) := Fin.pos_iff_nonempty.mp hM₂
  set f : Fin M₂ → ℝ≥0∞ := fun m₂ ↦ ∑ m₁ : Fin M₁, c.errorProbAt₁ W (m₁, m₂) with hf
  obtain ⟨m₂, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin M₂)) f
    ⟨Classical.arbitrary (Fin M₂), Finset.mem_univ _⟩
  refine ⟨m₂, ?_⟩
  have hM₁ne : ((M₁ : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM₁.ne'
  have hM₂ne : ((M₂ : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM₂.ne'
  have hLHS : (c.restrict₁ m₂).averageErrorProb (Kernel.fst W)
      = ((M₁ : ℕ) : ℝ≥0∞)⁻¹ * f m₂ := by
    unfold Code.averageErrorProb
    rw [if_neg hM₁.ne']
    exact congrArg _ (Finset.sum_congr rfl fun m₁ _ ↦ c.errorProbAt_restrict₁ W m₁ m₂)
  have hsplit : (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m) = ∑ m₂' : Fin M₂, f m₂' := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hRHS : c.averageErrorProb₁ W = ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₂' : Fin M₂, f m₂' := by
    unfold averageErrorProb₁
    rw [if_neg (Nat.mul_ne_zero hM₁.ne' hM₂.ne'), hsplit]
  have hcard : ((M₂ : ℕ) : ℝ≥0∞) * f m₂ ≤ ∑ m₂' : Fin M₂, f m₂' := by
    have h := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin M₂)) f (f m₂)
      fun i hi ↦ hmin i hi
    simpa [Finset.card_univ, nsmul_eq_mul] using h
  rw [hLHS, hRHS]
  calc ((M₁ : ℕ) : ℝ≥0∞)⁻¹ * f m₂
      = ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * (((M₂ : ℕ) : ℝ≥0∞) * f m₂) := by
        rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hM₁ne) (Or.inr hM₂ne), mul_assoc,
          ← mul_assoc (((M₂ : ℕ) : ℝ≥0∞)⁻¹),
          ENNReal.inv_mul_cancel hM₂ne (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₂' : Fin M₂, f m₂' := mul_le_mul_right hcard _

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₁] [MeasurableSingletonClass β₁] in
lemma exists_averageErrorProb_restrict₂_le (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    ∃ m₁ : Fin M₁,
      (c.restrict₂ m₁).averageErrorProb (Kernel.snd W) ≤ c.averageErrorProb₂ W := by
  classical
  haveI : Nonempty (Fin M₁) := Fin.pos_iff_nonempty.mp hM₁
  set f : Fin M₁ → ℝ≥0∞ := fun m₁ ↦ ∑ m₂ : Fin M₂, c.errorProbAt₂ W (m₁, m₂) with hf
  obtain ⟨m₁, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin M₁)) f
    ⟨Classical.arbitrary (Fin M₁), Finset.mem_univ _⟩
  refine ⟨m₁, ?_⟩
  have hM₁ne : ((M₁ : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM₁.ne'
  have hM₂ne : ((M₂ : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM₂.ne'
  have hLHS : (c.restrict₂ m₁).averageErrorProb (Kernel.snd W)
      = ((M₂ : ℕ) : ℝ≥0∞)⁻¹ * f m₁ := by
    unfold Code.averageErrorProb
    rw [if_neg hM₂.ne']
    exact congrArg _ (Finset.sum_congr rfl fun m₂ _ ↦ c.errorProbAt_restrict₂ W m₁ m₂)
  have hsplit : (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₂ W m) = ∑ m₁' : Fin M₁, f m₁' :=
    Fintype.sum_prod_type _
  have hRHS : c.averageErrorProb₂ W = ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁' : Fin M₁, f m₁' := by
    unfold averageErrorProb₂
    rw [if_neg (Nat.mul_ne_zero hM₁.ne' hM₂.ne'), hsplit]
  have hcard : ((M₁ : ℕ) : ℝ≥0∞) * f m₁ ≤ ∑ m₁' : Fin M₁, f m₁' := by
    have h := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin M₁)) f (f m₁)
      fun i hi ↦ hmin i hi
    simpa [Finset.card_univ, nsmul_eq_mul] using h
  rw [hLHS, hRHS]
  calc ((M₂ : ℕ) : ℝ≥0∞)⁻¹ * f m₁
      = ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * (((M₁ : ℕ) : ℝ≥0∞) * f m₁) := by
        rw [Nat.mul_comm, Nat.cast_mul, ENNReal.mul_inv (Or.inl hM₂ne) (Or.inr hM₁ne), mul_assoc,
          ← mul_assoc (((M₁ : ℕ) : ℝ≥0∞)⁻¹),
          ENNReal.inv_mul_cancel hM₁ne (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁' : Fin M₁, f m₁' := mul_le_mul_right hcard _

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [MeasurableSingletonClass β₂] in
lemma averageErrorProb_coop_le (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    c.coop.averageErrorProb W ≤ c.averageErrorProb₁ W + c.averageErrorProb₂ W := by
  classical
  by_cases hM : M₁ * M₂ = 0
  · unfold Code.averageErrorProb
    rw [if_pos hM]
    exact zero_le
  · have hsum : (∑ m : Fin (M₁ * M₂), c.coop.errorProbAt W m)
        ≤ (∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m)
          + ∑ m : Fin M₁ × Fin M₂, c.errorProbAt₂ W m := by
      calc (∑ m : Fin (M₁ * M₂), c.coop.errorProbAt W m)
          ≤ ∑ m : Fin (M₁ * M₂), (c.errorProbAt₁ W (finProdFinEquiv.symm m)
              + c.errorProbAt₂ W (finProdFinEquiv.symm m)) :=
            Finset.sum_le_sum fun m _ ↦ c.errorProbAt_coop_le W m
        _ = ∑ q : Fin M₁ × Fin M₂, (c.errorProbAt₁ W q + c.errorProbAt₂ W q) :=
            Equiv.sum_comp finProdFinEquiv.symm
              fun q ↦ c.errorProbAt₁ W q + c.errorProbAt₂ W q
        _ = _ := Finset.sum_add_distrib
    unfold Code.averageErrorProb averageErrorProb₁ averageErrorProb₂
    rw [if_neg hM, if_neg hM, if_neg hM, ← mul_add]
    exact mul_le_mul_right hsum _

end Reduction

end BroadcastCode

section CoopOuterBound

variable {α β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

omit [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSingletonClass β₂] in
theorem bc_rate₁_le_capacity_fst
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn
      (fun q : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure q) (Kernel.fst W)).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β₁, 0 < (outputDistribution (pmfToMeasure p) (Kernel.fst W)).real {b})
    {R₁ R₂ : ℝ} (hach : BCAchievable W R₁ R₂) :
    R₁ ≤ capacity (Kernel.fst W) := by
  refine channelCoding_operational_rate_le_capacity (Kernel.fst W) p hp hp_max hq_pos ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hach ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, c, he₁, -⟩ := hN n hn
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₁
  have hM₂pos : 0 < M₂ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₂
  obtain ⟨m₂, hm₂⟩ := c.exists_averageErrorProb_restrict₁_le W hM₁pos hM₂pos
  refine ⟨M₁, c.restrict₁ m₂, ?_, ?_⟩
  · calc Real.exp ((n : ℝ) * R₁) ≤ (⌈Real.exp ((n : ℝ) * R₁)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
  · calc ((c.restrict₁ m₂).averageErrorProb (Kernel.fst W)).toReal
        ≤ (c.averageErrorProb₁ W).toReal :=
          ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
            (c.averageErrorProb₁_le_one W)) hm₂
      _ < ε := he₁

omit [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSingletonClass β₁]
  [DecidableEq β₂] in
theorem bc_rate₂_le_capacity_snd
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn
      (fun q : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure q) (Kernel.snd W)).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β₂, 0 < (outputDistribution (pmfToMeasure p) (Kernel.snd W)).real {b})
    {R₁ R₂ : ℝ} (hach : BCAchievable W R₁ R₂) :
    R₂ ≤ capacity (Kernel.snd W) := by
  refine channelCoding_operational_rate_le_capacity (Kernel.snd W) p hp hp_max hq_pos ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hach ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, c, -, he₂⟩ := hN n hn
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₁
  have hM₂pos : 0 < M₂ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₂
  obtain ⟨m₁, hm₁⟩ := c.exists_averageErrorProb_restrict₂_le W hM₁pos hM₂pos
  refine ⟨M₂, c.restrict₂ m₁, ?_, ?_⟩
  · calc Real.exp ((n : ℝ) * R₂) ≤ (⌈Real.exp ((n : ℝ) * R₂)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (M₂ : ℝ) := by exact_mod_cast hM₂
  · calc ((c.restrict₂ m₁).averageErrorProb (Kernel.snd W)).toReal
        ≤ (c.averageErrorProb₂ W).toReal :=
          ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
            (c.averageErrorProb₂_le_one W)) hm₁
      _ < ε := he₂

omit [DecidableEq β₁] [DecidableEq β₂] in
theorem bc_sum_rate_le_capacity
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (p : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hp_max : IsMaxOn (fun q : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure q) W).toReal)
      (stdSimplex ℝ α) p)
    (hq_pos : ∀ b : β₁ × β₂, 0 < (outputDistribution (pmfToMeasure p) W).real {b})
    {R₁ R₂ : ℝ} (hach : BCAchievable W R₁ R₂) :
    R₁ + R₂ ≤ capacity W := by
  refine channelCoding_operational_rate_le_capacity W p hp hp_max hq_pos ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hach (ε / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, c, he₁, he₂⟩ := hN n hn
  have h₁ : Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hM₁)
  have h₂ : Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hM₂)
  have hne₁ : c.averageErrorProb₁ W ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (c.averageErrorProb₁_le_one W)
  have hne₂ : c.averageErrorProb₂ W ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (c.averageErrorProb₂_le_one W)
  refine ⟨M₁ * M₂, c.coop, ?_, ?_⟩
  · calc Real.exp ((n : ℝ) * (R₁ + R₂))
        = Real.exp ((n : ℝ) * R₁) * Real.exp ((n : ℝ) * R₂) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ (M₁ : ℝ) * (M₂ : ℝ) :=
          mul_le_mul h₁ h₂ (Real.exp_pos _).le (le_trans (Real.exp_pos _).le h₁)
      _ = ((M₁ * M₂ : ℕ) : ℝ) := by push_cast; ring
  · calc (c.coop.averageErrorProb W).toReal
        ≤ (c.averageErrorProb₁ W + c.averageErrorProb₂ W).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne₁, hne₂⟩)
            (c.averageErrorProb_coop_le W)
      _ = (c.averageErrorProb₁ W).toReal + (c.averageErrorProb₂ W).toReal :=
          ENNReal.toReal_add hne₁ hne₂
      _ < ε := by linarith

/-- The cooperative outer region: the rate pairs whose two coordinates are bounded by the
capacities of the two marginal channels and whose sum is bounded by the capacity of the channel
read with the output pair as a single output.

No sign constraint is imposed.  The operational region genuinely contains nonpositive rate
pairs, which a single-message code achieves, so a first-quadrant outer region would not contain
it; the three capacities are nonnegative, so the nonpositive part causes no loss. -/
def bcOuterRegionCoop (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ capacity (Kernel.fst W) ∧ p.2 ≤ capacity (Kernel.snd W) ∧
    p.1 + p.2 ≤ capacity W}

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] [Fintype β₁] [DecidableEq β₁]
  [Nonempty β₁] [MeasurableSingletonClass β₁] [Fintype β₂] [DecidableEq β₂] [Nonempty β₂]
  [MeasurableSingletonClass β₂] in
theorem bcOuterRegionCoop_isClosed (W : BCChannel α β₁ β₂) :
    IsClosed (bcOuterRegionCoop W) := by
  have h₁ : IsClosed {q : ℝ × ℝ | q.1 ≤ capacity (Kernel.fst W)} :=
    isClosed_le continuous_fst continuous_const
  have h₂ : IsClosed {q : ℝ × ℝ | q.2 ≤ capacity (Kernel.snd W)} :=
    isClosed_le continuous_snd continuous_const
  have h₃ : IsClosed {q : ℝ × ℝ | q.1 + q.2 ≤ capacity W} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  exact h₁.inter (h₂.inter h₃)

omit [DecidableEq β₁] [DecidableEq β₂] in
/-- The operational capacity region of a general broadcast channel is contained in the
cooperative outer region: letting the two receivers pool their outputs can only enlarge the set
of achievable rate pairs, and the resulting single-user converses bound each rate and the sum.

The three capacity achievers and their full-support output preconditions are those of
`channelCoding_operational_rate_le_capacity`, one set per single-user channel; none of them
carries a part of the converse argument. -/
@[entry_point]
theorem bc_capacity_subset_coop
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (p₁ : α → ℝ) (hp₁ : p₁ ∈ stdSimplex ℝ α)
    (hp₁_max : IsMaxOn
      (fun q : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure q) (Kernel.fst W)).toReal)
      (stdSimplex ℝ α) p₁)
    (hq₁_pos : ∀ b : β₁, 0 < (outputDistribution (pmfToMeasure p₁) (Kernel.fst W)).real {b})
    (p₂ : α → ℝ) (hp₂ : p₂ ∈ stdSimplex ℝ α)
    (hp₂_max : IsMaxOn
      (fun q : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure q) (Kernel.snd W)).toReal)
      (stdSimplex ℝ α) p₂)
    (hq₂_pos : ∀ b : β₂, 0 < (outputDistribution (pmfToMeasure p₂) (Kernel.snd W)).real {b})
    (p₀ : α → ℝ) (hp₀ : p₀ ∈ stdSimplex ℝ α)
    (hp₀_max : IsMaxOn (fun q : α → ℝ ↦ (mutualInfoOfChannel (pmfToMeasure q) W).toReal)
      (stdSimplex ℝ α) p₀)
    (hq₀_pos : ∀ b : β₁ × β₂, 0 < (outputDistribution (pmfToMeasure p₀) W).real {b}) :
    bcCapacityRegion W ⊆ bcOuterRegionCoop W := by
  refine (bcOuterRegionCoop_isClosed W).closure_subset_iff.mpr fun q hq ↦ ?_
  exact ⟨bc_rate₁_le_capacity_fst W p₁ hp₁ hp₁_max hq₁_pos hq,
    bc_rate₂_le_capacity_snd W p₂ hp₂ hp₂_max hq₂_pos hq,
    bc_sum_rate_le_capacity W p₀ hp₀ hp₀_max hq₀_pos hq⟩

end CoopOuterBound

end InformationTheory.Shannon.BroadcastChannel
