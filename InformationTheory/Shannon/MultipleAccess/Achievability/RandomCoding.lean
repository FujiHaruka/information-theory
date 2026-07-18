import InformationTheory.Shannon.MultipleAccess.Achievability.Codebook

/-!
# Multiple access channel — two-codebook random-coding average and achievability

The random-coding argument on top of the codebook plumbing (Cover–Thomas §15.3.1): the
per-event codebook-average swaps, the arithmetic aggregating them, the two-codebook average
bound, the random → deterministic pigeonhole, and the achievability headline `mac_achievability`.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ### Two-codebook averaging: per-event swaps -/

/-- **E0 swap (correct-pair atypicality).** -/
lemma mac_random_codebook_E0_swap
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ} (m₁ : Fin M₁) (m₂ : Fin M₂) :
    ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
          {y | (c₁ m₁, c₂ m₂, y) ∉
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      ≤ (macAmbientMeasure p₁ p₂ W).real
          {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
              macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε} := by
  classical
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε with hJ_def
  -- Step 1: marginalize c₂ (row m₂) then c₁ (row m₁) to the distributed form `D`.
  have h_marg :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂, y) ∉ J}
        = ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
            (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, x₂, y) ∉ J} := by
    have h_c2 : ∀ c₁ : MACCodebook M₁ n α₁,
        (∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂, y) ∉ J})
        = (codebookMeasure p₁ M₁ n).real {c₁} *
            ∑ x₂ : Fin n → α₂, (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (c₁ m₁ i, x₂ i))).real {y | (c₁ m₁, x₂, y) ∉ J} := by
      intro c₁
      rw [← codebook_marginal_one p₂ M₂ n m₂
            (fun x₂ ↦ (Measure.pi (fun i ↦ W (c₁ m₁ i, x₂ i))).real {y | (c₁ m₁, x₂, y) ∉ J})
            (fun _ ↦ measureReal_nonneg), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c₂ _ ↦ by ring)
    rw [Finset.sum_congr rfl (fun c₁ _ ↦ h_c2 c₁)]
    rw [codebook_marginal_one p₁ M₁ n m₁
        (fun x₁ ↦ ∑ x₂ : Fin n → α₂, (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
          (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, x₂, y) ∉ J})
        (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
    refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₂ _ ↦ by ring)
  -- Step 2: the right side equals the same distributed form `D` via the triple fold.
  have h_rhs : (macAmbientMeasure p₁ p₂ W).real
        {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉ J}
      = ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
          (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
            (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
            (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, x₂, y) ∉ J} := by
    have hg₀_meas : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
        (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
      (measurable_jointRV macX1s measurable_macX1s n).prodMk
        ((measurable_jointRV macX2s measurable_macX2s n).prodMk
          (measurable_jointRV macYs measurable_macYs n))
    rw [show {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉ J}
          = (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) ⁻¹'
              {t | t ∉ J} from rfl,
      ← map_measureReal_apply hg₀_meas (Set.toFinite _).measurableSet,
      mac_chan_fold_triple_set p₁ p₂ W n {t | t ∉ J}]
    simp only [Set.mem_setOf_eq]
  exact le_of_eq (h_marg.trans h_rhs.symm)

/-- **E1 swap (user-1 alias).**  The two-codebook average of the user-1 alias event
(`m₁' ≠ m₁`, user 2 correct) is bounded by `exp(n·(−I(X₁;(X₂,Y)) + 3ε))`. -/
lemma mac_random_codebook_E1_swap
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (m₁ m₁' : Fin M₁) (m₂ : Fin M₂) (hne : m₁ ≠ m₁') :
    ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
          {y | (c₁ m₁', c₂ m₂, y) ∈
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      ≤ Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)) := by
  classical
  haveI hμX1prob : IsProbabilityMeasure ((macAmbientMeasure p₁ p₂ W).map (jointRV macX1s n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV macX1s measurable_macX1s n).aemeasurable
  haveI hνA2prob : IsProbabilityMeasure ((macAmbientMeasure p₁ p₂ W).map
      (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω))) :=
    Measure.isProbabilityMeasure_map ((measurable_jointRV macX2s measurable_macX2s n).prodMk
      (measurable_jointRV macYs measurable_macYs n)).aemeasurable
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε with hJ_def
  -- Step 1: marginalize c₂ (row m₂) then c₁ (rows m₁, m₁') to the fully distributed form `D`.
  have h_marg :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J}
        = ∑ xa : Fin n → α₁, ∑ x₂ : Fin n → α₂, ∑ x₁ : Fin n → α₁,
            (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, x₂, y) ∈ J} := by
    have h_c2 : ∀ c₁ : MACCodebook M₁ n α₁,
        (∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J})
        = (codebookMeasure p₁ M₁ n).real {c₁} *
            ∑ x₂ : Fin n → α₂, (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (c₁ m₁ i, x₂ i))).real {y | (c₁ m₁', x₂, y) ∈ J} := by
      intro c₁
      rw [← codebook_marginal_one p₂ M₂ n m₂
            (fun x₂ ↦ (Measure.pi (fun i ↦ W (c₁ m₁ i, x₂ i))).real {y | (c₁ m₁', x₂, y) ∈ J})
            (fun _ ↦ measureReal_nonneg), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c₂ _ ↦ by ring)
    rw [Finset.sum_congr rfl (fun c₁ _ ↦ h_c2 c₁)]
    rw [codebook_marginal_two p₁ M₁ n m₁ m₁' hne
        (fun x₁ xa ↦ ∑ x₂ : Fin n → α₂, (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
          (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, x₂, y) ∈ J})
        (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
    -- Reorder ∑x₁∑xa∑x₂ → ∑xa∑x₂∑x₁ and distribute the codeword masses.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun xa _ ↦ ?_)
    refine (Finset.sum_congr rfl (fun x₁ _ ↦ Finset.mul_sum _ _ _)).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x₂ _ ↦ Finset.sum_congr rfl (fun x₁ _ ↦ by ring))
  -- Step 2: the gateway product equals the same distributed form `D`.
  have h_prod :
      (((macAmbientMeasure p₁ p₂ W).map (jointRV macX1s n)).prod
          ((macAmbientMeasure p₁ p₂ W).map
            (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω)))).real J
        = ∑ xa : Fin n → α₁, ∑ x₂ : Fin n → α₂, ∑ x₁ : Fin n → α₁,
            (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, x₂, y) ∈ J} := by
    rw [mac_prodReal_eq_slice_sum ((macAmbientMeasure p₁ p₂ W).map (jointRV macX1s n))
        ((macAmbientMeasure p₁ p₂ W).map (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω))) J,
      mac_block_law_X1 p₁ p₂ W n]
    refine Finset.sum_congr rfl (fun xa _ ↦ ?_)
    rw [mac_chan_fold_set p₁ p₂ W n {q | (xa, q) ∈ J}, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₂ _ ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
    show (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa} *
        ((Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
          (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
          (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, x₂, y) ∈ J}) = _
    ring
  -- Step 3: the gateway exponential bound, with the exponent rewritten to `-(macInfo₁) + 3ε`.
  have h_gw := macJTS_indep_prob_le_X1 (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
    measurable_macX1s measurable_macX2s measurable_macYs
    (macAmbient_iIndepFun_coord p₁ p₂ W Prod.fst measurable_fst)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.fst measurable_fst i)
    (macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ (q.2.1, q.2.2))
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.2.1, q.2.2))
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)) i)
    (fun x ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW Prod.fst measurable_fst 0 x
      (x, Classical.arbitrary α₂, Classical.arbitrary β) rfl)
    (fun q ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW
      (fun r ↦ (r.2.1, r.2.2))
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)) 0 q
      (Classical.arbitrary α₁, q.1, q.2) rfl)
    (fun q ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW id measurable_id 0 q q rfl)
    n hε
  rw [← hJ_def] at h_gw
  -- Exponent identification via the per-coordinate joint entropies.
  have he_id : entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
      = entropy (macJointDistribution p₁ p₂ W) id := by
    rw [show (macJointSequence macX1s macX2s macYs 0 : (ℕ → α₁ × α₂ × β) → α₁ × α₂ × β)
          = fun ω ↦ id (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W id measurable_id 0
  have he_fst : entropy (macAmbientMeasure p₁ p₂ W) (macX1s 0)
      = entropy (macJointDistribution p₁ p₂ W) Prod.fst := by
    rw [show (macX1s 0 : (ℕ → α₁ × α₂ × β) → α₁) = fun ω ↦ Prod.fst (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W Prod.fst measurable_fst 0
  have he_snd : entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX2s macYs 0)
      = entropy (macJointDistribution p₁ p₂ W) Prod.snd := by
    rw [show (jointSequence macX2s macYs 0 : (ℕ → α₁ × α₂ × β) → α₂ × β)
          = fun ω ↦ Prod.snd (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W Prod.snd measurable_snd 0
  have h_exp : ((entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
        - entropy (macAmbientMeasure p₁ p₂ W) (macX1s 0)
        - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX2s macYs 0)) + 3 * ε)
      = -(macInfo₁ p₁ p₂ W) + 3 * ε := by
    rw [he_id, he_fst, he_snd, macInfo₁]; ring
  calc ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J}
      = (((macAmbientMeasure p₁ p₂ W).map (jointRV macX1s n)).prod
          ((macAmbientMeasure p₁ p₂ W).map
            (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω)))).real J := h_marg.trans h_prod.symm
    _ ≤ Real.exp ((n : ℝ) * ((entropy (macAmbientMeasure p₁ p₂ W)
          (macJointSequence macX1s macX2s macYs 0)
          - entropy (macAmbientMeasure p₁ p₂ W) (macX1s 0)
          - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX2s macYs 0)) + 3 * ε)) := h_gw
    _ = Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)) := by rw [h_exp]

/-- **E2 swap (user-2 alias).** -/
lemma mac_random_codebook_E2_swap
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (m₁ : Fin M₁) (m₂ m₂' : Fin M₂) (hne : m₂ ≠ m₂') :
    ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
          {y | (c₁ m₁, c₂ m₂', y) ∈
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      ≤ Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)) := by
  classical
  haveI hμX2prob : IsProbabilityMeasure ((macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV macX2s measurable_macX2s n).aemeasurable
  haveI hνA1prob : IsProbabilityMeasure ((macAmbientMeasure p₁ p₂ W).map
      (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω))) :=
    Measure.isProbabilityMeasure_map ((measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macYs measurable_macYs n)).aemeasurable
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε with hJ_def
  -- Step 1: marginalize c₁ (row m₁) then c₂ (rows m₂, m₂') to the distributed form `D`.
  have h_marg :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J}
        = ∑ xb : Fin n → α₂, ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
            (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
              (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, xb, y) ∈ J} := by
    rw [Finset.sum_comm]
    have h_c1 : ∀ c₂ : MACCodebook M₂ n α₂,
        (∑ c₁ : MACCodebook M₁ n α₁,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J})
        = (codebookMeasure p₂ M₂ n).real {c₂} *
            ∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun i ↦ W (x₁ i, c₂ m₂ i))).real {y | (x₁, c₂ m₂', y) ∈ J} := by
      intro c₂
      rw [← codebook_marginal_one p₁ M₁ n m₁
            (fun x₁ ↦ (Measure.pi (fun i ↦ W (x₁ i, c₂ m₂ i))).real {y | (x₁, c₂ m₂', y) ∈ J})
            (fun _ ↦ measureReal_nonneg), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c₁ _ ↦ by ring)
    rw [Finset.sum_congr rfl (fun c₂ _ ↦ h_c1 c₂)]
    rw [codebook_marginal_two p₂ M₂ n m₂ m₂' hne
        (fun x₂ xb ↦ ∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
          (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, xb, y) ∈ J})
        (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
    -- Reorder ∑x₂∑xb∑x₁ → ∑xb∑x₁∑x₂ and distribute the codeword masses.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun xb _ ↦ ?_)
    refine (Finset.sum_congr rfl (fun x₂ _ ↦ Finset.mul_sum _ _ _)).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x₁ _ ↦ Finset.sum_congr rfl (fun x₂ _ ↦ by ring))
  -- Step 2: the gateway product equals the same distributed form `D`.
  have h_prod :
      (((macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n)).prod
          ((macAmbientMeasure p₁ p₂ W).map
            (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω)))).real
          {q : (Fin n → α₂) × ((Fin n → α₁) × (Fin n → β)) | (q.2.1, q.1, q.2.2) ∈ J}
        = ∑ xb : Fin n → α₂, ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
            (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
              (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, xb, y) ∈ J} := by
    rw [mac_prodReal_eq_slice_sum ((macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n))
        ((macAmbientMeasure p₁ p₂ W).map (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω)))
        {q : (Fin n → α₂) × ((Fin n → α₁) × (Fin n → β)) | (q.2.1, q.1, q.2.2) ∈ J},
      mac_block_law_X2 p₁ p₂ W n]
    refine Finset.sum_congr rfl (fun xb _ ↦ ?_)
    rw [mac_chan_fold_X1Y_set p₁ p₂ W n
        {b : (Fin n → α₁) × (Fin n → β) |
          (xb, b) ∈ {q : (Fin n → α₂) × ((Fin n → α₁) × (Fin n → β)) | (q.2.1, q.1, q.2.2) ∈ J}},
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₂ _ ↦ ?_)
    show (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
        ((Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
          (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
          (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, xb, y) ∈ J}) = _
    ring
  -- Step 3: the gateway exponential bound, exponent rewritten to `-(macInfo₂) + 3ε`.
  have h_gw := macJTS_indep_prob_le_X2_split p₁ p₂ W hp₁ hp₂ hW n hε
  rw [← hJ_def] at h_gw
  have he_id : entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
      = entropy (macJointDistribution p₁ p₂ W) id := by
    rw [show (macJointSequence macX1s macX2s macYs 0 : (ℕ → α₁ × α₂ × β) → α₁ × α₂ × β)
          = fun ω ↦ id (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W id measurable_id 0
  have he_x2 : entropy (macAmbientMeasure p₁ p₂ W) (macX2s 0)
      = entropy (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) := by
    rw [show (macX2s 0 : (ℕ → α₁ × α₂ × β) → α₂) = fun ω ↦ (fun q : α₁ × α₂ × β ↦ q.2.1) (ω 0)
          from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd) 0
  have he_x1y : entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macYs 0)
      = entropy (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.2)) := by
    rw [show (jointSequence macX1s macYs 0 : (ℕ → α₁ × α₂ × β) → α₁ × β)
          = fun ω ↦ (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) 0
  have h_exp : ((entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
        - entropy (macAmbientMeasure p₁ p₂ W) (macX2s 0)
        - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macYs 0)) + 3 * ε)
      = -(macInfo₂ p₁ p₂ W) + 3 * ε := by
    rw [he_id, he_x2, he_x1y, macInfo₂]; ring
  calc ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J}
      = (((macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n)).prod
          ((macAmbientMeasure p₁ p₂ W).map
            (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω)))).real
          {q : (Fin n → α₂) × ((Fin n → α₁) × (Fin n → β)) | (q.2.1, q.1, q.2.2) ∈ J} :=
        h_marg.trans h_prod.symm
    _ ≤ Real.exp ((n : ℝ) * ((entropy (macAmbientMeasure p₁ p₂ W)
          (macJointSequence macX1s macX2s macYs 0)
          - entropy (macAmbientMeasure p₁ p₂ W) (macX2s 0)
          - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macYs 0)) + 3 * ε)) := h_gw
    _ = Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)) := by rw [h_exp]

/-- **E3 swap (both aliases).** -/
lemma mac_random_codebook_E3_swap
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (m₁ m₁' : Fin M₁) (m₂ m₂' : Fin M₂) (hne₁ : m₁ ≠ m₁') (hne₂ : m₂ ≠ m₂') :
    ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
          {y | (c₁ m₁', c₂ m₂', y) ∈
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      ≤ Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) := by
  classical
  haveI hνsplit12prob : IsProbabilityMeasure ((macAmbientMeasure p₁ p₂ W).map
      (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω))) :=
    Measure.isProbabilityMeasure_map ((measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macX2s measurable_macX2s n)).aemeasurable
  haveI hμYprob : IsProbabilityMeasure ((macAmbientMeasure p₁ p₂ W).map (jointRV macYs n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV macYs measurable_macYs n).aemeasurable
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε with hJ_def
  -- Step 1: marginalize both codebooks (two rows each) to the distributed form `D`.
  have h_marg :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂', y) ∈ J}
        = ∑ xa : Fin n → α₁, ∑ xb : Fin n → α₂, ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
            (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
              (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, xb, y) ∈ J} := by
    have h_c2 : ∀ c₁ : MACCodebook M₁ n α₁,
        (∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂', y) ∈ J})
        = (codebookMeasure p₁ M₁ n).real {c₁} *
            ∑ xb : Fin n → α₂, ∑ x₂ : Fin n → α₂,
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (c₁ m₁ i, x₂ i))).real {y | (c₁ m₁', xb, y) ∈ J} := by
      intro c₁
      rw [← codebook_marginal_two p₂ M₂ n m₂' m₂ hne₂.symm
            (fun xb x₂ ↦ (Measure.pi (fun i ↦ W (c₁ m₁ i, x₂ i))).real {y | (c₁ m₁', xb, y) ∈ J})
            (fun _ _ ↦ measureReal_nonneg), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun c₂ _ ↦ by ring)
    rw [Finset.sum_congr rfl (fun c₁ _ ↦ h_c2 c₁)]
    rw [codebook_marginal_two p₁ M₁ n m₁' m₁ hne₁.symm
        (fun xa x₁ ↦ ∑ xb : Fin n → α₂, ∑ x₂ : Fin n → α₂,
          (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
          (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
          (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, xb, y) ∈ J})
        (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg
          (fun _ _ ↦ mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
            measureReal_nonneg)))]
    -- Reorder ∑xa∑x₁(∑xb∑x₂) → ∑xa∑xb∑x₁∑x₂ and distribute the codeword masses.
    refine Finset.sum_congr rfl (fun xa _ ↦ ?_)
    refine (Finset.sum_congr rfl (fun x₁ _ ↦ Finset.mul_sum _ _ _)).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun xb _ ↦ Finset.sum_congr rfl (fun x₁ _ ↦ ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₂ _ ↦ by ring)
  -- Step 2: the gateway product equals the same distributed form `D`.
  have h_prod :
      (((macAmbientMeasure p₁ p₂ W).map
            (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω))).prod
          ((macAmbientMeasure p₁ p₂ W).map (jointRV macYs n))).real
          {q : ((Fin n → α₁) × (Fin n → α₂)) × (Fin n → β) | (q.1.1, q.1.2, q.2) ∈ J}
        = ∑ xa : Fin n → α₁, ∑ xb : Fin n → α₂, ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
            (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
              (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
              (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
              (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, xb, y) ∈ J} := by
    rw [mac_prodReal_eq_slice_sum ((macAmbientMeasure p₁ p₂ W).map
          (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω)))
        ((macAmbientMeasure p₁ p₂ W).map (jointRV macYs n))
        {q : ((Fin n → α₁) × (Fin n → α₂)) × (Fin n → β) | (q.1.1, q.1.2, q.2) ∈ J},
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun xa _ ↦ Finset.sum_congr rfl (fun xb _ ↦ ?_))
    rw [mac_block_law_X1X2_singleton p₁ p₂ W n xa xb,
      mac_chan_fold_Y_set p₁ p₂ W n
        {b : Fin n → β | ((xa, xb), b) ∈
          {q : ((Fin n → α₁) × (Fin n → α₂)) × (Fin n → β) | (q.1.1, q.1.2, q.2) ∈ J}},
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x₂ _ ↦ ?_)
    show (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa} *
          (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} *
          ((Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} *
            (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} *
            (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (xa, xb, y) ∈ J}) = _
    ring
  -- Step 3: the gateway exponential bound, exponent rewritten to `-(macInfoBoth) + 3ε`.
  have h_gw := macJTS_indep_prob_le_both_split p₁ p₂ W hp₁ hp₂ hW n hε
  rw [← hJ_def] at h_gw
  have he_id : entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
      = entropy (macJointDistribution p₁ p₂ W) id := by
    rw [show (macJointSequence macX1s macX2s macYs 0 : (ℕ → α₁ × α₂ × β) → α₁ × α₂ × β)
          = fun ω ↦ id (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W id measurable_id 0
  have he_x1x2 : entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macX2s 0)
      = entropy (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.1)) := by
    rw [show (jointSequence macX1s macX2s 0 : (ℕ → α₁ × α₂ × β) → α₁ × α₂)
          = fun ω ↦ (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (ω 0) from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) 0
  have he_y : entropy (macAmbientMeasure p₁ p₂ W) (macYs 0)
      = entropy (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2) := by
    rw [show (macYs 0 : (ℕ → α₁ × α₂ × β) → β) = fun ω ↦ (fun q : α₁ × α₂ × β ↦ q.2.2) (ω 0)
          from rfl]
    exact macAmbient_entropy_coord p₁ p₂ W (fun q ↦ q.2.2) (measurable_snd.comp measurable_snd) 0
  have h_exp : ((entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
        - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macX2s 0)
        - entropy (macAmbientMeasure p₁ p₂ W) (macYs 0)) + 3 * ε)
      = -(macInfoBoth p₁ p₂ W) + 3 * ε := by
    rw [he_id, he_x1x2, he_y, macInfoBoth]; ring
  calc ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂', y) ∈ J}
      = (((macAmbientMeasure p₁ p₂ W).map
            (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω))).prod
          ((macAmbientMeasure p₁ p₂ W).map (jointRV macYs n))).real
          {q : ((Fin n → α₁) × (Fin n → α₂)) × (Fin n → β) | (q.1.1, q.1.2, q.2) ∈ J} :=
        h_marg.trans h_prod.symm
    _ ≤ Real.exp ((n : ℝ) * ((entropy (macAmbientMeasure p₁ p₂ W)
          (macJointSequence macX1s macX2s macYs 0)
          - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macX2s 0)
          - entropy (macAmbientMeasure p₁ p₂ W) (macYs 0)) + 3 * ε)) := h_gw
    _ = Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) := by rw [h_exp]

/-! ### Two-codebook averaging: arithmetic -/

/-- `(averageErrorProb).toReal = (1/(M₁·M₂)) · ∑ (errorProbAt).toReal`. -/
lemma mac_averageErrorProb_toReal_eq
    {M₁ M₂ n : ℕ} (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β)
    (hM : 0 < M₁ * M₂)
    (h_ne_top : ∀ m : Fin M₁ × Fin M₂, c.errorProbAt W m ≠ ∞) :
    (c.averageErrorProb W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂, (c.errorProbAt W m).toReal := by
  unfold MACCode.averageErrorProb
  rw [if_neg hM.ne']
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]

/-- Each MAC per-pair error probability is finite. -/
lemma mac_errorProbAt_ne_top
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂) (m : Fin M₁ × Fin M₂) :
    (macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).errorProbAt W m ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).errorProbAt_le_one W m)

set_option maxHeartbeats 1000000 in
/-- Linearity decomposition of the product-codebook expectation into the four error-event
sums (E0 diagonal + the three alias families), with the codebook-weight average swapped to
the inside of each term. -/
lemma mac_sum_weighted_quad_decomp
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {M₁ M₂ : ℕ} (w₁ : ι₁ → ℝ) (w₂ : ι₂ → ℝ)
    (a : ι₁ → ι₂ → Fin M₁ → Fin M₂ → ℝ)
    (b1 : ι₁ → ι₂ → Fin M₁ → Fin M₂ → Fin M₁ → ℝ)
    (b2 : ι₁ → ι₂ → Fin M₁ → Fin M₂ → Fin M₂ → ℝ)
    (b3 : ι₁ → ι₂ → Fin M₁ → Fin M₂ → Fin M₁ × Fin M₂ → ℝ)
    (Minv : ℝ) :
    ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ *
        (Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          (a c₁ c₂ m₁ m₂
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 c₁ c₂ m₁ m₂ m₁'
            + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 c₁ c₂ m₁ m₂ m₂'
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                      ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 c₁ c₂ m₁ m₂ p))
      = Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          ((∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * a c₁ c₂ m₁ m₂)
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
                ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * b1 c₁ c₂ m₁ m₂ m₁'
            + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
                ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * b2 c₁ c₂ m₁ m₂ m₂'
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                      ((Finset.univ : Finset (Fin M₂)).erase m₂),
                ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * b3 c₁ c₂ m₁ m₂ p) := by
  classical
  -- Reorder `∑c₁∑c₂∑m₁∑m₂` to `∑m₁∑m₂∑c₁∑c₂`.
  have hcomm : ∀ F : ι₁ → ι₂ → Fin M₁ → Fin M₂ → ℝ,
      ∑ c₁ : ι₁, ∑ c₂ : ι₂, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, F c₁ c₂ m₁ m₂
      = ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ c₁ : ι₁, ∑ c₂ : ι₂, F c₁ c₂ m₁ m₂ := by
    intro F
    calc ∑ c₁ : ι₁, ∑ c₂ : ι₂, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, F c₁ c₂ m₁ m₂
        = ∑ c : ι₁ × ι₂, ∑ m : Fin M₁ × Fin M₂, F c.1 c.2 m.1 m.2 := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun c₁ _ ↦ Finset.sum_congr rfl (fun c₂ _ ↦ ?_))
          rw [Fintype.sum_prod_type]
      _ = ∑ m : Fin M₁ × Fin M₂, ∑ c : ι₁ × ι₂, F c.1 c.2 m.1 m.2 := Finset.sum_comm
      _ = ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ c₁ : ι₁, ∑ c₂ : ι₂, F c₁ c₂ m₁ m₂ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun m₁ _ ↦ Finset.sum_congr rfl (fun m₂ _ ↦ ?_))
          rw [Fintype.sum_prod_type]
  -- Reorder `∑c₁∑c₂∑z∈s` to `∑z∈s∑c₁∑c₂`.
  have hcomm3 : ∀ {γ : Type} (s : Finset γ) (G : ι₁ → ι₂ → γ → ℝ),
      ∑ c₁ : ι₁, ∑ c₂ : ι₂, ∑ z ∈ s, G c₁ c₂ z
      = ∑ z ∈ s, ∑ c₁ : ι₁, ∑ c₂ : ι₂, G c₁ c₂ z := by
    intro γ s G
    rw [Finset.sum_congr rfl (fun c₁ _ ↦ Finset.sum_comm), Finset.sum_comm]
  -- Step 1: pull `Minv` and the codebook weights inside the message sums.
  have step1 : ∀ (c₁ : ι₁) (c₂ : ι₂),
      w₁ c₁ * w₂ c₂ *
        (Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          (a c₁ c₂ m₁ m₂
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 c₁ c₂ m₁ m₂ m₁'
            + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 c₁ c₂ m₁ m₂ m₂'
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                      ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 c₁ c₂ m₁ m₂ p))
      = Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          (w₁ c₁ * w₂ c₂ * a c₁ c₂ m₁ m₂
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
                w₁ c₁ * w₂ c₂ * b1 c₁ c₂ m₁ m₂ m₁'
            + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
                w₁ c₁ * w₂ c₂ * b2 c₁ c₂ m₁ m₂ m₂'
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                      ((Finset.univ : Finset (Fin M₂)).erase m₂),
                w₁ c₁ * w₂ c₂ * b3 c₁ c₂ m₁ m₂ p) := by
    intro c₁ c₂
    rw [← mul_assoc, mul_comm (w₁ c₁ * w₂ c₂) Minv, mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun m₁ _ ↦ ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m₂ _ ↦ ?_)
    rw [mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c₁ _ ↦ Finset.sum_congr rfl (fun c₂ _ ↦ step1 c₁ c₂))]
  -- Step 2: pull `Minv` out past the codebook sums and swap message sums outward.
  rw [Finset.sum_congr rfl (fun c₁ _ ↦ (Finset.mul_sum _ _ _).symm), ← Finset.mul_sum]
  congr 1
  rw [hcomm (fun c₁ c₂ m₁ m₂ ↦ w₁ c₁ * w₂ c₂ * a c₁ c₂ m₁ m₂
      + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, w₁ c₁ * w₂ c₂ * b1 c₁ c₂ m₁ m₂ m₁'
      + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, w₁ c₁ * w₂ c₂ * b2 c₁ c₂ m₁ m₂ m₂'
      + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                ((Finset.univ : Finset (Fin M₂)).erase m₂), w₁ c₁ * w₂ c₂ * b3 c₁ c₂ m₁ m₂ p)]
  refine Finset.sum_congr rfl (fun m₁ _ ↦ Finset.sum_congr rfl (fun m₂ _ ↦ ?_))
  -- Step 3: distribute `∑c₁∑c₂` over the four terms and pull the alias sums outward.
  have r1 : (∑ c₁ : ι₁, ∑ c₂ : ι₂, ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
                w₁ c₁ * w₂ c₂ * b1 c₁ c₂ m₁ m₂ m₁')
      = ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
          ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * b1 c₁ c₂ m₁ m₂ m₁' :=
    hcomm3 ((Finset.univ : Finset (Fin M₁)).erase m₁) _
  have r2 : (∑ c₁ : ι₁, ∑ c₂ : ι₂, ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
                w₁ c₁ * w₂ c₂ * b2 c₁ c₂ m₁ m₂ m₂')
      = ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
          ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * b2 c₁ c₂ m₁ m₂ m₂' :=
    hcomm3 ((Finset.univ : Finset (Fin M₂)).erase m₂) _
  have r3 : (∑ c₁ : ι₁, ∑ c₂ : ι₂, ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                ((Finset.univ : Finset (Fin M₂)).erase m₂), w₁ c₁ * w₂ c₂ * b3 c₁ c₂ m₁ m₂ p)
      = ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                ((Finset.univ : Finset (Fin M₂)).erase m₂),
          ∑ c₁ : ι₁, ∑ c₂ : ι₂, w₁ c₁ * w₂ c₂ * b3 c₁ c₂ m₁ m₂ p :=
    hcomm3 (((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
            ((Finset.univ : Finset (Fin M₂)).erase m₂)) _
  simp only [Finset.sum_add_distrib]
  rw [r1, r2, r3]

/-- Per-pair aggregation of the four uniform bounds into the closed-form average bound. -/
lemma mac_quad_aggregate
    {M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (A : ℝ) (e1 e2 e3 : ℝ)
    (d : Fin M₁ → Fin M₂ → ℝ)
    (b1 : Fin M₁ → Fin M₂ → Fin M₁ → ℝ)
    (b2 : Fin M₁ → Fin M₂ → Fin M₂ → ℝ)
    (b3 : Fin M₁ → Fin M₂ → Fin M₁ × Fin M₂ → ℝ)
    (Minv : ℝ) (hMinv : 0 ≤ Minv)
    (hMinvM : Minv * ((M₁ * M₂ : ℕ) : ℝ) = 1)
    (hd : ∀ m₁ m₂, d m₁ m₂ ≤ A)
    (hb1 : ∀ m₁ m₂, ∀ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 m₁ m₂ m₁' ≤ e1)
    (hb2 : ∀ m₁ m₂, ∀ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 m₁ m₂ m₂' ≤ e2)
    (hb3 : ∀ m₁ m₂, ∀ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
        ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 m₁ m₂ p ≤ e3)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) :
    Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
        (d m₁ m₂
          + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 m₁ m₂ m₁'
          + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 m₁ m₂ m₂'
          + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                    ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 m₁ m₂ p)
      ≤ A + ((M₁ : ℝ) - 1) * e1 + ((M₂ : ℝ) - 1) * e2
          + ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) * e3 := by
  classical
  set B : ℝ := A + ((M₁ : ℝ) - 1) * e1 + ((M₂ : ℝ) - 1) * e2
      + ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) * e3 with hB_def
  have hcard1 : ∀ m : Fin M₁, (((Finset.univ : Finset (Fin M₁)).erase m).card : ℝ) = (M₁ : ℝ) - 1 := by
    intro m
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hM₁, Nat.cast_one]
  have hcard2 : ∀ m : Fin M₂, (((Finset.univ : Finset (Fin M₂)).erase m).card : ℝ) = (M₂ : ℝ) - 1 := by
    intro m
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hM₂, Nat.cast_one]
  -- Each per-pair inner four-term sum is bounded by `B`.
  have h_inner : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂),
      (d m₁ m₂
        + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 m₁ m₂ m₁'
        + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 m₁ m₂ m₂'
        + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                  ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 m₁ m₂ p) ≤ B := by
    intro m₁ m₂
    have hb1sum : ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 m₁ m₂ m₁'
        ≤ ((M₁ : ℝ) - 1) * e1 := by
      calc ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 m₁ m₂ m₁'
          ≤ ∑ _m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, e1 :=
            Finset.sum_le_sum (hb1 m₁ m₂)
        _ = ((M₁ : ℝ) - 1) * e1 := by rw [Finset.sum_const, nsmul_eq_mul, hcard1 m₁]
    have hb2sum : ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 m₁ m₂ m₂'
        ≤ ((M₂ : ℝ) - 1) * e2 := by
      calc ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 m₁ m₂ m₂'
          ≤ ∑ _m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, e2 :=
            Finset.sum_le_sum (hb2 m₁ m₂)
        _ = ((M₂ : ℝ) - 1) * e2 := by rw [Finset.sum_const, nsmul_eq_mul, hcard2 m₂]
    have hb3sum : ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
            ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 m₁ m₂ p
        ≤ ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) * e3 := by
      calc ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
              ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 m₁ m₂ p
          ≤ ∑ _p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
              ((Finset.univ : Finset (Fin M₂)).erase m₂), e3 :=
            Finset.sum_le_sum (hb3 m₁ m₂)
        _ = ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) * e3 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul, hcard1 m₁,
              hcard2 m₂]
    rw [hB_def]
    have := add_le_add (add_le_add (add_le_add (hd m₁ m₂) hb1sum) hb2sum) hb3sum
    linarith [this]
  -- Aggregate over `(m₁, m₂)` and cancel `Minv * (M₁ M₂)`.
  have hsum_const : ∑ _m₁ : Fin M₁, ∑ _m₂ : Fin M₂, B = ((M₁ * M₂ : ℕ) : ℝ) * B := by
    rw [Finset.sum_congr rfl (fun _ _ ↦ by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      Nat.cast_mul]
  calc Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          (d m₁ m₂
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁, b1 m₁ m₂ m₁'
            + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂, b2 m₁ m₂ m₂'
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                      ((Finset.univ : Finset (Fin M₂)).erase m₂), b3 m₁ m₂ p)
      ≤ Minv * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, B :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun m₁ _ ↦ Finset.sum_le_sum (fun m₂ _ ↦ h_inner m₁ m₂))) hMinv
    _ = Minv * (((M₁ * M₂ : ℕ) : ℝ) * B) := by rw [hsum_const]
    _ = B := by rw [← mul_assoc, hMinvM, one_mul]

/-! ### Two-codebook averaging -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **Two-codebook random-coding average bound.**  For the i.i.d. MAC ambient measure
`macAmbientMeasure p₁ p₂ W`, averaging the per-pair error probability of the
joint-typical pair decoder over the product of the two codebook laws is bounded by the
four-event sum: the correct-pair atypicality probability `E0`, plus the three
exponential alias terms `E1`/`E2`/`E3` controlled by the gateway atoms
`macJTS_indep_prob_le_X1`/`_X2`/`_both`.

This is the two-codebook generalisation of the single-user
`random_codebook_average_le`, assembled from the four per-event swaps
(`mac_random_codebook_E0_swap`/`_E1_swap`/`_E2_swap`/`_E3_swap`), the four-event linearity
decomposition (`mac_sum_weighted_quad_decomp`), and the per-pair aggregation
(`mac_quad_aggregate`).
@audit:ok -/
theorem mac_random_codebook_average_le
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (hε : 0 < ε) :
    ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        ((macCodebookToCode (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
            hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal
      ≤ (macAmbientMeasure p₁ p₂ W).real
          {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
              macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε))
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε))
        + ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) *
            Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) := by
  classical
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε with hJ_def
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have hMcast_ne : ((M₁ * M₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  -- Per-codebook-pair averaging bound via the four-event Bonferroni union bound.
  have h_avg_le : ∀ (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂),
      ((macCodebookToCode (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
          hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal
        ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
            ((Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂, y) ∉ J}
              + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
                  (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J}
              + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
                  (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J}
              + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                        ((Finset.univ : Finset (Fin M₂)).erase m₂),
                  (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ p.1, c₂ p.2, y) ∈ J}) := by
    intro c₁ c₂
    rw [mac_averageErrorProb_toReal_eq _ W hMpos
        (fun m ↦ mac_errorProbAt_ne_top (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs W
          hM₁ hM₂ ε c₁ c₂ m), Fintype.sum_prod_type]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum (fun m₁ _ ↦ Finset.sum_le_sum (fun m₂ _ ↦ ?_))
    exact mac_errorProbAt_le_bonferroni4 (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs W
      hM₁ hM₂ c₁ c₂ m₁ m₂
  -- Weighted sum over the product codebook law.
  have h_weighted :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
          (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
          ((macCodebookToCode (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
              hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal
        ≤ ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
            (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
            (((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
              ((Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂, y) ∉ J}
                + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
                    (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J}
                + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
                    (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J}
                + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                          ((Finset.univ : Finset (Fin M₂)).erase m₂),
                    (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
                      {y | (c₁ p.1, c₂ p.2, y) ∈ J})) :=
    Finset.sum_le_sum (fun c₁ _ ↦ Finset.sum_le_sum (fun c₂ _ ↦
      mul_le_mul_of_nonneg_left (h_avg_le c₁ c₂)
        (mul_nonneg measureReal_nonneg measureReal_nonneg)))
  refine le_trans h_weighted ?_
  rw [mac_sum_weighted_quad_decomp
      (fun c₁ : MACCodebook M₁ n α₁ ↦ (codebookMeasure p₁ M₁ n).real {c₁})
      (fun c₂ : MACCodebook M₂ n α₂ ↦ (codebookMeasure p₂ M₂ n).real {c₂})
      (fun c₁ c₂ m₁ m₂ ↦
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂, y) ∉ J})
      (fun c₁ c₂ m₁ m₂ m₁' ↦
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J})
      (fun c₁ c₂ m₁ m₂ m₂' ↦
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J})
      (fun c₁ c₂ m₁ m₂ p ↦
        (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ p.1, c₂ p.2, y) ∈ J})
      (((M₁ * M₂ : ℕ) : ℝ)⁻¹)]
  exact mac_quad_aggregate hM₁ hM₂
    ((macAmbientMeasure p₁ p₂ W).real
      {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉ J})
    (Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)))
    (Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)))
    (Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)))
    (fun m₁ m₂ ↦ ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
      (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
      (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂, y) ∉ J})
    (fun m₁ m₂ m₁' ↦ ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
      (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
      (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁', c₂ m₂, y) ∈ J})
    (fun m₁ m₂ m₂' ↦ ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
      (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
      (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ m₁, c₂ m₂', y) ∈ J})
    (fun m₁ m₂ p ↦ ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
      (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
      (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real {y | (c₁ p.1, c₂ p.2, y) ∈ J})
    (((M₁ * M₂ : ℕ) : ℝ)⁻¹) (by positivity) (inv_mul_cancel₀ hMcast_ne)
    (fun m₁ m₂ ↦ mac_random_codebook_E0_swap p₁ p₂ W hp₁ hp₂ hW m₁ m₂)
    (fun m₁ m₂ m₁' hm₁' ↦ mac_random_codebook_E1_swap p₁ p₂ W hp₁ hp₂ hW hε m₁ m₁' m₂
      ((Finset.mem_erase.mp hm₁').1).symm)
    (fun m₁ m₂ m₂' hm₂' ↦ mac_random_codebook_E2_swap p₁ p₂ W hp₁ hp₂ hW hε m₁ m₂ m₂'
      ((Finset.mem_erase.mp hm₂').1).symm)
    (fun m₁ m₂ p hp ↦ mac_random_codebook_E3_swap p₁ p₂ W hp₁ hp₂ hW hε m₁ p.1 m₂ p.2
      ((Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1).symm
      ((Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1).symm)
    (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le

/-! ### Random → deterministic (two-codebook pigeonhole) -/

omit [DecidableEq α₁] [Nonempty α₁] [DecidableEq α₂] [Nonempty α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- Pigeonhole over the product codebook law: if the two-codebook expectation is `≤ B`,
some deterministic codebook pair achieves `averageErrorProb ≤ B`.
@audit:ok -/
theorem mac_exists_codebook_le_avg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (B : ℝ)
    (h_avg :
      ∑ c₁ : MACCodebook M₁ n α₁, ∑ c₂ : MACCodebook M₂ n α₂,
        (codebookMeasure p₁ M₁ n).real {c₁} * (codebookMeasure p₂ M₂ n).real {c₂} *
        ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal ≤ B) :
    ∃ (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂),
      ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).averageErrorProb W).toReal ≤ B := by
  classical
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- The two codebook laws are probability measures.
  haveI : MeasurableSingletonClass (Fin n → α₁) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → α₂) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (MACCodebook M₁ n α₁) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (MACCodebook M₂ n α₂) := Pi.instMeasurableSingletonClass
  haveI : IsProbabilityMeasure (codebookMeasure p₁ M₁ n) :=
    codebookMeasure.instIsProbabilityMeasure p₁ M₁ n
  haveI : IsProbabilityMeasure (codebookMeasure p₂ M₂ n) :=
    codebookMeasure.instIsProbabilityMeasure p₂ M₂ n
  -- Each codebook law sums to 1 over its (finite) codebook space.
  have h1 : ∑ c₁ : MACCodebook M₁ n α₁, (codebookMeasure p₁ M₁ n).real {c₁} = 1 := by
    have h_real_univ : (codebookMeasure p₁ M₁ n).real
        ((Finset.univ : Finset (MACCodebook M₁ n α₁)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
    rw [sum_measureReal_singleton (μ := codebookMeasure p₁ M₁ n)
      (Finset.univ : Finset (MACCodebook M₁ n α₁)), h_real_univ]
  have h2 : ∑ c₂ : MACCodebook M₂ n α₂, (codebookMeasure p₂ M₂ n).real {c₂} = 1 := by
    have h_real_univ : (codebookMeasure p₂ M₂ n).real
        ((Finset.univ : Finset (MACCodebook M₂ n α₂)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
    rw [sum_measureReal_singleton (μ := codebookMeasure p₂ M₂ n)
      (Finset.univ : Finset (MACCodebook M₂ n α₂)), h_real_univ]
  -- Flatten to a single sum over the product codebook space.
  set weight : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂ → ℝ :=
    fun p ↦ (codebookMeasure p₁ M₁ n).real {p.1} * (codebookMeasure p₂ M₂ n).real {p.2}
    with hweight_def
  set val : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂ → ℝ :=
    fun p ↦ ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε p.1 p.2).averageErrorProb W).toReal
    with hval_def
  have h_w_nn : ∀ p, 0 ≤ weight p := fun p ↦ mul_nonneg measureReal_nonneg measureReal_nonneg
  have h_weight_sum : ∑ p : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂, weight p = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hweight_def]
    rw [← h1]
    refine Finset.sum_congr rfl (fun c₁ _ ↦ ?_)
    rw [← Finset.mul_sum, h2, mul_one]
  -- The flattened expectation is the iterated double sum.
  have h_avg_flat : ∑ p : MACCodebook M₁ n α₁ × MACCodebook M₂ n α₂, weight p * val p ≤ B := by
    rw [Fintype.sum_prod_type]
    refine le_trans (le_of_eq ?_) h_avg
    simp only [hweight_def, hval_def]
  -- Some weight is positive (the weights sum to 1 ≠ 0).
  have h_exists_pos : ∃ p, 0 < weight p := by
    by_contra h_np
    simp only [not_exists, not_lt] at h_np
    have h_all_zero : ∀ p, weight p = 0 := fun p ↦ le_antisymm (h_np p) (h_w_nn p)
    have : ∑ p, weight p = 0 := Finset.sum_eq_zero (fun p _ ↦ h_all_zero p)
    rw [this] at h_weight_sum; exact one_ne_zero h_weight_sum.symm
  obtain ⟨p₀, hp₀_pos⟩ := h_exists_pos
  -- Contradiction: B = B·1 < ∑ weight·val ≤ B.
  have h_contra : B < ∑ p, weight p * val p := by
    calc B = B * 1 := (mul_one B).symm
      _ = B * ∑ p, weight p := by rw [h_weight_sum]
      _ = ∑ p, weight p * B := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ < ∑ p, weight p * val p := by
          refine Finset.sum_lt_sum (fun p _ ↦ ?_) ⟨p₀, Finset.mem_univ _, ?_⟩
          · exact mul_le_mul_of_nonneg_left (h_none p.1 p.2).le (h_w_nn p)
          · exact mul_lt_mul_of_pos_left (h_none p₀.1 p₀.2) hp₀_pos
  exact (lt_irrefl _) (lt_of_le_of_lt h_avg_flat h_contra)

/-- Closed-form `N` for the two-user (E3) "both indices wrong" term: with the AEP gap
`Iboth − (R₁ + R₂) − 3ε > 0`, the product `(⌈exp(nR₁)⌉−1)(⌈exp(nR₂)⌉−1)` of the two
codebook sizes times `exp(n(−Iboth+3ε))` falls below any tolerance for large `n`.
@audit:ok -/
theorem mac_E3_lt_of_rate {Iboth R₁ R₂ ε ε' : ℝ}
    (hgap : 0 < Iboth - (R₁ + R₂) - 3 * ε) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N,
      ((Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1) *
        ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
        Real.exp ((n : ℝ) * (-Iboth + 3 * ε)) < ε' := by
  obtain ⟨N, hN⟩ := exp_neg_mul_lt_of_rate hgap hε'
  refine ⟨N, fun n hn ↦ ?_⟩
  have he1 : (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1 ≤ Real.exp ((n : ℝ) * R₁) := by
    have := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R₁)).le; linarith
  have he2 : (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1 ≤ Real.exp ((n : ℝ) * R₂) := by
    have := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R₂)).le; linarith
  have hnn1 : 0 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
    linarith
  have hnn2 : 0 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
    linarith
  calc ((Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) - 1) *
          ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
          Real.exp ((n : ℝ) * (-Iboth + 3 * ε))
      ≤ Real.exp ((n : ℝ) * R₁) * Real.exp ((n : ℝ) * R₂) *
          Real.exp ((n : ℝ) * (-Iboth + 3 * ε)) := by
        gcongr
    _ = Real.exp (-(n : ℝ) * (Iboth - (R₁ + R₂) - 3 * ε)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ < ε' := hN n hn

/-! ### Headline -/

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **MAC achievability** (Cover–Thomas Theorem 15.3.1, corner-point form).  For an
independent product input `p₁ ⊗ p₂` with full-support marginals and a full-support MAC
channel `W`, any rate pair `(R₁, R₂)` strictly inside the corner-point region
`R₁ < I(X₁; (X₂, Y))`, `R₂ < I(X₂; (X₁, Y))`, `R₁ + R₂ < I((X₁, X₂); Y)` is
achievable: for every target error `ε' > 0` there is `N` such that for all `n ≥ N`
there is a length-`n` two-user code with at least `exp(n R₁)` / `exp(n R₂)` messages per
user whose average error probability is `< ε'`.
@audit:ok -/
@[entry_point]
theorem mac_achievability
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    {R₁ R₂ : ℝ} (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < macInfo₁ p₁ p₂ W) (hR₂lt : R₂ < macInfo₂ p₁ p₂ W)
    (hRsum : R₁ + R₂ < macInfoBoth p₁ p₂ W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁_lb : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂_lb : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : MACCode M₁ M₂ n α₁ α₂ β),
        (c.averageErrorProb W).toReal < ε' := by
  classical
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Rate slack `ε`: a sixth of the minimum of the three corner gaps.
  set gap : ℝ := min (min (macInfo₁ p₁ p₂ W - R₁) (macInfo₂ p₁ p₂ W - R₂))
      (macInfoBoth p₁ p₂ W - (R₁ + R₂)) with hgap_def
  have hgapA : gap ≤ macInfo₁ p₁ p₂ W - R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hgapB : gap ≤ macInfo₂ p₁ p₂ W - R₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hgapC : gap ≤ macInfoBoth p₁ p₂ W - (R₁ + R₂) := min_le_right _ _
  have hgap_pos : 0 < gap :=
    lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  set ε : ℝ := gap / 6 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have h3ε : 3 * ε = gap / 2 := by rw [hε_def]; ring
  have hgap1 : 0 < macInfo₁ p₁ p₂ W - R₁ - 3 * ε := by linarith
  have hgap2 : 0 < macInfo₂ p₁ p₂ W - R₂ - 3 * ε := by linarith
  have hgap3 : 0 < macInfoBoth p₁ p₂ W - (R₁ + R₂) - 3 * ε := by linarith
  have hε'4 : 0 < ε' / 4 := by linarith
  -- Measurability of the seven coordinate selectors.
  have hm_X2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hm_Y : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  have hm_X1X2 : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm_X1Y : Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  -- (N₀) AEP: the correct-pair-typical probability tends to 1.
  have h_aep := macJointlyTypicalSet_prob_tendsto_one μ macX1s macX2s macYs
    measurable_macX1s measurable_macX2s measurable_macYs
    (macAmbient_pairwise_coord p₁ p₂ W Prod.fst measurable_fst)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.fst measurable_fst i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ q.2.1) hm_X2)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.1) hm_X2 i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ q.2.2) hm_Y)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.2) hm_Y i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1)) hm_X1X2)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1)) hm_X1X2 i)
    (macAmbient_pairwise_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2)) hm_X1Y)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2)) hm_X1Y i)
    (macAmbient_pairwise_coord p₁ p₂ W Prod.snd measurable_snd)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.snd measurable_snd i)
    (macAmbient_pairwise_coord p₁ p₂ W id measurable_id)
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W id measurable_id i)
    hε_pos
  have h_aep_real : Filter.Tendsto
      (fun n : ℕ ↦ (μ {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
          macJointlyTypicalSet μ macX1s macX2s macYs n ε}).toReal)
      Filter.atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (a := (1 : ℝ≥0∞)) (by simp)).comp h_aep
    simpa [Function.comp_def] using h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (h_aep_real.eventually (eventually_gt_nhds (show (1 : ℝ) - ε' / 4 < 1 by linarith)))
  -- (N₁, N₂, N₃) exponential decay of the three alias terms.
  obtain ⟨N₁, hN₁⟩ := channelCoding_E2_lt_of_rate (I := macInfo₁ p₁ p₂ W) (R := R₁)
    (ε := ε) (ε' := ε' / 4) hgap1 hε'4
  obtain ⟨N₂, hN₂⟩ := channelCoding_E2_lt_of_rate (I := macInfo₂ p₁ p₂ W) (R := R₂)
    (ε := ε) (ε' := ε' / 4) hgap2 hε'4
  obtain ⟨N₃, hN₃⟩ := mac_E3_lt_of_rate (Iboth := macInfoBoth p₁ p₂ W) (R₁ := R₁) (R₂ := R₂)
    (ε := ε) (ε' := ε' / 4) hgap3 hε'4
  refine ⟨max (max N₀ N₁) (max N₂ N₃), fun n hn ↦ ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set M₁ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₁)) with hM₁_def
  set M₂ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₂)) with hM₂_def
  have hM₁_pos : 0 < M₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM₂_pos : 0 < M₂ := Nat.ceil_pos.mpr (Real.exp_pos _)
  -- The two-codebook average bound.
  have h_avg_bound := mac_random_codebook_average_le (M₁ := M₁) (M₂ := M₂) (n := n)
    p₁ p₂ W hp₁ hp₂ hW hM₁_pos hM₂_pos hε_pos
  -- Bound the four terms.
  have hE0 : μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
      macJointlyTypicalSet μ macX1s macX2s macYs n ε} ≤ ε' / 4 := by
    have h_meas_good : MeasurableSet
        {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∈
            macJointlyTypicalSet μ macX1s macX2s macYs n ε} := by
      have h_meas_triple : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
          (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
        (measurable_jointRV (α := α₁) macX1s measurable_macX1s n).prodMk
          ((measurable_jointRV (α := α₂) macX2s measurable_macX2s n).prodMk
            (measurable_jointRV (α := β) macYs measurable_macYs n))
      exact h_meas_triple (measurableSet_macJointlyTypicalSet μ macX1s macX2s macYs n ε)
    exact complementProbReal_le_of_one_sub_le h_meas_good (le_of_lt (hN₀ n hn0))
  have hE1 : ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε)) < ε' / 4 := by
    have := hN₁ n hn1
    rwa [hM₁_def]
  have hE2 : ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε)) < ε' / 4 := by
    have := hN₂ n hn2
    rwa [hM₂_def]
  have hE3 : ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) *
      Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) < ε' / 4 := by
    have := hN₃ n hn3
    rwa [hM₁_def, hM₂_def]
  have hRHS_lt :
      μ.real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉
            macJointlyTypicalSet μ macX1s macX2s macYs n ε}
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₁ p₁ p₂ W) + 3 * ε))
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(macInfo₂ p₁ p₂ W) + 3 * ε))
        + ((M₁ : ℝ) - 1) * ((M₂ : ℝ) - 1) *
            Real.exp ((n : ℝ) * (-(macInfoBoth p₁ p₂ W) + 3 * ε)) < ε' := by
    linarith
  -- Pigeonhole to a deterministic codebook pair, then package the code.
  obtain ⟨c₁, c₂, hcb⟩ := mac_exists_codebook_le_avg μ macX1s macX2s macYs W p₁ p₂
    hM₁_pos hM₂_pos _ h_avg_bound
  refine ⟨M₁, M₂, le_refl _, le_refl _,
    macCodebookToCode μ macX1s macX2s macYs hM₁_pos hM₂_pos ε c₁ c₂, ?_⟩
  exact lt_of_le_of_lt hcb hRHS_lt

end InformationTheory.Shannon.MAC
