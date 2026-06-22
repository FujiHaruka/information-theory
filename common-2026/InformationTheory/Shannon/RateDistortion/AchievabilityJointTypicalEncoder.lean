import InformationTheory.Shannon.RateDistortion.Achievability
import InformationTheory.Shannon.ChannelCoding.Achievability
import InformationTheory.Shannon.AEP.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.StrongLaw

/-!
# Rate-distortion achievability — joint-typical lossy encoder + distortion typical set

Two pieces of infrastructure for the lossy compression chain.

## Joint-typical lossy encoder

Symmetric counterpart to `ChannelCodingAchievability.jointTypicalDecoder` on the encoder
side of the lossy compression chain:

* `jointTypicalLossyEncoder` — given a codebook `c : Codebook M n β` and a source word
  `x : Fin n → α`, returns *some* (`Classical.choose`) message index `m` with
  `(x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε`. Falls back to `⟨0, hM⟩` if no such `m` exists.
* `lossyCodeOfCodebook` — bundles the joint-typical encoder + the codebook itself as
  decoder into a `LossyCode M n α β`.
* `jointTypicalLossyEncoder_spec_of_exists` / `_of_not_exists` — `dif_pos` / `dif_neg`
  characterisations of the two branches.

Note: unlike the channel-coding decoder side (`jointTypicalDecoder`), the lossy encoder
does not require uniqueness of the typical match — any one is fine because the
encoder's job is only to commit to a single index. Hence we use `Classical.choose`
of `∃ m, _` rather than `Classical.choose` of `∃! m, _`.

## Distortion typical set

The intersection of `jointlyTypicalSet` with the empirical-distortion constraint
`blockDistortion d n x y ≤ 𝔼[d(X_0, Y_0)] + δ`:

* `expectedJointDistortion μ X Y d` — Bochner integral of `d(X, Y)` under `μ`.
* `distortionTypicalSet μ Xs Ys d n ε δ` — set of `(x, y)` jointly typical *and*
  whose empirical block distortion is within `δ` of the joint expectation.
* basic structure lemmas: subset to `jointlyTypicalSet`, membership iff,
  `MeasurableSet`, finiteness.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open InformationTheory.Shannon.ChannelCoding (Codebook jointlyTypicalSet)
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
variable [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]

/-- Joint-typical lossy encoder. Given a codebook `c : Codebook M n β`,
returns the first (any) message index `m` whose codeword is jointly typical with the
source word `x`. Falls back to `⟨0, hM⟩` if no such `m` exists. -/
@[entry_point]
noncomputable def jointTypicalLossyEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    (Fin n → α) → Fin M := fun x ↦
  haveI : Decidable (∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε) :=
    Classical.propDecidable _
  if h : ∃ m : Fin M, (x, c m) ∈ jointlyTypicalSet μ Xs Ys n ε
    then Classical.choose h
    else ⟨0, hM⟩

/-- Bundle a codebook + joint-typical lossy encoder into a `LossyCode`. The codebook
itself serves as the decoder. -/
@[entry_point]
noncomputable def lossyCodeOfCodebook
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    {M n : ℕ} (hM : 0 < M) (ε : ℝ) (c : Codebook M n β) :
    LossyCode M n α β where
  encoder := jointTypicalLossyEncoder μ Xs Ys hM ε c
  decoder := c


/-! ## Distortion typical set -/

/-- Expected per-symbol distortion `𝔼_μ[d(X, Y)]` as a real Bochner integral. The
bound used in `distortionTypicalSet` references this quantity at `i = 0`; under
stationary i.i.d. hypotheses it is independent of `i`. -/
noncomputable def expectedJointDistortion
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (d : DistortionFn α β) : ℝ :=
  ∫ ω, ((d (X ω) (Y ω) : NNReal) : ℝ) ∂μ

/-- Distortion typical set. Pairs `(x, y) ∈ (Fin n → α) × (Fin n → β)` that are
both (a) jointly typical in the entropy sense (`jointlyTypicalSet μ Xs Ys n ε`) and
(b) whose empirical block distortion is within `δ` of the joint expectation
`𝔼[d(X_0, Y_0)]`. The set used by Cover-Thomas 10.5 to bound the distortion on
encoder-success events. -/
noncomputable def distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ) :
    Set ((Fin n → α) × (Fin n → β)) :=
  jointlyTypicalSet μ Xs Ys n ε ∩
    {p | blockDistortion d n p.1 p.2
          ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ}


omit [DecidableEq α] [DecidableEq β] in
/-- On `distortionTypicalSet`, the empirical block distortion is bounded
by the joint expectation plus `δ`. This is the structural fact that drives the
distortion bound on encoder-success events in Cover-Thomas 10.5 (10.85). -/
theorem blockDistortion_le_of_mem_distortionTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (d : DistortionFn α β) (n : ℕ) (ε δ : ℝ)
    {p : (Fin n → α) × (Fin n → β)}
    (h : p ∈ distortionTypicalSet μ Xs Ys d n ε δ) :
    blockDistortion d n p.1 p.2
      ≤ expectedJointDistortion μ (Xs 0) (Ys 0) d + δ := h.2


/-! ### Lower-bound joint-AEP independent probability

The lower-bound counterpart to `ChannelCoding.jointlyTypicalSet_indep_prob_le`
for the single-codeword typical-match probability (Cover–Thomas 10.5, (10.85)).
The input hypothesis is in joint-law form `μ.real {ω | (jX, jY) ∈ JTS} ≥ 1 - η`,
as supplied by `jointlyTypicalSet_prob_tendsto_one`.
-/

omit [DecidableEq α] [DecidableEq β] in
/-- Size lower bound on the jointly typical set (mirror of
`jointlyTypicalSet_card_le`). If under joint law the event
"`(jointRV Xs n ω, jointRV Ys n ω) ∈ JTS`" has measure ≥ `1 - η`, then
`|JTS| ≥ (1 - η) · exp(n · (H(Z) - ε))`. -/
private theorem jointlyTypicalSet_card_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepZ_full : iIndepFun (fun i ↦ ChannelCoding.jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
                      (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    (hposZ : ∀ p : α × β,
      0 < (μ.map (ChannelCoding.jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε η : ℝ}
    (hμJTS : (1 - η) ≤ μ.real
      {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}) :
    (1 - η) * Real.exp ((n : ℝ) *
        (entropy μ (ChannelCoding.jointSequence Xs Ys 0) - ε))
      ≤ ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) := by
  classical
  set Zs : ℕ → Ω → α × β := ChannelCoding.jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i ↦
    ChannelCoding.measurable_jointSequence Xs Ys hXs hYs i
  -- φ : (Fin n → α) × (Fin n → β) → Fin n → α × β reshapes pair into joint.
  let φ : (Fin n → α) × (Fin n → β) → (Fin n → α × β) :=
    fun p i ↦ (p.1 i, p.2 i)
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · funext i
      exact ((Prod.mk.injEq _ _ _ _).mp (congr_fun hpq i)).1
    · funext i
      exact ((Prod.mk.injEq _ _ _ _).mp (congr_fun hpq i)).2
  set JT : Finset ((Fin n → α) × (Fin n → β)) :=
    (ChannelCoding.jointlyTypicalSet_finite μ Xs Ys n ε).toFinset with hJT_def
  set H : ℝ := entropy μ (Zs 0) with hH_def
  set JTimg : Finset (Fin n → α × β) := JT.image φ with hJTimg_def
  have hJTimg_card : JTimg.card = JT.card :=
    Finset.card_image_of_injective _ hφ_inj
  -- Each q ∈ JTimg lies in typicalSet μ Zs n ε (third conjunct of JTS).
  have h_JTimg_sub_T : ∀ q ∈ JTimg, q ∈ typicalSet μ Zs n ε := by
    intro q hq
    rw [hJTimg_def, Finset.mem_image] at hq
    obtain ⟨⟨x, y⟩, hxy_mem, rfl⟩ := hq
    have hxy : (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε :=
      (Set.Finite.mem_toFinset _).mp hxy_mem
    exact hxy.2.2
  -- jointRV Zs n ω = φ (jointRV Xs n ω, jointRV Ys n ω).
  have h_jointRV_factor : ∀ ω,
      jointRV Zs n ω = φ (jointRV Xs n ω, jointRV Ys n ω) := by
    intro ω
    funext i
    rfl
  -- The joint event in Ω = preimage of (φ '' JTS) under jointRV Zs n.
  have h_event_eq : {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}
      = jointRV Zs n ⁻¹' (JTimg : Set (Fin n → α × β)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hJTimg_def, Finset.coe_image,
      Finset.mem_coe, Set.mem_image]
    constructor
    · intro h
      refine ⟨(jointRV Xs n ω, jointRV Ys n ω), ?_, ?_⟩
      · rw [hJT_def, Set.Finite.mem_toFinset]; exact h
      · exact (h_jointRV_factor ω).symm
    · rintro ⟨⟨x, y⟩, hxy_mem, hp_eq⟩
      rw [hJT_def, Set.Finite.mem_toFinset] at hxy_mem
      have h_φ_eq : φ (jointRV Xs n ω, jointRV Ys n ω) = φ (x, y) := by
        rw [← h_jointRV_factor ω]; exact hp_eq.symm
      have h_eq : (jointRV Xs n ω, jointRV Ys n ω) = (x, y) := hφ_inj h_φ_eq
      rw [h_eq]; exact hxy_mem
  -- The image is measurable (it lives in a finite ambient).
  have hJTimg_measurable : MeasurableSet (JTimg : Set (Fin n → α × β)) :=
    (Set.toFinite _).measurableSet
  -- Convert μ.real (joint event) into (μ.map jointRV Zs n).real (JTimg).
  have h_map : μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
        jointlyTypicalSet μ Xs Ys n ε}
      = (μ.map (jointRV Zs n)).real (JTimg : Set (Fin n → α × β)) := by
    show (μ {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}).toReal
        = ((μ.map (jointRV Zs n)) (JTimg : Set _)).toReal
    rw [h_event_eq]
    congr 1
    exact (Measure.map_apply (measurable_jointRV Zs hZs n) hJTimg_measurable).symm
  -- (μ.map jointRV Zs n).real (↑JTimg) = ∑ q ∈ JTimg, μ.real {q}.
  have h_sum_decomp : (μ.map (jointRV Zs n)).real (JTimg : Set (Fin n → α × β))
      = ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q} :=
    (sum_measureReal_singleton (μ := μ.map (jointRV Zs n)) JTimg).symm
  -- Each singleton ≤ exp(-n(H - ε)) via typicalSet_prob_le on Zs.
  have h_each_le : ∀ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q}
      ≤ Real.exp (- (n : ℝ) * (H - ε)) := by
    intro q hq
    have hq_T : q ∈ typicalSet μ Zs n ε := h_JTimg_sub_T q hq
    exact InformationTheory.Shannon.typicalSet_prob_le μ Zs hZs hindepZ_full hidentZ
      hposZ n q hq_T
  have h_sum_le : ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q}
      ≤ (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := by
    calc ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q}
        ≤ ∑ _q ∈ JTimg, Real.exp (- (n : ℝ) * (H - ε)) := Finset.sum_le_sum h_each_le
      _ = (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h_combined : (1 - η) ≤ (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := by
    calc (1 - η)
        ≤ μ.real {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε} := hμJTS
      _ = (μ.map (jointRV Zs n)).real (JTimg : Set _) := h_map
      _ = ∑ q ∈ JTimg, (μ.map (jointRV Zs n)).real {q} := h_sum_decomp
      _ ≤ (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε)) := h_sum_le
  -- Multiply by exp((n)(H-ε)) and cancel.
  have hexp_pos : 0 < Real.exp ((n : ℝ) * (H - ε)) := Real.exp_pos _
  have h_exp_cancel : Real.exp (- (n : ℝ) * (H - ε)) * Real.exp ((n : ℝ) * (H - ε)) = 1 := by
    rw [show -(n : ℝ) * (H - ε) = -((n : ℝ) * (H - ε)) from by ring, ← Real.exp_add]
    simp
  have h_mul := mul_le_mul_of_nonneg_right h_combined hexp_pos.le
  have h_rhs : (JTimg.card : ℝ) * Real.exp (- (n : ℝ) * (H - ε))
        * Real.exp ((n : ℝ) * (H - ε)) = (JTimg.card : ℝ) := by
    rw [mul_assoc, h_exp_cancel, mul_one]
  rw [h_rhs, hJTimg_card] at h_mul
  exact h_mul

omit [DecidableEq α] [DecidableEq β] in
/-- Anti-direction (lower-bound) joint-AEP indep probability.
The probability under the product measure `μX^n × μY^n` that `(X̃, Ỹ)` lies in
the jointly typical set is bounded below by `(1 - η) · exp(-n · (I + 3ε))`,
which is Cover-Thomas (10.85). Mirror of `jointlyTypicalSet_indep_prob_le`. -/
@[entry_point]
theorem jointlyTypicalSet_indep_prob_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i ↦ Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i ↦ ChannelCoding.jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i, IdentDistrib (ChannelCoding.jointSequence Xs Ys i)
                      (ChannelCoding.jointSequence Xs Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (ChannelCoding.jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε η : ℝ}
    (hμJTS : (1 - η) ≤ μ.real
      {ω | (jointRV Xs n ω, jointRV Ys n ω) ∈
            jointlyTypicalSet μ Xs Ys n ε}) :
    (1 - η) * Real.exp ((n : ℝ) *
        (entropy μ (ChannelCoding.jointSequence Xs Ys 0)
         - entropy μ (Xs 0) - entropy μ (Ys 0) - 3 * ε))
      ≤ ((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real
          (jointlyTypicalSet μ Xs Ys n ε) := by
  classical
  set μX : Measure (Fin n → α) := μ.map (jointRV Xs n) with hμX_def
  set μY : Measure (Fin n → β) := μ.map (jointRV Ys n) with hμY_def
  set HX : ℝ := entropy μ (Xs 0) with hHX_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set HZ : ℝ := entropy μ (ChannelCoding.jointSequence Xs Ys 0) with hHZ_def
  set A : Set ((Fin n → α) × (Fin n → β)) := jointlyTypicalSet μ Xs Ys n ε with hA_def
  set Afin : Finset ((Fin n → α) × (Fin n → β)) :=
    (ChannelCoding.jointlyTypicalSet_finite μ Xs Ys n ε).toFinset with hAfin_def
  have hXmeas : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
  have hYmeas : Measurable (jointRV Ys n) := measurable_jointRV Ys hYs n
  haveI : IsProbabilityMeasure μX :=
    Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  haveI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  haveI : IsProbabilityMeasure (μX.prod μY) := by
    have : IsFiniteMeasure μX := inferInstance
    have : IsFiniteMeasure μY := inferInstance
    infer_instance
  -- Step 1: rewrite (μX.prod μY).real A as a Finset sum over Afin.
  have h_sum_decomp :
      (μX.prod μY).real A
        = ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := by
    have h_real_eq : (μX.prod μY).real A = ∑ p ∈ Afin, (μX.prod μY).real {p} := by
      have h_coe : (Afin : Set _) = A :=
        (ChannelCoding.jointlyTypicalSet_finite μ Xs Ys n ε).coe_toFinset
      rw [← h_coe, ← sum_measureReal_singleton (μ := μX.prod μY) Afin]
    rw [h_real_eq]
    refine Finset.sum_congr rfl ?_
    intro p _
    have h_singleton_prod : ({p} : Set ((Fin n → α) × (Fin n → β)))
        = ({p.1} : Set (Fin n → α)) ×ˢ ({p.2} : Set (Fin n → β)) := by
      ext q
      simp [Prod.ext_iff]
    rw [h_singleton_prod]
    exact measureReal_prod_prod _ _
  -- Step 2: each summand bounded below by exp(-n(HX + ε)) · exp(-n(HY + ε)).
  have h_each_ge : ∀ p ∈ Afin,
      Real.exp (- (n : ℝ) * (HX + ε)) * Real.exp (- (n : ℝ) * (HY + ε))
        ≤ μX.real {p.1} * μY.real {p.2} := by
    intro p hp
    have hp_set : p ∈ A := (Set.Finite.mem_toFinset _).mp hp
    rcases hp_set with ⟨hxX, hyY, _hxyZ⟩
    have hbdX : Real.exp (- (n : ℝ) * (HX + ε)) ≤ μX.real {p.1} :=
      InformationTheory.Shannon.typicalSet_prob_ge μ Xs hXs hindepX_full hidentX
        hposX n p.1 hxX
    have hbdY : Real.exp (- (n : ℝ) * (HY + ε)) ≤ μY.real {p.2} :=
      InformationTheory.Shannon.typicalSet_prob_ge μ Ys hYs hindepY_full hidentY
        hposY n p.2 hyY
    have hY_exp_nn : 0 ≤ Real.exp (- (n : ℝ) * (HY + ε)) := (Real.exp_pos _).le
    have hX_exp_nn : 0 ≤ Real.exp (- (n : ℝ) * (HX + ε)) := (Real.exp_pos _).le
    have hX_nn : 0 ≤ μX.real {p.1} := measureReal_nonneg
    calc Real.exp (- (n : ℝ) * (HX + ε)) * Real.exp (- (n : ℝ) * (HY + ε))
        ≤ μX.real {p.1} * Real.exp (- (n : ℝ) * (HY + ε)) := by
          exact mul_le_mul_of_nonneg_right hbdX hY_exp_nn
      _ ≤ μX.real {p.1} * μY.real {p.2} := by
          exact mul_le_mul_of_nonneg_left hbdY hX_nn
  -- Step 3: lower bound the sum by card · C.
  set C : ℝ := Real.exp (- (n : ℝ) * (HX + ε)) * Real.exp (- (n : ℝ) * (HY + ε))
    with hC_def
  have hC_nn : 0 ≤ C := by
    simp only [hC_def]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have h_sum_ge : (Afin.card : ℝ) * C
      ≤ ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := by
    calc (Afin.card : ℝ) * C
        = ∑ _p ∈ Afin, C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := Finset.sum_le_sum h_each_ge
  -- Step 4: card lower bound via jointlyTypicalSet_card_ge.
  have h_card_ge : (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) ≤ (Afin.card : ℝ) := by
    have := jointlyTypicalSet_card_ge μ Xs Ys hXs hYs hindepZ_full hidentZ hposZ n
      (ε := ε) (η := η) hμJTS
    -- The goal uses Afin which is by hAfin_def equal to (jTS).toFinite.toFinset.
    convert this using 1
  -- Step 5: combine.
  have h_lhs_eq :
      (1 - η) * Real.exp ((n : ℝ) * ((HZ - HX - HY) - 3 * ε))
        = (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) * C := by
    have h_C_expand : C
        = Real.exp (- (n : ℝ) * (HX + ε) + - (n : ℝ) * (HY + ε)) := by
      rw [hC_def, ← Real.exp_add]
    rw [h_C_expand]
    rw [show (1 - η) * Real.exp ((n : ℝ) * (HZ - ε))
          * Real.exp (- (n : ℝ) * (HX + ε) + - (n : ℝ) * (HY + ε))
        = (1 - η) * (Real.exp ((n : ℝ) * (HZ - ε))
            * Real.exp (- (n : ℝ) * (HX + ε) + - (n : ℝ) * (HY + ε))) from by ring]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have h_card_mul_C : (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) * C
      ≤ (Afin.card : ℝ) * C := mul_le_mul_of_nonneg_right h_card_ge hC_nn
  calc (1 - η) * Real.exp ((n : ℝ) * ((HZ - HX - HY) - 3 * ε))
      = (1 - η) * Real.exp ((n : ℝ) * (HZ - ε)) * C := h_lhs_eq
    _ ≤ (Afin.card : ℝ) * C := h_card_mul_C
    _ ≤ ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := h_sum_ge
    _ = (μX.prod μY).real A := h_sum_decomp.symm

end InformationTheory.Shannon
