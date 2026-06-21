import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.AchievabilityCodebook
import InformationTheory.Shannon.AWGN.AchievabilityTypicalDecoder
import InformationTheory.Shannon.AWGN.AchievabilityExpurgation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# AWGN achievability assembly

The assembled achievability statement for the AWGN channel coding theorem
(Cover–Thomas 9.2, Theorem 9.1.1): combining the random Gaussian codebook, the
joint-typicality decoder and union bound, the power-constraint witness, and
worst-half expurgation into the existence of good `(M, n)` codes for any rate
below the Gaussian capacity.

## Main statements

* `isAwgnTypicalityHypothesis` — the assembled achievability statement consumed
  by the headline `awgn_achievability`.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

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
