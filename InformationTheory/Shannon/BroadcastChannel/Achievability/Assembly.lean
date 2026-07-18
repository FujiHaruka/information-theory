import InformationTheory.Shannon.BroadcastChannel.Achievability.ErrorAnalysis

/-!
# Degraded broadcast channel — superposition random-coding assembly and headline

The superposition random-coding assembly (E0 vanishing, per-codebook error decomposition,
two-codebook average bounds, random → deterministic two-tier pigeonhole, degradedness + rate
slack) and the headline `bc_achievability`.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.MAC
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

variable {U α β₁ β₂ : Type*}
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-! ### Assembly (superposition random-coding, two receivers)

The receiver-1/receiver-2 swap lemmas above are stitched into the headline through the
same skeleton as the MAC achievability assembly (`InformationTheory.Shannon.MAC`
`Achievability.lean`), adapted to the two-tier (cloud / conditional-satellite) codebook and
the two per-receiver error probabilities:

* **C.1** — E0 vanishing: the correct-cloud (`(U, Y₂)`) and correct-triple (`(U, X, Y₁)`)
  atypical masses tend to `0` (AEP / LLN).
* **C.2** — per-codebook `averageErrorProb.toReal` decomposition into the Bonferroni terms.
* **C.3** — two-codebook average bounds (weight-summed swaps).
* **C.4** — pigeonhole to a deterministic codebook pair.
* **C.5** — rate-slack vanishing + degradedness `I((U, X); Y₁) ≥ I(X; Y₁ ∣ U) + I(U; Y₂)`.
-/

/-- Pairwise independence of any BC coordinate selector under the ambient measure. -/
lemma bcAmbient_pairwise_coord {γ : Type*} [MeasurableSpace γ]
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (g : U × α × β₁ × β₂ → γ) (hg : Measurable g) :
    Pairwise fun i j ↦
      IndepFun (fun ω : ℕ → U × α × β₁ × β₂ ↦ g (ω i)) (fun ω ↦ g (ω j))
        (bcAmbientMeasure pU K W) := by
  intro i j hij
  exact (bcAmbient_iIndepFun_coord pU K W g hg).indepFun hij

/-! #### C.1 — E0 vanishing -/

/-- **`(U, X, Y₁)` channel fold.**  The `(U, X, Y₁)`-block law of a finite set `T` equals the
cloud/satellite/channel average of the `β₁`-projected channel mass.  Receiver-1 analogue of
`bc_chan_fold_UY₂_set`, obtained from the master fold by projecting the pair output to `β₁`. -/
lemma bc_chan_fold_UXY₁_set
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → U) × (Fin n → α) × (Fin n → β₁))) :
    ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real T
      = ∑ u : Fin n → U, ∑ x : Fin n → α,
          (Measure.pi (fun _ : Fin n ↦ pU)).real {u}
            * (Measure.pi (fun l ↦ K (u l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real {y | (u, x, fun i ↦ (y i).1) ∈ T} := by
  classical
  have hmeas_master : Measurable (fun ω : ℕ → U × α × β₁ × β₂ ↦
      (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω)) :=
    (measurable_jointRV bcUs (fun i ↦ (measurable_pi_apply i).fst) n).prodMk
      ((measurable_jointRV bcXs (fun i ↦ (measurable_pi_apply i).snd.fst) n).prodMk
        (measurable_jointRV bcYPs (fun i ↦ (measurable_pi_apply i).snd.snd) n))
  have hproj_meas : Measurable
      (fun t : (Fin n → U) × (Fin n → α) × (Fin n → β₁ × β₂) ↦
        ((t.1, t.2.1, fun i ↦ (t.2.2 i).1) : (Fin n → U) × (Fin n → α) × (Fin n → β₁))) :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_pi_lambda _ fun i ↦
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).fst))
  have hmap : (bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))
      = ((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcYPs n ω))).map
        (fun t ↦ (t.1, t.2.1, fun i ↦ (t.2.2 i).1)) := by
    rw [Measure.map_map hproj_meas hmeas_master]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    bc_chan_fold_master pU K W n
      ((fun t ↦ ((t.1, t.2.1, fun i ↦ (t.2.2 i).1) :
        (Fin n → U) × (Fin n → α) × (Fin n → β₁))) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- **Receiver-1 correct-triple averaged swap (E0).**  The two-tier random-codebook average of
the correct-triple atypical event equals the joint `(U, X, Y₁)`-block law of the atypical set.
Receiver-1 analogue of `bc_random_codebook_E0₂_swap`. -/
theorem bc_random_codebook_E0₁_swap
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} {ε : ℝ}
    (m : Fin M₁ × Fin M₂) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU m.2, cX m, fun i ↦ (y i).1)
                      ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      = ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
          { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
            q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε } := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  set J := macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε with hJ_def
  -- Step 1: satellite single-row marginalization (per cloud codebook).  The correct row `m`
  -- both drives the channel and indexes the atypical slice.
  have hsat : ∀ cU : BCCloudCodebook M₂ n U,
      (∑ cX : BCSatelliteCodebook M₁ M₂ n α, (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
          * (Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ | (cU m.2, cX m, fun i ↦ (y i).1) ∉ J })
        = ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (cU m.2 l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (cU m.2, x, fun i ↦ (y i).1) ∉ J } := by
    intro cU
    haveI : IsProbabilityMeasure (bcSatelliteCodebookMeasure K M₁ M₂ n cU) := by
      unfold bcSatelliteCodebookMeasure; infer_instance
    have hmp : (bcSatelliteCodebookMeasure K M₁ M₂ n cU).map (Function.eval m)
        = Measure.pi (fun l ↦ K (cU m.2 l)) :=
      (measurePreserving_eval
        (fun p : Fin M₁ × Fin M₂ ↦ Measure.pi (fun l ↦ K (cU p.2 l))) m).map_eq
    have h1 := sum_weighted_map (bcSatelliteCodebookMeasure K M₁ M₂ n cU) (Function.eval m)
      (measurable_pi_apply m)
      (fun z : Fin n → α ↦ (Measure.pi (fun i ↦ W (z i))).real
        { y : Fin n → β₁ × β₂ | (cU m.2, z, fun i ↦ (y i).1) ∉ J })
    rw [hmp] at h1
    exact h1
  -- Step 2: reduce the cloud codebook to the single transmitted row `m.2`.
  rw [show bcCloudCodebookMeasure pU M₂ n = codebookMeasure pU M₂ n from rfl]
  have e1 : ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ | (cU m.2, cX m, fun i ↦ (y i).1) ∉ J }
      = ∑ cU : Codebook M₂ n U, (codebookMeasure pU M₂ n).real {cU}
        * (fun a ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
            * (Measure.pi (fun i ↦ W (x i))).real
                { y : Fin n → β₁ × β₂ | (a, x, fun i ↦ (y i).1) ∉ J }) (cU m.2) := by
    refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
    rw [hsat cU]
  rw [e1, codebook_marginal_one pU M₂ n m.2
      (fun a ↦ ∑ x : Fin n → α, (Measure.pi (fun l ↦ K (a l))).real {x}
        * (Measure.pi (fun i ↦ W (x i))).real
            { y : Fin n → β₁ × β₂ | (a, x, fun i ↦ (y i).1) ∉ J })
      (fun _ ↦ Finset.sum_nonneg
        (fun _ _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg))]
  -- Step 3: fold the cloud/satellite/channel average back into the joint `(U, X, Y₁)`-block law.
  rw [bc_chan_fold_UXY₁_set pU K W n {q | q ∉ J}]
  simp only [Set.mem_setOf_eq]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  ring

/-- **Receiver-2 E0 vanishing.**  The correct-cloud atypical `(U, Y₂)`-block mass tends to `0`
by the two-variable joint AEP (`jointlyTypicalSet_prob_tendsto_one`). -/
theorem bc_E0₂_vanishing
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
          { q : (Fin n → U) × (Fin n → β₂) |
            q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε })
      Filter.atTop (nhds 0) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hmU : ∀ i, Measurable (bcUs i : (ℕ → U × α × β₁ × β₂) → U) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hmY₂ : ∀ i, Measurable (bcY₂s i : (ℕ → U × α × β₁ × β₂) → β₂) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.snd
  have hgY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hgUY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.2.2)) :=
    measurable_fst.prodMk hgY₂
  -- The AEP: the correct-cloud typical probability tends to 1.
  have h_aep := jointlyTypicalSet_prob_tendsto_one μ bcUs bcY₂s hmU hmY₂
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.1) measurable_fst)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.1) measurable_fst i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.2.2.2) hgY₂)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.2.2) hgY₂ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.2.2)) hgUY₂)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.2.2)) hgUY₂ i)
    hε
  -- Real version: the typical probability (as a real) tends to 1.
  have h_real : Filter.Tendsto
      (fun n : ℕ ↦ μ.real {ω | (jointRV bcUs n ω, jointRV bcY₂s n ω) ∈
          jointlyTypicalSet μ bcUs bcY₂s n ε}) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr (fun _ ↦ rfl) ((ENNReal.tendsto_toReal (by simp)).comp h_aep)
  -- The map-form atypical mass equals `1 − (typical real)`.
  have hg_n : ∀ n, Measurable
      (fun ω : ℕ → U × α × β₁ × β₂ ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω)) :=
    fun n ↦ (measurable_jointRV bcUs hmU n).prodMk (measurable_jointRV bcY₂s hmY₂ n)
  have key : ∀ n, ((μ.map (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
        { q : (Fin n → U) × (Fin n → β₂) | q ∉ jointlyTypicalSet μ bcUs bcY₂s n ε })
      = 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcY₂s n ω) ∈
          jointlyTypicalSet μ bcUs bcY₂s n ε} := by
    intro n
    rw [show { q : (Fin n → U) × (Fin n → β₂) | q ∉ jointlyTypicalSet μ bcUs bcY₂s n ε }
          = (jointlyTypicalSet μ bcUs bcY₂s n ε)ᶜ from rfl,
      map_measureReal_apply (hg_n n) (measurableSet_jointlyTypicalSet μ bcUs bcY₂s n ε).compl,
      Set.preimage_compl,
      probReal_compl_eq_one_sub ((hg_n n) (measurableSet_jointlyTypicalSet μ bcUs bcY₂s n ε))]
    rfl
  have h0 : Filter.Tendsto
      (fun n : ℕ ↦ 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcY₂s n ω) ∈
          jointlyTypicalSet μ bcUs bcY₂s n ε}) Filter.atTop (nhds 0) := by
    simpa using h_real.const_sub (1 : ℝ)
  exact Filter.Tendsto.congr (fun n ↦ (key n).symm) h0

/-- **Receiver-1 E0 vanishing.**  The correct-triple atypical `(U, X, Y₁)`-block mass tends to
`0` by the three-variable joint AEP (`macJointlyTypicalSet_prob_tendsto_one`). -/
theorem bc_E0₁_vanishing
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
          { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
            q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε })
      Filter.atTop (nhds 0) := by
  classical
  set μ := bcAmbientMeasure pU K W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hmU : ∀ i, Measurable (bcUs i : (ℕ → U × α × β₁ × β₂) → U) :=
    fun i ↦ (measurable_pi_apply i).fst
  have hmX : ∀ i, Measurable (bcXs i : (ℕ → U × α × β₁ × β₂) → α) :=
    fun i ↦ (measurable_pi_apply i).snd.fst
  have hmY₁ : ∀ i, Measurable (bcY₁s i : (ℕ → U × α × β₁ × β₂) → β₁) :=
    fun i ↦ (measurable_pi_apply i).snd.snd.fst
  have hgX : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hgY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hgUX : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) := measurable_fst.prodMk hgX
  have hgUY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.2.1)) := measurable_fst.prodMk hgY₁
  have hgXY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.2.1, q.2.2.1)) := hgX.prodMk hgY₁
  have hgUXY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk (hgX.prodMk hgY₁)
  -- The AEP: the correct-triple typical probability tends to 1.
  have h_aep := macJointlyTypicalSet_prob_tendsto_one μ bcUs bcXs bcY₁s hmU hmX hmY₁
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.1) measurable_fst)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.1) measurable_fst i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.2.1) hgX)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.1) hgX i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ q.2.2.1) hgY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ q.2.2.1) hgY₁ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.1)) hgUX)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1)) hgUX i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.2.1)) hgUY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.2.1)) hgUY₁ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.2.1, q.2.2.1)) hgXY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.2.1, q.2.2.1)) hgXY₁ i)
    (bcAmbient_pairwise_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2.1)) hgUXY₁)
    (fun i ↦ bcAmbient_identDistrib_coord pU K W (fun q ↦ (q.1, q.2.1, q.2.2.1)) hgUXY₁ i)
    hε
  have h_real : Filter.Tendsto
      (fun n : ℕ ↦ μ.real {ω | (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω) ∈
          macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε}) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr (fun _ ↦ rfl) ((ENNReal.tendsto_toReal (by simp)).comp h_aep)
  have hg_n : ∀ n, Measurable
      (fun ω : ℕ → U × α × β₁ × β₂ ↦
        (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω)) :=
    fun n ↦ (measurable_jointRV bcUs hmU n).prodMk
      ((measurable_jointRV bcXs hmX n).prodMk (measurable_jointRV bcY₁s hmY₁ n))
  have key : ∀ n, ((μ.map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
        { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
          q ∉ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε })
      = 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω) ∈
          macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε} := by
    intro n
    rw [show { q : (Fin n → U) × (Fin n → α) × (Fin n → β₁) |
              q ∉ macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε }
          = (macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε)ᶜ from rfl,
      map_measureReal_apply (hg_n n)
        (measurableSet_macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε).compl,
      Set.preimage_compl,
      probReal_compl_eq_one_sub
        ((hg_n n) (measurableSet_macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε))]
    rfl
  have h0 : Filter.Tendsto
      (fun n : ℕ ↦ 1 - μ.real {ω | (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω) ∈
          macJointlyTypicalSet μ bcUs bcXs bcY₁s n ε}) Filter.atTop (nhds 0) := by
    simpa using h_real.const_sub (1 : ℝ)
  exact Filter.Tendsto.congr (fun n ↦ (key n).symm) h0

/-! #### C.2 — per-codebook `averageErrorProb.toReal` decomposition -/

/-- **Receiver-2 per-codebook averaging bound.**  The `.toReal` of the receiver-2 average error
probability of the deterministic code `bcCodebookToCode cU cX` is at most the uniform average of
the two-event Bonferroni bound (`bc_errorProbAt₂_le_bonferroni`). -/
theorem bc_averageErrorProb₂_toReal_le
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α) :
    ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal
      ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU m.2, fun i ↦ (y i).2) ∉
                  jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
            + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
                (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU w₂', fun i ↦ (y i).2) ∈
                      jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }) := by
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have h_ne_top : ∀ m : Fin M₁ × Fin M₂,
      (bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂ W m ≠ ⊤ :=
    fun m ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂_le_one W m)
  have h_eq : ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₂ W m).toReal := by
    unfold BroadcastCode.averageErrorProb₂
    rw [if_neg hMpos.ne', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum (fun m _ ↦ bc_errorProbAt₂_le_bonferroni pU K W hM₁ hM₂ cU cX m)

/-- **Receiver-1 per-codebook averaging bound.**  The `.toReal` of the receiver-1 average error
probability of `bcCodebookToCode cU cX` is at most the uniform average of the three-event
Bonferroni bound (`bc_errorProbAt₁_le_bonferroni3`). -/
theorem bc_averageErrorProb₁_toReal_le
    (pU : Measure U) (K : Kernel U α) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α) :
    ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      ≤ ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((Measure.pi (fun i ↦ W (cX m i))).real
              { y : Fin n → β₁ × β₂ |
                (cU m.2, cX m, fun i ↦ (y i).1) ∉
                  macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
                (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1) ∈
                      macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                      (Finset.univ : Finset (Fin M₁)),
                (Measure.pi (fun i ↦ W (cX m i))).real
                  { y : Fin n → β₁ × β₂ |
                    (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1) ∈
                      macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }) := by
  have hMpos : 0 < M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have h_ne_top : ∀ m : Fin M₁ × Fin M₂,
      (bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁ W m ≠ ⊤ :=
    fun m ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁_le_one W m)
  have h_eq : ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m : Fin M₁ × Fin M₂,
          ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).errorProbAt₁ W m).toReal := by
    unfold BroadcastCode.averageErrorProb₁
    rw [if_neg hMpos.ne', ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ ↦ h_ne_top m)]
  rw [h_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum (fun m _ ↦ bc_errorProbAt₁_le_bonferroni3 pU K W hM₁ hM₂ cU cX m)

/-! #### C.3 — two-codebook average bounds

The two-tier codebook expectation is the nonnegative-weighted "linear functional"
`L f = ∑ cU, wU cU * ∑ cX, wX cU cX * f cU cX`.  The generic `bc_weighted_two_tier_*`
lemmas express its monotonicity and linearity; the per-alias swaps evaluate `L` on each
Bonferroni term, and `bc_pair_aggregate₂/₁` fold them into the closed-form bounds. -/

/-- Monotonicity of the two-tier nonnegative-weighted codebook average. -/
lemma bc_weighted_two_tier_mono {κU κX : Type*} [Fintype κU] [Fintype κX]
    (wU : κU → ℝ) (wX : κU → κX → ℝ)
    (hwU : ∀ cU, 0 ≤ wU cU) (hwX : ∀ cU cX, 0 ≤ wX cU cX)
    (f g : κU → κX → ℝ) (hfg : ∀ cU cX, f cU cX ≤ g cU cX) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * f cU cX
      ≤ ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * g cU cX :=
  Finset.sum_le_sum (fun cU _ ↦ mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun cX _ ↦ mul_le_mul_of_nonneg_left (hfg cU cX) (hwX cU cX)))
    (hwU cU))

/-- Additivity of the two-tier weighted codebook average. -/
lemma bc_weighted_two_tier_add {κU κX : Type*} [Fintype κU] [Fintype κX]
    (wU : κU → ℝ) (wX : κU → κX → ℝ) (f g : κU → κX → ℝ) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (f cU cX + g cU cX)
      = (∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * f cU cX)
        + (∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * g cU cX) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun cX _ ↦ by ring)

/-- Pulling a constant scalar out of the two-tier weighted codebook average. -/
lemma bc_weighted_two_tier_const_mul {κU κX : Type*} [Fintype κU] [Fintype κX]
    (wU : κU → ℝ) (wX : κU → κX → ℝ) (c : ℝ) (f : κU → κX → ℝ) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (c * f cU cX)
      = c * ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * f cU cX := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun cU _ ↦ Finset.sum_congr rfl (fun cX _ ↦ by ring))

/-- Interchanging a finite index sum with the two-tier weighted codebook average. -/
lemma bc_weighted_two_tier_sum_index {κU κX ι : Type*} [Fintype κU] [Fintype κX]
    (s : Finset ι) (wU : κU → ℝ) (wX : κU → κX → ℝ) (h : ι → κU → κX → ℝ) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (∑ i ∈ s, h i cU cX)
      = ∑ i ∈ s, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * h i cU cX := by
  have h1 : ∀ cU : κU, ∑ cX : κX, wX cU cX * (∑ i ∈ s, h i cU cX)
      = ∑ i ∈ s, ∑ cX : κX, wX cU cX * h i cU cX := by
    intro cU
    rw [Finset.sum_congr rfl (fun cX _ ↦ Finset.mul_sum _ _ _), Finset.sum_comm]
  calc ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (∑ i ∈ s, h i cU cX)
      = ∑ cU : κU, ∑ i ∈ s, wU cU * ∑ cX : κX, wX cU cX * h i cU cX := by
        refine Finset.sum_congr rfl (fun cU _ ↦ ?_)
        rw [h1 cU, Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * h i cU cX := Finset.sum_comm

/-- **Receiver-2 aggregation.**  Fold the per-message two-event Bonferroni bound and the two
`L`-evaluated swaps (E0 mass `A`, wrong-cloud exponent `e2`) into the closed form. -/
lemma bc_pair_aggregate₂ {κU κX : Type*} [Fintype κU] [Fintype κX]
    {M₁ M₂ : ℕ} (hM₂ : 0 < M₂)
    (wU : κU → ℝ) (wX : κU → κX → ℝ)
    (hwU : ∀ cU, 0 ≤ wU cU) (hwX : ∀ cU cX, 0 ≤ wX cU cX)
    (P : κU → κX → ℝ)
    (E0 : Fin M₁ × Fin M₂ → κU → κX → ℝ)
    (wc : Fin M₁ × Fin M₂ → Fin M₂ → κU → κX → ℝ)
    (A e2 : ℝ)
    (Minv : ℝ) (hMinv : 0 ≤ Minv) (hMinvM : Minv * ((M₁ * M₂ : ℕ) : ℝ) = 1)
    (hP : ∀ cU cX, P cU cX ≤ Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m cU cX + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, wc m w₂' cU cX))
    (hE0 : ∀ m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX = A)
    (hwc : ∀ (m : Fin M₁ × Fin M₂), ∀ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
        ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * wc m w₂' cU cX ≤ e2) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * P cU cX ≤ A + ((M₂ : ℝ) - 1) * e2 := by
  classical
  refine le_trans (bc_weighted_two_tier_mono wU wX hwU hwX _ _ hP) ?_
  have hdist : ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m cU cX + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, wc m w₂' cU cX))
      = Minv * ∑ m : Fin M₁ × Fin M₂,
          ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
            + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
                ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * wc m w₂' cU cX) := by
    rw [bc_weighted_two_tier_const_mul wU wX Minv]
    congr 1
    rw [bc_weighted_two_tier_sum_index (Finset.univ : Finset (Fin M₁ × Fin M₂)) wU wX
      (fun m cU cX ↦ E0 m cU cX + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
        wc m w₂' cU cX)]
    refine Finset.sum_congr rfl (fun m _ ↦ ?_)
    rw [bc_weighted_two_tier_add wU wX,
      bc_weighted_two_tier_sum_index ((Finset.univ : Finset (Fin M₂)).erase m.2) wU wX
        (fun w₂' cU cX ↦ wc m w₂' cU cX)]
  rw [hdist]
  have hbound : ∀ m : Fin M₁ × Fin M₂,
      ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
        + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
            ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * wc m w₂' cU cX)
      ≤ A + ((M₂ : ℝ) - 1) * e2 := by
    intro m
    rw [hE0 m]
    have hw : ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
          ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * wc m w₂' cU cX ≤ ((M₂ : ℝ) - 1) * e2 := by
      calc ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
              ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * wc m w₂' cU cX
          ≤ ∑ _w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2, e2 :=
            Finset.sum_le_sum (hwc m)
        _ = ((M₂ : ℝ) - 1) * e2 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, Nat.cast_sub hM₂, Nat.cast_one]
    linarith [hw]
  calc Minv * ∑ m : Fin M₁ × Fin M₂,
          ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
            + ∑ w₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m.2,
                ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * wc m w₂' cU cX)
      ≤ Minv * ∑ _m : Fin M₁ × Fin M₂, (A + ((M₂ : ℝ) - 1) * e2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ ↦ hbound m)) hMinv
    _ = A + ((M₂ : ℝ) - 1) * e2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hMinvM, one_mul]

/-- **Receiver-1 aggregation.**  Fold the per-message three-event Bonferroni bound and the
three `L`-evaluated swaps (E0 mass `A`, wrong-satellite exponent `eb`, wrong-cloud exponent
`ec`) into the closed form. -/
lemma bc_pair_aggregate₁ {κU κX : Type*} [Fintype κU] [Fintype κX]
    {M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (wU : κU → ℝ) (wX : κU → κX → ℝ)
    (hwU : ∀ cU, 0 ≤ wU cU) (hwX : ∀ cU cX, 0 ≤ wX cU cX)
    (P : κU → κX → ℝ)
    (E0 : Fin M₁ × Fin M₂ → κU → κX → ℝ)
    (Eb : Fin M₁ × Fin M₂ → Fin M₁ → κU → κX → ℝ)
    (Ec : Fin M₁ × Fin M₂ → Fin M₂ × Fin M₁ → κU → κX → ℝ)
    (A eb ec : ℝ)
    (Minv : ℝ) (hMinv : 0 ≤ Minv) (hMinvM : Minv * ((M₁ * M₂ : ℕ) : ℝ) = 1)
    (hP : ∀ cU cX, P cU cX ≤ Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m cU cX
          + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1, Eb m m₁' cU cX
          + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                    (Finset.univ : Finset (Fin M₁)), Ec m p cU cX))
    (hE0 : ∀ m, ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX = A)
    (hEb : ∀ (m : Fin M₁ × Fin M₂), ∀ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
        ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Eb m m₁' cU cX ≤ eb)
    (hEc : ∀ (m : Fin M₁ × Fin M₂), ∀ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
              (Finset.univ : Finset (Fin M₁)),
        ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ec m p cU cX ≤ ec) :
    ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * P cU cX
      ≤ A + ((M₁ : ℝ) - 1) * eb + ((M₂ : ℝ) - 1) * (M₁ : ℝ) * ec := by
  classical
  refine le_trans (bc_weighted_two_tier_mono wU wX hwU hwX _ _ hP) ?_
  have hdist : ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * (Minv * ∑ m : Fin M₁ × Fin M₂,
        (E0 m cU cX
          + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1, Eb m m₁' cU cX
          + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                    (Finset.univ : Finset (Fin M₁)), Ec m p cU cX))
      = Minv * ∑ m : Fin M₁ × Fin M₂,
          ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
                ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Eb m m₁' cU cX
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                      (Finset.univ : Finset (Fin M₁)),
                ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ec m p cU cX) := by
    rw [bc_weighted_two_tier_const_mul wU wX Minv]
    congr 1
    rw [bc_weighted_two_tier_sum_index (Finset.univ : Finset (Fin M₁ × Fin M₂)) wU wX
      (fun m cU cX ↦ E0 m cU cX
        + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1, Eb m m₁' cU cX
        + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                  (Finset.univ : Finset (Fin M₁)), Ec m p cU cX)]
    refine Finset.sum_congr rfl (fun m _ ↦ ?_)
    rw [bc_weighted_two_tier_add wU wX, bc_weighted_two_tier_add wU wX,
      bc_weighted_two_tier_sum_index ((Finset.univ : Finset (Fin M₁)).erase m.1) wU wX
        (fun m₁' cU cX ↦ Eb m m₁' cU cX),
      bc_weighted_two_tier_sum_index (((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
        (Finset.univ : Finset (Fin M₁))) wU wX (fun p cU cX ↦ Ec m p cU cX)]
  rw [hdist]
  have hbound : ∀ m : Fin M₁ × Fin M₂,
      ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
        + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
            ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Eb m m₁' cU cX
        + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                  (Finset.univ : Finset (Fin M₁)),
            ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ec m p cU cX)
      ≤ A + ((M₁ : ℝ) - 1) * eb + ((M₂ : ℝ) - 1) * (M₁ : ℝ) * ec := by
    intro m
    rw [hE0 m]
    have hb : ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
          ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Eb m m₁' cU cX ≤ ((M₁ : ℝ) - 1) * eb := by
      calc ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
              ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Eb m m₁' cU cX
          ≤ ∑ _m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1, eb :=
            Finset.sum_le_sum (hEb m)
        _ = ((M₁ : ℝ) - 1) * eb := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin, Nat.cast_sub hM₁, Nat.cast_one]
    have hc : ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                (Finset.univ : Finset (Fin M₁)),
          ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ec m p cU cX
        ≤ ((M₂ : ℝ) - 1) * (M₁ : ℝ) * ec := by
      calc ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                (Finset.univ : Finset (Fin M₁)),
              ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ec m p cU cX
          ≤ ∑ _p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                (Finset.univ : Finset (Fin M₁)), ec :=
            Finset.sum_le_sum (hEc m)
        _ = ((M₂ : ℝ) - 1) * (M₁ : ℝ) * ec := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product,
              Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
              Finset.card_univ, Fintype.card_fin, Nat.cast_mul, Nat.cast_sub hM₂, Nat.cast_one]
    linarith [hb, hc]
  calc Minv * ∑ m : Fin M₁ × Fin M₂,
          ((∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * E0 m cU cX)
            + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m.1,
                ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Eb m m₁' cU cX
            + ∑ p ∈ ((Finset.univ : Finset (Fin M₂)).erase m.2) ×ˢ
                      (Finset.univ : Finset (Fin M₁)),
                ∑ cU : κU, wU cU * ∑ cX : κX, wX cU cX * Ec m p cU cX)
      ≤ Minv * ∑ _m : Fin M₁ × Fin M₂,
          (A + ((M₁ : ℝ) - 1) * eb + ((M₂ : ℝ) - 1) * (M₁ : ℝ) * ec) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m _ ↦ hbound m)) hMinv
    _ = A + ((M₁ : ℝ) - 1) * eb + ((M₂ : ℝ) - 1) * (M₁ : ℝ) * ec := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hMinvM, one_mul]

/-- **Receiver-2 two-codebook average bound.**  The random-codebook expectation of the
receiver-2 average error is at most the (vanishing) E0 mass plus the wrong-cloud exponent.
-/
theorem bc_random_codebook_average₂_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (hε : 0 < ε) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal
      ≤ ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
          { q | q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
        + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₂ pU K W) + 3 * ε)) := by
  classical
  have hexp₂ : Real.exp (-(n : ℝ) * (bcInfo₂ pU K W - 3 * ε))
      = Real.exp ((n : ℝ) * (-(bcInfo₂ pU K W) + 3 * ε)) := by
    rw [show -(n : ℝ) * (bcInfo₂ pU K W - 3 * ε)
      = (n : ℝ) * (-(bcInfo₂ pU K W) + 3 * ε) from by ring]
  exact bc_pair_aggregate₂ hM₂
    (fun cU ↦ (bcCloudCodebookMeasure pU M₂ n).real {cU})
    (fun cU cX ↦ (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX})
    (fun _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_nonneg)
    (fun cU cX ↦ ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal)
    (fun m cU cX ↦ (Measure.pi (fun i ↦ W (cX m i))).real
        { y : Fin n → β₁ × β₂ | (cU m.2, fun i ↦ (y i).2)
            ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε })
    (fun m w₂' cU cX ↦ (Measure.pi (fun i ↦ W (cX m i))).real
        { y : Fin n → β₁ × β₂ | (cU w₂', fun i ↦ (y i).2)
            ∈ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε })
    _ _ _ (by positivity)
    (inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.mul_pos hM₁ hM₂).ne'))
    (fun cU cX ↦ bc_averageErrorProb₂_toReal_le pU K W hM₁ hM₂ cU cX)
    (fun m ↦ bc_random_codebook_E0₂_swap pU K W hpU hK hW m)
    (fun m w₂' hmem ↦ le_of_le_of_eq (bc_random_codebook_wrongcloud_swap pU K W hpU hK hW hε m w₂'
      (Finset.mem_erase.mp hmem).1) hexp₂)

/-- **Receiver-1 two-codebook average bound.**  The random-codebook expectation of the
receiver-1 average error is at most the (vanishing) E0 mass plus the wrong-satellite (`E_b`)
and wrong-cloud (`E_c`) exponents.
-/
theorem bc_random_codebook_average₁_le
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (hε : 0 < ε) :
    ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      ≤ ((bcAmbientMeasure pU K W).map
            (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
          { q | q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
        + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε))
        + ((M₂ : ℝ) - 1) * (M₁ : ℝ) *
            Real.exp ((n : ℝ) * (-(bcInfoJoint pU K W) + 3 * ε)) := by
  classical
  have hexpb : Real.exp (-(n : ℝ) * (bcInfo₁ pU K W - 4 * ε))
      = Real.exp ((n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε)) := by
    rw [show -(n : ℝ) * (bcInfo₁ pU K W - 4 * ε)
      = (n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε) from by ring]
  have hexpc : Real.exp (-(n : ℝ) * (bcInfoJoint pU K W - 3 * ε))
      = Real.exp ((n : ℝ) * (-(bcInfoJoint pU K W) + 3 * ε)) := by
    rw [show -(n : ℝ) * (bcInfoJoint pU K W - 3 * ε)
      = (n : ℝ) * (-(bcInfoJoint pU K W) + 3 * ε) from by ring]
  exact bc_pair_aggregate₁ hM₁ hM₂
    (fun cU ↦ (bcCloudCodebookMeasure pU M₂ n).real {cU})
    (fun cU cX ↦ (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX})
    (fun _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_nonneg)
    (fun cU cX ↦ ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal)
    (fun m cU cX ↦ (Measure.pi (fun i ↦ W (cX m i))).real
        { y : Fin n → β₁ × β₂ | (cU m.2, cX m, fun i ↦ (y i).1)
            ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε })
    (fun m m₁' cU cX ↦ (Measure.pi (fun i ↦ W (cX m i))).real
        { y : Fin n → β₁ × β₂ | (cU m.2, cX (m₁', m.2), fun i ↦ (y i).1)
            ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε })
    (fun m p cU cX ↦ (Measure.pi (fun i ↦ W (cX m i))).real
        { y : Fin n → β₁ × β₂ | (cU p.1, cX (p.2, p.1), fun i ↦ (y i).1)
            ∈ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε })
    _ _ _ _ (by positivity)
    (inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.mul_pos hM₁ hM₂).ne'))
    (fun cU cX ↦ bc_averageErrorProb₁_toReal_le pU K W hM₁ hM₂ cU cX)
    (fun m ↦ bc_random_codebook_E0₁_swap pU K W hpU hK hW m)
    (fun m m₁' hmem ↦ le_of_le_of_eq (bc_random_codebook_Eb_swap pU K W hpU hK hW m m₁'
      (Finset.mem_erase.mp hmem).1) hexpb)
    (fun m p hmem ↦ le_of_le_of_eq (bc_random_codebook_Ec_swap pU K W hpU hK hW hε m p
      (Finset.mem_erase.mp (Finset.mem_product.mp hmem).1).1) hexpc)

/-! #### C.4 — random → deterministic (two-tier pigeonhole) -/

/-- Abstract two-tier pigeonhole.  Nonnegative outer weights `wU` summing to `1`, and for every
outer index a nonnegative inner-weight family `wX cU` summing to `1`, whose weighted double
average of `val` is `≤ B`, force some index pair with `val cU cX ≤ B`.  (If every pair had
`val > B` the weighted average would strictly exceed `B`.) -/
lemma bc_two_tier_pigeonhole {κU κX : Type*} [Fintype κU] [Fintype κX]
    (wU : κU → ℝ) (wX : κU → κX → ℝ) (val : κU → κX → ℝ)
    (hwU_nn : ∀ cU, 0 ≤ wU cU) (hwX_nn : ∀ cU cX, 0 ≤ wX cU cX)
    (hwU_sum : ∑ cU, wU cU = 1) (hwX_sum : ∀ cU, ∑ cX, wX cU cX = 1)
    (B : ℝ)
    (h_avg : ∑ cU, wU cU * ∑ cX, wX cU cX * val cU cX ≤ B) :
    ∃ (cU : κU) (cX : κX), val cU cX ≤ B := by
  classical
  by_contra h_none
  simp only [not_exists, not_le] at h_none
  -- For every outer index the inner weighted average strictly exceeds `B`.
  have hinner_gt : ∀ cU, B < ∑ cX, wX cU cX * val cU cX := by
    intro cU
    obtain ⟨cX₀, hcX₀⟩ : ∃ cX, 0 < wX cU cX := by
      by_contra h
      push_neg at h
      have hz : ∑ cX, wX cU cX = 0 :=
        Finset.sum_eq_zero (fun cX _ ↦ le_antisymm (h cX) (hwX_nn cU cX))
      rw [hwX_sum cU] at hz; exact one_ne_zero hz
    calc B = B * ∑ cX, wX cU cX := by rw [hwX_sum cU, mul_one]
      _ = ∑ cX, wX cU cX * B := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ < ∑ cX, wX cU cX * val cU cX :=
          Finset.sum_lt_sum
            (fun cX _ ↦ mul_le_mul_of_nonneg_left (h_none cU cX).le (hwX_nn cU cX))
            ⟨cX₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h_none cU cX₀) hcX₀⟩
  -- Some outer weight is positive.
  obtain ⟨cU₀, hcU₀⟩ : ∃ cU, 0 < wU cU := by
    by_contra h
    push_neg at h
    have hz : ∑ cU, wU cU = 0 := Finset.sum_eq_zero (fun cU _ ↦ le_antisymm (h cU) (hwU_nn cU))
    rw [hwU_sum] at hz; exact one_ne_zero hz
  have h_contra : B < ∑ cU, wU cU * ∑ cX, wX cU cX * val cU cX := by
    calc B = B * ∑ cU, wU cU := by rw [hwU_sum, mul_one]
      _ = ∑ cU, wU cU * B := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ < ∑ cU, wU cU * ∑ cX, wX cU cX * val cU cX :=
          Finset.sum_lt_sum
            (fun cU _ ↦ mul_le_mul_of_nonneg_left (hinner_gt cU).le (hwU_nn cU))
            ⟨cU₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hinner_gt cU₀) hcU₀⟩
  exact absurd h_avg (not_le.mpr h_contra)

/-- **Two-tier pigeonhole.**  If the random-codebook expectation of the summed per-receiver
errors is `≤ B`, some deterministic cloud/satellite codebook pair achieves the summed error
`≤ B`.  Bounding the *sum* lets a single codebook meet both receivers' targets simultaneously. -/
theorem bc_exists_codebook_le_avg
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ} (B : ℝ)
    (h_avg :
      ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
                 + ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal) ≤ B) :
    ∃ (cU : BCCloudCodebook M₂ n U) (cX : BCSatelliteCodebook M₁ M₂ n α),
      ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
        + ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal ≤ B := by
  classical
  haveI : MeasurableSingletonClass (BCCloudCodebook M₂ n U) := Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (BCSatelliteCodebook M₁ M₂ n α) :=
    Pi.instMeasurableSingletonClass
  haveI : IsProbabilityMeasure (bcCloudCodebookMeasure pU M₂ n) := by
    unfold bcCloudCodebookMeasure; infer_instance
  -- The inner (conditional-satellite) law sums to `1` for every cloud codebook.
  have hwX_sum : ∀ cU : BCCloudCodebook M₂ n U,
      ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
        (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX} = 1 := by
    intro cU
    haveI : IsProbabilityMeasure (bcSatelliteCodebookMeasure K M₁ M₂ n cU) := by
      unfold bcSatelliteCodebookMeasure; infer_instance
    have h_real_univ : (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real
        ((Finset.univ : Finset (BCSatelliteCodebook M₁ M₂ n α)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
    rw [sum_measureReal_singleton (μ := bcSatelliteCodebookMeasure K M₁ M₂ n cU)
      (Finset.univ : Finset (BCSatelliteCodebook M₁ M₂ n α)), h_real_univ]
  -- The outer (cloud) law sums to `1`.
  have hwU_sum : ∑ cU : BCCloudCodebook M₂ n U,
      (bcCloudCodebookMeasure pU M₂ n).real {cU} = 1 := by
    have h_real_univ : (bcCloudCodebookMeasure pU M₂ n).real
        ((Finset.univ : Finset (BCCloudCodebook M₂ n U)) : Set _) = 1 := by
      rw [Finset.coe_univ, measureReal_def, measure_univ]; rfl
    rw [sum_measureReal_singleton (μ := bcCloudCodebookMeasure pU M₂ n)
      (Finset.univ : Finset (BCCloudCodebook M₂ n U)), h_real_univ]
  exact bc_two_tier_pigeonhole
    (fun cU ↦ (bcCloudCodebookMeasure pU M₂ n).real {cU})
    (fun cU cX ↦ (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX})
    (fun cU cX ↦ ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₁ W).toReal
      + ((bcCodebookToCode pU K W hM₁ hM₂ ε cU cX).averageErrorProb₂ W).toReal)
    (fun _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_nonneg) hwU_sum hwX_sum B h_avg

/-! #### C.5 — degradedness + rate slack -/

/-- Kernel identity: composing `κ` with a conditioner-only append `prodMkRight A' Q` equals
the plain product kernel `κ ×ₖ Q`. -/
private lemma kernel_compProd_prodMkRight_eq_prod
    {Z' A' B' : Type*} [MeasurableSpace Z'] [MeasurableSpace A'] [MeasurableSpace B']
    (κ : Kernel Z' A') [IsSFiniteKernel κ] (Q : Kernel Z' B') [IsSFiniteKernel Q] :
    κ ⊗ₖ Kernel.prodMkRight A' Q = κ ×ₖ Q := by
  rw [Kernel.ext_fun_iff]
  intro z f hf
  rw [Kernel.lintegral_compProd _ _ _ hf, Kernel.lintegral_prod _ _ _ hf]
  rfl

/-- If the target `Bs` is generated from the conditioner `Zc` by a Markov kernel `Q` (an
append that ignores `As`), then `As → Zc → Bs` is a Markov chain.  This is the stochastic
analogue of `isMarkovChain_comp_conditioner_right`, whose right endpoint is only a
*deterministic* function of the conditioner. -/
private lemma isMarkovChain_of_append
    {Ω' A' Z' B' : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace A'] [MeasurableSpace Z'] [MeasurableSpace B']
    [StandardBorelSpace A'] [Nonempty A']
    [StandardBorelSpace B'] [Nonempty B']
    (μ : Measure Ω') [IsProbabilityMeasure μ]
    (As : Ω' → A') (Zc : Ω' → Z') (Bs : Ω' → B')
    (hAs : Measurable As) (hZc : Measurable Zc) (hBs : Measurable Bs)
    (Q : Kernel Z' B') [IsMarkovKernel Q]
    (h_app : μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω))
           = (μ.map (fun ω ↦ (Zc ω, As ω))) ⊗ₘ (Kernel.prodMkRight A' Q)) :
    IsMarkovChain μ As Zc Bs := by
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc.aemeasurable
  have hZcAs : Measurable (fun ω ↦ (Zc ω, As ω)) := hZc.prodMk hAs
  have hg : Measurable (fun p : (Z' × A') × B' ↦ (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hmarg : μ.map (fun ω ↦ (Zc ω, Bs ω)) = (μ.map Zc) ⊗ₘ Q := by
    have e1 : μ.map (fun ω ↦ (Zc ω, Bs ω))
        = (μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω))).map (fun p : (Z' × A') × B' ↦ (p.1.1, p.2)) := by
      rw [Measure.map_map hg (hZcAs.prodMk hBs)]; rfl
    rw [e1, h_app]
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    have hF : Measurable (fun z ↦ ∫⁻ b, f (z, b) ∂(Q z)) :=
      hf.lintegral_kernel_prod_right'
    have hF2 : Measurable (fun a : (Z' × A') × B' ↦ f (a.1.1, a.2)) := hf.comp hg
    rw [lintegral_map hf hg, Measure.lintegral_compProd hF2,
        Measure.lintegral_compProd hf]
    have hfst : μ.map Zc = (μ.map (fun ω ↦ (Zc ω, As ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hZcAs]; rfl
    rw [hfst, lintegral_map hF measurable_fst]
    rfl
  have hcd_B : condDistrib Bs Zc μ =ᵐ[μ.map Zc] Q :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hBs.aemeasurable hmarg
  unfold IsMarkovChain
  have hLHS : μ.map (fun ω ↦ (Zc ω, As ω, Bs ω))
      = (μ.map (fun ω ↦ ((Zc ω, As ω), Bs ω))).map MeasurableEquiv.prodAssoc := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable (hZcAs.prodMk hBs)]; rfl
  rw [hLHS, h_app, ← compProd_map_condDistrib hAs.aemeasurable, Measure.compProd_assoc']
  refine Measure.compProd_congr ?_
  rw [kernel_compProd_prodMkRight_eq_prod]
  filter_upwards [hcd_B] with z hz
  rw [Kernel.prod_apply, Kernel.prod_apply, hz]

/-- Under physical degradedness `W a = ((W a).map fst) >>= (append `Q`)`, the degraded output
`Y₂` is appended to the `(Y₁, (U, X))` joint by the degrading kernel `Q` acting on `Y₁` alone. -/
private lemma bcDegraded_append
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (Q : Kernel β₁ β₂) [IsMarkovKernel Q]
    (hQeq : ∀ a : α, W a
        = ((W a).map Prod.fst).bind (fun y₁ ↦ (Q y₁).map (fun y₂ ↦ (y₁, y₂)))) :
    (bcJointDistribution pU K W).map
        (fun q : U × α × β₁ × β₂ ↦ ((q.2.2.1, (q.1, q.2.1)), q.2.2.2))
      = ((bcJointDistribution pU K W).map
          (fun q : U × α × β₁ × β₂ ↦ (q.2.2.1, (q.1, q.2.1))))
          ⊗ₘ (Kernel.prodMkRight (U × α) Q) := by
  have hψL : Measurable (fun q : U × α × β₁ × β₂ ↦ ((q.2.2.1, (q.1, q.2.1)), q.2.2.2)) := by
    fun_prop
  have hψB : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.2.2.1, (q.1, q.2.1))) := by fun_prop
  have hPL : Measurable (fun p : (U × α) × (β₁ × β₂) ↦ ((p.2.1, p.1), p.2.2)) := by fun_prop
  have hPB : Measurable (fun p : (U × α) × (β₁ × β₂) ↦ (p.2.1, p.1)) := by fun_prop
  have hapQ : Measurable (fun y₁ : β₁ ↦ (Q y₁).map (fun y₂ ↦ (y₁, y₂))) := by
    have heq : (fun y₁ : β₁ ↦ (Q y₁).map (fun y₂ ↦ (y₁, y₂)))
        = fun y₁ ↦ (Kernel.deterministic (id : β₁ → β₁) measurable_id ×ₖ Q) y₁ := by
      funext y₁
      rw [Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod]
      rfl
    rw [heq]
    exact (Kernel.deterministic (id : β₁ → β₁) measurable_id ×ₖ Q).measurable
  have hbind : ∀ (x : α) (g : β₁ × β₂ → ℝ≥0∞), Measurable g →
      ∫⁻ yy, g yy ∂(W x)
        = ∫⁻ y₁, ∫⁻ y₂, g (y₁, y₂) ∂(Q y₁) ∂((W x).map Prod.fst) := by
    intro x g hg
    have hmap : ∀ y₁ : β₁, ∫⁻ yy, g yy ∂((Q y₁).map (fun y₂ ↦ (y₁, y₂)))
        = ∫⁻ y₂, g (y₁, y₂) ∂(Q y₁) :=
      fun y₁ ↦ lintegral_map hg measurable_prodMk_left
    conv_lhs => rw [hQeq x]
    rw [Measure.lintegral_bind hapQ.aemeasurable hg.aemeasurable]
    simp_rw [hmap]
  rw [bcJointDistribution, Measure.map_map hψL MeasurableEquiv.prodAssoc.measurable,
      Measure.map_map hψB MeasurableEquiv.prodAssoc.measurable]
  have hcompL :
      (fun q : U × α × β₁ × β₂ ↦ ((q.2.2.1, (q.1, q.2.1)), q.2.2.2))
          ∘ ⇑(MeasurableEquiv.prodAssoc (α := U) (β := α) (γ := β₁ × β₂))
        = (fun p : (U × α) × (β₁ × β₂) ↦ ((p.2.1, p.1), p.2.2)) := rfl
  have hcompB :
      (fun q : U × α × β₁ × β₂ ↦ (q.2.2.1, (q.1, q.2.1)))
          ∘ ⇑(MeasurableEquiv.prodAssoc (α := U) (β := α) (γ := β₁ × β₂))
        = (fun p : (U × α) × (β₁ × β₂) ↦ (p.2.1, p.1)) := rfl
  rw [hcompL, hcompB]
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hfPL : Measurable (fun p : (U × α) × (β₁ × β₂) ↦ f ((p.2.1, p.1), p.2.2)) := hf.comp hPL
  have hLHS :
      ∫⁻ z, f z ∂(((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map
          (fun p : (U × α) × (β₁ × β₂) ↦ ((p.2.1, p.1), p.2.2)))
        = ∫⁻ ux : U × α, ∫⁻ y₁ : β₁, ∫⁻ y₂ : β₂, f ((y₁, ux), y₂)
            ∂(Q y₁) ∂((W ux.2).map Prod.fst) ∂(pU ⊗ₘ K) := by
    rw [lintegral_map hf hPL, Measure.lintegral_compProd hfPL]
    refine lintegral_congr fun ux ↦ ?_
    rw [Kernel.comap_apply]
    exact hbind ux.2 (fun yy ↦ f ((yy.1, ux), yy.2)) (by fun_prop)
  have hG : Measurable (fun w : β₁ × (U × α) ↦ ∫⁻ y₂ : β₂, f (w, y₂) ∂(Q w.1)) :=
    hf.lintegral_kernel_prod_right' (κ := Q.comap Prod.fst measurable_fst)
  have hRHS :
      ∫⁻ z, f z ∂((((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map
          (fun p : (U × α) × (β₁ × β₂) ↦ (p.2.1, p.1))) ⊗ₘ (Kernel.prodMkRight (U × α) Q))
        = ∫⁻ ux : U × α, ∫⁻ y₁ : β₁, ∫⁻ y₂ : β₂, f ((y₁, ux), y₂)
            ∂(Q y₁) ∂((W ux.2).map Prod.fst) ∂(pU ⊗ₘ K) := by
    rw [Measure.lintegral_compProd hf]
    simp only [Kernel.prodMkRight_apply]
    have hFPB : Measurable (fun p : (U × α) × (β₁ × β₂) ↦
        ∫⁻ y₂ : β₂, f ((p.2.1, p.1), y₂) ∂(Q (p.2.1, p.1).1)) := hG.comp hPB
    rw [lintegral_map hG hPB, Measure.lintegral_compProd hFPB]
    refine lintegral_congr fun ux ↦ ?_
    rw [Kernel.comap_apply]
    have hG'ux : Measurable (fun y₁ : β₁ ↦ ∫⁻ y₂ : β₂, f ((y₁, ux), y₂) ∂(Q y₁)) :=
      (hf.comp ((measurable_fst.prodMk measurable_const).prodMk
        measurable_snd)).lintegral_kernel_prod_right' (κ := Q)
    rw [lintegral_map hG'ux measurable_fst]
  rw [hLHS, hRHS]

/-- Base data-processing Markov chain `(U, X) → Y₁ → Y₂` for the degraded broadcast joint
law: under physical degradedness the degraded output `Y₂` is a stochastic function of `Y₁`
alone (via the degrading kernel `Q`), hence conditionally independent of the cloud/input
pair `(U, X)` given `Y₁`.
@audit:ok -/
lemma bcMarkovChain_UX_Y₁_Y₂
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) :
    IsMarkovChain (bcJointDistribution pU K W)
      (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1))
      (fun q : U × α × β₁ × β₂ ↦ q.2.2.1)
      (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) := by
  obtain ⟨Q, hQm, hQeq⟩ := hdeg
  haveI : IsMarkovKernel Q := hQm
  have hAs : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hZc : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  have hBs : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  exact isMarkovChain_of_append (bcJointDistribution pU K W) (fun q ↦ (q.1, q.2.1))
    (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2) hAs hZc hBs Q (bcDegraded_append pU K W Q hQeq)

/-- **Degradedness superadditivity.**  Under physical degradedness `X → Y₁ → Y₂`, the joint
information `I((U, X); Y₁)` dominates the sum of the two per-receiver informations
`I(X; Y₁ ∣ U) + I(U; Y₂)`.  Chain rule `I((U, X); Y₁) = I(U; Y₁) + I(X; Y₁ ∣ U)` plus data
processing `I(U; Y₁) ≥ I(U; Y₂)`.  This makes the receiver-1 joint-decoding rate sum
`R₁ + R₂ < I((U, X); Y₁)` follow automatically from the two corner constraints.
@audit:ok -/
theorem bc_degraded_infoJoint_ge
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) :
    bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W := by
  classical
  set μ := bcJointDistribution pU K W with hμ
  -- Coordinate selectors and their measurability.
  have hU : Measurable (Prod.fst : U × α × β₁ × β₂ → U) := measurable_fst
  have hY₁ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_snd
  have hY₂ : Measurable (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    (measurable_snd.comp measurable_snd).comp measurable_snd
  have hUX : Measurable (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  -- Markov chain `(U, X) → Y₁ → Y₂` from degradedness.
  have hbase := bcMarkovChain_UX_Y₁_Y₂ pU K W hdeg
  -- Post-process the source `(U, X) ↦ U`, giving `U → Y₁ → Y₂`.
  have hUY :
      IsMarkovChain μ (Prod.fst : U × α × β₁ × β₂ → U)
        (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) :=
    isMarkovChain_map_left μ (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1))
      (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2) hUX hY₁ hY₂ (f := Prod.fst) measurable_fst hbase
  -- Swap endpoints: `Y₂ → Y₁ → U`.
  have hswap :
      IsMarkovChain μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.2)
        (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) (Prod.fst : U × α × β₁ × β₂ → U) :=
    isMarkovChain_swap μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1)
      (fun q ↦ q.2.2.2) hU hY₁ hY₂ hUY
  -- Data processing: `I(Y₂; U) ≤ I(Y₁; U)`.
  have hdpi :
      mutualInfo μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.2) (Prod.fst : U × α × β₁ × β₂ → U)
        ≤ mutualInfo μ (fun q : U × α × β₁ × β₂ ↦ q.2.2.1) (Prod.fst : U × α × β₁ × β₂ → U) :=
    mutualInfo_le_of_markov μ (fun q ↦ q.2.2.2) (fun q ↦ q.2.2.1)
      (Prod.fst : U × α × β₁ × β₂ → U) hY₂ hY₁ hU hswap
  -- Symmetrize to `I(U; Y₂) ≤ I(U; Y₁)`.
  have hmi :
      mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.2)
        ≤ mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1) := by
    rw [mutualInfo_comm μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.2) hU hY₂,
        mutualInfo_comm μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1) hU hY₁]
    exact hdpi
  -- Push through `.toReal` (finiteness of the informations on finite alphabets).
  have hne1 : mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1) ≠ ⊤ :=
    mutualInfo_ne_top μ Prod.fst (fun q ↦ q.2.2.1) hU hY₁
  have htoReal :
      (mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.2)).toReal
        ≤ (mutualInfo μ (Prod.fst : U × α × β₁ × β₂ → U) (fun q ↦ q.2.2.1)).toReal :=
    ENNReal.toReal_mono hne1 hmi
  -- Entropy-form bridge: `I(U; Y₂) = H(U) + H(Y₂) − H(U, Y₂)`, similarly for `Y₁`.
  have hb2 := mutualInfo_toReal_eq_entropy_form μ (Prod.fst : U × α × β₁ × β₂ → U)
    (fun q ↦ q.2.2.2) hU hY₂
  have hb1 := mutualInfo_toReal_eq_entropy_form μ (Prod.fst : U × α × β₁ × β₂ → U)
    (fun q ↦ q.2.2.1) hU hY₁
  rw [hb2, hb1] at htoReal
  -- Reduce the three-information inequality to the entropy inequality.
  simp only [bcInfo₁, bcInfo₂, bcInfoJoint, ← hμ]
  linarith [htoReal]

/-- **Receiver-1 wrong-cloud rate-slack vanishing (`E_c`).**  With the joint AEP gap
`I((U, X); Y₁) − (R₁ + R₂) − 3ε > 0` and non-negative rate `0 ≤ R₁`, the wrong-cloud
prefactor `(⌈exp(nR₂)⌉−1)·⌈exp(nR₁)⌉` times `exp(n(−I((U, X); Y₁) + 3ε))` falls below any
tolerance for large `n`.  The `0 ≤ R₁` hypothesis is essential: for `R₁ < 0` the ceil
`⌈exp(nR₁)⌉` floors at `1` instead of shrinking like `exp(nR₁)`, so the negative slack the
gap allocates to the `R₁` factor is not delivered and the prefactor diverges.  The caller
`bc_achievability` supplies `0 < R₁`, so this precondition is met.
-/
theorem bc_Ec_lt_of_rate {Ijoint R₁ R₂ ε ε' : ℝ}
    (hR₁ : 0 ≤ R₁) (hgap : 0 < Ijoint - (R₁ + R₂) - 3 * ε) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N,
      ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
        (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) *
        Real.exp ((n : ℝ) * (-Ijoint + 3 * ε)) < ε' := by
  obtain ⟨N, hN⟩ := exp_neg_mul_lt_of_rate hgap (half_pos hε')
  refine ⟨N, fun n hn ↦ ?_⟩
  -- Receiver-2 codebook factor: `⌈exp(nR₂)⌉ − 1 ≤ exp(nR₂)`.
  have he2 : (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1 ≤ Real.exp ((n : ℝ) * R₂) := by
    have := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R₂)).le; linarith
  have hnn2 : 0 ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) := by
      exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos _)
    linarith
  -- Receiver-1 codebook factor: `⌈exp(nR₁)⌉ ≤ 2·exp(nR₁)`, using `exp(nR₁) ≥ 1` from `0 ≤ R₁`.
  have hnR₁_nonneg : 0 ≤ (n : ℝ) * R₁ := mul_nonneg (Nat.cast_nonneg n) hR₁
  have hexp1_ge : (1 : ℝ) ≤ Real.exp ((n : ℝ) * R₁) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hnR₁_nonneg
  have he1 : (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) ≤ 2 * Real.exp ((n : ℝ) * R₁) := by
    have hlt := Nat.ceil_lt_add_one (Real.exp_pos ((n : ℝ) * R₁)).le
    linarith
  -- Collapse the three exponentials into `2·exp(−n·gap)`.
  have hrw : Real.exp ((n : ℝ) * R₂) * (2 * Real.exp ((n : ℝ) * R₁)) *
        Real.exp ((n : ℝ) * (-Ijoint + 3 * ε))
      = 2 * Real.exp (-(n : ℝ) * (Ijoint - (R₁ + R₂) - 3 * ε)) := by
    have e1 : Real.exp ((n : ℝ) * R₂) * Real.exp ((n : ℝ) * R₁) *
          Real.exp ((n : ℝ) * (-Ijoint + 3 * ε))
        = Real.exp (-(n : ℝ) * (Ijoint - (R₁ + R₂) - 3 * ε)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp ((n : ℝ) * R₂) * (2 * Real.exp ((n : ℝ) * R₁)) *
            Real.exp ((n : ℝ) * (-Ijoint + 3 * ε))
        = 2 * (Real.exp ((n : ℝ) * R₂) * Real.exp ((n : ℝ) * R₁) *
            Real.exp ((n : ℝ) * (-Ijoint + 3 * ε))) := by ring
      _ = 2 * Real.exp (-(n : ℝ) * (Ijoint - (R₁ + R₂) - 3 * ε)) := by rw [e1]
  calc ((Nat.ceil (Real.exp ((n : ℝ) * R₂)) : ℝ) - 1) *
          (Nat.ceil (Real.exp ((n : ℝ) * R₁)) : ℝ) *
          Real.exp ((n : ℝ) * (-Ijoint + 3 * ε))
      ≤ Real.exp ((n : ℝ) * R₂) * (2 * Real.exp ((n : ℝ) * R₁)) *
          Real.exp ((n : ℝ) * (-Ijoint + 3 * ε)) := by gcongr
    _ = 2 * Real.exp (-(n : ℝ) * (Ijoint - (R₁ + R₂) - 3 * ε)) := hrw
    _ < ε' := by linarith [hN n hn]

/-! ### Headline: degraded broadcast achievability -/

/-- **Broadcast channel achievability (degraded, superposition inner bound).**
Cover–Thomas *Elements of Information Theory* Thm 15.6.2 achievability.  Over a physically
degraded broadcast channel `W` with cloud law `pU` and conditional input kernel `K`, any
rate pair strictly inside the auxiliary-variable region

* `R₁ < I(X; Y₁ ∣ U)` (`= bcInfo₁`, the strong receiver), and
* `R₂ < I(U; Y₂)` (`= bcInfo₂`, the degraded receiver)

is achievable: for all large enough block lengths `n` there is a `BroadcastCode` whose two
per-receiver average error probabilities are both below any prescribed `ε' > 0`.  The proof
is the two-tier superposition random-coding argument; degradedness `X → Y₁ → Y₂` is a
structural precondition ensuring the receiver-1 joint-decoding rate sum is met automatically.
@audit:ok -/
theorem bc_achievability
    (pU : Measure U) [IsProbabilityMeasure pU]
    (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hdeg : IsBCDegraded W)
    {R₁ R₂ : ℝ} (_hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
        (_hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
        (c : BroadcastCode M₁ M₂ n α β₁ β₂),
        (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε' := by
  classical
  -- Degradedness supplies the joint-decoding rate-sum constraint `R₁ + R₂ < I((U, X); Y₁)`.
  have hdeg_sum : bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W :=
    bc_degraded_infoJoint_ge pU K W hdeg
  have hRsum : R₁ + R₂ < bcInfoJoint pU K W := by linarith
  -- Rate slack `ε = gap/8` (the receiver-1 wrong-satellite window is `4ε`, hence `/8`, not `/6`).
  set gap : ℝ := min (min (bcInfo₁ pU K W - R₁) (bcInfo₂ pU K W - R₂))
      (bcInfoJoint pU K W - (R₁ + R₂)) with hgap_def
  have hgapA : gap ≤ bcInfo₁ pU K W - R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hgapB : gap ≤ bcInfo₂ pU K W - R₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hgapC : gap ≤ bcInfoJoint pU K W - (R₁ + R₂) := min_le_right _ _
  have hgap_pos : 0 < gap := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  set ε : ℝ := gap / 8 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have hgapb : 0 < bcInfo₁ pU K W - R₁ - 4 * ε := by rw [hε_def]; linarith
  have hgap₂ : 0 < bcInfo₂ pU K W - R₂ - 3 * ε := by rw [hε_def]; linarith
  have hgapc : 0 < bcInfoJoint pU K W - (R₁ + R₂) - 3 * ε := by rw [hε_def]; linarith
  have hε'5 : 0 < ε' / 5 := by linarith
  -- Threshold indices for the five vanishing contributions.
  obtain ⟨N₀₂, hN₀₂⟩ := Filter.eventually_atTop.mp
    ((bc_E0₂_vanishing pU K W hε_pos).eventually_lt_const hε'5)
  obtain ⟨N₀₁, hN₀₁⟩ := Filter.eventually_atTop.mp
    ((bc_E0₁_vanishing pU K W hε_pos).eventually_lt_const hε'5)
  obtain ⟨N₂, hN₂⟩ := channelCoding_E2_lt_of_rate (I := bcInfo₂ pU K W) (R := R₂)
    (ε := ε) (ε' := ε' / 5) hgap₂ hε'5
  obtain ⟨Nb, hNb⟩ := channelCoding_E2_lt_of_rate (I := bcInfo₁ pU K W) (R := R₁)
    (ε := 4 * ε / 3) (ε' := ε' / 5)
    (by have h34 : 3 * (4 * ε / 3) = 4 * ε := by ring
        rw [h34]; exact hgapb) hε'5
  obtain ⟨Nc, hNc⟩ := bc_Ec_lt_of_rate (Ijoint := bcInfoJoint pU K W) (R₁ := R₁) (R₂ := R₂)
    (ε := ε) (ε' := ε' / 5) _hR₁.le hgapc hε'5
  refine ⟨max (max N₀₂ N₀₁) (max (max N₂ Nb) Nc), fun n hn ↦ ?_⟩
  have hn₀₂ : N₀₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₀₁ : N₀₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hn
  have hnb : Nb ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hn
  have hnc : Nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  set M₁ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₁)) with hM₁_def
  set M₂ : ℕ := Nat.ceil (Real.exp ((n : ℝ) * R₂)) with hM₂_def
  have hM₁_pos : 0 < M₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM₂_pos : 0 < M₂ := Nat.ceil_pos.mpr (Real.exp_pos _)
  -- The two per-receiver random-codebook averaged bounds.
  have h_avg₂ := bc_random_codebook_average₂_le (M₁ := M₁) (M₂ := M₂) (n := n)
    pU K W hpU hK hW hM₁_pos hM₂_pos hε_pos
  have h_avg₁ := bc_random_codebook_average₁_le (M₁ := M₁) (M₂ := M₂) (n := n)
    pU K W hpU hK hW hM₁_pos hM₂_pos hε_pos
  -- Each of the five contributions is `< ε'/5`.
  have hE0₂ : ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
      { q | q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε } < ε' / 5 :=
    hN₀₂ n hn₀₂
  have hE0₁ : ((bcAmbientMeasure pU K W).map
        (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
      { q | q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε } < ε' / 5 :=
    hN₀₁ n hn₀₁
  have hexp₂ : ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₂ pU K W) + 3 * ε)) < ε' / 5 := by
    rw [hM₂_def]; exact hN₂ n hn₂
  have hexpb : ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε)) < ε' / 5 := by
    rw [hM₁_def, show (n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε)
        = (n : ℝ) * (-(bcInfo₁ pU K W) + 3 * (4 * ε / 3)) from by ring]
    exact hNb n hnb
  have hexpc : ((M₂ : ℝ) - 1) * (M₁ : ℝ) *
      Real.exp ((n : ℝ) * (-(bcInfoJoint pU K W) + 3 * ε)) < ε' / 5 := by
    rw [hM₂_def, hM₁_def]; exact hNc n hnc
  -- The summed random-codebook bound `B`, and `B < ε'`.
  set B : ℝ :=
    (((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcXs n ω, jointRV bcY₁s n ω))).real
        { q | q ∉ macJointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcXs bcY₁s n ε }
      + ((M₁ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₁ pU K W) + 4 * ε))
      + ((M₂ : ℝ) - 1) * (M₁ : ℝ) * Real.exp ((n : ℝ) * (-(bcInfoJoint pU K W) + 3 * ε)))
    + (((bcAmbientMeasure pU K W).map
          (fun ω ↦ (jointRV bcUs n ω, jointRV bcY₂s n ω))).real
        { q | q ∉ jointlyTypicalSet (bcAmbientMeasure pU K W) bcUs bcY₂s n ε }
      + ((M₂ : ℝ) - 1) * Real.exp ((n : ℝ) * (-(bcInfo₂ pU K W) + 3 * ε))) with hB_def
  have hB_lt : B < ε' := by rw [hB_def]; linarith
  -- The summed averaged error is `≤ B` (split the two receivers additively).
  have h_avg_le :
      ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
        * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
            (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
              * (((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₁ W).toReal
                 + ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₂ W).toReal)
        ≤ B := by
    rw [hB_def]
    calc ∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
          * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
              (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
                * (((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₁ W).toReal
                   + ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₂ W).toReal)
        = (∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
              * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
                  (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
                    * ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₁ W).toReal)
          + (∑ cU : BCCloudCodebook M₂ n U, (bcCloudCodebookMeasure pU M₂ n).real {cU}
              * ∑ cX : BCSatelliteCodebook M₁ M₂ n α,
                  (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX}
                    * ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₂ W).toReal)
          := bc_weighted_two_tier_add
            (fun cU ↦ (bcCloudCodebookMeasure pU M₂ n).real {cU})
            (fun cU cX ↦ (bcSatelliteCodebookMeasure K M₁ M₂ n cU).real {cX})
            (fun cU cX ↦
              ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₁ W).toReal)
            (fun cU cX ↦
              ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₂ W).toReal)
      _ ≤ _ := add_le_add h_avg₁ h_avg₂
  -- Pigeonhole to a deterministic codebook pair, then split the summed error.
  obtain ⟨cU, cX, hcb⟩ := bc_exists_codebook_le_avg pU K W hM₁_pos hM₂_pos B h_avg_le
  have hsum_lt : ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₁ W).toReal
      + ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₂ W).toReal < ε' :=
    lt_of_le_of_lt hcb hB_lt
  have hnn₁ : 0 ≤ ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₁ W).toReal :=
    ENNReal.toReal_nonneg
  have hnn₂ : 0 ≤ ((bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX).averageErrorProb₂ W).toReal :=
    ENNReal.toReal_nonneg
  refine ⟨M₁, M₂, le_refl _, le_refl _, bcCodebookToCode pU K W hM₁_pos hM₂_pos ε cU cX, ?_, ?_⟩
  · linarith
  · linarith

end InformationTheory.Shannon.BroadcastChannel
