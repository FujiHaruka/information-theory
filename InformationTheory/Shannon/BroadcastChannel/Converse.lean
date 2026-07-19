import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.ConverseGateway
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMIChainRule
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessMarkov

/-!
# Degraded broadcast channel — converse (outer bound)

The converse to the degraded BC coding theorem (Cover–Thomas Thm 15.6.2): for uniformly
distributed, independent messages `(W₁, W₂)` sent over a degraded broadcast channel
`X → Y₁ → Y₂` and decoded by per-receiver decoders, the rate pair `(log |M₁|, log |M₂|)`
lies in the auxiliary-variable capacity region with `Uᵢ = (W₂, Y₂^{i-1})`.

The structure mirrors the multiple-access converse `mac_converse`:

* **message level** (`bc_converse_message_level`): each rate is bounded by the relevant
  n-letter message–output mutual information plus the Fano slack, obtained from the
  single-shot Fano converse `shannon_converse_single_shot`.
* **single letter** (`bc_converse`): the message-level mutual informations are bridged to the
  per-letter channel quantities `∑ᵢ I(Uᵢ; Y_{2,i})` (receiver 2, the easy chain-rule half
  `bc_singleletterize_bound₂`) and `∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` (receiver 1, the Csiszár-sum
  single-letterization `bc_singleletterize_bound₁`), combined via `InBCCapacityRegion.mono`.

The degradedness `X → Y₁ → Y₂` and the memoryless block structure are taken as
**preconditions** (regularity / structural hypotheses); they do not carry the proof core.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*}
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [StandardBorelSpace α] [Nonempty α]
variable {β₁ : Type*}
  [Fintype β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Nonempty β₁]
variable {β₂ : Type*}
  [Fintype β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] [Nonempty β₂]
variable {M₁ M₂ n : ℕ}

/-! ## Typed Y-axis chain rule (helper for bound (a)) -/

/-- **Y-axis n-variable MI chain rule** with the left variable a different type from the
sequence: `I(W; Bⁿ) = ∑ᵢ I(W; Bᵢ | B^{<i})`. The typed analogue of the gateway's
`mutualInfo_chain_rule_Y_fin`. -/
lemma mutualInfo_chain_rule_Y_fin' {δ γ : Type*}
    [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [StandardBorelSpace γ] [Nonempty γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → δ) (Bs : Fin n → Ω → γ)
    (hW : Measurable W) (hBs : ∀ i, Measurable (Bs i)) :
    mutualInfo μ W (fun ω j ↦ Bs j ω)
      = ∑ i : Fin n,
          condMutualInfo μ W (Bs i)
            (fun ω (j : Fin i.val) ↦ Bs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  classical
  have hBpi : Measurable (fun ω j ↦ Bs j ω) := measurable_pi_iff.mpr hBs
  rw [mutualInfo_comm μ W (fun ω j ↦ Bs j ω) hW hBpi,
      mutualInfo_chain_rule_fin μ Bs hBs W hW]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpref : Measurable
      (fun ω (j : Fin i.val) ↦ Bs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr fun j ↦ hBs _
  exact condMutualInfo_comm μ (Bs i) W _ (hBs i) hW hpref

/-! ## Receiver-2 single-letterization (the easy chain-rule half, bound (a)) -/

/-- **BC converse bound (a)** (`R₂`-side, receiver 2): with `Uᵢ = (W₂, Y₂^{i-1})`,
`I(W₂; Y₂ⁿ) ≤ ∑ᵢ I(Uᵢ; Y_{2,i})`. Pure chain-rule plumbing on a prefix conditioner — no
Csiszár identity, no degradedness. Typed analogue of the gateway's `bc_converse_bound_a`. -/
theorem bc_singleletterize_bound₂
    [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → Fin M₂) (Y₂s : Fin n → Ω → β₂)
    (hW₂ : Measurable W₂) (hY₂s : ∀ i, Measurable (Y₂s i)) :
    mutualInfo μ W₂ (fun ω j ↦ Y₂s j ω)
      ≤ ∑ i : Fin n,
          mutualInfo μ
              (fun ω ↦ (W₂ ω,
                fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
              (Y₂s i) := by
  classical
  rw [mutualInfo_chain_rule_Y_fin' μ W₂ Y₂s hW₂ hY₂s]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  set pref : Ω → (Fin i.val → β₂) :=
    fun ω j ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω with hpref_def
  have hpref : Measurable pref := measurable_pi_iff.mpr fun j ↦ hY₂s _
  have hreshape : mutualInfo μ (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i)
      = mutualInfo μ (fun ω ↦ (pref ω, W₂ ω)) (Y₂s i) := by
    have h := mutualInfo_map_left_measurableEquiv μ
      (fun ω ↦ (W₂ ω, pref ω)) (Y₂s i) (hW₂.prodMk hpref) (hY₂s i)
      (MeasurableEquiv.prodComm (α := Fin M₂) (β := (Fin i.val → β₂)))
    simpa [MeasurableEquiv.prodComm] using h.symm
  rw [hreshape, mutualInfo_chain_rule μ W₂ (Y₂s i) pref hW₂ (hY₂s i) hpref]
  exact le_add_self

/-! ## Message-level Fano bounds

The message-level bounds are pure single-shot Fano plumbing on the output measurable spaces,
so the finite-alphabet / standard-Borel structure of the variable context is unused here. -/

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β₁] [Nonempty β₁] [Fintype β₂] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] [Nonempty β₂] in
/-- **BC converse, receiver-1 corner bound** (message level): under a uniform message `W₁`,
`log |M₁| ≤ I(W₁; (W₂, Y₁ⁿ)) + h(Pe₁) + Pe₁ · log(|M₁| − 1)`, with `Pe₁` the receiver-1
error probability of the `Y₁`-only decoder. -/
theorem bc_converse_bound₁
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ : Ω → Fin M₁) (W₂ : Ω → Fin M₂) (Y₁s : Fin n → Ω → β₁)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (hW₁ : Measurable W₁) (hW₂ : Measurable W₂) (hY₁s : ∀ i, Measurable (Y₁s i))
    (hW₁_uniform : μ.map W₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) :
    Real.log (M₁ : ℝ) ≤
      (mutualInfo μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
              (fun p ↦ c.decoder₁ p.2))
        + MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
              (fun p ↦ c.decoder₁ p.2) * Real.log ((M₁ : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₁) := ⟨⟨0, by omega⟩⟩
  set Yo : Ω → Fin M₂ × (Fin n → β₁) := fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω) with hYo_def
  have hYo : Measurable Yo := hW₂.prodMk (measurable_pi_iff.mpr hY₁s)
  have hdec : Measurable (fun p : Fin M₂ × (Fin n → β₁) ↦ c.decoder₁ p.2) :=
    measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₁) := by rw [Fintype.card_fin]; exact hcard₁
  have hMI_fin : mutualInfo μ W₁ Yo ≠ ∞ := mutualInfo_ne_top μ W₁ Yo hW₁ hYo
  have h := shannon_converse_single_shot μ W₁ Yo
    (fun p ↦ c.decoder₁ p.2) hW₁ hYo hdec hW₁_uniform hcard hMI_fin
  rw [Fintype.card_fin] at h
  exact h

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [StandardBorelSpace β₂] [Nonempty β₂] in
/-- **BC converse, receiver-2 corner bound** (message level): under a uniform message `W₂`,
`log |M₂| ≤ I(W₂; Y₂ⁿ) + h(Pe₂) + Pe₂ · log(|M₂| − 1)`, with `Pe₂` the receiver-2 error
probability. -/
theorem bc_converse_bound₂
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → Fin M₂) (Y₂s : Fin n → Ω → β₂)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (hW₂ : Measurable W₂) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hW₂_uniform : μ.map W₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₂ : 2 ≤ M₂) :
    Real.log (M₂ : ℝ) ≤
      (mutualInfo μ W₂ (fun ω i ↦ Y₂s i ω)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ W₂ (fun ω i ↦ Y₂s i ω) c.decoder₂)
        + MeasureFano.errorProb μ W₂ (fun ω i ↦ Y₂s i ω) c.decoder₂
            * Real.log ((M₂ : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₂) := ⟨⟨0, by omega⟩⟩
  set Yo : Ω → Fin n → β₂ := fun ω i ↦ Y₂s i ω with hYo_def
  have hYo : Measurable Yo := measurable_pi_iff.mpr hY₂s
  have hdec : Measurable c.decoder₂ := measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₂) := by rw [Fintype.card_fin]; exact hcard₂
  have hMI_fin : mutualInfo μ W₂ Yo ≠ ∞ := mutualInfo_ne_top μ W₂ Yo hW₂ hYo
  have h := shannon_converse_single_shot μ W₂ Yo c.decoder₂ hW₂ hYo hdec
    hW₂_uniform hcard hMI_fin
  rw [Fintype.card_fin] at h
  exact h

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- **BC converse — message-level Fano outer bound**: for uniform messages decoded by
per-receiver decoders, the rate pair satisfies the two message-level Fano information bounds,
packaged as `InBCCapacityRegion`. The single-letterization that turns this into the textbook
degraded-BC converse is `bc_converse`. -/
theorem bc_converse_message_level
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ : Ω → Fin M₁) (W₂ : Ω → Fin M₂) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hW₁_uniform : μ.map W₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hW₂_uniform : μ.map W₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((mutualInfo μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
              (fun p ↦ c.decoder₁ p.2))
        + MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
              (fun p ↦ c.decoder₁ p.2) * Real.log ((M₁ : ℝ) - 1))
      ((mutualInfo μ W₂ (fun ω i ↦ Y₂s i ω)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ W₂ (fun ω i ↦ Y₂s i ω) c.decoder₂)
        + MeasureFano.errorProb μ W₂ (fun ω i ↦ Y₂s i ω) c.decoder₂
            * Real.log ((M₂ : ℝ) - 1)) :=
  ⟨bc_converse_bound₁ μ W₁ W₂ Y₁s c hW₁ hW₂ hY₁s hW₁_uniform hcard₁,
   bc_converse_bound₂ (α := α) (β₁ := β₁) μ W₂ Y₂s c hW₂ hY₂s hW₂_uniform hcard₂⟩

/-! ## Receiver-1 single-letterization (Csiszár-sum half, bound (b)) -/

omit [Fintype β₂] [MeasurableSingletonClass β₂] in
private lemma bc_input_singleletterize_lhs_noise_collapse
    [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → Fin M₂) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW₂ : Measurable W₂) (hXs : ∀ i, Measurable (Xs i))
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (W₂ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
        (Xs i) (Y₁s i)) :
    MeasureFano.condEntropy μ (fun ω j ↦ Y₁s j ω) (fun ω ↦ (W₂ ω, fun j ↦ Xs j ω))
      = ∑ i : Fin n, MeasureFano.condEntropy μ (Y₁s i) (Xs i) := by
  classical
  set Xpi : Ω → (Fin n → α) := fun ω j ↦ Xs j ω with hXpi_def
  have hXpi : Measurable Xpi := measurable_pi_iff.mpr hXs
  have hY₁pre : ∀ i : Fin n, Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) := fun i ↦
    measurable_pi_iff.mpr fun j ↦ hY₁s _
  rw [condEntropy_pi_chain_rule_aux μ (fun ω ↦ (W₂ ω, Xpi ω)) Y₁s (hW₂.prodMk hXpi) hY₁s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Goal: `H(Y₁ᵢ | ((W₂, Xⁿ), Y₁^{<i})) = H(Y₁ᵢ | Xᵢ)`.
  -- Extract equiv splitting `Xⁿ ↔ (Xᵢ, X^{≠i})`.
  let eX : (Fin n → α) ≃ᵐ α × ({j : Fin n // j ≠ i} → α) :=
    ChannelCodingConverseGeneral.measurableEquivExtract (β := α) i
  have hext : (fun ω ↦ eX.symm (Xs i ω,
      fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)) = Xpi := by
    funext ω j
    change eX.symm (Xs i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω) j = Xs j ω
    by_cases hj : j = i
    · subst hj
      simp [eX, ChannelCodingConverseGeneral.measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr]
    · simp [eX, ChannelCodingConverseGeneral.measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, hj]
  -- Markov `Y₁ᵢ ⫫ (X^{≠i}, (W₂, Y₁^{<i})) | Xᵢ`, projected from `h_memo i` and swapped.
  have hblock : Measurable (fun ω ↦ (W₂ ω,
      ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
       ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
        (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω))))) :=
    hW₂.prodMk
      ((measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hXs j.val).prodMk
      ((measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hY₁s j.val).prodMk
        (measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hY₂s j.val)))
  have hRESTmeas : Measurable (fun ω ↦
      ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
       (W₂ ω, fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω))) :=
    (measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hXs j.val).prodMk
      (hW₂.prodMk (hY₁pre i))
  have hf2 : Measurable (fun (p : Fin M₂ × ((({j : Fin n // j ≠ i} → α)) ×
        ((({j : Fin n // j ≠ i} → β₁)) × ({j : Fin n // j ≠ i} → β₂)))) ↦
      (p.2.1,
       (p.1, fun (k : Fin i.val) ↦ p.2.2.1 ⟨⟨k.val, k.isLt.trans i.isLt⟩,
         by intro h; have hval : k.val = i.val := congrArg Fin.val h
            have hk := k.isLt; omega⟩))) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_pi_iff.mpr fun k ↦
        (measurable_pi_apply _).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have hml := isMarkovChain_map_left μ _ (Xs i) (Y₁s i) hblock (hXs i) (hY₁s i) hf2 (h_memo i)
  have hml' : IsMarkovChain μ (fun ω ↦
      ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
       (W₂ ω, fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω)))
      (Xs i) (Y₁s i) := hml
  have hmkv := isMarkovChain_swap μ _ (Xs i) (Y₁s i) hRESTmeas (hXs i) (hY₁s i) hml'
  have hd := condEntropy_drop_irrelevant_of_markov μ (Y₁s i) (Xs i) _
    (hY₁s i) (hXs i) hRESTmeas hmkv
  -- Reshape the chain-rule conditioner to `(Xᵢ, (X^{≠i}, (W₂, Y₁^{<i})))`, then drop.
  let Efull : α × ((({j : Fin n // j ≠ i} → α)) × (Fin M₂ × (Fin i.val → β₁)))
        ≃ᵐ (Fin M₂ × (Fin n → α)) × (Fin i.val → β₁) :=
    (MeasurableEquiv.prodAssoc.symm.trans
      (eX.symm.prodCongr (MeasurableEquiv.refl (Fin M₂ × (Fin i.val → β₁))))).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl (Fin i.val → β₁))))
  have hreshape : (fun ω ↦ ((W₂ ω, Xpi ω),
        fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      = fun ω ↦ Efull (Xs i ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           (W₂ ω, fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω))) := by
    funext ω
    have hx := congrFun hext ω
    rw [show Efull (Xs i ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           (W₂ ω, fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω)))
        = ((W₂ ω, eX.symm (Xs i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω)),
           fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω) from rfl, hx]
  rw [hreshape, condEntropy_measurableEquiv_comp μ (Y₁s i) (hY₁s i)
    (fun ω ↦ (Xs i ω,
      ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
       (W₂ ω, fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω))))
    ((hXs i).prodMk hRESTmeas) Efull]
  exact hd

/-- **BC converse, receiver-1 input-level single-letterization** (Route B, term-by-term
degradedness): under a memoryless broadcast channel with the conditioning message `W₂`
upstream of the channel and physical degradedness `X → Y₁ → Y₂`, the conditional block
input–output mutual information collapses to the per-letter auxiliary-variable sum
`I(Xⁿ; Y₁ⁿ | W₂) ≤ ∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` with `Uᵢ = (W₂, Y₂^{i-1})`.

Proof (entropy-difference route, mirroring the MAC single-letterization
`condMutualInfo_singleletter_le_of_memoryless`): both sides reduce to conditional-entropy
differences `H(Y₁ | ·) − H(Y₁ | ·, X)`.  The joint-output memoryless hypothesis `h_memo`
collapses every "noise" term `H(Y₁ᵢ | …, Xᵢ)` to the common `H(Y₁ᵢ | Xᵢ)` on both sides, so
those cancel; what remains is `H(Y₁ⁿ | W₂) ≤ ∑ᵢ H(Y₁ᵢ | W₂, Y₂^{i-1})`, which holds
term-by-term via the LHS chain rule and the conditioner swap
`H(Y₁ᵢ | W₂, Y₁^{<i}) ≤ H(Y₁ᵢ | W₂, Y₂^{<i})` (block-prefix degradedness `h_deg_block` plus
conditioning-reduces-entropy).

The two structural preconditions encode the channel, not the conclusion:

* `h_memo` — **joint-output memoryless**: `Y₁ᵢ ⫫ (W₂, X^{≠i}, Y₁^{≠i}, Y₂^{≠i}) | Xᵢ`.  It
  blocks the conditioning message `W₂` and *all* other letters (including the degraded
  outputs `Y₂^{≠i}`) at `Xᵢ`.  Blocking `Y₂^{≠i}` is needed by the entropy-difference route:
  it collapses the RHS noise term `H(Y₁ᵢ | W₂, Y₂^{<i}, Xᵢ)` to the common `H(Y₁ᵢ | Xᵢ)`.
* `h_deg_block` — **block-prefix degradedness**: `Y₁ᵢ ⫫ Y₂^{<i} | (W₂, Y₁^{<i})`.  This is the
  d-separation consequence of physical per-letter degradedness `X → Y₁ → Y₂` together with
  memorylessness; per-letter degradedness `Y₂ⱼ ⫫ Xⱼ | Y₁ⱼ` alone is insufficient (it is
  satisfied by the documented `n = 2` collider counterexample — an early degraded output
  leaking a later letter's input — which breaks the bound), and deriving the block form from
  the per-letter form needs graphoid / d-separation machinery absent from Mathlib, so it is
  taken as a structural precondition (parity with `h_memo`).  This is the hypothesis that
  rules out the collider counterexample (it fails there: `Y₁₁ ⫫ Y₂₀ | (·, Y₁₀)` is false when
  `Y₁₁ = Y₂₀`), whereas the strengthened `h_memo` still holds in it.

Both are regularity / structural preconditions (true in the operational degraded-memoryless
setup where `Xⁿ = encoder (W₁, W₂)`), not load-bearing.

@audit:ok -/
theorem bc_input_singleletterize
    [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₂ : Ω → Fin M₂) (Xs : Fin n → Ω → α) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW₂ : Measurable W₂) (hXs : ∀ i, Measurable (Xs i))
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (W₂ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
        (Xs i) (Y₁s i))
    (h_deg_block : ∀ i : Fin n,
      IsMarkovChain μ (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) :
    condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₁s j ω) W₂
      ≤ ∑ i : Fin n,
          condMutualInfo μ (Xs i) (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  classical
  set Xpi : Ω → (Fin n → α) := fun ω j ↦ Xs j ω with hXpi_def
  set Y₁pi : Ω → (Fin n → β₁) := fun ω j ↦ Y₁s j ω with hY₁pi_def
  have hXpi : Measurable Xpi := measurable_pi_iff.mpr hXs
  have hY₁pi : Measurable Y₁pi := measurable_pi_iff.mpr hY₁s
  -- per-letter prefix / auxiliary conditioner measurabilities.
  have hY₁pre : ∀ i : Fin n, Measurable
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) := fun i ↦
    measurable_pi_iff.mpr fun j ↦ hY₁s _
  have hY₂pre : ∀ i : Fin n, Measurable
      (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω) := fun i ↦
    measurable_pi_iff.mpr fun j ↦ hY₂s _
  have hUi : ∀ i : Fin n, Measurable
      (fun ω ↦ (W₂ ω, fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := fun i ↦
    hW₂.prodMk (hY₂pre i)
  have hV₁ : ∀ i : Fin n, Measurable
      (fun ω ↦ (W₂ ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := fun i ↦
    hW₂.prodMk (hY₁pre i)
  -- LHS as a conditional-entropy difference.
  have hLHS : (condMutualInfo μ Xpi Y₁pi W₂).toReal
      = MeasureFano.condEntropy μ Y₁pi W₂
        - MeasureFano.condEntropy μ Y₁pi (fun ω ↦ (W₂ ω, Xpi ω)) := by
    rw [condMutualInfo_comm μ Xpi Y₁pi W₂ hXpi hY₁pi hW₂]
    exact condMutualInfo_eq_condEntropy_sub_condEntropy μ Y₁pi W₂ Xpi hY₁pi hW₂ hXpi
  -- LHS chain rule on `H(Y₁ⁿ | W₂)`.
  have hLHSchain : MeasureFano.condEntropy μ Y₁pi W₂
      = ∑ i : Fin n, MeasureFano.condEntropy μ (Y₁s i)
          (fun ω ↦ (W₂ ω,
            fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) :=
    condEntropy_pi_chain_rule_aux μ W₂ Y₁s hW₂ hY₁s
  -- LHS noise collapse `H(Y₁ⁿ | (W₂, Xⁿ)) = ∑ᵢ H(Y₁ᵢ | Xᵢ)`.
  have hLHSnoise : MeasureFano.condEntropy μ Y₁pi (fun ω ↦ (W₂ ω, Xpi ω))
      = ∑ i : Fin n, MeasureFano.condEntropy μ (Y₁s i) (Xs i) :=
    bc_input_singleletterize_lhs_noise_collapse μ W₂ Xs Y₁s Y₂s hW₂ hXs hY₁s hY₂s h_memo
  -- RHS per-term as a conditional-entropy difference (noise collapses to `H(Y₁ᵢ | Xᵢ)`).
  have hRHS : ∀ i : Fin n,
      (condMutualInfo μ (Xs i) (Y₁s i)
          (fun ω ↦ (W₂ ω,
            fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal
        = MeasureFano.condEntropy μ (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
          - MeasureFano.condEntropy μ (Y₁s i) (Xs i) := by
    intro i
    rw [condMutualInfo_comm μ (Xs i) (Y₁s i) _ (hXs i) (hY₁s i) (hUi i),
      condMutualInfo_eq_condEntropy_sub_condEntropy μ (Y₁s i) _ (Xs i)
        (hY₁s i) (hUi i) (hXs i)]
    have hdrop : MeasureFano.condEntropy μ (Y₁s i)
        (fun ω ↦ ((W₂ ω,
            fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω), Xs i ω))
        = MeasureFano.condEntropy μ (Y₁s i) (Xs i) := by
      -- Markov `Y₁ᵢ ⫫ (W₂, Y₂^{<i}) | Xᵢ`, projected from `h_memo i` and swapped.
      have hblock : Measurable (fun ω ↦ (W₂ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω))))) :=
        hW₂.prodMk
          ((measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hXs j.val).prodMk
          ((measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hY₁s j.val).prodMk
            (measurable_pi_iff.mpr fun (j : {j : Fin n // j ≠ i}) ↦ hY₂s j.val)))
      have hf : Measurable (fun (p : Fin M₂ × ((({j : Fin n // j ≠ i} → α)) ×
            ((({j : Fin n // j ≠ i} → β₁)) × ({j : Fin n // j ≠ i} → β₂)))) ↦
          (p.1, fun (k : Fin i.val) ↦ p.2.2.2 ⟨⟨k.val, k.isLt.trans i.isLt⟩,
            by intro h; have hval : k.val = i.val := congrArg Fin.val h
               have hk := k.isLt; omega⟩)) :=
        measurable_fst.prodMk (measurable_pi_iff.mpr fun k ↦
          (measurable_pi_apply _).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      have hml := isMarkovChain_map_left μ _ (Xs i) (Y₁s i) hblock (hXs i) (hY₁s i) hf (h_memo i)
      have hml' : IsMarkovChain μ
          (fun ω ↦ (W₂ ω,
            fun (k : Fin i.val) ↦ Y₂s ⟨k.val, k.isLt.trans i.isLt⟩ ω)) (Xs i) (Y₁s i) := hml
      have hmkv := isMarkovChain_swap μ _ (Xs i) (Y₁s i) (hUi i) (hXs i) (hY₁s i) hml'
      have hd := condEntropy_drop_irrelevant_of_markov μ (Y₁s i) (Xs i)
        (fun ω ↦ (W₂ ω, fun (k : Fin i.val) ↦ Y₂s ⟨k.val, k.isLt.trans i.isLt⟩ ω))
        (hY₁s i) (hXs i) (hUi i) hmkv
      have hcomm := condEntropy_measurableEquiv_comp μ (Y₁s i) (hY₁s i)
        (fun ω ↦ ((W₂ ω,
          fun (k : Fin i.val) ↦ Y₂s ⟨k.val, k.isLt.trans i.isLt⟩ ω), Xs i ω))
        ((hUi i).prodMk (hXs i)) MeasurableEquiv.prodComm
      rw [show (fun ω ↦ (MeasurableEquiv.prodComm ((W₂ ω,
              fun (k : Fin i.val) ↦ Y₂s ⟨k.val, k.isLt.trans i.isLt⟩ ω), Xs i ω)))
            = (fun ω ↦ (Xs i ω, (W₂ ω,
              fun (k : Fin i.val) ↦ Y₂s ⟨k.val, k.isLt.trans i.isLt⟩ ω))) from rfl] at hcomm
      rw [← hcomm, hd]
    rw [hdrop]
  -- Per-letter conditioner swap `H(Y₁ᵢ | W₂, Y₁^{<i}) ≤ H(Y₁ᵢ | W₂, Y₂^{<i})`.
  have hStep : ∀ i : Fin n,
      MeasureFano.condEntropy μ (Y₁s i)
          (fun ω ↦ (W₂ ω,
            fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        ≤ MeasureFano.condEntropy μ (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
    intro i
    -- Step (i): `H(Y₁ᵢ | W₂, Y₁^{<i}) = H(Y₁ᵢ | (W₂, Y₁^{<i}), Y₂^{<i})` via `h_deg_block`.
    have h1 := (condEntropy_drop_irrelevant_of_markov μ (Y₁s i)
      (fun ω ↦ (W₂ ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      (hY₁s i) (hV₁ i) (hY₂pre i) (h_deg_block i)).symm
    rw [h1]
    -- Step (ii): reshape `((W₂,Y₁^{<i}),Y₂^{<i}) ↦ ((W₂,Y₂^{<i}),Y₁^{<i})` then drop `Y₁^{<i}`.
    let e : (Fin M₂ × (Fin i.val → β₁)) × (Fin i.val → β₂)
          ≃ᵐ (Fin M₂ × (Fin i.val → β₂)) × (Fin i.val → β₁) :=
      (MeasurableEquiv.prodAssoc.trans
        ((MeasurableEquiv.refl (Fin M₂)).prodCongr MeasurableEquiv.prodComm)).trans
        MeasurableEquiv.prodAssoc.symm
    have hreshape : MeasureFano.condEntropy μ (Y₁s i)
          (fun ω ↦ ((W₂ ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
            fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        = MeasureFano.condEntropy μ (Y₁s i)
            (fun ω ↦ ((W₂ ω, fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
              fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
      have h := condEntropy_measurableEquiv_comp μ (Y₁s i) (hY₁s i)
        (fun ω ↦ ((W₂ ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        ((hW₂.prodMk (hY₁pre i)).prodMk (hY₂pre i)) e
      rw [show (fun ω ↦ e ((W₂ ω,
              fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
            fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
          = (fun ω ↦ ((W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
            fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) from rfl] at h
      exact h.symm
    rw [hreshape]
    exact condEntropy_le_condEntropy_of_pair μ (Y₁s i)
      (fun ω ↦ (W₂ ω, fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      (fun ω (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      (hY₁s i) (hUi i) (hY₁pre i)
  -- Assemble the real inequality.
  have hreal : (condMutualInfo μ Xpi Y₁pi W₂).toReal
      ≤ ∑ i : Fin n,
          (condMutualInfo μ (Xs i) (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal := by
    rw [Finset.sum_congr rfl (fun i _ ↦ hRHS i), Finset.sum_sub_distrib, hLHS, hLHSchain,
      hLHSnoise]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hStep i)
    linarith
  -- Lift back to `ℝ≥0∞`.
  have hLfin : condMutualInfo μ Xpi Y₁pi W₂ ≠ ∞ :=
    condMutualInfo_ne_top μ Xpi Y₁pi W₂ hXpi hY₁pi hW₂
  have hRfin : ∀ i : Fin n,
      condMutualInfo μ (Xs i) (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) ≠ ∞ := fun i ↦
    condMutualInfo_ne_top μ (Xs i) (Y₁s i) _ (hXs i) (hY₁s i) (hUi i)
  have hsumfin : (∑ i : Fin n,
      condMutualInfo μ (Xs i) (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ ↦ (hRfin i).lt_top).ne
  rw [← ENNReal.toReal_le_toReal hLfin hsumfin, ENNReal.toReal_sum (fun i _ ↦ hRfin i)]
  exact hreal

/-- **BC converse, receiver-1 single-letterized corner bound** (bound (b)): the message–output
mutual information `I(W₁; (W₂, Y₁ⁿ))` is bounded by the per-letter auxiliary-variable sum
`∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` with `Uᵢ = (W₂, Y₂^{i-1})`, `Xᵢ = (encoder (W₁, W₂))ᵢ`.

Reduction: independence gives `I(W₁; (W₂, Y₁ⁿ)) = I(W₁; Y₁ⁿ | W₂)`; data processing along
`W₁ → Xⁿ → Y₁ⁿ` (conditioned on `W₂`) gives `≤ I(Xⁿ; Y₁ⁿ | W₂)`; then the input-level
single-letterization `bc_input_singleletterize` closes the bound.

@audit:ok -/
theorem bc_singleletterize_bound₁
    [NeZero M₁] [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ : Ω → Fin M₁) (W₂ : Ω → Fin M₂) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (h_indep : mutualInfo μ W₁ W₂ = 0)
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (W₂ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ c.encoder (W₁ ω, W₂ ω) j.val),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
        (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i))
    (h_deg_block : ∀ i : Fin n,
      IsMarkovChain μ (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    (hmarkov : IsMarkovChain μ (fun ω ↦ (W₂ ω, W₁ ω))
      (fun ω ↦ (W₂ ω, fun j ↦ c.encoder (W₁ ω, W₂ ω) j)) (fun ω j ↦ Y₁s j ω)) :
    mutualInfo μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
      ≤ ∑ i : Fin n,
          condMutualInfo μ (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  classical
  set Xs : Fin n → Ω → α := fun i ω ↦ c.encoder (W₁ ω, W₂ ω) i with hXs_def
  set Xpi : Ω → (Fin n → α) := fun ω j ↦ Xs j ω with hXpi_def
  have hY₁pi : Measurable (fun ω j ↦ Y₁s j ω) := measurable_pi_iff.mpr hY₁s
  have henc : Measurable (fun ω ↦ c.encoder (W₁ ω, W₂ ω)) :=
    (measurable_of_countable c.encoder).comp (hW₁.prodMk hW₂)
  have hXpi : Measurable Xpi := henc
  have hXs : ∀ i, Measurable (Xs i) := fun i ↦ (measurable_pi_apply i).comp henc
  -- Step 1: I(W₁; (W₂, Y₁ⁿ)) = I(W₁; Y₁ⁿ | W₂) under message independence.
  have hstep1 : mutualInfo μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
      = condMutualInfo μ W₁ (fun ω j ↦ Y₁s j ω) W₂ := by
    rw [mutualInfo_comm μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω)) hW₁ (hW₂.prodMk hY₁pi)]
    rw [mutualInfo_chain_rule μ (fun ω j ↦ Y₁s j ω) W₁ W₂ hY₁pi hW₁ hW₂]
    rw [mutualInfo_comm μ W₂ W₁ hW₂ hW₁, h_indep, zero_add]
    exact condMutualInfo_comm μ (fun ω j ↦ Y₁s j ω) W₁ W₂ hY₁pi hW₁ hW₂
  -- Step 2: data-processing `I(W₁; Y₁ⁿ | W₂) ≤ I(Xⁿ; Y₁ⁿ | W₂)` via the block Markov chain.
  have hWcYo_fin : mutualInfo μ W₂ (fun ω j ↦ Y₁s j ω) ≠ ∞ :=
    mutualInfo_ne_top μ W₂ (fun ω j ↦ Y₁s j ω) hW₂ hY₁pi
  have hstep2 : condMutualInfo μ W₁ (fun ω j ↦ Y₁s j ω) W₂
      ≤ condMutualInfo μ Xpi (fun ω j ↦ Y₁s j ω) W₂ :=
    ChannelCodingConverseGeneral.condMutualInfo_le_of_markov_joint μ
      W₁ Xpi (fun ω j ↦ Y₁s j ω) W₂ hW₁ hXpi hY₁pi hW₂ hmarkov hWcYo_fin
  -- Step 3: input-level single-letterization (Csiszár-sum core).
  have hstep3 := bc_input_singleletterize μ W₂ Xs Y₁s Y₂s hW₂ hXs hY₁s hY₂s h_memo h_deg_block
  rw [hstep1]
  exact hstep2.trans hstep3

/-! ## Single-letterized headline -/

/-- **BC converse — genuine single-letter outer bound** (Cover–Thomas Thm 15.6.2): for
uniform, independent messages sent over a degraded memoryless broadcast channel
`X → Y₁ → Y₂` and decoded per receiver, the rate pair `(log |M₁|, log |M₂|)` lies in the
auxiliary-variable capacity region whose information bounds are the per-letter channel sums
`∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` (receiver 1) and `∑ᵢ I(Uᵢ; Y_{2,i})` (receiver 2), with
`Uᵢ = (W₂, Y₂^{i-1})`, plus the Fano error slack.

The degradedness and memoryless structure are preconditions (parity with the single-user
`channel_coding_converse_general_memoryless_pure` and `mac_converse`). The operational
instantiation — building `μ` from uniform messages through the encoder and the channel — is a
separate wrapper, not part of this statement.

@audit:ok -/
theorem bc_converse
    [NeZero M₁] [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ : Ω → Fin M₁) (W₂ : Ω → Fin M₂) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hW₁_uniform : μ.map W₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hW₂_uniform : μ.map W₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (h_indep : mutualInfo μ W₁ W₂ = 0)
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (W₂ ω,
          ((fun (j : {j : Fin n // j ≠ i}) ↦ c.encoder (W₁ ω, W₂ ω) j.val),
           ((fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω),
            (fun (j : {j : Fin n // j ≠ i}) ↦ Y₂s j.val ω)))))
        (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i))
    (h_deg_block : ∀ i : Fin n,
      IsMarkovChain μ (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    (hmarkov : IsMarkovChain μ (fun ω ↦ (W₂ ω, W₁ ω))
      (fun ω ↦ (W₂ ω, fun j ↦ c.encoder (W₁ ω, W₂ ω) j)) (fun ω j ↦ Y₁s j ω))
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n,
          condMutualInfo μ (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
              (fun p ↦ c.decoder₁ p.2))
        + MeasureFano.errorProb μ W₁ (fun ω ↦ (W₂ ω, fun i ↦ Y₁s i ω))
              (fun p ↦ c.decoder₁ p.2) * Real.log ((M₁ : ℝ) - 1))
      ((∑ i : Fin n,
          mutualInfo μ
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
            (Y₂s i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ W₂ (fun ω i ↦ Y₂s i ω) c.decoder₂)
        + MeasureFano.errorProb μ W₂ (fun ω i ↦ Y₂s i ω) c.decoder₂
            * Real.log ((M₂ : ℝ) - 1)) := by
  have hX₁s : ∀ i, Measurable (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) := fun i ↦
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp (hW₁.prodMk hW₂))
  have hbound₁ := bc_singleletterize_bound₁ μ W₁ W₂ Y₁s Y₂s c hW₁ hW₂ hY₁s hY₂s
    h_indep h_memo h_deg_block hmarkov
  have hbound₂ := bc_singleletterize_bound₂ μ W₂ Y₂s hW₂ hY₂s
  have hfin₁ : (∑ i : Fin n,
      condMutualInfo μ (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i)
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ ↦
      (condMutualInfo_ne_top μ _ _ _ (hX₁s i) (hY₁s i)
        (hW₂.prodMk (measurable_pi_iff.mpr fun j ↦ hY₂s _))).lt_top).ne
  have hfin₂ : (∑ i : Fin n,
      mutualInfo μ
        (fun ω ↦ (W₂ ω,
          fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        (Y₂s i)) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ ↦
      (mutualInfo_ne_top μ _ _ (hW₂.prodMk (measurable_pi_iff.mpr fun j ↦ hY₂s _))
        (hY₂s i)).lt_top).ne
  refine (bc_converse_message_level μ W₁ W₂ Y₁s Y₂s c hW₁ hW₂ hY₁s hY₂s
    hW₁_uniform hW₂_uniform hcard₁ hcard₂).mono ?_ ?_
  · linarith [ENNReal.toReal_mono hfin₁ hbound₁]
  · linarith [ENNReal.toReal_mono hfin₂ hbound₂]

end InformationTheory.Shannon.BroadcastChannel
