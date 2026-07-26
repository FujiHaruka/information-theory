import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.MutualInfo

/-!
# Broadcast channel — from a block code to its ambient law

The canonical ambient probability measure attached to a broadcast block code: a uniform message
pair is passed through the per-letter product channel, and the messages and the two receiver
outputs are read off the resulting measure as coordinate projections.

## Main definitions

* `bcConverseInput` — the uniform law on the message pair.
* `bcConverseKernel` — the per-letter product channel `∏ᵢ W (encoder m i)`, as a kernel in the
  message pair.
* `bcConverseAmbient` — the ambient measure `bcConverseInput ⊗ₘ bcConverseKernel`.
* `bcConverseMsg₁`, `bcConverseMsg₂` — the two message projections.
* `bcConverseYs`, `bcConverseY₁s`, `bcConverseY₂s` — the output-pair projection and its two
  per-receiver components.
* `bcConverseCodeKernel` — the codeword → output-block kernel.

## Main statements

* `bcConverseKernel_apply` — the kernel at a message pair is the code's block output law.
* `bcConverseMsg₁_uniform`, `bcConverseMsg₂_uniform` — each message is uniform under the ambient.
* `bcConverse_mutualInfo_eq_zero` — the two messages are independent under the ambient.
* `bcConverse_memoryless₁`, `bcConverse_memoryless₂` — each output letter is conditionally
  independent of the other message, the other input letters and all other output letters, given
  the current input letter.  The two same-letter outputs are never decoupled from each other.
* `bcConverse_isMarkovChain₁`, `bcConverse_isMarkovChain₂` — the messages act on a receiver's
  output block only through the codeword: `(W₂, W₁) → (W₂, Xⁿ) → Y₁ⁿ` and its mirror.

## Implementation notes

The output block lives on `Fin n → β₁ × β₂`, a sequence of output *pairs*, rather than on a pair
of sequences.  With that choice the message-to-output kernel is literally
`BroadcastCode.blockOutputLaw`, so the product structure over letters is available to the
structural lemmas and the same-letter pair `(Y_{1,i}, Y_{2,i})` is never split; the two
per-receiver output sequences are recovered as further projections.

Together with the uniformity and independence statements the four structural lemmas are exactly
the preconditions of the message-level converse `bc_uv_converse`, so instantiating it at
`bcConverseAmbient` needs no further hypotheses on the code.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]
variable {M₁ M₂ n : ℕ}

/-! ### The ambient measure -/

/-- Uniform input law on the message pair: the product of the two uniform message laws. -/
noncomputable def bcConverseInput (M₁ M₂ : ℕ) : Measure (Fin M₁ × Fin M₂) :=
  ((Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count).prod
    ((Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)

instance bcConverseInput_isProbabilityMeasure [NeZero M₁] [NeZero M₂] :
    IsProbabilityMeasure (bcConverseInput M₁ M₂) := by
  unfold bcConverseInput; infer_instance

/-- Per-letter product-channel kernel: given the message pair `m`, the output law is the product
over the `n` letters of the broadcast channel `W` applied to the encoded letter `encoder m i`.
Each letter contributes an output *pair*, so the two receivers stay coupled within a letter. -/
noncomputable def bcConverseKernel
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Kernel (Fin M₁ × Fin M₂) (Fin n → β₁ × β₂) :=
  Kernel.ofFunOfCountable (fun m ↦ Measure.pi (fun i ↦ W (c.encoder m i)))

instance bcConverseKernel_isMarkovKernel
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsMarkovKernel (bcConverseKernel c W) := by
  refine ⟨fun m ↦ ?_⟩
  show IsProbabilityMeasure (Measure.pi (fun i ↦ W (c.encoder m i)))
  infer_instance

lemma bcConverseKernel_apply
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) (m : Fin M₁ × Fin M₂) :
    bcConverseKernel c W m = c.blockOutputLaw W m := rfl

/-- Canonical ambient measure for the broadcast converse: a uniform message pair passed through
the per-letter product channel. -/
noncomputable def bcConverseAmbient
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Measure ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) :=
  (bcConverseInput M₁ M₂) ⊗ₘ (bcConverseKernel c W)

instance bcConverseAmbient_isProbabilityMeasure
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    IsProbabilityMeasure (bcConverseAmbient c W) := by
  unfold bcConverseAmbient; infer_instance

/-! ### Projections -/

/-- Message-1 projection `ω ↦ ω.1.1`. -/
def bcConverseMsg₁ : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → Fin M₁ := fun ω ↦ ω.1.1

/-- Message-2 projection `ω ↦ ω.1.2`. -/
def bcConverseMsg₂ : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → Fin M₂ := fun ω ↦ ω.1.2

/-- Output-pair projection `i ↦ ω ↦ ω.2 i`. -/
def bcConverseYs : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → β₁ × β₂ :=
  fun i ω ↦ ω.2 i

/-- Receiver-1 output projection `i ↦ ω ↦ (ω.2 i).1`. -/
def bcConverseY₁s : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → β₁ :=
  fun i ω ↦ (ω.2 i).1

/-- Receiver-2 output projection `i ↦ ω ↦ (ω.2 i).2`. -/
def bcConverseY₂s : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → β₂ :=
  fun i ω ↦ (ω.2 i).2

lemma measurable_bcConverseMsg₁ :
    Measurable (bcConverseMsg₁ (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂)) :=
  measurable_fst.fst

lemma measurable_bcConverseMsg₂ :
    Measurable (bcConverseMsg₂ (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂)) :=
  measurable_fst.snd

lemma measurable_bcConverseYs (i : Fin n) :
    Measurable (bcConverseYs (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂) i) :=
  (measurable_pi_apply i).comp measurable_snd

lemma measurable_bcConverseY₁s (i : Fin n) :
    Measurable (bcConverseY₁s (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂) i) :=
  measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_bcConverseY₂s (i : Fin n) :
    Measurable (bcConverseY₂s (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂) i) :=
  measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)

/-! ### Uniformity and independence of the messages -/

lemma bcConverseInput_map_fst [NeZero M₁] [NeZero M₂] :
    (bcConverseInput M₁ M₂).map Prod.fst
      = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count := by
  unfold bcConverseInput
  rw [Measure.map_fst_prod, measure_univ, one_smul]

lemma bcConverseInput_map_snd [NeZero M₁] [NeZero M₂] :
    (bcConverseInput M₁ M₂).map Prod.snd
      = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  unfold bcConverseInput
  rw [Measure.map_snd_prod, measure_univ, one_smul]

omit [MeasurableSpace β₁] [MeasurableSpace β₂] in
lemma bcConverse_msgPair_eq_fst :
    (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ (bcConverseMsg₁ ω, bcConverseMsg₂ ω))
      = Prod.fst := by
  funext ω; exact Prod.mk.eta

lemma bcConverseMsg₁_uniform
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    (bcConverseAmbient c W).map bcConverseMsg₁
      = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count := by
  have hcomp : (bcConverseMsg₁ (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂))
      = Prod.fst ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst]
  have hfst : (bcConverseAmbient c W).map Prod.fst = bcConverseInput M₁ M₂ := by
    rw [bcConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, bcConverseInput_map_fst]

lemma bcConverseMsg₂_uniform
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    (bcConverseAmbient c W).map bcConverseMsg₂
      = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  have hcomp : (bcConverseMsg₂ (M₁ := M₁) (M₂ := M₂) (n := n) (β₁ := β₁) (β₂ := β₂))
      = Prod.snd ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_snd measurable_fst]
  have hfst : (bcConverseAmbient c W).map Prod.fst = bcConverseInput M₁ M₂ := by
    rw [bcConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, bcConverseInput_map_snd]

lemma bcConverse_mutualInfo_eq_zero
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    mutualInfo (bcConverseAmbient c W) bcConverseMsg₁ bcConverseMsg₂ = 0 := by
  rw [mutualInfo_eq_zero_iff_indep (bcConverseAmbient c W) bcConverseMsg₁ bcConverseMsg₂
      measurable_bcConverseMsg₁ measurable_bcConverseMsg₂,
    indepFun_iff_map_prod_eq_prod_map_map measurable_bcConverseMsg₁.aemeasurable
      measurable_bcConverseMsg₂.aemeasurable,
    bcConverseMsg₁_uniform c W, bcConverseMsg₂_uniform c W, bcConverse_msgPair_eq_fst]
  have hfst : (bcConverseAmbient c W).map Prod.fst = bcConverseInput M₁ M₂ := by
    rw [bcConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, bcConverseInput]

/-! ### The codeword kernel -/

section CodeKernel

variable [Fintype α] [MeasurableSingletonClass α]

/-- Codeword → output-block kernel: given an input codeword `x`, the output law is the per-letter
product `∏ᵢ W (x i)` of the broadcast channel. -/
noncomputable def bcConverseCodeKernel (W : BCChannel α β₁ β₂) :
    Kernel (Fin n → α) (Fin n → β₁ × β₂) :=
  Kernel.ofFunOfCountable (fun x ↦ Measure.pi (fun i ↦ W (x i)))

instance bcConverseCodeKernel_isMarkovKernel (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsMarkovKernel (bcConverseCodeKernel (n := n) (α := α) (β₁ := β₁) (β₂ := β₂) W) := by
  refine ⟨fun x ↦ ?_⟩
  show IsProbabilityMeasure (Measure.pi (fun i ↦ W (x i)))
  infer_instance

end CodeKernel

/-! ### Structural hypotheses of the message-level converse -/

section Structural

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Joint-output memorylessness at receiver 1, read off the ambient: the letter-`i` output of
receiver 1 is conditionally independent of message 2, of the other input letters and of all the
other output letters of both receivers, given the input letter `encoder m i`.  The same-letter
pair of outputs is never decoupled, so the two receivers stay arbitrarily correlated within a
letter.  This is the hypothesis `h_memo₁` of `bc_uv_converse` at `bcConverseAmbient`.
@audit:ok -/
lemma bcConverse_memoryless₁
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    IsMarkovChain (bcConverseAmbient c W)
      (fun ω ↦ (bcConverseMsg₂ ω,
        ((fun (j : {j : Fin n // j ≠ i}) ↦ c.encoder ω.1 j.val),
         ((fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₁s j.val ω),
          (fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₂s j.val ω)))))
      (fun ω ↦ c.encoder ω.1 i) (bcConverseY₁s i) := by
  set F : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) →
      Fin M₂ × (({j : Fin n // j ≠ i} → α) ×
        (({j : Fin n // j ≠ i} → β₁) × ({j : Fin n // j ≠ i} → β₂))) :=
    fun ω ↦ (bcConverseMsg₂ ω,
      ((fun (j : {j : Fin n // j ≠ i}) ↦ c.encoder ω.1 j.val),
       ((fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₁s j.val ω),
        (fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₂s j.val ω)))) with hF_def
  have hF : Measurable F := by
    rw [hF_def]
    exact measurable_bcConverseMsg₂.prodMk
      ((measurable_pi_iff.mpr fun j : {j : Fin n // j ≠ i} ↦ (measurable_pi_apply j.val).comp
          ((measurable_of_countable c.encoder).comp measurable_fst)).prodMk
        ((measurable_pi_iff.mpr fun j : {j : Fin n // j ≠ i} ↦
            measurable_bcConverseY₁s j.val).prodMk
          (measurable_pi_iff.mpr fun j : {j : Fin n // j ≠ i} ↦ measurable_bcConverseY₂s j.val)))
  have hupd : ∀ (m : Fin M₁ × Fin M₂) (y : Fin n → β₁ × β₂) (b : β₁ × β₂),
      F (m, Function.update y i b) = F (m, y) := by
    intro m y b
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_)))
    · exact congrArg Prod.fst (Function.update_of_ne j.2 b y)
    · exact congrArg Prod.snd (Function.update_of_ne j.2 b y)
  have hZc : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ c.encoder ω.1 i) :=
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)
  have hYo : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h₀ := isMarkovChain_of_compProd_pi (bcConverseInput M₁ M₂) c.encoder
    (measurable_of_countable _) W (bcConverseKernel c W) (fun m ↦ rfl) i F hF hupd
  have h₁ := isMarkovChain_swap (bcConverseAmbient c W) F _ (fun ω ↦ ω.2 i) hF hZc hYo h₀
  have h₂ := isMarkovChain_map_left (bcConverseAmbient c W) (fun ω ↦ ω.2 i) _ F hYo hZc hF
    measurable_fst h₁
  exact isMarkovChain_swap (bcConverseAmbient c W) _ _ F (measurable_bcConverseY₁s i) hZc hF h₂

omit [Fintype α] [MeasurableSingletonClass α] in
/-- Joint-output memorylessness at receiver 2, the mirror of `bcConverse_memoryless₁`: the
letter-`i` output of receiver 2 is conditionally independent of message 1, of the other input
letters and of all the other output letters of both receivers, given the input letter
`encoder m i`.  This is the hypothesis `h_memo₂` of `bc_uv_converse` at `bcConverseAmbient`.
@audit:ok -/
lemma bcConverse_memoryless₂
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    IsMarkovChain (bcConverseAmbient c W)
      (fun ω ↦ (bcConverseMsg₁ ω,
        ((fun (j : {j : Fin n // j ≠ i}) ↦ c.encoder ω.1 j.val),
         ((fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₁s j.val ω),
          (fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₂s j.val ω)))))
      (fun ω ↦ c.encoder ω.1 i) (bcConverseY₂s i) := by
  set F : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) →
      Fin M₁ × (({j : Fin n // j ≠ i} → α) ×
        (({j : Fin n // j ≠ i} → β₁) × ({j : Fin n // j ≠ i} → β₂))) :=
    fun ω ↦ (bcConverseMsg₁ ω,
      ((fun (j : {j : Fin n // j ≠ i}) ↦ c.encoder ω.1 j.val),
       ((fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₁s j.val ω),
        (fun (j : {j : Fin n // j ≠ i}) ↦ bcConverseY₂s j.val ω)))) with hF_def
  have hF : Measurable F := by
    rw [hF_def]
    exact measurable_bcConverseMsg₁.prodMk
      ((measurable_pi_iff.mpr fun j : {j : Fin n // j ≠ i} ↦ (measurable_pi_apply j.val).comp
          ((measurable_of_countable c.encoder).comp measurable_fst)).prodMk
        ((measurable_pi_iff.mpr fun j : {j : Fin n // j ≠ i} ↦
            measurable_bcConverseY₁s j.val).prodMk
          (measurable_pi_iff.mpr fun j : {j : Fin n // j ≠ i} ↦ measurable_bcConverseY₂s j.val)))
  have hupd : ∀ (m : Fin M₁ × Fin M₂) (y : Fin n → β₁ × β₂) (b : β₁ × β₂),
      F (m, Function.update y i b) = F (m, y) := by
    intro m y b
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_)))
    · exact congrArg Prod.fst (Function.update_of_ne j.2 b y)
    · exact congrArg Prod.snd (Function.update_of_ne j.2 b y)
  have hZc : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ c.encoder ω.1 i) :=
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)
  have hYo : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h₀ := isMarkovChain_of_compProd_pi (bcConverseInput M₁ M₂) c.encoder
    (measurable_of_countable _) W (bcConverseKernel c W) (fun m ↦ rfl) i F hF hupd
  have h₁ := isMarkovChain_swap (bcConverseAmbient c W) F _ (fun ω ↦ ω.2 i) hF hZc hYo h₀
  have h₂ := isMarkovChain_map_left (bcConverseAmbient c W) (fun ω ↦ ω.2 i) _ F hYo hZc hF
    measurable_snd h₁
  exact isMarkovChain_swap (bcConverseAmbient c W) _ _ F (measurable_bcConverseY₂s i) hZc hF h₂

omit [StandardBorelSpace α] [Nonempty α] in
/-- The messages act on receiver 1's output block only through the codeword: `(W₂, W₁) →
(W₂, Xⁿ) → Y₁ⁿ` under the ambient.  This is the hypothesis `hmarkov₁` of `bc_uv_converse` at
`bcConverseAmbient`.
@audit:ok -/
lemma bcConverse_isMarkovChain₁
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    IsMarkovChain (bcConverseAmbient c W)
      (fun ω ↦ (bcConverseMsg₂ ω, bcConverseMsg₁ ω))
      (fun ω ↦ (bcConverseMsg₂ ω, fun j ↦ c.encoder ω.1 j))
      (fun ω j ↦ bcConverseY₁s j ω) := by
  have hfstm : Measurable
      (Prod.fst : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → Fin M₁ × Fin M₂) := measurable_fst
  have hsndm : Measurable
      (Prod.snd : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → (Fin n → β₁ × β₂)) := measurable_snd
  have hZm : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦
      ((ω.1.2 : Fin M₂), c.encoder ω.1)) :=
    (measurable_of_countable (fun m : Fin M₁ × Fin M₂ ↦ (m.2, c.encoder m))).comp measurable_fst
  have hproj : Measurable (fun (y : Fin n → β₁ × β₂) (j : Fin n) ↦ (y j).1) :=
    measurable_pi_iff.mpr fun j ↦ measurable_fst.comp (measurable_pi_apply j)
  have hY₁m : Measurable
      (fun (ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) (j : Fin n) ↦ bcConverseY₁s j ω) :=
    measurable_pi_iff.mpr fun j ↦ measurable_bcConverseY₁s j
  have h₀ := isMarkovChain_of_compProd_encoder (bcConverseInput M₁ M₂)
    (fun m : Fin M₁ × Fin M₂ ↦ (m.2, c.encoder m)) (measurable_of_countable _)
    (bcConverseKernel c W) ((bcConverseCodeKernel W).comap Prod.snd measurable_snd)
    (fun m ↦ rfl)
  have h₁ := isMarkovChain_swap (bcConverseAmbient c W) Prod.fst _ Prod.snd hfstm hZm hsndm h₀
  have h₂ := isMarkovChain_map_left (bcConverseAmbient c W) Prod.snd _ Prod.fst hsndm hZm hfstm
    hproj h₁
  have h₃ := isMarkovChain_swap (bcConverseAmbient c W) _ _ Prod.fst hY₁m hZm hfstm h₂
  exact isMarkovChain_map_left (bcConverseAmbient c W) Prod.fst _ _ hfstm hZm hY₁m
    measurable_swap h₃

omit [StandardBorelSpace α] [Nonempty α] in
/-- The mirror of `bcConverse_isMarkovChain₁` at receiver 2: `(W₁, W₂) → (W₁, Xⁿ) → Y₂ⁿ` under
the ambient.  This is the hypothesis `hmarkov₂` of `bc_uv_converse` at `bcConverseAmbient`.
@audit:ok -/
lemma bcConverse_isMarkovChain₂
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    IsMarkovChain (bcConverseAmbient c W)
      (fun ω ↦ (bcConverseMsg₁ ω, bcConverseMsg₂ ω))
      (fun ω ↦ (bcConverseMsg₁ ω, fun j ↦ c.encoder ω.1 j))
      (fun ω j ↦ bcConverseY₂s j ω) := by
  have hfstm : Measurable
      (Prod.fst : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → Fin M₁ × Fin M₂) := measurable_fst
  have hsndm : Measurable
      (Prod.snd : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → (Fin n → β₁ × β₂)) := measurable_snd
  have hZm : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦
      ((ω.1.1 : Fin M₁), c.encoder ω.1)) :=
    (measurable_of_countable (fun m : Fin M₁ × Fin M₂ ↦ (m.1, c.encoder m))).comp measurable_fst
  have hproj : Measurable (fun (y : Fin n → β₁ × β₂) (j : Fin n) ↦ (y j).2) :=
    measurable_pi_iff.mpr fun j ↦ measurable_snd.comp (measurable_pi_apply j)
  have hY₂m : Measurable
      (fun (ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) (j : Fin n) ↦ bcConverseY₂s j ω) :=
    measurable_pi_iff.mpr fun j ↦ measurable_bcConverseY₂s j
  have h₀ := isMarkovChain_of_compProd_encoder (bcConverseInput M₁ M₂)
    (fun m : Fin M₁ × Fin M₂ ↦ (m.1, c.encoder m)) (measurable_of_countable _)
    (bcConverseKernel c W) ((bcConverseCodeKernel W).comap Prod.snd measurable_snd)
    (fun m ↦ rfl)
  have h₁ := isMarkovChain_swap (bcConverseAmbient c W) Prod.fst _ Prod.snd hfstm hZm hsndm h₀
  have h₂ := isMarkovChain_map_left (bcConverseAmbient c W) Prod.snd _ Prod.fst hsndm hZm hfstm
    hproj h₁
  exact isMarkovChain_swap (bcConverseAmbient c W) _ _ Prod.fst hY₂m hZm hfstm h₂

end Structural

end InformationTheory.Shannon.BroadcastChannel
