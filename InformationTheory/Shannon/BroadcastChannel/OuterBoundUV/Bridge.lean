import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV
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
* `bcConverse_errorProb₁_eq`, `bcConverse_errorProb₂_eq` — the ambient decode error at a
  receiver is the code's average error probability there.
* `bc_uv_converse_from_code` — the UV outer bound at a bare broadcast code, with the rate pair
  `(log M₁, log M₂)` and the Fano slack still symbolic.
* `bc_uv_rate_extract` — the same bound with the rate pair `(n R₁, n R₂)` of a code whose
  message counts satisfy `⌈exp (n Rₖ)⌉ ≤ Mₖ`.

## Implementation notes

The output block lives on `Fin n → β₁ × β₂`, a sequence of output *pairs*, rather than on a pair
of sequences.  With that choice the message-to-output kernel is literally
`BroadcastCode.blockOutputLaw`, so the product structure over letters is available to the
structural lemmas and the same-letter pair `(Y_{1,i}, Y_{2,i})` is never split; the two
per-receiver output sequences are recovered as further projections.

Together with the uniformity and independence statements the four structural lemmas discharge
the structural preconditions of the message-level converse `bc_uv_converse`.  Instantiating it
at `bcConverseAmbient` still asks the code for the measurability of the encoded letters and for
the two message counts to be at least `2`.
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

lemma bcConverseInput_eq :
    bcConverseInput M₁ M₂ = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton (fun q ↦ ?_)
  obtain ⟨a, b⟩ := q
  have hsgl : ({(a, b)} : Set (Fin M₁ × Fin M₂)) = {a} ×ˢ {b} := by
    ext ⟨x, y⟩; simp [Prod.ext_iff]
  have hR : ((Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count) {(a, b)}
      = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  have hL : (bcConverseInput M₁ M₂) {(a, b)}
      = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ * (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ := by
    unfold bcConverseInput
    rw [hsgl, Measure.prod_prod, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, Measure.count_singleton, Measure.count_singleton, mul_one, mul_one]
  rw [hL, hR, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

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

/-! ### Code-level converse and rate extraction -/

section CodeLevel

variable [Fintype β₁] [MeasurableSingletonClass β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂]

lemma bcConverse_errorProb₁_eq
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
        (fun ω i ↦ bcConverseY₁s i ω) c.decoder₁
      = (c.averageErrorProb₁ W).toReal := by
  have hM : M₁ * M₂ ≠ 0 := Nat.mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)
  set S : Set ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) :=
    {ω | bcConverseMsg₁ ω ≠ c.decoder₁ (fun i ↦ bcConverseY₁s i ω)} with hS_def
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_err : MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
      (fun ω i ↦ bcConverseY₁s i ω) c.decoder₁ = (bcConverseAmbient c W).real S := rfl
  have h_ker : ∀ m : Fin M₁ × Fin M₂,
      (bcConverseKernel c W) m (Prod.mk m ⁻¹' S) = c.errorProbAt₁ W m := by
    intro m
    have h_sec : Prod.mk m ⁻¹' S = c.errorEvent₁ m := by
      ext y
      simp only [Set.mem_preimage, hS_def, Set.mem_setOf_eq, BroadcastCode.errorEvent₁,
        bcConverseMsg₁, bcConverseY₁s]
      exact ne_comm
    rw [h_sec]
    rfl
  have h_measure : (bcConverseAmbient c W) S = c.averageErrorProb₁ W := by
    rw [bcConverseAmbient, Measure.compProd_apply hS_meas]
    simp_rw [h_ker]
    rw [bcConverseInput_eq, lintegral_smul_measure, lintegral_count, tsum_fintype,
      BroadcastCode.averageErrorProb₁, if_neg hM, smul_eq_mul]
    congr 1
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  rw [h_err, measureReal_def, h_measure]

lemma bcConverse_errorProb₂_eq
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
        (fun ω i ↦ bcConverseY₂s i ω) c.decoder₂
      = (c.averageErrorProb₂ W).toReal := by
  have hM : M₁ * M₂ ≠ 0 := Nat.mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)
  set S : Set ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) :=
    {ω | bcConverseMsg₂ ω ≠ c.decoder₂ (fun i ↦ bcConverseY₂s i ω)} with hS_def
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h_err : MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
      (fun ω i ↦ bcConverseY₂s i ω) c.decoder₂ = (bcConverseAmbient c W).real S := rfl
  have h_ker : ∀ m : Fin M₁ × Fin M₂,
      (bcConverseKernel c W) m (Prod.mk m ⁻¹' S) = c.errorProbAt₂ W m := by
    intro m
    have h_sec : Prod.mk m ⁻¹' S = c.errorEvent₂ m := by
      ext y
      simp only [Set.mem_preimage, hS_def, Set.mem_setOf_eq, BroadcastCode.errorEvent₂,
        bcConverseMsg₂, bcConverseY₂s]
      exact ne_comm
    rw [h_sec]
    rfl
  have h_measure : (bcConverseAmbient c W) S = c.averageErrorProb₂ W := by
    rw [bcConverseAmbient, Measure.compProd_apply hS_meas]
    simp_rw [h_ker]
    rw [bcConverseInput_eq, lintegral_smul_measure, lintegral_count, tsum_fintype,
      BroadcastCode.averageErrorProb₂, if_neg hM, smul_eq_mul]
    congr 1
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  rw [h_err, measureReal_def, h_measure]

section Converse

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

/-- The UV outer bound instantiated at a bare broadcast code: for any two-receiver block code
`c` and Markov channel `W`, the canonical ambient measure `bcConverseAmbient c W` discharges
every hypothesis of the message-level converse `bc_uv_converse`, so the rate pair
`(log M₁, log M₂)` lies in the Nair–El Gamal region determined by the per-letter auxiliaries.
No degradedness is assumed.  The Fano slack is still carried here; it vanishes only in the
`n → ∞` limit. -/
@[entry_point]
theorem bc_uv_converse_from_code
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCOuterRegionUV (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)).toReal
        + Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
            (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
        + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
            (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1))
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)).toReal
        + Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
            (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
        + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
            (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1))
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i))).toReal
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1))
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1)))
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i))).toReal
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1))
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1))) := by
  have h := bc_uv_converse (bcConverseAmbient c W) bcConverseMsg₁ bcConverseMsg₂
    (fun j ω ↦ c.encoder ω.1 j) bcConverseY₁s bcConverseY₂s c.decoder₁ c.decoder₂
    measurable_bcConverseMsg₁ measurable_bcConverseMsg₂
    (fun j ↦ (measurable_pi_apply j).comp
      ((measurable_of_countable c.encoder).comp measurable_fst))
    measurable_bcConverseY₁s measurable_bcConverseY₂s
    (bcConverseMsg₁_uniform c W) (bcConverseMsg₂_uniform c W)
    (by simpa only [Fintype.card_fin] using hcard₁)
    (by simpa only [Fintype.card_fin] using hcard₂)
    (bcConverse_mutualInfo_eq_zero c W)
    (bcConverse_memoryless₁ c W) (bcConverse_memoryless₂ c W)
    (bcConverse_isMarkovChain₁ c W) (bcConverse_isMarkovChain₂ c W)
  simpa only [Fintype.card_fin] using h

lemma bc_uv_rate_extract [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ}
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) :
    InBCOuterRegionUV ((n : ℝ) * R₁) ((n : ℝ) * R₂)
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)).toReal
        + Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
            (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
        + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
            (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1))
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)).toReal
        + Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
            (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
        + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
            (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1))
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i))).toReal
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1))
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1)))
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i))).toReal
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
              (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1))
        + (Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
            + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
              (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1))) := by
  have h := bc_uv_converse_from_code c W hcard₁ hcard₂
  have hlog₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlog₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  exact ⟨hlog₁.trans h.bound₁, hlog₂.trans h.bound₂,
    (add_le_add hlog₁ hlog₂).trans h.sumBound₂,
    (add_le_add hlog₁ hlog₂).trans h.sumBound₁⟩

end Converse

end CodeLevel

end InformationTheory.Shannon.BroadcastChannel
