import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.CondMutualInfoMixture
import InformationTheory.Shannon.MutualInfo

/-!
# Broadcast channel — from a block code to its ambient law

The canonical ambient probability measure attached to a broadcast block code: a uniform message
pair is passed through the per-letter product channel, and the messages and the two receiver
outputs are read off the resulting measure as coordinate projections.

Read off that measure are the structural hypotheses of the message-level bound
`bc_uv_converse` — memorylessness and the two Markov chains — together with the identification
of the ambient decode error with the code's average error probability; instantiating
`bc_uv_converse` there gives the headline `bc_uv_converse_from_code`.  Two further sections
re-encode the per-letter auxiliary variable onto a single alphabet, for an arbitrary ambient
measure, and then read the letter-`i` five-tuple law off the ambient of a code and identify
each summand of the bound with an information slot of that law.

## Main definitions

* `bcConverseInput` — the uniform law on the message pair.
* `bcConverseKernel` — the per-letter product channel `∏ᵢ W (encoder m i)`, as a kernel in the
  message pair.
* `bcConverseAmbient` — the ambient measure `bcConverseInput ⊗ₘ bcConverseKernel`.
* `bcConverseMsg₁`, `bcConverseMsg₂` — the two message projections.
* `bcConverseYs`, `bcConverseY₁s`, `bcConverseY₂s` — the output-pair projection and its two
  per-receiver components.
* `bcConverseCodeKernel` — the codeword → output-block kernel.
* `bcConverseFanoSlack₁`, `bcConverseFanoSlack₂` — the per-receiver Fano slack of the code.
* `uvPadMap`, `uvUnpadMap` — the re-encoding of the letter-`i` auxiliary alphabet into a
  fixed one, and its left inverse.
* `uvAuxPad` — the letter-`i` auxiliary variable read in that fixed alphabet.
* `uvInfo₁`, `uvInfo₂`, `uvInfoSum₂`, `uvInfoSum₁` — the four information slots of the outer
  bound, as functionals of a five-tuple law `(U, V, X, Y₁, Y₂)`.  The subscript of a sum-rate
  slot names the corner slot it extends, so `uvInfoSum₂` leads with `uvInfo₂` and `uvInfoSum₁`
  with `uvInfo₁`.
* `bcUVTuple` — the letter-`i` five-tuple of the two padded auxiliaries, the input letter and
  the two output letters.
* `bcUVJointDistribution` — the law of that five-tuple under the ambient.

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
* `uvAux_pad_mutualInfo_eq`, `uvAux_pad_condMutualInfo_eq` — re-encoding the auxiliary
  variable into the fixed alphabet changes neither the mutual information it carries about
  an output nor the conditional mutual information it conditions.
* `bc_uv_mutualInfo_eq_uvInfo₁_at`, `bc_uv_mutualInfo_eq_uvInfo₂_at`,
  `bc_uv_sum_eq_uvInfoSum₂_at`, `bc_uv_sum_eq_uvInfoSum₁_at` — each summand of the four
  information slots of the code-level bound is the corresponding information slot of the
  letter's five-tuple law, so the `n`-letter bound is a sum of single-letter quantities.

## Implementation notes

The output block lives on `Fin n → β₁ × β₂`, a sequence of output *pairs*, rather than on a pair
of sequences.  With that choice the message-to-output kernel is literally
`BroadcastCode.blockOutputLaw`, so the product structure over letters is available to the
structural lemmas and the same-letter pair `(Y_{1,i}, Y_{2,i})` is never split; the two
per-receiver output sequences are recovered as further projections.

The alphabet of `uvAux … i` depends on the letter `i`, so different letters produce auxiliary
variables of different types.  `uvAuxPad` moves all of them onto one alphabet by padding the
prefix and the suffix with a default value and keeping `i` as a first component; keeping `i`
is what makes the padding invertible, and invertibility is what turns the data processing
inequality into an equality of informations.

Together with the uniformity and independence statements the four structural lemmas discharge
the structural preconditions of the message-level converse `bc_uv_converse`.  The encoder is
measurable for free because the message pair ranges over a finite type, so the only hypotheses
`bc_uv_converse_from_code` keeps are `2 ≤ M₁` and `2 ≤ M₂`.

The five-tuple carries *both* auxiliaries, because the four information slots split two and
two between them; keeping them in one law is what lets a single distribution witness all four
inequalities.  `uvInfoSum₂` and `uvInfoSum₁` take `[IsFiniteMeasure ν]` since
`condMutualInfo` does, while the two corner slots need nothing beyond measurability.  The four
are declared in the field order of `InBCOuterRegionUV` (`bound₁`, `bound₂`, `sumBound₂`,
`sumBound₁`) rather than by subscript, so that an instantiation reads down the structure.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]
variable {M₁ M₂ n : ℕ}

/-! ## The ambient measure of a broadcast code -/

/-! ### The input law, the channel kernel and the ambient -/

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

/-! ## Structural hypotheses of the message-level converse -/

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

/-! ## Code-level converse and rate extraction -/

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

/-- Receiver-1 Fano slack of a broadcast code: the binary entropy of the ambient decode error
at receiver 1 together with that error probability scaled by `log (M₁ - 1)`.  This is the
additive term by which the message-level converse exceeds the per-letter information sum, and
it tends to zero with the error probability.
@audit:ok -/
noncomputable def bcConverseFanoSlack₁
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) : ℝ :=
  Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
      (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁)
    + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₁
        (fun ω j ↦ bcConverseY₁s j ω) c.decoder₁ * Real.log ((M₁ : ℝ) - 1)

/-- Receiver-2 Fano slack of a broadcast code, the mirror of `bcConverseFanoSlack₁`.
@audit:ok -/
noncomputable def bcConverseFanoSlack₂
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) : ℝ :=
  Real.binEntropy (MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
      (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂)
    + MeasureFano.errorProb (bcConverseAmbient c W) bcConverseMsg₂
        (fun ω j ↦ bcConverseY₂s j ω) c.decoder₂ * Real.log ((M₂ : ℝ) - 1)

section Converse

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

/-- The UV outer bound instantiated at a bare broadcast code: for any two-receiver block code
`c` and Markov channel `W`, the canonical ambient measure `bcConverseAmbient c W` discharges
every hypothesis of the message-level converse `bc_uv_converse`, so the rate pair
`(log M₁, log M₂)` lies in the Nair–El Gamal region determined by the per-letter auxiliaries.
No degradedness is assumed.  The Fano slack is still carried here; it vanishes only in the
`n → ∞` limit.
@audit:ok -/
@[entry_point]
theorem bc_uv_converse_from_code
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCOuterRegionUV (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)).toReal
        + bcConverseFanoSlack₁ c W)
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)).toReal
        + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i))).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i))).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
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
  simp only [Fintype.card_fin] at h
  exact ⟨by simpa only [bcConverseFanoSlack₁, add_assoc] using h.bound₁,
    by simpa only [bcConverseFanoSlack₂, add_assoc] using h.bound₂,
    by simpa only [bcConverseFanoSlack₁, bcConverseFanoSlack₂, add_assoc] using h.sumBound₂,
    by simpa only [bcConverseFanoSlack₁, bcConverseFanoSlack₂, add_assoc] using h.sumBound₁⟩

/-- @audit:ok -/
lemma bc_uv_rate_extract [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ}
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) :
    InBCOuterRegionUV ((n : ℝ) * R₁) ((n : ℝ) * R₂)
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)).toReal
        + bcConverseFanoSlack₁ c W)
      ((∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
            (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)).toReal
        + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i))).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
              (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
            + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
              (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i))).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
  have h := bc_uv_converse_from_code c W hcard₁ hcard₂
  have hlog₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlog₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  exact ⟨hlog₁.trans h.bound₁, hlog₂.trans h.bound₂,
    (add_le_add hlog₁ hlog₂).trans h.sumBound₂,
    (add_le_add hlog₁ hlog₂).trans h.sumBound₁⟩

end Converse

end CodeLevel

/-! ## Fixed-alphabet form of the auxiliary variable -/

section Pad

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ξ : Type*} [MeasurableSpace ξ]
variable {γ : Type*} [MeasurableSpace γ]

/-- Re-encoding of the letter-`i` auxiliary alphabet into one that does not depend on `i`: the
receiver-1 prefix and the receiver-2 suffix are extended to full-length sequences by a default
value, and the letter index is kept as a first component so that the extension can be undone. -/
noncomputable def uvPadMap [Nonempty β₁] [Nonempty β₂] (i : Fin n) :
    ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) →
      Fin n × ξ × (Fin n → β₁) × (Fin n → β₂) :=
  fun p ↦ (i, p.1,
    (fun j ↦ if h : j.val < i.val then p.2.1 ⟨j.val, h⟩ else Classical.arbitrary β₁),
    fun j ↦ if h : i.val < j.val then p.2.2 ⟨j, h⟩ else Classical.arbitrary β₂)

/-- Left inverse of `uvPadMap i`: restrict the two full-length sequences back to the
receiver-1 prefix `Y₁^{<i}` and the receiver-2 suffix `Y₂^{>i}`. -/
def uvUnpadMap (i : Fin n) :
    Fin n × ξ × (Fin n → β₁) × (Fin n → β₂) →
      ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂)) :=
  fun q ↦ (q.2.1,
    (fun j ↦ q.2.2.1 ⟨j.val, j.isLt.trans i.isLt⟩, fun j ↦ q.2.2.2 j.val))

/-- The letter-`i` auxiliary variable of the UV outer bound, re-encoded into the fixed
alphabet `Fin n × ξ × (Fin n → β₁) × (Fin n → β₂)`, which no longer depends on `i`. -/
noncomputable def uvAuxPad [Nonempty β₁] [Nonempty β₂]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂) (i : Fin n) :
    Ω → Fin n × ξ × (Fin n → β₁) × (Fin n → β₂) :=
  fun ω ↦ uvPadMap i (uvAux W Y₁s Y₂s i ω)

omit [MeasurableSpace β₁] [MeasurableSpace β₂] [MeasurableSpace ξ] in
lemma uvUnpadMap_uvPadMap [Nonempty β₁] [Nonempty β₂] (i : Fin n)
    (p : ξ × ((Fin i.val → β₁) × ({j : Fin n // i.val < j.val} → β₂))) :
    uvUnpadMap i (uvPadMap i p) = p := by
  obtain ⟨w, f, g⟩ := p
  simp only [uvPadMap, uvUnpadMap, Prod.mk.injEq, true_and]
  refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_⟩
  · rw [dif_pos j.isLt]
  · rw [dif_pos j.prop]

lemma measurable_uvPadMap [Nonempty β₁] [Nonempty β₂] (i : Fin n) :
    Measurable (uvPadMap (ξ := ξ) (β₁ := β₁) (β₂ := β₂) i) := by
  refine measurable_const.prodMk (measurable_fst.prodMk (Measurable.prodMk ?_ ?_))
  · refine measurable_pi_lambda _ fun j ↦ ?_
    by_cases h : j.val < i.val
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    · simp only [dif_neg h]
      exact measurable_const
  · refine measurable_pi_lambda _ fun j ↦ ?_
    by_cases h : i.val < j.val
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)
    · simp only [dif_neg h]
      exact measurable_const

lemma measurable_uvUnpadMap (i : Fin n) :
    Measurable (uvUnpadMap (ξ := ξ) (β₁ := β₁) (β₂ := β₂) i) := by
  have h₁ : Measurable
      (fun q : Fin n × ξ × (Fin n → β₁) × (Fin n → β₂) ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have h₂ : Measurable
      (fun q : Fin n × ξ × (Fin n → β₁) × (Fin n → β₂) ↦ q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact (measurable_fst.comp measurable_snd).prodMk
    ((measurable_pi_lambda _ fun j ↦ (measurable_pi_apply _).comp h₁).prodMk
      (measurable_pi_lambda _ fun j ↦ (measurable_pi_apply _).comp h₂))

lemma measurable_uvAuxPad [Nonempty β₁] [Nonempty β₂]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (hW : Measurable W) (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (i : Fin n) :
    Measurable (uvAuxPad W Y₁s Y₂s i) :=
  (measurable_uvPadMap i).comp (measurable_uvAux W Y₁s Y₂s hW hY₁s hY₂s i)

lemma uvAux_pad_mutualInfo_eq [Nonempty β₁] [Nonempty β₂]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂) (Yo : Ω → γ)
    (hW : Measurable W) (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hYo : Measurable Yo) (i : Fin n) :
    mutualInfo μ (uvAuxPad W Y₁s Y₂s i) Yo = mutualInfo μ (uvAux W Y₁s Y₂s i) Yo :=
  mutualInfo_eq_of_leftInverse μ (uvAux W Y₁s Y₂s i) Yo
    (measurable_uvAux W Y₁s Y₂s hW hY₁s hY₂s i) hYo
    (measurable_uvPadMap i) (measurable_uvUnpadMap i) (uvUnpadMap_uvPadMap i)

lemma uvAux_pad_mutualInfo_prod_eq [Nonempty β₁] [Nonempty β₂]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (Xs : Ω → α) (Yo : Ω → γ)
    (hW : Measurable W) (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hXs : Measurable Xs) (hYo : Measurable Yo) (i : Fin n) :
    mutualInfo μ (fun ω ↦ (uvAuxPad W Y₁s Y₂s i ω, Xs ω)) Yo
      = mutualInfo μ (fun ω ↦ (uvAux W Y₁s Y₂s i ω, Xs ω)) Yo :=
  mutualInfo_eq_of_leftInverse μ (fun ω ↦ (uvAux W Y₁s Y₂s i ω, Xs ω)) Yo
    ((measurable_uvAux W Y₁s Y₂s hW hY₁s hY₂s i).prodMk hXs) hYo
    (f := fun p ↦ (uvPadMap i p.1, p.2)) (g := fun q ↦ (uvUnpadMap i q.1, q.2))
    ((measurable_uvPadMap i).comp measurable_fst |>.prodMk measurable_snd)
    ((measurable_uvUnpadMap i).comp measurable_fst |>.prodMk measurable_snd)
    (fun a ↦ by rw [uvUnpadMap_uvPadMap i a.1])

lemma uvAux_pad_condMutualInfo_eq [Nonempty β₁] [Nonempty β₂]
    [Fintype ξ] [MeasurableSingletonClass ξ]
    [Fintype β₁] [MeasurableSingletonClass β₁]
    [Fintype β₂] [MeasurableSingletonClass β₂]
    [Fintype γ] [MeasurableSingletonClass γ] [StandardBorelSpace γ] [Nonempty γ]
    [StandardBorelSpace α] [Nonempty α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → ξ) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (Xs : Ω → α) (Yo : Ω → γ)
    (hW : Measurable W) (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hXs : Measurable Xs) (hYo : Measurable Yo) (i : Fin n) :
    condMutualInfo μ Xs Yo (uvAuxPad W Y₁s Y₂s i)
      = condMutualInfo μ Xs Yo (uvAux W Y₁s Y₂s i) := by
  classical
  have hAux := measurable_uvAux W Y₁s Y₂s hW hY₁s hY₂s i
  have hPad := measurable_uvAuxPad W Y₁s Y₂s hW hY₁s hY₂s i
  have hpair := uvAux_pad_mutualInfo_prod_eq μ W Y₁s Y₂s Xs Yo hW hY₁s hY₂s hXs hYo i
  rw [mutualInfo_chain_rule μ Xs Yo (uvAuxPad W Y₁s Y₂s i) hXs hYo hPad,
    mutualInfo_chain_rule μ Xs Yo (uvAux W Y₁s Y₂s i) hXs hYo hAux,
    uvAux_pad_mutualInfo_eq μ W Y₁s Y₂s Yo hW hY₁s hY₂s hYo i] at hpair
  exact (ENNReal.add_right_inj (mutualInfo_ne_top μ _ Yo hAux hYo)).mp hpair

end Pad

/-! ## Per-letter joint law and its information slots -/

section PerLetterInfo

/-! ### The four information slots of a five-tuple law -/

section Slots

variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

/-- Receiver-1 corner information `I(V; Y₁)` of a five-tuple law `(U, V, X, Y₁, Y₂)`.
@audit:ok -/
noncomputable def uvInfo₁ (ν : Measure (U × V × α × β₁ × β₂)) : ℝ≥0∞ :=
  mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)

/-- Receiver-2 corner information `I(U; Y₂)` of a five-tuple law `(U, V, X, Y₁, Y₂)`.
@audit:ok -/
noncomputable def uvInfo₂ (ν : Measure (U × V × α × β₁ × β₂)) : ℝ≥0∞ :=
  mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)

/-- Sum-rate information `I(U; Y₂) + I(X; Y₁ | U)` with the receiver-2 auxiliary leading.
@audit:ok -/
noncomputable def uvInfoSum₂ (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : ℝ≥0∞ :=
  uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)

/-- Sum-rate information `I(V; Y₁) + I(X; Y₂ | V)` with the receiver-1 auxiliary leading.
@audit:ok -/
noncomputable def uvInfoSum₁ (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : ℝ≥0∞ :=
  uvInfo₁ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)

end Slots

/-! ### The per-letter law read off the ambient -/

section Ambient

variable [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/-- The letter-`i` five-tuple of the UV outer bound, read off the ambient: the receiver-2
auxiliary, the receiver-1 auxiliary — both in the fixed alphabet of `uvAuxPad` — the input
letter and the two output letters.
@audit:ok -/
noncomputable def bcUVTuple (c : BroadcastCode M₁ M₂ n α β₁ β₂) (i : Fin n) :
    ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) →
      (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
        (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ :=
  fun ω ↦ (uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i ω,
    uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i ω,
    c.encoder ω.1 i, bcConverseY₁s i ω, bcConverseY₂s i ω)

omit [StandardBorelSpace α] [Nonempty α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
lemma measurable_bcUVTuple (c : BroadcastCode M₁ M₂ n α β₁ β₂) (i : Fin n) :
    Measurable (bcUVTuple c i) :=
  (measurable_uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₂
      measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
    ((measurable_uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₁
        measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
      (((measurable_pi_apply i).comp
            ((measurable_of_countable c.encoder).comp measurable_fst)).prodMk
        ((measurable_bcConverseY₁s i).prodMk (measurable_bcConverseY₂s i))))

/-- The joint law of the letter-`i` five-tuple under the ambient measure of a broadcast code:
the two auxiliaries, the input letter and the two output letters, all pushed forward from
`bcConverseAmbient`.
@audit:ok -/
noncomputable def bcUVJointDistribution
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) (i : Fin n) :
    Measure ((Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂) :=
  (bcConverseAmbient c W).map (bcUVTuple c i)

instance bcUVJointDistribution_isProbabilityMeasure
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    IsProbabilityMeasure (bcUVJointDistribution c W i) := by
  unfold bcUVJointDistribution
  exact Measure.isProbabilityMeasure_map (measurable_bcUVTuple c i).aemeasurable

omit [StandardBorelSpace α] [Nonempty α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
/-- @audit:ok -/
lemma bc_uv_mutualInfo_eq_uvInfo₁_at
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    mutualInfo (bcConverseAmbient c W)
        (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
      = uvInfo₁ (bcUVJointDistribution c W i) := by
  have hmap := mutualInfo_map_comp (bcConverseAmbient c W) (bcUVTuple c i)
    (measurable_bcUVTuple c i)
    (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd)
    (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (uvAux_pad_mutualInfo_eq (bcConverseAmbient c W) bcConverseMsg₁ bcConverseY₁s
    bcConverseY₂s (bcConverseY₁s i) measurable_bcConverseMsg₁ measurable_bcConverseY₁s
    measurable_bcConverseY₂s (measurable_bcConverseY₁s i) i).symm.trans hmap.symm

omit [StandardBorelSpace α] [Nonempty α] [Fintype β₁] [MeasurableSingletonClass β₁]
  [StandardBorelSpace β₁] [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
/-- @audit:ok -/
lemma bc_uv_mutualInfo_eq_uvInfo₂_at
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    mutualInfo (bcConverseAmbient c W)
        (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
      = uvInfo₂ (bcUVJointDistribution c W i) := by
  have hmap := mutualInfo_map_comp (bcConverseAmbient c W) (bcUVTuple c i)
    (measurable_bcUVTuple c i)
    (fun q ↦ q.1) measurable_fst
    (fun q ↦ q.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (uvAux_pad_mutualInfo_eq (bcConverseAmbient c W) bcConverseMsg₂ bcConverseY₁s
    bcConverseY₂s (bcConverseY₂s i) measurable_bcConverseMsg₂ measurable_bcConverseY₁s
    measurable_bcConverseY₂s (measurable_bcConverseY₂s i) i).symm.trans hmap.symm

omit [StandardBorelSpace β₂] in
/-- @audit:ok -/
lemma bc_uv_sum_eq_uvInfoSum₂_at
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    mutualInfo (bcConverseAmbient c W)
          (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
        + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
          (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i)
      = uvInfoSum₂ (bcUVJointDistribution c W i) := by
  have hX : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ c.encoder ω.1 i) :=
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)
  have hmap := condMutualInfo_map_comp (bcConverseAmbient c W) (bcUVTuple c i)
    (measurable_bcUVTuple c i)
    (fun q ↦ q.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun q ↦ q.1) measurable_fst
  have hcmi := (uvAux_pad_condMutualInfo_eq (bcConverseAmbient c W) bcConverseMsg₂
    bcConverseY₁s bcConverseY₂s (fun ω ↦ c.encoder ω.1 i) (bcConverseY₁s i)
    measurable_bcConverseMsg₂ measurable_bcConverseY₁s measurable_bcConverseY₂s hX
    (measurable_bcConverseY₁s i) i).symm.trans hmap.symm
  rw [bc_uv_mutualInfo_eq_uvInfo₂_at c W i, hcmi]
  rfl

omit [StandardBorelSpace β₁] in
/-- @audit:ok -/
lemma bc_uv_sum_eq_uvInfoSum₁_at
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    mutualInfo (bcConverseAmbient c W)
          (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
        + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
          (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i)
      = uvInfoSum₁ (bcUVJointDistribution c W i) := by
  have hX : Measurable (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦ c.encoder ω.1 i) :=
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)
  have hmap := condMutualInfo_map_comp (bcConverseAmbient c W) (bcUVTuple c i)
    (measurable_bcUVTuple c i)
    (fun q ↦ q.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (fun q ↦ q.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd)
  have hcmi := (uvAux_pad_condMutualInfo_eq (bcConverseAmbient c W) bcConverseMsg₁
    bcConverseY₁s bcConverseY₂s (fun ω ↦ c.encoder ω.1 i) (bcConverseY₂s i)
    measurable_bcConverseMsg₁ measurable_bcConverseY₁s measurable_bcConverseY₂s hX
    (measurable_bcConverseY₂s i) i).symm.trans hmap.symm
  rw [bc_uv_mutualInfo_eq_uvInfo₁_at c W i, hcmi]
  rfl

end Ambient

end PerLetterInfo

end InformationTheory.Shannon.BroadcastChannel
