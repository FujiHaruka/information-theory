import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Basic
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.Pi
import InformationTheory.Shannon.ChannelCoding.ConverseMemoryless
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessMarkov

/-!
# Multiple access channel — converse (outer bound)

The converse to the MAC coding theorem (Cover–Thomas Thm 15.3.1, eq. 15.85–15.90):
for uniformly distributed, independent messages decoded by a joint decoder, the rate pair
satisfies the three corner-point inequalities of `InMACCapacityRegion`.

Each of the three bounds is the **message-level Fano converse**, obtained from the
encoder-free single-shot converse `shannon_converse_single_shot` by placing the
conditioning message in the *output* slot:

* user 1: `log |M₁| ≤ I(M₁; (M₂, Yⁿ)) + h(Pe₁) + Pe₁ log(|M₁| − 1)`
* user 2: `log |M₂| ≤ I(M₂; (M₁, Yⁿ)) + h(Pe₂) + Pe₂ log(|M₂| − 1)`
* sum:    `log |M₁| + log |M₂| ≤ I((M₁, M₂); Yⁿ) + h(Pe) + Pe log(|M₁·M₂| − 1)`

Here `I(M₁; (M₂, Yⁿ)) = I(M₁; Yⁿ | M₂)` under message independence, the standard converse
intermediate. The single-letterization to the channel quantities `I(X₁; Y | X₂)` etc. is a
separate refinement, tracked in `mac-moonshot-plan.md` (Phase A2).

## Main statements

* `mac_converse_bound₁` / `mac_converse_bound₂` / `mac_converse_bound_sum` — the three
  corner-point inequalities.
* `mac_converse_message_level` — the packaged `InMACCapacityRegion` outer bound.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [MeasurableSpace α₁] [MeasurableSpace α₂]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
variable {M₁ M₂ n : ℕ}

/-- **MAC converse, user-1 corner bound** (message level): under a uniform message `Msg₁`,
`log |M₁| ≤ I(M₁; (M₂, Yⁿ)) + h(Pe₁) + Pe₁ · log(|M₁| − 1)`, where the user-1 error
probability `Pe₁` is measured against the joint decoder's first component. -/
theorem mac_converse_bound₁
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₁_uniform : μ.map Msg₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) :
    Real.log (M₁ : ℝ) ≤
      (mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₁) := ⟨⟨0, by omega⟩⟩
  set Yo : Ω → Fin M₂ × (Fin n → β) := fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω) with hYo_def
  have hYo : Measurable Yo := hMsg₂.prodMk (measurable_pi_iff.mpr hYs)
  have hdec : Measurable (fun p : Fin M₂ × (Fin n → β) ↦ (c.decoder p.2).1) :=
    measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₁) := by rw [Fintype.card_fin]; exact hcard₁
  have hMI_fin : mutualInfo μ Msg₁ Yo ≠ ∞ := mutualInfo_ne_top μ Msg₁ Yo hMsg₁ hYo
  have h := shannon_converse_single_shot μ Msg₁ Yo
    (fun p ↦ (c.decoder p.2).1) hMsg₁ hYo hdec hMsg₁_uniform hcard hMI_fin
  rw [Fintype.card_fin] at h
  exact h

/-- **MAC converse, user-2 corner bound** (message level): symmetric to
`mac_converse_bound₁`. -/
theorem mac_converse_bound₂
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₂_uniform : μ.map Msg₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₂ : 2 ≤ M₂) :
    Real.log (M₂ : ℝ) ≤
      (mutualInfo μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₂) := ⟨⟨0, by omega⟩⟩
  set Yo : Ω → Fin M₁ × (Fin n → β) := fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω) with hYo_def
  have hYo : Measurable Yo := hMsg₁.prodMk (measurable_pi_iff.mpr hYs)
  have hdec : Measurable (fun p : Fin M₁ × (Fin n → β) ↦ (c.decoder p.2).2) :=
    measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₂) := by rw [Fintype.card_fin]; exact hcard₂
  have hMI_fin : mutualInfo μ Msg₂ Yo ≠ ∞ := mutualInfo_ne_top μ Msg₂ Yo hMsg₂ hYo
  have h := shannon_converse_single_shot μ Msg₂ Yo
    (fun p ↦ (c.decoder p.2).2) hMsg₂ hYo hdec hMsg₂_uniform hcard hMI_fin
  rw [Fintype.card_fin] at h
  exact h

/-- **MAC converse, sum-rate bound** (message level): treating the pair `(M₁, M₂)` as a
single uniform message decoded jointly,
`log |M₁| + log |M₂| ≤ I((M₁, M₂); Yⁿ) + h(Pe) + Pe · log(|M₁·M₂| − 1)`. -/
theorem mac_converse_bound_sum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₁₂_uniform :
      μ.map (fun ω ↦ (Msg₁ ω, Msg₂ ω))
        = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) ≤
      (mutualInfo μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder)
        + MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set Msg : Ω → Fin M₁ × Fin M₂ := fun ω ↦ (Msg₁ ω, Msg₂ ω) with hMsg_def
  set Yo : Ω → Fin n → β := fun ω i ↦ Ys i ω with hYo_def
  have hMsg : Measurable Msg := hMsg₁.prodMk hMsg₂
  have hYo : Measurable Yo := measurable_pi_iff.mpr hYs
  have hdec : Measurable c.decoder := measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₁ × Fin M₂) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; nlinarith [hcard₁, hcard₂]
  have hMI_fin : mutualInfo μ Msg Yo ≠ ∞ := mutualInfo_ne_top μ Msg Yo hMsg hYo
  have h := shannon_converse_single_shot μ Msg Yo c.decoder hMsg hYo hdec
    hMsg₁₂_uniform hcard hMI_fin
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  have hM₁ne : (M₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM₂ne : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Real.log ((M₁ * M₂ : ℕ) : ℝ) = Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hM₁ne hM₂ne]
  rw [hlog] at h
  exact h

/-- **MAC converse — message-level Fano outer bound**: for uniform messages decoded by a
joint decoder, the rate pair `(log |M₁|, log |M₂|)` satisfies the three message-level Fano
information bounds, packaged as `InMACCapacityRegion`.

This is the **message-level step only**: the information slots are the n-letter
message–output mutual informations, not the single-letter channel quantities
`I(X₁; Y | X₂)` etc. The single-letterization that turns this into the textbook MAC
converse (Cover–Thomas Thm 15.3.1) is not yet done; it is tracked in
`mac-moonshot-plan.md` (Phase A2). -/
@[entry_point]
theorem mac_converse_message_level
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₁_uniform : μ.map Msg₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hMsg₂_uniform : μ.map Msg₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hMsg₁₂_uniform :
      μ.map (fun ω ↦ (Msg₁ ω, Msg₂ ω))
        = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InMACCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1))
      ((mutualInfo μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1))
      ((mutualInfo μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder)
        + MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1)) :=
  ⟨mac_converse_bound₁ μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs hMsg₁_uniform hcard₁,
   mac_converse_bound₂ μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs hMsg₂_uniform hcard₂,
   mac_converse_bound_sum μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs hMsg₁₂_uniform hcard₁ hcard₂⟩

/-! ## Phase A2 — single-letterization (genuine frontier)

The genuine MAC converse bridges the message-level mutual informations of
`mac_converse_message_level` down to the single-letter channel quantities
`I(X₁ᵢ; Yᵢ | X₂ᵢ)` etc.  The decisive analytic atom is the **conditional
single-letterization** of the block input–output mutual information; the operational
link from the message-level MI to the block input MI uses the standard data-processing
and conditioning identities under a memoryless channel.

This mirrors the single-user `mutualInfo_le_sum_per_letter_of_memoryless_strong`
(`CondEntropyMemoryless.lean`) lifted to a conditional form with the other user's input
`X₂ⁿ` sitting in the conditioner throughout. -/

section SingleLetterization

open InformationTheory.Shannon.ChannelCodingConverseGeneral

variable [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
variable [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
variable [DecidableEq β] [Nonempty β] [StandardBorelSpace β]

omit [DecidableEq β] [StandardBorelSpace β] in
/-- **Conditional subadditivity** of conditional entropy across a memoryless block:
`H(Yⁿ | Zⁿ) ≤ ∑ᵢ H(Yᵢ | Zᵢ)`.  Holds for any inputs `Zs` (no memoryless assumption
needed); the per-letter conditioner `Zᵢ` is a coarsening of the block conditioner
`(Zⁿ, Y^{<i})`, so conditioning-reduces-entropy gives each summand bound. -/
lemma condEntropy_pi_le_sum_condEntropy
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
      [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Zs : Fin n → Ω → γ) (Ys : Fin n → Ω → β)
    (hZs : ∀ i, Measurable (Zs i)) (hYs : ∀ i, Measurable (Ys i)) :
    MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω j ↦ Zs j ω)
      ≤ ∑ i : Fin n, MeasureFano.condEntropy μ (Ys i) (Zs i) := by
  classical
  have hZpi : Measurable (fun ω j ↦ Zs j ω) := measurable_pi_iff.mpr hZs
  rw [condEntropy_pi_chain_rule μ (fun ω j ↦ Zs j ω) Ys hZpi hYs]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  set Zpref : Ω → (Fin i.val → β) :=
    fun ω (j : Fin i.val) ↦ Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω with hZpref_def
  have hZpref : Measurable Zpref :=
    measurable_pi_iff.mpr (fun j ↦ hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  -- Step 1: drop the output prefix `Y^{<i}` from the conditioner.
  have h1 : MeasureFano.condEntropy μ (Ys i) (fun ω ↦ ((fun j ↦ Zs j ω), Zpref ω))
      ≤ MeasureFano.condEntropy μ (Ys i) (fun ω j ↦ Zs j ω) :=
    condEntropy_le_condEntropy_of_pair μ (Ys i) (fun ω j ↦ Zs j ω) Zpref
      (hYs i) hZpi hZpref
  -- Step 2: drop the other inputs `Z^{≠i}` from the conditioner (extract `Zᵢ`).
  have hZrest : Measurable (fun ω (j : {j : Fin n // j ≠ i}) ↦ Zs j.val ω) :=
    measurable_pi_iff.mpr (fun j ↦ hZs j.val)
  let e : γ × ({j : Fin n // j ≠ i} → γ) ≃ᵐ (Fin n → γ) :=
    (measurableEquivExtract (β := γ) i).symm
  have h_reshape : (fun ω j ↦ Zs j ω)
      = fun ω ↦ e (Zs i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Zs j.val ω) := by
    funext ω j
    show Zs j ω = e (Zs i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Zs j.val ω) j
    by_cases hj : j = i
    · subst hj
      simp [e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr]
    · simp [e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, hj]
  have h2 : MeasureFano.condEntropy μ (Ys i) (fun ω j ↦ Zs j ω)
      ≤ MeasureFano.condEntropy μ (Ys i) (Zs i) := by
    rw [h_reshape,
      condEntropy_measurableEquiv_comp μ (Ys i) (hYs i)
        (fun ω ↦ (Zs i ω, fun (j : {j : Fin n // j ≠ i}) ↦ Zs j.val ω))
        ((hZs i).prodMk hZrest) e]
    exact condEntropy_le_condEntropy_of_pair μ (Ys i) (Zs i)
      (fun ω (j : {j : Fin n // j ≠ i}) ↦ Zs j.val ω) (hYs i) (hZs i) hZrest
  exact h1.trans h2

omit [DecidableEq α₁] [DecidableEq β] in
/-- **Conditional single-letterization** (the decisive atom): under a strong memoryless
channel on the joint input `(X₁ᵢ, X₂ᵢ)`,
`I(X₁ⁿ; Yⁿ | X₂ⁿ) ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ)` (as reals). -/
lemma condMutualInfo_singleletter_le_of_memoryless
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X₁s : Fin n → Ω → α₁) (X₂s : Fin n → Ω → α₂) (Ys : Fin n → Ω → β)
    (hX₁s : ∀ i, Measurable (X₁s i)) (hX₂s : ∀ i, Measurable (X₂s i))
    (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter : ∀ i : Fin n,
      IsMarkovChain μ (fun ω j ↦ (X₁s j ω, X₂s j ω))
        (fun ω ↦ (X₁s i ω, X₂s i ω)) (Ys i))
    (h_outputs : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω (j : {j : Fin n // j ≠ i}) ↦ Ys j.val ω)
        (fun ω j ↦ (X₁s j ω, X₂s j ω)) (Ys i)) :
    (condMutualInfo μ (fun ω j ↦ X₁s j ω) (fun ω j ↦ Ys j ω)
        (fun ω j ↦ X₂s j ω)).toReal
      ≤ ∑ i : Fin n,
          (condMutualInfo μ (X₁s i) (Ys i) (X₂s i)).toReal := by
  classical
  have hX₁pi : Measurable (fun ω j ↦ X₁s j ω) := measurable_pi_iff.mpr hX₁s
  have hX₂pi : Measurable (fun ω j ↦ X₂s j ω) := measurable_pi_iff.mpr hX₂s
  have hYpi : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  have hJoint : ∀ i, Measurable (fun ω ↦ (X₁s i ω, X₂s i ω)) := fun i ↦
    (hX₁s i).prodMk (hX₂s i)
  have h21pi : Measurable
      (fun ω ↦ ((fun j ↦ X₂s j ω), (fun j ↦ X₁s j ω))) := hX₂pi.prodMk hX₁pi
  -- Bridge `I(X₁ⁿ; Yⁿ | X₂ⁿ) = H(Yⁿ | X₂ⁿ) − H(Yⁿ | (X₂ⁿ, X₁ⁿ))`.
  have hLHS : (condMutualInfo μ (fun ω j ↦ X₁s j ω) (fun ω j ↦ Ys j ω)
        (fun ω j ↦ X₂s j ω)).toReal
      = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω j ↦ X₂s j ω)
        - MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ ((fun j ↦ X₂s j ω), (fun j ↦ X₁s j ω))) := by
    rw [condMutualInfo_comm μ (fun ω j ↦ X₁s j ω) (fun ω j ↦ Ys j ω)
      (fun ω j ↦ X₂s j ω) hX₁pi hYpi hX₂pi]
    exact condMutualInfo_eq_condEntropy_sub_condEntropy μ (fun ω j ↦ Ys j ω)
      (fun ω j ↦ X₂s j ω) (fun ω j ↦ X₁s j ω) hYpi hX₂pi hX₁pi
  -- Memoryless: `H(Yⁿ | (X₁ⁿ, X₂ⁿ)) = ∑ᵢ H(Yᵢ | (X₁ᵢ, X₂ᵢ))`.
  have hMemo : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
        (fun ω j ↦ (X₁s j ω, X₂s j ω))
      = ∑ i : Fin n,
          MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₁s i ω, X₂s i ω)) :=
    condEntropy_pi_eq_sum_of_memoryless_strong μ
      (fun i ω ↦ (X₁s i ω, X₂s i ω)) Ys hJoint hYs h_per_letter h_outputs
  -- Reshape the joint conditioner `(X₂ⁿ, X₁ⁿ)` into the pi-of-pairs `(X₁ᵢ, X₂ᵢ)ⁿ`.
  have hReshape : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
        (fun ω ↦ ((fun j ↦ X₂s j ω), (fun j ↦ X₁s j ω)))
      = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω j ↦ (X₁s j ω, X₂s j ω)) := by
    let E : (Fin n → α₂) × (Fin n → α₁) ≃ᵐ (Fin n → α₁ × α₂) :=
      (MeasurableEquiv.prodComm
          (α := Fin n → α₂) (β := Fin n → α₁)).trans
        (MeasurableEquiv.arrowProdEquivProdArrow α₁ α₂ (Fin n)).symm
    have hE : (fun ω j ↦ (X₁s j ω, X₂s j ω))
        = fun ω ↦ E ((fun j ↦ X₂s j ω), (fun j ↦ X₁s j ω)) := by
      funext ω j
      simp [E, MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.prodComm]
    rw [hE]
    exact (condEntropy_measurableEquiv_comp μ (fun ω j ↦ Ys j ω) hYpi
      (fun ω ↦ ((fun j ↦ X₂s j ω), (fun j ↦ X₁s j ω))) h21pi E).symm
  -- Per-letter swap `H(Yᵢ | (X₁ᵢ, X₂ᵢ)) = H(Yᵢ | (X₂ᵢ, X₁ᵢ))`.
  have hSwap : ∀ i : Fin n,
      MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₁s i ω, X₂s i ω))
        = MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₂s i ω, X₁s i ω)) := by
    intro i
    have hE : (fun ω ↦ (X₁s i ω, X₂s i ω))
        = fun ω ↦ (MeasurableEquiv.prodComm (α := α₂) (β := α₁)) (X₂s i ω, X₁s i ω) := by
      funext ω; simp [MeasurableEquiv.prodComm]
    rw [hE]
    exact condEntropy_measurableEquiv_comp μ (Ys i) (hYs i)
      (fun ω ↦ (X₂s i ω, X₁s i ω)) ((hX₂s i).prodMk (hX₁s i))
      (MeasurableEquiv.prodComm (α := α₂) (β := α₁))
  -- Per-letter bridge `I(X₁ᵢ; Yᵢ | X₂ᵢ) = H(Yᵢ | X₂ᵢ) − H(Yᵢ | (X₂ᵢ, X₁ᵢ))`.
  have hRHS : ∀ i : Fin n,
      (condMutualInfo μ (X₁s i) (Ys i) (X₂s i)).toReal
        = MeasureFano.condEntropy μ (Ys i) (X₂s i)
          - MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₂s i ω, X₁s i ω)) := by
    intro i
    rw [condMutualInfo_comm μ (X₁s i) (Ys i) (X₂s i) (hX₁s i) (hYs i) (hX₂s i)]
    exact condMutualInfo_eq_condEntropy_sub_condEntropy μ (Ys i) (X₂s i) (X₁s i)
      (hYs i) (hX₂s i) (hX₁s i)
  -- Conditional subadditivity `H(Yⁿ | X₂ⁿ) ≤ ∑ᵢ H(Yᵢ | X₂ᵢ)`.
  have hSub : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω j ↦ X₂s j ω)
      ≤ ∑ i : Fin n, MeasureFano.condEntropy μ (Ys i) (X₂s i) :=
    condEntropy_pi_le_sum_condEntropy μ X₂s Ys hX₂s hYs
  -- Assemble.
  rw [hLHS, hReshape, hMemo]
  have hrhs_eq : (∑ i : Fin n, (condMutualInfo μ (X₁s i) (Ys i) (X₂s i)).toReal)
      = (∑ i : Fin n, MeasureFano.condEntropy μ (Ys i) (X₂s i))
        - (∑ i : Fin n,
            MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₂s i ω, X₁s i ω))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ hRHS i)
  have hswap_sum :
      (∑ i : Fin n, MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₁s i ω, X₂s i ω)))
        = ∑ i : Fin n, MeasureFano.condEntropy μ (Ys i) (fun ω ↦ (X₂s i ω, X₁s i ω)) :=
    Finset.sum_congr rfl (fun i _ ↦ hSwap i)
  rw [hrhs_eq, hswap_sum]
  linarith [hSub]

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **Operational link** (steps 1–2): under message independence and the block channel
Markov chain `(M₁, M₂) → (X₁ⁿ, X₂ⁿ) → Yⁿ`, the message-level mutual information is bounded
by the block input–output conditional mutual information,
`I(M₁; (M₂, Yⁿ)) ≤ I(X₁ⁿ; Yⁿ | X₂ⁿ)`.

Step 1 (`I(M₁; (M₂, Yⁿ)) = I(M₁; Yⁿ | M₂)` via the Y-axis chain rule and message
independence) is the first half.  Step 2 (the data-processing reduction
`I(M₁; Yⁿ | M₂) ≤ I(X₁ⁿ; Yⁿ | X₂ⁿ)`) lowers both the data variable `M₁ → X₁ⁿ` and the
conditioner `M₂ → X₂ⁿ` (each a deterministic function of the message) under the block channel
Markov chain.  It is carried out on the entropy difference: `I(·;·|·) = H(Yⁿ|·) − H(Yⁿ|·,·)`,
with `H(Yⁿ | (M₂, M₁)) = H(Yⁿ | (X₂ⁿ, X₁ⁿ))` (deterministic encoders plus the block Markov
chain) and `H(Yⁿ | M₂) ≤ H(Yⁿ | X₂ⁿ)` (conditioning on the finer message reduces entropy). -/
lemma mac_message_le_condMI
    [NeZero M₁] [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (h_indep : mutualInfo μ Msg₁ Msg₂ = 0)
    (hmarkov : IsMarkovChain μ (fun ω ↦ (Msg₁ ω, Msg₂ ω))
      (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
      (fun ω j ↦ Ys j ω)) :
    (mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))).toReal
      ≤ (condMutualInfo μ (fun ω j ↦ c.encoder₁ (Msg₁ ω) j) (fun ω j ↦ Ys j ω)
          (fun ω j ↦ c.encoder₂ (Msg₂ ω) j)).toReal := by
  classical
  have hYpi : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  -- Step 1: `I(M₁; (M₂, Yⁿ)) = I(M₁; Yⁿ | M₂)`.
  have hstep1 : mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
      = condMutualInfo μ Msg₁ (fun ω j ↦ Ys j ω) Msg₂ := by
    rw [mutualInfo_comm μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω)) hMsg₁
      (hMsg₂.prodMk hYpi)]
    rw [mutualInfo_chain_rule μ (fun ω j ↦ Ys j ω) Msg₁ Msg₂ hYpi hMsg₁ hMsg₂]
    rw [mutualInfo_comm μ Msg₂ Msg₁ hMsg₂ hMsg₁, h_indep, zero_add]
    exact condMutualInfo_comm μ (fun ω j ↦ Ys j ω) Msg₁ Msg₂ hYpi hMsg₁ hMsg₂
  rw [hstep1]
  -- Step 2: data-processing reduction `I(M₁; Yⁿ | M₂) ≤ I(X₁ⁿ; Yⁿ | X₂ⁿ)`, via the entropy
  -- route.  `X₁ⁿ`/`X₂ⁿ` are deterministic encoders of `M₁`/`M₂`, so conditioning on the
  -- (finer) messages dominates conditioning on the (coarser) codewords.
  have hX₁ : Measurable (fun ω j ↦ c.encoder₁ (Msg₁ ω) j) :=
    (measurable_of_countable c.encoder₁).comp hMsg₁
  have hX₂ : Measurable (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) :=
    (measurable_of_countable c.encoder₂).comp hMsg₂
  -- Entropy-difference bridges for both conditional mutual informations.
  have hLbridge : (condMutualInfo μ Msg₁ (fun ω j ↦ Ys j ω) Msg₂).toReal
      = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) Msg₂
        - MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₂ ω, Msg₁ ω)) := by
    rw [condMutualInfo_comm μ Msg₁ (fun ω j ↦ Ys j ω) Msg₂ hMsg₁ hYpi hMsg₂]
    exact condMutualInfo_eq_condEntropy_sub_condEntropy μ (fun ω j ↦ Ys j ω) Msg₂ Msg₁
      hYpi hMsg₂ hMsg₁
  have hRbridge : (condMutualInfo μ (fun ω j ↦ c.encoder₁ (Msg₁ ω) j) (fun ω j ↦ Ys j ω)
        (fun ω j ↦ c.encoder₂ (Msg₂ ω) j)).toReal
      = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω j ↦ c.encoder₂ (Msg₂ ω) j)
        - MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), (fun j ↦ c.encoder₁ (Msg₁ ω) j))) := by
    rw [condMutualInfo_comm μ (fun ω j ↦ c.encoder₁ (Msg₁ ω) j) (fun ω j ↦ Ys j ω)
      (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) hX₁ hYpi hX₂]
    exact condMutualInfo_eq_condEntropy_sub_condEntropy μ (fun ω j ↦ Ys j ω)
      (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) (fun ω j ↦ c.encoder₁ (Msg₁ ω) j) hYpi hX₂ hX₁
  rw [hLbridge, hRbridge]
  -- OL-2: `H(Yⁿ | M₂) ≤ H(Yⁿ | X₂ⁿ)`  (`X₂ⁿ = enc₂ ∘ M₂` is a coarsening of `M₂`).
  have hOL2 : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) Msg₂
      ≤ MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) := by
    have hmk : IsMarkovChain μ (fun ω j ↦ Ys j ω) Msg₂ (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) :=
      isMarkovChain_comp_conditioner_right μ (fun ω j ↦ Ys j ω) Msg₂ hYpi hMsg₂
        (measurable_of_countable c.encoder₂)
    have hdrop : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ (Msg₂ ω, (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
        = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) Msg₂ :=
      condEntropy_drop_irrelevant_of_markov μ (fun ω j ↦ Ys j ω) Msg₂
        (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) hYpi hMsg₂ hX₂ hmk
    have hpair_le : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), Msg₂ ω))
        ≤ MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) :=
      condEntropy_le_condEntropy_of_pair μ (fun ω j ↦ Ys j ω)
        (fun ω j ↦ c.encoder₂ (Msg₂ ω) j) Msg₂ hYpi hX₂ hMsg₂
    have hreshape : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), Msg₂ ω))
        = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ (Msg₂ ω, (fun j ↦ c.encoder₂ (Msg₂ ω) j))) := by
      have hE : (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), Msg₂ ω))
          = fun ω ↦ (MeasurableEquiv.prodComm (α := Fin M₂) (β := Fin n → α₂))
              (Msg₂ ω, (fun j ↦ c.encoder₂ (Msg₂ ω) j)) := by
        funext ω; simp [MeasurableEquiv.prodComm]
      rw [hE]
      exact condEntropy_measurableEquiv_comp μ (fun ω j ↦ Ys j ω) hYpi
        (fun ω ↦ (Msg₂ ω, (fun j ↦ c.encoder₂ (Msg₂ ω) j))) (hMsg₂.prodMk hX₂)
        (MeasurableEquiv.prodComm (α := Fin M₂) (β := Fin n → α₂))
    linarith [hdrop, hpair_le, hreshape]
  -- OL-1: `H(Yⁿ | (M₂, M₁)) = H(Yⁿ | (X₂ⁿ, X₁ⁿ))`.  Both conditioners carry the same
  -- information once the deterministic encoders and the block channel Markov chain are used.
  have hOL1 : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₂ ω, Msg₁ ω))
      = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), (fun j ↦ c.encoder₁ (Msg₁ ω) j))) := by
    -- Reshape A: H(Yⁿ | (M₂, M₁)) = H(Yⁿ | (M₁, M₂)).
    have hreshapeA : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₂ ω, Msg₁ ω))
        = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₁ ω, Msg₂ ω)) := by
      have hE : (fun ω ↦ (Msg₂ ω, Msg₁ ω))
          = fun ω ↦ (MeasurableEquiv.prodComm (α := Fin M₁) (β := Fin M₂)) (Msg₁ ω, Msg₂ ω) := by
        funext ω; simp [MeasurableEquiv.prodComm]
      rw [hE]
      exact condEntropy_measurableEquiv_comp μ (fun ω j ↦ Ys j ω) hYpi
        (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (hMsg₁.prodMk hMsg₂)
        (MeasurableEquiv.prodComm (α := Fin M₁) (β := Fin M₂))
    -- Reshape B: H(Yⁿ | (X₂ⁿ, X₁ⁿ)) = H(Yⁿ | (X₁ⁿ, X₂ⁿ)).
    have hreshapeB : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), (fun j ↦ c.encoder₁ (Msg₁ ω) j)))
        = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))) := by
      have hE : (fun ω ↦ ((fun j ↦ c.encoder₂ (Msg₂ ω) j), (fun j ↦ c.encoder₁ (Msg₁ ω) j)))
          = fun ω ↦ (MeasurableEquiv.prodComm (α := Fin n → α₁) (β := Fin n → α₂))
              ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)) := by
        funext ω; simp [MeasurableEquiv.prodComm]
      rw [hE]
      exact condEntropy_measurableEquiv_comp μ (fun ω j ↦ Ys j ω) hYpi
        (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
        (hX₁.prodMk hX₂) (MeasurableEquiv.prodComm (α := Fin n → α₁) (β := Fin n → α₂))
    -- Core: H(Yⁿ | (M₁, M₂)) = H(Yⁿ | (X₁ⁿ, X₂ⁿ)) in the natural order matching `hmarkov`.
    have hcore : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₁ ω, Msg₂ ω))
        = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))) := by
      -- Add the codewords (deterministic function of the messages).
      have hmk1 : IsMarkovChain μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₁ ω, Msg₂ ω))
          (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))) :=
        isMarkovChain_comp_conditioner_right μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₁ ω, Msg₂ ω))
          hYpi (hMsg₁.prodMk hMsg₂)
          (measurable_of_countable
            (fun p : Fin M₁ × Fin M₂ ↦
              ((fun j ↦ c.encoder₁ p.1 j), (fun j ↦ c.encoder₂ p.2 j))))
      have hadd : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ ((Msg₁ ω, Msg₂ ω),
              ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))))
          = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₁ ω, Msg₂ ω)) :=
        condEntropy_drop_irrelevant_of_markov μ (fun ω j ↦ Ys j ω) (fun ω ↦ (Msg₁ ω, Msg₂ ω))
          (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
          hYpi (hMsg₁.prodMk hMsg₂) (hX₁.prodMk hX₂) hmk1
      -- Drop the messages under the swapped block channel Markov chain `Yⁿ → (X₁ⁿ,X₂ⁿ) → (M₁,M₂)`.
      have hmk2 : IsMarkovChain μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
          (fun ω ↦ (Msg₁ ω, Msg₂ ω)) :=
        isMarkovChain_swap μ (fun ω ↦ (Msg₁ ω, Msg₂ ω))
          (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
          (fun ω j ↦ Ys j ω) (hMsg₁.prodMk hMsg₂) (hX₁.prodMk hX₂) hYpi hmarkov
      have hdropM : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ (((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)),
              (Msg₁ ω, Msg₂ ω)))
          = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))) :=
        condEntropy_drop_irrelevant_of_markov μ (fun ω j ↦ Ys j ω)
          (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
          (fun ω ↦ (Msg₁ ω, Msg₂ ω)) hYpi (hX₁.prodMk hX₂) (hMsg₁.prodMk hMsg₂) hmk2
      -- Reshape the conditioner ((M₁,M₂),(X₁ⁿ,X₂ⁿ)) → ((X₁ⁿ,X₂ⁿ),(M₁,M₂)).
      have hswapcond : MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ ((Msg₁ ω, Msg₂ ω),
              ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))))
          = MeasureFano.condEntropy μ (fun ω j ↦ Ys j ω)
            (fun ω ↦ (((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)),
              (Msg₁ ω, Msg₂ ω))) := by
        have hE : (fun ω ↦ ((Msg₁ ω, Msg₂ ω),
              ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j))))
            = fun ω ↦ (MeasurableEquiv.prodComm
                (α := (Fin n → α₁) × (Fin n → α₂)) (β := Fin M₁ × Fin M₂))
                (((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)),
                  (Msg₁ ω, Msg₂ ω)) := by
          funext ω; simp [MeasurableEquiv.prodComm]
        rw [hE]
        exact condEntropy_measurableEquiv_comp μ (fun ω j ↦ Ys j ω) hYpi
          (fun ω ↦ (((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)),
            (Msg₁ ω, Msg₂ ω)))
          ((hX₁.prodMk hX₂).prodMk (hMsg₁.prodMk hMsg₂))
          (MeasurableEquiv.prodComm
            (α := (Fin n → α₁) × (Fin n → α₂)) (β := Fin M₁ × Fin M₂))
      rw [← hadd, hswapcond, hdropM]
    rw [hreshapeA, hcore, hreshapeB]
  linarith [hOL1, hOL2]

/-- **MAC converse, user-1 single-letterized corner bound** (gateway atom): under a
memoryless joint channel, independent messages, and the block channel Markov chain,
the message–output mutual information `I(M₁; (M₂, Yⁿ))` is bounded by the per-letter
single-letter channel sum `∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ)`. -/
theorem mac_singleletterize_bound₁
    [NeZero M₁] [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ
        (fun i ω ↦ (c.encoder₁ (Msg₁ ω) i, c.encoder₂ (Msg₂ ω) i)) Ys)
    (h_indep : mutualInfo μ Msg₁ Msg₂ = 0)
    (hmarkov : IsMarkovChain μ (fun ω ↦ (Msg₁ ω, Msg₂ ω))
      (fun ω ↦ ((fun j ↦ c.encoder₁ (Msg₁ ω) j), (fun j ↦ c.encoder₂ (Msg₂ ω) j)))
      (fun ω j ↦ Ys j ω)) :
    mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
      ≤ ∑ i : Fin n,
          condMutualInfo μ (fun ω ↦ c.encoder₁ (Msg₁ ω) i) (Ys i)
            (fun ω ↦ c.encoder₂ (Msg₂ ω) i) := by
  classical
  -- Per-letter input random variables.
  have hX₁s : ∀ i, Measurable (fun ω ↦ c.encoder₁ (Msg₁ ω) i) := fun i ↦
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder₁).comp hMsg₁)
  have hX₂s : ∀ i, Measurable (fun ω ↦ c.encoder₂ (Msg₂ ω) i) := fun i ↦
    (measurable_pi_apply i).comp ((measurable_of_countable c.encoder₂).comp hMsg₂)
  have hJoint : ∀ i, Measurable
      (fun ω ↦ (c.encoder₁ (Msg₁ ω) i, c.encoder₂ (Msg₂ ω) i)) := fun i ↦
    (hX₁s i).prodMk (hX₂s i)
  -- Strong memoryless from the per-letter memoryless predicate.
  have h_per_letter := per_letter_markov_of_memoryless μ
    (fun i ω ↦ (c.encoder₁ (Msg₁ ω) i, c.encoder₂ (Msg₂ ω) i)) Ys hJoint hYs h_memo
  have h_outputs := outputs_cond_indep_of_memoryless μ
    (fun i ω ↦ (c.encoder₁ (Msg₁ ω) i, c.encoder₂ (Msg₂ ω) i)) Ys hJoint hYs h_memo
  -- The two analytic steps (at the `.toReal` level).
  have h_link := mac_message_le_condMI μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs h_indep hmarkov
  have h_single := condMutualInfo_singleletter_le_of_memoryless μ
    (fun i ω ↦ c.encoder₁ (Msg₁ ω) i) (fun i ω ↦ c.encoder₂ (Msg₂ ω) i) Ys
    hX₁s hX₂s hYs h_per_letter h_outputs
  -- Finiteness for the `ℝ≥0∞`-lift.
  have hYpi : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  have hLHS_fin : mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω)) ≠ ∞ :=
    mutualInfo_ne_top μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω)) hMsg₁
      (hMsg₂.prodMk hYpi)
  have hRHS_fin : ∀ i, condMutualInfo μ (fun ω ↦ c.encoder₁ (Msg₁ ω) i) (Ys i)
      (fun ω ↦ c.encoder₂ (Msg₂ ω) i) ≠ ∞ := fun i ↦
    condMutualInfo_ne_top μ _ _ _ (hX₁s i) (hYs i) (hX₂s i)
  have hSum_fin : (∑ i : Fin n,
      condMutualInfo μ (fun ω ↦ c.encoder₁ (Msg₁ ω) i) (Ys i)
        (fun ω ↦ c.encoder₂ (Msg₂ ω) i)) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ ↦ (hRHS_fin i).lt_top).ne
  -- Combine and lift.
  rw [← ENNReal.toReal_le_toReal hLHS_fin hSum_fin,
    ENNReal.toReal_sum (fun i _ ↦ hRHS_fin i)]
  exact h_link.trans h_single

end SingleLetterization

end InformationTheory.Shannon.MAC
