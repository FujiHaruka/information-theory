import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Basic
import InformationTheory.Shannon.BroadcastChannel.ConverseGateway
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.CondMIChainRule
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule

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

/-- **BC converse, receiver-1 input-level single-letterization** (the Csiszár-sum core): under
degradedness `X → Y₁ → Y₂` and a memoryless channel with the conditioning message `W₂` upstream
of the channel, the conditional block input–output mutual information collapses to the
per-letter auxiliary-variable sum `I(Xⁿ; Y₁ⁿ | W₂) ≤ ∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` with
`Uᵢ = (W₂, Y₂^{i-1})`.

This is the decisive analytic atom of the degraded-BC converse: the prefix conditioner
`Y₁^{i-1}` is swapped for the suffix-of-the-degraded-output `Y₂^{i-1}` via the Csiszár sum
identity (`csiszar_sum_identity`), and the memoryless + degradedness structure reduces each
term to the single-letter channel quantity.

The memoryless hypothesis `h_memo` is the **`W₂`-inclusive** form `Y_{1,i} ⟂ (W₂, X^{≠i},
Y₁^{≠i}) | X_i`: it blocks the conditioning message `W₂` together with the other letters at
`X_i`, encoding that `W₂` is *upstream* of the channel (the noise generating `Y₁,i` is
independent of `W₂` given `X_i`). This is essential — with a bare memoryless channel and a
*free* `W₂`, the bound is false (a "collider" message `W₂ = Y₁,j ⊕ X_k` opens a path that
breaks the per-letter reduction). It is a structural/regularity precondition (true in the
genuine operational setup where `Xⁿ = encoder (W₁, W₂)`), not load-bearing.

@audit:defect(false-statement) — STILL FALSE AS FRAMED (a distinct mechanism from the
`8cffe3cb` `free W₂` collider fix). The `W₂`-inclusive `h_memo` blocks `(W₂, X^{≠i},
Y₁^{≠i})` at `X_i` but does NOT block `Y₂^{≠i}`, and `h_degraded` is only per-letter, so the
degraded output of an early letter may leak a *later* letter's input. Machine-checkable
counterexample: `n = 2`, `M₂ = 1` (so `W₂` is the constant on `Fin 1`),
`α = β₁ = β₂ = Bool`, `Ω = Bool × Bool` uniform; with first/second bit `a, b`, set
`X₀ = Y₁₀ = a`, `X₁ = Y₁₁ = b`, `Y₂₀ = b`, `Y₂₁ = b`. Both hypotheses hold trivially (each
`Y₁ᵢ` is a function of `Xᵢ`, so `Y₁ᵢ ⊥ rest | Xᵢ`; `Y₂ᵢ ⊥ Xᵢ | Y₁ᵢ`), yet the LHS
`I(X⁰¹; Y₁⁰¹ | W₂) = H(a, b) = 2` while the RHS
`I(X₀; Y₁₀) + I(X₁; Y₁₁ | Y₂₀) = 1 + I(b; b | b) = 1 + 0 = 1`, so the claimed `2 ≤ 1`
fails. The fix is a *joint-output* memoryless hypothesis
`(W₂, X^{≠i}, Y₁^{≠i}, Y₂^{≠i}) → Xᵢ → (Y₁ᵢ, Y₂ᵢ)` (blocking `Y₂^{≠i}` as well), or an
equivalent block-degradedness assumption — a signature change owned by the plan.
@audit:closed-by-successor(bc-degraded-converse-plan)
@residual(plan:bc-degraded-converse-plan) -/
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
           (fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω))))
        (Xs i) (Y₁s i))
    (h_degraded : ∀ i, IsMarkovChain μ (Xs i) (Y₁s i) (Y₂s i)) :
    condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ Y₁s j ω) W₂
      ≤ ∑ i : Fin n,
          condMutualInfo μ (Xs i) (Y₁s i)
            (fun ω ↦ (W₂ ω,
              fun (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  sorry

/-- **BC converse, receiver-1 single-letterized corner bound** (bound (b)): the message–output
mutual information `I(W₁; (W₂, Y₁ⁿ))` is bounded by the per-letter auxiliary-variable sum
`∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` with `Uᵢ = (W₂, Y₂^{i-1})`, `Xᵢ = (encoder (W₁, W₂))ᵢ`.

Reduction: independence gives `I(W₁; (W₂, Y₁ⁿ)) = I(W₁; Y₁ⁿ | W₂)`; data processing along
`W₁ → Xⁿ → Y₁ⁿ` (conditioned on `W₂`) gives `≤ I(Xⁿ; Y₁ⁿ | W₂)`; then the Csiszár-sum
single-letterization `bc_input_singleletterize` closes the bound. -/
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
           (fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω))))
        (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i))
    (h_degraded : ∀ i, IsMarkovChain μ (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i) (Y₂s i))
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
  have hstep3 := bc_input_singleletterize μ W₂ Xs Y₁s Y₂s hW₂ hXs hY₁s hY₂s h_memo h_degraded
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
separate wrapper, not part of this statement. -/
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
           (fun (j : {j : Fin n // j ≠ i}) ↦ Y₁s j.val ω))))
        (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i))
    (h_degraded : ∀ i, IsMarkovChain μ (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i) (Y₂s i))
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
    h_indep h_memo h_degraded hmarkov
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
